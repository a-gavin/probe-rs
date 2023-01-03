use std::io;

use bitvec::{order::Lsb0, prelude::BitVec, slice::BitSlice};
use ftdi_mpsse::*;

use crate::{probe::CommandResult, DebugProbeError};

use super::ChainParams;

pub trait JtagCommand: std::fmt::Debug + Send {
    fn add_bytes(&mut self, buffer: &mut Vec<u8>);

    fn bytes_to_read(&self) -> usize;

    fn process_output(&self, data: &[u8]) -> Result<CommandResult, DebugProbeError>;
}

// ReadRegisterCommand and WriteRegisterCommand have same structure
// save that ReadRegisterCommand passes None for data and WriteRegisterCommand
// passes Some(Vec<u8>) in creating the TargetTransferCommand
#[derive(Debug)]
pub struct ReadRegisterCommand {
    subcommands: [Box<dyn JtagCommand>; 2],
}

impl ReadRegisterCommand {
    pub(super) fn new(
        address: u32,
        len: usize,
        idle_cycles: usize,
        chain_params: ChainParams,
    ) -> io::Result<ReadRegisterCommand> {
        let target_transfer = TargetTransferCommand::new(address, None, len, chain_params)?;
        let idle = IdleCommand::new(idle_cycles);

        Ok(ReadRegisterCommand {
            subcommands: [Box::new(target_transfer), Box::new(idle)],
        })
    }
}

impl JtagCommand for ReadRegisterCommand {
    fn add_bytes(&mut self, buffer: &mut Vec<u8>) {
        for subcommand in &mut self.subcommands {
            subcommand.add_bytes(buffer);
        }
    }

    fn bytes_to_read(&self) -> usize {
        self.subcommands.iter().map(|e| e.bytes_to_read()).sum()
    }

    fn process_output(&self, data: &[u8]) -> Result<CommandResult, DebugProbeError> {
        let r = self.subcommands[0].process_output(&data[0..(self.subcommands[0].bytes_to_read())]);
        self.subcommands[1].process_output(&data[self.subcommands[0].bytes_to_read()..])?;
        r
    }
}

#[derive(Debug)]
pub struct WriteRegisterCommand {
    subcommands: [Box<dyn JtagCommand>; 2],
}

impl WriteRegisterCommand {
    pub(super) fn new(
        address: u32,
        data: Vec<u8>,
        len: usize,
        idle_cycles: usize,
        chain_params: ChainParams,
    ) -> io::Result<WriteRegisterCommand> {
        let target_transfer = TargetTransferCommand::new(address, Some(data), len, chain_params)?;
        let idle = IdleCommand::new(idle_cycles);

        Ok(WriteRegisterCommand {
            subcommands: [Box::new(target_transfer), Box::new(idle)],
        })
    }
}

impl JtagCommand for WriteRegisterCommand {
    fn add_bytes(&mut self, buffer: &mut Vec<u8>) {
        for subcommand in &mut self.subcommands {
            subcommand.add_bytes(buffer);
        }
    }

    fn bytes_to_read(&self) -> usize {
        self.subcommands.iter().map(|e| e.bytes_to_read()).sum()
    }

    fn process_output(&self, data: &[u8]) -> Result<CommandResult, DebugProbeError> {
        let r = self.subcommands[0].process_output(&data[0..(self.subcommands[0].bytes_to_read())]);
        self.subcommands[1].process_output(&data[self.subcommands[0].bytes_to_read()..])?;
        r
    }
}

#[derive(Debug)]
struct TargetTransferCommand {
    len: usize,
    chain_params: ChainParams,
    shift_ir_cmd: ShiftIrCommand,
    transfer_dr_cmd: TransferDrCommand,
}

impl TargetTransferCommand {
    pub fn new(
        address: u32,
        data: Option<Vec<u8>>,
        len: usize,
        chain_params: ChainParams,
    ) -> io::Result<TargetTransferCommand> {
        let params = &chain_params;
        let max_address = (1 << params.irlen) - 1;
        assert!(address <= max_address);

        // Write IR register
        let irbits = params.irpre + params.irlen + params.irpost;
        assert!(irbits <= 32);
        let mut ir: u32 = (1 << params.irpre) - 1;
        ir |= address << params.irpre;
        ir |= ((1 << params.irpost) - 1) << (params.irpre + params.irlen);

        let shift_ir_cmd = ShiftIrCommand::new(ir.to_le_bytes().to_vec(), irbits);

        let drbits = params.drpre + len + params.drpost;
        let request = if let Some(data_slice) = data {
            // Write
            let data = BitSlice::<u8, Lsb0>::from_slice(&data_slice);
            let mut data = BitVec::<u8, Lsb0>::from_bitslice(data);
            data.truncate(len);

            let mut buf = BitVec::<u8, Lsb0>::new();
            buf.resize(params.drpre, false);
            buf.append(&mut data);
            buf.resize(buf.len() + params.drpost, false);

            buf.into_vec()
        } else {
            // Read
            vec![0; (drbits + 7) / 8]
        };

        let transfer_dr = TransferDrCommand::new(request.to_vec(), drbits);

        Ok(TargetTransferCommand {
            len,
            chain_params,
            shift_ir_cmd,
            transfer_dr_cmd: transfer_dr,
        })
    }
}

impl JtagCommand for TargetTransferCommand {
    fn add_bytes(&mut self, buffer: &mut Vec<u8>) {
        self.shift_ir_cmd.add_bytes(buffer);
        self.transfer_dr_cmd.add_bytes(buffer);
    }

    fn bytes_to_read(&self) -> usize {
        self.shift_ir_cmd.bytes_to_read() + self.transfer_dr_cmd.bytes_to_read()
    }

    fn process_output(&self, data: &[u8]) -> Result<CommandResult, DebugProbeError> {
        let params = self.chain_params;
        let reply = self.transfer_dr_cmd.process_output(data);

        let reply = if let Ok(CommandResult::VecU8(reply)) = reply {
            reply
        } else {
            return Err(DebugProbeError::ProbeSpecific(Box::new(
                std::io::Error::new(std::io::ErrorKind::InvalidData, "Unexpected data received"),
            )));
        };

        // Process the reply
        let mut reply = BitVec::<u8, Lsb0>::from_vec(reply);
        if params.drpre > 0 {
            reply = reply.split_off(params.drpre);
        }
        reply.truncate(self.len);
        let reply = reply.into_vec();

        Ok(CommandResult::VecU8(reply))
    }
}

#[derive(Debug)]
struct ShiftIrCommand {
    subcommands: [Box<dyn JtagCommand>; 3],
}
impl ShiftIrCommand {
    pub fn new(data: Vec<u8>, bits: usize) -> ShiftIrCommand {
        ShiftIrCommand {
            subcommands: [
                Box::new(ShiftTmsCommand::new(vec![0b0011], 4)), // RUN-TEST-IDLE to SHIFT-IR
                Box::new(ShiftTdiCommand::new(data, bits)),
                Box::new(ShiftTmsCommand::new(vec![0b01], 2)), // SHIFT-IR to RUN-TEST-IDLE, SHIFT-IR to EXIT-1-IR bit clocked in TransferTdiCommand
            ],
        }
    }
}

impl JtagCommand for ShiftIrCommand {
    fn add_bytes(&mut self, buffer: &mut Vec<u8>) {
        for subcommand in &mut self.subcommands {
            subcommand.add_bytes(buffer);
        }
    }

    fn bytes_to_read(&self) -> usize {
        self.subcommands.iter().map(|e| e.bytes_to_read()).sum()
    }

    fn process_output(&self, data: &[u8]) -> Result<CommandResult, DebugProbeError> {
        let mut start = 0usize;
        for subcommand in &self.subcommands {
            let end = start + subcommand.bytes_to_read();
            let cmd_data = data[start..end].to_vec();
            let _ = subcommand.process_output(&cmd_data); // TODO check if ok
            start += subcommand.bytes_to_read();
        }

        Ok(CommandResult::None)
    }
}

#[derive(Debug)]
pub(super) struct TransferDrCommand {
    subcommands: Vec<Box<dyn JtagCommand>>,
}

impl TransferDrCommand {
    pub fn new(data: Vec<u8>, bits: usize) -> TransferDrCommand {
        TransferDrCommand {
            subcommands: vec![
                Box::new(ShiftTmsCommand::new(vec![0b001], 3)), // RUN-TEST-IDLE to SHIFT-DR
                Box::new(TransferTdiCommand::new(data, bits)),
                Box::new(ShiftTmsCommand::new(vec![0b01], 2)), // SHIFT-DR to RUN-TEST-IDLE, SHIFT-DR to EXIT-1-DR bit clocked in TransferTdiCommand
            ],
        }
    }
}

impl JtagCommand for TransferDrCommand {
    fn add_bytes(&mut self, buffer: &mut Vec<u8>) {
        for subcommand in &mut self.subcommands {
            subcommand.add_bytes(buffer);
        }
    }

    fn bytes_to_read(&self) -> usize {
        self.subcommands.iter().map(|e| e.bytes_to_read()).sum()
    }

    fn process_output(&self, data: &[u8]) -> Result<CommandResult, DebugProbeError> {
        let mut start = 0usize;

        let end = start + self.subcommands[0].bytes_to_read();
        let cmd_data = data[start..end].to_vec();
        self.subcommands[0].process_output(&cmd_data)?;
        start += self.subcommands[0].bytes_to_read();

        let end = start + self.subcommands[1].bytes_to_read();
        let cmd_data = data[start..end].to_vec();
        let reply = self.subcommands[1].process_output(&cmd_data);
        start += self.subcommands[1].bytes_to_read();

        let end = start + self.subcommands[2].bytes_to_read();
        let cmd_data = data[start..end].to_vec();
        self.subcommands[2].process_output(&cmd_data)?;

        reply
    }
}

#[derive(Debug)]
pub(super) struct TransferIrCommand {
    subcommands: Vec<Box<dyn JtagCommand>>,
}

impl TransferIrCommand {
    pub fn new(data: Vec<u8>, bits: usize) -> TransferIrCommand {
        TransferIrCommand {
            subcommands: vec![
                Box::new(ShiftTmsCommand::new(vec![0b0011], 4)), // RUN-TEST-IDLE to SHIFT-IR
                Box::new(TransferTdiCommand::new(data, bits)),
                Box::new(ShiftTmsCommand::new(vec![0b01], 2)), // SHIFT-IR to RUN-TEST-IDLE, SHIFT-IR to EXIT-1-IR bit clocked in TransferTdiCommand
            ],
        }
    }
}

impl JtagCommand for TransferIrCommand {
    fn add_bytes(&mut self, buffer: &mut Vec<u8>) {
        for subcommand in &mut self.subcommands {
            subcommand.add_bytes(buffer);
        }
    }

    fn bytes_to_read(&self) -> usize {
        self.subcommands.iter().map(|e| e.bytes_to_read()).sum()
    }

    fn process_output(&self, data: &[u8]) -> Result<CommandResult, DebugProbeError> {
        let mut start = 0usize;

        let end = start + self.subcommands[0].bytes_to_read();
        let cmd_data = data[start..end].to_vec();
        self.subcommands[0].process_output(&cmd_data)?;
        start += self.subcommands[0].bytes_to_read();

        let end = start + self.subcommands[1].bytes_to_read();
        let cmd_data = data[start..end].to_vec();
        let reply = self.subcommands[1].process_output(&cmd_data);
        start += self.subcommands[1].bytes_to_read();

        let end = start + self.subcommands[2].bytes_to_read();
        let cmd_data = data[start..end].to_vec();
        self.subcommands[2].process_output(&cmd_data)?;

        reply
    }
}

#[derive(Debug)]
pub struct ShiftTmsCommand {
    data: Vec<u8>,
    bits: usize,
}

impl ShiftTmsCommand {
    /// Most significant bit in each byte of `data` is transferred on TDI, not as TMS.
    ///
    /// Can only clock up to 7 bits on TMS for each FTDI clock TMS command
    pub fn new(data: Vec<u8>, bits: usize) -> ShiftTmsCommand {
        assert!(bits > 0);
        assert!((bits + 7) / 8 <= data.len());

        ShiftTmsCommand { data, bits }
    }
}

impl JtagCommand for ShiftTmsCommand {
    fn add_bytes(&mut self, buffer: &mut Vec<u8>) {
        let mut command = MpsseCmdBuilder::new();

        // Clock Data to TMS pin, no read.
        //
        // Can only clock 7 TMS bits at a time, as 8th bit reserved for TDI output.
        // However, this is never called where we transfer TDI data at same time,
        // so TDI arg always false in clock_tms_out()
        //
        // See section 3.5 of https://www.ftdichip.com/Support/Documents/AppNotes/AN_108_Command_Processor_for_MPSSE_and_MCU_Host_Bus_Emulation_Modes.pdf
        let mut bits = self.bits;
        let mut data: &[u8] = &self.data;
        while bits > 0 {
            if bits >= 8 {
                command = command.clock_tms_out(ClockTMSOut::NegEdge, data[0], false, 7);
                data = &data[1..];
                bits -= 8;
            } else {
                command = command.clock_tms_out(ClockTMSOut::NegEdge, data[0], false, bits as u8);
                bits = 0;
            }
        }

        buffer.extend_from_slice(command.as_slice());
    }

    fn bytes_to_read(&self) -> usize {
        0
    }

    fn process_output(&self, _data: &[u8]) -> Result<CommandResult, DebugProbeError> {
        Ok(CommandResult::None)
    }
}

#[derive(Debug)]
struct ShiftTdiCommand {
    data: Vec<u8>,
    bits: usize,
}

impl ShiftTdiCommand {
    pub fn new(data: Vec<u8>, bits: usize) -> ShiftTdiCommand {
        ShiftTdiCommand { data, bits }
    }
}

impl JtagCommand for ShiftTdiCommand {
    fn add_bytes(&mut self, buffer: &mut Vec<u8>) {
        assert!(self.bits > 0);
        assert!((self.bits + 7) / 8 <= self.data.len());

        let mut command = MpsseCmdBuilder::new();
        let mut bits = self.bits;
        let mut data: &[u8] = &self.data;

        // Preserve one data bit for clocking out with TMS at end of ShiftTdiCommand
        let full_bytes = (bits - 1) / 8;

        // Clock out full byte data
        if full_bytes > 0 {
            assert!(full_bytes <= 65536);

            command = command.clock_data_out(ClockDataOut::LsbNeg, &data[..full_bytes]);

            bits -= full_bytes * 8;
            data = &data[full_bytes..];
        }

        // Clock out data less than full byte
        // Always have at least one bit leftover to clock TMS bit
        assert!(0 < bits && bits <= 8);
        let byte = data[0];

        // Clock out everything other than last data bit (last bit transferred with TMS in next command)
        if bits > 1 {
            command = command.clock_bits_out(ClockBitsOut::LsbNeg, byte, (bits - 1) as u8);
        }

        // Clock out last bit of TDI in conjunction with first bit of TMS
        // ShiftTdiCommand only used in ShiftIrCommand, which always returns to RUN-TEST-IDLE TAP state
        // after ShiftTdiCommand completion, so begin return to RUN-TEST-IDLE state here
        let last_tdi_bit = (byte >> (bits - 1)) & 0x01;
        let tms_cmd_data = 0x01 | (last_tdi_bit << 7); // Clock 1 to TMS to go from SHIFT-IR to EXIT-1-IR
        command = command.clock_tms_out(ClockTMSOut::NegEdge, tms_cmd_data, true, 1);

        buffer.extend_from_slice(command.as_slice());
    }

    fn bytes_to_read(&self) -> usize {
        0
    }

    fn process_output(&self, _data: &[u8]) -> Result<CommandResult, DebugProbeError> {
        Ok(CommandResult::None)
    }
}

#[derive(Debug)]
struct TransferTdiCommand {
    data: Vec<u8>,
    bits: usize,

    response_bytes: usize,
}

impl TransferTdiCommand {
    pub fn new(data: Vec<u8>, bits: usize) -> TransferTdiCommand {
        TransferTdiCommand {
            data,
            bits,
            response_bytes: 0,
        }
    }
}

impl JtagCommand for TransferTdiCommand {
    fn add_bytes(&mut self, buffer: &mut Vec<u8>) {
        assert!(self.bits > 0);
        assert!((self.bits + 7) / 8 <= self.data.len());

        let mut command = MpsseCmdBuilder::new();

        let mut bits = self.bits;
        let mut data: &[u8] = &self.data;

        // Preserve one data bit for clocking out with TMS at end of ShiftTdiCommand
        let full_bytes = (bits - 1) / 8;

        // Clock out full byte data
        if full_bytes > 0 {
            assert!(full_bytes <= 65536);

            command = command.clock_data(ClockData::LsbPosIn, &data[..full_bytes]);

            bits -= full_bytes * 8;
            data = &data[full_bytes..];
        }

        // Clock out data less than full byte
        // Always have at least one bit leftover to clock TMS bit
        assert!(0 < bits && bits <= 8);
        let byte = data[0];

        // Clock out everything other than last data bit (last bit transferred with TMS in next command)
        if bits > 1 {
            command = command.clock_bits(ClockBits::LsbPosIn, byte, (bits - 1) as u8);
        }

        // Clock out last bit of TDI in conjunction with first bit of TMS
        // ShiftTdiCommand only used in ShiftIrCommand, which always returns to RUN-TEST-IDLE TAP state
        // after ShiftTdiCommand completion, so begin return to RUN-TEST-IDLE state here
        let last_tdi_bit = (byte >> (bits - 1)) & 0x01;
        let tms_cmd_data = 0x01 | (last_tdi_bit << 7); // Clock 1 to TMS to go from SHIFT-DR to EXIT-1-DR
        command = command.clock_tms(ClockTMS::NegTMSPosTDO, tms_cmd_data, true, 1);

        buffer.extend_from_slice(command.as_slice());

        let mut expect_bytes = full_bytes + 1; // Plus one for TMS command
        if bits > 1 {
            expect_bytes += 1; // Plus one if more than one bit leftover
        }

        self.bits = bits;
        self.response_bytes = expect_bytes;
    }

    fn bytes_to_read(&self) -> usize {
        self.response_bytes
    }

    fn process_output(&self, data: &[u8]) -> Result<CommandResult, DebugProbeError> {
        let mut last_byte = data[data.len() - 1] >> 7;
        if self.bits > 1 {
            let byte = data[data.len() - 2] >> (8 - (self.bits - 1));
            last_byte = byte | (last_byte << (self.bits - 1));
        }

        let mut reply = Vec::<u8>::new();
        reply.extend_from_slice(data);
        reply.push(last_byte);
        Ok(CommandResult::VecU8(reply))
    }
}

/// Execute RUN-TEST/IDLE for a number of cycles
#[derive(Debug)]
struct IdleCommand {
    cycles: usize,
}

impl IdleCommand {
    pub fn new(cycles: usize) -> IdleCommand {
        IdleCommand { cycles }
    }
}

impl JtagCommand for IdleCommand {
    fn add_bytes(&mut self, buffer: &mut Vec<u8>) {
        if self.cycles == 0 {
            return;
        }

        // Resize buf to number of idle cycles desired
        // while accounting for FTDI TMS commands only clocking
        // 7 TMS bits per command (MSB is held static on TDI)
        //
        // See section 3.5 of https://www.ftdichip.com/Support/Documents/AppNotes/AN_108_Command_Processor_for_MPSSE_and_MCU_Host_Bus_Emulation_Modes.pdf
        let num_tms_cmds = if self.cycles % 7 == 0 {
            self.cycles / 7
        } else {
            (self.cycles / 7) + 1
        };

        let buf = vec![0; num_tms_cmds];
        ShiftTmsCommand::new(buf, self.cycles).add_bytes(buffer);
    }

    fn bytes_to_read(&self) -> usize {
        0
    }

    fn process_output(&self, _data: &[u8]) -> Result<CommandResult, DebugProbeError> {
        Ok(CommandResult::None)
    }
}
