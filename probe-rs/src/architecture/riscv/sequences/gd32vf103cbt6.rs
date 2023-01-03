//! Sequences for the GD32VF103CBT6.

use std::sync::Arc;

use super::RiscvDebugSequence;
use crate::architecture::riscv::{
    communication_interface::{RiscvCommunicationInterface, RiscvError},
    Dmstatus,
};

/// The debug sequence implementation for the GD32VF103CBT6.
pub struct GD32VF103CBT6(());

impl GD32VF103CBT6 {
    /// Creates a new debug sequence handle for the GD32VF103CBT6.
    pub fn create() -> Arc<dyn RiscvDebugSequence> {
        Arc::new(Self(()))
    }
}

impl RiscvDebugSequence for GD32VF103CBT6 {
    fn check_cores_reset(
        &self,
        interface: &mut RiscvCommunicationInterface,
    ) -> Result<(), crate::Error> {
        tracing::info!("Checking GD32VF103CBT6 cores have reset");
        let mut readback: Dmstatus = interface.read_dm_register()?;

        if readback.allunavail() {
            while readback.allunavail() {
                tracing::info!(
                    "Not all cores available, checking again, Dmstatus: {:?}",
                    readback
                );
                readback = interface.read_dm_register()?;
            }
        }

        if !readback.allhalted() {
            tracing::info!(
                "All cores available but not all halted, Dmstatus: {:?}",
                readback
            );
            return Err(RiscvError::RequestNotAcknowledged.into());
        }

        if !readback.allhavereset() {
            tracing::info!(
                "Not all cores have reset - ignoring, Dmstatus: {:?}",
                readback
            );
        }

        Ok(())
    }
}
