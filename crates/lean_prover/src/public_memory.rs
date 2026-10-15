use backend::{PrimeCharacteristicRing, log2_strict_usize};
use lean_vm::{F, MAX_LOG_MEMORY_SIZE};

/// An application-selected, aligned public slice of the committed VM memory.
/// The verifier must obtain its address and size from the expected program interface.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PublicMemoryRegion {
    pub start: usize,
    pub values: Vec<F>,
}

impl PublicMemoryRegion {
    pub const DOMAIN: u32 = 0x5055_4d31; // ASCII "PUM1".

    pub fn validate(&self) -> Result<(), &'static str> {
        if !self.values.len().is_power_of_two() {
            return Err("public memory length must be a nonzero power of two");
        }
        if !self.start.is_multiple_of(self.values.len()) {
            return Err("public memory start must be aligned to its length");
        }
        let end = self
            .start
            .checked_add(self.values.len())
            .ok_or("public memory end overflow")?;
        if end > 1usize << MAX_LOG_MEMORY_SIZE {
            return Err("public memory exceeds the VM address space");
        }
        Ok(())
    }

    pub fn validate_for_memory_len(&self, memory_len: usize) -> Result<(), &'static str> {
        self.validate()?;
        if self.start + self.values.len() > memory_len {
            return Err("public memory region exceeds committed memory");
        }
        Ok(())
    }

    pub(crate) fn check_witness(&self, memory: &[F]) -> Result<(), &'static str> {
        self.validate_for_memory_len(memory.len())?;
        if memory[self.start..self.start + self.values.len()] != self.values {
            return Err("executed memory does not match the public memory region");
        }
        Ok(())
    }

    /// Call after validation, before observing dimensions or the first commitment.
    pub fn transcript_header(&self) -> [F; 8] {
        [
            F::from_u32(Self::DOMAIN),
            F::from_usize(self.start),
            F::from_usize(self.values.len()),
            F::ZERO,
            F::ZERO,
            F::ZERO,
            F::ZERO,
            F::ZERO,
        ]
    }

    pub fn num_variables(&self) -> usize {
        log2_strict_usize(self.values.len())
    }

    pub fn selector(&self) -> usize {
        self.start >> self.num_variables()
    }
}

#[cfg(test)]
mod tests;
