pub struct AddressRangeIncl {
    begin: u16,
    end: u16,
}

const ADDR_BARE: AddressRangeIncl = AddressRangeIncl{ begin: 0x0000, end: 0xFFFF};

pub const MEMORY_ADDRESS: AddressRangeIncl = AddressRangeIncl{
    begin: ADDR_BARE.begin,
    end: ADDR_BARE.end
};
pub const STACK_ADDRESS: AddressRangeIncl = AddressRangeIncl{
    begin: 0x0100,
    end: 0x01FF
};
pub const IRQ_INTERRUPT_VECTOR: AddressRangeIncl = AddressRangeIncl{
    begin: 0xFFFE,
    end: 0xFFFF
};

const MEMORY_SIZE: usize = (ADDR_BARE.end - ADDR_BARE.begin) as usize + 1usize;

#[derive(Copy, Clone)]
pub struct Memory {
    bytes: [u8; MEMORY_SIZE]
}

impl Default for Memory {
    fn default() -> Self {
        Self::new()
    }
}

impl Memory {
    pub fn new() -> Memory {
        Memory {
            bytes: [0; MEMORY_SIZE],
        }
    }

    pub fn get_byte(&self, address: u16) -> u8 {
        self.bytes[address as usize]
    }

    pub fn get_byte_mut_ref(&mut self, address: u16) -> &mut u8 {
        &mut self.bytes[address as usize]
    }

    pub fn get_slice(&self, start_addr: u16, diff: u16) -> &[u8] {
        let original: usize = start_addr as usize;
        let end: usize = original + diff as usize;

        //Should panic if access out of range happens
        &self.bytes[original..end]
    }

    pub fn set_byte(&mut self, address: u16, value: u8) -> u8 {
        let old_value: u8 = self.get_byte(address);

        self.bytes[address as usize] = value;
        old_value
    }

    pub fn set_bytes(&mut self, start_addr: u16, values: &[u8]) {
        let end_addr: usize = start_addr as usize + values.len();
        let start_addr: usize = start_addr as usize;

        //start - end must be the same size as copy_from_slice
        //copy_from_slice copies each value into self
        self.bytes[start_addr..end_addr].copy_from_slice(values);
    }

    pub fn is_stack_address(address: u16) -> bool {
        address > 0xFF && address < 0x200
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_memory_set_bytes() {
        let mut memory = Memory::new();
        memory.set_bytes(0x0100, &[1, 2, 3, 4, 5]);
        assert_eq!(memory.get_slice(0x00FF, 7), &[0, 1, 2, 3, 4, 5, 0]);
    }

    #[test]
    #[should_panic]
    fn test_memory_overflow_panic() {
        let mut memory = Memory::new();
        memory.set_bytes(0xFFFE, &[1, 2, 3]);
    }
}