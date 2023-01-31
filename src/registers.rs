#[derive(Copy, Clone)]
pub struct StatusArgs {
    pub negative: bool,
    pub overflow: bool,
    pub unused: bool,
    pub brk: bool,
    pub decimal_mode: bool,
    pub disable_interrupts: bool,
    pub zero: bool,
    pub carry: bool
}

impl StatusArgs {
    pub fn none() -> StatusArgs {
        StatusArgs {
            negative: false,
            overflow: false,
            unused: false,
            brk: false,
            decimal_mode: false,
            disable_interrupts: false,
            zero: false,
            carry: false,
        }
    }
}

bitflags! {
    pub struct Status: u8 {
        const PS_NEGATIVE           = 0b1000_0000;
        const PS_OVERFLOW           = 0b0100_0000;
        const PS_UNUSED             = 0b0010_0000;
        const PS_BRK                = 0b0001_0000;
        const PS_DECIMAL_MODE       = 0b0000_1000;
        const PS_DISABLE_INTERRUPTS = 0b0000_0100;
        const PS_ZERO               = 0b0000_0010;
        const PS_CARRY              = 0b0000_0001;
    }
}

impl Status {
    pub fn default() -> Status {
        Status::new(StatusArgs {
            negative: false,
            overflow: false,
            unused: false,
            brk: false,
            decimal_mode: false,
            disable_interrupts: false,
            zero: false,
            carry: false,
        })
    }

    pub fn new(
        StatusArgs {
        negative, overflow, unused, brk, decimal_mode, disable_interrupts, zero, carry
        }: StatusArgs) -> Status {
            let mut out = Status::empty();

            if negative {
                out |= Status::PS_NEGATIVE
            }
            if overflow {
                out |= Status::PS_OVERFLOW
            }
            if unused {
                out |= Status::PS_UNUSED
            }
            if brk {
                out |= Status::PS_BRK
            }
            if decimal_mode {
                out |= Status::PS_DECIMAL_MODE
            }
            if disable_interrupts {
                out |= Status::PS_DISABLE_INTERRUPTS
            }
            if zero {
                out |= Status::PS_ZERO
            }
            if carry {
                out |= Status::PS_CARRY
            }

            out
    }

    pub fn and(&mut self, rhs: Status) {
        *self &= rhs;
    }

    pub fn or(&mut self, rhs: Status) {
        *self |= rhs;
    }

    pub fn set_with_mask(&mut self, mask: Status, rhs: Status) {
        *self = (*self & !mask) | rhs;
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct StackPointer(pub u8);

impl StackPointer {
    pub fn to_u16(self) -> u16 {
        let StackPointer(value) = self;
        u16::from_le_bytes([value, 0x01])
    }

    pub fn decrement(&mut self) {
        self.0 = self.0.wrapping_sub(1);
    }

    pub fn increment(&mut self) {
        self.0 = self.0.wrapping_add(1);
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Register {
    pub accumulator: i8,
    pub index_x: u8,
    pub index_y: u8,
    pub stack_pointer: StackPointer,
    pub program_counter: u16,
    pub status: Status,
}

impl Default for Register {
    fn default() -> Self {
        Self::new()
    }
}

impl Register {
    pub fn new() -> Register {
        Register {
            accumulator: 0,
            index_x: 0,
            index_y: 0,
            stack_pointer: StackPointer(0),
            program_counter: 0,
            status: Status::default(),
        }
    }
}