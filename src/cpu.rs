use crate::instructions;
use crate::instructions::{DecodedInstr, Instruction, OperationInput};
use crate::memory::Memory;
use crate::registers::{Register, StackPointer, Status, StatusArgs};

#[derive(Clone, Copy)]
pub struct CPU {
    pub registers: Register,
    pub memory: Memory,
}

impl Default for CPU {
    fn default() -> Self {
        Self::new()
    }
}

impl CPU {
    pub fn new() -> CPU {
        CPU {
            registers: Register::new(),
            memory: Memory::new(),
        }
    }

    pub fn reset(&mut self) {
        *self = CPU::new();
    }

    pub fn fetch_next_and_decode(&mut self) -> Option<DecodedInstr> {
        let x: u8 = self.memory.get_byte(self.registers.program_counter);

        match instructions::OPCODES[x as usize] {
            Some((instr, am)) => {
                let extra_bytes = am.extra_bytes();
                let num_bytes = extra_bytes + 1;

                let data_start = self.registers.program_counter.wrapping_add(1);

                //TODO: fix error[E0502]: cannot borrow `*self` as immutable because it is also borrowed as mutable
                let slice = self.memory.get_slice(data_start, extra_bytes);
                let am_out = am.process(
                    self,
                    slice
                );

                // Increment program counter
                self.registers.program_counter =
                    self.registers.program_counter.wrapping_add(num_bytes);

                Some((instr, am_out))
            }
            _ => None,
        }
    }

    pub fn execute_instruction(&mut self, decoded_instr: DecodedInstr) {
        match decoded_instr {
            (Instruction::ADC, OperationInput::UseImmediate(val)) => {
                self.add_with_carry(val as i8);
            }
            (Instruction::ADC, OperationInput::UseAddress(addr)) => {
                let val = self.memory.get_byte(addr) as i8;
                self.add_with_carry(val);
            }

            (Instruction::AND, OperationInput::UseImmediate(val)) => {
                self.and(val as i8);
            }
            (Instruction::AND, OperationInput::UseAddress(addr)) => {
                let val = self.memory.get_byte(addr) as i8;
                self.and(val as i8);
            }

            (Instruction::ASL, OperationInput::UseImplied) => {
                // Accumulator mode
                let mut val = self.registers.accumulator as u8;
                CPU::shift_left_with_flags(&mut val, &mut self.registers.status);
                self.registers.accumulator = val as i8;
            }
            (Instruction::ASL, OperationInput::UseAddress(addr)) => {
                CPU::shift_left_with_flags(
                    self.memory.get_byte_mut_ref(addr),
                    &mut self.registers.status,
                );
            }

            (Instruction::BCC, OperationInput::UseRelative(rel)) => {
                let addr = self.registers.program_counter.wrapping_add(rel);
                self.branch_if_carry_clear(addr);
            }

            (Instruction::BCS, OperationInput::UseRelative(rel)) => {
                let addr = self.registers.program_counter.wrapping_add(rel);
                self.branch_if_carry_set(addr);
            }

            (Instruction::BEQ, OperationInput::UseRelative(rel)) => {
                let addr = self.registers.program_counter.wrapping_add(rel);
                self.branch_if_equal(addr);
            }

            (Instruction::BIT, OperationInput::UseAddress(addr)) => {
                let a: u8 = self.registers.accumulator as u8;
                let m: u8 = self.memory.get_byte(addr);
                let res = a & m;

                // The zero flag is set based on the result of the 'and'.
                let is_zero = 0 == res;

                // The N flag is set to bit 7 of the byte from memory.
                let bit7 = 0 != (0x80 & res);

                // The V flag is set to bit 6 of the byte from memory.
                let bit6 = 0 != (0x40 & res);

                self.registers.status.set_with_mask(
                    Status::PS_ZERO | Status::PS_NEGATIVE | Status::PS_OVERFLOW,
                    Status::new(StatusArgs {
                        zero: is_zero,
                        negative: bit7,
                        overflow: bit6,
                        ..StatusArgs::none()
                    }),
                );
            }

            (Instruction::BMI, OperationInput::UseRelative(rel)) => {
                let addr = self.registers.program_counter.wrapping_add(rel);
                self.branch_if_minus(addr);
            }

            (Instruction::BPL, OperationInput::UseRelative(rel)) => {
                let addr = self.registers.program_counter.wrapping_add(rel);
                self.branch_if_positive(addr);
            }

            (Instruction::BVC, OperationInput::UseRelative(rel)) => {
                let addr = self.registers.program_counter.wrapping_add(rel);
                self.branch_if_overflow_clear(addr);
            }

            (Instruction::BVS, OperationInput::UseRelative(rel)) => {
                let addr = self.registers.program_counter.wrapping_add(rel);
                self.branch_if_overflow_set(addr);
            }

            (Instruction::CLC, OperationInput::UseImplied) => {
                self.registers.status.and(!Status::PS_CARRY);
            }
            (Instruction::CLD, OperationInput::UseImplied) => {
                self.registers.status.and(!Status::PS_DECIMAL_MODE);
            }
            (Instruction::CLI, OperationInput::UseImplied) => {
                self.registers.status.and(!Status::PS_DISABLE_INTERRUPTS);
            }
            (Instruction::CLV, OperationInput::UseImplied) => {
                self.registers.status.and(!Status::PS_OVERFLOW);
            }

            (Instruction::CMP, OperationInput::UseImmediate(val)) => {
                self.compare_with_a_register(val);
            }
            (Instruction::CMP, OperationInput::UseAddress(addr)) => {
                let val = self.memory.get_byte(addr);
                self.compare_with_a_register(val);
            }

            (Instruction::CPX, OperationInput::UseImmediate(val)) => {
                self.compare_with_x_register(val);
            }
            (Instruction::CPX, OperationInput::UseAddress(addr)) => {
                let val = self.memory.get_byte(addr);
                self.compare_with_x_register(val);
            }

            (Instruction::CPY, OperationInput::UseImmediate(val)) => {
                self.compare_with_y_register(val);
            }
            (Instruction::CPY, OperationInput::UseAddress(addr)) => {
                let val = self.memory.get_byte(addr);
                self.compare_with_y_register(val);
            }

            (Instruction::DEC, OperationInput::UseAddress(addr)) => {
                CPU::decrement(
                    self.memory.get_byte_mut_ref(addr),
                    &mut self.registers.status,
                );
            }

            (Instruction::DEY, OperationInput::UseImplied) => {
                CPU::decrement(&mut self.registers.index_y, &mut self.registers.status);
            }

            (Instruction::DEX, OperationInput::UseImplied) => {
                CPU::decrement(&mut self.registers.index_x, &mut self.registers.status);
            }

            (Instruction::EOR, OperationInput::UseImmediate(val)) => {
                self.exclusive_or(val);
            }
            (Instruction::EOR, OperationInput::UseAddress(addr)) => {
                let val = self.memory.get_byte(addr);
                self.exclusive_or(val);
            }

            (Instruction::INC, OperationInput::UseAddress(addr)) => {
                CPU::increment(
                    self.memory.get_byte_mut_ref(addr),
                    &mut self.registers.status,
                );
            }
            (Instruction::INX, OperationInput::UseImplied) => {
                CPU::increment(&mut self.registers.index_x, &mut self.registers.status);
            }
            (Instruction::INY, OperationInput::UseImplied) => {
                CPU::increment(&mut self.registers.index_x, &mut self.registers.status);
            }

            (Instruction::JMP, OperationInput::UseAddress(addr)) => self.jump(addr),

            (Instruction::LDA, OperationInput::UseImmediate(val)) => {
                self.load_accumulator(val as i8);
            }
            (Instruction::LDA, OperationInput::UseAddress(addr)) => {
                let val = self.memory.get_byte(addr);
                self.load_accumulator(val as i8);
            }

            (Instruction::LDX, OperationInput::UseImmediate(val)) => {
                self.load_x_register(val);
            }
            (Instruction::LDX, OperationInput::UseAddress(addr)) => {
                let val = self.memory.get_byte(addr);
                self.load_x_register(val);
            }

            (Instruction::LDY, OperationInput::UseImmediate(val)) => {
                self.load_y_register(val);
            }
            (Instruction::LDY, OperationInput::UseAddress(addr)) => {
                let val = self.memory.get_byte(addr);
                self.load_y_register(val);
            }

            (Instruction::LSR, OperationInput::UseImplied) => {
                // Accumulator mode
                let mut val = self.registers.accumulator as u8;
                CPU::shift_right_with_flags(&mut val, &mut self.registers.status);
                self.registers.accumulator = val as i8;
            }
            (Instruction::LSR, OperationInput::UseAddress(addr)) => {
                CPU::shift_right_with_flags(
                    self.memory.get_byte_mut_ref(addr),
                    &mut self.registers.status,
                );
            }

            (Instruction::ORA, OperationInput::UseImmediate(val)) => {
                self.inclusive_or(val);
            }
            (Instruction::ORA, OperationInput::UseAddress(addr)) => {
                let val = self.memory.get_byte(addr);
                self.inclusive_or(val);
            }

            (Instruction::PHA, OperationInput::UseImplied) => {
                // Push accumulator
                let val = self.registers.accumulator as u8;
                self.push_on_stack(val);
            }
            (Instruction::PHP, OperationInput::UseImplied) => {
                // Push status
                let val = self.registers.status.bits();
                self.push_on_stack(val);
            }
            (Instruction::PLA, OperationInput::UseImplied) => {
                // Pull accumulator
                let val: u8 = self.pull_from_stack();
                self.registers.accumulator = val as i8;
            }
            (Instruction::PLP, OperationInput::UseImplied) => {
                // Pull status
                let val: u8 = self.pull_from_stack();
                // The `truncate` here won't do anything because we have a
                // constant for the single unused flags bit. This probably
                // corresponds to the behavior of the 6502...? FIXME: verify
                self.registers.status = Status::from_bits_truncate(val);
            }

            (Instruction::ROL, OperationInput::UseImplied) => {
                // Accumulator mode
                let mut val = self.registers.accumulator as u8;
                CPU::rotate_left_with_flags(&mut val, &mut self.registers.status);
                self.registers.accumulator = val as i8;
            }
            (Instruction::ROL, OperationInput::UseAddress(addr)) => {
                CPU::rotate_left_with_flags(
                    self.memory.get_byte_mut_ref(addr),
                    &mut self.registers.status,
                );
            }
            (Instruction::ROR, OperationInput::UseImplied) => {
                // Accumulator mode
                let mut val = self.registers.accumulator as u8;
                CPU::rotate_right_with_flags(&mut val, &mut self.registers.status);
                self.registers.accumulator = val as i8;
            }
            (Instruction::ROR, OperationInput::UseAddress(addr)) => {
                CPU::rotate_right_with_flags(
                    self.memory.get_byte_mut_ref(addr),
                    &mut self.registers.status,
                );
            }

            (Instruction::SBC, OperationInput::UseImmediate(val)) => {
                self.subtract_with_carry(val as i8);
            }
            (Instruction::SBC, OperationInput::UseAddress(addr)) => {
                let val = self.memory.get_byte(addr) as i8;
                self.subtract_with_carry(val);
            }

            (Instruction::SEC, OperationInput::UseImplied) => {
                self.registers.status.or(Status::PS_CARRY);
            }
            (Instruction::SED, OperationInput::UseImplied) => {
                self.registers.status.or(Status::PS_DECIMAL_MODE);
            }
            (Instruction::SEI, OperationInput::UseImplied) => {
                self.registers.status.or(Status::PS_DISABLE_INTERRUPTS);
            }

            (Instruction::STA, OperationInput::UseAddress(addr)) => {
                self.memory.set_byte(addr, self.registers.accumulator as u8);
            }
            (Instruction::STX, OperationInput::UseAddress(addr)) => {
                self.memory.set_byte(addr, self.registers.index_x as u8);
            }
            (Instruction::STY, OperationInput::UseAddress(addr)) => {
                self.memory.set_byte(addr, self.registers.index_y as u8);
            }

            (Instruction::TAX, OperationInput::UseImplied) => {
                let val = self.registers.accumulator;
                self.load_x_register(val as u8);
            }
            (Instruction::TAY, OperationInput::UseImplied) => {
                let val = self.registers.accumulator;
                self.load_y_register(val as u8);
            }
            (Instruction::TSX, OperationInput::UseImplied) => {
                let StackPointer(val) = self.registers.stack_pointer;
                self.load_x_register(val);
            }
            (Instruction::TXA, OperationInput::UseImplied) => {
                let val = self.registers.index_x;
                self.load_accumulator(val as i8);
            }
            (Instruction::TXS, OperationInput::UseImplied) => {
                // Note that this is the only 'transfer' instruction that does
                // NOT set the zero and negative flags. (Because the target
                // is the stack pointer)
                let val = self.registers.index_x;
                self.registers.stack_pointer = StackPointer(val as u8);
            }
            (Instruction::TYA, OperationInput::UseImplied) => {
                let val = self.registers.index_y;
                self.load_accumulator(val as i8);
            }

            (Instruction::NOP, OperationInput::UseImplied) => {
            }
            (_, _) => {
                println!(
                    "attempting to execute unimplemented or invalid \
                     instruction"
                );
            }
        };
    }

    pub fn run(&mut self) {
        while let Some(decoded_instr) = self.fetch_next_and_decode() {
            self.execute_instruction(decoded_instr);
        }
    }

    fn set_flags_from_i8(status: &mut Status, value: i8) {
        let is_zero = value == 0;
        let is_negative = value < 0;

        status.set_with_mask(
            Status::PS_ZERO | Status::PS_NEGATIVE,
            Status::new(StatusArgs {
                zero: is_zero,
                negative: is_negative,
                ..StatusArgs::none()
            }),
        );
    }

    fn set_flags_from_u8(status: &mut Status, value: u8) {
        let is_zero = value == 0;
        let is_negative = value > 127;

        status.set_with_mask(
            Status::PS_ZERO | Status::PS_NEGATIVE,
            Status::new(StatusArgs {
                zero: is_zero,
                negative: is_negative,
                ..StatusArgs::none()
            }),
        );
    }

    fn shift_left_with_flags(p_val: &mut u8, status: &mut Status) {
        let mask = 1 << 7;
        let is_bit_7_set = (*p_val & mask) == mask;
        let shifted = (*p_val & !(1 << 7)) << 1;
        *p_val = shifted;
        status.set_with_mask(
            Status::PS_CARRY,
            Status::new(StatusArgs {
                carry: is_bit_7_set,
                ..StatusArgs::none()
            }),
        );
        CPU::set_flags_from_i8(status, *p_val as i8);
    }

    fn shift_right_with_flags(p_val: &mut u8, status: &mut Status) {
        let mask = 1;
        let is_bit_0_set = (*p_val & mask) == mask;
        *p_val >>= 1;
        status.set_with_mask(
            Status::PS_CARRY,
            Status::new(StatusArgs {
                carry: is_bit_0_set,
                ..StatusArgs::none()
            }),
        );
        CPU::set_flags_from_i8(status, *p_val as i8);
    }

    fn rotate_left_with_flags(p_val: &mut u8, status: &mut Status) {
        let is_carry_set = status.contains(Status::PS_CARRY);
        let mask = 1 << 7;
        let is_bit_7_set = (*p_val & mask) == mask;
        let shifted = (*p_val & !(1 << 7)) << 1;
        *p_val = shifted + if is_carry_set { 1 } else { 0 };
        status.set_with_mask(
            Status::PS_CARRY,
            Status::new(StatusArgs {
                carry: is_bit_7_set,
                ..StatusArgs::none()
            }),
        );
        CPU::set_flags_from_i8(status, *p_val as i8);
    }

    fn rotate_right_with_flags(p_val: &mut u8, status: &mut Status) {
        let is_carry_set = status.contains(Status::PS_CARRY);
        let mask = 1;
        let is_bit_0_set = (*p_val & mask) == mask;
        let shifted = *p_val >> 1;
        *p_val = shifted + if is_carry_set { 1 << 7 } else { 0 };
        status.set_with_mask(
            Status::PS_CARRY,
            Status::new(StatusArgs {
                carry: is_bit_0_set,
                ..StatusArgs::none()
            }),
        );
        CPU::set_flags_from_i8(status, *p_val as i8);
    }

    fn set_u8_with_flags(mem: &mut u8, status: &mut Status, value: u8) {
        *mem = value;
        CPU::set_flags_from_u8(status, value);
    }

    fn set_i8_with_flags(mem: &mut i8, status: &mut Status, value: i8) {
        *mem = value;
        CPU::set_flags_from_i8(status, value);
    }

    fn load_x_register(&mut self, value: u8) {
        CPU::set_u8_with_flags(
            &mut self.registers.index_x,
            &mut self.registers.status,
            value,
        );
    }

    fn load_y_register(&mut self, value: u8) {
        CPU::set_u8_with_flags(
            &mut self.registers.index_y,
            &mut self.registers.status,
            value,
        );
    }

    fn load_accumulator(&mut self, value: i8) {
        CPU::set_i8_with_flags(
            &mut self.registers.accumulator,
            &mut self.registers.status,
            value,
        );
    }

    fn add_with_carry(&mut self, value: i8) {
        let a_before: i8 = self.registers.accumulator;
        let c_before: i8 = if self.registers.status.contains(Status::PS_CARRY) {
            1
        } else {
            0
        };
        let a_after: i8 = a_before.wrapping_add(c_before).wrapping_add(value);

        debug_assert_eq!(
            a_after as u8,
            a_before.wrapping_add(c_before).wrapping_add(value) as u8
        );

        let bcd1: i8 = if (a_after & 0x0f) as u8 > 0x09 {
            0x06
        } else {
            0x00
        };

        let bcd2: i8 = if (a_after.wrapping_add(bcd1) as u8 & 0xf0) as u8 > 0x90 {
            0x60
        } else {
            0x00
        };

        #[cfg(feature = "decimal_mode")]
            let result: i8 = if self.registers.status.contains(Status::PS_DECIMAL_MODE) {
            a_after.wrapping_add(bcd1).wrapping_add(bcd2)
        } else {
            a_after
        };

        #[cfg(not(feature = "decimal_mode"))]
            let result: i8 = a_after;

        let did_carry = (result as u8) < (a_before as u8) || (c_before == 1 && value == -1);

        let did_overflow = (a_before < 0 && value < 0 && a_after >= 0)
            || (a_before > 0 && value > 0 && a_after <= 0);

        let mask = Status::PS_CARRY | Status::PS_OVERFLOW;

        self.registers.status.set_with_mask(
            mask,
            Status::new(StatusArgs {
                carry: did_carry,
                overflow: did_overflow,
                ..StatusArgs::none()
            }),
        );

        self.load_accumulator(result);

    }

    fn and(&mut self, value: i8) {
        let a_after = self.registers.accumulator & value;
        self.load_accumulator(a_after);
    }

    fn subtract_with_carry(&mut self, value: i8) {
        // A - M - (1 - C)

        // nc -- 'not carry'
        let nc: i8 = if self.registers.status.contains(Status::PS_CARRY) {
            0
        } else {
            1
        };

        let a_before: i8 = self.registers.accumulator;

        let a_after = a_before.wrapping_sub(value).wrapping_sub(nc);

        // The overflow flag is set on two's-complement overflow.
        //
        // range of A              is  -128 to 127
        // range of - M - (1 - C)  is  -128 to 128
        //                             -(127 + 1) to -(-128 + 0)
        //
        let over =
            ((nc == 0 && value < 0) || (nc == 1 && value < -1)) && a_before >= 0 && a_after < 0;

        let under =
            (a_before < 0) && (0i8.wrapping_sub(value).wrapping_sub(nc) < 0) && a_after >= 0;

        let did_overflow = over || under;

        let mask = Status::PS_CARRY | Status::PS_OVERFLOW;

        let bcd1: i8 = if (a_before & 0x0f).wrapping_sub(nc) < (value & 0x0f) {
            0x06
        } else {
            0x00
        };

        let bcd2: i8 = if (a_after.wrapping_sub(bcd1) as u8 & 0xf0) as u8 > 0x90 {
            0x60
        } else {
            0x00
        };

        #[cfg(feature = "decimal_mode")]
            let result: i8 = if self.registers.status.contains(Status::PS_DECIMAL_MODE) {
            a_after.wrapping_sub(bcd1).wrapping_sub(bcd2)
        } else {
            a_after
        };

        #[cfg(not(feature = "decimal_mode"))]
            let result: i8 = a_after;

        // The carry flag is set on unsigned overflow.
        let did_carry = (result as u8) > (a_before as u8);

        self.registers.status.set_with_mask(
            mask,
            Status::new(StatusArgs {
                carry: did_carry,
                overflow: did_overflow,
                ..StatusArgs::none()
            }),
        );

        self.load_accumulator(result);
    }

    fn increment(val: &mut u8, flags: &mut Status) {
        let value_new = val.wrapping_add(1);
        *val = value_new;

        let is_negative = (value_new as i8) < 0;
        let is_zero = value_new == 0;

        flags.set_with_mask(
            Status::PS_NEGATIVE | Status::PS_ZERO,
            Status::new(StatusArgs {
                negative: is_negative,
                zero: is_zero,
                ..StatusArgs::none()
            }),
        );
    }

    fn decrement(val: &mut u8, flags: &mut Status) {
        let value_new = val.wrapping_sub(1);
        *val = value_new;

        let is_negative = (value_new as i8) < 0;
        let is_zero = value_new == 0;

        flags.set_with_mask(
            Status::PS_NEGATIVE | Status::PS_ZERO,
            Status::new(StatusArgs {
                negative: is_negative,
                zero: is_zero,
                ..StatusArgs::none()
            }),
        );
    }

    fn jump(&mut self, addr: u16) {
        self.registers.program_counter = addr;
    }

    fn branch_if_carry_clear(&mut self, addr: u16) {
        if !self.registers.status.contains(Status::PS_CARRY) {
            self.registers.program_counter = addr;
        }
    }

    fn branch_if_carry_set(&mut self, addr: u16) {
        if self.registers.status.contains(Status::PS_CARRY) {
            self.registers.program_counter = addr;
        }
    }

    fn branch_if_equal(&mut self, addr: u16) {
        if self.registers.status.contains(Status::PS_ZERO) {
            self.registers.program_counter = addr;
        }
    }

    fn branch_if_minus(&mut self, addr: u16) {
        if self.registers.status.contains(Status::PS_NEGATIVE) {
            self.registers.program_counter = addr;
        }
    }

    fn branch_if_positive(&mut self, addr: u16) {
        if !self.registers.status.contains(Status::PS_NEGATIVE) {
            self.registers.program_counter = addr;
        }
    }

    fn branch_if_overflow_clear(&mut self, addr: u16) {
        if !self.registers.status.contains(Status::PS_OVERFLOW) {
            self.registers.program_counter = addr;
        }
    }

    fn branch_if_overflow_set(&mut self, addr: u16) {
        if self.registers.status.contains(Status::PS_OVERFLOW) {
            self.registers.program_counter = addr;
        }
    }

    // From http://www.6502.org/tutorials/compare_beyond.html:
    //   If the Z flag is 0, then A <> NUM and BNE will branch
    //   If the Z flag is 1, then A = NUM and BEQ will branch
    //   If the C flag is 0, then A (unsigned) < NUM (unsigned) and BCC will branch
    //   If the C flag is 1, then A (unsigned) >= NUM (unsigned) and BCS will branch
    //   ...
    //   The N flag contains most significant bit of the subtraction result.
    fn compare(&mut self, r: i8, val: u8) {
        if r as u8 >= val as u8 {
            self.registers.status.insert(Status::PS_CARRY);
        } else {
            self.registers.status.remove(Status::PS_CARRY);
        }

        if r as i8 == val as i8 {
            self.registers.status.insert(Status::PS_ZERO);
        } else {
            self.registers.status.remove(Status::PS_ZERO);
        }

        let diff: i8 = r.wrapping_sub(val as i8);
        if diff < 0 {
            self.registers.status.insert(Status::PS_NEGATIVE);
        } else {
            self.registers.status.remove(Status::PS_NEGATIVE);
        }
    }

    fn compare_with_a_register(&mut self, val: u8) {
        let a = self.registers.accumulator;
        self.compare(a, val);
    }

    fn compare_with_x_register(&mut self, val: u8) {

        let x = self.registers.index_x;
        self.compare(x as i8, val);
    }

    fn compare_with_y_register(&mut self, val: u8) {
        let y = self.registers.index_y;
        self.compare(y as i8, val);
    }

    fn exclusive_or(&mut self, val: u8) {
        let a_after = self.registers.accumulator ^ (val as i8);
        self.load_accumulator(a_after);
    }

    fn inclusive_or(&mut self, val: u8) {
        let a_after = self.registers.accumulator | (val as i8);
        self.load_accumulator(a_after);
    }

    fn push_on_stack(&mut self, val: u8) {
        let addr = self.registers.stack_pointer.to_u16();
        self.memory.set_byte(addr, val);
        self.registers.stack_pointer.decrement();
    }

    fn pull_from_stack(&mut self) -> u8 {
        let addr = self.registers.stack_pointer.to_u16();
        let out = self.memory.get_byte(addr);
        self.registers.stack_pointer.increment();
        out
    }
}

impl core::fmt::Debug for CPU {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(
            f,
            "CPU Dump:\n\nAccumulator: {}",
            self.registers.accumulator
        )
    }
}
