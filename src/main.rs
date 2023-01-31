
extern crate emulator6502;

#[cfg(not(test))]
use emulator6502::cpu;

#[cfg(not(test))]
fn main() {
    let mut cpu = cpu::CPU::new();

    let zero_page_data = [
        // ZeroPage data start
        0x00, 0x02, // ADC ZeroPage target
        0x00, 0x04, // ADC ZeroPageX target
        0x00, 0x00, 0x00, 0x00, 0x10, // ADC IndexedIndirectX address
        0x80, // ADC IndexedIndirectX address
        0x00, 0x00, 0x00, 0x00, 0x00, 0x08, // ADC IndirectIndexedY address
        0x80, // ADC IndirectIndexedY address
    ];

    let program = [
        // Code start
        0xA9, // LDA Immediate
        0x42,
    ];

    let data = [
        0x00, 0x09, // ADC Absolute target
        0x00, 0x00, 0x40, // ADC AbsoluteY target
        0x00, 0x00, 0x00, 0x11, // ADC AbsoluteX target
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x12, // ADC IndexedIndirectX target
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x06, // ADC IndirectIndexedY target
    ];

    cpu.memory.set_bytes(0x0000, &zero_page_data);
    cpu.memory.set_bytes(0x4000, &program);
    cpu.memory.set_bytes(0x8000, &data);

    cpu.registers.program_counter = 0x4000;

    cpu.run();

    println!("{:?}", cpu);
}