// TODO:
//  - Configurable quirks
//  - Super-Chip support
//  - XO-Chip support
//  - random number generation that works with wasm

use retroforge_core::{
    DisplayInfo, FrameBufferFormat, InputAction, KeyCode, Machine, MachineError, MachineInfo,
    MachineStepAction, OutputAction,
};
use std::collections::{HashSet, VecDeque};
use std::fmt;

static STACK_START_ADDR: usize = 0x0000;
static STACK_SIZE: usize = 32; // Space for 16 2-byte addresses

static FONT_START_ADDR: usize = 0x0050;
static FONT_MEM_SIZE: usize = 80;

static SCREEN_WIDTH: u8 = 64;
static SCREEN_HEIGHT: u8 = 32;
static SCREEN_BUFFER_SIZE: usize = (SCREEN_WIDTH as usize) * (SCREEN_HEIGHT as usize);

static PROGRAM_START_ADDR: usize = 0x0200;
static FLAG_REGISTER_ADDR: u8 = 0xF;

// static INSTRUCTIONS_PER_FRAME: u16 = 12;
static INSTRUCTIONS_PER_FRAME: u16 = 120;

pub struct Instruction {
    pub opcode: u16,
    pub group: u8,
    pub x: u8,
    pub y: u8,
    pub nnn: u16,
    pub nn: u8,
    pub n: u8,
}

impl Instruction {
    pub fn new(opcode: u16) -> Self {
        Self {
            opcode,
            group: ((opcode & 0xF000) >> 12) as u8,
            x: ((opcode & 0x0F00) >> 8) as u8,
            y: ((opcode & 0x00F0) >> 4) as u8,
            nnn: opcode & 0x0FFF,
            nn: (opcode & 0x00FF) as u8,
            n: (opcode & 0x000F) as u8,
        }
    }
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:04X}", self.opcode)
    }
}

impl fmt::Debug for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Instruction {{ opcode: {:04X}, group: {:}, x: {:}, y: {:}, n: {:}, nn: {:}, nnn: {:} }}",
            self.opcode, self.group, self.x, self.y, self.n, self.nn, self.nnn
        )
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct KeypadKey(u8);

impl TryFrom<KeyCode> for KeypadKey {
    type Error = ();

    fn try_from(value: KeyCode) -> Result<Self, Self::Error> {
        match value {
            KeyCode::Num1 => Ok(KeypadKey(0x1)),
            KeyCode::Num2 => Ok(KeypadKey(0x2)),
            KeyCode::Num3 => Ok(KeypadKey(0x3)),
            KeyCode::Num4 => Ok(KeypadKey(0xC)),
            KeyCode::Q => Ok(KeypadKey(0x4)),
            KeyCode::W => Ok(KeypadKey(0x5)),
            KeyCode::E => Ok(KeypadKey(0x6)),
            KeyCode::R => Ok(KeypadKey(0xD)),
            KeyCode::A => Ok(KeypadKey(0x7)),
            KeyCode::S => Ok(KeypadKey(0x8)),
            KeyCode::D => Ok(KeypadKey(0x9)),
            KeyCode::F => Ok(KeypadKey(0xE)),
            KeyCode::Z => Ok(KeypadKey(0xA)),
            KeyCode::X => Ok(KeypadKey(0x0)),
            KeyCode::C => Ok(KeypadKey(0xB)),
            KeyCode::V => Ok(KeypadKey(0xF)),
        }
    }
}

#[derive(Debug)]
pub struct Chip8 {
    // Processor memory and registers
    memory: [u8; 4096],
    registers: [u8; 17],
    p_c: u16,
    s_p: u8,
    i: u16,

    // timers and frame counters
    delay_timer: u8,
    sound_timer: u8,
    interframe_cycles: u16,

    // input and output
    framebuffer: [u8; SCREEN_BUFFER_SIZE],
    output_actions: VecDeque<OutputAction>,
    is_beeping: bool,
    input_state: HashSet<KeypadKey>,
}

impl Default for Chip8 {
    fn default() -> Self {
        Self::new()
    }
}

impl Chip8 {
    pub fn new() -> Self {
        let mut proc = Self {
            memory: [0; 4096],
            registers: [0; 17],
            p_c: PROGRAM_START_ADDR as u16,
            s_p: 0,
            i: 0,
            delay_timer: 0,
            sound_timer: 0,
            interframe_cycles: 0,
            framebuffer: [0; SCREEN_BUFFER_SIZE],
            output_actions: VecDeque::new(),
            is_beeping: false,
            input_state: HashSet::new(),
        };

        proc.load_font_data();

        proc
    }

    pub fn with_rom(rom: &[u8]) -> Result<Self, MachineError> {
        let mut machine = Self::new();
        machine.load_rom(rom)?;
        Ok(machine)
    }

    fn load_font_data(&mut self) {
        let font_data = include_bytes!("../assets/font.bin");
        self.memory[FONT_START_ADDR..FONT_START_ADDR + FONT_MEM_SIZE].copy_from_slice(font_data);
    }

    fn fetch_opcode(&mut self) -> Result<u16, MachineError> {
        let opcode = self.read_word_at(self.p_c)?;
        self.p_c = self.p_c.saturating_add(2);
        Ok(opcode)
    }

    fn get_register(&mut self, reg: u8) -> Result<u8, MachineError> {
        if reg > 0xF {
            return Err(MachineError::RegisterIndexOutOfBounds(reg));
        }

        Ok(self.registers[reg as usize])
    }

    fn set_register(&mut self, reg: u8, value: u8) -> Result<(), MachineError> {
        if reg > 0xF {
            return Err(MachineError::RegisterIndexOutOfBounds(reg));
        }

        self.registers[reg as usize] = value;
        Ok(())
    }

    fn get_flag_register(&mut self) -> u8 {
        self.registers[FLAG_REGISTER_ADDR as usize]
    }

    fn set_flag_register(&mut self, value: u8) {
        self.registers[FLAG_REGISTER_ADDR as usize] = value;
    }

    fn push_addr_to_stack(&mut self, value: u16) -> Result<(), MachineError> {
        self.memory[STACK_START_ADDR + self.s_p as usize] = ((value & 0xFF00) >> 8) as u8;
        self.memory[STACK_START_ADDR + self.s_p as usize + 1] = (value & 0x00FF) as u8;
        self.s_p = self.s_p.checked_add(2).ok_or(MachineError::StackOverflow)?;

        Ok(())
    }

    fn pop_addr_from_stack(&mut self) -> Result<u16, MachineError> {
        self.s_p = self
            .s_p
            .checked_sub(2)
            .ok_or(MachineError::StackUnderflow)?;
        let hi = self.memory[STACK_START_ADDR + self.s_p as usize];
        let lo = self.memory[STACK_START_ADDR + self.s_p as usize + 1];
        let value = ((hi as u16) << 8) | lo as u16;
        Ok(value)
    }

    fn execute(&mut self, instruction: Instruction) -> Result<MachineStepAction, MachineError> {
        match instruction.group {
            // 0x0 -> General Instructions
            0x0 => match instruction.nn {
                // 0x00E0 -> Clear Screen
                0xE0 => {
                    self.framebuffer.fill(0);
                    Ok(MachineStepAction::Continue)
                }

                // 0x00EE -> Return from subroutine
                0xEE => {
                    self.p_c = self.pop_addr_from_stack()?;
                    Ok(MachineStepAction::Continue)
                }

                // 0x0NNN -> Execute machine language routine. Skip for now
                _ => Ok(MachineStepAction::Continue),
            },

            // 0x1NNN -> Jump
            0x1 => {
                self.p_c = instruction.nnn;
                Ok(MachineStepAction::Continue)
            }

            // 0x2NNN -> Call
            0x2 => {
                self.push_addr_to_stack(self.p_c)?;
                self.p_c = instruction.nnn;
                Ok(MachineStepAction::Continue)
            }

            // 0x3XNN -> Skip next instruction if VX == NN
            0x3 => {
                let x = self.get_register(instruction.x)?;
                if x == instruction.nn {
                    self.p_c = self.p_c.saturating_add(2)
                }
                Ok(MachineStepAction::Continue)
            }

            // 0x4XNN -> Skip next instruction if VX != NN
            0x4 => {
                let x = self.get_register(instruction.x)?;
                if x != instruction.nn {
                    self.p_c = self.p_c.saturating_add(2)
                }
                Ok(MachineStepAction::Continue)
            }

            // 0x5XY0 -> Skip next instruction if VX == VY
            0x5 => {
                let x = self.get_register(instruction.x)?;
                let y = self.get_register(instruction.y)?;
                if x == y {
                    self.p_c = self.p_c.saturating_add(2)
                }
                Ok(MachineStepAction::Continue)
            }

            // 0x6XNN: Set Register X to NN
            0x6 => {
                self.set_register(instruction.x, instruction.nn)?;
                Ok(MachineStepAction::Continue)
            }

            // 0x7XNN: Add NN to Register X
            0x7 => {
                let x = self.get_register(instruction.x)?;
                self.set_register(instruction.x, x.wrapping_add(instruction.nn))?;
                Ok(MachineStepAction::Continue)
            }

            // 0x8 -> Logical and Arithmetic Operations
            0x8 => match instruction.n {
                // 0x8XY0 -> Set VX to the value of VY
                0x0 => {
                    let y = self.get_register(instruction.y)?;
                    self.set_register(instruction.x, y)?;
                    Ok(MachineStepAction::Continue)
                }

                // 0x8XY1 -> Set VX to VX OR VY
                0x1 => {
                    let x = self.get_register(instruction.x)?;
                    let y = self.get_register(instruction.y)?;
                    self.set_register(instruction.x, x | y)?;
                    Ok(MachineStepAction::Continue)
                }

                // 0x8XY2 -> Set VX to VX AND VY
                0x2 => {
                    let x = self.get_register(instruction.x)?;
                    let y = self.get_register(instruction.y)?;
                    self.set_register(instruction.x, x & y)?;
                    Ok(MachineStepAction::Continue)
                }

                // 0x8XY3 -> Set VX to VX XOR VY
                0x3 => {
                    let x = self.get_register(instruction.x)?;
                    let y = self.get_register(instruction.y)?;
                    self.set_register(instruction.x, x ^ y)?;
                    Ok(MachineStepAction::Continue)
                }

                // 0x8XY4 -> Set VX to VX + VY, set VF to 1 when there's a carry, and reset it to 0 when there isn't
                0x4 => {
                    let x = self.get_register(instruction.x)?;
                    let y = self.get_register(instruction.y)?;

                    let (result, carry) = x.overflowing_add(y);
                    self.set_register(instruction.x, result)?;
                    self.set_flag_register(carry as u8);
                    Ok(MachineStepAction::Continue)
                }

                // 0x8XY5 -> Set VX to VX - VY, set VF to 0 when there's a borrow, and reset it to 1 when there isn't
                0x5 => {
                    let x = self.get_register(instruction.x)?;
                    let y = self.get_register(instruction.y)?;

                    let (result, carry) = x.overflowing_sub(y);
                    self.set_register(instruction.x, result)?;
                    self.set_flag_register(!carry as u8);
                    Ok(MachineStepAction::Continue)
                }

                // 0x8XY6 -> Set VX to VY >> 1, store the shifted bit in VF
                0x6 => {
                    // let y = self.get_register(instruction.y)?;
                    let y = self.get_register(instruction.x)?;

                    self.set_register(instruction.x, y >> 1)?;
                    self.set_flag_register(y & 0x1);
                    Ok(MachineStepAction::Continue)
                }

                // 0x8XY7 -> Set VX to VY - VX, set VF to 0 when there's a borrow, and reset it to 1 when there isn't
                0x7 => {
                    let x = self.get_register(instruction.x)?;
                    let y = self.get_register(instruction.y)?;

                    let (result, carry) = y.overflowing_sub(x);
                    self.set_register(instruction.x, result)?;
                    self.set_flag_register(!carry as u8);
                    Ok(MachineStepAction::Continue)
                }

                // 0x8XYE -> Set VX to VY << 1, store the shifted bit in VF
                0xE => {
                    // let y = self.get_register(instruction.y)?;
                    let y = self.get_register(instruction.x)?;

                    self.set_flag_register((y & 0x80) >> 7);
                    self.set_register(instruction.x, y << 1)?;
                    Ok(MachineStepAction::Continue)
                }

                _ => Err(MachineError::UnknownInstruction(instruction.to_string())),
            },

            // 0x9XY0 -> Skip next instruction if VX != VY
            0x9 => {
                let x = self.get_register(instruction.x)?;
                let y = self.get_register(instruction.y)?;
                if x != y {
                    self.p_c = self.p_c.saturating_add(2)
                }
                Ok(MachineStepAction::Continue)
            }

            // 0xANNN: Set I to the address NNN
            0xA => {
                self.i = instruction.nnn;
                Ok(MachineStepAction::Continue)
            }

            // 0xBNNN: Jump to location NNN + V0
            0xB => {
                let offset = self.get_register(0x0)?;
                self.p_c = instruction.nnn.saturating_add(u16::from(offset));
                Ok(MachineStepAction::Continue)
            }

            // Random
            0xC => {
                let r = 0;
                self.set_register(instruction.x, r & instruction.nn)?;
                Ok(MachineStepAction::Continue)
            }

            // 0xDXYN: Draw a sprite at coordinate (VX, VY) with N bytes of sprite data starting at the address stored in I
            0xD => {
                let x = self.get_register(instruction.x)?;
                let y = self.get_register(instruction.y)?;
                let height = instruction.n;

                // & to wrap within screen bounds
                self.draw(x & (SCREEN_WIDTH - 1), y & (SCREEN_HEIGHT - 1), height)?;

                // Draw operations cause the machine to wait until the next frame
                // to sync with the display
                Ok(MachineStepAction::WaitForFrame)
            }

            // Skip If Key
            0xE => match instruction.nn {
                // 0xEX9E -> Skip next instruction if key with the value of VX is pressed
                0x9E => {
                    let key = self.get_register(instruction.x)?;
                    if self.input_state.contains(&KeypadKey(key)) {
                        self.p_c = self.p_c.saturating_add(2);
                    }

                    Ok(MachineStepAction::Continue)
                }

                // 0xEXA1 -> Skip next instruction if key with the value of VX is not pressed
                0xA1 => {
                    let key = self.get_register(instruction.x)?;
                    if !self.input_state.contains(&KeypadKey(key)) {
                        self.p_c = self.p_c.saturating_add(2);
                    }

                    Ok(MachineStepAction::Continue)
                }

                _ => Err(MachineError::UnknownInstruction(instruction.to_string())),
            },

            // Miscellaneous Instructions
            0xF => match instruction.nn {
                // 0xFX07 -> Set VX to the value of the delay timer
                0x07 => {
                    self.set_register(instruction.x, self.delay_timer)?;
                    Ok(MachineStepAction::Continue)
                }

                // 0xFX0A -> Get keyboard input and store it in VX
                0x0A => {
                    // Take the first key.
                    // TODO: Prioritise certain keys? Queue key presses?
                    if let Some(key) = self.input_state.iter().next() {
                        self.set_register(instruction.x, key.0)?;
                        Ok(MachineStepAction::Continue)
                    } else {
                        // No keys pressed. Wait until next frame
                        Ok(MachineStepAction::WaitForFrame)
                    }
                }

                // 0xFX15 -> Set the delay timer to the value in VX
                0x15 => {
                    self.delay_timer = self.get_register(instruction.x)?;
                    Ok(MachineStepAction::Continue)
                }

                // 0xFX18 -> Set the sound timer to the value in VX
                0x18 => {
                    self.sound_timer = self.get_register(instruction.x)?;

                    // Start the sound if the timer becomes non-zero and it is not already playing
                    if self.sound_timer > 0 && !self.is_beeping {
                        self.is_beeping = true;
                        self.output_actions.push_back(OutputAction::StartBeep);
                    }

                    Ok(MachineStepAction::Continue)
                }

                // 0xFX1E -> Add VX to I, set VF to 1 when I goes outside the normal address range
                0x1E => {
                    self.i = self
                        .i
                        .saturating_add(self.get_register(instruction.x)?.into());

                    if self.i > 0xFFF {
                        self.set_flag_register(0x1);
                    } else {
                        self.set_flag_register(0x0);
                    }

                    Ok(MachineStepAction::Continue)
                }

                // 0xFX29 -> Set I to the location of the sprite for the character in VX.
                0x29 => {
                    let char_code = self.get_register(instruction.x)? & 0x0F;
                    self.i = FONT_START_ADDR as u16 + 0x5 * u16::from(char_code);
                    Ok(MachineStepAction::Continue)
                }

                // 0xFX33 -> Binary Coded Decimal. Store the three digits of VX in memory starting at location I.
                0x33 => {
                    let value = self.get_register(instruction.x)?;
                    let hundreds = value / 100;
                    let tens = (value % 100) / 10;
                    let ones = value % 10;
                    self.write_byte_at(self.i, hundreds)?;
                    self.write_byte_at(self.i + 1, tens)?;
                    self.write_byte_at(self.i + 2, ones)?;

                    Ok(MachineStepAction::Continue)
                }

                // 0xFX55 -> Store registers V0 through VX in memory starting at location I
                0x55 => {
                    for reg in 0..=instruction.x {
                        let value = self.get_register(reg)?;
                        self.write_byte_at(self.i + u16::from(reg), value)?;
                    }

                    Ok(MachineStepAction::Continue)
                }

                // 0xFX65 -> Load registers V0 through VX from memory starting at location I
                0x65 => {
                    for reg in 0..=instruction.x {
                        let value = self.read_byte_at(self.i + u16::from(reg))?;
                        self.set_register(reg, value)?;
                    }

                    Ok(MachineStepAction::Continue)
                }

                _ => Err(MachineError::UnknownInstruction(instruction.to_string())),
            },

            _ => Err(MachineError::UnknownInstruction(instruction.to_string())),
        }
    }

    fn draw(&mut self, sprite_x: u8, sprite_y: u8, sprite_height: u8) -> Result<(), MachineError> {
        // TODO: Optimize this
        // Reset the flag register
        self.set_flag_register(0);

        // Loop through pixels and blit
        for row in 0..sprite_height {
            let pixel_y = sprite_y + row;
            if pixel_y >= SCREEN_HEIGHT {
                break;
            }

            let sprite_byte = self.read_byte_at(self.i + u16::from(row))?;

            for col in 0..8 {
                let pixel_x = sprite_x + col;
                if pixel_x >= SCREEN_WIDTH {
                    break;
                }

                let sprite_bit = (sprite_byte >> (7 - col)) & 0x1;
                let pixel_index = (pixel_y as usize) * (SCREEN_WIDTH as usize) + (pixel_x as usize);
                let screen_pixel = self.framebuffer[pixel_index];

                // Set the flag register if both screen pixel and sprite pixel are set
                if screen_pixel > 0 && sprite_bit > 0 {
                    self.set_flag_register(0x1);
                }

                self.framebuffer[pixel_index] = screen_pixel ^ sprite_bit;
            }
        }

        Ok(())
    }

    fn read_byte_at(&self, addr: u16) -> Result<u8, MachineError> {
        if addr > 0xFFF {
            return Err(MachineError::MemoryOutOfBounds(addr));
        }

        Ok(self.memory[addr as usize])
    }

    fn read_word_at(&self, addr: u16) -> Result<u16, MachineError> {
        let hi = self.read_byte_at(addr)?;
        let lo = self.read_byte_at(addr + 1)?;
        Ok(((hi as u16) << 8) | lo as u16)
    }

    fn write_byte_at(&mut self, addr: u16, value: u8) -> Result<(), MachineError> {
        if addr > 0xFFF {
            return Err(MachineError::MemoryOutOfBounds(addr));
        }

        self.memory[addr as usize] = value;
        Ok(())
    }
}

impl Machine for Chip8 {
    fn get_info(&self) -> MachineInfo {
        MachineInfo {
            name: "Chip8".to_owned(),
            display: DisplayInfo {
                width: u32::from(SCREEN_WIDTH),
                height: u32::from(SCREEN_HEIGHT),
                format: FrameBufferFormat::Monochrome,
            },
        }
    }

    fn load_rom(&mut self, rom: &[u8]) -> Result<(), MachineError> {
        self.memory[PROGRAM_START_ADDR..PROGRAM_START_ADDR + rom.len()].copy_from_slice(&rom);
        Ok(())
    }

    fn step(&mut self) -> Result<MachineStepAction, MachineError> {
        // fetch
        let opcode = self.fetch_opcode()?;

        // decode
        let instruction = Instruction::new(opcode);

        // execute
        let state = self.execute(instruction)?;
        if matches!(state, MachineStepAction::Halt) {
            return Ok(state);
        }

        self.interframe_cycles += 1;
        if self.interframe_cycles == INSTRUCTIONS_PER_FRAME {
            self.interframe_cycles = 0;

            // Decrement timers
            self.delay_timer = self.delay_timer.saturating_sub(1);
            self.sound_timer = self.sound_timer.saturating_sub(1);

            // Stop beep sound if sounds timer becomes zero
            if self.sound_timer == 0 && self.is_beeping {
                self.is_beeping = false;
                self.output_actions.push_back(OutputAction::StopBeep);
            }

            // Wait until the next frame before continuing
            return Ok(MachineStepAction::WaitForFrame);
        }

        Ok(state)
    }

    fn get_frame_buffer(&self) -> &[u8] {
        &self.framebuffer
    }

    fn push_input_actions(&mut self, keys_down: &[InputAction]) {
        // todo!()
    }

    fn get_output_actions(&mut self) -> Option<Vec<OutputAction>> {
        if self.output_actions.is_empty() {
            return None;
        }

        Some(self.output_actions.drain(..).collect())
    }
}
