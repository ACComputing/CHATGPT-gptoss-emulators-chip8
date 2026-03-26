import tkinter as tk
from tkinter import filedialog, messagebox
import random

# ------------------------------------------------------------
# 1. Constants & key mapping
# ------------------------------------------------------------

# Chip‑8 keypad layout mapped to common keyboard keys
KEY_MAP = {
    '1': 0x1, '2': 0x2, '3': 0x3, '4': 0xC,
    'q': 0x4, 'w': 0x5, 'e': 0x6, 'r': 0xD,
    'a': 0x7, 's': 0x8, 'd': 0x9, 'f': 0xE,
    'z': 0xA, 'x': 0x0, 'c': 0xB, 'v': 0xF,
}

# Standard Chip‑8 fontset (each character is 5 bytes)
FONTSET = [
    0xF0, 0x90, 0x90, 0x90, 0xF0,   # 0
    0x20, 0x60, 0x20, 0x20, 0x70,   # 1
    0xF0, 0x10, 0xF0, 0x80, 0xF0,   # 2
    0xF0, 0x10, 0xF0, 0x10, 0xF0,   # 3
    0x90, 0x90, 0xF0, 0x10, 0x10,   # 4
    0xF0, 0x80, 0xF0, 0x10, 0xF0,   # 5
    0xF0, 0x80, 0xF0, 0x90, 0xF0,   # 6
    0xF0, 0x10, 0x20, 0x40, 0x40,   # 7
    0xF0, 0x90, 0xF0, 0x90, 0xF0,   # 8
    0xF0, 0x90, 0xF0, 0x10, 0xF0,   # 9
    0xF0, 0x90, 0xF0, 0x90, 0x90,   # A
    0xE0, 0x90, 0xE0, 0x90, 0xE0,   # B
    0xF0, 0x80, 0x80, 0x80, 0xF0,   # C
    0xE0, 0x90, 0x90, 0x90, 0xE0,   # D
    0xF0, 0x80, 0xF0, 0x80, 0xF0,   # E
    0xF0, 0x80, 0xF0, 0x80, 0x80    # F
]

# ------------------------------------------------------------
# 2. Core Chip‑8 emulation logic
# ------------------------------------------------------------

class Chip8:
    def __init__(self):
        self.reset()

    # Reset or initialize the machine
    def reset(self):
        self.memory = [0] * 4096

        # Load fontset into memory starting at 0x00
        for i, byte in enumerate(FONTSET):
            self.memory[i] = byte

        # General‑purpose registers V0–VF
        self.V = [0] * 16
        # Index register and program counter
        self.I = 0
        self.pc = 0x200  # programs start at 0x200

        # Stack and stack pointer
        self.stack = []

        # Timers (in cycles, decremented at 60 Hz)
        self.delay_timer = 0
        self.sound_timer = 0

        # Keypad state (16 keys)
        self.keys = [0] * 16

        # Display buffer: 64×32 pixels
        self.display = [[0] * 64 for _ in range(32)]

        # ROM/halt state
        self.rom_loaded = False
        self.halted = False

    # Load a ROM into memory
    def load_rom(self, path):
        with open(path, 'rb') as f:
            rom = f.read()
        self.halted = False
        self.rom_loaded = True
        self.pc = 0x200
        for i, byte in enumerate(rom):
            self.memory[0x200 + i] = byte

    # Fetch the next opcode (2 bytes)
    def fetch_opcode(self):
        high = self.memory[self.pc]
        low = self.memory[self.pc + 1]
        return (high << 8) | low

    # Execute a single opcode
    def execute(self, opcode):
        nibbles = (opcode & 0xF000) >> 12
        x      = (opcode & 0x0F00) >> 8
        y      = (opcode & 0x00F0) >> 4
        n      = opcode & 0x000F
        nn     = opcode & 0x00FF
        nnn    = opcode & 0x0FFF

        advance_pc = True   # default: PC += 2

        if opcode == 0x00E0:                         # CLS
            self.display = [[0] * 64 for _ in range(32)]

        elif opcode == 0x00EE:                       # RET
            self.pc = self.stack.pop()

        elif nibbles == 0x1:                         # JP addr
            self.pc = nnn
            advance_pc = False

        elif nibbles == 0x2:                         # CALL addr
            self.stack.append(self.pc)
            self.pc = nnn
            advance_pc = False

        elif nibbles == 0x3:                         # SE Vx, byte
            if self.V[x] == nn:
                self.pc += 2

        elif nibbles == 0x4:                         # SNE Vx, byte
            if self.V[x] != nn:
                self.pc += 2

        elif nibbles == 0x5 and n == 0x0:            # SE Vx, Vy
            if self.V[x] == self.V[y]:
                self.pc += 2

        elif nibbles == 0x6:                         # LD Vx, byte
            self.V[x] = nn

        elif nibbles == 0x7:                         # ADD Vx, byte
            self.V[x] = (self.V[x] + nn) & 0xFF

        elif nibbles == 0x8:
            if   n == 0x0: self.V[x] = self.V[y]
            elif n == 0x1: self.V[x] |= self.V[y]
            elif n == 0x2: self.V[x] &= self.V[y]
            elif n == 0x3: self.V[x] ^= self.V[y]
            elif n == 0x4:
                total = self.V[x] + self.V[y]
                self.V[0xF] = 1 if total > 0xFF else 0
                self.V[x] = total & 0xFF
            elif n == 0x5:
                self.V[0xF] = 1 if self.V[x] > self.V[y] else 0
                self.V[x] = (self.V[x] - self.V[y]) & 0xFF
            elif n == 0x6:
                self.V[0xF] = self.V[y] & 0x1
                self.V[x]   = (self.V[y] >> 1) & 0xFF
            elif n == 0x7:
                self.V[0xF] = 1 if self.V[y] > self.V[x] else 0
                self.V[x] = (self.V[y] - self.V[x]) & 0xFF
            elif n == 0xE:
                self.V[0xF] = (self.V[y] >> 7) & 0x1
                self.V[x]   = (self.V[y] << 1) & 0xFF

        elif nibbles == 0x9 and n == 0x0:            # SNE Vx, Vy
            if self.V[x] != self.V[y]:
                self.pc += 2

        elif nibbles == 0xA:                         # LD I, addr
            self.I = nnn

        elif nibbles == 0xB:                         # JP V0, addr
            self.pc = nnn + self.V[0]
            advance_pc = False

        elif nibbles == 0xC:                         # RND Vx, byte
            self.V[x] = random.randint(0, 255) & nn

        elif nibbles == 0xD:                         # DRW Vx, Vy, nibble
            self.draw_sprite(self.V[x], self.V[y], n)

        elif nibbles == 0xE:
            if   nn == 0x9E:                        # SKP Vx
                if self.keys[self.V[x]]:
                    self.pc += 2
            elif nn == 0xA1:                        # SKNP Vx
                if not self.keys[self.V[x]]:
                    self.pc += 2

        elif nibbles == 0xF:
            if   nn == 0x07:                        # LD Vx, DT
                self.V[x] = self.delay_timer
            elif nn == 0x0A:                        # LD Vx, K
                pressed = False
                for k in range(16):
                    if self.keys[k]:
                        self.V[x] = k
                        pressed = True
                        break
                if not pressed:
                    # repeat this instruction until a key is pressed
                    return
            elif nn == 0x15:                        # LD DT, Vx
                self.delay_timer = self.V[x]
            elif nn == 0x18:                        # LD ST, Vx
                self.sound_timer = self.V[x]
            elif nn == 0x1E:                        # ADD I, Vx
                self.I = (self.I + self.V[x]) & 0xFFFF
            elif nn == 0x29:                        # LD F, Vx (sprite location)
                self.I = self.V[x] * 5
            elif nn == 0x33:                        # LD B, Vx (BCD)
                val = self.V[x]
                self.memory[self.I]     = (val // 100) % 10
                self.memory[self.I+1]   = (val // 10) % 10
                self.memory[self.I+2]   = val % 10
            elif nn == 0x55:                        # LD [I], Vx
                for i in range(x+1):
                    self.memory[self.I+i] = self.V[i]
            elif nn == 0x65:                        # LD Vx, [I]
                for i in range(x+1):
                    self.V[i] = self.memory[self.I+i]

        else:
            # Stop execution on invalid opcodes to avoid infinite terminal spam.
            # (Common case: running without a ROM leaves memory at 0x200 as 0x0000.)
            if not self.halted:
                print(f"Unknown opcode: {opcode:04X}")
            self.halted = True

        if advance_pc:
            self.pc += 2

    # Draw a sprite at (x, y) with height n
    def draw_sprite(self, x_coord, y_coord, height):
        self.V[0xF] = 0
        for row in range(height):
            sprite_byte = self.memory[self.I + row]
            for col in range(8):
                pixel = (sprite_byte >> (7 - col)) & 1
                if pixel:
                    x = (x_coord + col) % 64
                    y = (y_coord + row) % 32
                    if self.display[y][x] == 1:
                        self.V[0xF] = 1
                    self.display[y][x] ^= 1

    # Timer updates (called at ~60 Hz)
    def update_timers(self):
        if self.delay_timer > 0:
            self.delay_timer -= 1
        if self.sound_timer > 0:
            # Simple placeholder: could play a beep on Windows
            # try: import winsound; winsound.Beep(440, 50)
            self.sound_timer -= 1

# ------------------------------------------------------------
# 3. Tkinter UI
# ------------------------------------------------------------

class Chip8GUI(tk.Tk):
    def __init__(self, chip8):
        super().__init__()
        self.title("Chip‑8 Emulator – ChatGPT")
        self.chip8 = chip8

        # Canvas for 64×32 pixel display (scaled by 10)
        self.canvas = tk.Canvas(self, width=640, height=320, bg='black')
        self.canvas.pack()

        # Create rectangle objects for each pixel
        self.rects = [[self.canvas.create_rectangle(
            x*10, y*10, x*10+10, y*10+10,
            fill='black', outline=''
        ) for x in range(64)] for y in range(32)]

        # Menu bar
        menubar = tk.Menu(self)
        filemenu = tk.Menu(menubar, tearoff=0)
        filemenu.add_command(label="Load ROM", command=self.load_rom)
        filemenu.add_separator()
        filemenu.add_command(label="Reset", command=self.reset)
        menubar.add_cascade(label="File", menu=filemenu)
        self.config(menu=menubar)

        # Key bindings
        self.bind_all('<KeyPress>',  self.on_key_press)
        self.bind_all('<KeyRelease>',self.on_key_release)

        # Bottom stamp
        tk.Label(self, text="Emulator written by ChatGPT", font=("Arial", 8), fg='gray').pack(side=tk.BOTTOM)

        # Start the emulation loop
        self.after(1,   self.emulate_cycle)
        self.after(16,  self.update_timers)

    # ----------------------------------------------------------------
    # File operations
    # ----------------------------------------------------------------

    def load_rom(self):
        path = filedialog.askopenfilename(filetypes=[("Chip‑8 ROM", "*.c8 *.ch8 *.rom")])
        if path:
            try:
                self.chip8.load_rom(path)
            except Exception as e:
                messagebox.showerror("Error", f"Failed to load ROM:\n{e}")

    def reset(self):
        self.chip8.reset()

    # ----------------------------------------------------------------
    # Emulation cycle
    # ----------------------------------------------------------------

    def emulate_cycle(self):
        if not self.chip8.rom_loaded:
            # Don’t run until a ROM is loaded; avoids “0000” spam at pc=0x200.
            self.after(50, self.emulate_cycle)
            return
        if self.chip8.halted:
            return
        if not (0x200 <= self.chip8.pc < len(self.chip8.memory)):
            return  # PC out of bounds – stop

        opcode = self.chip8.fetch_opcode()
        self.chip8.execute(opcode)
        self.update_display()

        # Schedule next cycle
        self.after(1, self.emulate_cycle)

    def update_display(self):
        for y in range(32):
            for x in range(64):
                color = 'white' if self.chip8.display[y][x] else 'black'
                self.canvas.itemconfig(self.rects[y][x], fill=color)

    def update_timers(self):
        self.chip8.update_timers()
        self.after(16, self.update_timers)

    # ----------------------------------------------------------------
    # Keyboard handling
    # ----------------------------------------------------------------

    def on_key_press(self, event):
        key = event.keysym.lower()
        if key in KEY_MAP:
            self.chip8.keys[KEY_MAP[key]] = 1

    def on_key_release(self, event):
        key = event.keysym.lower()
        if key in KEY_MAP:
            self.chip8.keys[KEY_MAP[key]] = 0

# ------------------------------------------------------------
# 4. Entry point
# ------------------------------------------------------------

if __name__ == "__main__":
    chip8 = Chip8()
    app   = Chip8GUI(chip8)
    app.mainloop()
