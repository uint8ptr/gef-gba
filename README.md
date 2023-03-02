# GEF GBA

Custom version of [GEF](https://github.com/hugsy/gef) optimized for GBA debugging.

## Requirements

Make sure you have mGBA, `arm-none-eabi-gdb` 8.0+ and Python 3.6+ installed, and put the following lines in your `.gdbinit`:

```sh
define init-gef-gba
    source ~/gef-gba/gef.py
end

init-gef-gba
target remote localhost:2345
```

If you are using Windows, [xPack GNU Arm Embedded GCC](https://xpack.github.io/dev-tools/arm-none-eabi-gcc) ships with a version of `arm-none-eabi-gdb` compatible with Python 3.

## How to use

1. Load your game with mGBA
2. Go to mGBA > Tools > Start GDB server... > Start
3. Run the command `arm-none-eabi-gdb [cart.elf]`