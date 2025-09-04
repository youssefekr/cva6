bootrom_img = bootrom.img bootrom.sv

RISCV_GCC?=$(RISCV_CC)#riscv64-unknown-elf-gcc
RISCV_OBJCOPY?=$(RISCV)/bin/riscv-none-elf-objcopy#riscv64-unknown-elf-objcopy
DTB=ariane.dtb
PYTHON=python

all: $(bootrom_img)

%.img: %.bin
	dd if=$< of=$@ bs=128

%.bin: %.elf
	$(RISCV_OBJCOPY) -O binary $< $@

%.elf: %.S linker.ld $(DTB)
	$(RISCV_GCC) -Tlinker.ld -march=rv64gc_zba_zbb_zbs_zbc_zbkb_zbkx_zkne_zknd_zknh -mabi=lp64d $< -nostdlib -static -Wl,--no-gc-sections -o $@

%.dtb: %.dts
	dtc -I dts $< -O dtb -o $@

%.sv: %.img
	$(PYTHON) ./gen_rom.py $<

clean:
	rm -f $(bootrom_img) $(DTB)
