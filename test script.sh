source verif/sim/setup-env.sh
export DV_SIMULATORS=veri-testharness #,spike
#export TRACE_FAST=0
cd verif/sim
# helloworld cv32a65x
python3 cva6.py --target cv32a65x --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --c_tests ../tests/custom/hello_world/hello_world.c --linker=../../config/gen_from_riscv_config/linker/link.ld --gcc_opts="-static -mcmodel=medany -fvisibility=hidden -nostdlib -nostartfiles -g ../tests/custom/common/syscalls.c ../tests/custom/common/crt.S -lgcc -I../tests/custom/env -I../tests/custom/common"
# helloworld cv64a6_imafdc_sv39
#python3 cva6.py --target cv64a6_imafdc_sv39 --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --c_tests ../tests/custom/hello_world/hello_world.c --linker=../../config/gen_from_riscv_config/linker/link.ld --gcc_opts="-static -mcmodel=medany -fvisibility=hidden -nostdlib -nostartfiles -g ../tests/custom/common/syscalls.c ../tests/custom/common/crt.S -lgcc -I../tests/custom/env -I../tests/custom/common"
# helloworld oc_override
#python3 cva6.py --target cv64a6_imafdc_sv39_oc_override --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --isspostrun_opts="0x0000018000000000" --c_tests ../tests/custom/hello_world/hello_world.c --linker=../../config/gen_from_riscv_config/linker/link.ld --gcc_opts="-static -mcmodel=medany -fvisibility=hidden -nostdlib -nostartfiles -g ../tests/custom/common/syscalls.c ../tests/custom/common/crt.S -lgcc -I../tests/custom/env -I../tests/custom/common"
# testlist cv32a65x
#python3 cva6.py --target cv32a65x --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --testlist ../tests/testlist_riscv-arch-test-cv32a65x.yaml --test rv32im-fence-01  --linker=../tests/riscv-arch-test/riscv-target/spike/link.ld #rv32im-add-01
# testlist cv64a6_imafdc_sv39_oc_overrride
#python3 cva6.py --target cv64a6_imafdc_sv39_oc_override --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --isspostrun_opts="0x0000018000000000" --testlist ../tests/testlist_riscv-arch-test-cv64a6_imafdc_sv39.yaml --linker=../tests/riscv-arch-test/riscv-target/spike/link.ld --test rv64i_m-fence-01 #--spike_params="/top/dram_base:uint64_t=0x18000000000,/top/dram_size:uint64_t=0x1000000000" #,/top/core/0/boot_addr:uint64_t=0x18000000000" #--linker=../tests/riscv-tests/env/p/link.ld #--test rv64si-p-dirty # --test rv64ui-v-add # --linker=../tests/riscv-arch-test/riscv-target/spike/link.ld #--test rv64i_m-fence-01 #   #--linker=../../config/gen_from_riscv_config/linker/link.ld
# testlist cv64a6_imafdc_sv39
#python3 cva6.py --target cv64a6_imafdc_sv39 --iss=$DV_SIMULATORS --iss_yaml=cva6.yaml --testlist ../tests/testlist_riscv-tests-cv64a6_imafdc_sv39-v.yaml --linker=../tests/riscv-tests/env/v/link.ld #--test rv64ui-v-add #--test  rv32ui-add
#verilator_coverage logs/coverage.dat --annotate logs