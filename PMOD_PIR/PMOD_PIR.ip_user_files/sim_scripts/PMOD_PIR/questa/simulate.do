onbreak {quit -f}
onerror {quit -f}

vsim -t 1ps -pli "C:/Xilinx/Vivado/2016.4/lib/win64.o/libxil_vsim.dll" -lib xil_defaultlib PMOD_PIR_opt

do {wave.do}

view wave
view structure
view signals

do {PMOD_PIR.udo}

run -all

quit -force
