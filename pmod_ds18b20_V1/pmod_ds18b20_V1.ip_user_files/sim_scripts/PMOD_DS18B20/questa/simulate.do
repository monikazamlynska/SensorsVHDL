onbreak {quit -f}
onerror {quit -f}

vsim -t 1ps -pli "C:/Xilinx/Vivado/2016.4/lib/win64.o/libxil_vsim.dll" -lib xil_defaultlib PMOD_DS18B20_opt

do {wave.do}

view wave
view structure
view signals

do {PMOD_DS18B20.udo}

run -all

quit -force
