onbreak {quit -force}
onerror {quit -force}

asim -t 1ps +access +r +m+PMOD_DS18B20 -pli "C:/Xilinx/Vivado/2016.4/lib/win64.o/libxil_vsim.dll" -L processing_system7_bfm_v2_0_5 -L xil_defaultlib -L unisims_ver -L unimacro_ver -L secureip -O5 xil_defaultlib.PMOD_DS18B20 xil_defaultlib.glbl

do {wave.do}

view wave
view structure

do {PMOD_DS18B20.udo}

run -all

endsim

quit -force
