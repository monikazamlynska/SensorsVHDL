vlib work
vlib riviera

vlib riviera/processing_system7_bfm_v2_0_5
vlib riviera/xil_defaultlib

vmap processing_system7_bfm_v2_0_5 riviera/processing_system7_bfm_v2_0_5
vmap xil_defaultlib riviera/xil_defaultlib

vlog -work processing_system7_bfm_v2_0_5  -v2k5 "+incdir+../../../../PMOD_MAXSONAR.srcs/sources_1/bd/MAXONAR/ipshared/7dd0/hdl" "+incdir+../../../../PMOD_MAXSONAR.srcs/sources_1/bd/MAXONAR/ipshared/7dd0/hdl" \
"../../../../PMOD_MAXSONAR.srcs/sources_1/bd/MAXONAR/ipshared/7dd0/hdl/processing_system7_bfm_v2_0_vl_rfs.v" \

vlog -work xil_defaultlib  -v2k5 "+incdir+../../../../PMOD_MAXSONAR.srcs/sources_1/bd/MAXONAR/ipshared/7dd0/hdl" "+incdir+../../../../PMOD_MAXSONAR.srcs/sources_1/bd/MAXONAR/ipshared/7dd0/hdl" \
"../../../bd/MAXONAR/ip/MAXONAR_processing_system7_0_0/sim/MAXONAR_processing_system7_0_0.v" \
"../../../bd/MAXONAR/hdl/MAXONAR.v" \

vlog -work xil_defaultlib "glbl.v"

