proc start_step { step } {
  set stopFile ".stop.rst"
  if {[file isfile .stop.rst]} {
    puts ""
    puts "*** Halting run - EA reset detected ***"
    puts ""
    puts ""
    return -code error
  }
  set beginFile ".$step.begin.rst"
  set platform "$::tcl_platform(platform)"
  set user "$::tcl_platform(user)"
  set pid [pid]
  set host ""
  if { [string equal $platform unix] } {
    if { [info exist ::env(HOSTNAME)] } {
      set host $::env(HOSTNAME)
    }
  } else {
    if { [info exist ::env(COMPUTERNAME)] } {
      set host $::env(COMPUTERNAME)
    }
  }
  set ch [open $beginFile w]
  puts $ch "<?xml version=\"1.0\"?>"
  puts $ch "<ProcessHandle Version=\"1\" Minor=\"0\">"
  puts $ch "    <Process Command=\".planAhead.\" Owner=\"$user\" Host=\"$host\" Pid=\"$pid\">"
  puts $ch "    </Process>"
  puts $ch "</ProcessHandle>"
  close $ch
}

proc end_step { step } {
  set endFile ".$step.end.rst"
  set ch [open $endFile w]
  close $ch
}

proc step_failed { step } {
  set endFile ".$step.error.rst"
  set ch [open $endFile w]
  close $ch
}

set_msg_config -id {HDL 9-1061} -limit 100000
set_msg_config -id {HDL 9-1654} -limit 100000
set_msg_config -id {Synth 8-256} -limit 10000
set_msg_config -id {Synth 8-638} -limit 10000

start_step init_design
set ACTIVE_STEP init_design
set rc [catch {
  create_msg_db init_design.pb
  create_project -in_memory -part xc7z020clg400-1
  set_property board_part digilentinc.com:zybo-z7-20:part0:1.0 [current_project]
  set_property design_mode GateLvl [current_fileset]
  set_param project.singleFileAddWarning.threshold 0
  set_property webtalk.parent_dir E:/zybo/PMOD_MAXSONAR/PMOD_MAXSONAR.cache/wt [current_project]
  set_property parent.project_path E:/zybo/PMOD_MAXSONAR/PMOD_MAXSONAR.xpr [current_project]
  set_property ip_output_repo E:/zybo/PMOD_MAXSONAR/PMOD_MAXSONAR.cache/ip [current_project]
  set_property ip_cache_permissions {read write} [current_project]
  add_files -quiet E:/zybo/PMOD_MAXSONAR/PMOD_MAXSONAR.runs/synth_1/MAXONAR_wrapper.dcp
  add_files -quiet e:/zybo/PMOD_MAXSONAR/PMOD_MAXSONAR.srcs/sources_1/bd/MAXONAR/ip/MAXONAR_processing_system7_0_0/MAXONAR_processing_system7_0_0.dcp
  set_property netlist_only true [get_files e:/zybo/PMOD_MAXSONAR/PMOD_MAXSONAR.srcs/sources_1/bd/MAXONAR/ip/MAXONAR_processing_system7_0_0/MAXONAR_processing_system7_0_0.dcp]
  read_xdc -ref MAXONAR_processing_system7_0_0 -cells inst e:/zybo/PMOD_MAXSONAR/PMOD_MAXSONAR.srcs/sources_1/bd/MAXONAR/ip/MAXONAR_processing_system7_0_0/MAXONAR_processing_system7_0_0.xdc
  set_property processing_order EARLY [get_files e:/zybo/PMOD_MAXSONAR/PMOD_MAXSONAR.srcs/sources_1/bd/MAXONAR/ip/MAXONAR_processing_system7_0_0/MAXONAR_processing_system7_0_0.xdc]
  read_xdc E:/zybo/PMOD_MAXSONAR/PMOD_MAXSONAR.srcs/constrs_1/new/MAXSENSOR.xdc
  link_design -top MAXONAR_wrapper -part xc7z020clg400-1
  write_hwdef -file MAXONAR_wrapper.hwdef
  close_msg_db -file init_design.pb
} RESULT]
if {$rc} {
  step_failed init_design
  return -code error $RESULT
} else {
  end_step init_design
  unset ACTIVE_STEP 
}

start_step opt_design
set ACTIVE_STEP opt_design
set rc [catch {
  create_msg_db opt_design.pb
  opt_design 
  write_checkpoint -force MAXONAR_wrapper_opt.dcp
  catch { report_drc -file MAXONAR_wrapper_drc_opted.rpt }
  close_msg_db -file opt_design.pb
} RESULT]
if {$rc} {
  step_failed opt_design
  return -code error $RESULT
} else {
  end_step opt_design
  unset ACTIVE_STEP 
}

start_step place_design
set ACTIVE_STEP place_design
set rc [catch {
  create_msg_db place_design.pb
  implement_debug_core 
  place_design 
  write_checkpoint -force MAXONAR_wrapper_placed.dcp
  catch { report_io -file MAXONAR_wrapper_io_placed.rpt }
  catch { report_utilization -file MAXONAR_wrapper_utilization_placed.rpt -pb MAXONAR_wrapper_utilization_placed.pb }
  catch { report_control_sets -verbose -file MAXONAR_wrapper_control_sets_placed.rpt }
  close_msg_db -file place_design.pb
} RESULT]
if {$rc} {
  step_failed place_design
  return -code error $RESULT
} else {
  end_step place_design
  unset ACTIVE_STEP 
}

start_step route_design
set ACTIVE_STEP route_design
set rc [catch {
  create_msg_db route_design.pb
  route_design 
  write_checkpoint -force MAXONAR_wrapper_routed.dcp
  catch { report_drc -file MAXONAR_wrapper_drc_routed.rpt -pb MAXONAR_wrapper_drc_routed.pb -rpx MAXONAR_wrapper_drc_routed.rpx }
  catch { report_methodology -file MAXONAR_wrapper_methodology_drc_routed.rpt -rpx MAXONAR_wrapper_methodology_drc_routed.rpx }
  catch { report_timing_summary -warn_on_violation -max_paths 10 -file MAXONAR_wrapper_timing_summary_routed.rpt -rpx MAXONAR_wrapper_timing_summary_routed.rpx }
  catch { report_power -file MAXONAR_wrapper_power_routed.rpt -pb MAXONAR_wrapper_power_summary_routed.pb -rpx MAXONAR_wrapper_power_routed.rpx }
  catch { report_route_status -file MAXONAR_wrapper_route_status.rpt -pb MAXONAR_wrapper_route_status.pb }
  catch { report_clock_utilization -file MAXONAR_wrapper_clock_utilization_routed.rpt }
  close_msg_db -file route_design.pb
} RESULT]
if {$rc} {
  write_checkpoint -force MAXONAR_wrapper_routed_error.dcp
  step_failed route_design
  return -code error $RESULT
} else {
  end_step route_design
  unset ACTIVE_STEP 
}

start_step write_bitstream
set ACTIVE_STEP write_bitstream
set rc [catch {
  create_msg_db write_bitstream.pb
  catch { write_mem_info -force MAXONAR_wrapper.mmi }
  write_bitstream -force -no_partial_bitfile MAXONAR_wrapper.bit 
  catch { write_sysdef -hwdef MAXONAR_wrapper.hwdef -bitfile MAXONAR_wrapper.bit -meminfo MAXONAR_wrapper.mmi -file MAXONAR_wrapper.sysdef }
  catch {write_debug_probes -quiet -force debug_nets}
  close_msg_db -file write_bitstream.pb
} RESULT]
if {$rc} {
  step_failed write_bitstream
  return -code error $RESULT
} else {
  end_step write_bitstream
  unset ACTIVE_STEP 
}

