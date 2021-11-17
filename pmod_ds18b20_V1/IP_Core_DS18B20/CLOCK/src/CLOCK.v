module CLOCK(input CLK,
		output CLK_250KHz,
		output CLK_1MHz);



reg clk_250KHZ;
reg [4:0] cc;

reg clk_1MHz;
reg [4:0] ct;

always @(posedge CLK) 
 if (ct<24) ct<=ct+1;
 else 
 begin ct<=0; 
 clk_1MHz<=~clk_1MHz; 
end 

assign CLK_1MHz = clk_1MHz;

always @(posedge clk_1MHz) 
 if (cc<1) cc<=cc+1;
 else 
 begin cc<=0; 
 clk_250KHZ<=~clk_250KHZ; 
end
assign CLK_250KHz = clk_250KHZ;

endmodule