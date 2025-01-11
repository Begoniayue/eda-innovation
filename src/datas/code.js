export const originalCode = `module ct_pmp_regs(
  cp0_pmp_wdata,
  cpuclk,
  cpurst_b,
  pmp_cp0_data,
  pmp_csr_sel,
  pmp_csr_wen,
  pmpaddr0_value,
  pmpaddr1_value,
  pmpaddr2_value,
  pmpaddr3_value,
  pmpaddr4_value,
  pmpaddr5_value,
  pmpaddr6_value,
  pmpaddr7_value,
  pmpcfg0_value,
  pmpcfg2_value
);
input   [63:0]  cp0_pmp_wdata;
input           cpuclk;
input           cpurst_b;
input   [17:0]  pmp_csr_sel;
input   [17:0]  pmp_csr_wen;
output  [63:0]  pmp_cp0_data;
output  [28:0]  pmpaddr0_value;
output  [28:0]  pmpaddr1_value;
output  [28:0]  pmpaddr2_value;
output  [28:0]  pmpaddr3_value;
output  [28:0]  pmpaddr4_value;
output  [28:0]  pmpaddr5_value;
output  [28:0]  pmpaddr6_value;
output  [28:0]  pmpaddr7_value;
output  [63:0]  pmpcfg0_value;
output  [63:0]  pmpcfg2_value;
reg     [1 :0]  pmp0cfg_addr_mode;
reg             pmp0cfg_executeable;
reg             pmp0cfg_lock;
reg             pmp0cfg_readable;
reg             pmp0cfg_writable;
reg     [1 :0]  pmp1cfg_addr_mode;
reg             pmp1cfg_executeable;
reg             pmp1cfg_lock;
reg             pmp1cfg_readable;
reg             pmp1cfg_writable;
reg     [1 :0]  pmp2cfg_addr_mode;
reg             pmp2cfg_executeable;
reg             pmp2cfg_lock;
reg             pmp2cfg_readable;
reg             pmp2cfg_writable;
reg     [1 :0]  pmp3cfg_addr_mode;
reg             pmp3cfg_executeable;
reg             pmp3cfg_lock;
reg             pmp3cfg_readable;
reg             pmp3cfg_writable;
reg     [1 :0]  pmp4cfg_addr_mode;
reg             pmp4cfg_executeable;
reg             pmp4cfg_lock;
reg             pmp4cfg_readable;
reg             pmp4cfg_writable;
reg     [1 :0]  pmp5cfg_addr_mode;
reg             pmp5cfg_executeable;
reg             pmp5cfg_lock;
reg             pmp5cfg_readable;
reg             pmp5cfg_writable;
reg     [1 :0]  pmp6cfg_addr_mode;
reg             pmp6cfg_executeable;
reg             pmp6cfg_lock;
reg             pmp6cfg_readable;
reg             pmp6cfg_writable;
reg     [1 :0]  pmp7cfg_addr_mode;
reg             pmp7cfg_executeable;
reg             pmp7cfg_lock;
reg             pmp7cfg_readable;
reg             pmp7cfg_writable;
reg     [28:0]  pmpaddr0_value;
reg     [28:0]  pmpaddr1_value;
reg     [28:0]  pmpaddr2_value;
reg     [28:0]  pmpaddr3_value;
reg     [28:0]  pmpaddr4_value;
reg     [28:0]  pmpaddr5_value;
reg     [28:0]  pmpaddr6_value;
reg     [28:0]  pmpaddr7_value;
wire    [63:0]  cp0_pmp_wdata;
wire            cpuclk;
wire            cpurst_b;
wire    [63:0]  pmp_cp0_data;
wire    [17:0]  pmp_csr_sel;
wire    [17:0]  pmp_csr_wen;
wire            pmp_updt_pmp0cfg;
wire            pmp_updt_pmp1cfg;
wire            pmp_updt_pmp2cfg;
wire            pmp_updt_pmp3cfg;
wire            pmp_updt_pmp4cfg;
wire            pmp_updt_pmp5cfg;
wire            pmp_updt_pmp6cfg;
wire            pmp_updt_pmp7cfg;
wire            pmp_updt_pmpaddr0;
wire            pmp_updt_pmpaddr1;
wire            pmp_updt_pmpaddr2;
wire            pmp_updt_pmpaddr3;
wire            pmp_updt_pmpaddr4;
wire            pmp_updt_pmpaddr5;
wire            pmp_updt_pmpaddr6;
wire            pmp_updt_pmpaddr7;

wire    [63:0]  pmpcfg0_value;
wire    [63:0]  pmpcfg2_value;
parameter ADDR_WIDTH = 28+1;
assign pmp_updt_pmp0cfg = pmp_csr_wen[0] && !pmp0cfg_lock;
always @(posedge cpuclk or negedge cpurst_b)
begin
  if(!cpurst_b)
    pmp5cfg readable       <= 11'b1;
    pmp0cfg_readable       <= 1'b0;
    pmp0cfg_writable       <= 1'b0;
    pmp0cfg_executeable    <= 1'b0;
    pmp0cfg_addr_mode[1:0] <= 2'b0;
    pmp0cfg_lock           <= 1'b0;
  end
  else if(pmp_updt_pmp0cfg)
  begin
    pmp0cfg_readable       <= cp0_pmp_wdata[0];
    pmp0cfg_writable       <= cp0_pmp_wdata[1];
    pmp0cfg_executeable    <= cp0_pmp_wdata[2];
    pmp0cfg_addr_mode[1:0] <= cp0_pmp_wdata[4:3];
    pmp0cfg_lock           <= cp0_pmp_wdata[7];
  end
  else
  begin
    pmp0cfg_readable       <= pmp0cfg_readable;
    pmp0cfg_writable       <= pmp0cfg_writable;
    pmp0cfg_executeable    <= pmp0cfg_executeable;
    pmp0cfg_addr_mode[1:0] <= pmp0cfg_addr_mode[1:0];
    pmp0cfg_lock           <= pmp0cfg_lock;
  end
end
assign pmp_updt_pmp1cfg = pmp_csr_wen[0] && !pmp1cfg_lock;
always @(posedge cpuclk or negedge cpurst_b)
begin
  if(!cpurst_b)
  begin
    pmp1cfg_readable       <= 1'b0;
    pmp1cfg_writable       <= 1'b0;
    pmp1cfg_executeable    <= 1'b0;
    pmp1cfg_addr_mode[1:0] <= 2'b0;
    pmp1cfg_lock           <= 1'b0;
  end
  else if(pmp_updt_pmp1cfg)
  begin
    pmp1cfg_readable       <= cp0_pmp_wdata[8];
    pmp1cfg_writable       <= cp0_pmp_wdata[9];
    pmp1cfg_executeable    <= cp0_pmp_wdata[10];
    pmp1cfg_addr_mode[1:0] <= cp0_pmp_wdata[12:11];
    pmp1cfg_lock           <= cp0_pmp_wdata[15];
  end
  else
  begin
    pmp1cfg_readable       <= pmp1cfg_readable;
    pmp1cfg_writable       <= pmp1cfg_writable;
    pmp1cfg_executeable    <= pmp1cfg_executeable;
    pmp1cfg_addr_mode[1:0] <= pmp1cfg_addr_mode[1:0];
    pmp1cfg_lock           <= pmp1cfg_lock;
  end
end
assign pmp_updt_pmp2cfg = pmp_csr_wen[0] && !pmp2cfg_lock;
always @(posedge cpuclk or negedge cpurst_b)
begin
  if(!cpurst_b)
  begin
    pmp2cfg_readable       <= 1'b0;
    pmp2cfg_writable       <= 1'b0;
    pmp2cfg_executeable    <= 1'b0;
    pmp2cfg_addr_mode[1:0] <= 2'b0;
    pmp2cfg_lock           <= 1'b0;
  end
  else if(pmp_updt_pmp2cfg)
  begin
    pmp2cfg_readable       <= cp0_pmp_wdata[16];
    pmp2cfg_writable       <= cp0_pmp_wdata[17];
    pmp2cfg_executeable    <= cp0_pmp_wdata[18];
    pmp2cfg_addr_mode[1:0] <= cp0_pmp_wdata[20:19];
    pmp2cfg_lock           <= cp0_pmp_wdata[23];
  end
  else
  begin
    pmp2cfg_readable       <= pmp2cfg_readable;
    pmp2cfg_writable       <= pmp2cfg_writable;
    pmp2cfg_executeable    <= pmp2cfg_executeable;
    pmp2cfg_addr_mode[1:0] <= pmp2cfg_addr_mode[1:0];
    pmp2cfg_lock           <= pmp2cfg_lock;
  end
end
assign pmp_updt_pmp3cfg = pmp_csr_wen[0] && !pmp3cfg_lock;
always @(posedge cpuclk or negedge cpurst_b)
begin
  if(!cpurst_b)
  begin
    pmp3cfg_readable       <= 1'b0;
    pmp3cfg_writable       <= 1'b0;
    pmp3cfg_executeable    <= 1'b0;
    pmp3cfg_addr_mode[1:0] <= 2'b0;
    pmp3cfg_lock           <= 1'b0;
  end
  else if(pmp_updt_pmp3cfg)
  begin
    pmp3cfg_readable       <= cp0_pmp_wdata[24];
    pmp3cfg_writable       <= cp0_pmp_wdata[25];
    pmp3cfg_executeable    <= cp0_pmp_wdata[26];
    pmp3cfg_addr_mode[1:0] <= cp0_pmp_wdata[28:27];
    pmp3cfg_lock           <= cp0_pmp_wdata[31];
  end
  else
  begin
    pmp3cfg_readable       <= pmp3cfg_readable;
    pmp3cfg_writable       <= pmp3cfg_writable;
    pmp3cfg_executeable    <= pmp3cfg_executeable;
    pmp3cfg_addr_mode[1:0] <= pmp3cfg_addr_mode[1:0];
    pmp3cfg_lock           <= pmp3cfg_lock;
  end
end
assign pmp_updt_pmp4cfg = pmp_csr_wen[0] && !pmp4cfg_lock;
always @(posedge cpuclk or negedge cpurst_b)
begin
  if(!cpurst_b)
  begin
    pmp4cfg_readable       <= 1'b0;
    pmp4cfg_writable       <= 1'b0;
    pmp4cfg_executeable    <= 1'b0;
    pmp4cfg_addr_mode[1:0] <= 2'b0;
    pmp4cfg_lock           <= 1'b0;
  end
  else if(pmp_updt_pmp4cfg)
  begin
    pmp4cfg_readable        <= cp0_pmp_wdata[32];
    pmp4cfg_writable        <= cp0_pmp_wdata[33];
    pmp4cfg_executeable     <= cp0_pmp_wdata[34];
    pmp4cfg_addr_mode[1:0]  <= cp0_pmp_wdata[36:35];
    pmp4cfg_lock            <= cp0_pmp_wdata[39];
  end
  else
  begin
    pmp4cfg_readable       <= pmp4cfg_readable;
    pmp4cfg_writable       <= pmp4cfg_writable;
    pmp4cfg_executeable    <= pmp4cfg_executeable;
    pmp4cfg_addr_mode[1:0] <= pmp4cfg_addr_mode[1:0];
    pmp4cfg_lock           <= pmp4cfg_lock;
  end
end
assign pmp_updt_pmp5cfg = pmp_csr_wen[0] && !pmp5cfg_lock;
always @(posedge cpuclk or negedge cpurst_b)
begin
  if(!cpurst_b)
  begin
    pmp5cfg_readable       <= 1'b0;
    pmp5cfg_writable       <= 1'b0;
    pmp5cfg_executeable    <= 1'b0;
    pmp5cfg_addr_mode[1:0] <= 2'b0;
    pmp5cfg_lock           <= 1'b0;
  end
  else if(pmp_updt_pmp5cfg)
  begin
    pmp5cfg_readable       <= cp0_pmp_wdata[40];
    pmp5cfg_writable       <= cp0_pmp_wdata[41];
    pmp5cfg_executeable    <= cp0_pmp_wdata[42];
    pmp5cfg_addr_mode[1:0] <= cp0_pmp_wdata[44:43];
    pmp5cfg_lock           <= cp0_pmp_wdata[47];
  end
  else
  begin
    pmp5cfg_readable       <= pmp5cfg_readable;
    pmp5cfg_writable       <= pmp5cfg_writable;
    pmp5cfg_executeable    <= pmp5cfg_executeable;
    pmp5cfg_addr_mode[1:0] <= pmp5cfg_addr_mode[1:0];
    pmp5cfg_lock           <= pmp5cfg_lock;
  end
end
assign pmp_updt_pmp6cfg = pmp_csr_wen[0] && !pmp6cfg_lock;
always @(posedge cpuclk or negedge cpurst_b)
begin
  if(!cpurst_b)
  begin
    pmp6cfg_readable       <= 1'b0;
    pmp6cfg_writable       <= 1'b0;
    pmp6cfg_executeable    <= 1'b0;
    pmp6cfg_addr_mode[1:0] <= 2'b0;
    pmp6cfg_lock           <= 1'b0;
  end
  else if(pmp_updt_pmp6cfg)
  begin
    pmp6cfg_readable       <= cp0_pmp_wdata[48];
    pmp6cfg_writable       <= cp0_pmp_wdata[49];
    pmp6cfg_executeable    <= cp0_pmp_wdata[50];
    pmp6cfg_addr_mode[1:0] <= cp0_pmp_wdata[52:51];
    pmp6cfg_lock           <= cp0_pmp_wdata[55];
  end
  else
  begin
    pmp6cfg_readable       <= pmp6cfg_readable;
    pmp6cfg_writable       <= pmp6cfg_writable;
    pmp6cfg_executeable    <= pmp6cfg_executeable;
    pmp6cfg_addr_mode[1:0] <= pmp6cfg_addr_mode[1:0];
    pmp6cfg_lock           <= pmp6cfg_lock;
  end
end
assign pmp_updt_pmp7cfg = pmp_csr_wen[0] && !pmp7cfg_lock;
always @(posedge cpuclk or negedge cpurst_b)
begin
  if(!cpurst_b)
  begin
    pmp7cfg_readable       <= 1'b0;
    pmp7cfg_writable       <= 1'b0;
    pmp7cfg_executeable    <= 1'b0;
    pmp7cfg_addr_mode[1:0] <= 2'b0;
    pmp7cfg_lock           <= 1'b0;
  end
  else if(pmp_updt_pmp7cfg)
  begin
    pmp7cfg_readable       <= cp0_pmp_wdata[56];
    pmp7cfg_writable       <= cp0_pmp_wdata[57];
    pmp7cfg_executeable    <= cp0_pmp_wdata[58];
    pmp7cfg_addr_mode[1:0] <= cp0_pmp_wdata[60:59];
    pmp7cfg_lock           <= cp0_pmp_wdata[63];
  end
  else
  begin
    pmp7cfg_readable       <= pmp7cfg_readable;
    pmp7cfg_writable       <= pmp7cfg_writable;
    pmp7cfg_executeable    <= pmp7cfg_executeable;
    pmp7cfg_addr_mode[1:0] <= pmp7cfg_addr_mode[1:0];
    pmp7cfg_lock           <= pmp7cfg_lock;
  end
end
assign pmpcfg0_value[31:0] = {pmp3cfg_lock,2'b0,pmp3cfg_addr_mode[1:0],pmp3cfg_executeable,pmp3cfg_writable,pmp3cfg_readable,
                              pmp2cfg_lock,2'b0,pmp2cfg_addr_mode[1:0],pmp2cfg_executeable,pmp2cfg_writable,pmp2cfg_readable,
                              pmp1cfg_lock,2'b0,pmp1cfg_addr_mode[1:0],pmp1cfg_executeable,pmp1cfg_writable,pmp1cfg_readable,
                              pmp0cfg_lock,2'b0,pmp0cfg_addr_mode[1:0],pmp0cfg_executeable,pmp0cfg_writable,pmp0cfg_readable};
assign pmpcfg0_value[63:32] = {pmp7cfg_lock,2'b0,pmp7cfg_addr_mode[1:0],pmp7cfg_executeable,pmp7cfg_writable,pmp7cfg_readable,
                              pmp6cfg_lock,2'b0,pmp6cfg_addr_mode[1:0],pmp6cfg_executeable,pmp6cfg_writable,pmp6cfg_readable,
                              pmp5cfg_lock,2'b0,pmp5cfg_addr_mode[1:0],pmp5cfg_executeable,pmp5cfg_writable,pmp5cfg_readable,
                              pmp4cfg_lock,2'b0,pmp4cfg_addr_mode[1:0],pmp4cfg_executeable,pmp4cfg_writable,pmp4cfg_readable};
assign pmpcfg2_value[63:0] = 64'b0;
assign pmp_updt_pmpaddr0 = pmp_csr_wen[2] && !pmpcfg0_value[7] && !(pmpcfg0_value[15] && (pmpcfg0_value[12:11] == 2'b01)) ;
always @(posedge cpuclk or negedge cpurst_b)
begin
  if(!cpurst_b)
    pmpaddr0_value[ADDR_WIDTH-1:0] <= {ADDR_WIDTH{1'b0}};
  else if(pmp_updt_pmpaddr0)
    pmpaddr0_value[ADDR_WIDTH-1:0] <= cp0_pmp_wdata[ADDR_WIDTH+8:9];
  else
    pmpaddr0_value[ADDR_WIDTH-1:0] <= pmpaddr0_value[ADDR_WIDTH-1:0];
end
assign pmp_updt_pmpaddr1 = pmp_csr_wen[3] && !pmpcfg0_value[15] && !(pmpcfg0_value[23] && (pmpcfg0_value[20:19] == 2'b01));
always @(posedge cpuclk or negedge cpurst_b)
begin
  if(!cpurst_b)
    pmpaddr1_value[ADDR_WIDTH-1:0] <= {ADDR_WIDTH{1'b0}};
  else if(pmp_updt_pmpaddr1)
    pmpaddr1_value[ADDR_WIDTH-1:0] <= cp0_pmp_wdata[ADDR_WIDTH+8:9];
  else
    pmpaddr1_value[ADDR_WIDTH-1:0] <= pmpaddr1_value[ADDR_WIDTH-1:0];
end
assign pmp_updt_pmpaddr2 = pmp_csr_wen[4] && !pmpcfg0_value[23] && !(pmpcfg0_value[31] && (pmpcfg0_value[28:27] == 2'b01));
always @(posedge cpuclk or negedge cpurst_b)
begin
  if(!cpurst_b)
    pmpaddr2_value[ADDR_WIDTH-1:0] <= {ADDR_WIDTH{1'b0}};
  else if(pmp_updt_pmpaddr2)
    pmpaddr2_value[ADDR_WIDTH-1:0] <= cp0_pmp_wdata[ADDR_WIDTH+8:9];
  else
    pmpaddr2_value[ADDR_WIDTH-1:0] <= pmpaddr2_value[ADDR_WIDTH-1:0];
end
assign pmp_updt_pmpaddr3 = pmp_csr_wen[5] && !pmpcfg0_value[31] && !(pmpcfg0_value[39] && (pmpcfg0_value[36:35] == 2'b01));
always @(posedge cpuclk or negedge cpurst_b)
begin
  if(!cpurst_b)
    pmpaddr3_value[ADDR_WIDTH-1:0] <= {ADDR_WIDTH{1'b0}};
  else if(pmp_updt_pmpaddr3)
    pmpaddr3_value[ADDR_WIDTH-1:0] <= cp0_pmp_wdata[ADDR_WIDTH+8:9];
  else
    pmpaddr3_value[ADDR_WIDTH-1:0] <= pmpaddr3_value[ADDR_WIDTH-1:0];
end
assign pmp_updt_pmpaddr4 = pmp_csr_wen[6] && !pmpcfg0_value[39] && !(pmpcfg0_value[47] && (pmpcfg0_value[44:43] == 2'b01));
always @(posedge cpuclk or negedge cpurst_b)
begin
  if(!cpurst_b)
    pmpaddr4_value[ADDR_WIDTH-1:0] <= {ADDR_WIDTH{1'b0}};
  else if(pmp_updt_pmpaddr4)
    pmpaddr4_value[ADDR_WIDTH-1:0] <= cp0_pmp_wdata[ADDR_WIDTH+8:9];
  else
    pmpaddr4_value[ADDR_WIDTH-1:0] <= pmpaddr4_value[ADDR_WIDTH-1:0];
end
assign pmp_updt_pmpaddr5 = pmp_csr_wen[7] && !pmpcfg0_value[47] && !(pmpcfg0_value[55] && (pmpcfg0_value[52:51] == 2'b01));
always @(posedge cpuclk or negedge cpurst_b)
begin
  if(!cpurst_b)
    pmpaddr5_value[ADDR_WIDTH-1:0] <= {ADDR_WIDTH{1'b0}};
  else if(pmp_updt_pmpaddr5)
    pmpaddr5_value[ADDR_WIDTH-1:0] <= cp0_pmp_wdata[ADDR_WIDTH+8:9];
  else
    pmpaddr5_value[ADDR_WIDTH-1:0] <= pmpaddr5_value[ADDR_WIDTH-1:0];
end
assign pmp_updt_pmpaddr6 = pmp_csr_wen[8] && !pmpcfg0_value[55] && !(pmpcfg0_value[63] && (pmpcfg0_value[60:59] == 2'b01));
always @(posedge cpuclk or negedge cpurst_b)
begin
  if(!cpurst_b)
    pmpaddr6_value[ADDR_WIDTH-1:0] <= {ADDR_WIDTH{1'b0}};
  else if(pmp_updt_pmpaddr6)
    pmpaddr6_value[ADDR_WIDTH-1:0] <= cp0_pmp_wdata[ADDR_WIDTH+8:9];
  else
    pmpaddr6_value[ADDR_WIDTH-1:0] <= pmpaddr6_value[ADDR_WIDTH-1:0];
end
assign pmp_updt_pmpaddr7 = pmp_csr_wen[9] && !pmpcfg0_value[63] && !(pmpcfg2_value[7] && (pmpcfg2_value[4:3] == 2'b01));
always @(posedge cpuclk or negedge cpurst_b)
begin
  if(!cpurst_b)
    pmpaddr7_value[ADDR_WIDTH-1:0] <= {ADDR_WIDTH{1'b0}};
  else if(pmp_updt_pmpaddr7)
    pmpaddr7_value[ADDR_WIDTH-1:0] <= cp0_pmp_wdata[ADDR_WIDTH+8:9];
  else
    pmpaddr7_value[ADDR_WIDTH-1:0] <= pmpaddr7_value[ADDR_WIDTH-1:0];
end

assign pmp_cp0_data[63:0]  = {64{pmp_csr_sel[0]}}  & pmpcfg0_value[63:0];
endmodule`
export const appendCode = `
property p_pmpaddr5_value_retention;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (cpurst_b == 1 && pmp_updt_pmpaddr5 == 0) |-> ##1 pmpaddr5_value == $past(pmpaddr5_value);
endproperty

assert_p_pmpaddr5_value_retention: assert property (p_pmpaddr5_value_retention) else $error("Assertion failed: pmpaddr5_value does not retain its value when cpurst_b is 1 and pmp_updt_pmpaddr5 is 0");



property p_pmpaddr3_value_assignment_1;
    @(posedge cpuclk) disable iff (cpurst_b == 1)
        (cpurst_b == 0 && $past(cpurst_b) == 1) |-> ##1 (pmpaddr3_value == 0);
endproperty

assert_p_pmpaddr3_value_assignment_1: assert property (p_pmpaddr3_value_assignment_1) else $error("Assertion failed: pmpaddr3_value is not assigned to 0 one cycle after cpurst_b transitions from 1 to 0");

property p_pmpcfg2_value_unchanged_1;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        cpurst_b == 1 |->  pmpcfg2_value == cp0_pmp_wdata;
endproperty

assert_p_pmpcfg2_value_unchanged_1: assert property (p_pmpcfg2_value_unchanged_1) else $error("Assertion failed: pmpcfg2_value did not remain unchanged as expected.");


property p_pmp_updt_pmpaddr1_blocking_assign_zero_1;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        pmp_csr_wen[3] == 0 |-> pmp_updt_pmpaddr1 == 0;
endproperty

assert_p_pmp_updt_pmpaddr1_blocking_assign_zero_1: assert property (p_pmp_updt_pmpaddr1_blocking_assign_zero_1) else $error("Assertion failed: pmp_updt_pmpaddr1 is not zero when pmp_csr_wen[3] is zero");


property p_pmpaddr6_value_assignment_1;
    @(posedge cpuclk) disable iff (cpurst_b == 1)
        cpurst_b == 0 |-> ##1 pmpaddr6_value == {ADDR_WIDTH{1'b0}};
endproperty

assert_p_pmpaddr6_value_assignment_1: assert property (p_pmpaddr6_value_assignment_1) else $error("Assertion failed: pmpaddr6_value is not assigned to zero after cpurst_b is deasserted");

property p_pmp_updt_pmpaddr1_blocking_assign_zero;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (pmp_csr_wen[3] == 1 && pmpcfg0_value[15] == 1) |-> (pmp_updt_pmpaddr1 == 0);
endproperty

assert_p_pmp_updt_pmpaddr1_blocking_assign_zero: assert property (p_pmp_updt_pmpaddr1_blocking_assign_zero) else $error("Assertion failed: pmp_updt_pmpaddr1 is not zero when pmp_csr_wen[3] and pmpcfg0_value[15] are both 1");


property p_pmpaddr6_value_assignment_2;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (cpurst_b == 1 && pmp_csr_wen[8] && !pmpcfg0_value[55] && !(pmpcfg0_value[63] && (pmpcfg0_value[60:59] == 2'b01))) |-> ##1 pmpaddr6_value == $past(cp0_pmp_wdata[ADDR_WIDTH+8:9]);
endproperty

assert_p_pmpaddr6_value_assignment_2: assert property (p_pmpaddr6_value_assignment_2) else $error("Assertion failed: pmpaddr6_value does not match the past value of cp0_pmp_wdata[ADDR_WIDTH+8:9] after one clock cycle");



property pmp_updt_pmp0cfg_assignment_1;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        1 |-> (pmp_updt_pmp0cfg == (pmp_csr_wen[0] && !pmp0cfg_lock));
endproperty

assert_pmp_updt_pmp0cfg_assignment_1: assert property (pmp_updt_pmp0cfg_assignment_1) else $error("Assertion failed: pmp_updt_pmp0cfg does not reflect the correct state when cpurst_b is 1, pmp_csr_wen[0] is 1, and pmp0cfg_lock is 0");



property pmp_updt_pmp3cfg_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        1 |-> (pmp_updt_pmp3cfg == (pmp_csr_wen[0] && (!pmp3cfg_lock)));
endproperty

assert_pmp_updt_pmp3cfg_assignment: assert property (pmp_updt_pmp3cfg_assignment) else $error("Assertion failed: pmp_updt_pmp3cfg does not reflect the correct state when pmp_csr_wen[0] is 1 and pmp3cfg_lock is 0");



property p_pmpaddr6_value_retention;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (cpurst_b == 1 && pmp_updt_pmpaddr6 == 0) |-> ##1 pmpaddr6_value == $past(pmpaddr6_value);
endproperty

assert_p_pmpaddr6_value_retention: assert property (p_pmpaddr6_value_retention) else $error("Assertion failed: pmpaddr6_value does not retain its value when cpurst_b is 1 and pmp_updt_pmpaddr6 is 0");


property p_pmp_updt_pmp3cfg_blocking_assign_zero_1;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (pmp_csr_wen[0] == 0 && pmp3cfg_lock == 0) |-> (pmp_updt_pmp3cfg == 0);
endproperty

assert_p_pmp_updt_pmp3cfg_blocking_assign_zero_1: assert property (p_pmp_updt_pmp3cfg_blocking_assign_zero_1) else $error("Assertion failed: pmp_updt_pmp3cfg should be 0 when pmp_csr_wen[0] and pmp3cfg_lock are both 0");



property pmp_updt_pmp0cfg_assignment_2;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (cpurst_b == 1 && pmp_csr_wen[0] == 0 && pmp0cfg_lock == 0) |->
        (pmp_updt_pmp0cfg == (pmp_csr_wen[0] & ~pmp0cfg_lock));
endproperty

assert_pmp_updt_pmp0cfg_assignment_2: assert property (pmp_updt_pmp0cfg_assignment_2) else $error("Assertion failed: pmp_updt_pmp0cfg does not reflect the correct state when cpurst_b is 1, pmp_csr_wen[0] is 0, and pmp0cfg_lock is 0");



property p_pmpaddr6_value_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 1)
        (cpurst_b == 0 && $past(cpurst_b) == 1) |-> ##1 pmpaddr6_value == {ADDR_WIDTH{1'b0}};
endproperty

assert_p_pmpaddr6_value_assignment: assert property (p_pmpaddr6_value_assignment) else $error("Assertion failed: pmpaddr6_value is not assigned to zero after cpurst_b transitions from 1 to 0");



property p_pmp_updt_pmp3cfg_blocking_assign_zero;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (pmp_csr_wen[0] == 1 && pmp3cfg_lock == 1) |-> (pmp_updt_pmp3cfg == 0);
endproperty

assert_p_pmp_updt_pmp3cfg_blocking_assign_zero: assert property (p_pmp_updt_pmp3cfg_blocking_assign_zero) else $error("Assertion failed: pmp_updt_pmp3cfg should be 0 when pmp_csr_wen[0] is 1 and pmp3cfg_lock is 1");



property pmp_updt_pmp0cfg_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (cpurst_b == 1 && pmp_csr_wen[0] == 1 && pmp0cfg_lock == 1) |->
        (pmp_updt_pmp0cfg == (pmp_csr_wen[0] & ~pmp0cfg_lock));
endproperty

assert_pmp_updt_pmp0cfg_assignment: assert property (pmp_updt_pmp0cfg_assignment) else $error("Assertion failed: pmp_updt_pmp0cfg does not reflect the correct state when cpurst_b is 1, pmp_csr_wen[0] is 1, and pmp0cfg_lock is 1");



property pmp_updt_pmpaddr6_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (pmp_csr_wen[8] == 1 && pmpcfg0_value[55] == 0 && pmpcfg0_value[63] == 0 && pmpcfg0_value[60:59] != 2'b01) |-> (pmp_updt_pmpaddr6 == 1);
endproperty

assert_pmp_updt_pmpaddr6_assignment: assert property (pmp_updt_pmpaddr6_assignment) else $error("Assertion failed: pmp_updt_pmpaddr6 is not assigned correctly when pmp_csr_wen[8] is 1, pmpcfg0_value[55] is 0, pmpcfg0_value[63] is 0, and pmpcfg0_value[60:59] is not 2'b01");

property pmp_updt_pmpaddr0_1_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
         pmp_updt_pmpaddr0 == (pmp_csr_wen[2] && !pmpcfg0_value[7] && !(pmpcfg0_value[15] && (pmpcfg0_value[12:11] == 2'b01)));
endproperty

assert_pmp_updt_pmpaddr0_1_assignment: assert property (pmp_updt_pmpaddr0_1_assignment) else $error("Assertion failed: pmp_updt_pmpaddr0_1 is not assigned correctly when pmp_csr_wen[8] is 1, pmpcfg0_value[55] is 0, pmpcfg0_value[63] is 0, and pmpcfg0_value[60:59] is not 2'b01");

property pmp_updt_pmpaddr1_1_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
         pmp_updt_pmpaddr1 == (pmp_csr_wen[3] && !pmpcfg0_value[15] && !(pmpcfg0_value[23] && (pmpcfg0_value[20:19] == 2'b01)));
endproperty

assert_pmp_updt_pmpaddr1_1_assignment: assert property (pmp_updt_pmpaddr1_1_assignment) else $error("Assertion failed: pmp_updt_pmpaddr1_1 is not assigned correctly when pmp_csr_wen[8] is 1, pmpcfg0_value[55] is 0, pmpcfg0_value[63] is 0, and pmpcfg0_value[60:59] is not 2'b01");

property pmp_updt_pmpaddr2_1_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
         pmp_updt_pmpaddr2 == (pmp_csr_wen[4] && !pmpcfg0_value[23] && !(pmpcfg0_value[31] && (pmpcfg0_value[28:27] == 2'b01)));
endproperty

assert_pmp_updt_pmpaddr2_1_assignment: assert property (pmp_updt_pmpaddr2_1_assignment) else $error("Assertion failed: pmp_updt_pmpaddr2_1 is not assigned correctly when pmp_csr_wen[8] is 1, pmpcfg0_value[55] is 0, pmpcfg0_value[63] is 0, and pmpcfg0_value[60:59] is not 2'b01");

property pmp_updt_pmpaddr3_1_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
         pmp_updt_pmpaddr3 == (pmp_csr_wen[5] && !pmpcfg0_value[31] && !(pmpcfg0_value[39] && (pmpcfg0_value[36:35] == 2'b01)));
endproperty

assert_pmp_updt_pmpaddr3_1_assignment: assert property (pmp_updt_pmpaddr3_1_assignment) else $error("Assertion failed: pmp_updt_pmpaddr3_1 is not assigned correctly when pmp_csr_wen[8] is 1, pmpcfg0_value[55] is 0, pmpcfg0_value[63] is 0, and pmpcfg0_value[60:59] is not 2'b01");

property pmp_updt_pmpaddr4_1_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
         pmp_updt_pmpaddr4 == (pmp_csr_wen[6] && !pmpcfg0_value[39] && !(pmpcfg0_value[47] && (pmpcfg0_value[44:43] == 2'b01)));
endproperty

assert_pmp_updt_pmpaddr4_1_assignment: assert property (pmp_updt_pmpaddr4_1_assignment) else $error("Assertion failed: pmp_updt_pmpaddr4_1 is not assigned correctly when pmp_csr_wen[8] is 1, pmpcfg0_value[55] is 0, pmpcfg0_value[63] is 0, and pmpcfg0_value[60:59] is not 2'b01");

property pmp_updt_pmpaddr5_1_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
         pmp_updt_pmpaddr5 == (pmp_csr_wen[7] && !pmpcfg0_value[47] && !(pmpcfg0_value[55] && (pmpcfg0_value[52:51] == 2'b01)));
endproperty

assert_pmp_updt_pmpaddr5_1_assignment: assert property (pmp_updt_pmpaddr5_1_assignment) else $error("Assertion failed: pmp_updt_pmpaddr5_1 is not assigned correctly when pmp_csr_wen[8] is 1, pmpcfg0_value[55] is 0, pmpcfg0_value[63] is 0, and pmpcfg0_value[60:59] is not 2'b01");

property pmp_updt_pmpaddr6_1_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
         pmp_updt_pmpaddr6 == (pmp_csr_wen[8] && !pmpcfg0_value[55] && !(pmpcfg0_value[63] && (pmpcfg0_value[60:59] == 2'b01)));
endproperty

assert_pmp_updt_pmpaddr6_1_assignment: assert property (pmp_updt_pmpaddr6_1_assignment) else $error("Assertion failed: pmp_updt_pmpaddr6_1 is not assigned correctly when pmp_csr_wen[8] is 1, pmpcfg0_value[55] is 0, pmpcfg0_value[63] is 0, and pmpcfg0_value[60:59] is not 2'b01");

property pmp_updt_pmpaddr7_1_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
         pmp_updt_pmpaddr7 == (pmp_csr_wen[9] && !pmpcfg0_value[63] && !(pmpcfg2_value[7] && (pmpcfg2_value[4:3] == 2'b01)));
endproperty

assert_pmp_updt_pmpaddr7_1_assignment: assert property (pmp_updt_pmpaddr7_1_assignment) else $error("Assertion failed: pmp_updt_pmpaddr7_1 is not assigned correctly when pmp_csr_wen[8] is 1, pmpcfg0_value[55] is 0, pmpcfg0_value[63] is 0, and pmpcfg0_value[60:59] is not 2'b01");

property pmp_updt_pmpaddr4_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (pmp_csr_wen[6] == 1 && pmpcfg0_value[39] == 0 && pmpcfg0_value[47] == 0 && pmpcfg0_value[44:43] != 2'b01) |-> (pmp_updt_pmpaddr4 == 1);
endproperty

assert_pmp_updt_pmpaddr4_assignment: assert property (pmp_updt_pmpaddr4_assignment) else $error("Assertion failed: pmp_updt_pmpaddr4 is not assigned correctly when pmp_csr_wen[6] is 1, pmpcfg0_value[39] is 0, pmpcfg0_value[47] is 0, and pmpcfg0_value[44:43] is not 2'b01");



property p_pmp_updt_pmpaddr6_blocking_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        pmp_csr_wen[8] == 0 |-> pmp_updt_pmpaddr6 == 0;
endproperty

assert_p_pmp_updt_pmpaddr6_blocking_assignment: assert property (p_pmp_updt_pmpaddr6_blocking_assignment) else $error("Assertion failed: When pmp_csr_wen[8] is 0, pmp_updt_pmpaddr6 should also be 0");

property pmp_updt_pmpaddr6_blocking_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (pmp_csr_wen[8] == 1 && pmpcfg0_value[55] == 1) |-> (pmp_updt_pmpaddr6 == 0);
endproperty

assert_pmp_updt_pmpaddr6_blocking_assignment: assert property (pmp_updt_pmpaddr6_blocking_assignment) else $error("Assertion failed: pmp_updt_pmpaddr6 should be 0 when pmp_csr_wen[8] and pmpcfg0_value[55] are both 1");



property pmp_updt_pmpaddr4_blocking_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (pmp_csr_wen[6] == 1 && pmpcfg0_value[39] == 1 && pmpcfg0_value[47] == 0 && pmpcfg0_value[44:43] != 2'b01) |-> (pmp_updt_pmpaddr4 == 0);
endproperty

assert_pmp_updt_pmpaddr4_blocking_assignment: assert property (pmp_updt_pmpaddr4_blocking_assignment) else $error("Assertion failed: pmp_updt_pmpaddr4 should be 0 when pmp_csr_wen[6] is 1, pmpcfg0_value[39] is 1, pmpcfg0_value[47] is 0, and pmpcfg0_value[44:43] is not 2'b01");


property p_pmpaddr4_value_reset;
    @(posedge cpuclk) disable iff (cpurst_b == 1)
        cpurst_b == 0 |-> ##1 pmpaddr4_value == {ADDR_WIDTH-1{1'b0}};
endproperty

assert_p_pmpaddr4_value_reset: assert property (p_pmpaddr4_value_reset) else $error("Assertion failed: pmpaddr4_value is not reset to zero after cpurst_b is deasserted");

property pmp_updt_pmpaddr3_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (pmp_csr_wen[5] == 1 && pmpcfg0_value[31] == 0 && pmpcfg0_value[36:35] != 2'b01) |-> (pmp_updt_pmpaddr3 == 1);
endproperty

assert_pmp_updt_pmpaddr3_assignment: assert property (pmp_updt_pmpaddr3_assignment) else $error("Assertion failed: pmp_updt_pmpaddr3 is not assigned correctly when pmp_csr_wen[5] is 1, pmpcfg0_value[31] is 0, and pmpcfg0_value[36:35] is not 2'b01");

property p_pmpaddr4_value_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (cpurst_b == 1 && pmp_csr_wen[6] && !pmpcfg0_value[39] && !(pmpcfg0_value[47] && (pmpcfg0_value[44:43] == 2'b01))) |-> ##1 pmpaddr4_value == $past(cp0_pmp_wdata[ADDR_WIDTH+8:9]);
endproperty

assert_p_pmpaddr4_value_assignment: assert property (p_pmpaddr4_value_assignment) else $error("Assertion failed: pmpaddr4_value does not match the past value of cp0_pmp_wdata[ADDR_WIDTH+8:9] after one clock cycle");

property pmp_updt_pmp7cfg_assignment_1;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (pmp_csr_wen[0] == 1 && pmp7cfg_lock == 0) |-> (pmp_updt_pmp7cfg == 1);
endproperty

assert_pmp_updt_pmp7cfg_assignment_1: assert property (pmp_updt_pmp7cfg_assignment_1) else $error("Assertion failed: pmp_updt_pmp7cfg does not reflect the correct state when pmp_csr_wen[0] is 1 and pmp7cfg_lock is 0");



property p_pmp_updt_pmpaddr3_blocking_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        pmp_csr_wen[5] == 0 |-> pmp_updt_pmpaddr3 == 0;
endproperty

assert_p_pmp_updt_pmpaddr3_blocking_assignment: assert property (p_pmp_updt_pmpaddr3_blocking_assignment) else $error("Assertion failed: pmp_updt_pmpaddr3 should be 0 when pmp_csr_wen[5] is 0");



property pmp_updt_pmp6cfg_assignment_1;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (pmp_csr_wen[0] == 1 && pmp6cfg_lock == 0) |-> (pmp_updt_pmp6cfg == 1);
endproperty

assert_pmp_updt_pmp6cfg_assignment_1: assert property (pmp_updt_pmp6cfg_assignment_1) else $error("Assertion failed: pmp_updt_pmp6cfg does not reflect the correct state when pmp_csr_wen[0] is 1 and pmp6cfg_lock is 0");

property p_pmpaddr4_value_retention;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (cpurst_b == 1 && pmp_updt_pmpaddr4 == 0) |-> ##1 pmpaddr4_value == $past(pmpaddr4_value);
endproperty

assert_p_pmpaddr4_value_retention: assert property (p_pmpaddr4_value_retention) else $error("Assertion failed: pmpaddr4_value does not retain its value when cpurst_b is 1 and pmp_updt_pmpaddr4 is 0");



property pmp_updt_pmp7cfg_assignment_2;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        1 |-> (pmp_updt_pmp7cfg == (pmp_csr_wen[0] && !pmp7cfg_lock));
endproperty

assert_pmp_updt_pmp7cfg_assignment_2: assert property (pmp_updt_pmp7cfg_assignment_2) else $error("Assertion failed: pmp_updt_pmp7cfg does not reflect the correct state when pmp_csr_wen[0] is 0 and pmp7cfg_lock is 0");



property pmp_updt_pmpaddr3_blocking_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (pmp_csr_wen[5] == 1 && pmpcfg0_value[31] == 1) |-> (pmp_updt_pmpaddr3 == 0);
endproperty

assert_pmp_updt_pmpaddr3_blocking_assignment: assert property (pmp_updt_pmpaddr3_blocking_assignment) else $error("Assertion failed: pmp_updt_pmpaddr3 should be 0 when pmp_csr_wen[5] and pmpcfg0_value[31] are both 1");



property pmp_updt_pmp6cfg_assignment_2;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        1 |-> (pmp_updt_pmp6cfg == (pmp_csr_wen[0] && !pmp6cfg_lock));
endproperty

assert_pmp_updt_pmp6cfg_assignment_2: assert property (pmp_updt_pmp6cfg_assignment_2) else $error("Assertion failed: pmp_updt_pmp6cfg does not reflect the correct state when pmp_csr_wen[0] is 0 and pmp6cfg_lock is 0");



property pmp_updt_pmpaddr0_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (pmp_csr_wen[2] == 1 && pmpcfg0_value[7] == 0 && pmpcfg0_value[15] == 0 && pmpcfg0_value[12:11] != 2'b01) |-> (pmp_updt_pmpaddr0 == 1);
endproperty

assert_pmp_updt_pmpaddr0_assignment: assert property (pmp_updt_pmpaddr0_assignment) else $error("Assertion failed: pmp_updt_pmpaddr0 is not assigned correctly when pmp_csr_wen[2] is 1, pmpcfg0_value[7] is 0, pmpcfg0_value[15] is 0, and pmpcfg0_value[12:11] is not 2'b01");



property p_pmp_updt_pmpaddr0_blocking_assign;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        pmp_csr_wen[2] == 0 |-> pmp_updt_pmpaddr0 == 0;
endproperty

assert_p_pmp_updt_pmpaddr0_blocking_assign: assert property (p_pmp_updt_pmpaddr0_blocking_assign) else $error("Assertion failed: When pmp_csr_wen[2] is 0, pmp_updt_pmpaddr0 should also be 0");



property pmp_updt_pmp6cfg_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (pmp_csr_wen[0] == 1 && pmp6cfg_lock == 1) |-> (pmp_updt_pmp6cfg == 0);
endproperty

assert_pmp_updt_pmp6cfg_assignment: assert property (pmp_updt_pmp6cfg_assignment) else $error("Assertion failed: pmp_updt_pmp6cfg does not reflect the correct state when pmp_csr_wen[0] is 1 and pmp6cfg_lock is 1");



property p_pmp_updt_pmp1cfg;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        1 |-> (pmp_updt_pmp1cfg == (pmp_csr_wen[0] && !pmp1cfg_lock));
endproperty

assert_p_pmp_updt_pmp1cfg: assert property (p_pmp_updt_pmp1cfg) else $error("Assertion failed: pmp_updt_pmp1cfg signal is not set to 1 when pmp_csr_wen[0] is 1 and pmp1cfg_lock is 0");



property p_pmp_updt_pmpaddr0_blocking_assign_zero;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (pmp_csr_wen[2] == 1 && pmpcfg0_value[7] == 1) |-> (pmp_updt_pmpaddr0 == 0);
endproperty

assert_p_pmp_updt_pmpaddr0_blocking_assign_zero: assert property (p_pmp_updt_pmpaddr0_blocking_assign_zero) else $error("Assertion failed: pmp_updt_pmpaddr0 should be 0 when pmp_csr_wen[2] and pmpcfg0_value[7] are both 1");


property pmp_updt_pmp5cfg_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        1 |-> (pmp_updt_pmp5cfg == (pmp_csr_wen[0] && !pmp5cfg_lock));
endproperty

assert_pmp_updt_pmp5cfg_assignment: assert property (pmp_updt_pmp5cfg_assignment) else $error("Assertion failed: pmp_updt_pmp5cfg does not reflect the correct state when pmp_csr_wen[0] is 1 and pmp5cfg_lock is 0");


property p_pmpaddr7_value_assignment_1;
    @(posedge cpuclk) disable iff (cpurst_b == 1)
        cpurst_b == 0 |-> ##1 pmpaddr7_value == {ADDR_WIDTH{1'b0}};
endproperty

assert_p_pmpaddr7_value_assignment_1: assert property (p_pmpaddr7_value_assignment_1) else $error("Assertion failed: pmpaddr7_value is not assigned to zero after cpurst_b is deasserted");



property p_pmp_updt_pmp5cfg_blocking_assign_zero;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (pmp_csr_wen[0] == 1 && pmp5cfg_lock == 1) |-> (pmp_updt_pmp5cfg == 0);
endproperty

assert_p_pmp_updt_pmp5cfg_blocking_assign_zero: assert property (p_pmp_updt_pmp5cfg_blocking_assign_zero) else $error("Assertion failed: pmp_updt_pmp5cfg should be 0 when pmp_csr_wen[0] is 1 and pmp5cfg_lock is 1");



property p_pmpaddr0_value_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 1)
        cpurst_b == 0 |-> ##1 pmpaddr0_value == {ADDR_WIDTH{1'b0}};
endproperty

assert_p_pmpaddr0_value_assignment: assert property (p_pmpaddr0_value_assignment) else $error("Assertion failed: pmpaddr0_value is not assigned to zero after cpurst_b is deasserted");


property p_pmpaddr0_value_assignment_2;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (cpurst_b == 1 && pmp_updt_pmpaddr0 == 1) |-> ##1 pmpaddr0_value == $past(cp0_pmp_wdata[ADDR_WIDTH+8:9]);
endproperty


property p_pmpaddr0_value_pmp_updt_pmpaddr0_2;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (cpurst_b == 1 && pmp_csr_wen[2]) && (!pmpcfg0_value[7]) && (!pmpcfg0_value[15] ||(pmpcfg0_value[12:11] != 2'b01))|-> ##1 pmpaddr0_value == $past(cp0_pmp_wdata[ADDR_WIDTH+8:9]);
endproperty

assert_p_pmpaddr0_value_pmp_updt_pmpaddr0_2: assert property (p_pmpaddr0_value_pmp_updt_pmpaddr0_2) else $error("Assertion failed: pmpaddr0_value does not match the past value of cp0_pmp_wdata[ADDR_WIDTH+8:9] after one clock cycle");

property p_pmpaddr7_value_retention;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (cpurst_b == 1 && pmp_updt_pmpaddr7 == 0) |-> ##1 pmpaddr7_value == $past(pmpaddr7_value);
endproperty

assert_p_pmpaddr7_value_retention: assert property (p_pmpaddr7_value_retention) else $error("Assertion failed: pmpaddr7_value does not retain its value when cpurst_b is 1 and pmp_updt_pmpaddr7 is 0");


property p_pmpaddr7_value_retention_2;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (cpurst_b == 1 && pmp_csr_wen[9] && !pmpcfg0_value[63] && !(pmpcfg2_value[7] && (pmpcfg2_value[4:3] == 2'b01))) |-> ##1 pmpaddr7_value == $past(cp0_pmp_wdata[ADDR_WIDTH+8:9]);
endproperty

assert_p_pmpaddr7_value_retention_2: assert property (p_pmpaddr7_value_retention_2) else $error("Assertion failed: pmpaddr7_value does not retain its value when cpurst_b is 1 and pmp_updt_pmpaddr7 is 0");


property pmp_updt_pmp4cfg_assignment_1;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        1 |-> (pmp_updt_pmp4cfg == (pmp_csr_wen[0] && !pmp4cfg_lock));
endproperty

assert_pmp_updt_pmp4cfg_assignment_1: assert property (pmp_updt_pmp4cfg_assignment_1) else $error("Assertion failed: pmp_updt_pmp4cfg does not reflect the correct state when pmp_csr_wen[0] is 1 and pmp4cfg_lock is 0");



property p_pmpaddr0_value_retention;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (cpurst_b == 1 && pmp_updt_pmpaddr0 == 0) |-> ##1 pmpaddr0_value == $past(pmpaddr0_value);
endproperty

assert_p_pmpaddr0_value_retention: assert property (p_pmpaddr0_value_retention) else $error("Assertion failed: pmpaddr0_value does not retain its value when cpurst_b is 1 and pmp_updt_pmpaddr0 is 0");


property p_pmpaddr2_value_reset;
    @(posedge cpuclk) disable iff (cpurst_b == 1)
        cpurst_b == 0 |-> ##1 pmpaddr2_value == {ADDR_WIDTH{1'b0}};
endproperty

assert_p_pmpaddr2_value_reset: assert property (p_pmpaddr2_value_reset) else $error("Assertion failed: pmpaddr2_value is not reset to zero after cpurst_b is deasserted");

property pmp_updt_pmp4cfg_assignment_2;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (pmp_csr_wen[0] == 0 && pmp4cfg_lock == 0) |-> (pmp_updt_pmp4cfg == 0);
endproperty

assert_pmp_updt_pmp4cfg_assignment_2: assert property (pmp_updt_pmp4cfg_assignment_2) else $error("Assertion failed: pmp_updt_pmp4cfg does not reflect the correct state when pmp_csr_wen[0] is 0 and pmp4cfg_lock is 0");


property p_pmpaddr2_value_assignment_1;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (cpurst_b == 1 && pmp_csr_wen[4] && !pmpcfg0_value[23] && !(pmpcfg0_value[31] && (pmpcfg0_value[28:27] == 2'b01))) |-> ##1 pmpaddr2_value == $past(cp0_pmp_wdata[ADDR_WIDTH+8:9]);
endproperty

assert_p_pmpaddr2_value_assignment_1: assert property (p_pmpaddr2_value_assignment_1) else $error("Assertion failed: pmpaddr2_value does not match the past value of cp0_pmp_wdata[ADDR_WIDTH+8:9] after one clock cycle");



property pmp_updt_pmp4cfg_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (pmp_csr_wen[0] == 1 && pmp4cfg_lock == 1) |-> (pmp_updt_pmp4cfg == 0);
endproperty

assert_pmp_updt_pmp4cfg_assignment: assert property (pmp_updt_pmp4cfg_assignment) else $error("Assertion failed: pmp_updt_pmp4cfg does not reflect the correct state when pmp_csr_wen[0] is 1 and pmp4cfg_lock is 1");


property p_pmpaddr2_value_retention;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (cpurst_b == 1 && pmp_updt_pmpaddr2 == 0) |-> ##1 pmpaddr2_value == $past(pmpaddr2_value);
endproperty

assert_p_pmpaddr2_value_retention: assert property (p_pmpaddr2_value_retention) else $error("Assertion failed: pmpaddr2_value does not retain its value when cpurst_b is 1 and pmp_updt_pmpaddr2 is 0");


property p_pmpaddr2_value_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 1)
        (cpurst_b == 0 && $past(cpurst_b) == 1) |-> ##1 pmpaddr2_value == {ADDR_WIDTH{1'b0}};
endproperty

assert_p_pmpaddr2_value_assignment: assert property (p_pmpaddr2_value_assignment) else $error("Assertion failed: pmpaddr2_value is not assigned to zero after cpurst_b transitions from 1 to 0");




property p_pmp_cp0_data_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        pmp_csr_sel[0] == 1 |-> pmp_cp0_data[63:0] == pmpcfg0_value[63:0];
endproperty

assert_p_pmp_cp0_data_assignment: assert property (p_pmp_cp0_data_assignment) else $error("Assertion failed: pmp_cp0_data does not match pmpcfg0_value when pmp_csr_sel[0] is 1");

property p_pmp_cp0_data_assignment_1;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        pmp_csr_sel[0] == 0 |-> pmp_cp0_data[63:0] == 0;
endproperty

assert_p_pmp_cp0_data_assignment_1: assert property (p_pmp_cp0_data_assignment_1) else $error("Assertion failed: pmp_cp0_data does not match pmpcfg0_value when pmp_csr_sel[0] is 1");


property pmp_updt_pmpaddr2_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (pmp_csr_wen[4] == 1 && pmpcfg0_value[23] == 0 && pmpcfg0_value[31] == 0 && pmpcfg0_value[28:27] != 2'b01) |-> (pmp_updt_pmpaddr2 == 1);
endproperty

assert_pmp_updt_pmpaddr2_assignment: assert property (pmp_updt_pmpaddr2_assignment) else $error("Assertion failed: pmp_updt_pmpaddr2 is not assigned correctly when pmp_csr_wen[4] is 1, pmpcfg0_value[23] is 0, pmpcfg0_value[31] is 0, and pmpcfg0_value[28:27] is not 2'b01");


property p_pmp_updt_pmpaddr2_blocking_assignment_1;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        pmp_csr_wen[4] == 0 |-> pmp_updt_pmpaddr2 == 0;
endproperty

assert_p_pmp_updt_pmpaddr2_blocking_assignment_1: assert property (p_pmp_updt_pmpaddr2_blocking_assignment_1) else $error("Assertion failed: When pmp_csr_wen[4] is 0, pmp_updt_pmpaddr2 should also be 0");


property p_pmpcfg0_value_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (pmp7cfg_lock == 1 && pmp7cfg_addr_mode[1:0] == 2'b01 && pmp7cfg_executeable == 1 && pmp7cfg_writable == 0 && pmp7cfg_readable == 1 && pmp6cfg_lock == 0 && pmp6cfg_addr_mode[1:0] == 2'b10 && pmp6cfg_executeable == 0 && pmp6cfg_writable == 1 && pmp6cfg_readable == 0 && pmp5cfg_lock == 1 && pmp5cfg_addr_mode[1:0] == 2'b11 && pmp5cfg_executeable == 0 && pmp5cfg_writable == 0 && pmp5cfg_readable == 1 && pmp4cfg_lock == 0 && pmp4cfg_addr_mode[1:0] == 2'b00 && pmp4cfg_executeable == 1 && pmp4cfg_writable == 1 && pmp4cfg_readable == 0) |->
        (pmpcfg0_value[63:32] == {pmp7cfg_lock, 2'b0, pmp7cfg_addr_mode[1:0], pmp7cfg_executeable, pmp7cfg_writable, pmp7cfg_readable, pmp6cfg_lock, 2'b0, pmp6cfg_addr_mode[1:0], pmp6cfg_executeable, pmp6cfg_writable, pmp6cfg_readable, pmp5cfg_lock, 2'b0, pmp5cfg_addr_mode[1:0], pmp5cfg_executeable, pmp5cfg_writable, pmp5cfg_readable, pmp4cfg_lock, 2'b0, pmp4cfg_addr_mode[1:0], pmp4cfg_executeable, pmp4cfg_writable, pmp4cfg_readable});
endproperty

assert_p_pmpcfg0_value_assignment: assert property (p_pmpcfg0_value_assignment) else $error("Assertion failed: pmpcfg0_value[63:32] does not match the expected value based on the given conditions.");

property p_pmpcfg0_value_assignment_31to0;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
      1 |-> (pmpcfg0_value[31:0] == {pmp3cfg_lock,2'b0,pmp3cfg_addr_mode[1:0],pmp3cfg_executeable,pmp3cfg_writable,pmp3cfg_readable,
                              pmp2cfg_lock,2'b0,pmp2cfg_addr_mode[1:0],pmp2cfg_executeable,pmp2cfg_writable,pmp2cfg_readable,
                              pmp1cfg_lock,2'b0,pmp1cfg_addr_mode[1:0],pmp1cfg_executeable,pmp1cfg_writable,pmp1cfg_readable,
                              pmp0cfg_lock,2'b0,pmp0cfg_addr_mode[1:0],pmp0cfg_executeable,pmp0cfg_writable,pmp0cfg_readable});
endproperty

assert_p_pmpcfg0_value_assignment_31to0: assert property (p_pmpcfg0_value_assignment_31to0) else $error("Assertion failed: pmpcfg0_value[63:32]_31to0 does not match the expected value based on the given conditions.");

property p_pmpcfg0_value_assignment_63to32;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
      1 |-> (pmpcfg0_value[63:32] == {pmp7cfg_lock,2'b0,pmp7cfg_addr_mode[1:0],pmp7cfg_executeable,pmp7cfg_writable,pmp7cfg_readable,
                              pmp6cfg_lock,2'b0,pmp6cfg_addr_mode[1:0],pmp6cfg_executeable,pmp6cfg_writable,pmp6cfg_readable,
                              pmp5cfg_lock,2'b0,pmp5cfg_addr_mode[1:0],pmp5cfg_executeable,pmp5cfg_writable,pmp5cfg_readable,
                              pmp4cfg_lock,2'b0,pmp4cfg_addr_mode[1:0],pmp4cfg_executeable,pmp4cfg_writable,pmp4cfg_readable});
endproperty

assert_p_pmpcfg0_value_assignment_63to32: assert property (p_pmpcfg0_value_assignment_63to32) else $error("Assertion failed: pmpcfg0_value[63:32]_63to32 does not match the expected value based on the given conditions.");

property p_pmp_updt_pmpaddr2_blocking_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (pmp_csr_wen[4] == 1 && pmpcfg0_value[23] == 1) |-> (pmp_updt_pmpaddr2 == 0);
endproperty

assert_p_pmp_updt_pmpaddr2_blocking_assignment: assert property (p_pmp_updt_pmpaddr2_blocking_assignment) else $error("Assertion failed: pmp_updt_pmpaddr2 should be 0 when pmp_csr_wen[4] and pmpcfg0_value[23] are both 1");



property p_pmpaddr1_value_reset;
    @(posedge cpuclk) disable iff (cpurst_b == 1)
        cpurst_b == 0 |-> ##1 pmpaddr1_value == {ADDR_WIDTH{1'b0}};
endproperty

assert_p_pmpaddr1_value_reset: assert property (p_pmpaddr1_value_reset) else $error("Assertion failed: pmpaddr1_value is not reset to zero after cpurst_b is deasserted");


property p_pmpaddr1_value_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (cpurst_b == 1 && pmp_csr_wen[3] && (!pmpcfg0_value[15]) && (!pmpcfg0_value[23]|| pmpcfg0_value[20:19] != 2'b01)) |-> ##1 pmpaddr1_value == $past(cp0_pmp_wdata[ADDR_WIDTH+8:9]);
endproperty

assert_p_pmpaddr1_value_assignment: assert property (p_pmpaddr1_value_assignment) else $error("Assertion failed: pmpaddr1_value does not match the past value of cp0_pmp_wdata[ADDR_WIDTH+8:9] after one clock cycle");



property p_pmpaddr1_value_retention;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (cpurst_b == 1 && pmp_updt_pmpaddr1 == 0) |-> ##1 pmpaddr1_value == $past(pmpaddr1_value);
endproperty

assert_p_pmpaddr1_value_retention: assert property (p_pmpaddr1_value_retention) else $error("Assertion failed: pmpaddr1_value does not retain its value when cpurst_b is 1 and pmp_updt_pmpaddr1 is 0");

property pmp_updt_pmp2cfg_assignment_1;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        1 |-> (pmp_updt_pmp2cfg == (pmp_csr_wen[0] & (!pmp2cfg_lock)));
endproperty

assert_pmp_updt_pmp2cfg_assignment_1: assert property (pmp_updt_pmp2cfg_assignment_1) else $error("Assertion failed: pmp_updt_pmp2cfg does not reflect the correct state when pmp_csr_wen[0] is 1 and pmp2cfg_lock is 0");



property p_pmpaddr3_value_assignment_2;
    @(posedge cpuclk) disable iff (cpurst_b == 1)
        cpurst_b == 0 |-> ##1 pmpaddr3_value == 0;
endproperty

assert_p_pmpaddr3_value_assignment_2: assert property (p_pmpaddr3_value_assignment_2) else $error("Assertion failed: pmpaddr3_value is not 0 one cycle after cpurst_b is 0");



property p_pmpaddr5_value_assignment_2;
    @(posedge cpuclk) disable iff (cpurst_b == 1)
        cpurst_b == 0 |-> ##1 pmpaddr5_value == 0;
endproperty

assert_p_pmpaddr5_value_assignment_2: assert property (p_pmpaddr5_value_assignment_2) else $error("Assertion failed: pmpaddr5_value is not 0 one cycle after cpurst_b is 0");

property pmp_updt_pmp2cfg_assignment_2;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (pmp_csr_wen[0] == 1 && pmp2cfg_lock == 0) |-> (pmp_updt_pmp2cfg == 1);
endproperty

assert_pmp_updt_pmp2cfg_assignment_2: assert property (pmp_updt_pmp2cfg_assignment_2) else $error("Assertion failed: pmp_updt_pmp2cfg does not reflect the correct state when pmp_csr_wen[0] is 0 and pmp2cfg_lock is 0");



property pmp_updt_pmpaddr5_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (pmp_csr_wen[7] == 1 && pmpcfg0_value[47] == 0 && pmpcfg0_value[55] == 0 && pmpcfg0_value[52:51] != 2'b01) |-> (pmp_updt_pmpaddr5 == 1);
endproperty

assert_pmp_updt_pmpaddr5_assignment: assert property (pmp_updt_pmpaddr5_assignment) else $error("Assertion failed: pmp_updt_pmpaddr5 is not assigned correctly when pmp_csr_wen[7] is 1, pmpcfg0_value[47] is 0, pmpcfg0_value[55] is 0, and pmpcfg0_value[52:51] is not 2'b01");



property p_pmpaddr3_value_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (cpurst_b == 1 && pmp_csr_wen[5] && !pmpcfg0_value[31] && !(pmpcfg0_value[39] && (pmpcfg0_value[36:35] == 2'b01))) |-> ##1 pmpaddr3_value == $past(cp0_pmp_wdata[ADDR_WIDTH+8:9]);
endproperty

assert_p_pmpaddr3_value_assignment: assert property (p_pmpaddr3_value_assignment) else $error("Assertion failed: pmpaddr3_value does not match the past value of cp0_pmp_wdata[ADDR_WIDTH+8:9] after one clock cycle");





property p_pmpaddr5_value_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (cpurst_b == 1 && pmp_csr_wen[7] && !pmpcfg0_value[47] && !(pmpcfg0_value[55] && (pmpcfg0_value[52:51] == 2'b01))) |-> ##1 pmpaddr5_value == $past(cp0_pmp_wdata[ADDR_WIDTH+8:9]);
endproperty

assert_p_pmpaddr5_value_assignment: assert property (p_pmpaddr5_value_assignment) else $error("Assertion failed: pmpaddr5_value does not match the past value of cp0_pmp_wdata[ADDR_WIDTH+8:9] after one clock cycle");

property p_pmp_updt_pmpaddr5_blocking_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        pmp_csr_wen[7] == 0 |-> pmp_updt_pmpaddr5 == 0;
endproperty

assert_p_pmp_updt_pmpaddr5_blocking_assignment: assert property (p_pmp_updt_pmpaddr5_blocking_assignment) else $error("Assertion failed: When pmp_csr_wen[7] is 0, pmp_updt_pmpaddr5 should also be 0");



property pmp_updt_pmp2cfg_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (pmp_csr_wen[0] == 1 && pmp2cfg_lock == 1) |-> (pmp_updt_pmp2cfg == 0);
endproperty

assert_pmp_updt_pmp2cfg_assignment: assert property (pmp_updt_pmp2cfg_assignment) else $error("Assertion failed: pmp_updt_pmp2cfg does not reflect the correct state when pmp_csr_wen[0] is 1 and pmp2cfg_lock is 1");



property pmp_updt_pmpaddr1_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (pmp_csr_wen[3] == 1 && pmpcfg0_value[15] == 0 && pmpcfg0_value[23] == 0 && pmpcfg0_value[20:19] != 2'b01) |-> (pmp_updt_pmpaddr1 == 1);
endproperty

assert_pmp_updt_pmpaddr1_assignment: assert property (pmp_updt_pmpaddr1_assignment) else $error("Assertion failed: pmp_updt_pmpaddr1 is not assigned correctly when pmp_csr_wen[3] is 1, pmpcfg0_value[15] is 0, pmpcfg0_value[23] is 0, and pmpcfg0_value[20:19] is not 2'b01");



property p_pmpaddr3_value_retention;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        (cpurst_b == 1 && pmp_updt_pmpaddr3 == 0) |-> ##1 pmpaddr3_value == $past(pmpaddr3_value);
endproperty

assert_p_pmpaddr3_value_retention: assert property (p_pmpaddr3_value_retention) else $error("Assertion failed: pmpaddr3_value does not retain its value when cpurst_b is 1 and pmp_updt_pmpaddr3 is 0");

property p_pmp0cfg_readable_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 1)
        cpurst_b == 0 |-> ##1 pmp0cfg_readable == 0 && pmp0cfg_writable==0 && pmp0cfg_executeable==0 && pmp0cfg_addr_mode[1:0]==0 && pmp0cfg_lock ==0;
endproperty

assert_p_pmp0cfg_readable_assignment: assert property (p_pmp0cfg_readable_assignment) else $error("Assertion failed: pmp0cfg_readable is not 0 one cycle after cpurst_b is 0");

property p_pmp0cfg_writable_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        cpurst_b == 1 && pmp_updt_pmp0cfg==1 |-> ##1 pmp0cfg_readable == $past(cp0_pmp_wdata[0]) && pmp0cfg_writable== $past(cp0_pmp_wdata[1]) &&
        pmp0cfg_executeable== $past(cp0_pmp_wdata[2]) && pmp0cfg_addr_mode[1:0]==$past(cp0_pmp_wdata[4:3]) && pmp0cfg_lock ==$past(cp0_pmp_wdata[7]);
endproperty

assert_p_pmp0cfg_writable_assignment: assert property (p_pmp0cfg_writable_assignment) else $error("Assertion failed: pmp0cfg_writable is not 0 one cycle after cpurst_b is 0");

property p_pmp0cfg_executeable_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        cpurst_b == 1 && pmp_updt_pmp0cfg==0 |-> ##1 pmp0cfg_readable == $past(pmp0cfg_readable) && pmp0cfg_writable== $past(pmp0cfg_writable) &&
        pmp0cfg_executeable== $past(pmp0cfg_executeable) && pmp0cfg_addr_mode[1:0]==$past(pmp0cfg_addr_mode[1:0]) && pmp0cfg_lock ==$past(pmp0cfg_lock);
endproperty

assert_p_pmp0cfg_executeable_assignment: assert property (p_pmp0cfg_executeable_assignment) else $error("Assertion failed: pmp0cfg_executeable is not 0 one cycle after cpurst_b is 0");


property p_pmp1cfg_readable_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 1)
        cpurst_b == 0 |-> ##1 pmp1cfg_readable == 0 && pmp1cfg_writable == 0 && pmp1cfg_executeable == 0 && pmp1cfg_addr_mode[1:0] == 0 && pmp1cfg_lock == 0;
endproperty

assert_p_pmp1cfg_readable_assignment: assert property (p_pmp1cfg_readable_assignment) else $error("Assertion failed: pmp1cfg_readable is not 0 one cycle after cpurst_b is 0");

property p_pmp1cfg_writable_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        cpurst_b == 1 && pmp_updt_pmp1cfg==1 |-> ##1 pmp1cfg_readable == $past(cp0_pmp_wdata[8]) && pmp1cfg_writable == $past(cp0_pmp_wdata[9]) &&
        pmp1cfg_executeable == $past(cp0_pmp_wdata[10]) && pmp1cfg_addr_mode[1:0] == $past(cp0_pmp_wdata[12:11]) && pmp1cfg_lock == $past(cp0_pmp_wdata[15]);
endproperty

assert_p_pmp1cfg_writable_assignment: assert property (p_pmp1cfg_writable_assignment) else $error("Assertion failed: pmp1cfg_writable is not 0 one cycle after cpurst_b is 0");

property p_pmp1cfg_executeable_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        cpurst_b == 1 && pmp_updt_pmp1cfg==0 |-> ##1 pmp1cfg_readable == $past(pmp1cfg_readable) && pmp1cfg_writable == $past(pmp1cfg_writable) &&
        pmp1cfg_executeable == $past(pmp1cfg_executeable) && pmp1cfg_addr_mode[1:0] == $past(pmp1cfg_addr_mode[1:0]) && pmp1cfg_lock == $past(pmp1cfg_lock);
endproperty

assert_p_pmp1cfg_executeable_assignment: assert property (p_pmp1cfg_executeable_assignment) else $error("Assertion failed: pmp1cfg_executeable is not 0 one cycle after cpurst_b is 0");

property p_pmp2cfg_readable_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 1)
        cpurst_b == 0 |-> ##1 pmp2cfg_readable == 0 && pmp2cfg_writable==0 && pmp2cfg_executeable==0 && pmp2cfg_addr_mode[1:0]==0 && pmp2cfg_lock ==0;
endproperty

assert_p_pmp2cfg_readable_assignment: assert property (p_pmp2cfg_readable_assignment) else $error("Assertion failed: pmp2cfg_readable is not 0 one cycle after cpurst_b is 0");

property p_pmp2cfg_writable_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        cpurst_b == 1 && pmp_updt_pmp2cfg==1 |-> ##1 pmp2cfg_readable == $past(cp0_pmp_wdata[16]) && pmp2cfg_writable== $past(cp0_pmp_wdata[17]) &&
        pmp2cfg_executeable== $past(cp0_pmp_wdata[18]) && pmp2cfg_addr_mode[1:0]==$past(cp0_pmp_wdata[20:19]) && pmp2cfg_lock ==$past(cp0_pmp_wdata[23]);
endproperty

assert_p_pmp2cfg_writable_assignment: assert property (p_pmp2cfg_writable_assignment) else $error("Assertion failed: pmp2cfg_writable is not 0 one cycle after cpurst_b is 0");

property p_pmp2cfg_executeable_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        cpurst_b == 1 && pmp_updt_pmp2cfg==0 |-> ##1 pmp2cfg_readable == $past(pmp2cfg_readable) && pmp2cfg_writable== $past(pmp2cfg_writable) &&
        pmp2cfg_executeable== $past(pmp2cfg_executeable) && pmp2cfg_addr_mode[1:0]==$past(pmp2cfg_addr_mode[1:0]) && pmp2cfg_lock ==$past(pmp2cfg_lock);
endproperty

assert_p_pmp2cfg_executeable_assignment: assert property (p_pmp2cfg_executeable_assignment) else $error("Assertion failed: pmp2cfg_executeable is not 0 one cycle after cpurst_b is 0");

property p_pmp3cfg_readable_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 1)
        cpurst_b == 0 |-> ##1 pmp3cfg_readable == 0 && pmp3cfg_writable==0 && pmp3cfg_executeable==0 && pmp3cfg_addr_mode[1:0]==0 && pmp3cfg_lock ==0;
endproperty

assert_p_pmp3cfg_readable_assignment: assert property (p_pmp3cfg_readable_assignment) else $error("Assertion failed: pmp3cfg_readable is not 0 one cycle after cpurst_b is 0");

property p_pmp3cfg_writable_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        cpurst_b == 1 && pmp_updt_pmp3cfg==1 |-> ##1 pmp3cfg_readable == $past(cp0_pmp_wdata[24]) && pmp3cfg_writable== $past(cp0_pmp_wdata[25]) &&
        pmp3cfg_executeable== $past(cp0_pmp_wdata[26]) && pmp3cfg_addr_mode[1:0]==$past(cp0_pmp_wdata[28:27]) && pmp3cfg_lock ==$past(cp0_pmp_wdata[31]);
endproperty

assert_p_pmp3cfg_writable_assignment: assert property (p_pmp3cfg_writable_assignment) else $error("Assertion failed: pmp3cfg_writable is not 0 one cycle after cpurst_b is 0");

property p_pmp3cfg_executeable_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        cpurst_b == 1 && pmp_updt_pmp3cfg==0 |-> ##1 pmp3cfg_readable == $past(pmp3cfg_readable) && pmp3cfg_writable== $past(pmp3cfg_writable) &&
        pmp3cfg_executeable== $past(pmp3cfg_executeable) && pmp3cfg_addr_mode[1:0]==$past(pmp3cfg_addr_mode[1:0]) && pmp3cfg_lock ==$past(pmp3cfg_lock);
endproperty

assert_p_pmp3cfg_executeable_assignment: assert property (p_pmp3cfg_executeable_assignment) else $error("Assertion failed: pmp3cfg_executeable is not 0 one cycle after cpurst_b is 0");

property p_pmp4cfg_readable_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 1)
        cpurst_b == 0 |-> ##1 pmp4cfg_readable == 0 && pmp4cfg_writable==0 && pmp4cfg_executeable==0 && pmp4cfg_addr_mode[1:0]==0 && pmp4cfg_lock ==0;
endproperty

assert_p_pmp4cfg_readable_assignment: assert property (p_pmp4cfg_readable_assignment) else $error("Assertion failed: pmp4cfg_readable is not 0 one cycle after cpurst_b is 0");

property p_pmp4cfg_writable_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        cpurst_b == 1 && pmp_updt_pmp4cfg==1 |-> ##1 pmp4cfg_readable == $past(cp0_pmp_wdata[32]) && pmp4cfg_writable== $past(cp0_pmp_wdata[33]) &&
        pmp4cfg_executeable== $past(cp0_pmp_wdata[34]) && pmp4cfg_addr_mode[1:0]==$past(cp0_pmp_wdata[36:35]) && pmp4cfg_lock ==$past(cp0_pmp_wdata[39]);
endproperty

assert_p_pmp4cfg_writable_assignment: assert property (p_pmp4cfg_writable_assignment) else $error("Assertion failed: pmp4cfg_writable is not 0 one cycle after cpurst_b is 0");

property p_pmp4cfg_executeable_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        cpurst_b == 1 && pmp_updt_pmp4cfg==0 |-> ##1 pmp4cfg_readable == $past(pmp4cfg_readable) && pmp4cfg_writable== $past(pmp4cfg_writable) &&
        pmp4cfg_executeable== $past(pmp4cfg_executeable) && pmp4cfg_addr_mode[1:0]==$past(pmp4cfg_addr_mode[1:0]) && pmp4cfg_lock ==$past(pmp4cfg_lock);
endproperty

assert_p_pmp4cfg_executeable_assignment: assert property (p_pmp4cfg_executeable_assignment) else $error("Assertion failed: pmp4cfg_executeable is not 0 one cycle after cpurst_b is 0");

property p_pmp5cfg_readable_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 1)
        cpurst_b == 0 |-> ##1 pmp5cfg_readable == 0 && pmp5cfg_writable==0 && pmp5cfg_executeable==0 && pmp5cfg_addr_mode[1:0]==0 && pmp5cfg_lock ==0;
endproperty

assert_p_pmp5cfg_readable_assignment: assert property (p_pmp5cfg_readable_assignment) else $error("Assertion failed: pmp5cfg_readable is not 0 one cycle after cpurst_b is 0");

property p_pmp5cfg_writable_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        cpurst_b == 1 && pmp_updt_pmp5cfg==1 |-> ##1 pmp5cfg_readable == $past(cp0_pmp_wdata[40]) && pmp5cfg_writable== $past(cp0_pmp_wdata[41]) &&
        pmp5cfg_executeable== $past(cp0_pmp_wdata[42]) && pmp5cfg_addr_mode[1:0]==$past(cp0_pmp_wdata[44:43]) && pmp5cfg_lock ==$past(cp0_pmp_wdata[47]);
endproperty

assert_p_pmp5cfg_writable_assignment: assert property (p_pmp5cfg_writable_assignment) else $error("Assertion failed: pmp5cfg_writable is not 0 one cycle after cpurst_b is 0");

property p_pmp5cfg_executeable_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        cpurst_b == 1 && pmp_updt_pmp5cfg==0 |-> ##1 pmp5cfg_readable == $past(pmp5cfg_readable) && pmp5cfg_writable== $past(pmp5cfg_writable) &&
        pmp5cfg_executeable== $past(pmp5cfg_executeable) && pmp5cfg_addr_mode[1:0]==$past(pmp5cfg_addr_mode[1:0]) && pmp5cfg_lock ==$past(pmp5cfg_lock);
endproperty

assert_p_pmp5cfg_executeable_assignment: assert property (p_pmp5cfg_executeable_assignment) else $error("Assertion failed: pmp5cfg_executeable is not 0 one cycle after cpurst_b is 0");

property p_pmp6cfg_readable_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 1)
        cpurst_b == 0 |-> ##1 pmp6cfg_readable == 0 && pmp6cfg_writable==0 && pmp6cfg_executeable==0 && pmp6cfg_addr_mode[1:0]==0 && pmp6cfg_lock ==0;
endproperty

assert_p_pmp6cfg_readable_assignment: assert property (p_pmp6cfg_readable_assignment) else $error("Assertion failed: pmp6cfg_readable is not 0 one cycle after cpurst_b is 0");

property p_pmp6cfg_writable_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        cpurst_b == 1 && pmp_updt_pmp6cfg==1 |-> ##1 pmp6cfg_readable == $past(cp0_pmp_wdata[48]) && pmp6cfg_writable== $past(cp0_pmp_wdata[49]) &&
        pmp6cfg_executeable== $past(cp0_pmp_wdata[50]) && pmp6cfg_addr_mode[1:0]==$past(cp0_pmp_wdata[52:51]) && pmp6cfg_lock ==$past(cp0_pmp_wdata[55]);
endproperty

assert_p_pmp6cfg_writable_assignment: assert property (p_pmp6cfg_writable_assignment) else $error("Assertion failed: pmp6cfg_writable is not 0 one cycle after cpurst_b is 0");

property p_pmp6cfg_executeable_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        cpurst_b == 1 && pmp_updt_pmp6cfg==0 |-> ##1 pmp6cfg_readable == $past(pmp6cfg_readable) && pmp6cfg_writable== $past(pmp6cfg_writable) &&
        pmp6cfg_executeable== $past(pmp6cfg_executeable) && pmp6cfg_addr_mode[1:0]==$past(pmp6cfg_addr_mode[1:0]) && pmp6cfg_lock ==$past(pmp6cfg_lock);
endproperty

assert_p_pmp6cfg_executeable_assignment: assert property (p_pmp6cfg_executeable_assignment) else $error("Assertion failed: pmp6cfg_executeable is not 0 one cycle after cpurst_b is 0");

property p_pmp7cfg_readable_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 1)
        cpurst_b == 0 |-> ##1 pmp7cfg_readable == 0 && pmp7cfg_writable==0 && pmp7cfg_executeable==0 && pmp7cfg_addr_mode[1:0]==0 && pmp7cfg_lock ==0;
endproperty

assert_p_pmp7cfg_readable_assignment: assert property (p_pmp7cfg_readable_assignment) else $error("Assertion failed: pmp7cfg_readable is not 0 one cycle after cpurst_b is 0");

property p_pmp7cfg_writable_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        cpurst_b == 1 && pmp_updt_pmp7cfg==1 |-> ##1 pmp7cfg_readable == $past(cp0_pmp_wdata[56]) && pmp7cfg_writable== $past(cp0_pmp_wdata[57]) &&
        pmp7cfg_executeable== $past(cp0_pmp_wdata[58]) && pmp7cfg_addr_mode[1:0]==$past(cp0_pmp_wdata[60:59]) && pmp7cfg_lock ==$past(cp0_pmp_wdata[63]);
endproperty

assert_p_pmp7cfg_writable_assignment: assert property (p_pmp7cfg_writable_assignment) else $error("Assertion failed: pmp7cfg_writable is not 0 one cycle after cpurst_b is 0");

property p_pmp7cfg_executeable_assignment;
    @(posedge cpuclk) disable iff (cpurst_b == 0)
        cpurst_b == 1 && pmp_updt_pmp7cfg==0 |-> ##1 pmp7cfg_readable == $past(pmp7cfg_readable) && pmp7cfg_writable== $past(pmp7cfg_writable) &&
        pmp7cfg_executeable== $past(pmp7cfg_executeable) && pmp7cfg_addr_mode[1:0]==$past(pmp7cfg_addr_mode[1:0]) && pmp7cfg_lock ==$past(pmp7cfg_lock);
endproperty

assert_p_pmp7cfg_executeable_assignment: assert property (p_pmp7cfg_executeable_assignment) else $error("Assertion failed: pmp7cfg_executeable is not 0 one cycle after cpurst_b is 0");

endmodule`
