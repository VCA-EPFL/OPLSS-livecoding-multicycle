import FIFO::*;
import SpecialFIFOs::*;
import RVUtil::*;
import Vector::*;
import BRAM::*;

typedef enum {Fetch, Decode, Execute, Writeback} StateProcessor deriving(Eq, Bits);

function Bool isMMIO(Bit#(32) addr);
	return (addr == 32'hf000fff0 || addr == 32'hf000fff8);
endfunction

module mkmulticycle(Empty);
    BRAM1Port#(Bit#(16), Bit#(32)) mem <- mkMemory();
	Reg#(Bit#(32)) pc <- mkReg(0);
	Vector#(32, Reg#(Bit#(32))) rf <- replicateM(mkReg(0));
	Reg#(StateProcessor) current_state <- mkReg(Fetch);

	// microarchitectural state
	Reg#(DecodedInst) dInst <- mkReg(?);
	Reg#(Bit#(32)) rv1 <- mkReg(0);
	Reg#(Bit#(32)) rv2 <- mkReg(0);
	Reg#(Bit#(32)) rd <- mkReg(0);

	rule fetch if (current_state == Fetch);
		let req = BRAMRequest{
				write: False,
				address: truncate(pc >> 2),
				datain: ?,
				responseOnWrite: False};
		mem.portA.request.put(req);
		current_state <= Decode;
	endrule

	rule decode if (current_state == Decode);
		let instr <- mem.portA.response.get();
		let decodedInstr = decodeInst(instr);
		let rs1_idx = getInstFields(instr).rs1;
		let rs2_idx = getInstFields(instr).rs2;
		let rs1 = (rs1_idx == 0 ? 0 : rf[rs1_idx]);
		let rs2 = (rs2_idx == 0 ? 0 : rf[rs2_idx]);
		dInst <= decodedInstr;
		rv1 <= rs1;
		rv2 <= rs2;
		current_state <= Execute;
	endrule

	rule execute if (current_state == Execute);
		let imm = getImmediate(dInst);
		let data = execALU32(dInst.inst, rv1, rv2, imm, pc);
		let addr =  rv1 + imm;
		if (isMemoryInst(dInst)) begin 
			data = rv2;
			let type_mem = (dInst.inst[5] == 1);
			let req = BRAMRequest{
				write: type_mem,
				address: truncate(addr>>2),
				datain: data,
				responseOnWrite: True};
			if (isMMIO(addr)) begin 
				if (addr == 'hf000_fff0) $fwrite(stdout, "%c", data[7:0]);
				if (addr == 'hf000_fff8) begin 
					$display("TERMINATE");
					$finish;
				end
			end else begin 
				mem.portA.request.put(req);
			end
	    end
		else begin 
			if (isControlInst(dInst)) begin 
				data = pc + 4;
			end
	 
	    end
		let nextPc = execControl32(dInst.inst, rv1, rv2, imm, pc);
		pc <= nextPc.nextPC;
		rd <= data;
		current_state <= Writeback;
	endrule
	

	rule writeback if( current_state == Writeback);
		let data = rd;
		let addr = rv1 + getImmediate(dInst);
		if (isMemoryInst(dInst) && !isMMIO(addr)) begin 
			let resp <- mem.portA.response.get();
			data = resp;
		end

		// use [data] that correspond to either coming from memory, or coming from
		// previous stage
		if (dInst.valid_rd) begin 
			let rd_idx = getInstFields(dInst.inst).rd;
			if (rd_idx != 0) rf[rd_idx] <= data;
		end
		current_state <= Fetch;

		endrule

endmodule
