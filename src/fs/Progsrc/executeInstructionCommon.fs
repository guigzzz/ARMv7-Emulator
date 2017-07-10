namespace HLP
open common
module executeInstructionCommon =


//------------------------- Lizhang Created ------------------------------
    /// check conditional
    let matchCond (cond,input) = 
        let (regs:int array, memory, insLst, flags, _) = input
        match cond with
        |NoCond -> true
        |EQ when flags.Z = true -> true
        |NE when flags.Z = false -> true
        |CS|HS when flags.C = true -> true
        |CC|LO when flags.C = false -> true
        |MI when flags.N = true -> true
        |PL when flags.N = false -> true
        |VS when flags.V = true -> true
        |VC when flags.V = false -> true
        |HI when flags.C = true && flags.Z = false -> true
        |LS when flags.C = false || flags.Z = true -> true
        |GE when flags.N = flags.V -> true
        |LT when flags.N <> flags.V -> true
        |GT when flags.Z = false && flags.N = flags.V -> true
        |LE when flags.Z = true || flags.N <> flags.V -> true
        |AL -> true
        |_ -> false


//------------------------- Wuzheng Contributed / Tianci Created ------------------------------
    let newflag (myN, myZ, myC, myV) = {N = myN; Z = myZ; C = myC; V = myV} 

    let checkMSB value = 
        match int((uint32 value) &&& uint32 (0x80000000)) with
        |0 -> 0
        |_ -> 1

    let ALUsetflag (fo, so, setf) input ins=
        let ((regs: int array), ms, insLst,flags,_) = input
        let checkN = 
            match ins with
            |"SUB" -> if fo - so < 0 then true else false
            |"ADD" -> if (int32 (fo + so)) < 0 then true else false
            |"ADC" -> if (int32 (fo + so + 1)) < 0 then true else false
            |"SBC" -> if fo - (so+1) < 0 then true else false
            |"MOV" -> if fo < 0 then true else false
            |"AND" -> if (fo &&& so) < 0 then true else false
            |"ORR" -> if (fo ||| so) < 0 then true else false
            |"EOR" -> if (fo ^^^ so) < 0 then true else false
            |"BIC" -> if (fo &&& (~~~so)) < 0 then true else false
            | _ -> failwith "not implemented yet"
        let checkZ = 
            match ins with
            |"SUB" -> if fo - so = 0 then true else false
            |"ADD" -> if fo + so = 0 then true else false
            |"ADC" -> if fo + so + 1 = 0 then true else false
            |"SBC" -> if fo - (so+1) = 0 then true else false
            |"MOV" -> if fo = 0 then true else false
            |"AND" -> if (fo &&& so) = 0 then true else false
            |"ORR" -> if (fo ||| so) = 0 then true else false
            |"EOR" -> if (fo ^^^ so) = 0 then true else false
            |"BIC" -> if (fo &&& (~~~so)) = 0 then true else false
            | _ -> failwith "not implemented yet"
        let checkV = 
            match ins with
            |"SUB" -> if ((checkMSB (int32 fo)) <> (checkMSB(int32 so)) && (checkMSB(int32 fo)) <> (checkMSB (int32 (fo-so)))) then true else false
            |"ADD" -> if ((checkMSB (int32 fo)) = (checkMSB(int32 so)) && (checkMSB(int32 fo)) <> (checkMSB (int32 (fo+so)))) then true else false
            |"SBC" -> if ((checkMSB (int32 fo)) <> (checkMSB(int32 (so))) && (checkMSB(int32 fo)) <> (checkMSB (int32(int32 (fo) - int32(so+1))))) then true else false
            |"ADC" -> if ((checkMSB (int32 fo)) = (checkMSB(int32 so)) && (checkMSB(int32 fo)) <> (checkMSB (int32 (fo+so+1)))) then true else false
            |"MOV" -> flags.V
            |"AND" -> flags.V
            |"ORR" -> flags.V
            |"EOR" -> flags.V
            |"BIC" -> flags.V
            |_ -> failwith "not implemented"
        let checkC = 
            match ins with
            |"SUB" -> 
                match ((checkMSB (int32 fo)) = (checkMSB (int32 so))), (int32 fo >= int32 so) with
                |true, true -> true
                |false, false -> true
                |_,_ -> false
            |"SBC" -> 
                match ((checkMSB (int32 fo)) = (checkMSB (int32(int32(so) + 1)))), (int32 fo >= int32(int32 (so) + 1)), (so = -1)  with
                |true, true, false -> true
                |false, false, false -> true
                |_,_,_ -> false
            |"ADD" ->
                match ((checkMSB (int32 fo)) = (checkMSB (int32 so))), checkMSB (int32 fo), checkMSB (int32(int32 fo + int32 so)) with
                |true, 0, _-> false
                |true, 1, _ -> true
                |false, _, 0 -> true
                |false, _, 1 -> false
                |_,_,_ -> failwith "not implemented"
            |"ADC" ->
                match ((checkMSB (int32 fo)) = (checkMSB (int32 so))), checkMSB (int32 fo), checkMSB (int32(int32 fo + int32 so + 1)) with
                |true, 0, _-> false
                |true, 1, _ -> true
                |false, _, 0 -> true
                |false, _, 1 -> false
                |_,_,_ -> failwith "not implemented"
            |"MOV" -> flags.C
            |"AND" -> flags.C
            |"ORR" -> flags.C
            |"EOR" -> flags.C
            |"BIC" -> flags.C
            |_ -> failwith "not implemented"
        match setf with
        |Flag -> newflag(checkN, checkZ, checkC, checkV)
        |NoFlag -> flags



    let rec checkifmore1 value counter =
        match value &&& 1 with
        |1 -> false
        |0 -> if counter < 32 then checkifmore1 (value >>> 1) (counter+1) else true
        |_ -> false

//------------------------- Lizhang modified /Tianci ------------------------------
    let checkimmediatevalue value =
        let rec check v =
            if v &&& 1 = 1 then
                match checkifmore1 (v >>> 8) 0 with
                |true -> true
                |false -> false
            else check (v >>> 1)
            
        match value >= -256 || value <= 255 with
        |true -> None
        |false ->
            match check value with
            |true -> None
            |false -> Some ("value must be able to be shifted using a 8 bit value")

// ---------------------- Lizhang modified/ Tianci modified / Wuzheng Created -----------------------
    /// handles shift operand
    let shifter reg1 shift flags (regs:int array) =
        match shift with
        | LSL(shift) ->
            match shift with
            |Reg(shift) -> 
                //extract the least significant 8 bits of the register to be shifted (only these bits are used for shifts)
                let s = int32 (uint8 (regs.[shift]))
                match s>31 with
                |true -> 0 , None
                |false -> int32 ((uint32 regs.[reg1]) <<< s) , None
            |Value(shift) -> 
                let errormsg = checkimmediatevalue shift
                match shift > 31 with
                |true -> 0, errormsg
                |false -> int32 ((uint32 regs.[reg1]) <<< shift) , errormsg
            |_ -> 0, Some "Shift value must either be a register or a value"
        | LSR(shift) ->
            match shift with
            |Reg(shift) -> 
                //extract the least significant 8 bits of the register to be shifted (only these bits are used for shifts)
                let s = int32 (uint8 (regs.[shift]))
                match s > 31 with
                |true -> 0, None
                |false -> int32 ((uint32 regs.[reg1]) >>> s), None
            |Value(shift) -> 
                let errormsg = checkimmediatevalue shift
                match shift > 31 with
                |true -> 0, errormsg
                |false -> int32 ((uint32 regs.[reg1]) >>> shift), errormsg
            |_ -> 0, Some "Shift value must either be a register or a value"
        | ASR(shift) ->
            match shift with
            |Reg(shift) -> 
                //extract the least significant 8 bits of the register to be shifted (only these bits are used for shifts)
                let s = int32 (uint8 (regs.[shift]))
                match s> 31 && regs.[reg1] < 0 with
                |true -> -1,None
                |false ->
                    match s> 31 && regs.[reg1] >= 0 with 
                    |true -> 0,None
                    |false -> (regs.[reg1] >>> s), None
            |Value(shift) -> 
                let errormsg = checkimmediatevalue shift
                match shift > 31 && regs.[reg1] < 0 with
                |true -> -1,errormsg
                |false ->
                    match shift > 31 && regs.[reg1] >= 0 with
                    |true -> 0,errormsg
                    |false -> (regs.[reg1] >>> shift), errormsg
            |_ -> 0, Some "Shift value must either be a register or a value"
        | ROR(shift) -> 
            match shift with
            |Reg(shift) -> 
                //extract the least significant 8 bits of the register to be shifted (only these bits are used for shifts)
                let s = int32 (uint8 (regs.[shift])) % 32
                let out = int32 (((uint32 regs.[reg1])<<<(32-s))|||((uint32 regs.[reg1])>>>s))
                out, None
            |Value(shift) -> 
                let errormsg = checkimmediatevalue shift
                let s = shift % 32
                let out = int32 (((uint32 regs.[reg1])<<<(32-s))|||((uint32 regs.[reg1])>>> s))
                out, errormsg
            |_ -> 0, Some "Shift value must either be a register or a value"
        | RRX -> //int ((uint32 regs.[reg1])>>>1) 
            // assign value to dest register. Note that bit 31 is set to carry bit before execution
            match flags.C with
            |true -> 
                let out = int ((uint32 regs.[reg1])>>>1) + int (1<<<31)
                out, None
            |false -> 
                let out = int ((uint32 regs.[reg1])>>>1)
                out, None
        | NoShift -> regs.[reg1], None
        


//------------------------- tianci Modified / Lizhang Created ------------------------------
    let movUpdateCFlag (setf:Setflags, shift:Shift, dest, op1) input =
        let (regs:int array, memory, insLst, flags, _) = input
        let updateC = 
            match shift with 
            |RRX when (regs.[op1] &&& 1 = 1) -> true
            |RRX -> false
            |LSL(Reg(x)) -> 
                //extract the least significant 8 bits of op2 (only these bits are used for shifts)
                let s = int32 (uint8 (regs.[x]))
                if s>32 then false 
                else if s = 0 then flags.C 
                else if int32 (regs.[op1]<<<(s-1)) < 0 then true 
                else false
            |LSL(Value(s)) ->
                if s>32 then false 
                else if s <= 0 then flags.C
                else if int32 (regs.[op1]<<<(s-1)) < 0 then true 
                else false
            |LSR(Reg(x)) ->
                //extract the least significant 8 bits of op2 (only these bits are used for shifts)
                let s = int32 (uint8 (regs.[x]))
                if s>32 then false 
                else if s = 0 then flags.C 
                else if int32 (regs.[op1]>>>(s-1)) &&& 1 = 1 then true 
                else false
            |LSR(Value(s))  ->
                if s>32 then false 
                else if s <= 0 then flags.C
                else if int32 (regs.[op1]>>>(s-1)) &&& 1 = 1 then true 
                else false
            |ASR(Reg(x)) ->
                //extract the least significant 8 bits of op2 (only these bits are used for shifts)
                let s = int32 (uint8 (regs.[x]))
                if s>32 && regs.[op1] < 0 then true
                else if s>32 && regs.[op1] >= 0 then false
                else if s = 0 then flags.C 
                else if int32 (regs.[op1]>>>(s-1)) &&& 1 = 1 then true 
                else false
            |ASR(Value(s)) ->
                if s>32 && regs.[op1] < 0 then true
                else if s>32 && regs.[op1] >= 0 then false
                else if s <= 0 then flags.C
                else if int32 (regs.[op1]>>>(s-1)) &&& 1 = 1 then true 
                else false
            |ROR(Reg(x)) -> 
                //extract the least significant 8 bits of op2 (only these bits are used for shifts)
                let s = int32 (uint8 (regs.[x])) % 32 //note here shift is in the range 0-31
                if s = 0 then flags.C
                else if int32 (regs.[op1]>>>(s-1)) &&& 1 = 1 then true 
                else false 
            |ROR(Value(x)) -> 
                let s = x % 32
                if s = 0 then flags.C 
                else if int32 (regs.[op1]>>>(s-1)) &&& 1 = 1 then true 
                else false
            |NoShift -> flags.C // -------------- note, This is the rule followed by VISUAL 
        match setf with
        |Flag -> {flags with C = updateC}
        |NoFlag -> flags