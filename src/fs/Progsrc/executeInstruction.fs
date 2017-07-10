namespace HLP
open common
open executeInstructionCommon

module executeInstruction =

    let executeInstruction (input:Machinestate) = 

    // --------------------------------------------------- Beginning ofLogic Shifts ------------------------------------------------
    // --------------------------------------------------- Beginning ofLogic Shifts ------------------------------------------------
    // --------------------------------------------------- Created by Lizhang ------------------------------------------------
        /// updates flags after logic shift instructions
        let LogicShiftUpdateFlags (dest:int32,operand:uint32, shift, setF:Setflags,flags,ins:string) =
            let checkN = if dest < 0 then true else false
            let checkZ = if dest =  0 then true else false
            let checkC =
                match ins with
                |"LSL" -> 
                    if shift>32 then false
                    else if shift = 0 then flags.C 
                    else if int32 (operand<<<(shift-1)) < 0  then true else false
                |"LSR" ->
                    if shift>32 then false 
                    else if shift = 0 then flags.C
                    else if int32 (operand>>>(shift-1)) &&& 1 = 1 then true else false
                |"ASR" ->
                    if shift>32 && int32(operand) < 0 then true 
                    else if shift>32 && int32(operand) >= 0 then false
                    else if shift = 0 then flags.C
                    else if int32 (operand>>>(shift-1)) &&& 1 = 1 then true else false
                |"ROR" -> 
                    let shift = shift % 32
                    if shift = 0 then flags.C 
                    else if int32 (operand>>>(shift-1)) &&& 1 = 1 then true else false //note here shift is in the range 0-31
                |"RRX" -> if (int32 operand) &&& 1 = 1 then true else false
                |_ -> failwith "instruction doesn't exist"
            match setF with
            |Flag -> newflag (checkN, checkZ, checkC, false)
            |NoFlag -> flags

        ///LSL, LSR, ASR, ROR
        let LogicShiftInsts (cond, setf, dest, op1, op2) input inst =
            let (regs:int array, memory, insLst, flags, errormsg) = input
            match matchCond (cond,input) with 
            | true -> 
                match dest with
                | Reg (dest) when dest = 15 || dest = 13 -> 
                    let errormsg  = Some ("R15 or R13 cannot be destination")
                    (regs,memory,insLst,flags, errormsg)
                | Reg (dest) -> 
                    match op1,op2 with
                    |Reg (op1), Reg(op2) when op1 = 13 || op2 = 13 || op1 = 15 || op2 = 15 -> 
                        let errormsg  = Some ("R15 or R13 cannot be op1 or op2")
                        (regs,memory,insLst,flags, errormsg)
                    |Reg (op1), Reg(op2) ->
                        //extract the least significant 8 bits of op2 (only these bits are used for shifts)
                        let shift = int32 (uint8 (regs.[op2]))
                        // avoid the case that dest and op1 are the same register
                        let op1ValueBeforeExe = uint32 regs.[op1]
                        // shifting
                        match inst with
                        |"LSL" ->
                            if shift > 31 then regs.[dest] <- 0
                            else regs.[dest] <-  int32 ((uint32 regs.[op1]) <<< shift)
                        |"LSR" ->
                            if shift> 31 then regs.[dest] <- 0
                            else regs.[dest] <- int32 ((uint32 regs.[op1]) >>> shift)
                        |"ASR" -> 
                            if shift > 31 && regs.[op1] < 0 then regs.[dest] <- -1
                            else if shift > 31 && regs.[op1] >= 0 then regs.[dest] <- 0
                            else regs.[dest] <- (regs.[op1] >>> shift)
                        |"ROR" -> 
                            let shift = shift % 32
                            regs.[dest] <- int32 (((uint32 regs.[op1])<<<(32-shift))|||((uint32 regs.[op1])>>>shift))
                        
                        let newflags = LogicShiftUpdateFlags (regs.[dest],op1ValueBeforeExe,shift,setf,flags, inst)
                        regs.[15] <- regs.[15] + 4
                        (regs,memory,insLst,newflags,errormsg)    
                        
                    |Reg (op1), Value(op2) ->
                        op2 |> checkimmediatevalue 
                        // avoid the case that dest and op1 are the same register
                        let op1ValueBeforeExe = uint32 regs.[op1]
                        // shifting
                        match inst with
                        |"LSL" ->
                            if op2 > 31 then regs.[dest] <- 0
                            else regs.[dest] <-  int32 ((uint32 regs.[op1]) <<< op2)
                        |"LSR" ->
                            if op2 > 31 then regs.[dest] <- 0
                            else regs.[dest] <- int32 ((uint32 regs.[op1]) >>> op2)
                        |"ASR" ->
                            if op2 > 31 && regs.[op1] >= 0 then regs.[dest] <- 0
                            else if op2 > 31 && regs.[op1] < 0 then regs.[dest] <- -1
                            else regs.[dest] <- (regs.[op1] >>> op2)
                        |"ROR" ->
                            let op2 = op2 % 32
                            regs.[dest] <- int32 (((uint32 regs.[op1])<<<(32-op2))|||((uint32 regs.[op1])>>> op2))

                        let newflags = LogicShiftUpdateFlags (regs.[dest], op1ValueBeforeExe, op2, setf, flags, inst)
                        regs.[15] <- regs.[15] + 4
                        (regs,memory,insLst,newflags,errormsg)

                    |_ -> failwith "Invalid operands"
                | _ -> failwith "destination has to be a register"
            | false -> 
                regs.[15] <- regs.[15] + 4
                (regs,memory,insLst,flags, errormsg)

        ///RRX
        let LogicShiftRRX (cond, setf, dest, op1) input =
            let (regs:int array, memory, insLst, flags,errormsg) = input
            match matchCond (cond,input) with 
            | true -> 
                match dest,op1 with
                | Reg (dest), Reg (op1) when dest = 13 || op1 = 13 -> 
                    let errormsg = Some ("R13 cannot be destination or op1")
                    (regs,memory,insLst,flags,errormsg)
                | Reg (dest), Reg (op1) ->
                    // avoid the case that dest and op1 are the same register
                    let op1ValueBeforeExe = uint32 regs.[op1]
                    // assign value to dest register. Note that bit 31 is set to carry bit before execution
                    match flags.C with
                    |true -> regs.[dest] <- int ((uint32 regs.[op1])>>>1) + int (1<<<31)
                    |false -> regs.[dest] <- int ((uint32 regs.[op1])>>>1)
                    /// check and updateFlags flags
                    let newflags = LogicShiftUpdateFlags (regs.[dest],op1ValueBeforeExe,1,setf,flags,"ROR")
                    // update pc
                    regs.[15] <- regs.[15] + 4
                    (regs,memory,insLst,newflags,errormsg)
                | _ -> 
                    let errormsg = Some ("Both destination and op1 has to be a register")
                    (regs,memory,insLst,flags,errormsg)
            | false -> 
                regs.[15] <- regs.[15] + 4
                (regs,memory,insLst,flags,errormsg)
    // -------------------------------------------------- End of Logic Shifts ---------------------------------------------------
    // -------------------------------------------------- End of Logic Shifts ---------------------------------------------------
    
    // ------------------------------------------------------- mov / mvn -------------------------------------------------------------       
    // ------------------------------------------------------- mov / mvn -------------------------------------------------------------       
    // ---------------------------------------------------- Coded by Lizhang -------------------------------------------------------------       

        ///execute move instruction
        let exeMOVorMVN (cond,setf,dest,op1,shift) input ins =
            let (regs:int array, memory, insLst, flags, errormsg) = input
            match dest with
            | Reg(dest) -> 
                match op1 with
                | Reg(op1) when (setf = Flag) && (dest = 13 || dest = 15 || op1 = 13 || op1 = 15) ->
                    let errormsg = Some ("when R13 (SP) or R15 (PC) are used, set flag cannot be used")
                    (regs,memory,insLst,flags,errormsg)
                | Reg(op1) when (setf = NoFlag) && (dest = 13 || dest = 15 || op1 = 13 || op1 = 15) && (shift <> NoShift) ->
                    let errormsg = Some ("when R13 (SP) or R15 (PC) are used, the second op must be a reg without a shift")
                    (regs,memory,insLst,flags,errormsg)
                | Reg(op1) ->
                    // ---------------------- set C flag before exe ------------------------
                    let newflags1 = movUpdateCFlag (setf,shift,dest,op1) input
                    let mutable error = errormsg
                    match ins with
                    |"MOV" -> 
                        let value, errormsg = shifter op1 shift flags regs
                        match errormsg with
                        |Some(_) -> error <- errormsg
                        |None -> regs.[dest] <- value
                    |"MVN" -> 
                        let value, errormsg = shifter op1 shift flags regs
                        match errormsg with
                        |Some(_) -> error <- errormsg
                        |None -> regs.[dest] <- -value-1 

                    // if destination is PC, then remove bit 0.
                    if dest = 15 then regs.[dest] <- int32 (((uint32 regs.[dest])>>>1)<<<1)
                    // ---------------------- set C flag after exe ------------------------
                    match setf with
                    |Flag ->
                        let updateN = if regs.[dest] < 0 then true else false
                        let updateZ = if regs.[dest] = 0 then true else false
                        let newflags2 = {newflags1 with N = updateN; Z = updateZ}
                        (regs,memory,insLst,newflags2, error)
                    |NoFlag -> (regs,memory,insLst,flags, errormsg)                
                | Value(op1) when shift <> NoShift ->
                    let errormsg = Some ("Syntax error - op1 is a constant, cannot be followed by shift")
                    (regs,memory,insLst,flags, errormsg)
                | Value(op1) ->
                    let errormsg = checkimmediatevalue op1
                    match errormsg with
                    |Some(_) -> (regs,memory,insLst,flags, errormsg)
                    |None ->
                        // -------- execute ---------
                        match ins with
                        |"MOV" -> regs.[dest] <- op1
                        |"MVN" -> regs.[dest] <- -op1-1
                        // if destination is PC, then remove bit 0.
                        if dest = 15 then regs.[dest] <- int32 (((uint32 regs.[dest])>>>1)<<<1)

                        // ------------- set flag after execution -------------------
                        match setf with
                        |Flag -> 
                            let updateN = if regs.[dest] < 0 then true else false
                            let updateZ = if regs.[dest] = 0 then true else false
                            let newflags = {flags with N = updateN; Z = updateZ}
                            (regs,memory,insLst,newflags,errormsg)
                        |NoFlag -> (regs,memory,insLst,flags,errormsg)
                | _ -> 
                    let errormsg = Some ("Incorrect format - Operand1 must be a register or a number")
                    (regs,memory,insLst,flags, errormsg)
            | _ -> 
                let errormsg = Some ("Destination of MOV must be a register")
                (regs,memory,insLst,flags, errormsg)
            
        let movORmvn (cond,setf,dest,op1,shift) input ins = 
            let (regs:int array, memory, insLst, flags, errormsg) = input
            //Execute only when condition match 
            if matchCond (cond,input) then
                regs.[15] <- regs.[15] + 4
                exeMOVorMVN (cond,setf,dest,op1,shift) input ins
            else    
                regs.[15] <- regs.[15] + 4
                (regs, memory, insLst,flags,errormsg) 
            
//  ------------------------------------------------------- End of MOV/MVN -------------------------------------------------------------

//  ------------------------------------------------------- Begining of ALU -------------------------------------------------------------
// ------------------------------------------------------- Created by Tianci/Wuzheng ------------------------------------------------

    // ------------------------------------------------------- add -------------------------------------------------------------
        let executeADD ((regs: int array), reg, x1, fo, so, soAfter, carry, ms, insLst, setf, flags) =
            regs.[reg] <- regs.[x1] + so
            (regs,ms,insLst, (ALUsetflag (fo, so, setf) input "ADD"),None)
  
//    // ------------------------------------------------------- adc -------------------------------------------------------------
//        let executeADC ((regs: int array), reg, x1, fo, so, soAfter, carry, ms, insLst, setf, flags) =
//            regs.[reg] <- regs.[x1] + so + carry
//            (regs,ms,insLst, (ALUsetflag (fo, so + carry, setf) input "ADD"),None)

        let executeADC ((regs: int array), reg, x1, fo, so, soAfter, carry, ms, insLst, setf, flags) =
            regs.[reg] <- regs.[x1] + so + carry
            if flags.C = false then
                (regs,ms,insLst, (ALUsetflag (fo, so, setf) input "ADD"),None)
            else 
                (regs,ms,insLst, (ALUsetflag (fo, so, setf) input "ADC"),None)
            


    // ------------------------------------------------------- SUB -------------------------------------------------------------
        let executeSUB ((regs: int array), reg, x1, fo, so, soAfter, carry, ms, insLst, setf, flags) =
            regs.[reg] <- regs.[x1] - so
            (regs,ms,insLst, (ALUsetflag (fo, so, setf) input "SUB"),None)

     
    // ------------------------------------------------------- SBC -------------------------------------------------------------
        let executeSBC ((regs: int array), reg, x1, fo, so, soAfter, carry, ms, insLst, setf, flags) =
            regs.[reg] <- regs.[x1] - soAfter
            if flags.C = false then
                (regs,ms,insLst, (ALUsetflag (fo, so, setf) input "SBC"), None)
            else 
                (regs,ms,insLst, (ALUsetflag (fo, so, setf) input "SUB"), None)

    // ------------------------------------------------------- RSB -------------------------------------------------------------
        let executeRSB ((regs: int array), reg, x1, fo, so, soAfter, carry, ms, insLst, setf, flags) =
            regs.[reg] <- so - regs.[x1]
            (regs,ms,insLst, (ALUsetflag (so, fo, setf) input "SUB"), None)

    // ------------------------------------------------------- RSC -------------------------------------------------------------
        let executeRSC ((regs: int array), reg, x1, fo, so, soAfter, carry, ms, insLst, setf, flags) =
            regs.[reg] <- soAfter - regs.[x1]
            if flags.C = false then
                (regs,ms,insLst, (ALUsetflag (so, fo, setf) input "SBC"),None)
            else
                (regs,ms,insLst, (ALUsetflag (so, fo, setf) input "SUB"),None)

        let executeAR(setf, dest, op1, op2,shift) input instName =
                let ((regs: int array), ms, insLst,flags, errormsg) = input
                match dest with
                | Reg(reg) ->
                    match op1, op2 with
                    | Reg(x1), Reg(x2) ->
                        let fo = regs.[x1]
                        let carry = if (instName = "SBC" || instName = "ADC") then (if flags.C then 1 else 0) else (if flags.C then 0 else 1)
                        let so,errormsg = (shifter x2 shift flags regs)
                        match errormsg with
                        |Some(_) -> (regs,ms,insLst, flags,errormsg)
                        |None ->
                            let soAfter = (so - carry)
                            match instName with
                            |"RSC" -> executeRSC(regs, reg, x1, fo, so, (so - carry), carry, ms, insLst, setf, flags)
                            |"RSB" -> executeRSB(regs, reg, x1, fo, so, soAfter, carry, ms, insLst, setf, flags)
                            |"SBC" -> executeSBC(regs, reg, x1, fo, so, (so + 1 - carry), carry, ms, insLst, setf, flags)
                            |"SUB" -> executeSUB(regs, reg, x1, fo, so, soAfter, carry, ms, insLst, setf, flags)
                            |"ADC" -> executeADC(regs, reg, x1, fo, so, soAfter, carry, ms, insLst, setf, flags)
                            |"ADD" -> executeADD(regs, reg, x1, fo, so, soAfter, carry, ms, insLst, setf, flags)
                    | Reg(x1), Value(x2) ->
                        let fo = regs.[x1]
                        let carry = if (instName = "SBC" || instName = "ADC") then (if flags.C then 1 else 0) else (if flags.C then 0 else 1)
                        let so = x2
                        let soAfter = (so - carry)
                        match instName with
                        |"RSC" -> executeRSC(regs, reg, x1, fo, so, (so - carry), carry, ms, insLst, setf, flags)
                        |"RSB" -> executeRSB(regs, reg, x1, fo, so, soAfter, carry, ms, insLst, setf, flags)
                        |"SBC" -> executeSBC(regs, reg, x1, fo, so, (so + 1 - carry), carry, ms, insLst, setf, flags)
                        |"SUB" -> executeSUB(regs, reg, x1, fo, so, soAfter, carry, ms, insLst, setf, flags)
                        |"ADC" -> executeADC(regs, reg, x1, fo, so, soAfter, carry, ms, insLst, setf, flags)
                        |"ADD" -> executeADD(regs, reg, x1, fo, so, soAfter, carry, ms, insLst, setf, flags)
                        |_ -> failwithf "not implemented"
                    | _ -> 
                        let errormsg = Some ("Operands are not in the correct format (must be a register or a number)")
                        (regs,ms,insLst,flags, errormsg)
                | _ -> 
                    let errormsg = Some "Destination of BIC must be a register"
                    (regs,ms,insLst,flags, errormsg)

        let ARInst (cond, setf, dest, op1, op2, shift) input instName=
            let ((regs: int array), ms, insLst,flags, errormsg) = input
            if matchCond(cond, input) then
                regs.[15] <- regs.[15] + 4
                executeAR(setf, dest, op1, op2, shift) input instName
            else
                regs.[15] <- regs.[15] + 4
                (regs, ms, insLst,flags,errormsg) 
    
// --------------------------------------------------- Beginning of CMP/CMN/TEQ/TST -------------------------------------------------------------
// ------------------------------------------------------- Created by Wuzheng ------------------------------------------------

// ------------------------------------------------------- CMP -------------------------------------------------------------
        let executeCMP (op1, op2, shift) input =
            let setFlagOnDefault = Flag
            let ((regs: int array), ms, insLst,flags,errormsg) = input
            match op1, op2 with
            | Reg(x1), Reg(x2) ->
                let fo = regs.[x1]
                let so,errormsg = (shifter x2 shift flags regs)
                match errormsg with
                |Some(_) -> (regs,ms,insLst, flags,errormsg)
                |None -> (regs,ms,insLst, (ALUsetflag (fo, so, setFlagOnDefault) input "SUB"),errormsg)
            | Reg(x1), Value(x2) ->
                let fo = regs.[x1]
                let so = x2
                (regs,ms,insLst, (ALUsetflag (fo, so, setFlagOnDefault) input "SUB"),errormsg)
            | _ ->
                let errormsg = Some ("Operands are not in the correct format (must be a register or a number)")
                (regs, ms, insLst,flags, errormsg)  

        let cmp (cond, op1, op2, shift) input =
            let ((regs: int array), ms, insLst,flags, errormsg) = input
            if matchCond(cond, input) then
                regs.[15] <- regs.[15] + 4
                executeCMP(op1, op2, shift) input
            else
                regs.[15] <- regs.[15] + 4
                (regs, ms, insLst,flags, errormsg)  

    // ------------------------------------------------------- CMN -------------------------------------------------------------
        let executeCMN (op1, op2,shift) input =
            let setFlagOnDefault = Flag
            let ((regs: int array), ms, insLst,flags, errormsg) = input
            match op1, op2 with
            | Reg(x1), Reg(x2) when x2 = 13 || x2 = 15 -> 
                let errormsg = Some ("second operand cannot be R13 or R15")
                (regs, ms, insLst,flags, errormsg)  
            | Reg(x1), Reg(x2) ->
                let fo = regs.[x1]
                let so, errormsg = (shifter x2 shift flags regs)
                match errormsg with
                |Some(_) -> (regs,ms,insLst, flags, errormsg)
                |None -> (regs,ms,insLst, (ALUsetflag (fo, so, setFlagOnDefault) input "ADD"),errormsg)
            | Reg(x1), Value(x2) ->
                let fo = regs.[x1]
                let so = x2
                (regs,ms,insLst, (ALUsetflag (fo, so, setFlagOnDefault) input "ADD"),errormsg)
            | _ -> 
                let errormsg = Some ("Operands are not in the correct format (must be a register or a number)")
                (regs, ms, insLst,flags, errormsg)  

        let cmn (cond, op1, op2, shift) input =
            let ((regs: int array), ms, insLst,flags, errormsg) = input
            if matchCond(cond, input) then
                regs.[15] <- regs.[15] + 4
                executeCMN(op1, op2, shift) input
            else
                regs.[15] <- regs.[15] + 4
                (regs, ms, insLst,flags, errormsg)    

    // ------------------------------------------------------- TST --------------------------------------------------------------------------
        let executeTST (op1, op2,shift) input =
            let setFlagOnDefault = Flag
            let ((regs: int array), ms, insLst,flags, errormsg) = input
            match op1, op2 with
            | Reg(x1), Reg(x2) ->
                let newflags1 = movUpdateCFlag (setFlagOnDefault,shift,x1,x2) input
                let fo = regs.[x1]
                let so, errormsg = (shifter x2 shift flags regs)
                match errormsg with
                |Some(_) -> (regs,ms,insLst,flags, errormsg)
                |None ->
                    let tempResult = int32(fo &&& so)
                    let updateN = if tempResult < 0 then true else false
                    let updateZ = if tempResult = 0 then true else false
                    let newflags2 = {newflags1 with N = updateN; Z = updateZ}
                    (regs,ms,insLst,newflags2, errormsg)
            | Reg(x1), Value(x2) ->
                let fo = regs.[x1]
                let so = x2
                (regs,ms,insLst, (ALUsetflag (fo, so, setFlagOnDefault) input "AND"),errormsg)
            | _ -> 
                let errormsg = Some "Operands are not in the correct format (must be a register or a number)"
                (regs, ms, insLst,flags, errormsg)  

        let tst (cond, op1, op2, shift) input =
            let ((regs: int array), ms, insLst,flags, errormsg) = input
            if matchCond(cond, input) then
                regs.[15] <- regs.[15] + 4
                executeTST(op1, op2, shift) input
            else
                regs.[15] <- regs.[15] + 4
                (regs, ms, insLst,flags, errormsg) 

    // ------------------------------------------------------- TEQ ----------------------------------------------------------------------------------- 
        let executeTEQ (op1, op2,shift) input =
            let setFlagOnDefault = Flag
            let ((regs: int array), ms, insLst,flags, errormsg) = input
            match op1, op2 with
            | Reg(x1), Reg(x2) ->
                let newflags1 = movUpdateCFlag (setFlagOnDefault,shift,x1,x2) input
                let fo = regs.[x1]
                let so, errormsg = (shifter x2 shift flags regs)
                match errormsg with
                |Some(_) -> (regs,ms,insLst,flags, errormsg)
                |None -> 
                    let tempResult = int32(fo ^^^ so)
                    let updateN = if tempResult < 0 then true else false
                    let updateZ = if tempResult = 0 then true else false
                    let newflags2 = {newflags1 with N = updateN; Z = updateZ}
                    (regs,ms,insLst,newflags2,errormsg)
            | Reg(x1), Value(x2) ->
                let fo = regs.[x1]
                let so = x2
                (regs,ms,insLst, (ALUsetflag (fo, so, setFlagOnDefault) input "EOR"),errormsg)
            | _ -> 
                let errormsg = Some "Operands are not in the correct format (must be a register or a number)"
                (regs, ms, insLst,flags, errormsg)  

        let teq (cond, op1, op2, shift) input =
            let ((regs: int array), ms, insLst,flags,errormsg) = input
            if matchCond(cond, input) then
                regs.[15] <- regs.[15] + 4
                executeTEQ(op1, op2, shift) input
            else
                regs.[15] <- regs.[15] + 4
                (regs, ms, insLst,flags, errormsg) 

// ------------------------------------------------------- End of CMP/TEQ/CMN/TST ------------------------------------------------

// ----------------------------------------------------- Beginning of BITWISE OPERATOR ---------------------------------------------------
// ------------------------------------------------------- Created by Tianci ------------------------------------------------

        let executeBITWISE(setf, dest, op1, op2,shift) input instName =
                let ((regs: int array), ms, insLst,flags,errormsg) = input
                match dest with
                | Reg(reg) ->
                    match op1, op2 with
                    | Reg(x1), Reg(x2) ->
                        let newflags1 = movUpdateCFlag (setf,shift,dest,x2) input
                        let fo = regs.[x1]
                        let so, errormsg = (shifter x2 shift flags regs)
                        match errormsg with
                        |Some(_) -> (regs,ms,insLst,flags, errormsg)
                        |None ->
                            match instName with
                            |"AND" ->
                                regs.[reg] <- int32(fo &&& so)
                            |"ORR" ->
                                regs.[reg] <- int32(fo ||| so)
                            |"EOR" ->
                                regs.[reg] <- int32(fo ^^^ so)
                            |"BIC" -> 
                                regs.[reg] <- int32(fo &&& (~~~so))
                            |_ -> failwithf "not implemented"
                            match setf with
                            |Flag ->
                                let updateN = if regs.[reg] < 0 then true else false
                                let updateZ = if regs.[reg] = 0 then true else false
                                let newflags2 = {newflags1 with N = updateN; Z = updateZ}
                                (regs,ms,insLst,newflags2,errormsg)
                            |NoFlag -> (regs,ms,insLst,flags,errormsg)
                    | Reg(x1), Value(x2) ->
                        let fo = regs.[x1]
                        let so = x2
                        match instName with
                        |"AND" ->
                                regs.[reg] <- int32(fo &&& so)
                                (regs,ms,insLst, (ALUsetflag (fo, so, setf) input "AND"),errormsg)
                        |"ORR" ->
                                regs.[reg] <- int32(fo ||| so)
                                (regs,ms,insLst, (ALUsetflag (fo, so, setf) input "ORR"),errormsg)
                        |"EOR" ->
                                regs.[reg] <- int32(fo ^^^ so)
                                (regs,ms,insLst, (ALUsetflag (fo, so, setf) input "EOR"),errormsg)
                        |"BIC" -> 
                                regs.[reg] <- int32(fo &&& (~~~so))
                                (regs,ms,insLst, (ALUsetflag (fo, so, setf) input "BIC"),errormsg)
                        |_ -> failwithf "not implemented"
                    | _ -> 
                        let errormsg = Some "Operands are not in the correct format (must be a register or a number)"
                        (regs, ms, insLst,flags, errormsg)  
                | _ -> 
                    let errormsg = Some "Destination of BIC must be a register"
                    (regs, ms, insLst,flags, errormsg)  

        let bitwiseInst (cond, setf, dest, op1, op2, shift) input instName=
            let ((regs: int array), ms, insLst,flags,errormsg) = input
            if matchCond(cond, input) then
                regs.[15] <- regs.[15] + 4
                executeBITWISE(setf, dest, op1, op2, shift) input instName
            else
                regs.[15] <- regs.[15] + 4
                (regs, ms, insLst,flags,errormsg) 

// ------------------------------------------------------- End of Bitwise Operator ------------------------------------------------

// -------------------------------------------------- Beginning of Memory Operations ---------------------------------------------------
    
    // ------------------------------------------------------- LDR /STR -----------------------------------------------------------
        /// get offset value. raise exception if offset is out of the range
        let getOffset (offset,shift) input =
            let (regs, ms, insLst,flags,_) = input 
            /// returns the offset if offset is within the range, else raise exception
            let checkOffset value = 
                match value <= 4095 || value >= -4095 with
                |true -> value, None
                |false -> 0 , Some "offset must be in the range of +4095 and -4095" 

            match offset with
            | Reg(offset) when offset = 13 || offset = 15 -> 0, Some "offset cannot be R13 or R15"
            | Reg(offset) -> 
                let off, errormsg = shifter offset shift flags regs
                match errormsg with
                |Some(_) -> off, errormsg
                |None -> checkOffset off
            | Value(offset) -> checkOffset offset
            | _ -> 0 , Some "offset must be either a number or a register"

        //let isReadFromInstMEM value = if value >=0 && value <= 252 then () else failwith (sprintf "attempting to read word from instruction memory space at address %A" value)
        let isDivisibleBy4 value =  
            match value % 4 = 0 with
            |true -> value,None  
            |false -> value, Some "memory address must be divisible by 4"
    
    //-------------------------------------------------------------LDR--------------------------------------------------------        
        /// loads value from memory to destination register. Updates source register if instructed
        let ldrEXE (dataType,dest,source,offset,shift,idxing) input =
            let (regs:int array, ms, insLst,flags,errormsg) = input 
            
            /// returns updated destination register and source register
            let accessMem =
                 /// load value from memory address
                let loadValue addr = 
                    match ms |> Map.tryFind addr with
                    |Some(v) -> v
                    |None -> 0 // empty
                match offset with
                | Reg(offset) when offset = 13 || offset = 15 -> 
                    let errormsg = Some "Offset cannot be R13 or R15"
                    (regs.[dest], regs.[source],errormsg)
                | Value(offset) when source > 4095 || source < -4095 -> 
                    let errormsg = Some "If the offset is an immediate value, it must be in the range -4095 and 4095"
                    (regs.[dest], regs.[source],errormsg)
                | Reg(_) | Value(_) ->
                    // --------- execution -----------
                    match idxing with
                    |Post ->
                        let addr, errormsg = regs.[source] |> isDivisibleBy4
                        match errormsg with
                        |Some(_) -> (regs.[dest], regs.[source], errormsg)
                        |None ->
                            let updateDest = loadValue addr
                            let offsetValue, errormsg = getOffset (offset, shift) input
                            match errormsg with 
                            |Some(_) -> (regs.[dest], regs.[source],errormsg)
                            |None ->
                                let updateSource = addr + offsetValue
                                (updateDest,updateSource,errormsg)
                    |Pre ->
                        // the value is loaded from the address [base + offset]
                        let offsetValue, errormsg = getOffset (offset, shift) input
                        match errormsg with
                        |Some(_) -> (regs.[dest], regs.[source],errormsg)
                        |None -> 
                            let addr, errormsg = (regs.[source] + offsetValue) |> isDivisibleBy4
                            match errormsg with
                            |Some(_) -> (regs.[dest], regs.[source],errormsg)
                            |None ->    
                                let updateDest = loadValue addr
                                let updateSource = addr
                                (updateDest, updateSource,errormsg)
                    |Immediate -> 
                        let offsetValue, errormsg = getOffset (offset, shift) input
                        match errormsg with
                        |Some(_) -> (regs.[dest], regs.[source],errormsg)
                        |None -> 
                            // the value is loaded from the address [base + offset]
                            let addr, errormsg = (regs.[source] + offsetValue) |> isDivisibleBy4
                            match errormsg with
                            |Some(_) -> (regs.[dest], regs.[source],errormsg)
                            |None ->
                                let updateDest = loadValue addr
                                (updateDest, regs.[source],errormsg)
                | NoReg -> 
                    match idxing with
                    |Post -> 
                        let errormsg = Some "Post-indexing mode must have an offset"
                        (regs.[dest], regs.[source],errormsg)
                    |Pre -> 
                        let errormsg = Some "Pre-indexing mode must have an offset"
                        (regs.[dest], regs.[source],errormsg)
                    |Immediate ->
                        let updateDest = loadValue regs.[source]
                        (updateDest, regs.[source],errormsg)

            match dataType with
                |By -> 
                    let d,s,errormsg = accessMem
                    match errormsg with
                    |Some(_) -> errormsg
                    |None ->
                        regs.[dest] <- int32(uint8(d))
                        regs.[source] <- s
                        errormsg
                |SBy -> Some "Signed Byte data type is not implemented yet, also it's not implemented in Visual"
                |H -> Some "Half word data type is not implemented yet, also not implemented in Visual"
                |SH -> Some "Signed half word data type is not implemented yet, also not implemented in Visual"
                |W -> 
                    let d,s, errormsg = accessMem
                    match errormsg with
                    |Some(_) -> errormsg
                    |None ->
                        regs.[dest] <- d
                        regs.[source] <- s
                        errormsg
                    

    //-------------------------------------------------------------STR--------------------------------------------------------
        /// stores values from dest reg to memory, updates source reg if instructed
        let getSTRNewMEM (dataType,source,dest,offset,shift,idxing) input =
            let (regs:int array, mem:Map<int,int>, insLst,flags, errormsg) = input 
            
            /// returns updated destination register and source register
            let accessMem  =
                match offset with
                | Reg(offset) when offset = 13 || offset = 15 -> 
                    let errormsg = Some "Offset cannot be R13 or R15"
                    (regs.[dest],errormsg)
                | Value(offset) when source > 4095 || source < -4095 -> 
                    let errormsg = Some "If the offset is an immediate value, it must be in the range -4095 and 4095"
                    (regs.[dest],errormsg)
                | Reg(_) | Value(_) ->
                    match idxing with
                    |Post ->
                        // the value is stored to the address [dest]
                        let ofset,errormsg = getOffset (offset, shift) input
                        match errormsg with
                        |Some(_) -> regs.[dest],errormsg
                        |None -> 
                            let addr, errormsg = regs.[dest] |> isDivisibleBy4
                            match errormsg with
                            |Some(_) -> addr,errormsg
                            |None ->
                                regs.[dest] <- addr + ofset
                                addr,errormsg
                    |Pre ->
                        // the value is stored to the address [dest + offset]
                        let ofset, errormsg = getOffset (offset, shift) input
                        match errormsg with
                        |Some(_) -> regs.[dest], errormsg
                        |None ->
                            let addr,errormsg = (regs.[dest] + ofset) |> isDivisibleBy4
                            match errormsg with
                            |Some(_) -> addr,errormsg
                            |None ->
                                regs.[dest] <- addr
                                addr,errormsg
                    |Immediate -> 
                        // the value is stored to the address (dest+offset)
                        let ofset, errormsg = getOffset (offset, shift) input
                        match errormsg with
                        |Some(_) -> regs.[dest], errormsg
                        |None -> 
                            let addr,errormsg = (regs.[dest] + ofset) |> isDivisibleBy4
                            addr, errormsg
                | NoReg -> 
                    match idxing with
                    |Post -> regs.[dest], Some "Post-indexing mode must have an offset"
                    |Pre -> regs.[dest], Some "Pre-indexing mode must have an offset"
                    |Immediate -> regs.[dest] |> isDivisibleBy4
                    
            match dataType with
                |By -> 
                    let addr,errormsg = accessMem
                    match errormsg with
                    |Some(_) -> Map.empty, errormsg
                    |None -> 
                        let value = int32(uint8(regs.[source]))
                        let newMEM = mem |> Map.add addr value
                        newMEM, errormsg
                |SBy -> Map.empty, Some "not implemented yet, also not implemented in Visual"
                |H -> Map.empty, Some "not implemented yet, also not implemented in Visual"
                |SH -> Map.empty, Some "not implemented yet, also not implemented in Visual"
                |W -> 
                    let addr, errormsg = accessMem
                    match errormsg with
                    |Some(_) -> Map.empty, errormsg
                    |None ->
                        let value = regs.[source]
                        let newMEM = mem |> Map.add addr value
                        newMEM,errormsg

            ///check conditions and source/dest types
        let LDRorSTR (dataType,cond,dest,source,offset,shift,idxing) input inst =
            let (regs, mem, insLst,flags,errormsg) = input 
            match matchCond (cond,input) with
            |true ->
                match dest with
                | Reg(dest) ->
                    match source with
                    | Reg(source) when source = 13 -> 
                        let errormsg = Some "Source cannot have R13"
                        (regs,mem,insLst,flags,errormsg)
                    | Reg(source) when source = dest -> 
                        let errormsg = Some "destination register must be different from the source register"
                        (regs,mem,insLst,flags,errormsg)
                    | Reg(source) -> 
                        match inst with
                        |"LDR" -> 
                            let errormsg = ldrEXE (dataType,dest,source,offset,shift,idxing) input
                            regs.[15] <- regs.[15] + 4
                            (regs,mem,insLst,flags,errormsg)
                        |"STR" -> 
                            // check if any error
                            let newMEM, errormsg = getSTRNewMEM (dataType,dest,source,offset,shift,idxing) input
                            match errormsg with
                            |Some(_) -> 
                                regs.[15] <- regs.[15] + 4
                                (regs,mem,insLst,flags,errormsg)
                            |None ->
                                regs.[15] <- regs.[15] + 4
                                (regs,newMEM,insLst,flags,errormsg)
                    | _ -> 
                        let errormsg = Some (sprintf "the source of %A must be a register" inst)
                        (regs,mem,insLst,flags,errormsg)
                | _ -> 
                    let errormsg = Some (sprintf "the destination of %A must be a register" inst) 
                    (regs,mem,insLst,flags,errormsg)
            |false ->
                regs.[15] <- regs.[15] + 4
                (regs, mem, insLst,flags,errormsg) 
       
    // ---------------------------------------------- LDM/STM Instruction -----------------------------------------------------------
        let LDMorSTM (cond,stackType,updateP,pointer:Register,reglst:Register list) input inst =
            let (regs:int array, mem, insLst,flags, errormsg) = input 
            /// execute Load/Store operations
            /// returns new memory state if STM
            /// returns loaded values with if LDM
            let operation =
                fun (idx,reg:Register) -> 
                    //get the address of memory
                    let addr = 
                        match stackType with
                        |FD |IA -> regs.[pointer.getRegIdx] + idx*4
                        |FA |DA -> regs.[pointer.getRegIdx] - idx*4
                        |ED |IB -> regs.[pointer.getRegIdx] + (idx+1)*4
                        |EA |DB -> regs.[pointer.getRegIdx] - (idx+1)*4

                    match inst with
                    |"STM" -> 
                        // return new memory state
                        (addr,regs.[reg.getRegIdx])
                    |"LDM" ->
                        let loadValue =
                            match mem |> Map.tryFind addr with
                            |Some (v) -> v
                            |None -> 0 
                        // update reglst
                        regs.[reg.getRegIdx] <- loadValue
                        // return loaded value from memory
                        (addr,loadValue)
                        
            /// sort and index the reg list in ascending order 
            let indexedRegLst = 
                match stackType with 
                |FD |IA |ED |IB -> reglst |> List.sort |> ToIndexedList
                |FA |DA |EA |DB -> reglst |> List.sort |> List.rev |> ToIndexedList 
            
            let getAddrOfPointer stk = stk |> List.rev |> List.head |> fst
            let checkUpdateP stk =
                // update pointer register
                match updateP with
                |Update -> 
                    match stackType with 
                    |IA |FD -> regs.[pointer.getRegIdx] <- getAddrOfPointer stk + 4
                    |DA |FA -> regs.[pointer.getRegIdx] <- getAddrOfPointer stk - 4
                    |_ -> regs.[pointer.getRegIdx] <- getAddrOfPointer stk
                |NoUpdate -> ()

            // CHECK condition here
            match matchCond (cond,input) with
            |true ->
                match pointer with
                | Reg(_) when reglst |> List.exists (fun x -> x = pointer) -> 
                    let errormsg = Some "register list cannot contain the pointer register"
                    (regs, mem, insLst,flags,errormsg) 
                | Reg(_) when (reglst |> List.exists (fun x -> x = Reg(14)))  &&  (reglst |> List.exists (fun x -> x = Reg(15))) -> 
                    let errormsg = Some "register list cannot have R14 and R15 at the same time"
                    (regs, mem, insLst,flags,errormsg)
                | Reg(_) -> 
                    match inst with 
                    |"LDM" -> 
                        let stack = indexedRegLst |> List.map operation
                        checkUpdateP stack
                        regs.[15] <- regs.[15] + 4
                        (regs, mem, insLst,flags,errormsg) 
                    |"STM" -> 
                        let stack = indexedRegLst |> List.map operation
                        checkUpdateP stack
                        let newMEM = 
                            stack 
                            |> List.append (mem |> Map.toList) 
                            |> Map.ofList
                        regs.[15] <- regs.[15] + 4
                        (regs, newMEM, insLst,flags,errormsg) 
                | _ -> 
                    let errormsg = Some (sprintf "the pointer of %A must be a register" inst)
                    (regs, mem, insLst,flags,errormsg)
            |false ->
                regs.[15] <- regs.[15] + 4
                (regs, mem, insLst,flags, errormsg) 


// ------------------------------------------------------ End of Memory Operations ---------------------------------------------------

// -------------------------------------------------- Beginning of Branching Operations ---------------------------------------------------
// ----------------------------------------------=-=------- Created by Lizhang ---------------------------------------------------

    // --------------------------------------------------------- B & BL ---------------------------------------------------------- 
        let branch (cond,label) input inst =
            let (regs, ms, insLst, flags,errormsg) = input 
            match matchCond (cond,input) with
            |true -> 
                match inst with
                |"B" -> 
                    regs.[15] <- label*4
                    (regs, ms, insLst, flags,errormsg)
                |"BL" -> 
                    regs.[15] <- label*4
                    // updates the link register R14(LR) to the next line of the code
                    // this can be used to return from the subroutine
                    regs.[14] <- label
                    (regs, ms, insLst, flags,errormsg)
                |_ -> failwith "invalid instruction"
            |false ->
                    regs.[15] <- regs.[15] + 4
                    (regs, ms, insLst, flags,errormsg) 
    // ------------------------------------------------------- END Instruction -----------------------------------------------------------
        let End cond input = 
            let (regs, ms, insLst,flags,errormsg) = input 
            match matchCond (cond,input) with
            | true -> //skip
                regs.[15] <- regs.[15] + 4
                (regs, ms, insLst, flags,errormsg) 
            | false -> 
                (regs, ms, insLst, flags, errormsg) 
// -------------------------------------------------- End of Branching Operations ---------------------------------------------------


// ------------------------------------------------------- main function goes here -------------------------------------------------------------
        ///start executing instruction list cell by cell
        let execute input = 
            // get the registers, PC. memory states and instruction list
            let ((regs: int array), ms: (Map<int, int>), insLst: Map<int,Instruction>,flags,errormsg) = input 
            // check if there is any errormsg
            match errormsg with
            |Some(_) -> (regs,ms,insLst,flags,errormsg)
            |None ->
                // check if PC is divisible by 4.
                match regs.[15]%4 <> 0 with
                |true -> 
                    let errormsg = Some (sprintf "there is no instruction with the address %A" regs.[15] )
                    (regs,ms,insLst,flags,errormsg)
                |false ->
                    let insIndex = regs.[15]/4
                    match insLst |> Map.toList |> List.length with
                    |tmp when tmp > insIndex ->match insLst.[insIndex] with
                                                | MOV(cond, setf, dest, op1, shift) -> movORmvn (cond,setf,dest,op1,shift) input "MOV"
                                                | MVN(cond, setf, dest, op1, shift) -> movORmvn (cond,setf,dest,op1,shift) input "MVN"
                                                | ADD(cond, setf, dest, op1, op2, shift) -> ARInst (cond, setf, dest, op1, op2, shift) input "ADD"
                                                | ADC(cond, setf, dest, op1, op2, shift) -> ARInst (cond, setf, dest, op1, op2, shift) input "ADC"
                                                | SUB(cond, setf, dest, op1, op2, shift) -> ARInst (cond, setf, dest, op1, op2, shift) input "SUB"
                                                | SBC(cond, setf, dest, op1, op2, shift) -> ARInst (cond, setf, dest, op1, op2, shift) input "SBC"
                                                | RSB(cond, setf, dest, op1, op2, shift) -> ARInst (cond, setf, dest, op1, op2, shift) input "RSB"
                                                | RSC(cond, setf, dest, op1, op2, shift) -> ARInst (cond, setf, dest, op1, op2, shift) input "RSC"
                                                | CMP(cond, op1, op2, shift) -> cmp (cond, op1, op2, shift) input
                                                | CMN(cond, op1, op2, shift) -> cmn (cond, op1, op2, shift) input
                                                | TST(cond, op1, op2, shift) -> tst (cond, op1, op2, shift) input
                                                | TEQ(cond, op1, op2, shift) -> teq (cond, op1, op2, shift) input
                                                | AND(cond, setf, dest, op1, op2, shift) -> bitwiseInst (cond, setf, dest, op1, op2, shift) input "AND"
                                                | ORR(cond, setf, dest, op1, op2, shift) -> bitwiseInst (cond, setf, dest, op1, op2, shift) input "ORR"
                                                | EOR(cond, setf, dest, op1, op2, shift) -> bitwiseInst (cond, setf, dest, op1, op2, shift) input "EOR"
                                                | BIC(cond, setf, dest, op1, op2, shift) -> bitwiseInst (cond, setf, dest, op1, op2, shift) input "BIC"
                                                | LSLInst(cond, setf, dest, op1, op2) -> LogicShiftInsts (cond, setf, dest, op1 ,op2) input "LSL"
                                                | LSRInst(cond, setf, dest, op1, op2) -> LogicShiftInsts (cond, setf, dest, op1 ,op2) input "LSR"
                                                | ASRInst(cond, setf, dest, op1, op2) -> LogicShiftInsts (cond, setf, dest, op1 ,op2) input "ASR"
                                                | RORInst(cond, setf, dest, op1, op2) -> LogicShiftInsts (cond, setf, dest, op1 ,op2) input "ROR"
                                                | RRXInst(cond, setf, dest, op1) -> LogicShiftRRX (cond, setf, dest, op1) input
                                                | STR(dataType,cond,source,dest,offset,shift,idxing) -> LDRorSTR (dataType,cond,source,dest,offset,shift,idxing) input "STR"
                                                | LDR(dataType, cond, dest, source, offset, shift, idxing) -> LDRorSTR (dataType,cond,dest,source,offset,shift,idxing) input "LDR"
                                                | B(cond, label) -> branch (cond,label) input "B"
                                                | BL(cond, label) -> branch (cond,label) input "BL"
                                                | STM(cond,stackType,updateP,pointer,reglst) -> LDMorSTM (cond,stackType,updateP,pointer,reglst) input "STM"
                                                | LDM(cond,stackType,updateP,pointer,reglst) -> LDMorSTM (cond,stackType,updateP,pointer,reglst) input "LDM"
                                                | END(cond) -> End cond input
                                                |_ -> failwithf "not implemented"
                        |_ -> (regs,ms,insLst,flags,errormsg)
        execute input



    /// recursively execute all instructions and returns the final machine state
    let rec executeInstructionAll (input:Machinestate) = 
        let nextMS = executeInstruction input 
        let regs,mem,insMap,flags, errormsg = nextMS
        let isTheEndOfInstruction = insMap |> Map.tryFindKey (fun k v -> k = regs.[15]/4)
        match isTheEndOfInstruction, errormsg with
        |Some(_),None -> executeInstructionAll nextMS
        |_ -> nextMS

    /// interface with executeInstruction's step through function
    let rec getRecord insMap (nextIdx:int) =
        let regMap = Array.zeroCreate 16
        let memoryMap = Map<int,int> [] //Map.empty
        /// initial value for flags
        let initFlags:Flag = 
            {
                N = false
                Z = false
                C = false
                V = false
            }
        let initErrorMsg = None
        let input = (regMap, memoryMap, insMap, initFlags, initErrorMsg)
        let mutable currentMS = input
        for i in [0..nextIdx] do
            currentMS <- executeInstruction currentMS 
        let regs,_,_,_,errormsg = currentMS
        let isTheEndOfInstruction = insMap |> Map.tryFindKey (fun k v -> k = regs.[15]/4)
        match isTheEndOfInstruction, errormsg with
        |Some(_), None->  [currentMS] @ getRecord insMap (nextIdx+1) // getRecord insMap (nextIdx+1) @ [currentMS]
        |_-> [currentMS]