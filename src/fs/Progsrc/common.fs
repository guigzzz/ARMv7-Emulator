namespace HLP

open Microsoft.FSharp.Reflection

module common =
    /// convert the name of discriminated union to string
    (*
    let toStr (x:'a) = 
        match FSharpValue.GetUnionFields(x, typeof<'a>) with
        | case, _ -> case.Name
*)
    let ToIndexedList (lst: 'T list) = 
                lst |> List.map2 (fun i j -> (i,j)) [0..lst.Length-1]

    type Register = Reg of int | Value of int | NoReg
        with
        /// "R1" , "#1" , ""
        member m.toStr =
            match m with
            |Reg(x) -> "R" + x.ToString()
            |Value(x) -> "#" + x.ToString()
            |NoReg -> ""
        member m.getRegIdx =
            match m with
            |Reg(x) -> x
            |_ -> failwith "input has to be a register"
        member m.getValue =
            match m with
            |Value(x) -> x
            |_ -> failwith "input must be a number"

    type Shift = LSL of Register | LSR of Register | ASR of Register | ROR of Register| RRX | NoShift   //Shift can be either a number or a register
        with
        /// "LSL R1", "LSL #1", NoShift -> ""
        member s.toStr =
            match s with
            |LSL(x) -> "LSL " + x.toStr 
            |NoShift -> ""
            |_ -> failwith "not implemented"

    type STLDMmode = ED | EA | FD | FA | IA | DA | IB | DB
        with member x.toStr =
                match x with
                | ED -> "ED"
                | EA -> "EA"
                | FD -> "FD"
                | FA -> "FA"
                | IA -> "IA"
                | DA -> "DA"
                | IB -> "IB"
                | DB -> "DB"

    type SPupdate = Update | NoUpdate
        with
        /// "!" or ""
        member p.toStr = 
            match p with
            |Update -> "!"
            |_ -> ""
    type Conditional = EQ | NE | CS | HS | CC | LO | MI | PL | VS | VC | HI | LS | GE | LT | GT | LE | AL | NoCond
        with
        /// convert to string
        /// if no conditional, return ""
        member c.toStr =
            match c with
            |NoCond -> ""
            //|x -> toStr x 
            |x -> sprintf "%A" x 

    type Setflags = Flag | NoFlag
        with
        /// convert Setflags D.U to string
        member f.toStr =
            match f with
            |Flag -> "S"
            |_ -> ""

    type Indexing = Post | Pre | Immediate //for ldr,str,etc
    type DataType = By | SBy | H | SH | W
        with
        /// "B" , "SB", "H", "SH" or ""
        member x.toStr =
            match x with
            |By -> "B"
            |SBy -> "SB"
            |H -> "H"
            |SH -> "SH"
            |W -> ""

    type Flag = 
        {
            N: bool
            Z: bool
            C: bool
            V: bool
        }

    type ILDRPseudoArg = Val of int | Address of int

    type Instruction = MOV of (Conditional*Setflags*Register*Register*Shift)
                       | MVN of (Conditional*Setflags*Register*Register*Shift)
                       | ADD of (Conditional*Setflags*Register*Register*Register*Shift)
                       | BIC of (Conditional*Setflags*Register*Register*Register*Shift)
                       | MUL of (Conditional*Setflags*Register*Register*Register*Shift)
                       | ADC of (Conditional*Setflags*Register*Register*Register*Shift)
                       | SUB of (Conditional*Setflags*Register*Register*Register*Shift)
                       | RSB of (Conditional*Setflags*Register*Register*Register*Shift)
                       | RSC of (Conditional*Setflags*Register*Register*Register*Shift)
                       | SBC of (Conditional*Setflags*Register*Register*Register*Shift)
                       | CMP of (Conditional*Register*Register*Shift)
                       | CMN of (Conditional*Register*Register*Shift)
                       | TST of (Conditional*Register*Register*Shift)
                       | TEQ of (Conditional*Register*Register*Shift)
                       | AND of (Conditional*Setflags*Register*Register*Register*Shift)
                       | EOR of (Conditional*Setflags*Register*Register*Register*Shift)
                       | ORR of (Conditional*Setflags*Register*Register*Register*Shift)
                       | LSLInst of (Conditional*Setflags*Register*Register*Register)
                       | LSRInst of (Conditional*Setflags*Register*Register*Register)
                       | ASRInst of (Conditional*Setflags*Register*Register*Register)
                       | RORInst of (Conditional*Setflags*Register*Register*Register)
                       | RRXInst of (Conditional*Setflags*Register*Register)
                       | LDR of (DataType*Conditional*Register*Register*Register*Shift*Indexing)
                       | STR of (DataType*Conditional*Register*Register*Register*Shift*Indexing) 
                       | LDRPseudo of (Conditional*Register*ILDRPseudoArg)
                       | STM of (Conditional*STLDMmode*SPupdate*Register*Register list)
                       | LDM of (Conditional*STLDMmode*SPupdate*Register*Register list)
                       | B of (Conditional*int)
                       | BL of (Conditional*int)
                       | END of (Conditional)
                       | ParseError //if input string is invalid for any reason         

    //http://infocenter.arm.com/help/index.jsp?topic=/com.arm.doc.ddi0234b/i1010871.html
    //type Machinestate = array<int>*Map<int,int> *Map<int,Instruction>* Flag
    type Machinestate = array<int>*Map<int,int> *Map<int,Instruction>* Flag * Option<string>

    let ToLowerCase (str:string) = str.ToLower()