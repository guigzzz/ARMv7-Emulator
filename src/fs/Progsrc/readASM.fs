namespace HLP
open common
open System

module readASM = 
        
        let isOp (str:string) = List.contains str ["mov";"mvn";
                                                   "add";"adc";
                                                   "sub";"sbc";"rsb";"rsc";
                                                   "mul"
                                                   "ldr";"str";"ldm";"stm"
                                                   "lsl";"lsr";"asr";"ror";"rrx"
                                                   "b";"bl"
                                                   "cmp";"cmn";"and";"orr";"eor";"bic"
                                                   "tst";"teq"
                                                   ]  

        let isDigit (c : char) = List.contains c (['-';'#']@[ '0'..'9' ]@['x'])
        let isShift (str : string) = List.contains str ["lsl";"lsr";"asr";"ror";"rrx"]
        let isWhiteSpace (c : char) = List.contains c [' ';'\t']
        let isAlpha (c : char) = List.contains c (['a'..'z'])
        let isHex (c:char) =  List.contains c (['0'..'9']@['a'..'f'])

        let isBin (c:char) = List.contains c (['0';'1'])
        let isOther (c : char) = List.contains c [',';'[';']';'!';'{';'}';'=']
        
        let implode (x : char list) = x |> String.Concat
        let explode (x : string) = x |> List.ofSeq
        let isValidLabel (str:string) = str |> explode |> List.forall (fun c -> (isDigit c) || (isAlpha c))

        let (|PosInt|_|) (clst:char list) =
                match clst.IsEmpty with
                |false -> let allDigit = clst |> List.forall (isDigit)
                          match allDigit with
                          |true -> match clst |> implode |> int with  
                                   |num when num>=0 -> Some num
                                   |_-> None
                          |_ -> None
                |true -> None

        let (|RegInt|_|) (clst:char list) =
                 match clst.IsEmpty with
                 |false -> let allDigit = clst |> List.forall (isDigit)
                           match allDigit with
                           |true -> match clst |> implode |> int with  
                                    |num when num>=0 && num<=15 -> Some num
                                    |_-> None
                           |_ -> None
                 |true -> None
        
                

        let(|AllInt|_|) (clst:char list) =
                match clst.IsEmpty with
                |false -> let allDigit = clst |> List.forall (isDigit)
                          match allDigit with
                          |true -> clst |> implode |> int |> Some 
                          |_ -> None
                |true -> None

        let (|HexInt|_|) (clst:char list) =
                match clst with
                |'0'::'x'::t -> match List.forall (isHex) t with
                                      |true -> clst |> implode |> int32 |> Some
                                      |false -> None
                |_-> None

        let (|BinInt|_|) (clst: char list) =
                match clst with
                |'0'::'b'::t -> match List.forall (isBin) t with
                                |true -> clst |> implode |> int32 |> Some
                                |false -> None
                |_->None

        
        let (|RegMatchOpx|_|) (registerstr:string) =
                match registerstr |> Seq.toList with
                |'r'::RegInt(num) -> num |> Reg |> Some
                |'#'::HexInt(num) -> num |> Value |> Some
                |'#'::BinInt(num) -> num |> Value |> Some
                |'#'::AllInt(num) -> num |> Value |> Some   
                |['p';'c'] -> 15 |> Reg |> Some
                |['l';'r'] -> 14 |> Reg |> Some
                |['s';'p'] -> 13 |> Reg |> Some
                |_ -> None

        let (|RegMatchOp1|_|) (registerstr:string) =
                match registerstr |> Seq.toList with
                |'r'::RegInt(num) -> num |> Reg |> Some
                |['p';'c'] -> 15 |> Reg |> Some
                |['l';'r'] -> 14 |> Reg |> Some
                |['s';'p'] -> 13 |> Reg |> Some
                |_ -> None

        let (|CondMatch|_|) (condstr:string) =
                match condstr with
                |"eq" -> Some EQ
                |"ne" -> Some NE
                |"cs" -> Some CS
                |"cc" -> Some CC
                |"mi" -> Some MI
                |"pl" -> Some PL
                |"vs" -> Some VS
                |"vc" -> Some VC
                |"hi" -> Some HI
                |"ls" -> Some LS
                |"ge" -> Some GE
                |"lt" -> Some LT
                |"gt" -> Some GT
                |"le" -> Some LE
                |"al" -> Some AL
                |"lo" -> Some LO
                |"hs" -> Some HS
                |""   -> Some NoCond
                |_-> None

        let (|DataTypeMatch|_|) (dtstr:string) :DataType option=
                match dtstr with
                |"b"  -> Some By
                |"sb" -> Some SBy
                |"h"  -> Some H
                |"sh" -> Some SH
                |""   -> Some W
                |_    -> None

        let (|DTCondMatch|_|) (str:string) =
                let getCond dt (str:string) =
                        match str with
                        |CondMatch(cond) -> Some(dt,cond)
                        |"" -> Some(dt,NoCond)
                        |_ -> None
                match str with
                |CondMatch(cond) -> Some(W,cond)
                |DataTypeMatch(dt) -> Some(dt,NoCond)
                | _ when str.Length>=3 -> match str.[0..0],str.[0..1] with
                                          |DataTypeMatch(dt),_ -> getCond dt str.[1..]
                                          |_,DataTypeMatch(dt) -> getCond dt str.[2..]
                                          | _ -> None
                | _ -> None

        let (|FlagCondMatch|_|) (str: string) =
                match str.[0] with
                |'s' -> match str.[1..] with
                        |CondMatch(cond) -> Some(Flag,cond)
                        |"" -> Some(Flag,NoCond)
                        |_-> None
                | _ -> None

        let (|AlphaNumMatch|_|) cLst =
                let rec iMatch lst =
                        match lst with
                        | ch :: r when isDigit ch || isAlpha ch -> ch :: iMatch r
                        | _ -> []
                match implode (iMatch cLst) with
                | "" -> None
                | s -> Some (s, List.skip (s.Length) cLst)

        let (|OpMatch|_|) (opstr:string) =
                let (|IsOpMatch|_|) (str:string) =
                        match isOp str with
                        |true -> Some()
                        |false -> None

                let rec getOpCondFlag ind =
                        match opstr.[0..ind],opstr.[ind+1..] with
                        |"",_ -> None
                        |IsOpMatch,"" -> Some(opstr,NoCond,NoFlag)
                        |IsOpMatch,CondMatch(cond) -> Some(opstr.[0..ind],cond,NoFlag)
                        |IsOpMatch,FlagCondMatch(flag,cond) when opstr.[0..ind] <> "bl" -> Some(opstr.[0..ind],cond,flag)
                        | _ -> getOpCondFlag (ind-1)

                getOpCondFlag (opstr.Length-1)

        let (|GetShift|_|) (cLst:char list) =
                let rec iMatch lst =
                        match lst with
                        | ch :: r when (isAlpha ch || isWhiteSpace ch || isDigit ch) && not (isOther ch) -> ch :: iMatch r
                        | _ -> []

                match cLst with
                |[] -> None
                |','::t -> let matchstr = t |> iMatch |> implode
                           match  matchstr.Trim() with
                           |s when s.Length < 3 -> None
                           |"rrx" -> Some ("rrx",List.skip 4 cLst)
                           |s when isShift s.[0..2] -> 
                                match s.[3..].Trim() with
                                |regornum when regornum.Length >=2 -> 
                                        Some(s.[0..2]+" "+regornum,List.skip (matchstr.Length+1) cLst)
                                |_-> None
                           |_ -> None
                |_ -> None
        
        let (|ShiftMatch|_|) (sftstr: string) =
                let ret (reg:Register) = function
                |"lsl" -> LSL(reg) |> Some
                |"lsr" -> LSR(reg) |> Some
                |"asr" -> ASR(reg) |> Some
                |"ror" -> ROR(reg) |> Some
                |_ -> failwithf "should never happen - Shift Match"

                match sftstr with
                |"rrx" -> RRX |> Some
                |_ when sftstr.Length >=5 ->    match sftstr.[4] with
                                                |'#' -> match sftstr.[5..] |> explode  with
                                                        |PosInt(num) -> ret (Value num) sftstr.[0..2]
                                                        |_ -> None
                                                |'r' -> match sftstr.[5..] |> explode with
                                                        |RegInt(num) -> ret (Reg num) sftstr.[0..2]
                                                        |_-> None
                                                |_ -> None
                |_-> None
        

        let (|IndexMatch|_|) (strlst: string list) =
                match strlst with
                |[] -> Some Immediate
                |["!"] -> Some Pre
                |_ -> None             

        let (|LabelMatch|_|) (cLst: char list) =
                let rec iMatch lst =
                        match lst with
                        | ch :: r when not (isWhiteSpace ch) -> ch :: iMatch r
                        | _ -> []
                let label =  cLst |> iMatch |> implode
                match label with
                |_ when label.Length >=1 && isOp (string label.[0]) -> None //b case
                |_ when label.Length >=2 && isOp label.[0..1] -> None //bl case
                |_ when label.Length >=3 && isOp label.[0..2] -> None //other op cases
                |_ when isValidLabel label -> Some(label,List.skip (label.Length) cLst)
                |_ -> Some("abort",cLst)


        let (|MultRegMatch|_|) (strlst:string list) =
                let buildRegList (start:Register) (finish:Register) = 
                        match start,finish with
                        |Reg(numstart),Reg(numfinish) -> List.map (Reg) [numstart..numfinish]
                        |_-> [NoReg]

                let matcher (str:string) = 
                        match str |> explode with
                        |'r'::RegInt(num) -> [Reg num]
                        |s when s.Length >= 5 -> match str.Split [|'-'|] |> Array.toList with
                                                 |[RegMatchOp1(start);RegMatchOp1(finish)] -> (buildRegList start finish)
                                                 |_ -> [NoReg]
                        |['}']|[','] -> []
                        |_-> [NoReg]

                match strlst with
                |"{"::t -> let regs = t |> List.map (matcher) |>  List.collect (id)
                           match List.forall (fun reg -> reg <> NoReg) regs with
                           |true -> regs |> Some
                           |false -> None    
                |_ -> None

        let (|STLDModeMatch|_|) (modestr:string) = 
                match modestr with
                |"ed" -> Some ED
                |"ea" -> Some EA
                |"fd" -> Some FD
                |"fa" -> Some FA
                |"ia" -> Some IA
                |"da" -> Some DA
                |"ib" -> Some IB
                |"db" -> Some DB
                | _ -> None

        let (|STMLDMMatch|_|) (stldstr:string) = //for stm and ldm
                match stldstr.Length >=5 with
                |true -> match stldstr.[0..2] with
                         |"ldm"|"stm" -> 
                                match stldstr.[3..4] with
                                |STLDModeMatch(mode) -> Some(stldstr.[0..2],NoCond,mode)
                                |CondMatch(cond) -> 
                                        match stldstr.[5..] with
                                        |STLDModeMatch(mode) -> Some(stldstr.[0..2],cond,mode)
                                        |_->None
                                |_-> None 
                         |_-> None
                |false -> None


        let (|STRLDRMatch|_|) (str:string) = //for str and ldr
                match str.Length >=3 with
                |true -> match str.[0..2] with
                         |"str"|"ldr" -> 
                                match str.[3..] with
                                |"" -> Some(str.[0..2],W,NoCond)
                                |DTCondMatch(dt,cond) -> Some(str.[0..2],dt,cond)
                                |_-> None
                         |_-> None
                |_-> None

//////////////////////////////////////////// ONE PATTERN PER INSTRUCTION /////////////////////////////////////////////// 
       

        let(|LdmMatch|_|) (strlst: string list) =
                match strlst.Head with
                |STMLDMMatch("ldm",cond,mode) -> match strlst.Tail with
                                                 |RegMatchOp1(r1)::","::MultRegMatch(reglst) -> LDM(cond,mode,NoUpdate,r1,reglst) |> Some
                                                 |RegMatchOp1(r1)::"!"::","::MultRegMatch(reglst) -> LDM(cond,mode,Update,r1,reglst) |> Some
                                                 |_-> None                    
                | _ -> None

        let(|StmMatch|_|) (strlst: string list) =
                match strlst.Head with
                |STMLDMMatch("stm",cond,mode) -> match strlst.Tail with
                                                 |RegMatchOp1(r1)::","::MultRegMatch(reglst) -> STM(cond,mode,NoUpdate,r1,reglst) |> Some
                                                 |RegMatchOp1(r1)::"!"::","::MultRegMatch(reglst) -> STM(cond,mode,Update,r1,reglst) |> Some
                                                 |_-> None                    
                | _ -> None

        let(|LdrMatch|_|) (strlst: string list) =
                match strlst.Head with
                |STRLDRMatch("ldr",dt,cond) -> match strlst.Tail with
                                               |[RegMatchOp1(r1);",";"[";RegMatchOp1(r2);"]"] -> LDR(dt,cond,r1,r2,NoReg,NoShift,Immediate) |> Some  
                                               |RegMatchOp1(r1)::","::"["::RegMatchOp1(r2)::","::RegMatchOpx(r3)::"]"::IndexMatch(ind) -> LDR(dt,cond,r1,r2,r3,NoShift,ind) |> Some
                                               |RegMatchOp1(r1)::","::"["::RegMatchOp1(r2)::","::RegMatchOp1(r3)::ShiftMatch(shift)::"]"::IndexMatch(ind) -> LDR(dt,cond,r1,r2,r3,shift,ind) |> Some
                                               |[RegMatchOp1(r1);",";"[";RegMatchOp1(r2);"]";",";RegMatchOpx(r3)] -> LDR(dt,cond,r1,r2,r3,NoShift,Post) |> Some
                                               |[RegMatchOp1(r1);",";"[";RegMatchOp1(r2);"]";",";RegMatchOp1(r3);ShiftMatch(shift)] -> LDR(dt,cond,r1,r2,r3,shift,Post) |> Some
                                               |_-> None
                | _ -> None

        let(|LdrPseudoMatch|_|) (strlst:string list,labels:string list) = 
                match strlst.Head with
                |OpMatch("ldr",cond,NoFlag) -> match strlst.Tail with
                                               |[RegMatchOp1(r1);",";"=";label] 
                                                        when isValidLabel label 
                                                             && List.contains label labels 
                                                             && Seq.exists (isAlpha) label -> LDRPseudo(cond,r1,labels |> List.findIndex (fun c -> c = label) |> Address) |> Some
                                               |[RegMatchOp1(r1);",";"=";num] -> match num |> explode with
                                                                                 |HexInt(value)|AllInt(value)|BinInt(value) -> LDRPseudo(cond,r1,Val value) |> Some
                                                                                 |_-> None
                                               |_-> None
                |_->None

        let (|StrMatch|_|) (strlst: string list) =
                match strlst.Head with
                |STRLDRMatch("str",dt,cond) -> match strlst.Tail with
                                               |[RegMatchOp1(r1);",";"[";RegMatchOp1(r2);"]"] ->STR(dt,cond,r1,r2,NoReg,NoShift,Immediate) |> Some  
                                               |RegMatchOp1(r1)::","::"["::RegMatchOp1(r2)::","::RegMatchOpx(r3)::"]"::IndexMatch(ind) -> STR(dt,cond,r1,r2,r3,NoShift,ind) |> Some
                                               |RegMatchOp1(r1)::","::"["::RegMatchOp1(r2)::","::RegMatchOp1(r3)::ShiftMatch(shift)::"]"::IndexMatch(ind) -> STR(dt,cond,r1,r2,r3,shift,ind) |> Some
                                               |[RegMatchOp1(r1);",";"[";RegMatchOp1(r2);"]";",";RegMatchOpx(r3)] -> STR(dt,cond,r1,r2,r3,NoShift,Post) |> Some
                                               |[RegMatchOp1(r1);",";"[";RegMatchOp1(r2);"]";",";RegMatchOp1(r3);ShiftMatch(shift)] -> STR(dt,cond,r1,r2,r3,shift,Post) |> Some
                                               |_-> None
                | _ -> None

        let(|MvMatch|_|) (strlst: string list) =
                match strlst.Head with
                |OpMatch("mov",cond,flag) -> match strlst.Tail with
                                             |[RegMatchOp1(r1);",";RegMatchOp1(r2);ShiftMatch(shift)] -> MOV(cond,flag,r1,r2,shift) |> Some 
                                             |[RegMatchOp1(r1);",";RegMatchOpx(r2)] -> MOV(cond,flag,r1,r2,NoShift) |> Some 
                                             |_-> None
                | _ -> None

        let(|AddMatch|_|) (strlst: string list) =
                match strlst.Head with
                | OpMatch("add",cond,flag) -> match strlst.Tail with
                                              |[RegMatchOp1(r1);",";RegMatchOp1(r2);",";RegMatchOp1(r3);ShiftMatch(shift)] -> ADD(cond,flag,r1,r2,r3,shift) |> Some
                                              |[RegMatchOp1(r1);",";RegMatchOp1(r2);",";RegMatchOpx(r3)] -> ADD(cond,flag,r1,r2,r3,NoShift) |> Some
                                              |_-> None
                | _ -> None

        let(|MulMatch|_|) (strlst: string list) =
                match strlst.Head with
                | OpMatch("mul",cond,flag) -> match strlst.Tail with
                                              |[RegMatchOp1(r1);",";RegMatchOp1(r2);",";RegMatchOp1(r3);ShiftMatch(shift)] -> MUL(cond,flag,r1,r2,r3,shift) |> Some
                                              |[RegMatchOp1(r1);",";RegMatchOp1(r2);",";RegMatchOp1(r3)] -> MUL(cond,flag,r1,r2,r3,NoShift) |> Some
                                              |_-> None
                | _ -> None

        let(|AdcMatch|_|) (strlst: string list) =
                match strlst.Head with
                | OpMatch("adc",cond,flag) -> match strlst.Tail with
                                              |[RegMatchOp1(r1);",";RegMatchOp1(r2);",";RegMatchOp1(r3);ShiftMatch(shift)] -> ADC(cond,flag,r1,r2,r3,shift) |> Some
                                              |[RegMatchOp1(r1);",";RegMatchOp1(r2);",";RegMatchOpx(r3)] -> ADC(cond,flag,r1,r2,r3,NoShift) |> Some
                                              |_-> None
                | _ -> None

        let (|MvnMatch|_|) (strlst: string list)=
                match strlst.Head with
                | OpMatch("mvn",cond,flag) -> match strlst.Tail with
                                              |[RegMatchOp1(r1);",";RegMatchOp1(r2);ShiftMatch(shift)] -> MVN(cond,flag,r1,r2,shift) |> Some
                                              |[RegMatchOp1(r1);",";RegMatchOpx(r2)] -> MVN(cond,flag,r1,r2,NoShift) |> Some
                                              |_-> None
                |_-> None

        let (|SubMatch|_|) (strlst: string list)=
                match strlst.Head with
                | OpMatch("sub",cond,flag) -> match strlst.Tail with
                                              |[RegMatchOp1(r1);",";RegMatchOp1(r2);",";RegMatchOp1(r3);ShiftMatch(shift)] -> SUB(cond,flag,r1,r2,r3,shift) |> Some
                                              |[RegMatchOp1(r1);",";RegMatchOp1(r2);",";RegMatchOpx(r3)] -> SUB(cond,flag,r1,r2,r3,NoShift) |> Some
                                              |_-> None
                |_-> None

        let (|SbcMatch|_|) (strlst: string list)=
                match strlst.Head with
                | OpMatch("sbc",cond,flag) -> match strlst.Tail with
                                              |[RegMatchOp1(r1);",";RegMatchOp1(r2);",";RegMatchOp1(r3);ShiftMatch(shift)] -> SBC(cond,flag,r1,r2,r3,shift) |> Some
                                              |[RegMatchOp1(r1);",";RegMatchOp1(r2);",";RegMatchOpx(r3)] -> SBC(cond,flag,r1,r2,r3,NoShift) |> Some
                                              |_-> None
                |_-> None

        let (|RsbMatch|_|) (strlst: string list)=
                match strlst.Head with
                | OpMatch("rsb",cond,flag) -> match strlst.Tail with
                                              |[RegMatchOp1(r1);",";RegMatchOp1(r2);",";RegMatchOp1(r3);ShiftMatch(shift)] -> RSB(cond,flag,r1,r2,r3,shift) |> Some
                                              |[RegMatchOp1(r1);",";RegMatchOp1(r2);",";RegMatchOpx(r3)] -> RSB(cond,flag,r1,r2,r3,NoShift) |> Some
                                              |_-> None
                |_-> None

        let (|RscMatch|_|) (strlst: string list)=
                match strlst.Head with
                | OpMatch("rsc",cond,flag) -> match strlst.Tail with
                                              |[RegMatchOp1(r1);",";RegMatchOp1(r2);",";RegMatchOp1(r3);ShiftMatch(shift)] -> RSC(cond,flag,r1,r2,r3,shift) |> Some
                                              |[RegMatchOp1(r1);",";RegMatchOp1(r2);",";RegMatchOpx(r3)] -> RSC(cond,flag,r1,r2,r3,NoShift) |> Some
                                              |_-> None
                |_-> None

        let(|LSLMatch|_|) (strlst: string list) = 
                match strlst.Head with
                | OpMatch("lsl",cond,flag) -> match strlst.Tail with
                                              |[RegMatchOp1(r1);",";RegMatchOp1(r2);",";RegMatchOpx(r3)] -> LSLInst(cond,flag,r1,r2,r3) |> Some
                                              |_-> None
                |_-> None

        let(|LSRMatch|_|) (strlst: string list) = 
                match strlst.Head with
                | OpMatch("lsr",cond,flag) -> match strlst.Tail with
                                              |[RegMatchOp1(r1);",";RegMatchOp1(r2);",";RegMatchOpx(r3)] -> LSRInst(cond,flag,r1,r2,r3) |> Some
                                              |_-> None
                |_-> None

        let(|ASRMatch|_|) (strlst: string list) = 
                match strlst.Head with
                | OpMatch("asr",cond,flag) -> match strlst.Tail with
                                              |[RegMatchOp1(r1);",";RegMatchOp1(r2);",";RegMatchOpx(r3)] -> ASRInst(cond,flag,r1,r2,r3) |> Some
                                              |_-> None
                |_-> None
        
        let(|RORMatch|_|) (strlst: string list) = 
                match strlst.Head with
                | OpMatch("ror",cond,flag) -> match strlst.Tail with
                                              |[RegMatchOp1(r1);",";RegMatchOp1(r2);",";RegMatchOpx(r3)] -> RORInst(cond,flag,r1,r2,r3) |> Some
                                              |_-> None
                |_-> None

        let(|RRXMatch|_|) (strlst: string list) = 
                match strlst.Head with
                | OpMatch("rrx",cond,flag) -> match strlst.Tail with
                                              |[RegMatchOp1(r1);",";RegMatchOp1(r2)] -> RRXInst(cond,flag,r1,r2) |> Some
                                              |_-> None
                |_-> None

        let (|AndMatch|_|) (strlst: string list)=
                match strlst.Head with
                | OpMatch("and",cond,flag) -> match strlst.Tail with
                                              |[RegMatchOp1(r1);",";RegMatchOp1(r2);",";RegMatchOp1(r3);ShiftMatch(shift)] -> AND(cond,flag,r1,r2,r3,shift) |> Some
                                              |[RegMatchOp1(r1);",";RegMatchOp1(r2);",";RegMatchOpx(r3)] -> AND(cond,flag,r1,r2,r3,NoShift) |> Some
                                              |_-> None
                |_-> None
        
        let (|EorMatch|_|) (strlst: string list)=
                match strlst.Head with
                | OpMatch("eor",cond,flag) -> match strlst.Tail with
                                              |[RegMatchOp1(r1);",";RegMatchOp1(r2);",";RegMatchOp1(r3);ShiftMatch(shift)] -> EOR(cond,flag,r1,r2,r3,shift) |> Some
                                              |[RegMatchOp1(r1);",";RegMatchOp1(r2);",";RegMatchOpx(r3)] -> EOR(cond,flag,r1,r2,r3,NoShift) |> Some
                                              |_-> None
                |_-> None
        
        let (|OrrMatch|_|) (strlst: string list)=
                match strlst.Head with
                | OpMatch("orr",cond,flag) -> match strlst.Tail with
                                              |[RegMatchOp1(r1);",";RegMatchOp1(r2);",";RegMatchOp1(r3);ShiftMatch(shift)] -> ORR(cond,flag,r1,r2,r3,shift) |> Some
                                              |[RegMatchOp1(r1);",";RegMatchOp1(r2);",";RegMatchOpx(r3)] -> ORR(cond,flag,r1,r2,r3,NoShift) |> Some
                                              |_-> None
                |_-> None

        let (|BicMatch|_|) (strlst: string list)=
                match strlst.Head with
                | OpMatch("bic",cond,flag) -> match strlst.Tail with
                                              |[RegMatchOp1(r1);",";RegMatchOp1(r2);",";RegMatchOp1(r3);ShiftMatch(shift)] -> BIC(cond,flag,r1,r2,r3,shift) |> Some
                                              |[RegMatchOp1(r1);",";RegMatchOp1(r2);",";RegMatchOpx(r3)] -> BIC(cond,flag,r1,r2,r3,NoShift) |> Some
                                              |_-> None
                |_-> None

        let (|CmpMatch|_|) (strlst: string list)=
                match strlst.Head with
                | OpMatch("cmp",cond,NoFlag) -> match strlst.Tail with
                                                |[RegMatchOp1(r1);",";RegMatchOp1(r2);ShiftMatch(shift)] -> CMP(cond,r1,r2,shift) |> Some
                                                |[RegMatchOp1(r1);",";RegMatchOpx(r2)] -> CMP(cond,r1,r2,NoShift) |> Some
                                                |_-> None
                |_-> None

        let (|CmnMatch|_|) (strlst: string list)=
                match strlst.Head with
                | OpMatch("cmn",cond,NoFlag) -> match strlst.Tail with
                                                |[RegMatchOp1(r1);",";RegMatchOp1(r2);ShiftMatch(shift)] -> CMN(cond,r1,r2,shift) |> Some
                                                |[RegMatchOp1(r1);",";RegMatchOpx(r2)] -> CMN(cond,r1,r2,NoShift) |> Some
                                                |_-> None
                |_-> None

        let (|TstMatch|_|) (strlst: string list)=
                match strlst.Head with
                | OpMatch("tst",cond,NoFlag) -> match strlst.Tail with
                                                |[RegMatchOp1(r1);",";RegMatchOp1(r2);ShiftMatch(shift)] -> TST(cond,r1,r2,shift) |> Some
                                                |[RegMatchOp1(r1);",";RegMatchOpx(r2)] -> TST(cond,r1,r2,NoShift) |> Some
                                                |_-> None
                |_-> None

        let (|TeqMatch|_|) (strlst: string list)=
                match strlst.Head with
                | OpMatch("teq",cond,NoFlag) -> match strlst.Tail with
                                                |[RegMatchOp1(r1);",";RegMatchOp1(r2);ShiftMatch(shift)] -> TEQ(cond,r1,r2,shift) |> Some
                                                |[RegMatchOp1(r1);",";RegMatchOpx(r2)] -> TEQ(cond,r1,r2,NoShift) |> Some
                                                |_-> None
                |_-> None

        let (|BMatch|_|) (strlst: string list,labels:string list) =
                match strlst with
                |[OpMatch("b",cond,_);label] when List.contains label labels -> B(cond,List.findIndex (fun c -> c=label) labels) |> Some 
                | _ -> None

        let (|BLMatch|_|) (strlst: string list,labels:string list) =
                match strlst with
                |[OpMatch("bl",cond,_);label] when List.contains label labels -> BL(cond,List.findIndex (fun c -> c=label) labels) |> Some 
                | _ -> None


////////////////////////////////////////////////// MAIN CODE /////////////////////////////////////////////////////

        let rec tokeniser (lst:char list) =
                match lst with
                |';'::t -> []  //at end of line or remove comment
                |h::t when isWhiteSpace h -> tokeniser t
                |GetShift(s,t) -> s :: tokeniser t
                |h::t when isOther h -> (string h):: tokeniser t
                |AlphaNumMatch(s,t) -> s :: tokeniser t
                |[] -> [] 
                |_-> ["abort"]
                
        let Parse ((strlst: string list),(labels: string list)) =
                match List.contains "abort" strlst with
                |false ->match strlst with
                         |MvMatch(instr)|MvnMatch(instr) -> instr
                         |AddMatch(instr)|AdcMatch(instr) -> instr
                         |SubMatch(instr)|SbcMatch(instr)|RsbMatch(instr)|RscMatch(instr) -> instr
                         |MulMatch(instr) -> instr
                         |CmpMatch(instr)|CmnMatch(instr) -> instr
                         |AndMatch(instr)|OrrMatch(instr)|EorMatch(instr)|BicMatch(instr) -> instr
                         |TstMatch(instr)|TeqMatch(instr) -> instr
                         |LSLMatch(instr)|LSRMatch(instr)|ASRMatch(instr)|RORMatch(instr) -> instr
                         |RRXMatch(instr) -> instr
                         |StrMatch(instr)|LdrMatch(instr) -> instr
                         |LdmMatch(instr)|StmMatch(instr) -> instr
                         |_-> match (strlst,labels) with
                              |BLMatch(instr)|BMatch(instr) -> instr
                              |LdrPseudoMatch(instr) -> instr
                              |_-> ParseError
                |true -> ParseError

        let getMachineState (strlst:string list) :Machinestate=
                //let memoryMap = ref (Map<int,int> [])
                let memoryMap = Map<int,int> []
                let getlabel str = match str with
                                   |LabelMatch(label,lst) -> //printfn "label %A lst %A" label lst
                                                             match label with 
                                                             |"abort" -> ( "" , ['@'])
                                                             | _ -> (label,lst)   
                                   | _ -> ("",str)
                let commandMap = 
                        let tmp = strlst |> List.filter (fun c -> c.Trim()<>"" && c.Trim().[0] <> ';')
                                |> List.map (ToLowerCase 
                                             >> (fun c -> c.Trim())
                                             >> Seq.toList 
                                             >> getlabel)
                                  
                        let instructions = tmp |> List.map (fun (_,inst) -> inst) |> List.filter ((<>) []) |> List.map (tokeniser)

                        let labels = tmp 
                                     |> List.map (fun (label,_) -> label)

                        instructions
                        |> List.map (fun instruction -> Parse (instruction,labels))
                        |> ToIndexedList
                        |> Map.ofList

                let regarray: int array = Array.create 16 (0)
                let flags:Flag = {N = false
                                  Z = false
                                  C = false
                                  V = false}
                (regarray,memoryMap,commandMap,flags,None)