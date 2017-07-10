module App.Main
open Fable.Import
open App.CodeMirrorInterface
open App.Renderer
open App.CodeMirrorImports

open HLP.readASM
open HLP.common
open HLP.executeInstruction

let initFlags:Flag = 
        {
            N = false
            Z = false
            C = false
            V = false
        }

let emptyMacState = fun () ->
    let regMap = Array.create 16 (0)
    //regMap.[13] <- 0xFF000000 |> int
    let memoryMap = Map.empty
    let flags = initFlags
    let insMap = Map.empty
    (regMap,memoryMap,insMap,flags,None)

let main () =
    let config = [LineNumbers;Mode "arm"]
    let editIdEditor = getById<Browser.HTMLTextAreaElement> "code"
    let cmEditor = CodeMirror.fromTextArea(editIdEditor, config)
   
    cmEditor.setSize("100%","100%")
    cmEditor.refresh()
    
    let executeButton = getById<Browser.HTMLButtonElement> "execute_button"
    let resetButton = getById<Browser.HTMLButtonElement> "reset_button"
    let openButton = getById<Browser.HTMLButtonElement> "open_file_button"
    let saveButton = getById<Browser.HTMLButtonElement> "save_button"
    let stepForwardButton = getById<Browser.HTMLButtonElement> "step_forward_btn"
    let stepBackButton = getById<Browser.HTMLButtonElement> "step_back_btn"
    let decimalButton = getById<Browser.HTMLButtonElement> "decimal"
    let hexButton = getById<Browser.HTMLButtonElement> "hexa"
    
    cmEditor.setValue("     mov r0,#0x11
    mov r1,#2 
    ; this is a comment and a blank line next

    add r2,r1,r0,lsl #1
    subs r3,r2,r2
    str r1,[r2]
    ldr r5,[r2]
    str r1,[r2,r2,lsl #1]
    ldr r6,[r2,r2,lsl #1]
    mov r0,#10
    label add r7,r7,#1
        subs r0,r0,#1
        bne label
        mov r10,#1")

    let reg0 = getById<Browser.HTMLInputElement> "reg0"
    let reg1 = getById<Browser.HTMLInputElement> "reg1"
    let reg2 = getById<Browser.HTMLInputElement> "reg2"
    let reg3 = getById<Browser.HTMLInputElement> "reg3"
    let reg4 = getById<Browser.HTMLInputElement> "reg4"
    let reg5 = getById<Browser.HTMLInputElement> "reg5"
    let reg6 = getById<Browser.HTMLInputElement> "reg6"
    let reg7 = getById<Browser.HTMLInputElement> "reg7"
    let reg8 = getById<Browser.HTMLInputElement> "reg8"
    let reg9 = getById<Browser.HTMLInputElement> "reg9"
    let reg10 = getById<Browser.HTMLInputElement> "reg10"
    let reg11 = getById<Browser.HTMLInputElement> "reg11"
    let reg12 = getById<Browser.HTMLInputElement> "reg12"
    let reg13 = getById<Browser.HTMLInputElement> "reg13"
    let reg14 = getById<Browser.HTMLInputElement> "reg14"
    let reg15 = getById<Browser.HTMLInputElement> "reg15"
    let nflag = getById<Browser.HTMLInputElement> "N"
    let zflag = getById<Browser.HTMLInputElement> "Z"
    let cflag = getById<Browser.HTMLInputElement> "C"
    let vflag = getById<Browser.HTMLInputElement> "V"
    let regs = [|reg0;reg1;reg2;reg3;reg4;reg5;reg6;reg7;reg8;reg9;reg10;reg11;reg12;reg13;reg14;reg15|]
    let trace = getById<Browser.HTMLInputElement> "trace"
    let memorytable = getById<Browser.HTMLTableElement> "MemTable"

    let curMacStateInd = ref (0) //for step thru
    let allMacStates = ref(Array.empty)
    let oldmap = ref Map.empty //for memory output tracking
    let needIni = ref true //for step thru, whether to initialise an empty mac state or not
    let hexordec = ref "dec"

    let onHexFct = fun () -> 
        Array.iter (fun (c:Browser.HTMLInputElement) -> c.value <- c.value |> int32 |> sprintf "%X" |> (+) "0x") regs
        hexordec := "hex"
        null
    
    let onDecFct = fun () -> 
        Array.iter (fun (c:Browser.HTMLInputElement) -> c.value <- c.value |> int32 |> string) regs
        hexordec := "dec"
        null
    
    let b2i input = 
        match input with
        |true -> 1
        |false -> 0

    let cleartable map = 
        [1..(map |> Map.toList |> List.length)]
        |> List.iter (fun _ -> memorytable.deleteRow(0.0))

    let getPEline (raw:string) (instrlst:Instruction list) =
        let instrstr = raw.Split [|'\n'|] |> Array.toList
        let peIndex = List.findIndex ((=) ParseError) instrlst
        trace.value <- string peIndex
        let rec cal strlst counter =
            match counter>=0,strlst with
            |true,(h:string)::t -> match h.Trim() = "" || (h.Trim().[0] = ';') with
                                   |true -> 1 + cal t counter
                                   |false -> 1 + cal t (counter - 1)
            |false,_ -> 0
            |_ -> failwithf "shouldn't happen"
        cal instrstr (peIndex)
    
    let conditionoutput (macstate:Machinestate) = 
        let (registers,mem,instrmap,flags,_) = macstate
        registers 
        |> Array.iter2 (fun (htreg:Browser.HTMLInputElement) reg -> htreg.value <- string reg) regs
        //regs.[13].value <- regs.[13].value |> uint32 |> string
        match !hexordec with
        |"hex" -> onHexFct() |> ignore
        |"dec" -> onDecFct() |> ignore
        |_ -> failwithf "shouldn't happen"
        nflag.value <- flags.N |> b2i |> string
        zflag.value <- flags.Z |> b2i |> string
        cflag.value <- flags.C |> b2i |> string
        vflag.value <- flags.V |> b2i |> string
        //cmEditor.setLineClass(1.0,"background","background : #FBC2C4") //line highlighting test
        
        match mem = (!oldmap) with
        |true  -> ()
        |false ->    //cleartable !oldmap
                     printfn "%A" !oldmap
                     match (!oldmap) = Map.empty with
                     |true -> ()
                     |false -> cleartable !oldmap
                     match mem.IsEmpty with
                     |true -> oldmap := mem
                     |false -> oldmap := mem
                               mem 
                               |> Map.toList
                               |> List.sortBy (fun (add,_) -> add)
                               |> List.iter (fun (address,contents) -> let newrow = memorytable.insertRow(0.0)
                                                                       let newaddress = newrow.insertCell(0.0)
                                                                       let newcontents = newrow.insertCell(1.0)
                                                                       newaddress.innerText <- string address
                                                                       newcontents.innerText <- string contents)   
        

    let onExecuteFct = fun () -> 
        trace.value <- "Execute"
        let instr = cmEditor.getValue() 
        let (regmap,memorymap,instrMap,flags,errormsg) = instr.Split [|'\n'|] |> Array.toList |> getMachineState
        let macState =  (regmap,memorymap,instrMap,flags,None)
        let retlst = instrMap |> Map.toList |> List.map (fun (_,c) -> c)
        match List.contains ParseError retlst with
        |false -> let ret = macState |> executeInstructionAll 
                  let (_,_,_,_,emsg) = ret
                  match emsg with
                  |Some msg -> trace.value <- msg; printfn "%A" msg
                  |None -> trace.value <- "Execute Successful"
                  ret |> conditionoutput
        |_->let errorline = getPEline instr retlst
            trace.value <- sprintf "Invalid Syntax at line %A" errorline
            //cmEditor.setLineClass(float (errorline-1),"background","line-error") |> ignore
        null

    let onResetFct = fun () -> 
        cleartable !oldmap
        oldmap := Map.empty
        curMacStateInd := 0
        needIni := true
        emptyMacState()
        |> conditionoutput
        trace.value <- "Idle"
        null


    let rec getAllStates output macState =
        let ((regs:int array),memMap,insMap,flags,emsg) = macState
        let newRegs = Array.copy regs
        let macStateCopy = (newRegs,memMap,insMap,flags,emsg)
        match insMap |> Map.tryFindKey (fun k v -> k = regs.[15]/4) with
        |Some(_) ->  (macState |> executeInstruction |> getAllStates (macStateCopy::output))
        |None -> macStateCopy::output |> List.rev

    let iniMap = fun () -> 
        let instr = cmEditor.getValue()  
        //printfn "%A" (instr.Split [|'\n'|])
        //printfn "%A" ((instr.Split [|'\n'|]) |> Array.toList |> getMachineState)
        let macState = instr.Split [|'\n'|] 
                       |> Array.toList 
                       |> getMachineState
        let (_,_,instructions,_,_) = macState
        let retlst = instructions |> Map.toList |> List.map (snd)
        match List.contains ParseError retlst with
        |false -> //allMacStates := getRecord instructions 0 |> List.toArray
                  allMacStates := getAllStates [] macState |> List.toArray
                  //printfn "%A" !allMacStates
                  Some(1)
        |true -> let errorline = getPEline instr retlst
                 trace.value <- sprintf "Invalid Syntax at line %A" errorline
                 None

    let onForwardStep = fun () ->
        trace.value <- "Forward Step"
       
        match !needIni with
        |true -> let ini = iniMap()
                 //printfn "inimap called" 
                 match ini with
                 |None -> ()
                 |Some(_) -> needIni := false
                             (!allMacStates).[1] 
                             |> conditionoutput
                             curMacStateInd := 1
                             //printfn "%A" curMacStateInd
                             //printfn "macstateall length %A" (!allMacStates).Length
                             //printfn "macstateall %A" !allMacStates
                             

        |false when !curMacStateInd<((!allMacStates).Length-1) -> curMacStateInd := !curMacStateInd + 1
                                                                  //printfn "%A" curMacStateInd
                                                                  (!allMacStates).[!curMacStateInd] 
                                                                  |> conditionoutput
                                                              
        | _ -> trace.value <- "Cannot Step Forward"
        null

    

    let onBackwardStep = fun () ->
        trace.value <- "Backward Step"
        
        match !curMacStateInd>0 with
        |true -> curMacStateInd := !curMacStateInd - 1 
                 //printfn "%A" curMacStateInd
                 let curmap = (!allMacStates).[!curMacStateInd]
                 curmap |> conditionoutput
                 
        //|false when !curMacStateInd > 0 -> emptyMacState() |> conditionoutput
        //                                   curMacStateInd := 0
        |_ -> trace.value <- "Already at first instruction"
        null


    let onSaveFct = fun () -> cmEditor.getValue() 
                              |> writeFromFileDialog 
                              |> ignore
                              null

    let onOpenFct = fun () -> 
        match readFromFileDialog() with
        |Some(fName,data) -> cmEditor.setValue(data)
        | None -> ()
        onResetFct() |> ignore
        null

    executeButton.addEventListener_click(fun _ -> onExecuteFct()) 
    resetButton.addEventListener_click(fun _ -> onResetFct())
    openButton.addEventListener_click(fun _ -> onOpenFct())
    saveButton.addEventListener_click(fun _ -> onSaveFct())
    stepForwardButton.addEventListener_click(fun _ -> onForwardStep())
    stepBackButton.addEventListener_click(fun _ -> onBackwardStep())
    decimalButton.addEventListener_click(fun _ -> onDecFct())
    hexButton.addEventListener_click(fun _ -> onHexFct())
    onResetFct() |> ignore

main()

