module Optimize

open IR
open CFG
open DFA


module ConstantFolding =
    let foldConstant instr =
        match instr with
        | BinOp(r, AddOp, Reg r1, Imm 0)
        | BinOp(r, AddOp, Imm 0, Reg r1)
        | BinOp(r, SubOp, Reg r1, Imm 0)
        | BinOp(r, MulOp, Reg r1, Imm 1)
        | BinOp(r, MulOp, Imm 1, Reg r1)
        | BinOp(r, DivOp, Reg r1, Imm 1) -> (true, Set(r, Reg r1))
        | BinOp(r, SubOp, Imm 0, Reg r1) -> (true, UnOp(r, NegOp, Reg r1))
        | UnOp(r, NegOp, Imm x) -> (true, Set(r, Imm(-x)))
        | UnOp(r, NotOp, Imm x) -> (true, Set(r, Imm(if x = 0 then 1 else 0)))
        | BinOp(r, AddOp, Imm x, Imm y) -> (true, Set(r, Imm(x + y)))
        | BinOp(r, SubOp, Imm x, Imm y) -> (true, Set(r, Imm(x - y)))
        | BinOp(r, MulOp, Imm x, Imm y) -> (true, Set(r, Imm(x * y)))
        | BinOp(r, DivOp, Imm x, Imm y) -> (true, Set(r, Imm(x / y)))
        | BinOp(r, EqOp, Imm x, Imm y) ->
            if x = y then
                (true, Set(r, Imm 1))
            else
                (true, Set(r, Imm 0))
        | BinOp(r, NeqOp, Imm x, Imm y) ->
            if x <> y then
                (true, Set(r, Imm 1))
            else
                (true, Set(r, Imm 0))
        | BinOp(r, LeqOp, Imm x, Imm y) ->
            if x <= y then
                (true, Set(r, Imm 1))
            else
                (true, Set(r, Imm 0))
        | BinOp(r, LtOp, Imm x, Imm y) ->
            if x < y then
                (true, Set(r, Imm 1))
            else
                (true, Set(r, Imm 0))
        | BinOp(r, GeqOp, Imm x, Imm y) ->
            if x >= y then
                (true, Set(r, Imm 1))
            else
                (true, Set(r, Imm 0))
        | BinOp(r, GtOp, Imm x, Imm y) ->
            if x > y then
                (true, Set(r, Imm 1))
            else
                (true, Set(r, Imm 0))
        // You may add many more cases here.
        | GotoIf(Imm 1, label) -> (true, Goto label)
        | GotoIf(Imm 0, label) -> (true, Label "XGoIf")
        | GotoIfNot(Imm 0, label) -> (true, Goto label)
        | GotoIfNot(Imm 1, label) -> (true, Label "XGoIfNot")
        | _ -> (false, instr)

    let run instrs =
        let results = List.map foldConstant instrs
        let flags, instrs = List.unzip results
        let isOptimized = List.contains true flags
        (isOptimized, instrs)


module ConstantPropagation =
    let isValidRD instr goalRegi =
        match instr with
        | Set(r, _)
        | LocalAlloc(r, _)
        | UnOp(r, _, _)
        | BinOp(r, _, _, _)
        | Load(r, _) -> (goalRegi = r)
        | _ -> false


    let replace rdIn goalReg =
        let filteredRD = Set.filter (fun x -> isValidRD x goalReg) rdIn

        if Set.count filteredRD = 1 then //1개가 아니라면 볼필요도없음 여러개가 정의중이라는 뜻이므로
            (if true then
                 match Set.toList filteredRD with
                 | Set(goalReg, Imm i) :: _ -> (Imm i: Operand)
                 | _ -> Reg goalReg
             else
                 Reg goalReg) //1개라면, 그게 Set(r imm)라면, 교체해줘야함
        else
            Reg goalReg

    let propagateConstant idx instr predM rdMap =
        let rdIn = DFA.unionSet rdMap (DFA.findEdgeMToL idx predM)
        //부모거 Union 완.
        //이제 필터 걸어서 날릴거 날리자고
        match instr with
        | Set(r, Reg r1) -> Set(r, (replace rdIn r1))
        | UnOp(r, u, Reg r1) -> UnOp(r, u, (replace rdIn r1))
        // | Load(r, r1)-> Load(r, (replace rdIn r1))
        | Store(Reg r1, r) -> Store((replace rdIn r1), r)
        | GotoIf(Reg r1, l) -> GotoIf((replace rdIn r1), l)
        | GotoIfNot(Reg r1, l) -> GotoIfNot((replace rdIn r1), l)
        | Ret(Reg r1) -> Ret((replace rdIn r1))
        | BinOp(r, b, Reg r1, Reg r2) -> BinOp(r, b, (replace rdIn r1), (replace rdIn r2))
        | BinOp(r, b, Reg r1, o) -> BinOp(r, b, (replace rdIn r1), o)
        | BinOp(r, b, o, Reg r1) -> BinOp(r, b, o, (replace rdIn r1))
        | _ -> instr
    //이제 여기에
    //1. int보고 부모 찾아온다.
    //2. 부모거 다 Union 해온다
    //3. 검사해서 propa 되는지 본다.
    let run instrs =
        let cfg = CFG.make instrs
        let rdMap = RDAnalysis.run cfg
        let (instM, _, predM) = cfg
        //이게 아니라 rdMap이랑 cfg에 있는 InstrMap을 넘겨줘서 해야됨
        //그래야 그 index랑 맞춰서 rdMap보고 체크해서 처리.
        let afterMap: InstrMap =
            Map.map (fun key value -> propagateConstant key value predM rdMap) instM

        let (_, resultInstrs) = List.unzip (Map.toList afterMap)

        (instrs <> resultInstrs, resultInstrs) //변한게 있으면 true 반환하는거니까 다르다면true 반환

module DeadCodeElimination =
    let eliminateDeadCode idx instr succM lvMap =
        let lvOut = DFA.unionSet lvMap (DFA.findEdgeMToL idx succM)

        let isAlive =
            match instr with
            | Set(r, _)
            | LocalAlloc(r, _)
            | UnOp(r, _, _)
            | BinOp(r, _, _, _)
            | Load(r, _) -> Set.contains r lvOut //존재한다면 true (살아있음)
            | _ -> true

        if isAlive then instr else Label "TRASH"

    let rec delTrash instrs =
        match instrs with
        | [] -> []
        | head :: tail ->
            if head = Label "TRASH" then
                delTrash tail
            else
                [ head ] @ delTrash tail

    let run instrs =
        let cfg = CFG.make instrs
        let lvMap: Map<int, LVSet> = LVAnalysis.run cfg
        let (instM, succM, _) = cfg
        //이게 아니라 rdMap이랑 cfg에 있는 InstrMap을 넘겨줘서 해야됨
        //그래야 그 index랑 맞춰서 rdMap보고 체크해서 처리.
        //돌면서, 내가 사용하는 레지스터가
        //아무것도 Live중이 아니라면
        //해당 instr을 제거해
        let afterMap: InstrMap =
            Map.map (fun key value -> eliminateDeadCode key value succM lvMap) instM

        let (_, resultInstrs) = List.unzip (Map.toList afterMap)
        let resultInstrs = delTrash resultInstrs
        (instrs <> resultInstrs, resultInstrs) //변한게 있으면 true 반환하는거니까 다르다면true 반환

module CopyPropagation =
    let isValidAE instr goalRegi =
        match instr with
        | Set(r, _)
        | UnOp(r, _, _)
        | BinOp(r, _, _, _)
        | Load(r, _) -> (goalRegi = r)
        | _ -> false

    let replace rdIn goalReg =
        let filteredRD = Set.filter (fun x -> isValidAE x goalReg) rdIn

        if Set.count filteredRD = 1 then //1개가 아니라면 볼필요도없음 여러개가 정의중이라는 뜻이므로
            match Set.toList filteredRD with
            | Set(goalReg, Reg r) :: _ -> (r: Register)
            | _ -> goalReg
        //1개라면, 그게 Set(r imm)라면, 교체해줘야함
        else
            goalReg

    let propagateCopy idx instr predM aeMap allSet =
        let aeIn = intersectSet aeMap (findEdgeMToL idx predM) allSet
        // let _ = printfn "%A %A %A" idx instr aeIn
        //부모거 Union 완.
        //이제 필터 걸어서 날릴거 날리자고
        // let _ = printfn "now : [%A]\n%A - %A\n%A" idx instr (findEdgeMToL idx predM) aeIn
        match instr with
        | Set(r, Reg r1) -> Set(r, Reg(replace aeIn r1))
        | UnOp(r, u, Reg r1) -> UnOp(r, u, Reg(replace aeIn r1))
        | Load(r, r1) -> Load(r, (replace aeIn r1))
        | Store(Reg r1, r) -> Store(Reg(replace aeIn r1), (replace aeIn r))
        | Store(Imm i, r) -> Store(Imm i, (replace aeIn r))
        | GotoIf(Reg r1, l) -> GotoIf(Reg(replace aeIn r1), l)
        | GotoIfNot(Reg r1, l) -> GotoIfNot(Reg(replace aeIn r1), l)
        | Ret(Reg r1) -> Ret(Reg(replace aeIn r1))
        | BinOp(r, b, Reg r1, Reg r2) -> BinOp(r, b, Reg(replace aeIn r1), Reg(replace aeIn r2))
        | BinOp(r, b, Reg r1, o) -> BinOp(r, b, Reg(replace aeIn r1), o)
        | BinOp(r, b, o, Reg r1) -> BinOp(r, b, o, Reg(replace aeIn r1))
        | _ -> instr

    let run instrs =
        let cfg = CFG.make instrs
        let (instM, _, predM) = cfg
        let allSet, lvMap = AEAnalysis.run cfg instrs

        let afterMap: InstrMap =
            Map.map (fun key value -> propagateCopy key value predM lvMap allSet) instM

        let (_, resultInstrs) = List.unzip (Map.toList afterMap)
        (instrs <> resultInstrs, resultInstrs) //변한게 있으면 true 반환하는거니까 다르다면true 반환


module CommonSubexpressionElimination =
    let isValidAE instr goalInst =
        match instr, goalInst with
        | UnOp(r, u1, o1), UnOp(destiR, u2, o2) -> (u1 = u2 && o1 = o2)
        | BinOp(r, AddOp, o11, o12), BinOp(destiR, AddOp, o21, o22)
        | BinOp(r, MulOp, o11, o12), BinOp(destiR, MulOp, o21, o22) ->
            (o11 = o21 && o12 = o22) || (o11 = o22 && o12 = o21)
        | BinOp(r, b1, o11, o12), BinOp(destiR, b2, o21, o22) -> (b1 = b2 && o11 = o21 && o12 = o22)
        | Load(o, desti), Load(r2, src) -> desti = src
        | _ -> false

    let replace aeIn goalInst destiR =
        let filteredRD = Set.filter (fun x -> isValidAE x goalInst) aeIn

        if Set.count filteredRD = 1 then //1개가 아니라면 볼필요도없음 여러개가 정의중이라는 뜻이므로

            match Set.toList filteredRD with
            | UnOp(r, u1, o1) :: _ -> Set(destiR, Reg r)
            | BinOp(r, b1, o1, o2) :: _ -> Set(destiR, Reg r)
            | _ -> goalInst
        else
            goalInst



    let replaceLoad aeIn goalInst destiR =
        let filteredRD = Set.filter (fun x -> isValidAE x goalInst) aeIn

        if Set.count filteredRD = 1 then //1개가 아니라면 볼필요도없음 여러개가 정의중이라는 뜻이므로

            match Set.toList filteredRD with
            | Load(r1, r2) :: _ -> Set(destiR, Reg r1)
            | _ -> goalInst
        else
            goalInst

    let eliminateCommonSubexpression idx instr predM aeMap allSet =
        let aeIn = intersectSet aeMap (findEdgeMToL idx predM) allSet
        //부모거 Union 완.
        //이제 필터 걸어서 날릴거 날리자고
        let ret =
            match instr with
            | UnOp(destiR, u, o1) -> replace aeIn instr destiR
            | BinOp(destiR, b, o1, o2) -> replace aeIn instr destiR
            | Load(destiR, r) -> replaceLoad aeIn instr destiR
            | _ -> instr

        ret


    let run instrs =
        let cfg = CFG.make instrs
        let (instM, _, predM) = cfg
        let allSet, aeMap = AEAnalysis.run cfg instrs

        let afterMap: InstrMap =
            Map.map (fun key value -> eliminateCommonSubexpression key value predM aeMap allSet) instM

        let (_, resultInstrs) = List.unzip (Map.toList afterMap)
        (instrs <> resultInstrs, resultInstrs) //변한게 있으면 true 반환하는거니까 다르다면true 반환


module Mem2Reg =
    let parseGoalLabel (label: string) (goal: string) =
        if label.StartsWith(goal) then //주소참조 AddrOf
            let s = label.Split()
            (true, s[1])
        else
            (false, "")

    let rec findSet instrs retS goal =
        match instrs with
        | [] -> retS
        | head :: body ->
            match head with
            | Label l ->
                let (isFiltered, reg) = parseGoalLabel l goal

                if isFiltered then
                    findSet body (Set.add reg retS) goal
                else
                    findSet body retS goal
            | _ -> findSet body retS goal

    let rec delmem (instrs: Instr list) (s: Set<string>) =
        match instrs with
        | [] -> []
        | head :: tail ->
            match head with
            | LocalAlloc(reg, _) ->
                if Set.contains reg s then
                    delmem tail s
                else
                    [ head ] @ delmem tail s
            | Store(o, reg) ->
                if Set.contains reg s then
                    [ Set(reg, o) ] @ delmem tail s
                else
                    [ head ] @ delmem tail s
            | Load(r, reg) ->
                if Set.contains reg s then
                    [ Set(r, Reg reg) ] @ delmem tail s
                else
                    [ head ] @ delmem tail s
            | Label l ->
                if l.StartsWith("D") || l.StartsWith("A") || l.StartsWith("X") then
                    delmem tail s
                else
                    [ head ] @ delmem tail s
            | _ -> [ head ] @ delmem tail s

    let run instrs =
        let defineSet = findSet instrs Set.empty "D" //arr이 아닌 변수 선언 레지스터
        let addrSet = findSet instrs Set.empty "A" //주소참조 있는 레지스터
        let finalSet = Set.difference defineSet addrSet //arr제외 - 주소참조
        //이제 Final Set에 존재하는 놈들 다 바꿔도 됨 instrs
        delmem instrs finalSet

// module Mem2Reg2 =

//     let rec findCandiSet instrs retS =
//         match instrs with
//         | [] -> retS
//         | head :: body ->
//             match head with
//             | LocalAlloc(r, i) ->
//                 if i = 8 || i = 4 || i = 1 then
//                     findCandiSet body (Set.add r retS)
//                 else
//                     findCandiSet body retS
//             | _ -> findCandiSet body retS

//     let rec findR instrs x curS =
//         //
//         match instrs with
//         | [] -> curS
//         | head :: tail ->
//             match head with
//             | BinOp(r, _, Reg r1, Reg r2) ->
//                 if (r1 = x || r2 = x) && r <> x then
//                     findR tail x (Set.add r curS)
//                 else
//                     findR tail x curS
//             | BinOp(r, _, Imm i, Reg r1)
//             | BinOp(r, _, Reg r1, Imm i) ->
//                 if (r1 = x && r <> x) then
//                     findR tail x (Set.add r curS)
//                 else
//                     findR tail x curS
//             | Set(r, Reg r1) ->
//                 if (r1 = x && r <> x) then
//                     findR tail x (Set.add r curS)
//                 else
//                     findR tail x curS
//             | _ -> curS

//     let rec findDelSetWrapper instrs curS originS =
//         Set.fold (fun acc x -> Map.add x (findR instrs x Set.empty) acc) Map.empty originS

//     let rec delmem (instrs: Instr list) (s: Set<string>) =
//         match instrs with
//         | [] -> []
//         | head :: tail ->
//             match head with
//             | LocalAlloc(reg, _) ->
//                 if Set.contains reg s then
//                     delmem tail s
//                 else
//                     [ head ] @ delmem tail s
//             | Store(o, reg) ->
//                 if Set.contains reg s then
//                     [ Set(reg, o) ] @ delmem tail s
//                 else
//                     [ head ] @ delmem tail s
//             | Load(r, reg) ->
//                 if Set.contains reg s then
//                     [ Set(r, Reg reg) ] @ delmem tail s
//                 else
//                     [ head ] @ delmem tail s
//             | Label l ->
//                 if l.StartsWith("D") || l.StartsWith("A") || l.StartsWith("X") then
//                     delmem tail s
//                 else
//                     [ head ] @ delmem tail s
//             | _ -> [ head ] @ delmem tail s

//     let run instrs =
//         let candiSet = findCandiSet instrs Set.empty
//         //이제 Final Set에 존재하는 놈들 다 바꿔도 됨 instrs
//         // let _ = printfn "%A\n %A\n %A\n" candiSet delSet finalSet
//         let finalSet = Set.empty
//         delmem instrs finalSet

// // You will have to run optimization iteratively, as shown below.
let rec optimizeLoop instrs =

    // let instrs1 = Mem2Reg.run instrs

    // printfn
    //     "After M2R diff : %A \n -> \n\n %A"
    //     (Set.difference (Set.ofList instrs) (Set.ofList instrs1))
    //     (Set.difference (Set.ofList instrs1) (Set.ofList instrs))

    // printfn "%A" (IRCode.toStr ("", [], instrs1))

    // let cp, instrs2 = ConstantPropagation.run instrs1

    // printfn
    //     "After CP diff : %A \n -> \n\n %A"
    //     (Set.difference (Set.ofList instrs1) (Set.ofList instrs2))
    //     (Set.difference (Set.ofList instrs2) (Set.ofList instrs1))

    // printfn "%A" (IRCode.toStr ("", [], instrs2))

    // let cf, instrs3 = ConstantFolding.run instrs2
    // let instrs1 = Mem2Reg.run instrs

    // printfn
    //     "After M2R diff : %A \n -> \n\n %A"
    //     (Set.difference (Set.ofList instrs) (Set.ofList instrs1))
    //     (Set.difference (Set.ofList instrs1) (Set.ofList instrs))

    // printfn "%A" (IRCode.toStr ("", [], instrs1))

    // let cp, instrs2 = ConstantPropagation.run instrs1

    // printfn
    //     "After CP diff : %A \n -> \n\n %A"
    //     (Set.difference (Set.ofList instrs1) (Set.ofList instrs2))
    //     (Set.difference (Set.ofList instrs2) (Set.ofList instrs1))

    // printfn "%A" (IRCode.toStr ("", [], instrs2))

    // let cf, instrs3 = ConstantFolding.run instrs2
    // let instrs1 = Mem2Reg.run instrs

    // printfn
    //     "After M2R diff : %A \n -> \n\n %A"
    //     (Set.difference (Set.ofList instrs) (Set.ofList instrs1))
    //     (Set.difference (Set.ofList instrs1) (Set.ofList instrs))

    // printfn "%A" (IRCode.toStr ("", [], instrs1))

    // let cp, instrs2 = ConstantPropagation.run instrs1

    // printfn
    //     "After CP diff : %A \n -> \n\n %A"
    //     (Set.difference (Set.ofList instrs1) (Set.ofList instrs2))
    //     (Set.difference (Set.ofList instrs2) (Set.ofList instrs1))

    // printfn "%A" (IRCode.toStr ("", [], instrs2))

    // let cf, instrs3 = ConstantFolding.run instrs2
    // let instrs1 = Mem2Reg.run instrs

    // printfn
    //     "After M2R diff : %A \n -> \n\n %A"
    //     (Set.difference (Set.ofList instrs) (Set.ofList instrs1))
    //     (Set.difference (Set.ofList instrs1) (Set.ofList instrs))

    // printfn "%A" (IRCode.toStr ("", [], instrs1))

    // let cp, instrs2 = ConstantPropagation.run instrs1

    // printfn
    //     "After CP diff : %A \n -> \n\n %A"
    //     (Set.difference (Set.ofList instrs1) (Set.ofList instrs2))
    //     (Set.difference (Set.ofList instrs2) (Set.ofList instrs1))

    // printfn "%A" (IRCode.toStr ("", [], instrs2))

    // let cf, instrs3 = ConstantFolding.run instrs2
    // let instrs1 = Mem2Reg.run instrs

    // printfn
    //     "After M2R diff : %A \n -> \n\n %A"
    //     (Set.difference (Set.ofList instrs) (Set.ofList instrs1))
    //     (Set.difference (Set.ofList instrs1) (Set.ofList instrs))

    // printfn "%A" (IRCode.toStr ("", [], instrs1))

    // let cp, instrs2 = ConstantPropagation.run instrs1

    // printfn
    //     "After CP diff : %A \n -> \n\n %A"
    //     (Set.difference (Set.ofList instrs1) (Set.ofList instrs2))
    //     (Set.difference (Set.ofList instrs2) (Set.ofList instrs1))

    // printfn "%A" (IRCode.toStr ("", [], instrs2))

    // let cf, instrs3 = ConstantFolding.run instrs2

    // printfn
    //     "After CF diff : %A \n -> \n\n %A"
    //     (Set.difference (Set.ofList instrs2) (Set.ofList instrs3))
    //     (Set.difference (Set.ofList instrs3) (Set.ofList instrs2))

    // printfn "%A" (IRCode.toStr ("", [], instrs3))

    // let dce, instrs4 = DeadCodeElimination.run instrs3

    // printfn
    //     "After DCE diff : %A \n -> \n\n %A"
    //     (Set.difference (Set.ofList instrs3) (Set.ofList instrs4))
    //     (Set.difference (Set.ofList instrs4) (Set.ofList instrs3))

    // printfn "%A" (IRCode.toStr ("", [], instrs4))

    // let cpp, instrs5 = CopyPropagation.run instrs4

    // printfn
    //     "After CPP diff : %A \n -> \n\n %A"
    //     (Set.difference (Set.ofList instrs4) (Set.ofList instrs5))
    //     (Set.difference (Set.ofList instrs5) (Set.ofList instrs4))

    // printfn "%A" (IRCode.toStr ("", [], instrs5))

    // let cse, instrs6 = CommonSubexpressionElimination.run instrs5

    // printfn
    //     "After CSE diff : %A \n -> \n\n %A"
    //     (Set.difference (Set.ofList instrs5) (Set.ofList instrs6))
    //     (Set.difference (Set.ofList instrs6) (Set.ofList instrs5))

    // printfn "%A" (IRCode.toStr ("", [], instrs6))

    let instrs1 = Mem2Reg.run instrs
    let cp, instrs2 = ConstantPropagation.run instrs1
    let cf, instrs3 = ConstantFolding.run instrs2
    let dce, instrs4 = DeadCodeElimination.run instrs3
    let cse, instrs5 = CommonSubexpressionElimination.run instrs4
    let cpp, instrs6 = CopyPropagation.run instrs5


    if cp || cf || dce || cpp || cse then
        optimizeLoop instrs6
    else
        instrs6

// if cp || cf || dce then optimizeLoop instrs4 else instrs4
//  if cp || cf then optimizeLoop instrs else instrs

// Optimize input IR code into faster version.
let run (ir: IRCode) : IRCode =
    let (fname, args, instrs) = ir
    (fname, args, optimizeLoop instrs)
