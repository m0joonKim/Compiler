module DFA

open IR
open CFG


// You can represent a 'reaching definition' element with an instruction.
type RDSet = Set<Instr>
type LVSet = Set<Register>
type AESet = Set<Instr>

let rec findEdgeMToL instId edgeMap = // find instId Node's pred
    match Map.tryFind instId edgeMap with
    | None -> []
    | Some l -> l

let rec unionSet curEdgeMap edgeL = // Set Union (pred의 Set UNION)
    match edgeL with
    | [] -> Set.empty
    | head :: tail ->
        match Map.tryFind head curEdgeMap with
        | None -> unionSet curEdgeMap tail
        | Some s -> Set.union s (unionSet curEdgeMap tail)

let rec intersectSet curEdgeMap edgeL baseSet =
    match edgeL with
    | [] -> Set.empty
    | head :: [] ->

        match Map.tryFind head curEdgeMap with
        | None -> Set.empty
        | Some s -> s
    | head :: tail ->

        match Map.tryFind head curEdgeMap with
        | None -> intersectSet curEdgeMap tail baseSet
        | Some s -> Set.intersect s (intersectSet curEdgeMap tail baseSet)

module RDAnalysis = // related to "Constant Propagation"
    let rec doF curSet delRegi = // deletion part of F
        Set.filter
            (fun x ->
                match x with
                | LocalAlloc(r, _)
                | UnOp(r, _, _)
                | BinOp(r, _, _, _)
                | Load(r, _)
                | Set(r, _) -> delRegi <> r
                | _ -> true)
            curSet

    let makeRDout curRDMap instrM predM = // RD Out만드는 함수.
        Map.fold
            (fun acc key value ->
                let newSet = unionSet curRDMap (findEdgeMToL key predM)

                let newSet2 =
                    match value with //이번 키가 Set, Alloc, Unary ... 이었다면,
                    | LocalAlloc(r, _)
                    | UnOp(r, _, _)
                    | BinOp(r, _, _, _)
                    | Load(r, _)
                    | Set(r, _) -> Set.union (doF newSet r) (Set.add value Set.empty)
                    | _ -> newSet

                Map.add key newSet2 acc)
            (Map.empty: Map<int, Set<Instr>>)
            instrM

    let rec findRD rdM instrM predM = // RD를 찾는데, RDOut만드는 함수 돌려서, 이전이랑 같을때까지 반복
        let rdMap = makeRDout rdM instrM predM
        if rdMap = rdM then rdMap else findRD rdMap instrM predM

    let run (cfg: CFG) : Map<int, RDSet> = // base case 만들고, RD 찾는 함수 호출
        let (instM, _, predM) = cfg

        let baseRD =
            Map.fold (fun acc key value -> Map.add key Set.empty acc) Map.empty instM

        findRD baseRD instM predM

module LVAnalysis =
    let makeLVin cuvLVMap instrM succM =
        //succ거 다 갖고와서 합집합
        //내가 정의했으면 그거 빼버리고
        //내가 사용한거 있으면 더하기
        //즉 a = e
        //꼴이면 a를 빼고
        //e를 더해
        Map.fold
            (fun acc key value ->
                let newSet = unionSet cuvLVMap (findEdgeMToL key succM)
                //succM에 있는 LVMap내용 다 Union한거지
                let newSet2 =
                    //정의 다뺀거
                    match value with
                    //이번 키가 정의하는놈이 있다면-> 그건 빼줘야하고
                    //사용하는 놈이 있다면 -> 그건 더해줘야해
                    | Set(r, _)
                    | LocalAlloc(r, _)
                    | UnOp(r, _, _)
                    | BinOp(r, _, _, _)
                    | Load(r, _) -> Set.difference newSet (Set.add r Set.empty) //Union결과에 정의하는놈 빼주기
                    | _ -> newSet

                let newSet3 =
                    match value with
                    | Store(Reg r1, r2)
                    | BinOp(_, _, Reg r1, Reg r2) ->
                        let tmp = Set.add r1 Set.empty
                        let tmp = Set.add r2 tmp
                        Set.union newSet2 tmp
                    | Set(_, Reg r)
                    | UnOp(_, _, Reg r)
                    | Load(_, r)
                    | GotoIf(Reg r, _)
                    | GotoIfNot(Reg r, _)
                    | Ret(Reg r) -> Set.union newSet2 (Set.add r Set.empty)
                    | Store(Imm i, r) -> Set.union newSet2 (Set.add r Set.empty)
                    | BinOp(_, _, Reg r, Imm i)
                    | BinOp(_, _, Imm i, Reg r) -> Set.union newSet2 (Set.add r Set.empty)
                    | _ -> newSet2

                Map.add key newSet3 acc)
            (Map.empty: Map<int, Set<Register>>)
            instrM

    let rec findLV lvM instrM succM =
        let lvMap = makeLVin lvM instrM succM
        if lvMap = lvM then lvMap else findLV lvMap instrM succM
    //정의하면 빼고 사용하면 더하고
    //그럼 Live가 아닌 레지스터만 있는 instruction을 없애면 되는거구나!
    let run (cfg: CFG) : Map<int, LVSet> = // base case 만들고, LV 찾는 함수 호출
        let (instM, succM, _) = cfg

        let baseLV =
            Map.fold (fun acc key value -> Map.add key Set.empty acc) Map.empty instM

        findLV baseLV instM succM

module AEAnalysis =
    let isContainRHS instr goalRegi =
        match instr with
        | Set(_, Reg r1)
        | Load(_, r1)
        | UnOp(_, _, Reg r1) -> goalRegi = r1
        | BinOp(_, _, Imm i, Reg r1)
        | BinOp(_, _, Reg r1, Imm i) -> goalRegi = r1
        | BinOp(_, _, Reg r1, Reg r2) -> goalRegi = r1 || goalRegi = r2
        | _ -> false

    let isContainLHS instr goalRegi =
        match instr with
        | Set(r1, _)
        | UnOp(r1, _, _)
        | Load(r1, _)
        | BinOp(r1, _, _, _) -> goalRegi = r1
        | _ -> false

    // let isContainForStore instr goalRegi =
    //     match instr with //store가 goalRegi에 저장하고 있을 때, 문제가 생기는 경우는
    //     | Load(r1, r2) -> r1 = goalRegi || r2 = goalRegi //이전에 이미 goalRegi이라는 주소에서 Load중이거나
    //     | _ -> false
    let isdel instrs goalRegi =
        match instrs with
        | Set(r, _)
        | UnOp(r, _, _)
        | BinOp(r, _, _, _)
        | LocalAlloc(r, _)
        | Load(r, _) -> (isContainRHS instrs goalRegi) || (isContainLHS instrs goalRegi)
        | _ -> false

    let delLoad instr =
        match instr with
        | Load(_, _) -> true
        | _ -> false

    let makeAEout curAEMap instrM predM baseSet =
        Map.fold
            (fun acc key value ->
                // let (storeRegi, instr) = value
                // let _ = printfn "START makeAEIn\n"
                let newSet = intersectSet acc (findEdgeMToL key predM) baseSet
                // let _ = printfn "result RDIN is %A" newSet

                let minusSet = //newSet돌면서, value랑 겹치는놈 죽어야되는거였네?
                    match value with
                    | Set(goalRegi, _)
                    | UnOp(goalRegi, _, _)
                    | BinOp(goalRegi, _, _, _)
                    | Load(goalRegi, _)
                    | LocalAlloc(goalRegi, _) -> Set.filter (fun x -> (isdel x goalRegi)) newSet
                    // | Store(_, goalRegi) ->
                    | Store(_, _) -> Set.filter (fun x -> (delLoad x)) newSet
                    | _ -> Set.empty

                // let _ = printfn "%A : inst\n%A\n %A\n" value newSet minusSet
                let newSet2 = Set.difference newSet minusSet
                // let _ = printfn "%A : inst\n%A\n" value newSet2

                let newSet3 =
                    match value with
                    | Set(r, _)
                    | UnOp(r, _, _)
                    | BinOp(r, _, _, _)
                    | Load(r, _) ->
                        if isContainRHS value r then
                            newSet2
                        else
                            Set.union newSet2 (Set.add value Set.empty)
                    | _ -> newSet2

                // printfn "[%d] inst : %A par : %A aeIn %A \n\n" key value (findEdgeMToL key predM) newSet
                Map.add key newSet3 acc)
            curAEMap
            instrM

    let rec findAE aeM instrM predM baseSet =
        let aeMap = makeAEout aeM instrM predM baseSet

        // Map.iter (fun k v -> printfn "parL %A AESet[%d]: %A" (findEdgeMToL k predM) k v) aeMap

        if aeMap = aeM then
            aeMap
        else
            findAE aeMap instrM predM baseSet

    let run (cfg: CFG) (instrs: Instr list) = // base case 만들고, AE 찾는 함수 호출
        let (instM, _, predM) = cfg

        let allInstrSet =
            Map.fold (fun acc key value -> Set.union (Set.add value Set.empty) acc) Set.empty instM

        let baseAEMap =
            Map.fold (fun acc key value -> Map.add key allInstrSet acc) Map.empty instM

        (allInstrSet, findAE baseAEMap instM predM allInstrSet)
