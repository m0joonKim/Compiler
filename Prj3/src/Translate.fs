module Translate

open AST
open IR
open Helper

// Symbol table is a mapping from identifier to a pair of register and type.
// Register is recorded here will be containg the address of that variable.
type SymbolTable = Map<Identifier, Register * CType>

// Let's assume the following size for each data type.
let sizeof (ctyp: CType) =
    match ctyp with
    | CInt -> 4
    | CBool -> 1
    | CIntPtr -> 8
    | CBoolPtr -> 8
    | CIntArr n -> 4 * n
    | CBoolArr n -> n

// Find the register that contains pointer to variable 'vname'
let lookupVar (symtab: SymbolTable) (vname: Identifier) : Register =
    let _ =
        if not (Map.containsKey vname symtab) then
            failwith "Unbound variable"

    fst (Map.find vname symtab)

let lookupVarType (symtab: SymbolTable) (vname: Identifier) : CType =
    let _ =
        if not (Map.containsKey vname symtab) then
            failwith "Unbound variable"

    snd (Map.find vname symtab)

let rec transExp (symtab: SymbolTable) (e: Exp) : Register * Instr list =
    match e with
    | Null ->
        let r = createRegName ()
        (r, [ Set(r, Imm 0) ])
    | Num i ->
        let r = createRegName ()
        (r, [ Set(r, Imm i) ])
    | Boolean b ->
        let r = createRegName ()
        if b then (r, [ Set(r, Imm 1) ]) else (r, [ Set(r, Imm 0) ])
    | Var vname ->
        let varReg = lookupVar symtab vname // Contains the address of 'vname'
        let r = createRegName ()
        (r, [ Load(r, varReg) ])
    | Deref px ->
        let varReg = lookupVar symtab px
        let r = createRegName ()
        let r1 = createRegName ()
        (r, [ Load(r1, varReg); Load(r, r1) ])
    | AddrOf ax ->
        let varReg = lookupVar symtab ax
        let r = createRegName ()
        (r, [ Set(r, Reg varReg); Label("Addr " + varReg) ])
    // (r, [ Set(r, Reg varReg) ])
    | Arr(vname, e1) ->
        let varReg = lookupVar symtab vname
        let r = createRegName ()
        let r1 = createRegName ()
        let r2 = createRegName ()
        let (r3, l3) = transExp symtab e1
        let typ = lookupVarType symtab vname

        let size =
            match typ with
            | CIntArr n -> Imm 4
            | CBoolArr n -> Imm 1
            | _ -> failwith "UNVALID TYPE"

        (r,
         l3
         @ [ BinOp(r1, MulOp, size, Reg r3)
             BinOp(r2, AddOp, Reg r1, Reg varReg)
             Load(r, r2) ])
    | Neg e1 ->
        let r = createRegName ()
        let (r1, l1) = transExp symtab e1
        (r, l1 @ [ UnOp(r, NegOp, Reg r1) ])
    | Add(e1, e2) ->
        let r = createRegName ()
        let (r1, l1) = transExp symtab e1
        let (r2, l2) = transExp symtab e2
        (r, l1 @ l2 @ [ BinOp(r, AddOp, Reg r1, Reg r2) ])
    | Sub(e1, e2) ->
        let r = createRegName ()
        let (r1, l1) = transExp symtab e1
        let (r2, l2) = transExp symtab e2
        (r, l1 @ l2 @ [ BinOp(r, SubOp, Reg r1, Reg r2) ])
    | Mul(e1, e2) ->
        let r = createRegName ()
        let (r1, l1) = transExp symtab e1
        let (r2, l2) = transExp symtab e2
        (r, l1 @ l2 @ [ BinOp(r, MulOp, Reg r1, Reg r2) ])
    | Div(e1, e2) ->
        let r = createRegName ()
        let (r1, l1) = transExp symtab e1
        let (r2, l2) = transExp symtab e2
        (r, l1 @ l2 @ [ BinOp(r, DivOp, Reg r1, Reg r2) ])
    | Equal(e1, e2) ->
        let r = createRegName ()
        let (r1, l1) = transExp symtab e1
        let (r2, l2) = transExp symtab e2
        (r, l1 @ l2 @ [ BinOp(r, EqOp, Reg r1, Reg r2) ])
    | NotEq(e1, e2) ->
        let r = createRegName ()
        let (r1, l1) = transExp symtab e1
        let (r2, l2) = transExp symtab e2
        (r, l1 @ l2 @ [ BinOp(r, NeqOp, Reg r1, Reg r2) ])
    | LessEq(e1, e2) ->
        let r = createRegName ()
        let (r1, l1) = transExp symtab e1
        let (r2, l2) = transExp symtab e2
        (r, l1 @ l2 @ [ BinOp(r, LeqOp, Reg r1, Reg r2) ])
    | LessThan(e1, e2) ->
        let r = createRegName ()
        let (r1, l1) = transExp symtab e1
        let (r2, l2) = transExp symtab e2
        (r, l1 @ l2 @ [ BinOp(r, LtOp, Reg r1, Reg r2) ])
    | GreaterEq(e1, e2) ->
        let r = createRegName ()
        let (r1, l1) = transExp symtab e1
        let (r2, l2) = transExp symtab e2
        (r, l1 @ l2 @ [ BinOp(r, GeqOp, Reg r1, Reg r2) ])
    | GreaterThan(e1, e2) ->
        let r = createRegName ()
        let (r1, l1) = transExp symtab e1
        let (r2, l2) = transExp symtab e2
        (r, l1 @ l2 @ [ BinOp(r, GtOp, Reg r1, Reg r2) ])
    | And(e1, e2) ->
        let r = createRegName ()
        let (r1, l1) = transExp symtab e1
        let (r2, l2) = transExp symtab e2
        let lb1 = createLabel ()

        (r,
         l1
         @ [ Set(r2, Imm 0); GotoIfNot(Reg r1, lb1) ]
         @ l2
         @ [ Label(lb1); Set(r, Reg r2) ])
    | Or(e1, e2) ->
        let r = createRegName ()
        let (r1, l1) = transExp symtab e1
        let (r2, l2) = transExp symtab e2
        let lb1 = createLabel ()

        (r,
         l1
         @ [ Set(r2, Imm 1); GotoIf(Reg r1, lb1) ]
         @ l2
         @ [ Label(lb1); Set(r, Reg r2) ])
    | Not e1 ->
        let r = createRegName ()
        let (r1, l1) = transExp symtab e1
        (r, l1 @ [ UnOp(r, NotOp, Reg r1) ])
// TODO: Fill in the remaining cases to complete the code.

let rec transStmt (symtab: SymbolTable) stmt : SymbolTable * Instr list =
    match stmt with
    | Declare(_, typ, vname) ->
        let r = createRegName ()
        let size = sizeof typ
        let symtab = Map.add vname (r, typ) symtab

        match typ with
        | CInt -> (symtab, [ LocalAlloc(r, size); Label("DInt " + r) ])
        | CBool -> (symtab, [ LocalAlloc(r, size); Label("DBool " + r) ])
        | CIntPtr -> (symtab, [ LocalAlloc(r, size); Label("DIntPtr " + r) ])
        | CBoolPtr -> (symtab, [ LocalAlloc(r, size); Label("DBoolPtr " + r) ])
        | _ -> (symtab, [ LocalAlloc(r, size) ])
    | Define(_, typ, vname, e1) ->
        let r = createRegName ()
        let size = sizeof typ
        let symtab = Map.add vname (r, typ) symtab
        let (r1, l1) = transExp symtab e1

        match typ with
        | CInt -> (symtab, l1 @ [ LocalAlloc(r, size); Label("DInt " + r); Store(Reg r1, r) ])
        | CBool -> (symtab, l1 @ [ LocalAlloc(r, size); Label("DBool " + r); Store(Reg r1, r) ])
        | CIntPtr -> (symtab, l1 @ [ LocalAlloc(r, size); Label("DIntPtr " + r); Store(Reg r1, r) ])
        | CBoolPtr -> (symtab, l1 @ [ LocalAlloc(r, size); Label("DBoolPtr " + r); Store(Reg r1, r) ])
        | _ -> (symtab, l1 @ [ LocalAlloc(r, size); Store(Reg r1, r) ])
    | Assign(_, id, e1) ->
        //let (fr1, fl1) = transExp symtab (Var id)
        let fr1 = lookupVar symtab id
        let (r1, l1) = transExp symtab e1
        (symtab, l1 @ [ Store(Reg r1, fr1) ])
    | PtrUpdate(_, id, e1) ->
        let (fr1, fl1) = transExp symtab (Var id)
        let (r1, l1) = transExp symtab e1
        (symtab, fl1 @ l1 @ [ Store(Reg r1, fr1) ])
    | ArrUpdate(_, id, e1, e2) ->
        let varReg = lookupVar symtab id
        let (r1, l1) = transExp symtab e1
        let typ = lookupVarType symtab id

        let size =
            match typ with
            | CIntArr n -> Imm 4
            | CBoolArr n -> Imm 1
            | _ -> failwith "UNVALID TYPE"

        let (r2, l2) = transExp symtab e2
        let r3 = createRegName ()
        let r4 = createRegName ()

        (symtab,
         l1
         @ l2
         @ [ BinOp(r3, MulOp, size, Reg r1)
             BinOp(r4, AddOp, Reg r3, Reg varReg)
             Store(Reg r2, r4) ])
    | Return(_, e1) ->
        let (fr1, fl1) = transExp symtab e1
        (symtab, fl1 @ [ Ret(Reg fr1) ])
    | If(_, e1, s1, s2) ->
        //트루면 앞에거 아니면 뒤에거
        let (fr1, fl1) = transExp symtab e1
        let l1 = transStmts symtab s1
        let l2 = transStmts symtab s2
        let ltrue = createLabel ()
        let lend = createLabel ()

        (symtab,
         fl1
         @ [ GotoIf(Reg fr1, ltrue) ]
         @ l2
         @ [ Goto lend ]
         @ [ Label ltrue ]
         @ l1
         @ [ Label lend ])
    | While(_, e1, s1) ->
        let (fr1, fl1) = transExp symtab e1
        let l1 = transStmts symtab s1
        let lloop = createLabel ()
        let lend = createLabel ()

        (symtab,
         [ Label lloop ]
         @ fl1
         @ [ GotoIfNot(Reg fr1, lend) ]
         @ l1
         @ [ Goto lloop; Label lend ])

and transStmts symtab stmts : Instr list =
    match stmts with
    | [] -> []
    | headStmt :: tailStmts ->
        let symtab, instrs = transStmt symtab headStmt
        instrs @ transStmts symtab tailStmts

// This code allocates memory for each argument and records information to the
// symbol table. Note that argument can be handled similarly to local variable.
let rec transArgs accSymTab accInstrs args =
    match args with
    | [] -> accSymTab, accInstrs
    | headArg :: tailArgs ->
        // In our IR model, register 'argName' is already defined at the entry.
        let (argTyp, argName) = headArg
        let r = createRegName ()
        let size = sizeof argTyp
        // From now on, we can use 'r' as a pointer to access 'argName'.
        let accSymTab = Map.add argName (r, argTyp) accSymTab

        let accInstrs =
            match argTyp with
            | CInt -> [ LocalAlloc(r, size); Label("DInt " + r); Store(Reg argName, r) ] @ accInstrs
            | CBool -> [ LocalAlloc(r, size); Label("DBool " + r); Store(Reg argName, r) ] @ accInstrs
            | CIntPtr ->
                [ LocalAlloc(r, size); Label("DIntPtr " + r); Store(Reg argName, r) ]
                @ accInstrs
            | CBoolPtr ->
                [ LocalAlloc(r, size); Label("DBoolPtr " + r); Store(Reg argName, r) ]
                @ accInstrs
            | _ -> [ LocalAlloc(r, size); Store(Reg argName, r) ] @ accInstrs

        transArgs accSymTab accInstrs tailArgs

// Translate input program into IR code.
let run (prog: Program) : IRCode =
    let (_, fname, args, stmts) = prog
    let argRegs = List.map snd args
    let symtab, argInstrs = transArgs Map.empty [] args
    let bodyInstrs = transStmts symtab stmts
    (fname, argRegs, argInstrs @ bodyInstrs)
