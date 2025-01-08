module TypeCheck

open AST

// Symbol table is a mapping from 'Identifier' (string) to 'CType'. Note that
// 'Identifier' and 'Ctype' are defined in AST.fs file.
type SymbolTable = Map<Identifier, CType>

// For semantic analysis, you will need the following type definition. Note the
// difference between 'Ctype' and 'Typ': 'Ctype' represents the type annoted in
// the C code, whereas 'Typ' represents the type obtained during type checking.
type Typ =
    | Int
    | Bool
    | NullPtr
    | IntPtr
    | BoolPtr
    | Error

// Convert 'CType' into 'Typ'.
let ctypeToTyp (ctype: CType) : Typ =
    match ctype with
    | CInt -> Int
    | CBool -> Bool
    | CIntPtr -> IntPtr
    | CBoolPtr -> BoolPtr

// Check expression 'e' and return its type. If the type of expression cannot be
// decided due to some semantic error, return 'Error' as its type.
let rec checkExp (symTab: SymbolTable) (e: Exp) : Typ =
    match e with
    | Null -> NullPtr
    | Num _ -> Int
    | Boolean _ -> Bool
    | Var x ->
        if Map.containsKey x symTab then
            ctypeToTyp (Map.find x symTab)
        else
            Error
    | Deref px ->
        let t =
            if Map.containsKey px symTab then
                ctypeToTyp (Map.find px symTab)
            else
                Error

        if t = IntPtr then Int
        else if t = BoolPtr then Bool
        else Error
    | AddrOf ax ->
        let t =
            if Map.containsKey ax symTab then
                ctypeToTyp (Map.find ax symTab)
            else
                Error

        if t = Int then IntPtr
        else if t = Bool then BoolPtr
        else Error
    | Neg e -> if checkExp symTab e = Int then Int else Error
    | Add(e1, e2) ->
        if checkExp symTab e1 = Int && checkExp symTab e2 = Int then
            Int
        else
            Error
    | Sub(e1, e2) ->
        if checkExp symTab e1 = Int && checkExp symTab e2 = Int then
            Int
        else
            Error
    | Mul(e1, e2) ->
        if checkExp symTab e1 = Int && checkExp symTab e2 = Int then
            Int
        else
            Error
    | Div(e1, e2) ->
        if checkExp symTab e1 = Int && checkExp symTab e2 = Int then
            Int
        else
            Error
    | Equal(e1, e2)
    | NotEq(e1, e2) ->
        let t1 = checkExp symTab e1
        let t2 = checkExp symTab e2

        if t1 = t2 && t1 <> Error then
            Bool
        else
            match (t1, t2) with
            | (IntPtr, NullPtr)
            | (BoolPtr, NullPtr) -> Bool
            | (NullPtr, IntPtr)
            | (NullPtr, BoolPtr) -> Bool
            | _ -> Error
    //if checkExp symTab e1 = checkExp symTab e2 then Bool else Error
    //| NotEq (e1,e2) -> if checkExp symTab e1 = checkExp symTab e2 then Bool else Error
    | LessEq(e1, e2) ->
        if checkExp symTab e1 = Int && checkExp symTab e2 = Int then
            Bool
        else
            Error
    | LessThan(e1, e2) ->
        if checkExp symTab e1 = Int && checkExp symTab e2 = Int then
            Bool
        else
            Error
    | GreaterEq(e1, e2) ->
        if checkExp symTab e1 = Int && checkExp symTab e2 = Int then
            Bool
        else
            Error
    | GreaterThan(e1, e2) ->
        if checkExp symTab e1 = Int && checkExp symTab e2 = Int then
            Bool
        else
            Error
    | And(e1, e2) ->
        if checkExp symTab e1 = Bool && checkExp symTab e2 = Bool then
            Bool
        else
            Error
    | Or(e1, e2) ->
        if checkExp symTab e1 = Bool && checkExp symTab e2 = Bool then
            Bool
        else
            Error
    | Not e -> if checkExp symTab e = Bool then Bool else Error
// Check statement 'stmt' and return a pair of (1) list of line numbers that
// contain semantic errors, and (2) symbol table updated by 'stmt'.
let rec checkStmt (symTab: SymbolTable) (retTyp: CType) (stmt: Stmt) =
    match stmt with
    | Declare(line, ctyp, x) ->
        // If you think this statement is error-free, then return [] as error line
        // list. If you think it contains an error, you may return [line] instead.
        ([], Map.add x ctyp symTab)
    | Define(line, ctyp, x, e) ->
        let symTab2 = Map.add x ctyp symTab
        let et = checkExp symTab e
        let ct = ctypeToTyp ctyp

        if et = ct || ((ct = IntPtr || ct = BoolPtr) && et = NullPtr) then
            ([], symTab2)
        else
            ([ line ], symTab2)
    | Assign(line, x, e) ->
        let xt =
            if Map.containsKey x symTab then
                ctypeToTyp (Map.find x symTab)
            else
                Error

        let et = checkExp symTab e

        if xt = et || ((xt = IntPtr || xt = BoolPtr) && et = NullPtr) then
            ([], symTab)
        else
            ([ line ], symTab)
    | PtrUpdate(line, px, e) ->
        let pxt =
            if Map.containsKey px symTab then
                ctypeToTyp (Map.find px symTab)
            else
                Error

        let et = checkExp symTab e

        let xt =
            if pxt = IntPtr then Int
            else if pxt = BoolPtr then Bool
            else Error

        if (xt = Int && et = Int) || (xt = Bool && et = Bool) then
            ([], symTab)
        else
            ([ line ], symTab)
    | Return(line, e) ->
        let et = checkExp symTab e
        let rt = ctypeToTyp retTyp

        if et = rt || ((rt = IntPtr || rt = BoolPtr) && et = NullPtr) then
            ([], symTab)
        else
            ([ line ], symTab)
    | If(line, e, s1, s2) ->
        let et = checkExp symTab e
        let l1 = checkStmts symTab retTyp s1
        let l2 = checkStmts symTab retTyp s2

        if et = Error then
            ([ line ] @ l1 @ l2, symTab)
        else
            ([] @ l1 @ l2, symTab)
    | While(line, e, s) ->
        let et = checkExp symTab e
        let l1 = checkStmts symTab retTyp s

        if et = Error then
            ([ line ] @ l1, symTab)
        else
            ([] @ l1, symTab)
// Check the statement list and return the line numbers of semantic errors. Note
// that 'checkStmt' and 'checkStmts' are mutually-recursive (they can call each
// other). This function design will make your code more concise.
and checkStmts symTab (retTyp: CType) (stmts: Stmt list) : LineNo list =
    match stmts with
    | [] -> []
    | head :: tail ->
        let (headL, headTab) = checkStmt symTab retTyp head
        headL @ (checkStmts headTab retTyp tail)
// TODO: Fill in this case to complete the code

// Record the type of arguments to the symbol table.
let rec collectArgTypes argDecls symTab =
    match argDecls with
    | [] -> symTab
    | (CT, Id) :: tail -> collectArgTypes tail (Map.add Id CT symTab)

// Check the program and return the line numbers of semantic errors.
let run (prog: Program) : LineNo list =
    let (retTyp, _, args, stmts) = prog
    let symTab = collectArgTypes args Map.empty
    let errorLines = checkStmts symTab retTyp stmts
    // Remove duplicate entries and sort in ascending order.
    List.sort (List.distinct errorLines)
