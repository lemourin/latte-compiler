module Compiler where
  
  import ParLatte
  import LexLatte
  import AbsLatte
  import ErrM
  import qualified Data.Map as Map
  
  data Value = 
    ValueInteger Integer
  
  type Location = Integer

  type Environment = Map.Map Ident Location

  type StringData = String -> String
  
  data StateData = State {
    environment_stack :: [Environment],
    error_output :: StringData,
    output :: StringData,
    local_id :: Integer,
    label_id :: Integer
  }

  string s = (++) s
  
  state_empty = State [] ("" ++) ("" ++) 0 0

  argument_register i = 
    if i < 6 then
      Just (["rdi", "rsi", "rdx", "rcx", "r8", "r9"] !! i)
    else
      Nothing

  load_registers i = load_registers_aux 0 where
    load_registers_aux idx =
      if idx >= i then
        string ""
      else case argument_register idx of
         Just register -> string ("  pop " ++ register ++ "\n") . load_registers_aux (idx + 1)
         Nothing -> string ""
  
  location ident state@State { environment_stack = env } =
    foldl merge Nothing env where
      merge current e = case current of
        Nothing -> Map.lookup ident e
        _ -> current

  set_variable idx value =
    string ("  mov qword [rbp - " ++ (show (8 * (idx + 1))) ++ "], " ++ value ++ "\n")

  load_variable idx destination =
    string ("  mov " ++ destination ++ ", qword [rbp - " ++ (show (8 * (idx + 1))) ++ "]\n")

  load_argument idx =
    case argument_register idx of
      Just r -> set_variable idx r
      Nothing -> 
        string ("  mov rax, " ++ "[rbp + " ++ (show (8 * (idx - 6 + 2))) ++ "]\n") . set_variable idx "rax"

  required_stack :: Show a => TopDef a -> Int
  required_stack function@(FnDef _ _ _ args block) =
    8 * (length args + compute block) where
      compute (Block _ stmts) =
        current + subblock where 
          (current, subblock) = foldl merge (0, 0) stmts where
            merge (current, subblock) stmt =
              case stmt of
                Decl _ _ items -> (current + (length items), subblock)
                BStmt _ block -> (current, max (compute block) subblock)
                _ -> (current, subblock)

  match_expression_type :: Show a => Type a -> Expr a -> Maybe StringData
  match_expression_type t expr =
    case expr of
      EString a str -> case t of
        Str _ -> Nothing
        _ -> Just (error a)
      ELitInt a i -> case t of
        Int _ -> Nothing
        _ -> Just (error a)
      ELitTrue a -> case t of
        Bool _ -> Nothing
        _ -> Just (error a)
      ELitFalse a -> case t of
        Bool _ -> Nothing
        _ -> Just (error a)
      Neg a exp -> match_expression_type t exp
      Not a exp -> match_expression_type t exp
      EMul a exp1 _ exp2 ->
        compose a (match_expression_type t exp1) (match_expression_type t exp2)
      EAdd a exp1 _ exp2 ->
        compose a (match_expression_type t exp1) (match_expression_type t exp2)
      ERel a exp1 _ exp2 ->
        compose a (match_expression_type t exp1) (match_expression_type t exp2)
      EAnd a exp1 exp2 ->
        compose a (match_expression_type t exp1) (match_expression_type t exp2)
      EOr a exp1 exp2 ->
        compose a (match_expression_type t exp1) (match_expression_type t exp2)
      where
        error a = (((show a) ++ ": expression doesn't match type " ++ (show t) ++ "\n") ++)
        compose a e1 e2 = case (e1, e2) of
          (Nothing, Nothing) -> Nothing
          (Just e1, Just e2) -> Just (e1 . e2)
          (Just e, _) -> Just e
          (_, Just e) -> Just e

  match_return_type :: Show a => Type a -> Block a -> Maybe StringData
  match_return_type t block =
    case block of
      Block a stmts ->
        case foldl merge (Nothing, False) stmts of 
          (ret, _) -> ret
        where
          is_ok e = case e of
            BStmt a block -> match_return_type t block
            Ret a expr -> match_expression_type t expr
            VRet a -> case t of
              Void a -> Nothing
              _ -> Just (("expected non void return type at " ++ show a) ++)
            _ -> Nothing
          merge (error, return) e = 
            case error of
              Nothing -> (is_ok e, False)
              _ -> (error, False)

  
  generate_expression :: Show a => Expr a -> StateData -> StateData
  generate_expression expr state@State { output = output } =
    case expr of
      EVar _ ident -> 
        state {
          output = output . (load_variable idx "rax") . string "  push rax\n"
        } where
          idx = case location ident state of
            Just x -> x
      EApp _ ident expr -> case ident of 
        Ident id -> nstate {
          output = 
            output . load_registers (length expr) . string (
              "  call " ++ id ++ "\n\
              \  add rsp, " ++ (show (8 * (max 0 ((length expr) - 6)))) ++ "\n\
              \  push rax\n"
            )
        } where
          nstate@State { output = output } = foldl merge state (reverse expr)
          merge state e = generate_expression e state
      ELitInt _ int -> state {
        output = output . string ("  push " ++ (show int) ++ "\n")
      }
      EAnd _ e1 e2 -> merge_expressions e1 e2 operation state where
        operation =
          "  and rax, rcx\n\
          \  push rax\n"
      EOr _ e1 e2 -> merge_expressions e1 e2 operation state where
        operation =
          "  or rax, rcx\n\
          \  push rax\n"
      ERel _ e1 op e2 -> nstate { label_id = label_id + 2 } where
        nstate@State { label_id = label_id } = merge_expressions e1 e2 operation state
        mnemonic op = 
          case op of 
            LTH _ -> "jl"
            LE _ -> "jle"
            GTH _ -> "jg"
            GE _ -> "jge"
            EQU _ -> "je"
            NE _ -> "jne"
        operation = 
          "  cmp rax, rcx\n\
          \  " ++ (mnemonic op) ++ " L" ++ (show label_id) ++ "\n\
          \  push 0\n\
          \  jmp L" ++ (show (label_id + 1)) ++ "\n\
          \L" ++ (show label_id) ++ ": \n\
          \  push 1\n\
          \L" ++ (show (label_id + 1)) ++ ":\n"
      EMul _ e1 op e2 -> merge_expressions e1 e2 operation state where
        operation = case op of
          Times _ -> 
            "  imul rax, rcx \n\
            \  push rax\n"
          Div _ -> 
            "  mov rdx, 0\n\
            \  idiv rcx\n\
            \  push rax\n"
          Mod _ -> 
            "  mov rdx, 0\n\
            \  idiv rcx\n\
            \  push rdx\n"
      EAdd _ e1 op e2 -> merge_expressions e1 e2 operation state where
        operation = case op of
          Plus _ ->
            "  add rax, rcx\n\
            \  push rax\n"
          Minus _ ->
            "  sub rax, rcx\n\
            \  push rax\n"
      where
        merge_expressions exp1 exp2 operation state = 
          rstate { output = output . string merge } where
            rstate@State { output = output } = generate_expression exp2 nstate
            nstate = generate_expression exp1 state
            merge = 
              "  pop rcx\n\
              \  pop rax\n"
              ++ operation


  generate_condition :: Show a => Expr a -> Stmt a -> Stmt a -> StateData -> StateData
  generate_condition exp stmt_true stmt_false state =
    rstate_next {
      output = routput . string(
        "L" ++ (show (label_id + 2)) ++ ":\n"
      )
    } where
      rstate_next@State { output = routput } = generate_statement stmt_false rstate {
        output = noutput . string (
          "  jmp L" ++ (show (label_id + 2)) ++ "\n\
          \L" ++ (show (label_id + 1)) ++ ":\n"
        )
      } 
      rstate@State { output = noutput } = generate_statement stmt_true nstate { 
        output = output . string (
          "  pop rax\n\
          \  cmp rax, 0\n\
          \  jne L" ++ (show label_id) ++ "\n\
          \  jmp L" ++ (show (label_id + 1)) ++ "\n\
          \L" ++ show label_id ++ ":\n"
        ),
        label_id = label_id + 3
      }
      nstate@State { 
        output = output, label_id = label_id 
      } = generate_expression exp state

  generate_statement :: Show a => Stmt a -> StateData -> StateData
  generate_statement stmt state = 
    case stmt of
      Empty _ -> state
      BStmt _ block -> generate_block block state
      SExp _ exp -> generate_expression exp state
      Cond a exp stmt -> generate_condition exp stmt (Empty a) state
      CondElse _ exp stmt1 stmt2 -> generate_condition exp stmt1 stmt2 state
      Incr _ ident -> state {
        output = output . (load_variable idx "rax") . (string "  inc rax\n") . (set_variable idx "rax")
      } where
        State { output = output } = state
        Just idx = location ident state
      Decr _ ident -> state {
        output = output . (load_variable idx "rax") . (string "  dec rax\n") . (set_variable idx "rax")
      } where
        State { output = output } = state
        Just idx = location ident state
      Ass _ ident exp -> nstate {
        output = output . (string "  pop rax\n") . (set_variable idx "rax")
      } where 
        nstate@State { output = output } = generate_expression exp state
        Just idx = location ident nstate
      Decl _ t arr -> 
        foldl merge state arr where
          merge state@State {
            output = output, 
            environment_stack = env : rest,
            local_id = local_id
          } e = case e of
            NoInit _ ident -> state {
              environment_stack = (Map.insert ident local_id env) : rest,
              output = output . set_variable local_id "0",
              local_id = local_id + 1
            }
            Init _ ident expr -> nstate {
              environment_stack = (Map.insert ident local_id env) : rest,
              output = output . (string "  pop rax\n") . (set_variable local_id "rax"),
              local_id = local_id + 1
            } where
              nstate@State { 
                output = output, 
                environment_stack = env : rest
              } = generate_expression expr state
  
  generate_block :: Show a => Block a -> StateData -> StateData
  generate_block (Block _ stmts) state = 
    foldl merge state stmts where
      merge state e = generate_statement e state

  generate_function :: Show a => TopDef a -> StateData -> StateData 
  generate_function 
    function@(FnDef _ t (Ident name) args block) 
    state@State { output = output, environment_stack = environment_stack } = 
      nstate {
        output = noutput . epilogue
      } where
        nstate@State { output = noutput } = generate_block block state {
          output = output . prologue, 
          environment_stack = argument_map:environment_stack,
          local_id = toInteger (length args)
        }
        argument_map = foldl insert Map.empty (zip args [0..]) where
          insert map ((Arg _ _ ident), idx) = Map.insert ident idx map
        prologue = 
          string (name ++ ":\n  enter " ++ show (required_stack function) ++ ", 0\n") .
          (foldl (.) (string "") list) where
            list = map load_argument [0..((length args) - 1)]
        epilogue = string
          "  leave\n\
          \  ret\n\n"
            

  compile_function :: Show a => TopDef a -> StateData -> StateData 
  compile_function func state@State { output = output } =
    case func of
      FnDef _ t ident _ block -> 
        case match_return_type t block of
          Nothing -> generate_function func state
          Just str -> state { error_output = str }

  compile :: Show a => Program a -> StateData -> StateData
  compile code state@State { output = output } = 
    case code of
      Program _ [] -> state { 
        output = (
          "section .text\n\n\
          \global _start\n\n\
          \extern printInt\n\
          \extern printString\n\
          \extern error\n\
          \extern readInt\n\
          \extern readString\n\n\
          \_start:\n\
          \  call main\n\
          \  mov rdi, rax\n\
          \  mov rax, 60\n\
          \  syscall\n\n"
        ++) . output
      }
      Program d (head:lst) -> 
        let
          fst = compile_function head state
          rest = compile (Program d lst) fst
        in
          rest
  
  