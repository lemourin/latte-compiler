module Compiler where
  
  import ParLatte
  import LexLatte
  import AbsLatte
  import ErrM
  import qualified Data.Map as Map
  
  data Value = 
    ValueInteger Integer

  data ValueType =
    StringValue | 
    IntegerValue | 
    BooleanValue |
    VoidValue |
    ErrorValue |
    FunctionValue ValueType [ValueType] deriving (Eq, Show)
  
  type Location = Integer

  type Environment = Map.Map Ident (ValueType, Location)

  type StringData = String -> String
  
  data StateData = State {
    environment_stack :: [Environment],
    error_output :: StringData,
    output :: StringData,
    local_id :: Integer,
    label_id :: Integer,
    current_function :: ValueType
  }

  string s = (++) s
  
  state_empty = State [] ("" ++) ("" ++) 0 0 ErrorValue

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

  to_value_type t =
    case t of
      Int _ -> IntegerValue
      Str _ -> StringValue
      Bool _ -> BooleanValue
      Void _ -> VoidValue

  contains_return :: Show a => TopDef a -> Bool
  contains_return func@(FnDef _ _ _ _ (Block _ stmts)) =
    foldl merge False stmts where
      merge found stmt = found || has_return stmt
      has_return stmt = case stmt of
        BStmt _ (Block _ stmts) -> foldl merge False stmts
        CondElse _ _ stmt1 stmt2 -> (has_return stmt1) && (has_return stmt2)
        VRet _ -> True
        Ret _ _ -> True
        _ -> False
  
  typeof :: Show a => Expr a -> StateData -> ValueType
  typeof expr state =
    case expr of
      EString _ _ -> StringValue
      EApp _ ident _ -> case location ident state of
        Just (FunctionValue t _, _) -> t
        Nothing -> ErrorValue
      ELitInt _ _ -> IntegerValue
      ELitTrue _ -> BooleanValue
      ELitFalse _ -> BooleanValue
      Neg _ _ -> IntegerValue
      Not _ _ -> BooleanValue
      EMul _ _ _ _ -> IntegerValue
      EAdd _ exp _ _ -> typeof exp state
      ERel _ _ _ _ -> BooleanValue
      EAnd _ _ _ -> BooleanValue
      EOr _ _ _ -> BooleanValue
      EVar _ ident -> case location ident state of 
        Just (t, _) -> t
        Nothing -> ErrorValue

  required_stack :: Show a => TopDef a -> Int
  required_stack function@(FnDef a _ _ args block) =
    8 * (length args + compute (BStmt a block)) where
      compute stmt = case stmt of
        BStmt _ (Block _ stmts) -> current + subblock where
          (current, subblock) = foldl merge (0, 0) stmts where
            merge (current, subblock) stmt =
              case stmt of
                Decl _ _ items -> (current + (length items), subblock)
                _ -> (current, max (compute stmt) subblock)
        Cond _ _ stmt -> compute stmt
        CondElse _ _ stmt_true stmt_false -> max (compute stmt_true) (compute stmt_false)
        While _ _ stmt -> compute stmt
        Decl _ _ items -> length items
        _ -> 0

  generate_string :: String -> StateData -> StateData
  generate_string ('"':str) state@State { output = output } = state {
    output = output . string (
      "  mov rdi, " ++ (show ((length text) + 1)) ++ "\n\
      \  call malloc\n"
    ) . copy_string text . string (
      "  mov byte [rax + " ++ (show (length str)) ++ "], 0\n\
      \  push rax\n"
    )
  } where
    text = init str
    copy_string str =
      foldl merge (string "") (zip str [0..]) where
        merge str (letter, idx) =
          str . string ("  mov byte [rax + " ++ (show idx) ++ "], '" ++ (letter:[]) ++ "'\n")

  generate_lazy_expression :: Show a => Expr a -> StateData -> StateData
  generate_lazy_expression expr state@State { label_id = label_id } =
    case expr of
      EOr _ e1 e2 -> result e1 e2 "cmp dword [rsp], 1"
      EAnd _ e1 e2 -> result e1 e2 "cmp dword [rsp], 0"
    where 
      result e1 e2 condition = rstate {
          output = routput . string (
            "L" ++ (show label_id) ++ ":\n"
          )
      } where
          rstate@State { output = routput } = generate_expression e2 nstate {
            output = noutput . string (
              "  " ++ condition ++ "\n\
              \  je L" ++ show label_id ++ "\n\
              \  add rsp, 8\n"
            )
          }
          nstate@State { output = noutput } = generate_expression e1 state {
            label_id = label_id + 1
          }

  generate_function_call :: Show a => Expr a -> StateData -> StateData
  generate_function_call (EApp position ident@(Ident id) expr) state =
    nstate {
      output = output . load_registers (length expr) . string (
        "  call " ++ id ++ "\n\
        \  add rsp, " ++ (show (8 * (max 0 ((length expr) - 6)))) ++ "\n\
        \  push rax\n"
      ),
      error_output = error_output . error
    } where
      nstate@State { 
        output = output, error_output = error_output 
      } = foldl merge state (reverse expr)
      merge state e = generate_expression e state
      error = case location ident state of
        Nothing -> string ((show position) ++ ": undefined function call " ++ id ++ "\n")
        Just ((FunctionValue _ args), _) -> 
          if (length expr) == (length args) then
            foldl merge (string "") (zip args expr)
          else
            string ((show position) ++ ": invalid argument count for function call " ++ show id ++ "\n")
          where 
            merge str (t, expr) = 
              if ftype /= t then
                string ((show position) ++ 
                  ": function argument type mismatch: expected " ++ (show t) ++ 
                  ", got " ++ (show ftype) ++ "\n")
              else
                str
              where ftype = typeof expr state
        _ -> string (id ++ " at " ++ (show position) ++ " is not a function\n")
  
  generate_variable_load :: Show a => Expr a -> StateData -> StateData
  generate_variable_load (EVar position ident) state@State { output = output, error_output = error_output } = 
    case location ident state of
      Just (_, idx) -> state {
        output = output . (load_variable idx "rax") . string "  push rax\n"
      }
      Nothing -> state {
        error_output = error_output . string (
          (show position) ++ ": undeclared variable " ++ (show ident) ++ "\n"
        )
      }

  generate_expression :: Show a => Expr a -> StateData -> StateData
  generate_expression expr state@State { 
    output = output, 
    error_output = error_output, 
    label_id = label_id 
  } =
    case expr of
      EVar _ _ -> generate_variable_load expr state
      ELitFalse a -> generate_expression (ELitInt a 0) state
      ELitTrue a -> generate_expression (ELitInt a 1) state
      EString _ str -> generate_string str state
      EApp _ _ _ -> generate_function_call expr state
      ELitInt _ int -> state {
        output = output . string ("  push " ++ (show int) ++ "\n")
      }
      EAnd _ _ _ -> generate_lazy_expression expr state
      EOr _ _ _ -> generate_lazy_expression expr state
      ERel p e1 op e2 -> nstate { label_id = label_id + 2 } where
        nstate@State { label_id = label_id } = merge_expressions p e1 e2 operation state
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
      EMul p e1 op e2 -> merge_expressions p e1 e2 operation state where
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
      EAdd p e1 op e2 -> merge_expressions p e1 e2 operation state where
        operation = case op of
          Plus _ -> case typeof e1 state of
            IntegerValue ->
              "  add rax, rcx\n\
              \  push rax\n"
            StringValue ->
              "  mov rdi, rax\n\
              \  mov rsi, rcx\n\
              \  call concatenate\n\
              \  push rax\n"
            _ -> ""
          Minus _ ->
            "  sub rax, rcx\n\
            \  push rax\n"
      Not _ expr -> nstate {
        output = output . string 
          "  pop rax\n\
          \  not rax\n\
          \  and rax, 1\n\
          \  push rax\n"
      } where
        nstate@State { output = output } = generate_expression expr state
      Neg _ expr -> nstate {
        output = output . string 
          "  pop rax\n\
          \  not rax\n\
          \  add rax, 1\n\
          \  push rax\n"
      } where
        nstate@State { output = output } = generate_expression expr state
      where
        merge_expressions position exp1 exp2 operation state =
          rstate { 
            output = output . string merge,
            error_output = error_output . error
          } where
            rstate@State { 
              output = output,
              error_output = error_output
            } = generate_expression exp2 nstate
            nstate = generate_expression exp1 state
            merge = 
              "  pop rcx\n\
              \  pop rax\n"
              ++ operation
            type1 = typeof exp1 state
            type2 = typeof exp2 state
            error = 
              if type1 == type2 || type1 == ErrorValue || type2 == ErrorValue then 
                string ""
              else
                string ((show position) ++ ": type mismatch (" ++ show type1 ++ ", " ++ show type2 ++ ")\n")

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

  generate_while :: Show a => Stmt a -> StateData -> StateData
  generate_while (While a exp stmt) state@State { 
    output = output,
    label_id = label_id
  } =
    rstate {
      output = routput . string (
        "  jmp L" ++ show label_id ++ "\n\
        \L" ++ show (label_id + 1) ++ ":\n"
      )
    } where
      rstate@State { output = routput } = generate_statement stmt nstate {
        output = noutput . string (
          "  pop rax\n\
          \  cmp rax, 0\n\
          \  je L" ++ show (label_id + 1) ++ "\n"
        )
      }
      nstate@State { output = noutput } = generate_expression exp state { 
        output = output . string ("L" ++ (show label_id) ++ ":\n"),
        label_id = label_id + 2
      }
  
  generate_assignment :: Show a => Stmt a -> StateData -> StateData
  generate_assignment (Ass position ident exp) state = 
    nstate {
        output = output . (string "  pop rax\n") . (set_variable idx "rax"),
        error_output = error_output . error
      } where 
        nstate@State { output = output, error_output = error_output } = generate_expression exp state
        (idx, error) = case location ident nstate of 
          Just (t, idx) -> 
            if t == exptype || exptype == ErrorValue then
              (idx, string "")
            else
              (0, string (show position ++ 
                ": type mismatch: expected " ++ show t ++ ", got " ++ (show exptype) ++ "\n"))
            where exptype = typeof exp state
          _ -> (0, string ((show position) ++ ": assignment to undeclared variable " ++ show ident ++ "\n"))

  generate_incrementation :: Show a => Stmt a -> StateData -> StateData
  generate_incrementation stmt state =
    case stmt of
      Incr position ident -> result position ident "inc"
      Decr position ident -> result position ident "dec"
    where
      result position ident operation = state {
        output = output . (load_variable idx "rax") . 
          (string ("  " ++ operation ++ " rax\n")) . (set_variable idx "rax"),
        error_output = error_output . error
      } where
        State { output = output, error_output = error_output } = state
        (idx, error) = case location ident state of
          Just (t, idx) -> case t of
            IntegerValue -> (idx, string "")
            _ -> (idx, string (show position ++ ": variable " ++ show ident ++ " not an IntegerValue\n"))
          Nothing -> (0, string (show position ++ ": undeclared variable " ++ show ident ++ "\n"))

  generate_statement :: Show a => Stmt a -> StateData -> StateData
  generate_statement stmt state@State { 
    output = output,
    error_output = error_output,
    environment_stack = environment_stack,
    current_function = FunctionValue return_type _ 
  } = 
    case stmt of
      Empty _ -> state
      BStmt _ block -> generate_block block state {
        environment_stack = Map.empty : environment_stack
      }
      SExp _ exp -> generate_expression exp state
      Cond a exp stmt -> generate_condition exp stmt (Empty a) state
      CondElse _ exp stmt1 stmt2 -> generate_condition exp stmt1 stmt2 state
      While _ _ _ -> generate_while stmt state
      VRet position -> state {
        output = output . string
          "  leave\n\
          \  ret\n",
        error_output = error_output . error
      } where 
        error = if return_type == VoidValue then
          string ""
        else
          string ((show position) ++ ": return value mismatch: expected " ++ (show return_type) ++ " got VoidValue\n")
      Ret position expr -> nstate { 
        output = output . string 
          "  pop rax\n\
          \  leave\n\
          \  ret\n",
        error_output = error_output . error
      } where
        nstate@State { output = output, error_output = error_output } = generate_expression expr state
        error = 
          if exptype /= return_type && exptype /= ErrorValue then
            string ((show position) ++ ": return value mismatch: expected " ++ 
              (show return_type) ++ " got " ++ show exptype ++ "\n")
          else
            string ""
          where exptype = typeof expr state
      Incr _ _ -> generate_incrementation stmt state
      Decr _ _ -> generate_incrementation stmt state
      Ass _ _ _ -> generate_assignment stmt state
      Decl _ t arr -> 
        foldl merge state arr where
          merge state@State {
            output = output,
            error_output = error_output,
            environment_stack = env : rest,
            local_id = local_id
          } e = case e of
            NoInit position ident -> state {
              environment_stack = (Map.insert ident ((to_value_type t), local_id) env) : rest,
              output = output . set_variable local_id "0",
              error_output = error_output . (error position ident env),
              local_id = local_id + 1
            }
            Init position ident expr -> nstate {
              environment_stack = (Map.insert ident ((to_value_type t), local_id) env) : rest,
              output = output . (string "  pop rax\n") . (set_variable local_id "rax"),
              error_output = error_output . (error position ident env) . type_error,
              local_id = local_id + 1
            } where
              nstate@State { 
                output = output,
                error_output = error_output,
                environment_stack = env : rest
              } = generate_expression expr state
              exptype = typeof expr state
              type_error = if (exptype /= (to_value_type t)) && (exptype /= ErrorValue) then
                string ((show position) ++ ": type mismatch: expected " ++ 
                  (show (to_value_type t)) ++ ", got " ++ (show exptype) ++ "\n")
              else
                string ""
            where
              error position ident env = case Map.lookup ident env of
                Nothing -> string ""
                Just _ -> string ((show position) ++ ": variable " ++ (show ident) ++ " redeclared\n")

  generate_cleanup :: StateData -> StateData
  generate_cleanup state@State { environment_stack = env:rest } =
    foldl merge state env where
      merge state@State {
        output = output
      } (t, l) = case t of
        StringValue -> state {
          output = output . load_variable l "rdi" . string (
            "  call free\n"
          )
        }
        _ -> state
  
  generate_block :: Show a => Block a -> StateData -> StateData
  generate_block (Block _ stmts) state = 
    foldl merge state stmts where
      merge state e = generate_statement e state

  generate_function :: Show a => TopDef a -> StateData -> StateData 
  generate_function 
    function@(FnDef position t (Ident name) args block) 
    state@State { 
      output = output, 
      error_output = error_output, 
      environment_stack = environment_stack,
      current_function = current_function
    } = 
      nstate {
        environment_stack = environment_stack,
        output = noutput . epilogue,
        error_output = nerror_output . function_error,
        current_function = current_function
      } where
        nstate@State { output = noutput, error_output = nerror_output } = generate_block block state {
          output = output . prologue, 
          error_output = error_output . error,
          environment_stack = argument_map:environment_stack,
          local_id = toInteger (length args),
          current_function = FunctionValue (to_value_type t) (map (\(Arg _ t _) -> to_value_type t) args)
        }
        (argument_map, error) = foldl insert (Map.empty, string "") (zip args [0..]) where
          insert (map, error) ((Arg position t ident), idx) =
            case Map.lookup ident map of
              Nothing -> (Map.insert ident (to_value_type t, idx) map, error)
              _ -> (map, error . string ((show position) ++ ": argument " ++ (show ident) ++ " redeclared\n"))
        prologue = 
          string (name ++ ":\n  enter " ++ show (required_stack function) ++ ", 0\n") .
          (foldl (.) (string "") list) where
            list = map load_argument [0..((length args) - 1)]
        epilogue = string
          "  leave\n\
          \  ret\n\n"
        function_error = if ((to_value_type t) /= VoidValue) && not (contains_return function) then
          string (show position ++ 
            ": function " ++ show name ++ ": control reaches end of non-void function\n")
        else
          string ""

  compile_function :: Show a => TopDef a -> StateData -> StateData 
  compile_function func@(FnDef _ t ident _ block) state@State { output = output } =
    generate_function func state

  compile :: Show a => Program a -> StateData -> StateData
  compile (Program d code) state =
    result initial_state where
      result state = foldl merge state code where
        merge state func = compile_function func state
      initial_state = 
        foldl merge state { 
          environment_stack = [Map.fromList [
            (Ident "printInt", (FunctionValue VoidValue [IntegerValue], 0)),
            (Ident "printString", (FunctionValue VoidValue [StringValue], 0)),
            (Ident "error", (FunctionValue VoidValue [], 0)),
            (Ident "readInt", (FunctionValue IntegerValue [], 0)),
            (Ident "readString", (FunctionValue StringValue [], 0))
          ]],
          output = string (
            "section .text\n\n\
            \global _start\n\n\
            \extern malloc\n\
            \extern free\n\
            \extern concatenate\n\
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
          )
        } code where
          merge state@State{ 
            environment_stack = [env], error_output = error_output 
          } (FnDef position t ident args _) = 
            state { 
              environment_stack = [Map.insert ident (func_type, 0) env],
              error_output = error_output . error 
            } where
              func_type = FunctionValue (to_value_type t) (map (\(Arg _ t _) -> to_value_type t) args)
              error = case Map.lookup ident env of
                Nothing -> string ""
                Just _ -> string ((show position) ++ ": function " ++ show ident ++ " redeclared\n")
  
  