module Compiler where

import ParLatte
import LexLatte
import AbsLatte
import PrintLatte
import ErrM
import Debug.Trace
import qualified Data.Map as Map

data Value = 
  ValueInteger Integer

data ValueType =
  StringValue | 
  IntegerValue | 
  BooleanValue |
  VoidValue |
  ErrorValue |
  ArrayValue ValueType |
  ClassValue Ident |
  FunctionValue ValueType [ValueType] deriving (Eq, Show, Ord)

type Location = Integer

type Environment = Map.Map Ident (ValueType, Location)

type StringData = String -> String

data ClassData = ClassData {
  field :: Map.Map Ident (ValueType, Integer),
  method :: Map.Map Ident ValueType,
  base :: ValueType
} deriving (Eq, Show)

data StateData = State {
  environment_stack :: [Environment],
  error_output :: StringData,
  output :: StringData,
  local_id :: Integer,
  label_id :: Integer,
  block_id :: Integer,
  stack_size :: Integer,
  string_set :: [String],
  string_count :: Integer,
  current_function :: ValueType,
  current_block :: Maybe Integer,
  parent_block :: Maybe Integer,
  class_data :: Map.Map ValueType ClassData,
  refcounted_variables :: [Integer]
}

string :: String -> StringData
string s = (++) s

class_empty :: ValueType -> ClassData
class_empty base = ClassData Map.empty Map.empty base

state_empty :: StateData
state_empty = State [] ("" ++) ("" ++) 0 0 0 0 [] 0 ErrorValue Nothing Nothing Map.empty []

argument_register :: Int -> Maybe String
argument_register i = 
  if i < 6 then
    Just (["rdi", "rsi", "rdx", "rcx", "r8", "r9"] !! i)
  else
    Nothing

load_registers :: Int -> StringData
load_registers i = load_registers_aux 0 where
  load_registers_aux idx =
    if idx >= i then
      string ""
    else case argument_register idx of
        Just register -> string ("  pop " ++ register ++ "\n") . load_registers_aux (idx + 1)
        Nothing -> string ""

location :: Ident -> StateData -> Maybe (ValueType, Location)
location ident state@State { environment_stack = env } =
  foldl merge Nothing env where
    merge current e = case current of
      Nothing -> Map.lookup ident e
      _ -> current

show_variable idx = string ("qword [rbp - " ++ (show (8 * (idx + 1))) ++ "]")

set_variable idx value =
  (string "  mov ") . show_variable idx . string (", " ++ value ++ "\n")

load_variable idx destination =
  (string ("  mov " ++ destination)) . (string ", ") . show_variable idx . string "\n"

push_variable idx =
  string "  push " . (show_variable idx) . string "\n"

load_argument idx =
  case argument_register idx of
    Just r -> set_variable idx r
    Nothing -> 
      string ("  mov rax, " ++ "[rbp + " ++ (show (8 * (idx - 6 + 2))) ++ "]\n") . set_variable idx "rax"

class_struct expr state@State { class_data = class_data } =
  case typeof expr state of
    ArrayValue _ -> (class_empty (ClassValue (Ident "_object"))) {
      field = Map.fromList [(Ident "length", (IntegerValue, 0))]
    }
    name -> case Map.lookup name class_data of
      Just t -> t

equal_types t1 t2 =
  case (t1, t2) of
    (ClassValue _, ClassValue _) -> True
    _ -> t1 == t2

class_offset :: ClassData -> Ident -> StateData -> Int
class_offset (ClassData { base = base, field = class_field }) field state@State {
  class_data = class_data
} = 
  offset where
    Just base_offset = sizeof base state
    field_offset = case Map.lookup field class_field of
      Just (_, x) -> x
      _ -> case Map.lookup base class_data of
        Just cls -> toInteger (class_offset cls field state)
    offset = base_offset + (fromInteger field_offset)

method_name :: String -> ClassData -> Ident -> StateData -> String
method_name class_name (ClassData { base = base, method = method_data }) method state@State {
  class_data = class_data
} =
  name where
    name = case Map.lookup method method_data of
      Just _ -> class_name ++ "_" ++ (printTree method)
      _ -> case Map.lookup base class_data of
        Just cls -> method_name base_name cls method state where
          ClassValue (Ident base_name) = base
        _ -> "error"

from_value_type :: Show a => a -> ValueType -> Type a
from_value_type p t =
  case t of
    IntegerValue -> Int p
    StringValue -> Str p
    BooleanValue -> Bool p
    VoidValue -> Void p
    ArrayValue q -> Array p (from_value_type p q)
    ClassValue id -> Class p id

to_value_type :: Show a => Type a -> ValueType
to_value_type t =
  case t of
    Int _ -> IntegerValue
    Str _ -> StringValue
    Bool _ -> BooleanValue
    Void _ -> VoidValue
    Array _ t -> ArrayValue (to_value_type t)
    Class _ ident -> ClassValue ident

is_refcounted :: ValueType -> Bool
is_refcounted t =
  case t of
    IntegerValue -> False
    VoidValue-> False
    BooleanValue -> False
    ErrorValue -> False
    _ -> True

relational_function operator = 
  case operator of
    LTH _ -> (<)
    LE _ -> (<=)
    GTH _ -> (>)
    GE _ -> (>=)
    EQU _ -> (==)
    NE _ -> (/=)

multiplicative_function operator =
  case operator of
    Times _ -> (*)
    Div _ -> (div)
    Mod _ -> \a b -> (signum a) * ((abs a) `mod` (abs b))

additive_function operator =
  case operator of
    Plus _ -> (+)
    Minus _ -> (-)

expression_to_integer expr =
  case expr of
    ELitTrue _ -> Just 1
    ELitFalse _ -> Just 0
    ELitInt _ value -> Just value
    _ -> Nothing

expression_to_boolean expr =
  case expr of
    ELitTrue _ -> Just True
    ELitFalse _ -> Just False
    _ -> Nothing

boolean_to_expression position b =
  if b then
    ELitTrue position
  else
    ELitFalse position

merge_expressions exp1 exp2 operation state =
  rstate { 
    output = output . string merge
  } where
    rstate@State { 
      output = output
    } = generate_expression exp2 nstate
    nstate = generate_expression exp1 state
    merge = 
      "  pop rcx\n\
      \  pop rax\n"
      ++ operation
    type1 = typeof exp1 state
    type2 = typeof exp2 state

simplify_expression :: Show a => Expr a -> Expr a
simplify_expression expr = 
  case expr of 
    ERel p expr1 op expr2 -> 
      case (simplify_expression expr1, simplify_expression expr2) of
        (e1, e2) -> case (expression_to_integer e1, expression_to_integer e2) of
          (Just a, Just b) -> boolean_to_expression p (relational_function op a b)
          _ -> ERel p e1 op e2
    EMul p expr1 op expr2 ->
      case (simplify_expression expr1, simplify_expression expr2) of
        (e1, e2) -> case (expression_to_integer e1, expression_to_integer e2) of
          (Just a, Just b) -> ELitInt p (multiplicative_function op a b)
          _ -> EMul p e1 op e2
    EAdd p expr1 op expr2 ->
      case (simplify_expression expr1, simplify_expression expr2) of
        (e1, e2) -> case (expression_to_integer e1, expression_to_integer e2) of
          (Just a, Just b) -> ELitInt p (additive_function op a b)
          _ -> EAdd p e1 op e2
    EAnd p expr1 expr2 ->
      case (simplify_expression expr1, simplify_expression expr2) of
        (e1, e2) -> case (expression_to_boolean e1, expression_to_boolean e2) of
          (Just a, Just b) -> boolean_to_expression p (a && b)
          _ -> EAnd p e1 e2
    EOr p expr1 expr2 ->
      case (simplify_expression expr1, simplify_expression expr2) of
        (e1, e2) -> case (expression_to_boolean e1, expression_to_boolean e2) of
          (Just a, Just b) -> boolean_to_expression p (a || b)
          _ -> EOr p e1 e2
    Not p expr ->
      case simplify_expression expr of
        e -> case expression_to_boolean e of
          Just a -> boolean_to_expression p (not a)
          _ -> Not p e
    Neg p expr ->
      case simplify_expression expr of
        e -> case expression_to_integer e of
          Just a -> ELitInt p (-a)
          _ -> Neg p e
    _ -> expr

contains_return :: Show a => TopDef a -> Bool
contains_return func@(FnDef _ _ _ _ (Block _ stmts)) =
  foldl merge False stmts where
    merge found stmt = found || has_return stmt
    has_return stmt = case stmt of
      BStmt _ (Block _ stmts) -> foldl merge False stmts
      Cond _ expr stmt -> 
        case simplify_expression expr of
          ELitTrue _ -> has_return stmt
          _ -> False
      CondElse _ expr stmt1 stmt2 -> 
        case simplify_expression expr of
          ELitTrue _ -> has_return stmt1
          ELitFalse _ -> has_return stmt2
          _ -> (has_return stmt1) && (has_return stmt2)
      VRet _ -> True
      Ret _ _ -> True
      _ -> False

expression_position :: Show a => Expr a -> a
expression_position expr =
  case expr of
    EString p _ -> p
    ENull p _ -> p
    EApp p _ _ -> p
    ELitInt p _ -> p
    ELitTrue p -> p
    ELitFalse p -> p
    Neg p _ -> p
    Not p _ -> p
    EMul p _ _ _ -> p
    EAdd p _ _ _ -> p
    ERel p _ _ _ -> p
    EAnd p _ _ -> p
    EOr p _ _ -> p
    EVar p _ -> p

typeof :: Show a => Expr a -> StateData -> ValueType
typeof expr state@State { class_data = class_data } =
  case expr of
    EString _ _ -> StringValue
    ENull _ t -> to_value_type t
    EApp _ ident _ -> case location ident state of
      Just (FunctionValue t _, _) -> t
      Nothing -> ErrorValue
    EArrayGet _ e _ -> case typeof e state of
      ArrayValue t -> t
      _ -> ErrorValue
    EFieldGet _ e ident -> case typeof e state of
      t@(ArrayValue _) -> if ident == Ident "length" then IntegerValue else ErrorValue
      t@(ClassValue _) -> ErrorValue
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
    EArray _ t _ -> ArrayValue (to_value_type t)
    EObject _ t -> ClassValue t
    EMethodSimple p lvalue ident args -> typeof (EMethod p (EVar p lvalue) ident args) state
    EMethod _ e ident _ -> method_type (Map.lookup (typeof e state) class_data) where
      method_type cls =
        case cls of
          Just ClassData { method = method, base = base } -> 
            case Map.lookup ident method of
              Just (FunctionValue t _) -> t
              _ -> method_type (Map.lookup base class_data)
          _ -> ErrorValue
    EVar p lvalue -> case lvalue of
      LValueIdent _ ident -> case location ident state of 
        Just (t, _) -> t
        Nothing -> case location (Ident "self") state of
          Just x -> typeof (EVar p (LValueField p (LValueIdent p (Ident "self")) ident)) state
          _ -> ErrorValue
      LValueArray p l _ -> case typeof (EVar p l) state of
        ArrayValue t -> t
        _ -> ErrorValue
      LValueField p f ident -> case typeof (EVar p f) state of
        t@(ArrayValue _) -> if ident == Ident "length" then IntegerValue else ErrorValue
        t@(ClassValue _) -> field_type (Map.lookup t class_data) where
          field_type cls =
            case cls of
              Just ClassData { field = field, base = base } -> 
                case Map.lookup ident field of
                  Just (t, _) -> t
                  _ -> field_type (Map.lookup base class_data)
              _ -> ErrorValue
        _ -> ErrorValue

sizeof :: ValueType -> StateData -> Maybe Int
sizeof t state@State { class_data = class_data } = 
  case t of
    ClassValue (Ident "_object") -> Just 2
    ClassValue ident -> case Map.lookup t class_data of
      Just x@ClassData { field = field, base = base } -> 
        case sizeof base state of
          Just x -> Just (x + Map.size field)
          _ -> Nothing
      _ -> Nothing

match_type :: Show a => Expr a -> [ValueType] -> StateData -> StringData
match_type exp t state = 
  if exptype /= ErrorValue && (notElem exptype t) && not_class then
    string ((show (expression_position exp)) ++ ": expected one of " ++ show t ++ 
      ", got " ++ show exptype ++ "\n")
  else
    string ""
  where 
    exptype = typeof exp state
    not_class = case exptype of
      ClassValue _ -> False
      _ -> True

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
      ForEach _ _ _ _ _ -> compute (translate_foreach stmt)
      _ -> 0

generate_string :: String -> StateData -> StateData
generate_string ('"':str) state@State { 
  output = output, 
  string_set = string_set, 
  string_count = string_count, 
  stack_size = stack_size
} = state {
  output = output . stack_align_prologue . string (
    "  mov rdi, str" ++ (show string_count) ++ "\n\
    \  call string_new\n"
  ) . stack_align_epilogue . string "  push rax\n",
  stack_size = stack_size + 1,
  string_set = text : string_set,
  string_count = string_count + 1
} where
  text = init str
  stack_align = (stack_size `mod` 2) == 0
  stack_align_prologue = string (if stack_align then "  sub rsp, 8\n" else "")
  stack_align_epilogue = string (if stack_align then "  add rsp, 8\n" else "")

generate_lazy_expression :: Show a => Expr a -> StateData -> StateData
generate_lazy_expression expr state@State { label_id = label_id } =
  case expr of
    EOr _ e1 e2 -> result e1 e2 "cmp dword [rsp], 1"
    EAnd _ e1 e2 -> result e1 e2 "cmp dword [rsp], 0"
  where 
    result e1 e2 condition = rstate {
        output = routput . string (
          "L" ++ (show label_id) ++ ":\n"
        ),
        stack_size = stack_size - 1,
        error_output = error_output . match_type e1 [BooleanValue] state . 
          match_type e2 [BooleanValue] state
    } where
        rstate@State { 
          output = routput, 
          error_output = error_output,
          stack_size = stack_size
        } = generate_expression e2 nstate {
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
generate_function_call (EApp position ident@(Ident id) expr) state@State {
  output = output,
  stack_size = stack_size
} =
  nstate {
    output = noutput . load_registers (length expr) . string (
      "  call " ++ id ++ "\n\
      \  add rsp, " ++ (show (8 * stack_slots)) ++ "\n\
      \  push rax\n"
    ),
    error_output = error_output . error,
    stack_size = nstack_size - fromIntegral (length expr) - (if stack_align then 1 else 0) + 1
  } where
    nstate@State { 
      output = noutput, error_output = error_output, stack_size = nstack_size
    } = foldl merge state {
      output = output . 
        string (if stack_align then "  sub rsp, 8\n" else ""),
      stack_size = stack_size + (if stack_align then 1 else 0)
    } (reverse expr)
    merge state e = generate_expression e state
    stack_align = ((stack_arguments + stack_size) `mod` 2) == 0
    stack_arguments = toInteger (max 0 ((length expr) - 6))
    stack_slots = stack_arguments + (if stack_align then 1 else 0)
    error = case location ident state of
      Nothing -> string ((show position) ++ ": undefined function call " ++ id ++ "\n")
      Just ((FunctionValue _ args), _) -> 
        if (length expr) == (length args) then
          foldl merge (string "") (zip args expr)
        else
          string ((show position) ++ ": invalid argument count for function call " ++ show id ++ "\n")
        where 
          merge str (t, expr) = 
            if not (equal_types ftype t) then
              string ((show position) ++ 
                ": function argument type mismatch: expected " ++ (show t) ++ 
                ", got " ++ (show ftype) ++ "\n")
            else
              str
            where ftype = typeof expr state
      _ -> string (id ++ " at " ++ (show position) ++ " is not a function\n")

generate_find_variable :: Show a => Expr a -> StateData -> StateData
generate_find_variable expr@(EVar position lvalue) state@State {
  output = output, 
  error_output = error_output, 
  stack_size = stack_size, 
  class_data = class_data,
  current_function = current_function
} = case lvalue of
  LValueField _ lvalue field -> nstate {
    output = output . string (
      "  pop rax\n\
      \  mov rax, [rax]\n\
      \  add rax, " ++ (show (8 * offset)) ++ "\n\
      \  push rax\n"
    ),
    error_output = error_output
  } where 
    offset = class_offset (class_struct (EVar position lvalue) state) field state
    nstate@State{ output = output, error_output = error_output } = 
      generate_find_variable (EVar position lvalue) state
  LValueIdent _ ident -> case location ident state of
    Just (t, idx) -> state {
      output = output . string (
        "  mov rax, rbp\n\
        \  sub rax, " ++ (show (8 * (idx + 1))) ++ "\n\
        \  push rax\n"),
      stack_size = stack_size + 1
    }
    Nothing -> case location (Ident "self") state of
      Just x -> generate_find_variable 
        (EVar position (LValueField position (LValueIdent position (Ident "self")) ident)) state
      _ -> state {
        error_output = error_output . string (
          (show position) ++ ": undeclared variable " ++ (show ident) ++ "\n"
        )
    }
  LValueArray _ lvalue expr -> rstate {
    output = output . string
      "  pop rdi\n\
      \  pop rsi\n\
      \  mov rdi, [rdi]\n\
      \  call array_get\n\
      \  push rax\n"
  } where
    rstate@State { output = output } = generate_find_variable (EVar position lvalue) nstate
    nstate = generate_expression expr state

generate_variable_load :: Show a => Expr a -> StateData -> StateData
generate_variable_load expr@(EVar position lvalue) state@State { 
  output = output, error_output = error_output, stack_size = stack_size
} =
  nstate {
    output = output . string
      "  pop rax\n\
      \  mov rax, [rax]\n\
      \  push rax\n" . (string increase_refcount)
  } where 
    nstate@State { output = output } = generate_find_variable expr state
    increase_refcount = if is_refcounted (typeof expr state) then
      "  mov rdi, [rsp]\n\
      \  call increase_refcount\n"
    else
      ""

generate_array :: Show a => Expr a -> StateData -> StateData
generate_array (EArray p t expr) state = 
  nstate {
    output = output . string ("  pop rdi\n  call " ++ array_create ++ "\n  push rax\n")
  } where 
    nstate@State { output = output } = generate_expression expr state
    array_create = 
      if is_refcounted (to_value_type t) then
        "array_object_new"
      else
        "array_new"

generate_object :: Show a => Expr a -> StateData -> StateData
generate_object (EObject p t) state@State { output = output } =
  state {
    output = output . string (
      "  mov rdi, " ++ (show (8 * size)) ++ "\n\
      \  call object_new\n\
      \  mov qword [rax + 8], " ++ (printTree t) ++ "_destructor\n\
      \  push rax\n"
    )
  } where 
    size = case sizeof (to_value_type (Class p t)) state of
      Just x -> x
      _ -> 0

generate_relation_expression :: Show a => Expr a -> StateData -> StateData
generate_relation_expression (ERel p e1 op e2) state = 
  nstate { 
    label_id = label_id + 2, 
    error_output = error_output . error_one . error_two . error_not_same,
    stack_size = stack_size - 1
  } where
    error_one = match_type e1 [IntegerValue, BooleanValue] state
    error_two = match_type e2 [IntegerValue, BooleanValue] state
    error_not_same = 
      if error_one "" == "" && error_two "" == "" then
        match_type e1 [(typeof e2 state)] state
      else
        string ""
    nstate@State { 
      label_id = label_id, error_output = error_output, stack_size = stack_size
    } = merge_expressions e1 e2 operation state
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

generate_multiplication_expression :: Show a => Expr a -> StateData -> StateData
generate_multiplication_expression (EMul _ e1 op e2) state =
  nstate { 
      error_output = error_output . 
        match_type e1 [IntegerValue] state . match_type e2 [IntegerValue] state,
      stack_size = stack_size - 1
    } where
      nstate@State { error_output = error_output, stack_size = stack_size } =
        merge_expressions e1 e2 operation state
      operation = case op of
        Times _ -> 
          "  imul rax, rcx\n\
          \  push rax\n"
        Div _ -> 
          "  mov rdx, 0\n\
          \  idiv rcx\n\
          \  push rax\n"
        Mod _ -> 
          "  mov rdx, 0\n\
          \  idiv rcx\n\
          \  push rdx\n"

generate_add_expression :: Show a => Expr a -> StateData -> StateData
generate_add_expression (EAdd p e1 op e2) state =
  nstate {
    error_output = error_output . error, stack_size = stack_size - 1 
  } where
    nstate@State { error_output = error_output, stack_size = stack_size } = 
      merge_expressions e1 e2 operation state
    (operation, error) = case op of
      Plus _ -> case (typeof e1 state, typeof e2 state) of
        (IntegerValue, IntegerValue) -> (
          "  add rax, rcx\n\
          \  push rax\n", string "")
        (StringValue, StringValue) -> (
          "  mov rdi, rax\n\
          \  mov rsi, rcx\n\
          \  call string_concatenate\n\
          \  push rax\n", string "")
        (t1, t2) -> ("", 
          type_mismatch_error p t1 t2 
            "expected (StringValue, StringValue) or (IntegerValue, IntegerValue)")
      Minus _ -> case (typeof e1 state, typeof e2 state) of
        (IntegerValue, IntegerValue) -> (
          "  sub rax, rcx\n\
          \  push rax\n", string "")
        (t1, t2) -> ("", type_mismatch_error p t1 t2 "expected (IntegerValue, IntegerValue)")
      where 
        type_mismatch_error p t1 t2 expected = 
          if t1 /= ErrorValue && t2 /= ErrorValue then
            string ((show p) ++ ": type mismatch: got (" ++ 
              (show t1) ++ ", " ++ (show t2) ++ "), " ++ expected ++ "\n")
          else
            string ""

generate_expression :: Show a => Expr a -> StateData -> StateData
generate_expression expr state@State { output = output } =
  nstate {
    output = noutput . string ("; end " ++ printTree expr ++ "\n")
  } where
    nstate@State {output = noutput} = generate_expression_aux (simplify_expression expr) state { 
      output = output . string ("; begin " ++ printTree expr ++ "\n") 
    }

generate_array_get :: Show a => Expr a -> StateData -> StateData
generate_array_get (EArrayGet _ exp1 exp2) state =
  rstate {
    output = output . string
      "  pop rdi\n\
      \  pop rsi\n\
      \  push rbx\n\
      \  mov rbx, rdi\n\
      \  call array_get\n\
      \  mov rdi, rbx\n\
      \  mov rbx, [rax]\n\
      \  call decrease_refcount\n\
      \  mov rax, rbx\n\
      \  pop rbx\n\
      \  push rax\n"
  } where
    rstate@State { output = output } = generate_expression_aux exp1 nstate
    nstate = generate_expression_aux exp2 state

generate_field_get :: Show a => Expr a -> StateData -> StateData
generate_field_get (EFieldGet _ expr ident) state =
  nstate {
    output = output . string (
      "  pop rax\n\
      \  push rbx\n\
      \  mov rbx, [rax + " ++ show (8 * offset) ++ "]\n\
      \  mov rdi, rax\n\
      \  call decrease_refcount\n\
      \  mov rax, rbx\n\
      \  pop rbx\n\
      \  push rax\n")
  } where
    offset = class_offset (class_struct expr state) ident state
    nstate@State {
      output = output
    } = generate_expression_aux expr state

generate_method_call :: Show a => Expr a -> StateData -> StateData
generate_method_call (EMethod p exp ident args) state =
  generate_function_call (EApp p (Ident func_name) (exp:args)) state
  where
    ClassValue (Ident name) = typeof exp state
    cls = class_struct exp state
    func_name = method_name name cls ident state
    nstate@State { output = output } = state

generate_expression_aux :: Show a => Expr a -> StateData -> StateData
generate_expression_aux expr state@State {
  output = output, 
  error_output = error_output, 
  label_id = label_id,
  stack_size = stack_size
} =
  case expr of
    EVar _ _ -> generate_variable_load expr state
    ENull _ _ -> state { output = output . string "  push 0\n", stack_size = stack_size + 1 }
    ELitFalse a -> generate_expression_aux (ELitInt a 0) state
    ELitTrue a -> generate_expression_aux (ELitInt a 1) state
    EString _ str -> generate_string str state
    EApp _ _ _ -> generate_function_call expr state
    EArray _ _ _ -> generate_array expr state
    EObject _ _ -> generate_object expr state
    EArrayGet _ _ _ -> generate_array_get expr state
    EFieldGet _ _ _ -> generate_field_get expr state
    EMethodSimple p lvalue ident args -> 
      generate_method_call (EMethod p (EVar p lvalue) ident args) state
    EMethod _ _ _ _ -> generate_method_call expr state
    ELitInt _ int -> state {
      output = output . string ("  push " ++ (show int) ++ "\n"),
      stack_size = stack_size + 1
    }
    EAnd _ _ _ -> generate_lazy_expression expr state
    EOr _ _ _ -> generate_lazy_expression expr state
    ERel _ _ _ _ -> generate_relation_expression expr state
    EMul _ _ _ _ -> generate_multiplication_expression expr state
    EAdd _ _ _ _ -> generate_add_expression expr state
    Not _ expr -> nstate {
      output = output . string 
        "  pop rax\n\
        \  not rax\n\
        \  and rax, 1\n\
        \  push rax\n",
      error_output = error_output . match_type expr [BooleanValue] state
    } where
      nstate@State { output = output, error_output = error_output } = generate_expression_aux expr state
    Neg _ expr -> nstate {
      output = output . string 
        "  pop rax\n\
        \  not rax\n\
        \  add rax, 1\n\
        \  push rax\n",
      error_output = error_output . match_type expr [IntegerValue] state
    } where
      nstate@State { output = output, error_output = error_output } = generate_expression_aux expr state

generate_condition :: Show a => Expr a -> Stmt a -> Stmt a -> StateData -> StateData
generate_condition exp stmt_true stmt_false state =
  rstate_next {
    output = routput . string(
      "L" ++ (show (label_id + 2)) ++ ":\n"
    ),
    error_output = error_output . match_type exp [BooleanValue] state
  } where
    rstate_next@State { output = routput, error_output = error_output } = 
      generate_statement stmt_false rstate {
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
      label_id = label_id + 3,
      stack_size = stack_size - 1
    }
    nstate@State { 
      output = output, label_id = label_id, stack_size = stack_size
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
      ),
      stack_size = stack_size - 1
    }
    nstate@State { output = noutput, stack_size = stack_size } = generate_expression exp state { 
      output = output . string ("L" ++ (show label_id) ++ ":\n"),
      label_id = label_id + 2
    }

generate_assignment :: Show a => Stmt a -> StateData -> StateData
generate_assignment (Ass position lvalue exp) state = 
  rstate {
      output = output . (string 
        "  pop rax\n\
        \  pop rdi\n\
        \  push qword [rax]\n\
        \  mov [rax], rdi\n\
        \  pop rdi\n") . string decrease_refcount,
      error_output = error_output . error,
      stack_size = stack_size - 2
    } where 
      rstate@State { output = output, error_output = error_output, stack_size = stack_size } = 
        generate_find_variable (EVar position lvalue) nstate
      nstate = generate_expression exp state
      decrease_refcount = 
        if is_refcounted t1 then 
          "  call decrease_refcount\n"
        else 
          ""
      t1 = typeof (EVar position lvalue) state
      t2 = typeof exp state
      error = 
        if not (equal_types t1 t2) && t1 /= ErrorValue && t2 /= ErrorValue then
          string ((show position) ++ 
            ": type mismatch in assignment: expected " ++ (show t1) ++ ", got " ++ (show t2) ++ "\n")
        else
          string ""

generate_incrementation :: Show a => Stmt a -> StateData -> StateData
generate_incrementation stmt state =
  case stmt of
    Incr position lvalue -> result position lvalue "inc"
    Decr position lvalue -> result position lvalue "dec"
  where
    result position lvalue operation = nstate {
      output = output . string ("  pop rax\n" ++ operation ++ " qword [rax]\n"),
      error_output = error_output . error
    } where
      nstate@State { output = output, error_output = error_output } = 
        generate_find_variable (EVar position lvalue) state
      error = match_type (EVar position lvalue) [IntegerValue] state

generate_declaration :: Show a => Stmt a -> StateData -> StateData
generate_declaration (Decl _ t arr) state =
  foldl merge state arr where
    merge state@State {
      output = output,
      error_output = error_output,
      environment_stack = env : rest,
      local_id = local_id,
      refcounted_variables = refcounted_variables
    } e = case e of
      NoInit position ident -> state {
        environment_stack = (Map.insert ident ((to_value_type t), local_id) env) : rest,
        output = output . set_variable local_id "0",
        error_output = error_output . (error position ident env),
        local_id = local_id + 1,
        refcounted_variables = 
          (if is_refcounted (to_value_type t) then [local_id] else []) ++ refcounted_variables
      }
      Init position ident expr -> nstate {
        environment_stack = (Map.insert ident ((to_value_type t), local_id) env) : rest,
        output = output . (string "  pop rax\n") . (set_variable local_id "rax"),
        error_output = error_output . (error position ident env) . type_error,
        local_id = local_id + 1,
        stack_size = stack_size - 1,
        refcounted_variables = 
          (if is_refcounted (to_value_type t) then [local_id] else []) ++ refcounted_variables
      } where
        nstate@State { 
          output = output,
          error_output = error_output,
          environment_stack = env : rest,
          stack_size = stack_size,
          refcounted_variables = refcounted_variables
        } = generate_expression expr state
        exptype = typeof expr state
        type_error = if not (equal_types exptype (to_value_type t)) && (exptype /= ErrorValue) then
          string ((show position) ++ ": type mismatch: expected " ++ 
            (show (to_value_type t)) ++ ", got " ++ (show exptype) ++ "\n")
        else
          string ""
      where
        error position ident env = case Map.lookup ident env of
          Nothing -> string ""
          Just _ -> string ((show position) ++ ": variable " ++ (show ident) ++ " redeclared\n")

generate_return :: Show a => Stmt a -> StateData ->StateData
generate_return (Ret position expr) state@State {
  current_function = FunctionValue return_type _
} = nstate {
  output = output . string "  mov rbx, 1\n" . string ret,
  error_output = error_output . error,
  stack_size = stack_size - 1
} where
  ret = case parent_block of
    Nothing -> ""
    Just i -> "  jmp B" ++ show i ++ "\n"
  nstate@State {
    output = output,
    error_output = error_output,
    stack_size = stack_size,
    parent_block = parent_block
  } = generate_expression expr state
  error = 
    if exptype /= return_type && exptype /= ErrorValue then
      string ((show position) ++ ": return value mismatch: expected " ++ 
        (show return_type) ++ " got " ++ show exptype ++ "\n")
    else
      string ""
    where exptype = typeof expr state

generate_return_void :: Show a => Stmt a -> StateData ->StateData
generate_return_void (VRet position) state@State {
  current_function = FunctionValue return_type _,
  parent_block = parent_block,
  current_block = current_block,
  stack_size = stack_size,
  output = output,
  error_output = error_output
} = state {
  output = output . string "  mov rbx, 1\n" . string ret,
  error_output = error_output . error,
  stack_size = stack_size - 1
} where
  ret = case parent_block of
    Nothing -> ""
    Just i -> "  jmp B" ++ show i ++ "\n" 
  error = if return_type == VoidValue then
    string ""
  else
    string ((show position) ++ 
      ": return value mismatch: expected " ++ (show return_type) ++ " got VoidValue\n")

generate_expression_statement :: Show a => Stmt a -> StateData ->StateData
generate_expression_statement (SExp _ exp) state = 
  nstate {
      output = output . decrease_ref,
      stack_size = stack_size - 1
    } where
      nstate@State { output = output, stack_size = stack_size } = generate_expression exp state
      decrease_ref = 
        if is_refcounted (typeof exp state) then 
          string 
            "  pop rdi\n\
            \  call decrease_refcount\n"
        else 
          string "  add rsp, 8\n"

translate_foreach :: Show a => Stmt a -> Stmt a
translate_foreach (ForEach p t ident expr stmt) = foreach where
  foreach = (BStmt p (Block p [
    (Decl p (Int p) [NoInit p (Ident "_idx")]),
    (Decl p (Array p t) [Init p (Ident "_array") expr]),
    (While p condition body)]))
  condition = ERel p left_side (LTH p) right_side
  left_side = EVar p (LValueIdent p (Ident "_idx"))
  right_side = EVar p (LValueField p (LValueIdent p (Ident "_array")) (Ident "length"))
  body = BStmt p (Block p [
    (Decl p t [
      Init p ident (
        EVar p (
          LValueArray p 
            (LValueIdent p (Ident "_array")) 
            (EVar p (LValueIdent p (Ident "_idx")))
        )
      )
    ]),
    stmt,
    (Incr p (LValueIdent p (Ident "_idx")))])

generate_foreach :: Show a => Stmt a -> StateData -> StateData
generate_foreach foreach state =
  generate_statement (translate_foreach foreach) state

generate_statement :: Show a => Stmt a -> StateData -> StateData
generate_statement stmt state@State { 
  output = output,
  error_output = error_output,
  environment_stack = environment_stack,
  current_function = FunctionValue return_type _,
  stack_size = stack_size,
  parent_block = parent_block,
  current_block = current_block,
  block_id = block_id,
  refcounted_variables = refcounted_variables
} = 
  case stmt of
    Empty _ -> state
    BStmt _ block -> nstate { environment_stack = rest } where
      nstate@State { environment_stack = _ : rest } = generate_block block state {
        environment_stack = Map.empty : environment_stack,
        parent_block = current_block
      }
    SExp _ _ -> generate_expression_statement stmt state
    Cond a exp stmt -> generate_condition exp stmt (Empty a) state
    CondElse _ exp stmt1 stmt2 -> generate_condition exp stmt1 stmt2 state
    ForEach _ _ _ _ _ -> generate_foreach stmt state
    While _ _ _ -> generate_while stmt state
    VRet _ -> generate_return_void stmt state
    Ret _ _ -> generate_return stmt state
    Incr _ _ -> generate_incrementation stmt state
    Decr _ _ -> generate_incrementation stmt state
    Ass _ _ _ -> generate_assignment stmt state
    Decl _ _ _ -> generate_declaration stmt state

generate_block :: Show a => Block a -> StateData -> StateData
generate_block (Block _ stmts) state@State { 
  block_id = block_id,
  local_id = local_id,
  parent_block = parent_block,
  current_block = current_block,
  refcounted_variables = refcounted_variables
} = nstate {
    output = output . string ("B" ++ (show block_id) ++ ": \n") . cleanup . go_back,
    current_block = current_block,
    parent_block = parent_block,
    refcounted_variables = refcounted_variables,
    local_id = local_id
  } where
    nstate@State { output = output, refcounted_variables = cleanup_vars } = foldl merge state {
      current_block = Just block_id,
      block_id = block_id + 1,
      refcounted_variables = if current_block == Nothing then refcounted_variables else []
    } stmts
    cleanup = foldl merge (string (
      "; cleanup\n\
      \; " ++ (show cleanup_vars) ++ "\n")) cleanup_vars where
        merge str v = str . load_variable v "rdi" . string "  call decrease_refcount\n"
    go_back = case current_block of
      Nothing -> string ""
      Just i -> string (
        "  cmp rbx, 1\n\
        \  je B" ++ (show i) ++ "\n")
    merge state e = generate_statement e state

generate_function :: Show a => TopDef a -> StateData -> StateData 
generate_function 
  function@(FnDef position t (Ident name) args block) 
  state@State { 
    output = output, 
    error_output = error_output, 
    environment_stack = environment_stack,
    current_function = current_function,
    block_id = block_id
  } = 
    nstate {
      environment_stack = environment_stack,
      output = noutput . epilogue,
      error_output = nerror_output . function_error,
      current_function = current_function
    } where
      nstate@State { 
        output = noutput, 
        error_output = nerror_output
      } = generate_block block state {
        output = output . prologue, 
        error_output = error_output . error,
        environment_stack = argument_map:environment_stack,
        local_id = toInteger (length args),
        current_function = 
          FunctionValue (to_value_type t) (map (\(Arg _ t _) -> to_value_type t) args),
        parent_block = Just block_id,
        stack_size = fromIntegral (2 + ((required_stack function) `div` 8)),
        refcounted_variables =
          map snd (filter (\((Arg _ t _), _) -> is_refcounted (to_value_type t)) (zip args [0..]))
      }
      (argument_map, error) = foldl insert (Map.empty, string "") (zip args [0..]) where
        insert (map, error) ((Arg position t ident), idx) =
          case Map.lookup ident map of
            Nothing -> (Map.insert ident (to_value_type t, idx) map, error)
            _ -> (map, error . string ((show position) ++ ": argument " ++ (show ident) ++ " redeclared\n"))
      prologue = 
        string (name ++ ":\n  enter " ++ 
          show (required_stack function) ++ ", 0\n  push rbx\n  mov rbx, 0\n") .
        (foldl (.) (string "") list) where
          list = map load_argument [0..((length args) - 1)]
      epilogue = string (
          if (to_value_type t) /= VoidValue then 
            "  pop rax\n"
          else 
            ""
        ) . string
        "  pop rbx\n\
        \  leave\n\
        \  ret\n\n"
      function_error = if ((to_value_type t) /= VoidValue) && not (contains_return function) then
        string (show position ++ 
          ": function " ++ show name ++ ": control reaches end of non-void function\n")
      else
        string ""

generate_destructor :: ValueType -> StateData -> StateData
generate_destructor ident@(ClassValue d) state@State { output = output, class_data = class_data } =
  state { 
    output = output . string (
      (printTree d) ++ "_destructor:\n"
    ) . string "  push rbx\n  mov rbx, rdi\n" . free . (call_base base) . string "  pop rbx\n  ret\n\n"
  } where
    call_base id@(ClassValue d) = string (
      "  mov rdi, rbx\n\
      \  call " ++ (printTree d) ++ "_destructor\n")
    Just cls@ClassData { field = field, base = base } = Map.lookup ident class_data
    free = foldl merge (string "") field
    (Just base_size) = sizeof base state
    merge str (t, location) = 
      if is_refcounted t then
        str . string (
          "  mov rdi, rbx\n\
          \  add rdi, " ++ (show idx) ++ "\n\
          \  mov rdi, [rdi]\n\
          \  call decrease_refcount\n")
      else
        str
      where
        idx = 8 * ((toInteger base_size) + location)

translate_method :: Show a => String -> ClassElement a -> TopDef a
translate_method class_name (ClassMethod p ret (Ident name) args block) =
  FnDef p ret (Ident (class_name ++ "_" ++ name))
    ((Arg p (Class p (Ident class_name)) (Ident "self")):args) block

generate_class_definition :: Show a => TopDef a -> StateData -> StateData
generate_class_definition (ClassDef _ def) state =
  case def of
    ClassExtends _ ident base defs -> generate (ClassValue ident) base defs state
    ClassBase _ ident defs -> generate (ClassValue ident) (Ident "_object") defs state
  where 
    generate ident base defs state = 
      foldl merge (generate_destructor ident state) defs where
        ClassValue (Ident class_name) = ident
        merge state d = case d of
          ClassMethod _ _ _ _ _ -> 
            compile_top_definition (translate_method class_name d) state
          _ -> state

compile_top_definition :: Show a => TopDef a -> StateData -> StateData 
compile_top_definition def state =
  case def of
    FnDef _ _ _ _ _ -> generate_function def state
    ClassDef _ _ -> generate_class_definition def state

get_top_definition :: Show a => TopDef a -> StateData -> StateData
get_top_definition definition state@State{ 
  environment_stack = [env], error_output = error_output, class_data = class_data
} = 
  case definition of
    FnDef position t ident args _ -> state { 
      environment_stack = [Map.insert ident ((func_type t args), 0) env],
      error_output = error_output . error 
    } where
      error = case Map.lookup ident env of
        Nothing -> string ""
        Just _ -> string ((show position) ++ ": function " ++ show ident ++ " redeclared\n")
    ClassDef _ d -> 
      case d of 
        ClassExtends _ ident base defs -> collect (ClassValue ident) (ClassValue base) defs state
        ClassBase _ ident defs -> collect (ClassValue ident) (ClassValue (Ident "_object")) defs state
      where
        collect ident base defs state = state {
          class_data = Map.insert ident (new_class base defs) class_data,
          environment_stack = [methods defs]
        } where
          ClassValue (Ident class_name) = ident
          methods defs = foldl collect_methods env defs
          collect_methods env d = case d of
            ClassMethod _ _ _ _ _-> Map.insert ident ((func_type t args), 0) env where 
              FnDef position t ident args _ = translate_method class_name d
            _ -> env
        new_class base defs = fst (foldl merge (class_empty base, 0) defs)
        merge (cls, idx) d = case d of
          ClassField _ t items -> foldl merge (cls, idx) items where
            merge (cls@ClassData { field = field }, idx) (ClassItem _ i) = (ncls, idx + 1) where
              ncls = cls {
                field = Map.insert i (to_value_type t, idx) field
              }
          ClassMethod _ ret ident args _ -> (cls {
            method = Map.insert ident (func_type ret args) method
          }, idx) where ClassData { method = method } = cls
  where
    func_type t args = FunctionValue (to_value_type t) (map (\(Arg _ t _) -> to_value_type t) args)

compile :: Show a => Program a -> StateData -> StateData
compile (Program d code) state =
  result {
    output = string_section . string "\n" . output
  } where
    result@State { output = output, string_set = string_set } = preresult initial_state
    string_section = foldl merge (string "section .data\n\n") (zip (reverse string_set) [0..]) where
      merge result (str, idx) = result . string ("str" ++ (show idx) ++ ": db `" ++ str ++ "\\0`\n")
    preresult state = foldl merge state code where
      merge state def = compile_top_definition def state
    initial_state = 
      foldl (\a b -> get_top_definition b a) state { 
        environment_stack = [Map.fromList [
          (Ident "printInt", (FunctionValue VoidValue [IntegerValue], 0)),
          (Ident "printString", (FunctionValue VoidValue [StringValue], 0)),
          (Ident "error", (FunctionValue VoidValue [], 0)),
          (Ident "readInt", (FunctionValue IntegerValue [], 0)),
          (Ident "readString", (FunctionValue StringValue [], 0))
        ]],
        output = string (
          "section .text\n\n\
          \global main\n\n\
          \extern puts\n\
          \extern array_new\n\
          \extern array_object_new\n\
          \extern array_get\n\
          \extern string_new\n\
          \extern object_new\n\
          \extern _object_destructor\n\
          \extern string_concatenate\n\
          \extern increase_refcount\n\
          \extern decrease_refcount\n\
          \extern printHex\n\
          \extern printInt\n\
          \extern printString\n\
          \extern error\n\
          \extern readInt\n\
          \extern readString\n\n"
        )
      } code


