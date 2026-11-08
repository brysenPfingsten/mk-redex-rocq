module S = Search
exception Input_error of string
let fail text = raise (Input_error text)

type sexp = Atom of string | Text of string | Form of sexp list
let parse text =
  let size = String.length text in
  let position = ref 0 in
  let rec space () =
    if !position < size then
      match text.[!position] with
      | ' ' | '\t' | '\n' | '\r' -> incr position; space ()
      | ';' -> while !position < size && text.[!position] <> '\n' do incr position done; space ()
      | _ -> () in
  let rec value () =
    space ();
    if !position = size then fail "unexpected end of input";
    match text.[!position] with
    | '(' -> incr position; items []
    | ')' -> fail "unexpected closing parenthesis"
    | '"' -> incr position; quoted (Buffer.create 32)
    | _ ->
        let start = !position in
        while !position < size && not (List.mem text.[!position] ['('; ')'; ' '; '\t'; '\n'; '\r'; ';'; '"']) do
          incr position
        done;
        Atom (String.sub text start (!position-start))
  and items acc =
    space ();
    if !position = size then fail "unclosed parenthesis";
    if text.[!position] = ')' then (incr position; Form (List.rev acc))
    else let item = value () in items (item::acc)
  and quoted buffer =
    if !position = size then fail "unclosed string";
    let c = text.[!position] in incr position;
    match c with
    | '"' -> Text (Buffer.contents buffer)
    | '\\' ->
        if !position = size then fail "unfinished string escape";
        let escaped = text.[!position] in incr position;
        Buffer.add_char buffer (match escaped with
          | 'n' -> '\n' | 'r' -> '\r' | 't' -> '\t' | '\\' -> '\\' | '"' -> '"'
          | _ -> fail "unsupported string escape"); quoted buffer
    | c -> Buffer.add_char buffer c; quoted buffer in
  let result = value () in space ();
  if !position <> size then fail "unexpected trailing input";
  result

let nat n = let rec loop n acc = if n = 0 then acc else loop (n-1) (S.S acc) in loop n S.O
let integer context = function
  | Atom text ->
      (match int_of_string_opt text with
       | Some n when n >= 0 -> n
       | _ -> fail (context ^ " must be a nonnegative machine integer"))
  | _ -> fail (context ^ " must be an integer")
let number context sexp = nat (integer context sexp)
let rec list = function [] -> S.Nil | x::xs -> S.Cons (x,list xs)
let bool b = if b then S.True else S.False
let ascii c =
  let n = Char.code c in
  let bit i = bool (n land (1 lsl i) <> 0) in
  S.Ascii (bit 0,bit 1,bit 2,bit 3,bit 4,bit 5,bit 6,bit 7)
let rec string_at text i =
  if i = String.length text then S.EmptyString
  else S.String (ascii text.[i],string_at text (i+1))
let string text = string_at text 0

let rec term = function
  | Form [Atom "var"; n] -> S.Tvar (number "variable ID" n)
  | Form [Atom "par"; n] -> S.Tpar (number "parameter index" n)
  | Form [Atom "nat"; n] -> S.Tnat (number "natural value" n)
  | Form [Atom "sym"; Text text] -> S.Tsym (string text)
  | Form [Atom "str"; Text text] -> S.Tstr (string text)
  | Form [Atom "bool"; Atom "true"] -> S.Tbool S.True
  | Form [Atom "bool"; Atom "false"] -> S.Tbool S.False
  | Atom "nil" -> S.Tnil
  | Form [Atom "cons"; a; b] -> S.Tcons (term a,term b)
  | _ -> fail "invalid term (expected var, par, nat, sym, str, bool, nil or cons)"
let rec goal = function
  | Atom "success" -> S.Gsucc
  | Form [Atom "unify"; a; b] -> S.Gunify (term a,term b)
  | Form (Atom "call"::r::args) -> S.Grelcall (number "relation index" r,list (List.map term args))
  | Form [Atom "disj"; a; b] -> S.Gdisj (goal a,goal b)
  | Form [Atom "conj"; a; b] -> S.Gconj (goal a,goal b)
  | Form [Atom "fresh"; k; body] -> S.Gfresh (number "fresh binder width" k,goal body)
  | _ -> fail "invalid goal (expected success, unify, call, disj, conj or fresh)"
let relation = function
  | Form [Atom "relation"; arity; body] -> S.Pair (number "relation arity" arity,goal body)
  | _ -> fail "expected (relation ARITY GOAL)"

type program = { environment:S.env; counter:S.nat; query:S.nat S.list; goal:S.goal }
let parse_program text =
  match parse text with
  | Form (Atom "program"::fields) ->
      let get name =
        match List.filter_map (function Form (Atom key::values) when key=name -> Some values | _ -> None) fields with
        | [values] -> values
        | [] -> fail ("missing field: " ^ name)
        | _ -> fail ("duplicate field: " ^ name) in
      List.iter (function
        | Form (Atom ("relations"|"counter"|"query"|"goal")::_) -> ()
        | _ -> fail "unknown program field") fields;
      let singleton name = match get name with [x] -> x | _ -> fail (name ^ " expects one value") in
      { environment = (match get "relations" with
          | [Atom "standard"] -> S.relation_library
          | definitions -> list (List.map relation definitions));
        counter = number "initial counter" (singleton "counter");
        query = list (List.map (number "query variable ID") (get "query"));
        goal = goal (singleton "goal") }
  | _ -> fail "expected (program (relations ...) (counter N) (query ...) (goal GOAL))"
let run ~fuel ~trace program =
  if fuel < 0 then fail "fuel must be nonnegative";
  S.checked_run program.environment program.counter program.query program.goal (nat fuel) (bool trace)

let to_int n = let rec loop acc = function S.O -> acc | S.S n -> loop (acc+1) n in loop 0 n
let rec to_list = function S.Nil -> [] | S.Cons (x,xs) -> x::to_list xs
let bit = function S.True -> 1 | S.False -> 0
let to_char (S.Ascii (a,b,c,d,e,f,g,h)) =
  Char.chr (bit a + 2*bit b + 4*bit c + 8*bit d + 16*bit e + 32*bit f + 64*bit g + 128*bit h)
let rec to_string = function S.EmptyString -> "" | S.String (c,rest) -> String.make 1 (to_char c) ^ to_string rest
let rec show_term = function
  | S.Tvar n -> "_" ^ string_of_int (to_int n)
  | S.Tpar n -> "(par " ^ string_of_int (to_int n) ^ ")"
  | S.Tnat n -> string_of_int (to_int n)
  | S.Tsym s -> Printf.sprintf "(sym %S)" (to_string s)
  | S.Tstr s -> Printf.sprintf "%S" (to_string s)
  | S.Tbool S.True -> "true" | S.Tbool S.False -> "false"
  | S.Tnil -> "nil"
  | S.Tcons (a,b) -> "(" ^ show_term a ^ " . " ^ show_term b ^ ")"
let rec show_goal = function
  | S.Gsucc -> "success"
  | S.Gunify (a,b) -> "(unify " ^ show_term a ^ " " ^ show_term b ^ ")"
  | S.Grelcall (r,args) -> Printf.sprintf "(call %d%s)" (to_int r)
      (String.concat "" (List.map (fun t -> " " ^ show_term t) (to_list args)))
  | S.Gdisj (a,b) -> "(disj " ^ show_goal a ^ " " ^ show_goal b ^ ")"
  | S.Gconj (a,b) -> "(conj " ^ show_goal a ^ " " ^ show_goal b ^ ")"
  | S.Gfresh (k,g) -> Printf.sprintf "(fresh %d %s)" (to_int k) (show_goal g)
let show_state s =
  let bindings = List.map (fun (S.Pair (x,t)) -> Printf.sprintf "_%d=%s" (to_int x) (show_term t)) (to_list s.S.st_sub) in
  Printf.sprintf "{next=%d; %s}" (to_int s.S.st_cnt) (String.concat "; " bindings)
let rec show_tree = function
  | S.Tfail -> "fail"
  | S.Tgoal (g,s) -> "(goal " ^ show_goal g ^ " " ^ show_state s ^ ")"
  | S.Tproceed (r,args,s) -> "(proceed " ^ show_goal (S.Grelcall (r,args)) ^ " " ^ show_state s ^ ")"
  | S.Tdelay t -> "(delay " ^ show_tree t ^ ")"
  | S.Tconj (t,g) -> "(continue " ^ show_tree t ^ " " ^ show_goal g ^ ")"
  | S.TdisjL (a,b) -> "(select-left " ^ show_tree a ^ " " ^ show_tree b ^ ")"
  | S.TdisjR (a,b) -> "(select-right " ^ show_tree a ^ " " ^ show_tree b ^ ")"
let format_response = function
  | S.InputRejected reason -> "input rejected: " ^ (match reason with
      | S.InvalidEnvironment -> "invalid relation definitions (check parameter scope, relation indices and arities; bodies cannot contain allocated variables)"
      | S.InvalidGoal -> "invalid goal (check variable/parameter scope, relation indices and arities)"
      | S.InvalidQuery -> "query variable IDs must be below the initial counter") ^ "\n"
  | S.Evaluated report ->
      let buffer = Buffer.create 256 in
      Buffer.add_string buffer (Printf.sprintf "status: %s\nsteps: %d\nanswers: %d\n"
        (match report.S.report_completion with S.Complete -> "complete" | S.FuelExhausted -> "fuel exhausted")
        (to_int report.S.report_steps) (List.length (to_list report.S.report_answers)));
      List.iteri (fun i answer ->
        let bindings = List.map (fun (S.Pair (x,t)) -> Printf.sprintf "q%d = %s" (to_int x) (show_term t)) (to_list answer) in
        Buffer.add_string buffer (Printf.sprintf "answer %d: {%s}\n" (i+1) (String.concat "; " bindings)))
        (to_list report.S.report_answers);
      List.iteri (fun i (S.Pair (answers,t)) -> Buffer.add_string buffer
        (Printf.sprintf "trace %d: promoted=%d %s\n" i (List.length (to_list answers)) (show_tree t)))
        (to_list report.S.report_execution.S.execution_trace);
      Buffer.contents buffer
