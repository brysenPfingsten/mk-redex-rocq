module S = Search
let checks = ref 0
let check label condition = incr checks; if not condition then failwith label
let run ?(fuel=100) ?(trace=false) text = Frontend.run ~fuel ~trace (Frontend.parse_program text)
let program ?(relations="") ?(counter=0) ?(query="") goal =
  Printf.sprintf "(program (relations %s) (counter %d) (query %s) (goal %s))" relations counter query goal
let evaluated = function S.Evaluated r -> r | _ -> failwith "unexpected rejection"
let rec nat = function 0 -> S.O | n -> S.S (nat (n-1))
let rec length = function S.Nil -> 0 | S.Cons (_,xs) -> 1+length xs
let reject label expected text = check label (run text = S.InputRejected expected)
let parse_error label text =
  check label (try ignore (Frontend.parse_program text); false with Frontend.Input_error _ -> true)
let () =
  let seven = program ~counter:1 ~query:"0" "(unify (var 0) (nat 7))" in
  let r = evaluated (run ~fuel:1 ~trace:true seven) in
  check "exact-boundary completion" (r.S.report_completion = S.Complete);
  check "actual step count" (r.S.report_steps = nat 1);
  check "final success included" (r.S.report_answers = S.Cons (S.Cons (S.Pair (S.O,S.Tnat (nat 7)),S.Nil),S.Nil));
  check "trace length" (length r.S.report_execution.S.execution_trace = 2);
  let rec last = function S.Cons (x,S.Nil) -> x | S.Cons (_,xs) -> last xs | S.Nil -> failwith "empty trace" in
  check "trace ends at final expression" (last r.S.report_execution.S.execution_trace = r.S.report_execution.S.execution_final);
  let zero = evaluated (run ~fuel:0 seven) in
  check "zero fuel active goal" (zero.S.report_completion=S.FuelExhausted && zero.S.report_steps=S.O);
  let success = evaluated (run ~fuel:0 (program "success")) in
  check "zero fuel terminal success" (success.S.report_completion=S.Complete && length success.S.report_answers=1);
  let fail = evaluated (run (program "(unify nil (nat 0))")) in
  check "failed search completes without answers" (fail.S.report_completion=S.Complete && fail.S.report_answers=S.Nil);
  check "trace disabled" (fail.S.report_execution.S.execution_trace=S.Nil);
  reject "unknown relation" S.InvalidGoal (program "(call 0)");
  reject "call arity" S.InvalidGoal (program ~relations:"(relation 1 success)" "(call 0)");
  reject "query allocation" S.InvalidQuery (program ~query:"0" "success");
  reject "unallocated logic variable" S.InvalidGoal (program "(unify (var 0) nil)");
  reject "fresh binds parameters only" S.InvalidGoal (program "(fresh 1 (unify (var 0) nil))");
  reject "unbound parameter" S.InvalidGoal (program "(unify (par 0) nil)");
  reject "environment raw variables" S.InvalidEnvironment (program ~relations:"(relation 0 (unify (var 0) nil))" "success");
  reject "environment bad call" S.InvalidEnvironment (program ~relations:"(relation 0 (call 1))" "success");
  reject "environment wrong arity" S.InvalidEnvironment (program ~relations:"(relation 1 (call 0))" "success");
  let cyclic = evaluated (run (program "(fresh 1 (unify (par 0) (cons (par 0) nil)))")) in
  check "occurs-check failure is valid execution" (cyclic.S.report_completion=S.Complete && cyclic.S.report_answers=S.Nil);
  let alias = evaluated (run (program ~counter:2 ~query:"0 1"
    "(conj (unify (var 0) (cons (var 1) nil)) (unify (var 1) (nat 7)))")) in
  let expected = S.Cons (S.Pair (S.O,S.Tcons (S.Tnat (nat 7),S.Tnil)),
    S.Cons (S.Pair (nat 1,S.Tnat (nat 7)),S.Nil)) in
  check "deep substitution projection" (alias.S.report_answers=S.Cons (expected,S.Nil));
  let loop = evaluated (run ~fuel:10 (program ~relations:"(relation 0 (call 0))" "(call 0)")) in
  check "pure recursion bounded" (loop.S.report_completion=S.FuelExhausted && loop.S.report_steps=nat 10 && loop.S.report_answers=S.Nil);
  let recursive = evaluated (run ~fuel:30 (program ~relations:"(relation 0 (disj (call 0) success))" "(call 0)")) in
  check "fuel exhaustion retains answers" (recursive.S.report_completion=S.FuelExhausted && length recursive.S.report_answers>0);
  let scoped = evaluated (run (program ~relations:"(relation 1 (fresh 1 (conj (unify (par 0) (nat 7)) (unify (par 1) (par 0)))))"
    ~counter:1 ~query:"0" "(call 0 (var 0))")) in
  check "nested opening" (scoped.S.report_answers=r.S.report_answers);
  parse_error "negative variable" (program "(unify (var -1) nil)");
  parse_error "duplicate field" "(program (relations) (counter 0) (counter 1) (query) (goal success))";
  parse_error "unknown field/raw state" "(program (relations) (counter 0) (query) (goal success) (state ()))";
  parse_error "trailing input" (program "success" ^ " extra");
  parse_error "unterminated string" "(program (relations) (counter 0) (query) (goal (unify (str \"bad) nil)))";
  let quoted = evaluated (run (program "(unify (str \"hello\\nworld\") (str \"hello\\nworld\"))")) in
  check "string escapes" (quoted.S.report_completion=S.Complete && length quoted.S.report_answers=1);
  check "negative fuel" (try ignore (run ~fuel:(-1) seven); false with Frontend.Input_error _ -> true);
  Printf.printf "passed %d checked-interface tests\n" !checks
