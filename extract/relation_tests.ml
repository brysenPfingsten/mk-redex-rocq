module S = Search
let checks = ref 0
let check label value = incr checks; if not value then failwith label
let rec to_list = function S.Nil -> [] | S.Cons (x,xs) -> x::to_list xs
let rec to_int = function S.O -> 0 | S.S n -> 1+to_int n
let read path =
  let channel = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in channel)
    (fun () -> really_input_string channel (in_channel_length channel))
let run ?(fuel=200) source =
  match Frontend.run ~fuel ~trace:false (Frontend.parse_program source) with
  | S.Evaluated r -> r
  | response -> failwith (Frontend.format_response response)
let file name = run (read ("examples/" ^ name ^ ".sexp"))
let answers r = List.map to_list (to_list r.S.report_answers)
let binding id answer =
  match List.find_opt (fun (S.Pair (n,_)) -> to_int n=id) answer with
  | Some (S.Pair (_,term)) -> term | None -> failwith "missing query binding"
let rec list_term = function
  | S.Tnil -> []
  | S.Tcons (S.Tnat n,tail) -> to_int n::list_term tail
  | _ -> failwith "expected a proper ground integer list"
let expect_ground_lists label expected report =
  check (label ^ " completes") (report.S.report_completion=S.Complete);
  check (label ^ " answers")
    (List.map (List.map (fun (S.Pair (_,t)) -> list_term t)) (answers report)=expected)
let rec term = function
  | [] -> "nil" | x::xs -> Printf.sprintf "(cons (nat %d) %s)" x (term xs)
let program ?(counter=1) ?(query="0") goal =
  Printf.sprintf "(program (relations standard) (counter %d) (query %s) (goal %s))" counter query goal
let rec proper_length = function S.Tnil -> 0 | S.Tcons (_,tail) -> 1+proper_length tail | _ -> failwith "improper list"
let rec symbolic_heads = function
  | S.Tnil -> [] | S.Tcons (S.Tvar n,tail) -> to_int n::symbolic_heads tail
  | _ -> failwith "expected independent symbolic elements"
let rec member_position = function
  | S.Tcons (S.Tnat n,S.Tvar _) when to_int n=7 -> 0
  | S.Tcons (S.Tvar _,tail) -> 1+member_position tail
  | _ -> failwith "incorrect symbolic member answer"
let rec prefix xs ys = match xs,ys with
  | [],_ -> true | x::xs,y::ys when x=y -> prefix xs ys | _ -> false
let () =
  expect_ground_lists "appendo forward" [[[1;2;3]]] (file "appendo-forward");
  expect_ground_lists "appendo backward" [[[1;2]]] (file "appendo-backward");
  expect_ground_lists "appendo splits" [[[];[1;2]];[[1];[2]];[[1;2];[]]] (file "appendo-splits");
  List.iter (fun (xs,ys) ->
    expect_ground_lists "append boundary" [[xs@ys]]
      (run (program (Printf.sprintf "(call 0 %s %s (var 0))" (term xs) (term ys)))))
    [[],[];[],[1;2];[1;2],[]];
  expect_ground_lists "recover suffix" [[[2;3]]]
    (run (program (Printf.sprintf "(call 0 %s (var 0) %s)" (term [1]) (term [1;2;3]))));
  expect_ground_lists "inconsistent append" []
    (run (program (Printf.sprintf "(call 0 (var 0) %s %s)" (term [8]) (term [1;2;3]))));
  let partial = file "appendo-partial" in
  check "partial query completes" (partial.S.report_completion=S.Complete);
  check "partial query preserves sharing" (match answers partial with
    | [answer] -> (match binding 0 answer,binding 1 answer with
        | S.Tvar x,S.Tcons (S.Tvar y,S.Tcons (S.Tnat n,S.Tnil)) -> x=y && to_int n=2
        | _ -> false)
    | _ -> false);
  let members = file "membero" in
  check "membership completes" (members.S.report_completion=S.Complete);
  check "membership order" (List.map (fun a -> match binding 0 a with S.Tnat n -> to_int n | _ -> -1) (answers members)=[1;2;3]);
  let duplicates = run (program (Printf.sprintf "(call 1 (var 0) %s)" (term [1;1]))) in
  check "membership retains duplicate derivations" (List.length (answers duplicates)=2 &&
    List.for_all (fun a -> binding 0 a=S.Tnat (S.S S.O)) (answers duplicates));
  let missing = run (program ~counter:0 ~query:"" (Printf.sprintf "(call 1 (nat 7) %s)" (term [1;2;3]))) in
  check "missing member finishes with no answers" (missing.S.report_completion=S.Complete && answers missing=[]);
  let lists = file "listo" in
  let projected = List.map (binding 0) (answers lists) in
  check "list generation remains active" (lists.S.report_completion=S.FuelExhausted);
  check "list generation gives several lengths" (List.length projected>=3);
  check "list lengths increase from zero" (List.mapi (fun i t -> proper_length t=i) projected |> List.for_all Fun.id);
  check "list elements are independent fresh variables" (List.for_all (fun t ->
    let heads=symbolic_heads t in List.length (List.sort_uniq compare heads)=List.length heads) projected);
  let more = run ~fuel:300 (read "examples/listo.sexp") in
  check "longer fuel preserves answer prefix" (prefix (answers lists) (answers more));
  let generated = file "membero-generate" in
  check "backward membership remains active" (generated.S.report_completion=S.FuelExhausted);
  let positions = List.map (fun a -> member_position (binding 0 a)) (answers generated) in
  check "backward membership explores successive positions" (List.length positions>=3 &&
    List.mapi (fun i n -> i=n) positions |> List.for_all Fun.id);
  Printf.printf "passed %d representative-relation checks\n" !checks
