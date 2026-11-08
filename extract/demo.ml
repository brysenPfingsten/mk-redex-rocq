open Search

let rec count = function
  | Nil -> 0
  | Cons (_, rest) -> 1 + count rest

let rec nat n = if n = 0 then O else S (nat (n - 1))

let run environment goal fuel =
  let state = { st_sub = Nil; st_cnt = O } in
  run_steps environment (nat fuel) (Pair (Nil, Tgoal (goal, state)))

let check_count label expected result =
  let actual = count (observed_answers result) in
  if actual <> expected then
    failwith (Printf.sprintf "%s: expected %d answers, got %d" label expected actual)

let () =
  let result = run Nil (Gdisj (Gsucc, Gsucc)) 10 in
  check_count "disjunction" 2 result;
  Printf.printf "observed answers: %d\n" (count (observed_answers result));
  let fresh = run Nil (Gfresh (nat 1, Gunify (Tpar O, Tnat (nat 7)))) 10 in
  check_count "fresh unification" 1 fresh;
  (match observed_answers fresh with
   | Cons (answer, Nil) ->
       (match lookup O answer.st_sub with
        | Some (Tnat value) when value = nat 7 -> ()
        | _ -> failwith "fresh unification: incorrect binding")
   | _ -> failwith "fresh unification: incorrect answers");
  check_count "occurs check" 0
    (run Nil (Gfresh (nat 1, Gunify (Tpar O, Tcons (Tpar O, Tnil)))) 10);
  check_count "conjunction continuation" 2
    (run Nil (Gconj (Gdisj (Gsucc, Gsucc), Gsucc)) 30);
  check_count "failing continuation" 0
    (run Nil (Gconj (Gdisj (Gsucc, Gsucc), Gunify (Tnil, Tnat O))) 30);
  check_count "relation opening" 1
    (run (Cons (Pair (nat 1, Gunify (Tpar O, Tnat (nat 7))), Nil))
       (Grelcall (O, Cons (Tnat (nat 7), Nil))) 10);
  let recursive_env = Cons (Pair (O, Gdisj (Grelcall (O, Nil), Gsucc)), Nil) in
  let recursive = run recursive_env (Grelcall (O, Nil)) 100 in
  if count (observed_answers recursive) = 0 then
    failwith "recursive relation: the recursive branch stranded the base clause";
  let base = Gfresh (nat 1,
    Gconj (Gunify (Tpar O, Tnat (nat 7)), Gunify (Tpar (nat 1), Tpar O))) in
  let combined_env = Cons (Pair (nat 1,
    Gdisj (Grelcall (O, Cons (Tpar O, Nil)), base)), Nil) in
  let combined_start = Pair (Nil,
    Tgoal (Grelcall (O, Cons (Tvar O, Nil)), { st_sub = Nil; st_cnt = nat 1 })) in
  let combined = run_steps combined_env (nat 100) combined_start in
  (match observed_answers combined with
   | Cons (answer, _) ->
       (match walk_valid answer.st_sub (Tvar O) with
        | Tnat value when value = nat 7 -> ()
        | _ -> failwith "combined relation: incorrect query binding")
   | Nil -> failwith "combined relation: query answer was stranded");
  Printf.printf "passed 8 executable checks\n"
