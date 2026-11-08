open Search

let rec count = function
  | Nil -> 0
  | Cons (_, rest) -> 1 + count rest

let () =
  let state = { st_sub = Nil; st_cnt = O } in
  let start = Pair (Nil, Tgoal (Gdisj (Gsucc, Gsucc), state)) in
  let ten = S (S (S (S (S (S (S (S (S (S O))))))))) in
  let result = run_steps Nil ten start in
  Printf.printf "observed answers: %d\n" (count (observed_answers result))
