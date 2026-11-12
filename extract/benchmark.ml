module S = Benchmark_search

let rec nat n = if n = 0 then S.O else S.S (nat (n - 1))
let rec int = function S.O -> 0 | S.S n -> 1 + int n
let rec list = function [] -> S.Nil | x :: xs -> S.Cons (x, list xs)
let rec host_list = function S.Nil -> [] | S.Cons (x, xs) -> x :: host_list xs
let var n = S.Tvar (nat n)
let seven = S.Tnat (nat 7)
let rec conjunction = function
  | [] -> S.Gsucc
  | [g] -> g
  | g :: gs -> S.Gconj (g, conjunction gs)
let rec ground_chain n =
  if n = 0 then S.Tnil else S.Tcons (seven, ground_chain (n - 1))
let rec balanced n =
  if n = 0 then seven else S.Tcons (balanced (n - 1), balanced (n - 1))
let rec contains_var n =
  if n = 0 then var 0 else S.Tcons (seven, contains_var (n - 1))
let numbers n = List.init n (fun i -> S.Tnat (nat (i mod 8)))
let rec term_list = function
  | [] -> S.Tnil | x :: xs -> S.Tcons (x, term_list xs)

type workload = {
  name : string; size : int; environment : S.env;
  counter : S.nat; query : S.nat S.list; goal : S.goal; fuel : S.nat
}
let workload ?(standard = false) ?(counter = 1) ?(query = [0])
    ?(fuel = 10000) name size goal =
  {name; size; environment = (if standard then S.relation_library else S.Nil);
   counter = nat counter; query = list (List.map nat query); goal; fuel = nat fuel}
let call r args = S.Grelcall (nat r, list args)

let workloads () =
  [workload ~fuel:4 "single_binding" 1 (S.Gunify (var 0, seven))]
  @ List.map (fun n -> workload ~counter:n ~fuel:4 "unused_scope" n
      (S.Gunify (var 0, seven))) [64; 256]
  @ List.map (fun n -> workload ~counter:0 ~query:[] ~fuel:4 "ground_chain" n
      (S.Gunify (ground_chain n, ground_chain n))) [16; 64; 256]
  @ List.map (fun n -> workload ~counter:0 ~query:[] ~fuel:4 "ground_balanced" n
      (S.Gunify (balanced n, balanced n))) [6; 9]
  @ List.map (fun n -> workload ~counter:n "binding_chain" n
      (conjunction (List.init (n - 1) (fun i -> S.Gunify (var i, var (i + 1)))
        @ [S.Gunify (var (n - 1), seven)]))) [8; 24; 48]
  @ List.map (fun n -> workload ~standard:true "appendo_forward" n
      (call 0 [term_list (numbers n); term_list (numbers n); var 0])) [4; 12; 24]
  @ List.map (fun n -> workload ~standard:true ~counter:2 ~query:[0;1] "appendo_splits" n
      (call 0 [var 0; var 1; term_list (numbers n)])) [4; 8]
  @ List.map (fun n -> workload ~standard:true "membero" n
      (call 1 [var 0; term_list (numbers n)])) [8; 24]
  @ List.map (fun fuel -> workload ~standard:true ~fuel "listo_prefix" fuel
      (call 2 [var 0])) [128; 256]
  @ List.map (fun n -> workload ~fuel:4 "occurs_failure" n
      (S.Gunify (var 0, contains_var n))) [64; 256]

(* Projection expands bindings. Canonical names preserve sharing jointly
   across all query terms within an answer, without requiring equal raw IDs. *)
type value = V of int | Sym of S.string | Str of S.string | N of int
           | B of S.bool | Nil | Pair of value * value
let canonical_answer answer =
  let names = Hashtbl.create 16 in
  let rec canonical = function
    | S.Tvar n ->
        let id = int n in
        let name = match Hashtbl.find_opt names id with
          | Some name -> name
          | None -> let name = Hashtbl.length names in Hashtbl.add names id name; name in
        V name
    | S.Tsym s -> Sym s | S.Tstr s -> Str s | S.Tnat n -> N (int n)
    | S.Tbool b -> B b | S.Tnil -> Nil
    | S.Tcons (a,b) -> Pair (canonical a, canonical b)
    | S.Tpar _ -> failwith "unopened parameter in projected answer"
  in
  List.map (fun (S.Pair (id,t)) -> int id, canonical t) (host_list answer)
let canonical_answers xs = List.map canonical_answer (host_list xs)
let report = function
  | S.Evaluated r -> r | S.InputRejected _ -> failwith "invalid benchmark request"
let checked solve w = report (solve w.environment w.counter w.query w.goal w.fuel S.False)
let initial w = S.Pair (S.Nil, S.Tgoal (w.goal, {S.st_sub = S.Nil; st_cnt = w.counter}))
let projected w e =
  let states = S.observed_answers e in
  List.map (fun s -> canonical_answer (S.project_answer w.query s)) (host_list states)
let verify w =
  let r = checked S.reference_checked_run w in
  let s = checked S.structural_checked_run w in
  if r.S.report_completion <> s.S.report_completion
     || r.S.report_steps <> s.S.report_steps
     || canonical_answers r.S.report_answers <> canonical_answers s.S.report_answers
  then failwith ("checked outputs differ: " ^ w.name);
  if w.name <> "listo_prefix" && r.S.report_completion <> S.Complete
  then failwith ("finite benchmark did not complete: " ^ w.name);
  let a = S.reference_execute w.environment S.False w.fuel (initial w) in
  let b = S.structural_execute w.environment S.False w.fuel (initial w) in
  if a.S.execution_steps <> b.S.execution_steps
     || projected w a.S.execution_final <> projected w b.S.execution_final
     || projected w a.S.execution_final <> canonical_answers r.S.report_answers
  then failwith ("search-only outputs differ: " ^ w.name);
  int r.S.report_steps, List.length (host_list r.S.report_answers)

type measurement = { cpu : float; wall : float; bytes : float }
let measure repeats run =
  Gc.full_major ();
  let before = Gc.quick_stat () in
  let cpu = Sys.time () and wall = Unix.gettimeofday () in
  let sink = ref None in
  for _ = 1 to repeats do sink := Some (run ()) done;
  let wall = Unix.gettimeofday () -. wall and cpu = Sys.time () -. cpu in
  let after = Gc.quick_stat () in
  ignore (Sys.opaque_identity !sink);
  {cpu = cpu /. float repeats; wall = wall /. float repeats;
   bytes = (after.Gc.minor_words +. after.Gc.major_words -. after.Gc.promoted_words
         -. before.Gc.minor_words -. before.Gc.major_words +. before.Gc.promoted_words)
           *. float (Sys.word_size / 8) /. float repeats}
let calibrate target run =
  let rec loop repeats =
    let m = measure repeats run in
    if m.cpu *. float repeats >= target || repeats >= 100000 then repeats
    else loop (min 100000 (repeats * 2))
  in loop 1

let () =
  let samples = ref 7 and target = ref 0.05 and filter = ref "" and backend = ref "bytecode" in
  Arg.parse ["--samples", Arg.Set_int samples, "Number of paired samples";
             "--target-seconds", Arg.Set_float target, "CPU seconds per solver sample";
             "--case", Arg.Set_string filter, "Only this workload name";
             "--backend", Arg.Set_string backend, "Backend label for CSV"]
    (fun _ -> raise (Arg.Bad "unexpected positional argument")) "benchmark [options]";
  if !samples < 1 || !target <= 0. then invalid_arg "positive samples and target required";
  let cases = workloads () |> List.filter (fun w -> !filter = "" || w.name = !filter) in
  if cases = [] then invalid_arg "no matching workloads";
  Printf.eprintf "OCaml %s; %s; %d-bit; minor heap %d words; %d samples; target %.3fs\n%!"
    Sys.ocaml_version !backend Sys.word_size (Gc.get ()).Gc.minor_heap_size !samples !target;
  Printf.printf "backend,mode,workload,size,budget,steps,answers,solver,sample,repeats,cpu_us,wall_us,allocated_bytes\n%!";
  List.iter (fun w ->
    let steps, answers = verify w in
    Printf.eprintf "verified %s/%d: %d steps, %d answers\n%!" w.name w.size steps answers;
    let e = initial w in
    List.iter (fun (mode,reference,structural) ->
      let nr = calibrate !target reference and ns = calibrate !target structural in
      let emit solver sample repeats run =
        let m = measure repeats run in
        Printf.printf "%s,%s,%s,%d,%d,%d,%d,%s,%d,%d,%.6f,%.6f,%.1f\n%!"
          !backend mode w.name w.size (int w.fuel) steps answers solver sample repeats
          (m.cpu *. 1e6) (m.wall *. 1e6) m.bytes
      in
      for sample = 1 to !samples do
        if sample mod 2 = 1 then
          (emit "reference" sample nr reference; emit "structural" sample ns structural)
        else (emit "structural" sample ns structural; emit "reference" sample nr reference)
      done)
      ["search", (fun () -> ignore (Sys.opaque_identity
           (S.reference_execute w.environment S.False w.fuel e))),
                 (fun () -> ignore (Sys.opaque_identity
           (S.structural_execute w.environment S.False w.fuel e)));
       "checked", (fun () -> ignore (Sys.opaque_identity (checked S.reference_checked_run w))),
                  (fun () -> ignore (Sys.opaque_identity (checked S.structural_checked_run w)))]) cases
