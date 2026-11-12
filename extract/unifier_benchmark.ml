module S = Benchmark_search
let rec nat n = if n = 0 then S.O else S.S (nat (n - 1))
let rec int = function S.O -> 0 | S.S n -> 1 + int n
let rec list = function [] -> S.Nil | x :: xs -> S.Cons (x, list xs)
let rec host_list = function S.Nil -> [] | S.Cons (x,xs) -> x :: host_list xs
let var i = S.Tvar (nat i)
let seven = S.Tnat (nat 7)
let rec chain n tail = if n = 0 then tail else S.Tcons (seven, chain (n - 1) tail)
let rec balanced n = if n = 0 then seven else S.Tcons (balanced (n - 1), balanced (n - 1))
let unwrap = function S.Some x -> x | S.None -> failwith "invalid benchmark construction"

type workload = {
  name : string; size : int; bound : S.nat;
  initial : S.sub0; accumulator : S.acc;
  equations : (S.term * S.term) array;
  indexed : (S.term0 * S.term0) array
}

let reference_run bound initial equations =
  let rec go i store =
    if i = Array.length equations then S.Some store
    else let t,u = equations.(i) in
      match S.reference_unify bound store t u with
      | S.None -> S.None | S.Some next -> go (i + 1) next
  in go 0 initial

let structural_run bound initial equations =
  let rec go i accumulator =
    if i = Array.length equations then S.Some accumulator
    else let t,u = equations.(i) in
      match S.structural_unify bound t u accumulator with
      | S.None -> S.None | S.Some next -> go (i + 1) next
  in go 0 initial

(* Conversion is preparation only. Neither timed loop calls index_term,
   encode_sub, decode_acc, projection, validation, or the search machine. *)
let prepare name size scope setup equations =
  let bound = nat scope in
  let index = Array.map (fun (t,u) -> unwrap (S.index_term bound t), unwrap (S.index_term bound u)) in
  let setup = Array.of_list setup and equations = Array.of_list equations in
  let initial = unwrap (reference_run bound S.Nil setup) in
  let accumulator = unwrap (structural_run bound (S.ExistT (bound, S.Anil bound)) (index setup)) in
  {name; size; bound; initial; accumulator; equations; indexed = index equations}

let aliases n = List.init (n - 1) (fun i -> var i, var (i + 1)) @ [var (n - 1), seven]
let constants n = List.init n (fun i -> var i, seven)
let workloads () =
  [prepare "single_binding" 1 1 [] [var 0, seven]]
  @ List.map (fun n -> prepare "unused_scope" n n [] [var 0,seven]) [64;256]
  @ List.map (fun n -> prepare "ground_chain" n 0 [] [chain n S.Tnil, chain n S.Tnil]) [16;64;256]
  @ List.map (fun n -> prepare "ground_balanced" n 0 [] [balanced n,balanced n]) [6;9]
  @ List.map (fun n -> prepare "alias_batch" n n [] (aliases n)) [8;24;48;96]
  @ List.map (fun n -> prepare "constant_batch" n n [] (constants n)) [8;24;48;96]
  @ List.map (fun n -> prepare "list_spine_batch" n (n + 1) []
      (List.init n (fun i -> var i,S.Tcons (seven,var (i + 1))) @ [var n,S.Tnil])) [8;24;48]
  @ List.concat_map (fun n ->
      [prepare "read_oldest_binding" n n (constants n) [var 0,seven];
       prepare "read_newest_binding" n n (constants n) [var (n - 1),seven]]) [32;96]
  @ List.map (fun n -> prepare "occurs_failure" n 1 [] [var 0,chain n (var 0)]) [64;256]
  @ [prepare "constructor_clash" 1 0 [] [seven,S.Tnil]]

type value = V of int | N of int | Nil | Pair of value * value
let canonical bindings =
  let names = Hashtbl.create 16 in
  let rec term = function
    | S.Tvar id ->
        let id = int id in
        let name = match Hashtbl.find_opt names id with
          | Some n -> n
          | None -> let n = Hashtbl.length names in Hashtbl.add names id n; n in
        V name
    | S.Tnat n -> N (int n) | S.Tnil -> Nil
    | S.Tcons (a,b) -> Pair (term a,term b)
    | _ -> failwith "unexpected benchmark term"
  in List.map (fun (S.Pair (id,t)) -> int id, term t) (host_list bindings)

let verify w =
  let projected store =
    let query = list (List.init (int w.bound) nat) in
    canonical (S.project_answer query {S.st_sub = store; st_cnt = w.bound}) in
  (* Check setup too; its construction is excluded from the timing. *)
  if projected w.initial <> projected (S.decode_acc w.bound w.accumulator)
  then failwith ("initial states differ: " ^ w.name);
  match reference_run w.bound w.initial w.equations,
        structural_run w.bound w.accumulator w.indexed with
  | S.None,S.None -> ()
  | S.Some a,S.Some b ->
      if projected a <> projected (S.decode_acc w.bound b)
      then failwith ("results differ: " ^ w.name)
  | _ -> failwith ("success/failure differs: " ^ w.name)

let measure repeats run =
  Gc.full_major ();
  let before = Gc.quick_stat () in
  let cpu = Sys.time () and wall = Unix.gettimeofday () in
  for _ = 1 to repeats do run () done;
  let wall = Unix.gettimeofday () -. wall and cpu = Sys.time () -. cpu in
  let after = Gc.quick_stat () in
  cpu /. float repeats, wall /. float repeats,
  (after.Gc.minor_words +. after.Gc.major_words -. after.Gc.promoted_words
   -. before.Gc.minor_words -. before.Gc.major_words +. before.Gc.promoted_words)
   *. float (Sys.word_size / 8) /. float repeats

let calibrate target run =
  let rec go n =
    let cpu,_,_ = measure n run in
    if cpu *. float n >= target || n >= 100000 then n else go (min 100000 (2 * n))
  in go 1

let () =
  let samples = ref 7 and target = ref 0.03 and backend = ref "bytecode" in
  Arg.parse ["--samples",Arg.Set_int samples,"Paired samples";
             "--target-seconds",Arg.Set_float target,"CPU seconds per sample";
             "--backend",Arg.Set_string backend,"CSV backend label"]
    (fun _ -> raise (Arg.Bad "unexpected argument")) "unifier-benchmark [options]";
  if !samples < 1 || !target <= 0. then invalid_arg "positive samples and target required";
  Printf.printf "backend,mode,workload,size,equations,solver,sample,repeats,cpu_us,wall_us,allocated_bytes\n%!";
  List.iter (fun w ->
    verify w;
    Printf.eprintf "verified %s/%d (%d equations)\n%!" w.name w.size (Array.length w.equations);
    let reference () = ignore (Sys.opaque_identity (reference_run w.bound w.initial w.equations)) in
    let structural () = ignore (Sys.opaque_identity (structural_run w.bound w.accumulator w.indexed)) in
    let nr = calibrate !target reference and ns = calibrate !target structural in
    let emit name sample repeats run =
      let cpu,wall,bytes = measure repeats run in
      Printf.printf "%s,kernel,%s,%d,%d,%s,%d,%d,%.6f,%.6f,%.1f\n%!"
        !backend w.name w.size (Array.length w.equations) name sample repeats
        (cpu *. 1e6) (wall *. 1e6) bytes in
    for sample = 1 to !samples do
      if sample mod 2 = 1 then
        (emit "reference" sample nr reference; emit "structural" sample ns structural)
      else (emit "structural" sample ns structural; emit "reference" sample nr reference)
    done) (workloads ())
