let () =
  let fuel = ref 1000 and trace = ref false and filename = ref None in
  let input_file name = match !filename with None -> filename := Some name | Some _ -> raise (Arg.Bad "expected one program file") in
  Arg.parse ["--fuel",Arg.Set_int fuel,"N maximum reduction steps (default 1000)";
             "--trace",Arg.Set trace," print each reduction state"] input_file
    "mk-search [--fuel N] [--trace] PROGRAM.sexp";
  try
    let path = match !filename with Some path -> path | None -> raise (Frontend.Input_error "provide a program file") in
    let channel = open_in_bin path in
    let text = Fun.protect ~finally:(fun () -> close_in channel)
      (fun () -> really_input_string channel (in_channel_length channel)) in
    let response = Frontend.run ~fuel:!fuel ~trace:!trace (Frontend.parse_program text) in
    (match response with
     | Search.InputRejected _ -> prerr_string (Frontend.format_response response); exit 2
     | Search.Evaluated report -> print_string (Frontend.format_response response);
         match report.Search.report_completion with Search.Complete -> () | Search.FuelExhausted -> exit 3)
  with
  | Frontend.Input_error message | Sys_error message -> prerr_endline ("input error: " ^ message); exit 2
