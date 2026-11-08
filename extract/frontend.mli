(** Text input and display around the extracted, certified checked runner.
    Parsed programs remain subject to validation by [run]. *)
type program
exception Input_error of string
val parse_program : string -> program
val run : fuel:int -> trace:bool -> program -> Search.response
val format_response : Search.response -> string
