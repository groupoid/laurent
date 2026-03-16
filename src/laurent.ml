open Tactics
open Theorems
open Suite

(* LAURENT LAUNCHER 🚀 *)

let usage = "laurent [ repl | banner | *file* ]"

let banner =
"https://laurent.groupoid.space/

  ∮ Laurent Theorem Prover version 0.3.26 (c) 2025 Groupoїd Infinity

For help type `help`."

let evalFile path : unit =
  let chan = open_in path in
  let lexbuf = Lexing.from_channel chan in
  let commands = Parser.main Lexer.read lexbuf in
  close_in chan;
  flush_all ()

let () =
    let args = Array.to_list Sys.argv in
    match args with
    | [_; "repl"] ->   print_endline "Starting REPL...";
                       print_endline banner;
                       ignore (console_loop [] state1)
    | [_; "banner"] -> test_foundations ();
                       test_mathematics ();
                       print_endline banner
    | [_; file] when Sys.file_exists file ->
                       evalFile file
    | _ ->             print_endline usage
