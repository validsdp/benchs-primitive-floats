(** The main program. *)

let prog_name = "parse-coq-stmt"

(** Options. *)

type output = Out_pvs | Out_hl_alex | Out_hl_sos | Out_tex
let output = ref Out_tex

let keep_going = ref false
let failed_stmts = ref 0

(** Command line parsing. *)

let usage ?(error=true) ?(str="bad command line syntax.") () =
  if error then prerr_endline (prog_name^": " ^ str ^"\n");
  (if error then prerr_endline else print_endline)
    ("Usage: " ^ prog_name ^ " [option]
       " ^ prog_name ^ " [option] < input.txt > output.txt

Summary:
  " ^ prog_name ^ " assumes standard input is a Coq type judgement, that is
  the text produced by coqtop or coqc when parsing some vernacular command
  Check (thm_1, thm_2, ..., thm_n).
  where thm_1, ..., are lemmas (involving non-linear inequalities over R),
  then it prints on standard output each statement in the desired format,
  according to the chosen option below.

Options:
  --pvs : output PVS lemmas (compatible w. strategies bernstein/interval/metit)
  --hl-alex : output HOL Light lemmas (compatible w. Alexey.Solovyev's library)
  --hl-sos : output HOL Light lemmas (compatible w. John.Harrison's REAL_SOS)
  --tex : output TeX equations (default option)
  -k, --keep-going : if the conversion of some statement fails (for example,
    because of some unsupported construct), skip it and continue converting
    the other statements (but print a warning on standard error)
  -h, --help : give this help list

Exit status:
  0: no error
  1: error during command-line parsing or standard input parsing
  2: error during the conversion of some statement

Report bugs to <Erik Martin-Dorel <erik.martin-dorel@ens-lyon.org>>.
");
  exit (if error then 1 else 0)

let parse () =
  let rec parse_rec = function
    | "--pvs" :: rem ->
      output := Out_pvs; parse_rec rem
    | "--hl-alex" :: rem ->
      output := Out_hl_alex; parse_rec rem
    | "--hl-sos" :: rem ->
      output := Out_hl_sos; parse_rec rem
    | "--tex" :: rem ->
      output := Out_tex; parse_rec rem
    | ("-k" | "--keep-going") :: rem ->
      keep_going := true; parse_rec rem
    | ("-h" | "--help") :: rem ->
	usage ~error:false ()
    | [] -> ()
    | _ -> usage ()
  in 
    parse_rec (List.tl (Array.to_list Sys.argv))

(** Main: reads input, parses, and prints the result. *)

let main () =
  parse ();
  try let lst = Parser.toplevel Lexer.token (Lexing.from_channel stdin) in
      List.iter (fun a ->
	try
	  print_endline
	    ((match !output with
	    | Out_pvs -> Print.Printer_pvs.str_stmt
	    | Out_hl_alex -> Print.Printer_hl_alex.str_stmt
	    | Out_hl_sos -> Print.Printer_hl_sos.str_stmt
	    | Out_tex -> Print.Printer_tex.str_stmt) a
	     ^ "\n")
	with
	  Print.Unsupported str -> prerr_endline ("Unsupported: " ^ str);
	    if !keep_going
	    then failed_stmts := 1 + !failed_stmts
	    else exit 2)
	lst;
      if !failed_stmts > 0
      then (prerr_endline
	      (string_of_int !failed_stmts ^ " statement(s) skipped.");
	    exit 2)
      else exit 0
  with
    Failure str -> prerr_endline ("Error: " ^ str); exit 1
  | Parsing.Parse_error ->
    (* prerr_endline "Syntax error."; *)
    (* FIXME: Handle "bad input" and "no input" errors apart. *)
    usage ~str:"no valid input found." ()

let () = main ();
