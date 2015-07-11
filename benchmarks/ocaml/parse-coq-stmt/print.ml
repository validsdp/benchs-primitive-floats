open Syntax

exception Unsupported of string

let inp a = "(" ^ a ^ ")"

module type PRINT =
sig
  type s = string
  val str_Zint : bool * s -> s
  val str_IZR_Zint : bool * s -> s
  val str_Rpow_Zint : s * (bool * s) -> s
  val str_Zvar : s -> s
  val str_Zopp : s -> s
  val str_Zabs : s -> s
  val str_Zbin : zbin * s * s -> s

  val str_Rvar : s -> s
  val str_Rcst : rcst -> s
  val str_IZR : s -> s
  val str_Ropp : s -> s
  val str_Rinv : s -> s
  val str_Rabs : s -> s
  val str_Rpow : s * s -> s
  val str_Rbin : rbin * s * s -> s
  val str_Rfun : rfun * s -> s

  val str_typ : typ -> s

  val str_Ptrue : s
  val str_Pfalse : s
  val str_Zle : s * s -> s
  val str_Zlt : s * s -> s
  val str_Zeq : s * s -> s
  val str_Rle : s * s -> s
  val str_Rlt : s * s -> s
  val str_Req : s * s -> s
  val str_Pnot : s -> s
  val str_Pand : s * s -> s
  val str_Por : s * s -> s
  val str_Parrow : s * s -> s
  val str_Piff : s * s -> s
  val str_Pexists : s * s * s -> s
  val str_Pforall : s * s * s -> s

  val str_stmt : s * s -> s
end

let dest_big n = (Big_int.sign_big_int n < 0, (* in practice, it'll be false *)
		  Big_int.string_of_big_int (Big_int.abs_big_int n))

module Printer_gen (A : PRINT) =
struct

let rec str_zint = function
  | Zint n -> A.str_Zint (dest_big n)
  | Zvar n -> A.str_Zvar n
  | Zopp a -> A.str_Zopp (str_zint a)
  | Zabs a -> A.str_Zabs (str_zint a)
  | Zbin (o, a, b) -> A.str_Zbin (o, str_zint a, str_zint b)

let rec str_real = function
  | Rvar n -> A.str_Rvar n
  | Rcst c -> A.str_Rcst c
  | IZR a ->
    (match a with
    | Zint n -> A.str_IZR_Zint (dest_big n)
    | _ -> A.str_IZR (str_zint a))
  | Ropp a -> A.str_Ropp (str_real a)
  | Rinv a -> A.str_Rinv (str_real a)
  | Rabs a -> A.str_Rabs (str_real a)
  | Rpow (a, b) ->
    (match b with
    | Zint n -> A.str_Rpow_Zint (str_real a, dest_big n)
    | _ -> A.str_Rpow (str_real a, str_zint b))
  | Rbin (o, a, b) -> A.str_Rbin (o, str_real a, str_real b)
  | Rfun (f, a) -> A.str_Rfun (f, str_real a)

let rec str_prop = function
  | Ptrue -> A.str_Ptrue
  | Pfalse -> A.str_Pfalse
  | Zle (a, b) -> A.str_Zle (str_zint a, str_zint b)
  | Rle (a, b) -> A.str_Rle (str_real a, str_real b)
  | Zlt (a, b) -> A.str_Zlt (str_zint a, str_zint b)
  | Rlt (a, b) -> A.str_Rlt (str_real a, str_real b)
  | Zeq (a, b) -> A.str_Zeq (str_zint a, str_zint b)
  | Req (a, b) -> A.str_Req (str_real a, str_real b)
  | Pnot a -> A.str_Pnot (str_prop a)
  | Pand (a, b) -> A.str_Pand (str_prop a, str_prop b)
  | Por (a, b) -> A.str_Por (str_prop a, str_prop b)
  | Parrow (a, b) -> A.str_Parrow (str_prop a, str_prop b)
  | Piff (a, b) -> A.str_Piff (str_prop a, str_prop b)
  | Pexists (a, b, c) -> A.str_Pexists (a, A.str_typ b, str_prop c)
  | Pforall (a, b, c) -> A.str_Pforall (a, A.str_typ b, str_prop c)
  
let str_stmt (a : stmt) =
  A.str_stmt (fst a, str_prop (snd a))

end

module Print_tex : PRINT =
struct
  type s = string

  let inP a = "\\left(" ^ a ^ "\\right)"

  (* in braces *)
  let inb a = "{" ^ a ^ "}"

  let aux_var a = "\\textit" ^ (inb a)

  let sgn b = if b then "-" else ""
  let str_Zint (b, a) = (sgn b) ^ a
  let str_IZR_Zint = str_Zint

  let str_Zvar = aux_var
  let str_Zopp a = inP ("- " ^ a)
  let str_Zabs a = "\\left|" ^ a ^ "\\right|"
  let str_Zbin (o, a, b) =
    let o' = match o with Zadd -> "+" | Zsub -> "-"
      | Zmul -> "\\times" | Zpow -> "^" in
    if o' = "^" then (a ^ "^" ^ (inb b))
    else inP (a ^ " " ^ o' ^ " " ^ b)

  let str_Rvar = aux_var
  let str_Rcst _ = "\\pi "
  let str_IZR a = a (*!*)
  let str_Ropp a = inP ("- " ^ a)
  let str_Rinv a = inP ("1 / " ^ a)
  let str_Rabs = str_Zabs
  let str_Rpow (a, b) = inP (a ^ "^" ^ (inb b))
  let str_Rpow_Zint (a, (b, c)) = str_Rpow (a, str_Zint (b, c))
  let str_Rbin (o, a, b) =
    let o' = match o with Radd -> "+" | Rsub -> "-"
      | Rmul -> "\\times" | Rdiv -> "/" in
    if o' = "/" then "\\frac" ^ (inb a) ^ (inb b)
    else inP (a ^ " " ^ o' ^ " " ^ b)
  let str_Rfun (f, a) =
    let f' = match f with Rsqrt -> "\\sqrt"
    | Rcos -> "\\cos" | Rsin -> "\\sin" | Rtan -> "\\tan" | Ratan -> "\\arctan"
    | Rexp -> "\\exp" | Rln -> "\\ln" in
    if f' = "\\sqrt" then f' ^ (inb a)
    else f' ^ (inP a)
  let str_typ = function
    | Tzint -> "\\mathbb{Z}"
    | Treal -> "\\mathbb{R}"
  let str_Ptrue = "\\top"
  let str_Pfalse = "\\bot"
  let str_Zle (a, b) = inP (a ^ " \\leq " ^ b)
  let str_Zlt (a, b) = inP (a ^ " < " ^ b)
  let str_Zeq (a, b) = inP (a ^ " = " ^ b)
  let str_Rle = str_Zle
  let str_Rlt = str_Zlt
  let str_Req = str_Zeq
  let str_Pnot a = inP ("\\neg" ^ a)
  let str_Pand (a, b) = inP (a ^ " \\wedge " ^ b)
  let str_Por (a, b) = inP (a ^ " \\vee " ^ b)
  let str_Parrow (a, b) = inP (a ^ " \\implies " ^ b)
  let str_Piff (a, b) = inP (a ^ " \\iff " ^ b)
  let str_Pexists (a, b, c) =
    inP ("\\exists " ^ (aux_var a) ^ " \\in " ^ b ^ ", " ^ c)
  let str_Pforall (a, b, c) =
    inP ("\\forall " ^ (aux_var a) ^ " \\in " ^ b ^ ", " ^ c)
  let str_stmt (a, b) =
    "\\begin{equation}\n"
    ^ "\\text" ^ (inb a) ^ " : " ^ b
    ^ "\n\\end{equation}\n"

end

module Printer_tex = Printer_gen(Print_tex);;

module Print_pvs : PRINT =
struct
  type s = string

  let aux_var a : s = a

  let sgn b = if b then "-" else ""
  let str_Zint (b, a) = (sgn b) ^ a
  let str_IZR_Zint = str_Zint

  let str_Zvar = aux_var
  let str_Zopp a = inp ("- " ^ a)
  let str_Zabs a = "abs" ^ (inp a)
  let str_Zbin (o, a, b) =
    let o' = match o with Zadd -> "+" | Zsub -> "-"
      | Zmul -> "*" | Zpow -> "^" in
    inp (a ^ " " ^ o' ^ " " ^ b)

  let str_Rvar = aux_var
  let str_Rcst _ = "pi"
  let str_IZR a = a (*!*)
  let str_Ropp a = inp ("- " ^ a)
  let str_Rinv a = inp ("1 / " ^ a)
  let str_Rabs = str_Zabs
  let str_Rpow (a, b) = inp (a ^ " ^ " ^ b)
  let str_Rpow_Zint (a, (b, c)) = str_Rpow (a, str_Zint (b, c))
  let str_Rbin (o, a, b) =
    let o' = match o with Radd -> "+" | Rsub -> "-"
      | Rmul -> "*" | Rdiv -> "/" in
    inp (a ^ " " ^ o' ^ " " ^ b)
  let str_Rfun (f, a) =
    let f' = match f with Rsqrt -> "sqrt"
      | Rcos -> "cos" | Rsin -> "sin" | Rtan -> "tan" | Ratan -> "atan"
      | Rexp -> "exp" | Rln -> "ln" in
    f' ^ (inp a)
  let str_typ = function
    | Tzint -> "int"
    | Treal -> "real"
  let str_Ptrue = "TRUE"
  let str_Pfalse = "FALSE"
  let str_Zle (a, b) = inp (a ^ " <= " ^ b)
  let str_Zlt (a, b) = inp (a ^ " < " ^ b)
  let str_Zeq (a, b) = inp (a ^ " = " ^ b)
  let str_Rle = str_Zle
  let str_Rlt = str_Zlt
  let str_Req = str_Zeq
  let str_Pnot a = inp ("NOT " ^ a)
  let str_Pand (a, b) = inp (a ^ " AND " ^ b)
  let str_Por (a, b) = inp (a ^ " OR " ^ b)
  let str_Parrow (a, b) = inp (a ^ " IMPLIES " ^ b)
  let str_Piff (a, b) = inp (a ^ " IFF " ^ b)
  let str_Pexists (a, b, c) =
    inp ("EXISTS (" ^ (aux_var a) ^ " : " ^ b ^ "): " ^ c)
  let str_Pforall (a, b, c) =
    inp ("FORALL (" ^ (aux_var a) ^ " : " ^ b ^ "): " ^ c)
  let str_stmt (a, b) = a ^ " : LEMMA " ^ b

end

module Printer_pvs = Printer_gen(Print_pvs);;

(* Print_hl_common implements PRINT, except str_Zabs, str_Rabs, str_stmt *)

module Print_hl_common =
struct
  type s = string

  let aux_var a : s = a

  let sgn b = if b then "-- " else ""
  let str_Zint (b, a) = (sgn b) ^ "&" ^ a
  let str_IZR_Zint = str_Zint

  let str_Zvar = aux_var
  let str_Zopp a = inp ("-- " ^ a)

  let str_Zbin (o, a, b) =
    let o' = match o with Zadd -> "+" | Zsub -> "-"
      | Zmul -> "*" | Zpow -> raise (Unsupported "Zpow") in
    inp (a ^ " " ^ o' ^ " " ^ b)

  let str_Rvar = aux_var
  let str_Rcst _ = "pi"
  let str_IZR a = "real_of_int" ^ (inp a)
  let str_Ropp a = inp ("-- " ^ a)
  let str_Rinv a = inp ("&1 / " ^ a)

  let str_Rpow (a, b) = (* inp (a ^ " pow " ^ b) *)
    raise (Unsupported "Rpow (exponent must be a non-negative constant)")
  let str_Rpow_Zint (a, (b, c)) =
    if b then raise (Unsupported "_ pow (-- _)")
    else inp (a ^ " pow " ^ c)
  let str_Rbin (o, a, b) =
    let o' = match o with Radd -> "+" | Rsub -> "-"
      | Rmul -> "*" | Rdiv -> "/" in
    inp (a ^ " " ^ o' ^ " " ^ b)
  let str_Rfun (f, a) =
    let f' = match f with Rsqrt -> "sqrt"
      | Rcos -> "cos" | Rsin -> "sin" | Rtan -> "tan" | Ratan -> "atn"
      | Rexp -> "exp" | Rln -> "log" in
    f' ^ (inp a)
  let str_typ = function
    | Tzint -> "int"
    | Treal -> "real"
  let str_Ptrue = "TRUE"
  let str_Pfalse = "FALSE"
  let str_Zle (a, b) = inp (a ^ " <= " ^ b)
  let str_Zlt (a, b) = inp (a ^ " < " ^ b)
  let str_Zeq (a, b) = inp (a ^ " = " ^ b)
  let str_Rle = str_Zle
  let str_Rlt = str_Zlt
  let str_Req = str_Zeq
  let str_Pnot a = inp ("~ " ^ a)
  let str_Pand (a, b) = inp (a ^ " /\\ " ^ b)
  let str_Por (a, b) = inp (a ^ " \\/ " ^ b)
  let str_Parrow (a, b) = inp (a ^ " ==> " ^ b)
  let str_Piff (a, b) = inp (a ^ " <=> " ^ b)
  let str_Pexists (a, b, c) =
    raise (Unsupported "exists")
  let str_Pforall (a, b, c) : s = c (*!*)

end

module Print_hl_alex : PRINT =
struct
  include Print_hl_common
  let str_Zabs a = "abs" ^ (inp a)
  (* raise (Unsupported "Zabs") *)
  let str_Rabs a = "abs" ^ (inp a)
  (* raise (Unsupported "Rabs") *)
  let str_stmt (a, b) =
    "let " ^ a ^ " =\n  `" ^ b ^ "`;;\n\n"
    ^ "let th_"^a^", st_"^a ^ " = verify_ineq default_params 5 " ^ a ^ ";;"
end

module Printer_hl_alex = Printer_gen(Print_hl_alex);;

module Print_hl_sos : PRINT =
struct
  include Print_hl_common
  let str_Zabs a = "abs" ^ (inp a)
  let str_Rabs a = "abs" ^ (inp a)
  let str_stmt (a, b) =
    "let " ^ a ^ " =\n  `" ^ b ^ "`;;\n\n"
    ^ "let th_"^a^ " = time REAL_SOS " ^ a ^ ";;"
end

module Printer_hl_sos = Printer_gen(Print_hl_sos);;
