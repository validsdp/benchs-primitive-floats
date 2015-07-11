type name = string

(* binary operations over Z *)
type zbin =
  Zadd | Zsub | Zmul | Zpow

type zint =
  Zint of Big_int.big_int
| Zvar of name
| Zopp of zint
| Zabs of zint
| Zbin of zbin * zint * zint 

let z0 : zint = Zint Big_int.zero_big_int

let z1 : zint  = Zint Big_int.unit_big_int

(* binary operations over R *)
type rbin =
  Radd | Rsub | Rmul | Rdiv

(* elementary functions *)
type rfun =
  Rsqrt | Rcos | Rsin | Rtan | Ratan | Rexp | Rln

type rcst =
  Pi

type real =
  Rvar of name
| Rcst of rcst
| IZR of zint
| Ropp of real
| Rinv of real
| Rabs of real
| Rpow of real * zint
| Rbin of rbin * real * real
| Rfun of rfun * real

(* DISCLAIMER: only first-order for now *)

type typ =
  Tzint
| Treal

(* type scope = typ *)

type prop =
  Ptrue
| Pfalse
| Zle of zint * zint
| Zlt of zint * zint
| Zeq of zint * zint
| Rle of real * real
| Rlt of real * real
| Req of real * real
| Pnot of prop
| Pand of prop * prop
| Por of prop * prop
| Parrow of prop * prop
| Piff of prop * prop
| Pexists of name * typ * prop
| Pforall of name * typ * prop

type stmt =
  name * prop

let typ_of_string s =
  match s with
  | "R" -> Treal
  | "Z" -> Tzint 
  (* | "nat" -> *)
  | _ -> failwith ("Unknown type: "^s)

(*
let scope_of_string s =
  match s with
  | "R" -> Treal
  | "Z" -> Tzint 
  (* | "N" -> *)
  | _ -> failwith ("Unknown scope: "^s)
*)
