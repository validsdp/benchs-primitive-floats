(* generate random positive definite matrices *)

let random_float () =
  if Random.bool () then Random.float (-1.) else Random.float 1.

let rand_square_matrix n =
  let m = Array.make_matrix n n 0. in
  for i = 0 to n - 1 do
    for j = 0 to n - 1 do
      m.(i).(j) <- random_float ()
    done
  done;
  m

(* preconditions:
 * [a] and [b] are matrices (float array array whose elements are all
   array of the same length)
 * [b] has at least one line
 * number of columns of [a] and number of rows of [b] are equal *)
let mult_matrix a b =
  let l = Array.length a in
  let r = Array.length b.(0) in
  let lb = Array.length b in
  let c = Array.make_matrix l r 0. in
  for i = 0 to l - 1 do
    for j = 0 to r - 1 do
      for k = 0 to lb - 1 do
        c.(i).(j) <- c.(i).(j) +. a.(i).(k) *. b.(k).(j)
      done
    done
  done;
  c

let transpose a =
  let l = Array.length a in
  let b = Array.make_matrix l l 0. in
  for i = 0 to l - 1 do
    for j = 0 to l - 1 do
      b.(j).(i) <- a.(i).(j)
    done
  done;
  b

let add_matrix a b =
  let l = Array.length a in
  let r = Array.length a.(0) in
  let c = Array.make_matrix l r 0. in
  for i = 0 to l - 1 do
    for j = 0 to r - 1 do
      c.(i).(j) <- a.(i).(j) +. b.(i).(j)
    done
  done;
  c

(* precondition : a must be a square matrix *)
let add_to_diag a x =
  let l = Array.length a in
  let b = Array.make_matrix l l 0. in
  for i = 0 to l - 1 do
    for j = 0 to l - 1 do
      b.(i).(j) <- a.(i).(j) +. (if i = j then x else 0.)
    done
  done;
  b

let rand_posdef_matrix n =
  let a = rand_square_matrix n in
  let b = mult_matrix a (transpose a) in
  let c = add_matrix b (transpose b) in
  add_to_diag c 1.

(* pretty printing *)

let pp_array ~sep pp_elem fmt a =
  let l = Array.length a in
  if l > 0 then
    begin
      Format.fprintf fmt "%a" pp_elem a.(0);
      for i = 1 to l - 1 do
        Format.fprintf fmt "%(%)%a" sep pp_elem a.(i)
      done
    end

let pp_array_as_list ~begl pp_elem fmt a =
  Format.fprintf fmt "[%s@[%a@]]" begl (pp_array ~sep:";@ " pp_elem) a

let pp_matrix ~begl pp_elem fmt a =
  pp_array_as_list ~begl (pp_array_as_list ~begl pp_elem) fmt a

let pp_coq fmt lm =
  let pp_print_float_coq fmt f =
    let m, e = frexp f in
    let m = int_of_float (m *. (2. ** 53.)) in
    let e = e - 53 in
    Format.fprintf fmt "Float (%d) (%d)" m e in
  let pp_m fmt m =
    let sz = Array.length m in
    Format.fprintf
      fmt
      "@[<v>(* size %d *)@ Definition matrix :=@   %a.@]"
      sz
      (pp_matrix ~begl:":: " pp_print_float_coq) m in
  Format.fprintf
    fmt
    {|@[<v>(* randomly generated positive definite matrix *)

From Bignums Require Import BigZ.
Require Import Interval.Float.Specific_ops.
Require Import mathcomp.ssreflect.seq.
Require Import ValidSDP.posdef_check.

(*
BEGIN DEFINITION *)

Local Open Scope bigZ_scope.
%a

Definition matrix_float := Eval vm_compute in map (map BigZFloat2Prim) matrix.

(* END DEFINITION
 *)

(* TEST *)

(* EMULATED
Goal posdef_seqF matrix.
idtac "emulated, size %d".
Time posdef_check.
Qed.
EMULATED *)
(* PRIMITIVE
Goal posdef_seqF matrix.
idtac "primitive, size %d".
Time primitive_posdef_check.
Qed.
PRIMITIVE *)@]|}
    pp_m lm (Array.length lm) (Array.length lm)

let pp_file filename f =
  let oc = open_out filename in
  let fmt = Format.formatter_of_out_channel oc in
  f fmt;
  close_out oc

(* main program *)

let rec rand_matrices from_sz to_sz incr =
  if from_sz > to_sz then [] else
    rand_posdef_matrix from_sz :: rand_matrices (from_sz + incr) to_sz incr

let _ =
  Random.init 42;
  let matrices = rand_matrices 50 500 50 in
  List.iter
    (fun mx ->
      let filename = Printf.sprintf "matrices/mat%04d.v" (Array.length mx) in
      pp_file
        filename
        (fun fmt -> Format.fprintf fmt "%a@." pp_coq mx))
    matrices

