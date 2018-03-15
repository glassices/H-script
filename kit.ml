let pmap f =
  let rec pmapf l =
    match l with
      [] -> []
    | (a,b)::t -> (f a,f b)::(pmapf t) in
  pmapf;;

let rec pop p l =
  match l with
    [] -> failwith "pop"
  | h::t -> if p(h) then h,t
            else let x,s = pop p t in x,(h::s);;

(*
 * Input: `:A->B->C->D`
 * Output: ([`:A`; `:B`; `:C`], `:D`)
 *)
let rec dest_fun ty : hol_type list * hol_type =
  try let a,b = dest_fun_ty ty in
      let tyl,apex = dest_fun b in
      (a::tyl),apex
  with Failure "dest_fun_ty" -> [],ty;;

(*
 * Input: ([`:A`; `:B`; `:C`], `:D`)
 * Output: `:A->B->C->D`
 *)
let rec mk_fun (tyl,apex) : hol_type =
  match tyl with
    h::t -> mk_fun_ty h (mk_fun (t,apex))
  | [] -> apex;;

(*
 * Input: `f` [`x`; `y`]
 * Output: `f x y`
 *)
let rec mk_lcomb (f : term) (args : term list) : term =
  match args with
    h::t -> mk_lcomb (mk_comb (f,h)) t
  | [] -> f;;

let (beta_eta_conv : conv) = (TOP_DEPTH_CONV BETA_CONV) THENC (TOP_DEPTH_CONV ETA_CONV);;

let (beta_eta_term : term -> term) = rand o concl o beta_eta_conv;;

(* conv the concl of a theorem *)
let conv_concl (cnv : conv) (th : thm) : thm =
  EQ_MP (cnv (concl th)) th;;

(* Conv assumptions and the conclusion of a theorem *)
let conv_thm (cnv : conv) (th : thm) : thm =
  let asl,c = dest_thm th in
  let work a th =
    let eth = cnv a in
    let gth = EQ_MP (SYM eth) (ASSUME (rand (concl eth))) in
    EQ_MP (DEDUCT_ANTISYM_RULE gth th) gth in
  conv_concl cnv (itlist work asl th);;
