(*
 * Expand every defined constant in a term
 *)
let expand_const tm =
  let rec work tm defs =
    match tm with
      Comb(f,x) -> mk_comb (work f defs, work x defs)
    | Abs(var,bod) -> mk_abs (var, work bod defs)
    | Const(c,ty) -> (match defs with
                        (h::t) -> let op,sub = dest_eq (concl h) in
                                  let c_name,c_ty = dest_const op in
                                  if c = c_name then (
                                    let ty_sub = type_match c_ty ty [] in
                                    work (inst ty_sub sub) t
                                  ) else work tm t
                      | [] -> tm
                     )
    | Var(_,_) -> tm in
  work tm (definitions());;

(*
 * Beta normal form of a term
 *)
let beta_norm = rand o concl o (TOP_DEPTH_CONV BETA_CONV);;
let eta_norm = rand o concl o (TOP_DEPTH_CONV ETA_CONV);;
let beta_eta_norm = rand o concl o ((TOP_DEPTH_CONV BETA_CONV) THENC (TOP_DEPTH_CONV ETA_CONV));;

let size_of_term tm =
  let rec work tm =
    match tm with
      Comb(f,x) -> (work f) + (work x)
    | Abs(_,bod) -> work bod
    | _ -> 1 in
  work tm;;
