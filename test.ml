let rec get_bound (tm : term) : term list * term =
  match tm with
    Abs(bvar,bod) -> let tml,tm' = get_bound bod in (bvar::tml),tm'
  | _ -> [],tm;;

get_bound `\x y z. f x y z`;;

let rec bound_eta_norm (tm1,tm2) : term * term =
  match tm1,tm2 with
    Abs(bv1,bod1),Abs(bv2,bod2) -> let bod1,bod2 = bound_eta_norm (bod1,bod2) in
                                   if not (vfree_in bv1 bod1) && not (vfree_in bv2 bod2) then bod1,bod2
                                   else (try let f1,x1 = dest_comb bod1 in
                                             if Pervasives.compare bv1 x1 = 0 && not (vfree_in bv1 f1) then f1
                                             else mk_abs (bv1,bod1)
                                         with Failure _ -> mk_abs (bv1,bod1)),
                                        (try let f2,x2 = dest_comb bod2 in
                                             if Pervasives.compare bv2 x2 = 0 && not (vfree_in bv2 f2) then f2
                                             else mk_abs (bv2,bod2)
                                         with Failure _ -> mk_abs (bv2,bod2))
  | _ -> tm1,tm2;;

let decompose (tm : term) : term list * (term * term list) =
  let bvars,ctm = get_bound tm in
  bvars,strip_comb ctm;;

let head_free (tm : term) : bool =
  let bvars,tm = get_bound tm in
  let hsym = repeat rator tm in
  not (is_const hsym) && not (mem hsym bvars);;

let bindex (var : term) (bvars : term list) : int =
  try let ret = index var (rev bvars) in
      (length bvars) - ret - 1
  with Failure _ -> -1;;

let rec check_rr (obj : (term * term) list) : (hol_type * hol_type) list =
  match obj with
    [] -> []
  | (tm1,tm2)::t -> let bv1,(hs1,_) = decompose tm1 and bv2,(hs2,_) = decompose tm2 in
                    let bin1 = bindex hs1 bv1 and bin2 = bindex hs2 bv2 in
                    if bin1 <> bin2 || is_const hs1 <> is_const hs2 then failwith "check_rr"
                    else if is_const hs1 && is_const hs2 then
                      if fst (dest_const hs1) <> fst (dest_const hs2) then failwith "check_rr"
                      else (type_of hs1,type_of hs2)::(check_rr t)
                    else check_rr t;;

let f bv2 bv1 args2 args1 =
  let l1 = length bv1 and l2 = length bv2 in
  if l1 = l2 then bv1,bv2,args1,args2
  else if l1 < l2 then
    let extra = Array.to_list (Array.sub (Array.of_list bv2) l1 (l2-l1)) in
    bv1 @ extra,args1 @ extra,bv2,args2
  else
    let extra = Array.to_list (Array.sub (Array.of_list bv1) l2 (l1-l2)) in
    bv1,args1,bv2 @ extra,args2 @ extra;;
