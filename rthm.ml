needs "script/unification.ml";;

if not (can get_const_type "mogic") then
  new_constant("mogic",`:A`);;

if not (can get_const_type "tmp") then
  new_constant("tmp",`:A`);;

let abs_name = "xdq";;

let varyname_thm th =
  let rec variant avoid s =
    if not (mem s avoid) then s
    else variant avoid (s ^ "'") in
  let rec f fvars used =
    match fvars with
      h::t -> let name,_ = dest_var h in
              let name' = variant used name in
              if name' = name then f t (name'::used)
              else (mk_var(name',type_of h),h)::(f t (name'::used))
    | [] -> [] in
  let asl,c = dest_thm th in
  let fvars = freesl (c::asl) in
  INST (f fvars []) th;;

module type Rthm_kernel =
  sig
    type rthm

    val mk_rthm : thm -> rthm
    val dest_rthm : rthm -> term list * term * term list
    val rhyp : rthm -> term list
    val rconcl : rthm -> term
    val get_rthm : rthm -> (unifier list) -> thm

    val normalize_name : rthm -> string -> string -> rthm
    val rinst : unifier -> rthm -> rthm
    val rtrans : rthm -> rthm -> rthm list
    val req_mp : rthm -> rthm -> rthm list

end;;

let h = ref ([] : unifier list);;

module Rthm : Rthm_kernel = struct

  (*
   * Philosopy of Rthm
   * 1: Any term in a rthm MUST be beta-eta normal form
   * 2: rsl must be in the most succinct form
   * 3*: invoke function is private and can not be called from the outside
   * 4: invoke [old;...;new]
   *)

  type rthm = Rhythm of (term list * term * term list * (unifier list -> thm));;

  let mk_rthm th =
    let th = conv_thm beta_eta_conv th in
    let asl,c = dest_thm th in
    Rhythm(asl,c,[],fun unfl -> conv_thm beta_eta_conv (rev_itlist unify_thm unfl th));;

  let dest_rthm (Rhythm(asl,c,rsl,_)) = (asl,c,rsl);;

  let rhyp (Rhythm(asl,_,_,_)) = asl;;
  
  let rconcl (Rhythm(_,c,_,_)) = c;;

  let rec is_mogical tm =
    match tm with
      Comb(f,x) -> is_mogical f || is_mogical x
    | Abs(_,bod) -> is_mogical bod
    | Const("mogic",_) -> true
    | _ -> false;;

  let get_rthm (Rhythm(_,_,rsl,invoke)) unfl =
    (* check whether unfl can clean "mogic" *)
    do_list (fun tm -> if is_mogical (beta_eta_term (rev_itlist unify_term unfl tm)) then
                         failwith "get_rthm"
                       else ()) rsl;
    invoke unfl;;

  let purify (asl,c,rsl) =
    let qsort = List.sort (fun x y -> Pervasives.compare x y) in

    let rec clean bvars fvars =
      match bvars with
        h::t -> let cnt = clean t fvars in
                if not (mem h fvars) || (mem h cnt) then cnt
                else h::cnt
      | [] -> [] in

    let rec work env tm =
      let bvars,bod = get_bound tm in
      let hsym,args = strip_comb bod in
      let env = env @ bvars in
      if is_const hsym && fst (dest_const hsym) = "mogic" then
        failwith "purify"
      else if is_const hsym || mem hsym env then
        itlist ((@) o (work env)) args []
      else if is_mogical bod then
        (* clean extra bound vars *)
        let bvars = clean bvars (frees bod) in
        [conv_term eta_conv (mk_term bvars bod)]
      else [] in

    (* beta-eta normalization, deduplicate, simple work on rsl *)
    let asl = uniq (qsort (map beta_eta_term asl)) in
    let c = beta_eta_term c in
    let rsl = map beta_eta_term rsl in
    let rsl = uniq (qsort (itlist ((@) o (work [])) rsl [])) in
    (asl,c,rsl);;

  (*
   * TODO deep purify: kill all FVs that dont appear in asl,c
   *)

  let rinst unf (Rhythm(asl,c,rsl,invoke)) =
    try let asl,c,rsl = purify (map (unify_term unf) asl,
                                unify_term unf c,
                                map (unify_term unf) rsl) in
        if rsl = [] then
          let th = invoke [unf] in
          Rhythm(asl,c,[],fun unfl -> conv_thm beta_eta_conv (rev_itlist unify_thm unfl th))
        else Rhythm(asl,c,rsl,fun unfl -> invoke (unf::unfl))
    with Failure "purify" -> failwith "rinst";;

  (*
   * normalize the name of freevars and typevars in a rtheorem
   * all freevars will be renamed to be vpre{#n}
   * all tyvars will be renamed to be tpre{#n}
   *)
  let normalize_name rth vpre tpre =
    let asl,c,rsl = dest_rthm rth in
    let fv = freesl ((c::asl) @ rsl) and tv = itlist (union o type_vars_in_term) ((c::asl) @ rsl) [] in
    (* rename vars first then tyvars, since renaming tyvars will make (x:A) and (x:B) conflict *)
    let tmins = List.mapi (fun i var -> (mk_var (vpre ^ (string_of_int (i+1)),type_of var),var)) fv in
    let tyins = List.mapi (fun i ty -> (mk_vartype (tpre ^ (string_of_int (i+1))),ty)) tv in
    rinst (tmins,tyins,[]) rth;;

  let rec term_image f l =
    match l with
      h::t -> let h' = f h and t' = term_image f t in
              if mem h' t' then t' else h'::t'
    | [] -> [];;

  let rec variant avoid s =
    if not (mem s avoid) then s
    else variant avoid (s ^ "'");;

  let vnames_of_rthm (Rhythm(asl,c,rsl,_)) =
    let fvars = freesl ((c::asl) @ rsl) in
    term_image (fst o dest_var) fvars;;

  let tnames_of_rthm (Rhythm(asl,c,rsl,_)) =
    let tvars = itlist (union o type_vars_in_term) ((c::asl) @ rsl) [] in
    map dest_vartype tvars;;

  let rec c_mogic tm =
    match tm with
      Comb(f,x) -> mk_comb (c_mogic f,c_mogic x)
    | Abs(bvar,bod) -> mk_abs (bvar,c_mogic bod)
    | Const("tmp",ty) -> mk_const ("mogic",[ty,`:A`])
    | _ -> tm

  let rec c_movar tm =
    match tm with
      Comb(f,x) -> mk_comb (c_movar f,c_movar x)
    | Abs(bvar,bod) -> mk_abs (bvar,c_movar bod)
    | Const("tmp",ty) -> mk_var (abs_name,ty)
    | _ -> tm

  let rtrans rth1 rth2 =
    let infer rth1 rth2 (unf : unifier) : rthm =
      let (Rhythm(asl1,c1,rsl1,invoke1)) = rinst unf rth1 in
      let (Rhythm(asl2,c2,rsl2,invoke2)) = rinst unf rth2 in
      Rhythm(union asl1 asl2,mk_eq (lhs c1,rhs c2),union rsl1 rsl2,
             fun unfl -> TRANS (invoke1 unfl) (invoke2 unfl)) in

    let linfer (Rhythm(asl1,c1,rsl1,invoke1)) (Rhythm(asl2,c2,rsl2,invoke2)) (pre,tyins,tmins) cty =
      let x = mk_var (abs_name,cty) in
      let unfm = (pre,tyins,map (fun (b,a) -> (c_mogic b,a)) tmins) in
      let unfx = (pre,tyins,map (fun (b,a) -> (c_movar b,a)) tmins) in
      let s,t = dest_eq c1 and u,v = dest_eq c2 in
      let asl,c,rsl = purify(map (unify_term unfm) (asl1 @ asl2),
                             mk_eq (unify_term unfm s,mk_abs (x,unify_term unfx v)),
                             map (unify_term unfm) (rsl1 @ rsl2 @ asl1 @ asl2 @ [s;t])) in
      (* (\x. T) c <=> T *)
      Rhythm(asl,c,rsl,
             fun unfl -> TRANS (invoke1 (unfx::unfl))
                               (conv_concl top_eta_conv
                                           (ABS (rev_itlist (fun (_,tyins,_) v -> inst tyins v) unfl x)
                                                (invoke2 (unfx::unfl))))) in

    let rinfer (Rhythm(asl1,c1,rsl1,invoke1)) (Rhythm(asl2,c2,rsl2,invoke2)) (pre,tyins,tmins) cty =
      let x = mk_var (abs_name,cty) in
      let unfm = (pre,tyins,map (fun (b,a) -> (c_mogic b,a)) tmins) in
      let unfx = (pre,tyins,map (fun (b,a) -> (c_movar b,a)) tmins) in
      let s,t = dest_eq c1 and u,v = dest_eq c2 in
      let asl,c,rsl = purify(map (unify_term unfm) (asl1 @ asl2),
                             mk_eq (mk_abs (x,unify_term unfx s),unify_term unfm v),
                             map (unify_term unfm) (rsl1 @ rsl2 @ asl1 @ asl2 @ [u;v])) in
      (* (\x. T) c <=> T *)
      Rhythm(asl,c,rsl,
             fun unfl -> TRANS (conv_concl top_eta_conv
                                           (ABS (rev_itlist (fun (_,tyins,_) v -> inst tyins v) unfl x)
                                                (invoke1 (unfx::unfl))))
                               (invoke2 (unfx::unfl))) in

    let work rth1 rth2 : rthm list =
      let rth1 = normalize_name rth1 "x" "A" and rth2 = normalize_name rth2 "y" "B" in
      let asl1,c1,_ = dest_rthm rth1 and asl2,c2,_ = dest_rthm rth2 in
      let fnames = union (vnames_of_rthm rth1) (vnames_of_rthm rth2) in
      let s,t = dest_eq c1 and u,v = dest_eq c2 in
      let asl1 = Array.of_list asl1 and asl2 = Array.of_list asl2 in
      let n = Array.length asl1 and m = Array.length asl2 in
      let pairs = map (fun x -> (x / m,x mod m)) (0--(n*m-1)) in
      let rec dfs (ps : (int * int) list) (task : (term * term) list) : unifier list =
        match ps with
          (i,j)::t -> let res = dfs t task in
                      if res = [] then []
                      else (dfs t ((Array.get asl1 i,Array.get asl2 j)::task)) @ res
        | [] -> hol_unify fnames task in
      let std = try let _ = type_unify [type_of t,type_of u] in
                    let unfs = dfs pairs [t,u] in
                    map (fun unf -> infer rth1 rth2 unf) unfs
                with Failure "type_unify" -> [] in
      let ltd = try let p,q = dest_fun_ty (type_of t) in
                    try let _ = type_unify [q,type_of u] in
                        let c = mk_const ("tmp",[p,`:A`]) in
                        let unfs = dfs pairs [mk_comb (t,c),u] in
                        map (fun ((_,tyins,_) as unf) ->
                             linfer rth1 rth2 unf (type_subst tyins p)) unfs
                    with Failure "type_unify" -> []
                with Failure "dest_fun_ty" -> [] in
      let rtd = try let p,q = dest_fun_ty (type_of u) in
                    try let _ = type_unify [q,type_of t] in
                        let c = mk_const ("tmp",[p,`:A`]) in
                        let unfs = dfs pairs [t,mk_comb (u,c)] in
                        map (fun ((_,tyins,_) as unf) ->
                             rinfer rth1 rth2 unf (type_subst tyins p)) unfs
                    with Failure "type_unify" -> []
                with Failure "dest_fun_ty" -> [] in
      std @ ltd @ rtd in

    let v1 = vnames_of_rthm rth1 and t1 = tnames_of_rthm rth1 in
    let u = variant v1 "u" and v = variant v1 "v" and t = variant t1 "U" in
    let unf1 = hol_unify v1 [(rconcl rth1),mk_eq (mk_var(u,mk_vartype(t)),mk_var(v,mk_vartype(t)))] in
    let v2 = vnames_of_rthm rth2 and t2 = tnames_of_rthm rth2 in
    let u = variant v2 "u" and v = variant v2 "v" and t = variant t2 "U" in
    let unf2 = hol_unify v2 [(rconcl rth2),mk_eq (mk_var(u,mk_vartype(t)),mk_var(v,mk_vartype(t)))] in
    flat (allpairs (fun x y -> work (rinst x rth1) (rinst y rth2)) unf1 unf2);;

  let req_mp rth1 rth2 =
    let infer rth1 rth2 (unf : unifier) : rthm =
      let (Rhythm(asl1,c1,rsl1,invoke1)) = rinst unf rth1 in
      let (Rhythm(asl2,c2,rsl2,invoke2)) = rinst unf rth2 in
      Rhythm(union asl1 asl2,mk_eq (lhs c1,rhs c2),union rsl1 rsl2,
             fun unfl -> TRANS (invoke1 unfl) (invoke2 unfl)) in

    let linfer (Rhythm(asl1,c1,rsl1,invoke1)) (Rhythm(asl2,c2,rsl2,invoke2)) (pre,tyins,tmins) cty =
      let x = mk_var (abs_name,cty) in
      let unfm = (pre,tyins,map (fun (b,a) -> (c_mogic b,a)) tmins) in
      let unfx = (pre,tyins,map (fun (b,a) -> (c_movar b,a)) tmins) in
      let s,t = dest_eq c1 and u,v = dest_eq c2 in
      let asl,c,rsl = purify(map (unify_term unfm) (asl1 @ asl2),
                             mk_eq (unify_term unfm s,mk_abs (x,unify_term unfx v)),
                             map (unify_term unfm) (rsl1 @ rsl2 @ asl1 @ asl2 @ [s;t])) in
      (* (\x. T) c <=> T *)
      Rhythm(asl,c,rsl,
             fun unfl -> TRANS (invoke1 (unfx::unfl))
                               (conv_concl top_eta_conv
                                           (ABS (rev_itlist (fun (_,tyins,_) v -> inst tyins v) unfl x)
                                                (invoke2 (unfx::unfl))))) in

    let rinfer (Rhythm(asl1,c1,rsl1,invoke1)) (Rhythm(asl2,c2,rsl2,invoke2)) (pre,tyins,tmins) cty =
      let x = mk_var (abs_name,cty) in
      let unfm = (pre,tyins,map (fun (b,a) -> (c_mogic b,a)) tmins) in
      let unfx = (pre,tyins,map (fun (b,a) -> (c_movar b,a)) tmins) in
      let s,t = dest_eq c1 and u,v = dest_eq c2 in
      let asl,c,rsl = purify(map (unify_term unfm) (asl1 @ asl2),
                             mk_eq (mk_abs (x,unify_term unfx s),unify_term unfm v),
                             map (unify_term unfm) (rsl1 @ rsl2 @ asl1 @ asl2 @ [u;v])) in
      (* (\x. T) c <=> T *)
      Rhythm(asl,c,rsl,
             fun unfl -> TRANS (conv_concl top_eta_conv
                                           (ABS (rev_itlist (fun (_,tyins,_) v -> inst tyins v) unfl x)
                                                (invoke1 (unfx::unfl))))
                               (invoke2 (unfx::unfl))) in

    let work rth1 rth2 : rthm list =
      let rth1 = normalize_name rth1 "x" "A" and rth2 = normalize_name rth2 "y" "B" in
      let asl1,c1,_ = dest_rthm rth1 and asl2,c2,_ = dest_rthm rth2 in
      let fnames = union (vnames_of_rthm rth1) (vnames_of_rthm rth2) in
      let s,t = dest_eq c1 and u,v = dest_eq c2 in
      let asl1 = Array.of_list asl1 and asl2 = Array.of_list asl2 in
      let n = Array.length asl1 and m = Array.length asl2 in
      let pairs = map (fun x -> (x / m,x mod m)) (0--(n*m-1)) in
      let rec dfs (ps : (int * int) list) (task : (term * term) list) : unifier list =
        match ps with
          (i,j)::t -> let res = dfs t task in
                      if res = [] then []
                      else (dfs t ((Array.get asl1 i,Array.get asl2 j)::task)) @ res
        | [] -> hol_unify fnames task in
      let std = try let _ = type_unify [type_of t,type_of u] in
                    let unfs = dfs pairs [t,u] in
                    map (fun unf -> infer rth1 rth2 unf) unfs
                with Failure "type_unify" -> [] in
      let ltd = try let p,q = dest_fun_ty (type_of t) in
                    try let _ = type_unify [q,type_of u] in
                        let c = mk_const ("tmp",[p,`:A`]) in
                        let unfs = dfs pairs [mk_comb (t,c),u] in
                        map (fun ((_,tyins,_) as unf) ->
                             linfer rth1 rth2 unf (type_subst tyins p)) unfs
                    with Failure "type_unify" -> []
                with Failure "dest_fun_ty" -> [] in
      let rtd = try let p,q = dest_fun_ty (type_of u) in
                    try let _ = type_unify [q,type_of t] in
                        let c = mk_const ("tmp",[p,`:A`]) in
                        let unfs = dfs pairs [t,mk_comb (u,c)] in
                        map (fun ((_,tyins,_) as unf) ->
                             rinfer rth1 rth2 unf (type_subst tyins p)) unfs
                    with Failure "type_unify" -> []
                with Failure "dest_fun_ty" -> [] in
      std @ ltd @ rtd in

    let v1 = vnames_of_rthm rth1 and t1 = tnames_of_rthm rth1 in
    let u = variant v1 "u" and v = variant v1 "v" and t = variant t1 "U" in
    let unf1 = hol_unify v1 [(rconcl rth1),mk_eq (mk_var(u,mk_vartype(t)),mk_var(v,mk_vartype(t)))] in
    let v2 = vnames_of_rthm rth2 and t2 = tnames_of_rthm rth2 in
    let u = variant v2 "u" and v = variant v2 "v" and t = variant t2 "U" in
    let unf2 = hol_unify v2 [(rconcl rth2),mk_eq (mk_var(u,mk_vartype(t)),mk_var(v,mk_vartype(t)))] in
    flat (allpairs (fun x y -> work (rinst x rth1) (rinst y rth2)) unf1 unf2);;

end;;

include Rthm;;

let a = mk_rthm (mk_fthm ([],`z f = SUC (f 0)`));;
let b = mk_rthm (mk_fthm ([],`g (SUC 0) = z g`));;

let a = mk_rthm (mk_fthm ([],`(\x. a b) = \(x:num). (+) (a x) b`));;
let b = mk_rthm (mk_fthm ([],`(+) p p = p`));;

let a = mk_rthm (mk_fthm ([],`p = (+) p p`));;
let b = mk_rthm (mk_fthm ([],`(\(x:num). (+) (a x) b) = (\x. a b)`));;
