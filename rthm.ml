needs "script/unification.ml";;

(* optimize eta-conv after ABS *)

if not (can get_const_type "mogic") then
  new_constant("mogic",`:A`);;

if not (can get_const_type "tmp") then
  new_constant("tmp",`:A`);;

let T_TAUT = DEDUCT_ANTISYM_RULE (ASSUME `t:bool`) TRUTH;;

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
    val rrsl : rthm -> term list
    val get_rthm : rthm -> (unifier list) -> thm

    val normalize_name : rthm -> string -> string -> rthm
    val rinst : unifier -> rthm -> rthm
    val rtrans : rthm -> rthm -> rthm list
    val req_mp : rthm -> rthm -> rthm list
    val rmk_comb : rthm -> rthm -> rthm list
    val rdeduct : rthm -> rthm -> rthm list

    val gen_compare : rthm -> rthm -> int
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

  type rthm = Rhythm of (term list * term * term list * (unifier list -> thm))

  let rec is_mogical tm =
    match tm with
      Comb(f,x) -> is_mogical f || is_mogical x
    | Abs(_,bod) -> is_mogical bod
    | Const("mogic",_) -> true
    | _ -> false

  let tinker (asl,c,rsl,invoke) =
    (* asl,c,rsl might not be in beta-eta normal form
     * invoke must return a theorem in normal form
     *)
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
        failwith "tinker"
      else if is_const hsym || mem hsym env then
        itlist ((@) o (work env)) args []
      else if is_mogical bod then
        (* clean extra bound vars *)
        let bvars = clean bvars (frees bod) in
        [conv_term eta_conv (mk_term bvars bod)]
      else [] in

    let self_reduce asl c =
      (* can not self-deduced
       * For a sequent A |- a, there does not exist a unifier s, such that
       * s(a) = a, s(A) is a proper subset of A
       * TODO
       *)


    (* beta-eta normalization, deduplicate, simple work on rsl *)
    let asl = uniq (qsort (map beta_eta_term asl)) in
    let c = beta_eta_term c in

    let unf = self_reduce asl c in
    (* TODO unify *)


    let rsl = map beta_eta_term rsl in
    let rsl = uniq (qsort (itlist ((@) o (work [])) rsl [])) in

    if rsl = [] then
      let th = invoke [] in
      Rhythm(asl,c,rsl,fun unfl -> conv_thm beta_eta_conv (rev_itlist unify_thm unfl th))
    else Rhythm(asl,c,rsl,invoke)

  let mk_rthm th =
    let th = conv_thm beta_eta_conv th in
    let asl,c = dest_thm th in
    tinker(asl,c,[],fun unfl -> conv_thm beta_eta_conv (rev_itlist unify_thm unfl th))

  let dest_rthm (Rhythm(asl,c,rsl,_)) = (asl,c,rsl)

  let rhyp (Rhythm(asl,_,_,_)) = asl
  
  let rconcl (Rhythm(_,c,_,_)) = c

  let rrsl (Rhythm(_,_,rsl,_)) = rsl

  let get_rthm (Rhythm(_,_,rsl,invoke)) unfl =
    (* check whether unfl can clean "mogic" *)
    do_list (fun tm -> if is_mogical (beta_eta_term (rev_itlist unify_term unfl tm)) then
                         failwith "get_rthm"
                       else ()) rsl;
    invoke unfl

  let rinst unf (Rhythm(asl,c,rsl,invoke)) =
    try tinker(map (unify_term unf) asl,
               unify_term unf c,
               map (unify_term unf) rsl,
               fun unfl -> invoke (unf::unfl))
    with Failure "tinker" -> failwith "rinst"

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
    rinst (tmins,tyins,[]) rth

  let rec term_image f l =
    match l with
      h::t -> let h' = f h and t' = term_image f t in
              if mem h' t' then t' else h'::t'
    | [] -> []

  let rec variant avoid s =
    if not (mem s avoid) then s
    else variant avoid (s ^ "'")

  let vnames_of_rthm (Rhythm(asl,c,rsl,_)) =
    let fvars = freesl ((c::asl) @ rsl) in
    term_image (fst o dest_var) fvars

  let tnames_of_rthm (Rhythm(asl,c,rsl,_)) =
    let tvars = itlist (union o type_vars_in_term) ((c::asl) @ rsl) [] in
    map dest_vartype tvars

  let rec c_mogic tm =
    match tm with
      Comb(f,x) -> mk_comb(c_mogic f,c_mogic x)
    | Abs(bvar,bod) -> mk_abs(bvar,c_mogic bod)
    | Const("tmp",ty) -> mk_const("mogic",[ty,`:A`])
    | _ -> tm

  let rec c_movar tm =
    match tm with
      Comb(f,x) -> mk_comb(c_movar f,c_movar x)
    | Abs(bvar,bod) -> mk_abs(bvar,c_movar bod)
    | Const("tmp",ty) -> mk_var (abs_name,ty)
    | _ -> tm

  let rtrans rth1 rth2 =
    let infer (Rhythm(asl1,c1,rsl1,invoke1)) (Rhythm(asl2,c2,rsl2,invoke2)) (unf : unifier) : rthm =
      (*
      printf "-------------------\n%s\n%s\n%s\n%s\n%s\n%s\n"
             (string_of_term c1) (string_of_term c2)
             (string_of_term (unify_term unf c1))
             (string_of_term (unify_term unf c2))
             (string_of_term (concl (invoke1 [unf])))
             (string_of_term (concl (invoke2 [unf])));
      printf "%s\n" (string_of_term (concl (TRANS (invoke1 [unf]) (invoke2 [unf]))));
      *)
      try tinker((map (unify_term unf) asl1) @ (map (unify_term unf) asl2),
                 mk_eq(lhs (unify_term unf c1),rhs (unify_term unf c2)),
                 (map (unify_term unf) rsl1) @ (map (unify_term unf) rsl2),
                 fun unfl -> TRANS (invoke1 (unf::unfl)) (invoke2 (unf::unfl)))
      with Failure "tinker" -> failwith "infer" in

    let linfer (Rhythm(asl1,c1,rsl1,invoke1)) (Rhythm(asl2,c2,rsl2,invoke2)) (pre,tyins,tmins) cty =
      try let x = mk_var(abs_name,cty) in
          let unfm = (pre,tyins,map (fun (b,a) -> (c_mogic b,a)) tmins) in
          let unfx = (pre,tyins,map (fun (b,a) -> (c_movar b,a)) tmins) in
          let s,t = dest_eq c1 and u,v = dest_eq c2 in
          tinker(map (unify_term unfm) (asl1 @ asl2),
                 mk_eq(unify_term unfm s,mk_abs(x,unify_term unfx v)),
                 map (unify_term unfm) (rsl1 @ rsl2 @ asl1 @ asl2 @ [s;t]),
                 fun unfl -> TRANS (invoke1 (unfx::unfl))
                                   (conv_concl eta_conv
                                               (ABS (rev_itlist (fun (_,tyins,_) v -> inst tyins v) unfl x)
                                                    (invoke2 (unfx::unfl)))))
      with Failure "tinker" -> failwith "infer" in

    let rinfer (Rhythm(asl1,c1,rsl1,invoke1)) (Rhythm(asl2,c2,rsl2,invoke2)) (pre,tyins,tmins) cty =
      let unf = (pre,tyins,tmins) in
      try let x = mk_var(abs_name,cty) in
          let unfm = (pre,tyins,map (fun (b,a) -> (c_mogic b,a)) tmins) in
          let unfx = (pre,tyins,map (fun (b,a) -> (c_movar b,a)) tmins) in
          let s,t = dest_eq c1 and u,v = dest_eq c2 in
          tinker(map (unify_term unfm) (asl1 @ asl2),
                 mk_eq(mk_abs(x,unify_term unfx s),unify_term unfm v),
                 map (unify_term unfm) (rsl1 @ rsl2 @ asl1 @ asl2 @ [u;v]),
                 fun unfl -> TRANS (conv_concl eta_conv
                                               (ABS (rev_itlist (fun (_,tyins,_) v -> inst tyins v) unfl x)
                                                    (invoke1 (unfx::unfl))))
                                   (invoke2 (unfx::unfl)))
      with Failure "tinker" -> failwith "infer" in

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
                    safe_map (fun unf -> infer rth1 rth2 unf) "infer" unfs
                with Failure "type_unify" -> [] in
      let ltd = try let a,b = dest_fun_ty (type_of t) in
                    try let _ = type_unify [b,type_of u] in
                        let c = mk_const("tmp",[a,`:A`]) in
                        let unfs = dfs pairs [mk_comb(t,c),u] in
                        safe_map (fun ((_,tyins,_) as unf) ->
                                  linfer rth1 rth2 unf (type_subst tyins a)) "infer" unfs
                    with Failure "type_unify" -> []
                with Failure "dest_fun_ty" -> [] in
      let rtd = try let a,b = dest_fun_ty (type_of u) in
                    try let _ = type_unify [b,type_of t] in
                        let c = mk_const("tmp",[a,`:A`]) in
                        let unfs = dfs pairs [t,mk_comb(u,c)] in
                        safe_map (fun ((_,tyins,_) as unf) ->
                                  rinfer rth1 rth2 unf (type_subst tyins a)) "infer" unfs
                    with Failure "type_unify" -> []
                with Failure "dest_fun_ty" -> [] in
      std @ ltd @ rtd in

    let v1 = vnames_of_rthm rth1 and t1 = tnames_of_rthm rth1 in
    let u = variant v1 "u" and v = variant v1 "v" and t = variant t1 "U" in
    let unf1 = hol_unify v1 [(rconcl rth1),mk_eq(mk_var(u,mk_vartype(t)),mk_var(v,mk_vartype(t)))] in
    let v2 = vnames_of_rthm rth2 and t2 = tnames_of_rthm rth2 in
    let u = variant v2 "u" and v = variant v2 "v" and t = variant t2 "U" in
    let unf2 = hol_unify v2 [(rconcl rth2),mk_eq(mk_var(u,mk_vartype(t)),mk_var(v,mk_vartype(t)))] in
    let r1 = safe_map (fun unf -> rinst unf rth1) "rinst" unf1 in
    let r2 = safe_map (fun unf -> rinst unf rth2) "rinst" unf2 in
    flat (allpairs (fun x y -> work x y) r1 r2)

  let req_mp rth1 rth2 =
    let infer (Rhythm(asl1,c1,rsl1,invoke1)) (Rhythm(asl2,c2,rsl2,invoke2)) unf =
      try tinker((map (unify_term unf) asl1) @ (map (unify_term unf) asl2),
                 rhs (unify_term unf c1),
                 (map (unify_term unf) rsl1) @ (map (unify_term unf) rsl2),
                 fun unfl -> EQ_MP (invoke1 (unf::unfl)) (invoke2 (unf::unfl)))
      with Failure "tinker" -> failwith "infer" in

    let ninfer (Rhythm(asl1,c1,rsl1,invoke1)) (Rhythm(asl2,c2,rsl2,invoke2)) (pre,tyins,tmins) cty =
      (* (s = t) = p and u = v *)
      try let x = mk_var(abs_name,cty) in
          let unfm = (pre,tyins,map (fun (b,a) -> (c_mogic b,a)) tmins) in
          let unfx = (pre,tyins,map (fun (b,a) -> (c_movar b,a)) tmins) in
          let q,p = dest_eq c1 in
          let s,t = dest_eq q in
          tinker(map (unify_term unfm) (asl1 @ asl2),
                 unify_term unfm p,
                 map (unify_term unfm) (rsl1 @ rsl2 @ asl1 @ asl2 @ [s;t;p]),
                 fun unfl -> EQ_MP (invoke1 (unfx::unfl))
                                   (conv_concl eta_conv
                                               (ABS (rev_itlist (fun (_,tyins,_) v -> inst tyins v) unfl x)
                                                    (invoke2 (unfx::unfl)))))
      with Failure "tinker" -> failwith "infer" in

    let work rth1 rth2 : rthm list =
      let rth1 = normalize_name rth1 "x" "A" and rth2 = normalize_name rth2 "y" "B" in
      let asl1,c1,_ = dest_rthm rth1 and asl2,c2,_ = dest_rthm rth2 in
      let fnames = union (vnames_of_rthm rth1) (vnames_of_rthm rth2) in
      let s,t = dest_eq c1 in
      let asl1 = Array.of_list asl1 and asl2 = Array.of_list asl2 in
      let n = Array.length asl1 and m = Array.length asl2 in
      let pairs = map (fun x -> (x / m,x mod m)) (0--(n*m-1)) in
      let rec dfs (ps : (int * int) list) (task : (term * term) list) : unifier list =
        match ps with
          (i,j)::t -> let res = dfs t task in
                      if res = [] then []
                      else (dfs t ((Array.get asl1 i,Array.get asl2 j)::task)) @ res
        | [] -> hol_unify fnames task in
      try let _ = type_unify [type_of s,type_of c2] in
          let unfs = dfs pairs [s,c2] in
          safe_map (fun unf -> infer rth1 rth2 unf) "infer" unfs
      with Failure "type_unify" -> [] in

    let work' rth1 rth2 : rthm list =
      let rth1 = normalize_name rth1 "x" "A" and rth2 = normalize_name rth2 "y" "B" in
      let asl1,c1,_ = dest_rthm rth1 and asl2,c2,_ = dest_rthm rth2 in
      let fnames = union (vnames_of_rthm rth1) (vnames_of_rthm rth2) in
      let q,p = dest_eq c1 in
      let s,t = dest_eq q and u,v = dest_eq c2 in
      let asl1 = Array.of_list asl1 and asl2 = Array.of_list asl2 in
      let n = Array.length asl1 and m = Array.length asl2 in
      let pairs = map (fun x -> (x / m,x mod m)) (0--(n*m-1)) in
      let rec dfs (ps : (int * int) list) (task : (term * term) list) : unifier list =
        match ps with
          (i,j)::t -> let res = dfs t task in
                      if res = [] then []
                      else (dfs t ((Array.get asl1 i,Array.get asl2 j)::task)) @ res
        | [] -> hol_unify fnames task in
      try let a,b = dest_fun_ty (type_of s) in
          try let _ = type_unify [b,type_of u] in
              let c = mk_const("tmp",[a,`:A`]) in
              let unfs = dfs pairs [mk_comb(s,c),u;mk_comb(t,c),v] in
              safe_map (fun ((_,tyins,_) as unf) ->
                        ninfer rth1 rth2 unf (type_subst tyins a)) "infer" unfs
          with Failure "type_unify" -> []
      with Failure "dest_fun_ty" -> [] in

    let v1 = vnames_of_rthm rth1 and t1 = tnames_of_rthm rth1 in
    let v2 = vnames_of_rthm rth2 and t2 = tnames_of_rthm rth2 in
    let u = variant v1 "u" and v = variant v1 "v" and t = variant t1 "U" in
    let unfs = hol_unify v1 [(rconcl rth1),mk_eq(mk_var(u,mk_vartype(t)),
                                                        mk_var(v,mk_vartype(t)))] in
    let r1 = safe_map (fun unf -> rinst unf rth1) "rinst" unfs in
    let std = flat (map (fun x -> work x rth2) r1) in
    let u = variant v1 "u" and v = variant v1 "v" and w = variant v1 "w" and t = variant t1 "U" in
    let unf1 = hol_unify v1 [(rconcl rth1),mk_eq(mk_eq(mk_var(u,mk_vartype(t)),
                                                       mk_var(v,mk_vartype(t))),
                                                  mk_var(w,`:bool`))] in
    let u = variant v2 "u" and v = variant v2 "v" and t = variant t2 "U" in
    let unf2 = hol_unify v2 [(rconcl rth2),mk_eq(mk_var(u,mk_vartype(t)),
                                                 mk_var(v,mk_vartype(t)))] in
    let r1 = safe_map (fun unf -> rinst unf rth1) "rinst" unf1 in
    let r2 = safe_map (fun unf -> rinst unf rth2) "rinst" unf2 in
    let rtd = flat (allpairs (fun x y -> work' x y) r1 r2) in
    std @ rtd

  let rmk_comb rth1 rth2 =
    let infer (Rhythm(asl1,c1,rsl1,invoke1)) (Rhythm(asl2,c2,rsl2,invoke2)) unf =
      try tinker((map (unify_term unf) asl1) @ (map (unify_term unf) asl2),
                 mk_eq(mk_comb(lhs (unify_term unf c1),lhs (unify_term unf c2)),
                       mk_comb(rhs (unify_term unf c1),rhs (unify_term unf c2))),
                 (map (unify_term unf) rsl1) @ (map (unify_term unf) rsl2),
                 fun unfl -> conv_thm beta_eta_conv (MK_COMB(invoke1 (unf::unfl),invoke2 (unf::unfl))))
      with Failure "tinker" -> failwith "infer" in

    let work rth1 rth2 : rthm list =
      let rth1 = normalize_name rth1 "x" "A" and rth2 = normalize_name rth2 "y" "B" in
      let s = lhs (rconcl rth1) and t = lhs (rconcl rth2) in
      try let tyins = type_unify [type_of s,mk_fun_ty (type_of t) `:C`] in
          let rth1 = rinst ([],tyins,[]) rth1 and rth2 = rinst ([],tyins,[]) rth2 in
          let fnames = union (vnames_of_rthm rth1) (vnames_of_rthm rth2) in
          let asl1 = rhyp rth1 and asl2 = rhyp rth2 in
          let asl1 = Array.of_list asl1 and asl2 = Array.of_list asl2 in
          let n = Array.length asl1 and m = Array.length asl2 in
          let pairs = map (fun x -> (x / m,x mod m)) (0--(n*m-1)) in
          let rec dfs (ps : (int * int) list) (task : (term * term) list) : unifier list =
            match ps with
              (i,j)::t -> let res = dfs t task in
                          if res = [] then []
                          else (dfs t ((Array.get asl1 i,Array.get asl2 j)::task)) @ res
            | [] -> hol_unify fnames task in
          let unfs = dfs pairs [] in
          safe_map (fun unf -> infer rth1 rth2 unf) "infer" unfs
      with Failure "type_unify" -> [] in

    let v1 = vnames_of_rthm rth1 and t1 = tnames_of_rthm rth1 in
    let u = variant v1 "u" and v = variant v1 "v" and t = variant t1 "U" in
    let unf1 = hol_unify v1 [(rconcl rth1),mk_eq(mk_var(u,mk_vartype(t)),mk_var(v,mk_vartype(t)))] in
    let v2 = vnames_of_rthm rth2 and t2 = tnames_of_rthm rth2 in
    let u = variant v2 "u" and v = variant v2 "v" and t = variant t2 "U" in
    let unf2 = hol_unify v2 [(rconcl rth2),mk_eq(mk_var(u,mk_vartype(t)),mk_var(v,mk_vartype(t)))] in
    let r1 = safe_map (fun unf -> rinst unf rth1) "rinst" unf1 in
    let r2 = safe_map (fun unf -> rinst unf rth2) "rinst" unf2 in
    flat (allpairs (fun x y -> work x y) r1 r2)

  let rdeduct rth1 rth2 =
    let infer rth1 rth2 unf =
      try let (Rhythm(asl1,c1,rsl1,invoke1)) = rinst unf rth1 in
          let (Rhythm(asl2,c2,rsl2,invoke2)) = rinst unf rth2 in
          tinker(union (subtract asl1 [c2]) (subtract asl2 [c1]),
                 mk_eq(c1,c2), union rsl1 rsl2,
                 fun unfl -> conv_thm beta_eta_conv
                                      (DEDUCT_ANTISYM_RULE (invoke1 unfl) (invoke2 unfl)))
      with Failure "rinst" | Failure "tinker" -> failwith "infer" in

    let rth1 = normalize_name rth1 "x" "A" and rth2 = normalize_name rth2 "y" "B" in
    let fnames = union (vnames_of_rthm rth1) (vnames_of_rthm rth2) in
    let al1,c1,_ = dest_rthm rth1 and al2,c2,_ = dest_rthm rth2 in
    let asl1 = Array.of_list al1 and asl2 = Array.of_list al2 in
    let n = Array.length asl1 and m = Array.length asl2 in
    let pairs = map (fun x -> (x / m,x mod m)) (0--(n*m-1)) in
    let rec dfs (ps : (int * int) list) (task : (term * term) list) : unifier list =
      match ps with
        (i,j)::t -> let res = dfs t task in
                    if res = [] then []
                    else (dfs t ((Array.get asl1 i,Array.get asl2 j)::task)) @ res
      | [] -> hol_unify fnames task in
    let unfs = flat ((map (fun al -> let res = dfs pairs [al,c2] in
                                     if res = [] then []
                                     else res @ (flat (map (fun bl -> dfs pairs [al,c2;bl,c1])
                                                           al2)))
                          al1) @
                     (map (fun al -> dfs pairs [al,c1]) al2)) in
    safe_map (fun unf -> infer rth1 rth2 unf) "infer" unfs

  (* return -1 if rth1 is more general *)
  let gen_compare (Rhythm(asl1,c1,rsl1,_)) (Rhythm(asl2,c2,rsl2,_)) = 0
    (* Currently only support theorems without restrictions *)

end;;

include Rthm;;

(*
let a = mk_rthm (mk_fthm ([],`z f = SUC (f 0)`));;
let b = mk_rthm (mk_fthm ([],`g (SUC 0) = z g`));;

let a = mk_rthm (mk_fthm ([],`(\x. a b) = \(x:num). (+) (a x) b`));;
let b = mk_rthm (mk_fthm ([],`(+) p p = p`));;

let a = mk_rthm (mk_fthm ([],`p = (+) p p`));;
let b = mk_rthm (mk_fthm ([],`(\(x:num). (+) (a x) b) = (\x. a b)`));;

let a = mk_rthm (mk_fthm ([`x:bool`],`x = x`));;
let b = mk_rthm (mk_fthm ([],`a = b`));;

let a = mk_rthm (mk_fthm ([],`((a:A->B) = b) = p a b`));;
let b = mk_rthm (mk_fthm ([],`f x = f y`));;

let a = mk_rthm (mk_fthm ([],`(\x. (\x. Q) x ==> (?x. P /\ Q)) = (\x. T) <=> (!x. (\x. Q) x ==> (?x. P /\ Q))`));;
let b = mk_rthm (mk_fthm ([],`(\x. Q) x ==> (?x. P /\ Q) <=> T`));;

let a = mk_rthm (mk_fthm ([],`(\x. EVEN x \/ ODD x) = (\x. x * x < 10)`));;
let b = mk_rthm (mk_fthm ([],`11 = 13`));;

let a = mk_rthm (mk_fthm ([`a:bool`;`b:bool`],`a:bool`));;
let b = mk_rthm (mk_fthm ([`x:bool`],`x:bool`));;
*)

(*
let r0 = mk_rthm T_DEF;;
let r1 = mk_rthm (REFL `a:A`);;
let r2 = mk_rthm (REFL `a:A`);;
let r3 = mk_rthm (REFL `a:A`);;
let r4 = el 0 (rmk_comb r3 r0);;
let r5 = el 0 (rmk_comb r4 r2);;
let r6 = el 2 (req_mp r5 r2);;
let r7 = el 0 (req_mp r6 r1);;
let r8 = mk_rthm (ASSUME `a:bool`);;
let r9 = mk_rthm T_TAUT;;
let r10 = mk_rthm (ASSUME `a:bool`);;
let r11 = mk_rthm (REFL `a:A`);;
let r12 = mk_rthm (REFL `a:A`);;
let r13 = el 0 (rmk_comb r12 r10);;
let r14 = el 0 (rmk_comb r13 r11);;
let r15 = el 3 (req_mp r14 r11);;
let r16 = el 0 (req_mp r15 r7);;
let r17 = el 0 (rdeduct r16 r9);;
let r18 = mk_rthm AND_DEF;;
let r19 = mk_rthm (REFL `a:A`);;
let r20 = el 0 (rmk_comb r18 r19);;
let r24 = r20;;
let r25 = mk_rthm (REFL `a:A`);;
let r26 = el 0 (rmk_comb r24 r25);;
let r30 = r26;;
let r31 = mk_rthm (ASSUME `a:bool`);;
let r32 = el 0 (req_mp r30 r31);;
let r33 = mk_rthm (REFL `a:A`);;
let r34 = el 0 (rmk_comb r32 r33);;
let r56 = r34;;
let r57 = mk_rthm (REFL `a:A`);;
let r58 = mk_rthm (REFL `a:A`);;
let r59 = el 0 (rmk_comb r58 r56);;
let r60 = el 0 (rmk_comb r59 r57);;
let r61 = el 10 (req_mp r60 r57);;
let r62 = el 0 (req_mp r61 r7);;
let r63 = mk_rthm (ASSUME `a:bool`);;
let r64 = mk_rthm (ASSUME `a:bool`);;
let r65 = r17;;
let r66 = el 0 (req_mp r65 r64);;
let r67 = r17;;
let r68 = el 0 (req_mp r67 r63);;
let r69 = mk_rthm (REFL `a:A`);;
let r70 = el 0 (rmk_comb r69 r68);;
let r71 = el 1 (rmk_comb r70 r66);;
let r72 = r71;;
let r73 = mk_rthm (REFL `a:A`);;
let r74 = el 0 (rmk_comb r18 r73);;
let r75 = mk_rthm (REFL `a:A`);;
let r76 = el 0 (rmk_comb r74 r75);;
let r84 = r76;;
let r85 = mk_rthm (REFL `a:A`);;
let r86 = mk_rthm (REFL `a:A`);;
let r87 = el 0 (rmk_comb r86 r84);;
let r88 = el 0 (rmk_comb r87 r85);;
let r89 = el 2 (req_mp r88 r85);;
let r90 = el 1 (req_mp r89 r72);;
let r91 = el 0 (rdeduct r62 r90);;
let r92 = mk_rthm (REFL `a:A`);;
let r93 = el 0 (rmk_comb r18 r92);;
let r98 = r93;;
let r99 = mk_rthm (REFL `a:A`);;
let r100 = el 0 (rmk_comb r98 r99);;
let r105 = r100;;
let r106 = mk_rthm (ASSUME `a:bool`);;
let r107 = el 0 (req_mp r105 r106);;
let r108 = mk_rthm (REFL `a:A`);;
let r109 = el 0 (rmk_comb r107 r108);;
let r133 = r109;;
let r134 = mk_rthm (REFL `a:A`);;
let r135 = mk_rthm (REFL `a:A`);;
let r136 = el 0 (rmk_comb r135 r133);;
let r137 = el 0 (rmk_comb r136 r134);;
let r138 = el 8 (req_mp r137 r134);;
let r139 = el 0 (req_mp r138 r7);;
let r140 = mk_rthm (REFL `a:A`);;
let r141 = el 0 (rmk_comb r18 r140);;
let r146 = r141;;
let r147 = mk_rthm (REFL `a:A`);;
let r148 = el 0 (rmk_comb r146 r147);;
let r153 = r148;;
let r154 = mk_rthm (ASSUME `a:bool`);;
let r155 = el 0 (req_mp r153 r154);;
let r156 = mk_rthm (REFL `a:A`);;
let r157 = el 0 (rmk_comb r155 r156);;
let r181 = r157;;
let r182 = mk_rthm (REFL `a:A`);;
let r183 = mk_rthm (REFL `a:A`);;
let r184 = el 0 (rmk_comb r183 r181);;
let r185 = el 0 (rmk_comb r184 r182);;
let r186 = el 10 (req_mp r185 r182);;
let r187 = el 0 (req_mp r186 r7);;
let r188 = mk_rthm IMP_DEF;;
let r189 = mk_rthm (REFL `a:A`);;
let r190 = el 0 (rmk_comb r188 r189);;
let r191 = mk_rthm (REFL `a:A`);;
let r192 = el 0 (rmk_comb r190 r191);;
let r200 = r192;;
let r201 = mk_rthm (ASSUME `a:bool`);;
let r202 = mk_rthm (ASSUME `a:bool`);;
let r203 = r91;;
let r204 = el 1 (rdeduct r202 r203);;
let r205 = el 0 (req_mp r204 r202);;
let r206 = el 1 (req_mp r205 r201);;
let r207 = mk_rthm (ASSUME `a:bool`);;
let r208 = r139;;
let r209 = el 1 (rdeduct r207 r208);;
let r210 = el 0 (req_mp r209 r207);;
let r211 = el 2 (rdeduct r206 r210);;
let r212 = mk_rthm (REFL `a:A`);;
let r213 = mk_rthm (REFL `a:A`);;
let r214 = el 0 (rmk_comb r213 r200);;
let r215 = el 0 (rmk_comb r214 r212);;
*)
