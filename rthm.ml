needs "april/unification.ml";;

(* optimize eta-conv after ABS *)

if not (can get_const_type "mogic") then
  new_constant("mogic",`:A`);;

if not (can get_const_type "tmp") then
  new_constant("tmp",`:A`);;

let T_TAUT = DEDUCT_ANTISYM_RULE (ASSUME `t:bool`) TRUTH;;

let abs_name = "xdq";;
let tot = ref 0;;

let hunfs = ref ([] : unifier list);;

let term_uniq = List.sort_uniq alphaorder;;

let rec term_merge l1 l2 =
  match (l1,l2) with
    ([],l2) -> l2
  | (l1,[]) -> l1
  | (h1::t1,h2::t2) -> let c = alphaorder h1 h2 in
                       if c = 0 then h1::(term_merge t1 t2)
                       else if c < 0 then h1::(term_merge t1 l2)
                       else h2::(term_merge l1 t2);;

let rec term_remove t l =
  match l with
    s::ss -> let c = alphaorder t s in
             if c > 0 then
               let ss' = term_remove t ss in
               if ss' == ss then l else s::ss'
             else if c = 0 then ss else l
  | [] -> l;;

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

    val is_gen : rthm -> rthm -> bool
    val simplify : rthm -> rthm -> rthm

    val hrthm1 : unit -> rthm
    val hrthm2 : unit -> rthm
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
       *)
      let n = length asl in
      if n = 0 then null_unf else
      let tml,dc,dt = constantize (c::asl) in
      let c' = hd tml and asl' = Array.of_list (tl tml) and asl = Array.of_list asl in
      let best = ref n and unf = ref null_unf in
      let rec dfs t uset pairs =
        if length uset >= !best then () else
          if t = n then (
            let unfs = hol_unify [] pairs in
            if unfs <> [] then (
              best := length uset;
              unf := hd unfs
            ) else ()
          ) else (
            for i = 0 to n-1 do
              dfs (t+1) (if mem i uset then uset else (i::uset))
                  ((Array.get asl t,Array.get asl' i)::pairs)
            done
          ) in
      ( dfs 0 [] [c,c'];
        let pre,tyins,tmins = !unf in
        pmap (varize_tm dc dt) pre,pmap (varize_ty dt) tyins,pmap (varize_tm dc dt) tmins) in

    (* beta-eta normalization, deduplicate, simple work on rsl *)
    let asl = term_uniq (map beta_eta_term asl) in
    let c = beta_eta_term c in
    let unf = self_reduce asl c in
    let asl,c,rsl = if unf = null_unf then asl,c,rsl
                    else term_uniq (map (beta_eta_term o (unify_term unf)) asl),
                         beta_eta_term (unify_term unf c),
                         map (unify_term unf) rsl in
    let rsl = map beta_eta_term rsl in
    let rsl = term_uniq (itlist ((@) o (work [])) rsl []) in

    if unf = null_unf then 
      if rsl = [] then
        let th = invoke [] in
        if length (hyp th) > length asl then failwith "tinker: fatal";
        Rhythm(asl,c,rsl,fun unfl -> conv_thm beta_eta_conv (rev_itlist unify_thm unfl th))
      else Rhythm(asl,c,rsl,invoke)
    else
      if rsl = [] then
        let th = invoke [unf] in
        if length (hyp th) > length asl then failwith "tinker: fatal";
        Rhythm(asl,c,rsl,fun unfl -> conv_thm beta_eta_conv (rev_itlist unify_thm unfl th))
      else Rhythm(asl,c,rsl,fun unfl -> invoke (unf::unfl))

  let mk_rthm th =
    let th = conv_thm beta_eta_conv th in
    let asl,c = dest_thm th in
    tinker(asl,c,[],fun unfl -> conv_thm beta_eta_conv (rev_itlist unify_thm unfl th))

  let hh1 = ref (mk_rthm(REFL `t`))
  let hh2 = ref (mk_rthm(REFL `t`))
  let hrthm1() = !hh1
  let hrthm2() = !hh2

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
      hh1 := rth1; hh2 := rth2;
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
      try let _ = type_unify [type_of s,`:bool`] in
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
          tinker(term_merge (term_remove c2 asl1) (term_remove c1 asl2),
                 mk_eq(c1,c2), term_merge rsl1 rsl2,
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

  let is_gen (Rhythm(asl1,c1,rsl1,_)) (Rhythm(asl2,c2,_,_)) =
    (* Currently only support theorems without restrictions *)
    if rsl1 <> [] then false else
    let n = length asl1 and m = length asl2 in
    if n > 0 && m = 0 then false else
    let asl1 = Array.of_list asl1 and asl2 = Array.of_list asl2 in
    let rec dfs t i sofar =
      if t = n then true
      else if i = m then false
      else try let sofar' = naive_match (Array.get asl1 t,Array.get asl2 i) sofar in
               if dfs (t+1) 0 sofar' then true
               else dfs t (i+1) sofar
           with Failure "naive_match" -> dfs t (i+1) sofar in
    try dfs 0 0 (naive_match (c1,c2) ([],[]))
    with Failure "naive_match" -> false

  let simplify rth1 rth2 =
    let rec work rth1 rth2 pos =
      if pos < 0 then rth2 else
      let asl1,c1,_ = dest_rthm rth1 and asl2,c2,_ = dest_rthm rth2 in
      if (length asl1) > 0 && (length asl2) <= 1 then rth2 else
      let csl,dc,dt = constantize asl2 in
      let c = el pos csl in
      let asl1 = Array.of_list asl1 and asl2 = Array.of_list (rm pos csl) in
      let n = Array.length asl1 and m = Array.length asl2 in
      let rec dfs t i pairs =
        if t = n then let ret = hol_unify [] pairs in
                      if ret <> [] then hd ret else null_unf
        else if i = m then null_unf
        else let ret = dfs (t+1) 0 ((Array.get asl1 t,Array.get asl2 i)::pairs) in
             if ret <> null_unf then ret
             else dfs t (i+1) pairs in
      let unf = dfs 0 0 [c1,c] in
      if unf = null_unf then work rth1 rth2 (pos-1) else
      let pre,tyins,tmins = unf in
      let pre,tyins,tmins = pmap (varize_tm dc dt) pre,pmap (varize_ty dt) tyins,pmap (varize_tm dc dt) tmins in
      let Rhythm(asl1,c1,rsl1,invoke1) = rinst (pre,tyins,tmins) rth1 and Rhythm(asl2,c2,rsl2,invoke2) = rth2 in
      let rth2 = tinker(term_remove c1 asl2,
                        c2,term_merge rsl1 rsl2,
                        fun unfl -> let r1 = invoke1 unfl in
                                    EQ_MP (DEDUCT_ANTISYM_RULE r1 (invoke2 unfl)) r1) in
      work rth1 rth2 (pos-1) in
    work rth1 rth2 ((length (rhyp rth2))-1)

end;;

include Rthm;;

(*
let a = mk_rthm (mk_fthm([`a:bool`;`b:bool`;`a /\ b`],`a \/ b`));;
let b = mk_rthm (mk_fthm([`a:bool`;`b:bool`],`a /\ b`));;
*)

(*
let a = mk_rthm (mk_fthm([`a:bool`;`b:bool`],`a:bool`));;
let b = mk_rthm (mk_fthm([`a:bool`;`a==>b`;`c:bool`;`c==>b`;`d:bool`],`b:bool`));;
let c = mk_rthm (mk_fthm([`(\(y:bool).y) = Q`;`(P:bool->bool) = Q`],`(P:bool->bool) (x:bool)`));;
*)

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


let t_def = mk_rthm(T_DEF);;
let and_def = mk_rthm(AND_DEF);;
let t_taut = mk_rthm(T_TAUT);;
let refl = mk_rthm(REFL `a:A`);;
let assume = mk_rthm(ASSUME `a:bool`);;
let r4 = el 0 (rmk_comb refl t_def);;
let r5 = el 0 (rmk_comb r4 refl);;
let r6 = el 2 (req_mp r5 refl);;
let r7 = el 0 (req_mp r6 refl);;
let r13 = el 0 (rmk_comb refl assume);;
let r14 = el 0 (rmk_comb r13 refl);;
let r15 = el 3 (req_mp r14 refl);;
let r16 = el 0 (req_mp r15 r7);;
let r17 = el 0 (rdeduct r16 t_taut);;
let r66 = el 0 (req_mp r17 assume);;
let r70 = el 0 (rmk_comb refl r66);;
let r71 = el 1 (rmk_comb r70 r66);;
let r74 = el 0 (rmk_comb and_def refl);;
let r76 = el 0 (rmk_comb r74 refl);;
let r87 = el 0 (rmk_comb refl r76);;
let r88 = el 0 (rmk_comb r87 refl);;
let r89 = el 2 (req_mp r88 refl);;
let r90 = el 1 (req_mp r89 r71);;
