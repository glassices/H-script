(*
 * Higher-order unification
 * Only output a list of most general unifiers, might not be complete
 * For some case of flex-flex, the mgu exits, and we need to extend the
 * number of these specific cased in the futhre
 *)

(*
 * First part is variable renaming. The object of this part is to make freevars
 * `x:A` and `x:B` have different name. Otherwise if we do type inst like
 * [`:A`, `:B`] we will end with `x:A` and `x:B`, which will make two different
 * freevars into the same one.
 * Second part is ordinary type instantiation
 * Third part is ordinary freevar instantiation, like [term1,var1; term2,var2]
 *)

(*
 * Greedy instantiation. Won't introduce any typevar
 *)

needs "april/kit.ml";;

type unifier =
  (term * term) list * (hol_type * hol_type) list * (term * term) list;;

let null_unf = ([],[],[] : unifier);;

let unify_term ((pre,tyins,tmins) : unifier) tm =
  vsubst tmins (inst tyins (vsubst pre tm));;

let unify_thm ((pre,tyins,tmins) : unifier) th =
  INST tmins (INST_TYPE tyins (INST pre th));;

(*
 * Constantize and variablize a term
 *)

let n_fc_limit = 50 and n_ft_limit = 30;;

for i = 0 to n_fc_limit do
  if not (can get_const_type ("_c_" ^ (string_of_int i))) then
    new_constant("_c_" ^ (string_of_int i),`:A`)
done;;

for i = 0 to n_ft_limit do
  if not (can get_type_arity ("_t_" ^ (string_of_int i))) then
    new_type("_t_" ^ (string_of_int i),0)
done;;

(* given a term list, constantize it, and output the result and the dict for
 * constants and types *)
let constantize (tml : term list) : term list * (string * string) list * (hol_type * string) list =
  let fvars = freesl tml in
  let tvars = itlist (union o type_vars_in_term) tml [] in
  if (length fvars) < n_fc_limit && (length tvars) < n_ft_limit then
    let tmins = List.mapi (fun i var -> "_c_" ^ (string_of_int i),var) fvars in
    let tyins = List.mapi (fun i var -> mk_type("_t_" ^ (string_of_int i),[]),var) tvars in

    let rec con_term env tm =
      match tm with
        Comb(f,x)  -> let f' = con_term env f and x' = con_term env x in
                      if f' == f && x' == x then tm else mk_comb(f',x')
      | Abs(y,t)   -> let y' = inst tyins y in
                      let t' = con_term (y::env) t in
                      if y' == y && t' == t then tm else mk_abs(y',t')
      | Const(_,_) -> inst tyins tm
      | Var(n,ty)  -> if mem tm env then inst tyins tm else
                      let ty' = type_subst tyins ty in
                      mk_const(rev_assoc tm tmins,[ty',`:A`]) in
                         
    (qmap (con_term []) tml,
     List.mapi (fun i var -> fst(dest_var var),"_c_" ^ (string_of_int i)) fvars,
     List.mapi (fun i tyvar -> tyvar,"_t_" ^ (string_of_int i)) tvars)
  else failwith "constantize";;

let rec varize_ty (dt : (hol_type * string) list) = let rec work ty =
    match ty with
      Tyapp(tycon,args) -> if args <> [] then
                             let args' = qmap work args in
                             if args' == args then ty else mk_type(tycon,args')
                           else if has_prefix tycon "_t_" then
                             rev_assoc tycon dt
                           else ty
    | Tyvar(_) -> ty in
  fun ty -> work ty;;

exception Conflict of term;;

let rec varize_tm (dc : (string * string) list) (dt : (hol_type * string) list) =
  (* return not only free vars but also temporary constants *)
  let rec exfrees tm =
    match tm with
      Var(_,_) -> [tm]
    | Const(c,_) -> if has_prefix c "_c_" then [tm] else []
    | Abs(bv,bod) -> subtract (exfrees bod) [bv]
    | Comb(s,t) -> union (exfrees s) (exfrees t) in

  let rec work env tm =
    match tm with
      Comb(f,x)   -> let f' = work env f and x' = work env x in
                     if f' == f && x' == x then tm else mk_comb(f',x')
    | Var(n,ty)   -> let ty' = varize_ty dt ty in
                     let tm' = if ty' == ty then tm else mk_var(n,ty') in
                     if Pervasives.compare (rev_assocd tm' env tm) tm = 0
                     then tm'
                     else raise (Conflict tm')
    | Const(c,ty) -> let ty' = varize_ty dt ty in
                     if not (has_prefix c "_c_") then
                       if ty' == ty then tm else
                       let tyins = type_match (type_of (mk_const(c,[]))) ty' [] in
                       mk_const(c,tyins)
                     else let tm' = mk_var(rev_assoc c dc,ty') in
                          if Pervasives.compare (rev_assocd tm' env tm) tm = 0
                          then tm'
                          else raise (Conflict tm')
    | Abs(y,t)    -> let y' = work [] y in
                     let env' = (y,y')::env in
                     try let t' = work env' t in
                         if y' == y && t' == t then tm else mk_abs(y',t')
                     with (Conflict(w') as ex) ->
                     if Pervasives.compare w' y' <> 0 then raise ex else
                     let ifrees = map (work []) (exfrees t) in
                     let y'' = variant ifrees y' in
                     let z = mk_var(fst(dest_var y''),snd(dest_var y)) in
                     work env (mk_abs(z,vsubst[z,y] t)) in
  fun tm -> work [] tm;;


let safe_tyins i theta =
  i::(map (fun (a,b) -> type_subst [i] a,b) theta);;

(*
 * Only variables start with x are regarded as original free variables
 *)
let safe_tmins i theta =
  let theta = map (fun (a,b) -> beta_eta_term (vsubst [i] a),b) theta in
  if String.get (fst (dest_var (snd i))) 0 = 'x' then i::theta else theta;;

(* DONE CHECKING *)
let (type_unify : (hol_type * hol_type) list -> (hol_type * hol_type) list) =
  let rec tfree_in t ty =
    if is_vartype ty then Pervasives.compare t ty = 0
    else
      exists (tfree_in t) (snd (dest_type ty)) in
  let rec unify ty1 ty2 sofar =
    let ty1 = if is_vartype ty1 then rev_assocd ty1 sofar ty1 else ty1 in
    let ty2 = if is_vartype ty2 then rev_assocd ty2 sofar ty2 else ty2 in
    let ty1,ty2 = if is_vartype ty2 then ty2,ty1 else ty1,ty2 in
    if is_vartype ty1 then
      if is_vartype ty2 then
        if Pervasives.compare ty1 ty2 = 0 then sofar
        else safe_tyins (ty2,ty1) sofar
      else
        let ty2 = type_subst sofar ty2 in
        if tfree_in ty1 ty2 then failwith "type_unify"
        else safe_tyins (ty2,ty1) sofar
    else
      let op1,args1 = dest_type ty1 and op2,args2 = dest_type ty2 in
      if op1 = op2 then itlist2 unify args1 args2 sofar
      else failwith "type_unify" in
  fun obj ->
    let obj = filter (fun (u,v) -> Pervasives.compare u v <> 0) obj in
    let obj1,obj2 = unzip obj in
    itlist2 unify obj1 obj2 [];;

let hol_unify (avoid : string list) =
  let vcounter = ref 0 in
  let run_time = ref 0 in
  let new_name is_origin =
    vcounter := !vcounter + 1;
    let prefix = if is_origin then "x" else "_" in
    while mem (prefix ^ (string_of_int !vcounter)) avoid do
      vcounter := !vcounter + 1
    done;
    prefix ^ (string_of_int !vcounter) in

  (* DONE CHECKING *)
  let rename obj =
    let fvars = itlist (fun (tm1,tm2) b -> union (union (frees tm1) (frees tm2)) b) obj [] in
    let tre = map (fun var -> (mk_var(new_name true, type_of var),var)) fvars in
    tre,pmap (vsubst tre) obj in

  (*
   * mk_term [x1;x2;x3] t = \x1 x2 x3. t
   * DONE CHECKING
   *)
  let rec mk_term bvars bod =
    match bvars with
      [] -> bod
    | h::t -> mk_abs(h,mk_term t bod) in

  (*
   * Strip off the binder \x where x does not occur in both terms
   * Then do eta-conversion to the remaining part, since bound-vars stripping
   * may generate new eta-redex
   * DONE CHECKING
   *)
  let rec bound_eta_norm (tm1,tm2) : term * term =
    match tm1,tm2 with
      Abs(bv1,bod1),Abs(bv2,bod2) ->
        let bod1,bod2 = bound_eta_norm (bod1,bod2) in
        if not (vfree_in bv1 bod1) && not (vfree_in bv2 bod2) then bod1,bod2
        else (try let f1,x1 = dest_comb bod1 in
                  if Pervasives.compare bv1 x1 = 0 && not (vfree_in bv1 f1) then f1
                  else mk_abs(bv1,bod1)
              with Failure _ -> mk_abs(bv1,bod1)),
             (try let f2,x2 = dest_comb bod2 in
                  if Pervasives.compare bv2 x2 = 0 && not (vfree_in bv2 f2) then f2
                  else mk_abs(bv2,bod2)
              with Failure _ -> mk_abs(bv2,bod2))
    | _ -> tm1,tm2 in

  (* test whether the head symbol is a free variable of a term
   * DONE CHECKING
   *)
  let head_free (tm : term) : bool =
    let bvars,tm = get_bound tm in
    let hsym = repeat rator tm in
    not (is_const hsym) && not (mem hsym bvars) in

  (* get the index of bvar, -1 if not bounded
   * find from the tail, e.g.
   * bindex x [x;x;x] = 2
   * bindex x [x;x;y] = 1
   * bindex x [x;y;y] = 0
   * bindex x [y;y;y] = -1
   * DONE CHECKING
   *)
  let bindex (var : term) (bvars : term list) : int =
    try let ret = index var (rev bvars) in
        (length bvars) - ret - 1
    with Failure "index" -> -1 in

  (* try to check rigid-rigid pairs
   * if rigid head not match then raise exception
   * else return type of pairs of const if type not match
   * DONE CHECKING
   *)
  let rec check_rr (obj : (term * term) list) : (hol_type * hol_type) list =
    match obj with
      [] -> []
    | (tm1,tm2)::t -> let bv1,(hs1,_) = decompose tm1 and bv2,(hs2,_) = decompose tm2 in
                      let bin1 = bindex hs1 bv1 and bin2 = bindex hs2 bv2 in
                      if (is_const hs1 || bin1 >= 0) && (is_const hs2 || bin2 >= 0) then
                        (* righ-rigid *)
                        if bin1 <> bin2 || is_const hs1 <> is_const hs2 then failwith "check_rr"
                        else if is_const hs1 && is_const hs2 then
                          if fst (dest_const hs1) <> fst (dest_const hs2) then failwith "check_rr"
                          else (type_of hs1,type_of hs2)::(check_rr t)
                        else check_rr t
                      else check_rr t in

  (* each pair of obj must have matched type *)
  let rec work (dep : int) (obj : (term * term) list) (tyins,tmins) sofar =
    (* check maximum depth *)
    (*
    List.iter (fun (u,v) -> Printf.printf "0\t%s\t%s\n%!" (string_of_term u) (string_of_term v)) obj;
    *)
    if dep >= 10 then sofar else (
    (* step 0: beta-eta normalization and kill extra bvars *)
    let obj = pmap beta_eta_term obj in
    let obj = map bound_eta_norm obj in
    (* step D: remove all identical pairs *)
    (*
    List.iter (fun (u,v) -> Printf.printf "1\t%s\t%s\n%!" (string_of_term u) (string_of_term v)) obj;
    print_endline "";
    *)
    let obj = filter (fun (u,v) -> alphaorder u v <> 0) obj in
    (* step O: swap all bound-free pairs *)
    let obj = map (fun (u,v) -> if is_var v || not (head_free u) && head_free v then (v,u)
                                else (u,v)) obj in
    (* step V: try to find FV-term pair *)
    try let (fv,tm),obj = pop (fun (u,v) -> is_var u && not (vfree_in u v)) obj in
        let tmins = safe_tmins (tm,fv) tmins in
        work dep (pmap (vsubst [tm,fv]) obj) (tyins,tmins) sofar
    with Failure "pop" ->
      (* step T_S: match all types of const head
       * might cause incompleteness here *)
      try let tmp_ins = type_unify (check_rr obj) in
          if length tmp_ins > 0 then
            let tyins = itlist safe_tyins tmp_ins tyins in
            let tmins = pmap (inst tmp_ins) tmins in
            work dep (pmap (inst tmp_ins) obj) (tyins,tmins) sofar else
          (* step S: match one rigid-rigid pair *)
          try let (tm1,tm2),obj = pop (fun (u,v) -> not (head_free u)) obj in
              let bv1,(hs1,args1) = decompose tm1 and bv2,(hs2,args2) = decompose tm2 in
              let bv1,bv2,args1,args2 =
                let l1 = length bv1 and l2 = length bv2 in
                if l1 = l2 then bv1,bv2,args1,args2
                else if l1 < l2 then
                  let extra = Array.to_list (Array.sub (Array.of_list bv2) l1 (l2-l1)) in
                  bv1 @ extra,bv2,args1 @ extra,args2
                else
                  let extra = Array.to_list (Array.sub (Array.of_list bv1) l2 (l1-l2)) in
                  bv1,bv2 @ extra,args1,args2 @ extra in
              let obj = itlist2 (fun u1 u2 t -> (mk_term bv1 u1,mk_term bv2 u2)::t) args1 args2 obj in
              work dep obj (tyins,tmins) sofar
          with Failure "pop" ->
            if length obj = 0 then (tyins,tmins)::sofar else
            let tm1,tm2 = try find (fun (u,v) -> not (head_free v)) obj 
                          (* In the case only flex-flex cases exist, just pick the first
                           * one and do proj-transformation. Need more heuristic method
                           * here in the future
                           * In the case of x,f x we should change the order and let it
                           * to be f x,x
                           * Let u = \x y z. bodu and v = \x y. bodv. First, bodu and bodv
                           * can't both be freevars, or it will either be solve by FV-term case
                           * or identical same.
                           * So at most one of bodu,bodv will be FV, just move the FV to the
                           * latter
                           *)
                          with Failure "find" -> let u,v = hd obj in
                                                 let _,(_,argu) = decompose u in
                                                 if length argu = 0 then v,u else u,v in
            let bv1,(hs1,args1) = decompose tm1 and bv2,(hs2,args2) = decompose tm2 in
            (* step I: imitation
             * Imitation will not consider to increase the depth of searching
             * Or the unification algorihtm cant even solve problem like
             * [`f 1234`, `1234 + 1234`]
             * TODO however some constant imitation will loop forever
             * optimize it
             *)
            let sofar =
              if is_const hs2 then
                let tyl1,apx1 = dest_fun (type_of hs1) and tyl2,apx2 = dest_fun (type_of hs2) in
                let bvars = map (fun ty -> mk_var(new_name false,ty)) tyl1 in
                let args = map (fun ty -> mk_lcomb (mk_var(new_name false,mk_fun (tyl1,ty))) bvars) tyl2 in
                let tm = mk_term bvars (mk_lcomb hs2 args) in
                let tmins' = safe_tmins (tm,hs1) tmins in
                work (dep+1) (pmap (vsubst [tm,hs1]) obj) (tyins,tmins') sofar
              else sofar in
            (* step T_P and P: projection *)
            let tyl1,apx1 = dest_fun (type_of hs1) in
            let bvars = map (fun ty -> mk_var(new_name false,ty)) tyl1 in
            let noname (k : int) sofar =
              let pvar = el k bvars in
              let tyl2,apx2 = dest_fun (type_of pvar) in
              (* unify type apx1 and apx2 *)
              try let tty = type_unify [apx1,apx2] in
                  let args = map (fun ty -> mk_lcomb (mk_var(new_name false,mk_fun (tyl1,ty))) bvars) tyl2 in
                  let tm = mk_term bvars (mk_lcomb pvar args) in
                  let t,x = inst tty tm,inst tty hs1 in
                  let tyins' = itlist safe_tyins tty tyins in
                  let tmins' = safe_tmins (t,x) (pmap (inst tty) tmins) in
                  work (dep+1) (pmap ((vsubst [t,x]) o (inst tty)) obj) (tyins',tmins') sofar
              with Failure "type_unify" -> sofar in
            itlist noname (0--((length bvars)-1)) sofar
      with Failure s when s = "check_rr" || s = "type_unify" -> sofar ) in

  (* DONE CHECKING *)
  let unify obj =
    let tre,obj = rename obj in
    let tyins = try type_unify (pmap type_of obj)
                with Failure "type_unify" -> failwith "hol_unify: Type unification failed" in
    let obj = pmap (inst tyins) obj in
    map (fun (a,b) -> tre,a,b) (work 0 obj (tyins,[]) []) in

  fun (obj : (term * term) list) ->
    let unfs = unify obj in
    if forall (fun unf ->
                 forall (fun (tm1,tm2) ->
                   alphaorder (beta_eta_term (unify_term unf tm1))
                            (beta_eta_term (unify_term unf tm2)) = 0) obj) unfs then
      unfs
    else failwith "hol_unify: produce wrong unifiers";;


let naive_match (tm1,tm2) sofar =
  let rec term_match tm1 tm2 env1 env2 ((tmins,tyins) as sofar) =
    match tm1,tm2 with
      Comb(f1,x1),Comb(f2,x2) -> let sofar = term_match f1 f2 env1 env2 sofar in
                                 term_match x1 x2 env1 env2 sofar
    | Abs(y1,t1),Abs(y2,t2) -> let tyins = type_match (type_of y1) (type_of y2) tyins in
                               term_match t1 t2 (y1::env1) (y2::env2) (tmins,tyins)
    | Const(n1,ty1),Const(n2,ty2) -> if n1 <> n2 then failwith "term_match"
                                     else tmins,type_match ty1 ty2 tyins
    | Var(_,ty1),_ -> if mem tm1 env1 then (
                         try if is_var tm2 && (index tm1 env1) = (index tm2 env2) then sofar
                             else failwith "term_match"
                         with Failure "index" -> failwith "term_match"
                       ) else if exists (fun x -> vfree_in x tm2) env2 then failwith "term_match"
                       else ( try if Pervasives.compare (rev_assoc tm1 tmins) tm2 = 0 then sofar
                                  else failwith "term_match"
                              with Failure "find" -> (tm2,tm1)::tmins,type_match ty1 (type_of tm2) tyins )
    | _ -> failwith "term_match" in
  try term_match tm1 tm2 [] [] sofar
  with Failure _ -> failwith "naive_match";;

