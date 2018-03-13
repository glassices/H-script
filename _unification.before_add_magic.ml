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

if not (can get_const_type "magic") then
  new_constant("magic",mk_vartype "MAGIC");;

type unifier =
  (term * term) list * ((hol_type * hol_type) list * (term * term) list) list;;

(*
 * DONE CHECKING
 *)
let pmap f =
  let rec pmapf l =
    match l with
      [] -> []
    | (a,b)::t -> (f a,f b)::(pmapf t) in
  pmapf;;

(*
 * DONE CHECKING
 *)
let rec pop p l =
  match l with
    [] -> failwith "pop"
  | h::t -> if p(h) then h,t
            else let x,s = pop p t in x,(h::s);;

(*
 * Input: `:A->B->C->D`
 * Output: ([`:A`; `:B`; `:C`], `:D`)
 * DONE CHECKING
 *)
let rec dest_fun ty : hol_type list * hol_type =
  try let a,b = dest_fun_ty ty in
      let tyl,apex = dest_fun b in
      (a::tyl),apex
  with Failure _ -> [],ty;;

(*
 * Input: ([`:A`; `:B`; `:C`], `:D`)
 * Output: `:A->B->C->D`
 * DONE CHECKING
 *)
let rec mk_fun (tyl,apex) : hol_type =
  match tyl with
    h::t -> mk_fun_ty h (mk_fun (t,apex))
  | [] -> apex;;

(*
 * Input: `f` [`x`; `y`]
 * Output: `f x y`
 * DONE CHECKING
 *)
let rec mk_lcomb (f : term) (args : term list) : term =
  match args with
    h::t -> mk_lcomb (mk_comb (f,h)) t
  | [] -> f;;

let (beta_eta_conv : conv) = (TOP_DEPTH_CONV BETA_CONV) THENC (TOP_DEPTH_CONV ETA_CONV);;

(* DONE CHECKING *)
let (beta_eta_term : term -> term) = rand o concl o beta_eta_conv;;

(* DONE CHECKING *)
let safe_tyins i theta =
  i::(map (fun (a,b) -> type_subst [i] a,b) theta);;

(* DONE CHECKING
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

let (hol_unify : (term * term) list -> unifier) =
  let vcounter = ref 0 in
  let new_var () = (vcounter := !vcounter + 1;
                    "_" ^ (string_of_int !vcounter)) in

  (* DONE CHECKING *)
  let rename obj =
    let fvars = itlist (fun (tm1,tm2) b -> union (union (frees tm1) (frees tm2)) b) obj [] in
    let tre = List.mapi (fun i var -> (mk_var ("x" ^ (string_of_int (i+1)), type_of var),var)) fvars in
    tre,pmap (vsubst tre) obj in

  (* get bound variables and remain term
   * Input: `\x y z. f x y z`
   * Output: ([`x`; `y`; `z`], `f x y z`)
   * DONE CHECKING
   *)
  let rec get_bound (tm : term) : term list * term =
    match tm with
      Abs(bvar,bod) -> let tml,tm' = get_bound bod in (bvar::tml),tm'
    | _ -> [],tm in

  (*
   * mk_term [x1;x2;x3] t = \x1 x2 x3. t
   * DONE CHECKING
   *)
  let rec mk_term bvars bod =
    match bvars with
      [] -> bod
    | h::t -> mk_abs (h,mk_term t bod) in

  (*
   * Strip off the binder \x where x does not occur in both terms
   * Then do eta-conversion to the remaining part, since bound-vars stripping
   * may generate new eta-redex
   * DONE CHECKING
   *)
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
    | _ -> tm1,tm2 in

  (* decompose a beta-eta normal term into bound_vars,(head symbol,args)
   * DONE CHECKING
   *)
  let decompose (tm : term) : term list * (term * term list) =
    let bvars,ctm = get_bound tm in
    bvars,strip_comb ctm in

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
    with Failure _ -> -1 in

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
    List.iter (fun (u,v) -> Printf.printf "0\t%s\t%s\n%!" (string_of_term u) (string_of_term v)) obj;
    if dep >= 5 then sofar else
    (* step 0: beta-eta normalization and kill extra bvars *)
    let obj = pmap beta_eta_term obj in
    let obj = map bound_eta_norm obj in
    (* step D: remove all identical pairs *)
    List.iter (fun (u,v) -> Printf.printf "1\t%s\t%s\n%!" (string_of_term u) (string_of_term v)) obj;
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
                          with Failure _ -> let u,v = hd obj in
                                            let _,(_,argu) = decompose u in
                                            if length argu = 0 then v,u else u,v in
            let bv1,(hs1,args1) = decompose tm1 and bv2,(hs2,args2) = decompose tm2 in
            (* step I: imitation
             * Imitation will not consider to increase the depth of searching
             * Or the unification algorihtm cant even solve problem like
             * [`f 1234`, `1234 + 1234`]
             *)
            let sofar =
              if is_const hs2 then
                let tyl1,apx1 = dest_fun (type_of hs1) and tyl2,apx2 = dest_fun (type_of hs2) in
                let bvars = map (fun ty -> mk_var (new_var(),ty)) tyl1 in
                let args = map (fun ty -> mk_lcomb (mk_var (new_var(),mk_fun (tyl1,ty))) bvars) tyl2 in
                let tm = mk_term bvars (mk_lcomb hs2 args) in
                let tmins' = safe_tmins (tm,hs1) tmins in
                work dep (pmap (vsubst [tm,hs1]) obj) (tyins,tmins') sofar
              else sofar in
            (* step T_P and P: projection *)
            let tyl1,apx1 = dest_fun (type_of hs1) in
            let bvars = map (fun ty -> mk_var (new_var(),ty)) tyl1 in
            let noname (k : int) sofar =
              let pvar = el k bvars in
              let tyl2,apx2 = dest_fun (type_of pvar) in
              (* unify type apx1 and apx2 *)
              try let tty = type_unify [apx1,apx2] in
                  let args = map (fun ty -> mk_lcomb (mk_var (new_var(),mk_fun (tyl1,ty))) bvars) tyl2 in
                  let tm = mk_term bvars (mk_lcomb pvar args) in
                  let t,x = inst tty tm,inst tty hs1 in
                  let tyins' = itlist safe_tyins tty tyins in
                  let tmins' = safe_tmins (t,x) (pmap (inst tty) tmins) in
                  work (dep+1) (pmap ((vsubst [t,x]) o (inst tty)) obj) (tyins',tmins') sofar
              with Failure "type_unify" -> sofar in
            itlist noname (0--((length bvars)-1)) sofar
      with Failure s when s = "check_rr" || s = "type_unify" -> sofar in

  (* DONE CHECKING *)
  fun (obj : (term * term) list) ->
    let tre,obj = rename obj in
    let tyins = try type_unify (pmap type_of obj)
                with Failure _ -> failwith "hol_unify: Type unification failed" in
    let obj = pmap (inst tyins) obj in
    tre,work 0 obj (tyins,[]) [];;

(*
 * normalize the name of freevars and typevars in a theorem
 * all freevars will be renamed to be vpre{#n}
 * all tyvars will be renamed to be tpre{#n}
 *)
let normalize_name thm vpre tpre =
  let asl,c = dest_thm thm in
  let fv = freesl (c::asl) and tv = itlist (union o type_vars_in_term) (c::asl) [] in
  (* rename vars first then tyvars, since renaming tyvars will make vars unmatched *)
  let tmins = List.mapi (fun i var -> (mk_var (vpre ^ (string_of_int (i+1)),type_of var),var)) fv in
  let tyins = List.mapi (fun i ty -> (mk_vartype (tpre ^ (string_of_int (i+1))),ty)) tv in
  INST_TYPE tyins (INST tmins thm);;

(* Only conv the concl of a theorem *)
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

let substantiate (pre,(tyins,tmins)) th =
  INST tmins (INST_TYPE tyins (INST pre th));;

(*
 * Generalized EQ_MP inference rule
 *)
let (gen_eq_mp : thm -> thm -> thm list) =
  let infer th1 th2 (pre,insl : unifier) : thm list =
    map (fun ins -> EQ_MP (conv_thm beta_eta_conv (substantiate (pre,ins) th1))
                          (conv_thm beta_eta_conv (substantiate (pre,ins) th2))) insl in

  let work th1 th2 : thm list =
    let th1 = conv_thm beta_eta_conv th1 and th2 = conv_thm beta_eta_conv th2 in
    let th1 = normalize_name th1 "x" "A" and th2 = normalize_name th2 "y" "B" in 
    let u,v = dest_eq (concl th1) and p = concl th2 in
    let asl1 = Array.of_list (hyp th1) and asl2 = Array.of_list (hyp th2) in
    let n = Array.length asl1 and m = Array.length asl2 in
    let pairs = map (fun x -> (x / m,x mod m)) (0--(n*m-1)) in
    let rec dfs (ps : (int * int) list) (task : (term * term) list) : unifier list =
      match ps with
        (i,j)::t -> let res = dfs t task in
                    if res = [] then []
                    else (dfs t ((Array.get asl1 i,Array.get asl2 j)::task)) @ res
      | [] -> [hol_unify task] in
    let unfs = dfs pairs [u,p] in
    flat (map (fun unf -> infer th1 th2 unf) unfs) in

  fun th1 th2 ->
    (* step 1: unify (concl th1) and (=) (u:U) (v:U)
     * Rename th1 in case that th1 contains varible u or v
     *)
    let th1 = normalize_name th1 "x" "A" in
    let pre,insl = hol_unify [snd (dest_thm th1),`(u:U) = (v:U)`] in
    flat (map (fun ins -> work (substantiate (pre,ins) th1) th2) insl);;

