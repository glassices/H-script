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

type unifier =
  (term * term) list * ((hol_type * hol_type) list * (term * term) list) list;;

let pmap f =
  let rec pmapf l =
    match l with
      [] -> []
    | (a,b)::t -> (f a,f b)::(pmapf t) in
  pmapf;;

let rec pop p l =
  match l with
    [] -> failwith "pop: no proper element"
  | h::t -> if p(h) then h,t
            else let x,s = pop p t in x,(h::s);;

let rec dest_fun ty : hol_type list * hol_type =
  try let a,b = dest_fun_ty ty in
      let tyl,apex = dest_fun b in
      (a::tyl),apex
  with Failure _ -> [],ty;;

let rec mk_fun tyl apex : hol_type =
  match tyl with
    h::t -> mk_fun_ty h (mk_fun t apex)
  | [] -> apex;;

let rec mk_lcomb (f : term) (args : term list) : term =
  match args with
    h::t -> mk_lcomb (mk_comb (f,h)) t
  | [] -> f;;

let beta_eta_norm = rand o concl o ((TOP_DEPTH_CONV BETA_CONV) THENC (TOP_DEPTH_CONV ETA_CONV));;

let safe_tyins i theta =
  let a,b = unzip theta in
  i::(zip (map (type_subst [i]) a) b);;

let safe_tmins i theta =
  let a,b = unzip theta in
  i::(zip (map (beta_eta_norm o (vsubst [i])) a) b);;

let (type_unify : (hol_type * hol_type) list -> (hol_type * hol_type) list) =
  let rec tfree_in t ty =
    if is_vartype ty then Pervasives.compare t ty = 0
    else
      exists (tfree_in t) (snd (dest_type ty)) in
  let rec unify ty1 ty2 sofar =
    let ty1' = if is_vartype ty1 then rev_assocd ty1 sofar ty1 else ty1 in
    let ty2' = if is_vartype ty2 then rev_assocd ty2 sofar ty2 else ty2 in
    let ty1 = if is_vartype ty2' then ty2' else ty1' in
    let ty2 = if is_vartype ty2' then ty1' else ty2' in
    if is_vartype ty1 then
      if is_vartype ty2 then
        if Pervasives.compare ty1 ty2 = 0 then sofar
        else safe_tyins (ty2,ty1) sofar
      else
        if tfree_in ty1 ty2 then failwith "unify"
        else safe_tyins (ty2,ty1) sofar
    else
      let op1,args1 = dest_type ty1 and op2,args2 = dest_type ty2 in
      if op1 = op2 then itlist2 unify args1 args2 sofar
      else failwith "unify" in
  fun obj ->
    let obj = filter (fun (u,v) -> Pervasives.compare u v <> 0) obj in
    let obj1,obj2 = unzip obj in
    itlist2 unify obj1 obj2 [];;

let hol_unify =
  let vcounter = ref 0 in
  let new_var () = (vcounter := !vcounter + 1;
                    "_v" ^ (string_of_int !vcounter)) in
  let rename obj =
    let fvars = itlist (fun (tm1,tm2) b -> union (union (frees tm1) (frees tm2)) b) obj [] in
    let tre = map (fun var -> (mk_var (new_var(), type_of var),var)) fvars in
    tre,pmap (vsubst tre) obj in

  (* get bound variables and remain term *)
  let rec get_bound (tm : term) : term list * term =
    match tm with
      Abs(bvar,bod) -> let tml,tm' = get_bound bod in (bvar::tml),tm'
    | _ -> [],tm in

  (*
   * mk_term [x1;x2;x3] t = \x1 x2 x3. t
   *)
  let rec mk_term bvars bod =
    match bvars with
      [] -> bod
    | h::t -> mk_abs (h,mk_term t bod) in

  (*
   * rev_mk_term [x1;x2;x3] t = \x3 x2 x1. t
   *)
  let rec rev_mk_term bvars bod =
    match bvars with
      [] -> bod
    | h::t -> rev_mk_term t (mk_abs (h,bod)) in

  (*
   * Strip off the binder \x where x does not occur in both terms
   * Then do eta-conversion to the remaining part, since bound-vars stripping
   * may generate new eta-redex
   *)
  let bound_eta_norm: term * term -> term * term =
    let rec reduce bv1 bv2 bod1 bod2 =
      match (bv1,bv2) with
        (h1::t1,h2::t2) -> if not (vfree_in h1 bod1) && not (vfree_in h2 bod2) then
                             reduce t1 t2 bod1 bod2
                           else (
                             try let f1,x1 = dest_comb bod1 and f2,x2 = dest_comb bod2 in
                                 if Pervasives.compare h1 x1 = 0 && Pervasives.compare h2 x2 = 0 &&
                                    not (vfree_in h1 f1) && not (vfree_in h2 f2) then
                                   reduce t1 t2 f1 f2
                                 else bv1,bv2,bod1,bod2
                             with Failure _ -> bv1,bv2,bod1,bod2 )
      | _ -> bv1,bv2,bod1,bod2 in
    fun (tm1,tm2) ->
      let bv1,bod1 = get_bound tm1 and bv2,bod2 = get_bound tm2 in
      if length bv1 = length bv2 then
        let bv1,bv2,bod1,bod2 = reduce bv1 bv2 bod1 bod2 in
        rev_mk_term bv1 bod1,rev_mk_term bv2 bod2
      else rev_mk_term bv1 bod1,rev_mk_term bv2 bod2 in

  (* decompose a beta-eta normal term into bound_vars,(head symbol,args) *)
  let decompose (tm : term) : term list * (term * term list) =
    let bvars,ctm = get_bound tm in
    bvars,strip_comb ctm in

  (* test whether the head symbol is a free variable of a term *)
  let head_free (tm : term) : bool =
    let bvars,tm = get_bound tm in
    let hsym = repeat rator tm in
    not (is_const hsym) && not (mem hsym bvars) in

  (* get the index of bvar, -1 if not bounded *)
  let bindex (var : term) (bvars : term list) : int =
    try let ret = index var bvars in
        (length bvars) - ret - 1
    with Failure _ -> -1 in

  (* try to check rigid-rigid pairs
   * if rigid head not match then raise exception
   * else return type of pairs of const if type not match
   *)
  let rec check_rr (obj : (term * term) list) : (hol_type * hol_type) list =
    match obj with
      [] -> []
    | (tm1,tm2)::t -> let bv1,(hs1,args1) = decompose tm1 and bv2,(hs2,args2) = decompose tm2 in
                      let bin1 = bindex hs1 bv1 and bin2 = bindex hs2 bv2 in
                      if bin1 <> bin2 || is_const hs1 <> is_const hs2 then failwith "check_rr"
                      else if is_const hs1 && is_const hs2 then
                        if fst (dest_const hs1) <> fst (dest_const hs2) then failwith "check_rr"
                        else (type_of hs1,type_of hs2)::(check_rr t)
                      else check_rr t in

  (* each pair of obj must have matched type *)
  let rec work (obj : (term * term) list) (tyins,tmins) sofar =
    (* step 0: beta-eta normalization and kill extra bvars *)
    let obj = pmap beta_eta_norm obj in
    let obj = map bound_eta_norm obj in
    (* step D: remove all identical pairs *)
    let obj = filter (fun (u,v) -> alphaorder u v = 0) obj in
    (* step O: swap all bound-free pairs *)
    let obj = map (fun (u,v) -> if is_var v || not (head_free u) && head_free v then (v,u)
                                else (u,v)) obj in
    (* step V: try to find FV-term pair *)
    try let (fv,tm),obj = pop (fun (u,v) -> is_var u && not (vfree_in u v)) obj in
        let tmins = safe_tmins (tm,fv) tmins in
        work (pmap (vsubst [tm,fv]) obj) (tyins,tmins) sofar
    with Failure _ ->
      (* step T_S: match all types of const head
       * might cause incompleteness here *)
      try let tmp_ins = type_unify (check_rr obj) in
        if length tmp_ins > 0 then
          let tyins = itlist safe_tyins tmp_ins tyins in
          let tmins = pmap (inst tmp_ins) tmins in
          work (pmap (inst tmp_ins) obj) (tyins,tmins) sofar else
        (* step S: match one rigid-rigid pair *)
        try let (tm1,tm2),obj = pop (fun (u,v) -> not (head_free u)) obj in
            let bv1,(hs1,args1) = decompose tm1 and bv2,(hs2,args2) = decompose tm2 in
            let bv1,bv2,args1,args2 =
              let l1 = length bv1 and l2 = length bv2 in
              if l1 = l2 then bv1,bv2,args1,args2
              else if l1 < l2 then
                let extra = Array.to_list (Array.sub (Array.of_list (rev bv2)) l1 (l2-l1)) in
                (rev extra) @ bv1,args1 @ extra,bv2,args2
              else
                let extra = Array.to_list (Array.sub (Array.of_list (rev bv1)) l2 (l1-l2)) in
                bv1,args1,(rev extra) @ bv2,args2 @ extra in
            let obj = itlist2 (fun u1 -> fun u2 -> fun t -> (rev_mk_term bv1 u1,rev_mk_term bv2 u2)::t) args1 args2 obj in
            work obj (tyins,tmins) sofar
        with Failure _ ->
          try let tm1,tm2 = find (fun (u,v) -> not (head_free v)) obj in
              let bv1,(hs1,args1) = decompose tm1 and bv2,(hs2,args2) = decompose tm2 in
              (* step I: imitation *)
              let sofar =
                if is_const hs2 then
                  let tyl1,apx1 = dest_fun (type_of hs1) and tyl2,apx2 = dest_fun (type_of hs2) in
                  let bvars = map (fun ty -> mk_var (new_var(),ty)) tyl1 in
                  let args = map (fun ty -> mk_lcomb (mk_var (new_var(),mk_fun tyl1 ty)) bvars) tyl2 in
                  let tm = mk_term bvars (mk_lcomb hs2 args) in
                  let tmins' = safe_tmins (tm,hs1) tmins in
                  work (pmap (vsubst [tm,hs1]) obj) (tyins,tmins') sofar
                else sofar in
              (* step T_P and P: projection *)
              let tyl1,apx1 = dest_fun (type_of hs1) in
              let bvars = map (fun ty -> mk_var (new_var(),ty)) tyl1 in
              let noname (k : int) sofar =
                let pvar = el k bvars in
                let tyl2,apx2 = dest_fun (type_of pvar) in
                (* unify type apx1 and apx2 *)
                try let tty = type_unify [apx1,apx2] in
                    let args = map (fun ty -> mk_lcomb (mk_var (new_var(),mk_fun tyl1 ty)) bvars) tyl2 in
                    let tm = mk_term bvars (mk_lcomb pvar args) in
                    let t,x = inst tty tm,inst tty hs1 in
                    let tyins' = itlist safe_tyins tty tyins in
                    let tmins' = pmap ((vsubst [t,x]) o (inst tty)) tmins in
                    work (pmap ((vsubst [t,x]) o (inst tty)) obj) (tyins',tmins') sofar
                with Failure _ -> sofar in
              itlist noname (0--((length bvars)-1)) sofar
          with Failure _ ->
            (* Everything is flex-flex *)
            if length obj = 0 then (tyins,tmins)::sofar else sofar
      with Failure _ -> sofar in

  fun (obj : (term * term) list) ->
    let tre,obj = rename obj in
    let tyins = try type_unify (pmap type_of obj)
                with Failure _ -> failwith "hol_unify: Type unification failed" in
    let obj = pmap (inst tyins) obj in
    work obj ([],[]) [];;
