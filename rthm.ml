if not (can get_const_type "mogic") then
  new_constant("mogic",aty);;

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


let fnames_of_thm (th : thm) =
  let rec term_image f l =
    match l with
      h::t -> let h' = f h and t' = term_image f t in
              if mem h' t' then t' else h'::t'
    | [] -> [] in
  let asl,c = dest_thm th in
  let fvars = freesl (c::asl) in
  term_image (fst o dest_var) fvars;;

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

end;;

module Rthm : Rthm_kernel = struct

  (*
   * Philosopy of Rthm
   * 1: Any term in a rthm MUST be beta-eta normal form
   * 2: Different variables MUST have different names
   * 3: For any theta related to inst or inst_type, dom(theta) MUST be disjoint to codom(theta)
   * 4: dom(tyins) and dom(tmins) must be in FV(asl,c) and codom(tmins) must be out of FV(asl,c)
   * 5*: sigma function is private and can not be called from the outside
   * TODO: modify unification.ml according to these three rules
   *)
  type rthm = Rhythm of (term list * term * term list * (unifier -> thm))

  let is_valid ((tyins,tmins) : unifier) : bool =
    true

  let mk_rthm th =
    let th = conv_thm beta_eta_conv th in
    let th = varyname_thm th in
    let asl,c = dest_thm th in
    Rhythm(asl,c,[],fun (x : unifier) -> th)

  let dest_rthm (Rhythm(asl,c,rsl,sigma)) = (asl,c,rsl)

end;;

include Rthm;;





(*
 * Generalized EQ_MP inference rule
 *)

let (gen_eq_mp : thm -> thm -> thm list) =
  let infer th1 th2 (sdf : solidifier) : thm =
    EQ_MP (conv_thm beta_eta_conv (solidify_thm sdf th1))
          (conv_thm beta_eta_conv (solidify_thm sdf th2)) in

  let work th1 th2 : thm list =
    let th1 = conv_thm beta_eta_conv th1 and th2 = conv_thm beta_eta_conv th2 in
    let th1 = normalize_name th1 "x" "A" and th2 = normalize_name th2 "y" "B" in 
    let fnames = union (fnames_of_thm th1) (fnames_of_thm th2) in
    let u,v = dest_eq (concl th1) and p = concl th2 in
    let asl1 = Array.of_list (hyp th1) and asl2 = Array.of_list (hyp th2) in
    let n = Array.length asl1 and m = Array.length asl2 in
    let pairs = map (fun x -> (x / m,x mod m)) (0--(n*m-1)) in
    let rec dfs (ps : (int * int) list) (task : (term * term) list) : solidifier list =
      match ps with
        (i,j)::t -> let res = dfs t task in
                    if res = [] then []
                    else (dfs t ((Array.get asl1 i,Array.get asl2 j)::task)) @ res
      | [] -> hol_unify fnames task in
    let sdfs = dfs pairs [u,p] in
    map (fun sdf -> infer th1 th2 sdf) sdfs in

  fun th1 th2 ->
    (* step 1: unify (concl th1) and (=) (u:U) (v:U)
     * Rename th1 in case that th1 contains varible u or v
     *)
    let th1 = normalize_name th1 "x" "A" in
    let sdfs = hol_unify (fnames_of_thm th1) [snd (dest_thm th1),`(u:U) = (v:U)`] in
    flat (map (fun sdf -> work (solidify_thm sdf th1) th2) sdfs);;
