needs "script/rthm.ml";;

let kept = ref ([] : rthm list);;
(* T_TAUT "t | t <=> T" is the only theorem that is deduced without canceling any hyp *)
let unprocessed = ref ([mk_rthm(REFL `t:A`);mk_rthm(ASSUME `t:bool`);mk_rthm(T_TAUT);
                        mk_rthm(T_DEF);mk_rthm(AND_DEF)] : rthm list);;
let x = ref 0 and y = ref 0;;

let h1 = ref (mk_rthm(REFL `t`));;
let h2 = ref (mk_rthm(REFL `t`));;

let main n =
  let gen_test rth1 rth2 =
    (* -1 if rth1 is more general than rth2
     * +1 if rth1 is less general than rth2
     * 0 if they are excluded
     * return -1 if they are equally general
     *)
    let asl1,c1,rsl1 = dest_rthm rth1 and asl2,c2,rsl2 = dest_rthm rth2 in
    if length asl1 = length asl2 && length rsl1 = length rsl2 then
      if (forall (fun (x,y) -> alphaorder x y = 0) (zip asl1 asl2)) &&
         (forall (fun (x,y) -> alphaorder x y = 0) (zip rsl1 rsl2)) &&
         alphaorder c1 c2 = 0 then -1
      else 0
    else 0 in

  let rec work pos rth (rem : rthm list) =
    match rem with
      h::t -> let cmp = gen_test h rth in
              if cmp = -1 then rem
              else if cmp = 1 then (
                if pos < !x then x := !x-1 else ();
                if pos < !y then y := !y-1 else ();
                t @ [rth])
              else h::(work (pos+1) rth t)
    | [] -> [rth] in

  for i = 1 to n do
    Printf.printf "%d %d %d\n%!" i (length !kept) (length !unprocessed);
    while length (!unprocessed) > 0 do
      let rth = hd (!unprocessed) in
      unprocessed := tl (!unprocessed);
      kept := work 0 rth (!kept)
    done;
    let r1 = el !x (!kept) and r2 = el !y (!kept) in
    x := !x+1; if x > y then (x := 0; y := !y+1) else ();
    let l1 = (req_mp r1 r2) @ (req_mp r2 r1) in
    let l2 = (rtrans r1 r2) @ (rtrans r2 r1) in
    h1 := r1; h2 := r2;
    let l3 = (rdeduct r1 r2) @ (rdeduct r2 r1) in
    let l4 = (rmk_comb r1 r2) @ (rmk_comb r2 r1) in
    unprocessed := l1 @ l2 @ l3 @ l4
    (*
    unprocessed := (req_mp r1 r2) @ (req_mp r2 r1) @ (rtrans r1 r2) @ (rtrans r2 r1) @
                   (rdeduct r1 r2) @ (rdeduct r2 r1) @ (rmk_comb r1 r2) @ (rmk_comb r2 r1)
    *)
  done;

