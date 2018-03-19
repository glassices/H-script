needs "script/rthm.ml";;

let kept = ref ([] : rthm list);;
(* T_TAUT "t | t <=> T" is the only theorem that is deduced without canceling any hyp *)
let unprocessed = ref ([mk_rthm(REFL `t:A`);mk_rthm(ASSUME `t:bool`);mk_rthm(T_TAUT);
                        mk_rthm(T_DEF);mk_rthm(AND_DEF)] : rthm list);;
let x = ref 0 and y = ref 0;;

let h1 = ref (mk_rthm(REFL `t`));;
let h2 = ref (mk_rthm(REFL `t`));;

let main n =
  let rec work pos rth (rem : rthm list) =
    tot := !tot + 1;
    match rem with
      h::t -> if is_gen h rth then rem
              else if is_gen rth h then (
                if pos < !x then x := !x-1 else ();
                if pos < !y then y := !y-1 else ();
                work pos rth t)
              else h::(work (pos+1) rth t)
    | [] -> [rth] in

  let rec self_clean rthl =
    match rthl with
      h::t -> let l = self_clean t in
              if exists (fun x -> is_gen x h) l then l
              else h::(filter (fun x -> not (is_gen h x)) t)
    | [] -> [] in

  for i = 1 to n do
    Printf.printf "%d %d %d %d\n%!" i (length !kept) (length !unprocessed) !tot;
    while length (!unprocessed) > 0 do
      let rth = hd (!unprocessed) in
      unprocessed := tl (!unprocessed);
      kept := work 0 rth (!kept)
    done;
    let r1 = el !x (!kept) and r2 = el !y (!kept) in
    x := !x+1; if x > y then (x := 0; y := !y+1) else ();
    let l1 = (req_mp r1 r2) @ (req_mp r2 r1) in
    let l2 = (rtrans r1 r2) @ (rtrans r2 r1) in
    let l3 = (rdeduct r1 r2) @ (rdeduct r2 r1) in
    let l4 = (rmk_comb r1 r2) @ (rmk_comb r2 r1) in
    unprocessed := l1 @ l2 @ l3 @ l4;
    unprocessed := self_clean (!unprocessed)
  done;

