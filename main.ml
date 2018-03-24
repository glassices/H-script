needs "april/rthm.ml";;

module Rthm = struct
  type t = rthm
  let compare th0 th1 =
    Pervasives.compare (dest_rthm th0) (dest_rthm th1);;
end;;

module Dict_rthm = Map.Make(Rthm);;

let kept = ref ([] : rthm list);;
(* T_TAUT "t | t <=> T" is the only theorem that is deduced without canceling any hyp *)
let unprocessed = ref ([] : rthm list);;
let x = ref 0 and y = ref 0 and k = ref 0;;

let h1 = ref (mk_rthm(REFL `t`));;
let h2 = ref (mk_rthm(REFL `t`));;

let mm = ref Dict_rthm.empty;;
let baba = ref ([] : rthm list);;

let rthm_size rth =
  itlist (fun x y -> (tm_size x) + y) (rhyp rth) (tm_size (rconcl rth));;

let part_sort l s t cmp =
  let arr = Array.of_list l in
  let p1 = Array.sub arr 0 s in
  let p2 = Array.sub arr s (t-s) in
  let p3 = Array.sub arr t ((length l)-t) in
  Array.fast_sort cmp p2;
  Array.to_list (Array.append (Array.append p1 p2) p3);;

let bfs n =
  let lo = ref 0 and hi = ref 5 in
  let x = ref 0 and y = ref 0 in
  kept := [mk_rthm(REFL `t:A`);mk_rthm(ASSUME `t:bool`);mk_rthm(T_TAUT);
           mk_rthm(T_DEF);mk_rthm(AND_DEF)];
  (*
  let lo = ref 0 and hi = ref 3 in
  let x = ref 0 and y = ref 0 in
  kept := [mk_rthm(REFL `t:A`);mk_rthm(ASSUME `t:bool`);
           mk_rthm(DEDUCT_ANTISYM_RULE (ASSUME `t:bool`) (REFL `\p:bool. p`))];
  *)
           
  let rec work pos rth (rem : rthm list) =
    match rem with
      h::t -> if is_gen rth h then (
                if pos < !x then x := !x-1 else ();
                if pos < !y then y := !y-1 else if pos = !y then x := 0 else ();
                if pos < !lo then lo := !lo-1 else ();
                if pos < !hi then hi := !hi-1 else ();
                work pos rth t)
              else h::(work (pos+1) rth t)
    | [] -> [rth] in

  for loop = 1 to n do
    kept := part_sort !kept !lo !hi (fun x y -> (rthm_size x) - (rthm_size y));
    x := 0; y := !lo;
    while !y < !hi do
        printf "loop:%d x:%d y:%d lo:%d hi:%d n_kept%d\n%!" loop !x !y !lo !hi (length !kept);
        let r1 = el !x (!kept) and r2 = el !y (!kept) in
        let l1 = if r1 != r2 then (req_mp r1 r2) @ (req_mp r2 r1) else req_mp r1 r2 in
        let l2 = if r1 != r2 then (rtrans r1 r2) @ (rtrans r2 r1) else rtrans r1 r2 in
        let l3 = if r1 != r2 then (rdeduct r1 r2) @ (rdeduct r2 r1) else rdeduct r1 r2 in
        (*
        let l4 = if r1 != r2 then (rmk_comb r1 r2) @ (rmk_comb r2 r1) else rmk_comb r1 r2 in
        *)
        let l4 = rmk_comb refl r2 in
        if !x < !y then x := !x + 1 else (x := 0; y := !y + 1);
        do_list (fun rth -> if not (exists (fun x -> is_gen x rth) !kept) then
                              kept := work 0 rth !kept
                            else ()) (l1 @ l2 @ l3 @ l4)
    done;
    lo := !hi;
    hi := length !kept
  done;;

let main n =
  kept := [];
  (* T_TAUT "t | t <=> T" is the only theorem that is deduced without canceling any hyp *)
  unprocessed := [mk_rthm(REFL `t:A`);mk_rthm(ASSUME `t:bool`);mk_rthm(T_TAUT);
                  mk_rthm(T_DEF);mk_rthm(AND_DEF)];
  let rec work pos rth (rem : rthm list) =
    match rem with
      h::t -> if is_gen rth h then (
                if pos = !y then x := 0 else (
                  if pos < !x then x := !x-1 else ();
                  if pos < !y then y := !y-1 else ());
                work pos rth t)
              else (
                let h' = simplify rth h in
                if h == h' then h::(work (pos+1) rth t)
                else (
                  print_endline "mddd";
                  if pos = !y then x := 0 else (
                    if pos < !x then x := !x-1 else ();
                    if pos < !y then y := !y-1 else ());
                  unprocessed := h'::(!unprocessed);
                  work pos rth t
                )
              )
    | [] -> [rth] in

  let rec self_clean rthl =
    match rthl with
      h::t -> let l = self_clean t in
              if exists (fun x -> is_gen x h) l then l
              else h::(filter (fun x -> not (is_gen h x)) t)
    | [] -> [] in

  for i = 1 to n do
    Printf.printf "iter:%d\tn_kept:%d\tn_unpro:%d\tx:%d\ty:%d\n%!" i (length !kept) (length !unprocessed) !x !y;
    while length (!unprocessed) > 0 do
      let rth = hd (!unprocessed) in
      unprocessed := tl (!unprocessed);
      do_list (fun x -> if is_gen x rth then (
                          try let cnt = Dict_rthm.find x !mm in
                              mm := Dict_rthm.add x (cnt+1) (Dict_rthm.remove x !mm)
                          with Not_found -> mm := Dict_rthm.add x 1 !mm
                        ) else ()) (!kept);
      try let rth = itlist (fun x y -> if is_gen x y then failwith "gen_test"
                                       else simplify x y) (!kept) rth in
              if rrsl rth <> [] then (
                print_endline "baba";
                baba := rth::(!baba)
              ) else ();
              kept := work 0 rth (!kept)
      with Failure "gen_test" -> ()
    done;
    let r1 = el !x (!kept) and r2 = el !y (!kept) in
    x := !x+1; if x > y then (x := 0; y := !y+1) else ();
    let l1 = if r1 != r2 then (req_mp r1 r2) @ (req_mp r2 r1) else req_mp r1 r2 in
    let l2 = if r1 != r2 then (rtrans r1 r2) @ (rtrans r2 r1) else rtrans r1 r2 in
    let l3 = if r1 != r2 then (rdeduct r1 r2) @ (rdeduct r2 r1) else rdeduct r1 r2 in
    let l4 = if r1 != r2 then (rmk_comb r1 r2) @ (rmk_comb r2 r1) else rmk_comb r1 r2 in
    Printf.printf "eq_mp:%d\ttrans:%d\tdeduct:%d\tmk_comb:%d\n" (length l1) (length l2) (length l3) (length l4);
    unprocessed := l1 @ l2 @ l3 @ l4;
    unprocessed := self_clean (!unprocessed)
  done;;

let lst = ref ([] : (rthm * int) list);;

let calc() =
  lst := [];
  Dict_rthm.iter (fun x y -> lst := (x,y)::(!lst)) !mm;
  lst := List.sort (fun x y -> (snd y) - (snd x)) (!lst);;


module Pint = struct
  type t = int * int
  let compare (x1,y1) (x2,y2) =
    if x1 = x2 then y1-y2 else x1-x2
end;;
module Pset = Set.Make(Pint);;

let hack = ref (mk_rthm (REFL `t`));;
let tag_kept = ref ([] : (rthm * int) list);;
let tag = ref 0;;
(* sort rthm according to their lengths *)
let main_len n =
  tag_kept := [];
  unprocessed := [mk_rthm(REFL `t:A`);mk_rthm(ASSUME `t:bool`);mk_rthm(T_TAUT);
                  mk_rthm(T_DEF);mk_rthm(AND_DEF)];

  let used = ref Pset.empty in

  let rec work rth (rem : (rthm * int) list) =
    match rem with
      (h,it)::t -> if is_gen rth h then work rth t
                   else (
                     let h' = simplify rth h in
                     if h == h' then (h,it)::(work rth t)
                     else (
                       print_endline "mddd";
                       unprocessed := h'::(!unprocessed);
                       work rth t))
    | [] -> [] in

  let rec insert (rth,tag) rem =
    match rem with
      (h,it)::t -> if rthm_size rth <= rthm_size h then
                     (rth,tag)::rem
                   else (h,it)::(insert (rth,tag) t)
    | [] -> [rth,tag] in

  let rec self_clean rthl =
    match rthl with
      h::t -> let l = self_clean t in
              if exists (fun x -> is_gen x h) l then l
              else h::(filter (fun x -> not (is_gen h x)) l)
    | [] -> [] in

  let next_job() =
    let rec work (x,y) =
      let px = (el x !tag_kept) and py = (el y !tag_kept) in
      let xx,yy = if snd px <= snd py then snd px,snd py else snd py,snd px in
      if Pset.mem (xx,yy) !used then
        if x = y then work (0,y+1) else work (x+1,y)
      else (used := Pset.add (xx,yy) !used; printf "%d %d\n%!" xx yy; fst px,fst py) in
    work (0,0) in

  for i = 1 to n do
    Printf.printf "iter:%d\tn_kept:%d\tn_unpro:%d\n%!" i (length !tag_kept) (length !unprocessed);
    while length (!unprocessed) > 0 do
      hack := hd (!unprocessed);
      let rth = hd (!unprocessed) in
      unprocessed := tl (!unprocessed);
      try let rth = itlist (fun (x,_) y -> if is_gen x y then failwith "gen_test"
                                           else simplify x y) (!tag_kept) rth in
              if rrsl rth <> [] then (
                print_endline "baba";
                baba := rth::(!baba)
              ) else ();
              tag_kept := work rth (!tag_kept);
              tag := !tag+1;
              tag_kept := insert (rth,!tag) (!tag_kept);
      with Failure "gen_test" -> ()
    done;

    let r1,r2 = next_job() in
    let l1 = if r1 != r2 then (req_mp r1 r2) @ (req_mp r2 r1) else req_mp r1 r2 in
    let l2 = if r1 != r2 then (rtrans r1 r2) @ (rtrans r2 r1) else rtrans r1 r2 in
    let l3 = if r1 != r2 then (rdeduct r1 r2) @ (rdeduct r2 r1) else rdeduct r1 r2 in
    let l4 = if r1 != r2 then (rmk_comb r1 r2) @ (rmk_comb r2 r1) else rmk_comb r1 r2 in
    Printf.printf "eq_mp:%d\ttrans:%d\tdeduct:%d\tmk_comb:%d\n" (length l1) (length l2) (length l3) (length l4);
    unprocessed := l1 @ l2 @ l3 @ l4;
    unprocessed := self_clean !unprocessed
  done;;

