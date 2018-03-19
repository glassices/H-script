needs "april/rthm.ml";;

let pp_print_rthm fmt rth =
  let asl,tm,rsl = dest_rthm rth in
  (if not (asl = []) then
    (if !print_all_thm then
      (pp_print_term fmt (hd asl);
       do_list (fun x -> pp_print_string fmt ",";
                         pp_print_space fmt ();
                         pp_print_term fmt x)
               (tl asl))
     else pp_print_string fmt "...";
     pp_print_space fmt ())
   else ();
   pp_open_hbox fmt();
   pp_print_string fmt "|- ";
   pp_print_term fmt tm;
   if not (rsl = []) then (
     pp_print_space fmt ();
     pp_print_string fmt "[";
     pp_print_term fmt (hd rsl);
     do_list (fun x -> pp_print_string fmt ";";
                       pp_print_space fmt ();
                       pp_print_term fmt x)
             (tl rsl);
     pp_print_string fmt "]";
   ) else ();
   pp_close_box fmt ());;

let print_rthm = pp_print_rthm std_formatter;;
#install_printer print_rthm;;
