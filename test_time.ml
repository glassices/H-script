let n = 20000;;
let a = (0--n);;
let b = Array.of_list a;;

print_endline "start list";;
for i = 0 to n do
  let v = List.nth a i in ()
done;;
print_endline "done list";;

print_endline "start array";;
for i = 0 to n do
  let v = Array.get b i in ()
done;;
print_endline "done array";;
