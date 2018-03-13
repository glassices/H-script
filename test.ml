try
  failwith "aaa"
with Failure x -> Printf.printf "%s\n%!" x;;
             
