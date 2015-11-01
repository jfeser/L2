open Core.Std

let () =
  let arrays = ref [] in
  while true do
    Unix.sleep 1;
    arrays := !arrays @ [Array.create 100000 0];
    let allocated_mb = ((Float.of_int (Gc.heap_words ())) *. 8.0) /. 1000000.0 in
    printf "Allocated %f Mb.\n" allocated_mb;
    flush stdout
  done
