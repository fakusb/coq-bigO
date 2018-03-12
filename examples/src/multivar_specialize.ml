let g (m, n) =
  for i = 1 to n do
    for j = 1 to m do () done
  done

let f n = g (0, n)

(*---------------*)

let rec f2 m n =
  if n > 0 then f2 (m+1) (n-1)
  else if m > 0 then f2 (m-1) 0
  else ()

let f3 m n =
  let nr = ref n in
  let mr = ref m in
  while !nr > 0 do
    incr mr; decr nr
  done;
  while !mr > 0 do
    decr mr
  done

let g2_1 n = f2 0 n
let g2_2 m = f2 m 0

let g3_1 n = f3 0 n
let g3_2 m = f3 m 0
