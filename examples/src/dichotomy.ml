let rec bsearch (arr: int array) v i j =
  if j <= i then -1 else begin
    let m = i + (j - i) / 2 in
    if v = arr.(m) then
      m
    else if v < arr.(m) then
      bsearch arr v i m
    else
      bsearch arr v (m+1) j
  end

(* For future reference; not used at the moment *)
let bsearch_iter (arr: int array) v =
  let i = ref 0 in
  let j = ref (Array.length arr) in
  let found = ref (-1) in
  while !i < !j && !found = -1 do
    let m = !i + (!j - !i) / 2 in
    if v = arr.(m) then
      found := m
    else if v < arr.(m) then
      j := m
    else
      i := m + 1
  done;
  !found
