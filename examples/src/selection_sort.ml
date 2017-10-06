let swap a i j =
  let tmp = a.(i) in
  a.(i) <- a.(j);
  a.(j) <- tmp

let selection_sort (a : int array) =
  let n = Array.length a in
  for i = 0 to n - 2 do
    let p = ref i in
    for j = i + 1 to n - 1 do
      if a.(j) < a.(!p) then
        p := j
    done;
    swap a i (!p)
  done
