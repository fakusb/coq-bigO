let g (m, n) =
  for i = 1 to n do
    for j = 1 to m do () done
  done

let f n = g (0, n)
