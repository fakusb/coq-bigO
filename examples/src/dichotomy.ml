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
