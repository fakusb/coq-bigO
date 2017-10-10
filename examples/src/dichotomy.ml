(* Pour prouver la récursion : si |j-i| < 2^k, alors on termine en k étapes.

   François a un principe d'induction généralisé qui permet de diviser par 2.
*)
let rec bsearch (t: int array) v i j =
  if j <= i then -1 else begin
    let m = i + (j - i) / 2 in
    if v = t.(m) then
      m
    else if v < t.(m) then
      bsearch t v i m
    else
      bsearch t v (m+1) j
  end
