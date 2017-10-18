let g1 () = ()
let g2 () = ()

let rec f n =
  if n <= 1 then ()
  else begin
    g1 (); g2 ();
    f (n-1)
  end
