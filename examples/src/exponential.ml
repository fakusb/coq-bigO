let rec f n =
  if n = 0 then ()
  else begin
    f (n-1);
    f (n-1)
  end
