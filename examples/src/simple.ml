let tick () =
  ()

let tick3 () =
  tick ();
  tick ();
  tick ()

let loop1 n =
  for i = 0 to n - 1 do
    tick (); tick ()
  done

let let1 n =
  let m = tick (); n + 1 in
  loop1 m
