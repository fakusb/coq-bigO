let tick () =
  ()

let rand n =
  0

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

let let2 n =
  let m = rand n in
  loop1 m

let loop2 n =
  let a = rand n in
  let b = rand n in
  for i = a to (a + b) - 1 do
    tick ()
  done

let if1 n cond =
  let a = rand n in
  let b = rand n in
  if cond then loop1 a else loop1 b

let rec rec1 n =
  if n <= 0 then ()
  else rec1 (n-1)

let rec quick n =
  if n = 0 then ()
  else (
    loop1 n;
    let2 n;
    quick (n - 1)
  )

let looploop n =
  for i = 0 to n - 1 do
    for j = 0 to i - 1 do
      tick ()
    done
  done
