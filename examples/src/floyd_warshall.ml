(* Invariant pour la correction : à la k-ième étape, g.(i).(j) est <= au min des
   chemins de longueur au plus k *)
let floyd_warshall (g : int array array) =
  let n = Array.length g in
  for k = 0 to n - 1 do
    for i = 0 to n - 1 do
      for j = 0 to n - 1 do
        g.(i).(j) <- min g.(i).(j) (g.(i).(k) + g.(k).(j))
      done
    done
  done
