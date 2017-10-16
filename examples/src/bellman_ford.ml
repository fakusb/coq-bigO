(* O(nb_nodes * |edges|) *)
(* Sous la précondition qu'il n'y a pas d'arêtes dupliquées,
   O(|edges|) = O(n²) => O(n³)

   Preuve coq indépendante : |edges| sans duplicats, avec des entiers valides (\in [0, nb_nodes-1])

   Puis raisonner sur les O()...
*)
(* On peut faire une boucle à la place du List.iter, en prenant un tableau
   d'arêtes *)
let bellman_ford inf (edges : (int * int * int) list) nb_nodes =
  let d = Array.make nb_nodes inf in
  for i = 0 to nb_nodes - 2 do
    List.iter (fun (v1, v2, w) ->
      d.(v2) <- min d.(v2) (d.(v1) + w)
    ) edges
  done;
  d

let bellman_ford2 inf (edges : (int * int * int) array) nb_nodes =
  let d = Array.make nb_nodes inf in
  for i = 0 to nb_nodes - 2 do
    for j = 0 to Array.length edges - 1 do
      let (v1, v2, w) = edges.(j) in
      d.(v2) <- min d.(v2) (d.(v1) + w)
    done
  done;
  d
