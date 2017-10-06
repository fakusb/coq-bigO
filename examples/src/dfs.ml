(*************************************************************************)
(** DFS Algorithm, Sedgewick's presentation *)

module Sedgewick = struct
  type color = White | Gray | Black

  let rec dfs_from (g : int list array) (c : color array) (i : int) =
    c.(i) <- Gray;
    List.iter (fun j ->
      if c.(j) = White
      then dfs_from g c j) g.(i);
    c.(i) <- Black

  let dfs_main (g : int list array) (root : int) =
    let n = Array.length g in
    let c = Array.make n White in
    dfs_from g c root;
    c
end

(*************************************************************************)
(** Simpler version without cycle detection (no Gray color) *)

(* Termination argument: number of nodes marked false decreases at each step *)

(* Pre: only called on "false" nodes.

   First line of code decreases the measure (number of false nodes)
*)

(* Cost : number of edges + number of nodes

   Potential : sum of the degree of false nodes
     Initially: number of edges
*)

module Simple = struct
  let rec dfs_from (g : int list array) (c : bool array) (i : int) =
    c.(i) <- true;
    List.iter (fun j ->
      if not c.(j)
      then dfs_from g c j) g.(i)

  let dfs_main (g : int list array) (root : int) =
    let n = Array.length g in
    let c = Array.make n false in
    dfs_from g c root;
    c
end
