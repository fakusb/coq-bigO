(* O(n) *)
let rec split_at n xs =
  match n, xs with
  | 0, xs ->
    [], xs
  | n, x::xs when n > 0 ->
    let xs', xs'' = split_at (pred n) xs in
    x::xs', xs''
  | _, _ ->
    failwith "invalid argument"

(* O(|l1|+|l2|) *)
let rec merge cmp l1 l2 =
  match (l1, l2) with
  | [], _ -> l2
  | _, [] -> l1
  | x1::xs1, x2::xs2 ->
    if cmp x1 x2 <= 0
    then x1 :: merge cmp xs1 l2
    else x2 :: merge cmp l1 xs2

(* O(n lg n) *)
(* Avoir la bonne fonction de coût qui permet de résoudre la récursion *)
let rec merge_sort cmp = function
  | [] -> []
  | [x] -> [x]
  | xs ->
    let n = List.length xs in
    let (xs, ys) = split_at (n / 2) xs in
    let xs' = merge_sort cmp xs in
    let ys' = merge_sort cmp ys in
    merge cmp xs' ys'
