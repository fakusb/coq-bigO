(* [maxsum_iter a] runs in O(n³), where [n] is [Array.length a].
*)
let maxsum_iter (a: int array): int =
  let m = ref 0 in
  for i = 0 to Array.length a do
    for j = i to Array.length a do
      let sum = ref 0 in
      for k = i to j - 1 do
        sum := !sum + a.(k)
      done;
      m := max !m !sum
    done
  done;
  !m


(* [maxsum_opt] runs in O(n²).
*)
let maxsum_opt (a: int array): int =
  let m = ref 0 in
  for i = 0 to Array.length a - 1 do
    let sum = ref 0 in
    for k = i to Array.length a - 1 do
      sum := !sum + a.(k);
      m := max !m !sum
    done
  done;
  !m


(* [maxsum_td] runs in O(n²).
*)

(* [maxsuffix_td a] returns the maximum suffix sum of [a]. *)
let rec maxsuffix_td (a: int array) (len: int): int =
  if len = 0 then 0
  else max 0 (a.(len - 1) + maxsuffix_td a (len - 1))

let rec maxsum_td_aux (a: int array) (len: int): int =
  if len = 0 then 0
  else max (maxsum_td_aux a (len - 1)) (maxsuffix_td a len)

let maxsum_td (a: int array): int =
  maxsum_td_aux a (Array.length a)


(* [maxsum_bu] runs in O(n).
*)
let maxsum_bu (a: int array): int =
  let m = ref 0 in
  let msuf = ref 0 in
  (* Invariant:
     - [m] is the maximum subsequence sum of a.(0)...a.(i-1).
     - [msuf] is the maximum suffix sum for a.(0)...a.(i-1).
  *)
  for i = 0 to Array.length a - 1 do
    msuf := max 0 (!msuf + a.(i));
    m := max !m !msuf
  done;
  !m
