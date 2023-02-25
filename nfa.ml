open List
open Sets

(*********)
(* Types *)
(*********)

type ('q, 's) transition = 'q * 's option * 'q

type ('q, 's) nfa_t = {
  sigma : 's list;
  qs : 'q list;
  q0 : 'q;
  fs : 'q list;
  delta : ('q, 's) transition list;
}

(***********)
(* Utility *)
(***********)

(* explode converts a string to a character list *)
let explode (s : string) : char list =
  let rec exp i l = if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

(****************)
(* Part 1: NFAs *)
(****************)

let move (nfa : ('q, 's) nfa_t) (qs : 'q list) (s : 's option) : 'q list =
  (* if symbol is not in alphabet return empty list*)
  List.sort_uniq Stdlib.compare (
    List.fold_right (fun x lst -> match x with (a,b,c) ->
      if exists (fun x -> x = a)qs && s = b  then
         c::lst else lst
    ) nfa.delta []
  )

let rec e_closure (nfa : ('q, 's) nfa_t) (qs : 'q list) : 'q list =
  let rec_lst = List.sort_uniq Stdlib.compare(
    qs @ (move nfa qs None)) in
  if List.length rec_lst = List.length qs then rec_lst else 
  e_closure nfa rec_lst

(* if i do e_closure [0;1;2] it will output [0;1;2;2], also lets chec
to see what happens if there is two valid transitions. I fixed this 
problem but it still isn't passing the semi public*)
let rec check (nfa : ('q, char) nfa_t) (lst: 'q list) = 
  match lst with | [] -> false | h::t -> if elem h nfa.fs then true else check nfa t

let accept (nfa : ('q, char) nfa_t) (s : string) : bool =
  let ans = List.fold_left (fun x a -> move nfa (e_closure nfa x) (Some a)) (e_closure nfa [nfa.q0]) (explode s) in
  check nfa (e_closure nfa ans)
  (* if ans = [] then false else
  subset (ans) nfa.fs *)
(*******************************)
(* Part 2: Subset Construction *)
(*******************************)

let new_states (nfa : ('q, 's) nfa_t) (qs : 'q list) : 'q list list =
  (* gotta check for dead states *)
  if List.length qs = 0 then [[]] else

  List.sort_uniq Stdlib.compare (
    List.fold_left (fun a x -> 
      
      (List.fold_left 
        (fun b y-> 
          (
          e_closure nfa(move nfa [y] (Some x))
          ) @ b
        ) [] qs
      ) :: a
    ) [] nfa.sigma
  )

let new_trans (nfa : ('q, 's) nfa_t) (qs : 'q list) :
    ('q list, 's) transition list =
  List.sort_uniq Stdlib.compare (
    List.fold_left (fun a x -> 
      (qs, Some x,
      (List.fold_left 
        (fun b y-> 
          (
          e_closure nfa(move nfa [y] (Some x))
          ) @ b
        ) [] qs
      )) :: a
    ) [] nfa.sigma
  )

let new_finals (nfa : ('q, 's) nfa_t) (qs : 'q list) : 'q list list =
  if elem true (map (fun x -> if elem x nfa.fs then true else false) qs) then [qs] else []

let rec nfa_to_dfa_step (nfa : ('q, 's) nfa_t) (dfa : ('q list, 's) nfa_t)
    (work : 'q list list) : ('q list, 's) nfa_t =
    (* failwith "unimplemented" *)
  (*The dfa will act as an accumulator (visited), the wrk is a list of univisted states. *)
  (*One possibility would be *)
  match work with 
  | [] -> dfa
  | h::t -> (* also need to check if head is empty*)
          if List.length h = 0 then nfa_to_dfa_step nfa dfa t
          else       
            (*h is a list here, so we can append it to our list of lists dfa.qs  *)
            if elem h dfa.qs = false then 
              let dfa = {
                sigma = dfa.sigma;
                qs = h::dfa.qs;
                q0 = dfa.q0;
                fs = (new_finals nfa h) @ dfa.fs; (*dfa.fs should be a list of lists *)
                delta = (new_trans nfa h) @ dfa.delta; (*delta should also be a list of lists, with transition type ('q list -> s) *)
              } in
              nfa_to_dfa_step (nfa) (dfa) ((new_states nfa (e_closure nfa h)) @ work)
              else nfa_to_dfa_step (nfa) (dfa) (t)

let nfa_to_dfa (nfa : ('q, 's) nfa_t) : ('q list, 's) nfa_t =
  (*Initialize the dfa value  *)
  (*For the final states, I have to check if the final state is in the 
  outputted state. *)
  let dfa = {
    sigma = nfa.sigma;
    qs = [e_closure nfa [nfa.q0]]; (*type 'q list list *)
    q0 = [nfa.q0]; (*type 'q list *)
    fs = new_finals nfa [nfa.q0]; (*type 'q list list*)
    delta = new_trans nfa [nfa.q0]; (*type ('q list, 's) transition list *)
  } 
  in nfa_to_dfa_step nfa dfa (new_states nfa (e_closure nfa [nfa.q0]))

