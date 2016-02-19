open Core.Std
open Printf

exception CompareFunctionResultError

(* ctci 1.1 *)
let uniq (s : string) : bool =
  let empty = Char.Map.empty in
  let rec go s m =
    if s = "" then true
    else (
      let s' = String.drop_prefix s 1 in
      let c = String.get s 0 in
      match (Map.find m c) with
      | Some _ -> false
      | None   -> go s' (Map.add m ~key:c ~data:1)
    )
  in go s empty

(* ctci 1.3
   Given two strings, write a method to decide if one is a permutation of the other *)
let is_permutation (x : string) (y : string) : bool =
  let sort xs = List.sort ~cmp:Char.compare (String.to_list xs) in
  sort x = sort y

let test_is_permutation =
  print_string (if (is_permutation "asdf" "fdsa") then "true" else "false")

(* ctci 1.4 replace all spaces in a string with'%20'. *)
let percent_twenty s =
  let words = String.split (String.rstrip s) ~on:' ' in
  String.concat ~sep:"%20" words

(* ctci 1.5 basic string compression *)
let compress s =
  let s_len = String.length s
  and s_list = String.to_list s in
  let rec aux xs res len =
    if len >= s_len then s
    else
      match List.hd xs with
      | Some c ->
        let freq = List.length (List.take_while xs ~f:(fun char -> char = c)) in
        let xs' = List.drop xs freq
        and res' = res @ [(Char.to_string c);(Int.to_string freq)] in
        aux xs' res' (len + 2)
      | None -> String.concat res
  in aux s_list [] 0

(* ctci 1.7: Write an algorithm such that if an element in an MxN matrix is 0, its
 * entire row and column are set to 0. *)
let zero_cols_and_rows matrix width height =
  let cols = Array.create ~len:height false
  and rows = Array.create ~len:width  false in
  let mark =
    for i=0 to height-1 do
      for j=0 to width-1 do
        if matrix.(i).(j) = 0 then (
          cols.(i) <- true;
          rows.(j) <- true;
        )
      done
    done
  and zero_out =
    for i=0 to height-1 do
      for j=0 to width-1 do
        if cols.(i) || rows.(j) then matrix.(i).(j) <- 0;
        print_string (Int.to_string matrix.(i).(j) ^ " ")
      done;
      print_string "\n"
    done
  in mark; zero_out

(* ctci 1.8
 * Assume you have a method isSubstring which checks if one word is a substring
 * of another. Given two strings, s i and s2, write code to check if s2 is a
 * rotation of si using only one call to isSubstring (e.g.,"waterbottle"is a rota-
 * tion of"erbottlewat"). *)
let is_rotation x y =
  (String.length x = String.length y) && (String.is_substring (x ^ x) ~substring:y)

(* ctci 2.1: Write code to remove duplicates from an unsorted linked list. *)
let remove_dups xs =
  let table = Int.Table.create () in
  let rec go newlist = function
    | [] -> newlist
    | hd :: tl ->
      match Hashtbl.find table hd with
      | Some _ -> go newlist tl
      | None   ->
        Hashtbl.replace table ~key:hd ~data:0;
        go ([hd] @ newlist) tl
  in go [] xs

(* ctci 2.2: Implement an algorithm to find the kth to last element of a singly
 * linked list. *)
let kth_to_last (xs : 'a list) (n : int) : 'a option =
  let runner = List.drop xs n in
  let rec go xs runner =
    match runner with
    | [] -> List.hd xs (* let Some n = List.hd xs in n *)
    | hd :: tl -> match xs with
      | [] -> None
      | y :: ys -> go ys tl
  in go xs runner

(* 2.3: Implement an algorithm to delete a node in the middle of a singly linked
 * list, given only access to that node. *)
let delete_node = function
  | []       -> []
  | hd :: tl -> tl

(* ctci 2.4 Write code to partition a linked list around a value x, such that al
 * nodes less than x come before all nodes greater than or equal to x *)
let partition_ll xs n =
  let rec pll xs left right =
    match xs with
    | [] -> left @ right
    | hd :: tl ->
      if hd < n
      then pll tl (hd :: left) right
      else pll tl left (hd :: right)
  in pll xs [] []

(* ctci 2.5 You have two numbers represented by a linked list, where each node
 * contains a single digit. The digits are stored in reverse order, such that the
 * 1's digit is at the head of the list. Write a function that adds the two numbers
 * and returns the sum as a linked list. *)
let add_two_nums_ll xs ys =
  let rec go xs ys carry res =
    match (xs,ys) with
    | ([], []) -> res
    | (xs, []) -> go xs [0] carry res
    | ([], ys) -> go [0] ys carry res
    | ((x :: xs), (y :: ys)) ->
      let sum = x + y + carry in
      if sum > 9
      then go xs ys 1 (res @ [(sum - 10)])
      else go xs ys 0 (res @ [sum])
  in go xs ys 0 []

(* ctci Part B: Suppose the digits are stored in forward order. Repeat the above
 * problem. *)
let list_to_int xs place =
  let rec go xs len place =
    match xs with
    | []       -> place
    | hd :: tl -> go tl (len - 1) (((Int.pow 10 len) * hd) + place)
  in go xs place 0

let forward_add_two_nums_ll xs ys =
  let len_x = List.length xs
  and len_y = List.length ys in
  let x     = list_to_int xs (pred len_x)
  and y     = list_to_int ys (pred len_y) in
  x + y

(* ctci 3.2 How would you design a stack which, in addition to push and pop, also has
 * a function min which returns the minimum element? Push, pop and min should all
 * operate in O(1) time. *)
module type STACKMIN =
sig
  type 'a stackmin

  val newstack : 'a -> ('a -> 'a -> int) -> 'a stackmin
  val push : 'a -> 'a stackmin -> 'a stackmin
  val pop : 'a stackmin -> ('a option * 'a stackmin)
  val peek : 'a stackmin -> 'a option
end

module MyStackMin : STACKMIN =
struct
  type 'a stackmin = { stack : 'a list ; min : 'a list ; comp : 'a -> 'a -> int }

  let newstack elem f = { stack = [elem] ; min = [elem] ; comp = f }

  let push elem ({ stack ; min ; comp } as s) =
    let min' = match List.hd min with
      | Some n -> (match comp elem n with
          | -1 | 0 -> elem :: min
          | 1      -> n    :: min
          | _      -> raise CompareFunctionResultError)
      | None -> [elem]
    in { s with stack = elem :: stack; min = min' }

  let pop ({ stack ; min } as s) =
    let safe_tl xs = match List.tl xs with
      | Some tl -> tl
      | None    -> []
    in
    let newstack = safe_tl stack
    and newmin   = safe_tl min
    in
    let popped = { s with stack=newstack; min=newmin }
    and top = List.hd stack
    in (top, popped)

  let peek {stack} = List.hd stack
end

let mystack = MyStackMin.newstack 3 Int.compare

(* ctci 4.1: Implement a function to check if a binary tree is balanced. For the
 * purposes of this question, a balanced tree is defined to be a tree such that the
 * heights of the two subtrees of any node never differ by more than one. *)
type btree =
  | Leaf
  | Node of btree*btree

let bal t =
  let cont n expr =
    match n with
    | -1 -> -1
    | _  -> expr
  in
  let rec aux = function
    | Leaf          -> 0
    | Node (t1, t2) ->
      let h1 = aux t1 in
      cont h1 (
        let h2 = aux t2 in
        cont h2 (
          if abs (h1 - h2) > 1 then -1
          else (max h1 h2) + 1
        )
      )
  in aux t <> -1

(* ctci 4.2: Given a directed graph, design an algorithm to find out whether
 * there is a route between two nodes. *)
module Graph =
struct
  type node   = int
  type graph  = { nodes : node list; edges : (node*node) list }
  let mk = { nodes=[] ; edges= [] }

  let mk_outgoing g =
    fun n ->
      let keep ((left,_) as edge) acc = if left = n then [edge] @ acc else acc in
      let next_to = List.fold_right g.edges ~f:keep ~init:[] in
      Int.Set.of_list (List.map next_to ~f:snd)

  let bfs_traverse_until g root ~f:action =
    let outgoing = mk_outgoing g
    and visited  = Int.Set.empty
    and to_visit = Queue.create () in
    Queue.enqueue to_visit root;
    let rec loop visited =
      Option.value_map
        (Queue.dequeue to_visit)
        ~default:None
        ~f:(fun id ->
            if action id then Some id
            else begin
              if not (Int.Set.mem visited id) then
                let children = Int.Set.diff (outgoing id) visited in
                Int.Set.iter children ~f:(fun n -> Queue.enqueue to_visit n);
                let visited' = Int.Set.add visited id in
                loop visited'
              else
                loop visited
            end
          )
    in loop visited

  let route g n1 n2 =
    Option.is_some (bfs_traverse_until g n1 ~f:(fun node -> node = n2))
end

let my_graph : Graph.graph =
  { Graph.nodes = [1;2;3;4;5;6;7;8;9;10]
  ; Graph.edges = [(1,2); (1,3); (1,5); (1,8); (1,9)
                  ;(2,3); (2,10); (2,7)
                  ;(3,8)
                  ;(4,6); (4,10)
                  ;(5,4); (5,6)
                  ;(6,3)
                  ;(7,8); (7,10); (7,1)
                  ;(8,9); (8,6)
                  ;(9,6); (9,3)
                  ;(10,9); (10,8)] }

(* ctci 4.3 Given a sorted (increasing order) array with unique integer
 * elements, write an algorithm to create a binary search tree with minimal
 * height. *)

type 'a bintree =
  | Empty
  | Node of 'a * 'a bintree * 'a bintree

let build_bintree (a : int array) : int bintree =
  let rec insert x y =
    if y < x then Empty
    else
      let mid   = (x + y) / 2 in
      let elem  = a.(mid)
      and left  = insert x (mid - 1)
      and right = insert (mid + 1) y in
      Node (elem, left, right)
  and len = Array.length a in
  insert 0 (len - 1)


(* ctci 4.4 Given a binary tree, design an algorithm which creates a linked list
 * of all the nodes at each depth (e.g., if you have a tree with depth D, you'll
 * have D linked lists). *)
let ll_per_layer (t : 'a bintree) : 'a list list =
  let rec gen_next_layer elems nl = function
    | [] -> (elems,nl)
    | Empty::xs ->
      gen_next_layer elems nl xs
    | (Node (value, left, right))::xs ->
      gen_next_layer ([value] @ elems) ([left;right] @ nl) xs
  in
  let rec gen_all_layers (acc : 'a list list) (xs : 'a bintree list) : 'a list list =
    match gen_next_layer [] [] xs with
    | (_, [])     -> acc
    | (elems, ts) -> gen_all_layers ([elems] @ acc) ts
  in gen_all_layers [] [t]

(* ctci 11.1: You are given two sorted arrays, A and B, where A has a large enough
 * buffer at the end to hold B. Write a method to merge B into A in sorted order. *)
let rec merge_in a b last_a last_b =
    let index_a      = ref (last_a - 1)
    and index_b      = ref (last_b - 1)
    and index_merged = ref (last_a + last_b - 1) in
    while !index_a >= 0 && !index_b >= 0 do
      if a.(!index_a) > b.(!index_b) then (
        a.(!index_merged) <- a.(!index_a);
        decr index_a
      ) else (
        a.(!index_merged) <- b.(!index_b);
        decr index_b
      );
      decr index_merged;
    done;
    while !index_b >= 0 do
      a.(!index_merged) <- b.(!index_b);
      decr index_merged;
      decr index_b
    done

(* ctci 11.2: Write a method to sort an array of strings so that all the
 * anagrams are next to each other. *)
let group_anagrams (xs : string array) : unit =
  let join (xs : char array) : string =
    String.concat_array (Array.map ~f:Char.to_string xs) in
  let key (s : string) : string =
    let chars = String.to_array s in
    Array.sort chars ~cmp:Char.compare;
    join chars in
  let table = String.Table.create () in
  Array.iter xs ~f:(fun s -> Hashtbl.add_multi table ~key:(key s) ~data:s);
  let i = ref 0 in
  Hashtbl.iter_vals table ~f:(fun ys ->
      List.iter ys ~f:(fun s -> xs.(!i) <- s; incr i));

type ('a,'b) binary_tree =
    | Empty
    | Node of ('a*'b) * ('a,'b) binary_tree * ('a,'b) binary_tree
