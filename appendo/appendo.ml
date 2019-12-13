module L = List 

open OCanren 
open GT

module Helper = struct 
    let show_ground_int = show(int)
    let show_ground_nat = show(Std.Nat.ground)
    let show_ground_list = show(Std.List.ground) show_ground_nat
    let show_ground_pair_list = show(Std.Pair.ground) show_ground_list show_ground_list
    
    let show_logic_int  = show(logic) (show(int))    
    let show_logic_int_pair = show(Std.Pair.logic) show_logic_int show_logic_int    
    let show_logic_int_list = show(Std.List.logic) show_logic_int
    let show_logic_pair_list_int = show(Std.Pair.logic) show_logic_int_list show_logic_int_list 

    let reify_list' = Std.List.reify reify   
    let reify_list c = c#reify reify_list'    
    let reify_pair_list c = c#reify (Std.Pair.reify reify_list' reify_list')
  
    let print_results n result shower reifier =
      Printf.printf "------------------------------\n";
      L.iter (fun c -> Printf.printf "%s\n%!" @@ shower @@ reifier c) @@ 
              Stream.take ~n:n (result (fun c -> c))
          
    let print_ground_results shower n result = 
      Printf.printf "------------------------------\n";
      L.iter (fun c -> Printf.printf "%s\n%!" @@ shower @@ c#prj) @@ 
              Stream.take ~n:n (result (fun c -> c))
  
    let run_ground_list = print_ground_results show_ground_list
    let run_ground_pair_list = print_ground_results show_ground_pair_list
  
    let run_list n result = 
      print_results n result show_logic_int_list reify_list 

    let run_list_pair n result = 
      print_results n result show_logic_pair_list_int reify_pair_list 
  end 
  
 

let rec append xs ys = 
  match xs with 
  | [] -> ys 
  | (h :: t) -> h :: append t ys 

(* appendo [] xs xs  *) 
let rec appendo xs ys out = ocanren (
    (xs == []) & ys == out | 
    fresh h, t, r in 
      h :: t == xs & 
      (appendo t ys r) & 
      h :: r == out   
  ) 
 
let _ =
  Helper.run_ground_list 1 @@ 
  run q (fun xs -> ocanren (appendo [0; 1] [2] xs)) ;
  
  Helper.run_ground_list 1 @@ 
  run q (fun xs -> ocanren (appendo [0; 1] xs [0; 1; 2]) ) ;
  
  Helper.run_ground_list 1 @@ 
  run q (fun xs -> ocanren (appendo xs xs [0;0;0;0]) ) ; 
  
  Helper.run_ground_pair_list 5 @@ 
  run q (fun q -> ocanren (fresh xs, ys in 
                             q == (xs, ys) & 
                            (appendo xs ys [0;0;0;0]))); 
                          
  Helper.run_list 1 @@ 
  run q (fun xs -> appendo xs xs xs) ;
  
  Helper.run_list 1 @@ 
  run q (fun xs -> ocanren (appendo [] xs xs)) 
  
let rec reverso xs sx = ocanren (
    ([] == xs) & ([] == sx) |
     fresh h, t, r in 
       h :: t == xs & 
      (reverso t r) & 
      (appendo r [h] sx)
  )


let _ =
  Printf.printf "------------------------------\n" ; 
  Helper.run_ground_list 1 @@ 
  run q (fun xs -> ocanren (reverso [0;1;2] xs)) ;
  
  Helper.run_ground_list 1 @@ 
  run q (fun xs -> ocanren (reverso xs [0;1;2])) ;
  
  Helper.run_list 5 @@ 
  run q (fun xs -> reverso xs xs) ; 
  
  Helper.run_list_pair 3 @@ 
  run q (fun q -> ocanren (fresh xs, ys in q == (xs, ys) & (reverso xs ys)))  
 

