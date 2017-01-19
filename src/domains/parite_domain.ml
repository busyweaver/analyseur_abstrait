(*
  Cours "Typage et Analyse Statique"
  Université Pierre et Marie Curie
  Antoine Miné 2015
*)

(* 
   The constant domain
*)

open Abstract_syntax_tree
open Value_domain
  
module Parity = (struct

  (* types *)
  (* ***** *)

  (* type of abstract values *)
  type t =
    | Odd
    | Even
    | BOT         (* the set is empty (not reachable) *)
    | TOP         (* the set of all integers (not constant)  *)


  (* utilities *)
  (* ********* *)


  (* lift unary arithmetic operations, from integers to t *)
  let lift1 f x =
    match x with
    | BOT -> BOT
    | TOP -> TOP
    | Even -> Even
    | Odd -> Odd
    
  (* lift binary arithmetic operations *)
  let lift2 f x y =
    match x,y with
    | BOT,_ | _,BOT -> BOT
    | TOP,_ | _,TOP -> TOP
    | Even,Odd| Odd,Even -> Odd
    | Even,Even -> Even
    | Odd,Odd-> Even
  
  (* interface implementation *)
  (* ************************ *)

  (* unrestricted value *)
  let top = TOP

  (* bottom value *)
  let bottom = BOT

  (*check if a is bottom *)
  let is_bottom a =
    a=BOT

  (* constant *)
  let const c =
   if(Z.equal (Z.erem c (Z.succ Z.one)) Z.one) then Odd else Even 

  (* interval *)
  let rand x y =
     if(Z.equal x y) then (if (Z.equal (Z.erem x (Z.succ Z.one)) Z.one) then Odd else Even)
     else (if(Z.compare x y >0) then BOT else TOP)

  (* arithmetic operations *)
  let neg = lift1 Z.neg

  let add = lift2 Z.add

  let sub = lift2 Z.sub

  let mul x y = 
    match x,y with
    |BOT,_|_,BOT -> BOT
    |Odd,Odd -> Odd
    |Even,_|_,Even ->Even
    |TOP, _|_,TOP ->TOP

  let modu = lift2 Z.rem

  let div a b =
    match a,b with
    |BOT, _| _,BOT -> BOT
    |_ -> TOP

(* Set operations *)
  let meet a b =
   match a, b with
   |x, y when (x=y) -> x
   |TOP, x|x,TOP -> x
   |_ -> BOT

  let join a b =
   match a,b with 
   |BOT,x|x,BOT -> x
   |_,TOP|TOP,_ -> TOP
   |Even,Odd|Odd,Even -> TOP
   |_ -> a

 let widen a b =
   join a b


  let subset a b =
   match a,b with
    |Odd,Odd|Even,Even -> true
    |_,BOT|TOP,_->false
    |Even,Odd|Odd,Even -> false
    |_,TOP|BOT,_ -> true

 

  (* comparison operations (filters) *)
 let eq a b =
  let m = meet a b in
    m, m
 
 let neq a b =
  match a, b with   
  |BOT,_|_,BOT -> BOT,BOT
  |Even, Odd|Odd,Even -> a,b
  |Even, TOP|TOP,Odd -> Even,Odd
  |TOP,Even |Odd, TOP->  Odd,Even
  |_ -> BOT,BOT

 let geq a b = 
  match a, b with
  |BOT,_|Even,Odd|Odd,Even|_,TOP ->BOT,BOT
  |x,BOT ->x,BOT
  |TOP,x -> TOP,x
  |_ -> a,b

  let gt a b =
   match a, b with 
   |BOT,_|_,TOP -> BOT,b
   |Even, Odd|Odd,Even ->BOT,b
   |_ -> TOP,b
  

  (* prints abstract element *)
  let print fmt x = match x with
  | BOT -> Format.fprintf fmt "bottom"
  | TOP -> Format.fprintf fmt "top"
  | Odd -> Format.fprintf fmt "Odd"
  |Even -> Format.fprintf fmt "Even"
  
  (* operator dispatch *)
        
  let unary x op = match op with
  | AST_UNARY_PLUS  -> x
  | AST_UNARY_MINUS -> neg x

  let binary x y op = match op with
  | AST_PLUS     -> add x y
  | AST_MINUS    -> sub x y
  | AST_MULTIPLY -> mul x y
  | AST_MODULO -> modu x y
  | AST_DIVIDE   -> div x y

  let compare x y op = match op with
  | AST_EQUAL         -> eq x y
  | AST_NOT_EQUAL     -> neq x y
  | AST_GREATER_EQUAL -> geq x y
  | AST_GREATER       -> gt x y
  | AST_LESS_EQUAL    -> let y',x' = geq y x in x',y'
  | AST_LESS          -> let y',x' = gt y x in x',y'
        

  let bwd_unary x op r = match op with
  | AST_UNARY_PLUS  -> meet x r
  | AST_UNARY_MINUS -> meet x (neg r)

        
  let bwd_binary x y op r = match op with

  | AST_PLUS ->
      (* r=x+y => x=r-y and y=r-x *)      
      meet x (sub r y), meet y (sub r x)

  | AST_MINUS ->
      (* r=x-y => x=y+r and y=x-r *)
      meet x (add y r), meet y (sub y r)
        
  | AST_MULTIPLY ->
      (* r=x*y => (x=r/y or y=r=0) and (y=r/x or x=r=0)  *)
      let contains_zero o = subset (const Z.zero) o in
      (if contains_zero y && contains_zero r then x else meet x (div r y)),
      (if contains_zero x && contains_zero r then y else meet y (div r x))
  | AST_MODULO ->
      (* m x%y => (k in env.Z, x= k*y+m *)
      x,y (* A implémenter *)
        
  | AST_DIVIDE ->
      (* this is sound, but not precise *)
      TOP, TOP (* A implementer *)
        
      
end : VALUE_DOMAIN)

