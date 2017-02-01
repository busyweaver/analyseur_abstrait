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

  (* constant *)
  let const x = if (Z.equal (Z.erem x (Z.of_string "2")) Z.one ) then Odd else Even

                 (* interval *)
                 
  let rand x y =
    if (x=y) then (if (Z.equal (Z.erem x (Z.of_string "2")) Z.one ) then Odd else Even )  
    else TOP


  (* arithmetic operations *)

  let neg = lift1 Z.neg

  let add = lift2 Z.add

  let sub = lift2 Z.sub

  let mul x y =
    match x,y with
    | BOT,_ | _,BOT -> BOT
    | TOP,_ | _,TOP -> TOP
    | Even,Odd| Odd,Even -> Even
    | Even,Even -> Even
    | Odd,Odd-> Odd
    

    
  let div  x y=TOP
   


  let modu x y=TOP

  (* set-theoretic operations *)
  
  let join x y = match x,y with
    | BOT,_ | _,BOT -> BOT
    | TOP,_ | _,TOP -> TOP
    | Even,Odd| Odd,Even -> TOP
    | Even,Even -> Even
    | Odd,Odd-> Odd
    
 
  

  let meet x y =
     match x,y with
    | BOT,_ | _,BOT -> BOT
    | TOP,x | x,TOP -> x
    | Even,Odd| Odd,Even -> BOT
    | Even,Even -> Even
    | Odd,Odd-> Odd
    
 

  (* no need for a widening as the domain has finite height; we use the join : Pas besoin d'un elargissement *)
  let widen = join


  (* comparison operations (filters) *)

  let eq  x y= x,y 
 
(*let nenv= meet a b in
    nenv, nenv*)

  let neq x y =    match x,y with
    | BOT,_ | _,BOT -> BOT,BOT
    | TOP,Odd -> Even,Odd
    | Odd,TOP -> Odd,Even
    | TOP,Even ->Odd,Even
    | Even,TOP -> Even,Odd
    | Even,Odd -> Even,Odd
    | Odd,Even -> Odd,Even 
    | Even,Even -> BOT,BOT
    | Odd,Odd-> BOT,BOT
    |TOP,TOP ->TOP,TOP
  
  let geq x y = x,y
     

    
  let gt a b = a,b
   
  (* subset inclusion of concretizations *)
  let subset a b = true
  
  (* check the emptyness of the concretization *)
  let is_bottom a = true
  

  (* prints abstract element *)
  let print fmt x = match x with
  | BOT -> Format.fprintf fmt "bottom"
  | TOP -> Format.fprintf fmt "top"
  | Odd -> Format.fprintf fmt "Odd"
  | Even -> Format.fprintf fmt "Even"


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

  let compare (x:t) (y:t) op = match op with
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


  let concrete x = []
        
      
end)

    
