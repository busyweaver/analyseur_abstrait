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

  
module Intervals = (struct
  
  (* types *)
  (* ***** *)
  type aux =
    | Pinf
    | Minf
    | Cst of Z.t

  (* type of abstract values *)
  type t =
    | Iv of aux*aux
    | BOT         (* the set is empty (not reachable) *)
   
  (* utilities *)
  (* ********* *)

  (* lift unary arithmetic operations, from integers to t *)
  let lift1 f x =
    match x with
    | BOT -> BOT
    | Iv (a,b) -> (
		match a,b with
        	|Cst x,Cst y -> Iv (f x, f y)
        	|Cst x,Pinf -> Iv ((f x),Pinf)  
      		|Minf,Cst x ->Iv (Minf, f x)
        	|_ -> Iv (a,b)) 

  (*let ouex a b = (a && (not b)) || ((not a) && b)*)
  
  (* lift binary arithmetic operations *)
  let lift2 f x y =
     match x with
       | BOT,_|_,BOT -> BOT
       | Iv (a,b),Iv (c,d) when ((a=Minf || c=Minf) && (b=Pinf || d=Pinf))-> Iv (Minf,Pinf)
       | Iv (a,b),Iv (c,d) when (a=Minf || c=Minf) -> Iv (Minf,(f b d))
       | Iv (a,b),Iv (c,d) when (b=Pinf || d=Pinf) -> Iv ((f a c),Pinf)
       | Iv (a,b),Iv (c,d) -> Iv (f a c,f b d)
    

  (* interface implementation *)
  (* ************************ *)

  (* unrestricted value *)
  let top = Iv (Pinf ,Minf)

  (* bottom value *)
  let bottom = BOT

  (* constant *)
  let const c = Iv (c ,c)

  (* interval *)
  let rand x y =
    if x=y then Iv( x ,x)
    else if x<y then Iv (x, y)
    else BOT
      
  let mulbis a c =
    match a,c with
    |Cst x ,Cst y -> Z.mul x y 
    |Minf,Cst x|Cst x,Minf -> if (lt_big_int x Z.zero) then Pinf else (if (gt_big_int x Z.zero) then Minf else Z.zero)
    |Pinf,Cst x|Cst x,Pinf -> if (gt_big_int x Z.zero) then Pinf else (if (lt_big_int x Z.zero) then Minf else Z.zero)

let divbis a c =
    match a,c with
      |Cst x ,Cst y -> if (y=Z.zero) then (if Z.gt_big_int x Z.zero then Pinf else (if (Z.lt_big_int x Z.zero) then Minf else Z.zero)) else Z.div_big_int  x y
      | Cst x,Minf | Cst,Pinf -> Z.zero
      | Pinf,Cst y -> (if (gt_big_int y Z.zero) then Pinf else Minf)
      | Minf,Cst y -> (if (gt_big_int y Z.zero) then Minf else Pinf)
   
  
let rec rl f l def = match l with |[]->def |[z] -> z| z::zs -> f z (maxl f zs def)

  let maxval a c =
    match a,c with
    |Cst x, Cst y ->  if Z.gt_big_int x y then x else y
    |Minf,x -> x
    |x,Minf -> x
    |x,Pinf-> Pinf
    |Pinf,x-> Pinf

  let minval a c =
    match a,c with
    |Cst x, Cst y ->  if Z.lt_big_int x y then x else y
    |Minf,x -> Minf
    |x,Minf -> Minf
    |x,Pinf-> x
    |Pinf,x-> x

let join a b = match a,b with
  | BOT,x | x,BOT -> x
  | Iv (a, b),Iv (c, d) -> Iv ((minval a c), (maxval c d))
  
  let meet a b = match a,b with
  | BOT,x | x,BOT -> BOT
  | Iv (a, b),Iv (c, d) -> Iv ((maxval a c), (minval c d))
  


  (* arithmetic operations *)

  let neg = lift1 Z.neg

  let add = lift2 Z.add

  let sub = lift2 Z.sub

  let mul x y = 
	match x,y with
	| Bot,_|_,BOT -> BOT
        | Iv (a,b),Iv (c,d)-> Iv (rl minval [mulbis a c;mulbis a d;mulbis b c;mulbis b d ],rl maxval [mulbis a c;mulbis a d;mulbis b c;mulbis b d ])

  let modu = lift2 Z.rem

  let div a b =
    join (div_bis a (meet b Iv (Z.one,Pinf))) (div_bis a (meet b Iv (Minf,Z.minus_one)))

  (* set-theoretic operations *)

  
  let gbis a c =
    match a,c with
    | x,y when x=y -> false
    |Cst x, Cst y ->  if Z.gt_big_int x y then true else false
    |Minf,x -> false
    |x,Minf -> true
    |x,Pinf-> false
    |Pinf,x-> true


  let lbis b d =
    match b,d with
    |x,y when (x=y) -> false
    |Cst x , Cst y ->  if Z.lt_big_int x y then true else false
    |Minf,x-> true
    |x,Minf -> false
    |x,Pinf-> true
    |Pinf,x-> false

  let eqbis a c = 
    match a,c with
    | x,x -> true
    |Cst x , Cst y ->  if Z.gt_big_int x y then true else false
    |Minf,x-> false
    |x,Minf -> true
    |x,Pinf-> false
    |Pinf,x-> true

  
  (* no need for a widening as the domain has finite height; we use the join *)
  let widen = join


  (* comparison operations (filters) *)

  let eq a b =a,b
(*	match a,b with
	| TOP,Cst x -> Cst x,Cst x
	| Cst x,TOP -> Cst x,Cst x
	|  Cst x, Cst y when Z.compare x y != 0 -> BOT,BOT
  | x,y -> x,y*)

  let neq a b =a,b 
	(*match a,b with
	|  Cst x, Cst y when Z.compare x y = 0 -> BOT,BOT
	| x,y -> x,y
 *)
  let geq a b =a,b
   (* match a,b with 
	|  Cst x, Cst y when Z.compare x y < 0 -> BOT,BOT
	| x,y -> x,y
	 
   *) 
  let gt a b =a,b
   (* match a, b with
    |  Cst x, Cst y when Z.compare x y <= 0 -> BOT,BOT
    |x,y -> x,y
     
   *)

  (* subset inclusion of concretizations *)
  let subset a b = match a,b with
  | BOT,_ | _,TOP -> true
  | Iv (a , b), Iv (c , d) -> true  (*if (ge_big_int a c && le_big_int b d) then true else false*)

  (* check the emptyness of the concretization *)
  let is_bottom a =
    a=BOT


  let print_rest r = 
   match r with
	| Pinf -> "+inf"
	| Minf -> "-inf"
	| Cst x -> Z.to_string x

  (* prints abstract element *)
  let print fmt x = match x with
  | BOT -> Format.fprintf fmt "bottom"
  | Iv (r , s) -> let p1 = print_rest r in
		let p2 = print_rest s in
			Format.fprintf fmt "iv [%s , %s]" p1 p2			

  

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
      x,y
        
  | AST_DIVIDE ->
      (* this is sound, but not precise *)
      x, y
        
      
end : VALUE_DOMAIN)

    
