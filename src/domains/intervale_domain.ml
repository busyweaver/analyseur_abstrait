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

  
module Constants = (struct
  
  (* types *)
  (* ***** *)
  type aux =
    | pinf
    | minf
    | Cst of Z.a

  (* type of abstract values *)
  type t =
    | iv of aux*aux
    | BOT         (* the set is empty (not reachable) *)
   
  (* utilities *)
  (* ********* *)

  (* lift unary arithmetic operations, from integers to t *)
  let lift1 f x =
    match x with
    | BOT -> BOT
    | iv (a,b) -> (match a,b with
        |Cst x,Cst y -> iv (f x, f y)
        |Cst x,pinf -> iv ((f x),pinf)  
        |minf,Cst x ->iv (minf, f x)
        |_ -> iv (a,b)) 

  (*let ouex a b = (a && (not b)) || ((not a) && b)*)
  
  (* lift binary arithmetic operations *)
  let lift2 f x y =
     match x with
       | BOT,_|_,BOT -> BOT
       | iv (a,b),iv (c,d) when ((a=minf || c=minf) && (b=pinf || d=pinf))-> iv (minf,pinf)
       | iv (a,b),iv (c,d) when (a=minf || c=minf) -> iv (minf,(f b d))
       | iv (a,b),iv (c,d) when (b=pinf || d=pinf) -> iv ((f a c),pinf)
       | iv (a,b),iv (c,d) -> iv (f a c,f b d)
    



  (* interface implementation *)
  (* ************************ *)


  (* unrestricted value *)
  let top = iv (pinf ,minf)

  (* bottom value *)
  let bottom = BOT

  (* constant *)
  let const c = iv (c ,c)

  (* interval *)
  let rand x y =
    if x=y then iv( x ,x)
    else if x<y then iv (x, y)
    else BOT
      
  let mulbis a c =
    match a,c with
    |Cst x ,Cst y -> Z.mul x y 
    |minf,Cst x|Cst x,minf -> if (Z.lt_big_int x Z.zero) then pinf else (if (Z.gt_big_int x Z.zero) then minf else Z.zero)
    |pinf,Cst x|Cst x,pinf -> if (Z.gt_big_int x Z.zero) then pinf else (if (Z.lt_big_int x Z.zero) then minf else Z.zero)

let divbis a c =
    match a,c with
      |Cst x ,Cst y -> if (y=Z.zero) then (if Z.gt_big_int x Z.zero then pinf else (if (Z.lt_big_int x Z.zero) then minf else Z.zero)) else Z.div_big_int  x y
      | Cst x,minf | Cst,pinf -> Z.zero
      | pinf,Cst y -> (if (gt_big_int y Z.zero) then pinf else minf)
      | minf,Cst y -> (if (gt_big_int y Z.zero) then minf else pinf)
   
  
let rec rl f l def = match l with |[]->def |[z] -> z| z::zs -> f z (maxl f zs def)

  let maxval a c =
    match a,c with
    |Cst x, Cst y ->  if Z.gt_big_int x y then x else y
    |minf,x -> x
    |x,minf -> x
    |x,pinf-> pinf
    |pinf,x-> pinf

  let minval a c =
    match a,c with
    |Cst x, Cst y ->  if Z.lt_big_int x y then x else y
    |minf,x -> minf
    |x,minf -> minf
    |x,pinf-> x
    |pinf,x-> x

let join a b = match a,b with
  | BOT,x | x,BOT -> x
  | iv (a, b),iv (c, d) -> iv ((minval a c), (maxval c d))
  
  let meet a b = match a,b with
  | BOT,x | x,BOT -> BOT
  | iv (a, b),iv (c, d) -> iv ((maxval a c), (minval c d))
  


  (* arithmetic operations *)

  let neg = lift1 Z.neg

  let add = lift2 Z.add

  let sub = lift2 Z.sub

  let mul x y = 
	match x,y with
	| Bot,_|_,BOT -> BOT
        | iv (a,b),iv (c,d)-> iv (rl minval [mulbis a c;mulbis a d;mulbis b c;mulbis b d ],rl maxval [mulbis a c;mulbis a d;mulbis b c;mulbis b d ])

  let modu = lift2 Z.rem

  let div a b =
    join (div_bis a (meet b iv (Z.one,pinf))) (div_bis a (meet b iv (minf,Z.minus_one)))

  (* set-theoretic operations *)

  
  let gbis a c =
    match a,c with
    | x,y when x=y -> false
    |Cst x, Cst y ->  if Z.gt_big_int x y then true else false
    |minf,x -> false
    |x,minf -> true
    |x,pinf-> false
    |pinf,x-> true


  let lbis b d =
    match b,d with
    |x,y when (x=y) -> false
    |Cst x , Cst y ->  if Z.lt_big_int x y then true else false
    |minf,x-> true
    |x,minf -> false
    |x,pinf-> true
    |pinf,x-> false

  let eqbis a c = 
    match a,c with
    | x,x -> true
    |Cst x , Cst y ->  if Z.gt_big_int x y then true else false
    |minf,x-> false
    |x,minf -> true
    |x,pinf-> false
    |pinf,x-> true

  
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
  | iv a b, iv c d -> (
                        match 
  | _ -> false

  (* check the emptyness of the concretization *)
  let is_bottom a =
    a=BOT

  (* prints abstract element *)
  let print fmt x = match x with
  | BOT -> Format.fprintf fmt "bottom"
  | TOP -> Format.fprintf fmt "top"
  | Cst x -> Format.fprintf fmt "{%s}" (Z.to_string x)


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

    
