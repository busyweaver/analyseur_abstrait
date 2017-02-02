(*
  Cours "Typage et Analyse Statique"
  Université Pierre et Marie Curie
  Antoine Miné 2015
*)

(* 
   The interval domain
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
    | BOT (* the set is empty (not reachable) *)
   
  (* utilities *)
  (* ********* *)

  let print_rest r = 
   match r with
	| Pinf -> "+inf"
	| Minf -> "-inf"
	| Cst x -> Z.to_string x

  
let print_v x = match x with
  | BOT ->  print_string "bottom\n"
  | Iv (r , s) -> let p1 = print_rest r in
		let p2 = print_rest s in
    print_string (  String.concat "" [
        "iv [" ; p1 ; ", "; p2 ;" ]\n"
      ] )			


  (* lift unary arithmetic operations, from integers to t *)
  let lift1 f x =
    match x with
    | BOT -> BOT
    | Iv (a,b) -> (
		match a,b with
        	|Cst x,Cst y -> Iv (Cst (f x),Cst (f y))
        	|Cst x,Pinf -> Iv (Cst (f x),Pinf)  
      		|Minf,Cst x ->Iv (Minf, Cst (f x))
        	|_ -> Iv (a,b)) 

  (*let ouex a b = (a && (not b)) || ((not a) && b)*)
  
  (* lift binary arithmetic operations *)
  let lift2 f x y =
     match x,y with
       | BOT,_|_,BOT -> BOT
       | Iv (a,b),Iv (c,d) ->(match a,b,c,d with
           |Minf,_,_,Pinf| _,Pinf,Minf,_| Minf,Pinf,_,_ | _,_,Minf,Pinf -> Iv(Minf,Pinf)
           |Minf,Cst b,_,Cst d| _,Cst b,Minf,Cst d -> Iv (Minf, Cst (f b d))
           |Cst a,Pinf,Cst c,_| Cst a,_,Cst c,Pinf -> Iv (Cst (f a c),Pinf)
           |Cst a,Cst b,Cst c,Cst d -> Iv (Cst (f a c),Cst (f b d))
           |_ -> BOT)
       
             
  (* interface implementation *)
  (* ************************ *)

  (* unrestricted value *)
  let top = Iv (Minf ,Pinf)

  (* bottom value *)
  let bottom = BOT

  (* constant *)
  let const c = Iv (Cst c ,Cst c)

  (* interval *)
  let rand x y =
    if x=y then Iv(Cst x ,Cst x)
    else (if x<y then Iv (Cst x,Cst y)
    else BOT)
      
  let mulbis a c =
    match a,c with
    |Cst x ,Cst y -> Cst (Z.mul x y) 
    |Minf,Cst x|Cst x,Minf -> if (Z.compare x Z.zero < 0) then Pinf else (if (Z.compare x Z.zero > 0) then Minf else Cst Z.zero)
    |Pinf,Cst x|Cst x,Pinf -> if (Z.compare x Z.zero > 0) then Pinf else (if (Z.compare x Z.zero < 0) then Minf else Cst Z.zero)
    |_ -> Minf(* we should not get this case.. maybe it is better to throw an exception*)


  let divaux a c =
    match a,c with
      |Cst x ,Cst y -> if (y=Z.zero) then (if Z.compare x Z.zero > 0 then Pinf else (if (Z.compare x Z.zero < 0) then Minf else Cst Z.zero)) else Cst (Z.ediv  x y)
      | Cst x,Minf | Cst x,Pinf -> Cst Z.zero
      | Pinf,Cst y -> (if (Z.compare y Z.zero > 0) then Pinf else Minf)
      | Minf,Cst y -> (if (Z.compare y Z.zero > 0) then Minf else Pinf)
      |_ -> Minf(* we should not get this case.. maybe it is better to throw an exception*)
  
 let gbis a c =
    match a,c with
    |x,y when (x=y) ->false
    |Cst x, Cst y ->  if Z.compare x y > 0 then true else false
    |Minf,_|_,Pinf -> false
    |Pinf,_|_,Minf -> true
 
    
let rec rl f l def = match l with |[]->def |[z] -> z| z::zs -> f z (rl f zs def)

  let maxval a b =
    match a,b with
    |Cst x, Cst y ->  if (Z.compare x y > 0) then Cst x else Cst y
    |Minf,x|x,Minf -> x
    |_,Pinf|Pinf,_-> Pinf

  let minval a b =
    match a,b with
    |Cst x, Cst y ->  if (Z.compare x y < 0) then Cst x else Cst y
    |Minf,_|_,Minf -> Minf
    |x,Pinf|Pinf,x-> x

  

  let join x y = 
                  (match x,y with
  | BOT,a | a,BOT -> a
  | Iv(a, b), Iv (c, d) -> Iv ((minval a c), (maxval b d)))
  
  let meet x y = match x,y with
  | BOT,_ | _,BOT -> BOT
  | Iv (a, b),Iv (c, d) -> if((gbis c b) || (gbis a d)) then BOT else Iv((maxval a c), (minval b d))

let divbis x y =
    match x,y with
    |BOT,_ | _,BOT -> BOT
    |Iv(a,b),Iv(c,d) -> Iv((minval (divaux a c) (divaux a d)) , (maxval (divaux b c) (divaux b d))) 
(*must be something like when(gbis c Z.one ) ->// But I don't really know what's wrong because it don't work *)


  (* arithmetic operations *)
  (*there is problems in neg. Redefinition requierd*)
  let neg = lift1 Z.neg

  let add = lift2 Z.add

  let sub = lift2 Z.sub


   let mul x y = 
	match x,y with
	| BOT,_|_,BOT -> BOT
        | Iv (a,b),Iv (c,d)-> Iv (rl minval [mulbis a c;mulbis a d;mulbis b c;mulbis b d ] Minf,rl maxval [mulbis a c;mulbis a d;mulbis b c;mulbis b d ] Minf)

  
  (* let mul x y =  *)
  (*       match x,y with *)
  (*       | BOT,_|_,BOT -> BOT *)
  (*       | Iv (a,b),Iv (c,d)-> Iv (rl minval [(mulbis a c);(mulbis a d); (mulbis b c); (mulbis b d) ] Pinf, rl maxval [(mulbis a c);(mulbis a d);(mulbis b c);(mulbis b d) ] Minf) *)

  let modu = lift2 Z.rem

  let div a b =
     join (divbis a (meet b (Iv (Cst Z.one,Pinf)))) (divbis a (meet b (Iv (Minf,Cst Z.minus_one))))
    

  (* set-theoretic operations *)


  let lbis b d =
    match b,d with
    |x,y when (x=y) -> false
    |Cst x , Cst y ->  if Z.compare x y < 0 then true else false
    |Minf,_|_,Pinf-> true
    |_,Minf|Pinf,_ -> false


  let eqbis a c = 
    match a,c with
    | x,y when (x=y)-> true
    |Cst x , Cst y ->  if Z.compare x y = 0 then true else false
    |Minf,_|_,Pinf-> false
    |_,Minf|Pinf,_ -> true

  let plus_one x =
    match x with
    |Pinf -> Pinf
    |Minf -> Minf
    |Cst a -> Cst (Z.add a Z.one)

  let minus_one x =
    match x with
    |Pinf -> Pinf
    |Minf -> Minf
    |Cst a -> Cst (Z.sub a Z.one)
  
  
  (* needs to be implemented *)
  let widen x y = 
     match x,y with
     |BOT,x|x,BOT -> x
     |Iv(a,b), Iv (c,d) when ((not (gbis a c)) && (not (lbis b d))) -> Iv(a,b)
     |Iv(a,b), Iv (c,d) when ((gbis a c) && (not (lbis b d)))  -> Iv(Minf,b)
     |Iv(a,b), Iv (c,d) when ((not (gbis a c)) && (lbis b d)) -> Iv(a,Pinf)
     |Iv(a,b), Iv (c,d) when ((gbis a c) && (lbis b d)) -> Iv(Minf,Pinf)
     |_ -> join x y

  


   let add_simple a b=
	match a,b with
    |Cst x,Minf|Minf,Cst x -> Minf
	|Pinf, Cst x|Cst x,Pinf -> Pinf
    |Cst x,Cst y -> Cst (Z.add x y)
    |_ -> failwith "Unhold in case add_simple operation!"

   let negbis a =
	match a with 
	|Cst x -> Cst (Z.neg x);
	|Minf -> Pinf
	|Pinf -> Minf

   let minus x y  = 
    match x,y with
      |x,BOT -> x
      |BOT,x ->BOT
    |Iv(a,b),Iv(c,d) when ((gbis c b) || (gbis a d)) -> Iv (a,b)
    |Iv(a,b),Iv(c,d) when ((lbis c a) && (gbis d b)) -> BOT
    |Iv(a,b),Iv(c,d) when (not(gbis c b)) -> Iv(a, (minus_one c))
    |Iv(a,b),Iv(c,d) when (not(gbis a d)) -> Iv(plus_one c, b)
	|_ -> failwith "Unhold case in minus operator!"

    
  (* comparison operations (filters) *)

  let eq a b =
	let m = meet a b in
   ((print_v m); m, m)
   
  let neq a b =
  	let z = meet a b in
  	  minus a z,minus b z

  
  let meet_strict x y=
  match x, y with 
  | BOT,_ | _,BOT -> BOT
  | Iv (a, b),Iv (c, d) -> if((gbis c b) || (gbis a d)) then BOT else Iv((plus_one (maxval a c)), (minus_one (minval b d)))

  let gt x y = 
                match x,y with

                |BOT,_ | _,BOT -> BOT,BOT
                |Iv(a,b),Iv(c,d) when (gbis c b) -> BOT,BOT
                |Iv(a,b),Iv(c,d) when (gbis a d) -> Iv(a,b),Iv(c,d)
                |Iv(a,b),Iv(c,d) when ((lbis a c) && (gbis b d)) ->Iv(plus_one c,b),Iv(c,d)
                |Iv(a,b),Iv(c,d) when ((lbis c a) && (gbis d b)) -> Iv(a,b),Iv(c,minus_one b)
                |Iv(a,b),Iv(c,d) when (not(gbis c b)) -> Iv(plus_one c,b),Iv(c,minus_one b)
                |Iv(a,b),Iv(c,d) when (not(gbis a d)) -> Iv(a,b),Iv(c,d) 
                |_ ,_-> x,y




   
let geq a b =
  let x = gt a b in
  let y = eq a b in
    join (fst x) (fst y),join (snd x) (snd y)
(*Seem not work as expected *)  
  
            

  (* subset inclusion of concretizations *)
  let subset a b = match a,b with
    | a,b when (a=b) -> true
    | BOT,_ | _,Iv (Minf,Pinf) -> true
    | _,BOT | Iv (Minf,Pinf), _ -> false
    | Iv (a , b), Iv (c , d) -> if ((gbis a c || eqbis a c) && (lbis b d || eqbis b d)) then true else false

  (* check the emptyness of the concretization *)
  let is_bottom a =
    a=BOT



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


  let concrete e =
    match e with
    |BOT -> []
    |Iv (a,b) ->
      match a,b with
      |Cst x,Cst y ->
        let (r,s) = (int_of_string (Z.to_string x),int_of_string (Z.to_string y)) in
        let rec f r s acc =
          
          if(r>s)
          then
            acc
          else
            f (r+1) s (r::acc)
        in
        (f r s [])
      |_,_ -> failwith "concrete not supported"
        
  let is_even x =
    match x with
    | Minf -> false
    | Pinf -> false
    | Cst y -> (if (Z.erem y (Z.of_string "2")== Z.one) then false else true)
       
      
end )

    
