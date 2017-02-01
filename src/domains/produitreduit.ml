(*
  Cours "Typage et Analyse Statique"
  Université Pierre et Marie Curie
  Antoine Miné 2015
*)

(* 
 prduitreduit domain
*)

open Abstract_syntax_tree
    open Value_domain

module I =
  
     Intervale_domain.Intervals

module P =

     Parite_domain.Parity



module Produitreduit =
  (struct
  
  (* types *)
  (* ***** *)
  
  (* type of abstract values *)
  type t = I.t *  P.t
   
  (* utilities *)
  (* ********* *)
 
  (*let print_v x = I.print_v (fst x);P.print_v (snd x)	*)	
  let reduce x =
    match (fst x,snd x) with
    | I.BOT,_|_,P.BOT -> I.BOT,P.BOT
    | I.Iv (x,y),P.Odd ->
     ( match (I.is_even x,I.is_even y) with
      |false,false -> I.Iv (x,y),P.Odd
      |true,true ->I.Iv(I.plus_one x,I.minus_one y),P.Odd
      |true,false ->I.Iv(I.plus_one x,y),P.Odd
      |false,true ->I.Iv(x,I.minus_one y),P.Odd)
        
            
    | I.Iv (x,y),P.Even ->
        ( match (I.is_even x,I.is_even y) with
      |true,true -> I.Iv (x,y),P.Even
      |false,false ->I.Iv(I.plus_one x,I.minus_one y),P.Even
      |false,true ->I.Iv(I.plus_one x,y),P.Even
      |true,false ->I.Iv(x,I.minus_one y),P.Even)
        
    | x,y -> x,y

      

  (* lift unary arithmetic operations, from integers to t *)
  let lift1 f x = reduce ((I.lift1 f (fst x)),P.lift1 f (snd x))
   
  (*let ouex a b = (a && (not b)) || ((not a) && b)*)
  
  (* lift binary arithmetic operations *)
  let lift2 f x y = reduce ((I.lift2 f (fst x) (fst y)),(P.lift2 f (snd x) (snd y)))
   
       
             
  (* interface implementation *)
  (* ************************ *)

  (* unrestricted value *)
  let top = reduce (I.top,P.top)

  (* bottom value *)
  let bottom = reduce (I.bottom,P.bottom)

  (* constant *)
  let const c = reduce (I.const c,P.const c)

  (* interval *)
  let rand x y = reduce (I.rand x y,P.rand x y)
      
  

  let join x y = reduce (I.join (fst x)  (fst y),P.join (snd x) (snd y))
  let meet x y = reduce (I.meet (fst x) (fst y),P.meet (snd x)  (snd y))

   let neg =  lift1 Z.neg

  let add =  lift2 Z.add

  let sub =  lift2 Z.sub


   let mul x y = reduce (I.mul (fst x) (fst y),P.mul (snd x) (snd y))
	
  let modu = lift2 Z.rem

  let div x y = reduce (I.div (fst x) (fst y),P.div (snd x) (snd y))
   
    

  (* set-theoretic operations *)


  
  (* needs to be implemented *)
  let widen x y = (I.widen (fst x) (fst y),P.widen (snd x) (snd y))
  


    
  (* comparison operations (filters) *)

  let eq x y =  let (x1,x2)= I.eq (fst x) (fst y)in
    let (y1,y2) =  P.eq (snd x) (snd y) in
    reduce (x1,y1), reduce (x2,y2)

  
  let neq x y=  let (x1,x2)= I.neq (fst x) (fst y)in
    let (y1,y2) =  P.neq (snd x) (snd y) in
    reduce (x1,y1), reduce (x2,y2)
  



   
let geq x y = let (x1,x2)= I.geq (fst x) (fst y)in
    let (y1,y2) =  P.geq (snd x) (snd y) in
    reduce (x1,y1), reduce (x2,y2)

let gt x y = let (x1,x2)= I.gt (fst x) (fst y)in
    let (y1,y2) =  P.gt (snd x) (snd y) in
  reduce (x1,y1), reduce (x2,y2)



  (* subset inclusion of concretizations *)
  let subset (x:t) (y:t) = ((I.subset (fst x) (fst y)) && (P.subset (snd x) (snd y)))
  (* check the emptyness of the concretization *)
  let is_bottom a =
    ((I.is_bottom (fst a)) && (P.is_bottom (snd a)))



  (* prints abstract element *)
  let print fmt x = I.print fmt (fst x);Format.fprintf fmt "2eme domaine "; P.print fmt (snd x)
  
  (* operator dispatch *)
        
  let unary x op = reduce ((I.unary (fst x) op), (P.unary (snd x) op))
 

  let binary x y op = reduce ((I.binary (fst x) (fst y) op),(P.binary (snd x) (snd y) op))

  let compare (x:t) (y:t) op =
    let (x1,x2) = (I.compare (fst x) (fst y) op) in
    let (y1,y2) = (P.compare (snd x) (snd y) op) in
     (reduce (x1,y1),reduce (x2,y2))
    
  let bwd_unary x op r = reduce ((I.bwd_unary (fst x) op (fst r)),(P.bwd_unary (snd x) op (snd r)))

        
  let bwd_binary x y op r =
    let (x1,x2) = (I.bwd_binary (fst x) (fst y) op (fst r)) in
    let (y1,y2) = (P.bwd_binary (snd x) (snd y) op (snd r)) in
     (reduce (x1,y1),reduce (x2,y2))



  let concrete e =
    let res = (I.concrete (fst e))
    in
    match (snd e) with
    |P.BOT -> []
    |P.TOP -> res
    |P.Even -> List.filter  (fun x -> if(x mod 2==0) then true else false) res
    |P.Odd -> List.filter  (fun x -> if(x mod 2==1) then true else false) res

       
end: VALUE_DOMAIN )

    
