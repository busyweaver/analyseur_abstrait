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


  (* lift unary arithmetic operations, from integers to t *)
  let lift1 f x = ((I.lift1 f (fst x)),P.lift1 f (snd x))
   
  (*let ouex a b = (a && (not b)) || ((not a) && b)*)
  
  (* lift binary arithmetic operations *)
  let lift2 f x y = ((I.lift2 f (fst x) (fst y)),(P.lift2 f (snd x) (snd y)))
   
       
             
  (* interface implementation *)
  (* ************************ *)

  (* unrestricted value *)
  let top = (I.top,P.top)

  (* bottom value *)
  let bottom = (I.bottom,P.bottom)

  (* constant *)
  let const c = (I.const c,P.const c)

  (* interval *)
  let rand x y = (I.rand x y,P.rand x y)
      
  

  let join x y = (I.join (fst x)  (fst y),P.join (snd x) (snd y))
  let meet x y = (I.meet (fst x) (fst y),P.meet (snd x)  (snd y))

   let neg = lift1 Z.neg

  let add = lift2 Z.add

  let sub = lift2 Z.sub


   let mul x y = (I.mul (fst x) (fst y),P.mul (snd x) (snd y))
	
  let modu = lift2 Z.rem

  let div x y = (I.div (fst x) (fst y),P.div (snd x) (snd y))
   
    

  (* set-theoretic operations *)


  
  (* needs to be implemented *)
  let widen x y = (I.widen (fst x) (fst y),P.widen (snd x) (snd y))
  


    
  (* comparison operations (filters) *)

  let eq x y = (I.eq (fst x) (fst y),P.eq (snd x) (snd y))
  let neq x y=(I.neq (fst x) (fst y),P.neq (snd x) (snd y))
  



   
let geq x y =(I.geq (fst x) (fst y),P.geq (snd x) (snd y))

let gt x y =(I.gt (fst x) (fst y),P.gt (snd x) (snd y))
  (* subset inclusion of concretizations *)
  let subset (x:t) (y:t) = ((I.subset (fst x) (fst y)) && (P.subset (snd x) (snd y)))
  (* check the emptyness of the concretization *)
  let is_bottom a =
    ((I.is_bottom (fst a)) && (P.is_bottom (snd a)))



  (* prints abstract element *)
  let print fmt x = I.print fmt (fst x);Format.fprintf fmt "2eme domaine "; P.print fmt (snd x)
  
  (* operator dispatch *)
        
  let unary x op = ((I.unary (fst x) op),(P.unary (snd x) op))
 

  let binary x y op = ((I.binary (fst x) (fst y) op),(P.binary (snd x) (snd y) op))

  let compare (x:t) (y:t) op =
    let (x1,x2) = (I.compare (fst x) (fst y) op) in
    let (y1,y2) = (P.compare (snd x) (snd y) op) in
    ((x1,y1),(x2,y2))
    
  let bwd_unary x op r = ((I.bwd_unary (fst x) op (fst r)),(P.bwd_unary (snd x) op (snd r)))

        
  let bwd_binary x y op r =
    let (x1,x2) = (I.bwd_binary (fst x) (fst y) op (fst r)) in
    let (y1,y2) = (P.bwd_binary (snd x) (snd y) op (snd r)) in
    ((x1,y1),(x2,y2))



  let concrete e =
    let res = (I.concrete (fst e))
    in
    match (snd e) with
    |P.BOT -> []
    |P.TOP -> res
    |P.Even -> List.filter  (fun x -> if(x mod 2==0) then true else false) res
    |P.Odd -> List.filter  (fun x -> if(x mod 2==1) then true else false) res

       
end: VALUE_DOMAIN )

    
