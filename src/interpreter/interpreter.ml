(*
  Cours "Typage et Analyse Statique"
  Université Pierre et Marie Curie
  Antoine Miné 2015
*)


(* 
  Abstract interpreter by induction on the syntax.
  Parameterized by an abstract domain.
*)


open Abstract_syntax_tree
open Abstract_syntax_printer
open Domain


(* parameters *)
(* ********** *)


(* for debugging *)
let trace = ref false

(* widening delay *)
let widen_delay = ref 3

(* loop unrolling *)
let loop_unrolling = ref 3



(* utilities *)
(* ********* *)


(* print errors *)
let error ext s =
  Format.printf "%s: ERROR: %s@\n" (string_of_extent ext) s

let fatal_error ext s =
  Format.printf "%s: FATAL ERROR: %s@\n" (string_of_extent ext) s;
  exit 1



(* interpreter signature *)
(* ********************* *)


(* an interpreter only exports a single function, which does all the work *)
module type INTERPRETER = 
sig
  (* analysis of a program, given its abstract syntax tree *)
  val eval_prog: int->int->int->prog->unit
end



(* interpreter *)
(* *********** *)


(* the interpreter is parameterized by the choice of a domain D 
   of signature Domain.DOMAIN
 *)

module Interprete(D : DOMAIN) =
(struct

  (* abstract element representing a set of environments;
     given by the abstract domain
   *)
  type t = D.t

       
  (* utility function to reduce the compexity of testing boolean expressions;
     it handles the boolean operators &&, ||, ! internally, by induction
     on the syntax, and call the domain's function D.compare, to handle
     the arithmetic part

     if r=true, keep the states that may satisfy the expression;
     if r=false, keep the states that may falsify the expression
   *)
  let filter (a:t) (e:bool_expr ext) (r:bool) : t =

    (* recursive exploration of the expression *)
    let rec doit a (e,x) r = match e with

    (* boolean part, handled recursively *)
    | AST_bool_unary (AST_NOT, e) -> 
        doit a e (not r)
    | AST_bool_binary (AST_AND, e1, e2) ->
        (if r then D.meet else D.join) (doit a e1 r) (doit a e2 r)
    | AST_bool_binary (AST_OR, e1, e2) -> 
        (if r then D.join else D.meet) (doit a e1 r) (doit a e2 r)
    | AST_bool_const b ->
        if b = r then a else D.bottom ()
          
    (* arithmetic comparison part, handled by D *)
    | AST_compare (cmp, (e1,_), (e2,_)) ->
        (* utility function to negate the comparison, when r=false *)
        let inv = function
        | AST_EQUAL         -> AST_NOT_EQUAL
        | AST_NOT_EQUAL     -> AST_EQUAL
        | AST_LESS          -> AST_GREATER_EQUAL
        | AST_LESS_EQUAL    -> AST_GREATER
        | AST_GREATER       -> AST_LESS_EQUAL
        | AST_GREATER_EQUAL -> AST_LESS
        in
        let cmp = if r then cmp else inv cmp in
        D.compare a e1 cmp e2

    in
    doit a e r


      
  (* interprets a statement, by induction on the syntax *)
  let rec eval_stat (c:int) (n:int) (xt:int) (a:t) ((s,ext):stat ext) : t = (* evalue une instruction dans un environement donné *)

    let r = match s with    

    | AST_block (decl,inst) ->
        (* add the local variables *)
        let a =
          List.fold_left
            (fun a ((_,v,s1),_) -> let size = int_of_string s1 in let size2 = size in
             
              if(size==0)
              then
                D.add_var a v
              else
                let v = String.concat "" ["$";v] in
                (* type d extension*)
              if (xt==1)
              then (* extension with one stored value*)
                D.assign (D.add_var  (D.add_var a (String.concat "" [v;"[";"*";"]"])) v) v (AST_int_const (string_of_int (size-1),ext))
              else (*extension with independent values on indeces*)
                
                let rec f v size a =
                match size with
                |0 -> D.assign (D.add_var  a v) v (AST_int_const (string_of_int (size2-1),ext))
                |n-> f v (n-1) (D.add_var a (String.concat "" [v;"[";(string_of_int (size-1));"]"]))
                in
                 (f v size a)
                
            )  
            a decl
        in
        (* interpret the block recursively *)

        let a = List.fold_left (eval_stat c n xt) a inst in
        
        (* destroy the local variables *)
        List.fold_left
          (fun a ((_,v,s),_) -> (D.del_var a v))
          a decl
        
    | AST_assign ((i,_),(e,_)) ->
        (* assigment is delegated to the domain *)
               D.assign a i e

   | AST_assign_array ((i,_),(e1,_),(e2,_)) ->
        (* assigment is delegated to the domain *)
        D.assign_array  a (String.concat "" ["$"; i]) e1 e2
          
    | AST_if (e,s1,Some s2) ->
        (* compute both branches *)
        let t = eval_stat c n xt (filter a e true ) s1 in
        let f = eval_stat c n xt (filter a e false) s2 in
        (* then join *)
        D.join t f
    | AST_if (e,s1,None) ->
        (* compute both branches *)
        let t = eval_stat c n xt (filter a e true ) s1 in
        let f = filter a e false in
        (* then join *)
        D.join t f
          
    | AST_while (e,s) ->
      let rec fix  (x:t) c n : t =
     
        let app =
          if(c==1)
          then if (n>0)
            then D.join x (eval_stat c n xt (filter x e true) s)
            else D.widen x (eval_stat c n xt (filter x e true) s)
          else if(c==2)
          then if(n>0)
              then (eval_stat c n xt (filter x e true) s)
              else  D.widen x (eval_stat c n xt (filter x e true) s)
          else
            (* le cas classique on fait un widen*)
             D.widen x (eval_stat c n xt (filter x e true) s) 
        in
        let new_n =
          if(c==1 || c==2) then n-1
          else n
        in
          if D.subset app x then x
          else fix app c new_n

      in
        
      let inv = fix a c n 
      in
      (* and then filter by exit condition *)
      (Format.printf "fixpoint is  %a\n" D.print_all inv ;
      filter inv e false)
    (*inv*)

    | AST_assert e ->
        let nenv = filter a e false in
		if not(D.is_bottom nenv) then
		(error ext "Assertion can not be always approved"; filter a e true)
		else a
          
    | AST_print l ->
        (* print the current abstract environment *)
        let l' = List.map fst l in
        Format.printf "%s: %a@\n"
          (string_of_extent ext) (fun fmt v -> D.print fmt a v) l';
        (* then, return the original element unchanged *)
        a
          
    | AST_HALT ->
        (* after halt, there are no more environments *)
        D.bottom ()
          
    in
    
    (* tracing, useful for debugging *)
    if !trace then 
      Format.printf "stat trace: %s: %a@\n" 
        (string_of_extent ext) D.print_all r;
    r
      


  (* entry-point of the program analysis *)
  let rec eval_prog (c:int) (n:int) (xt:int) (l:prog)  : unit =
    (* simply analyze each statement in the program *)
    let _ = List.fold_left (eval_stat c n xt) (D.init()) l in
    (* nothing useful to return *)
    ()

      
end : INTERPRETER)
