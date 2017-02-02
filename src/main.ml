(*
  Cours "Typage et Analyse Statique"
  Université Pierre et Marie Curie
  Antoine Miné 2015
*)


module ConcreteAnalysis =
  Interpreter.Interprete(Concrete_domain.Concrete)
    
module ConstantAnalysis =
  Interpreter.Interprete
    (Non_relational_domain.NonRelational
       (Constant_domain.Constants))
    
module IntervaleAnalysis =
  Interpreter.Interprete
    (Non_relational_domain.NonRelational
       (Intervale_domain.Intervals))

module ParityAnalysis =
  Interpreter.Interprete
    (Non_relational_domain.NonRelational
       (Parite_domain.Parity))


module ProduitAnalysis =
  Interpreter.Interprete
    (Non_relational_domain.NonRelational
       (Produitreduit.Produitreduit))


(* parse and print filename *)
let doit filename =
  let prog = File_parser.parse_file filename in
  Abstract_syntax_printer.print_prog Format.std_formatter prog

    
(* default action: print back the source *)
let eval_prog prog =
  Abstract_syntax_printer.print_prog Format.std_formatter prog

(* entry point *)
let main () =
  let action = ref eval_prog in
  let files = ref [] in
  (* parse arguments *)
  let ext = ref 0 in
  let unr = ref 0 in
  let ty = ref 0 in
  Arg.parse
    (* handle options *)
    ["-trace", Arg.Set Interpreter.trace, "";
     "-concrete", Arg.Unit (fun () -> action := ConcreteAnalysis.eval_prog !ty !unr !ext),"";
     "-constant", Arg.Unit (fun () -> action := ConstantAnalysis.eval_prog !ty !unr !ext),"";
     "-interval", Arg.Unit (fun () -> action := IntervaleAnalysis.eval_prog !ty !unr !ext),"";
     "-singlearray", Arg.Unit (fun () -> ext:=1),"";
     "-delay", Arg.Int (fun (n) -> unr:=n;ty:=1),"";
     "-unroll", Arg.Int (fun (n) -> unr:=n;ty:=2),"";
     "-reduit", Arg.Unit (fun () ->  action := ProduitAnalysis.eval_prog !ty !unr !ext),"";
      "-parity", Arg.Unit (fun () -> action := ParityAnalysis.eval_prog !ty !unr !ext),"";
   
     
   ]
    (* handle filenames *)
    (fun filename -> files := (!files)@[filename])
    "";
  List.iter
    (fun filename ->
      let prog = File_parser.parse_file filename in
      !action  prog
    )
    !files
    
let _ = main ()
