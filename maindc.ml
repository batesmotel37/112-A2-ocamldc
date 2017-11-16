(* $Id: maindc.ml,v 1.4 2012-02-16 17:47:43-08 - - $ *)

include Scanner
include Bigint

open Bigint
open Printf
open Scanner

type stack_t = Bigint.bigint Stack.t
let push = Stack.push
let pop = Stack.pop

let aget = Array.get
let aset = Array.set
let amake = Array.make
let ord = Char.code

let ord thechar = int_of_char thechar
type binop_t = bigint -> bigint -> bigint

let print_number number = printf "%s\n%!" (string_of_bigint number)

let print_stackempty () = eprintf "dc: stack empty\n%!"

let symbol_table = amake 256 (false, zero)

let load sym = (
         let entry = aget symbol_table (ord sym)
         in match entry with
            | false, _ -> printf "register '%c' is empty\n%!" sym; 
                          false, zero
            | true, value -> true, value
      )

let store (sym, value) = (
         aset symbol_table (ord sym) (true, value);
         printf "%!"
      )

let executereg (thestack: stack_t) (oper: char) (reg: int) =
    try match oper with
        | 'l' -> let valid,loaded = (load (char_of_int reg))
                 in if valid then push loaded thestack
                 else printf "%!"
        | 's' -> store ((char_of_int reg), (pop thestack))
        | _   -> printf "0%o 0%o is unimplemented\n%!" (ord oper) reg
    with Stack.Empty -> print_stackempty()

let executebinop (thestack: stack_t) (oper: binop_t) =
    try let right = pop thestack
        in  try let left = pop thestack
                in  push (oper left right) thestack
            with Stack.Empty -> (print_stackempty ();
                                 push right thestack)
    with Stack.Empty -> print_stackempty ()

let execute (thestack: stack_t) (oper: char) =
    try match oper with
        | '+'  -> executebinop thestack Bigint.add
        | '-'  -> executebinop thestack Bigint.sub
        | '*'  -> executebinop thestack Bigint.mul
        | '/'  -> executebinop thestack Bigint.div
        | '%'  -> executebinop thestack Bigint.rem
        | '^'  -> executebinop thestack Bigint.pow
        | 'c'  -> Stack.clear thestack
        | 'd'  -> push (Stack.top thestack) thestack
        | 'f'  -> Stack.iter print_number thestack
        | 'l'  -> failwith "operator l scanned with no register"
        | 'p'  -> print_number (Stack.top thestack)
        | 's'  -> failwith "operator s scanned with no register"
        | '\n' -> ()
        | ' '  -> ()
        | _    -> printf "0%o is unimplemented\n%!" (ord oper)
    with Stack.Empty -> print_stackempty()

let toploop (thestack: stack_t) inputchannel =
    let scanbuf = Lexing.from_channel inputchannel in
    let rec toploop () = 
        try  let nexttoken = Scanner.scanner scanbuf
             in  (match nexttoken with
                 | Number number       -> push number thestack
                 | Regoper (oper, reg) -> executereg thestack oper reg
                 | Operator oper       -> execute thestack oper
                 );
             toploop ()
        with End_of_file -> printf "";(*"End_of_file\n%!";*)
    in  toploop ()

let readfiles () =
    let thestack : bigint Stack.t = Stack.create ()
    in  ((if Array.length Sys.argv > 1 
         then try  let thefile = open_in Sys.argv.(1)
                   in  toploop thestack thefile
              with Sys_error message -> (
                   printf "%s: %s\n%!" Sys.argv.(0) message;
                   exit 1));
        toploop thestack stdin)

let interact () =
    let thestack : bigint Stack.t = Stack.create ()
    in  toploop thestack stdin

let _ = if not !Sys.interactive then readfiles ()

