(* Minimal HOL Light sanity check: prove a trivial theorem. *)
let HELLO_THM = prove(`T`, ITAUT_TAC);;
Printf.printf "hello: HOL Light is working\n";;
