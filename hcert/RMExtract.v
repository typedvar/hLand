Require Import VUtils.
Require Import RM.

(** Finally, we extract this machine to a Haskell implementation. The extracted
implementation is then packaged into an executable. 
*)

Extraction Language Haskell.

Recursive Extraction RM.