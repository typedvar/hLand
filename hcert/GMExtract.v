(** Finally, we extract this machine to a Haskell implementation. The extracted
implementation is then packaged into an executable. 
*)

Require Import GM.

Extraction Language Haskell.

Recursive Extraction GMImpl.