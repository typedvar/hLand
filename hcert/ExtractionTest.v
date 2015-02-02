Module Export Test.

Inductive tEV : Type :=
  | ev : tEV.

CoInductive tProgramTrace : Type :=
    | NextEv : tEV -> tProgramTrace -> tProgramTrace.

(** The [generateTrace] function, given a G-machine state,
    creates a program trace
*)

Definition stepFunc (e : tEV) : tEV :=
e.
    
CoFixpoint generateTrace (m : tEV) : tProgramTrace := 
    NextEv m (generateTrace (stepFunc m)).

End Test.

Extraction Language Haskell.

Recursive Extraction Test.