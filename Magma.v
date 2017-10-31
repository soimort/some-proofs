(* Magma *)

(** A magma is an algebraic structure ([M], [•]) consisting of:
    - a set [M].
    - a binary operation [•] on [M].
 *)

Parameter M : Set.

Parameter op : M -> M -> M.
Infix "•" := op (left associativity, at level 50): type_scope.

(* No more axioms. *)
