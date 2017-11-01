(* Quasigroup *)

(** A quasigroup is an algebraic structure ([Q], [•]) consisting of:
    - a set [Q].
    - a binary operation [•] on [Q], which satisfies the Latin square property.
 *)

Parameter Q : Set.

Parameter op : Q -> Q -> Q.
Infix "•" := op (left associativity, at level 50): type_scope.

Axiom left_latin_square_property :
  forall a b, exists x, a • x = b /\ (forall x', a • x' = b -> x' = x).

Axiom right_latin_square_property :
  forall a b, exists y, y • b = a /\ (forall y', y' • b = a -> y' = y).
