(* Loop *)

(** A loop is an algebraic structure ([Q], [•]) consisting of:
    - a set [Q].
    - a binary operation [•] on [Q], which satisfies the Latin square property and has an identity element.

    A loop is just a quasigroup with an identity element.
 *)

Parameter Q : Set.

Parameter op : Q -> Q -> Q.
Infix "•" := op (left associativity, at level 50): type_scope.

Axiom left_latin_square_property :
  forall a b, exists x, a • x = b /\ (forall x', a • x' = b -> x' = x).

Axiom right_latin_square_property :
  forall a b, exists y, y • b = a /\ (forall y', y' • b = a -> y' = y).

Axiom identity_element_existence :
  exists e, forall a, a • e = a /\ e • a = a.
