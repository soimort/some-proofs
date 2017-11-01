(* Monoid *)

(** A monoid is an algebraic structure ([S], [•]) consisting of:
    - a set [S].
    - a binary operation [•] on [S], which satisfies the associative property.

    A monoid is just a semigroup with an identity element.
 *)

Parameter S : Set.

Parameter op : S -> S -> S.
Infix "•" := op (left associativity, at level 50): type_scope.

Axiom op_associativity : forall a b c, a • (b • c) = (a • b) • c.

Axiom identity_element_existence :
  exists e, forall a, a • e = a /\ e • a = a.
