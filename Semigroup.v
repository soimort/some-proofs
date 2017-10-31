(* Semigroup *)

(** A semigroup is an algebraic structure ([S], [•]) consisting of:
    - a set [S].
    - a binary operation [•] on [S], which satisfies the associative property.
 *)

Parameter S : Set.

Parameter op : S -> S -> S.
Infix "•" := op (left associativity, at level 50): type_scope.

Axiom associativity : forall a b c, a • (b • c) = (a • b) • c.
