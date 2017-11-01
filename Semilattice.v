(* Semilattice *)

(** A semilattice is an algebraic structure ([S], [•]) consisting of:
    - a set [S].
    - a binary operation [•] on [S], which satisfies the commutative, the associative and the idempotent properties.

    A semilattice is just a commutative band, i.e., a commutative idempotent semigroup.
 *)

Parameter S : Set.

Parameter op : S -> S -> S.
Infix "•" := op (left associativity, at level 50): type_scope.

Axiom op_commutativity : forall a b, a • b = b • a.

Axiom op_associativity : forall a b c, a • (b • c) = (a • b) • c.

Axiom op_idempotency : forall a, a • a = a.
