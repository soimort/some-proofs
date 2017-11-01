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

(* TODO: order-theoretic definition
   Is this actually a total order? *)
Parameter po : S -> S -> Prop.
Infix "≤" := po (left associativity, at level 50): type_scope.
Infix "≥" := po (left associativity, at level 50): type_scope.

(* The existence of infimum gives rise to a meet-semilattice. *)
Axiom infimum_existence : forall a b, a ≤ b <-> a = a • b.

(* The existence of supremum gives rise to a join-semilattice. *)
Axiom supremum_existence : forall a b, a ≥ b <-> a = a • b.
