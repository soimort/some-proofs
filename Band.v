(* Band *)

(** A band is an algebraic structure ([S], [•]) consisting of:
    - a set [S].
    - a binary operation [•] on [S], which satisfies the associative and the idempotent properties.

    A band is just an idempotent semigroup.
 *)

Parameter S : Set.

Parameter op : S -> S -> S.
Infix "•" := op (left associativity, at level 50): type_scope.

Axiom op_associativity : forall a b c, a • (b • c) = (a • b) • c.

Axiom op_idempotence : forall a, a • a = a.
