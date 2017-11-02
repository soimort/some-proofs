(* Semiring *)

(** A semiring is an algebraic structure ([R], [➕], [•]) consisting of:
    - a set [R].
    - two binary operations [➕] and [•] on [R], such that
      - ([R], [➕]) is a commutative monoid with identity element 0.
      - ([R], [•]) is a monoid with identity element 1.
      - Multiplication left and right distributes over addition.
      - Multiplication by 0 annihilates [R].
 *)

Parameter R : Set.

Parameter O : R.
Parameter I : R.

Parameter add : R -> R -> R.
Infix "➕" := add (left associativity, at level 50): type_scope.

Parameter mult : R -> R -> R.
Infix "•" := mult (left associativity, at level 50): type_scope.

Axiom addition_associativity : forall a b c, a ➕ (b ➕ c) = (a ➕ b) ➕ c.

Axiom addition_identity_element_existence : forall a, a ➕ O = a.

Axiom addition_commutativity : forall a b, a ➕ b = b ➕ a.

Axiom multiplication_associativity : forall a b c, a • (b • c) = (a • b) • c.

Axiom multiplication_identity_element_existence : forall a, a • I = a /\ I • a = a.

Axiom left_distributivity : forall a b c, a • (b ➕ c) = (a • b) ➕ (a • c).
Axiom right_distributivity: forall a b c, (a ➕ b) • c = (a • c) ➕ (b • c).

Axiom annihilativity : forall a, a • O = O /\ O • a = O.
