(* De Morgan Algebra *)

(** A De Morgan algebra is an algebraic structure ([A], [∨], [∧], [¬]) consisting of:
    - a set [A].
    - three binary operations [∨], [∧] and [¬] on [A], such that
      - ([A], [∨], [∧]) is a bounded distributive lattice.
      - [¬] is a De Morgan involution.
 *)

Parameter A : Set.

Parameter O : A.
Parameter I : A.

Parameter join : A -> A -> A.
Infix "∨" := join (left associativity, at level 50): type_scope.

Parameter meet : A -> A -> A.
Infix "∧" := meet (left associativity, at level 50): type_scope.

Parameter involution : A -> A.
Notation "¬ x" := (involution x) (at level 50): type_scope.

Axiom join_commutativity : forall a b, a ∨ b = b ∨ a.
Axiom meet_commutativity : forall a b, a ∧ b = b ∧ a.

Axiom join_associativity : forall a b c, a ∨ (b ∨ c) = (a ∨ b) ∨ c.
Axiom meet_associativity : forall a b c, a ∧ (b ∧ c) = (a ∧ b) ∧ c.

Axiom join_absorptivity : forall a b, a ∨ (a ∧ b) = a.
Axiom meet_absorptivity : forall a b, a ∧ (a ∨ b) = a.

(* bounded lattice *)
Axiom join_identity_element_existence : forall a, a ∨ O = a /\ O ∨ a = a.
Axiom meet_identity_element_existence : forall a, a ∧ I = a /\ I ∧ a = a.

(* distributive lattice *)
Axiom left_distributivity : forall a b c, a ∨ (b ∧ c) = (a ∨ b) ∧ (a ∨ c).
Axiom right_distributivity: forall a b c, (a ∧ b) ∨ c = (a ∨ c) ∧ (b ∨ c).

(* De Morgan's laws *)
Axiom de_morgan_1 : forall a b, ¬(a ∧ b) = ¬a ∨ ¬b.
Axiom de_morgan_2 : forall a, ¬(¬a) = a.
