(* Lattice *)

(** A lattice is an algebraic structure ([L], [∨], [∧]) consisting of:
    - a set [L].
    - two binary operations [∨] and [∧] on [L], which satisfy the commutative, the associative and the absorptive properties.
 *)

Parameter L : Set.

Parameter join : L -> L -> L.
Infix "∨" := join (left associativity, at level 50): type_scope.

Parameter meet : L -> L -> L.
Infix "∧" := meet (left associativity, at level 50): type_scope.

Axiom join_commutativity : forall a b, a ∨ b = b ∨ a.
Axiom meet_commutativity : forall a b, a ∧ b = b ∧ a.

Axiom join_associativity : forall a b c, a ∨ (b ∨ c) = (a ∨ b) ∨ c.
Axiom meet_associativity : forall a b c, a ∧ (b ∧ c) = (a ∧ b) ∧ c.

Axiom join_absorptivity : forall a b, a ∨ (a ∧ b) = a.
Axiom meet_absorptivity : forall a b, a ∧ (a ∨ b) = a.

(* The idempotent properties follow from the absorptivity of join and meet:
   a ∨ a = a ∨ (a ∧ (a ∨ a)) = a *)
Theorem join_idempotency : forall a, a ∨ a = a.
Proof.
  intro a.
  pattern a at 2; rewrite <- meet_absorptivity with (b := a).
  apply join_absorptivity.
Qed.

Theorem meet_idempotency : forall a, a ∧ a = a.
Proof.
  intro a.
  pattern a at 2; rewrite <- join_absorptivity with (b := a).
  apply meet_absorptivity.
Qed.

(* TODO: order-theoretic definition *)
