(* Partially ordered set *)

(** A poset is an algebraic structure ([S], [≤]) consisting of:
    - a set [S].
    - a binary relation [≤] over [S], which is reflexive, antisymmetric, and transitive.
 *)

Parameter S : Set.

(* Coercion for subset type of S *)
Parameter S' : Set.
Parameter inj_S'_S : S' -> S.
Axiom inj_S'_S_inj : forall x y : S', inj_S'_S x = inj_S'_S y -> x = y.
Coercion inj_S'_S : S' >-> S.

Parameter po : S' -> S' -> Prop.
Infix "≤" := po (left associativity, at level 50): type_scope.

Axiom po_reflexivity : forall a, a ≤ a.

Axiom po_antisymmetry : forall a b, a ≤ b /\ b ≤ a -> a = b.

Axiom po_transitivity : forall a b c, a ≤ b /\ b ≤ c -> a ≤ c.
