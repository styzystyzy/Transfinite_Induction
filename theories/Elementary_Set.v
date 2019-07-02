Require Export Elementary_Logic.

Module ElementSet.

(* ELEMENTARY ALGEBRA OF CLASSES *)

(* 2 Definition  x∪y = { z : z∈x or z∈y }. *)

Definition Union x y : Class := \{ λ z, z∈x \/ z∈y \}.

Notation "x ∪ y" := (Union x y) (at level 65, right associativity).

Hint Unfold Union : set.


(* 3 Definition  x∩y = { z : z∈x and z∈y }. *)

Definition Intersection x y : Class := \{ λ z, z∈x /\ z∈y \}.

Notation "x ∩ y" := (Intersection x y) (at level 60, right associativity).

Hint Unfold Intersection : set.


(* 4 Theorem  z∈x∪y if and only if z∈x or z∈y, and z∈x∩y if and only if
   z∈x and z∈y. *)

Theorem Theorem4 : forall (x y: Class) (z: Class),
  z∈x \/ z∈y <-> z ∈ (x ∪ y).
Proof.
  intros.
  split; intros.
  - apply Axiom_Scheme; split.
    + destruct H; Ens.
    + apply H.
  - apply Axiom_Scheme in H.
    apply H.
Qed.

Theorem Theorem4' : forall x y z, z∈x /\ z∈y <-> z∈(x∩y).
Proof.
  intros; unfold Intersection; split; intros.
  - apply Axiom_Scheme; split; Ens; exists y; apply H.
  - apply Axiom_Scheme in H; apply H.
Qed.

Hint Resolve Theorem4 Theorem4' : set.


(* 5 Theorem  x∪x=x and x∩x=x. *)

Theorem Theorem5 : forall x, x ∪ x = x.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Theorem4 in H; tauto.
  - apply Theorem4; tauto.
Qed.

Theorem Theorem5' : forall x, x ∩ x = x.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Theorem4' in H; tauto.
  - apply Theorem4'; tauto.
Qed.

Hint Rewrite Theorem5 Theorem5' : set.


(* 6 Theorem  x∪y=y∪x and x∩y=y∩x. *)

Theorem Theorem6 : forall x y, x ∪ y = y ∪ x.
Proof.
  intros; apply Axiom_Extent; split; intro.
  - apply Theorem4 in H; apply Theorem4; tauto.
  - apply Theorem4 in H; apply Theorem4; tauto.
Qed.

Theorem Theorem6' : forall x y, x ∩ y = y ∩ x.
Proof.
  intros; apply Axiom_Extent; split; intro.
  - apply Theorem4' in H; apply Theorem4'; tauto.
  - apply Theorem4' in H; apply Theorem4'; tauto.
Qed.

Hint Rewrite Theorem6 Theorem6' : set.


(* 7 Theorem  (x∪y)∪z=x∪(y∪z) and (x∩y)∩z=x∩(y∩z). *)

Theorem Theorem7 : forall x y z, (x ∪ y) ∪ z = x ∪ (y ∪ z).
Proof.
  intros; apply Axiom_Extent; split; intro.
  - apply Theorem4 in H; apply Theorem4; destruct H.
    + apply Theorem4 in H; destruct H; try tauto.
      right; apply Theorem4; auto.
    + right; apply Theorem4; auto.
  - apply Theorem4 in H; apply Theorem4; destruct H.
    + left; apply Theorem4; auto.
    + apply Theorem4 in H; destruct H; try tauto.
      left; apply Theorem4; tauto.
Qed.

Theorem Theorem7' : forall x y z, (x ∩ y) ∩ z = x ∩ (y ∩ z).
Proof.
  intros; apply Axiom_Extent; split; intro.
  - repeat (apply Theorem4' in H; destruct H).
    apply Theorem4'; split; auto; apply Theorem4'; auto.
  - apply Theorem4' in H; destruct H; apply Theorem4'.
    apply Theorem4' in H0; destruct H0; split; auto.
    apply Theorem4'; split; auto.
Qed.

Hint Rewrite Theorem7 Theorem7' : set.


(* 8 Theorem  x∩(y∪z)=(x∩y)∪(x∩z) and x∪(y∩z)=(x∪y)∩(x∪z). *)

Theorem Theorem8 : forall x y z, x ∩ (y ∪ z) = (x ∩ y) ∪ (x ∩ z).
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Theorem4; apply Theorem4' in H; destruct H.
    apply Theorem4 in H0; destruct H0.
    + left; apply Theorem4'; split; auto.
    + right; apply Theorem4'; split; auto.
  - apply Theorem4 in H; apply Theorem4'; destruct H.
    + apply Theorem4' in H; destruct H; split; auto.
      apply Theorem4; left; auto.
    + apply Theorem4' in H; destruct H; split; auto.
      apply Theorem4; right; auto.
Qed.


Theorem Theorem8' : forall x y z, x ∪ (y ∩ z) = (x ∪ y) ∩ (x ∪ z).
Proof.
  intros; apply Axiom_Extent; split; intro.
  - apply Theorem4'; apply Theorem4 in H.
    destruct H; split; try apply Theorem4; auto.
    + apply Theorem4' in H; tauto.
    + apply Theorem4' in H; tauto.
  - apply Theorem4; apply Theorem4' in H; destruct H.
    apply Theorem4 in H; apply Theorem4 in H0.
    destruct H, H0; auto; right; apply Theorem4'; auto.
Qed.

Hint Rewrite Theorem8 Theorem8' : set.


(* 9 Definition  x∉y if and only if it is false that x∈y. *)

Definition NotIn x y : Prop := ~ x∈y.

Notation "x ∉ y" := (NotIn x y) (at level 10).

Hint Unfold NotIn : set.


(* 10 Definition  ¬x = { y : y ∉ x }. *)

Definition Complement x : Class := \{λ y, y ∉ x \}.

Notation "¬ x" := (Complement x) (at level 5, right associativity).

Hint Unfold Complement : set.


(* 11 Theorem  ¬ (¬ x) = x *)

Theorem Theorem11: forall x, ¬ (¬ x) = x.
Proof.
  intros; apply Axiom_Extent; split; intro.
  - apply Axiom_Scheme in H; unfold NotIn in H; destruct H.
    assert (z ∈ ¬ x <-> Ensemble z /\ z∉x ).
    { split; intros.
      - apply Axiom_Scheme in H1; auto.
      - apply Axiom_Scheme; auto. }
    apply definition_not in H1; auto.
    apply not_and_or in H1; destruct H1; tauto.
  - apply Axiom_Scheme; split; Ens; unfold NotIn; intro.
    apply Axiom_Scheme in H0; destruct H0; contradiction.
Qed.

Hint Rewrite Theorem11 : set.


(* 12 Theorem (De Morgan)  ¬(x∪y)=(¬x)∩(¬y) and ¬(x∩y)=(¬x)∪(¬y). *)

Theorem Theorem12 : forall x y, ¬ (x ∪ y) = (¬ x) ∩ (¬ y).
Proof.
  intros; generalize (Theorem4 x y); intros.
  apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme in H0; destruct H0; unfold NotIn in H1.
    apply definition_not with (B:= z∈x \/ z∈y ) in H1.
    + apply not_or_and in H1; apply Theorem4'; split.
      * apply Axiom_Scheme; split; auto; unfold NotIn; tauto.
      * apply Axiom_Scheme; split; auto; unfold NotIn; tauto.
    + split; apply H.
  - apply Theorem4' in H0; destruct H0.
    apply Axiom_Scheme in H0; apply Axiom_Scheme in H1.
    apply Axiom_Scheme; split; try tauto.
    destruct H0, H1; unfold NotIn in H2,H3; unfold NotIn.
    apply definition_not with (A:= z∈x \/ z∈y ); auto.
    apply and_not_or; split; auto.
Qed.

Theorem Theorem12' : forall x y, ¬ (x ∩ y) = (¬ x) ∪ (¬ y).
Proof.
  intros; generalize (Theorem4' x y); intros.
  apply Axiom_Extent; split; intro.
  - apply Axiom_Scheme in H0; unfold NotIn in H0; destruct H0.
    apply definition_not with (B:= z∈x /\ z∈y) in H1.
    + apply Theorem4; apply not_and_or in H1; destruct H1.
      * left; apply Axiom_Scheme; split; auto.
      * right; apply Axiom_Scheme; split; auto.
    + split; apply H.
  - apply Axiom_Scheme; split; Ens.
    unfold NotIn; apply definition_not with (A:= z∈x /\ z∈y); auto.
    apply or_not_and; apply Theorem4 in H0; destruct H0.
    + apply Axiom_Scheme in H0; unfold NotIn in H0; tauto.
    + apply Axiom_Scheme in H0; unfold NotIn in H0; tauto.
Qed.

Hint Rewrite Theorem12 Theorem12' : set.


(* 13 Definition  x~y = x ∩ (¬ y). *)

Definition Difference x y : Class := x ∩ (¬ y).

Notation "x ~ y" := (Difference x y) (at level 50, left associativity).

Hint Unfold Difference : set.


(* 14 Theorem  x ∩ (y~z) = (x∩y) ~ z. *)

Theorem Theorem14 : forall x y z, x ∩ (y ~ z) = (x ∩ y) ~ z.
Proof.
  intros; unfold Difference; rewrite Theorem7'; auto.
Qed.

Hint Rewrite Theorem14 : set.


(* Definition (85)  x≠y if and only if it is false that x=y. *)

Definition Inequality (x y: Class) : Prop := ~ (x = y).

Notation "x ≠ y" := (Inequality x y) (at level 70).

Corollary Property_Ineq : forall x y, (x ≠ y) <-> (y ≠ x).
Proof.
 intros; split; intros; intro; apply H; auto.
Qed.

Hint Unfold Inequality: set.
Hint Resolve Property_Ineq: set.


(* 15 Definition  Φ = { x : x ≠ x }. *)

Definition Φ : Class := \{λ x, x ≠ x \}.

Hint Unfold Φ : set.


(* 16 Theorem  x ∉ Φ. *)

Theorem Theorem16 : forall x, x ∉ Φ.
Proof.
  intros; unfold NotIn; intro.
  apply Axiom_Scheme in H; destruct H; contradiction.
Qed.

Hint Resolve Theorem16 : set. 


(* 17 Theorem  Φ ∪ x = x and Φ ∩ x = Φ. *)

Theorem Theorem17 : forall x, Φ ∪ x = x.
Proof.
  intros; apply Axiom_Extent; split; intro.
  - apply Theorem4 in H; destruct H; try tauto.
    generalize (Theorem16 z); contradiction.
  - apply Theorem4; tauto.
Qed.

Theorem Theorem17' : forall x, Φ ∩ x = Φ.
Proof.
  intros; apply Axiom_Extent; split; intro.
  - apply Theorem4' in H; destruct H; auto.
  - generalize (Theorem16 z); contradiction.
Qed.

Hint Rewrite Theorem17 Theorem17' : set.


(* 18 Definition  μ = { x : x = x }. *)

Definition μ : Class := \{ λ x, x = x \}.

Corollary Property_μ : forall x, x ∪ (¬ x) = μ.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme; split; Ens.
  - apply Axiom_Scheme in H; destruct H; apply Theorem4.
    generalize (classic (z∈x)); intros; destruct H1; try tauto.
    right; apply Axiom_Scheme; split; auto.
Qed.

Hint Unfold μ : set.
Hint Rewrite Property_μ : set.


(* 19 Theorem  x∈μ if and only if x is a set.  *)

Theorem Theorem19 : forall x, x ∈ μ <-> Ensemble x.
Proof.
  intros; split; intro.
  - apply Axiom_Scheme in H; destruct H; tauto.
  - apply Axiom_Scheme; split; auto.
Qed.

Hint Resolve Theorem19 : set.


(* 20 Theorem  x ∪ μ = μ and x ∩ μ = x. *)

Theorem Theorem20 : forall x, x ∪ μ = μ.
Proof.
  intros; apply Axiom_Extent; split; intro.
  - apply Theorem4 in H; destruct H; try tauto.
    apply Theorem19; Ens.
  - apply Theorem4; tauto.
Qed.

Theorem Theorem20' : forall x, x ∩ μ = x.
Proof.
  intros; apply Axiom_Extent; split; intro.
  - apply Theorem4' in H; tauto.
  - apply Theorem4'; split; auto.
    apply Theorem19; Ens.
Qed.

Hint Rewrite Theorem20 Theorem20' : set.


(* 21 Theorem  ¬ Φ = μ and ¬ μ = Φ. *)

Theorem Theorem21 : ¬ Φ = μ.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Theorem19; Ens.
  - apply Theorem19 in H; apply Axiom_Scheme; split; auto.
    apply Theorem16; auto.
Qed.

Theorem Theorem21' : ¬ μ = Φ.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme in H; destruct H.
    apply Theorem19 in H; contradiction.
  - apply Axiom_Scheme in H; destruct H; contradiction.
Qed.

Hint Rewrite Theorem21 Theorem21' : set.


(* 22 Definition  ∩x = { z : for each y, if y∈x, then z∈y }. *)

Definition Element_I x : Class := \{ λ z, forall y, y ∈ x -> z ∈ y \}.

Notation "∩ x" := (Element_I x) (at level 66).

Hint Unfold Element_I : set.


(* 23 Definition  ∪x = { z : for some y, z∈y and y∈x }. *)

Definition Element_U x : Class := \{ λ z, exists y, z ∈ y /\ y ∈ x \}.

Notation "∪ x" := (Element_U x) (at level 66).

Hint Unfold Element_U : set.


(* 24 Theorem  ∩Φ = μ and ∪Φ = Φ. *)

Theorem Theorem24 : ∩ Φ = μ.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Theorem19; Ens.
  - apply Axiom_Scheme; apply Theorem19 in H; split; auto.
    intros; generalize (Theorem16 y); contradiction.
Qed.

Theorem Theorem24' : ∪ Φ = Φ.
Proof.
  intros; apply Axiom_Extent; split; intro.
  - apply Axiom_Scheme in H; destruct H, H0, H0.
    generalize (Theorem16 x); contradiction.
  - generalize (Theorem16 z); contradiction.
Qed.

Hint Rewrite Theorem24 Theorem24' : set. 


(* 25 Definition  x ⊂ y iff for each z, if z∈x, then z∈y. *)

Definition Subclass x y : Prop := forall z, z∈x -> z∈y.

Notation "x ⊂ y" := (Subclass x y) (at level 70).

Hint Unfold Subclass : set.


(* 26 Theorem  Φ ⊂ x and x ⊂ μ. *)

Theorem Theorem26 : forall x, Φ ⊂ x.
Proof.
  intros; unfold Subclass; intros.
  generalize (Theorem16 z); contradiction.
Qed.

Theorem Theorem26' : forall x, x ⊂ μ.
Proof.
  intros; unfold Subclass; intros; apply Theorem19; Ens.
Qed.

Hint Resolve Theorem26 Theorem26' : set.


(* 27 Theorem  x=y iff x⊂y and y⊂x. *)

Theorem Theorem27 : forall x y, (x ⊂ y /\ y ⊂ x) <-> x=y.
Proof.
  intros; split; intros.
  - destruct H; intros; apply Axiom_Extent; split; auto.
  - rewrite <- H; split; unfold Subclass; auto.
Qed.

Hint Resolve Theorem27 : set.


(* 28 Theorem  If x⊂y and y⊂z, then x⊂z. *)

Theorem Theorem28 : forall x y z, x ⊂ y /\ y ⊂ z -> x ⊂ z.
Proof.
  intros; destruct H; unfold Subclass; auto.
Qed.

Hint Resolve Theorem28 : set.


(* 29 Theorem  x⊂y iff x∪y = y. *)

Theorem Theorem29 : forall x y, x ∪ y = y <-> x ⊂ y.
Proof.
  intros; split; intros.
  - unfold Subclass; intros; apply Axiom_Extent with (z:=z) in H.
    apply H; apply Theorem4; tauto.
  - apply Axiom_Extent; split; intros.
    + apply Theorem4 in H0; destruct H0; auto.
    + apply Theorem4; tauto.
Qed.

Hint Resolve Theorem29 : set.


(* 30 Theorem  x⊂y iff x∩y = x. *)

Theorem Theorem30 : forall x y, x ∩ y = x <-> x ⊂ y.
Proof.
  intros; split; intros.
  - unfold Subclass; intros; apply Axiom_Extent with (z:=z) in H.
    apply H in H0; apply Theorem4' in H0; tauto.
  - apply Axiom_Extent; split; intros.
    + apply Theorem4' in H0; tauto.
    + apply Theorem4'; split; auto.
Qed.

Hint Resolve Theorem30 : set.


(* 31 Theorem  If x ⊂ y, then ∪x ⊂ ∪y and ∩y ⊂ ∩x. *)

Theorem Theorem31 : forall x y, x ⊂ y -> (∪x ⊂ ∪y) /\ (∩y ⊂ ∩x).
Proof.
  intros; split.
  - unfold Subclass; intros; apply Axiom_Scheme in H0; destruct H0.
    apply Axiom_Scheme; split; auto; intros; destruct H1.
    exists x0; split; unfold Subclass in H; destruct H1; auto.
  - unfold Subclass in H; unfold Subclass; intros.
    apply Axiom_Scheme in H0; destruct H0; apply Axiom_Scheme; split; auto.
Qed.

Hint Resolve Theorem31 : set.


(* 32 Theorem  If x∈y, then x ⊂ ∪y and ∩y ⊂ x. *)

Theorem Theorem32 : forall x y, x ∈ y -> (x ⊂ ∪y) /\ (∩y ⊂ x).
Proof.
  intros; split.
  - unfold Subclass; intros; apply Axiom_Scheme; split; Ens.
  - unfold Subclass; intros; apply Axiom_Scheme in H0.
    destruct H0; apply H1; auto.
Qed.

Hint Resolve Theorem32 : set.


(* Proper Subclass *)

Definition ProperSubclass x y : Prop := x ⊂ y /\ x ≠ y.

Notation "x ⊊ y" := (ProperSubclass x y) (at level 70).

Corollary Property_ProperSubclass : forall (x y: Class),
  x ⊂ y -> (x ⊊ y) \/ x = y.
Proof.
  intros.
  generalize (classic (x = y)); intros.
  destruct H0; auto.
  left; unfold ProperSubclass; auto.
Qed.

Corollary Property_ProperSubclass' : forall (x y: Class),
  x ⊊ y -> exists z, z ∈ y /\ z ∉ x.
Proof.
  intros.
  unfold ProperSubclass in H; destruct H.
  generalize (Theorem27 x y); intros.
  apply definition_not with (B:= (x ⊂ y /\ y ⊂ x)) in H0; try tauto.
  apply not_and_or in H0; destruct H0; try tauto.
  unfold Subclass in H0; apply not_all_ex_not in H0; destruct H0.
  apply imply_to_and in H0; Ens.
Qed.

Hint Unfold ProperSubclass : set.
Hint Resolve Property_ProperSubclass Property_ProperSubclass' : set.


(* Property_Φ *)

Lemma Property_Φ : forall x y, y ⊂ x -> x ~ y = Φ <-> x = y.
Proof.
  intros; split; intros.
  - apply Property_ProperSubclass in H; destruct H; auto.
    apply Property_ProperSubclass' in H; destruct H as [z H], H.
    assert (z ∈ (x ~ y)).
    { unfold Difference; apply Theorem4'; split; auto.
      unfold Complement; apply Axiom_Scheme; split; Ens. }
    rewrite H0 in H2; generalize (Theorem16 z); intros.
    contradiction.
  - rewrite <- H0; apply Axiom_Extent; split; intros.
    + unfold Difference in H1; apply Theorem4' in H1.
      destruct H1; unfold Complement in H2.
      apply Axiom_Scheme in H2; destruct H2; contradiction.
    + generalize (Theorem16 z); intros; contradiction.
Qed.

Hint Resolve Property_Φ : set.


(* EXISTENCE OF SETS *)

(* III Axiom of subsets  If x is a set there is a set y such that for each z,
   if z⊂x, then z∈y. *)

Axiom Axiom_Subsets : forall (x: Class),
  Ensemble x -> exists y, Ensemble y /\ (forall z, z⊂x -> z∈y).

Hint Resolve Axiom_Subsets : set.


(* 33 Theorem  If x is a set and z⊂x, then z is a set. *)

Theorem Theorem33 : forall x z,
  Ensemble x -> z ⊂ x -> Ensemble z.
Proof.
  intros; apply Axiom_Subsets in H; destruct H.
  apply H in H0; Ens.
Qed.

Hint Resolve Theorem33 : set.


(* 34 Theorem  Φ = ∩μ and ∪μ = μ. *)

Theorem Theorem34 : Φ = ∩μ.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - generalize (Theorem16 z); contradiction.
  - apply Axiom_Scheme in H; destruct H; apply H0.
    apply Theorem19; generalize (Theorem26 z); intros.
    apply Theorem33 in H1; auto.
Qed.

Theorem Theorem34' : μ = ∪μ.
Proof.
  apply Axiom_Extent; split; intros.
  - apply Lemma_x in H; destruct H; apply Axiom_Scheme in H.
    destruct H; apply Axiom_Scheme; split; try auto.
    generalize (Axiom_Subsets z H); intros.
    destruct H2; destruct H2; exists x; split.
    + apply H3; unfold Subclass; auto.
    + apply Theorem19; auto.
  - apply Axiom_Scheme in H; destruct H; apply Theorem19; auto.
Qed.

Hint Rewrite Theorem34 Theorem34' : set.


(* 35 Theorem  If x ≠ Φ, then ∩x is a set. *)

Lemma Lemma35 : forall x, x ≠ Φ <-> exists z, z∈x.
Proof.
  intros; assert (x = Φ <-> ~ (exists y, y∈x)).
  { split; intros.
    - intro; destruct H0; rewrite H in H0.
      apply Axiom_Scheme in H0; destruct H0; case H1; auto.
    - apply Axiom_Extent; split; intros.
      + elim H; exists z; auto.
      + generalize (Theorem16 z); contradiction. }
  split; intros.
  - apply definition_not with (B:= ~(exists y, y∈x)) in H0; auto.
    apply NNPP in H0; destruct H0; exists x0; auto.
  - apply definition_not with (A:=(~ (exists y, y∈x))); auto.
    destruct H; split; auto.
Qed.

Theorem Theorem35 : forall x, x ≠ Φ -> Ensemble (∩x).
Proof.
  intros; apply Lemma35 in H; destruct H; AssE x0.
  generalize (Theorem32 x0 x H); intros.
  destruct H1; apply Theorem33 in H2; auto.
Qed.

Hint Resolve Lemma35 Theorem35 : set.


(* 36 Definition  pow(x) = { y : y ⊂ x }. *)

Definition PowerClass x : Class := \{ λ y, y ⊂ x \}.

Notation "pow( x )" := (PowerClass x) (at level 0, right associativity).

Hint Unfold PowerClass : set.


(* 37 Theorem  μ = pow(μ). *)

Theorem Theorem37 : μ = pow(μ).
Proof.
  apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme; split; Ens; apply Theorem26'.
  - apply Axiom_Scheme in H; destruct H; apply Theorem19; auto.
Qed.

Hint Rewrite Theorem37 : set.


(* 38 Theorem  If x is a set, then pow(x) is a set, and for each y, y ⊂ x iff
   y ∈ pow(x). *)

Theorem Theorem38 : forall x y,
  Ensemble x -> Ensemble pow(x) /\ (y ⊂ x <-> y ∈ pow(x)).
Proof.
  intros; split.
  - apply Axiom_Subsets in H; destruct H, H.
    assert (pow(x) ⊂ x0).
    { unfold Subclass; intros; apply Axiom_Scheme in H1.
      destruct H1; apply H0 in H2; auto. }
    apply Theorem33 in H1; auto.
  - split; intros.
    + apply Theorem33 with (z:=y) in H; auto.
      apply Axiom_Scheme; split; auto.
    + apply Axiom_Scheme in H0; apply H0.
Qed.

Hint Resolve Theorem38 : set.


(* 39 Theorem  μ is not a set. *)

(* Russell paradox *)

Lemma Lemma_N : ~ Ensemble \{ λ x, x ∉ x \}.
Proof.
  generalize (classic (\{ λ x, x ∉ x \} ∈ \{ λ x, x ∉ x \})).
  intros; destruct H.
  - double H; apply Axiom_Scheme in H; destruct H; contradiction.
  - intro; elim H; apply Axiom_Scheme; split; auto.
Qed.

Theorem Theorem39 : ~ Ensemble μ.
Proof.
  unfold not; generalize Lemma_N; intros.
  generalize (Theorem26' \{ λ x, x ∉ x \}); intros.
  apply Theorem33 in H1; auto.
Qed.

Hint Resolve Lemma_N Theorem39 : set.


(* 40 Definition  [x] = { z : if x∈μ, then z=x }. *)

Definition Singleton x : Class := \{ λ z, x∈μ -> z=x \}.

Notation "[ x ]" := (Singleton x) (at level 0, right associativity).

Hint Unfold Singleton : set.


(* 41 Theorem  If x is a set, for each y, y∈[x] iff y=x. *)

Theorem Theorem41 : forall x, Ensemble x -> (forall y, y∈[x] <-> y=x).
Proof.
  intros; split; intros.
  - apply Axiom_Scheme in H0; destruct H0; apply H1.
    apply Theorem19 in H; auto.
  - apply Axiom_Scheme; split; intros; auto.
    rewrite <- H0 in H; auto.
Qed.

Hint Resolve Theorem41 : set.


(* 42 Theorem  If x is a set, then [x] is a set. *)

Theorem Theorem42 : forall x, Ensemble x -> Ensemble [x].
Proof.
  intros; double H; apply Theorem33 with (x:= pow(x)).
  - apply Theorem38 with (y:=x) in H0; destruct H0; auto.
  - unfold Subclass; intros.
    apply Theorem38 with (y:=z) in H0; destruct H0.
    apply H2; apply Axiom_Scheme in H1; destruct H1.
    apply Theorem19 in H; apply H3 in H.
    rewrite H; unfold Subclass; auto.
Qed.

Hint Resolve Theorem42 : set.


(* 43 Theorem  [x] = μ if and only if x is not a set. *)

Theorem Theorem43 : forall x, [x] = μ <-> ~ Ensemble x.
Proof.
  split; intros.
  - unfold not; intros; apply Theorem42 in H0.
    rewrite H in H0; generalize Theorem39; contradiction.
  - generalize (Theorem19 x); intros.
    apply definition_not with (B:= x∈μ) in H; try tauto.
    apply Axiom_Extent; split; intros.
    * apply Axiom_Scheme in H1; destruct H1; apply Theorem19; auto.
    * apply Axiom_Scheme; split; try contradiction.
      apply Theorem19 in H1; auto.
Qed.

Hint Rewrite Theorem43 : set.


(* 42' Theorem  If [x] is a set, then x is a set. *)

Theorem Theorem42' : forall x, Ensemble [x] -> Ensemble x.
Proof.
  intros.
  generalize (classic (Ensemble x)); intros.
  destruct H0; auto; generalize (Theorem39); intros.
  apply Theorem43 in H0; auto.
  rewrite H0 in H; contradiction.
Qed.

Hint Resolve Theorem42' : set.


(* 44 Theorem  If x is a set, then ∩[x] = x and ∪[x] = x; if x is not a set,
   then ∩[x] = Φ and ∪[x] = μ. *)

Theorem Theorem44 : forall x, Ensemble x -> ∩[x] = x /\ ∪[x] = x.
Proof.
  intros; generalize (Theorem41 x H); intros.
  split; apply Axiom_Extent.
  - split; intros.
    + apply Axiom_Scheme in H1; destruct H1; apply H2; apply H0; auto.
    + apply Axiom_Scheme; split; Ens; intros.
      apply H0 in H2; rewrite H2; auto.
  - split; intros.
    + apply Axiom_Scheme in H1; destruct H1, H2, H2.
      unfold Singleton in H3; apply Axiom_Scheme in H3; destruct H3.
      rewrite H4 in H2; auto; apply Theorem19; auto.
    + apply Axiom_Scheme; split; Ens; exists x; split; auto.
      unfold Singleton; apply Axiom_Scheme; auto.
Qed.

Theorem Theorem44' : forall x, ~ Ensemble x -> ∩[x] = Φ /\ ∪[x] = μ.
Proof.
  intros; apply Theorem43 in H; split; rewrite H.
  - rewrite Theorem34; auto.
  - rewrite <- Theorem34'; auto.
Qed.

Hint Resolve Theorem44 Theorem44' : set.


(* IV Axiom of union  If x is a set and y is a set so is x∪y. *)

Axiom Axiom_Union : forall (x y: Class),
  Ensemble x /\ Ensemble y -> Ensemble (x∪y).

Corollary Axiom_Union': forall x y,
  Ensemble (x∪y) -> Ensemble x /\ Ensemble y.
Proof.
  intros; split.
  - assert (x ⊂ (x∪y)).
    { unfold Subclass; intros; apply Theorem4; tauto. }
    apply Theorem33 in H0; auto.
  - assert (y ⊂ (x∪y)).
    { unfold Subclass; intros; apply Theorem4; tauto. }
    apply Theorem33 in H0; auto.
Qed.

Hint Resolve Axiom_Union Axiom_Union' : set.


(* 45 Definition  [x|y] = [x] ∪ [y]. *)

Definition Unordered x y : Class := [x]∪[y].

Notation "[ x | y ]" := (Unordered x y) (at level 0).

Hint Unfold Unordered : set.


(* 46 Theorem  If x is a set and y is a set, then [x|y] is a set and z∈[x|y]
   iff z=x or z=y; [x|y] = μ iff x is not a set or y is not a set. *)

Theorem Theorem46 : forall x y z,
  Ensemble x /\ Ensemble y -> Ensemble [x|y] /\ (z∈[x|y] <-> (z=x \/ z=y)).
Proof.
  split; intros; destruct H.
  - apply Theorem42 in H; apply Theorem42 in H0; apply Axiom_Union; auto.
  - split; intros.
    + apply Axiom_Scheme in H1; destruct H1.
      destruct H2; apply Axiom_Scheme in H2; destruct H2.
      * left; apply H3; apply Theorem19; auto.
      * right; apply H3; apply Theorem19; auto.
    + apply Axiom_Scheme; split.
      * destruct H1; try rewrite <- H1 in H; auto.
        rewrite <- H1 in H0; auto.
      * destruct H1.
        -- left; apply Axiom_Scheme; split; rewrite <- H1 in H; auto.
        -- right; apply Axiom_Scheme; split; rewrite <- H1 in H0; auto.
Qed.

Theorem Theorem46' : forall x y, [x|y] = μ <-> ~ Ensemble x \/ ~ Ensemble y.
Proof.
  unfold Unordered; split; intros.
  - generalize (Theorem43 ([x] ∪ [y])); intros.
    destruct H0; rewrite H in H0.
    assert ([μ] = μ); try apply Theorem43; try apply Theorem39.
    apply H0 in H2; rewrite <- H in H2.
    assert (Ensemble([x]∪[y]) <-> Ensemble [x] /\ Ensemble [y]).
    { split; try apply Axiom_Union; try apply Axiom_Union'. }
    apply definition_not in H3; auto.
    generalize (not_and_or (Ensemble [x]) (Ensemble [y])); intros.
    apply H4 in H3; destruct H3.
    + assert (Ensemble [x] <-> Ensemble x).
      { split; try apply Theorem42'; try apply Theorem42; auto. }
      apply definition_not in H5; auto.
    + assert (Ensemble [y] <-> Ensemble y).
      { split; try apply Theorem42'; try apply Theorem42; auto. }
      apply definition_not in H5; auto.
  - destruct H; apply Theorem43 in H; rewrite H; try apply Theorem20.
    generalize (Theorem6 μ [y]); intros; rewrite H0; apply Theorem20.
Qed.

Hint Resolve Theorem46 Theorem46' : set.


(* 47 Theorem  If x and y are sets, then ∩[x|y] = x ∩ y and ∪[x|y] = x ∪ y;
   if either x or y is not a set, then ∩[x|y] = Φ and ∪[x|y] = μ. *)

Theorem Theorem47 : forall x y,
  Ensemble x /\ Ensemble y -> (∩[x|y] = x ∩ y) /\ (∪[x|y] = x ∪ y).
Proof.
  intros; split; apply Axiom_Extent; intros.
  - split; intros.
    + apply Theorem4'.
      split; apply Axiom_Scheme in H0; destruct H0; apply H1; apply Theorem4.
      * left; apply Axiom_Scheme; split; try apply H; auto.
      * right; apply Axiom_Scheme; split; try apply H; auto.
    + apply Theorem4' in H0; destruct H0.
      apply Axiom_Scheme; split; intros; try AssE z.
      apply Theorem4 in H2; destruct H2.
      * apply Axiom_Scheme in H2; destruct H2; destruct H.
        apply Theorem19 in H; apply H4 in H; rewrite H; auto.
      * apply Axiom_Scheme in H2; destruct H2; destruct H.
        apply Theorem19 in H5; apply H4 in H5; rewrite H5; auto.
  - split; intros.
    + apply Axiom_Scheme in H0; destruct H0; destruct H1; destruct H1.
      apply Theorem4 in H2; apply Theorem4.
      destruct H2; apply Axiom_Scheme in H2; destruct H2.
      * left; destruct H; apply Theorem19 in H.
        apply H3 in H; rewrite H in H1; auto.
      * right; destruct H; apply Theorem19 in H4.
        apply H3 in H4; rewrite H4 in H1; auto.
    + apply Theorem4 in H0; apply Axiom_Scheme.
      split; destruct H0; try AssE z.
      * exists x; split; auto; apply Theorem4; left.
        apply Axiom_Scheme; split; try apply H; trivial.
      * exists y; split; auto; apply Theorem4; right.
        apply Axiom_Scheme; split; try apply H; trivial.
Qed.

Theorem Theorem47' : forall x y,
  ~ Ensemble x \/ ~ Ensemble y -> (∩[x|y] = Φ) /\ (∪[x|y] = μ).
Proof.
  intros; split; apply Theorem46' in H; rewrite H.
  - rewrite Theorem34; auto.
  - rewrite <- Theorem34'; auto.
Qed.

Hint Resolve Theorem47 Theorem47' : set.


(* ORDERED PAIRS: RELATIONS *)

(* 48 Definition  [x,y] = [[x]|[x|y]] *)

Definition Ordered x y : Class := [ [x] | [x|y]].

Notation "[ x , y ]" := (Ordered x y) (at level 0).

Hint Unfold Ordered : set.


(* 49 Theorem  [x,y] is a set if and only if x is a set and y is a set;
   if [x,y] is not a set, then [x,y] = μ. *)

Theorem Theorem49 : forall (x y: Class),
  Ensemble [x,y] <-> Ensemble x /\ Ensemble y.
Proof.
  intros; split; intro.
  - unfold Ordered in H; unfold Unordered in H.
    apply Axiom_Union' in H; destruct H; apply Theorem42' in H.
    apply Theorem42' in H; apply Theorem42' in H0; split; auto.
    unfold Unordered in H0; apply Axiom_Union' in H0.
    destruct H0; apply Theorem42' in H1; auto.
  - destruct H; unfold Ordered, Unordered; apply Axiom_Union; split.
    + apply Theorem42; auto; apply Theorem42; auto.
    + apply Theorem42; auto; apply Theorem46; auto.
Qed.

Theorem Theorem49' : forall (x y: Class),
  ~ Ensemble [x,y] -> [x,y] = μ.
Proof.
  intros; generalize (Theorem49 x y); intros.
  apply definition_not with (B:= Ensemble x /\ Ensemble y) in H; try tauto.
  apply not_and_or in H; apply Theorem46' in H; auto.
  generalize Theorem39; intros; rewrite <-H in H1.
  unfold Ordered; apply Theorem46'; auto.
Qed.

Hint Resolve Theorem49 Theorem49' : set.


(* 50 Theorem  If x and y are sets, then ∪[x,y]=[x|y], ∩[x,y]=[x], ∪∩[x,y]=x,
   ∩∩[x,y]=x, ∪∪[x,y]=x∪y, ∩∪[x,y]=x∩y. If either x or y is not a set,
   then ∪∩[x,y]=Φ, ∩∩[x,y]=Φ, ∪∪[x,y]=Φ, ∩∪[x,y]=Φ. *)

Lemma Lemma50 : forall (x y: Class),
  Ensemble x /\ Ensemble y -> Ensemble [x] /\ Ensemble [x | y].
Proof.
  intros; apply Theorem49 in H; auto.
  unfold Ordered in H; unfold Unordered in H.
  apply Axiom_Union' in H; destruct H.
  apply Theorem42' in H; auto.
  apply Theorem42' in H0; auto.
Qed.

Theorem Theorem50 : forall (x y: Class),
  Ensemble x /\ Ensemble y -> (∪[x,y] = [x|y]) /\ (∩[x,y] = [x]) /\
  (∪(∩[x,y]) = x) /\ (∩(∩[x,y]) = x) /\ (∪(∪[x,y]) = x∪y) /\ (∩(∪[x,y]) = x∩y).
Proof.
  intros; elim H; intros.
  repeat unfold Ordered; apply Lemma50 in H.
  apply Theorem47 in H; auto; elim H; intros; repeat split.
  - rewrite H3; apply Axiom_Extent; split; intros; try (apply Theorem4; tauto).
    apply Theorem4 in H4; destruct H4; auto; apply Theorem4; tauto.
  - rewrite H2; apply Axiom_Extent; split; intros.
    + apply Theorem4' in H4; apply H4.
    + apply Theorem4'; split; auto; apply Theorem4; tauto.
  - rewrite H2; apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H4; destruct H4, H5, H5. 
      apply Theorem4' in H6; destruct H6; apply Axiom_Scheme in H6.
      destruct H6; rewrite <- H8; auto.
      apply Theorem19; auto.
    + apply Axiom_Scheme; split; Ens; exists x. 
      split; auto; apply Theorem4'; split.
      * apply Axiom_Scheme; split; auto.
      * apply Theorem4; left; apply Axiom_Scheme.
        split; try apply H0; trivial.
  - rewrite H2; apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H4; destruct H4.
      apply H5; apply Theorem4'; split.
      * apply Axiom_Scheme; split; auto.
      * apply Theorem4; left; apply Axiom_Scheme; split; auto.
    + apply Axiom_Scheme; split; Ens.
      intros; apply Theorem4' in H5. destruct H5. 
      apply Axiom_Scheme in H5. destruct H5. rewrite H7; auto. 
      apply Theorem19; auto.
  - rewrite H3; apply Axiom_Extent; split; intros.
    + apply Theorem4; apply Axiom_Scheme in H4; destruct H4, H5, H5. 
      apply Theorem4 in H6; destruct H6.
      * apply Axiom_Scheme in H6; destruct H6; left; rewrite <- H7; auto. 
        apply Theorem19; auto.
      * apply Theorem4 in H6; destruct H6. 
        -- apply Axiom_Scheme in H6; destruct H6.
           left; rewrite <- H7; auto; apply Theorem19; auto.
        -- apply Axiom_Scheme in H6; destruct H6.
           right; rewrite <- H7; auto; apply Theorem19; auto.
    + apply Axiom_Scheme; apply Theorem4 in H4; split.
      * unfold Ensemble; destruct H4; Ens.
      * destruct H4.
        -- exists x; split; auto; apply Theorem4; left.
           apply Axiom_Scheme; split; auto.
        -- exists y; split; auto; apply Theorem4; right.
           apply Theorem4; right; apply Axiom_Scheme; split; auto.
  - rewrite H3; apply Axiom_Extent; split; intros.
    + apply Lemma_x in H4; elim H4; intros.
      apply Axiom_Scheme in H5; apply Axiom_Scheme in H6.
      destruct H4; apply Theorem4'; split; auto.
      * apply H5; apply Theorem4; left.
        apply Axiom_Scheme; split; auto.
      * apply H6; apply Theorem4; right.
        apply Theorem4; right.
        apply Axiom_Scheme; split; auto.
    + apply Theorem4' in H4; destruct H4. 
      apply Axiom_Scheme; split; Ens.
      intros; apply Theorem4 in H6; destruct H6.
      * apply Axiom_Scheme in H6; destruct H6; rewrite H7; auto.
        apply Theorem19; auto.
      * apply Axiom_Scheme in H6; destruct H6, H7.
        -- apply Axiom_Scheme in H7; destruct H7. 
           rewrite H8; auto; apply Theorem19; auto.
        -- apply Axiom_Scheme in H7; destruct H7.
           rewrite H8; auto; apply Theorem19; auto.
Qed.

Lemma Lemma50' : forall (x y: Class),
  ~Ensemble x \/ ~Ensemble y -> ~Ensemble [x] \/ ~Ensemble [x | y].
Proof.
  intros; elim H; intros. 
  - left; apply Theorem43 in H0; auto.
    rewrite H0; apply Theorem39; auto.
  - right; apply Theorem46' in H; auto.
    rewrite H; apply Theorem39; auto.
Qed.

Theorem Theorem50' : forall (x y: Class),
  ~Ensemble x \/ ~Ensemble y -> (∪(∩[x,y]) = Φ) /\ (∩(∩[x,y]) = μ)
  /\ (∪(∪[x,y]) = μ) /\ (∩(∪[x,y]) = Φ).
Proof.
  intros; apply Lemma50' in H; auto.
  apply Theorem47' in H; destruct H.
  repeat unfold Ordered; repeat split.
  - rewrite H; apply Theorem24'; auto.
  - rewrite H; apply Theorem24; auto.
  - rewrite H0; rewrite <- Theorem34'; auto.
  - rewrite H0; rewrite <- Theorem34; auto.
Qed.

Hint Resolve Theorem50 Theorem50' : set.


(* 51 Definition  1st coord z = ∩∩z. *)

Definition First z := ∩∩z.

Hint Unfold First : set.


(* 52 Definition  2nd coord z = (∩∪z)∪(∪∪z)~(∪∩z). *)

Definition Second z := (∩∪z)∪(∪∪z)~(∪∩z).

Hint Unfold Second : set.


(* 53 Theorem  2nd coord μ = μ. *)

Lemma Lemma53 : μ ~ Φ = μ.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Theorem4' in H; destruct H; auto.
  - apply Theorem4'; split; auto.
    apply Axiom_Scheme; split.
    * apply Theorem19 in H; auto.
    * apply Theorem16; auto.
Qed.

Theorem Theorem53 : Second μ = μ.
Proof.
  intros; unfold Second.
  repeat rewrite <-Theorem34'; auto.
  repeat rewrite <-Theorem34 ; auto.
  rewrite Theorem24'; auto.
  rewrite Lemma53; auto.
  apply Theorem20; auto.
Qed.

Hint Rewrite Theorem53 : set.


(* 54 Theorem  If x and y are sets, 1st coord [x,y] = x and 2nd coord [x,y] = y.
   If either of x and y is not a set, then 1st coord [x,y] = μ and
   2nd coord [x,y] = μ. *)

Lemma Lemma54 : forall (x y: Class),
  (x ∪ y) ~ x = y ~ x.
Proof.
  intros.
  apply Axiom_Extent; split; intros.
  - apply Theorem4' in H; apply Theorem4'.
    destruct H; apply Theorem4 in H; split; auto.
    destruct H; auto; apply Axiom_Scheme in H0.
    destruct H0; elim H1; auto.
  - apply Theorem4' in H; apply Theorem4'.
    destruct H; split; auto.
    apply Theorem4; tauto.
Qed.

Theorem Theorem54 : forall (x y: Class),
  Ensemble x /\ Ensemble y -> First [x,y] = x /\ Second [x,y] = y.
Proof.
  intros; apply Theorem50 in H; auto; split.
  - unfold First; apply H.
  - destruct H, H0, H1, H2, H3; unfold Second.
    rewrite H4; rewrite H3; rewrite H1.
    rewrite Lemma54; auto; unfold Difference.
    rewrite Theorem6'; auto; rewrite <- Theorem8; auto.
    rewrite Property_μ; auto; rewrite Theorem20'; auto.
Qed.


Theorem Theorem54' : forall (x y: Class),
  ~Ensemble x \/ ~Ensemble y -> First [x,y] = μ /\ Second [x,y] = μ.
Proof.
  intros; apply Theorem50' in H; auto; split.
  - unfold First; apply H.
  - destruct H, H0, H1; unfold Second.
    rewrite H2; rewrite H1; rewrite H.
    rewrite Lemma53; auto.
    apply Theorem20; auto.
Qed.

Hint Resolve Theorem54 Theorem54' : set.


(* 55 Theorem  If x and y are sets and [x,y] = [u,v], then x=u and y=v. *)

Theorem Theorem55 : forall (x y u v: Class),
  Ensemble x /\ Ensemble y -> ([x,y] = [u,v] <-> x = u /\ y = v).
Proof.
  intros; split; intros.
  - double H; apply Theorem49 in H; apply Theorem54 in H1; destruct H1.
    rewrite H0 in H, H1, H2; apply Theorem49 in H; apply Theorem54 in H.
    destruct H; rewrite H1 in H; rewrite H2 in H3; split; auto.
  - destruct H0; rewrite H0, H1; auto.
Qed.

Hint Resolve Theorem55 : set.


(* 56 Definition  r is a relation if and only if for each member z of r there
   is x and y such that z = [x,y]. *)

Definition Relation r : Prop :=
  forall z, z∈r -> exists x y, z = [x,y].

Hint Unfold Relation: set.


(* II Classification axiom-scheme  For each b, b ∈ { a : A } if and only if
   b is a set and B. *)

(* { [x,y] : ... }  If the member is a ordered pair, then { [x,y] : ... } is
   used. The definition of { [x,y] : ... } is to avoid excessive notation. We
   agree that { [x,y] : ... } is to be identical with { u : for some x, some y,
   u = (x,y) and ... }. *)

Parameter Classifier_P : (Class -> Class -> Prop) -> Class.

Notation "\{\ P \}\" := (Classifier_P P) (at level 0).

Axiom Axiom_SchemeP : forall (a b: Class) (P: Class -> Class -> Prop),
  [a,b] ∈ \{\ P \}\ <-> Ensemble [a,b] /\ (P a b).

Axiom Property_P : forall (z: Class) (P: Class -> Class -> Prop),
  z ∈ \{\ P \}\ -> (exists a b, z = [a,b]) /\ z ∈ \{\ P \}\.

Ltac PP H a b := apply Property_P in H; destruct H as [[a [b H]]];
  rewrite H in *.

Hint Resolve Axiom_SchemeP Property_P : set.


(* 57 Definition  r ∘ s = { [x,z] : for some y, [x,y]∈s and [y,z]∈r }. *)

Definition Composition r s : Class :=
 \{\ λ x z, exists y, [x,y]∈s /\ [y,z]∈r \}\.

Notation "r ∘ s" := (Composition r s) (at level 50, no associativity).

(* r∘s = {u : for some x, some y and some z, u=[x,z], [x,y]∈s and [y,z]∈r}. *)

Definition Composition' r s : Class :=
  \{ λ u, exists x y z, u = [x,z] /\ [x,y] ∈ s /\ [y,z] ∈ r \}.

Hint Unfold Composition Composition' : set.


(* 58 Theorem  (r∘s)∘t = r∘(s∘t). *)

Theorem Theorem58 : forall (r s t: Class),
  (r ∘ s) ∘ t = r ∘ (s ∘ t).
Proof.
  intros; apply Axiom_Extent; split; intros.
  - PP H a b. apply Axiom_SchemeP in H0; destruct H0, H1 as [y H1], H1.
    apply Axiom_SchemeP in H2; destruct H2, H3, H3.
    apply Axiom_SchemeP; split; auto.
    exists x; split; try tauto; apply Axiom_SchemeP; split; Ens.
    AssE [a,y]; AssE [y,x]; apply Theorem49 in H5; apply Theorem49 in H6.
    destruct H5, H6; apply Theorem49; auto.
  - PP H a b; apply Axiom_SchemeP in H0; destruct H0, H1 as [y H1], H1.
    apply Axiom_SchemeP in H1; destruct H1, H3, H3.
    apply Axiom_SchemeP; split; auto.
    exists x; split; auto; apply Axiom_SchemeP; split; Ens.
    AssE [a,x]; AssE [y,b]; apply Theorem49 in H5; apply Theorem49 in H6.
    destruct H5, H6; apply Theorem49; Ens.
Qed.

Hint Rewrite Theorem58 : set.


(* 59 Theorem  r∘(s∪t) = r∘s ∪ r∘t and r∘(s∩t) ⊂ r∘s ∩ r∘t. *)

Theorem Theorem59 : forall (r s t: Class),
  Relation r /\ Relation s -> r ∘ (s ∪ t) = (r ∘ s) ∪ (r ∘ t) /\ 
  r ∘ (s ∩ t) ⊂ (r ∘ s) ∩ (r ∘ t).
Proof.
  intros; split.
  - apply Axiom_Extent; split; intros.
    + PP H0 a b; apply Axiom_SchemeP in H1; destruct H1.
      apply Theorem4.
      destruct H2 as [y H2]; destruct H2.
      apply Theorem4 in H2; destruct H2.
      * left; apply Axiom_SchemeP; split; auto.
        exists y; split; auto.
      * right; apply Axiom_SchemeP; split; auto.
        exists y; split; auto.
    + apply Theorem4 in H0; destruct H0; PP H0 a b; apply Axiom_SchemeP.
      * apply Axiom_SchemeP in H1; destruct H1.
        destruct H2 as [y H2]; destruct H2; split; auto.
        exists y; split; auto; apply Theorem4; try tauto.
      * apply Axiom_SchemeP in H1; destruct H1.
        destruct H2 as [y H2]; destruct H2; split; auto.
        exists y; split; auto; apply Theorem4; try tauto.
  - unfold Subclass; intros; PP H0 a b.
    apply Axiom_SchemeP in H1; destruct H1.
    destruct H2 as [y H2]; destruct H2.
    apply Theorem4' in H2; apply Theorem4'; split.
    + apply Axiom_SchemeP; split; auto.
      exists y; split; try apply H2; auto.
    + apply Axiom_SchemeP; split; auto.
      exists y; split; try apply H2; auto.
Qed.

Hint Resolve Theorem59 : set.


(* 60 Definition  r⁻¹ = { [x,y] : [y,x] ∈ r }. *)

Definition Inverse r : Class := \{\ λ x y, [y,x]∈r \}\.

Notation "r ⁻¹" := (Inverse r)(at level 5).

Hint Unfold Inverse : set.


(* 61 Theorem  If r is a relation, then (r⁻¹)⁻¹ = r. *)

Lemma Lemma61 : forall (x y: Class),
  Ensemble [x,y] <-> Ensemble [y,x].
Proof.
  intros; split; intros.
  - apply Theorem49 in H; auto.
    destruct H; apply Theorem49; auto.
  - apply Theorem49 in H; auto.
    destruct H; apply Theorem49; auto.
Qed.

Theorem Theorem61 : forall (r: Class),
  Relation r -> (r ⁻¹)⁻¹ = r.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - PP H0 a b; apply Axiom_SchemeP in H1; destruct H1.
    apply Axiom_SchemeP in H2; apply H2.
  - unfold Relation in H; double H0; apply H in H1.
    destruct H1 as [a [b H1]]; rewrite H1 in *; clear H1.
    apply Axiom_SchemeP; split; Ens; apply Axiom_SchemeP; split; auto.
    apply Lemma61; auto; Ens.
Qed.

Hint Rewrite Theorem61 : set.


(* 62 Theorem  (r∘s)⁻¹ = (s⁻¹) ∘ (r⁻¹). *)

Theorem Theorem62 : forall (r s: Class),
  (r ∘ s)⁻¹ = (s⁻¹) ∘ (r⁻¹).
Proof.
  intros; apply Axiom_Extent; split; intros.
  - PP H a b; apply Axiom_SchemeP in H0; destruct H0 as [H0 H1].
    apply Axiom_SchemeP; split; auto.
    apply Axiom_SchemeP in H1; destruct H1, H2, H2.
    exists x; split.
    + apply Axiom_SchemeP; split; auto. 
      apply Lemma61; Ens; exists r; auto.
    + apply Axiom_SchemeP; split; auto.
      apply Lemma61; Ens.
  - PP H a b; apply Axiom_SchemeP in H0; destruct H0, H1, H1.
    apply Axiom_SchemeP; split; auto.
    apply Axiom_SchemeP in H1; apply Axiom_SchemeP in H2.
    apply Axiom_SchemeP; split.
    + apply Lemma61; auto.
    + exists x; split; try apply H0; try apply H2.
      destruct H1; auto.
Qed.

Hint Rewrite Theorem62 : set.


(* FUNCTIONS *)

(* 63 Definition  f is a function if and only if f is a relation and for each x,
   each y, each z, if [x,y]∈f and [x,z]∈f, then y = z. *)

Definition Function f : Prop :=
  Relation f /\ (forall x y z, [x,y] ∈ f /\ [x,z] ∈ f -> y=z).

Hint Unfold Function : set.


(* 64 Theorem  If f is a function and g is a function so is f∘g. *)

Theorem Theorem64 : forall f g,
  Function f /\ Function g -> Function (f ∘ g).
Proof.
  intros; destruct H.
  unfold Function; split; intros.
  - unfold Relation; intros; PP H1 a b; eauto.
  - destruct H1; apply Axiom_SchemeP in H1; apply Axiom_SchemeP in H2.
    destruct H1, H2, H3, H4, H3, H4.
    unfold Function in H, H0; destruct H; destruct H0.
    assert (x0=x1). { apply H8 with x; split; auto. }
    rewrite H9 in H5; apply H7 with x1; split; auto.
Qed.

Hint Resolve Theorem64 : set.


(* 65 Definition  domain f = { x : for some y, [x,y]∈f }. *)

Definition Domain f : Class := \{ λ x, exists y, [x,y] ∈ f \}.

Notation "dom( f )" := (Domain f)(at level 5).

Corollary Property_dom : forall x y f,
  [x,y] ∈ f -> x ∈ dom( f ).
Proof.
  intros; unfold Domain; apply Axiom_Scheme; split; eauto.
  AssE [x,y]; apply Theorem49 in H0; apply H0.
Qed.

Hint Unfold Domain : set.


(* 66 Definition  range f = { y : for some x, [x,y]∈f }. *)

Definition Range f : Class := \{ λ y, exists x, [x,y] ∈ f \}.

Notation "ran( f )" := (Range f)(at level 5).

Corollary Property_ran : forall x y f,
  [x,y] ∈ f -> y ∈ ran( f ).
Proof.
  intros; apply Axiom_Scheme.
  split; eauto; AssE [x,y].
  apply Theorem49 in H0; apply H0.
Qed.

Hint Unfold Range : set.


(* 67 Theorem  domain μ = μ and range μ = μ. *)

Theorem Theorem67 : dom( μ ) = μ /\ ran( μ ) = μ.
Proof.
  intros; split; apply Axiom_Extent; split; intros.
  - AssE z; apply Theorem19; auto.
  - apply Theorem19 in H.
    unfold Domain; apply Axiom_Scheme; split; auto.
    exists z; apply Theorem19.
    apply Theorem49; split; auto.
  - AssE z; apply Theorem19; auto.
  - apply Theorem19 in H.
    unfold Range; apply Axiom_Scheme; split; auto.
    exists z; apply Theorem19.
    apply Theorem49; split; auto.
Qed.

Hint Rewrite Theorem67 : set.


(* 68 Definition  f[x] = ∩{ y : [x,y]∈f }. *)

Definition Value f x : Class := ∩ \{ λ y, [x,y] ∈ f \}.

Notation "f [ x ]" := (Value f x)(at level 5).

Corollary Property_Value : forall f x,
  Function f -> x ∈ dom( f ) -> [x,f[x]] ∈ f.
Proof.
  intros; unfold Function in H;destruct H as [_ H].
  apply Axiom_Scheme in H0; destruct H0, H1.
  assert (x0=f[x]).
  - apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme; split; intros; try Ens.
      apply Axiom_Scheme in H3; destruct H3.
      assert (x0=y). { apply H with x; split; auto. }
      rewrite <- H5; auto.
    + apply Axiom_Scheme in H2; destruct H2 as [_ H2].
      apply H2; apply Axiom_Scheme; split; auto.
      AssE [x, x0]; apply Theorem49 in H3; apply H3.
  - rewrite <- H2; auto.
Qed.

Hint Unfold Value : set.
Hint Resolve Property_Value : set.


(* 69 Theorem  If x ∉ domain f, then f[x]=μ; if x ∈ domain f, then f[x]∈μ. *)

Lemma Lemma69 : forall x f,
  Function f -> (x ∉ dom(f) -> \{ λ y, [x,y] ∈ f \} = Φ) /\
  (x ∈ dom(f) -> \{ λ y, [x,y] ∈ f \} <> Φ).
Proof.
  intros; split; intros.
  - generalize (classic (\{ λ y0, [x, y0] ∈ f \} = Φ)); intro.
    destruct H1; auto; apply Lemma35 in H1; auto.
    elim H1; intro z; intros; apply Axiom_Scheme in H2.
    destruct H2 as [H2 H3]; apply Property_dom in H3; contradiction.
  - apply Lemma35; auto; exists f[x].
    apply Axiom_Scheme; eapply Property_Value in H0; auto.
    split; auto; apply Property_ran in H0; Ens.
Qed.

Theorem Theorem69 : forall x f,
  ( x ∉ dom( f ) -> f[x] = μ ) /\ ( x ∈ dom( f ) -> f[x] ∈  μ ).
Proof.
  intros; split; intros.
  - assert (\{ λ y, [x,y] ∈ f \} = Φ).
    { apply Axiom_Extent; split; intros.
      apply Axiom_Scheme in H0; destruct H0.
      apply Property_dom in H1; contradiction.
      generalize (Theorem16 z); intro; contradiction. }
    unfold Value; rewrite H0; apply Theorem24.
  - assert (\{ λ y, [x,y] ∈ f \} <> Φ).
    { intro; apply Axiom_Scheme in H; destruct H, H1.
      generalize (Axiom_Extent \{ λ y, [x, y] ∈ f \} Φ); intro.
      destruct H2; apply H2 with x0 in H0; destruct H0.
      assert (x0 ∈ Φ).
      { apply H0; apply Axiom_Scheme; split; auto.
        AssE [x, x0];  apply Theorem49 in H5; tauto. }
      eapply Theorem16; eauto. }
    apply Theorem35 in H0; apply Theorem19; auto.
Qed.

Corollary Property_Value' : forall f x,
  Function f -> f[x] ∈ ran(f) -> [x,f[x]] ∈ f.
Proof.
  intros; apply Property_Value; auto.
  apply Axiom_Scheme in H0; destruct H0, H1.
  generalize (classic (x ∈ dom( f))); intros.
  destruct H2; auto; apply Theorem69 in H2; auto.
  rewrite H2 in H0; generalize (Theorem39); intro; contradiction.
Qed.

Hint Resolve Theorem69 : set.
Hint Resolve Property_Value' : set.


(* 70 Theorem  If f is a function, then f = { [x,y] : y = f[x] }. *)

Theorem Theorem70 : forall f,
  Function f -> f = \{\ λ x y, y = f[x] \}\.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - double H0; unfold Function, Relation in H; destruct H.
    apply H in H1; destruct H1 as [a [b H1]]; rewrite H1 in *; clear H1.
    apply Axiom_SchemeP; split; try Ens; apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme; split; intros; try Ens.
      apply Axiom_Scheme in H3; destruct H3.
      apply Lemma_xy with (y:=[a, y] ∈ f) in H0; auto.
      apply H2 in H0; rewrite <- H0; auto.
    + unfold Value, Element_I in H1; apply Axiom_Scheme in H1; destruct H1.
      apply H3; apply Axiom_Scheme; split; auto; AssE [a,b].
      apply Theorem49 in H4; try apply H4.
  - PP H0 a b; apply Axiom_SchemeP in H1; destruct H1.
    generalize (classic (a ∈ dom( f ))); intros; destruct H3.
    + apply Property_Value in H3; auto; rewrite H2; auto.
    + apply Theorem69 in H3; auto.
      rewrite H3 in H2; rewrite H2 in H1.
      apply Theorem49 in H1; destruct H1 as [_ H1].
      generalize Theorem39; intro; contradiction.
Qed.

Hint Resolve Theorem70 : set.


(* 71 Theorem  If f and g are functions, then f=g iff f[x]=g[x] for each x. *)

Theorem Theorem71 : forall f g,
  Function f /\ Function g -> (f = g <-> forall x, f[x] = g[x]).
Proof.
  intros; split; intros; try rewrite H0; trivial.
  destruct H; intros; apply (Theorem70 f) in H; apply (Theorem70 g) in H1.
  rewrite H; rewrite H1; apply Axiom_Extent; split; intros.
  - PP H2 a b; apply Axiom_SchemeP in H3; apply Axiom_SchemeP.
    destruct H3; split; auto; rewrite <- H0; auto.
  - PP H2 a b; apply Axiom_SchemeP in H3; apply Axiom_SchemeP.
    destruct H3; split; auto; rewrite -> H0; auto.
Qed.

Hint Resolve Theorem71 : set.


(* V Axiom of substitution  If f is a function and domain f is a set, then 
   range f is a set. *)

Axiom Axiom_Substitution : forall f,
  Function f -> Ensemble dom(f) -> Ensemble ran(f).

Hint Resolve Axiom_Substitution : set.


(* VI Axiom of amalgamation  If x is a set so is ∪x. *)

Axiom Axiom_Amalgamation : forall x, Ensemble x -> Ensemble (∪ x).

Hint Resolve Axiom_Amalgamation : set.


(* 72 Definition  x × y = { [u,v] : u∈x /\ v∈y }. *)

Definition Cartesian x y : Class := \{\ λ u v, u∈x /\ v∈y \}\.

Notation "x × y" := (Cartesian x y)(at level 2, right associativity).

Hint Unfold Cartesian : set.


(* 73 Theorem  If u and y are sets so is [u] × y. *)

Lemma Ex_Lemma73 : forall u y,
  Ensemble u /\ Ensemble y ->
  exists f, Function f /\ dom(f) = y /\ ran(f) = [u] × y.
Proof.
  intros; destruct H.
  exists (\{\ λ w z, w∈y /\ z = [u,w] \}\).
  repeat split; intros.
  - red; intros; PP H1 a b; Ens.
  - destruct H1; apply Axiom_SchemeP in H1; apply Axiom_SchemeP in H2.
    destruct H1 as [_ [_ H1]]; destruct H2 as [_ [_ H2]].
    rewrite H2; auto.
  - apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H1; destruct H1 as [_ [t H1]].
      apply Axiom_SchemeP in H1; tauto.
    + apply Axiom_Scheme; split; try Ens.
      exists [u,z]; apply Axiom_SchemeP; split; auto.
      AssE z; apply Theorem49; split; auto.
      apply Theorem49; tauto.
  - apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H1; destruct H1, H1, H2.
      apply Axiom_SchemeP in H2; destruct H2, H3.
      rewrite H4; apply Axiom_SchemeP; repeat split; auto.
      * apply Theorem49; split; auto; AssE x0.
      * apply Axiom_Scheme; split; auto.
    + PP H1 a b; apply Axiom_SchemeP in H2; destruct H2, H3.
      apply Axiom_Scheme; split; auto; exists b.
      apply Axiom_SchemeP; repeat split; auto.
      * apply Theorem49; split; auto; AssE b.
      * apply Theorem19 in H; apply Axiom_Scheme in H3.
        destruct H3; rewrite H5; auto.
Qed.

Theorem Theorem73 : forall u y,
  Ensemble u /\ Ensemble y -> Ensemble ([u] × y).
Proof.
  intros.
  elim H; intros; apply Ex_Lemma73 in H; auto.
  destruct H, H, H2; rewrite <- H3; apply Axiom_Substitution; auto.
  rewrite H2; auto.
Qed.

Hint Resolve Theorem73 : set.


(* 74 Theorem  If x and y are sets so is x × y. *)

Lemma Ex_Lemma74 : forall x y,
  Ensemble x /\ Ensemble y -> exists f, Function f /\ dom( f ) = x /\
  ran( f ) = \{ λ z, exists u, u∈x /\ z = [u] × y \}.
Proof.
  intros; destruct H.
  exists (\{\ λ u z, u∈x /\ z = [u] × y \}\).
  repeat split; intros.
  - red; intros; PP H1 a b; Ens.
  - destruct H1; apply Axiom_SchemeP in H1; apply Axiom_SchemeP in H2.
    destruct H1, H2, H3, H4; subst z; auto.
  - apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H1; destruct H1, H2.
      apply Axiom_SchemeP in H2; tauto.
    + apply Axiom_Scheme; split; try AssE z.
      exists (([z]) × y); apply Axiom_SchemeP.
      repeat split; auto; apply Theorem49; split; auto.
      apply Theorem73; auto.
  - apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H1; destruct H1, H2.
      apply Axiom_SchemeP in H2; apply Axiom_Scheme.
      split; auto; exists x0; tauto.
    + apply Axiom_Scheme in H1; destruct H1, H2, H2.
      apply Axiom_Scheme; split; auto.
      exists x0; apply Axiom_SchemeP; repeat split; auto.
      apply Theorem49; split; auto; AssE x0.
Qed.

Lemma Lemma74 : forall x y,
  Ensemble x /\ Ensemble y ->
  ∪ \{ λ z, exists u, u∈x /\ z = [u] × y \} = x × y.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme in H0; destruct H0, H1, H1.
    apply Axiom_Scheme in H2; destruct H2, H3, H3.
    rewrite H4 in H1; PP H1 a b.
    apply Axiom_SchemeP in H5; destruct H5, H6.
    apply Axiom_SchemeP; repeat split; auto.
    apply Axiom_Scheme in H6; destruct H6 as [_ H6].
    AssE x1; apply Theorem19 in H8.
    rewrite <- H6 in H3; auto.
  - PP H0 a b; apply Axiom_SchemeP in H1; destruct H1, H2.
    apply Axiom_Scheme; split; auto.
    exists (([a]) × y); split; AssE a.
    + apply Axiom_SchemeP; repeat split; auto.
      apply Axiom_Scheme; intros; auto.
    + apply Axiom_Scheme; split.
      * apply Theorem73; split; try apply H; auto.
      * exists a; split; auto.
Qed.

Theorem Theorem74 : forall x y,
  Ensemble x /\ Ensemble y -> Ensemble x × y.
Proof.
  intros; double H; double H0; destruct H0.
  apply Ex_Lemma74 in H; destruct H, H, H3.
  rewrite <- H3 in H0; apply Axiom_Substitution in H0; auto.
  rewrite H4 in H0; apply Axiom_Amalgamation in H0.
  rewrite Lemma74 in H0; auto.
Qed.

Hint Resolve Theorem74 : set.


(* 75 Theorem  If f is a function and domain f is a set, then f is a set. *)

Theorem Theorem75 : forall f,
  Function f /\ Ensemble dom( f ) -> Ensemble f.
Proof.
  intros; destruct H.
  assert (Ensemble ran(f)); try apply Axiom_Substitution; auto.
  assert (Ensemble (dom(f) × ran(f))).
  { apply Theorem74; split; auto. }
  apply Theorem33 with (x:=(dom( f ) × ran( f ))); auto.
  unfold Subclass; intros; rewrite Theorem70 in H3; auto.
  PP H3 a b; rewrite <- Theorem70 in H4; auto; AssE [a,b].
  repeat split; auto; apply Axiom_SchemeP; split; auto.
  generalize (Property_dom a b f H4); intro.
  generalize (Property_ran a b f H4); intro; tauto.
Qed.

Hint Resolve Theorem75 : set.


(* 76 Definition  Exponent y x = { f : f is a function, domain f = x and
   range f ⊂ y }. *)

Definition Exponent y x : Class :=
  \{ λ f, Function f /\ dom( f ) = x /\ ran( f ) ⊂ y \}.

Hint Unfold Exponent : set.


(* 77 Theorem  If x and y are sets so is Exponent y x. *)

Theorem Theorem77 : forall x y,
  Ensemble x /\ Ensemble y -> Ensemble (Exponent y x).
Proof.
  intros; apply Theorem33 with (x:=(pow(x × y))).
  - apply Theorem38; auto; apply Theorem74; auto.
  - unfold Subclass; intros; apply Theorem38.
    + apply Theorem74; auto.
    + apply Axiom_Scheme in H0; destruct H0, H1, H2.
    unfold Subclass; intros; rewrite Theorem70 in H4; auto.
    PP H4 a b; rewrite <- Theorem70 in H5; auto.
    AssE [a,b]; apply Axiom_SchemeP; split; auto.
    generalize (Property_dom a b z H5); intro; rewrite H2 in H7.
    generalize (Property_ran a b z H5); intro.
    unfold Subclass in H3; apply H3 in H8; split; auto.
Qed.

Hint Resolve Theorem77 : set.


(* 78 Definition  f is on x if and only if f is a function and x = domain f. *)

Definition On f x : Prop := Function f /\ dom( f ) = x.

Hint Unfold On : set.


(* 79 Definition  f is to y if and only if f is a function and rang f ⊂ y. *)

Definition To f y : Prop := Function f /\ ran(f) ⊂ y.

Hint Unfold To : set.


(* 80 Definition  f is onto y if and only if f is a function and range f = y. *)

Definition Onto f y : Prop := Function f /\ ran(f) = y.

Hint Unfold Onto : set.


End ElementSet.

Export ElementSet.

