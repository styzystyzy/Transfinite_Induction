Require Export Ordinals.

(* NON-NEGATIVE INTEGERS *)

Module NInt.

(* VIII Axiom of infinity : For some y, y is a set, Φ ∈ y and (x ∪ {x}) ∈ y
   whenever x ∈ y. *)

Axiom Axiom_Infinity : exists y, Ensemble y /\ Φ ∈ y /\
  (forall x, x ∈ y -> (x ∪ [x]) ∈ y).

Hint Resolve Axiom_Infinity : set.


(* 129 Definition  x is an integer if and only if x is an ordinal and E⁻¹
   well-orders x. *)

Definition NInteger x : Prop := Ordinal x /\ WellOrdered (E ⁻¹) x.

Hint Unfold NInteger : set.


(* 130 Definition  x is an E-last member of y is and only if x is an E⁻¹-first
   member of y. *)

Definition LastMember x E y : Prop := FirstMember x (E ⁻¹) y.

Hint Unfold LastMember : set.


(* 131 Definition  W = { x : x is an integer }. *)

Definition W : Class := \{ λ x, NInteger x \}.

Hint Unfold W : set.


(* 132 Theorem  A member of an integer is an integer. *)

Theorem Theorem132 : forall x y, NInteger x -> y∈x -> NInteger y.
Proof.
  intros.
  unfold NInteger in H; unfold NInteger; destruct H.
  double H; apply Lemma_xy with (y:= y∈x) in H2; auto.
  apply Theorem111 in H2; split; auto.
  unfold WellOrdered in H1; unfold WellOrdered.
  unfold Ordinal in H; destruct H.
  unfold full in H3; apply H3 in H0.
  destruct H1; split; intros.
  - unfold Connect in H1; unfold Connect; intros.
    apply H1; destruct H5; unfold Subclass in H0.
    apply H0 in H5; apply H0 in H6; split; auto.
  - destruct H5; apply H4; split; auto.
    apply (Theorem28 _ y _); auto.
Qed.

Hint Resolve Theorem132 : set.


(* 133 Theorem  If y∈R and x is an E-last member of y, then y = x+1. *)

Theorem Theorem133 : forall x y,
  y ∈ R /\ LastMember x E y -> y = PlusOne x.
Proof.
  intros; destruct H.
  unfold LastMember, FirstMember in H0.
  unfold R in H; apply Axiom_Scheme in H; destruct H, H0.
  double H1; add (x ∈ y) H3; apply Theorem111 in H3.
  assert (x ∈ R). { unfold R; apply Axiom_Scheme; Ens. }
  apply Theorem123 in H4; unfold FirstMember in H4; destruct H4.
  assert (y ∈ \{ λ z, z ∈ R /\ x ≺ z \}).
  { apply Axiom_Scheme; repeat split; auto.
    unfold R; apply Axiom_Scheme; split; auto. }
  apply H5 in H6; clear H5; generalize (Theorem113); intros.
  destruct H5; clear H7; apply Theorem107 in H5.
  unfold WellOrdered in H5; destruct H5; clear H7.
  unfold Connect in H5; apply Axiom_Scheme in H4; destruct H4, H7.
  clear H8; assert (y ∈ R /\ (PlusOne x) ∈ R).
  { split; auto; unfold R; apply Axiom_Scheme; Ens. }
  apply H5 in H8; clear H5; destruct H8; try contradiction.
  destruct H5; auto; unfold Rrelation, E in H5.
  apply Axiom_SchemeP in H5; destruct H5.
  apply H2 in H8; elim H8; unfold Rrelation, Inverse.
  apply Axiom_SchemeP; split; try apply Theorem49; Ens.
  unfold E; apply Axiom_SchemeP; split; try apply Theorem49; Ens.
  unfold PlusOne; apply Theorem4; right.
  unfold Singleton; apply Axiom_Scheme; Ens.
Qed.

Hint Resolve Theorem133 : set.


(* 134 Theorem  If x ∈ W, then x+1 ∈ W. *)

Theorem Theorem134 : forall x, x ∈ W -> (PlusOne x) ∈ W.
Proof.
  intros.
  unfold W in H; apply Axiom_Scheme in H; destruct H.
  unfold NInteger in H0; destruct H0.
  unfold W; apply Axiom_Scheme; split.
  - unfold PlusOne; apply Axiom_Union; split; auto.
    apply Theorem42 in H; auto.
  - unfold NInteger; split.
    + assert (x ∈ R). { apply Axiom_Scheme; Ens. }
      apply Lemma123 in H2; apply Axiom_Scheme in H2; apply H2.
    + unfold WellOrdered in H1; unfold WellOrdered.
      destruct H1; split; intros.
      { clear H2; unfold Connect in H1; unfold Connect; intros.
        unfold PlusOne in H2; destruct H2; apply Theorem4 in H2.
        apply Theorem4 in H3; destruct H2, H3.
        - apply H1; auto.
        - unfold Singleton in H3; apply Axiom_Scheme in H3; destruct H3.
          rewrite <- H4 in H2; try apply Theorem19; Ens.
          right; left; unfold Rrelation, Inverse, E.
          apply Axiom_SchemeP; split; try apply Theorem49; Ens.
          apply Axiom_SchemeP; split; try apply Theorem49; Ens.
        - unfold Singleton in H2; apply Axiom_Scheme in H2; destruct H2.
          rewrite <- H4 in H3; try apply Theorem19; Ens.
          left; unfold Rrelation, Inverse, E.
          apply Axiom_SchemeP; split; try apply Theorem49; Ens.
          apply Axiom_SchemeP; split; try apply Theorem49; Ens.
        - unfold Singleton in H2; apply Axiom_Scheme in H2; destruct H2.
          unfold Singleton in H3; apply Axiom_Scheme in H3; destruct H3.
          right; right; rewrite H4, H5; try apply Theorem19; Ens. }
      { destruct H3; unfold PlusOne in H3.
        generalize (classic (x ∈ y)); intro; destruct H5.
        - exists x; unfold FirstMember; split; intros; auto.
          intro; unfold Rrelation in H7; apply Axiom_SchemeP in H7.
          destruct H7; apply Axiom_SchemeP in H8; destruct H8.
          apply H3 in H6; apply Theorem4 in H6; destruct H6.
          + eapply Theorem102; eauto.
          + apply Axiom_Scheme in H6; destruct H6.
            rewrite H10 in H9; try apply Theorem19; Ens.
            apply Theorem101 in H9; auto.
        - apply H2; split; auto; unfold Subclass; intros; double H6.
          apply H3 in H6; apply Theorem4 in H6; destruct H6; auto.
          apply Axiom_Scheme in H6; destruct H6; apply Theorem19 in H.
          rewrite <- H8 in H5; auto; contradiction. }
Qed.

Hint Resolve Theorem134 : set.


(* 135 Theorem  Φ ∈ W and if x ∈ W, then Φ ≠ x+1. *)

Theorem Theorem135 : forall x, 
  Φ ∈ W /\ (x ∈ W -> Φ ≠ PlusOne x).
Proof.
  intros; split; intros.
  - unfold W; apply Axiom_Scheme; split.
    + generalize Axiom_Infinity; intros; destruct H, H, H0; Ens.
    + unfold NInteger; split.
      * unfold Ordinal; split.
        -- unfold Connect; intros; destruct H.
           generalize (Theorem16 u); contradiction.
        -- unfold full; intros.
           generalize (Theorem16 m); contradiction.
      * unfold WellOrdered; split; intros.
        -- unfold Connect; intros; destruct H.
           generalize (Theorem16 u); contradiction.
        -- destruct H; generalize (Theorem26 y); intros.
           absurd (y = Φ); try apply Theorem27; auto.
  - intro; unfold PlusOne in H0; assert (x ∈ Φ).
    { rewrite H0; apply Theorem4; right.
      unfold Singleton; apply Axiom_Scheme; split; Ens. }
    generalize (Theorem16 x); intro; contradiction.
Qed.

Hint Resolve Theorem135 : set.


(* 136 Theorem  If x and y are members of W and x + 1 = y + 1, then x = y. *)

Theorem Theorem136 : forall x y,
  x ∈ W /\ y ∈ W -> PlusOne x = PlusOne y -> x = y.
Proof.
  intros; destruct H.
  unfold W in H, H1; apply Axiom_Scheme in H.
  apply Axiom_Scheme in H1; destruct H, H1.
  unfold NInteger in H2, H3; destruct H2, H3.
  assert (x∈R /\ y∈R).
  { split; unfold R; apply Axiom_Scheme; auto. }
  destruct H6; apply Theorem124 in H6.
  apply Theorem124 in H7; rewrite <- H6, <- H7.
  rewrite H0; auto.
Qed.

Hint Resolve Theorem136 : set.


(* 137 Theorem  If x ⊂ W, Φ∈x and u+1∈x whenever u∈x, then x = W. *)

Corollary Property_W : Ordinal W.
Proof.
  unfold Ordinal; split.
  - unfold Connect; intros; destruct H; unfold W in H, H0.
    apply Axiom_Scheme in H; apply Axiom_Scheme in H0; destruct H, H0.
    unfold NInteger in H1, H2; destruct H1, H2; add (Ordinal v) H1.
    apply Theorem110 in H1; destruct H1 as [H1|[H1|H1]]; try tauto.
    + left; unfold Rrelation, E; apply Axiom_SchemeP.
      split; auto; apply Theorem49; split; auto.
    + right; left; unfold Rrelation, E; apply Axiom_SchemeP.
      split; auto; apply Theorem49; split; auto.
  - unfold full; intros; unfold Subclass; intros.
    unfold W in H; apply Axiom_Scheme in H; destruct H.
    apply (Theorem132 _ z) in H1; auto.
    unfold W; apply Axiom_Scheme; Ens.
Qed.

Theorem Theorem137 : forall x,
  x ⊂ W -> Φ ∈ x ->
  (forall u, u ∈ x -> (PlusOne u) ∈ x) -> x = W.
Proof.
  intros.
  generalize (classic (x = W)); intros; destruct H2; auto.
  assert (exists y, FirstMember y E (W ~ x)).
  { assert (WellOrdered E W).
    { apply Theorem107; apply Property_W. }
    unfold WellOrdered in H3; destruct H3; apply H4; split.
    - unfold Subclass; intros; unfold Difference in H5.
      apply Theorem4' in H5; apply H5.
    - intro; apply Property_Φ in H; apply H in H5.
      symmetry in H5; contradiction. }
  destruct H3 as [y H3]; unfold FirstMember in H3; destruct H3.
  unfold Difference in H3; apply Theorem4' in H3; destruct H3.
  unfold W in H3; apply Axiom_Scheme in H3; destruct H3; double H6.
  unfold NInteger in H7; destruct H7; unfold WellOrdered in H8.
  destruct H8; assert (y ⊂ y /\ y ≠ Φ).
  { split; try unfold Subclass; auto.
    intro; rewrite H10 in H5; unfold Complement in H5.
    apply Axiom_Scheme in H5; destruct H5; contradiction. }
  apply H9 in H10; clear H9; destruct H10 as [u H9].
  assert (u ∈ x).
  { unfold FirstMember in H9; destruct H9; clear H10.
    generalize (classic (u∈x)); intros; destruct H10; auto.
    assert (u ∈ (W ~ x)).
    { unfold Difference; apply Theorem4'; split.
      - unfold W; apply Axiom_Scheme; split; Ens.
        apply Theorem132 in H9; auto.
      - unfold Complement; apply Axiom_Scheme; Ens. }
    apply H4 in H11; elim H11; unfold Rrelation, E.
    apply Axiom_SchemeP; split; try apply Theorem49; Ens. }
  assert (y ∈ R /\ LastMember u E y).
  { split; auto; unfold R; apply Axiom_Scheme; Ens. }
  apply Theorem133 in H11; apply H1 in H10; rewrite <- H11 in H10.
  clear H11; unfold Complement in H5; apply Axiom_Scheme in H5.
  destruct H5; unfold NotIn in H11; contradiction.
Qed.

Hint Resolve Theorem137 : set.


(* 138 Theorem  W ∈ R. *)

Theorem Theorem138 : W ∈ R.
Proof.
  unfold R; apply Axiom_Scheme; split; try apply Property_W.
  generalize Axiom_Infinity; intros; destruct H, H, H0.
  assert (W ∩ x = W).
  { apply Theorem137; intros.
    - unfold Subclass; intros; apply Theorem4' in H2; apply H2.
    - apply Theorem4'; split; auto; apply Theorem135; auto.
    - apply Theorem4' in H2; destruct H2; apply Theorem134 in H2.
      apply H1 in H3; apply Theorem4'; split; auto. }
  rewrite <- H2; apply Theorem33 with (x:=x); auto.
  unfold Subclass; intros; apply Theorem4' in H3; apply H3.
Qed.

Hint Resolve Theorem138 : set.


End NInt.

Export NInt.

