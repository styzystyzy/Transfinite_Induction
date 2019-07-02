Require Export NIntegers.


(* Mathematical Induction *)

Theorem MiniMember_Principle : forall S,
  S ⊂ W /\ S ≠ Φ -> exists a, a ∈ S /\ (forall c, c ∈ S -> a ≼ c).
Proof.
  intros; destruct H.
  assert (exists y, FirstMember y E S).
  { assert (WellOrdered E W).
    { apply Theorem107; apply Property_W. }
    unfold WellOrdered in H1; destruct H1; apply H2; auto. }
  destruct H1 as [a H1]; exists a; unfold FirstMember in H1; destruct H1.
  split; auto; intros; double H3; apply H2 in H4.
  unfold Subclass in H; apply H in H1; apply H in H3.
  unfold W in H1, H3; apply Axiom_Scheme in H1; apply Axiom_Scheme in H3.
  destruct H1, H3; unfold NInteger in H5, H6; destruct H5, H6.
  add (Ordinal c) H5; clear H6 H7 H8; apply Theorem110 in H5.
  unfold LessEqual; destruct H5 as [H5|[H5|H5]]; try tauto.
  elim H4; unfold Rrelation, E; apply Axiom_SchemeP; split; auto.
  apply Theorem49; split; Ens.
Qed.

Definition En_S P : Class := \{ λ x, x ∈ W /\ ~ (P x) \}.

Theorem Mathematical_Induction : forall (P: Class -> Prop),
  P Φ -> (forall k, k ∈ W /\ P k -> P (PlusOne k)) ->
  (forall n, n ∈ W -> P n).
Proof.
  intros.
  generalize (classic ((En_S P) = Φ)); intros; destruct H2.
  - generalize (classic (P n)); intros; destruct H3; auto.
    assert (n ∈ (En_S P)). { apply Axiom_Scheme; split; Ens. }
    rewrite H2 in H4; generalize (Theorem16 n); contradiction.
  - assert ((En_S P) ⊂ W).
    { unfold En_S, Subclass; intros; apply Axiom_Scheme in H3; apply H3. }
    add ((En_S P) <> Φ) H3; clear H2.
    apply MiniMember_Principle in H3; destruct H3 as [h H3], H3.
    unfold En_S in H2; apply Axiom_Scheme in H2; destruct H2, H4.
    unfold W in H4; apply Axiom_Scheme in H4; clear H2; destruct H4.
    double H4; unfold NInteger in H6; destruct H6.
    unfold WellOrdered in H7; destruct H7.
    assert (h ⊂ h /\ h ≠ Φ).
    { split; try (unfold Subclass; intros; auto).
      generalize (classic (h = Φ)); intros; destruct H9; auto.
      rewrite H9 in H5; contradiction. }
    apply H8 in H9; clear H8; destruct H9.
    assert (h ∈ R /\ LastMember x E h).
    { split; auto; unfold R; apply Axiom_Scheme; split; auto. }
    apply Theorem133 in H9; unfold PlusOne in H9.
    unfold FirstMember in H8; destruct H8.
    generalize (classic (x ∈ (En_S P))); intros; destruct H11.
    + apply H3 in H11; assert (x ∈ h).
      { rewrite H9; apply Theorem4; right; apply Axiom_Scheme; Ens. }
      unfold LessEqual in H11; destruct H11.
      * add (x ∈ h) H11; clear H12.
        generalize (Theorem102 h x); intros; contradiction.
      * rewrite H11 in H12; generalize (Theorem101 x); contradiction.
    + assert (x ∈ (En_S P) <-> (Ensemble x /\ x ∈ W /\ ~ (P x))).
      { unfold En_S; split; intros.
        - apply Axiom_Scheme in H12; apply H12.
        - apply Axiom_Scheme; auto. }
      apply definition_not in H12; auto; clear H11.
      apply not_and_or in H12; destruct H12.
      * absurd (Ensemble x); Ens.
      * assert (x ∈ W).
        { unfold W; apply Axiom_Scheme; split; Ens.
          apply Theorem132 in H8; auto. }
        apply not_and_or in H11; destruct H11; try contradiction.
        apply NNPP in H11; add (P x) H12; clear H11.
        apply H0 in H12; unfold PlusOne in H12.
        rewrite <- H9 in H12; contradiction.
Qed.

Theorem Complete_Induction : forall (P: Class -> Prop),
  P Φ -> (forall k, k ∈ W /\ (forall m, m ≺ k -> P m) -> P k) ->
  (forall n, n ∈ W -> P n).
Proof.
  intros.
  apply H0; split; auto; generalize dependent n.
  set (P' := (fun n => (forall j, j ∈ n -> P j))).
  generalize (Mathematical_Induction P'); intro.
  apply H1; red; intros.
  - destruct (Theorem16 j H2).
  - destruct H2; apply H0; split; intros.
    + apply Theorem134 in H2.
      unfold W in H2; apply Axiom_Scheme in H2; destruct H2.
      eapply Theorem132 in H5; eauto.
      unfold W; apply Axiom_Scheme; Ens.
    + apply H4; unfold PlusOne in H3.
      apply Axiom_Scheme in H3; destruct H3, H6.
      * unfold W in H2; apply Axiom_Scheme in H2; destruct H2.
        unfold NInteger in H7; destruct H7.
        unfold Ordinal in H7; destruct H7.
        unfold full in H9; eapply H9; eauto.
      * apply Axiom_Scheme in H6; destruct H6; AssE k.
        apply Theorem19 in H8; apply H7 in H8; subst j; auto.
Qed.

Theorem Complete_Induction' : forall (P: Class -> Prop),
  P Φ -> (forall k, k ∈ W /\ (forall j, j ∈ k -> P j) -> P k) ->
  (forall n, n ∈ W -> P n).
Proof.
  intros.
  generalize (classic ((En_S P) = Φ)); intros; destruct H2.
  - generalize (classic (P n)); intros; destruct H3; auto.
    assert (n ∈ (En_S P)). { apply Axiom_Scheme; split; Ens. }
    rewrite H2 in H4; generalize (Theorem16 n); contradiction.
  - assert ((En_S P) ⊂ W).
    { unfold En_S, Subclass; intros; apply Axiom_Scheme in H3; apply H3. }
    add ((En_S P) <> Φ) H3; clear H2.
    apply MiniMember_Principle in H3; destruct H3 as [h H3], H3.
    unfold En_S in H2; apply Axiom_Scheme in H2; destruct H2, H4.
    assert (forall a, a ∈ W -> a = Φ \/ exists b, a = (PlusOne b)).
    { apply Mathematical_Induction; auto; intros; right; eauto. }
    destruct H6 with h; auto.
    + rewrite H7 in H5; contradiction.
    + destruct H7; subst h.
      elim H5; apply H0; split; auto; intros.
      generalize (classic (P j)); intros; destruct H8; auto.
      assert (j ∈ (En_S P)).
      { apply Axiom_Scheme; repeat split; Ens.
        unfold W in H4; apply Axiom_Scheme in H4; clear H2; destruct H4.
        apply Axiom_Scheme; split; Ens; eapply Theorem132; eauto. }
      apply H3 in H9; destruct H9.
      * add ((PlusOne x) ∈ j) H7; clear H9.
        destruct (Theorem102 _ _ H7).
      * subst j; destruct (Theorem101 _ H7).
Qed.

Theorem Mathematical_Induction_Theorem137 : forall (P: Class -> Prop),
  (P Φ -> (forall k, k ∈ W /\ P k -> P (PlusOne k)) ->
  (forall n, n ∈ W -> P n)) <->
  (\{ λ x, x ∈ W /\ P x \} ⊂ W -> Φ ∈ \{ λ x, x ∈ W /\ P x \} -> (forall u,
  u ∈ \{ λ x, x ∈ W /\ P x \} -> (PlusOne u) ∈ \{ λ x, x ∈ W /\ P x \}) ->
  \{ λ x, x ∈ W /\ P x \} = W).
Proof.
  split; intros.
  - apply Axiom_Scheme in H1; destruct H1, H3; apply Axiom_Extent; split; intros.
    + apply H0 in H5; auto.
    + apply H with (n:= z) in H4; auto; try apply Axiom_Scheme; Ens; intros.
      destruct H6; assert (k ∈ \{λ x, x∈W /\ P x\}). { apply Axiom_Scheme; Ens. }
      apply H2 in H8; apply Axiom_Scheme in H8; apply H8.
  - assert (\{ λ x, x ∈ W /\ P x \} ⊂ W).
    { unfold Subclass; intros; apply Axiom_Scheme in H3; apply H3. }
    assert (Φ ∈ \{ λ x, x ∈ W /\ P x \}).
    { apply Axiom_Scheme; generalize (Theorem135 n); intros.
      destruct H4 as [H4 _]; Ens. }
    assert ((forall u, u ∈ \{ λ x, x ∈ W /\ P x \} ->
     (PlusOne u) ∈ \{ λ x, x ∈ W /\ P x \})).
    { intros; apply Axiom_Scheme in H5; destruct H5, H6; double H6.
      apply Theorem134 in H8; apply Axiom_Scheme; repeat split; Ens. }
    apply H in H5; auto; rewrite <- H5 in H2; clear H H3 H4 H5.
    apply Axiom_Scheme in H2; apply H2.
Qed.

