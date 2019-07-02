Require Export Ordinals.

Definition En_nem P : Class := \{ λ u, Ordinal_Number u /\ ~ (P u) \}.

Theorem Transfinite_Induction_Ordinals : forall P: Class -> Prop,
  (forall y, Ordinal_Number y /\ (forall x, x ≺ y -> P x) -> P y) ->
  (forall z, Ordinal_Number z -> P z).
Proof.
  intros.
  generalize (classic ((En_nem P) = Φ)); intros; destruct H1.
  - generalize (classic (P z)); intros; destruct H2; auto.
    unfold Ordinal_Number in H1; assert (z ∈ (En_nem P)).
    { unfold En_nem; apply Axiom_Scheme; repeat split; Ens. }
    rewrite H1 in H3; destruct (Theorem16 _ H3).
  - generalize Theorem113; intros; destruct H2 as [H2 _].
    apply Theorem107 in H2; assert ((En_nem P) ⊂ R).
    { red; intros; apply Axiom_Scheme in H3; destruct H3, H4; auto. }
    apply Lemma97 with (r:= E) in H3; auto; clear H2.
    unfold WellOrdered in H3; destruct H3 as [_ H2].
    assert ((En_nem P) ⊂ (En_nem P) /\ (En_nem P) ≠ Φ).
    { split; red; intros; auto. } apply H2 in H3; clear H1 H2.
    destruct H3 as [y H1]; unfold FirstMember in H1; destruct H1.
    unfold En_nem in H1; apply Axiom_Scheme in H1; destruct H1, H3.
    destruct H4; apply H; split; auto; intros x H4. 
    generalize (classic (P x)); intros; destruct H5; auto.
    assert (x ∈ (En_nem P)).
    { unfold En_nem; apply Axiom_Scheme; repeat split; Ens.
      unfold Ordinal_Number; red in H3; unfold R in H3; unfold R.
      apply Axiom_Scheme in H3; destruct H3 as [_ H3].
      apply Axiom_Scheme; split; Ens; apply (Theorem111 y _); auto. }
    apply H2 in H6; destruct H6; unfold Rrelation, E.
    apply Axiom_SchemeP; split; try apply Theorem49; Ens.
Qed.