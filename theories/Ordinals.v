Require Export Elementary_Set.

Module Ord.

(* WELL ORDERING *)

(* 81 Definition  x r y if and only [x,y] ∈ r. *)

Definition Rrelation x r y : Prop := [x,y] ∈ r.

Hint Unfold Rrelation : set.


(* 82 Definition  r connects x if and only if when u and v belong to x either
   u r v or v r u or v = u. *)

Definition Connect r x : Prop := 
  forall u v, u∈x /\ v∈x -> (Rrelation u r v) \/ (Rrelation v r u) \/ (u=v).

Hint Unfold Connect : set.


(* 83 Definition  r is transitive in x if and only if, when u, v, and w
   are members of x and u r v and v r w, then u r w. *)

Definition Transitive r x : Prop :=
  forall u v w, (u∈x /\ v∈x /\ w∈x /\ Rrelation u r v /\  Rrelation v r w) ->
  Rrelation u r w.

Hint Unfold Transitive: set.


(* 84 Definition  r is asymmetric in x if and only if, when u and v are
   members of x and u r v, then it is not true that v r u. *)

Definition Asymmetric r x : Prop := 
  forall u v, (u ∈ x /\ v ∈ x /\ Rrelation u r v) -> ~ Rrelation v r u.

Corollary Property_Asy : forall r x u,
  Asymmetric r x -> u ∈ x -> ~ Rrelation u r u.
Proof.
  intros; intro. 
  unfold Asymmetric in H; eapply H; eauto.
Qed.

Hint Unfold Asymmetric: set.
Hint Resolve Property_Asy: set.


(* 85 Definition Inequality (x y:Class) := ~ (x = y) . *)

(* Notation "x ≠ y" := (Inequality x y) (at level 70). *)


(* 86 Definition  z is an r-first member of x if and only if z∈x and if y∈x,
   then it is false that y r z. *)

Definition FirstMember z r x : Prop :=
  z ∈ x /\ (forall y, y ∈ x -> ~ Rrelation y r z).

Hint Unfold FirstMember : set.


(* 87 Definition  r well-orders x if and only if r connects x and if y⊂x and
   y ≠ Φ, then there is an r-first member of y. *)

Definition WellOrdered r x : Prop :=
  Connect r x /\ (forall y, y ⊂ x /\ y ≠ Φ -> exists z, FirstMember z r y).

Hint Unfold WellOrdered : set.


(* 88 Theorem  If r well-orders x, then r is transitive in x and r is
   asymmetric in x. *)

Lemma Lemma88 : forall x u v w,
  Ensemble u -> Ensemble v -> Ensemble w -> 
  x ∈ ([u] ∪ [v] ∪ [w]) -> x = u \/ x= v \/ x = w.
Proof.
  intros.
  apply Theorem19 in H; apply Theorem19 in H0; apply Theorem19 in H1.
  apply Axiom_Scheme in H2; destruct H2, H3.
  - left; apply Axiom_Scheme in H3; destruct H3; auto.
  - apply Axiom_Scheme in H3; destruct H3, H4.
    + right; left; apply Axiom_Scheme in H4; destruct H4; auto.
    + right; right; apply Axiom_Scheme in H4; destruct H4; auto.
Qed.

Theorem Theorem88 : forall r x,
  WellOrdered r x -> Transitive r x /\ Asymmetric r x .
Proof.
  intros; generalize H; intro.
  unfold WellOrdered in H0; destruct H0.
  assert (Asymmetric r x).
  { unfold Asymmetric; intros.
    destruct H2, H3; AssE u; AssE v.
    assert (([u | v] ⊂ x) /\ ([u | v] ≠ Φ)).
    { split.
      - unfold Subclass; intros; apply Axiom_Scheme in H7; destruct H7, H8.
        + apply Theorem19 in H5; apply Axiom_Scheme in H8.
          destruct H8; rewrite H9; auto.
        + apply Theorem19 in H6; apply Axiom_Scheme in H8.
          destruct H8; rewrite H9; auto.
      - apply Lemma35; exists u; apply Axiom_Scheme; split; auto;
        left; apply Axiom_Scheme; split; auto. }
  apply H1 in H7; destruct H7; unfold FirstMember in H7; destruct H7.
  apply Theorem46 in H7; auto; destruct H7; subst x0.
  - apply H8; apply Axiom_Scheme; split; auto; right; apply Axiom_Scheme; split; auto.
  - intro; apply H8 with u; auto.
    apply Axiom_Scheme; split; auto; left; apply Axiom_Scheme; split; auto. }
  split; auto; unfold Transitive; intros.
  - destruct H3, H4, H5, H6; unfold Connect in H0; specialize H0 with w u.
    destruct H0 as [H0 | [H0 | H0]]; try split; auto.
    * assert (([u] ∪ [v] ∪ [w] ⊂ x) /\ ([u] ∪ [v] ∪ [w] ≠ Φ)).
      { split.
        - unfold Subclass; intros; apply Axiom_Scheme in H8.
          destruct H8 as [_ H8]; destruct H8.
          + AssE u; apply Theorem19 in H9; apply Axiom_Scheme in H8.
            destruct H8; rewrite H10; auto.
          + apply Axiom_Scheme in H8; destruct H8 as [_ H8]; destruct H8.
            * AssE v; apply Theorem19 in H9; apply Axiom_Scheme in H8.
              destruct H8; rewrite H10; auto.
            * AssE w; apply Theorem19 in H9; apply Axiom_Scheme in H8.
              destruct H8; rewrite H10; auto.
        - intro; generalize (Theorem16 u); intro.
          apply H9; rewrite <- H8; apply Axiom_Scheme; split; Ens.
          left; apply Axiom_Scheme; split; intros; auto; Ens. }
      apply H1 in H8; destruct H8.
      unfold FirstMember in H8; destruct H8.
      assert (u ∈ ([u] ∪ [v] ∪ [w])).
      { apply Theorem4; left; apply Axiom_Scheme; split; Ens. }
      assert (v ∈ ([u] ∪ [v] ∪ [w])).
      { apply Theorem4; right; apply Axiom_Scheme; split; Ens.
        left; apply Axiom_Scheme; split; Ens. }
      assert (w ∈ ([u] ∪ [v] ∪ [w])).
      { apply Theorem4; right; apply Axiom_Scheme; split; Ens. 
        right; apply Axiom_Scheme; split; Ens. }
      apply Lemma88 in H8; Ens; destruct H8 as [H8|[H8|H8]]; subst x0.
      + apply H9 in H12; contradiction.
      + apply H9 in H10; contradiction.
      + apply H9 in H11; contradiction.
    * subst w; unfold Asymmetric in H2; absurd (Rrelation u r v); auto.
Qed.

Hint Resolve Theorem88: set.


(* 89 Definition  y is an r-section of x if and only if y⊂x, r well-orders x,
   and for each u and v such that u∈x, v∈y, and u r v it is true that u∈y. *)

Definition Section y r x : Prop :=
  y ⊂ x /\ WellOrdered r x /\
  (forall u v, (u ∈ x /\ v ∈ y /\ Rrelation u r v) -> u ∈ y).

Hint Unfold Section : set.


(* 90 Theorem  If n ≠ Φ and each member of n is an r-section of x, then ∪n and
   ∩n are r-sections of x. *)

Theorem Theorem90 : forall n x r,
  n ≠ Φ /\ (forall y, y ∈ n -> Section y r x) -> 
  Section (∩ n) r x /\ Section (∪ n) r x.
Proof.
  intros; destruct H; double H.
  apply Lemma35 in H; destruct H; double H; apply H0 in H.
  red in H; destruct H, H3; split; unfold Section; intros.
  - split; try split; auto; intros.
    + unfold Subclass; intros; apply Axiom_Scheme in H5.
      destruct H5; apply H6 in H2; auto.
    + destruct H5, H6; apply Axiom_Scheme; split; intros; Ens.
      apply Axiom_Scheme in H6; destruct H6; double H8; apply H0 in H8.
      unfold Section in H8; eapply H8; split; eauto.
  - split; try split; auto; intros.
    + unfold Subclass; intros; apply Axiom_Scheme in H5; destruct H5, H6, H6.
      apply H0 in H7; unfold Section in H7; destruct H7 as [H7 _]; auto.
    + destruct H5, H6; apply Axiom_Scheme; split; intros; Ens.
      apply Axiom_Scheme in H6; destruct H6, H8, H8.
      double H9; apply H0 in H9; unfold Section in H9; destruct H9, H11.
      exists x1; split; auto; eapply H12; split; eauto.
Qed.

Hint Resolve Theorem90 : set.


(* 91 Theorem  If y is an r-section of x an y≠x, then y = {u : u∈x and u r v}
   for some v in x. *)

Theorem Theorem91 : forall x y r,
  Section y r x /\ y≠x ->
  (exists v, v ∈ x /\ y = \{ λ u, u ∈ x /\ Rrelation u r v \}).
Proof.
  intros; destruct H.
  assert (exists v0, FirstMember v0 r (x ~ y)).
  { unfold Section in H; destruct H, H1; unfold WellOrdered in H1; destruct H1.
    assert ((x ~ y) ⊂ x).
    { unfold Subclass; intros; apply Axiom_Scheme in H4; tauto. }
    generalize (classic (x ~ y = Φ)); intro; destruct H5.
    - apply Property_Φ in H; apply H in H5.
      apply Property_Ineq in H0; contradiction.
    - apply H3; split; auto. }
  destruct H1; unfold FirstMember in H1; destruct H1.
  exists x0; apply Axiom_Scheme in H1; destruct H1, H3.
  split; auto; apply Axiom_Extent; split; intros.
  unfold Section in H; destruct H, H6.
  - apply Axiom_Scheme; repeat split; Ens; assert (z ∈ x); auto.
    unfold WellOrdered in H6; destruct H6 as [H6 _]; unfold Connect in H6.
    specialize H6 with x0 z; destruct H6 as [H6 | [H6 | H6]]; auto.
    + assert (x0 ∈ y). { apply H7 with z; repeat split; auto. }
      apply Axiom_Scheme in H4; destruct H4; contradiction.
    + apply Axiom_Scheme in H4; destruct H4; subst x0; contradiction.
  - apply Axiom_Scheme in H5; destruct H5, H6.
    generalize (classic (z ∈ (x ~ y))); intro; destruct H8.
    + apply H2 in H8; contradiction.
    + generalize (classic (z ∈ y)); intro; destruct H9; auto.
      elim H8; apply Axiom_Scheme.
      repeat split; auto; apply Axiom_Scheme; tauto.
Qed.

Hint Resolve Theorem91 : set.


(* 92 Theorem  If x and y are r-sections of z, then x⊂y or y⊂x. *)

Theorem Theorem92 : forall x y z r,
  Section x r z /\ Section y r z -> x ⊂ y \/ y ⊂ x.
Proof.
  intros; destruct H.
  generalize (classic (x = z)); intro; destruct H1.
  - right; red in H0; subst z; tauto.
  - generalize (classic (y = z)); intro; destruct H2.
    + left; red in H; subst z; tauto.
    + apply Lemma_xy with (x:= (Section x r z)) in H1; auto.
      apply Lemma_xy with (x:= (Section y r z)) in H2; auto.
      apply Theorem91 in H1; destruct H1, H1.
      apply Theorem91 in H2; destruct H2, H2.
      unfold Section in H; destruct H as [_ [H _]].
      unfold WellOrdered in H; destruct H as [H _].
      unfold Section in H0; destruct H0, H5.
      apply Theorem88 in H5; destruct H5; unfold Transitive in H5.
      assert ((x0 ∈ z) /\ (x1 ∈ z)); try split; auto.
      unfold Connect in H; generalize (H _ _ H8); intros.
      destruct H9 as [H9 | [H9 | H9]].
      * left; unfold Subclass; intros; rewrite H3 in H10.
        apply Axiom_Scheme in H10; destruct H10, H11; rewrite H4.
        apply Axiom_Scheme.
        repeat split; auto; apply H5 with x0; auto.
      * right; unfold Subclass; intros; rewrite H4 in H10.
        apply Axiom_Scheme in H10; destruct H10, H11.
        rewrite H3; apply Axiom_Scheme.
        repeat split; auto; apply H5 with x1; auto.
      * right; subst x0; rewrite H3, H4; unfold Subclass; intros; auto.
Qed.

Hint Resolve Theorem92 : set.


(* 93 Definition  f is r-s order preserving if and only if f is a function,
   r well-orders domain f, s well-orders range f, and f[u] s f[v] whenever u
   and v are members of domain f such that u r v. *)

Definition Order_Pr f r s : Prop := 
  Function f /\ WellOrdered r dom(f) /\ WellOrdered s ran(f) /\
  (forall u v, u ∈ dom(f) /\ v ∈ dom(f) /\ Rrelation u r v ->
  Rrelation f[u] s f[v]).

Hint Unfold Order_Pr : set.


(* 94 Theorem  If x is an r-section of y and f is an r-r order-preserving
   function on x to y, then for each u in x it is false that f[u] r u. *)

Theorem Theorem94 : forall x r y f,
  Section x r y /\ Order_Pr f r r /\ On f x /\ To f y -> 
  (forall u, u ∈ x -> ~ Rrelation f[u] r u).
Proof.
  intros; destruct H, H1, H2.
  unfold Order_Pr in H1; destruct H1, H4, H5.
  unfold On in H2; destruct H2 as [H2 H7].
  unfold To in H3; destruct H3 as [_ H3].
  generalize (classic (\{ λ u, u ∈ x /\ Rrelation (Value f u) r u \} = Φ)).
  intros; destruct H8.
  - intro.
    assert (u ∈ Φ). { rewrite <- H8; apply Axiom_Scheme; repeat split; Ens. }
    generalize (Theorem16 u); intro; contradiction.
  - unfold Section in H; destruct H, H9.
    assert (\{ λ u, u ∈ x /\ Rrelation f [u] r u \} ⊂ y).
    { red; intros; apply Axiom_Scheme in H11; destruct H11, H12; auto. }
    unfold WellOrdered in H9; destruct H9.
    add (\{ λ u, u ∈ x /\ Rrelation f [u] r u \} ≠ Φ) H11.
    apply H12 in H11; destruct H11; unfold FirstMember in H11; destruct H11.
    apply Axiom_Scheme in H11; destruct H11, H14.
    assert (f[x0] ∈ ran( f)).
    { rewrite <- H7 in H14; apply Property_Value in H14; auto.
      apply Property_ran in H14; auto. }
    assert (f [x0] ∈ y); auto; subst x.
    assert (f [x0] ∈ \{ λ u, u ∈ dom( f) /\ Rrelation f [u] r u \}).
    { apply Axiom_Scheme; repeat split; try Ens.
      apply H6; repeat split; auto; apply H10 with x0; split; auto. }
    apply H13 in H7; contradiction.
Qed.

Hint Resolve Theorem94 : set.


(* 95 Definition  f is a 1_1 function iff both f and f⁻¹ are functions. *)

Definition Function1_1 f : Prop := Function f /\ Function (f⁻¹).

Hint Unfold Function1_1 : set.


(* 96 Theorem  If f is r-s order preserving, then f is a 1_1 function and
   f ⁻¹ is s-r order preserving. *)

Lemma Lemma96 : forall f, dom( f) = ran( f⁻¹ ).
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme in H; destruct H, H0; apply Axiom_Scheme; split; auto.
    exists x; apply Axiom_SchemeP; split; auto; apply Lemma61; Ens.
  - apply Axiom_Scheme in H; destruct H, H0; apply Axiom_Scheme.
    split; auto; exists x; apply Axiom_SchemeP in H0; tauto.
Qed.

Lemma Lemma96' : forall f, ran( f) = dom( f⁻¹ ).
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme in H; destruct H, H0; apply Axiom_Scheme; split; auto.
    exists x; apply Axiom_SchemeP; split; auto; apply Lemma61; Ens.
  - apply Axiom_Scheme in H; destruct H, H0; apply Axiom_Scheme.
    split; auto; exists x; apply Axiom_SchemeP in H0; tauto.
Qed.

Lemma Lemma96'' : forall f u,
  Function f -> Function f⁻¹ -> u ∈ ran(f) ->  (f⁻¹)[u] ∈ dom(f).
Proof.
  intros; rewrite Lemma96' in H1; apply Property_Value in H1; auto.
  apply Axiom_SchemeP in H1; destruct H1; apply Property_dom in H2; auto.
Qed.

Lemma Lemma96''' : forall f u,
  Function f -> Function f⁻¹ -> u ∈ ran(f) -> u = f[(f⁻¹)[u]].
Proof.
  intros; generalize (Lemma96'' _ _ H H0 H1); intro.
  apply Property_Value in H2; auto; rewrite Lemma96' in H1.
  apply Property_Value in H1; auto; apply Axiom_SchemeP in H1.
  destruct H1; red in H; destruct H; eapply H4; eauto.
Qed.

Theorem Theorem96 : forall f r s,
  Order_Pr f r s -> Function1_1 f /\ Order_Pr (f⁻¹) s r.
Proof.
  intros; unfold Order_Pr in H; destruct H, H0, H1.
  assert (Function1_1 f).
  { unfold Function1_1; split; auto; unfold Function; split; intros.
    - red; intros; PP H3 a b; Ens.
    - destruct H3; rename y into u; rename z into v.
      apply Axiom_SchemeP in H3; destruct H3; apply Axiom_SchemeP in H4.
      destruct H4; double H5; double H6.
      apply Property_dom in H5; apply Property_dom in H6.
      double H7; double H8; apply Property_dom in H7.
      apply Property_dom in H8; rewrite Theorem70 in H9; auto.
      apply Axiom_SchemeP in H9; destruct H9 as [_ H9].
      rewrite Theorem70 in H10; auto.
      apply Axiom_SchemeP in H10; destruct H10 as [_ H10].
      rewrite H10 in H9; symmetry in H9; clear H10.
      apply Property_Value in H7; apply Property_Value in H8; auto.
      apply Property_ran in H7; apply Property_ran in H8.
      double H0; double H1; apply Theorem88 in H11; destruct H11.
      unfold WellOrdered in H1; destruct H1 as [H1 _].
      unfold Connect in H1; specialize H1 with f [u] f [v].
      unfold WellOrdered in H0; destruct H0.
      unfold Connect in H0; specialize H0 with u v.
      destruct H0 as [H0 | [H0 | H0]]; try split; auto.
      + assert (Rrelation f [u] s f [v]); try apply H2; try tauto.
        rewrite H9 in H14; generalize (Property_Asy _ _ _ H12 H8).
        intro; contradiction.
      + assert (Rrelation f [v] s f [u]); try apply H2; try tauto.
        rewrite H9 in H14; generalize (Property_Asy _ _ _ H12 H8).
        intro; contradiction. }
  split; auto.
  - unfold Function1_1 in H3; destruct H3 as [_ H3]; unfold Order_Pr; intros.
    repeat rewrite <- Lemma96; repeat rewrite <- Lemma96'; split; auto.
    split; auto; split; intros; auto; destruct H4, H5.
    assert ((f⁻¹) [u] ∈ dom(f)); try apply Lemma96''; auto.
    assert ((f⁻¹) [v] ∈ dom(f)); try apply Lemma96''; auto.
    unfold WellOrdered in H0; destruct H0 as [H0 _]; unfold Connect in H0.
    specialize H0 with (f⁻¹) [u] (f⁻¹) [v].
    destruct H0 as [H0 | [H0 | H0]]; try split; auto.
    + assert (Rrelation f  [(f⁻¹) [v]] s f [(f⁻¹) [u]] ); auto.
      rewrite <- Lemma96''' in H9; rewrite <- Lemma96''' in H9; auto.
      apply Theorem88 in H1; destruct H1; unfold Asymmetric in H10.
      generalize (Lemma_xy _ _ H5 (Lemma_xy _ _ H4 H9)); intro.
      generalize (H10 _ _ H11); intro; contradiction.
    + assert (f [(f⁻¹) [u]] = f [(f⁻¹) [v]]); rewrite H0; auto.
      rewrite <- Lemma96''' in H9; rewrite <- Lemma96''' in H9; auto.
      apply Theorem88 in H1; destruct H1.
      rewrite H9 in H6; apply Property_Asy with (r:=s) in H5; tauto.
Qed.

Hint Resolve Theorem96 : set.


(* 97 Theorem  If f and g are r-s order preserving, domain f and domain g are
   r-sections of x and range f and range g are s-sections of y, then f⊂g or
   g⊂f. *)

Lemma Lemma97 : forall y r x,
  WellOrdered r x -> y ⊂ x -> WellOrdered r y.
Proof.
  intros; unfold WellOrdered in H; destruct H.
  unfold WellOrdered; intros; split; intros.
  - red; intros.
    apply H; destruct H2; split; auto.
  - specialize H1 with y0.
    apply H1; destruct H2.
    split; auto; eapply Theorem28; eauto.
Qed.

Lemma Lemma97' :  forall f g u r s v x y,
  Order_Pr f r s /\ Order_Pr g r s -> 
  FirstMember u r (\{ λ a ,a ∈ (dom( f) ∩ dom( g)) /\ f [a] ≠ g [a] \}) ->
  g[v] ∈ ran( g) -> Section ran( f) s y -> Section dom( f) r x -> 
  Section dom( g) r x -> Rrelation g [v] s g [u] -> 
  f[u] = g[v] -> f ⊂ g \/ g ⊂ f.
Proof.
  intros.
  unfold FirstMember in H0; destruct H0.
  apply Axiom_Scheme in H0; destruct H0, H8.
  apply Axiom_Scheme in H8; destruct H8 as [_ [H8 H10]].
  destruct H; unfold Order_Pr in H, H11.
  apply Property_Value in H8; apply Property_Value in H10; try tauto.
  apply Property_ran in H8; apply Property_ran in H10; auto.
  assert (Rrelation v r u).
  { elim H11; intros; clear H13.
    apply Theorem96 in H11; destruct H11 as [_ H11].
    red in H11; destruct H11 as [H11 [_ [_ H13]]].
    double H1; double H10; rewrite Lemma96' in H14, H15.
    apply Property_Value' in H10; auto; apply Property_dom in H10.
    rewrite Lemma96 in H10; apply Property_Value' in H1; auto.
    apply Property_dom in H1; rewrite Lemma96 in H1.
    rewrite Lemma96''' with (f:=g⁻¹); try (rewrite Theorem61; apply H12); auto.
    pattern v; rewrite Lemma96''' with (f:=(g⁻¹));
    try rewrite Theorem61; try apply H11; try apply H12; auto. }
  assert (v ∈ \{ λ a, a ∈ (dom(f) ∩ dom(g)) /\ f [a] ≠ g [a] \}).
  { apply Property_Value' in H1; try tauto; apply Property_dom in H1.
    apply Property_Value' in H8; try tauto; apply Property_dom in H8.
    apply Axiom_Scheme; repeat split; try Ens.
    - apply Axiom_Scheme; repeat split; try Ens.
      apply H3 with u; repeat split; auto.
      unfold Section in H4; apply H4; auto.
    - intro.
      assert (v ∈ dom(f)).
      { apply H3 with u; repeat split; auto; apply H4 in H1; auto. }
      assert (Rrelation f [v] s f [u]).
      { apply H; repeat split; auto. }
      rewrite H13 in H15; unfold Section in H2; destruct H2, H16.
      generalize (Lemma97 _ _ _ H16 H2); intro.
      apply Theorem88 in H18; destruct H18.
      rewrite <- H13 in H15; rewrite H6 in H15; rewrite <- H13 in H15.
      apply Property_Value in H14; try tauto; apply Property_ran in H14.
      generalize (Property_Asy _ _ _ H19 H14); intro; contradiction. }
  apply H7 in H13; contradiction.
Qed.

Lemma Lemma97'' : forall f g,
  \{ λ a, a ∈ (dom(f) ∩ dom(g)) /\ f[a] ≠ g[a] \} =
  \{ λ a, a ∈ (dom(g) ∩ dom(f)) /\ g[a] ≠ f[a] \}.
Proof.
  intros.
  apply Axiom_Extent; split; intros; rewrite Theorem6'; apply Axiom_Scheme in H;
  apply Axiom_Scheme; repeat split; try tauto; apply Property_Ineq; tauto.
Qed.

Lemma Lemma97''' : forall f g,
  f ⊂ g \/ g ⊂ f <-> g ⊂ f \/ f ⊂ g.
Proof.
  intros; split; intros; destruct H; tauto.
Qed.

Theorem Theorem97 : forall f g r s x y,
  Order_Pr f r s /\ Order_Pr g r s -> 
  Section dom(f) r x /\ Section dom(g) r x -> 
  Section ran(f) s y /\ Section ran(g) s y -> f ⊂ g \/ g ⊂ f.
Proof.
  intros; destruct H, H0, H1.
  assert (Order_Pr (g ⁻¹) s r).
  { apply Theorem96 in H2; tauto. }
  generalize (classic (\{ λ a, a ∈ (dom(f) ∩ dom(g)) /\ f[a] ≠ g[a] \} = Φ)).
  intro; destruct H6.
  - generalize (Lemma_xy _ _ H0 H3); intro.
    unfold Order_Pr in H; destruct H; unfold Order_Pr in H2; destruct H2.
    generalize (Theorem92 _ _ _ _ H7); intro; destruct H10.
    + left; unfold Subclass; intros.
      rewrite Theorem70 in H11; auto; PP H11 a b; double H12.
      rewrite <- Theorem70 in H12; auto; apply Property_dom in H12.
      apply Axiom_SchemeP in H13; destruct H13.
      rewrite Theorem70; auto; apply Axiom_SchemeP; split; auto; rewrite H14.
      generalize (classic (f[a] = g[a])); intro; destruct H15; auto.
      assert (a ∈ \{ λ a, a ∈ (dom( f) ∩ dom( g)) /\ f [a] ≠ g [a] \}).
      { apply Axiom_Scheme; split; Ens; split; auto.
        apply Theorem30 in H10; rewrite H10; auto. }
      eapply Axiom_Extent in H6; apply H6 in H16.
      generalize (Theorem16 a); contradiction.
    + right; unfold Subclass; intros.
      rewrite Theorem70 in H11; auto; PP H11 a b; double H12.
      rewrite <- Theorem70 in H12; auto; apply Property_dom in H12.
      apply Axiom_SchemeP in H13; destruct H13.
      rewrite Theorem70; auto; apply Axiom_SchemeP; split; auto; rewrite H14.
      generalize (classic (f[a] = g[a])); intro; destruct H15; auto.
      assert (a ∈ \{ λ a, a ∈ (dom( f) ∩ dom( g)) /\ f [a] ≠ g [a] \}).
      { apply Axiom_Scheme; split; Ens; split; auto. apply Theorem30 in H10.
        rewrite Theorem6' in H10; rewrite H10; auto. }
      eapply Axiom_Extent in H6; apply H6 in H16.
      generalize (Theorem16 a); contradiction.
  - assert (\{ λ a, a ∈ (dom( f) ∩ dom( g)) /\ f [a] ≠ g [a] \} ⊂ dom(f)).
    { unfold Subclass; intros; apply Axiom_Scheme in H7; destruct H7, H8.
      apply Theorem4' in H8; tauto. }
    double H2; double H; unfold Order_Pr in H9; destruct H9, H10, H11.
    unfold WellOrdered in H10; destruct H10.
    generalize (Lemma_xy _ _ H7 H6); intro.
    apply H13 in H14; destruct H14 as [u H14].
    double H14; unfold FirstMember in H15; destruct H15.
    apply Axiom_Scheme in H15; destruct H15, H17.
    unfold Order_Pr in H2; destruct H2 as [H19 [_ [H2 _]]].
    apply Axiom_Scheme in H17; destruct H17 as [_ [H17 H20]].
    double H17; double H20.
    apply Property_Value in H17; apply Property_Value in H20; auto.
    apply Property_ran in H17; apply Property_ran in H20.
    generalize (Lemma_xy _ _ H1 H4); intro.
    apply Theorem92 in H23; auto; destruct H23.
    + apply H23 in H17; double H17.
      apply Axiom_Scheme in H17; destruct H17 as [_ [v H17]].
      rewrite Theorem70 in H17; auto; apply Axiom_SchemeP in H17.
      destruct H17; rewrite H25 in H24.
      generalize (Lemma_xy _ _ H24 H20); intro.
      unfold WellOrdered in H2; destruct H2 as [H2 _].
      unfold Connect in H2; apply H2 in H26.
      destruct H26 as [H26 | [H26 | H26]].
      * apply (Lemma97' f g u r s v x y); auto.
      * rewrite <- H25 in H26.
        assert (g [u] ∈ ran( f)).
        { unfold Section in H4; apply H4 in H20.
          unfold Section in H1; apply H1 with f[u]; repeat split; auto.
          apply Property_ran with u; apply Property_Value; auto. }
        double H27; apply Axiom_Scheme in H27; destruct H27 as [_ [v1 H27]].
        rewrite Theorem70 in H27; auto.
        apply Axiom_SchemeP in H27; destruct H27 as [_H27].
        rewrite H27 in H26, H28; rewrite Lemma97'' in H14; apply Lemma97'''.
        apply (Lemma97' g f u r s v1 x y); try tauto.
      * rewrite H26 in H25; contradiction.
    + apply H23 in H20; double H20.
      apply Axiom_Scheme in H20; destruct H20 as [_ [v H20]].
      rewrite Theorem70 in H20; auto.
      apply Axiom_SchemeP in H20; destruct H20; rewrite H25 in H24.
      generalize (Lemma_xy _ _ H17 H24); intro.
      unfold WellOrdered in H11; destruct H11 as [H11 _].
      unfold Connect in H11; apply H11 in H26.
      destruct H26 as [H26 | [H26 | H26]]; try contradiction.
      * rewrite <- H25 in H26.
        assert (f [u] ∈ ran( g)).
        { unfold Section in H1; apply H1 in H17.
          unfold Section in H4; eapply H4; repeat split; eauto.
          apply Property_ran with u; apply Property_Value; auto. }
        double H27; apply Axiom_Scheme in H27; destruct H27 as [_ [v1 H27]].
        rewrite Theorem70 in H27; auto; apply Axiom_SchemeP in H27.
        destruct H27 as [_H27]; rewrite H27 in H26, H28.
        apply (Lemma97' f g u r s v1 x y); try tauto.
      * rewrite Lemma97'' in H14; apply Lemma97'''.
        apply (Lemma97' g f u r s v x y); try tauto.
      * rewrite <- H25 in H26; contradiction.
Qed.

Hint Resolve Theorem97 : set.


(* 98 Definition  f is r-s order preserving in x and y if and only if r
   well-orders x, s well-orders y, f is r-s order preserving, domain f is an
   r-section of x, and range f is an s-section of y. *)

Definition Order_PXY f x y r s : Prop :=
  WellOrdered r x /\ WellOrdered s y /\ Order_Pr f r s /\
  Section dom(f) r x /\ Section ran(f) s y.

Hint Unfold Order_PXY : set.


(* 99 Theorem  If r well-orders x and s well-orders y, then there is a function
   f which is r-s order preserving in x and y such that either domain f = x or
   range f = y. *)

Definition En_f x y r s := 
  \{\ λ u v, u ∈ x /\ (exists g, Function g /\ Order_PXY g x y r s /\
  u ∈ dom(g) /\ [u,v] ∈ g ) \}\.

Lemma Lemma99 : forall y r x,
  WellOrdered r x -> Section y r x -> WellOrdered r y.
Proof.
  intros; red in H0; eapply Lemma97; eauto; tauto.
Qed.

Lemma Lemma99' : forall a b f z,
  ~ a ∈ dom(f) -> Ensemble a -> Ensemble b ->
  (z ∈ dom(f) -> (f ∪ [[a,b]]) [z] = f [z]).
Proof.
  intros; apply Axiom_Extent; split; intros; apply Axiom_Scheme in H3; destruct H3;
  apply Axiom_Scheme; split; intros; auto.
  - apply H4; apply Axiom_Scheme in H5; destruct H5; apply Axiom_Scheme; split; auto.
    apply Axiom_Scheme; split; Ens.
  - apply H4; apply Axiom_Scheme in H5; destruct H5.
    apply Axiom_Scheme in H6; destruct H6, H7; apply Axiom_Scheme; auto.
    assert ([a, b] ∈ μ). { apply Theorem19; apply Theorem49; tauto. }
    apply Axiom_Scheme in H7; destruct H7; apply H9 in H8.
    apply Theorem55 in H8; destruct H8; Ens.
    rewrite H8 in H2; contradiction.
Qed.

Lemma Lemma99'' : forall a b f z,
  ~ a ∈ dom(f) -> Ensemble a -> Ensemble b ->
  (z=a -> (f ∪ [[a,b]]) [z] = b).
Proof.
  intros; apply Axiom_Extent; split; intros; subst z.
  - apply Axiom_Scheme in H3; destruct H3; apply H3; apply Axiom_Scheme; split; auto.
    apply Axiom_Scheme; split; try apply Theorem49; try tauto.
    right; apply Axiom_Scheme; split; try apply Theorem49; try tauto.
  - apply Axiom_Scheme; split; intros; Ens.
    apply Axiom_Scheme in H2; destruct H2; apply Axiom_Scheme in H4; destruct H4, H5.
    + apply Property_dom in H5; contradiction.
    + apply Axiom_Scheme in H5; destruct H5.
      assert ([a, b] ∈ μ). { apply Theorem19; apply Theorem49; tauto. }
      generalize (H6 H7); intro; apply Theorem55 in H8;
      apply Theorem49 in H4; auto; destruct H8; rewrite H9; auto.
Qed.

Lemma Lemma99''' : forall y r x a b,  
  Section y r x -> a ∈ y -> ~ b ∈ y -> b ∈ x -> Rrelation a r b.
Proof.
  intros; unfold Section in H; destruct H, H3.
  unfold WellOrdered in H3; destruct H3; unfold Connect in H3.
  assert (a ∈ x); auto; generalize (Lemma_xy _ _ H2 H6); intro.
  apply H3 in H7; destruct H7 as [H7 | [H7 | H7]]; auto.
  - assert (b ∈ y). { eapply H4; eauto. } contradiction.
  - rewrite H7 in H1; contradiction.
Qed.

Theorem Theorem99 : forall r s x y,
  WellOrdered r x /\ WellOrdered s y ->
  exists f, Function f /\ Order_PXY f x y r s /\((dom(f) = x) \/ (ran(f) = y)).
Proof.
  intros.
  assert (Function (En_f x y r s)).
  { unfold Function; split; intros.
    - unfold Relation; intros; PP H0 a b; eauto.
    - destruct H0; apply Axiom_SchemeP in H0; destruct H0, H2, H3, H3, H4, H5.
      unfold Order_PXY in H4; destruct H4 as [_ [_ [H4 [H7 H8]]]].
      apply Axiom_SchemeP in H1; destruct H1, H9, H10, H10, H11, H12.
      unfold Order_PXY in H11; destruct H11 as [_ [_ [H11 [H14 H15]]]].
      assert (x1 ⊂ x2 \/ x2 ⊂ x1). { apply (Theorem97 x1 x2 r s x y); tauto. }
      destruct H16.
      + apply H16 in H6; eapply H10; eauto.
      + apply H16 in H13; eapply H3; eauto. }
  exists (En_f x y r s); split; auto.
  assert (Section (dom(En_f x y r s)) r x).
  { unfold Section; split.
    - unfold Subclass; intros; apply Axiom_Scheme in H1; destruct H1, H2.
      apply Axiom_SchemeP in H2; tauto.
    - split; try tauto; intros; destruct H1, H2.
      apply Axiom_Scheme in H2; destruct H2, H4.
      apply Axiom_SchemeP in H4; destruct H4, H5, H6; apply Axiom_Scheme; split; Ens.
      exists ((En_f x y r s)[u]); apply Property_Value; auto.
      apply Axiom_Scheme; split; Ens.
      assert (u ∈ dom( x1)).
      { destruct H6, H7; unfold Order_PXY in H7; destruct H7, H9, H10, H11.
        unfold Section in H11; destruct H11, H13; apply H14 with v.
        destruct H8; tauto. }
      exists (x1[u]); apply Axiom_SchemeP; repeat split; auto.
      + apply Theorem49; split; Ens.
        apply Theorem19; apply Theorem69; try tauto.
      + exists x1; split; try tauto; split; try tauto; split; auto.
        apply Property_Value; try tauto. }
  assert (Section (ran(En_f x y r s)) s y).
  { unfold Section; split.
    - unfold Subclass; intros; apply Axiom_Scheme in H2; destruct H2, H3.
      apply Axiom_SchemeP in H3; destruct H3, H4, H5, H5, H6, H7.
      unfold Order_PXY in H6; destruct H6 as [_ [_ [_ [_ H6]]]].
      unfold Section in H6; destruct H6 as [H6 _].
      apply Property_ran in H8; auto.
    - split; try tauto; intros; destruct H2, H3.
      apply Axiom_Scheme in H3; destruct H3, H5.
      apply Axiom_SchemeP in H5; destruct H5, H6, H7.
      apply Axiom_Scheme; split; Ens; exists (x1⁻¹[u]).
      apply Axiom_SchemeP; destruct H7 as [H7 [H8 [H9 H10]]]; double H8.
      unfold Order_PXY in H8; destruct H8 as [_ [_ [H12 [H13 H8]]]].
      generalize H11 as H20; intro.
      unfold Order_PXY in H11; destruct H11 as [H11 [_ H19]].
      unfold Section in H8; destruct H8 as [H8 [_ H15]].
      assert (u ∈ ran( x1)).
      { apply Property_ran in H10; apply H15 with v; tauto. }
      generalize H14 as H21; intro; apply Theorem96 in H12; destruct H12.
      unfold Function1_1 in H12; destruct H12; apply Lemma96'' in H14; auto.
      repeat split; auto.
      + apply Theorem49; split; Ens.
      + apply Property_Value in H14; auto. rewrite <- Lemma96''' in H14; auto.
        apply Property_dom in H14; destruct H19 as [_ [[H19 _] _]]; auto.
      + exists x1; split; try tauto; split; try tauto; split; auto.
        apply Property_Value in H14; auto; rewrite <- Lemma96''' in H14; auto. }
  assert (Order_PXY (En_f x y r s) x y r s).
  { unfold Order_PXY; split; try tauto; split; try tauto.
    split; [idtac | tauto]; unfold Order_Pr; split; auto.
    destruct H; split; try eapply Lemma99; eauto.
    split; intros; try eapply Lemma99; eauto.
    destruct H4, H5; double H4; double H5.
    apply Property_Value in H4; apply Property_Value in H5; auto.
    apply Axiom_SchemeP in H4; apply Axiom_SchemeP in H5.
    destruct H4 as [H4 [H9 [g1 [H10 [H11 [H12 H13]]]]]].
    destruct H5 as [H5 [H14 [g2 [H15 [H16 [H17 H18]]]]]].
    rewrite Theorem70 in H13; rewrite Theorem70 in H18; auto.
    apply Axiom_SchemeP in H13; destruct H13 as [_ H13].
    apply Axiom_SchemeP in H18; destruct H18 as [_ H18].
    rewrite H13, H18; clear H13 H18.
    unfold Order_PXY in H11; destruct H11 as [_ [_ [H11 [H13 H18]]]].
    unfold Order_PXY in H16; destruct H16 as [_ [_ [H16 [H19 H20]]]].
    generalize (Lemma_xy _ _ H11 H16); intro.
    apply (Theorem97 g1 g2 r s x y) in H21; auto.
    apply Property_Value in H12; apply Property_Value in H17; auto.
    destruct H21.
    - apply H21 in H12; double H12; rewrite Theorem70 in H12; auto.
      apply Axiom_SchemeP in H12; destruct H12 as [_ H12]; rewrite H12.
      apply Property_dom in H22; apply Property_dom in H17; apply H16; tauto.
    - apply H21 in H17; double H17; rewrite Theorem70 in H17; auto.
      apply Axiom_SchemeP in H17; destruct H17 as [_ H17]; rewrite H17.
      apply Property_dom in H12; apply Property_dom in H22; apply H11; tauto. }
  split; auto; apply NNPP; intro; apply not_or_and in H4; destruct H4.
  assert (exists u, FirstMember u r (x ~ dom( En_f x y r s))).
  { unfold Section in H1; destruct H1, H6.
    assert ((x ~ dom( En_f x y r s)) ⊂ x).
    { red; intros; apply Axiom_Scheme in H8; tauto. }
    assert ((x ~ dom( En_f x y r s)) <> Φ).
    { intro; apply Property_Φ in H1; apply H1 in H9; apply H4; auto. }
    generalize (Lemma97 _ _ _ H6 H8); intro.
    apply H10; repeat split; auto; red; auto. }
  assert (exists v, FirstMember v s (y ~ ran( En_f x y r s))).
  { unfold Section in H2; destruct H2, H7.
    assert ((y ~ ran( En_f x y r s)) ⊂ y).
    { red; intros; apply Axiom_Scheme in H9; tauto. }
    assert ((y ~ ran( En_f x y r s)) <> Φ).
    { intro; apply Property_Φ in H2; apply H2 in H10; apply H5; auto. }
    generalize (Lemma97 _ _ _ H7 H9); intro.
    apply H11; repeat split; auto; red; auto. }
  destruct H6 as [u H6]; destruct H7 as [v H7].
  unfold FirstMember in H6; unfold FirstMember in H7; destruct H6, H7.
  apply Axiom_Scheme in H6; destruct H6 as [_ [H6 H10]].
  apply Axiom_Scheme in H10; destruct H10 as [_ H10].
  apply H10; apply Axiom_Scheme; split; Ens.
  exists v; apply Axiom_SchemeP.
  split; try apply Theorem49; split; try Ens.
  exists ((En_f x y r s) ∪ [[u,v]]).
  assert (Function (En_f x y r s ∪ [[u, v]])).
  { assert ([u, v] ∈ μ) as H18.
    { apply Theorem19; apply Theorem49; split; try Ens. }
    unfold Function; split; intros.
    - unfold Relation; intros.
      apply Axiom_Scheme in H11; destruct H11 as [H11 [H12 | H12]].
      + PP H12 a b; eauto.
      + apply Axiom_Scheme in H12; exists u,v; apply H12; auto.
    - destruct H11; apply Axiom_Scheme in H11; apply Axiom_Scheme in H12.
      destruct H11 as [H11 [H13 | H13]], H12 as [H12 [H14 | H14]].
      + unfold Function in H0; eapply H0; eauto.
      + apply Property_dom in H13; apply Axiom_Scheme in H14; destruct H14.
        apply Theorem55 in H15; apply Theorem49 in H12; auto.
        destruct H15; rewrite H15 in H13; contradiction.
      + apply Property_dom in H14; apply Axiom_Scheme in H13; destruct H13.
        apply Theorem55 in H15; apply Theorem49 in H11; auto.
        destruct H15; rewrite H15 in H14; contradiction.
      + apply Axiom_Scheme in H13; destruct H13; apply Theorem55 in H15;
        apply Theorem49 in H13; auto.
        apply Axiom_Scheme in H14; destruct H14; apply Theorem55 in H16; 
        apply Theorem49 in H12; auto.
        destruct H15, H16; rewrite H17; auto. }
  split; auto.
  assert (Section (dom(En_f x y r s ∪ [[u, v]])) r x).
  { unfold Section; split.
    - unfold Subclass; intros; apply Axiom_Scheme in H12; destruct H12, H13.
      apply Axiom_Scheme in H13; destruct H13, H14.
      + apply Property_dom in H14; unfold Section in H1; apply H1; auto.
      + apply Axiom_Scheme in H14; destruct H14.
        assert ([u, v] ∈ μ).
        { apply Theorem19; apply Theorem49; split; try Ens. }
        apply H15 in H16; apply Theorem55 in H16; apply Theorem49 in H13; auto.
        destruct H16; rewrite H16; auto.
    - split; try tauto; intros; destruct H12, H13.
      apply Axiom_Scheme in H13; destruct H13, H15.
      apply Axiom_Scheme in H15; destruct H15, H16.
      + apply Axiom_Scheme; split; Ens.
        assert ([u0, (En_f x y r s) [u0]] ∈ (En_f x y r s)).
        { apply Property_dom in H16; apply Property_Value; auto.
          apply H1 with v0; repeat split; auto. }
        exists (En_f x y r s) [u0]; apply Axiom_Scheme; split; Ens.
      + apply Axiom_Scheme in H16; destruct H16.
        assert ([u,v] ∈ μ). { apply Theorem19; apply Theorem49; split; Ens. }
        apply H17 in H18; apply Theorem55 in H18;
        apply Theorem49 in H16; auto; destruct H18; subst v0.
        assert ([u0, (En_f x y r s) [u0]] ∈ (En_f x y r s)).
        { apply Property_Value; auto.
          generalize (classic (u0 ∈ dom( En_f x y r s))); intro.
          destruct H18; auto; absurd (Rrelation u0 r u); auto.
          apply H8; apply Axiom_Scheme; repeat split; Ens.
          apply Axiom_Scheme; split; Ens. }
        apply Axiom_Scheme; split; Ens.
        exists ((En_f x y r s)[u0]); apply Axiom_Scheme; split; Ens. }
  assert (Section (ran(En_f x y r s ∪ [[u, v]])) s y).
  { unfold Section; split.
    - unfold Subclass; intros; apply Axiom_Scheme in H13; destruct H13, H14.
      apply Axiom_Scheme in H7; destruct H7 as [_ [H7 _]] .
      apply Axiom_Scheme in H14; destruct H14, H15.
      + apply Property_ran in H15; unfold Section in H2; apply H2; auto.
      + apply Axiom_Scheme in H15; destruct H15.
        assert ([u, v] ∈ μ).
        { apply Theorem19; apply Theorem49; split; try Ens. }
        apply H16 in H17; apply Theorem55 in H17;
        apply Theorem49 in H14; auto; destruct H17; rewrite H18; auto.
    - split; try tauto; intros; destruct H13, H14.
      apply Axiom_Scheme in H14; destruct H14, H16.
      unfold Order_PXY in H3; destruct H3 as [_ [_ [H3 _]]].
      apply Theorem96 in H3; destruct H3 as [[_ H3] _].
      apply Axiom_Scheme in H16; destruct H16, H17.
      + apply Axiom_Scheme; split; Ens.
        assert ([((En_f x y r s) ⁻¹) [u0], u0] ∈ (En_f x y r s)).
        { assert (u0 ∈ ran( En_f x y r s)).
          { apply Property_ran in H17; apply H2 with v0; repeat split; auto. }
          pattern u0 at 2; rewrite Lemma96''' with (f:=(En_f x y r s)); auto.
          apply Property_Value'; auto; rewrite <- Lemma96'''; auto. }
        exists ((En_f x y r s) ⁻¹) [u0]; apply Axiom_Scheme; split; Ens.
      + apply Axiom_Scheme in H17; destruct H17.
        assert ([u,v] ∈ μ). { apply Theorem19; apply Theorem49; split; Ens. }
        apply H18 in H19; apply Theorem55 in H19;
        apply Theorem49 in H16; auto; destruct H19; subst v0.
        assert ([((En_f x y r s) ⁻¹) [u0], u0] ∈ (En_f x y r s)).
        { generalize (classic (u0 ∈ ran( En_f x y r s))); intro; destruct H20.
          - pattern u0 at 2; rewrite Lemma96''' with (f:=(En_f x y r s)); auto.
            apply Property_Value'; auto; rewrite <- Lemma96'''; auto.
          - absurd (Rrelation u0 s v); auto.
            apply H9; apply Axiom_Scheme; repeat split; Ens.
            apply Axiom_Scheme; split; Ens. }
        apply Axiom_Scheme; split; Ens.
        exists ((En_f x y r s) ⁻¹) [u0]; apply Axiom_Scheme; split; Ens. }
  split.
  - unfold Order_PXY; split; try tauto.
    split; try tauto; split; [idtac | tauto].
    unfold Order_Pr; intros; split; auto.
    split; try eapply Lemma99; eauto; try apply H.
    split; try eapply Lemma99; eauto; try apply H; intros.
    destruct H14, H15; apply Axiom_Scheme in H14; destruct H14, H17.
    apply Axiom_Scheme in H17; destruct H17 as [_ H17].
    apply Axiom_Scheme in H15; destruct H15, H18.
    apply Axiom_Scheme in H18; destruct H18 as [_ H18].
    assert ([u,v] ∈ μ) as H20.
    { apply Theorem19; apply Theorem49; split; Ens. }
    destruct H17, H18.
    + apply Property_dom in H17; apply Property_dom in H18;
      repeat rewrite Lemma99'; auto; Ens.
      unfold Order_PXY in H3; destruct H3 as [_ [_ [H3 _]]].
      unfold Order_Pr in H3; eapply H3; eauto.
    + apply Property_dom in H17; rewrite Lemma99'; auto; Ens.
      apply Axiom_Scheme in H18; destruct H18.
      apply H19 in H20;  apply Theorem55 in H20; destruct H20;
      apply Theorem49 in H18; auto; rewrite Lemma99''; auto; Ens.
      apply Lemma99''' with (y:=(ran( En_f x y r s))) (x:=y); auto.
      * apply Property_Value in H17; auto.
        double H17; apply Property_ran in H17.
        apply Axiom_Scheme; split; Ens; exists u0; apply Axiom_Scheme; split; Ens.
      * apply Axiom_Scheme in H7; destruct H7, H22; apply Axiom_Scheme in H23; tauto.
      * apply Axiom_Scheme in H7; tauto.
    + apply Property_dom in H18.
      pattern ((En_f x y r s ∪ [[u, v]]) [v0]); rewrite Lemma99'; Ens.
      assert (u0 ∈ dom( En_f x y r s)).
      { unfold Section in H1; apply H1 with v0; split; auto.
        apply Axiom_Scheme in H17; destruct H17; apply H19 in H20.
        apply Theorem55 in H20; apply Theorem49 in H17; auto.
        destruct H20; rewrite H20; auto. }
      rewrite Lemma99'; Ens; unfold Order_PXY in H3.
      destruct H3 as [_ [_ [H3 _]]]; unfold Order_Pr in H3; eapply H3; eauto.
    + double H20; apply Axiom_Scheme in H17; destruct H17; apply H21 in H19.
      apply Axiom_Scheme in H18; destruct H18; apply H22 in H20.
      apply Theorem55 in H20; destruct H20; apply Theorem49 in H18; auto.
      apply Theorem55 in H19; destruct H19; apply Theorem49 in H17; auto.
      subst u0 v0; destruct H as [H _]; apply Theorem88 in H.
      destruct H as [_ H]; apply Property_Asy with (u:=u) in H; auto.
      contradiction.
  - assert (Ensemble ([u,v])). { apply Theorem49; split; Ens. } split.
    + apply Axiom_Scheme; split; Ens; exists v; apply Axiom_Scheme; split; Ens.
      right; apply Axiom_Scheme; split; auto.
    + apply Axiom_Scheme; split; Ens; right; apply Axiom_Scheme; split; auto.
Qed.

Hint Resolve Theorem99 : set.


(* 100 Theorem  If r well-orders x, s well-orders y, x is a set, and y is not
   a set, then there is a unique r-s order-preserving function in x and y whose
   domain is x. *)

Theorem Theorem100 : forall r s x y,
  WellOrdered r x /\ WellOrdered s y -> Ensemble x -> ~ Ensemble y ->
  exists f, Function f /\ Order_PXY f x y r s /\ dom( f) = x.
Proof.
  intros; destruct H.
  generalize (Lemma_xy _ _ H H2); intro.
  apply Theorem99 in H3; destruct H3, H3, H4.
  exists x0; split; auto; split; auto; destruct H5; auto.
  unfold Order_PXY in H4; destruct H4 as [_ [_ [_ [H4 _]]]].
  unfold Section in H4; destruct H4; apply Theorem33 in H4; auto.
  apply Axiom_Substitution in H4; auto; rewrite H5 in H4; contradiction.
Qed.

Theorem Theorem100' : forall r s x y,
  WellOrdered r x /\ WellOrdered s y -> Ensemble x -> ~ Ensemble y ->
  forall f, Function f /\ Order_PXY f x y r s /\ dom(f) = x ->
  forall g, Function g /\ Order_PXY g x y r s /\ dom(g) = x -> f = g.
Proof.
  intros; destruct H, H2, H5, H3, H7; unfold Order_PXY in H5, H7.
  destruct H5 as [_ [_ H5]], H5, H9, H7 as [_ [_ H7]], H7, H11.
  generalize (Lemma_xy _ _ H5 H7); intro.
  apply (Theorem97 f g r s x y) in H13; auto; destruct H13.
  - apply Theorem27; split; auto; unfold Subclass; intros.
    rewrite Theorem70; rewrite Theorem70 in H14; auto.
    PP H14 a b; double H15; rewrite <- Theorem70 in H15; auto.
    apply Axiom_SchemeP in H16; destruct H16.
    apply Axiom_SchemeP; split; auto; rewrite H17 in *.
    assert ([a,f[a]] ∈ f).
    { apply Property_Value; auto; subst x.
      apply Property_dom in H15; rewrite <- H8; auto. }
    apply H13 in H18; eapply H3; eauto.
  - apply Theorem27; split; auto; unfold Subclass; intros.
    rewrite Theorem70; rewrite Theorem70 in H14; auto.
    PP H14 a b; double H15; rewrite <- Theorem70 in H15; auto.
    apply Axiom_SchemeP in H16; destruct H16.
    apply Axiom_SchemeP; split; auto; rewrite H17 in *.
    assert ([a,g[a]] ∈ g).
    { apply Property_Value; auto; subst x.
      apply Property_dom in H15; rewrite H8; auto. }
    apply H13 in H18; eapply H2; eauto.
Qed.

Hint Resolve Theorem100 Theorem100' : set.


(* ORDINALS *)

(* VII Axiom of regularity : If x ≠ Φ there is a member y of x such x∩y = Φ. *)

Axiom Axiom_Regularity : forall x, x ≠ Φ -> exists y, y ∈ x /\ x ∩ y = Φ.

Hint Resolve Axiom_Regularity : set.


(* 101 Theorem101  x ∉ x. *)

Theorem Theorem101 : forall x, x ∉ x.
Proof.
  intros; intro.
  assert ([x] ≠ Φ).
  { apply Lemma35; exists x; apply Axiom_Scheme; split; Ens. }
  apply Axiom_Regularity in H0; destruct H0, H0.
  assert (x0 = x).
  { apply Axiom_Scheme in H0; destruct H0; apply H2; apply Theorem19; Ens. }
  subst x0; assert (x ∈ ([x] ∩ x)). { apply Axiom_Scheme; repeat split; Ens. }
  rewrite H1 in H2; generalize (Theorem16 x); intro; contradiction.
Qed.

Hint Resolve Theorem101 : set.


(* 102 Theorem  It is false that x∈y and y∈x. *)

Theorem Theorem102 : forall x y, ~ (x ∈ y /\ y ∈ x).
Proof.
  intros; intro; destruct H.
  assert (\{ λ z, z = x \/ z =y \} ≠ Φ).
  { apply Lemma35; exists x; apply Axiom_Scheme; split; Ens. }
  apply Axiom_Regularity in H1; destruct H1, H1; apply Axiom_Scheme in H1.
  destruct H1, H3; subst x0.
  + assert (y ∈ (\{ λ z, z = x \/ z = y \} ∩ x)).
    { apply Axiom_Scheme; repeat split; Ens; apply Axiom_Scheme; split; Ens. }
    rewrite H2 in H3; generalize (Theorem16 y); intro; contradiction.
  + assert (x ∈ (\{ λ z, z = x \/ z = y \} ∩ y)).
    { apply Axiom_Scheme; repeat split; Ens; apply Axiom_Scheme; split; Ens. }
    rewrite H2 in H3; generalize (Theorem16 x); intro; contradiction.
Qed.

Hint Resolve Theorem102 : set.


(* 103 Definition  E = { [x,y] : x∈y}. *)

Definition E : Class := \{\ λ x y, x ∈ y \}\.

Hint Unfold E : set.


(* 104 Theorem  E is not a set. *)

Lemma Lemma104 : forall a b c, a ∈ b -> b ∈ c -> c ∈ a -> False.
Proof.
  intros.
  assert (\{ λ x, x = a \/ x =b \/ x = c \} ≠ Φ).
  { apply Lemma35; exists a; apply Axiom_Scheme; split; Ens. }
  apply Axiom_Regularity in H2; destruct H2, H2; apply Axiom_Scheme in H2; destruct H2.
  destruct H4 as [H4 | [H4 | H4]]; subst x.
  + assert (c ∈ (\{ λ x, x = a \/ x =b \/ x = c \} ∩ a)).
    { apply Axiom_Scheme; repeat split; Ens; apply Axiom_Scheme; split; Ens. }
    rewrite H3 in H4; generalize (Theorem16 c); intro; contradiction.
  + assert (a ∈ (\{ λ x, x = a \/ x =b \/ x = c \} ∩ b)).
    { apply Axiom_Scheme; repeat split; Ens; apply Axiom_Scheme; split; Ens. }
    rewrite H3 in H4; generalize (Theorem16 a); intro; contradiction.
  + assert (b ∈ (\{ λ x, x = a \/ x =b \/ x = c \} ∩ c)).
    { apply Axiom_Scheme; repeat split; Ens; apply Axiom_Scheme; split; Ens. }
    rewrite H3 in H4; generalize (Theorem16 b); intro; contradiction.
Qed.

Theorem Theorem104 : ~ Ensemble E.
Proof.
  intro; generalize (Theorem42 _ H); intro.
  assert (E ∈ [E]). { apply Axiom_Scheme; split; auto. }
  assert ([E, [E]] ∈ E).
  { apply Axiom_SchemeP; split; auto; apply Theorem49; tauto. }
  assert ([E] ∈ [E, [E]]).
  { apply Axiom_Scheme; split; Ens; left; apply Axiom_Scheme; split; auto. }
  eapply Lemma104; eauto.
Qed.

Hint Resolve Theorem104 : set.


(* 105 Definition  x is full iff each member of x is a subset of x. *)

Definition full x : Prop := forall m, m∈x -> m⊂x.

Corollary Property_Full : forall x, 
  full x <-> (forall u v : Class, v ∈ x /\ u ∈ v -> u ∈ x).
Proof.
  intros; split; intros.
  - unfold full in H; destruct H0; apply H in H0; auto.
  - unfold full; intros; unfold Subclass; intros; apply H with m; tauto.
Qed.

Hint Unfold full : set.
Hint Resolve Property_Full : set.


(* 106 Definition  x is an ordinal iff E connects x and x is full. *)

Definition Ordinal x : Prop := Connect E x /\ full x.

Hint Unfold Ordinal : set.


(* 107 Theorem  If x is an ordinal E well-orders x. *)

Theorem Theorem107 : forall x, 
  Ordinal x -> WellOrdered E x.
Proof.
  intros.
  unfold Ordinal in H; destruct H; unfold WellOrdered.
  intros; split; auto; intros; destruct H1.
  apply Axiom_Regularity in H2; destruct H2, H2.
  exists x0; unfold FirstMember; intros.
  split; auto; intros; intro.
  unfold Rrelation in H5; apply Axiom_SchemeP in H5; destruct H5.
  assert (y0 ∈ (y ∩ x0)). { apply Axiom_Scheme; split; Ens. }
  rewrite H3 in H7; generalize (Theorem16 y0); intro; contradiction.
Qed.

Hint Resolve Theorem107 : set.


(* 108 Theorem  If x is an ordinal, y⊂x, y≠x, and y is full, then y∈x. *)

Theorem Theorem108 : forall x y, 
  Ordinal x -> y ⊂ x -> y≠x -> full y -> y ∈ x.
Proof.
  intros.
  assert (Section y E x).
  { apply Theorem107 in H; unfold Section; intros.
    split; auto; split; auto; intros; destruct H3, H4.
    unfold Rrelation in H5; apply Axiom_SchemeP in H5; destruct H5.
    unfold full in H2; apply H2 in H4; auto. }
  generalize (Lemma_xy _ _ H3 H1); intro.
  apply Theorem91 in H4; destruct H4, H4.
  assert (x0 = \{ λ u : Class,u ∈ x /\ Rrelation u E x0 \}).
  { apply Axiom_Extent; split; intros; AssE z.
    - apply Axiom_Scheme; split; auto.
      unfold Ordinal in H; destruct H.
      double H4; unfold full in H8; apply H8 in H4.
      split; auto; apply Axiom_SchemeP; split; auto.
      apply Theorem49; split; Ens.
    - apply Axiom_Scheme in H6; destruct H6, H8.
      unfold Rrelation in H9; apply Axiom_SchemeP in H9; tauto. }
  rewrite <- H6 in H5; subst x0; auto.
Qed.

Hint Resolve Theorem108 : set.


(* 109 Theorem  If x is an ordinal an y is an ordinal, then x⊂y or y⊂x. *)

Lemma Lemma109 : forall x y,
  Ordinal x /\ Ordinal y -> full (x ∩ y).
Proof.
  intros; destruct H; unfold Ordinal in H, H0; destruct H, H0.
  unfold full in *; intros; apply Axiom_Scheme in H3; destruct H3, H4.
  apply H1 in H4; apply H2 in H5.
  unfold Subclass; intros; apply Axiom_Scheme; repeat split; Ens.
Qed.

Lemma Lemma109' : forall x y,
  Ordinal x /\ Ordinal y -> ((x ∩ y) = x) \/ ((x ∩ y) ∈ x).
Proof.
  intros.
  generalize (classic ((x ∩ y) = x)); intro; destruct H0; try tauto.
  assert ((x ∩ y) ⊂ x).
  { unfold Subclass; intros; apply Theorem4' in H1; tauto. }
  elim H; intros; apply Lemma109 in H.
  eapply Theorem108 in H2; eauto.
Qed.

Theorem Theorem109 : forall x y,
  Ordinal x /\ Ordinal y -> x ⊂ y \/ y ⊂ x.
Proof.
  intros; elim H; intros; generalize (Lemma_xy _ _ H1 H0); intro.
  apply Lemma109' in H; apply Lemma109' in H2; destruct H.
  - apply Theorem30 in H; tauto.
  - destruct H2.
    + apply Theorem30 in H2; tauto.
    + assert ((x ∩ y) ∈ (x ∩ y)).
      { rewrite Theorem6' in H2; apply Axiom_Scheme; repeat split; Ens. }
      apply Theorem101 in H3; elim H3.
Qed.

Hint Resolve Theorem109 : set.


(* 110 Theorem  If x is an ordinal an y is an ordinal, then x∈y or y∈x or
   x = y. *)

Theorem Theorem110 : forall x y,
  Ordinal x /\ Ordinal y -> x ∈ y \/ y ∈ x \/ x = y.
Proof.
  intros; generalize (classic (x = y)); intro; destruct H0; try tauto.
  elim H; intros; apply Theorem109 in H; destruct H.
  - left; unfold Ordinal in H1; destruct H1; eapply Theorem108; eauto.
  - right; left; unfold Ordinal in H2; destruct H2.
    eapply Theorem108; eauto; intro; auto.
Qed.

Hint Resolve Theorem110 : set.


(* 111 Theorem  If x is an ordinal and y∈x, then y is an ordinal. *)

Theorem Theorem111 : forall x y, Ordinal x /\ y ∈ x -> Ordinal y.
Proof.
  intros; destruct H; double H; unfold Ordinal in H; destruct H.
  assert (Connect E y).
  { unfold Connect; intros; unfold Ordinal in H1; apply H1 in H0.
    unfold Connect in H; destruct H3; apply H; auto. }
  unfold Ordinal; split; auto.
  unfold full; intros; unfold Subclass; intros.
  apply Theorem107 in H1; unfold Ordinal in H1.
  assert (y ⊂ x); auto; assert (m ∈ x); auto.
  assert (m ⊂ x); auto; assert (z ∈ x); auto.
  apply Theorem88 in H1; destruct H1.
  unfold Transitive in H1; specialize H1 with z m y.
  assert (Rrelation z E y).
  { apply H1; repeat split; Ens.
    - unfold Rrelation; apply Axiom_SchemeP; split; auto.
      apply Theorem49; split; Ens.
    - unfold Rrelation; apply Axiom_SchemeP; split; auto.
      apply Theorem49; split; Ens. }
  unfold Rrelation in H11; apply Axiom_SchemeP in H11; tauto.
Qed.

Hint Resolve Theorem111 : set.


(* 112 Definition  R = { x : x is an ordinal }. *)

Definition R : Class := \{ λ x, Ordinal x \}.

Hint Unfold R : set.


(* 113 Theorem  R is an ordinal and R is not a set. *)

Lemma Lemma113 :forall u v,
  Ensemble u -> Ensemble v -> Ordinal u /\ Ordinal v ->
  (Rrelation u E v \/ Rrelation v E u \/ u = v) .
Proof.
  intros; apply Theorem110 in H1; repeat split.
  destruct H1 as [H1 | [H1 | H1]].
  - left; unfold Rrelation; apply Axiom_SchemeP; split; Ens.
    apply Theorem49; auto.
  - right; left; apply Axiom_SchemeP; split; Ens.
    apply Theorem49; auto.
  - right; right; auto.
Qed.

Theorem Theorem113 : Ordinal R /\ ~ Ensemble R.
Proof.
  intros.
  assert (Ordinal R).
  { unfold Ordinal; intros; split.
    - unfold Connect; intros; destruct H.
      apply Axiom_Scheme in H; destruct H; apply Axiom_Scheme in H0; destruct H0.
      generalize (Lemma_xy _ _ H1 H2); intro; apply Lemma113; auto.
    - unfold full; intros; apply Axiom_Scheme in H; destruct H.
      unfold Subclass; intros; apply Axiom_Scheme; split; Ens.
      eapply Theorem111; eauto. }
  split; auto; intro.
  assert (R ∈ R). { apply Axiom_Scheme; split; auto. }
  apply Theorem101 in H1; auto.
Qed.

Hint Resolve Theorem113 : set.


(* 114 Theorem  Each E-section of R is an ordinal. *)

Theorem Theorem114 : forall x, Section x E R -> Ordinal x.
Proof.
  intros.
  generalize (classic (x = R)); intro; destruct H0.
  - rewrite H0; apply Theorem113.
  - generalize (Lemma_xy _ _ H H0); intro.
    apply Theorem91 in H1; destruct H1, H1.
    assert (x0 = \{ λ u, u ∈ R /\ Rrelation u E x0 \}).
    { apply Axiom_Extent; split; intros.
      - apply Axiom_Scheme; repeat split; Ens.
        + apply Axiom_Scheme in H1; destruct H1.
          apply Axiom_Scheme; split; Ens; eapply Theorem111; eauto.
        + unfold Rrelation; apply Axiom_SchemeP; split; auto.
          apply Theorem49; Ens.
      - apply Axiom_Scheme in H3; destruct H3, H4.
        unfold Rrelation in H5; apply Axiom_SchemeP in H5; tauto. }
    subst x; rewrite H3 in H1; apply Axiom_Scheme in H1; tauto.
Qed.

Corollary Property114 : forall x, Ordinal x -> Section x E R.
Proof.
  intros; unfold Section; split.
  - unfold Subclass; intros; apply Axiom_Scheme; split; try Ens.
    eapply Theorem111; eauto.
  - split; intros; try apply Theorem107; try apply Theorem113.
    destruct H0, H1; unfold Ordinal in H2; apply Axiom_SchemeP in H2.
    destruct H2; unfold Ordinal in H; destruct H; apply H4 in H1; auto.
Qed.


Hint Resolve Theorem114 : set.


(* 115 Definition  x is an ordinal number iff x ∈ R. *)

Definition Ordinal_Number x : Prop := x ∈ R.

Hint Unfold Ordinal_Number : set.


(* 116 Definition  x ≺ y if and only if x ∈ y. *)

Definition Less x y : Prop := x ∈ y.

Notation "x ≺ y" := (Less x y)(at level 67, left associativity).

Hint Unfold Less : set.


(* 117 Definition  x ≼ y if and only if x ∈ y or x = y. *)

Definition LessEqual x y := x ∈ y \/ x=y.

Notation "x ≼ y" := (LessEqual x y)(at level 67, left associativity).


(* 118 Theorem  If x and y are ordinals, then x ≼ y if and only if x ⊂ y. *)

Theorem Theorem118 : forall x y,
  Ordinal x /\ Ordinal y -> (x ⊂ y <-> x ≼ y).
Proof.
  intros; destruct H; split; intros.
  - unfold LessEqual.
    generalize (classic (x = y)); intro; destruct H2; try tauto.
    unfold Ordinal in H; destruct H.
    left; apply Theorem108; auto.
  - unfold LessEqual in H1; destruct H1.
    + unfold Ordinal in H0; destruct H0; auto.
    + rewrite H1; auto; unfold Subclass; intros; auto.
Qed.

Hint Resolve Theorem118 : set.


(* 119 Theorem  If x is an ordinal, then x = { y : y ∈ R /\ y ≺ x }. *)

Theorem Theorem119 : forall x,
  Ordinal x -> x = \{ λ y, y ∈ R /\ y ≺ x \}.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme; repeat split; Ens.
    apply Axiom_Scheme; split; Ens; eapply Theorem111; eauto.
  - apply Axiom_Scheme in H0; destruct H0, H1; auto.
Qed.

Hint Resolve Theorem119 : set.


(* 120 Theorem  If x ⊂ R, then ∪x is an ordinal. *)

Theorem Theorem120 : forall x, x ⊂ R -> Ordinal (∪ x).
Proof.
  intros; red; split.
  - unfold Connect; intros; destruct H0; apply Axiom_Scheme in H0.
    apply Axiom_Scheme in H1; destruct H0, H2, H2, H1, H4, H4.
    apply H in H3; apply H in H5; apply Axiom_Scheme in H3.
    destruct H3; apply Axiom_Scheme in H5; destruct H5.
    assert (Ordinal u). { eapply Theorem111; eauto. }
    assert (Ordinal v). { eapply Theorem111; eauto. }
    generalize (Lemma_xy _ _ H8 H9); intro; apply Lemma113; auto.
  - apply Property_Full; intros; destruct H0.
    apply Axiom_Scheme in H0; destruct H0, H2, H2.
    apply Axiom_Scheme; split; Ens; exists x0; split; auto.
    apply H in H3; apply Axiom_Scheme in H3; destruct H3 as [_ H3].
    unfold Ordinal in H3; destruct H3; apply H4 in H2; auto.
Qed.

Hint Resolve Theorem120 : set.


(* 121 Theorem  If x ⊂ R and x ≠ Φ, then ∩x ∈ x. *)

Lemma Lemma121 : forall x, x ⊂ R /\ x ≠ Φ -> FirstMember (∩ x) E x.
Proof.
  intros; destruct H.
  generalize (Theorem113); intro; destruct H1.
  apply Theorem107 in H1; unfold WellOrdered in H1; destruct H1.
  generalize (Lemma_xy _ _ H H0); intro; apply H3 in H4; destruct H4.
  double H4; unfold FirstMember in H4; destruct H4.
  assert ((∩ x) = x0).
  { apply Axiom_Extent; split; intros.
    - apply Axiom_Scheme in H7; destruct H7; apply H8; auto.
    - apply Axiom_Scheme; split; Ens; intros.
      assert (~ Rrelation y E x0); auto.
      assert (Ordinal x0). { apply H in H4; apply Axiom_Scheme in H4; tauto. }
      assert (Ordinal y). { apply H in H8; apply Axiom_Scheme in H8; tauto. }
      generalize (Lemma_xy _ _ H10 H11); intro; apply Theorem110 in H12.
      destruct H12 as [H12 | [H12 | H12]].
      + apply H in H8; apply Axiom_Scheme in H8; destruct H8 as [_ H8].
        unfold Ordinal in H8; destruct H8; generalize (Property_Full y); intro.
        destruct H14; eapply H14; eauto.
      + elim H9; unfold Rrelation; apply Axiom_SchemeP; split; auto.
        apply Theorem49; Ens.
      + subst x0; auto. }
  rewrite H7 ; auto.
Qed.

Theorem Theorem121 : forall x, x ⊂ R /\ x ≠ Φ -> (∩ x) ∈ x.
Proof.
  intros; apply Lemma121 in H.
  unfold FirstMember in H; tauto.
Qed.

Hint Resolve Theorem121 : set.


(* 122 Definition  x + 1 = x ∪ {x}. *)

Definition PlusOne x := x ∪ [x].

Hint Unfold PlusOne: set.


(* 123 Theorem  If x∈R, then x+1 is the E-first member of {y : y∈R and x≺y}. *)

Lemma Lemma123 : forall x, x ∈ R -> (PlusOne x) ∈ R.
Proof.
  intros; apply Axiom_Scheme; split.
  - apply Axiom_Union; split; Ens; apply Theorem42; Ens.
  - unfold Connect; split.
    + unfold Connect; intros; destruct H0.
      apply Axiom_Scheme in H0; apply Axiom_Scheme in H1; destruct H0, H1, H2, H3.
      * apply Axiom_Scheme in H; destruct H as [_ H].
        assert (Ordinal u). { eapply Theorem111; eauto. }
        assert (Ordinal v). { eapply Theorem111; eauto. }
        generalize (Lemma_xy _ _ H4 H5); intro; apply Lemma113; auto.
      * apply Axiom_Scheme in H3; destruct H3.
        AssE x; apply Theorem19 in H5; apply H4 in H5; subst v.
        left; unfold Rrelation; apply Axiom_SchemeP; split; auto.
        apply Theorem49; tauto.
      * apply Axiom_Scheme in H2; destruct H2.
        AssE x; apply Theorem19 in H5; apply H4 in H5; subst u.
        right; left; unfold Subclass; apply Axiom_SchemeP; split; auto.
        apply Theorem49; tauto.
      * AssE x; apply Theorem19 in H4; double H4.
        apply Axiom_Scheme in H2; destruct H2; apply H6 in H4.
        apply Axiom_Scheme in H3; destruct H3; apply H7 in H5.
        subst u; subst v; tauto.
    + unfold full; intros; unfold Subclass; intros.
      apply Axiom_Scheme in H; apply Axiom_Scheme in H0; destruct H, H0.
      apply Axiom_Scheme; split; Ens; destruct H3.
      * unfold Ordinal in H2; destruct H2.
        unfold full in H4; left; eapply H4; eauto.
      * apply Axiom_Scheme in H3; destruct H3.
        apply Theorem19 in H; apply H4 in H; subst m; tauto.
Qed.

Theorem Theorem123 : forall x,
  x ∈ R -> FirstMember (PlusOne x) E (\{ λ y, (y ∈ R /\ Less x y) \}).
Proof.
  intros; unfold FirstMember; split; intros.
  - apply Axiom_Scheme; repeat split.
    + unfold Ensemble; exists R; apply Lemma123; auto.
    + apply Lemma123; auto.
    + unfold Less; intros; apply Axiom_Scheme; split; Ens.
      right; apply Axiom_Scheme; split; Ens.
  - intro; apply Axiom_Scheme in H0; destruct H0, H2.
    unfold Rrelation in H1; apply Axiom_SchemeP in H1; destruct H1.
    apply Axiom_Scheme in H4; destruct H4; unfold Less in H3; destruct H5.
    + eapply Theorem102; eauto.
    + AssE x; apply Theorem19 in H6; apply Axiom_Scheme in H5; destruct H5.
      apply H7 in H6; subst y; eapply Theorem101; eauto.
Qed.

Hint Resolve Theorem123 : set.


(* 124 Theorem  If x ∈ R, then ∪(x+1) = x. *)

Theorem Theorem124 : forall x, 
  x ∈ R -> ∪ PlusOne x = x.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme in H0; destruct H0, H1, H1.
    apply Axiom_Scheme in H2; destruct H2, H3.
    + apply Axiom_Scheme in H; destruct H, H4.
      generalize (Property_Full x); intro; destruct H6.
      apply H6 with (u:=z) (v:=x0) in H5; tauto.
    + apply Axiom_Scheme in H3; destruct H3.
      rewrite <- H4; auto; try (apply Theorem19; Ens).
  - apply Axiom_Scheme; split; Ens; exists x; split; auto.
    apply Axiom_Scheme; split; Ens; right; apply Axiom_Scheme; Ens.
Qed.

Hint Resolve Theorem124 : set.


(* 125 Definition  f|x = f ∩ (x × μ). *)

Definition Restriction f x : Class := f ∩ (x × μ).

Notation "f | ( x )" := (Restriction f x)(at level 30).

Hint Unfold Restriction: set.


(* 126 Theorem  If f is a function, f|x is a function whose domain is
   x ∩ (domain f) and (f|x)[y] = f[y] for each y in domain f|x. *)

Theorem Theorem126 : forall f x,
  Function f -> Function (f|(x)) /\ dom(f|(x)) = x ∩ dom( f) /\
  (forall y, y ∈ dom(f|(x)) -> (f|(x)) [y] = f [y]).
Proof.
  intros; repeat split; intros.
  - unfold Relation; intros; apply Axiom_Scheme in H0; destruct H0, H1.
    PP H2 a b; eauto.
  - destruct H0; apply Axiom_Scheme in H0; destruct H0 as [_ [H0 _]].
    apply Axiom_Scheme in H1; destruct H1 as [_ [H1 _]].
    unfold Function in H; eapply H; eauto.
  - apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H0; destruct H0, H1.
      apply Axiom_Scheme in H1; destruct H1, H2.
      apply Property_dom in H2; apply Axiom_SchemeP in H3.
      apply Axiom_Scheme; split; tauto.
    + apply Axiom_Scheme in H0; destruct H0, H1.
      apply Axiom_Scheme; split; auto.
      apply Property_Value in H2; auto.
      exists f[z]; apply Axiom_Scheme; repeat split; Ens.
      apply Axiom_SchemeP; repeat split; Ens; apply Theorem19.
      apply Property_ran in H2; Ens.
  - apply Axiom_Extent; split; intros.
    + apply Axiom_Scheme in H1; destruct H1.
      apply Axiom_Scheme in H0; destruct H0, H3.
      apply Axiom_Scheme in H3; destruct H3, H4.
      apply Property_dom in H4; apply H2.
      assert (Ensemble f[y]). { apply Theorem19; apply Theorem69; auto. }
      apply Axiom_Scheme; split; Ens; apply Axiom_Scheme; repeat split.
      * apply Theorem49; auto.
      * apply Property_Value in H4; auto.
      * apply Axiom_SchemeP in H5; apply Theorem19 in H6.
        apply Axiom_SchemeP; repeat split; try tauto; try apply Theorem49; Ens.
    + apply Axiom_Scheme in H1; destruct H1.
      apply Axiom_Scheme; split; auto; intros.
      apply Axiom_Scheme in H3; destruct H3; apply Axiom_Scheme in H4.
      apply H2; apply Axiom_Scheme; split; tauto.
Qed.

Hint Resolve Theorem126 : set.


(* 127 Theorem  Let f be a function such that domain f is an ordinal and
   f[u] = g[f|u] for u in domain f. If h is also a function such that domain h
   is an ordinal and h[u] = g[h|u] for u in domain h, then h ⊂ f or f ⊂ h. *)

Theorem Lemma127 : forall f h,
  dom( f) ⊂ dom( h) -> Function f -> Function h ->
  \{ λ a,a ∈ (dom( f) ∩ dom( h)) /\ f [a] ≠ h [a] \} = Φ -> f ⊂ h.
Proof.
  intros.
  unfold Subclass; intros; rewrite Theorem70 in H3; auto; PP H3 a b.
  double H4; rewrite <- Theorem70 in H4; auto; apply Property_dom in H4.
  apply Axiom_SchemeP in H5; destruct H5.
  rewrite Theorem70; auto; apply Axiom_SchemeP; split; auto; rewrite H6.
  generalize (classic (f[a] = h[a])); intro; destruct H7; auto.
  assert (a ∈ \{ λ a, a ∈ (dom(f) ∩ dom(h)) /\ f[a] ≠ h[a] \}).
  { apply Theorem30 in H; rewrite H; apply Axiom_Scheme; split; Ens. }
  rewrite H2 in H8; generalize (Theorem16 a); contradiction.
Qed.

Theorem Theorem127 : forall f h g,
  Function f -> Ordinal dom(f) ->
  (forall u0, u0 ∈ dom(f) -> f[u0] = g[f|(u0)]) ->
  Function h -> Ordinal dom(h) ->
  (forall u1, u1 ∈ dom(h) -> h[u1] = g [h|(u1)]) -> h ⊂ f \/ f ⊂ h.
Proof.
  intros.
  generalize (Lemma_xy _ _ H0 H3); intro; apply Theorem109 in H5.
  generalize (classic (\{ λ a, a ∈ (dom(f) ∩ dom(h)) /\ f[a] ≠ h[a] \} = Φ));
  intro; destruct H6.
  - destruct H5.
    + right; apply Lemma127; auto.
    + left; rewrite Lemma97'' in H6; apply Lemma127; auto.
  - assert (exists u, FirstMember u E \{λ a, a∈(dom(f)∩dom(h))/\f[a]≠h[a]\}).
    { apply Theorem107 in H0; unfold WellOrdered in H0; apply H0; split; auto.
      unfold Subclass; intros; apply Axiom_Scheme in H7; destruct H7, H8.
      apply Axiom_Scheme in H8; tauto. }
    destruct H7 as [u H7]; unfold FirstMember in H7; destruct H7.
    apply Axiom_Scheme in H7; destruct H7, H9.
    apply Axiom_Scheme in H9; destruct H9 as [_[H9 H11]].
    generalize (H1 _ H9); generalize (H4 _ H11); intros.
    assert ((h | (u)) = (f | (u))).
    { apply Axiom_Extent; intros; split; intros.
      - apply Axiom_Scheme in H14; destruct H14, H15.
        apply Axiom_Scheme; repeat split; auto; PP H16 a b.
        apply Axiom_SchemeP in H17; destruct H17 ,H18.
        generalize H15 as H22; intro; apply Property_dom in H22.
        rewrite Theorem70 in H15; auto; rewrite Theorem70; auto.
        apply Axiom_SchemeP in H15; destruct H15.
        apply Axiom_SchemeP; split; auto.
        rewrite H20; symmetry.
        generalize (classic (f [a] = h [a])); intro; destruct H21; auto.
        assert (a ∈ \{ λ a, a ∈ (dom(f) ∩ dom(h)) /\ f[a] ≠ h[a] \}).
        { apply Axiom_Scheme.
          repeat split; Ens; apply Axiom_Scheme; repeat split; Ens.
          unfold Ordinal in H0; destruct H0; apply H23 in H9; auto. }
        apply H8 in H23; elim H23; unfold Rrelation, E.
        apply Axiom_SchemeP; split; auto; apply Theorem49; split; Ens.
      - apply Axiom_Scheme in H14; destruct H14, H15.
        apply Axiom_Scheme; repeat split; auto; PP H16 a b.
        apply Axiom_SchemeP in H17; destruct H17 ,H18.
        generalize H15 as H22; intro; apply Property_dom in H22.
        rewrite Theorem70 in H15; auto; rewrite Theorem70; auto.
        apply Axiom_SchemeP in H15; destruct H15.
        apply Axiom_SchemeP; split; auto.
        rewrite H20; symmetry.
        generalize (classic (f[a] = h[a])); intro; destruct H21; auto.
        assert (a ∈ \{ λ a, a ∈ (dom(f) ∩ dom(h)) /\ f[a] ≠ h[a] \}).
        { apply Axiom_Scheme.
          repeat split; Ens; apply Axiom_Scheme; repeat split; Ens.
          unfold Ordinal in H3; destruct H3; apply H23 in H11; auto. }
        apply H8 in H23; elim H23; unfold Rrelation, E.
        apply Axiom_SchemeP; split; auto; apply Theorem49; split; Ens. }
  rewrite <- H14 in H13; rewrite <- H12 in H13; contradiction.
Qed.

Hint Resolve Theorem127 : set.


(* 128 Theorem  For each g there is a unique function f such that domain f is
   an ordinal and f[x] = g[f|x] for each ordinal number x. *)

Definition En_f' g := \{\ λ u v, u ∈ R /\ (exists h, Function h /\
  Ordinal dom(h) /\ (forall z, z ∈ dom(h) -> h[z] = g [h | (z)] ) /\
  [u,v] ∈ h ) \}\.

Lemma Lemma128 : forall u v w,
  Ordinal u -> v ∈ u -> w ∈ v -> w ∈ u.
Proof.
  intros; unfold Ordinal in H; destruct H.
  unfold full in H2; eapply H2; eauto.
Qed.

Lemma Lemma128' : forall f x,
  Function f -> Ordinal dom(f) -> Ordinal_Number x ->
  ~ x ∈ dom(f) -> f | (x) = f .
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme in H3; tauto.
  - apply Axiom_Scheme; split; Ens; split; auto.
    unfold Function, Relation in H; destruct H as [H _].
    double H3; apply H in H4; destruct H4 as [a [b H4]]; rewrite H4 in *.
    clear H H4; apply Axiom_SchemeP; split; Ens; split.
    + unfold Ordinal in H1; apply Axiom_Scheme in H1; destruct H1.
      assert (Ordinal dom(f) /\ Ordinal x); auto.
      apply Theorem110 in H4; apply Property_dom in H3; auto.
      destruct H4 as [H4 | [H4 | H4]]; try contradiction.
      * eapply Lemma128; eauto.
      * rewrite H4 in H3; auto.
    + apply Property_ran in H3; apply Theorem19; Ens.
Qed.

Theorem Theorem128 :  forall g,
  exists f, Function f /\ Ordinal dom(f) /\
  (forall x, Ordinal_Number x -> f [x] = g [f | (x)]).
Proof.
  intros; exists (En_f' g).
  assert (Function (En_f' g)).
  { unfold Function; intros; split; intros.
    - unfold Relation; intros; PP H a b; eauto.
    - destruct H; apply Axiom_SchemeP in H; apply Axiom_SchemeP in H0.
      destruct H, H1, H2, H2, H3, H4, H0, H6, H7, H7, H8, H9.
      generalize (Theorem127 _ _ _ H2 H3 H4 H7 H8 H9); intro; destruct H11.
      + apply H11 in H10; eapply H2; eauto.
      + apply H11 in H5; eapply H7; eauto. }
  split; auto.
  - assert (Ordinal dom(En_f' g)).
    { apply Theorem114; unfold Section; intros; split.
      - unfold Subclass; intros; apply Axiom_Scheme in H0.
        destruct H0, H1; apply Axiom_SchemeP in H1; tauto.
      - split; intros.
        + apply Theorem107; apply Theorem113.
        + destruct H0, H1; apply Axiom_Scheme in H1; destruct H1, H3.
          apply Axiom_SchemeP in H3; destruct H3, H4, H5, H5, H6, H7.
          apply Axiom_SchemeP in H2; destruct H2.
          apply Theorem49 in H2; destruct H2.
          apply Axiom_Scheme; split; auto; apply Property_dom in H8.
          assert (u ∈ dom( x0)). { eapply Lemma128; eauto. }
          exists (x0[u]); apply Axiom_SchemeP.
          split; try apply Theorem49; split; auto.
          * apply Theorem19; apply Theorem69; auto.
          * exists x0; split; auto; split; auto; split; auto.
            apply Property_Value; auto. }
    split; intros; auto.
    generalize (classic (x ∈ dom(En_f' g))); intro; destruct H2.
    + apply Axiom_Scheme in H2; destruct H2, H3; apply Axiom_SchemeP in H3.
      destruct H2, H3, H4, H5 as [h [H5 [H6 [H7 H8]]]].
      assert (h ⊂ En_f' g).
      { double H5; unfold Subclass; intros; unfold Function, Relation in H9.
        destruct H9 as [H9 _]; double H10; apply H9 in H11.
        destruct H11 as [a [b H11]]; rewrite H11 in *; clear H9 H11 z.
        apply Axiom_SchemeP; split; try Ens.
        double H10; apply Property_dom in H9.
        split; try apply Axiom_Scheme; Ens; split; Ens.
        eapply Theorem111; eauto. }
      double H8; apply H9 in H10; double H8.
      apply Property_dom in H11; apply H7 in H11.
      double H8; apply Property_dom in H12; apply Property_dom in H8.
      apply Property_Value in H8; auto; apply Property_dom in H10.
      apply Property_Value in H10; auto; apply H9 in H8.
      assert (h [x] = (En_f' g) [x]). { eapply H; eauto. }
      rewrite <- H13; clear H13.
      assert (h | (x) = En_f' g | (x)).
      { apply Axiom_Extent.
        split; intros; apply Axiom_Scheme in H13; destruct H13, H14.
        - apply Axiom_Scheme; repeat split; auto.
        - apply Axiom_Scheme; repeat split; auto; rewrite Theorem70; auto.
          PP H15 a b; apply Axiom_SchemeP in H16.
          apply Axiom_SchemeP; split; auto.
          destruct H16, H17; assert (a ∈ dom(h)). { eapply Lemma128; eauto. }
          apply Property_Value in H19; auto; apply H9 in H19; eapply H; eauto. }
      rewrite <- H13; auto.
    + generalize H2; intro; apply Theorem69 in H2; auto.
      rewrite (Lemma128' _ _ H H0 H1 H3).
      generalize (classic (En_f' g ∈ dom(g))); intro; destruct H4.
      * generalize Theorem113; intro; destruct H5 as [H5 _].
        apply Theorem107 in H5; unfold WellOrdered in H5; destruct H5.
        assert ((R ~ dom(En_f' g)) ⊂ R /\ (R ~ dom(En_f' g)) ≠ Φ).
        { split; try (red; intros; apply Axiom_Scheme in H7; tauto).
          intro; generalize (Property114 _ H0); intro.
          unfold Section in H8; destruct H8.
          apply Property_Φ in H8; apply H8 in H7.
          rewrite <- H7 in H3; contradiction. }
        apply H6 in H7; destruct H7 as [y H7].
        assert (((En_f' g) ∪ [[y,g[En_f' g]]]) ⊂ (En_f' g)).
        { unfold Subclass; intros.
          apply Axiom_Scheme in H8; destruct H8, H9; auto.
          assert (Ensemble ([y, g [En_f' g]])).
          { destruct H7; AssE y; apply Theorem69 in H4.
            apply Theorem19 in H4; apply Theorem49; tauto. }
          apply Axiom_Scheme in H9; destruct H9.
          rewrite H11; try apply Theorem19; auto.
          apply Axiom_SchemeP; split; auto; split.
          - unfold FirstMember in H7; destruct H7.
            apply Axiom_Scheme in H7; tauto.
          - exists ((En_f' g) ∪ [[y,g[En_f' g]]]).
            assert (Function (En_f' g ∪ [[y, g [En_f' g]]])).
            { unfold Function; split; intros.
              - unfold Relation; intros; apply Axiom_Scheme in H12.
                destruct H12, H13; try PP H13 a b; eauto.
                apply Axiom_Scheme in H13; destruct H13; apply Theorem19 in H10.
                apply H14 in H10; eauto.
              - destruct H12; apply Axiom_Scheme in H12.
                destruct H12 as [_ H12].
                apply Axiom_Scheme in H13; destruct H13 as [_ H13].
                unfold FirstMember in H7; destruct H7.
                apply Axiom_Scheme in H7; destruct H7 as [_ [_ H7]].
                apply Axiom_Scheme in H7; destruct H7, H12, H13.
                + eapply H; eauto.
                + apply Axiom_Scheme in H13; destruct H13.
                  apply Theorem19 in H10.
                  apply H16 in H10; apply Theorem55 in H10;
                  destruct H10; try apply Theorem49; auto; rewrite H10 in H12.
                  apply Property_dom in H12; contradiction.
                + apply Axiom_Scheme in H12; destruct H12.
                  apply Theorem19 in H10.
                  apply H16 in H10; apply Theorem55 in H10; destruct H10;
                  try apply Theorem49; auto; rewrite H10 in H13.
                  apply Property_dom in H13; contradiction.
                + double H12; apply Axiom_Scheme in H12.
                  apply Axiom_Scheme in H13.
                  destruct H12, H13; double H10.
                  apply Theorem19 in H10; apply H17 in H10.
                  apply Theorem19 in H19; apply H18 in H19.
                  apply Theorem55 in H10; destruct H10;
                  apply Theorem49 in H12; auto.
                  apply Theorem55 in H19; destruct H19;
                  apply Theorem49 in H13; auto.
                  rewrite H20, H21; auto. }
            split; auto; split.
            + apply Theorem114; unfold Section; intros; split.
              * unfold Subclass; intros.
                apply Axiom_Scheme in H13; destruct H13, H14.
                apply Axiom_Scheme in H14; destruct H14, H15.
                -- apply Property_dom in H15; apply Axiom_Scheme.
                   split; Ens; eapply Theorem111; eauto.
                -- apply Axiom_Scheme in H15; destruct H15.
                   apply Theorem19 in H10.
                   apply H16 in H10; apply Theorem55 in H10; destruct H10;
                   try apply Theorem49; auto; destruct H7.
                   apply Axiom_Scheme in H7; rewrite H10; tauto.
              * split; try (apply Theorem107; apply Theorem113); intros.
                destruct H13, H14; apply Axiom_Scheme in H14; destruct H14, H16.
                apply Axiom_Scheme in H16; destruct H16, H17.
                -- apply Axiom_Scheme; split; Ens.
                   assert ([u, (En_f' g) [u]] ∈ (En_f' g)).
                   { apply Property_Value; auto; apply Property_dom in H17.
                     unfold Rrelation in H15; apply Axiom_SchemeP in H15.
                     destruct H15; eapply Lemma128; eauto. }
                   exists ((En_f' g) [u]); apply Axiom_Scheme; split; Ens.
                -- assert ([u, (En_f' g) [u]] ∈ (En_f' g)).
                   { apply Property_Value; auto.
                     apply Axiom_Scheme in H17; destruct H17.
                     apply Theorem19 in H10; apply H18 in H10.
                     apply Theorem55 in H10;
                     destruct H10; try apply Theorem49; auto.
                     subst v; unfold FirstMember in H7; destruct H7.
                     generalize (classic (u ∈ dom( En_f' g))); intro.
                     destruct H20; auto.
                     absurd (Rrelation u E y); auto; try apply H10.
                     apply Axiom_Scheme; repeat split; Ens.
                     apply Axiom_Scheme; split; Ens. }
                   apply Axiom_Scheme; split; Ens; exists ((En_f' g) [u]).
                   apply Axiom_Scheme; split; Ens.
            + split; intros.
              * apply Property_Value in H13; auto.
                apply Axiom_Scheme in H13; destruct H13, H14.
                -- apply Axiom_SchemeP in H14; destruct H14, H15.
                   destruct H16 as [h [H16 [H17 [H18 H19]]]].
                   double H19; apply Property_dom in H20.
                   rewrite Theorem70 in H19; auto.
                   apply Axiom_SchemeP in H19; destruct H19.
                   assert (h ⊂ En_f' g).
                   { unfold Subclass; intros; double H16.
                     unfold Function, Relation in H23; destruct H23 as [H23 _].
                     double H22; apply H23 in H24; destruct H24 as [a [b H24]].
                     rewrite H24 in *; clear H23 H24; apply Axiom_SchemeP.
                     split; try Ens; double H22; apply Property_dom in H23.
                     split; try apply Axiom_Scheme; Ens.
                     split; try Ens; eapply Theorem111; eauto. }
                   assert ((En_f' g ∪ [[y, g[En_f' g]]])|(z0) = En_f' g|(z0)).
                   { unfold Restriction; rewrite Theorem6'; rewrite Theorem8.
                     assert ((z0) × μ ∩ [[y, g [En_f' g]]] = Φ).
                     { apply Axiom_Extent; split; intros.
                       - apply Axiom_Scheme in H23; destruct H23, H24; auto.
                         PP H24 a b; apply Axiom_SchemeP in H26.
                         destruct H26, H27.
                         apply Axiom_Scheme in H25; destruct H25.
                         apply Theorem19 in H10; apply H29 in H10.
                         apply Theorem55 in H10; apply Theorem49 in H25; auto.
                         destruct H10; rewrite H10 in H27.
                         assert (y ∈ dom( h)).   { eapply Lemma128; eauto. }
                         apply Property_Value in H31; auto.
                         apply H22 in H31; apply Property_dom in H31.
                         unfold FirstMember in H7; destruct H7.
                         apply Axiom_Scheme in H7; destruct H7, H33.
                         apply Axiom_Scheme in H34; destruct H34; contradiction.
                       - generalize (Theorem16 z1); contradiction. }
                     rewrite H23, Theorem6, Theorem17; apply Theorem6'. }
                   rewrite H21, H23.
                   assert (h | (z0) = En_f' g | (z0)).
                   { apply Axiom_Extent; split; intros.
                     - apply Axiom_Scheme in H24; destruct H24, H25.
                       apply Axiom_Scheme; repeat split; auto.
                     - apply Axiom_Scheme in H24; destruct H24, H25.
                       apply Axiom_Scheme.
                       repeat split; auto; rewrite Theorem70; auto.
                       PP H26 a b; apply Axiom_SchemeP in H27.
                       apply Axiom_SchemeP.
                       split; auto; destruct H27 as [_ [H27 _]].
                       assert (a ∈ dom(h)). { eapply Lemma128; eauto. }
                       apply Property_Value in H28; auto; apply H22 in H28.
                       eapply H; eauto. }
                   rewrite <- H24; auto.
                -- apply Axiom_Scheme in H14; destruct H14.
                   double H10; apply Theorem19 in H10; apply H15 in H10.
                   apply Theorem55 in H10; apply Theorem49 in H13; auto.
                   destruct H10; subst z0; rewrite H17.
                   assert ((En_f' g ∪ [[y, g [En_f' g]]])|(y) = En_f' g|(y)).
                   { apply Axiom_Extent; split; intros.
                     - apply Axiom_Scheme in H10; destruct H10, H18.
                       apply Axiom_Scheme in H18; destruct H18, H20.
                       + apply Axiom_Scheme; tauto.
                       + PP H19 a b; apply Axiom_SchemeP in H21.
                         destruct H21, H22.
                         apply Axiom_Scheme in H20; destruct H20.
                         apply Theorem19 in H16; apply H24 in H16.
                         apply Theorem55 in H16; apply Theorem49 in H21; auto.
                         destruct H16; rewrite H16 in H22.
                         generalize (Theorem101 y); intro; contradiction.
                     - unfold Restriction; rewrite Theorem6', Theorem8.
                       apply Axiom_Scheme.
                       split; Ens; left; rewrite Theorem6'; Ens. }
                   rewrite H10; unfold FirstMember in H7; destruct H7.
                   apply Axiom_Scheme in H7; destruct H7, H19.
                   apply Axiom_Scheme in H20; destruct H20.
                   rewrite Lemma128'; auto.
              * apply Axiom_Scheme; split; Ens; right.
                apply Axiom_Scheme; split; Ens. }
        unfold FirstMember in H7; destruct H7.
        assert (y ∈ dom(En_f' g ∪ [[y, g [En_f' g]]])).
        { apply Axiom_Scheme; split; Ens; exists g [En_f' g].
          assert (Ensemble ([y, g [En_f' g]])).
          { apply Theorem49; split; Ens.
            apply Theorem69 in H4; apply Theorem19; auto. }
          apply Axiom_Scheme; split; Ens; right; apply Axiom_Scheme; auto. }
        apply Axiom_Scheme in H7; destruct H7, H11; apply Axiom_Scheme in H12.
        destruct H12; elim H13; apply Axiom_Scheme in H10; destruct H10, H14.
        apply H8 in H14; apply Property_dom in H14; auto.
      * apply Theorem69 in H4; rewrite H2, H4; auto.
Qed.

Lemma Lemma128'' : forall f h,
  Function f -> Function h -> h ⊂ f -> f | (dom(h)) = h.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme in H2; destruct H2, H3.
    PP H4 a b; apply Axiom_SchemeP in H5; destruct H5, H6; double H3.
    rewrite Theorem70; rewrite Theorem70 in H3; auto.
    apply Axiom_SchemeP in H3; destruct H3.
    apply Axiom_SchemeP; split; Ens; rewrite H9 in *.
    apply Property_Value in H6; auto.
    apply H1 in H6; eapply H; eauto.
  - apply Axiom_Scheme; repeat split; Ens.
    rewrite Theorem70 in H2; auto.
    PP H2 a b; rewrite <- Theorem70 in H3; auto.
    apply Axiom_SchemeP; repeat split; Ens.
    + apply Property_dom in H3; auto.
    + AssE [a,b]; apply Theorem49 in H4.
      apply Theorem19; tauto.
Qed.

Lemma Lemma128''' : forall h, Function h -> h | (dom(h)) = h.
Proof.
  intros; apply Axiom_Extent; split; intros.
  - apply Axiom_Scheme in H0; tauto.
  - apply Axiom_Scheme; repeat split; Ens.
    rewrite Theorem70 in H0; auto.
    PP H0 a b; rewrite <- Theorem70 in H1; auto.
    apply Axiom_SchemeP; repeat split; Ens.
    + apply Property_dom in H1; auto.
    + AssE [a,b]; apply Theorem49 in H2.
      apply Theorem19; tauto.
Qed.

Lemma Lemma128'''' : forall f g h,
  Function f -> Function h -> Ordinal dom(f) ->
  Ordinal dom( h)-> (forall x, Ordinal_Number x -> f [x] = g [f | (x)]) ->
  (forall x, Ordinal_Number x -> h [x] = g [h | (x)]) -> h ⊂ f -> h = f.
Proof.
  intros.
  generalize (Theorem110 _ _ (Lemma_xy _ _ H1 H2)); intro.
  destruct H6 as [H8 | [H6 | H6]].
  - apply Property_Value in H8; auto.
    apply H5 in H8; apply Property_dom in H8.
    apply Theorem101 in H8; elim H8.
  - assert (Ordinal_Number dom(h)).
    { unfold Ordinal_Number; apply Axiom_Scheme; split; Ens. }
    double H7; apply H3 in H7; apply H4 in H8.
    rewrite Lemma128'' in H7; rewrite Lemma128''' in H8; auto.
    apply Theorem69 in H6; rewrite H7 in H6.
    generalize (Theorem101 dom(h)); intro.
    apply Theorem69 in H9; rewrite H8 in H9.
    rewrite H9 in H6; apply Theorem101 in H6; elim H6.
  - apply Theorem27; split; auto.
    unfold Subclass; intros.
    rewrite Theorem70; rewrite Theorem70 in H7; auto.
    PP H7 a b; double H8; rewrite <- Theorem70 in H8; auto.
    apply Axiom_SchemeP in H9; destruct H9.
    apply Axiom_SchemeP; split; auto; rewrite H10 in *.
    assert ([a,h[a]] ∈ h).
    { apply Property_Value; auto.
      apply Property_dom in H8; rewrite <- H6; auto. }
    apply H5 in H11; eapply H; eauto.
Qed.

Theorem Theorem128' :  forall g,
  forall f, Function f /\ Ordinal dom(f) /\
  (forall x, Ordinal_Number x -> f [x] = g [f | (x)]) ->
  forall h, Function h /\ Ordinal dom(h) /\
  (forall x, Ordinal_Number x -> h [x] = g [h | (x)]) -> f = h.
Proof.
  intros; destruct H, H0, H1, H2.
  assert (forall u, u ∈ dom(f) -> f [u] = g [f | (u)]); intros.
  { apply H3; unfold Ordinal_Number; apply Axiom_Scheme; split; Ens.
    apply Theorem111 with (x:= dom(f)); auto. }
  assert (forall u, u ∈ dom(h) -> h [u] = g [h | (u)]); intros.
  { apply H4; unfold Ordinal_Number; apply Axiom_Scheme; split; Ens.
    apply Theorem111 with (x:= dom(h)); auto. }
  generalize (Theorem127 f h g H H1 H5 H0 H2 H6); intro; destruct H7.
  - symmetry; eapply Lemma128''''; eauto.
  - eapply Lemma128''''; eauto.
Qed.

Hint Resolve Theorem128 : set.


End Ord.

Export Ord.

