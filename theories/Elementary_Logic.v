Require Export Classical.

(* ELEMENTARY LOGIC *)

Module Logic.

Proposition Lemma_x : forall x: Prop, x -> x /\ x.
Proof. intros; split; auto. Qed.

Ltac double H := apply Lemma_x in H; destruct H.

Proposition Lemma_xy : forall (x y: Prop), x -> y -> x /\ y.
Proof. intros; split; auto. Qed.

Ltac add y H:= apply (Lemma_xy _ y) in H; auto.

Proposition definition_not : forall A B, (A<->B) -> (~ A) -> (~ B).
Proof. intros; destruct H; apply imply_to_or in H1; destruct H1; tauto. Qed.

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' 'λ' x .. y ']' , t").

Hint Resolve Lemma_x Lemma_xy : set.


(* THE CLASSIFICATION AXIOM SCHEME *)

(* Class: the universe of discourse consists of classes. *)

Parameter Class : Type.


(* ∈: is read 'is a member of' or 'belongs to.' *)

Parameter In : Class -> Class -> Prop.

Notation "x ∈ y" := (In x y) (at level 10).


(* I Axiom of extent  For each x and each y it is true that x=y if and only if
   for each z, z∈x when and only when z∈y. *)

Axiom Axiom_Extent : forall (x y: Class),
  x = y <-> (forall z: Class, z∈x <-> z∈y).

Hint Resolve Axiom_Extent : set.


(* 1 Definition  x is a set iff for some y, x∈y. *)

Definition Ensemble (x: Class) : Prop := exists y: Class, x∈y.

Ltac Ens := unfold Ensemble; eauto.

Ltac AssE x := assert (Ensemble x); Ens.

Hint Unfold Ensemble : set.


(* {...:...} : the classifier. *)

Parameter Classifier : forall P: Class -> Prop, Class.

Notation "\{ P \}" := (Classifier P) (at level 0).


(* II Classification axiom-scheme  An axiom results if in the following 'a' and
   'b' are replaced by variables, 'A' by a formula P and 'B' by the formula
   obtained from P by replacing each occurrence of the variable which replaced
   a by the variable which replaced b:
   For each b, b ∈ { a : A } if and only if b is a set and B. *)

Axiom Axiom_Scheme : forall (b: Class) (P: Class -> Prop),
  b ∈ \{ P \} <-> Ensemble b /\ (P b).

Hint Resolve Axiom_Scheme : set.


End Logic.

Export Logic.

