Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
Open Scope string_scope.
From Coq Require Import Program.Equality.
From MySystem Require Import Smallstep.
From MySystem Require Import Maps.
From MySystem Require Import BaseSystem.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Logic.FunctionalExtensionality.
Module TypeSafety.
Import BaseSystem.

(* Lemma TypeOverComp : forall (P1 P2: Proc) (Omega: context) (z: string) (T: CType),
  Omega |-- <{P1 | P2}> :: z \in T ->
  exists (Omega1 Omega2: context) (z1 z2: string) (T1 T2: CType),
  (Omega1 |-- P1 :: z1 \in T1) /\ (Omega2 |-- P2 :: z2 \in T2).
Proof.
  intros. dependent induction H.
  - apply IHhas_type. reflexivity.
  - apply IHhas_type. reflexivity.
  - apply IHhas_type. reflexivity.
  - apply IHhas_type. reflexivity.
  - apply IHhas_type. *)

Lemma not_so_empty: forall (Omega: context) (x: string) (A: CType),
  ~(x |-> A; Omega) = empty.
Proof.
  intros. unfold not. intros.
  assert (empty x = Some A).
  - rewrite <- H. unfold update. unfold t_update. destruct (String.eqb x x) eqn:E1.
    + reflexivity.
    + apply eqb_neq in E1. unfold not in E1. assert (x = x). { reflexivity. }
      apply E1 in H0. inversion H0.
  - inversion H0.
Qed.

Lemma functional_equality: forall {A B: Type} (f g: A -> B),
  f = g -> forall (x: A), f x = g x.
Proof.
  intros. rewrite H. reflexivity.
Qed.

Lemma so_empty: forall (Omega Omega': context),
  (Omega; Omega') = empty -> Omega = empty /\ Omega' = empty.
Proof.
  intros. unfold merge in H. unfold empty in H. unfold t_empty in H.
  split.
  - unfold empty. unfold t_empty. apply functional_extensionality.
    intros. apply functional_equality with (x := x) in H.
    destruct (Omega x) eqn:E1.
    + inversion H.
    + reflexivity.
  - unfold empty. unfold t_empty. apply functional_extensionality.
    intros. apply functional_equality with (x := x) in H.
    destruct (Omega x) eqn:E1.
    + inversion H.
    + assumption.
Qed.

(* Lemma single_comp_impossible : forall (Omega: context) (P Q: Proc) (z: string) (T: CType),
  ~ (Omega |-- <{P | Q}> :: z \in T).
Proof.
  intros. unfold not. intros. dependent induction H.
  - apply IHhas_type with (P := P) (Q := Q). reflexivity.
  - apply IHhas_type with (P := P) (Q := Q). reflexivity.
  - apply IHhas_type with (P := P) (Q := Q). reflexivity.
  - apply IHhas_type with (P := P) (Q := Q). reflexivity.
  - dependent induction H0.
    + apply IHhas_type with (P := P) (Q := Q). reflexivity.
    + apply IHmulti with (P := P) (Q := Q).
      * apply TCong with (P := x). apply H. apply multi_R. apply H1.
      * reflexivity.
      * intros. clear P Q H0 IHmulti. induction H1.
        9:{ inversion H2. }
        9:{ inversion H2. }
        9:{ inversion H2. }
        ** inversion H2.
        ** inversion H2.
        ** apply IHhas_type with (P := P) (Q := Q). reflexivity.
        ** apply IHhas_type with (P := <{P | Q}>) (Q := R). reflexivity.
        ** apply IHhas_type with (P := P) (Q := <{Q | R}>). reflexivity.
        ** inversion H2.
        ** Admitted. *)

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~ Q -> ~ P).
Proof.
  intros. unfold not. intros. apply H in H1. apply H0 in H1. contradiction.
Qed.

Theorem de_morgan_not_or : forall (P Q : Prop),
  ~ (P \/ Q) -> ~ P /\ ~ Q.
Proof.
  intros. split.
  - unfold not. intros. unfold not in H. apply H. left. apply H0.
  - unfold not. intros. unfold not in H. apply H. right. apply H0.
Qed.

Theorem de_morgan_not_and : forall (P Q : Prop),
  ~ (P /\ Q) -> ~ P \/ ~ Q.
Proof.
  intros.
  unfold not.
  unfold not in H.
  Admitted.

Lemma merge_update_assoc : forall (Omega Omega': context) (x: string) (T: CType),
  ((x |-> T; Omega); Omega') = (x |-> T; (Omega; Omega')).
Proof. Admitted.

Lemma merge_swap : forall (Omega Omega': context),
  (Omega; Omega') = (Omega'; Omega).
Proof. Admitted.

Lemma merge_assoc : forall (Omega1 Omega2 Omega3: context),
  ((Omega1; Omega2); Omega3) = (Omega1; (Omega2; Omega3)).
Proof. Admitted.

Lemma merge_equal : forall (Omega Omega': context) (x: string) (A B: CType),
  (x |-> A; Omega) = (x |-> B; Omega') -> A = B.
Proof. Admitted.

Lemma update_swap : forall (Omega: context) (x y: string) (A B: CType),
  x <> y -> (x |-> A; y |-> B; Omega) = (y |-> B; x |-> A; Omega).
Proof. Admitted.

Lemma tmp1 : forall (Omega Omega': context) (x: string) (A B: CType),
  (x |-> A; Omega) = (x |->A; Omega') -> (x |-> B; Omega) = (x |-> B; Omega').
Proof. Admitted.

Theorem Preservation : forall (P Q: Proc) (Omega: context) (z: string) (T: CType),
  Omega |-- P :: z \in T -> P --> Q -> Omega |-- Q :: z \in T.
Proof.
  intros.
  induction H0.
  - inversion H.
    + subst. inversion H2.
      * subst. inversion H3.
        ** subst. apply merge_equal in H0 as H1. inversion H1. subst.
           apply TCong with (P := <{P0 | Q0 | [z0 := y] P}>).
           *** rewrite merge_assoc. apply TCut with (x := y) (A := A0).
               **** apply H6.
               **** rewrite merge_swap. rewrite <- merge_update_assoc. rewrite merge_swap.
                    apply TCut with (x := x0) (A := B).
                    ***** apply H7.
                    ***** apply tmp1 with (B := B) in H0.
                          rewrite update_swap. 2:{ apply H14. } rewrite <- H0.
                          apply rename_type_context with (x := z0) (y := y) in H15.
                          apply H15.
    
    dependent induction H4.
      * specialize IHhas_type with (y := y) (Q := Q).
        rewrite merge_assoc. apply TSubBoxL.
        ** rewrite <- merge_assoc. apply IHhas_type.
           *** apply TCut with (A := T0).
               **** apply H4.
               **** apply H6.
               **** clear z T z0 P w z1 y Q T0 H4 H1 IHhas_type H H0 H6 H10.
                    unfold not in H9. unfold has_comm in H9.
                    unfold not. intros. unfold has_comm in H.
                    inversion H. inversion H0. inversion H1. clear H H0 H1.
                    destruct H9. destruct H2. exists x0.
                    unfold update in H. unfold t_update in H.
                    unfold update. unfold t_update.
                    destruct (String.eqb x x0) eqn:E1.
                    ***** exists A. exists x2. split. reflexivity. apply H0.
                    ***** exists x1. exists x2. split. apply H. apply H0.
               **** clear T z0 P Omega' w z1 y Q T0 H4 H1 IHhas_type H H0 H6 H9.
                    unfold update in H10. unfold t_update in H10.
                    unfold update. unfold t_update.
                    destruct (String.eqb x z) eqn:E1.
                    ***** inversion H10.
                    ***** apply H10.
           *** apply H0.
           *** reflexivity.
           *** apply H6.
           *** clear z T z0 P w z1 y Q T0 H4 H1 IHhas_type H H0 H6 H10.
               unfold not. intros. destruct H9.
               unfold has_comm. unfold has_comm in H.
               inversion H. inversion H0. clear H H0. inversion H1. clear H1.
               exists x0.
               unfold update. unfold t_update.
               unfold update in H. unfold t_update in H.
               destruct (String.eqb x x0) eqn:E1.
               ***** exists A. exists x2. split. reflexivity. apply H.
               ***** exists x1. exists x2. inversion H. split. apply H0. apply H1.
           *** clear T z0 P Omega' w z1 y Q T0 H4 H1 IHhas_type H H0 H6 H9.
               unfold update. unfold t_update.
               unfold update in H10. unfold t_update in H10.
               destruct (String.eqb x z) eqn:E1.
               ***** inversion H10.
               ***** apply H10.
        ** apply H1.
      * specialize IHhas_type with (y := y) (Q := Q).
        apply IHhas_type.
        ** apply H.
        ** apply H0.
        ** reflexivity.
        ** apply TSubBoxL. apply H6. apply H1.
        ** apply H9.
        ** apply H10.
      * rewrite merge_assoc. apply TSubDiaL.
        ** rewrite <- merge_assoc. apply IHhas_type.
           *** apply TCut with (A := T0).
               **** apply H4.
               **** apply H6.
               **** clear z T z0 P w z1 y Q T0 H4 H1 IHhas_type H H0 H6 H10.
                    unfold not in H9. unfold has_comm in H9.
                    unfold not. intros. unfold has_comm in H.
                    inversion H. inversion H0. inversion H1. clear H H0 H1.
                    destruct H9. destruct H2. exists x0.
                    unfold update in H. unfold t_update in H.
                    unfold update. unfold t_update.
                    destruct (String.eqb x x0) eqn:E1.
                    ***** exists <{\Next A}>. exists x2. split. reflexivity. apply H0.
                    ***** exists x1. exists x2. split. apply H. apply H0.
               **** clear T z0 P Omega' w z1 y Q T0 H4 H1 IHhas_type H H0 H6 H9.
                    unfold update in H10. unfold t_update in H10.
                    unfold update. unfold t_update.
                    destruct (String.eqb x z) eqn:E1.
                    ***** inversion H10.
                    ***** apply H10.
           *** apply H0.
           *** reflexivity.
           *** apply H6.
           *** clear z T z0 P w z1 y Q T0 H4 H1 IHhas_type H H0 H6 H10.
               unfold not. intros. destruct H9.
               unfold has_comm. unfold has_comm in H.
               inversion H. inversion H0. clear H H0. inversion H1. clear H1.
               exists x0.
               unfold update. unfold t_update.
               unfold update in H. unfold t_update in H.
               destruct (String.eqb x x0) eqn:E1.
               ***** exists <{\Next A}>. exists x2. split. reflexivity. apply H.
               ***** exists x1. exists x2. inversion H. split. apply H0. apply H1.
           *** clear T z0 P Omega' w z1 y Q T0 H4 H1 IHhas_type H H0 H6 H9.
               unfold update. unfold t_update.
               unfold update in H10. unfold t_update in H10.
               destruct (String.eqb x z) eqn:E1.
               ***** inversion H10.
               ***** apply H10.
        ** apply H1.
      * apply IHhas_type.
        ** apply H.
        ** apply H0.
        ** reflexivity.
        ** apply TSubDiaL. apply H6. apply H1.
        ** apply H9.
        ** apply H10.
      * apply IHhas_type.
        ** apply H.
        ** apply H0.
        ** clear z T z0 P Omega' w Omega T0 H4 IHhas_type H H0 H6 H9 H10.
           dependent induction H1. reflexivity.
           specialize IHmulti with (y := y) (Q := Q) (z1 := z1).
           assert (y0 = <{z1<y>; Q}>). { apply IHmulti. reflexivity. }
           subst. clear IHmulti H1.
           inversion H.
        ** apply H6.
        ** apply H9.
        ** apply H10.
    + subst.

(* Lemma Progress : forall (P : Proc) (z: string) (T: CType),
  empty |-- P :: z \in T -> not_poised P ->
  exists (Q: Proc), P --> Q.
Proof.
  intros. subst. dependent induction H.
  - apply not_so_empty in x. contradiction.
  - dependent induction H0. apply IHnot_poised.
    clear H0 IHnot_poised. dependent induction H.
    + reflexivity.
    + specialize IHmulti with (x := x).
      assert (y = <{C[x]}>). { apply IHmulti. reflexivity. }
      clear H0 IHmulti. inversion H.
      * subst. inversion H.
      * subst. inversion H.
      * subst. inversion H.
      * subst. inversion H.
      * subst. inversion H.
      * subst. inversion H.
      * subst. inversion H.
      * subst. inversion H.
      * subst. inversion H.
      * subst. inversion H.
      * subst. inversion H.
  - apply not_so_empty in x. contradiction.
  - clear IHhas_type1 IHhas_type2.
    apply so_empty in x. destruct x. rewrite H5 in H. rewrite H6 in H0.
    clear Omega Omega' H1 H2 H5 H6. dependent induction H4.
    + assert (x0 = z /\ forall (z: string), @empty CType z = None <-> (x0 |-> B0; Omega') z = None).
      { apply type_uniqueness with (P := Q) (A := B) (B := T).
        * apply H0.
        * apply H7. }
      destruct H9. destruct H10 with (z := x0).
      unfold empty in H11. unfold t_empty in H11.
      unfold update in H11. unfold t_update in H11.
      assert (@None CType = @None CType). { reflexivity. }
      apply H11 in H13. destruct (String.eqb x0 x0) eqn: E1.
      * inversion H13.
      * apply eqb_neq in E1. assert (x0 = x0). { reflexivity. }
        apply E1 in H14. contradiction.
    + dependent induction H1.
      * apply IHnot_poised.
        ** apply H3.
        ** apply H0.
        ** apply H.
        ** reflexivity.
      * apply IHmulti.
        ** apply PTCong with (P := x).
           *** apply H4.
           *** apply multi_step with (y := y0). apply H. apply multi_refl.
        ** reflexivity.
        ** intros. apply IHnot_poised.
           *** apply H5.
           *** apply H6.
           *** apply H7.
           *** subst. clear A B y x0 P Q IHmulti H1 H4 IHnot_poised H3 H0 H2 H5 H6 H7.
               inversion H. subst. inversion H2.
        ** apply H3.
        ** apply H0.
        ** apply H2.
  - apply not_so_empty in x. contradiction.
  - dependent induction H0.
    + subst. apply type_uniqueness with (Omega := y |-> A) (x := x) (A := B) in H2.
      * destruct H2. destruct H3 with (z := x).
        unfold update in H4. unfold t_update in H4.
        destruct (String.eqb y x) eqn: E1.
        ** apply eqb_eq in E1. assert (x = y). { rewrite E1. reflexivity. }
           apply H0 in H6. contradiction.
        ** unfold empty in H4. unfold t_empty in H4.
           assert (@None CType = @None CType). { reflexivity. }
           apply H4 in H6. destruct (String.eqb x x) eqn: E2.
           *** inversion H6.
           *** apply eqb_neq in E2. assert (x = x). { reflexivity. } apply E2 in H7. contradiction.
      * apply H.
    + apply IHnot_poised.
      * apply H.
      * apply IHhas_type.
      * clear A B H0 IHnot_poised H IHhas_type.
        dependent induction H1.
        ** reflexivity.
        ** specialize IHmulti with (x := x) (y := y) (P := P).
           assert (y0 = <{ x (y); P }>). { apply IHmulti. reflexivity. }
           subst. clear H1 IHmulti. inversion H.
  - apply so_empty in x. destruct x. subst. clear H2 H1.
    inversion H3.
    + subst. *)

End TypeSafety.