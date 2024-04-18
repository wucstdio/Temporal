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
        -- inversion H2.
        -- inversion H2.
        -- apply IHhas_type with (P := P) (Q := Q). reflexivity.
        -- apply IHhas_type with (P := <{P | Q}>) (Q := R). reflexivity.
        -- apply IHhas_type with (P := P) (Q := <{Q | R}>). reflexivity.
        -- inversion H2.
        -- Admitted. *)

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

Lemma has_comm_mergeL : forall (Omega1 Omega2 Omega3: context),
  has_comm Omega1 Omega3 -> has_comm (Omega1; Omega2) Omega3.
Proof. Admitted.

Lemma has_comm_mergeR : forall (Omega1 Omega2 Omega3: context),
  has_comm Omega1 Omega2 -> has_comm Omega1 (Omega2; Omega3).
Proof. Admitted.

Lemma has_comm_mergeL' : forall (Omega1 Omega2 Omega3: context),
  has_comm (Omega1; Omega2) Omega3 -> (has_comm Omega1 Omega2 \/ has_comm Omega2 Omega3).
Proof. Admitted.

Lemma has_comm_mergeR' : forall (Omega1 Omega2 Omega3: context),
  has_comm Omega1 (Omega2; Omega3) -> (has_comm Omega1 Omega2 \/ has_comm Omega1 Omega3).
Proof. Admitted.

Lemma tmp1 : forall (Omega Omega': context) (x: string) (A B: CType),
  (x |-> A; Omega) = (x |-> A; Omega') -> (x |-> B; Omega) = (x |-> B; Omega').
Proof. Admitted.

Theorem Preservation' : forall (P Q: Proc) (Omega: context) (z: string) (T: CType),
  Omega |-- P :: z \in T -> P --> Q -> Omega |-- Q :: z \in T.
Proof.
  intros.
  generalize dependent H0. generalize dependent Q.
  induction H.
  23:{ intros. apply IHhas_type. apply RCong with (P' := Q) (Q' := Q0).
    assumption. assumption. apply multi_refl. }
  - clear. intros. dependent induction H0.
    apply TCong with (P := Q'). 2:{ assumption. }
    apply IHreduction with (P := P).
    generalize dependent H. clear. intros.
    dependent induction H. reflexivity. apply IHmulti. inversion H.
  - clear. intros. dependent induction H0.
    apply TCong with (P := Q'). 2:{ assumption. }
    apply IHreduction.
    generalize dependent H. clear. intros.
    dependent induction H. reflexivity. apply IHmulti. inversion H.
  - clear. intros. dependent induction H0.
    apply TCong with (P := Q'). 2:{ assumption. }
    apply IHreduction with (P := P) (y := y).
    generalize dependent H. clear. intros.
    dependent induction H. reflexivity. apply IHmulti. inversion H.
  - clear. intros. dependent induction H0.
    apply TCong with (P := Q'). 2:{ assumption. }
    apply IHreduction with (P := P) (Q := Q) (y := y).
    generalize dependent H. clear. intros.
    dependent induction H. reflexivity. apply IHmulti. inversion H.
  - clear. intros. dependent induction H0.
    apply TCong with (P := Q'). 2:{ assumption. }
    apply IHreduction with (P := P) (Q := Q) (y := y).
    generalize dependent H. clear. intros.
    dependent induction H. reflexivity. apply IHmulti. inversion H.
  - clear. intros. dependent induction H0.
    apply TCong with (P := Q'). 2:{ assumption. }
    apply IHreduction with (P := P) (y := y).
    generalize dependent H. clear. intros.
    dependent induction H. reflexivity. apply IHmulti. inversion H.
  - intros. inversion H4.
    + subst. simpl. clear IHhas_type1 IHhas_type2 H4.
      remember Q1 as Q. clear Q1 HeqQ.
      remember P0 as P. clear P0 HeqP.
      remember x0 as x1. clear x0 Heqx1.
      remember x as x0. clear x Heqx0.
      remember x1 as x. clear x1 Heqx.
      remember z0 as z1. clear z0 Heqz1.
      remember z as z0. clear z Heqz0.
      remember z1 as z. clear z1 Heqz.
      remember H as H0_. clear H HeqH0_.
      remember H0 as H0_0. clear H0 HeqH0_0.
      remember H2 as H0. clear H2 HeqH0.
      remember H1 as H2. clear H1 HeqH2.
      remember H3 as H1. clear H3 HeqH1.
      remember H8 as H. clear H8 HeqH.
      dependent induction H0_.
      * clear IHH0_1 IHH0_2. dependent induction H0_0.
        -- clear IHH0_0. apply merge_equal in x as H9. inversion H9. subst.
          clear H9. apply TCong with (P := <{P0 | Q0 | [z := y] P}>).
          ++ rewrite merge_assoc. apply TCut with (x := y) (A := A).
            ** assumption.
            ** rewrite merge_swap. rewrite <- merge_update_assoc. rewrite merge_swap.
              apply TCut with (x := x1) (A := B).
              --- assumption.
              --- apply tmp1 with (B := B) in x.
                rewrite update_swap. 2:{ assumption. } rewrite <- x.
                generalize dependent H0_0. clear. intros.
                apply rename_type_context with (x := z) (y := y) in H0_0 as H.
                2:{ apply no_dup in H0_0. unfold update in H0_0. unfold t_update in H0_0.
                    destruct (String.eqb z z0) eqn:E1. inversion H0_0.
                    apply eqb_neq in E1. assumption. }
                clear H0_0. assert ([z ::= y] (z |-> A; x1 |-> B; Omega0) = (y |-> A; x1 |-> B; Omega0)).
                { clear z0 T P H. apply functional_extensionality. intros.
                  unfold subst_context. unfold update. unfold t_update.
                  destruct (String.eqb x y) eqn:E1.
                  apply eqb_eq in E1.
                  destruct (String.eqb z z) eqn:E2. 2:{ apply eqb_neq in E2. contradiction. }
                  destruct (String.eqb y x) eqn:E3. reflexivity. rewrite E1 in E3. apply eqb_neq in E3. contradiction. }
                rewrite <- H0. apply H.
              --- generalize dependent H2. generalize dependent H6. clear. intros.
                unfold update. unfold t_update.
                destruct (String.eqb y x1) eqn:E1.
                +++ apply eqb_eq in E1. rewrite E1 in H2. contradiction.
                +++ apply H6.
              --- generalize dependent H1. generalize dependent H5. clear. intros.
                unfold not. intros. destruct H5.
                inversion H. destruct H0 as [A']. destruct H0 as [B].
                unfold has_comm. unfold update in H0. unfold t_update in H0.
                exists x. destruct (String.eqb y x) eqn:E1.
                +++ apply eqb_eq in E1. subst. inversion H0. rewrite H1 in H2. inversion H2.
                +++ inversion H0. clear H0. unfold merge. destruct (Omega x) eqn:E2.
                  *** exists c. exists B. split. reflexivity. assumption.
                  *** exists A'. exists B. split. assumption. assumption.
              --- clear P0 Q0 y Omega0 P x1 z T A B H0_0 H3 H4 Omega' H0_1 H0_2 H H0 H1 H2 x H5 H6 H8.
                unfold merge in H7. destruct (Omega z0) eqn:E1.
                +++ inversion H7.
                +++ apply H7.
            ** clear P0 Q0 H3 H4 Omega H0_1 H0_2 H H0 H2 H5 H6 H7.
              apply not_exist with (x := y) in H0_0. 2:{ assumption. } inversion H0_0.
              unfold merge. rewrite H1.
              clear Omega'0 P z0 H1 H0_0 H H8 T.
              apply tmp1 with (B := B) in x. rewrite x in H0. clear Omega0 x.
              unfold update in H0. unfold t_update in H0.
              destruct (String.eqb z y). inversion H0.
              destruct (String.eqb x1 y). inversion H0. assumption.
            ** generalize dependent H. generalize dependent H5. clear. intros.
              unfold not. intros. destruct H5.
              apply has_comm_mergeR' in H0. inversion H0.
              --- apply H in H1. contradiction.
              --- apply has_comm_mergeL. assumption.
            ** clear P0 Q0 y Omega0 P x1 z T A B H0_0 H3 H4 Omega' H0_1 H0_2 H H0 H1 H2 x H5 H6 H8.
              unfold merge in H7. destruct (Omega z0) eqn:E1.
              inversion H7. reflexivity.
          ++ clear. apply multi_step with (y := <{(P0 | Q0) | [z := y] P}>).
            apply SAssoc'. apply multi_refl.
        -- apply no_dup in H0_0.
          clear H3 IHH0_0 H0_1 H0_2 H H0 H1 H2 H4 H5 H6 H7.
          unfold update in H0_0. unfold t_update in H0_0.
          destruct (String.eqb z x). inversion H0_0.
          destruct (String.eqb x x) eqn:E1. inversion H0_0. apply eqb_neq in E1. contradiction.
        -- apply IHH0_0 with (x := x1) (A := A) (B := B).
          ++ assumption.
          ++ assumption.
          ++ assumption.
          ++ assumption.
          ++ assumption.
          ++ assumption.
          ++ rewrite <- x. clear. apply context_inequality with (x := x0).
            unfold not. intros. unfold update in H. unfold t_update in H.
            destruct (String.eqb x0 x0) eqn:E1.
            ** inversion H. apply no_infinite_next with (T := A0).
              rewrite H1. reflexivity.
            ** apply eqb_neq in E1. contradiction.
          ++ reflexivity.
          ++ assumption.
          ++ assumption.
          ++ assumption.
          ++ assumption.
        -- apply TSubBoxR. 2:{ assumption. }
          apply IHH0_0 with (x := x) (A := A) (B := B).
          ++ assumption.
          ++ assumption.
          ++ assumption.
          ++ assumption.
          ++ assumption.
          ++ assumption.
          ++ apply buggy_lemma1.
          ++ reflexivity.
          ++ assumption.
          ++ assumption.
          ++ assumption.
          ++ assumption.
        -- apply IHH0_0 with (x := x1) (A := A) (B := B).
          ++ assumption.
          ++ assumption.
          ++ assumption.
          ++ assumption.
          ++ assumption.
          ++ assumption.
          ++ rewrite <- x. clear. apply context_inequality with (x := x0).
            unfold not. intros. unfold update in H. unfold t_update in H.
            destruct (String.eqb x0 x0) eqn:E1.
            ** inversion H. apply no_infinite_next with (T := A0). assumption.
            ** apply eqb_neq in E1. contradiction.
          ++ reflexivity.
          ++ assumption.
          ++ assumption.
          ++ assumption.
          ++ assumption.
        -- apply TSubDiaR. 2:{ assumption. }
          apply IHH0_0 with (x := x) (A := A) (B := B).
          ++ assumption.
          ++ assumption.
          ++ assumption.
          ++ assumption.
          ++ assumption.
          ++ assumption.
          ++ apply buggy_lemma1.
          ++ reflexivity.
          ++ assumption.
          ++ assumption.
          ++ assumption.
          ++ assumption.
        -- apply IHH0_0 with (x := x) (A := A) (B := B).
          ++ assumption.
          ++ assumption.
          ++ assumption.
          ++ assumption.
          ++ assumption.
          ++ assumption.
          ++ apply buggy_lemma1.
          ++ clear Omega Omega'0 P0 Q0 y Omega' A B z0 T H0_0 IHH0_0 H0_1 H0_2 H H0 H1 H2 H4 H5 H6 H7.
            dependent induction H3. reflexivity.
            assert (y = <{x(z); P}>). { apply IHmulti. reflexivity. }
            subst. clear IHmulti H3. inversion H.
          ++ assumption.
          ++ assumption.
          ++ assumption.
          ++ assumption.
      * destruct H6. apply no_dup in H0_2.
        generalize dependent H0_0. generalize dependent H0_2. generalize dependent H8. clear. intros.
        unfold update in H0_2. unfold t_update in H0_2.
        destruct (String.eqb x z1) eqn:E1. inversion H0_2.
        apply eqb_neq in E1. clear H0_2.
        unfold update in H8. unfold t_update in H8.
        destruct (String.eqb x z0) eqn:E2. inversion H8.
        apply eqb_neq in E2. clear H8.
        assert (exists T: CType, Omega' x = Some T).
        { clear Omega Omega'0 A B.
          dependent induction H0_0.
          -- generalize dependent x. generalize dependent E1. clear. intros.
            assert (Omega' x1 = Some <{A * B}>).
            { apply functional_equality with (x := x1) in x.
              unfold update in x. unfold t_update in x.
              destruct (String.eqb x1 x1) eqn:E2. 2:{ apply eqb_neq in E2. contradiction. }
              destruct (String.eqb z1 x1) eqn:E3. apply eqb_eq in E3. rewrite E3 in E1. contradiction.
              rewrite x. reflexivity. }
            unfold has_comm. exists <{A * B}>. assumption.
          -- contradiction.
          -- apply IHH0_0 with (T0 := T0) (z1 := z1) (z := z) (P := P).
            ++ assumption.
            ++ assumption.
            ++ rewrite <- x. clear. apply context_inequality with (x := x0).
              unfold not. intros. unfold update in H. unfold t_update in H.
              destruct (String.eqb x0 x0) eqn:E1.
              ** inversion H. apply no_infinite_next with (T := A). rewrite H1. reflexivity.
              ** apply eqb_neq in E1. contradiction.
            ++ reflexivity.
          -- apply IHH0_0 with (T0 := T0) (z1 := z1) (z := z) (P := P).
            ++ assumption.
            ++ assumption.
            ++ apply buggy_lemma1.
            ++ reflexivity.
          -- apply IHH0_0 with (T0 := T0) (z1 := z1) (z := z) (P := P).
            ++ assumption.
            ++ assumption.
            ++ rewrite <- x. clear. apply context_inequality with (x := x0).
              unfold not. intros. unfold update in H. unfold t_update in H.
              destruct (String.eqb x0 x0) eqn:E1.
              ** inversion H. apply no_infinite_next with (T := A). assumption.
              ** apply eqb_neq in E1. contradiction.
            ++ reflexivity.
          -- apply IHH0_0 with (T0 := T0) (z1 := z1) (z := z) (P := P).
            ++ assumption.
            ++ assumption.
            ++ apply buggy_lemma1.
            ++ reflexivity.
          -- apply IHH0_0 with (T0 := T0) (z1 := z1) (z := z) (P := P).
            ++ assumption.
            ++ assumption.
            ++ apply buggy_lemma1.
            ++ generalize dependent H. clear. intros.
              dependent induction H.
              ** reflexivity.
              ** assert (y = <{x(z); P}>). { apply IHmulti. reflexivity. }
                subst. clear IHmulti H0. inversion H. }
        generalize dependent H. clear. intros.
        unfold has_comm. destruct H.
        exists x. exists <{A -o B}>. exists x0. split.
        -- unfold update. unfold t_update.
          destruct (String.eqb x x) eqn:E1. reflexivity. apply eqb_neq in E1. contradiction.
        -- assumption.
      * rewrite merge_update_assoc. apply TSubBoxL. 2:{ assumption. }
        rewrite <- merge_update_assoc. apply IHH0_ with (x := x).
        -- reflexivity.
        -- assumption.
        -- generalize dependent H0. clear. intros.
          unfold not. intros. destruct H0. unfold has_comm in H.
          destruct H. destruct H. destruct H. destruct H.
          unfold update in H. unfold t_update in H.
          unfold has_comm. exists x.
          unfold update. unfold t_update.
          destruct (String.eqb x0 x) eqn:E1.
          ++ exists A. exists x2. split. reflexivity. assumption.
          ++ exists x1. exists x2. split. assumption. assumption.
        -- assumption.
        -- generalize dependent H1. clear. intros.
          unfold update in H1. unfold t_update in H1.
          unfold update. unfold t_update.
          destruct (String.eqb x0 z0) eqn:E1.
          ++ inversion H1.
          ++ assumption.
        -- assumption.
      * apply IHH0_ with (x := x).
        -- reflexivity.
        -- apply TSubBoxL. assumption. assumption.
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
      * rewrite merge_update_assoc. apply TSubDiaL. 2:{ assumption. }
        rewrite <- merge_update_assoc. apply IHH0_ with (x := x).
        -- reflexivity.
        -- assumption.
        -- generalize dependent H0. clear. intros.
          unfold not. intros. destruct H0. unfold has_comm in H.
          destruct H. destruct H. destruct H. destruct H.
          unfold update in H. unfold t_update in H.
          unfold has_comm. exists x.
          unfold update. unfold t_update.
          destruct (String.eqb x0 x) eqn:E1.
          ++ exists <{\Next A}>. exists x2. split. reflexivity. assumption.
          ++ exists x1. exists x2. split. assumption. assumption.
        -- assumption.
        -- generalize dependent H1. clear. intros.
          unfold update in H1. unfold t_update in H1.
          unfold update. unfold t_update.
          destruct (String.eqb x0 z0) eqn:E1.
          ++ inversion H1.
          ++ assumption.
        -- assumption.
      * apply IHH0_ with (x := x).
        -- reflexivity.
        -- apply TSubDiaL. assumption. assumption.
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
      * apply IHH0_ with (x := x).
        -- generalize dependent H. clear. intros.
          dependent induction H.
          ++ reflexivity.
          ++ assert (y0 = <{x<y>; Q}>). { apply IHmulti. reflexivity. }
            subst. clear IHmulti H0. inversion H.
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
    + subst. clear IHhas_type1 IHhas_type2 H4.
      dependent induction H.
      * clear IHhas_type. dependent induction H0.
        -- clear IHhas_type1 IHhas_type2. apply TCut with (x := x0) (A := A).
          ++ assumption.
          ++ generalize dependent H0_. generalize dependent x. clear. intros.
            apply merge_equal in x as H. inversion H. subst. clear H.
            apply tmp1 with (B := A) in x. rewrite x in H0_. assumption.
          ++ assumption.
          ++ assumption.
          ++ assumption.
        -- apply no_dup in H0_. generalize dependent H0_. clear. intros.
          unfold update in H0_. unfold t_update in H0_.
          destruct (String.eqb x0 x0) eqn:E1.
          ++ inversion H0_.
          ++ apply eqb_neq in E1. contradiction.
        -- apply IHhas_type with (x0 := x0) (A := A) (B := B) (R := R).
          ++ assumption.
          ++ rewrite <- x. clear. apply context_inequality with (x := x1).
            unfold update. unfold t_update.
            destruct (String.eqb x1 x1) eqn:E1.
            ** unfold not. intros. inversion H.
              apply no_infinite_next with (T := A0). rewrite H1. reflexivity.
            ** apply eqb_neq in E1. contradiction.
          ++ reflexivity.
          ++ assumption.
          ++ assumption.
          ++ assumption.
        -- apply TSubBoxR. 2:{ assumption. }
          apply IHhas_type with (x0 := x0) (A := A) (B := B) (R := R).
          ++ assumption.
          ++ apply buggy_lemma1.
          ++ reflexivity.
          ++ assumption.
          ++ assumption.
          ++ assumption.
        -- apply IHhas_type with (x0 := x0) (A := A) (B := B) (R := R).
          ++ assumption.
          ++ rewrite <- x. clear. apply context_inequality with (x := x1).
            unfold update. unfold t_update.
            destruct (String.eqb x1 x1) eqn:E1.
            ** unfold not. intros. inversion H.
              apply no_infinite_next with (T := A0). assumption.
            ** apply eqb_neq in E1. contradiction.
          ++ reflexivity.
          ++ assumption.
          ++ assumption.
          ++ assumption.
        -- apply TSubDiaR. 2:{ assumption. }
          apply IHhas_type with (x0 := x0) (A := A) (B := B) (R := R).
          ++ assumption.
          ++ apply buggy_lemma1.
          ++ reflexivity.
          ++ assumption.
          ++ assumption.
          ++ assumption.
        -- apply IHhas_type with (x0 := x0) (A := A) (B := B) (R := R).
          ++ assumption.
          ++ apply buggy_lemma1.
          ++ generalize dependent H1. clear. intros.
            dependent induction H1.
            ** reflexivity.
            ** assert (y = <{x0.case(Q1, R)}>). { apply IHmulti. reflexivity. }
              subst. clear IHmulti H1. inversion H.
          ++ assumption.
          ++ assumption.
          ++ assumption.
      * destruct H2.
        unfold update in H3. unfold t_update in H3.
        destruct (String.eqb x0 z) eqn:E. inversion H3.
        apply eqb_neq in E.
        generalize dependent H. generalize dependent H0. generalize dependent E. clear. intros.
        apply no_dup in H. unfold update in H. unfold t_update in H.
        destruct (String.eqb x0 z0) eqn:E1. inversion H.
        apply eqb_neq in E1. clear H.
        unfold has_comm. exists x0. exists <{A & B}>.
        unfold update. unfold t_update.
        destruct (String.eqb x0 x0) eqn:E2. 2:{ apply eqb_neq in E2. contradiction. }
        clear E2.
        dependent induction H0.
        -- exists <{A0 + B0}>. split. reflexivity.
          generalize dependent x. generalize dependent E1. clear. intros.
          apply functional_equality with (x := x0) in x.
          unfold update in x. unfold t_update in x.
          destruct (String.eqb x0 x0) eqn:E2. 2:{ apply eqb_neq in E2. contradiction. }
          clear E2. destruct (String.eqb z0 x0) eqn:E2.
          ++ apply eqb_eq in E2. rewrite E2 in E1. contradiction.
          ++ rewrite x. reflexivity.
        -- contradiction.
        -- apply IHhas_type with (z0 := z0) (T0 := T0) (Q1 := Q1) (R := R).
          ++ assumption.
          ++ rewrite <- x. clear.
            apply context_inequality with (x := x1).
            unfold update. unfold t_update. destruct (String.eqb x1 x1) eqn:E1.
            ** unfold not. intros. inversion H. apply no_infinite_next with (T := A0). rewrite H1. reflexivity.
            ** apply eqb_neq in E1. contradiction.
          ++ reflexivity.
          ++ assumption.
        -- apply IHhas_type with (z0 := z0) (T0 := T0) (Q1 := Q1) (R := R).
          ++ assumption.
          ++ apply buggy_lemma1.
          ++ reflexivity.
          ++ assumption.
        -- apply IHhas_type with (z0 := z0) (T0 := T0) (Q1 := Q1) (R := R).
          ++ assumption.
          ++ rewrite <- x. clear.
            apply context_inequality with (x := x1).
            unfold update. unfold t_update. destruct (String.eqb x1 x1) eqn:E1.
            ** unfold not. intros. inversion H. apply no_infinite_next with (T := A0). assumption.
            ** apply eqb_neq in E1. contradiction.
          ++ reflexivity.
          ++ assumption.
        -- apply IHhas_type with (z0 := z0) (T0 := T0) (Q1 := Q1) (R := R).
          ++ assumption.
          ++ apply buggy_lemma1.
          ++ reflexivity.
          ++ assumption.
        -- apply IHhas_type with (z0 := z0) (T0 := T0) (Q1 := Q1) (R := R).
          ++ assumption.
          ++ apply buggy_lemma1.
          ++ generalize dependent H. clear. intros.
            dependent induction H.
            ** reflexivity.
            ** assert (y = <{x0.case(Q1, R)}>). { apply IHmulti. reflexivity. }
              subst. clear IHmulti H0. inversion H.
          ++ assumption.
      * rewrite merge_update_assoc. apply TSubBoxL. 2:{ assumption. }
        rewrite <- merge_update_assoc. apply IHhas_type with (x0 := x0) (R := R).
        -- reflexivity.
        -- assumption.
        -- assumption.
        -- generalize dependent H3. clear. intros.
          unfold not. intros. destruct H3.
          unfold has_comm in H. destruct H. destruct H. destruct H. destruct H.
          unfold has_comm. exists x0.
          unfold update in H. unfold t_update in H.
          unfold update. unfold t_update.
          destruct (String.eqb x x0) eqn:E1.
          ** exists A. exists x2. split. reflexivity. assumption.
          ** exists x1. exists x2. split. assumption. assumption.
        -- generalize dependent H4. clear.
          unfold update. unfold t_update. intros.
          destruct (String.eqb x z) eqn:E1. inversion H4. assumption.
      * apply IHhas_type with (x0 := x0) (R := R).
        -- reflexivity.
        -- apply TSubBoxL. assumption. assumption.
        -- assumption.
        -- assumption.
        -- assumption.
      * rewrite merge_update_assoc. apply TSubDiaL. 2:{ assumption. }
        rewrite <- merge_update_assoc. apply IHhas_type with (x0 := x0) (R := R).
        -- reflexivity.
        -- assumption.
        -- assumption.
        -- generalize dependent H3. clear. intros.
          unfold not. intros. destruct H3.
          unfold has_comm in H. destruct H. destruct H. destruct H. destruct H.
          unfold has_comm. exists x0.
          unfold update in H. unfold t_update in H.
          unfold update. unfold t_update.
          destruct (String.eqb x x0) eqn:E1.
          ** exists <{\Next A}>. exists x2. split. reflexivity. assumption.
          ** exists x1. exists x2. split. assumption. assumption.
        -- generalize dependent H4. clear.
          unfold update. unfold t_update. intros.
          destruct (String.eqb x z) eqn:E1. inversion H4. assumption.
      * apply IHhas_type with (x0 := x0) (R := R).
        -- reflexivity.
        -- apply TSubDiaL. assumption. assumption.
        -- assumption.
        -- assumption.
        -- assumption.
      * apply IHhas_type with (x0 := x0) (R := R).
        -- generalize dependent H0. clear. intros.
          dependent induction H0.
          ++ reflexivity.
          ++ assert (y = <{x0.inl; P0}>). { apply IHmulti. reflexivity. }
            subst. clear H0 IHmulti. inversion H.
        -- assumption.
        -- assumption.
        -- assumption.
        -- assumption.
    + subst. clear IHhas_type1 IHhas_type2 H4.
      dependent induction H0.
      * clear IHhas_type. dependent induction H.
        -- generalize dependent H4. clear. intros.
          unfold update in H4. unfold t_update in H4.
          destruct (String.eqb x0 x0) eqn:E1.
          ++ inversion H4.
          ++ apply eqb_neq in E1. contradiction.
        -- apply no_dup in H0.
          generalize dependent H0. clear. intros.
          unfold update in H0. unfold t_update in H0.
          destruct (String.eqb x0 x0) eqn:E1.
          ++ inversion H0.
          ++ apply eqb_neq in E1. contradiction.
        -- rewrite merge_update_assoc. apply TSubBoxL. 2:{ assumption. }
          rewrite <- merge_update_assoc. apply IHhas_type with (R := R).
          ++ assumption.
          ++ reflexivity.
          ++ assumption.
          ++ generalize dependent H3. clear. intros.
            unfold not. intros. destruct H3.
            unfold has_comm in H. destruct H. destruct H. destruct H. destruct H.
            unfold update in H. unfold t_update in H.
            unfold has_comm. exists x0. unfold update. unfold t_update.
            destruct (String.eqb x x0).
            ** exists A. exists x2. split. reflexivity. assumption.
            ** exists x1. exists x2. split. assumption. assumption.
          ++ generalize dependent H4. clear.
            unfold update. unfold t_update. intros.
            destruct (String.eqb x x0) eqn:E1. inversion H4. assumption.
        -- apply IHhas_type with (R := R).
          ++ apply TSubBoxL. assumption. assumption.
          ++ reflexivity.
          ++ assumption.
          ++ assumption.
          ++ assumption.
        -- rewrite merge_update_assoc. apply TSubDiaL. 2:{ assumption. }
          rewrite <- merge_update_assoc. apply IHhas_type with (R := R).
          ++ assumption.
          ++ reflexivity.
          ++ assumption.
          ++ generalize dependent H3. clear. intros.
            unfold not. intros. destruct H3.
            unfold has_comm in H. destruct H. destruct H. destruct H. destruct H.
            unfold update in H. unfold t_update in H.
            unfold has_comm. exists x0. unfold update. unfold t_update.
            destruct (String.eqb x x0).
            ** exists <{\Next A}>. exists x2. split. reflexivity. assumption.
            ** exists x1. exists x2. split. assumption. assumption.
          ++ generalize dependent H4. clear.
            unfold update. unfold t_update. intros.
            destruct (String.eqb x x0) eqn:E1. inversion H4. assumption.
        -- apply IHhas_type with (R := R).
          ++ apply TSubDiaL. assumption. assumption.
          ++ reflexivity.
          ++ assumption.
          ++ assumption.
          ++ assumption.
        -- apply IHhas_type with (R := R).
          ++ assumption.
          ++ generalize dependent H1. clear. intros.
            dependent induction H1.
            ** reflexivity.
            ** assert (y = <{x0.case(Q1, R)}>). { apply IHmulti. reflexivity. }
              subst. clear H1 IHmulti. inversion H.
          ++ assumption.
          ++ assumption.
          ++ assumption.
      * clear IHhas_type. dependent induction H.
        -- destruct H3. apply no_dup in H.
          generalize dependent H. generalize dependent x. clear. intros.
          unfold update in H. unfold t_update in H.
          destruct (String.eqb x0 z0) eqn:E1. inversion H. clear H.
          apply functional_equality with (x := x0) in x.


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
        -- apply H3.
        -- apply H0.
        -- apply H.
        -- reflexivity.
      * apply IHmulti.
        -- apply PTCong with (P := x).
           ++ apply H4.
           ++ apply multi_step with (y := y0). apply H. apply multi_refl.
        -- reflexivity.
        -- intros. apply IHnot_poised.
           ++ apply H5.
           ++ apply H6.
           ++ apply H7.
           ++ subst. clear A B y x0 P Q IHmulti H1 H4 IHnot_poised H3 H0 H2 H5 H6 H7.
               inversion H. subst. inversion H2.
        -- apply H3.
        -- apply H0.
        -- apply H2.
  - apply not_so_empty in x. contradiction.
  - dependent induction H0.
    + subst. apply type_uniqueness with (Omega := y |-> A) (x := x) (A := B) in H2.
      * destruct H2. destruct H3 with (z := x).
        unfold update in H4. unfold t_update in H4.
        destruct (String.eqb y x) eqn: E1.
        -- apply eqb_eq in E1. assert (x = y). { rewrite E1. reflexivity. }
           apply H0 in H6. contradiction.
        -- unfold empty in H4. unfold t_empty in H4.
           assert (@None CType = @None CType). { reflexivity. }
           apply H4 in H6. destruct (String.eqb x x) eqn: E2.
           ++ inversion H6.
           ++ apply eqb_neq in E2. assert (x = x). { reflexivity. } apply E2 in H7. contradiction.
      * apply H.
    + apply IHnot_poised.
      * apply H.
      * apply IHhas_type.
      * clear A B H0 IHnot_poised H IHhas_type.
        dependent induction H1.
        -- reflexivity.
        -- specialize IHmulti with (x := x) (y := y) (P := P).
           assert (y0 = <{ x (y); P }>). { apply IHmulti. reflexivity. }
           subst. clear H1 IHmulti. inversion H.
  - apply so_empty in x. destruct x. subst. clear H2 H1.
    inversion H3.
    + subst. *)

End TypeSafety.