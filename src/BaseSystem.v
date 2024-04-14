Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
Open Scope string_scope.
From Coq Require Import Program.Equality.
From MySystem Require Import Smallstep.
From MySystem Require Import Maps.
From Coq Require Import Lists.List. Import ListNotations.

(* Channel Types *)
Inductive CType : Type :=
  | Unit : CType
  | Tensor : CType -> CType -> CType
  | Lolli : CType -> CType -> CType
  | Plus : CType -> CType -> CType
  | With : CType -> CType -> CType
  | Next : CType -> CType
  | Box : CType -> CType
  | Diamond : CType -> CType.

(* Processes *)
Inductive Proc : Type :=
  | Comp : Proc -> Proc -> Proc
  | Send : string -> string -> Proc -> Proc
  | Recv : string -> string -> Proc -> Proc
  | Inl : string -> Proc -> Proc
  | Inr : string -> Proc -> Proc
  | Case : string -> Proc -> Proc -> Proc
  | Wait : string -> Proc -> Proc
  | Close : string -> Proc
  | When : string -> Proc -> Proc
  | Now : string -> Proc -> Proc
  | Delay : Proc -> Proc.

Fixpoint Multi_delay (n: nat) (P: Proc) : Proc :=
  match n with
  | 0 => P
  | S n' => Delay (Multi_delay n' P)
  end.

Declare Custom Entry baseSystem.
Notation "<{ e }>" := e (e custom baseSystem at level 99).
Notation "( x )" := x (in custom baseSystem, x at level 99).
Notation "x" := x (in custom baseSystem at level 0, x constr at level 0).
Notation "'1'" := Unit (in custom baseSystem at level 0).
Notation "A * B" := (Tensor A B) (in custom baseSystem at level 50, right associativity).
Notation "A -o B" := (Lolli A B) (in custom baseSystem at level 50, right associativity).
Notation "A + B" := (Plus A B) (in custom baseSystem at level 50, right associativity).
Notation "A & B" := (With A B) (in custom baseSystem at level 50, right associativity).
Notation "\Next A" := (Next A) (in custom baseSystem at level 49, right associativity).
Notation "\Box A" := (Box A) (in custom baseSystem at level 49, right associativity).
Notation "\Dia A" := (Diamond A) (in custom baseSystem at level 49, right associativity).

Example test_CType : CType := <{\Box (\Next 1 & (\Dia 1 -o 1))}>.

Theorem no_infinite_next: forall (T: CType),
  ~(T = <{\Next T}>).
Proof. intros. unfold not. intros. dependent induction T.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H.
  - apply IHT. inversion H. assumption.
  - inversion H.
  - inversion H.
Qed.

Notation "P | Q" := (Comp P Q) (in custom baseSystem at level 90, right associativity).
Notation "x < y > ; P" := (Send x y P) (in custom baseSystem at level 80,
                                        right associativity).
Notation "x ( y ) ; P" := (Recv x y P) (in custom baseSystem at level 80,
                                        right associativity).
Notation "x '.inl;' P" := (Inl x P) (in custom baseSystem at level 80,
                                      right associativity).
Notation "x '.inr;' P" := (Inr x P) (in custom baseSystem at level 80,
                                      right associativity).
Notation "x '.case' ( P , Q )" := (Case x P Q) (in custom baseSystem at level 89,
                                      right associativity).
Notation "'C' [ x ]" := (Close x) (in custom baseSystem at level 80,
                                    right associativity).
Notation "'W' [ x ] ; P" := (Wait x P) (in custom baseSystem at level 80,
                                    right associativity).
Notation "? [ x ] ; P" := (When x P) (in custom baseSystem at level 80,
                                    right associativity).
Notation "! [ x ] ; P" := (Now x P) (in custom baseSystem at level 80,
                                    right associativity).
Notation "'D;' P" := (Delay P) (in custom baseSystem at level 80,
                                    right associativity).
Notation "'D{' n '};' P" := (Multi_delay n P) (in custom baseSystem at level 80,
                                    right associativity).

Definition w : string := "w".
Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold w : core.
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.

Example test_Proc := <{(C[z] | (x(w); W[w]; C[x] | x<z>; W[x]; C[y]))}>.

(* Free: free variables *)
(* Inductive Free : string -> Proc -> Prop :=
  | FCompL : forall (x : string) (P Q : Proc), Free x P -> Free x <{P | Q}>
  | FCompR : forall (x : string) (P Q : Proc), Free x Q -> Free x <{P | Q}>
  | FNew : forall (x y : string) (P : Proc), Free x P -> x <> y -> Free x <{\y, P}>
  | FSendM : forall (x y : string) (P : Proc), Free x <{y<x>; P}>
  | FSendC : forall (x z : string) (P : Proc), Free x <{x<z>; P}>
  | FSendP : forall (x y z : string) (P : Proc), Free x P -> Free x <{y<z>; P}>
  | FRecvC : forall (x z : string) (P : Proc), Free x <{x(z); P}>
  | FRecvP : forall (x y z : string) (P : Proc), Free x P -> x <> z -> Free x <{y(z); P}>
  | FInlC : forall (x : string) (P : Proc), Free x <{x.inl; P}>
  | FInlP : forall (x y : string) (P : Proc), Free x P -> Free x <{y.inl; P}>
  | FInrC : forall (x : string) (P : Proc), Free x <{x.inr; P}>
  | FInrP : forall (x y : string) (P : Proc), Free x P -> Free x <{y.inr; P}>
  | FCaseC : forall (x : string) (P Q: Proc), Free x <{x.case(P, Q)}>
  | FCaseL : forall (x y : string) (P Q: Proc), Free x P -> Free x <{y.case(P, Q)}>
  | FCaseR : forall (x y : string) (P Q: Proc), Free x Q -> Free x <{y.case(P, Q)}>
  | FWaitC : forall (x : string) (P: Proc), Free x <{W[x]; P}>
  | FWaitP : forall (x y : string) (P: Proc), Free x P -> Free x <{W[y]; P}>
  | FClose : forall (x : string), Free x <{C[x]}>
  | FWhenC : forall (x : string) (P: Proc), Free x <{?[x]; P}>
  | FWhenP : forall (x y : string) (P: Proc), Free x P -> Free x <{?[y]; P}>
  | FNowC : forall (x : string) (P: Proc), Free x <{![x]; P}>
  | FNowP : forall (x y : string) (P: Proc), Free x P -> Free x <{![y]; P}>
  | FDelay : forall (x : string) (P: Proc), Free x P -> Free x <{D; P}>. *)

(* Exist: existing variables, useful when checking congruency *)
Inductive Exist : string -> Proc -> Prop :=
  | ECompL : forall (x : string) (P Q : Proc), Exist x P -> Exist x <{P | Q}>
  | ECompR : forall (x : string) (P Q : Proc), Exist x Q -> Exist x <{P | Q}>
  | ESendM : forall (x y : string) (P : Proc), Exist x <{y<x>; P}>
  | ESendC : forall (x z : string) (P : Proc), Exist x <{x<z>; P}>
  | ESendP : forall (x y z : string) (P : Proc), Exist x P -> Exist x <{y<z>; P}>
  | ERecvM : forall (x y : string) (P : Proc), Exist x <{y(x); P}>
  | ERecvC : forall (x z : string) (P : Proc), Exist x <{x(z); P}>
  | ERecvP : forall (x y z : string) (P : Proc), Exist x P -> Exist x <{y(z); P}>
  | EInlC : forall (x : string) (P : Proc), Exist x <{x.inl; P}>
  | EInlP : forall (x y : string) (P : Proc), Exist x P -> Exist x <{y.inl; P}>
  | EInrC : forall (x : string) (P : Proc), Exist x <{x.inr; P}>
  | EInrP : forall (x y : string) (P : Proc), Exist x P -> Exist x <{y.inr; P}>
  | ECaseC : forall (x : string) (P Q: Proc), Exist x <{x.case(P, Q)}>
  | ECaseL : forall (x y : string) (P Q: Proc), Exist x P -> Exist x <{y.case(P, Q)}>
  | ECaseR : forall (x y : string) (P Q: Proc), Exist x Q -> Exist x <{y.case(P, Q)}>
  | EWaitC : forall (x : string) (P: Proc), Exist x <{W[x]; P}>
  | EWaitP : forall (x y : string) (P: Proc), Exist x P -> Exist x <{W[y]; P}>
  | EClose : forall (x : string), Exist x <{C[x]}>
  | EWhenC : forall (x : string) (P: Proc), Exist x <{?[x]; P}>
  | EWhenP : forall (x y : string) (P: Proc), Exist x P -> Exist x <{?[y]; P}>
  | ENowC : forall (x : string) (P: Proc), Exist x <{![x]; P}>
  | ENowP : forall (x y : string) (P: Proc), Exist x P -> Exist x <{![y]; P}>
  | EDelay : forall (P: Proc), Exist x P -> Exist x <{D; P}>.

Reserved Notation "'[' x ':=' s ']' P" (in custom baseSystem at level 20, right associativity, x constr).
(* Rename function *)
Fixpoint subst (x : string) (s : string) (P : Proc) : Proc :=
  match P with
  | <{Q | R}> => <{[x:=s] Q | [x:=s] R}>
  | <{y<z>; Q}> =>
      if String.eqb x y then (if String.eqb x z then <{s<s>; [x:=s] Q}> else <{s<z>; [x:=s] Q}>)
      else (if String.eqb x z then <{y<s>; [x:=s] Q}> else <{y<z>; [x:=s] Q}>)
  | <{y(z); Q}> =>
      if String.eqb x y then (if String.eqb x z then <{s(z); Q}> else <{s(z); [x:=s] Q}>)
      else (if String.eqb x z then <{y(s); [x:=s] Q}> else <{y(z); [x:=s] Q}>)
  | <{y.inl; Q}> => if String.eqb x y then <{s.inl; [x:=s] Q}> else <{y.inl; [x:=s] Q}>
  | <{y.inr; Q}> => if String.eqb x y then <{s.inr; [x:=s] Q}> else <{y.inr; [x:=s] Q}>
  | <{y.case( Q, R )}> => if String.eqb x y then <{s.case( [x:=s]Q, [x:=s]R )}> else <{y.case( [x:=s]Q, [x:=s]R )}>
  | <{W[y]; Q}> => if String.eqb x y then <{W[s]; [x:=s]Q}> else <{W[y]; [x:=s]Q}>
  | <{C[y]}> => if String.eqb x y then <{C[s]}> else <{C[y]}>
  | <{?[y]; Q}> => if String.eqb x y then <{?[s]; [x:=s]Q}> else <{?[y]; [x:=s]Q}>
  | <{![y]; Q}> => if String.eqb x y then <{![s]; [x:=s]Q}> else <{![y]; [x:=s]Q}>
  | <{D; Q}> => <{D; [x:=s]Q}>
  end
where "'[' x ':=' s ']' P" := (subst x s P) (in custom baseSystem).

Reserved Notation "P ≡' Q" (at level 99).
Inductive Congruence' : Proc -> Proc -> Prop :=
  | SComp : forall (P Q: Proc), <{P | Q}> ≡' <{Q | P}>
  | SAssoc : forall (P Q R: Proc), <{(P | Q) | R}> ≡' <{P | (Q | R)}>
  | SAssoc' : forall (P Q R: Proc), <{P | (Q | R)}> ≡' <{(P | Q) | R}>
  | SDelay : forall (P Q: Proc), <{D; (P | Q)}> ≡' <{(D; P) | (D; Q)}>
  | SDelay' : forall (P Q: Proc), <{(D; P) | (D; Q)}> ≡' <{D; (P | Q)}>
where "P ≡' Q" := (Congruence' P Q).

Theorem SSwap : forall (P Q: Proc), P ≡' Q -> Q ≡' P.
Proof.
  intros.
  induction H.
  - apply SComp.
  - apply SAssoc'.
  - apply SAssoc.
  - apply SDelay'.
  - apply SDelay.
Qed.

Notation Congruence := (multi Congruence').
Notation "P ≡ Q" := (Congruence P Q) (at level 99).

Definition has_comm {A: Type} (M1 M2: partial_map A): Prop :=
  exists (x: string) (a b: A), M1 x = Some a /\ M2 x = Some b.

Definition merge {A: Type} (M1 M2: partial_map A): partial_map A :=
  fun x => match M1 x with
    | Some a => Some a
    | None => M2 x
  end.
Notation "M1 ; M2" := (merge M1 M2) (at level 100).

Definition context := partial_map CType.

Definition _Next (Omega: context): context :=
  fun x => match Omega x with
    | Some T => Some (Next T)
    | None => None
  end.

Inductive delayed_box' : CType -> Prop :=
  | DBBase: forall (A: CType), delayed_box' <{\Box A}>
  | DBInd: forall (A: CType), delayed_box' A -> delayed_box' <{\Next A}>.

Definition delayed_box (Omega: context): Prop :=
  forall (x: string) (A: CType),
    Omega x = Some A -> delayed_box' A.

Inductive delayed_dia' : CType -> Prop :=
  | DDBase: forall (A: CType), delayed_dia' <{\Dia A}>
  | DDInd: forall (A: CType), delayed_dia' A -> delayed_dia' <{\Next A}>.

Definition delayed_dia (Omega: context): Prop :=
  forall (x: string) (A: CType),
    Omega x = Some A -> delayed_dia' A.

(* Rename context *)
Definition subst_context (x : string) (y : string) (Gamma : context) : context :=
  fun x' => if (String.eqb x' y) then Gamma x else Gamma x'.
Notation "'[' x '::=' y ']' Gamma" := (subst_context x y Gamma) (at level 20, right associativity, x constr).

Reserved Notation "Omega '|--' P '::' x '\in' T"
            (at level 101, P custom baseSystem, T custom baseSystem at level 0).
Inductive has_type : context -> Proc -> string -> CType -> Prop :=
  | T1L : forall (Omega: context) (P: Proc) (x y: string) (T: CType),
      Omega |-- P :: x \in T -> x <> y ->
      y |-> <{1}>; Omega |-- <{W[y]; P}> :: x \in T
  | T1R : forall (x: string),
      empty |-- <{C[x]}> :: x \in 1
  | TOtimesL : forall (Omega: context) (P: Proc) (x y z: string) (A B T: CType),
      y |-> A; x |-> B; Omega |-- P :: z \in T -> x <> y -> Omega y = None ->
      x |-> <{A * B}>; Omega |-- <{x(y); P}> :: z \in T
  | TOtimesR : forall (Omega Omega': context) (P Q: Proc) (x y: string) (A B: CType),
      Omega |-- P :: y \in A ->
      Omega' |-- Q :: x \in B ->
      ~has_comm Omega Omega' ->
      Omega x = None -> Omega' y = None -> x <> y ->
      Omega; Omega' |-- <{x<y>; (P | Q)}> :: x \in <{A * B}>
  | TLolliL : forall (Omega Omega': context) (P Q: Proc) (x y z: string) (A B T: CType),
      Omega |-- P :: y \in A ->
      x |-> B; Omega' |-- Q :: z \in T -> Omega' x = None ->
      ~has_comm Omega Omega' ->
      Omega' y = None -> Omega z = None -> Omega x = None ->
      x <> y -> z <> y ->
      x |-> <{A -o B}>; Omega; Omega' |-- <{x<y>; (P | Q)}> :: z \in T
  | TLolliR : forall (Omega: context) (P: Proc) (x y: string) (A B: CType),
      y |-> A; Omega |-- P :: x \in B -> Omega y = None ->
      Omega |-- <{x(y); P}> :: x \in <{A -o B}>
  | TCut : forall (Omega Omega': context) (P Q: Proc) (x z: string) (A T: CType),
      Omega |-- P :: x \in A ->
      x |-> A; Omega' |-- Q :: z \in T -> Omega' x = None ->
      ~has_comm Omega Omega' ->
      Omega z = None ->
      Omega; Omega' |-- <{P | Q}> :: z \in T
  (* TCut', TCopy, T!L, T!R *)
  | TOplusL : forall (Omega: context) (P Q: Proc) (x z: string) (A B T: CType),
      x |-> A; Omega |-- P :: z \in T ->
      x |-> B; Omega |-- Q :: z \in T ->
      x |-> <{A + B}>; Omega |-- <{x.case(P, Q)}> :: z \in T
  | TOplusR1 : forall (Omega: context) (P: Proc) (x: string) (A B: CType),
      Omega |-- P :: x \in A ->
      Omega |-- <{x.inl; P}> :: x \in <{A + B}>
  | TOplusR2 : forall (Omega: context) (P: Proc) (x: string) (A B: CType),
      Omega |-- P :: x \in B ->
      Omega |-- <{x.inr; P}> :: x \in <{A + B}>
  | TWithL1 : forall (Omega: context) (P: Proc) (x z: string) (A B T: CType),
      x |-> A; Omega |-- P :: z \in T ->
      x |-> <{A & B}>; Omega |-- <{x.inl; P}> :: z \in T
  | TWithL2 : forall (Omega: context) (P: Proc) (x z: string) (A B T: CType),
      x |-> B; Omega |-- P :: z \in T ->
      x |-> <{A & B}>; Omega |-- <{x.inr; P}> :: z \in T
  | TWithR : forall (Omega: context) (P Q: Proc) (x: string) (A B: CType),
      Omega |-- P :: x \in A ->
      Omega |-- Q :: x \in B ->
      Omega |-- <{x.case(P, Q)}> :: x \in <{A & B}>
  | TDelay : forall (Omega: context) (P: Proc) (z: string) (T: CType),
      Omega |-- P :: z \in T ->
      _Next Omega |-- <{D; P}> :: z \in <{\Next T}>
  | TBoxL : forall (Omega: context) (P: Proc) (x z: string) (A T: CType),
      x |-> A; Omega |-- P :: z \in T ->
      x |-> <{\Box A}>; Omega |-- <{![x]; P}> :: z \in T
  | TBoxR : forall (Omega: context) (P: Proc) (x: string) (A: CType),
      Omega |-- P :: x \in A ->
      delayed_box Omega ->
      Omega |-- <{?[x]; P}> :: x \in <{\Box A}>
  | TDiaL : forall (Omega: context) (P: Proc) (x z: string) (A T: CType),
      x |-> A; Omega |-- P :: z \in T ->
      delayed_box Omega ->
      delayed_dia' T ->
      x |-> <{\Dia A}>; Omega |-- <{?[x]; P}> :: z \in T
  | TDiaR : forall (Omega: context) (P: Proc) (x: string) (A: CType),
      Omega |-- P :: x \in A ->
      Omega |-- <{![x]; P}> :: x \in <{\Dia A}>
  | TSubBoxL : forall (Omega: context) (P: Proc) (x z: string) (A T: CType),
      x |-> <{\Next A}>; Omega |-- P :: z \in T ->
      delayed_box' A ->
      x |-> A; Omega |-- P :: z \in T
  | TSubBoxR : forall (Omega: context) (P: Proc) (x: string) (A: CType),
      Omega |-- P :: x \in A ->
      delayed_box' A ->
      Omega |-- P :: x \in <{\Next A}>
  | TSubDiaL : forall (Omega: context) (P: Proc) (x z: string) (A T: CType),
      x |-> A; Omega |-- P :: z \in T ->
      delayed_dia' A ->
      x |-> <{\Next A}>; Omega |-- P :: z \in T
  | TSubDiaR : forall (Omega: context) (P: Proc) (x: string) (A: CType),
      Omega |-- P :: x \in <{\Next A}> ->
      delayed_dia' A ->
      Omega |-- P :: x \in A
  | TCong : forall (Omega: context) (P Q: Proc) (z: string) (T: CType),
      Omega |-- P :: z \in T -> P ≡ Q ->
      Omega |-- Q :: z \in T
where "Omega '|--' P '::' x '\in' T" := (has_type Omega P x T).

Theorem type_uniqueness: forall (Omega Omega': context) (P: Proc) (x y: string) (A B: CType),
  Omega |-- P :: x \in A -> Omega' |-- P :: y \in B ->
  x = y /\ forall (z: string), Omega z = None <-> Omega' z = None.
Proof.
  intros.
  split.
  - generalize dependent H0.
    generalize dependent B.
    generalize dependent y0.
    generalize dependent Omega'.
    induction H.
    + intros. dependent induction H1.
      * apply IHhas_type in H1. apply H1.
      * apply IHhas_type0 with (P := P) (y0 := y0).
        ** apply H.
        ** apply H0.
        ** apply IHhas_type.
        ** reflexivity.
      * apply IHhas_type0 with (P := P) (y0 := y0).
        ** apply H.
        ** apply H0.
        ** apply IHhas_type.
        ** reflexivity.
      * apply IHhas_type0 with (P := P) (y0 := y0).
        ** apply H.
        ** apply H0.
        ** apply IHhas_type.
        ** reflexivity.
      * apply IHhas_type0 with (P := P) (y0 := y0).
        ** apply H.
        ** apply H0.
        ** apply IHhas_type.
        ** reflexivity.
      * apply IHhas_type0 with (P := P) (y0 := y0).
        ** apply H.
        ** apply H0.
        ** apply IHhas_type.
        ** clear Omega x0 T Omega0 z0 T0 H1 H H0 IHhas_type0 IHhas_type.
           dependent induction H2.
           *** reflexivity.
           *** specialize IHmulti with (P := P) (y0 := y0).
               assert (y1 = <{ W [y0]; P }>). { apply IHmulti. reflexivity. }
               subst. clear IHmulti H2. inversion H.
    + intros. dependent induction H0.
      * reflexivity.
      * apply IHhas_type. reflexivity.
      * apply IHhas_type. reflexivity.
      * apply IHhas_type. reflexivity.
      * apply IHhas_type. reflexivity.
      * apply IHhas_type. clear Omega z0 T H0 IHhas_type.
        dependent induction H.
        ** reflexivity.
        ** specialize IHmulti with (x0 := x0).
           assert (y0 = <{C[x0]}>). { apply IHmulti. reflexivity. }
           subst. clear IHmulti H0. inversion H.
    + intros. dependent induction H2.
      * apply IHhas_type in H2. apply H2.
      * apply IHhas_type in H2. apply H2.
      * apply IHhas_type0 with (y0 := y0) (x0 := x0) (P := P).
        ** apply H1.
        ** apply H0.
        ** apply H.
        ** apply IHhas_type.
        ** reflexivity.
      * apply IHhas_type0 with (y0 := y0) (x0 := x0) (P := P).
        ** apply H1.
        ** apply H0.
        ** apply H.
        ** apply IHhas_type.
        ** reflexivity.
      * apply IHhas_type0 with (y0 := y0) (x0 := x0) (P := P).
        ** apply H1.
        ** apply H0.
        ** apply H.
        ** apply IHhas_type.
        ** reflexivity.
      * apply IHhas_type0 with (y0 := y0) (x0 := x0) (P := P).
        ** apply H1.
        ** apply H0.
        ** apply H.
        ** apply IHhas_type.
        ** reflexivity.
      * apply IHhas_type0 with (y0 := y0) (x0 := x0) (P := P).
        ** apply H1.
        ** apply H0.
        ** apply H.
        ** apply IHhas_type.
        ** Admitted.

Theorem rename_type_context : forall (Omega: context) (P: Proc) (x y z: string) (T: CType),
  Omega |-- P :: z \in T -> x <> z ->
  [x ::= y] Omega |-- [x := y] P :: z \in T.
Proof. Admitted.

Theorem rename_type_service : forall (Omega: context) (P: Proc) (x y: string) (T: CType),
  Omega |-- P :: x \in T ->
  Omega |-- [x := y] P :: y \in T.
Proof. Admitted.

Theorem rename_not_exist : forall (Omega: context) (P: Proc) (x y z: string) (T: CType),
  Omega |-- [x := y]P :: z \in T ->
  Omega x = None.
Proof. Admitted.

Theorem not_exist : forall (Omega: context) (P: Proc) (x z: string) (T: CType),
  Omega |-- P :: z \in T -> ~Exist x P -> x <> z /\ Omega x = None.
Proof. Admitted.

Theorem no_dup : forall (Omega: context) (P: Proc) (x: string) (A: CType),
  Omega |-- P :: x \in A ->
  Omega x = None.
Proof.
  intros.
  induction H.
  - unfold update. unfold t_update.
    destruct (String.eqb y0 x0) eqn:E1.
    + apply eqb_eq in E1. rewrite E1 in H0. unfold not in H0. assert (x0 = x0). { reflexivity. } apply H0 in H1. inversion H1.
    + apply IHhas_type.
  - unfold empty. unfold t_empty. reflexivity.
  - unfold update. unfold t_update.
    unfold update in IHhas_type. unfold t_update in IHhas_type.
    destruct (String.eqb y0 z0) eqn:E1.
    + inversion IHhas_type.
    + destruct (String.eqb x0 z0) eqn:E2.
      * inversion IHhas_type.
      * apply IHhas_type.
  - unfold merge. rewrite H2. apply IHhas_type2.
  - unfold update. unfold t_update.
    unfold update in IHhas_type2. unfold t_update in IHhas_type2.
    destruct (String.eqb x0 z0) eqn:E1.
    + inversion IHhas_type2.
    + unfold merge. rewrite H4. apply IHhas_type2.
  - unfold update in IHhas_type. unfold t_update in IHhas_type.
    destruct (String.eqb y0 x0) eqn:E1.
    + inversion IHhas_type.
    + apply IHhas_type.
  - unfold update in IHhas_type2. unfold t_update in IHhas_type2.
    destruct (String.eqb x0 z0) eqn:E1.
    + inversion IHhas_type2.
    + unfold merge. rewrite H3. apply IHhas_type2.
  - unfold update. unfold t_update.
    unfold update in IHhas_type1. unfold t_update in IHhas_type1.
    destruct (String.eqb x0 z0) eqn:E1.
    + inversion IHhas_type1.
    + apply IHhas_type1.
  - apply IHhas_type.
  - apply IHhas_type.
  - unfold update. unfold t_update.
    unfold update in IHhas_type. unfold t_update in IHhas_type.
    destruct (String.eqb x0 z0) eqn:E1.
    + inversion IHhas_type.
    + apply IHhas_type.
  - unfold update. unfold t_update.
    unfold update in IHhas_type. unfold t_update in IHhas_type.
    destruct (String.eqb x0 z0) eqn:E1.
    + inversion IHhas_type.
    + apply IHhas_type.
  - apply IHhas_type2.
  - unfold _Next. rewrite IHhas_type. reflexivity.
  - unfold update. unfold t_update.
    unfold update in IHhas_type. unfold t_update in IHhas_type.
    destruct (String.eqb x0 z0) eqn:E1.
    + inversion IHhas_type.
    + apply IHhas_type.
  - apply IHhas_type.
  - unfold update. unfold t_update.
    unfold update in IHhas_type. unfold t_update in IHhas_type.
    destruct (String.eqb x0 z0) eqn:E1.
    + inversion IHhas_type.
    + apply IHhas_type.
  - apply IHhas_type.
  - unfold update. unfold t_update.
    unfold update in IHhas_type. unfold t_update in IHhas_type.
    destruct (String.eqb x0 z0) eqn:E1.
    + inversion IHhas_type.
    + apply IHhas_type.
  - apply IHhas_type.
  - unfold update. unfold t_update.
    unfold update in IHhas_type. unfold t_update in IHhas_type.
    destruct (String.eqb x0 z0) eqn:E1.
    + inversion IHhas_type.
    + apply IHhas_type.
  - apply IHhas_type.
  - apply IHhas_type.
Qed.

Reserved Notation "P '-->' P'" (at level 40).
Inductive reduction : Proc -> Proc -> Prop :=
  | RSend : forall (x y z: string) (P Q: Proc),
      ~Exist y P -> <{x<y>; Q | x(z); P}> --> <{Q | [z := y]P}>
  | RInL1 : forall (x: string) (P Q R: Proc),
      <{x.inl; P | x.case( Q, R )}> --> <{P | Q}>
  | RInL2 : forall (x: string) (P Q R: Proc),
      <{x.case( Q, R ) | x.inl; P}> --> <{Q | P}>
  | RInR1 : forall (x: string) (P Q R: Proc),
      <{x.inr; P | x.case( Q, R )}> --> <{P | R}>
  | RInR2 : forall (x: string) (P Q R: Proc),
      <{x.case( Q, R ) | x.inr; P}> --> <{R | P}>
  | RComp1 : forall (P P' Q: Proc),
      P --> P' -> <{P | Q}> --> <{P' | Q}>
  | RComp2 : forall (P Q Q': Proc),
      Q --> Q' -> <{P | Q}> --> <{P | Q'}>
  | RClose : forall (x: string) (P: Proc),
      <{C[x] | W[x]; P}> --> P
  | RCong : forall (P Q P' Q': Proc),
      P ≡ P' -> P' --> Q' -> Q' ≡ Q -> P --> Q
  | RDelay : forall (P Q: Proc),
      P --> Q -> <{D; P}> --> <{D; Q}>
  | RWhen : forall (x: string) (n: nat) (P Q: Proc),
      <{?[x]; P | D{n}; ![x]; Q}> --> <{D{n}; P | D{n}; Q}>
where "P '-->' P'" := (reduction P P').

Theorem RRecv : forall (x y z: string) (P Q: Proc),
  ~Exist y P -> <{x(z); P | x<y>; Q}> --> <{[z := y]P | Q}>.
Proof.
  intros.
  apply RCong with (P' := <{x0<y0>; Q | x0(z0); P}>) (Q' := <{Q | [z0 := y0]P}>).
  - apply multi_step with (y := <{x0<y0>; Q | x0(z0); P}>).
    + apply SComp.
    + apply multi_refl.
  - apply RSend. assumption.
  - apply multi_step with (y := <{[z0 := y0]P | Q}>).
    + apply SComp.
    + apply multi_refl.
Qed.

Theorem RNow : forall (x: string) (n: nat) (P Q: Proc),
  <{D{n}; ![x]; Q | ?[x]; P}> --> <{D{n}; Q | D{n}; P}>.
Proof.
  intros.
  apply RCong with (P' := <{?[x0]; P | D{n}; ![x0]; Q}>) (Q' := <{D{n}; P | D{n}; Q}>).
  - apply multi_step with (y := <{?[x0]; P | D{n}; ![x0]; Q}>).
    + apply SComp.
    + apply multi_refl.
  - apply RWhen.
  - apply multi_step with (y := <{D{n}; Q | D{n}; P}>).
    + apply SComp.
    + apply multi_refl.
Qed.
(* z:1 |-- \x, (x<z>; close x | x(y); wait x; wait y; close y') :: y':1
z:1 |-- \x, ( close x |  wait x; wait z; close y') :: y':1
z:1 |-- wait z; close y' :: y':1
|-- \z, (close z | \x, (x(w); wait w; close x | x<z>; wait x; close y)) :: y:1
z:1 |-- \x, ( wait z; close x | wait x; close y) :: y:1 *)

Notation multistep := (multi reduction).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Theorem example4 : test_Proc -->* <{C[y]}>.
Proof.
  apply multi_step with (y := <{C[z] | (W[z]; C[x] | W[x]; C[y])}>).
  - apply RComp2. apply RRecv. unfold not. intros.
    inversion H. subst. inversion H2.
  - apply multi_step with (y := <{ C[x] | W[x]; C[y]}>).
    + apply RCong with (P' := <{(C[z] | W[z]; C[x]) | W[x]; C[y]}>)
                       (Q' := <{C[x] | W[x]; C[y]}>).
      * apply multi_step with (y := <{(C[z] | W[z]; C[x]) | W[x]; C[y]}>).
        ** apply SAssoc'.
        ** apply multi_refl.
      * apply RComp1. apply RClose.
      * apply multi_refl.
    + apply multi_step with (y := <{C[y]}>).
      * apply RClose.
      * apply multi_refl.
Qed.
