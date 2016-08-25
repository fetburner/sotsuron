Require Import Arith List Omega Program.

Definition shift_var x c d :=
  (if lt_dec x c then x
  else d + x).

Lemma shift_var_0 : forall x c,
  shift_var x c 0 = x.
Proof.
  intros x c.
  unfold shift_var.
  destruct (lt_dec x c); auto.
Qed.

Lemma shift_var_meld : forall x c c' d d',
  c <= c' <= c + d ->
  shift_var (shift_var x c d) c' d' = shift_var x c (d + d').
Proof.
  intros x c c' d d' Hle.
  unfold shift_var.
  repeat match goal with
  | [ |- context [ lt_dec ?x ?c ] ] =>
      destruct (lt_dec x c)
  end; omega.
Qed.

Lemma shift_var_swap : forall x c c' d d',
  c' <= c ->
  shift_var (shift_var x c d) c' d' = shift_var (shift_var x c' d') (d' + c) d.
Proof.
  intros x c c' d d' Hle.
  unfold shift_var.
  repeat match goal with
  | [ |- context [ lt_dec ?x ?c ] ] =>
      destruct (lt_dec x c)
  end; omega.
Qed.

Module Exp.
  Inductive t :=
    | Var : nat -> t
    | Abs : t -> t
    | App : t -> t -> t.

  Fixpoint shift e c d :=
    match e with
    | Var x => Var (shift_var x c d)
    | Abs e => Abs (shift e (S c) d)
    | App e1 e2 => App (shift e1 c d) (shift e2 c d)
    end.

  Fixpoint subst e x es :=
    match e with
    | Var y =>
        if le_dec x y then shift (nth (y - x) es (Var (y - x - length es))) 0 x
        else Var y
    | Abs e => Abs (subst e (S x) es)
    | App e1 e2 => App (subst e1 x es) (subst e2 x es)
    end.

  Lemma shift_0 : forall e c,
    shift e c 0 = e.
  Proof.
    intros e.
    induction e; intros c; simpl; f_equal;
      try apply shift_var_0; eauto.
  Qed.

  Lemma shift_meld : forall e c c' d d',
    c <= c' <= c + d ->
    shift (shift e c d) c' d' = shift e c (d + d').
  Proof.
    intros e.
    induction e; intros c c' d d' Hle; simpl; f_equal;
      try (apply shift_var_meld; omega);
      match goal with
      | [ IH : forall _ _ _ _, _ -> shift (shift _ _ _) _ _ = shift _ _ _ |- _ ] =>
          apply IH
      end; omega.
  Qed.

  Lemma shift_swap : forall e c c' d d',
    c' <= c ->
    shift (shift e c d) c' d' = shift (shift e c' d') (d' + c) d.
  Proof.
    intros e.
    induction e; intros c c' d d' Hle; simpl; f_equal;
      try apply shift_var_swap;
      repeat match goal with
      | [ |- context [ S (?d + ?c) ] ] =>
          replace (S (d + c)) with (d + (S c)) by omega
      | [ IH : forall _ _ _ _, _ -> shift (shift _ _ _) _ _ = shift (shift _ _ _) _ _ |- _ ] =>
          apply IH
      end; omega.
  Qed.

  Lemma subst_shift : forall e c d x es,
    c <= x ->
    shift (subst e x es) c d = subst (shift e c d) (d + x) es.
  Proof.
    intros e.
    induction e; intros c d x es Hle; simpl; f_equal;
      repeat (simpl; unfold shift_var; match goal with
      | [ |- context [ le_dec ?x ?n ] ] =>
          destruct (le_dec x n)
      | [ |- context [ lt_dec ?x ?n ] ] =>
          destruct (lt_dec x n)
      end); eauto; try omega.

      rewrite shift_meld by omega.
      replace (d + n - (d + x)) with (n - x) by omega.
      replace (x + d) with (d + x) by omega.
      reflexivity.

      replace (S (d + x)) with (d + S x) by omega.
      apply IHe.
      omega.
  Qed.

  Lemma subst_ignore : forall e c d x es,
    c <= x ->
    length es + x <= d + c ->
    subst (shift e c d) x es = shift e c (d - length es).
  Proof.
    intros e.
    induction e; intros c d x es Hle Hlength; simpl; f_equal.
      unfold shift_var.
      repeat (try (rewrite nth_overflow by omega; simpl; unfold shift_var);
        match goal with
        | [ |- context [ lt_dec ?n ?c ] ] => destruct (lt_dec n c)
        | [ |- context [ le_dec ?n ?c ] ] => destruct (le_dec n c)
        end); f_equal; omega.

      apply IHe; omega.
      apply IHe1; omega.
      apply IHe2; omega.
  Qed.

  Inductive value : t -> Prop :=
    | V_Abs : forall e, value (Abs e).
  Hint Constructors value.

  Inductive evalto : t -> t -> Prop :=
    | E_Abs : forall t,
        evalto (Abs t) (Abs t)
    | E_App : forall t1 t2 t0 v2 v,
        evalto t1 (Abs t0) ->
        evalto t2 v2 ->
        evalto (subst t0 0 [v2]) v ->
        evalto (App t1 t2) v.
  Hint Constructors evalto.

  Lemma evalto_value : forall e v,
    evalto e v -> value v.
  Proof.
    intros e v Hevalto.
    induction Hevalto; auto.
  Qed.

  Lemma evalto_ident : forall v,
    value v -> evalto v v.
  Proof.
    intros v Hvalue.
    inversion Hvalue.
    constructor.
  Qed.

  CoInductive diverge : t -> Prop :=
    | D_AppL : forall t1 t2,
        diverge t1 ->
        diverge (App t1 t2)
    | D_AppR : forall t1 v1 t2,
        evalto t1 v1 ->
        diverge t2 ->
        diverge (App t1 t2)
    | D_App : forall t1 t2 t0 v2,
        evalto t1 (Abs t0) ->
        evalto t2 v2 ->
        diverge (subst t0 0 [v2]) ->
        diverge (Exp.App t1 t2).

  Fixpoint knormal e :=
    match e with
    | Var x => Var x
    | Abs e => Abs (knormal e)
    | App e1 e2 =>
        App
          (Abs
            (App
              (Abs
                (App (Var 1) (Var 0)))
              (shift (knormal e2) 0 1)))
          (knormal e1)
    end.

  Lemma knormal_preserve_value : forall v,
    value v -> value (knormal v).
  Proof.
    intros v Hvalue.
    inversion Hvalue.
    simpl.
    constructor.
  Qed.

  Lemma knormal_shift : forall e c d,
    knormal (shift e c d) = shift (knormal e) c d.
  Proof.
    intros e.
    induction e; simpl; intros c d; f_equal; auto.
      f_equal.
      f_equal.
      rewrite IHe2. rewrite shift_swap by omega. reflexivity.
  Qed.

  Lemma knormal_subst : forall e x es,
    knormal (subst e x es) = subst (knormal e) x (map knormal es).
  Proof.
    intros e.
    induction e; intros x es; simpl; f_equal; eauto.
      destruct (le_dec x n); auto.
      rewrite knormal_shift.
      f_equal.
      replace (Var (n - x - length (map knormal es))) with
        (knormal (Var (n - x - length (map knormal es)))) by reflexivity.
      rewrite map_nth.
      rewrite map_length.
      reflexivity.

      f_equal.
      f_equal.
      rewrite IHe2.

      eauto.
      rewrite subst_shift by omega.
      reflexivity.
  Qed.

  Theorem knormal_correctness : forall e v,
    evalto e v -> evalto (knormal e) (knormal v).
  Proof.
    intros e v.
    intros Hevalto.
    induction Hevalto; simpl.
      auto.

      econstructor.
        constructor.
        eassumption.
        simpl. econstructor.
          constructor.
          rewrite subst_ignore by (simpl; omega). simpl. rewrite shift_0. eassumption.
          simpl. econstructor.
            rewrite subst_ignore by (simpl; omega). simpl. rewrite shift_0. constructor.
            rewrite shift_0. apply evalto_ident. apply knormal_preserve_value. eapply evalto_value. eauto.
            rewrite knormal_subst in IHHevalto3. apply IHHevalto3.
  Qed.
End Exp.