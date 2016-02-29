Require Import Arith ZArith Reals List Omega Program.

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
    | Unit : t
    | Bool : bool -> t
    | Int : Z -> t
    | Float : R -> t
    | Not : t -> t
    | Neg : t -> t
    | Add : t -> t -> t
    | Sub : t -> t -> t
    | FNeg : t -> t
    | FAdd : t -> t -> t
    | FSub : t -> t -> t
    | FMul : t -> t -> t
    | FDiv : t -> t -> t
    | Eq : t -> t -> t
    | LE : t -> t -> t
    | If : t -> t -> t -> t
    | Let : t -> t -> t
    | Var : nat -> t
    | Abs : t -> t
    | App : t -> t -> t.

  Fixpoint shift e c d :=
    match e with
    | Unit => Unit
    | Bool b => Bool b
    | Int n => Int n
    | Float r => Float r
    | Not e => Not (shift e c d)
    | Neg e => Neg (shift e c d)
    | Add e1 e2 => Add (shift e1 c d) (shift e2 c d)
    | Sub e1 e2 => Sub (shift e1 c d) (shift e2 c d)
    | FNeg e => FNeg (shift e c d)
    | FAdd e1 e2 => FAdd (shift e1 c d) (shift e2 c d)
    | FSub e1 e2 => FSub (shift e1 c d) (shift e2 c d)
    | FMul e1 e2 => FMul (shift e1 c d) (shift e2 c d)
    | FDiv e1 e2 => FDiv (shift e1 c d) (shift e2 c d)
    | Eq e1 e2 => Eq (shift e1 c d) (shift e2 c d)
    | LE e1 e2 => LE (shift e1 c d) (shift e2 c d)
    | If e1 e2 e3 => If (shift e1 c d) (shift e2 c d) (shift e3 c d)
    | Let e1 e2 => Let (shift e1 c d) (shift e2 (S c) d)
    | Abs e => Abs (shift e (S c) d)
    | Var x => Var (shift_var x c d)
    | App e1 e2 => App (shift e1 c d) (shift e2 c d)
    end.

  Fixpoint subst e x es :=
    match e with
    | Unit => Unit
    | Bool b => Bool b
    | Int n => Int n
    | Float r => Float r
    | Not e => Not (subst e x es)
    | Neg e => Neg (subst e x es)
    | Add e1 e2 => Add (subst e1 x es) (subst e2 x es)
    | Sub e1 e2 => Sub (subst e1 x es) (subst e2 x es)
    | FNeg e => FNeg (subst e x es)
    | FAdd e1 e2 => FAdd (subst e1 x es) (subst e2 x es)
    | FSub e1 e2 => FSub (subst e1 x es) (subst e2 x es)
    | FMul e1 e2 => FMul (subst e1 x es) (subst e2 x es)
    | FDiv e1 e2 => FDiv (subst e1 x es) (subst e2 x es)
    | Eq e1 e2 => Eq (subst e1 x es) (subst e2 x es)
    | LE e1 e2 => LE (subst e1 x es) (subst e2 x es)
    | If e1 e2 e3 => If (subst e1 x es) (subst e2 x es) (subst e3 x es)
    | Let e1 e2 => Let (subst e1 x es) (subst e2 (S x) es)
    | Abs e => Abs (subst e (S x) es)
    | Var y =>
        if le_dec x y then shift (nth (y - x) es (Var (y - x - length es))) 0 x
        else Var y
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
    induction e; intros c c' d d' Hle; simpl; f_equal; auto;
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
    induction e; intros c c' d d' Hle; simpl; f_equal; auto;
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
    induction e; intros c d x es Hle; simpl; f_equal; eauto.
      replace (S (d + x)) with (d + S x) by omega.
      apply IHe2.
      omega.

      repeat (simpl; unfold shift_var; match goal with
      | [ |- context [ le_dec ?x ?n ] ] =>
          destruct (le_dec x n)
      | [ |- context [ lt_dec ?x ?n ] ] =>
          destruct (lt_dec x n)
      end); 
      try rewrite shift_meld by omega;
      eauto; try omega.

      replace (d + n - (d + x)) with (n - x) by omega.
      f_equal.
      omega.

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
    induction e; intros c d x es Hle Hlength; simpl; f_equal; eauto.
      apply IHe2; omega.

      unfold shift_var.
      repeat (try (rewrite nth_overflow by omega; simpl; unfold shift_var); 
        match goal with
        | [ |- context [ lt_dec ?n ?c ] ] => destruct (lt_dec n c)
        | [ |- context [ le_dec ?n ?c ] ] => destruct (le_dec n c)
        end); f_equal; omega.

      apply IHe; omega.
  Qed.

  Inductive value : t -> Prop :=
    | V_Unit : value Unit
    | V_Bool : forall b, value (Bool b)
    | V_Int : forall n, value (Int n)
    | V_Float : forall r, value (Float r)
    | V_Abs : forall e, value (Abs e).
  Hint Constructors value.

  Inductive evalto : t -> t -> Prop :=
    | E_Unit : evalto Unit Unit
    | E_Bool : forall b, evalto (Bool b) (Bool b)
    | E_Int : forall n, evalto (Int n) (Int n)
    | E_Float : forall r, evalto (Float r) (Float r)
    | E_Not : forall e b b',
        evalto e (Bool b') ->
        b = negb b' ->
        evalto (Not e) (Bool b)
    | E_Neg : forall e n n',
        evalto e (Int n') ->
        n = (0 - n')%Z ->
        evalto (Neg e) (Int n)
    | E_Add : forall e1 e2 n n1 n2,
        evalto e1 (Int n1) ->
        evalto e2 (Int n2) ->
        n = (n1 + n2)%Z ->
        evalto (Add e1 e2) (Int n)
    | E_Sub : forall e1 e2 n n1 n2,
        evalto e1 (Int n1) ->
        evalto e2 (Int n2) ->
        n = (n1 - n2)%Z ->
        evalto (Sub e1 e2) (Int n)
    | E_FNeg : forall e r r',
        evalto e (Float r') ->
        r = (0 - r')%R ->
        evalto (FNeg e) (Float r)
    | E_FAdd : forall e1 e2 r r1 r2,
        evalto e1 (Float r1) ->
        evalto e2 (Float r2) ->
        r = (r1 + r2)%R ->
        evalto (FAdd e1 e2) (Float r)
    | E_FSub : forall e1 e2 r r1 r2,
        evalto e1 (Float r1) ->
        evalto e2 (Float r2) ->
        r = (r1 - r2)%R ->
        evalto (FSub e1 e2) (Float r)
    | E_FMul : forall e1 e2 r r1 r2,
        evalto e1 (Float r1) ->
        evalto e2 (Float r2) ->
        r = (r1 * r2)%R ->
        evalto (FMul e1 e2) (Float r)
    | E_FDiv : forall e1 e2 r r1 r2,
        evalto e1 (Float r1) ->
        evalto e2 (Float r2) ->
        r = (r1 / r2)%R ->
        evalto (FDiv e1 e2) (Float r)
    | E_EqBool : forall e1 e2 b b1 b2,
        evalto e1 (Bool b1) ->
        evalto e2 (Bool b2) ->
        b = Bool.eqb b1 b2 ->
        evalto (Eq e1 e2) (Bool b)
    | E_EqInt : forall e1 e2 b n1 n2,
        evalto e1 (Int n1) ->
        evalto e2 (Int n2) ->
        b = (n1 =? n2)%Z ->
        evalto (Eq e1 e2) (Bool b)
    | E_EqFloat : forall e1 e2 b r1 r2,
        evalto e1 (Float r1) ->
        evalto e2 (Float r2) ->
        r1 = r2 /\ b = true \/ r1 <> r2 /\ b = false ->
        evalto (Eq e1 e2) (Bool b)
    | E_LEBool : forall e1 e2 b b1 b2,
        evalto e1 (Bool b1) ->
        evalto e2 (Bool b2) ->
        b = (negb b1 || b2)%bool ->
        evalto (LE e1 e2) (Bool b)
    | E_LEInt : forall e1 e2 b n1 n2,
        evalto e1 (Int n1) ->
        evalto e2 (Int n2) ->
        b = (n1 <=? n2)%Z ->
        evalto (LE e1 e2) (Bool b)
    | E_LEFloat : forall e1 e2 b r1 r2,
        evalto e1 (Float r1) ->
        evalto e2 (Float r2) ->
        (r1 <= r2)%R /\ b = true \/ ~ (r1 <= r2)%R /\ b = false ->
        evalto (LE e1 e2) (Bool b)
    | E_IfTrue : forall e1 e2 e3 v,
        evalto e1 (Bool true) ->
        evalto e2 v ->
        evalto (If e1 e2 e3) v
    | E_IfFalse : forall e1 e2 e3 v,
        evalto e1 (Bool false) ->
        evalto e3 v ->
        evalto (If e1 e2 e3) v
    | E_Abs : forall t,
        evalto (Abs t) (Abs t)
    | E_App : forall t1 t2 t0 v2 v,
        evalto t1 (Abs t0) ->
        evalto t2 v2 ->
        evalto (subst t0 0 [v2]) v ->
        evalto (App t1 t2) v
    | E_Let : forall t1 t2 v1 v2,
        evalto t1 v1 ->
        evalto (subst t2 0 [v1]) v2 ->
        evalto (Let t1 t2) v2.
  Hint Constructors evalto.

  CoInductive diverge : t -> Prop :=
    | D_Not : forall t,
        diverge t ->
        diverge (Not t)
    | D_Neg : forall t,
        diverge t ->
        diverge (Neg t)
    | D_AddL : forall t1 t2,
        diverge t1 ->
        diverge (Add t1 t2)
    | D_AddR : forall t1 t2 v,
        evalto t1 v ->
        diverge t2 ->
        diverge (Add t1 t2)
    | D_SubL : forall t1 t2,
        diverge t1 ->
        diverge (Sub t1 t2)
    | D_SubR : forall t1 t2 v,
        evalto t1 v ->
        diverge t2 ->
        diverge (Sub t1 t2)
    | D_FNeg : forall t,
        diverge t ->
        diverge (FNeg t)
    | D_FAddL : forall t1 t2,
        diverge t1 ->
        diverge (FAdd t1 t2)
    | D_FAddR : forall t1 t2 v,
        evalto t1 v ->
        diverge t2 ->
        diverge (FAdd t1 t2)
    | D_FSubL : forall t1 t2,
        diverge t1 ->
        diverge (FSub t1 t2)
    | D_FSubR : forall t1 t2 v,
        evalto t1 v ->
        diverge t2 ->
        diverge (FSub t1 t2)
    | D_FMulL : forall t1 t2,
        diverge t1 ->
        diverge (FMul t1 t2)
    | D_FMulR : forall t1 t2 v,
        evalto t1 v ->
        diverge t2 ->
        diverge (FMul t1 t2)
    | D_FDivL : forall t1 t2,
        diverge t1 ->
        diverge (FDiv t1 t2)
    | D_FDivR : forall t1 t2 v,
        evalto t1 v ->
        diverge t2 ->
        diverge (FDiv t1 t2)
    | D_EqL : forall t1 t2,
        diverge t1 ->
        diverge (Eq t1 t2)
    | D_EqR : forall t1 t2 v,
        evalto t1 v ->
        diverge t2 ->
        diverge (Eq t1 t2)
    | D_LEL : forall t1 t2,
        diverge t1 ->
        diverge (LE t1 t2)
    | D_LER : forall t1 t2 v,
        evalto t1 v ->
        diverge t2 ->
        diverge (LE t1 t2)
    | D_IfCond : forall t1 t2 t3,
        diverge t1 ->
        diverge (If t1 t2 t3)
    | D_IfTrue : forall t1 t2 t3,
        evalto t1 (Bool true) ->
        diverge t2 ->
        diverge (If t1 t2 t3)
    | D_IfFalse : forall t1 t2 t3,
        evalto t1 (Bool false) ->
        diverge t3 ->
        diverge (If t1 t2 t3)
    | D_LetL : forall t1 t2,
        diverge t1 ->
        diverge (Let t1 t2)
    | D_LetR : forall t1 v1 t2,
        evalto t1 v1 ->
        diverge (subst t2 0 [v1]) ->
        diverge (Let t1 t2)
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
        diverge (App t1 t2).
  Hint Constructors diverge.

  Lemma evalto_value : forall e v,
    evalto e v -> value v.
  Proof.
    intros e v Hevalto.
    induction Hevalto; auto.
  Qed.
  Hint Resolve evalto_value.

  Lemma evalto_ident : forall v,
    value v -> evalto v v.
  Proof.
    intros v Hvalue.
    inversion Hvalue; auto.
  Qed.
  Hint Resolve evalto_ident.

  Lemma evalto_decidable : forall e v1 v2,
    evalto e v1 -> evalto e v2 -> v1 = v2.
  Proof.
    intros e v1 v2 Hevalto1.
    generalize dependent v2.
    induction Hevalto1; intros v2_ Hevalto2; inversion Hevalto2; clear Hevalto2;
      repeat (subst; match goal with
      | [ H : Abs _ = Abs _ |- _ ] => inversion H; clear H
      | [ Hevalto : evalto ?t ?v, IH : forall v, evalto ?t v -> _ = v |- _ ] =>
          generalize (IH _ Hevalto); intros; clear Hevalto
      | [ H : _ \/ _ |- _ ] => destruct H
      | [ H : _ /\ _ |- _ ] => destruct H
      end); congruence.
  Qed.

  Lemma evalto_diverge_disjoint : forall e v,
    evalto e v -> diverge e -> False.
  Proof.
    intros e v Hevalto.
    induction Hevalto; intros Hdiverge; inversion Hdiverge; clear Hdiverge;
      repeat (subst; match goal with
      | [ H : Abs _ = Abs _ |- _ ] => inversion H; clear H
      | [ Hevalto : evalto ?t ?v, Hevalto' : evalto ?t ?v' |- _ ] =>
          generalize (evalto_decidable _ _ _ Hevalto Hevalto'); intros; clear Hevalto; clear Hevalto'
      end); subst; auto; discriminate.
  Qed.

  Fixpoint knormal e :=
    match e with
    | Unit => Unit
    | Bool b => Bool b
    | Int n => Int n
    | Float r => Float r
    | Not e =>
        Let (knormal e)
          (Not (Var 0))
    | Neg e =>
        Let (knormal e)
          (Neg (Var 0))
    | Add e1 e2 =>
        Let (knormal e1)
          (Let (shift (knormal e2) 0 1)
            (Add (Var 1) (Var 0)))
    | Sub e1 e2 =>
        Let (knormal e1)
          (Let (shift (knormal e2) 0 1)
            (Sub (Var 1) (Var 0)))
    | FNeg e =>
        Let (knormal e)
          (FNeg (Var 0))
    | FAdd e1 e2 =>
        Let (knormal e1)
          (Let (shift (knormal e2) 0 1)
            (FAdd (Var 1) (Var 0)))
    | FSub e1 e2 =>
        Let (knormal e1)
          (Let (shift (knormal e2) 0 1)
            (FSub (Var 1) (Var 0)))
    | FMul e1 e2 =>
        Let (knormal e1)
          (Let (shift (knormal e2) 0 1)
            (FMul (Var 1) (Var 0)))
    | FDiv e1 e2 =>
        Let (knormal e1)
          (Let (shift (knormal e2) 0 1)
            (FDiv (Var 1) (Var 0)))
    | Eq e1 e2 =>
        Let (knormal e1)
          (Let (shift (knormal e2) 0 1)
            (Eq (Var 1) (Var 0)))
    | LE e1 e2 =>
        Let (knormal e1)
          (Let (shift (knormal e2) 0 1)
            (LE (Var 1) (Var 0)))
    | If e1 e2 e3 =>
        Let (knormal e1)
          (If (Var 0) (shift (knormal e2) 0 1) (shift (knormal e3) 0 1))
    | Let e1 e2 => Let (knormal e1) (knormal e2)
    | Var x => Var x
    | Abs e => Abs (knormal e)
    | App e1 e2 =>
        Let (knormal e1)
          (Let (shift (knormal e2) 0 1)
            (App (Var 1) (Var 0)))
    end.

  Lemma knormal_preserve_value : forall v,
    value v -> value (knormal v).
  Proof.
    intros v Hvalue.
    inversion Hvalue; simpl; auto.
  Qed.
  Hint Resolve knormal_preserve_value.

  Lemma knormal_shift : forall e c d,
    knormal (shift e c d) = shift (knormal e) c d.
  Proof.
    intros e.
    induction e; simpl; intros c d; f_equal; auto;
      repeat (try rewrite shift_swap by omega;
      match goal with
      | [ |- Let _ _ = Let _ _ ] => f_equal
      | [ IH : forall _ _, knormal (shift _ _ _) = shift (knormal _) _ _ |- _ ] =>
          try rewrite IH; clear IH
      end); reflexivity.
  Qed.

  Lemma knormal_subst : forall e x es,
    knormal (subst e x es) = subst (knormal e) x (map knormal es).
  Proof.
    intros e.
    induction e; intros x es; simpl; f_equal; eauto;
      try (repeat (try rewrite subst_shift by omega;
      match goal with
      | [ |- Let _ _ = Let _ _ ] => f_equal
      | [ IH : forall _ _, knormal (subst _ _ _) = subst (knormal _) _ _ |- _ ] =>
          try rewrite IH; clear IH
      end); reflexivity).
      
      destruct (le_dec x n); auto.
      rewrite knormal_shift.
      f_equal.
      replace (Var (n - x - length (map knormal es))) with
        (knormal (Var (n - x - length (map knormal es)))) by reflexivity.
      rewrite map_nth.
      rewrite map_length.
      reflexivity.
  Qed.

  Theorem knormal_evalto : forall e v,
    evalto e v -> evalto (knormal e) (knormal v).
  Proof.
    intros e v Hevalto.
    induction Hevalto;
      repeat (simpl in * |- *;
      try (rewrite subst_ignore by (simpl; omega));
      match goal with
      | [ |- evalto (Let _ _) _ ] => econstructor
      | [ |- evalto (Not _) _ ] => econstructor
      | [ |- evalto (Neg _) _ ] => econstructor
      | [ |- evalto (Add _ _) _ ] => econstructor
      | [ |- evalto (Sub _ _) _ ] => econstructor
      | [ |- evalto (Eq (Bool _) (Bool _)) _ ] => eapply E_EqBool
      | [ |- evalto (Eq (Int _) (Int _)) _ ] => eapply E_EqInt
      | [ |- evalto (LE (Bool _) (Bool _)) _ ] => eapply E_LEBool
      | [ |- evalto (LE (Int _) (Int _)) _ ] => eapply E_LEInt
      | [ |- evalto (If (Bool true) _ _) _ ] => eapply E_IfTrue
      | [ |- evalto (If (Bool false) _ _) _ ] => eapply E_IfFalse
      | [ |- evalto (App _ _) _ ] => eapply E_App
      | [ |- context [ shift _ _ 0 ] ] => rewrite shift_0
      | [ H : context [ knormal (subst _ _ _) ] |- _ ] => rewrite knormal_subst in H; simpl in * |- *
      end); simpl; eauto.
  Qed.

  Theorem knormal_diverge : forall e,
    diverge e -> diverge (knormal e).
  Proof.
    cofix.
    intros e Hdiverge.
    inversion Hdiverge; subst; clear Hdiverge; simpl;
      timeout 1 repeat (simpl in * |- *;
      try (rewrite subst_ignore by (simpl; omega); simpl in * |- *);
      match goal with
      | [ H : diverge ?t |- diverge (Let (knormal ?t) _) ] =>
          apply D_LetL; auto
      | [ H : evalto ?t _ |- diverge (Let (knormal ?t) _) ] =>
          eapply D_LetR
      | [ |- evalto (knormal _) _ ] =>
          eapply knormal_evalto; try eassumption
      | [ |- context [ shift _ _ 0 ] ] => rewrite shift_0
      | [ |- diverge (If (Bool true) _ _) ] => eapply D_IfTrue; auto
      | [ |- diverge (If (Bool false) _ _) ] => eapply D_IfFalse; auto
      end).

      specialize (knormal_diverge _ H0).
      rewrite knormal_subst in knormal_diverge.
      assumption.

      eapply D_App.
        eauto.

        eapply knormal_evalto.
        apply evalto_ident.
        eapply evalto_value.
        eauto.

        specialize (knormal_diverge _ H1).
        rewrite knormal_subst in knormal_diverge.
        assumption.
  Qed.
End Exp.
