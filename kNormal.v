Require Import Arith List Omega Program.

Definition id := nat.

Definition shift_var c d x :=
  if le_dec (S x) c then x else d + x.

Module Exp.
  Inductive t :=
    | Var : nat -> t
    | Fix : t -> t
    | App : t -> t -> t
    | Let : t -> t -> t
    | Int : nat -> t
    | Add : t -> t -> t
    | Sub : t -> t -> t
    | Bool : bool -> t
    | If : t -> t -> t -> t
    | ExtVar : id -> t
    | Pair : t -> t -> t
    | Fst : t -> t
    | Snd : t -> t.

  Fixpoint shift c d e :=
    match e with
    | Var x => Var (shift_var c d x)
    | Fix e => Fix (shift (S (S c)) d e)
    | App e1 e2 => App (shift c d e1) (shift c d e2)
    | Let e1 e2 => Let (shift c d e1) (shift (S c) d e2)
    | Int n => Int n
    | Add e1 e2 => Add (shift c d e1) (shift c d e2)
    | Sub e1 e2 => Sub (shift c d e1) (shift c d e2)
    | Bool b => Bool b
    | If e1 e2 e3 => If (shift c d e1) (shift c d e2) (shift c d e3)
    | ExtVar x => ExtVar x
    | Pair e1 e2 => Pair (shift c d e1) (shift c d e2)
    | Fst e1 => Fst (shift c d e1)
    | Snd e1 => Snd (shift c d e1)
    end.

  Definition subst_var x es y :=
    if le_dec x y then shift 0 x (nth (y - x) es (Var (y - x - length es)))
    else Var y.

  Ltac elim_shift_subst_var :=
    repeat (unfold shift_var in *; unfold subst_var in *; match goal with
    | |- context [le_dec ?x ?c] => destruct (le_dec x c)
    | H : context [le_dec ?x ?c] |- _ => destruct (le_dec x c)
    end; simpl in *).

  Lemma shift_0 : forall e c,
    shift c 0 e = e.
  Proof.
    intros e.
    induction e; intros ?; simpl;
      f_equal;
      elim_shift_subst_var;
      eauto.
  Qed.
  Hint Rewrite shift_0.

  Lemma shift_meld : forall e c c' d d',
    c <= c' <= c + d ->
    shift c' d' (shift c d e) = shift c (d + d') e.
  Proof.
    fix 1.
    intros e ? ? ? ? ?.
    destruct e; simpl;
      repeat rewrite shift_meld by omega;
      eauto.
    elim_shift_subst_var; f_equal; omega.
  Qed.

  Lemma shift_swap : forall e c c' d d',
    c' <= c ->
    shift c' d' (shift c d e) = shift (d' + c) d (shift c' d' e).
  Proof.
    fix 1.
    intros e ? ? ? ? ?.
    destruct e; simpl; f_equal;
      try rewrite shift_swap by omega;
      try solve [auto | f_equal; omega].
    elim_shift_subst_var; omega.
  Qed.
  Hint Rewrite shift_swap using omega.

  Fixpoint subst x es e :=
    match e with
    | Var y => subst_var x es y
    | Fix e => Fix (subst (S (S x)) es e)
    | App e1 e2 => App (subst x es e1) (subst x es e2)
    | Let e1 e2 => Let (subst x es e1) (subst (S x) es e2)
    | Int n => Int n
    | Add e1 e2 => Add (subst x es e1) (subst x es e2)
    | Sub e1 e2 => Sub (subst x es e1) (subst x es e2)
    | Bool b => Bool b
    | If e1 e2 e3 => If (subst x es e1) (subst x es e2) (subst x es e3)
    | ExtVar x => ExtVar x
    | Pair e1 e2 => Pair (subst x es e1) (subst x es e2)
    | Fst e1 => Fst (subst x es e1)
    | Snd e1 => Snd (subst x es e1)
    end.

  Lemma subst_ignore : forall e c d x es,
    c <= x ->
    length es + x <= d + c ->
    subst x es (shift c d e) = shift c (d - length es) e.
  Proof.
    fix 1.
    intros e ? ? ? ? ? ?.
    destruct e; simpl; f_equal;
      try apply subst_ignore;
      try omega.
    repeat ((rewrite nth_overflow by omega; simpl)
      || elim_shift_subst_var);
    f_equal; omega.
  Qed.
  Hint Rewrite subst_ignore using (simpl; omega).

  Lemma subst_meld : forall e x x' es es',
    x' = length es + x ->
    subst x es (subst x' es' e) = subst x (es ++ es') e.
  Proof.
    fix 1.
    intros e ? ? ? ? ?.
    subst.
    destruct e; simpl;
      repeat rewrite subst_meld in * by omega;
      auto.
    elim_shift_subst_var; auto; try omega.
    + rewrite subst_ignore by omega.
      rewrite app_nth2 by omega.
      rewrite app_length.
      repeat (f_equal; try omega).
    + rewrite app_nth1 by omega.
      f_equal.
      apply nth_indep.
      omega.
  Qed.

  Lemma shift_subst_distr : forall e c d x es,
    c <= x ->
    shift c d (subst x es e) = subst (d + x) es (shift c d e).
  Proof.
    fix 1.
    intros e ? ? ? ? ?.
    destruct e; simpl;
      repeat rewrite shift_subst_distr by omega;
      repeat (f_equal; try omega).
    elim_shift_subst_var;
      try rewrite shift_meld by omega;
      repeat (f_equal; try omega).
  Qed.
  Hint Rewrite shift_subst_distr using omega.

  Lemma subst_shift_distr : forall e c d x es,
    x <= c ->
    shift c d (subst x es e) =
    subst x (map (shift (c - x) d) es) (shift (length es + c) d e).
  Proof.
    fix 1.
    intros e ? ? ? ? ?.
    destruct e; simpl;
      repeat rewrite subst_shift_distr by omega;
      repeat (f_equal; try omega).
    elim_shift_subst_var; auto; try omega;
      repeat rewrite <- map_nth with (f := shift 0 x);
      rewrite <- map_nth with (f := shift c d);
      rewrite map_length.
    - replace (map (shift c d) (map (shift 0 x) es))
      with (map (shift 0 x) (map (shift (c - x) d) es)).
      + destruct (lt_dec (n - x) (length es)).
        * apply nth_indep.
          repeat rewrite map_length.
          omega.
        * simpl.
          do 2 f_equal.
          elim_shift_subst_var; omega.
      + repeat rewrite map_map.
        apply map_ext.
        intros ?.
        rewrite shift_swap by omega.
        f_equal.
        omega.
    - repeat rewrite nth_overflow by (repeat rewrite map_length; omega).
      simpl.
      f_equal.
      elim_shift_subst_var; omega.
  Qed.

  Lemma subst_subst_distr : forall e x x' es es',
    x' <= x ->
    subst x es (subst x' es' e)
    = subst x' (map (subst (x - x') es) es') (subst (length es' + x) es e).
  Proof.
    fix 1.
    intros e ? ? ? ? ?.
    destruct e; simpl;
      try solve
        [ eauto
        | f_equal;
          rewrite subst_subst_distr by omega;
          repeat (f_equal; try omega) ].
    elim_shift_subst_var; eauto; try omega.
    - rewrite nth_overflow by (repeat rewrite map_length; omega).
      simpl.
      rewrite subst_ignore by (try rewrite map_length; omega).
      rewrite map_length.
      elim_shift_subst_var; try omega.
      clear l1.
      (* repeat (f_equal; try omega) *)
      f_equal.
      + omega.
      + f_equal.
        * omega.
        * do 2 f_equal.
          omega.
    - clear l0.
      rewrite map_length.
      repeat rewrite <- map_nth with (f := shift 0 x').
      rewrite <- map_nth with (f := subst x es).
      replace (map (subst x es) (map (shift 0 x') es'))
        with (map (shift 0 x') (map (subst (x - x') es) es'));
      repeat rewrite map_map.
      + destruct (eq_nat_dec x x').
        * subst.
          apply nth_indep.
          rewrite map_length.
          omega.
        * f_equal.
          simpl.
          elim_shift_subst_var; eauto; omega.
      + apply map_ext.
        intros ?.
        rewrite shift_subst_distr by omega.
        f_equal.
        omega.
  Qed.

  Lemma subst_nil : forall x e,
    subst x [] e = e.
  Proof.
    fix 2.
    intros ? e.
    destruct e; simpl;
      f_equal;
      eauto.
    elim_shift_subst_var; auto.
    remember (n - x) as y.
    destruct y; simpl; elim_shift_subst_var; f_equal; omega.
  Qed.

  Inductive value : t -> Prop :=
    | V_Fix : forall e, value (Fix e)
    | V_Int : forall n, value (Int n)
    | V_Bool : forall b, value (Bool b)
    | V_ExtVar : forall x, value (ExtVar x)
    | V_Pair : forall v1 v2,
        value v1 ->
        value v2 ->
        value (Pair v1 v2).
  Hint Constructors value.

  Inductive label :=
    | L_ExtApp : nat -> nat -> nat -> label.

  Inductive evalto : list label -> Exp.t -> Exp.t -> Prop :=
    | E_Fix : forall e,
        evalto [] (Fix e) (Fix e)
    | E_App : forall e1 e2 e v2 v l1 l2 l3 l,
        evalto l1 e1 (Fix e) ->
        evalto l2 e2 v2 ->
        evalto l3 (subst 0 [Fix e; v2] e) v ->
        l = l1 ++ l2 ++ l3 ->
        evalto l (App e1 e2) v
    | E_ExtApp : forall e1 e2 x v2 v l1 l2 l,
        evalto l1 e1 (ExtVar x) ->
        evalto l2 e2 (Int v2) ->
        l = l1 ++ l2 ++ [L_ExtApp x v2 v] ->
        evalto l (App e1 e2) (Int v)
    | E_Let : forall e1 e2 v1 v2 l1 l2 l,
        evalto l1 e1 v1 ->
        evalto l2 (subst 0 [v1] e2) v2 ->
        l = l1 ++ l2 ->
        evalto l (Let e1 e2) v2
    | E_Int : forall n,
        evalto [] (Int n) (Int n)
    | E_Add : forall e1 e2 n1 n2 l1 l2 l,
        evalto l1 e1 (Int n1) ->
        evalto l2 e2 (Int n2) ->
        l = l1 ++ l2 ->
        evalto l (Add e1 e2) (Int (n1 + n2))
    | E_Sub : forall e1 e2 n1 n2 l1 l2 l,
        evalto l1 e1 (Int n1) ->
        evalto l2 e2 (Int n2) ->
        l = l1 ++ l2 ->
        evalto l (Sub e1 e2) (Int (n1 - n2))
    | E_Bool : forall b,
        evalto [] (Bool b) (Bool b)
    | E_IfTrue : forall e1 e2 e3 v2 l1 l2 l,
        evalto l1 e1 (Bool true) ->
        evalto l2 e2 v2 ->
        l = l1 ++ l2 ->
        evalto l (If e1 e2 e3) v2
    | E_IfFalse : forall e1 e2 e3 v3 l1 l3 l,
        evalto l1 e1 (Bool false) ->
        evalto l3 e3 v3 ->
        l = l1 ++ l3 ->
        evalto l (If e1 e2 e3) v3
    | E_ExtVar : forall x,
        evalto [] (ExtVar x) (ExtVar x)
    | E_Pair : forall e1 e2 v1 v2 l1 l2 l,
        evalto l1 e1 v1 ->
        evalto l2 e2 v2 ->
        l = l1 ++ l2 ->
        evalto l (Pair e1 e2) (Pair v1 v2)
    | E_Fst : forall e v1 v2 l,
        evalto l e (Pair v1 v2) ->
        evalto l (Fst e) v1
    | E_Snd : forall e v1 v2 l,
        evalto l e (Pair v1 v2) ->
        evalto l (Snd e) v2.
  Hint Constructors evalto.

  CoInductive trace :=
    | TNil
    | TCons : label -> trace -> trace.

  Fixpoint tapp ls t :=
    match ls with
    | [] => t
    | l :: ls' => TCons l (tapp ls' t)
    end.

  CoInductive diverge : trace -> Exp.t -> Prop :=
    | D_AppL : forall e1 e2 l1,
        diverge l1 e1 ->
        diverge l1 (App e1 e2)
    | D_AppR : forall e1 e2 l1 l2 l v1,
        evalto l1 e1 v1 ->
        diverge l2 e2 ->
        l = tapp l1 l2 ->
        diverge l (App e1 e2)
    | D_App : forall e1 e2 e l1 l2 l3 l v2,
        evalto l1 e1 (Fix e) ->
        evalto l2 e2 v2 ->
        diverge l3 (subst 0 [Fix e; v2] e) ->
        l = tapp l1 (tapp l2 l3) ->
        diverge l (App e1 e2)
    | D_LetL : forall e1 e2 l1,
        diverge l1 e1 ->
        diverge l1 (Let e1 e2)
    | D_LetR : forall e1 e2 l1 l2 l v1,
        evalto l1 e1 v1 ->
        diverge l2 (subst 0 [v1] e2) ->
        l = tapp l1 l2 ->
        diverge l (Let e1 e2)
    | D_AddL : forall e1 e2 l1,
        diverge l1 e1 ->
        diverge l1 (Add e1 e2)
    | D_AddR : forall e1 e2 l1 l2 l v1,
        evalto l1 e1 v1 ->
        diverge l2 e2 ->
        l = tapp l1 l2 ->
        diverge l (Add e1 e2)
    | D_SubL : forall e1 e2 l1,
        diverge l1 e1 ->
        diverge l1 (Sub e1 e2)
    | D_SubR : forall e1 e2 l1 l2 l v1,
        evalto l1 e1 v1 ->
        diverge l2 e2 ->
        l = tapp l1 l2 ->
        diverge l (Sub e1 e2)
    | D_If : forall e1 e2 e3 l1,
        diverge l1 e1 ->
        diverge l1 (If e1 e2 e3)
    | D_IfTrue : forall e1 e2 e3 l1 l2 l,
        evalto l1 e1 (Bool true) ->
        diverge l2 e2 ->
        l = tapp l1 l2 ->
        diverge l (If e1 e2 e3) 
    | D_IfFalse : forall e1 e2 e3 l1 l3 l,
        evalto l1 e1 (Bool false) ->
        diverge l3 e3 ->
        l = tapp l1 l3 ->
        diverge l (If e1 e2 e3)
    | D_PairL : forall e1 e2 l1,
        diverge l1 e1 ->
        diverge l1 (Pair e1 e2)
    | D_PairR : forall e1 e2 l1 l2 l v1,
        evalto l1 e1 v1 ->
        diverge l2 e2 ->
        l = tapp l1 l2 ->
        diverge l (Pair e1 e2)
    | D_Fst : forall e l,
        diverge l e ->
        diverge l (Fst e)
    | D_Snd : forall e l,
        diverge l e ->
        diverge l (Snd e).
  Hint Constructors diverge.

  Lemma evalto_ident : forall v,
    Exp.value v ->
    evalto [] v v.
  Proof.
    intros ? Hv.
    induction Hv; eauto.
  Qed.
  Hint Resolve evalto_ident.

  Lemma evalto_value_determinism : forall e,
    Exp.value e ->
    forall l v,
    evalto l e v ->
    l = [] /\ e = v.
  Proof.
    intros ? Hvalue.
    induction Hvalue;
      intros ? ? Hevalto;
      inversion Hevalto;
      eauto.
    destruct (IHHvalue1 _ _ H1).
    destruct (IHHvalue2 _ _ H3).
    subst.
    eauto.
  Qed.

  Lemma evalto_value : forall e v l,
    evalto l e v ->
    Exp.value v.
  Proof.
    intros ? ? ? Hevalto.
    induction Hevalto; eauto.
    - inversion IHHevalto. eauto.
    - inversion IHHevalto. eauto.
  Qed.
  Hint Resolve evalto_value.

  Lemma value_never_diverge : forall v,
    value v -> forall l, diverge l v -> False.
  Proof.
    intros ? Hv.
    induction Hv;
      intros ? Hdiverge;
      inversion Hdiverge; eauto.
  Qed.
  Hint Resolve value_never_diverge.
End Exp.

Module KNormal.
  Inductive t :=
    | Var : nat -> t
    | Fix : t -> t
    | App : nat -> nat -> t
    | Let : t -> t -> t
    | Int : nat -> t
    | Add : nat -> nat -> t
    | Sub : nat -> nat -> t
    | Bool : bool -> t
    | If : nat -> t -> t -> t
    | ExtVar : id -> t
    | Pair : nat -> nat -> t
    | Fst : nat -> t
    | Snd : nat -> t.

  Fixpoint shift c d e :=
    match e with
    | Var x => Var (shift_var c d x)
    | Fix e => Fix (shift (S (S c)) d e)
    | App x y => App (shift_var c d x) (shift_var c d y)
    | Let e1 e2 => Let (shift c d e1) (shift (S c) d e2)
    | Int n => Int n
    | Add x y => Add (shift_var c d x) (shift_var c d y)
    | Sub x y => Sub (shift_var c d x) (shift_var c d y)
    | Bool b => Bool b
    | If x e2 e3 => If (shift_var c d x) (shift c d e2) (shift c d e3)
    | ExtVar x => ExtVar x
    | Pair x y => Pair (shift_var c d x) (shift_var c d y)
    | Fst x => Fst (shift_var c d x)
    | Snd x => Snd (shift_var c d x)
    end.

  Fixpoint toExp e :=
    match e with
    | Fix e => Exp.Fix (toExp e)
    | App x y => Exp.App (Exp.Var x) (Exp.Var y)
    | Var x => Exp.Var x
    | Let e1 e2 => Exp.Let (toExp e1) (toExp e2)
    | Int n => Exp.Int n
    | Add x y => Exp.Add (Exp.Var x) (Exp.Var y)
    | Sub x y => Exp.Sub (Exp.Var x) (Exp.Var y)
    | Bool b => Exp.Bool b
    | If x e2 e3 => Exp.If (Exp.Var x) (toExp e2) (toExp e3)
    | ExtVar x => Exp.ExtVar x
    | Pair x y => Exp.Pair (Exp.Var x) (Exp.Var y)
    | Fst x => Exp.Fst (Exp.Var x)
    | Snd x => Exp.Snd (Exp.Var x)
    end.

  Lemma toExp_inj : forall e e',
    toExp e = toExp e' -> e = e'.
  Proof.
    intros e.
    induction e;
    intros e' HtoExp;
    destruct e';
    simpl in *;
    inversion HtoExp;
    subst;
    f_equal;
    eauto.
  Qed.

  Lemma toExp_shift_commute : forall e c d,
    toExp (shift c d e) = Exp.shift c d (toExp e).
  Proof.
    intros e.
    induction e;
    intros ? ?;
    simpl;
    f_equal;
    eauto.
  Qed.

  Fixpoint knormal e :=
    match e with
    | Exp.Var x => Var x
    | Exp.Fix e => Fix (knormal e)
    | Exp.App e1 e2 =>
        Let (knormal e1)
          (Let (shift 0 1 (knormal e2))
            (App 1 0))
    | Exp.Let e1 e2 => Let (knormal e1) (knormal e2)
    | Exp.Int n => Int n
    | Exp.Add e1 e2 =>
        Let (knormal e1)
          (Let (shift 0 1 (knormal e2))
            (Add 1 0))
    | Exp.Sub e1 e2 =>
        Let (knormal e1)
          (Let (shift 0 1 (knormal e2))
            (Sub 1 0))
    | Exp.Bool b => Bool b
    | Exp.If e1 e2 e3 =>
        Let (knormal e1)
          (If 0
            (shift 0 1 (knormal e2))
            (shift 0 1 (knormal e3)))
    | Exp.ExtVar x => ExtVar x
    | Exp.Pair e1 e2 =>
        Let (knormal e1)
          (Let (shift 0 1 (knormal e2))
            (Pair 1 0))
    | Exp.Fst e =>
        Let (knormal e) (Fst 0)
    | Exp.Snd e =>
        Let (knormal e) (Snd 0)
    end.

  Inductive vknormal : Exp.t -> Exp.t -> Prop :=
    | V_Fix : forall e vs kvs,
        length vs = length kvs ->
        (forall i v kv,
          nth i (map Some vs) None = Some v ->
          nth i (map Some kvs) None = Some kv ->
          vknormal v kv) ->
        vknormal (Exp.Fix (Exp.subst 2 vs e)) (Exp.Fix (Exp.subst 2 kvs (toExp (knormal e))))
    | V_ExtVar : forall x,
        vknormal (Exp.ExtVar x) (Exp.ExtVar x)
    | V_Int : forall n,
        vknormal (Exp.Int n) (Exp.Int n)
    | V_Bool : forall b,
        vknormal (Exp.Bool b) (Exp.Bool b)
    | V_Pair : forall v1 v2 kv1 kv2,
        vknormal v1 kv1 ->
        vknormal v2 kv2 ->
        vknormal (Exp.Pair v1 v2) (Exp.Pair kv1 kv2).
  Hint Constructors vknormal.

  Lemma vknormal_value1 : forall v kv,
    vknormal v kv ->
    Exp.value v.
  Proof.
    intros ? ? Hvknormal.
    induction Hvknormal; eauto.
  Qed.
  Hint Resolve vknormal_value1.

  Lemma vknormal_value2 : forall v kv,
    vknormal v kv ->
    Exp.value kv.
  Proof.
    intros ? ? Hvknormal.
    induction Hvknormal; eauto.
  Qed.
  Hint Resolve vknormal_value2.

  Lemma knormal_shift : forall c d e,
    knormal (Exp.shift c d e) = shift c d (knormal e).
  Proof.
    fix 3.
    intros ? ? e.
    apply toExp_inj.
    destruct e; simpl in *;
      repeat rewrite knormal_shift in *;
      repeat rewrite toExp_shift_commute;
      repeat (f_equal; rewrite Exp.shift_swap by omega; eauto).
  Qed.

  Lemma knormal_subst : forall x es e,
    Exp.subst x (map (fun e => toExp (knormal e)) es) (toExp (knormal e))
    = toExp (knormal (Exp.subst x es e)).
  Proof.
    fix 3.
    intros ? ? e.
    destruct e; simpl in *;
      repeat rewrite toExp_shift_commute;
      repeat rewrite <- Exp.shift_subst_distr with (d := 1) by omega;
      repeat rewrite knormal_subst;
      eauto.
    Exp.elim_shift_subst_var; eauto.
    rewrite knormal_shift.
    rewrite toExp_shift_commute.
    f_equal.
    rewrite <- map_nth with (f := knormal).
    rewrite <- map_nth with (f := toExp).
    rewrite map_length.
    rewrite map_map.
    reflexivity.
  Qed.

  Theorem knormal_evalto : forall l e v,
    Exp.evalto l e v ->
    forall vs kvs e',
    e = Exp.subst 0 vs e' ->
    length vs = length kvs ->
    (forall i v kv,
      nth i (map Some vs) None = Some v ->
      nth i (map Some kvs) None = Some kv ->
      vknormal v kv) ->
    exists kv, Exp.evalto l (Exp.subst 0 kvs (toExp (knormal e'))) kv /\ vknormal v kv.
  Proof.
    intros ? ? ? Hevalto.
    induction Hevalto;
      intros ? kvs e' Heq Hlength HForall;
      destruct e';
      simpl in *;
      inversion Heq;
      subst;
      repeat (match goal with
      | |- context [Exp.subst_var _ _ _] => unfold Exp.subst_var in *
      | H : context [Exp.subst_var _ _ _] |- _ => unfold Exp.subst_var in *
      | _ => rewrite <- minus_n_O in *
      | _ => rewrite Exp.shift_0 in *
      | _ => rewrite toExp_shift_commute
      | _ => rewrite <- Exp.shift_subst_distr with (d := 1) by omega
      | _ => rewrite Exp.subst_ignore by (simpl; omega)
      | H : Exp.evalto ?l1 (Exp.subst ?x ?vs ?e1) ?v1
      |- exists _, Exp.evalto (?ll ++ ?l2) (Exp.Let (Exp.subst ?x ?kvs (toExp (knormal ?e1))) ?e2) _ /\ vknormal ?v _ =>
        clear H;
        let H1 := fresh in
        assert (H1 : exists kv, Exp.evalto l1 (Exp.subst x kvs (toExp (knormal e1))) kv /\ vknormal v1 kv);
        [
        | let kv1 := fresh in
          destruct H1 as [kv1 []];
          let H2 := fresh in
          assert (H2 : exists kv, Exp.evalto l2 (Exp.subst 0 [kv1] e2) kv /\ vknormal v kv);
          [
          | destruct H2 as [? []]; eauto ] ]
      | |- exists _, Exp.evalto ?l (Exp.Let _ _) _ /\ vknormal _ _ =>
          replace l with (l ++ []) by apply app_nil_r
      end; simpl in *; subst);
      try match goal with
      | H : _ = nth ?n ?vs _ |- _ =>
          assert (n < length vs) by
          (destruct (lt_dec n (length vs));
          [ assumption
          | rewrite nth_overflow in H by omega; discriminate ])
      end;
      try match goal with
      | |- exists _, Exp.evalto _ (nth ?n kvs ?d) _ /\ _ =>
          assert (vknormal (nth n vs d) (nth n kvs d)) by
            (apply HForall with (i := n);
             rewrite <- map_nth with (f := Some);
             apply nth_indep;
             rewrite map_length;
             omega)
      end;
      repeat (match goal with
      | _ => rewrite Hlength in *
      | H : _ = nth _ _ _ |- _ => rewrite <- H in *
      | H : vknormal (Exp.Fix _) _ |- _ => inversion H; clear H
      | H : vknormal (Exp.App _ _) _ |- _ => inversion H
      | H : vknormal (Exp.Let _ _) _ |- _ => inversion H
      | H : vknormal (Exp.Int _) _ |- _ => inversion H; clear H
      | H : vknormal (Exp.Add _ _) _ |- _ => inversion H
      | H : vknormal (Exp.Sub _ _) _ |- _ => inversion H
      | H : vknormal (Exp.Bool _) _ |- _ => inversion H; clear H
      | H : vknormal (Exp.If _ _ _) _ |- _ => inversion H
      | H : vknormal (Exp.ExtVar _) _ |- _ => inversion H; clear H
      | H : vknormal (Exp.Pair _ _) _ |- _ => inversion H; clear H
      | H : vknormal (Exp.Fst _) _ |- _ => inversion H; clear H
      | H : vknormal (Exp.Snd _) _ |- _ => inversion H
      end; subst);
      eauto 7.
    - assert (IHHevalto3' : exists kv,
        Exp.evalto l3
          (Exp.subst 0
            (Exp.Fix (Exp.subst 2 kvs0 (toExp (knormal e0))) :: H3 :: kvs0)
            (toExp (knormal e0))) kv /\ vknormal v kv).
      + apply IHHevalto3 with (vs := Exp.Fix (Exp.subst 2 vs0 e0) :: v2 :: vs0); simpl; eauto.
        * rewrite Exp.subst_meld by (simpl; omega).
          eauto.
        * { intros i ? ? Hnth1 Hnth2.
            destruct i as [| []].
            - inversion Hnth1.
              inversion Hnth2.
              subst.
              eauto.
            - congruence.
            - eauto. }
      + destruct IHHevalto3' as [? []].
        eexists.
        split; eauto.
        eapply Exp.E_App; eauto;
          [ rewrite Exp.subst_meld by (simpl; omega) |];
          eauto.
    - eexists.
      split; eauto.
      eauto.
    - rewrite Exp.subst_meld in * by (simpl; omega).
      apply IHHevalto2 with (vs0 := v1 :: vs); simpl; eauto.
      intros i ? ? ? ?.
      destruct i.
      + congruence.
      + eauto.
    - assert (Hevalto2' : exists kv,
        Exp.evalto l2 (Exp.subst 0 kvs (toExp (knormal e'2))) kv
        /\ vknormal v2 kv)
        by (apply IHHevalto2 with (vs0 := vs); eauto).
      destruct Hevalto2' as [? []].
      eauto.
    - assert (Hevalto3' : exists kv,
        Exp.evalto l3 (Exp.subst 0 kvs (toExp (knormal e'3))) kv
        /\ vknormal v3 kv)
        by (apply IHHevalto2 with (vs0 := vs); eauto).
      destruct Hevalto3' as [? []].
      eauto.
    - assert (Hv1 : Exp.value e1) by eauto.
      destruct (Exp.evalto_value_determinism _ Hv1 _ _ Hevalto1).
      assert (Hv2 : Exp.value e2) by eauto.
      destruct (Exp.evalto_value_determinism _ Hv2 _ _ Hevalto2).
      subst.
      eauto 7.
  Qed.

  Theorem knormal_diverge : forall l e vs kvs,
    Exp.diverge l (Exp.subst 0 vs e) ->
    length vs = length kvs ->
    (forall i v kv,
      nth i (map Some vs) None = Some v ->
      nth i (map Some kvs) None = Some kv ->
      vknormal v kv) ->
    Exp.diverge l (Exp.subst 0 kvs (toExp (knormal e))).
  Proof.
    cofix.
    intros ? e ? ? Hdiverge Hlength Henv.
    destruct e;
      simpl in *;
      [ Exp.elim_shift_subst_var;
        [ rewrite Exp.shift_0 in *;
          destruct (lt_dec (n - 0) (length vs));
          [ assert (vknormal
              (nth (n - 0) vs (Exp.Var (n - 0 - length vs)))
              (nth (n - 0) kvs (Exp.Var (n - 0 - length kvs)))) by
              (eapply Henv;
              rewrite <- map_nth with (f := Some);
              apply nth_indep;
              rewrite map_length;
              omega);
            exfalso; eauto
          | rewrite nth_overflow in * by omega ]|]| | | | | | | | | | | |];
      inversion Hdiverge; subst;
      repeat (match goal with
      | |- context [Exp.subst_var _ _ _] => unfold Exp.subst_var in *
      | _ => rewrite Exp.shift_0
      | _ => rewrite toExp_shift_commute
      | _ => rewrite <- Exp.shift_subst_distr with (d := 1) by omega
      | _ => rewrite Exp.subst_ignore by (simpl; omega)
      | H : Exp.evalto ?l (Exp.subst 0 ?vs ?e) ?v |-
        Exp.diverge (Exp.tapp ?l _) (Exp.Let (Exp.subst 0 ?kvs (toExp (knormal ?e))) _) =>
          let Hevalto := fresh in
          assert (Hevalto : exists kv, Exp.evalto l (Exp.subst 0 kvs (toExp (knormal e))) kv /\ vknormal v kv);
          [ eapply knormal_evalto; eauto
          | destruct Hevalto as [? []];
            eapply Exp.D_LetR; eauto ]
      | H : Exp.diverge ?l (Exp.subst _ _ ?e) |-
        Exp.diverge ?l (Exp.Let (Exp.subst _ _ (toExp (knormal ?e))) _) =>
          eapply Exp.D_LetL; eauto
      | H : vknormal (Exp.Bool _) _ |- _ =>
          inversion H; clear H
      end; simpl in *; subst); eauto.
    - inversion H0; subst.
      eapply Exp.D_App; eauto; simpl; eauto.
      rewrite Exp.subst_meld in * by (simpl; omega).
      apply knormal_diverge with (vs := Exp.Fix (Exp.subst 2 vs0 e0) :: v2 :: vs0); simpl in *; eauto.
      intros i ? ? ? ?.
      destruct i as [| []].
      + congruence.
      + congruence.
      + eauto.
    - rewrite Exp.subst_meld in * by reflexivity.
      simpl in *.
      eapply knormal_diverge; eauto; simpl; eauto.
      intros i ? ? ? ?.
      destruct i.
      + congruence.
      + eauto.
  Qed.
End KNormal.
