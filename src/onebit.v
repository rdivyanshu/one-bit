From stdpp Require Import functions.
From RecordUpdate Require Import RecordUpdate.

From TLA Require Import logic.
From TLA Require Import classical.

Module onebit.

Inductive pc := ncs | wait | w2 | w3 | w4 | cs | exit.
Inductive th := th0 | th1.

#[global]
Instance th_eqdecision : EqDecision th.
Proof.
  solve_decision.
Defined.

Record state := mkState
{
  thpc : th -> pc;
  thflag : th -> bool;
}.

#[global]
Instance _eta : Settable _ := settable! mkState <thpc; thflag>.

Definition init  (s: state) :=
      ∀ t : th, s.(thpc) t = ncs
    ∧ ∀ t : th, s.(thflag) t = false.

Definition pc_ncs (t: th) : action state :=
    λ s s', s.(thpc) t = ncs
          ∧ s' = s <| thpc ::= <[ t := wait ]> |>.

Definition pc_wait (t: th) : action state :=
    λ s s', s.(thpc) t = wait
          ∧ s' = s <| thpc ::= <[ t := w2 ]> |>
                   <| thflag ::= <[ t := true ]> |>.

Definition pc_w2 (t: th) : action state :=
    λ s s', (  t = th0
             ∧ s.(thpc) th0 = w2
             ∧ s.(thflag) th1 = false
             ∧ s' = s <| thpc ::= <[ th0 := cs ]> |>
            ) ∨
            (  t = th1
             ∧ s.(thpc) th1 = w2
             ∧ s.(thflag) th0 = true
             ∧ s' = s <| thpc ::= <[ th1 := w3 ]> |>
            ) ∨
            (  t = th1
             ∧ s.(thpc) th1 = w2
             ∧ s.(thflag) th0 = false
             ∧ s' = s <| thpc ::= <[ th1 := w4 ]> |>).

Definition pc_w3 (t: th) : action state :=
    λ s s', s.(thpc) t = w3
          ∧ s' = s <| thflag ::= <[ th1 := false]> |>
                   <| thpc ::= <[ t := w4 ]> |>.

Definition pc_w4 (t: th) : action state :=
    λ s s', s.(thpc) t = w4
          ∧ s.(thflag) th0 = false
          ∧ s' = s <| thpc ::= <[ t := wait ]> |>.

Definition pc_cs (t: th) : action state :=
    λ s s', s.(thpc) t = cs
          ∧ s' = s <| thpc ::= <[ t := exit ]> |>.

Definition pc_exit (t: th) : action state :=
    λ s s', s.(thpc) t = exit
          ∧ s' = s <| thflag ::= <[ t := false]> |>
                   <| thpc ::= <[ t := ncs ]> |>.

Definition pnext (t: th) : action state :=
    λ s s', pc_wait t s s'
          ∨ pc_w2 t s s'
          ∨ pc_w3 t s s'
          ∨ pc_w4 t s s'
          ∨ pc_cs t s s'
          ∨ pc_exit t s s'.

Definition next : action state :=
    λ s s', (∃ t, pc_ncs t s s') ∨ (∃ t, pnext t s s') ∨ s = s'.

Definition OBFair0 := (weak_fairness (pnext th0)).
Definition OBFair1 := (weak_fairness (pnext th1)).

Definition spec : predicate state :=
    ⌜init⌝ ∧ □⟨next⟩ ∧ OBFair0 ∧ OBFair1.

Definition ind_invariant : state -> Prop :=
    λ s, (∀ t, s.(thpc) t = w2 ∨ s.(thpc) t = cs  -> s.(thflag) t = true)
       ∧ (∀ t, s.(thpc) t = cs -> (∀  t', t' <> t -> s.(thpc) t' <> cs))
       ∧ (∀ t, s.(thpc) t = w3 ∨ s.(thpc) t = w4 -> t <> th0).

#[global]
Hint Unfold init next pc_ncs pc_wait
    pc_w2 pc_w3 pc_w4 pc_cs pc_exit pnext : definitions.

Ltac lookup_simp :=
  repeat
    match goal with
     | H: _ |- _ => rewrite fn_lookup_insert in H
     | H: _ |- _ => rewrite -> fn_lookup_insert_ne in H
     | _ => rewrite fn_lookup_insert
     | _ => rewrite -> fn_lookup_insert_ne
    end.

Ltac logic_simp :=
  repeat
    match goal with
     | |- (_ ∧ _) => split
     | H: _ ∧ _ |- _  => destruct H
     | H: _ ∨  _ |- _  => destruct H
     | H1: ?P ∨  ?Q -> ?R, H2 : ?P |- ?R =>
        apply H1; left; assumption
     | H1: ?P ∨  ?Q -> ?R, H2 : ?Q |- ?R =>
        apply H1; right; assumption
    end.

Ltac simp :=
    autounfold with definitions in *;
    autounfold with tla in *;
    repeat(
     match goal with
        | |- (∀ (s: state), _) => intro s
        | |- (∀ (t: th), _) => intro t
        | s: state |- _ => destruct s
        | t: th |- _ =>  destruct t
        | H: (∀ (t: th), _)  |- _  =>
          pose proof (H th0); pose proof (H th1); clear H
        | H: (∃ (t: th), _)  |- _  => destruct H
        | H: @eq state (mkState _ _) (mkState _ _) |- _ =>
          invc H; cbn in *
        | H: context[@set state _ _ _ _ _] |- _ =>
          unfold set in H; simpl in H
        | _ => progress logic_simp
        | _ => progress lookup_simp
        | _ => progress cbn in *
        end);
        try congruence.

Lemma ind_invariant_lemma :
    spec ⊢ □⌜ind_invariant⌝.
Proof.
    rewrite /spec. tla_clear OBFair0. tla_clear OBFair1.
    unfold ind_invariant; apply init_invariant.
    + repeat (intros; simp).
    + intros s s' H1 H2. unfold next in H2.
      destruct H2 as [H2 | H2].
      - destruct H2 as [t H2]; repeat (intros; simp).
      - destruct H2 as [H2 | H2]; repeat (intros; simp).
        * pose proof H4 (or_introl H). congruence.
        * pose proof H4 (or_introl H). congruence.
        * intro. pose proof H9 (or_intror H10). congruence.
        * pose proof H9 (or_intror  H0). congruence.
        * pose proof (H1 H) th1. apply H7. congruence.
        * pose proof (H4 H) th0. apply H7. congruence.
Qed.

Definition safety : state -> Prop :=
    λ s, (∀ t, s.(thpc) t = cs ->
            (∀  t', t' <> t -> s.(thpc) t' <> cs)).

Theorem safety_theorem :
    spec ⊢ □⌜safety⌝.
Proof.
    rewrite ind_invariant_lemma.
    apply always_impl_proper.
    unseal. intros H.
    unfold ind_invariant in H.
    unfold safety.
    apply H.
Qed.

Theorem liveness_aux1 :
    spec ⊢ ⌜λ s, s.(thpc) th0 = wait ∨ s.(thpc) th0 = w2⌝
                ~~> ⌜λ s, s.(thpc) th0 = w2⌝.
Proof.
    rewrite /spec. tla_clear ⌜init⌝. tla_clear OBFair1.
    lt_split_or.
    + apply wf1.
      - repeat (intros; simp; unseal).
      - repeat (intros; simp; unseal).
      - repeat (intros; simp; unseal).
    +  unfold pred_impl. intros. apply leads_to_refl.
Qed.

Lemma drop_Sk_drop_k {Σ} k1 k2
    (e: exec Σ) : drop (S k1) (drop k2 e)  = drop 1 (drop (k1 + k2) e).
Proof.
  extensionality n.  rewrite /drop.
  f_equal; lia.
Qed.

Lemma drop_1 {Σ} k2
    (e: exec Σ) : drop 1 (drop k2 e) 0 = drop k2 e 1.
Proof.
  rewrite /drop.
  f_equal; lia.
Qed.

Theorem liveness_aux2 :
    spec ∧ □ ⌜λ s, s.(thpc) th0 <> cs⌝ ⊢
        ⌜λ s, s.(thpc) th0 = w2⌝
          ~~> (□ (  ⌜λ s, s.(thpc) th0 = w2⌝
                  ∧ ⌜λ s, s.(thflag) th0 = true⌝)).
Proof.
    apply (leads_to_assume ⌜ind_invariant⌝).
    + apply impl_drop_one. apply ind_invariant_lemma.
    + rewrite /spec. tla_clear OBFair0. tla_clear OBFair1.
      exists 0. rewrite drop_0.
      unfold always. intro k'. induction k'.
      - rewrite drop_0. unfold state_pred in *. simp; clear H2.
        unfold ind_invariant in H1. destruct H1.
        pose proof (H1 th0). apply H6.
        left. assumption.
      - rewrite drop_Sk_drop_k.
        autounfold with tla in *;
        destruct H. destruct H1. pose proof (H1 (k' + k)).
        rewrite drop_drop in IHk'.
        destruct H3 as [H3 | [H3 | H3]]; simp; clear H1;
        rewrite drop_1;
          try (rewrite H7; simp); try (rewrite H9; simp);
          try (rewrite H12; simp); try (rewrite H10; simp).
        * pose proof H2 (S k' + k).
          rewrite <- drop_drop in H1.
          rewrite -> drop_Sk_drop_k in H1.
          rewrite -> drop_1 in H1.
          rewrite H12 in H1. simp.
        * rewrite <- H3. simp.
        * rewrite <- H3. assumption.
Qed.

Theorem liveness_aux3a :
    spec ⊢ ⌜λ s, s.(thpc) th1 = ncs⌝
                ~~> ⌜λ s, s.(thpc) th1 = ncs⌝.
Proof.
    rewrite /spec. tla_clear ⌜init⌝. tla_clear OBFair0.
    unfold pred_impl. intros. apply leads_to_refl.
Qed.

Theorem liveness_aux3b :
    spec ⊢ ⌜λ s, s.(thpc) th1 = exit⌝
                ~~> ⌜λ s, s.(thpc) th1 = ncs⌝.
Proof.
    rewrite /spec. tla_clear ⌜init⌝. tla_clear OBFair0.
    apply wf1.
    - repeat (intros; simp; unseal).
    - repeat (intros; simp; unseal).
    - intros s H. exists (s <| thflag ::= <[ th1 := false]> |>
                            <| thpc ::= <[ th1 := ncs ]> |>).
      unfold pnext. repeat right. simp.
Qed.

Theorem liveness_aux3c :
    spec ⊢ ⌜λ s, s.(thpc) th1 = cs⌝
                ~~> ⌜λ s, s.(thpc) th1 = exit⌝.
Proof.
    rewrite /spec. tla_clear ⌜init⌝. tla_clear OBFair0.
    apply wf1.
    - repeat (intros; simp; unseal).
    - repeat (intros; simp; unseal).
    - intros s H. exists (s <| thpc ::= <[ th1 := exit ]> |>).
      unfold pnext. do 4 right. left. simp.
Qed.

Theorem liveness_aux4a :
    spec ⊢ ⌜λ s, s.(thpc) th1 = w4⌝
                ~~> ⌜λ s, s.(thpc) th1 = w4⌝.
Proof.
    rewrite /spec. tla_clear ⌜init⌝. tla_clear OBFair0.
    unfold pred_impl. intros. apply leads_to_refl.
Qed.

Theorem liveness_aux4b :
    spec ⊢ ⌜λ s, s.(thpc) th1 = w3⌝
                ~~> ⌜λ s, s.(thpc) th1 = w4⌝.
Proof.
    rewrite /spec. tla_clear ⌜init⌝. tla_clear OBFair0.
    apply wf1.
    - repeat (intros; simp; unseal).
    - repeat (intros; simp; unseal).
    - intros s H. exists (s <| thflag ::= <[ th1 := false]> |>
                            <| thpc ::= <[ th1 := w4 ]> |>).
      unfold pnext. do 2 right. left. simp.
Qed.

Theorem liveness_aux4c :
    spec ⊢  (⌜λ s, s.(thpc) th1 = w2⌝
                 ~~> (  ⌜λ s, s.(thpc) th1 = w3⌝
                      ∨ ⌜λ s, s.(thpc) th1 = w4⌝)).
Proof.
    rewrite /spec. tla_clear ⌜init⌝. tla_clear OBFair0.
    apply wf1.
    - intros. unfold next in H0. destruct H0 as [H0 | [H0 | H0]].
      + repeat (intros; simp; unseal).
      + destruct H0. destruct x.
        * repeat (intros; simp; unseal).
        * unfold pnext in H0.
          destruct (s .(thflag) th0) eqn:H2.
          -- simp. right. left. trivial.
          -- simp. do 2 right. trivial.
      + repeat (intros; simp; unseal).
    - repeat (intros; simp; unseal).
    - intros s H. destruct (s .(thflag) th0) eqn:H2.
       + exists (s <| thpc ::= <[ th1 := w3 ]> |>).
         unfold pnext. right. left.
         unfold pc_w2. right. left. simp.
       + exists (s <| thpc ::= <[ th1 := w4 ]> |>).
         unfold pnext.  right. left.
         unfold pc_w2. right. right. simp.
Qed.

Theorem liveness_aux4d :
    spec ⊢  (⌜λ s, s.(thpc) th1 = wait⌝
                 ~~> ⌜λ s, s.(thpc) th1 = w2⌝).
Proof.
    rewrite /spec. tla_clear ⌜init⌝. tla_clear OBFair0.
    apply wf1.
    - repeat (intros; simp; unseal).
    - repeat (intros; simp; unseal).
    - intros s H. exists (s <| thpc ::= <[ th1 := w2 ]> |>
                            <| thflag ::= <[ th1 := true]> |>).
      unfold pnext. left. simp.
Qed.

End onebit.