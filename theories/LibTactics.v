From Corelib Require Export Equivalence Program.Tactics.

Module Program_Equality.

Axiom UIP_refl : forall (U : Type) (x : U) (p : x = x), p = eq_refl.
Axiom UIP : forall (U : Type) (x y : U) (p1 p2 : x = y), p1 = p2.

Ltac elim_eq_rect :=
  match goal with
    | [ |- ?t ] =>
      match t with
        | context [ @eq_rect _ _ _ _ _ ?p ] =>
          let P := fresh "P" in
            set (P := p); simpl in P ;
              ((case P ; clear P) || (clearbody P; rewrite (UIP_refl _ _ P); clear P))
        | context [ @eq_rect _ _ _ _ _ ?p _ ] =>
          let P := fresh "P" in
            set (P := p); simpl in P ;
              ((case P ; clear P) || (clearbody P; rewrite (UIP_refl _ _ P); clear P))
      end
  end.

Ltac simpl_uip :=
  match goal with
    [ H : ?X = ?X |- _ ] => rewrite (UIP_refl _ _ H) in *; clear H
  end.

Ltac abstract_eq_hyp H' p :=
  let ty := type of p in
  let tyred := eval simpl in ty in
    match tyred with
      ?X = ?Y =>
      match goal with
        | [ H : X = Y |- _ ] => fail 1
        | _ => set (H':=p) ; try (change p with H') ; clearbody H' ; simpl in H'
      end
    end.

Ltac on_coerce_proof tac T :=
  match T with
    | context [ eq_rect _ _ _ _ ?p ] => tac p
  end.

Ltac on_coerce_proof_gl tac :=
  match goal with
    [ |- ?T ] => on_coerce_proof tac T
  end.

Ltac abstract_eq_proof := on_coerce_proof_gl ltac:(fun p => let H := fresh "eqH" in abstract_eq_hyp H p).

Ltac abstract_eq_proofs := repeat abstract_eq_proof.

Ltac pi_eq_proof_hyp p :=
  let ty := type of p in
  let tyred := eval simpl in ty in
  match tyred with
    ?X = ?Y =>
    match goal with
      | [ H : X = Y |- _ ] =>
        match p with
          | H => fail 2
          | _ => rewrite (UIP _ X Y p H)
        end
      | _ => fail " No hypothesis with same type "
    end
  end.

Ltac pi_eq_proof := on_coerce_proof_gl pi_eq_proof_hyp.

Ltac pi_eq_proofs := repeat pi_eq_proof.

Ltac clear_eq_proofs :=
  abstract_eq_proofs ; pi_eq_proofs.

Ltac rewrite_refl_id := autorewrite with refl_id.

Ltac clear_eq_ctx :=
  rewrite_refl_id ; clear_eq_proofs.

Ltac simpl_eqs :=
  repeat (elim_eq_rect ; simpl ; clear_eq_ctx).

Ltac clear_refl_eq :=
  match goal with [ H : ?X = ?X |- _ ] => clear H end.
Ltac clear_refl_eqs := repeat clear_refl_eq.

Ltac simplify_eqs :=
  simpl ; simpl_eqs ; clear_eq_ctx ; clear_refl_eqs ;
    try subst ; simpl ; repeat simpl_uip ; rewrite_refl_id.

End Program_Equality.

Open Scope predicate_scope.

Create HintDb mctt discriminated.

(** Transparency setting for generalized rewriting *)
#[export]
Typeclasses Transparent arrows.

(** Destruct existential quantification but keeps the name *)
Ltac deex_once_in H :=
  match type of H with
    | exists (name:_), _ =>
      let name' := fresh name in
      destruct H as [name' H]
    end.

Ltac deex_in H :=
  repeat deex_once_in H.

Ltac deex_once :=
  match goal with
    | [ H: exists (name:_), _ |- _ ] => deex_once_in H
    end.

Ltac deex := repeat deex_once.

(** *** Generalization of Variables *)

Tactic Notation "gen" ident(x) := generalize dependent x.
Tactic Notation "gen" ident(x) ident(y) := gen x; gen y.
Tactic Notation "gen" ident(x) ident(y) ident(z) := gen x y; gen z.
Tactic Notation "gen" ident(x) ident(y) ident(z) ident(w) := gen x y z; gen w.

(** *** Marking-based Tactics *)

Definition __mark__ (n : nat) A (a : A) : A := a.
Arguments __mark__ n {A} a : simpl never.

Ltac mark H :=
  let t := type of H in
  fold (__mark__ 0 t) in H.
Ltac unmark H := unfold __mark__ in H.

Ltac mark_all :=
  repeat match goal with [H: ?P |- _] =>
    try (match P with __mark__ _ _ => fail 2 end); mark H
  end.
Ltac unmark_all := unfold __mark__ in *.

Ltac mark_with H n :=
  let t := type of H in
  fold (__mark__ n t) in H.
Ltac mark_all_with n :=
  repeat match goal with [H: ?P |- _] =>
    try (match P with __mark__ _ _ => fail 2 end); mark_with H n
  end.
Ltac unmark_all_with n :=
  repeat match goal with [H: ?P |- _] =>
    match P with __mark__ ?n' _ => tryif unify n n' then unmark H else fail 1 end
  end.

Ltac on_all_marked_hyp tac :=
  repeat match goal with
    | [ H : __mark__ _ ?A |- _ ] => unmark H; tac H
    end.
Ltac on_all_marked_hyp_rev tac :=
  repeat match reverse goal with
    | [ H : __mark__ _ ?A |- _ ] => unmark H; tac H
    end.
Tactic Notation "on_all_marked_hyp:" tactic4(tac) := on_all_marked_hyp tac; unmark_all_with 0.
Tactic Notation "on_all_marked_hyp_rev:" tactic4(tac) := on_all_marked_hyp_rev tac; unmark_all_with 0.
Tactic Notation "on_all_hyp:" tactic4(tac) :=
  mark_all_with 0; (on_all_marked_hyp: tac).
Tactic Notation "on_all_hyp_rev:" tactic4(tac) :=
  mark_all_with 0; (on_all_marked_hyp_rev: tac).

(** *** Simple helper *)

Ltac destruct_logic :=
  destruct_one_pair
  || deex_once
  || match goal with
    | [ H : ?X \/ ?Y |- _ ] => destruct H
    | [ ev : { _ } + { _ } |- _ ] => destruct ev
    | [ ev : _ + { _ } |- _ ] => destruct ev
    | [ ev : _ + _ |- _ ] => destruct ev
    end.

Ltac destruct_all := repeat destruct_logic.

Ltac not_let_bind name :=
  match goal with
  | [x := _ |- _] =>
      lazymatch name with
      | x => fail 1
      | _ => fail
      end
  | _ => idtac
  end.

Ltac find_dup_hyp tac non :=
  match goal with
  | [ H : ?X, H' : ?X |- _ ] =>
    not_let_bind H;
    not_let_bind H';
    let T := type of X in
    unify T Prop;
    tac H H' X
  | _ => non
  end.

Ltac fail_at_if_dup n :=
  find_dup_hyp ltac:(fun H H' X => fail n "dup hypothesis" H "and" H' ":" X)
                      ltac:(idtac).

Ltac fail_if_dup := fail_at_if_dup ltac:(1).

Ltac clear_dups :=
  repeat find_dup_hyp ltac:(fun H H' _ => clear H || clear H')
                             ltac:(idtac).

Ltac directed tac :=
  let ng := numgoals in
  tac;
  let ng' := numgoals in
  guard ng' <= ng.

Tactic Notation "directed" tactic2(tac) := directed tac.

Ltac progressive_invert H :=
  (** We use dependent destruction as it is more general than inversion *)
  directed dependent destruction H.

#[local]
Ltac progressive_invert_once H n :=
  let T := type of H in
  lazymatch T with
  | __mark__ _ _ => fail
  | forall _, _ => fail
  | _ => idtac
  end;
  lazymatch type of T with
  | Prop => idtac
  | Type => idtac
  end;
  directed inversion H;
  Program_Equality.simplify_eqs;
  Program_Equality.clear_refl_eqs;
  clear_dups;
  try mark_with H n.

#[global]
Ltac progressive_inversion :=
  clear_dups;
  repeat match goal with
    | H : _ |- _ =>
        progressive_invert_once H 100
    end;
  unmark_all_with 100.

Ltac clean_replace_by exp0 exp1 tac :=
  tryif unify exp0 exp1
  then fail
  else
    (let H := fresh "H" in
     assert (exp0 = exp1) as H by ltac:(tac);
     subst;
     try rewrite <- H in *).

Tactic Notation "clean" "replace" uconstr(exp0) "with" uconstr(exp1) "by" tactic3(tac) := clean_replace_by exp0 exp1 tac.

#[global]
Ltac find_head t :=
  lazymatch t with
  | ?t' _ => find_head t'
  | _ => t
  end.

Ltac unify_by_head_of t head :=
  match t with
  | ?X _ _ _ _ _ _ _ _ _ _ _ _ => unify X head
  | ?X _ _ _ _ _ _ _ _ _ _ _ => unify X head
  | ?X _ _ _ _ _ _ _ _ _ _ => unify X head
  | ?X _ _ _ _ _ _ _ _ _ => unify X head
  | ?X _ _ _ _ _ _ _ _ => unify X head
  | ?X _ _ _ _ _ _ _ => unify X head
  | ?X _ _ _ _ _ _ => unify X head
  | ?X _ _ _ _ _ => unify X head
  | ?X _ _ _ _ => unify X head
  | ?X _ _ _ => unify X head
  | ?X _ _ => unify X head
  | ?X _ => unify X head
  | ?X => unify X head
  end.

Ltac match_by_head1 head tac :=
  match goal with
  | [ H : ?T |- _ ] => unify_by_head_of T head; tac H
  end.
Ltac match_by_head head tac := repeat (match_by_head1 head ltac:(fun H => tac H; try mark H)); unmark_all.

Ltac inversion_by_head head := match_by_head head ltac:(fun H => inversion H).
Ltac dir_inversion_by_head head := match_by_head head ltac:(fun H => directed inversion H).
Ltac inversion_clear_by_head head := match_by_head head ltac:(fun H => inversion_clear H).
Ltac dir_inversion_clear_by_head head := match_by_head head ltac:(fun H => directed inversion_clear H).
Ltac destruct_by_head head := match_by_head head ltac:(fun H => destruct H).
Ltac dir_destruct_by_head head := match_by_head head ltac:(fun H => directed destruct H).

(** *** McTT automation *)

Tactic Notation "mauto" :=
  eauto with mctt core.

Tactic Notation "mauto" int_or_var(pow) :=
  eauto pow with mctt core.

Tactic Notation "mauto" "using" uconstr(use) :=
  eauto using use with mctt core.

Tactic Notation "mauto" "using" uconstr(use1) "," uconstr(use2) :=
  eauto using use1, use2 with mctt core.

Tactic Notation "mauto" "using" uconstr(use1) "," uconstr(use2) "," uconstr(use3) :=
  eauto using use1, use2, use3 with mctt core.

Tactic Notation "mauto" "using" uconstr(use1) "," uconstr(use2) "," uconstr(use3) "," uconstr(use4) :=
  eauto using use1, use2, use3, use4 with mctt core.

Tactic Notation "mauto" int_or_var(pow) "using" uconstr(use) :=
  eauto pow using use with mctt core.

Tactic Notation "mauto" int_or_var(pow) "using" uconstr(use1) "," uconstr(use2) :=
  eauto pow using use1, use2 with mctt core.

Tactic Notation "mauto" int_or_var(pow) "using" uconstr(use1) "," uconstr(use2) "," uconstr(use3) :=
  eauto pow using use1, use2, use3 with mctt core.

Tactic Notation "mauto" int_or_var(pow) "using" uconstr(use1) "," uconstr(use2) "," uconstr(use3) "," uconstr(use4) :=
  eauto pow using use1, use2, use3, use4 with mctt core.

Ltac mautosolve_impl pow := unshelve solve [mauto pow]; solve [constructor].

Tactic Notation "mautosolve" := mautosolve_impl integer:(5).
Tactic Notation "mautosolve" int_or_var(pow) := mautosolve_impl pow.

(** Improve type class resolution for Equivalence and PER *)

#[export]
Hint Extern 1 => eassumption : typeclass_instances.

#[export]
Hint Extern 1 (@Reflexive _ (@predicate_equivalence _)) => simple apply @Equivalence_Reflexive : typeclass_instances.
#[export]
Hint Extern 1 (@Symmetric _ (@predicate_equivalence _)) => simple apply @Equivalence_Symmetric : typeclass_instances.
#[export]
Hint Extern 1 (@Transitive _ (@predicate_equivalence _)) => simple apply @Equivalence_Transitive : typeclass_instances.
#[export]
Hint Extern 1 (@Transitive _ (@predicate_implication _)) => simple apply @PreOrder_Transitive : typeclass_instances.
