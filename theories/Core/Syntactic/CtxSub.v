From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export System.
Import Syntax_Notations.

Lemma ctx_sub_refl : forall {Γ},
    {{ ⊢ Γ }} ->
    {{ ⊢ Γ ⊆ Γ }}.
Proof with mautosolve.
  induction 1...
Qed.

#[export]
Hint Resolve ctx_sub_refl : mctt.

  #[local]
  Ltac gen_ctxsub_helper_IH ctxsub_exp_helper ctxsub_exp_eq_helper ctxsub_sub_helper ctxsub_sub_eq_helper ctxsub_subtyp_helper H :=
  match type of H with
  | {{ ^?Γ ⊢ ^?M : ^?A }} => pose proof ctxsub_exp_helper _ _ _ H
  | {{ ^?Γ ⊢ ^?M ≈ ^?N : ^?A }} => pose proof ctxsub_exp_eq_helper _ _ _ _ H
  | {{ ^?Γ ⊢s ^?σ : ^?Δ }} => pose proof ctxsub_sub_helper _ _ _ H
  | {{ ^?Γ ⊢s ^?σ ≈ ^?τ : ^?Δ }} => pose proof ctxsub_sub_eq_helper _ _ _ _ H
  | {{ ^?Γ ⊢ ^?M ⊆ ^?M' }} => pose proof ctxsub_subtyp_helper _ _ _ H
  end.

  #[local]
  Lemma ctxsub_exp_helper : forall {Γ M A}, {{ Γ ⊢ M : A }} -> forall {Δ}, {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢ M : A }}
  with
  ctxsub_exp_eq_helper : forall {Γ M M' A}, {{ Γ ⊢ M ≈ M' : A }} -> forall {Δ}, {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢ M ≈ M' : A }}
  with
  ctxsub_sub_helper : forall {Γ Γ' σ}, {{ Γ ⊢s σ : Γ' }} -> forall {Δ}, {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢s σ : Γ' }}
  with
  ctxsub_sub_eq_helper : forall {Γ Γ' σ σ'}, {{ Γ ⊢s σ ≈ σ' : Γ' }} -> forall {Δ}, {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢s σ ≈ σ' : Γ' }}
  with
  ctxsub_subtyp_helper : forall {Γ M M'}, {{ Γ ⊢ M ⊆ M' }} -> forall {Δ}, {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢ M ⊆ M' }}.
  Proof with mautosolve.
    all: inversion_clear 1;
      (on_all_hyp: gen_ctxsub_helper_IH ctxsub_exp_helper ctxsub_exp_eq_helper ctxsub_sub_helper ctxsub_sub_eq_helper ctxsub_subtyp_helper);
      clear ctxsub_exp_helper ctxsub_exp_eq_helper ctxsub_sub_helper ctxsub_sub_eq_helper ctxsub_subtyp_helper;
      intros * HΓΔ; destruct (presup_ctx_sub HΓΔ); mauto 4;
      try (rename B into C); try (rename B' into C'); try (rename A0 into B); try (rename A' into B').
    (** ctxsub_exp_helper & ctxsub_exp_eq_helper recursion cases *)
    1,12-14: assert {{ ⊢ Δ, ℕ ⊆ Γ, ℕ }} by (econstructor; mautosolve);
    assert {{ Δ, ℕ ⊢ B : Type@i }} by eauto; econstructor...
    (** ctxsub_exp_helper & ctxsub_exp_eq_helper function cases *)
    1-3,11-15: assert {{ Δ ⊢ B : Type@i }} by eauto; assert {{ ⊢ Δ, B ⊆ Γ, B }} by mauto;
    try econstructor...
    (** equality type case *)
    6,15:idtac...

    (** ctxsub_exp_helper & ctxsub_exp_eq_helper variable cases *)
    5,16: assert (exists B, {{ #x : B ∈ Δ }} /\ {{ Δ ⊢ B ⊆ A }}); destruct_conjs; mautosolve 4.
    (** ctxsub_sub_helper & ctxsub_sub_eq_helper weakening cases *)
    16,17: inversion_clear HΓΔ; econstructor; mautosolve 4.

    (** eqrec related cases *)
    5,12-14: assert {{ ⊢ Δ, B ⊆ Γ, B }} by mauto;
      assert {{ Γ, B ⊢s Wk : Γ }} by mauto 3;
      assert {{ Γ, B ⊢ B[Wk] : Type@i }} by mauto 3;
      assert {{ Γ, B, B[Wk] ⊢s Wk : Γ, B }} by mauto 4;
      assert {{ Γ, B, B[Wk] ⊢s Wk∘Wk : Γ }} by mauto 3;
      assert {{ Δ, B ⊢s Wk : Δ }} by mauto 3;
      assert {{ Δ, B ⊢ B[Wk] : Type@i }} by mauto 3;
      assert {{ Δ, B, B[Wk] ⊢s Wk : Δ, B }} by mauto 4;
      assert {{ Δ, B, B[Wk] ⊢s Wk∘Wk : Δ }} by mauto 3;
      assert {{ Δ, B, B[Wk] ⊢ B[Wk∘Wk] : Type@i }} by mauto 3;
      assert {{ Δ, B, B[Wk] ⊢ B[Wk∘Wk] : Type@i }} by mauto 3;
      assert {{ ⊢ Δ, B, B[Wk] ⊆ Γ, B, B[Wk] }} by (econstructor; mauto 4);
      assert {{ Γ, B, B[Wk] ⊢ Eq B[Wk∘Wk] #1 #0 : Type@i }} by (econstructor; mauto 3; eapply wf_conv; mauto 4);
      assert {{ Δ, B, B[Wk] ⊢ Eq B[Wk∘Wk] #1 #0 : Type@i }} by (econstructor; mauto 3; eapply wf_conv; mauto 4);
      assert {{ ⊢ Δ, B, B[Wk], Eq B[Wk∘Wk] #1 #0 ⊆ Γ, B, B[Wk], Eq B[Wk∘Wk] #1 #0 }} by mauto 3;
      econstructor; mauto 2.

    (* sigma type case *)
    1-10:
      match goal with
      | _ : context [ {{{ ^?Γ , ^?A }}} ] , _ : {{ ⊢ ^?Δ ⊆ ^?Γ }} |- _ =>
        assert {{ ⊢ Δ, A ⊆ Γ, A }} by (econstructor; mautosolve 3)
      end; econstructor; mauto 3.

    - (** ctxsub_exp_eq_helper variable case *)
      inversion_clear HΓΔ as [|Δ0 ? ? C'].
      assert (exists D, {{ #x : D ∈ Δ0 }} /\ {{ Δ0 ⊢ D ⊆ B }}) as [D [i0 ?]] by mauto.
      destruct_conjs.
      assert {{ ⊢ Δ0, C' }} by mauto.
      assert {{ Δ0, C' ⊢ D[Wk] ⊆ B[Wk] }}...
    - eapply wf_subtyp_pi with (i := i); firstorder mauto 4.
    - eapply wf_subtyp_sigma with (i := i); firstorder mauto 4.
    all: idtac "START!".
    Time Guarded.
  Abort.

