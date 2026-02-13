From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Import Definitions.
Import Syntax_Notations.

(** ** Basic Context Properties *)

Lemma ctx_lookup_lt : forall {Γ A x},
    {{ #x : A ∈ Γ }} ->
    x < length Γ.
Proof.
Admitted.

#[export]
Hint Resolve ctx_lookup_lt : mctt.

Lemma functional_ctx_lookup : forall {Γ A A' x},
    {{ #x : A ∈ Γ }} ->
    {{ #x : A' ∈ Γ }} ->
    A = A'.
Proof.
Admitted.

Lemma ctx_decomp : forall {Γ A}, {{ ⊢ Γ, A }} -> {{ ⊢ Γ }} /\ exists i, {{ Γ ⊢ A : Type@i }}.
Proof.
Admitted.

#[export]
Hint Resolve ctx_decomp : mctt.

Corollary ctx_decomp_left : forall {Γ A}, {{ ⊢ Γ , A }} -> {{ ⊢ Γ }}.
Proof.
Admitted.

Corollary ctx_decomp_right : forall {Γ A}, {{ ⊢ Γ, A }} -> exists i, {{ Γ ⊢ A : Type@i }}.
Proof.
Admitted.

#[export]
Hint Resolve ctx_decomp_left ctx_decomp_right : mctt.

(** ** Core Presuppositions *)

(** *** Context Presuppositions *)

Lemma presup_ctx_eq : forall {Γ Δ}, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Γ }} /\ {{ ⊢ Δ }}.
Proof.
Admitted.

Corollary presup_ctx_eq_left : forall {Γ Δ}, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Γ }}.
Proof.
Admitted.

Corollary presup_ctx_eq_right : forall {Γ Δ}, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Δ }}.
Proof.
Admitted.

#[export]
Hint Resolve presup_ctx_eq presup_ctx_eq_left presup_ctx_eq_right : mctt.

Lemma presup_sub : forall {Γ Δ σ}, {{ Γ ⊢s σ : Δ }} -> {{ ⊢ Γ }} /\ {{ ⊢ Δ }}.
Proof.
Admitted.

Corollary presup_sub_left : forall {Γ Δ σ}, {{ Γ ⊢s σ : Δ }} -> {{ ⊢ Γ }}.
Proof.
Admitted.

Corollary presup_sub_right : forall {Γ Δ σ}, {{ Γ ⊢s σ : Δ }} -> {{ ⊢ Δ }}.
Proof.
Admitted.

#[export]
Hint Resolve presup_sub presup_sub_left presup_sub_right : mctt.

(** With [presup_sub], we can prove similar for [exp]. *)

Lemma presup_exp_ctx : forall {Γ M A}, {{ Γ ⊢ M : A }} -> {{ ⊢ Γ }}.
Proof.
Admitted.

#[export]
Hint Resolve presup_exp_ctx : mctt.

(** and other presuppositions about context well-formedness. *)

Lemma presup_sub_eq_ctx : forall {Γ Δ σ σ'}, {{ Γ ⊢s σ ≈ σ' : Δ }} -> {{ ⊢ Γ }} /\ {{ ⊢ Δ }}.
Proof.
Admitted.

Corollary presup_sub_eq_ctx_left : forall {Γ Δ σ σ'}, {{ Γ ⊢s σ ≈ σ' : Δ }} -> {{ ⊢ Γ }}.
Proof.
Admitted.

Corollary presup_sub_eq_ctx_right : forall {Γ Δ σ σ'}, {{ Γ ⊢s σ ≈ σ' : Δ }} -> {{ ⊢ Δ }}.
Proof.
Admitted.

#[export]
Hint Resolve presup_sub_eq_ctx presup_sub_eq_ctx_left presup_sub_eq_ctx_right : mctt.

Lemma presup_exp_eq_ctx : forall {Γ M M' A}, {{ Γ ⊢ M ≈ M' : A }} -> {{ ⊢ Γ }}.
Proof.
Admitted.

#[export]
Hint Resolve presup_exp_eq_ctx : mctt.

(** *** Immediate Results of Context Presuppositions *)

(** Recover some rules we had before adding subtyping.
    Rest are recovered after presupposition lemmas (in SystemOpt). *)

Lemma wf_cumu : forall Γ A i,
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ A : Type@(S i) }}.
Proof.
Admitted.

Lemma wf_exp_eq_cumu : forall Γ A A' i,
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊢ A ≈ A' : Type@(S i) }}.
Proof.
Admitted.

#[export]
Hint Resolve wf_cumu wf_exp_eq_cumu : mctt.

Lemma wf_ctx_sub_refl : forall Γ Δ,
    {{ ⊢ Γ ≈ Δ }} ->
    {{ ⊢ Γ ⊆ Δ }}.
Proof.
Admitted.

#[export]
Hint Resolve wf_ctx_sub_refl : mctt.

Lemma wf_conv : forall Γ M A i A',
    {{ Γ ⊢ M : A }} ->
    (** The next argument will be removed in SystemOpt *)
    {{ Γ ⊢ A' : Type@i }} ->
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊢ M : A' }}.
Proof.
Admitted.

#[export]
Hint Resolve wf_conv : mctt.

Lemma wf_sub_conv : forall Γ σ Δ Δ',
  {{ Γ ⊢s σ : Δ }} ->
  {{ ⊢ Δ ≈ Δ' }} ->
  {{ Γ ⊢s σ : Δ' }}.
Proof.
Admitted.

#[export]
Hint Resolve wf_sub_conv : mctt.

Lemma wf_exp_eq_conv : forall Γ M M' A A' i,
   {{ Γ ⊢ M ≈ M' : A }} ->
   (** The next argument will be removed in SystemOpt *)
   {{ Γ ⊢ A' : Type@i }} ->
   {{ Γ ⊢ A ≈ A' : Type@i }} ->
   {{ Γ ⊢ M ≈ M' : A' }}.
Proof.
Admitted.

#[export]
Hint Resolve wf_exp_eq_conv : mctt.

Lemma wf_sub_eq_conv : forall Γ σ σ' Δ Δ',
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ ⊢ Δ ≈ Δ' }} ->
    {{ Γ ⊢s σ ≈ σ' : Δ' }}.
Proof.
Admitted.

#[export]
Hint Resolve wf_sub_eq_conv : mctt.

(** We can prove some additional lemmas for type presuppositions as well. *)

Lemma lift_exp_ge : forall {Γ A n m},
    n <= m ->
    {{ Γ ⊢ A : Type@n }} ->
    {{ Γ ⊢ A : Type@m }}.
Proof.
Admitted.

#[export]
Hint Resolve lift_exp_ge : mctt.

Corollary lift_exp_max_left : forall {Γ A n} m,
    {{ Γ ⊢ A : Type@n }} ->
    {{ Γ ⊢ A : Type@(max n m) }}.
Proof.
Admitted.

Corollary lift_exp_max_right : forall {Γ A} n {m},
    {{ Γ ⊢ A : Type@m }} ->
    {{ Γ ⊢ A : Type@(max n m) }}.
Proof.
Admitted.

Lemma lift_exp_eq_ge : forall {Γ A A' n m},
    n <= m ->
    {{ Γ ⊢ A ≈ A': Type@n }} ->
    {{ Γ ⊢ A ≈ A' : Type@m }}.
Proof.
Admitted.

#[export]
Hint Resolve lift_exp_eq_ge : mctt.

Corollary lift_exp_eq_max_left : forall {Γ A A' n} m,
    {{ Γ ⊢ A ≈ A' : Type@n }} ->
    {{ Γ ⊢ A ≈ A' : Type@(max n m) }}.
Proof.
Admitted.

Corollary lift_exp_eq_max_right : forall {Γ A A'} n {m},
    {{ Γ ⊢ A ≈ A' : Type@m }} ->
    {{ Γ ⊢ A ≈ A' : Type@(max n m) }}.
Proof.
Admitted.

(** *** Additional Lemmas for Syntactic PERs *)

Lemma exp_eq_refl : forall {Γ M A},
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ M ≈ M : A }}.
Proof.
Admitted.

#[export]
Hint Resolve exp_eq_refl : mctt.

Lemma exp_eq_trans_typ_max : forall {Γ i i' A A' A''},
    {{ Γ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊢ A' ≈ A'' : Type@i' }} ->
    {{ Γ ⊢ A ≈ A'' : Type@(max i i') }}.
Proof.
Admitted.

#[export]
Hint Resolve exp_eq_trans_typ_max : mctt.

Lemma sub_eq_refl : forall {Γ σ Δ},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢s σ ≈ σ : Δ }}.
Proof.
Admitted.

#[export]
Hint Resolve sub_eq_refl : mctt.

Lemma ctx_eq_refl : forall {Γ},
    {{ ⊢ Γ }} ->
    {{ ⊢ Γ ≈ Γ }}.
Proof.
Admitted.

#[export]
Hint Resolve ctx_eq_refl : mctt.

(** *** Lemmas for [exp] of [{{{ Type@i }}}] *)

Lemma exp_sub_typ : forall {Δ Γ A σ i},
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ A[σ] : Type@i }}.
Proof.
Admitted.

#[export]
Hint Resolve exp_sub_typ : mctt.

Lemma presup_ctx_lookup_typ : forall {Γ A x},
    {{ ⊢ Γ }} ->
    {{ #x : A ∈ Γ }} ->
    exists i, {{ Γ ⊢ A : Type@i }}.
Proof.
Admitted.

#[export]
Hint Resolve presup_ctx_lookup_typ : mctt.

Lemma exp_eq_sub_cong_typ1 : forall {Δ Γ A A' σ i},
    {{ Δ ⊢ A ≈ A' : Type@i }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ A[σ] ≈ A'[σ] : Type@i }}.
Proof.
Admitted.

Lemma exp_eq_sub_cong_typ2' : forall {Δ Γ A σ τ i},
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢s σ ≈ τ : Δ }} ->
    {{ Γ ⊢ A[σ] ≈ A[τ] : Type@i }}.
Proof.
Admitted.

Lemma exp_eq_sub_compose_typ : forall {Ψ Δ Γ A σ τ i},
    {{ Ψ ⊢ A : Type@i }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢ A[σ][τ] ≈ A[σ∘τ] : Type@i }}.
Proof.
Admitted.

#[export]
Hint Resolve exp_eq_sub_cong_typ1 exp_eq_sub_cong_typ2' exp_eq_sub_compose_typ : mctt.

Lemma exp_eq_sub_compose_weaken_extend_typ : forall {Γ σ Δ i A j B M},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Δ ⊢ B : Type@j }} ->
    {{ Γ ⊢ M : B[σ] }} ->
    {{ Γ ⊢ A[Wk][σ,,M] ≈ A[σ] : Type@i }}.
Proof.
Admitted.

#[export]
Hint Resolve exp_eq_sub_compose_weaken_extend_typ : mctt.

Lemma exp_eq_sub_compose_weaken_id_extend_typ : forall {Γ i A j B M},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ B : Type@j }} ->
    {{ Γ ⊢ M : B }} ->
    {{ Γ ⊢ A[Wk][Id,,M] ≈ A : Type@i }}.
Proof.
Admitted.

#[export]
Hint Resolve exp_eq_sub_compose_weaken_id_extend_typ : mctt.

Lemma exp_eq_sub_compose_double_weaken_double_extend_typ : forall {Γ σ Δ i A j B M k C N},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Δ ⊢ B : Type@j }} ->
    {{ Γ ⊢ M : B[σ] }} ->
    {{ Δ, B ⊢ C : Type@k }} ->
    {{ Γ ⊢ N : C[σ,,M] }} ->
    {{ Γ ⊢ A[Wk∘Wk][(σ,,M),,N] ≈ A[σ] : Type@i }}.
Proof.
Admitted.

#[export]
Hint Resolve exp_eq_sub_compose_double_weaken_double_extend_typ : mctt.

Lemma exp_eq_sub_compose_double_weaken_id_double_extend_typ : forall {Γ i A j B M k C N},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ B : Type@j }} ->
    {{ Γ ⊢ M : B }} ->
    {{ Γ, B ⊢ C : Type@k }} ->
    {{ Γ ⊢ N : C[Id,,M] }} ->
    {{ Γ ⊢ A[Wk∘Wk][(Id,,M),,N] ≈ A : Type@i }}.
Proof.
Admitted.

#[export]
Hint Resolve exp_eq_sub_compose_double_weaken_id_double_extend_typ : mctt.

Lemma exp_eq_typ_sub_sub : forall {Γ Δ Ψ σ τ i},
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢ Type@i[σ][τ] ≈ Type@i : Type@(S i) }}.
Proof.
Admitted.

#[export]
Hint Resolve exp_eq_typ_sub_sub : mctt.
#[export]
Hint Rewrite -> @exp_eq_sub_compose_typ @exp_eq_typ_sub_sub using mauto 4 : mctt.

Lemma vlookup_0_typ : forall {Γ i},
    {{ ⊢ Γ }} ->
    {{ Γ, Type@i ⊢ #0 : Type@i }}.
Proof.
Admitted.

Lemma vlookup_1_typ : forall {Γ i A j},
    {{ Γ, Type@i ⊢ A : Type@j }} ->
    {{ (Γ, Type@i), A ⊢ #1 : Type@i }}.
Proof.
Admitted.

#[export]
Hint Resolve vlookup_0_typ vlookup_1_typ : mctt.

Lemma exp_sub_typ_helper : forall {Γ σ Δ M i},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : Type@i }} ->
    {{ Γ ⊢ M : Type@i[σ] }}.
Proof.
Admitted.

#[export]
Hint Resolve exp_sub_typ_helper : mctt.

Lemma exp_eq_var_0_sub_typ : forall {Γ σ Δ M i},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : Type@i }} ->
    {{ Γ ⊢ #0[σ,,M] ≈ M : Type@i }}.
Proof.
Admitted.

Lemma exp_eq_var_1_sub_typ : forall {Γ σ Δ A i M j},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ #0 : Type@j[Wk] ∈ Δ }} ->
    {{ Γ ⊢ #1[σ,,M] ≈ #0[σ] : Type@j }}.
Proof.
Admitted.

#[export]
Hint Resolve exp_eq_var_0_sub_typ exp_eq_var_1_sub_typ : mctt.
#[export]
Hint Rewrite -> @exp_eq_var_0_sub_typ @exp_eq_var_1_sub_typ : mctt.

Lemma exp_eq_var_0_weaken_typ : forall {Γ A i},
    {{ ⊢ Γ, A }} ->
    {{ #0 : Type@i[Wk] ∈ Γ }} ->
    {{ Γ, A ⊢ #0[Wk] ≈ #1 : Type@i }}.
Proof.
Admitted.

#[export]
Hint Resolve exp_eq_var_0_weaken_typ : mctt.

Lemma sub_extend_typ : forall {Γ σ Δ M i},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : Type@i }} ->
    {{ Γ ⊢s σ,,M : Δ, Type@i }}.
Proof.
Admitted.

#[export]
Hint Resolve sub_extend_typ : mctt.

Lemma sub_eq_extend_cong_typ : forall {Γ σ σ' Δ M M' i},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ Γ ⊢ M ≈ M' : Type@i }} ->
    {{ Γ ⊢s σ,,M ≈ σ',,M' : Δ, Type@i }}.
Proof.
Admitted.

Lemma sub_eq_extend_compose_typ : forall {Γ τ Γ' σ Γ'' A i M j},
    {{ Γ' ⊢s σ : Γ'' }} ->
    {{ Γ'' ⊢ A : Type@i }} ->
    {{ Γ' ⊢ M : Type@j }} ->
    {{ Γ ⊢s τ : Γ' }} ->
    {{ Γ ⊢s (σ,,M)∘τ ≈ (σ∘τ),,M[τ] : Γ'', Type@j }}.
Proof.
Admitted.

Lemma sub_eq_p_extend_typ : forall {Γ σ Γ' M i},
    {{ Γ' ⊢s σ : Γ }} ->
    {{ Γ' ⊢ M : Type@i }} ->
    {{ Γ' ⊢s Wk∘(σ,,M) ≈ σ : Γ }}.
Proof.
Admitted.

#[export]
Hint Resolve sub_eq_extend_cong_typ sub_eq_extend_compose_typ sub_eq_p_extend_typ : mctt.


Lemma exp_eq_sub_sub_compose_cong_typ : forall {Γ Δ Δ' Ψ σ τ σ' τ' A i},
    {{ Ψ ⊢ A : Type@i }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Δ' ⊢s σ' : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢s τ' : Δ' }} ->
    {{ Γ ⊢s σ∘τ ≈ σ'∘τ' : Ψ }} ->
    {{ Γ ⊢ A[σ][τ] ≈ A[σ'][τ'] : Type@i }}.
Proof.
Admitted.

#[export]
Hint Resolve exp_eq_sub_sub_compose_cong_typ : mctt.

(** *** Lemmas for [exp] of [{{{ ℕ }}}] *)

Lemma exp_sub_nat : forall {Δ Γ M σ},
    {{ Δ ⊢ M : ℕ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M[σ] : ℕ }}.
Proof.
Admitted.

#[export]
Hint Resolve exp_sub_nat : mctt.

Lemma exp_eq_sub_cong_nat1 : forall {Δ Γ M M' σ},
    {{ Δ ⊢ M ≈ M' : ℕ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M[σ] ≈ M'[σ] : ℕ }}.
Proof.
Admitted.

Lemma exp_eq_sub_cong_nat2 : forall {Δ Γ M σ τ},
    {{ Δ ⊢ M : ℕ }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢s σ ≈ τ : Δ }} ->
    {{ Γ ⊢ M[σ] ≈ M[τ] : ℕ }}.
Proof.
Admitted.

Lemma exp_eq_sub_compose_nat : forall {Ψ Δ Γ M σ τ},
    {{ Ψ ⊢ M : ℕ }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢ M[σ][τ] ≈ M[σ∘τ] : ℕ }}.
Proof.
Admitted.

#[export]
Hint Resolve exp_sub_nat exp_eq_sub_cong_nat1 exp_eq_sub_cong_nat2 exp_eq_sub_compose_nat : mctt.

Lemma exp_eq_nat_sub_sub : forall {Γ Δ Ψ σ τ},
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢ ℕ[σ][τ] ≈ ℕ : Type@0 }}.
Proof.
Admitted.

#[export]
Hint Resolve exp_eq_nat_sub_sub : mctt.

Lemma exp_eq_nat_sub_sub_to_nat_sub : forall {Γ Δ Ψ Ψ' σ τ σ'},
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢s σ' : Ψ' }} ->
    {{ Γ ⊢ ℕ[σ][τ] ≈ ℕ[σ'] : Type@0 }}.
Proof.
Admitted.

#[export]
Hint Resolve exp_eq_nat_sub_sub_to_nat_sub : mctt.

Lemma exp_eq_sub_compose_weaken_extend_nat : forall {Γ σ Δ M i B N},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ M : ℕ }} ->
    {{ Δ ⊢ B : Type@i }} ->
    {{ Γ ⊢ N : B[σ] }} ->
    {{ Γ ⊢ M[Wk][σ,,N] ≈ M[σ] : ℕ }}.
Proof.
Admitted.

#[export]
Hint Resolve exp_eq_sub_compose_weaken_extend_nat : mctt.

Lemma exp_eq_sub_compose_weaken_id_extend_nat : forall {Γ M i B N},
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ B : Type@i }} ->
    {{ Γ ⊢ N : B }} ->
    {{ Γ ⊢ M[Wk][Id,,N] ≈ M : ℕ }}.
Proof.
Admitted.

#[export]
Hint Resolve exp_eq_sub_compose_weaken_id_extend_nat : mctt.

Lemma exp_eq_sub_compose_double_weaken_double_extend_nat : forall {Γ σ Δ M i B N j C L},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ M : ℕ }} ->
    {{ Δ ⊢ B : Type@i }} ->
    {{ Γ ⊢ N : B[σ] }} ->
    {{ Δ, B ⊢ C : Type@j }} ->
    {{ Γ ⊢ L : C[σ,,N] }} ->
    {{ Γ ⊢ M[Wk∘Wk][(σ,,N),,L] ≈ M[σ] : ℕ }}.
Proof.
Admitted.

#[export]
Hint Resolve exp_eq_sub_compose_double_weaken_double_extend_nat : mctt.

Lemma exp_eq_sub_compose_double_weaken_id_double_extend_nat : forall {Γ M i B N j C L},
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ B : Type@i }} ->
    {{ Γ ⊢ N : B }} ->
    {{ Γ, B ⊢ C : Type@j }} ->
    {{ Γ ⊢ L : C[Id,,N] }} ->
    {{ Γ ⊢ M[Wk∘Wk][(Id,,N),,L] ≈ M : ℕ }}.
Proof.
Admitted.

#[export]
Hint Resolve exp_eq_sub_compose_double_weaken_id_double_extend_nat : mctt.

Lemma vlookup_0_nat : forall {Γ},
    {{ ⊢ Γ }} ->
    {{ Γ, ℕ ⊢ #0 : ℕ }}.
Proof.
Admitted.

Lemma vlookup_1_nat : forall {Γ A i},
    {{ Γ, ℕ ⊢ A : Type@i }} ->
    {{ (Γ, ℕ), A ⊢ #1 : ℕ }}.
Proof.
Admitted.

#[export]
Hint Resolve vlookup_0_nat vlookup_1_nat : mctt.

Lemma exp_sub_nat_helper : forall {Γ σ Δ M},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ M : ℕ[σ] }}.
Proof.
Admitted.

#[export]
Hint Resolve exp_sub_nat_helper : mctt.

Lemma exp_eq_var_0_sub_nat : forall {Γ σ Δ M},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ #0[σ,,M] ≈ M : ℕ }}.
Proof.
Admitted.

Lemma exp_eq_var_1_sub_nat : forall {Γ σ Δ A i M},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ #0 : ℕ[Wk] ∈ Δ }} ->
    {{ Γ ⊢ #1[σ,,M] ≈ #0[σ] : ℕ }}.
Proof.
Admitted.

#[export]
Hint Resolve exp_eq_var_0_sub_nat exp_eq_var_1_sub_nat : mctt.

Lemma exp_eq_var_0_weaken_nat : forall {Γ A},
    {{ ⊢ Γ, A }} ->
    {{ #0 : ℕ[Wk] ∈ Γ }} ->
    {{ Γ, A ⊢ #0[Wk] ≈ #1 : ℕ }}.
Proof.
Admitted.

#[export]
Hint Resolve exp_eq_var_0_weaken_nat : mctt.

Lemma sub_extend_nat : forall {Γ σ Δ M},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢s σ,,M : Δ, ℕ }}.
Proof.
Admitted.

#[export]
Hint Resolve sub_extend_nat : mctt.

Lemma sub_eq_extend_cong_nat : forall {Γ σ σ' Δ M M'},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢s σ ≈ σ' : Δ }} ->
    {{ Γ ⊢ M ≈ M' : ℕ }} ->
    {{ Γ ⊢s σ,,M ≈ σ',,M' : Δ, ℕ }}.
Proof.
Admitted.

Lemma sub_eq_extend_compose_nat : forall {Γ τ Γ' σ Γ'' M},
    {{ Γ' ⊢s σ : Γ'' }} ->
    {{ Γ' ⊢ M : ℕ }} ->
    {{ Γ ⊢s τ : Γ' }} ->
    {{ Γ ⊢s (σ,,M)∘τ ≈ (σ∘τ),,M[τ] : Γ'', ℕ }}.
Proof.
Admitted.

Lemma sub_eq_p_extend_nat : forall {Γ σ Γ' M},
    {{ Γ' ⊢s σ : Γ }} ->
    {{ Γ' ⊢ M : ℕ }} ->
    {{ Γ' ⊢s Wk∘(σ,,M) ≈ σ : Γ }}.
Proof.
Admitted.

#[export]
Hint Resolve sub_eq_extend_cong_nat sub_eq_extend_compose_nat sub_eq_p_extend_nat : mctt.

Lemma exp_eq_sub_sub_compose_cong_nat : forall {Γ Δ Δ' Ψ σ τ σ' τ' M},
    {{ Ψ ⊢ M : ℕ }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Δ' ⊢s σ' : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢s τ' : Δ' }} ->
    {{ Γ ⊢s σ∘τ ≈ σ'∘τ' : Ψ }} ->
    {{ Γ ⊢ M[σ][τ] ≈ M[σ'][τ'] : ℕ }}.
Proof.
Admitted.

#[export]
Hint Resolve exp_eq_sub_sub_compose_cong_nat : mctt.

(** *** Other Tedious Lemmas *)

Lemma sub_eq_weaken_var0_id : forall {Γ A i},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ, A ⊢s Wk,,#0 ≈ Id : Γ, A }}.
Proof.
Admitted.

#[export]
Hint Resolve sub_eq_weaken_var0_id : mctt.
#[export]
Hint Rewrite -> @sub_eq_weaken_var0_id using mauto 4 : mctt.

Lemma exp_eq_sub_sub_compose_cong : forall {Γ Δ Δ' Ψ σ τ σ' τ' M A i},
    {{ Ψ ⊢ A : Type@i }} ->
    {{ Ψ ⊢ M : A }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Δ' ⊢s σ' : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ Γ ⊢s τ' : Δ' }} ->
    {{ Γ ⊢s σ∘τ ≈ σ'∘τ' : Ψ }} ->
    {{ Γ ⊢ M[σ][τ] ≈ M[σ'][τ'] : A[σ∘τ] }}.
Proof.
Admitted.

#[export]
Hint Resolve exp_eq_sub_sub_compose_cong : mctt.

Lemma ctxeq_ctx_lookup : forall {Γ Δ A x},
    {{ ⊢ Γ ≈ Δ }} ->
    {{ #x : A ∈ Γ }} ->
    exists B i,
      {{ #x : B ∈ Δ }} /\
        {{ Γ ⊢ A ≈ B : Type@i }} /\
        {{ Δ ⊢ A ≈ B : Type@i }}.
Proof.
Admitted.

#[export]
Hint Resolve ctxeq_ctx_lookup : mctt.

Lemma sub_id_on_typ : forall {Γ M A i},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢ M : A[Id] }}.
Proof.
Admitted.

#[export]
Hint Resolve sub_id_on_typ : mctt.

Lemma sub_id_extend : forall {Γ M A i},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢s Id,,M : Γ, A }}.
Proof.
Admitted.

#[export]
Hint Resolve sub_id_extend : mctt.

Lemma sub_eq_id_on_typ : forall {Γ M M' A i},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ Γ ⊢ M ≈ M' : A[Id] }}.
Proof.
Admitted.

#[export]
Hint Resolve sub_eq_id_on_typ : mctt.

Lemma sub_eq_id_extend_cong : forall {Γ M M' A i},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M ≈ M' : A }} ->
    {{ Γ ⊢s Id,,M ≈ Id,,M' : Γ, A }}.
Proof.
Admitted.

#[export]
Hint Resolve sub_eq_id_extend_cong : mctt.

Lemma sub_eq_p_id_extend : forall {Γ M A i},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢s Wk∘(Id,,M) ≈ Id : Γ }}.
Proof.
Admitted.

#[export]
Hint Resolve sub_eq_p_id_extend : mctt.
#[export]
Hint Rewrite -> @sub_eq_p_id_extend using mauto 4 : mctt.

Lemma sub_q : forall {Γ A i σ Δ},
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, A[σ] ⊢s q σ : Δ, A }}.
Proof.
Admitted.

Lemma sub_q_typ : forall {Γ σ Δ i},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, Type@i ⊢s q σ : Δ, Type@i }}.
Proof.
Admitted.

Lemma sub_q_nat : forall {Γ σ Δ},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, ℕ ⊢s q σ : Δ, ℕ }}.
Proof.
Admitted.

#[export]
Hint Resolve sub_q sub_q_typ sub_q_nat : mctt.

Lemma exp_eq_var_1_sub_q_sigma_nat : forall {Γ A i σ Δ},
    {{ Δ, ℕ ⊢ A : Type@i }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ (Γ, ℕ), A[q σ] ⊢ #1[q (q σ)] ≈ #1 : ℕ }}.
Proof.
Admitted.

#[export]
Hint Resolve exp_eq_var_1_sub_q_sigma_nat : mctt.

Lemma sub_id_extend_zero : forall {Γ},
    {{ ⊢ Γ }} ->
    {{ Γ ⊢s Id,,zero : Γ, ℕ }}.
Proof.
Admitted.

Lemma sub_weak_compose_weak_extend_succ_var_1 : forall {Γ A i},
    {{ Γ, ℕ ⊢ A : Type@i }} ->
    {{ (Γ, ℕ), A ⊢s Wk∘Wk,,succ #1 : Γ, ℕ }}.
Proof.
Admitted.

Lemma sub_eq_id_extend_nat_compose_sigma : forall {Γ M σ Δ},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ M : ℕ }} ->
    {{ Γ ⊢s (Id,,M)∘σ ≈ σ,,M[σ] : Δ, ℕ }}.
Proof.
Admitted.

Lemma sub_eq_id_extend_compose_sigma : forall {Γ M A σ Δ i},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Δ ⊢ A : Type@i }} ->
    {{ Δ ⊢ M : A }} ->
    {{ Γ ⊢s (Id,,M)∘σ ≈ σ,,M[σ] : Δ, A }}.
Proof.
Admitted.

#[export]
Hint Resolve sub_id_extend_zero sub_weak_compose_weak_extend_succ_var_1 sub_eq_id_extend_nat_compose_sigma sub_eq_id_extend_compose_sigma : mctt.

Lemma sub_eq_sigma_compose_weak_id_extend : forall {Γ M A i σ Δ},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢s (σ∘Wk)∘(Id,,M) ≈ σ : Δ }}.
Proof.
Admitted.

#[export]
Hint Resolve sub_eq_sigma_compose_weak_id_extend : mctt.

Lemma sub_eq_q_sigma_id_extend : forall {Γ M A i σ Δ},
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ M : A[σ] }} ->
    {{ Γ ⊢s q σ∘(Id,,M) ≈ σ,,M : Δ, A }}.
Proof.
Admitted.

#[export]
Hint Resolve sub_eq_q_sigma_id_extend : mctt.
#[export]
Hint Rewrite -> @sub_eq_q_sigma_id_extend using mauto 4 : mctt.

Lemma sub_eq_p_q_sigma : forall {Γ A i σ Δ},
    {{ Δ ⊢ A : Type@i }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, A[σ] ⊢s Wk∘q σ ≈ σ∘Wk : Δ }}.
Proof.
Admitted.

#[export]
Hint Resolve sub_eq_p_q_sigma : mctt.

Lemma sub_eq_p_q_sigma_nat : forall {Γ σ Δ},
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ, ℕ ⊢s Wk∘q σ ≈ σ∘Wk : Δ }}.
Proof.
Admitted.

#[export]
Hint Resolve sub_eq_p_q_sigma_nat : mctt.

Lemma sub_eq_p_p_q_q_sigma_nat : forall {Γ A i σ Δ},
    {{ Δ, ℕ ⊢ A : Type@i }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ (Γ, ℕ), A[q σ] ⊢s Wk∘(Wk∘q (q σ)) ≈ (σ∘Wk)∘Wk : Δ }}.
Proof.
Admitted.

#[export]
Hint Resolve sub_eq_p_p_q_q_sigma_nat : mctt.

Lemma sub_eq_q_sigma_compose_weak_weak_extend_succ_var_1 : forall {Γ A i σ Δ},
    {{ Δ, ℕ ⊢ A : Type@i }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ (Γ, ℕ), A[q σ] ⊢s q σ∘(Wk∘Wk,,succ #1) ≈ (Wk∘Wk,,succ #1)∘q (q σ) : Δ, ℕ }}.
Proof.
Admitted.

#[export]
Hint Resolve sub_eq_q_sigma_compose_weak_weak_extend_succ_var_1 : mctt.

(** *** Lemmas for [wf_subtyp] *)

Fact wf_subtyp_refl : forall {Γ A i},
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ A ⊆ A }}.
Proof.
Admitted.

#[export]
Hint Resolve wf_subtyp_refl : mctt.

Lemma wf_subtyp_ge : forall {Γ i j},
    {{ ⊢ Γ }} ->
    i <= j ->
    {{ Γ ⊢ Type@i ⊆ Type@j }}.
Proof.
Admitted.

#[export]
Hint Resolve wf_subtyp_ge : mctt.

Lemma wf_subtyp_sub : forall {Δ A A'},
    {{ Δ ⊢ A ⊆ A' }} ->
    forall Γ σ,
    {{ Γ ⊢s σ : Δ }} ->
    {{ Γ ⊢ A[σ] ⊆ A'[σ] }}.
Proof.
Admitted.

#[export]
Hint Resolve wf_subtyp_sub : mctt.

Lemma wf_subtyp_univ_weaken : forall {Γ i j A},
    {{ Γ ⊢ Type@i ⊆ Type@j }} ->
    {{ ⊢ Γ, A }} ->
    {{ Γ, A ⊢ Type@i ⊆ Type@j }}.
Proof.
Admitted.

Lemma ctx_sub_ctx_lookup : forall {Γ Δ},
    {{ ⊢ Δ ⊆ Γ }} ->
    forall {A x},
      {{ #x : A ∈ Γ }} ->
      exists B,
        {{ #x : B ∈ Δ }} /\
          {{ Δ ⊢ B ⊆ A }}.
Proof.
Admitted.

#[export]
Hint Resolve ctx_sub_ctx_lookup : mctt.

Lemma var_compose_subs : forall {Γ τ Δ σ Ψ i A x},
    {{ Ψ ⊢ A : Type@i }} ->
    {{ Δ ⊢s σ : Ψ }} ->
    {{ Γ ⊢s τ : Δ }} ->
    {{ #x : A[σ][τ] ∈ Γ }} ->
    {{ Γ ⊢ #x : A[σ∘τ] }}.
Proof.
Admitted.

#[export]
Hint Resolve var_compose_subs : mctt.

Lemma sub_lookup_var0 : forall Δ Γ σ M1 M2 B i,
    {{ Δ ⊢s σ : Γ }} ->
    {{ Γ ⊢ B : Type@i }} ->
    {{ Δ ⊢ M1 : B[σ] }} ->
    {{ Δ ⊢ M2 : B[σ] }} ->
    {{ Δ ⊢ #0[(σ,,M1),,M2] ≈ M2 : B[σ] }}.
Proof.
Admitted.

Lemma id_sub_lookup_var0 : forall Γ M1 M2 B i,
    {{ Γ ⊢ B : Type@i }} ->
    {{ Γ ⊢ M1 : B }} ->
    {{ Γ ⊢ M2 : B }} ->
    {{ Γ ⊢ #0[(Id,,M1),,M2] ≈ M2 : B }}.
Proof.
Admitted.

Lemma sub_lookup_var1 : forall Δ Γ σ M1 M2 B i,
    {{ Δ ⊢s σ : Γ }} ->
    {{ Γ ⊢ B : Type@i }} ->
    {{ Δ ⊢ M1 : B[σ] }} ->
    {{ Δ ⊢ M2 : B[σ] }} ->
    {{ Δ ⊢ #1[(σ,,M1),,M2] ≈ M1 : B[σ] }}.
Proof.
Admitted.

Lemma id_sub_lookup_var1 : forall Γ M1 M2 B i,
    {{ Γ ⊢ B : Type@i }} ->
    {{ Γ ⊢ M1 : B }} ->
    {{ Γ ⊢ M2 : B }} ->
    {{ Γ ⊢ #1[(Id,,M1),,M2] ≈ M1 : B }}.
Proof.
Admitted.

Lemma exp_eq_var_1_sub_q_sigma : forall {Γ A i B j σ Δ},
    {{ Δ ⊢ B : Type@j }} ->
    {{ Δ, B ⊢ A : Type@i }} ->
    {{ Γ ⊢s σ : Δ }} ->
    {{ (Γ, B[σ]), A[q σ] ⊢ #1[q (q σ)] ≈ #1 : B[σ][Wk∘Wk] }}.
Proof.
Admitted.

(** *** Type Presuppositions *)

Lemma presup_exp_typ : forall {Γ M A},
    {{ Γ ⊢ M : A }} ->
    exists i, {{ Γ ⊢ A : Type@i }}.
Proof.
Admitted.

Lemma presup_exp : forall {Γ M A},
    {{ Γ ⊢ M : A }} ->
    {{ ⊢ Γ }} /\ exists i, {{ Γ ⊢ A : Type@i }}.
Proof.
Admitted.
