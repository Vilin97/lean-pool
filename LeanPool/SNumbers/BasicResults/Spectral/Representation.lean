/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import LeanPool.SNumbers.SNumbers.Approximation
import LeanPool.SNumbers.BasicResults.Spectral.RealProjection

/-!
# The spectral projection of `S*S` and the lower-bound subspace

*Why this file is needed:* it is the capstone of the `BasicResults.Spectral` subpackage — the
single spectral-theory input that the `s`-number uniqueness theorem consumes for **arbitrary
bounded** operators. It assembles the per-field constructions into one uniform statement and
derives the geometric fact the factorisation needs.

## What it provides

* `SpectralRepresentation.exists_spectral_projection` — for **every** `RCLike` field `𝕜` and a
  bounded `S : H₁ →L[𝕜] H₂`, the spectral projection `E = E_{[c²,∞)}(S*S)` with its two
  operator-norm bounds:
  * `c · ‖E x‖ ≤ ‖S (E x)‖` (on `ran E`, `S` is bounded below by `c`);
  * `‖S ∘ (1 - E)‖ ≤ c` (on the complement, `S` is bounded above by `c`).

  It is proved **uniformly over `RCLike`** by realification: view `H₁, H₂` as real Hilbert spaces,
  apply the real spectral projection (`exists_spectral_projection_real`, itself built by
  complexification), and lift the result back to a `𝕜`-linear operator — it *is* `𝕜`-linear
  because it commutes with scalar multiplication. This avoids any case split on `𝕜 = ℝ`/`ℂ` (which
  Lean cannot do) and any spectral hypothesis on downstream theorems.

* `SpectralRepresentation.exists_lowerBound_subspace` — **(★)**: for `0 ≤ c < aₙ(S)` there is an
  `(n+1)`-dimensional subspace `M ⊆ H₁` with `‖S x‖ ≥ c ‖x‖` on `M`. The range of `E` has dimension
  `≥ n+1` (else `S∘E` is rank `≤ n` with `‖S - S∘E‖ ≤ c`, contradicting `aₙ(S) > c`), and `S` is
  bounded below by `c` there. This is the geometric heart of `SVD.exists_scalar_factorisation`.
-/

open ContinuousLinearMap Complexification RCLike

universe u

namespace SpectralRepresentation

variable {𝕜 : Type u} [RCLike 𝕜]
variable {H₁ H₂ : Type u}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]

/-- **Spectral projection of `S*S`, uniformly over any `RCLike` field.** Realify `H₁, H₂` to real
Hilbert spaces, take the real spectral projection, and lift it back to a `𝕜`-linear operator: the
lift is `𝕜`-linear because it commutes with scalar multiplication (the commutation conjunct of
`exists_spectral_projection_real`). The key sublemma `adjoint (S.restrictScalars ℝ) =
(adjoint S).restrictScalars ℝ` is proved inline. -/
theorem exists_spectral_projection (S : H₁ →L[𝕜] H₂) {c : ℝ} (hc0 : 0 ≤ c) :
    ∃ E : H₁ →L[𝕜] H₁,
      (∀ x : H₁, c * ‖E x‖ ≤ ‖S (E x)‖) ∧ ‖S.comp (1 - E)‖ ≤ c := by
  rcases subsingleton_or_nontrivial H₁ with hsub | hnt
  · have := hsub
    have hS0 : S = 0 := by ext x; rw [Subsingleton.elim x 0]; simp
    exact ⟨0, fun x => by simp, by rw [hS0]; simpa using hc0⟩
  · have := hnt
    let : InnerProductSpace ℝ H₁ := InnerProductSpace.rclikeToReal 𝕜 H₁
    let : InnerProductSpace ℝ H₂ := InnerProductSpace.rclikeToReal 𝕜 H₂
    -- The real adjoint of the realified operator equals the realified `𝕜`-adjoint.
    have hadj : adjoint (S.restrictScalars ℝ) = (adjoint S).restrictScalars ℝ := by
      symm
      rw [ContinuousLinearMap.eq_adjoint_iff]
      intro x y
      show re (inner 𝕜 (adjoint S x) y) = re (inner 𝕜 x (S y))
      rw [ContinuousLinearMap.adjoint_inner_left]
    obtain ⟨E₀, ha, hb, hcomm⟩ := exists_spectral_projection_real (S.restrictScalars ℝ) hc0
    -- `E₀` commutes with scalar multiplication, hence is `𝕜`-linear.
    have hsmul : ∀ (a : 𝕜) (x : H₁), E₀ (a • x) = a • E₀ x := by
      intro a x
      refine (hcomm ((a • (1 : H₁ →L[𝕜] H₁)).restrictScalars ℝ) (fun z => ?_) x).symm
      rw [hadj]
      simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.comp_apply,
        smul_apply, one_apply_eq_self, map_smul]
    let Eₖ : H₁ →ₗ[𝕜] H₁ :=
      { toFun := E₀, map_add' := E₀.map_add, map_smul' := fun a x => hsmul a x }
    refine ⟨Eₖ.mkContinuous ‖E₀‖ fun x => E₀.le_opNorm x, fun x => ha x, ?_⟩
    have hcomp : (S.comp (1 - Eₖ.mkContinuous ‖E₀‖ fun x => E₀.le_opNorm x)).restrictScalars ℝ
        = (S.restrictScalars ℝ).comp (1 - E₀) := by
      ext x; rfl
    rw [← ContinuousLinearMap.norm_restrictScalars (𝕜' := ℝ), hcomp]
    exact hb

/-- **(★) Lower-bound subspace.** For `0 ≤ c < aₙ(S)` there is an `(n+1)`-dimensional subspace
`M ⊆ H₁` on which `S` is bounded below by `c`. Take the spectral projection `E` of `S*S` at
threshold `c`; its range has dimension `≥ n+1`, and `S` is bounded below by `c` there. -/
theorem exists_lowerBound_subspace
    (S : H₁ →L[𝕜] H₂) (n : ℕ) {c : ℝ} (hc0 : 0 ≤ c)
    (hca : c < SNumbers.approximationNumber S n) :
    ∃ M : Submodule 𝕜 H₁, FiniteDimensional 𝕜 M ∧
      Module.finrank 𝕜 M = n + 1 ∧
      ∀ x ∈ M, c * ‖x‖ ≤ ‖S x‖ := by
  classical
  obtain ⟨E, hElb, hEub⟩ := exists_spectral_projection S hc0
  set V : Submodule 𝕜 H₁ := LinearMap.range (E : H₁ →ₗ[𝕜] H₁) with hVdef
  -- `S` is bounded below by `c` on the range of `E`: every element is `E y`.
  have hbound : ∀ x ∈ V, c * ‖x‖ ≤ ‖S x‖ := by
    intro x hx
    obtain ⟨y, hy⟩ := hx
    have hEy : E y = x := hy
    have := hElb y; rwa [hEy] at this
  -- `S ∘ (1 - E)` is small, so `S ∘ E` cannot be low rank.
  have hSE : S - S.comp E = S.comp (1 - E) := by
    ext x
    simp only [sub_apply, ContinuousLinearMap.comp_apply,
      one_apply_eq_self, map_sub]
  have hrank_se : (S.comp E).rank ≤ E.rank := by
    have h := ContinuousLinearMap.rank_comp_comp_le (ContinuousLinearMap.id 𝕜 H₁) E S
    rwa [ContinuousLinearMap.comp_id] at h
  -- The range of `E` has dimension at least `n + 1`.
  have hrankV : ((n + 1 : ℕ) : Cardinal) ≤ Module.rank 𝕜 V := by
    by_contra hcon
    rw [not_le] at hcon
    have hEn : E.rank ≤ (n : Cardinal) := by
      apply Order.lt_succ_iff.mp
      have hcast : ((n + 1 : ℕ) : Cardinal) = (n : Cardinal) + 1 := by push_cast; ring
      rw [Cardinal.succ_natCast, ← hcast]
      exact hcon
    have hbad : SNumbers.approximationNumber S n ≤ c :=
      le_trans (SNumbers.approximationNumber_le_norm_sub (le_trans hrank_se hEn))
        (by rw [hSE]; exact hEub)
    exact absurd hca (not_lt.mpr hbad)
  -- Extract `n + 1` independent vectors of `V`; their span is the subspace `M`.
  obtain ⟨v, hv⟩ := Module.le_rank_iff.mp hrankV
  set w : Fin (n + 1) → H₁ := fun i => (v i : H₁) with hwdef
  have hw : LinearIndependent 𝕜 w := hv.map' V.subtype (Submodule.ker_subtype V)
  refine ⟨Submodule.span 𝕜 (Set.range w),
    FiniteDimensional.span_of_finite 𝕜 (Set.finite_range w), ?_, ?_⟩
  · rw [finrank_span_eq_card hw, Fintype.card_fin]
  · intro x hx
    refine hbound x ?_
    refine (Submodule.span_le.mpr ?_) hx
    rintro _ ⟨i, rfl⟩
    exact (v i).2

end SpectralRepresentation

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
