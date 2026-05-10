/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import LeanPool.OSforGFF.GaussianField.SchwartzNuclear.SchwartzHermiteExpansion

/-!
# Nuclear Schauder Basis for S(ℝ, ℝ) — 1D Case

Assembles the proved Hermite function results into the three properties
needed for a `DyninMityaginSpace` instance:
1. **Expansion**: φ f = ∑' n, cₙ(f) · φ(ψₙ) for all CLFs φ
2. **Basis growth**: ‖ψₙ‖_{k,l} ≤ C · (1+n)^s
3. **Coefficient decay**: |cₙ(f)| · (1+n)^k ≤ C · ‖f‖_{q₁,q₂}

All three are proved from theorems in `HermiteFunctions.lean` and
`SchwartzHermiteExpansion.lean`. No axioms.
-/

open MeasureTheory Real SchwartzMap

noncomputable section

/-! ## Hermite Coefficient as a Continuous Linear Map

`hermiteCoeff1D` is linear (proved) and bounded by a Schwartz seminorm
(from the decay estimate at k=0), hence continuous.
-/

/-- The Hermite coefficient as a continuous linear map on Schwartz space. -/
def hermiteCoeff1DCLM (n : ℕ) : SchwartzMap ℝ ℝ →L[ℝ] ℝ where
  toLinearMap := {
    toFun := hermiteCoeff1D n
    map_add' := (hermiteCoeff1D_linear n).map_add
    map_smul' := (hermiteCoeff1D_linear n).map_smul
  }
  cont := by
    -- Continuity from the decay bound at k = 0:
    -- |cₙ(f)| ≤ C · sup-seminorm(f)
    obtain ⟨C, q, hC, hbound⟩ := hermiteCoeff1D_decay (0 : ℝ)
    -- At k=0: |cₙ(f)| * 1 ≤ C * sup-seminorm(f)
    have h0 : ∀ f, |hermiteCoeff1D n f| ≤
        C * (Finset.Iic q).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f := by
      intro f
      have := hbound f n
      simp only [rpow_zero, mul_one] at this
      exact this
    -- Use norm from the decay bound
    have key : ∀ f, ‖hermiteCoeff1D n f‖ ≤
        C * (Finset.Iic q).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f := by
      intro f
      calc ‖hermiteCoeff1D n f‖
          = |hermiteCoeff1D n f| := Real.norm_eq_abs _
        _ ≤ C * (Finset.Iic q).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f := h0 f
    -- Apply continuous_of_isBounded
    -- The linear map is: {toFun := hermiteCoeff1D n, ...}
    -- and we show it's bounded by Schwartz seminorms
    let lm : SchwartzMap ℝ ℝ →ₗ[ℝ] ℝ := {
      toFun := hermiteCoeff1D n
      map_add' := (hermiteCoeff1D_linear n).map_add
      map_smul' := (hermiteCoeff1D_linear n).map_smul
    }
    apply WithSeminorms.continuous_of_isBounded
      (schwartz_withSeminorms ℝ ℝ ℝ) (norm_withSeminorms ℝ ℝ) lm
    intro _
    use Finset.Iic q, ⟨C, le_of_lt hC⟩
    exact fun f => key f

@[simp] theorem hermiteCoeff1DCLM_apply (n : ℕ) (f : SchwartzMap ℝ ℝ) :
    hermiteCoeff1DCLM n f = hermiteCoeff1D n f := rfl

/-! ## Expansion Identity for Scalar CLFs

Specializing `schwartz_hermite_expansion_1D` to H = ℝ gives the
expansion for arbitrary continuous linear functionals.
-/

/-- The Hermite expansion recovers any continuous linear functional.
    For φ : S(ℝ) →L[ℝ] ℝ and f ∈ S(ℝ):
      φ(f) = ∑' n, cₙ(f) · φ(ψₙ)
-/
theorem schwartz_hermite_expansion_CLF
    (φ : SchwartzMap ℝ ℝ →L[ℝ] ℝ) (f : SchwartzMap ℝ ℝ) :
    φ f = ∑' n, hermiteCoeff1D n f * φ (schwartzHermiteBasis1D n) := by
  -- Specialize schwartz_hermite_expansion_1D with H = ℝ, T = φ, w = 1
  have h := @schwartz_hermite_expansion_1D ℝ _ _ _ φ f 1
  -- h states: inner 1 (φ f) = ∑' n, hermiteCoeff1D n f * inner 1 (φ (schwartzHermiteBasis1D n))
  -- On ℝ, RCLike.inner_apply tells us: inner x y = y * conj x
  -- For real numbers, conj x = x, so inner 1 x = x * 1 = x
  have key : ∀ x : ℝ, @inner ℝ ℝ _ 1 x = x := fun x => by
    rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply, conj_trivial, RCLike.re_to_real]
    simp
  simp only [key] at h
  exact h

/-! ## Seminorm Bounds

The decay theorem bounds coefficients by a sup of finitely many seminorms.
We show this sup is controlled by a single seminorm using:
- For the weight index k: ‖x‖^k' ≤ (1 + ‖x‖)^q.1 when k' ≤ q.1
- The `one_add_le_sup_seminorm_apply` lemma then bounds each pointwise value
- We apply `seminorm_le_bound` to lift to the seminorm level

Key fact: Mathlib's Schwartz seminorms use ‖x‖^k (NOT (1+‖x‖)^k), so they are
NOT individually monotone in k. The bound goes through the (1+‖x‖) framework.
-/

/-- Each individual Schwartz seminorm in `Finset.Iic q` is bounded by
    `2^q.1` times the sup over the same finite set. Combined with
    `finset_sup_apply_le`, this gives the sup bounded by itself (with constant),
    which then allows us to bound by any element with a larger constant.
-/
private theorem seminorm_le_sup_of_mem {q : ℕ × ℕ} {k' l' : ℕ}
    (hk : k' ≤ q.1) (hl : l' ≤ q.2) (f : SchwartzMap ℝ ℝ) :
    SchwartzMap.seminorm ℝ k' l' f ≤
      2 ^ q.1 * (Finset.Iic q).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f := by
  apply SchwartzMap.seminorm_le_bound ℝ k' l' f (by positivity)
  intro x
  have hx_le : ‖x‖ ^ k' ≤ (1 + ‖x‖) ^ q.1 :=
    calc ‖x‖ ^ k'
        ≤ (1 + ‖x‖) ^ k' :=
          pow_le_pow_left₀ (norm_nonneg x) (le_add_of_nonneg_left zero_le_one) k'
      _ ≤ (1 + ‖x‖) ^ q.1 :=
          pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg x)) hk
  calc ‖x‖ ^ k' * ‖iteratedFDeriv ℝ l' f x‖
      ≤ (1 + ‖x‖) ^ q.1 * ‖iteratedFDeriv ℝ l' f x‖ := by gcongr
    _ ≤ 2 ^ q.1 * (Finset.Iic q).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f :=
        SchwartzMap.one_add_le_sup_seminorm_apply le_rfl hl f x

/-- Coefficient decay with a finset-sup seminorm bound. This is the natural form
    that follows directly from `hermiteCoeff1D_decay`.
-/
theorem hermiteCoeff1D_decay_single :
    ∀ (k : ℕ), ∃ (C : ℝ) (q : ℕ × ℕ), 0 < C ∧
      ∀ (f : SchwartzMap ℝ ℝ) (n : ℕ),
        |hermiteCoeff1D n f| * (1 + (n : ℝ)) ^ (k : ℝ) ≤
          C * (Finset.Iic q).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f := by
  intro k
  exact hermiteCoeff1D_decay (k : ℝ)

/-! ## Basis Growth (seminorm bound)

Repackage `hermiteFunction_seminorm_bound` with ℕ exponent.
-/

/-- Basis growth: Schwartz seminorms of Hermite functions grow polynomially.
    Compatible with DyninMityaginSpace.basis_growth.
-/
theorem schwartzHermiteBasis1D_growth (k l : ℕ) :
    ∃ (C : ℝ), 0 < C ∧ ∃ (s : ℕ),
      ∀ m, SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D m) ≤
        C * (1 + (m : ℝ)) ^ s := by
  obtain ⟨C, s, hC, _hs, hbound⟩ := hermiteFunction_seminorm_bound k l
  -- s is ℝ, need to convert to ℕ
  refine ⟨C, hC, ⌈max s 0⌉₊, fun m => ?_⟩
  calc SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D m)
      = SchwartzMap.seminorm ℝ k l (Classical.choose (hermiteFunction_schwartz m)) := by
        congr 1 -- schwartzHermiteBasis1D m = Classical.choose ...
    _ ≤ C * (1 + ↑m) ^ s := hbound m
    _ ≤ C * (1 + ↑m) ^ (↑⌈max s 0⌉₊ : ℝ) := by
        gcongr
        · exact le_add_of_nonneg_right (Nat.cast_nonneg m)
        · exact le_trans (le_max_left s 0) (Nat.le_ceil (max s 0))
    _ = C * (1 + ↑m) ^ ⌈max s 0⌉₊ := by rw [rpow_natCast]

end
