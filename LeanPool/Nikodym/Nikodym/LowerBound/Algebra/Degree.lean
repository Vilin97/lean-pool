/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.Interface
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.HilbertPolynomial
import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.PolyAsymptotics

/-!
# Degree and leading term of the affine Hilbert polynomial

This file implements blueprint node **A04′** of the algebra backend: for an ideal `I` of
`P_d = MvPolynomial (Fin d) K` whose affine Hilbert function is sandwiched, for all large `t`,
between `∑ i, (t - e i + k).choose k` and `Δ * (t + k).choose k` (with `k = quotDim I`, `Δ > 0`
and shifts `e : Fin Δ → ℕ`), the affine Hilbert polynomial has `natDegree = k` and leading
coefficient `Δ / k!`, so `degree I = Δ`, `0 < degree I`, and the upper bound reads
`hilbert I t ≤ degree I * (t + k).choose k` (the final form of blueprint node **A08**).

The two bounds are taken as *hypotheses* (`_of_eventually_bounds` for the `∀ᶠ` form,
`_of_bounds` for the `∀ t` form). They are produced, for `[Infinite K]` and prime `I`, by node
**A08-core** (`exists_hilbert_bounds` in `Hilbert/DegreeUpper.lean`): the lower bound comes from
a free submodule of rank `Δ` of the homogeneous coordinate ring over a Noether normalization, the
upper bound from the generic rank `Δ`. Everything here is field-free and needs no primality.

Main declarations:

* `Nikodym.LowerBound.lowerPoly k e`: the comparison polynomial `∑ i, choosePoly k ∘ (X - e i)`,
  with `lowerPoly_eval_natCast`, `natDegree_lowerPoly_le`, `coeff_lowerPoly`.
* `Nikodym.LowerBound.natDegree_affineHilbertPoly_of_bounds`,
  `coeff_quotDim_affineHilbertPoly_of_bounds`, `degree_eq_of_bounds`,
  `leadingCoeff_affineHilbertPoly_of_bounds`, `degree_pos_of_bounds`,
  `hilbert_le_degree_mul_choose_of_bounds`, and their `_of_eventually_bounds` versions.
-/

namespace Nikodym.LowerBound

open Polynomial Filter

variable {K : Type*} [Field K] {d : ℕ}

/-! ### The comparison polynomials -/

section ComparisonPolynomials

/-- Blueprint A04′: the lower comparison polynomial `∑ i, (choosePoly k).comp (X - C (e i))`,
whose value at a natural number `t ≥ max e` is `∑ i, (t - e i + k).choose k`. -/
noncomputable def lowerPoly (k : ℕ) {Δ : ℕ} (e : Fin Δ → ℕ) : ℚ[X] :=
  ∑ i, (choosePoly k).comp (X - C (e i : ℚ))

/-- Blueprint A04′: `(lowerPoly k e).eval t = ∑ i, (t - e i + k).choose k` for `t ≥ e i`. -/
theorem lowerPoly_eval_natCast (k : ℕ) {Δ : ℕ} (e : Fin Δ → ℕ) {t : ℕ} (ht : ∀ i, e i ≤ t) :
    (lowerPoly k e).eval (t : ℚ) = ((∑ i, (t - e i + k).choose k : ℕ) : ℚ) := by
  rw [lowerPoly, eval_finsetSum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [eval_comp_X_sub_C_natCast _ (ht i), choosePoly_eval_natCast]

/-- Blueprint A04′: `lowerPoly k e` has degree at most `k`. -/
theorem natDegree_lowerPoly_le (k : ℕ) {Δ : ℕ} (e : Fin Δ → ℕ) :
    (lowerPoly k e).natDegree ≤ k :=
  natDegree_sum_le_of_forall_le _ _ fun i _ ↦ by
    rw [natDegree_comp_X_sub_C, natDegree_choosePoly]

/-- Blueprint A04′: the coefficient of `X ^ k` in `choosePoly k` is `1 / k!`. -/
theorem coeff_choosePoly_self (k : ℕ) : (choosePoly k).coeff k = (k.factorial : ℚ)⁻¹ := by
  have h := leadingCoeff_choosePoly k
  rwa [leadingCoeff, natDegree_choosePoly] at h

/-- Blueprint A04′: the coefficient of `X ^ k` in `lowerPoly k e` is `Δ / k!`: each of the `Δ`
shifted copies of `choosePoly k` contributes its leading coefficient `1 / k!`. -/
theorem coeff_lowerPoly (k : ℕ) {Δ : ℕ} (e : Fin Δ → ℕ) :
    (lowerPoly k e).coeff k = (Δ : ℚ) / k.factorial := by
  rw [lowerPoly, finsetSum_coeff]
  have h : ∀ i : Fin Δ, ((choosePoly k).comp (X - C (e i : ℚ))).coeff k = (k.factorial : ℚ)⁻¹ := by
    intro i
    have h := leadingCoeff_comp_X_sub_C (choosePoly k) (e i : ℚ)
    rwa [leadingCoeff, natDegree_comp_X_sub_C, natDegree_choosePoly, leadingCoeff_choosePoly] at h
  rw [Finset.sum_congr rfl fun i _ ↦ h i, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, div_eq_mul_inv]

/-- Blueprint A04′: `(C Δ * choosePoly k).eval t = Δ * (t + k).choose k` for `t : ℕ`. -/
theorem eval_C_mul_choosePoly_natCast (Δ k t : ℕ) :
    (C (Δ : ℚ) * choosePoly k).eval (t : ℚ) = ((Δ * (t + k).choose k : ℕ) : ℚ) := by
  rw [eval_mul, eval_C, choosePoly_eval_natCast, Nat.cast_mul]

/-- Blueprint A04′: `C Δ * choosePoly k` has degree at most `k`. -/
theorem natDegree_C_mul_choosePoly_le (Δ k : ℕ) : (C (Δ : ℚ) * choosePoly k).natDegree ≤ k :=
  (natDegree_C_mul_le _ _).trans_eq (natDegree_choosePoly k)

/-- Blueprint A04′: the coefficient of `X ^ k` in `C Δ * choosePoly k` is `Δ / k!`. -/
theorem coeff_C_mul_choosePoly (Δ k : ℕ) :
    (C (Δ : ℚ) * choosePoly k).coeff k = (Δ : ℚ) / k.factorial := by
  rw [coeff_C_mul, coeff_choosePoly_self, div_eq_mul_inv]

end ComparisonPolynomials

/-! ### The affine Hilbert polynomial under a two-sided bound -/

section Bounds

variable {I : Ideal (MvPolynomial (Fin d) K)} {Δ : ℕ} {e : Fin Δ → ℕ}

/-- Blueprint A04′: the eventual sandwich `lowerPoly ≤ affineHilbertPoly I ≤ C Δ * choosePoly`
along `ℕ`, from the two-sided bound on the Hilbert function and `hilbert I t = p.eval t` for
large `t`. -/
theorem eventually_between_of_eventually_bounds
    (hlow : ∀ᶠ t : ℕ in atTop, ∑ i, (t - e i + quotDim I).choose (quotDim I) ≤ hilbert I t)
    (hup : ∀ᶠ t : ℕ in atTop, hilbert I t ≤ Δ * (t + quotDim I).choose (quotDim I)) :
    ∀ᶠ t : ℕ in atTop,
      (lowerPoly (quotDim I) e).eval (t : ℚ) ≤ (affineHilbertPoly I).eval (t : ℚ) ∧
        (affineHilbertPoly I).eval (t : ℚ) ≤ (C (Δ : ℚ) * choosePoly (quotDim I)).eval (t : ℚ) := by
  have he : ∀ᶠ t : ℕ in atTop, ∀ i, e i ≤ t := eventually_all.mpr fun i ↦ eventually_ge_atTop _
  filter_upwards [hilbert_eventually_eq_affineHilbertPoly I, hlow, hup, he] with t hp hl hu he
  rw [← hp, lowerPoly_eval_natCast _ _ he, eval_C_mul_choosePoly_natCast]
  exact ⟨Nat.cast_le.mpr hl, Nat.cast_le.mpr hu⟩

/-- Blueprint A04′: under the eventual two-sided bound, `natDegree (affineHilbertPoly I) ≤ k`
and the coefficient of `X ^ k` is `Δ / k!`, where `k = quotDim I`. -/
theorem natDegree_le_and_coeff_of_eventually_bounds
    (hlow : ∀ᶠ t : ℕ in atTop, ∑ i, (t - e i + quotDim I).choose (quotDim I) ≤ hilbert I t)
    (hup : ∀ᶠ t : ℕ in atTop, hilbert I t ≤ Δ * (t + quotDim I).choose (quotDim I)) :
    (affineHilbertPoly I).natDegree ≤ quotDim I ∧
      (affineHilbertPoly I).coeff (quotDim I) = (Δ : ℚ) / (quotDim I).factorial := by
  have h := eventually_between_of_eventually_bounds hlow hup
  have h₁ := natDegree_lowerPoly_le (quotDim I) e
  have h₂ := natDegree_C_mul_choosePoly_le Δ (quotDim I)
  have hle := natDegree_le_of_eventually_between h₁ h₂ h
  refine ⟨hle, le_antisymm ?_ ?_⟩
  · rw [← coeff_C_mul_choosePoly Δ (quotDim I)]
    exact coeff_le_coeff_of_eventually_le hle h₂ (h.mono fun _ ht ↦ ht.2)
  · rw [← coeff_lowerPoly (quotDim I) e]
    exact coeff_le_coeff_of_eventually_le h₁ hle (h.mono fun _ ht ↦ ht.1)

/-- Blueprint A04′: under the eventual two-sided bound, the coefficient of `X ^ quotDim I` in
the affine Hilbert polynomial is `Δ / (quotDim I)!`. -/
theorem coeff_quotDim_affineHilbertPoly_of_eventually_bounds
    (hlow : ∀ᶠ t : ℕ in atTop, ∑ i, (t - e i + quotDim I).choose (quotDim I) ≤ hilbert I t)
    (hup : ∀ᶠ t : ℕ in atTop, hilbert I t ≤ Δ * (t + quotDim I).choose (quotDim I)) :
    (affineHilbertPoly I).coeff (quotDim I) = (Δ : ℚ) / (quotDim I).factorial :=
  (natDegree_le_and_coeff_of_eventually_bounds hlow hup).2

/-- Blueprint A04′: under the eventual two-sided bound with `0 < Δ`, the affine Hilbert
polynomial has `natDegree = quotDim I`. -/
theorem natDegree_affineHilbertPoly_of_eventually_bounds (hΔ : 0 < Δ)
    (hlow : ∀ᶠ t : ℕ in atTop, ∑ i, (t - e i + quotDim I).choose (quotDim I) ≤ hilbert I t)
    (hup : ∀ᶠ t : ℕ in atTop, hilbert I t ≤ Δ * (t + quotDim I).choose (quotDim I)) :
    (affineHilbertPoly I).natDegree = quotDim I := by
  obtain ⟨hle, hc⟩ := natDegree_le_and_coeff_of_eventually_bounds hlow hup
  refine natDegree_eq_of_le_of_coeff_ne_zero hle ?_
  rw [hc]
  exact div_ne_zero (Nat.cast_ne_zero.mpr hΔ.ne')
    (Nat.cast_ne_zero.mpr (quotDim I).factorial_ne_zero)

/-- Blueprint A04′: under the eventual two-sided bound with `0 < Δ`, `degree I = Δ`. -/
theorem degree_eq_of_eventually_bounds (hΔ : 0 < Δ)
    (hlow : ∀ᶠ t : ℕ in atTop, ∑ i, (t - e i + quotDim I).choose (quotDim I) ≤ hilbert I t)
    (hup : ∀ᶠ t : ℕ in atTop, hilbert I t ≤ Δ * (t + quotDim I).choose (quotDim I)) :
    degree I = Δ := by
  rw [degree, leadingCoeff, natDegree_affineHilbertPoly_of_eventually_bounds hΔ hlow hup,
    coeff_quotDim_affineHilbertPoly_of_eventually_bounds hlow hup,
    div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (quotDim I).factorial_ne_zero), Nat.floor_natCast]

/-- Blueprint A04′: under the eventual two-sided bound with `0 < Δ`, the leading coefficient of
the affine Hilbert polynomial is `degree I / (quotDim I)!`. -/
theorem leadingCoeff_affineHilbertPoly_of_eventually_bounds (hΔ : 0 < Δ)
    (hlow : ∀ᶠ t : ℕ in atTop, ∑ i, (t - e i + quotDim I).choose (quotDim I) ≤ hilbert I t)
    (hup : ∀ᶠ t : ℕ in atTop, hilbert I t ≤ Δ * (t + quotDim I).choose (quotDim I)) :
    (affineHilbertPoly I).leadingCoeff = (degree I : ℚ) / (quotDim I).factorial := by
  rw [leadingCoeff, natDegree_affineHilbertPoly_of_eventually_bounds hΔ hlow hup,
    coeff_quotDim_affineHilbertPoly_of_eventually_bounds hlow hup,
    degree_eq_of_eventually_bounds hΔ hlow hup]

/-- Blueprint A04′: under the eventual two-sided bound with `0 < Δ`, `0 < degree I`. -/
theorem degree_pos_of_eventually_bounds (hΔ : 0 < Δ)
    (hlow : ∀ᶠ t : ℕ in atTop, ∑ i, (t - e i + quotDim I).choose (quotDim I) ≤ hilbert I t)
    (hup : ∀ᶠ t : ℕ in atTop, hilbert I t ≤ Δ * (t + quotDim I).choose (quotDim I)) :
    0 < degree I :=
  (degree_eq_of_eventually_bounds hΔ hlow hup).symm ▸ hΔ

/-- Blueprint A04′/A08: under the eventual lower bound and the upper bound at every `t`, with
`0 < Δ`, the Hilbert function satisfies `hilbert I t ≤ degree I * (t + quotDim I).choose
(quotDim I)` for all `t`. -/
theorem hilbert_le_degree_mul_choose_of_eventually_bounds (hΔ : 0 < Δ)
    (hlow : ∀ᶠ t : ℕ in atTop, ∑ i, (t - e i + quotDim I).choose (quotDim I) ≤ hilbert I t)
    (hup : ∀ t, hilbert I t ≤ Δ * (t + quotDim I).choose (quotDim I)) (t : ℕ) :
    hilbert I t ≤ degree I * (t + quotDim I).choose (quotDim I) := by
  rw [degree_eq_of_eventually_bounds hΔ hlow (Eventually.of_forall hup)]
  exact hup t

/-! ### The `∀ t` versions -/

/-- Blueprint A04′: `natDegree (affineHilbertPoly I) = quotDim I` from the two-sided bound
`∑ i, (t - e i + k).choose k ≤ hilbert I t ≤ Δ * (t + k).choose k` at every `t`, with `0 < Δ`. -/
theorem natDegree_affineHilbertPoly_of_bounds (hΔ : 0 < Δ)
    (hlow : ∀ t, ∑ i, (t - e i + quotDim I).choose (quotDim I) ≤ hilbert I t)
    (hup : ∀ t, hilbert I t ≤ Δ * (t + quotDim I).choose (quotDim I)) :
    (affineHilbertPoly I).natDegree = quotDim I :=
  natDegree_affineHilbertPoly_of_eventually_bounds hΔ (Eventually.of_forall hlow)
    (Eventually.of_forall hup)

/-- Blueprint A04′: the coefficient of `X ^ quotDim I` in the affine Hilbert polynomial is
`Δ / (quotDim I)!`, from the two-sided bound at every `t`. -/
theorem coeff_quotDim_affineHilbertPoly_of_bounds
    (hlow : ∀ t, ∑ i, (t - e i + quotDim I).choose (quotDim I) ≤ hilbert I t)
    (hup : ∀ t, hilbert I t ≤ Δ * (t + quotDim I).choose (quotDim I)) :
    (affineHilbertPoly I).coeff (quotDim I) = (Δ : ℚ) / (quotDim I).factorial :=
  coeff_quotDim_affineHilbertPoly_of_eventually_bounds (Eventually.of_forall hlow)
    (Eventually.of_forall hup)

/-- Blueprint A04′: `degree I = Δ` from the two-sided bound at every `t`, with `0 < Δ`. -/
theorem degree_eq_of_bounds (hΔ : 0 < Δ)
    (hlow : ∀ t, ∑ i, (t - e i + quotDim I).choose (quotDim I) ≤ hilbert I t)
    (hup : ∀ t, hilbert I t ≤ Δ * (t + quotDim I).choose (quotDim I)) :
    degree I = Δ :=
  degree_eq_of_eventually_bounds hΔ (Eventually.of_forall hlow) (Eventually.of_forall hup)

/-- Blueprint A04′: the leading coefficient of the affine Hilbert polynomial is
`degree I / (quotDim I)!`, from the two-sided bound at every `t`, with `0 < Δ`. -/
theorem leadingCoeff_affineHilbertPoly_of_bounds (hΔ : 0 < Δ)
    (hlow : ∀ t, ∑ i, (t - e i + quotDim I).choose (quotDim I) ≤ hilbert I t)
    (hup : ∀ t, hilbert I t ≤ Δ * (t + quotDim I).choose (quotDim I)) :
    (affineHilbertPoly I).leadingCoeff = (degree I : ℚ) / (quotDim I).factorial :=
  leadingCoeff_affineHilbertPoly_of_eventually_bounds hΔ (Eventually.of_forall hlow)
    (Eventually.of_forall hup)

/-- Blueprint A04′: `0 < degree I` from the two-sided bound at every `t`, with `0 < Δ`. -/
theorem degree_pos_of_bounds (hΔ : 0 < Δ)
    (hlow : ∀ t, ∑ i, (t - e i + quotDim I).choose (quotDim I) ≤ hilbert I t)
    (hup : ∀ t, hilbert I t ≤ Δ * (t + quotDim I).choose (quotDim I)) :
    0 < degree I :=
  degree_pos_of_eventually_bounds hΔ (Eventually.of_forall hlow) (Eventually.of_forall hup)

/-- Blueprint A08 (final form, modulo A08-core): `hilbert I t ≤ degree I * (t + quotDim I).choose
(quotDim I)` for all `t`, from the two-sided bound at every `t`, with `0 < Δ`. -/
theorem hilbert_le_degree_mul_choose_of_bounds (hΔ : 0 < Δ)
    (hlow : ∀ t, ∑ i, (t - e i + quotDim I).choose (quotDim I) ≤ hilbert I t)
    (hup : ∀ t, hilbert I t ≤ Δ * (t + quotDim I).choose (quotDim I)) (t : ℕ) :
    hilbert I t ≤ degree I * (t + quotDim I).choose (quotDim I) :=
  hilbert_le_degree_mul_choose_of_eventually_bounds hΔ (Eventually.of_forall hlow) hup t

end Bounds

/-!
### Glue with A08-core

Node A08-core (`Hilbert/DegreeUpper.lean`, `exists_hilbert_bounds`) supplies the two-sided bounds
for every prime over an infinite field; the resulting unconditional `_of_infinite` statements live
in `Algebra/Assembly.lean`.
-/

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
