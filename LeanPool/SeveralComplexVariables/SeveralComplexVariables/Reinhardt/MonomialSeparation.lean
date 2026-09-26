/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.SpecificLimits.Basic
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Reinhardt.Hull

/-!
# Monomial separation on complete logarithmically convex Reinhardt sets

Logarithmic separation can be restricted to the nonzero coordinates of an exterior point.
Approximating the nonnegative separating weights by integer exponents then gives a monomial
separating that point from a compact subset of the domain.

## Main results

`exists_logarithmic_lift` produces a logarithmic lift of a modulus vector with some zero
coordinates. `exists_nat_weights` approximates nonnegative separating weights by integer
exponents. `exists_monomial_separator_of_finite_radii` is the resulting monomial separator.
-/

public noncomputable section

open Set Filter
open scoped Topology NNReal

namespace SeveralComplexVariables

variable {ι : Type*} [Fintype ι]

/-- Exponentiation on the coordinate face determined by the nonzero entries of `z`. -/
private def faceExp (z : ι → ℂ) (t : ι → ℝ) : ι → ℂ :=
  fun i => if z i = 0 then 0 else (Real.exp (t i) : ℂ)

omit [Fintype ι] in
/-- Exponentiation on a fixed coordinate face is continuous. -/
private theorem continuous_faceExp (z : ι → ℂ) : Continuous (faceExp z) := by
  classical
  apply continuous_pi
  intro i
  by_cases hi : z i = 0 <;> simp only [faceExp, hi, ite_true, ite_false]
  · exact continuous_const
  · fun_prop

omit [Fintype ι] in
/-- A face point in an open complete Reinhardt set has a positive lift with the same nonzero
coordinates. -/
private theorem exists_logarithmic_lift [Finite ι] {U : Set (ι → ℂ)} (ho : IsOpen U)
    (hc : IsCompleteReinhardt U) {z : ι → ℂ} {t : ι → ℝ} (ht : faceExp z t ∈ U) :
    ∃ y ∈ logarithmicImage U, ∀ i, z i ≠ 0 → y i = t i := by
  classical
  let := Fintype.ofFinite ι
  classical
  obtain ⟨r, hrU, hr⟩ := hc.isReinhardt.exists_strict_modulus_majorant ho ht
  have hrpos (i) : 0 < (r i : ℝ) := by
    exact_mod_cast (show (0 : ℝ≥0) ≤ ‖faceExp z t i‖₊ from zero_le).trans_lt (hr i)
  let y (i : ι) := if z i = 0 then Real.log (r i) else t i
  refine ⟨y, hc hrU ?_, ?_⟩
  · intro i
    by_cases hi : z i = 0
    · simp [y, hi, Real.exp_log (hrpos i)]
    · have hri : ‖faceExp z t i‖ < (r i : ℝ) := by exact_mod_cast hr i
      simpa [y, faceExp, hi, abs_of_pos (hrpos i)] using hri.le
  · intro i hi
    simp [y, hi]

omit [Fintype ι] in
/-- Logarithmic coordinates on any coordinate face form an open convex lower set. -/
private theorem convex_faceLog [Finite ι] {U : Set (ι → ℂ)} (ho : IsOpen U)
    (hc : IsCompleteReinhardt U) (hl : IsLogarithmicallyConvex U) (z : ι → ℂ) :
    Convex ℝ {t | faceExp z t ∈ U} := by
  classical
  let := Fintype.ofFinite ι
  classical
  intro x hx y hy a b ha hb hab
  obtain ⟨x', hx', hxx⟩ := exists_logarithmic_lift ho hc hx
  obtain ⟨y', hy', hyy⟩ := exists_logarithmic_lift ho hc hy
  apply hc (hl hx' hy' ha hb hab)
  intro i
  by_cases hi : z i = 0
  · simp [faceExp, hi]
  · simp [faceExp, hi, hxx i hi, hyy i hi]

omit [Fintype ι] in
/-- The logarithmic face set is closed under decreasing coordinates. -/
private theorem faceExp_mem_of_le {U : Set (ι → ℂ)} (hc : IsCompleteReinhardt U)
    {z : ι → ℂ} {x y : ι → ℝ} (hx : faceExp z x ∈ U) (hy : y ≤ x) :
    faceExp z y ∈ U := by
  classical
  apply hc hx
  intro i
  by_cases hi : z i = 0
  · simp [faceExp, hi]
  · simpa [faceExp, hi] using Real.exp_le_exp.mpr (hy i)

omit [Fintype ι] in
/-- A separating functional for a lower set has nonnegative coordinate weights. -/
private theorem nonneg_separating_weights [DecidableEq ι] {S : Set (ι → ℝ)}
    (hdown : ∀ x ∈ S, ∀ y, y ≤ x → y ∈ S) {x y : ι → ℝ} (hy : y ∈ S)
    {l : (ι → ℝ) →L[ℝ] ℝ} (hl : ∀ t ∈ S, l t < l x) (i : ι) :
    0 ≤ l (Pi.single i 1) := by
  classical
  by_contra h
  have hi : l (Pi.single i 1) < 0 := lt_of_not_ge h
  let a := (l x - l y + 1) / (-l (Pi.single i 1))
  have ha : 0 ≤ a := le_of_lt (div_pos (by linarith [hl y hy]) (neg_pos.mpr hi))
  have ht := hl (y - a • Pi.single i 1) (hdown y hy _ (by
    intro j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_le_self_iff]
    exact mul_nonneg ha (by simp [Pi.single_apply]; split_ifs <;> norm_num)))
  rw [map_sub, map_smul, smul_eq_mul] at ht
  have he : a * (-l (Pi.single i 1)) = l x - l y + 1 :=
    div_mul_cancel₀ _ (neg_ne_zero.mpr hi.ne)
  nlinarith

omit [Fintype ι] in
/-- Coordinates absent from a face have zero weight in any separating functional. -/
private theorem separating_weight_zero [DecidableEq ι] {U : Set (ι → ℂ)} {z : ι → ℂ}
    {x y : ι → ℝ} (hy : faceExp z y ∈ U) {l : (ι → ℝ) →L[ℝ] ℝ}
    (hl : ∀ t, faceExp z t ∈ U → l t < l x) (i : ι) (hi : z i = 0) :
    l (Pi.single i 1) = 0 := by
  classical
  by_contra hn
  let a := (l x - l y + 1) / l (Pi.single i 1)
  have he : faceExp z (y + a • Pi.single i 1) = faceExp z y := by
    funext j
    by_cases hj : j = i
    · subst j; simp [faceExp, hi]
    · simp [faceExp, Pi.single_eq_of_ne hj]
  have ht := hl _ (he ▸ hy)
  rw [map_add, map_smul, smul_eq_mul] at ht
  have heq : a * l (Pi.single i 1) = l x - l y + 1 := div_mul_cancel₀ _ hn
  linarith

/-- A linear functional on a finite coordinate space is the sum of its coordinate weights. -/
private theorem linear_functional_eq_sum [DecidableEq ι] (l : (ι → ℝ) →L[ℝ] ℝ) (t : ι → ℝ) :
    l t = ∑ i, l (Pi.single i 1) * t i := by
  rw [← Finset.univ_sum_single t, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : Pi.single i (t i) = t i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply, mul_ite]
  rw [he, map_smul, smul_eq_mul, mul_comm, Finset.univ_sum_single]

/-- Finitely many strict inequalities with nonnegative real weights persist for suitable nonnegative
integer weights. Zero weights remain zero. -/
private theorem exists_nat_weights {κ : Type*} [Finite κ] {a x : ι → ℝ}
    {y : κ → ι → ℝ} (ha : ∀ i, 0 ≤ a i)
    (hxy : ∀ j, (∑ i, a i * y j i) < ∑ i, a i * x i) :
    ∃ m : ι → ℕ, (∀ i, a i = 0 → m i = 0) ∧
      ∀ j, (∑ i, (m i : ℝ) * y j i) < ∑ i, (m i : ℝ) * x i := by
  classical
  let := Fintype.ofFinite κ
  have hlim (j : κ) : Tendsto
      (fun t : ℝ => ∑ i, ((⌊a i * t⌋₊ : ℝ) / t) * (x i - y j i)) atTop
      (𝓝 (∑ i, a i * (x i - y j i))) :=
    tendsto_finsetSum _ (fun i _ => (tendsto_nat_floor_mul_div_atTop (ha i)).mul_const _)
  have hpos (j : κ) : 0 < ∑ i, a i * (x i - y j i) := by
    simpa only [mul_sub, Finset.sum_sub_distrib] using sub_pos.mpr (hxy j)
  have hall : ∀ᶠ t : ℝ in atTop, ∀ j, 0 < ∑ i, ((⌊a i * t⌋₊ : ℝ) / t) * (x i - y j i) :=
    Filter.eventually_all.mpr (fun j => (hlim j).eventually (lt_mem_nhds (hpos j)))
  obtain ⟨t, ht, h⟩ := (hall.and (eventually_gt_atTop (0 : ℝ))).exists
  refine ⟨fun i => ⌊a i * t⌋₊, fun i hi => by simp [hi], ?_⟩
  intro j
  have hj := ht j
  simp only [div_mul_eq_mul_div, ← Finset.sum_div, mul_sub, Finset.sum_sub_distrib] at hj
  exact (div_lt_div_iff_of_pos_right h).mp (sub_pos.mp hj)

/-- A monomial separates an exterior point from finitely many positive radius vectors in an open
complete logarithmically convex Reinhardt set. -/
theorem exists_monomial_separator_of_finite_radii {κ : Type*} [Finite κ] [Nonempty κ]
    {U : Set (ι → ℂ)} (ho : IsOpen U) (hc : IsCompleteReinhardt U)
    (hl : IsLogarithmicallyConvex U) {r : κ → ι → ℝ}
    (hr : ∀ j i, 0 < r j i) (hrU : ∀ j, (fun i => (r j i : ℂ)) ∈ U)
    {z : ι → ℂ} (hz : z ∉ U) :
    ∃ m : ι → ℕ, ∀ j, (∏ i, r j i ^ m i) < ∏ i, ‖z i‖ ^ m i := by
  classical
  let := Fintype.ofFinite κ
  classical
  let x (i : ι) := Real.log ‖z i‖
  let y (j : κ) (i : ι) := Real.log (r j i)
  have hx : faceExp z x ∉ U := by
    intro hx
    apply hz (hc.isReinhardt hx ?_)
    intro i
    by_cases hi : z i = 0
    · simp [faceExp, hi]
    · simp [faceExp, hi, x, Real.exp_log (norm_pos_iff.mpr hi)]
  have hy (j : κ) : faceExp z (y j) ∈ U := by
    apply hc (hrU j)
    intro i
    by_cases hi : z i = 0
    · simp [faceExp, hi]
    · simp [faceExp, hi, y, Real.exp_log (hr j i)]
  obtain ⟨l, hsep⟩ := geometric_hahn_banach_open_point (convex_faceLog ho hc hl z)
    (ho.preimage (continuous_faceExp z)) hx
  let a (i : ι) := l (Pi.single i 1)
  have ha (i : ι) : 0 ≤ a i := nonneg_separating_weights
    (fun _ ht _ hle => faceExp_mem_of_le hc ht hle) (hy (Classical.arbitrary κ)) hsep i
  have ha0 (i : ι) (hi : z i = 0) : a i = 0 :=
    separating_weight_zero (hy (Classical.arbitrary κ)) hsep i hi
  obtain ⟨m, hm0, hm⟩ := exists_nat_weights ha (fun j => by
    simpa only [linear_functional_eq_sum l (y j), linear_functional_eq_sum l x] using hsep _ (hy j))
  refine ⟨m, fun j => ?_⟩
  have hexp (v : ι → ℝ) (hv : ∀ i, 0 < v i) :
      Real.exp (∑ i, (m i : ℝ) * Real.log (v i)) = ∏ i, v i ^ m i := by
    simp [Real.exp_sum, Real.exp_nat_mul, Real.exp_log (hv _)]
  have hzexp : Real.exp (∑ i, (m i : ℝ) * x i) = ∏ i, ‖z i‖ ^ m i := by
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : z i = 0
    · simp [hm0 i (ha0 i hi)]
    · simp [x, Real.exp_nat_mul, Real.exp_log (norm_pos_iff.mpr hi)]
  rw [← hexp (r j) (hr j), ← hzexp]
  exact Real.exp_lt_exp.mpr (hm j)

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
