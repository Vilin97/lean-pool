/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-! # Source Stable Bivariate -/

@[expose] public section

namespace BeyondBethe

/-!
# The bivariate core of the stable-coefficient inequality

After all other variables have been specialized to positive real numbers, a
multiaffine bistable polynomial has the form

`a*y*z + b*y + c*z + d`.

Stability of the sign-reversed polynomial forces `b*c ≤ a*d`.  The short
argument below is the elementary two-variable content behind the Rayleigh
inequality used in Anari--Oveis Gharan.
-/

/-- A nonnegative bivariate multiaffine polynomial is bistable when its
sign-reversal in the second variable has no zero with both variables in the
open upper half-plane. -/
def BivariateBistable (a b c d : ℝ) : Prop :=
  ∀ y z : ℂ, 0 < y.im → 0 < z.im →
    -(a : ℂ) * y * z + (b : ℂ) * y - (c : ℂ) * z + (d : ℂ) ≠ 0

/-- The bivariate Rayleigh determinant inequality, proved directly by
exhibiting an upper-half-plane zero if `a*d < b*c`. -/
theorem bivariate_rayleigh_of_bistable
    {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hstable : BivariateBistable a b c d) :
    b * c ≤ a * d := by
  by_contra hnot
  have hgap : a * d < b * c := lt_of_not_ge hnot
  have hbpos : 0 < b := by
    by_contra hbnot
    have hbzero : b = 0 := le_antisymm (le_of_not_gt hbnot) hb
    rw [hbzero, zero_mul] at hgap
    exact (not_lt_of_ge (mul_nonneg ha hd)) hgap
  have hcpos : 0 < c := by
    by_contra hcnot
    have hczero : c = 0 := le_antisymm (le_of_not_gt hcnot) hc
    rw [hczero, mul_zero] at hgap
    exact (not_lt_of_ge (mul_nonneg ha hd)) hgap
  let y : ℂ := Complex.I
  let z : ℂ := ((d : ℂ) + (b : ℂ) * Complex.I) /
    ((c : ℂ) + (a : ℂ) * Complex.I)
  have hden : (c : ℂ) + (a : ℂ) * Complex.I ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    exact hcpos.ne' hre
  have hyim : 0 < y.im := by simp [y]
  have hzim_formula : z.im = (b * c - a * d) / (c ^ 2 + a ^ 2) := by
    dsimp only [z]
    rw [Complex.div_im]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, mul_zero, Complex.add_im,
      Complex.ofReal_im, zero_add, Complex.mul_im, zero_mul, mul_one,
      add_zero, Complex.normSq_apply]
    congr 1 <;> ring
  have hdenpos : 0 < c ^ 2 + a ^ 2 := by positivity
  have hzim : 0 < z.im := by
    rw [hzim_formula]
    exact div_pos (sub_pos.mpr hgap) hdenpos
  have hzero :
      -(a : ℂ) * y * z + (b : ℂ) * y - (c : ℂ) * z + (d : ℂ) = 0 := by
    dsimp only [y, z]
    field_simp [hden]
    ring
  exact (hstable y z hyim hzim) hzero

/-! ## The scalar capacity inequality -/

/-- The boundary factor `α^α * (1 - α)^(1 - α)` with real exponents. -/
noncomputable def stableBoundaryScalar (α : ℝ) : ℝ :=
  (α : ℝ) ^ α * (1 - α) ^ (1 - α)

/-- The weighted AM--GM inequality in the normalization used by the source
proof. -/
theorem normalized_weighted_geometric_mean_le_add
    {α u v : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    u ^ α * v ^ (1 - α) ≤ stableBoundaryScalar α * (u + v) := by
  have hα : 0 ≤ α := hα0.le
  have h1α : 0 ≤ 1 - α := sub_nonneg.mpr hα1.le
  have hamgm := Real.geom_mean_le_arith_mean2_weighted
    hα h1α (div_nonneg hu hα) (div_nonneg hv h1α) (by ring)
  rw [stableBoundaryScalar]
  have hboundary : 0 < α ^ α * (1 - α) ^ (1 - α) :=
    mul_pos (Real.rpow_pos_of_pos hα0 α)
      (Real.rpow_pos_of_pos (sub_pos.mpr hα1) (1 - α))
  have hscaled := mul_le_mul_of_nonneg_left hamgm hboundary.le
  calc
    u ^ α * v ^ (1 - α) =
        (α ^ α * (1 - α) ^ (1 - α)) *
          ((u / α) ^ α * (v / (1 - α)) ^ (1 - α)) := by
            rw [Real.div_rpow hu hα, Real.div_rpow hv h1α]
            field_simp [hα0.ne', (sub_pos.mpr hα1).ne']
    _ ≤ (α ^ α * (1 - α) ^ (1 - α)) *
        (α * (u / α) + (1 - α) * (v / (1 - α))) := hscaled
    _ = (α ^ α * (1 - α) ^ (1 - α)) * (u + v) := by
      field_simp [hα0.ne', (sub_pos.mpr hα1).ne']

/-- The candidate minimizing point `α * v / ((1 - α) * u)` for the linear capacity calculation. -/
noncomputable def linearCapacityCandidate (α u v : ℝ) : ℝ :=
  α * v / ((1 - α) * u)

theorem linearCapacityCandidate_pos
    {α u v : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hu : 0 < u) (hv : 0 < v) :
    0 < linearCapacityCandidate α u v := by
  exact div_pos (mul_pos hα0 hv) (mul_pos (sub_pos.mpr hα1) hu)

/-- Evaluation of a positive affine linear form at its weighted-AM--GM
minimizer. -/
theorem linearCapacityCandidate_ratio
    {α u v : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hu : 0 < u) (hv : 0 < v) :
    (u * linearCapacityCandidate α u v + v) /
        (linearCapacityCandidate α u v) ^ α =
      u ^ α * v ^ (1 - α) / stableBoundaryScalar α := by
  have h1α : 0 < 1 - α := sub_pos.mpr hα1
  have ht : 0 < linearCapacityCandidate α u v :=
    linearCapacityCandidate_pos hα0 hα1 hu hv
  have hnum : u * linearCapacityCandidate α u v + v = v / (1 - α) := by
    rw [linearCapacityCandidate]
    field_simp [hu.ne', h1α.ne']
    ring
  rw [hnum, linearCapacityCandidate, stableBoundaryScalar]
  rw [Real.div_rpow (mul_nonneg hα0.le hv.le)
      (mul_nonneg h1α.le hu.le),
    Real.mul_rpow hα0.le hv.le,
    Real.mul_rpow h1α.le hu.le]
  field_simp [hα0.ne', h1α.ne', hu.ne', hv.ne',
    (Real.rpow_pos_of_pos hα0 α).ne',
    (Real.rpow_pos_of_pos h1α (1 - α)).ne',
    (Real.rpow_pos_of_pos hu α).ne',
    (Real.rpow_pos_of_pos hv α).ne']
  have hsum : α + (1 - α) = 1 := by ring
  calc
    v * (1 - α) ^ α * (1 - α) ^ (1 - α) =
        v * ((1 - α) ^ α * (1 - α) ^ (1 - α)) := by ring
    _ = v * (1 - α) := by
      rw [← Real.rpow_add h1α, hsum, Real.rpow_one]
    _ = (1 - α) * v := by ring
    _ = (1 - α) * (v ^ α * v ^ (1 - α)) := by
      rw [← Real.rpow_add hv, hsum, Real.rpow_one]
    _ = (1 - α) * v ^ α * v ^ (1 - α) := by ring

/-- The exact bivariate capacity step used by the inductive
stable-coefficient proof, in the strictly positive interior case. -/
theorem exists_bivariate_capacity_witness
    {α a b c d : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 < c) (hd : 0 < d)
    (hrayleigh : b * c ≤ a * d) :
    ∃ y z : ℝ, 0 < y ∧ 0 < z ∧
      stableBoundaryScalar α *
          ((a * y * z + b * y + c * z + d) / (y * z) ^ α) ≤
        a + d := by
  let y := linearCapacityCandidate α a c
  let z := linearCapacityCandidate α 1 (d / c)
  have hdc : 0 < d / c := div_pos hd hc
  have hy : 0 < y := linearCapacityCandidate_pos hα0 hα1 ha hc
  have hz : 0 < z := linearCapacityCandidate_pos hα0 hα1 (by norm_num) hdc
  have hb' : b ≤ a * d / c := by
    rw [le_div_iff₀ hc]
    nlinarith
  have hpoly : a * y * z + b * y + c * z + d ≤
      (a * y + c) * (z + d / c) := by
    have := mul_le_mul_of_nonneg_right hb' hy.le
    field_simp [hc.ne'] at this ⊢
    nlinarith
  have hden : 0 < (y * z) ^ α :=
    Real.rpow_pos_of_pos (mul_pos hy hz) α
  have hboundary : 0 < stableBoundaryScalar α := by
    rw [stableBoundaryScalar]
    exact mul_pos (Real.rpow_pos_of_pos hα0 α)
      (Real.rpow_pos_of_pos (sub_pos.mpr hα1) (1 - α))
  have hratio := div_le_div_of_nonneg_right hpoly hden.le
  have hscaled := mul_le_mul_of_nonneg_left hratio hboundary.le
  have hfactor :
      ((a * y + c) * (z + d / c)) / (y * z) ^ α =
        ((a * y + c) / y ^ α) * ((z + d / c) / z ^ α) := by
    rw [Real.mul_rpow hy.le hz.le]
    field_simp [(Real.rpow_pos_of_pos hy α).ne',
      (Real.rpow_pos_of_pos hz α).ne']
  have hyvalue : (a * y + c) / y ^ α =
      a ^ α * c ^ (1 - α) / stableBoundaryScalar α := by
    exact linearCapacityCandidate_ratio hα0 hα1 ha hc
  have hzvalue : (z + d / c) / z ^ α =
      (d / c) ^ (1 - α) / stableBoundaryScalar α := by
    simpa using linearCapacityCandidate_ratio hα0 hα1
      (by norm_num : (0 : ℝ) < 1) hdc
  have hcollapse :
      stableBoundaryScalar α *
          ((a ^ α * c ^ (1 - α) / stableBoundaryScalar α) *
            ((d / c) ^ (1 - α) / stableBoundaryScalar α)) =
        a ^ α * d ^ (1 - α) / stableBoundaryScalar α := by
    rw [Real.div_rpow hd.le hc.le]
    have hcPow : 0 < c ^ (1 - α) := Real.rpow_pos_of_pos hc _
    field_simp [hboundary.ne', hcPow.ne']
  have hamgm := normalized_weighted_geometric_mean_le_add
    hα0 hα1 ha.le hd.le
  have hfinal :
      a ^ α * d ^ (1 - α) / stableBoundaryScalar α ≤ a + d := by
    exact (div_le_iff₀ hboundary).mpr (by simpa [mul_comm] using hamgm)
  refine ⟨y, z, hy, hz, ?_⟩
  calc
    stableBoundaryScalar α *
        ((a * y * z + b * y + c * z + d) / (y * z) ^ α) ≤
      stableBoundaryScalar α *
        (((a * y + c) * (z + d / c)) / (y * z) ^ α) := hscaled
    _ = stableBoundaryScalar α *
        (((a * y + c) / y ^ α) * ((z + d / c) / z ^ α)) := by
          rw [hfactor]
    _ = stableBoundaryScalar α *
        ((a ^ α * c ^ (1 - α) / stableBoundaryScalar α) *
          ((d / c) ^ (1 - α) / stableBoundaryScalar α)) := by
            rw [hyvalue, hzvalue]
    _ = a ^ α * d ^ (1 - α) / stableBoundaryScalar α := hcollapse
    _ ≤ a + d := hfinal

/-- The strictly positive scalar lemma is sufficient after an arbitrarily
small coefficient regularization.  This is the version needed by the source
induction: no coefficient is assumed positive, and the conclusion loses only
an arbitrary additive `ε`. -/
theorem exists_bivariate_capacity_witness_nonnegative_interior
    {α a b c d ε : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hrayleigh : b * c ≤ a * d) (hε : 0 < ε) :
    ∃ y z : ℝ, 0 < y ∧ 0 < z ∧
      stableBoundaryScalar α *
          ((a * y * z + b * y + c * z + d) / (y * z) ^ α) ≤
        a + d + ε := by
  let δ : ℝ := ε / 4
  let c' : ℝ := c + δ ^ 2 / (b + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hb1 : 0 < b + 1 := by linarith
  have hc' : 0 < c' := by
    dsimp [c']
    exact add_pos_of_nonneg_of_pos hc (div_pos (sq_pos_of_pos hδ) hb1)
  have hrayleigh' : b * c' ≤ (a + δ) * (d + δ) := by
    have hfrac : b * (δ ^ 2 / (b + 1)) ≤ δ ^ 2 := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hb1).2
      nlinarith
    dsimp only [c']
    nlinarith [mul_nonneg ha hδ.le, mul_nonneg hd hδ.le]
  obtain ⟨y, z, hy, hz, hwitness⟩ :=
    exists_bivariate_capacity_witness hα0 hα1
      (add_pos_of_nonneg_of_pos ha hδ)
      hb hc' (add_pos_of_nonneg_of_pos hd hδ) hrayleigh'
  have hden : 0 < (y * z) ^ α :=
    Real.rpow_pos_of_pos (mul_pos hy hz) α
  have hpoly :
      a * y * z + b * y + c * z + d ≤
        (a + δ) * y * z + b * y + c' * z + (d + δ) := by
    have hcc' : c ≤ c' := by
      dsimp [c']
      exact le_add_of_nonneg_right (div_nonneg (sq_nonneg δ) hb1.le)
    nlinarith [mul_nonneg hy.le hz.le,
      mul_le_mul_of_nonneg_right hcc' hz.le]
  have hboundary : 0 ≤ stableBoundaryScalar α := by
    rw [stableBoundaryScalar]
    positivity
  refine ⟨y, z, hy, hz, ?_⟩
  calc
    stableBoundaryScalar α *
        ((a * y * z + b * y + c * z + d) / (y * z) ^ α) ≤
      stableBoundaryScalar α *
        (((a + δ) * y * z + b * y + c' * z + (d + δ)) /
          (y * z) ^ α) := by
            exact mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right hpoly hden.le) hboundary
    _ ≤ (a + δ) + (d + δ) := hwitness
    _ ≤ a + d + ε := by dsimp [δ]; linarith

/-- The endpoint `α = 0`: send both variables to zero. -/
theorem exists_bivariate_capacity_witness_zero
    {a b c d ε : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hε : 0 < ε) :
    ∃ y z : ℝ, 0 < y ∧ 0 < z ∧
      stableBoundaryScalar 0 *
          ((a * y * z + b * y + c * z + d) / (y * z) ^ (0 : ℝ)) ≤
        a + d + ε := by
  let s : ℝ := a + b + c + 1
  let t : ℝ := ε / ((ε + 1) * s)
  have hs : 0 < s := by dsimp [s]; linarith
  have hε1 : 0 < ε + 1 := by linarith
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    rw [div_le_one (mul_pos hε1 hs)]
    have hs1 : 1 ≤ s := by dsimp [s]; linarith
    nlinarith [mul_nonneg hε.le hs.le]
  have hsmall : (a + b + c) * t < ε := by
    dsimp [t]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (mul_pos hε1 hs)).2
    have hsum : a + b + c < s := by dsimp [s]; linarith
    have hs_scaled : s ≤ (ε + 1) * s := by
      nlinarith [mul_nonneg hε.le hs.le]
    simpa [mul_comm] using
      (mul_lt_mul_of_pos_left (hsum.trans_le hs_scaled) hε)
  refine ⟨t, t, ht, ht, ?_⟩
  rw [stableBoundaryScalar]
  norm_num
  have hatt : a * t * t ≤ a * t := by
    nlinarith [mul_nonneg ha ht.le]
  nlinarith

/-- The endpoint `α = 1`: send both variables to infinity. -/
theorem exists_bivariate_capacity_witness_one
    {a b c d ε : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hε : 0 < ε) :
    ∃ y z : ℝ, 0 < y ∧ 0 < z ∧
      stableBoundaryScalar 1 *
          ((a * y * z + b * y + c * z + d) / (y * z) ^ (1 : ℝ)) ≤
        a + d + ε := by
  let s : ℝ := b + c + d + 1
  let t : ℝ := (ε + 1) * s / ε
  have hs : 0 < s := by dsimp [s]; linarith
  have hε1 : 0 < ε + 1 := by linarith
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : 1 ≤ t := by
    dsimp [t]
    rw [le_div_iff₀ hε]
    have hs1 : 1 ≤ s := by dsimp [s]; linarith
    nlinarith [mul_nonneg hε.le hs.le]
  have hsmall : (b + c + d) / t < ε := by
    rw [div_lt_iff₀ ht]
    dsimp [t]
    have hsum : b + c + d < s := by dsimp [s]; linarith
    have hs_scaled : s ≤ (ε + 1) * s := by
      nlinarith [mul_nonneg hε.le hs.le]
    have hcancel : ε * ((ε + 1) * s / ε) = (ε + 1) * s := by
      field_simp [hε.ne']
    rw [hcancel]
    exact hsum.trans_le hs_scaled
  refine ⟨t, t, ht, ht, ?_⟩
  rw [stableBoundaryScalar]
  norm_num [Real.rpow_one]
  field_simp [ht.ne']
  have hdt : d ≤ d * t := by nlinarith [mul_nonneg hd (sub_nonneg.mpr ht1)]
  have hsmall' : (b + c + d) * t < ε * t ^ 2 := by
    rw [div_lt_iff₀ ht] at hsmall
    nlinarith
  nlinarith

/-- Complete bivariate scalar step, including both boundary exponents. -/
theorem exists_bivariate_capacity_witness_nonnegative
    {α a b c d ε : ℝ}
    (hα : 0 ≤ α ∧ α ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hrayleigh : b * c ≤ a * d) (hε : 0 < ε) :
    ∃ y z : ℝ, 0 < y ∧ 0 < z ∧
      stableBoundaryScalar α *
          ((a * y * z + b * y + c * z + d) / (y * z) ^ α) ≤
        a + d + ε := by
  rcases hα with ⟨hα0, hα1⟩
  rcases eq_or_lt_of_le hα0 with rfl | hαpos
  · exact exists_bivariate_capacity_witness_zero ha hb hc hd hε
  rcases eq_or_lt_of_le hα1 with rfl | hαlt
  · exact exists_bivariate_capacity_witness_one ha hb hc hd hε
  exact exists_bivariate_capacity_witness_nonnegative_interior
    hαpos hαlt ha hb hc hd hrayleigh hε

end BeyondBethe
