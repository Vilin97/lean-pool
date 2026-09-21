/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.BiholomorphicRigidity

import Mathlib.Tactic.Module

/-!
# Automorphisms of the Euclidean ball and the ball–polydisc distinction

The explicit involution exchanges an interior point with zero. Holomorphy, a nonvanishing
denominator, the metric identity, preservation of the ball, and involutivity are proved.
Packaging as a biholomorphism and transitivity are proved consequences, independent of Cartan
uniqueness and circular-domain rigidity. The ball–polydisc inequivalence follows independently
from Schwarz bounds on derivatives and the parallelogram identity in dimension at least two. The
source uses the supremum norm and the target uses `EuclideanSpace`, explicitly. References:
[Scheidemann][Scheidemann2005] (2005), Theorem 3.2.1 and Exercise 3.3.4.

## Main definitions

* `ballParallelComponent`: Projection onto the complex line through `a`, with value zero when `a =
  0`.
* `ballMobius`: The standard ball involution.
* `ballMobiusOpenPartialHomeomorph`: The standard involution as an equivalence of open unit balls,
  with an explicit formula.

## Main results

* `ballMobius_norm_identity`: The metric identity for the standard ball map, expressed without
  division.
* `mapsTo_ballMobius`: The standard ball map preserves the unit ball, by its metric identity.
* `ballMobius_ballMobius`: The ball automorphism is an involution of the unit ball, using the
  parallel and perpendicular components.
* `isBiholomorphic_ballMobius`: Both directions of the explicit ball equivalence are holomorphic.
* `exists_ball_automorphism`: The unit ball is homogeneous under biholomorphic automorphisms: any
  interior point can be sent to any other, by composing two explicit ball involutions.
* `not_exists_isBiholomorphic_polydisc_ball`: The Euclidean unit ball and the unit polydisc are not
  biholomorphic in dimension at least two.

## References

* [V. Scheidemann, *Introduction to Complex Analysis in Several Variables*][Scheidemann2005]
-/

public noncomputable section

open Set Metric
open scoped InnerProductSpace

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Projection onto the complex line through `a`, with value zero when `a = 0`. -/
@[expose] def ballParallelComponent (a z : E) : E :=
  (⟪a, z⟫_ℂ / (‖a‖ : ℂ) ^ 2) • a

/-- The standard ball involution. Mathlib's inner product is linear in its second argument; the
scalar in the perpendicular component is `sqrt (1 - ‖a‖²)`. -/
@[expose] def ballMobius (a z : E) : E :=
  (1 - ⟪a, z⟫_ℂ)⁻¹ •
    (a - ballParallelComponent a z -
      (Real.sqrt (1 - ‖a‖ ^ 2) : ℂ) • (z - ballParallelComponent a z))

/-- At the origin, the standard involution is negation, including dimension zero. -/
theorem ballMobius_zero (z : E) : ballMobius 0 z = -z := by
  simp [ballMobius, ballParallelComponent]

/-- The ball involution exchanges zero with its parameter. -/
theorem ballMobius_apply_zero (a : E) : ballMobius a 0 = a := by
  simp [ballMobius, ballParallelComponent]

/-- The ball involution sends its parameter to zero. -/
theorem ballMobius_apply_self (a : E) : ballMobius a a = 0 := by
  by_cases ha : a = 0
  · simp [ha, ballMobius_zero]
  · have hn : (‖a‖ : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast (norm_ne_zero_iff.mpr ha))
    simp [ballMobius, ballParallelComponent, inner_self_eq_norm_sq_to_K, div_self hn]

/-- The denominator in the ball involution is nonzero on the unit ball. -/
theorem ballMobius_denominator_ne_zero {a z : E} (ha : a ∈ ball 0 1) (hz : z ∈ ball 0 1) :
    1 - ⟪a, z⟫_ℂ ≠ 0 := by
  have ha' : ‖a‖ < 1 := by simpa only [mem_ball, dist_zero_right] using ha
  have hz' : ‖z‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hz
  have hi : ‖⟪a, z⟫_ℂ‖ < 1 := calc
    ‖⟪a, z⟫_ℂ‖ ≤ ‖a‖ * ‖z‖ := norm_inner_le_norm _ _
    _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right ha'.le (norm_nonneg _)
    _ < 1 := by simpa using hz'
  intro h
  have he := (sub_eq_zero.mp h).symm
  simp [he] at hi

/-- The projection formula is complex differentiable even for the zero parameter. -/
theorem differentiable_ballParallelComponent (a : E) : Differentiable ℂ (ballParallelComponent a)
  := by
  unfold ballParallelComponent
  simpa only [innerSL_apply_apply, div_eq_mul_inv] using
    ((innerSL ℂ a).differentiable.mul_const (((‖a‖ : ℂ) ^ 2)⁻¹)).smul_const a

/-- The explicit ball involution is holomorphic on the unit ball. -/
theorem differentiableOn_ballMobius {a : E} (ha : a ∈ ball 0 1) :
    DifferentiableOn ℂ (ballMobius a) (ball 0 1) := by
  intro z hz
  have hi : DifferentiableAt ℂ (fun w => ⟪a, w⟫_ℂ) z := (innerSL ℂ a).differentiableAt
  have hp := differentiable_ballParallelComponent a z
  exact ((((differentiableAt_const (1 : ℂ)).sub hi).inv
    (ballMobius_denominator_ne_zero ha hz)).smul
      (((differentiableAt_const a).sub hp).sub
        ((differentiableAt_const (Real.sqrt (1 - ‖a‖ ^ 2) : ℂ)).smul
          (differentiableAt_id.sub hp)))).differentiableWithinAt

/-- Orthogonal projection onto the parameter line preserves its inner product with the parameter. -/
theorem inner_ballParallelComponent (a z : E) :
    ⟪a, ballParallelComponent a z⟫_ℂ = ⟪a, z⟫_ℂ := by
  by_cases ha : a = 0
  · simp [ha]
  · have hn : (‖a‖ : ℂ) ^ 2 ≠ 0 := by exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr ha)
    simp [ballParallelComponent, inner_smul_right, inner_self_eq_norm_sq_to_K, hn]

/-- The squared norm of the parallel component, in a form valid also for a zero parameter. -/
theorem norm_ballParallelComponent_sq_mul (a z : E) :
    ‖ballParallelComponent a z‖ ^ 2 * ‖a‖ ^ 2 = ‖⟪a, z⟫_ℂ‖ ^ 2 := by
  by_cases ha : a = 0
  · simp [ha]
  · have hn := norm_ne_zero_iff.mpr ha
    simp only [ballParallelComponent, norm_smul, norm_div, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_norm]
    field_simp

/-- The metric identity for the standard ball map, expressed without division. -/
theorem ballMobius_norm_identity {a z : E} (ha : a ∈ ball 0 1) (hz : z ∈ ball 0 1) :
    (1 - ‖ballMobius a z‖ ^ 2) * ‖1 - ⟪a, z⟫_ℂ‖ ^ 2 =
      (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
  let p := ballParallelComponent a z
  let q := z - p
  let s := Real.sqrt (1 - ‖a‖ ^ 2)
  have ha' : ‖a‖ < 1 := by simpa using ha
  have hs : s ^ 2 = 1 - ‖a‖ ^ 2 := Real.sq_sqrt (by nlinarith [norm_nonneg a])
  have haq : ⟪a, q⟫_ℂ = 0 := by
    simp [q, p, inner_sub_right, inner_ballParallelComponent]
  have hpq : ⟪p, q⟫_ℂ = 0 := by
    simp only [p, ballParallelComponent, inner_smul_left, haq, mul_zero]
  have horth : ⟪a - p, (s : ℂ) • q⟫_ℂ = 0 := by
    simp only [inner_smul_right, inner_sub_left, haq, hpq, sub_self, mul_zero]
  have hq : ‖z‖ ^ 2 = ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
    have h := norm_add_sq (𝕜 := ℂ) p q
    simpa only [q, add_sub_cancel, hpq, map_zero, mul_zero, add_zero] using h
  have hp : ‖a - p‖ ^ 2 = ‖a‖ ^ 2 - 2 * (⟪a, z⟫_ℂ).re + ‖p‖ ^ 2 := by
    simpa only [p, inner_ballParallelComponent, RCLike.re_to_complex] using
      (norm_sub_sq (𝕜 := ℂ) a p)
  have hN : ‖a - p - (s : ℂ) • q‖ ^ 2 =
      ‖a‖ ^ 2 - 2 * (⟪a, z⟫_ℂ).re + ‖⟪a, z⟫_ℂ‖ ^ 2 +
        (1 - ‖a‖ ^ 2) * ‖z‖ ^ 2 := by
    have h := norm_sub_sq (𝕜 := ℂ) (a - p) ((s : ℂ) • q)
    simp only [horth, map_zero, mul_zero, sub_zero, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, sq_abs] at h
    have hpp := norm_ballParallelComponent_sq_mul a z
    change ‖p‖ ^ 2 * ‖a‖ ^ 2 = _ at hpp
    rw [hs, hp] at h
    nlinarith [hq]
  have hd : ‖1 - ⟪a, z⟫_ℂ‖ ≠ 0 := norm_ne_zero_iff.mpr (ballMobius_denominator_ne_zero ha hz)
  have hscale : ‖ballMobius a z‖ ^ 2 * ‖1 - ⟪a, z⟫_ℂ‖ ^ 2 =
      ‖a - p - (s : ℂ) • q‖ ^ 2 := by
    simp only [ballMobius, norm_smul, norm_inv, mul_pow, p, q, s]
    field_simp
  have hden : ‖1 - ⟪a, z⟫_ℂ‖ ^ 2 = 1 - 2 * (⟪a, z⟫_ℂ).re + ‖⟪a, z⟫_ℂ‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im]
    ring
  rw [hN] at hscale
  nlinarith

/-- The standard ball map preserves the unit ball, by its metric identity. -/
theorem mapsTo_ballMobius {a : E} (ha : a ∈ ball 0 1) :
    MapsTo (ballMobius a) (ball 0 1) (ball 0 1) := by
  intro z hz
  have ha' : ‖a‖ < 1 := by simpa using ha
  have hz' : ‖z‖ < 1 := by simpa using hz
  have hpos : 0 < (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) :=
    mul_pos (by nlinarith [norm_nonneg a]) (by nlinarith [norm_nonneg z])
  rw [← ballMobius_norm_identity ha hz] at hpos
  have hn : 0 < 1 - ‖ballMobius a z‖ ^ 2 :=
    pos_of_mul_pos_left hpos (sq_nonneg _)
  simpa only [mem_ball, dist_zero_right] using
    (show ‖ballMobius a z‖ < 1 by nlinarith [norm_nonneg (ballMobius a z)])

/-- The ball automorphism is an involution of the unit ball, using the parallel and perpendicular
components. -/
theorem ballMobius_ballMobius {a : E} (ha : a ∈ ball 0 1) :
    ∀ z ∈ ball 0 1, ballMobius a (ballMobius a z) = z := by
  intro z hz
  let s : ℂ := (Real.sqrt (1 - ‖a‖ ^ 2) : ℂ)
  let A : ℂ := (‖a‖ : ℂ) ^ 2
  let P : E →ₗ[ℂ] E := A⁻¹ • (innerSL ℂ a).toLinearMap.smulRight a
  let T : E →ₗ[ℂ] E := P + s • (LinearMap.id - P)
  have hP (w : E) : P w = ballParallelComponent a w := by
    simp only [P, A, LinearMap.smul_apply, LinearMap.smulRight_apply,
      ContinuousLinearMap.coe_coe, innerSL_apply_apply, ballParallelComponent, div_eq_mul_inv]
    module
  have hT (w : E) : T w = P w + s • (w - P w) := rfl
  have hiP (w : E) : ⟪a, P w⟫_ℂ = ⟪a, w⟫_ℂ := by
    rw [hP, inner_ballParallelComponent]
  have hiT (w : E) : ⟪a, T w⟫_ℂ = ⟪a, w⟫_ℂ := by
    simp only [hT, inner_add_right, inner_smul_right, inner_sub_right, hiP,
      sub_self, mul_zero, add_zero]
  have hPa : P a = a := by
    by_cases h : a = 0
    · simp [h]
    · have hn : A ≠ 0 := by dsimp [A]; exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr h)
      simp [hP, ballParallelComponent, inner_self_eq_norm_sq_to_K, A, hn]
  have hTa : T a = a := by rw [hT, hPa]; simp
  have hAP (w : E) : A • P w = ⟪a, w⟫_ℂ • a := by
    by_cases h : a = 0
    · simp [A, h]
    · have hn : A ≠ 0 := by dsimp [A]; exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr h)
      simp [P, smul_smul, hn]
  have hs : s ^ 2 = 1 - A := by
    have ha' : ‖a‖ < 1 := by simpa using ha
    have h := Real.sq_sqrt (show 0 ≤ 1 - ‖a‖ ^ 2 by nlinarith [norm_nonneg a])
    dsimp [s, A]
    exact_mod_cast h
  have hPT (w : E) : P (T w) = P w := by
    simp only [hP, ballParallelComponent, hiT]
  have hTT (w : E) : T (T w) = (1 - A) • w + ⟪a, w⟫_ℂ • a := by
    calc
      T (T w) = P w + s ^ 2 • (w - P w) := by rw [hT, hPT, hT]; module
      _ = (1 - A) • w + A • P w := by rw [hs]; module
      _ = _ := by rw [hAP]
  have hmob (w : E) : ballMobius a w = (1 - ⟪a, w⟫_ℂ)⁻¹ • (a - T w) := by
    rw [ballMobius, hT, hP]
    dsimp [s]
    module
  let c := ⟪a, z⟫_ℂ
  let d := 1 - c
  have hd : d ≠ 0 := ballMobius_denominator_ne_zero ha hz
  have hd' : 1 - ⟪a, ballMobius a z⟫_ℂ ≠ 0 :=
    ballMobius_denominator_ne_zero ha (mapsTo_ballMobius ha hz)
  have hden : d * (1 - ⟪a, ballMobius a z⟫_ℂ) = 1 - A := by
    rw [hmob]
    simp only [inner_smul_right, inner_sub_right, inner_self_eq_norm_sq_to_K, hiT]
    change d * (1 - d⁻¹ * (A - c)) = 1 - A
    field_simp
    dsimp [d]
    ring
  rw [hmob, inv_smul_eq_iff₀ hd']
  apply smul_right_injective E hd
  change d • (a - T (ballMobius a z)) = d • ((1 - ⟪a, ballMobius a z⟫_ℂ) • z)
  rw [smul_sub]
  conv_lhs => rw [hmob, map_smul, map_sub, hTa, hTT]
  change d • a - d • (d⁻¹ • (a - ((1 - A) • z + c • a))) =
    d • ((1 - ⟪a, ballMobius a z⟫_ℂ) • z)
  rw [smul_inv_smul₀ hd, smul_smul, hden]
  dsimp [d]
  module

/-- The standard involution as an equivalence of open unit balls, with an explicit formula. -/
@[expose] def ballMobiusOpenPartialHomeomorph (a : E) (ha : a ∈ ball 0 1) :
    OpenPartialHomeomorph E E where
  toFun := ballMobius a
  invFun := ballMobius a
  source := ball 0 1
  target := ball 0 1
  map_source' := mapsTo_ballMobius ha
  map_target' := mapsTo_ballMobius ha
  left_inv' := ballMobius_ballMobius ha
  right_inv' := ballMobius_ballMobius ha
  continuousOn_toFun := (differentiableOn_ballMobius ha).continuousOn
  continuousOn_invFun := (differentiableOn_ballMobius ha).continuousOn
  open_source := isOpen_ball
  open_target := isOpen_ball

/-- Both directions of the explicit ball equivalence are holomorphic. -/
theorem isBiholomorphic_ballMobius (a : E) (ha : a ∈ ball 0 1) :
    IsBiholomorphic (ballMobiusOpenPartialHomeomorph a ha) :=
  ⟨differentiableOn_ballMobius ha, differentiableOn_ballMobius ha⟩

/-- The unit ball is homogeneous under biholomorphic automorphisms: any interior point can be sent
to any other, by composing two explicit ball involutions. -/
theorem exists_ball_automorphism {a b : E}
    (ha : a ∈ ball 0 1) (hb : b ∈ ball 0 1) :
    ∃ e : OpenPartialHomeomorph E E, IsBiholomorphic e ∧
      e.source = ball 0 1 ∧ e.target = ball 0 1 ∧ e a = b := by
  let A := ballMobiusOpenPartialHomeomorph a ha
  let B := ballMobiusOpenPartialHomeomorph b hb
  refine ⟨A.trans B, (isBiholomorphic_ballMobius a ha).trans (isBiholomorphic_ballMobius b hb),
    ?_, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.trans_source]
    exact inter_eq_left.mpr (mapsTo_ballMobius ha)
  · rw [OpenPartialHomeomorph.trans_target]
    exact inter_eq_left.mpr (mapsTo_ballMobius hb)
  · change ballMobius b (ballMobius a a) = b
    rw [ballMobius_apply_self a, ballMobius_apply_zero]

/-- The derivative at zero of an origin-preserving biholomorphism between unit balls preserves
norms. Schwarz bounds for the map and its inverse prove both inequalities, without Cartan
uniqueness or finite-dimensional assumptions. -/
theorem IsBiholomorphic.norm_fderiv_apply_eq_of_unit_ball
    {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    {e : OpenPartialHomeomorph A B} (he : IsBiholomorphic e)
    (hs : e.source = ball 0 1) (ht : e.target = ball 0 1) (hfix : e 0 = 0)
    (x : A) : ‖fderiv ℂ e 0 x‖ = ‖x‖ := by
  have hzero : (0 : A) ∈ e.source := by rw [hs]; exact mem_ball_self zero_lt_one
  have hinv : e.symm 0 = 0 := by simpa [hfix] using e.left_inv hzero
  have hd : ‖fderiv ℂ e 0‖ ≤ 1 :=
    Complex.norm_fderiv_le_one_of_mapsTo_ball (hs ▸ he.1)
      (fun z hz => by
        rw [hfix]
        exact ball_subset_closedBall (ht ▸ e.map_source (hs ▸ hz))) zero_lt_one
  have hi : ‖fderiv ℂ e.symm 0‖ ≤ 1 :=
    Complex.norm_fderiv_le_one_of_mapsTo_ball (ht ▸ he.2)
      (fun z hz => by
        rw [hinv]
        exact ball_subset_closedBall (hs ▸ e.map_target (ht ▸ hz))) zero_lt_one
  have hleft : fderiv ℂ e.symm 0 (fderiv ℂ e 0 x) = x := by
    simpa [hfix] using DFunLike.congr_fun (he.fderiv_symm_comp hzero) x
  apply le_antisymm
  · simpa using (fderiv ℂ e 0).le_of_opNorm_le_of_le hd (le_refl ‖x‖)
  · calc
      ‖x‖ = ‖fderiv ℂ e.symm 0 (fderiv ℂ e 0 x)‖ := congrArg norm hleft.symm
      _ ≤ ‖fderiv ℂ e 0 x‖ := by
        simpa using (fderiv ℂ e.symm 0).le_of_opNorm_le_of_le hi
          (le_refl ‖fderiv ℂ e 0 x‖)

/-- The Euclidean unit ball and the unit polydisc are not biholomorphic in dimension at least two.
Normalize at zero using a ball automorphism; Schwarz's lemma makes the derivative
norm-preserving, contradicting the parallelogram identity. This proof is independent of Cartan
uniqueness. The dimension hypothesis excludes the singleton and one-variable cases. -/
theorem not_exists_isBiholomorphic_polydisc_ball {ι : Type*} [Fintype ι]
    (hdim : 2 ≤ Fintype.card ι) :
    ¬ ∃ e : OpenPartialHomeomorph (ι → ℂ) (EuclideanSpace ℂ ι),
      IsBiholomorphic e ∧ e.source = ball 0 1 ∧ e.target = ball 0 1 := by
  classical
  rintro ⟨e, he, hs, ht⟩
  have hzero : (0 : ι → ℂ) ∈ e.source := by rw [hs]; exact mem_ball_self zero_lt_one
  have ha : e 0 ∈ ball 0 1 := ht ▸ e.map_source hzero
  let M := ballMobiusOpenPartialHomeomorph (e 0) ha
  let g := e.trans M
  have hg : IsBiholomorphic g := he.trans (isBiholomorphic_ballMobius (e 0) ha)
  have hgs : g.source = ball 0 1 := by
    rw [OpenPartialHomeomorph.trans_source]
    change e.source ∩ e ⁻¹' ball 0 1 = ball 0 1
    rw [← ht]
    exact (inter_eq_left.mpr (fun z hz => e.map_source hz)).trans hs
  have hgt : g.target = ball 0 1 := by
    rw [OpenPartialHomeomorph.trans_target]
    change ball 0 1 ∩ (ballMobius (e 0)) ⁻¹' e.target = ball 0 1
    rw [ht]
    exact inter_eq_left.mpr (mapsTo_ballMobius ha)
  have hg0 : g 0 = 0 := ballMobius_apply_self (e 0)
  let L := fderiv ℂ g 0
  have hL (x : ι → ℂ) : ‖L x‖ = ‖x‖ :=
    hg.norm_fderiv_apply_eq_of_unit_ball hgs hgt hg0 x
  obtain ⟨i, j, hij⟩ := Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card ι)
  let u : ι → ℂ := Pi.single i 1
  let v : ι → ℂ := Pi.single j 1
  have hu : ‖u‖ = 1 := by simp [u, Pi.norm_single]
  have hv : ‖v‖ = 1 := by simp [v, Pi.norm_single]
  have hnorm (c : ℂ) (hc : ‖c‖ = 1) : ‖u + c • v‖ = 1 := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
      intro k
      by_cases hki : k = i
      · subst k
        simp [u, v, hij]
      · by_cases hkj : k = j
        · subst k
          simp [u, v, hij.symm, hc]
        · simp [u, v, hki, hkj]
    · simpa [u, v, Pi.single_apply, hij] using norm_le_pi_norm (u + c • v) i
  have hadd : ‖u + v‖ = 1 := by simpa using hnorm 1 (by simp)
  have hsub : ‖u - v‖ = 1 := by simpa [sub_eq_add_neg] using hnorm (-1) (by simp)
  have hp := parallelogram_law_with_norm ℂ (L u) (L v)
  rw [← map_add, ← map_sub, hL, hL, hL, hL, hu, hv, hadd, hsub] at hp
  norm_num at hp

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
