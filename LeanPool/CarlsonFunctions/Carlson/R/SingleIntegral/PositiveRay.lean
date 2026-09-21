/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.R.SingleIntegral.Continuation

/-! # Positive-ray representation and its change of variables -/

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Classical Topology
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- The positive-ray form of Carlson's single-integral representation. -/
def carlsonRPositiveRayIntegral (a : ℂ) (b z : ι → ℂ) : ℂ :=
  ∫ s : ℝ in Set.Ioi 0,
    (s : ℂ) ^ (a - 1) * ∏ i, (z i + (s : ℂ)) ^ (-b i)

/-- The reciprocal translation `s ↦ (s + 1)⁻¹` maps the positive ray onto the open unit
interval. -/
private lemma image_recip_add_one_Ioi :
    (fun s : ℝ => (s + 1)⁻¹) '' Set.Ioi 0 = Set.Ioo 0 1 := by
  ext u
  constructor
  · rintro ⟨s, hs, rfl⟩
    change 0 < s at hs
    constructor
    · exact inv_pos.mpr (by linarith)
    · rw [inv_lt_one₀ (by linarith : 0 < s + 1)]
      linarith
  · intro hu
    refine ⟨u⁻¹ - 1, ?_, ?_⟩
    · change 0 < u⁻¹ - 1
      rw [sub_pos]
      exact (one_lt_inv₀ hu.1).2 hu.2
    · have hu0 : u ≠ 0 := hu.1.ne'
      field_simp
      ring

/-- The reciprocal translation is injective on the positive ray. -/
private lemma injOn_recip_add_one :
    Set.InjOn (fun s : ℝ => (s + 1)⁻¹) (Set.Ioi 0) := by
  intro x hx y hy hxy
  change 0 < x at hx
  change 0 < y at hy
  have hx0 : x + 1 ≠ 0 := by linarith
  have hy0 : y + 1 ≠ 0 := by linarith
  exact add_right_cancel (inv_injective hxy)

/-- Derivative of the reciprocal translation on the positive ray. -/
private lemma hasDerivAt_recip_add_one (s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun x : ℝ => (x + 1)⁻¹) (-((s + 1) ^ 2)⁻¹) s := by
  have hs0 : s + 1 ≠ 0 := by linarith
  convert! ((hasDerivAt_id s).add_const 1 |>.inv hs0) using 1
  all_goals simp only [id_eq]
  all_goals ring

/-- Complex powers split over a product whose first factor is a positive real number. -/
private lemma ofReal_mul_cpow {r : ℝ} (hr : 0 < r) {x e : ℂ} (hx : x ≠ 0) :
    ((r : ℂ) * x) ^ e = (r : ℂ) ^ e * x ^ e := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hr0 hx),
    Complex.cpow_def_of_ne_zero hr0, Complex.cpow_def_of_ne_zero hx,
    Complex.log_ofReal_mul hr hx, ofReal_log hr.le, add_mul, Complex.exp_add]

omit [Fintype ι] in
/-- A finite product of complex powers with the same nonzero base combines by adding the
exponents. -/
private lemma prod_cpow_same_base
    (s : Finset ι) (r : ℂ) (hr : r ≠ 0) (e : ι → ℂ) :
    ∏ i ∈ s, r ^ e i = r ^ (∑ i ∈ s, e i) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, ← Complex.cpow_add _ _ hr]
/-- Pointwise form of the reciprocal-translation substitution relating Carlson's ray and
unit-interval integrands. -/
private lemma ray_substitution_point
    {a a' : ℂ} {b z : ι → ℂ}
    (hsum : a + a' = ∑ i, b i) (hz : z ∈ carlsonRVariableDomain)
    {s : ℝ} (hs : s ∈ Set.Ioi 0) :
    |-((s + 1) ^ 2)⁻¹| •
        (((((s + 1)⁻¹ : ℝ) : ℂ) ^ (a' - 1) *
          (1 - (((s + 1)⁻¹ : ℝ) : ℂ)) ^ (a - 1)) *
          ∏ i, ((1 - (((s + 1)⁻¹ : ℝ) : ℂ)) +
            (((s + 1)⁻¹ : ℝ) : ℂ) * z i) ^ (-b i)) =
      (s : ℂ) ^ (a - 1) * ∏ i, (z i + (s : ℂ)) ^ (-b i) := by
  change 0 < s at hs
  let d : ℝ := s + 1
  let r : ℝ := d⁻¹
  have hd : 0 < d := by dsimp [d]; linarith
  have hr : 0 < r := inv_pos.mpr hd
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  have habs : |-((s + 1) ^ 2)⁻¹| = r ^ 2 := by
    dsimp [r, d]
    rw [abs_neg, abs_inv, abs_pow, abs_of_pos (by linarith : 0 < s + 1), inv_pow]
  have hone : (1 : ℂ) - (r : ℂ) = (r : ℂ) * (s : ℂ) := by
    have hreal : 1 - r = r * s := by
      dsimp [r, d]
      field_simp
      ring
    exact_mod_cast hreal
  have hq (i : ι) : (1 : ℂ) - (r : ℂ) + (r : ℂ) * z i =
      (r : ℂ) * (z i + (s : ℂ)) := by
    rw [hone]
    ring
  have hzi (i : ι) : z i + (s : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [add_re, ofReal_re, zero_re] at hre
    have := hz i
    dsimp only [carlsonRightHalfPlane, Set.mem_ofPred_eq] at this
    linarith
  have hprod :
      (∏ i, ((r : ℂ) * (z i + (s : ℂ))) ^ (-b i)) =
        (r : ℂ) ^ (∑ i, -b i) * ∏ i, (z i + (s : ℂ)) ^ (-b i) := by
    simp_rw [ofReal_mul_cpow hr (hzi _)]
    rw [Finset.prod_mul_distrib, prod_cpow_same_base Finset.univ (r : ℂ) hr0]
  have hexp : (2 : ℂ) + (a' - 1) + (a - 1) + ∑ i, -b i = 0 := by
    rw [Finset.sum_neg_distrib, ← hsum]
    ring
  have hrpow : (r : ℂ) ^ (2 : ℕ) * (r : ℂ) ^ (a' - 1) *
      (r : ℂ) ^ (a - 1) * (r : ℂ) ^ (∑ i, -b i) = 1 := by
    rw [← Complex.cpow_natCast]
    rw [← Complex.cpow_add _ _ hr0, ← Complex.cpow_add _ _ hr0,
      ← Complex.cpow_add _ _ hr0]
    have hexp' : ((2 : ℕ) : ℂ) + (a' - 1) + (a - 1) + ∑ i, -b i = 0 := by
      simpa only [Nat.cast_ofNat] using hexp
    rw [hexp', Complex.cpow_zero]
  rw [habs]
  change (r ^ 2 : ℝ) • _ = _
  rw [Complex.real_smul]
  rw [show ((r ^ 2 : ℝ) : ℂ) = (r : ℂ) ^ (2 : ℕ) by norm_cast]
  change (r : ℂ) ^ (2 : ℕ) *
      (((r : ℂ) ^ (a' - 1) * ((1 : ℂ) - (r : ℂ)) ^ (a - 1)) *
        ∏ i, ((1 : ℂ) - (r : ℂ) + (r : ℂ) * z i) ^ (-b i)) = _
  rw [show
      (fun i => ((1 : ℂ) - (r : ℂ) + (r : ℂ) * z i) ^ (-b i)) =
        fun i => ((r : ℂ) * (z i + (s : ℂ))) ^ (-b i) by
          funext i
          rw [hq i], hprod, hone, Complex.mul_cpow_ofReal_nonneg hr.le hs.le]
  calc
    (r : ℂ) ^ (2 : ℕ) *
        (((r : ℂ) ^ (a' - 1) *
          ((r : ℂ) ^ (a - 1) * (s : ℂ) ^ (a - 1))) *
          ((r : ℂ) ^ (∑ i, -b i) * ∏ i, (z i + (s : ℂ)) ^ (-b i))) =
        ((r : ℂ) ^ (2 : ℕ) * (r : ℂ) ^ (a' - 1) *
          (r : ℂ) ^ (a - 1) * (r : ℂ) ^ (∑ i, -b i)) *
          ((s : ℂ) ^ (a - 1) * ∏ i, (z i + (s : ℂ)) ^ (-b i)) := by ring
    _ = _ := by rw [hrpow, one_mul]

/-- Under the balancing relation, reciprocal translation identifies the positive-ray
integral with the unit-interval integral having its beta exponents interchanged. -/
theorem carlsonRPositiveRayIntegral_eq_unitInterval
    {a a' : ℂ} {b z : ι → ℂ}
    (hsum : a + a' = ∑ i, b i) (hz : z ∈ carlsonRVariableDomain) :
    carlsonRPositiveRayIntegral a b z = carlsonRUnitIntervalIntegral a' a b z := by
  let φ : ℝ → ℝ := fun s => (s + 1)⁻¹
  let φ' : ℝ → ℝ := fun s => -((s + 1) ^ 2)⁻¹
  let g : ℝ → ℂ := fun u =>
    ((u : ℂ) ^ (a' - 1) * (1 - u : ℂ) ^ (a - 1)) *
      ∏ i, ((1 - u : ℂ) + (u : ℂ) * z i) ^ (-b i)
  have hchange := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi
    (fun s hs => (hasDerivAt_recip_add_one s hs).hasDerivWithinAt)
    injOn_recip_add_one g
  rw [show φ '' Set.Ioi 0 = Set.Ioo 0 1 by
      simpa [φ] using image_recip_add_one_Ioi] at hchange
  have hright : (∫ s : ℝ in Set.Ioi 0, |φ' s| • g (φ s)) =
      carlsonRPositiveRayIntegral a b z := by
    unfold carlsonRPositiveRayIntegral
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    simpa [φ, φ', g] using ray_substitution_point hsum hz hs
  rw [hright] at hchange
  exact hchange.symm.trans <| by
    unfold carlsonRUnitIntervalIntegral
    simp [g]

/-- Carlson's Theorem 6.8-1 in positive-ray form. -/
theorem carlsonRPositiveRayIntegral_eq
    {a a' : ℂ} {b z : ι → ℂ}
    (ha : 0 < a.re) (ha' : 0 < a'.re)
    (hsum : a + a' = ∑ i, b i)
    (hb : b ∈ mvBetaConvergent)
    (hz : z ∈ carlsonRVariableDomain) :
    carlsonRPositiveRayIntegral a b z =
      betaIntegral a a' * carlsonRIntegral (-a') b z := by
  rw [carlsonRPositiveRayIntegral_eq_unitInterval hsum hz]
  rw [carlsonRUnitIntervalIntegral_eq ha' ha (by simpa [add_comm] using hsum) hb hz]
  rw [betaIntegral_symm]

/-- The positive-ray representation with no individual Dirichlet-parameter
restrictions; only the two endpoint convergence conditions remain. -/
theorem carlsonRPositiveRayIntegral_eq_gamma_mul_continued
    {a a' : ℂ} {b z : ι → ℂ}
    (ha : 0 < a.re) (ha' : 0 < a'.re)
    (hsum : a + a' = ∑ i, b i) (hz : z ∈ carlsonRVariableDomain) :
    carlsonRPositiveRayIntegral a b z =
      (Gamma a * Gamma a') * regCarlsonRContinued (-a') z hz b := by
  rw [carlsonRPositiveRayIntegral_eq_unitInterval hsum hz,
    carlsonRUnitIntervalIntegral_eq_gamma_mul_continued ha' ha
      (by simpa [add_comm] using hsum) hz, mul_comm (Gamma a')]

end DirichletTransform
