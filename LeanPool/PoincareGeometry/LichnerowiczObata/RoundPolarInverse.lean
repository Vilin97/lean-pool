/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.RoundPolarCoordinates
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! # Recovering polar data from a point away from the poles -/

@[expose] public noncomputable section

namespace LichnerowiczObata

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Off the two poles, the height of a unit sphere point is strictly
between minus one and one. -/
theorem unit_sphere_height_strict (p y : E) (hp : ‖p‖ = 1) (hy : ‖y‖ = 1)
    (hn : y ≠ p) (hs : y ≠ -p) : -1 < inner ℝ p y ∧ inner ℝ p y < 1 := by
  have hsub := norm_sub_sq_real y p
  have hadd := norm_add_sq_real y p
  rw [hy, hp, real_inner_comm p y] at hsub hadd
  have hsubpos : 0 < ‖y - p‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hn))
  have haddne : y + p ≠ 0 := by
    intro he
    exact hs (eq_neg_of_add_eq_zero_left he)
  have haddpos : 0 < ‖y + p‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr haddne)
  constructor <;> nlinarith

/-- An explicit angular direction and arccosine angle reconstruct every
non-polar unit sphere point. -/
theorem unit_sphere_polar_decomposition (p y : E) (hp : ‖p‖ = 1) (hy : ‖y‖ = 1)
    (hn : y ≠ p) (hs : y ≠ -p) :
    ∃ q : E, ‖q‖ = 1 ∧ inner ℝ p q = 0 ∧
      Real.arccos (inner ℝ p y) ∈ Set.Ioo 0 Real.pi ∧
      y = Real.cos (Real.arccos (inner ℝ p y)) • p +
        Real.sin (Real.arccos (inner ℝ p y)) • q := by
  let c := inner ℝ p y
  let θ := Real.arccos c
  let v := y - c • p
  have hc := unit_sphere_height_strict p y hp hy hn hs
  have hθ : θ ∈ Set.Ioo 0 Real.pi :=
    ⟨Real.arccos_pos.mpr hc.2, Real.arccos_lt_pi.mpr hc.1⟩
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hcos : Real.cos θ = c := Real.cos_arccos hc.1.le hc.2.le
  have hperp : inner ℝ p v = 0 := by
    simp [v, inner_sub_right, real_inner_smul_right, hp, c]
  have hnorm : ‖v‖ ^ 2 = 1 - c ^ 2 := by
    dsimp only [v]
    rw [norm_sub_sq_real]
    simp only [hy, norm_smul, Real.norm_eq_abs, hp, mul_one, sq_abs,
      real_inner_smul_right]
    rw [real_inner_comm p y]
    dsimp only [c]
    ring
  have hvnorm : ‖v‖ = Real.sin θ := by
    have htrig := Real.sin_sq_add_cos_sq θ
    rw [hcos] at htrig
    nlinarith [norm_nonneg v]
  refine ⟨(Real.sin θ)⁻¹ • v, ?_, ?_, hθ, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsin), hvnorm]
    exact inv_mul_cancel₀ hsin.ne'
  · rw [real_inner_smul_right, hperp, mul_zero]
  · change y = Real.cos θ • p + Real.sin θ • ((Real.sin θ)⁻¹ • v)
    rw [hcos, smul_smul, mul_inv_cancel₀ hsin.ne', one_smul]
    dsimp only [v]
    abel

/-- Every actual sphere point other than the two poles has polar coordinates. -/
theorem roundPolarMap_surjective_off_poles {R : ℝ} (hR : 0 < R) (p : E)
    (hp : ‖p‖ = 1) (x : Metric.sphere (0 : E) R)
    (hn : (x : E) ≠ R • p) (hs : (x : E) ≠ -(R • p)) :
    ∃ a, roundPolarMap hR p hp a = x := by
  let y : E := R⁻¹ • (x : E)
  have hxnorm : ‖(x : E)‖ = R := by
    simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  have hy : ‖y‖ = 1 := by
    simp only [y, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR), hxnorm]
    exact inv_mul_cancel₀ hR.ne'
  have hscale : R • y = (x : E) := by
    simp only [y, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  have hyn : y ≠ p := by
    intro he
    exact hn (by rw [← hscale, he])
  have hys : y ≠ -p := by
    intro he
    exact hs (by rw [← hscale, he, smul_neg])
  obtain ⟨q, hq, hpq, hθ, he⟩ := unit_sphere_polar_decomposition p y hp hy hyn hys
  let θ := Real.arccos (inner ℝ p y)
  have hrange : R * θ ∈ Set.Ioo 0 (Real.pi * R) := by
    exact ⟨mul_pos hR hθ.1, by nlinarith [hθ.2]⟩
  refine ⟨(⟨q, hq, hpq⟩, ⟨R * θ, hrange⟩), ?_⟩
  apply Subtype.ext
  change roundPolarCurve R p q (R * θ) = (x : E)
  have harg : R * θ / R = θ := by field_simp
  rw [roundPolarCurve, harg, ← he]
  exact hscale

/-- The open radial interval omits both poles. -/
theorem roundPolarCurve_ne_poles {R : ℝ} (hR : 0 < R) (p q : E)
    (hp : ‖p‖ = 1) (hpq : inner ℝ p q = 0) {s : ℝ}
    (hs : s ∈ Set.Ioo 0 (Real.pi * R)) :
    roundPolarCurve R p q s ≠ R • p ∧ roundPolarCurve R p q s ≠ -(R • p) := by
  have hθ : 0 < s / R ∧ s / R < Real.pi :=
    ⟨div_pos hs.1 hR, (div_lt_iff₀ hR).mpr hs.2⟩
  have hi := Real.arccos_cos hθ.1.le hθ.2.le
  constructor
  · intro he
    have hh := congrArg (fun x => inner ℝ p x) he
    rw [roundPolarCurve_height R s p q hp hpq] at hh
    have hc : Real.cos (s / R) = 1 := by
      have hp' : inner ℝ p p = 1 := by simp [hp]
      rw [real_inner_smul_right, hp', mul_one] at hh
      exact (mul_left_cancel₀ hR.ne') (hh.trans (mul_one R).symm)
    rw [hc, Real.arccos_one] at hi
    linarith [hθ.1]
  · intro he
    have hh := congrArg (fun x => inner ℝ p x) he
    rw [roundPolarCurve_height R s p q hp hpq] at hh
    have hc : Real.cos (s / R) = -1 := by
      have hp' : inner ℝ p p = 1 := by simp [hp]
      rw [inner_neg_right, real_inner_smul_right, hp', mul_one] at hh
      apply (mul_left_cancel₀ hR.ne')
      simpa using hh
    rw [hc, Real.arccos_neg_one] at hi
    linarith [hθ.2]

/-- The sphere with its two polar points removed. -/
abbrev RoundPuncturedSphere (R : ℝ) (p : E) :=
  {x : Metric.sphere (0 : E) R // (x : E) ≠ R • p ∧ (x : E) ≠ -(R • p)}

def roundPolarPuncturedMap {R : ℝ} (hR : 0 < R) (p : E) (hp : ‖p‖ = 1)
    (a : RoundPolarDirections p × Set.Ioo (0 : ℝ) (Real.pi * R)) :
    RoundPuncturedSphere R p :=
  ⟨roundPolarMap hR p hp a,
    roundPolarCurve_ne_poles hR p a.1.1 hp a.1.2.2 a.2.2⟩

theorem roundPolarPuncturedMap_bijective {R : ℝ} (hR : 0 < R) (p : E) (hp : ‖p‖ = 1) :
    Function.Bijective (roundPolarPuncturedMap hR p hp) := by
  constructor
  · intro a b he
    exact roundPolarMap_injective hR p hp (congrArg Subtype.val he)
  · intro x
    obtain ⟨a, ha⟩ := roundPolarMap_surjective_off_poles hR p hp x.1 x.2.1 x.2.2
    exact ⟨a, Subtype.ext ha⟩

/-- Set-theoretic polar coordinates of the punctured sphere. -/
def roundPolarEquiv {R : ℝ} (hR : 0 < R) (p : E) (hp : ‖p‖ = 1) :
    (RoundPolarDirections p × Set.Ioo (0 : ℝ) (Real.pi * R)) ≃ RoundPuncturedSphere R p :=
  Equiv.ofBijective (roundPolarPuncturedMap hR p hp) (roundPolarPuncturedMap_bijective hR p hp)

theorem continuous_roundPolarPuncturedMap {R : ℝ} (hR : 0 < R) (p : E) (hp : ‖p‖ = 1) :
    Continuous (roundPolarPuncturedMap hR p hp) :=
  (continuous_roundPolarMap hR p hp).subtype_mk _

end LichnerowiczObata
