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

public import LeanPool.PoincareGeometry.LichnerowiczObata.RoundPolarMetric

/-! # Uniqueness of round-sphere polar coordinates away from the poles -/

@[expose] public noncomputable section

namespace LichnerowiczObata

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Height above the equatorial hyperplane recovers the cosine of radius. -/
theorem roundPolarCurve_height (R s : ℝ) (p q : E)
    (hp : ‖p‖ = 1) (hpq : inner ℝ p q = 0) :
    inner ℝ p (roundPolarCurve R p q s) = R * Real.cos (s / R) := by
  simp [roundPolarCurve, inner_add_right, real_inner_smul_right,
    hp, hpq]

/-- In the open pole-to-pole interval, both radius and angular direction
are determined by the actual point on the sphere. -/
theorem roundPolarCurve_coordinates_unique {R : ℝ} (hR : 0 < R) (p q₁ q₂ : E)
    (hp : ‖p‖ = 1) (hpq₁ : inner ℝ p q₁ = 0) (hpq₂ : inner ℝ p q₂ = 0)
    {s₁ s₂ : ℝ} (hs₁ : s₁ ∈ Set.Ioo 0 (Real.pi * R))
    (hs₂ : s₂ ∈ Set.Ioo 0 (Real.pi * R))
    (he : roundPolarCurve R p q₁ s₁ = roundPolarCurve R p q₂ s₂) :
    s₁ = s₂ ∧ q₁ = q₂ := by
  have hh := congrArg (fun x => inner ℝ p x) he
  rw [roundPolarCurve_height R s₁ p q₁ hp hpq₁,
    roundPolarCurve_height R s₂ p q₂ hp hpq₂] at hh
  have hc : Real.cos (s₁ / R) = Real.cos (s₂ / R) := mul_left_cancel₀ hR.ne' hh
  have ht₁ : s₁ / R ∈ Set.Icc 0 Real.pi :=
    ⟨(div_pos hs₁.1 hR).le, (div_lt_iff₀ hR).mpr hs₁.2 |>.le⟩
  have ht₂ : s₂ / R ∈ Set.Icc 0 Real.pi :=
    ⟨(div_pos hs₂.1 hR).le, (div_lt_iff₀ hR).mpr hs₂.2 |>.le⟩
  have hs : s₁ = s₂ := (div_left_inj' hR.ne').mp (Real.injOn_cos ht₁ ht₂ hc)
  refine ⟨hs, ?_⟩
  subst s₂
  have hsin : Real.sin (s₁ / R) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (div_pos hs₁.1 hR) ((div_lt_iff₀ hR).mpr hs₁.2)).ne'
  unfold roundPolarCurve at he
  have hsum := (smul_right_injective E hR.ne') he
  have hang := add_left_cancel hsum
  exact (smul_right_injective E hsin) hang

/-- Unit angular directions perpendicular to the chosen pole. -/
abbrev RoundPolarDirections (p : E) := {q : E // ‖q‖ = 1 ∧ inner ℝ p q = 0}

/-- The actual sphere-valued polar parametrization on the open radial range. -/
def roundPolarMap {R : ℝ} (hR : 0 < R) (p : E) (hp : ‖p‖ = 1)
    (a : RoundPolarDirections p × Set.Ioo (0 : ℝ) (Real.pi * R)) :
    Metric.sphere (0 : E) R :=
  ⟨roundPolarCurve R p a.1.1 a.2.1,
    roundPolarCurve_mem_sphere hR p a.1.1 hp a.1.2.1 a.1.2.2 a.2.1⟩

/-- No two polar coordinate pairs represent the same sphere point. -/
theorem roundPolarMap_injective {R : ℝ} (hR : 0 < R) (p : E) (hp : ‖p‖ = 1) :
    Function.Injective (roundPolarMap hR p hp) := by
  intro a b hab
  have he := congrArg Subtype.val hab
  have hh := roundPolarCurve_coordinates_unique hR p a.1.1 b.1.1 hp
    a.1.2.2 b.1.2.2 a.2.2 b.2.2 he
  exact Prod.ext (Subtype.ext hh.2) (Subtype.ext hh.1)

theorem continuous_roundPolarMap {R : ℝ} (hR : 0 < R) (p : E) (hp : ‖p‖ = 1) :
    Continuous (roundPolarMap hR p hp) := by
  unfold roundPolarMap roundPolarCurve
  fun_prop

end LichnerowiczObata
