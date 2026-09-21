/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.NormalLevelHomeomorph
public import LeanPool.PoincareGeometry.LichnerowiczObata.RadialProduct

/-! # Product coordinates retaining the actual normal-flow map -/

@[expose] public noncomputable section
open Set
open scoped Topology

namespace LichnerowiczObata

/-- A normal chart and a complete radial family supply a spherical product
whose forward map is exactly normal coordinates followed by radial transport.
The radius and whole-level coverage are constructed using compactness. -/
theorem exists_normal_radial_product_map {E M : Type*} [NormedAddCommGroup E]
    [TopologicalSpace M] [CompactSpace M] (e : OpenPartialHomeomorph E M)
    (he0 : (0 : E) ∈ e.source) {ρ : M → ℝ} (hcρ : Continuous ρ)
    (hn : ∀ x, 0 ≤ ρ x) (hz : ∀ x, ρ x = 0 ↔ x = e 0)
    {t ℓ : ℝ} (ht : 0 < t) (hℓ : 0 < ℓ)
    (helevel : ∀ v ∈ e.source, ρ (e v) = t * ‖v‖)
    (U : Set M) (hU : ∀ x, x ∈ U ↔ ρ x ∈ Ioo 0 ℓ)
    (η : M × ℝ → M) (hcη : ContinuousOn η (U ×ˢ Ioo 0 ℓ))
    (hlevel : ∀ x ∈ U, ∀ r ∈ Ioo 0 ℓ, ρ (η (x, r)) = r)
    (hinit : ∀ x ∈ U, η (x, ρ x) = x)
    (hreset : ∀ x ∈ U, ∀ r ∈ Ioo 0 ℓ, ∀ s ∈ Ioo 0 ℓ, η (η (x, r), s) = η (x, s)) :
    ∃ R : ℝ, 0 < R ∧ t * R ∈ Ioo 0 ℓ ∧
      Metric.ball (0 : E) (2 * R) ⊆ e.source ∧
      (∀ v : Metric.sphere (0 : E) R, (v : E) ∈ e.source) ∧
      ∃ H : Metric.sphere (0 : E) R × Ioo 0 ℓ ≃ₜ U,
      ∀ z, (H z : M) = η (e z.1, z.2) := by
  obtain ⟨ε, hε, hball, hsmall⟩ := exists_small_sphere_level_homeomorph_map e he0 hcρ hn hz ht helevel
  let r := min ε ℓ / 2
  have hr : 0 < r := div_pos (lt_min hε hℓ) (by norm_num)
  have hre : r < ε := by
    have := min_le_left ε ℓ
    dsimp [r] at *
    linarith
  have hrℓ : r < ℓ := by
    have := min_le_right ε ℓ
    dsimp [r] at *
    linarith
  obtain ⟨s, hsource, hs⟩ := hsmall r ⟨hr, hre⟩
  have hρ : ∀ x ∈ U, ρ x ∈ Ioo 0 ℓ := fun x hx => (hU x).mp hx
  have hη : ∀ x ∈ U, ∀ r ∈ Ioo 0 ℓ, η (x, r) ∈ U := by
    intro x hx r hr
    apply (hU _).mpr
    rw [hlevel x hx r hr]
    exact hr
  have hwhole : ∀ x, ρ x = r → x ∈ U := by
    intro x hx
    apply (hU x).mpr
    rw [hx]
    exact ⟨hr, hrℓ⟩
  let A := s.trans (wholeLevelHomeomorph U ρ r hwhole).symm
  let P := radialProductHomeomorph U (Ioo 0 ℓ) ρ η r ⟨hr, hrℓ⟩
    hρ hη hlevel hinit hreset hcρ.continuousOn hcη
  let H := (A.prodCongr (Homeomorph.refl (Ioo 0 ℓ))).trans P.symm
  have htr : t * (r / t) = r := by field_simp
  refine ⟨r / t, div_pos hr ht, ?_, ?_, hsource, H, ?_⟩
  · rw [htr]
    exact ⟨hr, hrℓ⟩
  · apply Set.Subset.trans (Metric.ball_subset_ball ?_) hball
    have htwo : 2 * r ≤ ε := by
      dsimp [r]
      linarith [min_le_left ε ℓ]
    calc
      2 * (r / t) = (2 * r) / t := by ring
      _ ≤ ε / t := div_le_div_of_nonneg_right htwo ht.le
  · intro z
    change η ((s z.1 : M), (z.2 : ℝ)) = η (e z.1, z.2)
    rw [hs]

end LichnerowiczObata
