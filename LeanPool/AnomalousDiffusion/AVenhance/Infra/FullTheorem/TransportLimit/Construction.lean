/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.TransportLimit.AbstractLimit
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.WeakUniqueness.WeakEnergyPassage

/-!
# The limit profile of a uniformly `L²`-Cauchy family of space-time functions

Given `θ j : ℝ → Vec 2 → ℝ` that are slice-wise and jointly `L²` and uniformly Cauchy in
`L²(cell)` over `t ∈ [0,1]`, a fast subsequence defines an everywhere-defined limit `Θ` (via
`limUnder`) which is periodic, slice-wise and jointly `L²`, and is the uniform `L²` limit.
-/

@[expose] public section

open MeasureTheory Filter Topology Homogenization AVenhance
open scoped ENNReal

noncomputable section

namespace AVenhance.Infra.FullTheorem.TransportLimit

open AVenhance.Infra.Parabolic.WeakUniqueness

/-- Fubini bound on the space-time cell from slice bounds. -/
theorem joint_eLpNorm_le {F : ℝ × Vec 2 → ℝ}
    (hF : MemLp F 2 (volume.restrict timeCube)) {η : ℝ} (hη : 0 ≤ η)
    (h : ∀ t ∈ Set.Ioo (0 : ℝ) 1, Real.sqrt (∫ x in unitCube, F (t, x) ^ 2) ≤ η) :
    eLpNorm F 2 (volume.restrict timeCube) ≤ ENNReal.ofReal η := by
  apply eLpNorm_le_of_sqrt_integral_sq_le hF
  apply Real.sqrt_le_iff.2
  refine ⟨hη, ?_⟩
  have hint : Integrable (fun p => F p ^ 2) (volume.restrict timeCube) :=
    (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).1 hF
  rw [weakEnergy_timeCube_measure_eq_product] at hint ⊢
  rw [integral_prod _ hint]
  calc ∫ t, ∫ x, F (t, x) ^ 2 ∂(volume.restrict unitCube) ∂(volume.restrict (Set.Ioo (0 : ℝ) 1))
      ≤ ∫ _t, η ^ 2 ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
        refine integral_mono_ae hint.integral_prod_left (integrable_const _) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        have := h t ht
        exact (Real.sqrt_le_left hη).1 this
    _ = η ^ 2 := by simp

/-- The limit profile along the subsequence `s`. -/
def limitProfile (θ : ℕ → ℝ → Vec 2 → ℝ) (s : ℕ → ℕ) (t : ℝ) (x : Vec 2) : ℝ :=
  limUnder atTop (fun k => θ (s k) t x)

theorem limitProfile_periodic {θ : ℕ → ℝ → Vec 2 → ℝ} {s : ℕ → ℕ} {t : ℝ}
    (hper : ∀ j, IsZ2Periodic (θ j t)) : IsZ2Periodic (limitProfile θ s t) := by
  intro n x
  unfold limitProfile
  simp only [hper _ n x]

/-- Existence of the limit profile with all its properties. -/
theorem exists_uniform_l2_limit (θ : ℕ → ℝ → Vec 2 → ℝ)
    (hper : ∀ j, ∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (θ j t))
    (hmem : ∀ j, ∀ t ∈ Set.Icc (0 : ℝ) 1, MemL2On unitCube (θ j t))
    (hjoint : ∀ j, MemLp (fun p : ℝ × Vec 2 => θ j p.1 p.2) 2 (volume.restrict timeCube))
    (hcau : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => θ j t x - θ k t x)) ≤ η) :
    ∃ Θ : ℝ → Vec 2 → ℝ,
      (∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (Θ t)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, MemL2On unitCube (Θ t)) ∧
      MemLp (fun p : ℝ × Vec 2 => Θ p.1 p.2) 2 (volume.restrict timeCube) ∧
      ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ j ≥ N, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Real.sqrt (l2NormSq (fun x => θ j t x - Θ t x)) ≤ η := by
  obtain ⟨s, -, hs, hfast⟩ := exists_fast_index
    (fun n j k => ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => θ j t x - θ k t x)) ≤ (1 / 2 : ℝ) ^ n)
    (fun n => by
      obtain ⟨N, hN⟩ := hcau ((1 / 2 : ℝ) ^ n) (by positivity)
      exact ⟨N, fun j hj k hk => hN j hj k hk⟩)
  set Θ : ℝ → Vec 2 → ℝ := limitProfile θ s with hΘ
  -- slice-wise facts
  have hslice : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ η : ℝ, 0 < η → ∀ N : ℕ,
      (∀ j ≥ N, ∀ k ≥ N, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Real.sqrt (l2NormSq (fun x => θ j t x - θ k t x)) ≤ η) →
      ∀ j ≥ N, MemL2On unitCube (fun x => θ j t x - Θ t x) ∧
        Real.sqrt (l2NormSq (fun x => θ j t x - Θ t x)) ≤ η := by
    intro t ht η hη N hN j hj
    have hae := ae_tendsto_fast (μ := volume.restrict unitCube) (f := fun k => θ k t)
      (fun k => hmem k t ht) (s := s) (by
        intro n a ha b hb
        have hsq := hfast n a ha b hb t ht
        exact eLpNorm_le_of_sqrt_integral_sq_le
          ((hmem _ t ht).sub (hmem _ t ht)) hsq)
    have hlim : ∀ᵐ x ∂(volume.restrict unitCube),
        Tendsto (fun k => θ j t x - θ (s k) t x) atTop (𝓝 (θ j t x - Θ t x)) := by
      filter_upwards [hae] with x hx
      exact tendsto_const_nhds.sub hx
    have hev : ∀ᶠ k in atTop,
        eLpNorm (fun x => θ j t x - θ (s k) t x) 2 (volume.restrict unitCube) ≤
          ENNReal.ofReal η := by
      filter_upwards [eventually_ge_atTop N] with k hk
      exact eLpNorm_le_of_sqrt_integral_sq_le ((hmem _ t ht).sub (hmem _ t ht))
        (hN j hj (s k) ((hk.trans (hs k))) t ht)
    obtain ⟨hmL, hbd⟩ := memLp_limit_of_bound
      (fun k => ((hmem j t ht).sub (hmem _ t ht)).aestronglyMeasurable) hlim
      ENNReal.ofReal_ne_top hev
    exact ⟨hmL, sqrt_integral_sq_le_of_eLpNorm_le hmL hη.le hbd⟩
  have hunif : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ j ≥ N, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => θ j t x - Θ t x)) ≤ η := by
    intro η hη
    obtain ⟨N, hN⟩ := hcau η hη
    exact ⟨N, fun j hj t ht => (hslice t ht η hη N hN j hj).2⟩
  -- joint facts
  have hjae := ae_tendsto_fast (μ := volume.restrict timeCube)
    (f := fun k p => θ k p.1 p.2) hjoint (s := s) (by
      intro n a ha b hb
      refine joint_eLpNorm_le ((hjoint _).sub (hjoint _)) (by positivity) ?_
      intro t ht
      exact hfast n a ha b hb t ⟨ht.1.le, ht.2.le⟩)
  obtain ⟨N1, hN1⟩ := hcau 1 one_pos
  have hjlim : ∀ᵐ p ∂(volume.restrict timeCube),
      Tendsto (fun k => θ N1 p.1 p.2 - θ (s k) p.1 p.2) atTop
        (𝓝 (θ N1 p.1 p.2 - Θ p.1 p.2)) := by
    filter_upwards [hjae] with p hp
    exact tendsto_const_nhds.sub hp
  have hjev : ∀ᶠ k in atTop,
      eLpNorm (fun p : ℝ × Vec 2 => θ N1 p.1 p.2 - θ (s k) p.1 p.2) 2
        (volume.restrict timeCube) ≤ ENNReal.ofReal 1 := by
    filter_upwards [eventually_ge_atTop N1] with k hk
    refine joint_eLpNorm_le ((hjoint _).sub (hjoint _)) zero_le_one ?_
    intro t ht
    exact hN1 N1 le_rfl (s k) (hk.trans (hs k)) t ⟨ht.1.le, ht.2.le⟩
  obtain ⟨hjL, -⟩ := memLp_limit_of_bound
    (fun k => ((hjoint N1).sub (hjoint _)).aestronglyMeasurable) hjlim
    ENNReal.ofReal_ne_top hjev
  refine ⟨Θ, fun t ht => limitProfile_periodic (fun j => hper j t ht), ?_, ?_, hunif⟩
  · intro t ht
    have h := (hslice t ht 1 one_pos N1 hN1 N1 le_rfl).1
    have := (hmem N1 t ht).sub h
    exact this.ae_eq (Filter.Eventually.of_forall fun x => by simp)
  · have := (hjoint N1).sub hjL
    exact this.ae_eq (Filter.Eventually.of_forall fun x => by simp)

end AVenhance.Infra.FullTheorem.TransportLimit
