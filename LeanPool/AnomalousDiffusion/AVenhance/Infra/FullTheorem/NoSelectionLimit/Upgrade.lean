/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.NoSelectionLimit.Middle

/-! # Hölder upgrade by interpolation

A function with small sup-`L²` norm and bounded `μ`-Hölder seminorm has small
`C^{0,μ/2}([0,1];L²)` norm; and the limit of uniformly `μ`-Hölder functions is `μ`-Hölder. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

theorem holderL2Le_of_small {μ H α : ℝ} {f : ℝ → Vec 2 → ℝ}
    (hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, MemL2On unitCube (f t))
    (hsup : ∀ t ∈ Set.Icc (0 : ℝ) 1, Real.sqrt (l2NormSq (f t)) ≤ α)
    (hhol : IsHolderTimeL2 μ H f) :
    HolderTimeL2Le (μ / 2) (α + Real.sqrt (2 * α * H)) f := by
  refine ⟨hmem, α, Real.sqrt (2 * α * H), le_rfl, hsup, ?_⟩
  intro s hs t ht
  have h1 : Real.sqrt (l2NormSq (fun x => f t x - f s x)) ≤ 2 * α := by
    have := sqrt_l2NormSq_sub_le_memL2 (hmem t ht) (hmem s hs)
    linarith [hsup t ht, hsup s hs]
  exact min_interp (abs_nonneg _) (Real.sqrt_nonneg _) h1 (hhol s hs t ht)

theorem exists_small_alpha {H : ℝ} (hH : 0 ≤ H) {η : ℝ} (hη : 0 < η) :
    ∃ α : ℝ, 0 < α ∧ α + Real.sqrt (2 * α * H) ≤ η := by
  refine ⟨min (η / 2) (η ^ 2 / (16 * (H + 1))), lt_min (by linarith) (by positivity), ?_⟩
  set α := min (η / 2) (η ^ 2 / (16 * (H + 1))) with hα
  have h1 : α ≤ η / 2 := min_le_left _ _
  have h2 : α ≤ η ^ 2 / (16 * (H + 1)) := min_le_right _ _
  have hα0 : 0 ≤ α := le_min (by linarith) (by positivity)
  have h3 : Real.sqrt (2 * α * H) ≤ η / 2 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by linarith, ?_⟩
    have h4 : α * (16 * (H + 1)) ≤ η ^ 2 := (le_div_iff₀ (by positivity)).1 h2
    nlinarith
  linarith

/-- Passing a uniform `L²` limit through the time-Hölder seminorm. -/
theorem holder_of_limit {μ H : ℝ} {f : ℕ → ℝ → Vec 2 → ℝ} {Θ : ℝ → Vec 2 → ℝ}
    (hmf : ∀ j, ∀ t ∈ Set.Icc (0 : ℝ) 1, MemL2On unitCube (f j t))
    (hmΘ : ∀ t ∈ Set.Icc (0 : ℝ) 1, MemL2On unitCube (Θ t))
    (hlim : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ j ≥ N, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => f j t x - Θ t x)) ≤ η)
    (hH : ∀ j, IsHolderTimeL2 μ H (f j)) : IsHolderTimeL2 μ H Θ := by
  intro s hs t ht
  refine le_of_forall_pos_le_add fun η hη => ?_
  obtain ⟨N, hN⟩ := hlim (η / 2) (by linarith)
  have a1 := sqrt_l2_tri (hmΘ t ht) (hmf N t ht) (hmΘ s hs)
  have a2 := sqrt_l2_tri (hmf N t ht) (hmf N s hs) (hmΘ s hs)
  have b1 := hN N le_rfl t ht
  have b2 := hN N le_rfl s hs
  have b1' : Real.sqrt (l2NormSq (fun x => Θ t x - f N t x)) ≤ η / 2 := by
    rw [sqrt_l2_comm]; exact b1
  have h3 := hH N s hs t ht
  linarith

/-- Reverse triangle inequality for `L²` norms of `L²` functions. -/
theorem abs_sqrt_l2_sub_le {f g : Vec 2 → ℝ} (hf : MemL2On unitCube f) (hg : MemL2On unitCube g) :
    |Real.sqrt (l2NormSq f) - Real.sqrt (l2NormSq g)| ≤
      Real.sqrt (l2NormSq (fun x => f x - g x)) := by
  have h1 : Real.sqrt (l2NormSq f) ≤
      Real.sqrt (l2NormSq (fun x => f x - g x)) + Real.sqrt (l2NormSq g) := by
    have := Infra.Section5.sqrt_l2NormSq_add_le (f := fun x => f x - g x) (g := g)
      (hf.sub hg) hg
    simpa only [sub_add_cancel] using this
  have h2 : Real.sqrt (l2NormSq g) ≤
      Real.sqrt (l2NormSq (fun x => f x - g x)) + Real.sqrt (l2NormSq f) := by
    have := Infra.Section5.sqrt_l2NormSq_add_le (f := fun x => g x - f x) (g := f)
      (hg.sub hf) hf
    simp only [sub_add_cancel] at this
    rwa [sqrt_l2_comm] at this
  rw [abs_le]
  constructor <;> linarith

end AVenhance.Infra.FullTheorem
