/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.NoSelectionLimit.Chain
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.NoSelectionLimit.Real
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Contracts.NoSelectionInputs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Contracts.FlipFlop

/-! # The middle term: same drift, two diffusivities; the two vanishing-viscosity families -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

/-- The diffusivity family `κ_j = t ε_{2j+1}^{p}`, `p = 2β/(qβ+1)`. -/
def kfam (β : ℝ) (Λ : ℕ) (t : ℝ) (j : ℕ) : ℝ :=
  t * epsilon β Λ (2 * j + 1) ^ (2 * β / (q β + 1))

theorem kfam_mem {β : ℝ} {Λ : ℕ} {t : ℝ} (ht : t = 1 / 2 ∨ t = 2) (j : ℕ)
    (hε : 0 ≤ epsilon β Λ (2 * j + 1)) : kfam β Λ t j ∈ permittedInterval β Λ (2 * j + 1) := by
  have h := Real.rpow_nonneg hε (2 * β / (q β + 1))
  unfold kfam permittedInterval
  rcases ht with rfl | rfl <;> constructor <;> linarith

theorem kfam_mem_permissible {β : ℝ} {Λ : ℕ} {t : ℝ} (ht : t = 1 / 2 ∨ t = 2) (j : ℕ)
    (hε : 0 ≤ epsilon β Λ (2 * j + 1)) : kfam β Λ t j ∈ permissibleSet β Λ :=
  Set.mem_iUnion₂.2 ⟨2 * j + 1, by omega, kfam_mem ht j hε⟩

/-- Triangle inequality through an intermediate `L²` function. -/
theorem sqrt_l2_tri {u v w : Vec 2 → ℝ} (hu : MemL2On unitCube u) (hv : MemL2On unitCube v)
    (hw : MemL2On unitCube w) :
    Real.sqrt (l2NormSq (fun x => u x - w x)) ≤
      Real.sqrt (l2NormSq (fun x => u x - v x)) + Real.sqrt (l2NormSq (fun x => v x - w x)) := by
  have e : (fun x => u x - w x) = fun x => (u x - v x) + (v x - w x) := by
    funext x; ring
  rw [e]
  exact Infra.Section5.sqrt_l2NormSq_add_le (hu.sub hv) (hv.sub hw)

theorem sqrt_l2_comm (u v : Vec 2 → ℝ) :
    Real.sqrt (l2NormSq (fun x => u x - v x)) = Real.sqrt (l2NormSq (fun x => v x - u x)) := by
  have e : ∀ x, (u x - v x) ^ 2 = (v x - u x) ^ 2 := fun x => by ring
  simp only [l2NormSq, e]

/-- Two classical solutions with the same drift and flip-flop-close diffusivities. -/
theorem middle_bound {Ψ : ℝ → Vec 2 → ℝ} (hΨ : IsAdmissibleStream Ψ)
    {a b D L e : ℝ} (ha : 0 < a) (hb : 0 < b) (hD : 0 < D)
    (h1 : |Real.log (a / D) - L| ≤ e) (h2 : |Real.log (b / D) - L| ≤ e) (he : 2 * e ≤ 1)
    {θ₀ : Vec 2 → ℝ} (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀) (hper : IsZ2Periodic θ₀)
    {θ θ' : ℝ → Vec 2 → ℝ}
    (hθ : IsClassicalSol (streamVel Ψ) a (fun _ _ => 0) θ₀ θ)
    (hθ' : IsClassicalSol (streamVel Ψ) b (fun _ _ => 0) θ₀ θ') {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Real.sqrt (l2NormSq (fun x => θ t x - θ' t x)) ≤ 4 * e * Real.sqrt (l2NormSq θ₀) := by
  have h := Contracts.twoDiffusivity_contract Ψ hΨ a b ha hb θ₀ hθ₀ hper θ θ' hθ hθ' t ht
  have hr := diffusivity_ratio_le ha hb (d := e + e) (log_ratio_le ha hb hD h1 h2) (by linarith)
  refine h.trans ?_
  calc _ ≤ (2 * (e + e)) * Real.sqrt (l2NormSq θ₀) :=
        mul_le_mul_of_nonneg_right hr (Real.sqrt_nonneg _)
    _ = _ := by ring

end AVenhance.Infra.FullTheorem
