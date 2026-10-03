/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.BaseEnergyRate
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.FrozenBridge
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.L2NormSq
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.GradNormSq
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.SpaceTimeGradNormSq

/-! # integrated energy identity for classical solutions

For an admissible stream `φ`, a classical solution `θ` with zero forcing and mean-zero
smooth periodic datum `g` satisfies, for `t ∈ [0,1]`,
`‖θ(t)‖² + 2κ ∫_0^t ‖∇θ(s)‖² ds = ‖g‖²`, the mean of `θ(t)` vanishes, and the
`spaceTimeGradNormSq` equals `∫_0^1 ‖∇θ(s)‖² ds`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Homogenization
open AVenhance.Infra.Torus
open AVenhance.Infra.Classical
open scoped Topology

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance

section CellFacts

/-- `∫_cell (f + 1)² = ∫_cell f² + 2 ∫_cell f + ∫_cell 1` for continuous `f`. -/
theorem integral_cell_shift_sq {f : Vec 2 → ℝ} (hf : Continuous f) :
    ∫ x in unitCell 2, (f x + 1) ^ 2 =
      (∫ x in unitCell 2, f x ^ 2) + 2 * (∫ x in unitCell 2, f x) +
        ∫ _ in unitCell 2, (1 : ℝ) := by
  have h1 : IntegrableOn (fun x => f x ^ 2) (unitCell 2) :=
    continuous_integrableOn_unitCell (hf.pow 2)
  have h2 : IntegrableOn f (unitCell 2) := continuous_integrableOn_unitCell hf
  have h3 : IntegrableOn (fun _ : Vec 2 => (1 : ℝ)) (unitCell 2) :=
    continuous_integrableOn_unitCell continuous_const
  calc ∫ x in unitCell 2, (f x + 1) ^ 2
      = ∫ x in unitCell 2, ((f x ^ 2 + 2 * f x) + 1) := by
        apply integral_congr_ae
        filter_upwards with x
        ring
    _ = _ := by
        have e1 : ∫ x in unitCell 2, ((f x ^ 2 + 2 * f x) + 1) =
            (∫ x in unitCell 2, (f x ^ 2 + 2 * f x)) + ∫ _ in unitCell 2, (1 : ℝ) :=
          integral_add (h1.add (h2.const_mul 2)) h3
        have e2 : ∫ x in unitCell 2, (f x ^ 2 + 2 * f x) =
            (∫ x in unitCell 2, f x ^ 2) + ∫ x in unitCell 2, 2 * f x :=
          integral_add h1 (h2.const_mul 2)
        rw [e1, e2, integral_const_mul]

end CellFacts

section Classical

variable {φ : ℝ → Vec 2 → ℝ} {κ : ℝ} {g : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}

/-- The cell integral `∫_cell |∇θ(s)|²`. -/
def cellGrad (θ : ℝ → Vec 2 → ℝ) (s : ℝ) : ℝ :=
  ∫ x in unitCell 2, vecDot (spaceGrad (θ s) x) (spaceGrad (θ s) x)

/-- Energy of a shifted solution is continuous on `[0,T]`. -/
theorem shift_energy_continuousOn (hsol : IsClassicalSol (streamVel φ) κ (fun _ _ => 0) g θ)
    (c : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun s => ∫ x in unitCell 2, (θ s x + c) ^ 2) (Set.Icc 0 T) :=
  unitCell_energy_continuousOn (u := fun s x => θ s x + c) (hsol.1.add contDiffOn_const) hT

/-- `cellGrad` splits as the sum of the squared component integrals. -/
theorem cellGrad_eq_sum (hsol : IsClassicalSol (streamVel φ) κ (fun _ _ => 0) g θ)
    {s : ℝ} (hs : 0 ≤ s) :
    cellGrad θ s = (∫ x in unitCell 2, spaceGrad (θ s) x 0 ^ 2) +
      ∫ x in unitCell 2, spaceGrad (θ s) x 1 ^ 2 := by
  have hc (i : Fin 2) : Continuous (fun x => spaceGrad (θ s) x i) := by
    have hsl := classicalSmooth_slice_nonneg (spaceGrad_component_contDiffOn hsol i) hs
    exact hsl.continuous
  unfold cellGrad
  have e : ∫ x in unitCell 2, (spaceGrad (θ s) x 0 ^ 2 + spaceGrad (θ s) x 1 ^ 2) =
      (∫ x in unitCell 2, spaceGrad (θ s) x 0 ^ 2) + ∫ x in unitCell 2, spaceGrad (θ s) x 1 ^ 2 :=
    integral_add (continuous_integrableOn_unitCell ((hc 0).pow 2))
      (continuous_integrableOn_unitCell ((hc 1).pow 2))
  rw [← e]
  apply integral_congr_ae
  filter_upwards with x
  simp [vecDot, Fin.sum_univ_two, pow_two]

/-- `cellGrad` is continuous on `[0,T]`. -/
theorem cellGrad_continuousOn (hsol : IsClassicalSol (streamVel φ) κ (fun _ _ => 0) g θ)
    {T : ℝ} (hT : 0 ≤ T) : ContinuousOn (cellGrad θ) (Set.Icc 0 T) := by
  have h0 := unitCell_energy_continuousOn
    (u := fun s x => spaceGrad (θ s) x 0) (spaceGrad_component_contDiffOn hsol 0) hT
  have h1 := unitCell_energy_continuousOn
    (u := fun s x => spaceGrad (θ s) x 1) (spaceGrad_component_contDiffOn hsol 1) hT
  refine (h0.add h1).congr ?_
  intro s hs
  exact cellGrad_eq_sum hsol hs.1

/-- The mean of a classical solution with mean-zero datum vanishes at every nonnegative time. -/
theorem classical_meanZero (hφ : IsAdmissibleStream φ)
    (hsol : IsClassicalSol (streamVel φ) κ (fun _ _ => 0) g θ)
    (hg : ∫ x in unitCell 2, g x = 0) {t : ℝ} (ht : 0 ≤ t) :
    ∫ x in unitCell 2, θ t x = 0 := by
  let D : ℝ → ℝ := fun s => (∫ x in unitCell 2, (θ s x + 1) ^ 2) - ∫ x in unitCell 2, (θ s x + 0)
      ^ 2
  have hslice (s : ℝ) (hs : 0 ≤ s) : Continuous (θ s) :=
    (classicalSmooth_slice_nonneg hsol.1 hs).continuous
  have hDs (s : ℝ) (hs : 0 ≤ s) :
      D s = 2 * (∫ x in unitCell 2, θ s x) + ∫ _ in unitCell 2, (1 : ℝ) := by
    simp only [D, add_zero]
    rw [integral_cell_shift_sq (hslice s hs)]
    ring
  rcases ht.eq_or_lt with h0 | htpos
  · subst h0
    have : ∫ x in unitCell 2, θ 0 x = ∫ x in unitCell 2, g x := by
      apply integral_congr_ae
      filter_upwards with x
      exact hsol.2.2.1 x
    rw [this, hg]
  · have hDcont : ContinuousOn D (Set.Icc 0 t) :=
      (shift_energy_continuousOn hsol 1 ht).sub (shift_energy_continuousOn hsol 0 ht)
    have hDderiv (s : ℝ) (hs : 0 < s) : HasDerivAt D 0 s := by
      have h1 := classical_shift_hasDerivAt φ hφ hsol 1 hs
      have h0 := classical_shift_hasDerivAt φ hφ hsol 0 hs
      have h := h1.sub h0
      rwa [sub_self] at h
    obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope D htpos hDcont
      (fun s hs => (hDderiv s hs.1).differentiableAt.differentiableWithinAt)
    rw [(hDderiv c hc.1).deriv] at hcd
    have hDeq : D t = D 0 := by
      have : D t - D 0 = 0 := by
        have h := hcd.symm
        rw [div_eq_zero_iff] at h
        rcases h with h | h
        · exact h
        · exact absurd h (by linarith)
      linarith
    have h0 : ∫ x in unitCell 2, θ 0 x = 0 := by
      have : ∫ x in unitCell 2, θ 0 x = ∫ x in unitCell 2, g x := by
        apply integral_congr_ae
        filter_upwards with x
        exact hsol.2.2.1 x
      rw [this, hg]
    rw [hDs t ht, hDs 0 le_rfl, h0] at hDeq
    linarith

end Classical

end AVenhance.Infra.Section5.RelativeError
