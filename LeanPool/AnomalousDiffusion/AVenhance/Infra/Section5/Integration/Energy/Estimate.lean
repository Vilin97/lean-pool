/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.Energy.Integrated

/-! # The classical forced energy estimate

`forced_energy_estimate`: the energy-estimate form of the classical forced bound for the error
`w = u - v` between a classical solution `u` with zero forcing and an arbitrary jointly `C²`
periodic comparison function `v`, in terms of the `L²(0,1; HDot⁻¹)` norm of the defect
`advDiffOp b κ v`.

Proof chain (each step a separate module):
`Energy/TimeDerivative` (energy differentiable), `Energy/Rate` (rate identity, IBP and transport
cancellation), `Energy/Duality` (HDot⁻¹ pairing), `Energy/Inequality` (Young), `Energy/Abstract`
(integration of the a.e. differential inequality), `Energy/FiniteNorm` (consequences of
`hfin`), `Energy/Integrated` (assembly), and the elementary square-root step below. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Homogenization
open AVenhance.Infra.Torus AVenhance.Infra.Section5

namespace AVenhance.Infra.Section5.Integration

open AVenhance

/-- The elementary square-root arithmetic of the final step. -/
theorem sqrt_energy_arith {a b E₀ F κ : ℝ} (hκ : 0 < κ) (hE₀ : 0 ≤ E₀) (hF : 0 ≤ F)
    (ha : a ≤ E₀ + F ^ 2 / κ) (hb : κ * b ≤ E₀ + F ^ 2 / κ) :
    Real.sqrt a + Real.sqrt κ * Real.sqrt b ≤ 2 * (Real.sqrt E₀ + F / Real.sqrt κ) := by
  set A := E₀ + F ^ 2 / κ with hA
  have hsκ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have h1 : Real.sqrt a ≤ Real.sqrt A := Real.sqrt_le_sqrt ha
  have h2 : Real.sqrt κ * Real.sqrt b ≤ Real.sqrt A := by
    rw [← Real.sqrt_mul hκ.le]
    exact Real.sqrt_le_sqrt hb
  have h3 : Real.sqrt A ≤ Real.sqrt E₀ + F / Real.sqrt κ := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have hsq : (F / Real.sqrt κ) ^ 2 = F ^ 2 / κ := by
      rw [div_pow, Real.sq_sqrt hκ.le]
    have hE : Real.sqrt E₀ ^ 2 = E₀ := Real.sq_sqrt hE₀
    have hcross : 0 ≤ Real.sqrt E₀ * (F / Real.sqrt κ) := by positivity
    rw [hA, add_sq, hE, hsq]
    linarith
  linarith

/-- The classical forced energy estimate (standard: test the equation of `w = u - v` with `w`,
the divergence-free drift drops out, pair the forcing `-advDiffOp b κ v` by HDot⁻¹ duality with
`‖∇w(t)‖`, Young, integrate in time). `u` is a classical solution with zero forcing; `v` is any
jointly C² periodic function with smooth slices. The finiteness premise is essential: the
`toReal` of an infinite norm is `0`. -/
theorem forced_energy_estimate {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) {κ : ℝ}
    (hκ : 0 < κ) {θ₀ : Vec 2 → ℝ} {u v : ℝ → Vec 2 → ℝ}
    (hu : IsClassicalSol (streamVel φ) κ (fun _ _ => 0) θ₀ u)
    (hv : ContDiffOn ℝ 2 (fun p : ℝ × Vec 2 => v p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hvs : ∀ t, 0 ≤ t → ContDiff ℝ (⊤ : ℕ∞) (v t))
    (hvp : ∀ t, 0 ≤ t → IsZ2Periodic (v t))
    (hfin : timeHMinusOneNorm (fun s x => advDiffOp (streamVel φ) κ v s x) ≠ ⊤) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => u t x - v t x)) +
        Real.sqrt κ * Real.sqrt (spaceTimeGradNormSq (fun s x =>
          spaceGrad (u s) x - spaceGrad (v s) x)) ≤
      2 * (Real.sqrt (l2NormSq (fun x => u 0 x - v 0 x)) +
        (timeHMinusOneNorm (fun s x => advDiffOp (streamVel φ) κ v s x)).toReal / Real.sqrt κ) := by
  intro t ht
  have S : Energy.ForcedSetup φ κ θ₀ u v := ⟨hφ, hκ, hu, hv, hvs, hvp⟩
  have hb := Energy.integrated_energy_bound S hfin
  set F := (timeHMinusOneNorm (fun s x => advDiffOp (streamVel φ) κ v s x)).toReal with hF
  have hcell : ∀ s, l2NormSq (fun x => u s x - v s x) = ∫ x in unitCell 2, (u s x - v s x) ^ 2 :=
    fun s => (integral_unitCell_eq_unitCube _).symm
  have hint : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ ∫ r in (0 : ℝ)..s, Energy.errGrad u v r :=
    fun s hs => intervalIntegral.integral_nonneg hs.1 fun r _ => Energy.errGrad_nonneg u v r
  have hV : ContinuousOn (fun p : ℝ × Vec 2 => spaceGrad (u p.1) p.2 - spaceGrad (v p.1) p.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) :=
    S.errGrad_jointContinuousOn.mono (Set.prod_mono Set.Icc_subset_Ici_self le_rfl)
  have hstg : spaceTimeGradNormSq (fun s x => spaceGrad (u s) x - spaceGrad (v s) x) =
      ∫ r in (0 : ℝ)..1, Energy.errGrad u v r := by
    rw [LeftToShow.spaceTimeGradNormSq_eq_intervalIntegral hV]
    rfl
  have hE : ∀ s, 0 ≤ l2NormSq (fun x => u s x - v s x) := fun s =>
    integral_nonneg fun _ => sq_nonneg _
  have h1 := hb t ht
  have h2 := hb 1 ⟨zero_le_one, le_rfl⟩
  have hFnn : 0 ≤ F := ENNReal.toReal_nonneg
  have hI1 := hint 1 ⟨zero_le_one, le_rfl⟩
  have hIt := hint t ht
  rw [← hcell, ← hcell] at h1 h2
  refine sqrt_energy_arith hκ (hE 0) hFnn ?_ ?_
  · nlinarith [mul_nonneg hκ.le hIt]
  · rw [hstg]
    nlinarith [hE 1]

end AVenhance.Infra.Section5.Integration

end
