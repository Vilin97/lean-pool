/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredTime
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredArith
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermCenteredErgodic

/-! # Time integration and scale arithmetic for the centered contracts

`sd_final_time`: a pointwise-in-time bound of a slice's `HDot⁻¹` norm by an affine combination of
    the
slice energies of three fields, with coefficients of the form produced by the centered ergodic
estimate, integrates in time and, with the scale arithmetic `sd_arith_final`, gives the source
right side `C · ε^δ · √κ · B`. -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ENNReal

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5

theorem sd_final_time {f : ℝ → Vec 2 → ℝ} {V : Fin 3 → ℝ → Vec 2 → Vec 2}
    {x y κ ν ψ B A K Cd c₀ c₁ c₂ cfl M ρ e d E : ℝ}
    (hV : ∀ j (i : Fin 2), ContinuousOn (fun p : ℝ × Vec 2 => V j p.1 p.2 i)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ))
    (hpt : ∀ t ∈ Set.Ioo (0 : ℝ) 1, hMinusOneNorm (f t) ≤ ENNReal.ofReal
      ((144 * Cd * y * (c₀ * ψ * e / x) + cfl * e * ψ) * Real.sqrt (gradNormSq (V 0 t)) +
        144 * Cd * y * (c₁ * ψ * e) * Real.sqrt (gradNormSq (V 1 t)) +
        144 * Cd * y * (c₁ * ψ * e) * Real.sqrt (gradNormSq (V 2 t)) +
        144 * Cd * c₂ * B * ψ * ((ρ ^ 2)⁻¹ * E)))
    (hK : 1 ≤ K) (hκ : 0 < κ) (hν : 0 < ν) (hνK : ν ≤ K) (hψ : 0 ≤ ψ)
    (hψκ : ψ ^ 2 ≤ K * κ * ν)
    (hx : 0 < x) (hy : 0 < y) (hρ : 0 < ρ) (hyx : y ≤ K * x) (hyρ : y ≤ K * ρ)
    (he : 0 ≤ e) (hed : e ≤ d) (hB : 0 ≤ B) (hA : 0 ≤ A) (hCd : 0 ≤ Cd)
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hcfl : 0 ≤ cfl) (hM : 0 ≤ M)
    (hD₀b : Real.sqrt ν * Real.sqrt (spaceTimeGradNormSq (V 0)) ≤ A * B)
    (hD₁b : Real.sqrt ν * Real.sqrt (spaceTimeGradNormSq (V 1)) ≤ A * (A / ρ) * B)
    (hD₂b : Real.sqrt ν * Real.sqrt (spaceTimeGradNormSq (V 2)) ≤ A * (A / ρ) * B)
    (hE : 0 ≤ E) (hEb : (ρ ^ 2)⁻¹ * E ≤ M * d) :
    timeHMinusOneNorm f ≤ ENNReal.ofReal
      ((2 * (144 * Cd * c₀ * K + cfl) * Real.sqrt K * A +
        576 * Cd * c₁ * A ^ 2 * K * Real.sqrt K + 288 * Cd * c₂ * M * K) *
          d * Real.sqrt κ * B) := by
  have hCd0 := hCd
  have hψ0 := hψ
  have he0 := he
  have hkey := sd_time_transfer (f := f) (V := V)
    (P := ![144 * Cd * y * (c₀ * ψ * e / x) + cfl * e * ψ, 144 * Cd * y * (c₁ * ψ * e),
      144 * Cd * y * (c₁ * ψ * e)])
    (P₂ := 144 * Cd * c₂ * B * ψ * ((ρ ^ 2)⁻¹ * E))
    (by
      intro j
      fin_cases j <;> simp only [Fin.reduceFinMk, Matrix.cons_val] <;> positivity)
    (by positivity) hV (by
      intro t ht
      refine (hpt t ht).trans (le_of_eq ?_)
      simp [Fin.sum_univ_three])
  refine hkey.trans (ENNReal.ofReal_le_ofReal ?_)
  have hd : 0 ≤ d := he.trans hed
  have := sd_arith_final (x := x) (y := y) (κ := κ) (ν := ν) (ψ := ψ) (B := B) (A := A) (K := K)
    (Cd := Cd) (c₀ := c₀) (c₁ := c₁) (c₂ := c₂) (cfl := cfl) (M := M) (ρ := ρ) (e := e) (d := d)
    (D₀ := Real.sqrt (spaceTimeGradNormSq (V 0))) (D₁ := Real.sqrt (spaceTimeGradNormSq (V 1)))
    (D₂ := Real.sqrt (spaceTimeGradNormSq (V 2))) (E := E) hK hκ hν hνK hψ hψκ hx hy hρ hyx hyρ
    he hed hB hA hCd hc₀ hc₁ hc₂ hcfl hM (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) hD₀b hD₁b hD₂b hE hEb
  simpa [Fin.sum_univ_three, mul_assoc] using this

end AVenhance.Infra.Section5.Contracts
end
