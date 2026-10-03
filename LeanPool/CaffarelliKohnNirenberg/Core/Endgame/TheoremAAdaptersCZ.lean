/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationCZP1Unconditional

/-!
# Re-quantifying the Calderón--Zygmund pressure estimate for Theorem A

The established transfer `pressureP1_thetaDecay_hCZ_of_global_slice` turns one
almost-every-time slice certificate for the centred first pressure potential of
the decomposition `prop:pressure-decomposition` into the `r`-scaled
extended-real Calderón--Zygmund estimate `ext:CZ` on the concentric parabolic
sub-cylinder.  The small-data statement `thm:A` consumes that estimate
quantified over *all* suitable weak solutions at a fixed force exponent `q`,
so the slice hypothesis must itself be uniform in the solution.

This file provides the single re-quantification adapter: from a slice
certificate available for every suitable weak solution, it produces the
solution-uniform `ext:CZ` estimate with the exact binder consumed downstream.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Euclidean
open CKN.Core.Step3

noncomputable section
namespace CKN
namespace Core.Endgame

/-- Re-quantify the singly-centred slice certificate of
`prop:pressure-decomposition` over all suitable weak solutions, yielding the
solution-uniform `r`-scaled extended-real Calderón--Zygmund estimate `ext:CZ`
on the concentric parabolic sub-cylinder. -/
theorem theoremA_hCZ_p1_of_slice_bounds
    (q C₁₂_p1 C_CZ : ℝ) (hC_CZ : 0 ≤ C_CZ)
    (hconst : C_CZ * (9 * sobolevPoincareL6Constant.toReal) ≤ C₁₂_p1)
    (hSlice :
      ∀ (Ω : Set Vec3) (I : Set ℝ)
        (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {z : ParabolicPoint} {ρ : ℝ}, (hρ : 0 < ρ) →
        closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
        ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
          MemLp (fun x : Vec3 => pressureP1
            (mollifiedBallCutoff z.1 hρ) u
            (fun t j => MeasureTheory.average
              (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
            p f s x) (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
          lpNorm (fun x : Vec3 => pressureP1
            (mollifiedBallCutoff z.1 hρ) u
            (fun t j => MeasureTheory.average
              (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
            p f s x) (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
            C_CZ *
              (∫ y in vec3Ball z.1 ρ,
                (utensorNorm u z.1 ρ s y) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ)) :
    ∀ (Ω : Set Vec3) (I : Set ℝ)
      (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
      (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      ∀ {z : ParabolicPoint} {ρ r : ℝ}, (hρ : 0 < ρ) → 0 < r →
      r ≤ ρ / 2 →
      closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
      ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
        eLpNorm' (fun w : ParabolicPoint => pressureP1
          (mollifiedBallCutoff z.1 hρ) u
          (fun t j => MeasureTheory.average
            (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
          p f w.2 w.1) (3 / 2 : ℝ)
          (volume.restrict (parabolicCylinder z.1 z.2 r)) ≤
        ENNReal.ofReal (C₁₂_p1 * (r / ρ)⁻¹ *
          alpha u z ρ * beta u Du z ρ) := by
  intro Ω I u Du p f hsol z ρ r hρ hr hhalf hsub
  exact pressureP1_thetaDecay_hCZ_of_global_slice
    C₁₂_p1 C_CZ hC_CZ hconst hsol hρ hr hhalf hsub
    (hSlice Ω I u Du p f hsol hρ hsub)

end Core.Endgame
end CKN
