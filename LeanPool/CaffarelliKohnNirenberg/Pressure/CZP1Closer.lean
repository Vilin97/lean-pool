/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.CZP1UnconditionalAssembly
public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionGrowthSWS
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.TheoremBAdaptersCZ

/-!
# Unconditional singly centred pressure bound for theta decay

The suitable-solution slice and residual estimates identify the selected
pressure with the scalar Calderón--Zygmund extension. The component sum
contributes a factor nine, retained in the slice constant. The cylinder
adapter supplies the pressure input shared by the two regularity criteria.
No pressure estimate or source certificate is assumed here.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Core.Step3

noncomputable section
namespace CKN

/-- The fixed cylinder constant, including the tensor-component sum and
the Sobolev slice-to-cylinder factor. -/
def czP1ThetaDecayConstant : ℝ :=
  (9 * max czP1OperatorConstant 0) * (9 * sobolevPoincareL6Constant.toReal)

/-- The fixed pressure constant is nonnegative. -/
theorem czP1ThetaDecayConstant_nonneg : 0 ≤ czP1ThetaDecayConstant := by
  unfold czP1ThetaDecayConstant
  exact mul_nonneg (mul_nonneg (by norm_num) (le_max_right _ _))
    (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)

/-- The exact singly centred pressure input of theta decay follows from
suitability alone, with a constant fixed before all solution data. -/
theorem pressureP1_thetaDecay_hCZ_unconditional (q : ℝ) :
    ∀ (Ω : Set Vec3) (I : Set ℝ)
        (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {z : ParabolicPoint} {ρ r : ℝ}, (hρ : 0 < ρ) → 0 < r → r ≤ ρ / 2 →
        closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
        ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
          eLpNorm' (fun w : ParabolicPoint => pressureP1
            (mollifiedBallCutoff z.1 hρ) u
            (fun t j => MeasureTheory.average
              (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
            p f w.2 w.1) (3 / 2 : ℝ)
            (volume.restrict (parabolicCylinder z.1 z.2 r)) ≤
          ENNReal.ofReal (czP1ThetaDecayConstant * (r / ρ)⁻¹ *
            alpha u z ρ * beta u Du z ρ) := by
  apply Core.Endgame.theoremB_hCZ_p1_of_slice_bounds q czP1ThetaDecayConstant
    (9 * max czP1OperatorConstant 0)
    (mul_nonneg (by norm_num) (le_max_right _ _)) le_rfl
  intro Ω I u Du p f hsol z ρ hρ hsub
  exact pressureP1_thetaDecay_hCZ_of_sws (max czP1OperatorConstant 0)
    (le_max_right _ _) (le_max_left _ _) hsol hρ hsub
    (pressureSecondExtension_residual_growth_ae_of_sws hsol hρ hsub)

end CKN
