/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginKPAffineSlot
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginKPComparison

/-!
# Pressure Gradient Origin KPAffine Source

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Endgame

noncomputable section

namespace CKN.Core.Step4

/-!
# The divergence source meets the enlarged small-cell budget

For a suitable weak solution with velocity budgets `KU`, `KD` on `Q_{R₀}` and
data size `ε`, the `6/5` power of the Morrey norm of the divergence source
`Du·u - f` of the pressure equation is bounded by `X^{6/5}`, where
`X = 3·KU·KD + forceSourceMorreyBound q ε`
(`origin_divergence_source_numerical_bounds_of_sws`). That coefficient lies
below `originKPAffineASlot`, so the source meets the enlarged budget with no
further analytic input. The linear budget `c·3X` of
`oneSidedPressureGradientKP` does not dominate `X^{6/5}` once `X > 3c`, which
is the scaling defect the enlarged budget removes.
-/

/-- **The source Morrey norm against the enlarged budget.** Under the
hypotheses of the origin pressure-gradient obligation, the `6/5` power of the
Morrey norm of the vector divergence source on `Q_{R₁}` lies below
`originKPAffineASlot q C_CZ ε KU KD`. -/
theorem origin_divergence_source_morrey_rpow_le_KPAffine_slot
    (q τ C_CZ R₀ R₁ ε : ℝ) (KU KD : ℝ≥0∞)
    (hq : 5 / 2 < q) (hτ : 25 / 3 ≤ τ) (hR : 0 < R₁) (hR₁₀ : R₁ ≤ R₀) (hR₀le : R₀ ≤ 1)
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hU : ∀ i, morreyNorm 3 τ
      ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => u z i)) ≤ KU)
    (hD : ∀ i j, morreyNorm 2 (25 / 8 : ℝ)
      ((parabolicCylinder (0 : Vec3) 0 R₀).indicator (fun z => Du z i j)) ≤ KD)
    (hsize : (∫⁻ z in parabolicCylinder (0 : Vec3) 0 1,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε) :
    morreyNorm (6 / 5 : ℝ) (min ((1 / τ + 8 / 25)⁻¹) q)
        (fun z => vec3EuclideanNorm
          ((parabolicCylinder (0 : Vec3) 0 R₁).indicator
            (fun w => fun i => ∑ j, Du w i j * u w j - f w i) z)) ^ (6 / 5 : ℝ) ≤
      originKPAffineASlot q C_CZ ε KU KD := by
  apply rpow_le_originKPAffineASlot_of_le
  calc
    _ ≤ 3 * (3 * KU * KD + forceSourceMorreyBound q ε) :=
      (origin_divergence_source_numerical_bounds_of_sws q τ R₀ R₁ ε KU KD
        hq hτ hR hR₁₀ hR₀le hsol hdom hU hD hsize).1
    _ = 1 * (3 * (3 * KU * KD + forceSourceMorreyBound q ε)) := (one_mul _).symm
    _ ≤ _ := mul_le_mul' (one_le_ofReal_abs_add_one C_CZ) le_rfl

end CKN.Core.Step4

end
