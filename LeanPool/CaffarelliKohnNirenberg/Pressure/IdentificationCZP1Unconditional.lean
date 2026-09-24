/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.CZCylinderBridge
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.ThetaDecayTShape
public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionUnconditional

/-!
# Identification CZP1 Unconditional

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Euclidean
open CKN.Core.Step3

noncomputable section

namespace CKN

/-! The global indexed extension is used for the pressure term.  The local
slice estimate is the only interface needed by the cylinder bridge. -/

/-- Transfer the singly-centred slice certificate to the exact pressure input
of the theta-decay display (paper label: `ext:CZ`). -/
theorem pressureP1_thetaDecay_hCZ_of_global_slice
    (C₁₂_p1 C_CZ : ℝ) (hC_CZ : 0 ≤ C_CZ)
    (hconst : C_CZ * (9 * sobolevPoincareL6Constant.toReal) ≤ C₁₂_p1)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hhalf : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hCZ_p1 : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
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
    ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
        eLpNorm' (fun w : ParabolicPoint => pressureP1
          (mollifiedBallCutoff z.1 hρ) u
          (fun t j => MeasureTheory.average
            (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
          p f w.2 w.1) (3 / 2 : ℝ)
          (volume.restrict (parabolicCylinder z.1 z.2 r)) ≤
      ENNReal.ofReal (C₁₂_p1 * (r / ρ)⁻¹ * alpha u z ρ * beta u Du z ρ) := by
  exact CKN.Foundation.Euclidean.hCZ_p1_cylinder_of_global_slice_le
    C₁₂_p1 C_CZ hC_CZ hconst hsol hρ hr hhalf hsub hCZ_p1

end CKN
