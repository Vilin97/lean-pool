/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34CentredCZ
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34CentredPairingSWS

/-!
# Lin34 Centred CZResidual

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

open CKN.Foundation.Euclidean

/-!
# `ext:CZ` for the centred potential from the residual growth alone

Feeding the centred identification data of `Lin34CentredPairingSWS.lean` into the
unconditional singular-integral estimate leaves a single named input: the local
`L^{3/2}` membership, with linear growth, of the difference between the centred
potential `p₁` of `prop:pressure-decomposition` and the indexed second-order
Riesz extension of its source.  That is the decay hypothesis of the Liouville
step of `ext:newtonian`.
-/

/-- **`ext:CZ` at solution level, from the residual decay alone.**  For a
suitable weak solution and almost every time of the cylinder `Q_ρ(z₀)`, the
centred first potential is globally `L^{3/2}` with norm at most
`lin34CZConstant` times the velocity oscillation `eq:Chat` to the power `2/3`.
This is the hypothesis `hCZ_p1` of `pressure_lin34_force_lambda_of_sws`. -/
theorem lin34_hCZ_p1_of_residual_ae_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hresidual : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2), ∃ C : ℝ, 0 ≤ C ∧
      (∀ R : ℝ, 0 < R →
        MemLp (fun x => lin34CentredP1 u p f z.1 ρ hρ s x -
          pressureSecondExtensionOperator rieszSecondL2Input
            rieszSecondL2_weak_type (lin34CentredSource u z.1 hρ s) x)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) R))) ∧
      (∀ R : ℝ, 0 < R →
        lpNorm (fun x => lin34CentredP1 u p f z.1 ρ hρ s x -
          pressureSecondExtensionOperator rieszSecondL2Input
            rieszSecondL2_weak_type (lin34CentredSource u z.1 hρ s) x)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall (0 : Vec3) R)) ≤ C * (1 + R))) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp (lin34CentredP1 u p f z.1 ρ hρ s)
          (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
        lpNorm (lin34CentredP1 u p f z.1 ρ hρ s)
            (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
          lin34CZConstant * lin34VelocitySlice u z ρ s ^ (2 / 3 : ℝ) := by
  have hdata := lin34_centredP1_cz_data_ae_of_sws hsol hρ hsub
  refine lin34_hCZ_p1_ae_of_sws hsol hρ hsub ?_ ?_ hresidual
  · filter_upwards [hdata] with s hs using hs.1
  · filter_upwards [hdata] with s hs using hs.2

end CKN
