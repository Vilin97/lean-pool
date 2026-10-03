/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.WeakGradientPeriodization
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.ScalarFourierDerivative

/-!
# Almost-everywhere periodic H¹ slices

The common Fourier derivative identities identify the synchronized limit's Euclidean weak
gradient on almost every slice.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped RealInnerProductSpace Topology

namespace AVenhance.Infra.Parabolic.FourierGalerkin

/-- The synchronized scalar and gradient representatives form the exact periodic `H¹`
pair on almost every open time slice. -/
theorem synchronized_limit_isPeriodicH1With_ae
    (Uprod : ScalarProductTimeL2) (Gprod : GradientProductTimeL2)
    (u : Icc (0 : ℝ) 1 → ScalarTorusL2) (S : Set ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ t, ‖u t‖ ≤ B)
    (hS : ∀ t ∈ S, synchronizedScalarSliceGood Uprod u t)
    (hmode : ∀ᵐ t ∂GalerkinTimeMeasure, ∀ i : Fin 2, ∀ N : ℕ,
      ∀ j : Fin (RealFourierDimension N),
        ∫ x in AVenhance.unitCube,
          synchronizedScalarRepresentative Uprod u S t x *
            AVenhance.spaceGrad
              (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j)) x i =
        -∫ x in AVenhance.unitCube,
          synchronizedGradientRepresentative Gprod t x i *
            realFourierModeAmbient N
              ((realFourierIndexEquivFin N).symm j) x) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
      AVenhance.IsPeriodicH1With
        (synchronizedScalarRepresentative Uprod u S t)
        (synchronizedGradientRepresentative Gprod t) := by
  have hscalar := (synchronizedScalarRepresentative_pointwise_clauses
    Uprod u S B hB hS hbound).1
  have hgrad := synchronizedGradientRepresentative_gradMemL2On_ae Gprod
  have hmodeIoc : ∀ᵐ t ∂GalerkinTimeMeasure, ∀ i : Fin 2, ∀ N : ℕ,
      ∀ j : Fin (RealFourierDimension N),
        ∫ x in AVenhance.unitCube,
          synchronizedScalarRepresentative Uprod u S t x *
            AVenhance.spaceGrad
              (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j)) x i =
        -∫ x in AVenhance.unitCube,
          synchronizedGradientRepresentative Gprod t x i *
            realFourierModeAmbient N
              ((realFourierIndexEquivFin N).symm j) x := hmode
  have hmodeVol : ∀ᵐ t ∂volume, t ∈ Set.Ioc (0 : ℝ) 1 →
      ∀ i : Fin 2, ∀ N : ℕ, ∀ j : Fin (RealFourierDimension N),
        ∫ x in AVenhance.unitCube,
          synchronizedScalarRepresentative Uprod u S t x *
            AVenhance.spaceGrad
              (realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j)) x i =
        -∫ x in AVenhance.unitCube,
          synchronizedGradientRepresentative Gprod t x i *
            realFourierModeAmbient N
              ((realFourierIndexEquivFin N).symm j) x := by
    exact (ae_restrict_iff' measurableSet_Ioc).mp hmodeIoc
  have hgradVol : ∀ᵐ t ∂volume, t ∈ Set.Ioc (0 : ℝ) 1 →
      GradMemL2On AVenhance.unitCube (synchronizedGradientRepresentative Gprod t) := by
    exact (ae_restrict_iff' measurableSet_Ioc).mp hgrad
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hmodeVol, hgradVol] with t hmode_t hgrad_t htIoo
  have htIoc : t ∈ Set.Ioc (0 : ℝ) 1 := ⟨htIoo.1, le_of_lt htIoo.2⟩
  have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt htIoo.1, le_of_lt htIoo.2⟩
  have hscalar_t := hscalar t htIcc
  have hgrad_t' := hgrad_t htIoc
  have hweak := hasWeakGradientOn_of_realFourierModes
    hscalar_t.2 (fun i => hgrad_t' i) hscalar_t.1
    (synchronizedGradientRepresentative_periodic Gprod t)
    (fun i N j => hmode_t htIoc i N j)
  exact ⟨hscalar_t.1,
    synchronizedGradientRepresentative_periodic Gprod t,
    hscalar_t.2, hgrad_t', hweak⟩

end AVenhance.Infra.Parabolic.FourierGalerkin

end
