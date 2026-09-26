/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalEquationRepresentation
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.DuhamelAdjoint

/-!
# Source Morrey Gradient

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open CKN.Foundation.Parabolic
open CKN.Core.HeatPotential
open CKN.Core.Step3


noncomputable section

namespace CKN.Core.Step4

/-! The pressure-gradient source is kept in the heat slot.  The definitions
below are deliberately separate from the divergence-form sources: the latter
place `p * φ` in the spatial derivative slot and therefore have a different
Morrey order. -/

/-- Localized scalar heat source after subtracting the cutoff times the weak pressure gradient. -/
@[expose]
def localizedGradientSourceG (φ : ParabolicPoint → ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (f : ParabolicPoint → Vec3) (Dp : ParabolicPoint → Vec3) :
    ParabolicPoint → Vec3 :=
  fun z i => localizedEquationG φ u Du f z i - φ z * Dp z i

/-- Localized divergence source in the pressure-gradient formulation of the heat equation. -/
@[expose]
def localizedGradientSourceH (φ : ParabolicPoint → ℝ)
    (u : ParabolicPoint → Vec3) : Fin 3 → ParabolicPoint → Vec3 :=
  localizedEquationH φ u

/-- Componentwise vector heat potential of scalar and divergence sources. -/
def vectorHeatPotential (F : ParabolicPoint → Vec3)
    (G : Fin 3 → ParabolicPoint → Vec3) : ParabolicPoint → Vec3 :=
  fun z i => heatPotential (fun w => F w i) (fun j w => G j w i) z

theorem vectorHeatPotential_eq_duhamelPotential_neg
    {F : ParabolicPoint → Vec3} {G : Fin 3 → ParabolicPoint → Vec3}
    (z : ParabolicPoint) :
    vectorHeatPotential F G z =
      duhamelPotential F (fun j w => -G j w) z := by
  funext i
  simp only [vectorHeatPotential, duhamelPotential, heatPotential, Pi.neg_apply,
    mul_neg, integral_neg, Finset.sum_neg_distrib, sub_eq_add_neg]
  ring

/-- The exact sign adapter for the gradient-slot representation.  Thus a
representation through the Duhamel-named interface passes `-G` as its
derivative source, while the heat-potential consumer sees `G`. -/
theorem localized_gradient_slot_heat_representation
    {φ : ParabolicPoint → ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {f : ParabolicPoint → Vec3}
    {Dp : ParabolicPoint → Vec3}
    (hrep : localizedVelocity φ u =ᵐ[volume]
      duhamelPotential
        (localizedGradientSourceG φ u Du f Dp)
        (fun j w => -localizedGradientSourceH φ u j w)) :
    localizedVelocity φ u =ᵐ[volume]
      vectorHeatPotential
        (localizedGradientSourceG φ u Du f Dp)
        (localizedGradientSourceH φ u) := by
  filter_upwards [hrep] with z hz
  exact hz.trans (vectorHeatPotential_eq_duhamelPotential_neg z).symm


end CKN.Core.Step4
