/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Lifetime.Basic
public import Mathlib.Probability.Kernel.Composition.MapComap


/-!
# Continuous laws as nonexplosive lifetime-path laws

This file transports kernels on ordinary continuous paths through the infinite-lifetime
embedding. It records the resulting nonexplosion and coordinate identities without asserting
that any particular dense-time or PDE law has continuous paths.
-/

@[expose] public section

noncomputable section PortComputability

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MarkovProcess

section

namespace Kernel

variable {beta alpha : Type*} [MeasurableSpace beta] [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]

/-- A kernel on lifetime paths is nonexplosive when its lifetime is almost surely infinite
from every starting point. -/
def IsNonexplosive (kappa : Kernel beta (LifetimePath alpha)) : Prop :=
  ∀ x, ∀ᵐ omega ∂kappa x, omega.lifetime = ∞

/-- Regard a kernel on ordinary continuous paths as a kernel on infinite-lifetime paths. -/
def toLifetimePathKernel (kappa : Kernel beta (ContinuousPath alpha)) :
    Kernel beta (LifetimePath alpha) :=
  Kernel.mapOfMeasurable kappa LifetimePath.ofContinuousPath
    LifetimePath.measurable_ofContinuousPath

/-- The lifetime-path transport agrees with ordinary kernel mapping. -/
theorem toLifetimePathKernel_eq_map (kappa : Kernel beta (ContinuousPath alpha)) :
    toLifetimePathKernel kappa = kappa.map LifetimePath.ofContinuousPath :=
  Kernel.mapOfMeasurable_eq_map _ LifetimePath.measurable_ofContinuousPath

/-- A Markov continuous-path kernel remains Markov after the infinite-lifetime embedding. -/
theorem isMarkovKernel_toLifetimePathKernel
    (kappa : Kernel beta (ContinuousPath alpha)) [IsMarkovKernel kappa] :
    IsMarkovKernel (toLifetimePathKernel kappa) := by
  rw [toLifetimePathKernel_eq_map]
  exact Kernel.IsMarkovKernel.map _ LifetimePath.measurable_ofContinuousPath

/-- Transporting an ordinary continuous-path law through the infinite-lifetime embedding is
nonexplosive. -/
theorem isNonexplosive_toLifetimePathKernel
    (kappa : Kernel beta (ContinuousPath alpha)) :
    IsNonexplosive (toLifetimePathKernel kappa) := by
  intro x
  rw [toLifetimePathKernel_eq_map,
    Kernel.map_apply _ LifetimePath.measurable_ofContinuousPath]
  refine (ae_map_iff (μ := kappa x)
    LifetimePath.measurable_ofContinuousPath.aemeasurable ?_).2 ?_
  · exact measurableSet_eq_fun LifetimePath.measurable_lifetime measurable_const
  · exact Filter.Eventually.of_forall LifetimePath.lifetime_ofContinuousPath

/-- At every time, the coordinate law of the lifetime-path transport is the original
continuous-path coordinate law, embedded as a live cemetery state. -/
theorem toLifetimePathKernel_map_coordinate
    (kappa : Kernel beta (ContinuousPath alpha)) (t : NNReal) :
    (toLifetimePathKernel kappa).map (LifetimePath.coordinate t) =
      kappa.map (fun omega => Cemetery.alive (omega t)) := by
  rw [toLifetimePathKernel_eq_map, ← Kernel.map_comp_right]
  · apply congrArg (Kernel.map kappa)
    funext omega
    exact LifetimePath.coordinate_ofContinuousPath omega t
  · exact LifetimePath.measurable_ofContinuousPath
  · exact LifetimePath.measurable_coordinate t

end Kernel
end
end MarkovProcess

end PortComputability
