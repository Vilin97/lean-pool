/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Kernel.C0
import LeanPool.MarkovProcess.MarkovProcess.Semigroup.Basic

/-!
# Strongly continuous `C₀` semigroups from kernels

This file isolates continuity in time as an explicit hypothesis on the `C₀` kernel operators and
packages those operators as a strongly continuous contraction semigroup. Spatial preservation of
`C₀`, continuity of its time orbits, and conservativity of the kernels remain separate properties.
No stochastic process or Hunt process is constructed here.
-/

open Topology
open scoped ZeroAtInfty

namespace MarkovProcess

namespace SubMarkovKernelSemigroup

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]

/-- The `C₀` kernel operators have continuous time orbits in the `C₀` norm. This is an
additional hypothesis beyond the spatial `MapsC0` property. -/
def HasContinuousC0Orbits (P : SubMarkovKernelSemigroup α) (hC0 : P.MapsC0) : Prop :=
  ∀ f : C₀(α, ℝ), Continuous fun t : NNReal ↦ P.c0Operator hC0 t f

/-- A sub-Markov kernel semigroup on a locally compact Hausdorff space has the `C₀`
Feller-semigroup properties when it maps `C₀` into itself and its resulting `C₀` operator orbits
are continuous in time. Conservativity is not part of this predicate. -/
def IsFellerKernelSemigroup (P : SubMarkovKernelSemigroup α)
      : Prop :=
  ∃ hC0 : P.MapsC0, P.HasContinuousC0Orbits hC0

variable (P : SubMarkovKernelSemigroup α) (hC0 : P.MapsC0)

/-- Package the kernel action on `C₀` as a strongly continuous contraction semigroup. -/
noncomputable def c0Semigroup (hTime : P.HasContinuousC0Orbits hC0) :
    Semigroup.StronglyContinuousContractionSemigroup C₀(α, ℝ) where
  operator := P.c0Operator hC0
  operator_zero := P.c0Operator_zero hC0
  operator_add := P.c0Operator_add hC0
  opNorm_le_one := P.norm_c0Operator_le hC0
  continuous_orbit := hTime

@[simp]
theorem c0Semigroup_operator (hTime : P.HasContinuousC0Orbits hC0) (t : NNReal) :
    (P.c0Semigroup hC0 hTime) t = P.c0Operator hC0 t :=
  rfl

theorem c0Semigroup_apply (hTime : P.HasContinuousC0Orbits hC0)
    (t : NNReal) (f : C₀(α, ℝ)) :
    (P.c0Semigroup hC0 hTime) t f = P.c0KernelIntegral hC0 t f :=
  rfl

/-- Evaluation of the packaged semigroup is exactly the raw kernel integral. -/
@[simp]
theorem c0Semigroup_apply_apply (hTime : P.HasContinuousC0Orbits hC0)
    (t : NNReal) (f : C₀(α, ℝ)) (x : α) :
    (P.c0Semigroup hC0 hTime) t f x = kernelIntegral (P t) f x :=
  rfl

section Feller

variable [LocallyCompactSpace α] [T2Space α]

/-- A combined Feller predicate supplies its spatial `C₀` property. -/
theorem IsFellerKernelSemigroup.mapsC0 {P : SubMarkovKernelSemigroup α}
    (hP : P.IsFellerKernelSemigroup) : P.MapsC0 :=
  hP.choose

/-- A combined Feller predicate supplies continuity of the corresponding `C₀` orbits. -/
theorem IsFellerKernelSemigroup.hasContinuousC0Orbits {P : SubMarkovKernelSemigroup α}
    (hP : P.IsFellerKernelSemigroup) : P.HasContinuousC0Orbits hP.mapsC0 :=
  hP.choose_spec

/-- The strongly continuous contraction semigroup selected by the combined Feller predicate. -/
noncomputable def IsFellerKernelSemigroup.c0Semigroup {P : SubMarkovKernelSemigroup α}
    (hP : P.IsFellerKernelSemigroup) :
    Semigroup.StronglyContinuousContractionSemigroup C₀(α, ℝ) :=
  P.c0Semigroup hP.mapsC0 hP.hasContinuousC0Orbits

@[simp]
theorem IsFellerKernelSemigroup.c0Semigroup_apply_apply
    {P : SubMarkovKernelSemigroup α} (hP : P.IsFellerKernelSemigroup)
    (t : NNReal) (f : C₀(α, ℝ)) (x : α) :
    hP.c0Semigroup t f x = kernelIntegral (P t) f x :=
  rfl

end Feller

end SubMarkovKernelSemigroup

end MarkovProcess
