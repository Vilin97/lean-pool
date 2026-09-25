/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Core
public import Mathlib.Logic.Small.Basic
/-!
# The carrier of a nonarchimedean local field is universe-small

The integer ring injects into the sequence of its finite quotients by powers
of the maximal ideal.  Its fraction field is therefore also small enough to
be represented in `Type 0`.  No countability of the field itself is asserted.
-/

@[expose] public section

noncomputable section

namespace LocalFieldTheory

open ValuationTheory.DiscreteValuationField
open ValuativeRel

universe u

/-- A local field in any universe has a carrier equivalent to a type in
`Type 0`. -/
theorem nonarchimedeanLocalField_small
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Small.{0} K := by
  let F : CompleteDVF.{u, u} K := localCompleteDVF K
  let O := F.valuationSubring
  let I := F.maximalIdeal
  let : Finite F.residueField := by
    change Finite 𝓀[K]
    infer_instance
  let : IsAdicComplete I O := F.isAdicComplete
  have hO : Small.{0} O := by
    let f : O → (∀ n : ℕ, O ⧸ I ^ n) :=
      fun x n => Ideal.Quotient.mk (I ^ n) x
    have hf : Function.Injective f := by
      intro x y h
      apply (IsHausdorff.eq_iff_smodEq (I := I)).2
      intro n
      simpa [f, Ideal.Quotient.mk_eq_mk_iff_sub_mem, SModEq] using congrFun h n
    exact small_of_injective hf
  let : Small.{0} O := hO
  let : IsFractionRing O K := F.toDVF.valuationSubring_isFractionRing
  apply small_of_surjective
    (f := fun p : O × O => (algebraMap O K p.1) / (algebraMap O K p.2))
  intro x
  obtain ⟨a, b, _, hab⟩ := IsFractionRing.div_surjective O x
  exact ⟨(a, b), hab⟩

end LocalFieldTheory
