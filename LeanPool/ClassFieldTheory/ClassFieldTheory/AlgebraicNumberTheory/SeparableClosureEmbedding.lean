/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KrullTopology
import Mathlib.NumberTheory.NumberField.Basic
/-!
# Embeddings into a separable closure

This file provides the common realization of a separable extension inside the
chosen separable closure of its base field.
-/

noncomputable section

namespace AlgebraicNumberTheory

universe u v

/-- Conjugation by a field equivalence is continuous on automorphism
groups equipped with the Krull topology. -/
theorem continuous_algEquiv_autCongr
    {F E E' : Type*}
    [Field F] [Field E] [Field E']
    [Algebra F E] [Algebra F E']
    (e : E ≃ₐ[F] E') :
    Continuous (AlgEquiv.autCongr e) := by
  apply continuous_of_continuousAt_one _
  rw [continuousAt_def]
  intro s hs
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨M, hMfinite, hMs⟩ := hs
  let : FiniteDimensional F M := hMfinite
  let N : IntermediateField F E :=
    M.map e.symm.toAlgHom
  let : FiniteDimensional F N :=
    (M.equivMap e.symm.toAlgHom).toLinearEquiv.finiteDimensional
  rw [krullTopology_mem_nhds_one_iff]
  refine ⟨N, inferInstance, ?_⟩
  intro σ hσ
  apply hMs
  apply (IntermediateField.mem_fixingSubgroup_iff M
    (AlgEquiv.autCongr e σ)).2
  intro x hx
  have hxN : e.symm x ∈ N :=
    ⟨x, hx, rfl⟩
  have hfix :=
    (IntermediateField.mem_fixingSubgroup_iff N σ).1 hσ
      (e.symm x) hxN
  change e (σ (e.symm x)) = x
  rw [hfix, e.apply_symm_apply]

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
  [Algebra.IsSeparable K L]

/-- A chosen embedding of a separable extension into the separable closure of
its base field. -/
noncomputable def separableEmbeddingIntoSeparableClosure :
    L →ₐ[K] SeparableClosure K :=
  IsSepClosed.lift

variable (K : Type*) [Field K] [NumberField K]

/-- A chosen `ℚ`-embedding of a number field into mathlib's fixed
separable closure of `ℚ`. -/
noncomputable def numberFieldSeparableClosureEmbedding :
    K →ₐ[ℚ] SeparableClosure ℚ :=
  IsSepClosed.lift

/-- The actual copy of `K` cut out by the chosen embedding into
`SeparableClosure ℚ`. -/
def numberFieldInRationalSeparableClosure :
    IntermediateField ℚ (SeparableClosure ℚ) :=
  (numberFieldSeparableClosureEmbedding K).fieldRange

noncomputable instance
    numberFieldInRationalSeparableClosure_finiteDimensional :
    FiniteDimensional ℚ
      (numberFieldInRationalSeparableClosure K) :=
  ((numberFieldSeparableClosureEmbedding K).equivFieldRange.toLinearEquiv).finiteDimensional

noncomputable instance
    numberFieldInRationalSeparableClosure_numberField :
    NumberField (numberFieldInRationalSeparableClosure K) where
  to_charZero := inferInstance
  to_finiteDimensional := inferInstance

end AlgebraicNumberTheory
