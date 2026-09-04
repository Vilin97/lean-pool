/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Descriptive.StructureSpace
import LeanPool.InfinitaryLogic.Lomega1omega.Theory
/-!
# Transport of codes along equivalences (generic `StructureSpaceOn` API)

The generic transport API for coded structures: given an `L`-structure on `M` and a
bijection `e : M ≃ α`, `encodeViaEquiv e` is the code on `α` obtained by pushing the
structure forward along `e`.  Its decoded structure is the induced structure, it satisfies
the same sentences, and it is `L`-isomorphic to the source.

These were previously private in `Descriptive/FiniteCarrier.lean`; they are not
finite-specific and are the transport layer the López–Escobar converse (issue #10) consumes,
so they live here at the `StructureSpaceOn` level.
-/

namespace FirstOrder.Language

namespace StructureSpaceOn

variable {L : Language.{u, v}} [L.IsRelational]

/-- Transport a structure along a bijection and encode it: the resulting code on `α`
decodes to a structure `L`-isomorphic to the source. -/
noncomputable def encodeViaEquiv {M : Type*} [L.Structure M] {α : Type*}
    (e : M ≃ α) : StructureSpaceOn L α :=
  ofStructure (@Equiv.inducedStructure L M α _ e)

/-- The decoded structure from `encodeViaEquiv` is the induced structure. -/
theorem toStructure_encodeViaEquiv_eq {M : Type*} [L.Structure M] {α : Type*}
    (e : M ≃ α) :
    (encodeViaEquiv e).toStructure = @Equiv.inducedStructure L M α _ e := by
  have hR := ‹L.IsRelational›
  ext n
  · exact (hR n).elim ‹_›
  · constructor
    · intro h
      rw [relMap_toStructure, encodeViaEquiv, ofStructure] at h
      simp only [decide_eq_true_eq] at h
      rwa [Equiv.inducedStructure_RelMap]
    · intro h
      rw [Equiv.inducedStructure_RelMap] at h
      rw [relMap_toStructure, encodeViaEquiv, ofStructure]
      simp [h]

/-- The encoded structure via an equivalence satisfies the same sentences. -/
theorem encodeViaEquiv_models {M : Type w} [L.Structure M] {α : Type w}
    [Countable α] {φ : L.Sentenceω} (e : M ≃ α) (hφ : Sentenceω.Realize φ M) :
    @Sentenceω.Realize L φ α (encodeViaEquiv e).toStructure := by
  rw [toStructure_encodeViaEquiv_eq]
  let : L.Structure α := Equiv.inducedStructure e
  exact (LomegaEquiv.of_equiv (Equiv.inducedStructureEquiv e) φ).mp hφ

/-- The encoded structure is `L`-isomorphic to the source via the equivalence. -/
theorem encodeViaEquiv_iso {M : Type*} [L.Structure M] {α : Type*} (e : M ≃ α) :
    Nonempty (@Language.Equiv L M α ‹_› (encodeViaEquiv e).toStructure) := by
  rw [toStructure_encodeViaEquiv_eq]
  exact ⟨Equiv.inducedStructureEquiv e⟩

end StructureSpaceOn

end FirstOrder.Language
