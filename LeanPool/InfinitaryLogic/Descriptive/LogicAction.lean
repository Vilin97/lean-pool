/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Descriptive.LopezEscobarEasy
import Mathlib.GroupTheory.Perm.Basic

/-!
# The logic action of `S∞ = Equiv.Perm ℕ` on the structure space (issue #27, algebraic layer)

The topology-free core of issue #27: `S∞ = Equiv.Perm ℕ` acts on `StructureSpace L` by relabeling
the carrier, orbits coincide with decoded-structure isomorphism, and action-invariance coincides
with the repository's `IsomorphismInvariant`.

**Frozen convention** (the inverse must be pinned before any invariance / measurable API is built
on it): `(σ • c) ⟨R, v⟩ = c ⟨R, σ⁻¹ ∘ v⟩`. Then the orbit of `c` is exactly its decoded
isomorphism class.

The `Fin n` analogue (`Descriptive/FiniteCarrier.lean`, `permSmul`/`iso_iff_orbit`) is the pilot;
this is the `ℕ`-tier that issue #27 packages (and that #28 will build its σ-algebra on). The
topology, Polish-group structure, and `ContinuousSMul` are the *next* milestones of #27, not here.
-/

namespace FirstOrder

namespace Language

open Structure

variable {L : Language.{0, 0}}

/-! ## The action -/

/-- `S∞ = Equiv.Perm ℕ` acts on `StructureSpace L` by relabeling the carrier:
`(σ • c) ⟨R, v⟩ = c ⟨R, σ⁻¹ ∘ v⟩`. -/
instance instSMulPermStructureSpace : SMul (Equiv.Perm ℕ) (StructureSpace L) where
  smul σ c := fun q => c ⟨q.1, ⇑σ⁻¹ ∘ q.2⟩

@[simp] theorem logicAction_apply (σ : Equiv.Perm ℕ) (c : StructureSpace L)
    (R : Σ l, L.Relations l) (v : Fin R.1 → ℕ) :
    (σ • c) ⟨R, v⟩ = c ⟨R, ⇑σ⁻¹ ∘ v⟩ := rfl

/-- **Action invariance** of a class of coded structures. -/
def ActionInvariant (B : Set (StructureSpace L)) : Prop :=
  ∀ (σ : Equiv.Perm ℕ) (c : StructureSpace L), c ∈ B ↔ σ • c ∈ B

variable [L.IsRelational]

/-! ## Orbits are decoded-structure isomorphism -/

/-- **Orbit = isomorphism**: two codes lie in the same `S∞`-orbit iff their decoded structures are
`L`-isomorphic. -/
private theorem orbit_iff_iso (c d : StructureSpace L) :
    (∃ σ : Equiv.Perm ℕ, σ • c = d) ↔
      Nonempty (@Language.Equiv L ℕ ℕ c.toStructure d.toStructure) := by
  constructor
  · rintro ⟨σ, rfl⟩
    refine ⟨@Language.Equiv.mk L ℕ ℕ c.toStructure (σ • c).toStructure σ
      (fun f => isEmptyElim f) (fun {l} R v => ?_)⟩
    rw [StructureSpace.relMap_toStructure, StructureSpace.relMap_toStructure, logicAction_apply]
    simp only [Equiv.toFun_as_coe]
    rw [show (⇑σ⁻¹ ∘ ⇑σ ∘ v) = v from by funext i; simp]
  · rintro ⟨e⟩
    refine ⟨@Language.Equiv.toEquiv L ℕ ℕ c.toStructure d.toStructure e, ?_⟩
    set σ := @Language.Equiv.toEquiv L ℕ ℕ c.toStructure d.toStructure e with hσ
    funext q
    obtain ⟨⟨l, R⟩, v⟩ := q
    simp only [logicAction_apply]
    have hrel := @Language.Equiv.map_rel' L ℕ ℕ c.toStructure d.toStructure e l R (⇑σ⁻¹ ∘ v)
    rw [StructureSpace.relMap_toStructure, StructureSpace.relMap_toStructure] at hrel
    simp only [Equiv.toFun_as_coe, ← hσ] at hrel
    rw [show (⇑σ ∘ ⇑σ⁻¹ ∘ v) = v from by funext i; simp] at hrel
    cases h₁ : c ⟨⟨l, R⟩, ⇑σ⁻¹ ∘ v⟩ <;> cases h₂ : d ⟨⟨l, R⟩, v⟩ <;> simp_all

/-! ## Action invariance = isomorphism invariance -/

/-- **The equivalence** (issue #27, milestone 10): action-invariance and isomorphism-invariance of
a class of coded structures coincide. -/
theorem actionInvariant_iff_isomorphismInvariant (B : Set (StructureSpace L)) :
    ActionInvariant B ↔ IsomorphismInvariant B := by
  constructor
  · intro hact c d hiso
    obtain ⟨σ, hσ⟩ := (orbit_iff_iso c d).mpr hiso
    rw [← hσ]; exact hact σ c
  · intro hiso σ c
    exact hiso c (σ • c) ((orbit_iff_iso c (σ • c)).mp ⟨σ, rfl⟩)

end Language

end FirstOrder
