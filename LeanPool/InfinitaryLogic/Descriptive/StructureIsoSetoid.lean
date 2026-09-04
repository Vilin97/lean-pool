/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Descriptive.ModelClassStandardBorel
import LeanPool.InfinitaryLogic.Descriptive.PerfectAntichain
import LeanPool.InfinitaryLogic.Descriptive.SatisfactionBorel
/-!
# The ambient isomorphism relation on coded structures

`isoSetoid φ` lives on the subtype `↥(ModelsOf φ)`, which means every statement about it is
implicitly a statement about a chosen Polish structure *on that subtype*.  For a perfect set
that is the wrong place to work: whether a set is perfect should be a fact about the ambient
`StructureSpace L`, not about a refinement chosen to make one particular model class Polish.

So the isomorphism relation is defined **once**, ambiently, as `structureIsoSetoid L`, and
`isoSetoid φ` *is* its pullback along the subtype inclusion — that is its definition, not a
theorem about it.  The sentence-level predicates below then quantify over perfect subsets of
`StructureSpace L` contained in `ModelsOf φ`, and the chosen refinement never enters their
statements.
-/

open Cardinal Set

universe u v

namespace FirstOrder.Language

variable {L : Language.{u, v}} [L.IsRelational]

/-- **The ambient isomorphism relation**: two codes are related iff the structures they decode
on `ℕ` are `L`-isomorphic.  Stated on all of `StructureSpace L`, with no reference to any
sentence. -/
def structureIsoSetoid (L : Language.{u, v}) [L.IsRelational] : Setoid (StructureSpace L) where
  r c₁ c₂ := Nonempty (@Language.Equiv L ℕ ℕ c₁.toStructure c₂.toStructure)
  iseqv :=
    { refl := fun c => ⟨@Language.Equiv.refl L ℕ c.toStructure⟩
      symm := fun {c₁ c₂} ⟨e⟩ => ⟨@Language.Equiv.symm L ℕ ℕ c₁.toStructure c₂.toStructure e⟩
      trans := fun {c₁ c₂ c₃} ⟨e₁⟩ ⟨e₂⟩ =>
        ⟨@Language.Equiv.comp L ℕ ℕ c₁.toStructure c₂.toStructure ℕ c₃.toStructure e₂ e₁⟩ }

variable [Countable (Σ l, L.Relations l)]

/-- The isomorphism equivalence relation on coded ℕ-models of φ: the ambient relation
restricted to the models of `φ`.  Two codes are related iff the decoded structures on ℕ are
L-isomorphic. -/
def isoSetoid (φ : L.Sentenceω) : Setoid ↥(ModelsOf φ) :=
  (structureIsoSetoid L).comap Subtype.val





/-! ### Sentence-level predicates

Stated ambiently, so that no Polish refinement of the model subtype appears in the
definitions. -/



/-- `φ` is thin on its countable models: no such perfect set. -/
private def Sentenceω.IsThinOnNatModels (φ : L.Sentenceω) : Prop :=
  IsThinOn (structureIsoSetoid L) (ModelsOf φ)





/-! ### From a Polish refinement back to the ambient space

A Cantor antichain is built where the model class is well behaved — in a finer Polish topology
of the kind `modelsOf_isClopenable` supplies.  The perfect set, though, must be perfect in the
*ambient* `StructureSpace L`, or `IsThinOnNatModels` would be a statement about whichever
refinement happened to be chosen.

The two steps are ordered so that the delicate one never arises: coarsening is applied to the
**Cantor** antichain, where only continuity moves, and perfectness is then obtained in the
ambient space.  Nothing here asserts that perfectness survives coarsening — it does not in
general. -/









end FirstOrder.Language
