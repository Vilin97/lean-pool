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

omit [Countable ((l : ℕ) × L.Relations l)] in
/-- `isoSetoid φ` is the ambient relation pulled back along the subtype inclusion.  True by
definition; stated so consumers can rewrite with it without unfolding. -/
theorem isoSetoid_eq_comap (φ : L.Sentenceω) :
    isoSetoid φ = (structureIsoSetoid L).comap (Subtype.val : ↥(ModelsOf φ) → StructureSpace L) :=
  rfl

omit [Countable ((l : ℕ) × L.Relations l)] in
/-- Membership in the pulled-back relation is membership in the ambient one. -/
theorem isoSetoid_r_iff {φ : L.Sentenceω} {c₁ c₂ : ↥(ModelsOf φ)} :
    (isoSetoid φ).r c₁ c₂ ↔ (structureIsoSetoid L).r c₁.1 c₂.1 := Iff.rfl

/-! ### Sentence-level predicates

Stated ambiently, so that no Polish refinement of the model subtype appears in the
definitions. -/

/-- `φ` has a perfect set of pairwise non-isomorphic countable models. -/
def Sentenceω.HasPerfectSetOfPairwiseNonisomorphicNatModels (φ : L.Sentenceω) : Prop :=
  HasPerfectAntichainOn (structureIsoSetoid L) (ModelsOf φ)

/-- `φ` is thin on its countable models: no such perfect set. -/
def Sentenceω.IsThinOnNatModels (φ : L.Sentenceω) : Prop :=
  IsThinOn (structureIsoSetoid L) (ModelsOf φ)

omit [Countable ((l : ℕ) × L.Relations l)] in
theorem Sentenceω.isThinOnNatModels_iff {φ : L.Sentenceω} :
    φ.IsThinOnNatModels ↔ ¬φ.HasPerfectSetOfPairwiseNonisomorphicNatModels := Iff.rfl

/-- **The bridge to the existing quotient**: a perfect set of pairwise non-isomorphic models
gives continuum-many isomorphism classes.

The antichain lives in the ambient space, while the quotient is over the subtype, so the
transversal is transported through the inclusion — which is exactly what `isoSetoid_eq_comap`
licenses. -/
theorem Sentenceω.HasPerfectSetOfPairwiseNonisomorphicNatModels.continuum_le
    {φ : L.Sentenceω} (h : φ.HasPerfectSetOfPairwiseNonisomorphicNatModels) :
    Cardinal.continuum ≤ #(Quotient (isoSetoid φ)) := by
  obtain ⟨P, hperf, hne, hsub, hanti⟩ := h
  -- the ambient perfect set sits inside `ModelsOf φ`, so it maps into the subtype quotient
  have hinj : Function.Injective
      (fun x : P => (Quotient.mk (isoSetoid φ) ⟨x.1, hsub x.2⟩)) := by
    intro x y hxy
    have hq : Quotient.mk (isoSetoid φ) ⟨x.1, hsub x.2⟩
        = Quotient.mk (isoSetoid φ) ⟨y.1, hsub y.2⟩ := hxy
    have hr : (isoSetoid φ).r ⟨x.1, hsub x.2⟩ ⟨y.1, hsub y.2⟩ := Quotient.exact hq
    exact Subtype.ext (hanti x.1 x.2 y.1 y.2 (isoSetoid_r_iff.mp hr))
  -- `StructureSpace L` is metrizable but carries no chosen metric, so upgrade the Polish
  -- structure here; the topology is unchanged, hence `hperf` still applies.
  let := TopologicalSpace.upgradeIsCompletelyMetrizable (StructureSpace L)
  calc Cardinal.continuum = #P := (hperf.mk_eq_continuum hne).symm
    _ ≤ #(Quotient (isoSetoid φ)) := Cardinal.mk_le_of_injective hinj

/-! ### From a Polish refinement back to the ambient space

A Cantor antichain is built where the model class is well behaved — in a finer Polish topology
of the kind `modelsOf_isClopenable` supplies.  The perfect set, though, must be perfect in the
*ambient* `StructureSpace L`, or `IsThinOnNatModels` would be a statement about whichever
refinement happened to be chosen.

The two steps are ordered so that the delicate one never arises: coarsening is applied to the
**Cantor** antichain, where only continuity moves, and perfectness is then obtained in the
ambient space.  Nothing here asserts that perfectness survives coarsening — it does not in
general. -/

/-- The ambient topology on the structure space, bound by name so that statements quantifying
over a refinement can compare against it explicitly. -/
private abbrev ambientTop (L : Language.{u, v}) [L.IsRelational]
    [Countable (Σ l, L.Relations l)] : TopologicalSpace (StructureSpace L) := inferInstance

/-- The ambient half of the route: a Cantor antichain on the model class in the ambient topology
gives a perfect set of pairwise non-isomorphic models.

`StructureSpace L` is metrizable but carries no chosen metric, so the `T2Space` instance that
`HasCantorAntichainOn.hasPerfectAntichainOn` needs is produced here rather than assumed. -/
theorem Sentenceω.hasPerfectSet_of_ambient_cantorAntichain {φ : L.Sentenceω}
    (h : HasCantorAntichainOn (structureIsoSetoid L) (ModelsOf φ)) :
    φ.HasPerfectSetOfPairwiseNonisomorphicNatModels := by
  -- upgrading supplies a metric, hence `T2Space`, without changing the topology
  let := TopologicalSpace.upgradeIsCompletelyMetrizable (StructureSpace L)
  exact h.hasPerfectAntichainOn

/-- A Cantor antichain in any finer topology yields an **ambient** perfect set of pairwise
non-isomorphic models. -/
theorem Sentenceω.hasPerfectSet_of_refined_cantorAntichain {φ : L.Sentenceω}
    {t' : TopologicalSpace (StructureSpace L)} (hle : t' ≤ ambientTop L)
    (h : @HasCantorAntichainOn _ t' (structureIsoSetoid L) (ModelsOf φ)) :
    φ.HasPerfectSetOfPairwiseNonisomorphicNatModels :=
  Sentenceω.hasPerfectSet_of_ambient_cantorAntichain (h.mono_topology hle)

/-- The refinement `modelsOf_isClopenable` produces is one the route above accepts, and it is
still genuinely clopen: the conclusion keeps `IsClosed[t']` and `IsOpen[t']` alongside the
implication, so a consumer needing the clopen structure — as the tiered counting theorem may —
does not have to rebuild the refinement. -/
theorem Sentenceω.exists_clopenable_refinement_forcing_perfectSet (φ : L.Sentenceω) :
    ∃ t' : TopologicalSpace (StructureSpace L),
      t' ≤ ambientTop L ∧ @PolishSpace _ t' ∧
        @IsClosed _ t' (ModelsOf φ) ∧ @IsOpen _ t' (ModelsOf φ) ∧
        (@HasCantorAntichainOn _ t' (structureIsoSetoid L) (ModelsOf φ) →
          φ.HasPerfectSetOfPairwiseNonisomorphicNatModels) := by
  obtain ⟨t', hle, hpolish, hclosed, hopen⟩ := modelsOf_isClopenable φ
  exact ⟨t', hle, hpolish, hclosed, hopen,
    fun h => Sentenceω.hasPerfectSet_of_refined_cantorAntichain hle h⟩

end FirstOrder.Language
