/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.LopezEscobar.FunctionalTheta
import LeanPool.InfinitaryLogic.Methods.LanguageMapOccurrence
import LeanPool.InfinitaryLogic.Methods.LopezEscobar.RelationalizeSpike
import LeanPool.InfinitaryLogic.Methods.SchemaCompletion
/-!
# Assembly and graph translation: the PC sentence (issue #10, Unit 2b)

The side-parametric functional sentence — `functionalTheta` mapped into the tagged `KLang`
along the left or right witness embedding — and its relationalized PC form

`pcSentence side T = graphAxioms (sideFunsSet side) ⊓ relationalizeFormula (functionalPCSentence side T)`.

Acceptance gates (audit v2, Unit 2b):

* `graphExpansion_realizes_pcSentence` — graph expansions of functional models satisfy the
  PC sentence;
* `reconstruct_realizes_functionalPCSentence` — reconstruction from any model of the PC
  sentence satisfies the functional sentence;
* `functionsIn_pcSentence` — the PC sentence has **no** function symbols;
* `relationsIn_pcSentence_subset` — its relation symbols lie in the graph images of base
  symbols plus that side's tagged witness symbols;
* the support lemmas discharge the `occurrence_intersection_base` hypotheses directly, and
  `pcSentence_relationsIn_inter` is the two-presentation intersection bound.
-/

namespace FirstOrder.Language

open FirstOrder Structure Set

variable {L : Language.{0, 0}}


/-! ## Sides -/

/-- The two PC presentations. -/
inductive PCSide | left | right

variable (L) in
/-- The side embedding: base symbols in place, the witness copy tagged left or right. -/
def sideEmb : PCSide → (MidLang L →ᴸ KLang L)
  | .left => LHom.sumMap (LHom.id L) LHom.sumInl
  | .right => LHom.sumMap (LHom.id L) LHom.sumInr

variable (L) in
/-- That side's tagged witness function symbols. -/
def sideWitnessFuns : PCSide → Set (Σ n, (KLang L).Functions n)
  | .left => leftFuns L
  | .right => rightFuns L

variable (L) in
/-- That side's tagged witness relation symbols. -/
def sideWitnessRels : PCSide → Set (Σ n, (KLang L).Relations n)
  | .left => leftRels L
  | .right => rightRels L

variable (L) in
/-- The function symbols a side may mention: base plus its witness copy. -/
def sideFunsSet (side : PCSide) : Set (Σ n, (KLang L).Functions n) :=
  baseFuns L ∪ sideWitnessFuns L side

instance [Countable (Σ n, L.Functions n)] (side : PCSide) :
    Countable ↥(sideFunsSet L side) := by
  cases side <;>
    exact ((Set.countable_range _).union (Set.countable_range _)).to_subtype

/-- Every mid-language function symbol lands in base-or-side. -/
private theorem sideEmb_onFunction_mem (side : PCSide) (p : Σ n, (MidLang L).Functions n) :
    (⟨p.1, (sideEmb L side).onFunction p.2⟩ : Σ n, (KLang L).Functions n) ∈
      baseFuns L ∪ sideWitnessFuns L side := by
  obtain ⟨n, f⟩ := p
  cases side <;> cases f with
  | inl f => exact Or.inl ⟨⟨n, f⟩, rfl⟩
  | inr w => exact Or.inr ⟨⟨n, w⟩, rfl⟩

/-- Every mid-language relation symbol lands in base-or-side. -/
private theorem sideEmb_onRelation_mem (side : PCSide) (p : Σ n, (MidLang L).Relations n) :
    (⟨p.1, (sideEmb L side).onRelation p.2⟩ : Σ n, (KLang L).Relations n) ∈
      baseRels L ∪ sideWitnessRels L side := by
  obtain ⟨n, r⟩ := p
  cases side <;> cases r with
  | inl r => exact Or.inl ⟨⟨n, r⟩, rfl⟩
  | inr w => exact Or.inr ⟨⟨n, w⟩, rfl⟩

/-! ## The side-parametric functional sentence and its support -/

variable (L) in
/-- **The side-parametric functional PC sentence**: `functionalTheta` mapped into the
tagged language along the side's embedding — defined once, instantiated twice. -/
noncomputable def functionalPCSentence [Countable (Σ l, L.Relations l)] (side : PCSide)
    (T : (n : ℕ) → Set ((Fin n → Bool) × (Fin n → ℕ))) : (KLang L).Sentenceω :=
  (functionalTheta L T).mapLanguage (sideEmb L side)

private theorem functionsIn_functionalPCSentence [Countable (Σ l, L.Relations l)] (side : PCSide)
    (T : (n : ℕ) → Set ((Fin n → Bool) × (Fin n → ℕ))) :
    (functionalPCSentence L side T).functionsIn ⊆ baseFuns L ∪ sideWitnessFuns L side := by
  rw [functionalPCSentence, BoundedFormulaω.functionsIn_mapLanguage]
  rintro p ⟨q, -, rfl⟩
  exact sideEmb_onFunction_mem side q

private theorem relationsIn_functionalPCSentence [Countable (Σ l, L.Relations l)] (side : PCSide)
    (T : (n : ℕ) → Set ((Fin n → Bool) × (Fin n → ℕ))) :
    (functionalPCSentence L side T).relationsIn ⊆ baseRels L ∪ sideWitnessRels L side := by
  rw [functionalPCSentence, BoundedFormulaω.relationsIn_mapLanguage]
  rintro p ⟨q, -, rfl⟩
  exact sideEmb_onRelation_mem side q

/-! ## The PC sentence -/

variable (L) in
/-- **The PC sentence** of a side: that side's graph axioms conjoined with the
relationalized functional sentence. -/
noncomputable def pcSentence [Countable (Σ l, L.Relations l)]
    [Countable (Σ n, L.Functions n)] (side : PCSide)
    (T : (n : ℕ) → Set ((Fin n → Bool) × (Fin n → ℕ))) :
    (graphLanguage (KLang L)).Sentenceω :=
  (graphAxioms (sideFunsSet L side)).and
    (relationalizeFormula (functionalPCSentence L side T))

variable [Countable (Σ l, L.Relations l)] [Countable (Σ n, L.Functions n)]

/-- Realizing the PC sentence splits into the two conjuncts. -/
theorem realize_pcSentence_iff {N : Type} [(graphLanguage (KLang L)).Structure N]
    (side : PCSide) (T : (n : ℕ) → Set ((Fin n → Bool) × (Fin n → ℕ))) :
    Sentenceω.Realize (pcSentence L side T) N ↔
      (Sentenceω.Realize (graphAxioms (sideFunsSet L side)) N ∧
        Sentenceω.Realize (relationalizeFormula (functionalPCSentence L side T)) N) := by
  show BoundedFormulaω.Realize _ _ _ ↔ _
  rw [pcSentence, BoundedFormulaω.realize_and]
  rfl

/-- **Gate (a)**: the graph expansion of a functional model satisfies the PC sentence. -/
theorem graphExpansion_realizes_pcSentence {M : Type} [Nonempty M]
    [instM : (KLang L).Structure M] (side : PCSide)
    (T : (n : ℕ) → Set ((Fin n → Bool) × (Fin n → ℕ)))
    (hreal : Sentenceω.Realize (functionalPCSentence L side T) M) :
    @Sentenceω.Realize (graphLanguage (KLang L)) (pcSentence L side T) M
      (graphExpansion (KLang L) M) := by
  let := graphExpansion (KLang L) M
  rw [realize_pcSentence_iff]
  exact ⟨graphExpansion_realizes_graphAxioms _ M,
    (realize_relationalizeFormula _ _ _).mpr hreal⟩

/-- **Gate (b)**: the reconstruction of any model of the PC sentence's conjuncts satisfies
the functional sentence. -/
theorem reconstruct_realizes_functionalPCSentence {N : Type} [Nonempty N]
    [(graphLanguage (KLang L)).Structure N] (side : PCSide)
    (T : (n : ℕ) → Set ((Fin n → Bool) × (Fin n → ℕ)))
    (hAx : Sentenceω.Realize (graphAxioms (sideFunsSet L side)) N)
    (hrel : Sentenceω.Realize (relationalizeFormula (functionalPCSentence L side T)) N) :
    @Sentenceω.Realize (KLang L) (functionalPCSentence L side T) N
      (reconstructStructure (sideFunsSet L side) hAx) :=
  (realize_relationalize_reconstruct hAx _
    (functionsIn_functionalPCSentence side T) Empty.elim Fin.elim0).mp hrel

/-- **Gate (c)**: the PC sentence has no function symbols. -/
theorem functionsIn_pcSentence (side : PCSide)
    (T : (n : ℕ) → Set ((Fin n → Bool) × (Fin n → ℕ))) :
    (pcSentence L side T).functionsIn = ∅ :=
  BoundedFormulaω.functionsIn_of_isRelational _

/-- **Gate (d)**: the PC sentence's relation symbols lie in the graph images of the base
symbols plus that side's tagged witness symbols. -/
theorem relationsIn_pcSentence (side : PCSide)
    (T : (n : ℕ) → Set ((Fin n → Bool) × (Fin n → ℕ))) :
    (pcSentence L side T).relationsIn ⊆
      relSym (KLang L) (sideFunsSet L side) (baseRels L ∪ sideWitnessRels L side) := by
  rw [pcSentence, BoundedFormulaω.relationsIn_and, relationsIn_graphAxioms,
    relationsIn_relationalizeFormula]
  rintro p (hp | hp)
  · exact Set.mem_union_right _ hp
  · rcases hp with hp | hp
    · rcases hp with ⟨q, hq, rfl⟩
      exact Set.mem_union_left _
        (Set.mem_image_of_mem _ (relationsIn_functionalPCSentence side T hq))
    · rcases hp with ⟨q, hq, rfl⟩
      exact Set.mem_union_right _
        (Set.mem_image_of_mem _ (Set.union_subset_union_right _
          (fun _ h => h) (functionsIn_functionalPCSentence side T hq)))

/-- **Gate (e)**: the two presentations' relation symbols meet only in graph images of base
symbols — no witness symbol survives. -/
theorem pcSentence_relationsIn_inter
    (T₀ T₁ : (n : ℕ) → Set ((Fin n → Bool) × (Fin n → ℕ))) :
    (pcSentence L .left T₀).relationsIn ∩ (pcSentence L .right T₁).relationsIn ⊆
      relSym (KLang L) (baseFuns L) (baseRels L) := by
  have hFinter : sideFunsSet L .left ∩ sideFunsSet L .right ⊆ baseFuns L := by
    rintro p ⟨h0, h1⟩
    rcases h0 with hb | hl
    · exact hb
    · rcases h1 with hb | hr
      · exact hb
      · have hdisj := leftFuns_inter_rightFuns L
        rw [Set.eq_empty_iff_forall_notMem] at hdisj
        exact absurd ⟨hl, hr⟩ (hdisj p)
  have hRinter : (baseRels L ∪ sideWitnessRels L .left) ∩
      (baseRels L ∪ sideWitnessRels L .right) ⊆ baseRels L := by
    rintro p ⟨h0, h1⟩
    rcases h0 with hb | hl
    · exact hb
    · rcases h1 with hb | hr
      · exact hb
      · have hdisj := leftRels_inter_rightRels L
        rw [Set.eq_empty_iff_forall_notMem] at hdisj
        exact absurd ⟨hl, hr⟩ (hdisj p)
  rintro p ⟨hp0, hp1⟩
  have hp0' := relationsIn_pcSentence (L := L) .left T₀ hp0
  have hp1' := relationsIn_pcSentence (L := L) .right T₁ hp1
  have hmem : p ∈ relSym (KLang L)
      (sideFunsSet L .left ∩ sideFunsSet L .right)
      ((baseRels L ∪ sideWitnessRels L .left) ∩ (baseRels L ∪ sideWitnessRels L .right)) := by
    rw [← relSym_inter]
    exact ⟨hp0', hp1'⟩
  exact Set.union_subset_union (Set.image_mono hRinter) (Set.image_mono hFinter) hmem

end FirstOrder.Language
