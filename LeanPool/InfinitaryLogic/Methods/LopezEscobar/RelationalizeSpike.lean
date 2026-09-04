/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.LopezEscobar.WitnessLang
import LeanPool.InfinitaryLogic.Methods.Interpolation.GraphReconstruction
/-!
# The graph-relationalization spike (issue #10, Unit 1 part 2)

The two remaining Unit-1 acceptance gates of audit v2 (D4, graph-translation route):

* **the relationalization micro-pilot** — a nested numeral formula (`f(s(c)) = s(c)`,
  Marker's bullet-2 shape) mapped into the tagged `KLang L` along the left-witness
  embedding, relationalized through the Craig Layer-3 files, with its realization verified
  through `graphExpansion` all the way back to the witness-language semantics
  (`pilot_realize`), plus the side-specific graph axioms realized by the expansion
  (`pilot_graphAxioms`);
* **the decisive occurrence theorem** (`occurrence_intersection_base`) — the intersection
  of the two sides' complete relationalized symbol sets, *graph axioms included*, contains
  only graph-language images of base-`L` symbols.  No witness symbol survives: left/right
  witness symbols are disjoint (`WitnessLang.lean`), equality introduces no relation
  symbols (`relationsIn_relationalizeFormula`, `.equal` case), and the sharp calculation is
  Craig's `relSym_inter`.

With this compiled, the graph-language route is **frozen** and the hand-rolled relational
vocabulary of the audit's D4 is retired to its historical fallback note.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable (L : Language.{0, 0})

/-- Countability of a formula's function-symbol occurrence set, as an instance (feeds
`graphAxioms`). -/
instance {L' : Language.{0, 0}} {α : Type} {n : ℕ} (ψ : L'.BoundedFormulaω α n) :
    Countable ↥ψ.functionsIn :=
  ψ.functionsIn_countable.to_subtype

instance : Countable ↥(leftFuns L) := (Set.countable_range _).to_subtype



/-! ## The micro-pilot -/

/-- The pilot formula `f(s(c)) = s(c)` — Marker's bullet-2 shape, with a nested numeral. -/
private def pilotFormula : WitnessLang.Sentenceω :=
  BoundedFormulaω.equal
    (Term.func WitnessFun.f ![numTerm (Empty ⊕ Fin 0) 1])
    (numTerm (Empty ⊕ Fin 0) 1)

/-- **Micro-pilot, realization**: the relationalized image of the mapped pilot formula
realizes through the graph expansion exactly as the pilot formula realizes through the
left-witness reduct. -/
private theorem pilot_realize {M : Type} [instM : (KLang L).Structure M] :
    (@BoundedFormulaω.Realize (graphLanguage (KLang L)) M (graphExpansion (KLang L) M)
        Empty 0 (relationalizeFormula ((pilotFormula).mapLanguage (leftWitnessEmb L)))
        Empty.elim Fin.elim0) ↔
      (@Sentenceω.Realize WitnessLang pilotFormula M ((leftWitnessEmb L).reduct M)) := by
  let : WitnessLang.Structure M := (leftWitnessEmb L).reduct M
  have : (leftWitnessEmb L).IsExpansionOn M := LHom.isExpansionOn_reduct _ _
  exact (realize_relationalizeFormula _ _ _).trans
    (BoundedFormulaω.realize_mapLanguage (leftWitnessEmb L) pilotFormula
      (Empty.elim : Empty → M) Fin.elim0)

/-- **Micro-pilot, side-specific graph axioms**: the graph expansion of any tagged
structure realizes the left-witness graph axioms. -/
private theorem pilot_graphAxioms {M : Type} [Nonempty M] [(KLang L).Structure M] :
    letI := graphExpansion (KLang L) M
    Sentenceω.Realize (graphAxioms (leftFuns L)) M :=
  graphExpansion_realizes_graphAxioms (leftFuns L) M

/-! ## The decisive occurrence theorem -/

/-- `relSym` is monotone in both symbol sets. -/
private theorem relSym_mono {L' : Language.{0, 0}}
    {F F' : Set (Σ n, L'.Functions n)} {R R' : Set (Σ n, L'.Relations n)}
    (hF : F ⊆ F') (hR : R ⊆ R') : relSym L' F R ⊆ relSym L' F' R' :=
  Set.union_subset_union (Set.image_mono hR) (Set.image_mono hF)

/-- **The decisive occurrence theorem** (Unit-1 acceptance gate): for two `KLang`-sentences
whose symbols lie in base-plus-left and base-plus-right respectively, the intersection of
their complete relationalized symbol sets — graph axioms included — contains only
graph-language images of base-`L` symbols.  No witness symbol survives. -/
theorem occurrence_intersection_base (ψ₀ ψ₁ : (KLang L).Sentenceω)
    (hF₀ : ψ₀.functionsIn ⊆ baseFuns L ∪ leftFuns L)
    (hR₀ : ψ₀.relationsIn ⊆ baseRels L ∪ leftRels L)
    (hF₁ : ψ₁.functionsIn ⊆ baseFuns L ∪ rightFuns L)
    (hR₁ : ψ₁.relationsIn ⊆ baseRels L ∪ rightRels L) :
    ((graphAxioms ψ₀.functionsIn).and (relationalizeFormula ψ₀)).relationsIn ∩
      ((graphAxioms ψ₁.functionsIn).and (relationalizeFormula ψ₁)).relationsIn ⊆
      relSym (KLang L) (baseFuns L) (baseRels L) := by
  have hFinter : ψ₀.functionsIn ∩ ψ₁.functionsIn ⊆ baseFuns L := by
    rintro p ⟨h0, h1⟩
    rcases hF₀ h0 with hb | hl
    · exact hb
    · rcases hF₁ h1 with hb | hr
      · exact hb
      · have hdisj := leftFuns_inter_rightFuns L
        rw [Set.eq_empty_iff_forall_notMem] at hdisj
        exact absurd ⟨hl, hr⟩ (hdisj p)
  have hRinter : ψ₀.relationsIn ∩ ψ₁.relationsIn ⊆ baseRels L := by
    rintro p ⟨h0, h1⟩
    rcases hR₀ h0 with hb | hl
    · exact hb
    · rcases hR₁ h1 with hb | hr
      · exact hb
      · have hdisj := leftRels_inter_rightRels L
        rw [Set.eq_empty_iff_forall_notMem] at hdisj
        exact absurd ⟨hl, hr⟩ (hdisj p)
  rintro p ⟨hp0, hp1⟩
  rw [BoundedFormulaω.relationsIn_and, relationsIn_graphAxioms,
    relationsIn_relationalizeFormula] at hp0 hp1
  have hp0' : p ∈ relSym (KLang L) ψ₀.functionsIn ψ₀.relationsIn := by
    rcases hp0 with h | h
    · exact Set.mem_union_right _ h
    · exact h
  have hp1' : p ∈ relSym (KLang L) ψ₁.functionsIn ψ₁.relationsIn := by
    rcases hp1 with h | h
    · exact Set.mem_union_right _ h
    · exact h
  have hmem : p ∈ relSym (KLang L) (ψ₀.functionsIn ∩ ψ₁.functionsIn)
      (ψ₀.relationsIn ∩ ψ₁.relationsIn) := by
    rw [← relSym_inter]
    exact ⟨hp0', hp1'⟩
  exact relSym_mono hFinter hRinter hmem

end FirstOrder.Language
