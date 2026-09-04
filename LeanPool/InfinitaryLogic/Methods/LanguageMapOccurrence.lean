/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.GeneratedSublanguage
/-!
# Occurrence calculus for language maps

The exact image laws for `LHom.onTerm` / `BoundedFormulaω.mapLanguage`: symbol occurrences of a
mapped object are the image of the original's occurrences under the symbol map.

Neutral by construction — no schema, interpolation or PC content.  These were previously duplicated
across `SchemaCompletion.lean`, `Interpolation/CraigRelational.lean` and
`LopezEscobar/PCSentence.lean`; the last two declared **the same name**
`BoundedFormulaω.relationsIn_mapLanguage`, so which one a downstream file saw depended on import
order.  Consolidating here removes that hazard.
-/

namespace FirstOrder.Language

variable {L L' : Language.{0, 0}} (g : L →ᴸ L')

/-- `functionsIn` of a language-mapped term is the image of the term's `functionsIn` under the
symbol map `⟨n, f⟩ ↦ ⟨n, g.onFunction f⟩`. -/
private theorem Term.functionsIn_onTerm {α : Type} (t : L.Term α) :
    (g.onTerm t).functionsIn =
      (fun p : Σ n, L.Functions n => ⟨p.1, g.onFunction p.2⟩) '' t.functionsIn := by
  induction t with
  | var x => simp [LHom.onTerm, Term.functionsIn]
  | func f ts ih =>
    simp only [LHom.onTerm, Term.functionsIn, Set.image_insert_eq, Set.image_iUnion, ih]

/-- `functionsIn` of a language-mapped formula is the image of the formula's `functionsIn` under
the symbol map `⟨n, f⟩ ↦ ⟨n, g.onFunction f⟩`. -/
theorem BoundedFormulaω.functionsIn_mapLanguage {α : Type} {n : ℕ}
    (φ : L.BoundedFormulaω α n) :
    (φ.mapLanguage g).functionsIn =
      (fun p : Σ n, L.Functions n => ⟨p.1, g.onFunction p.2⟩) '' φ.functionsIn := by
  induction φ with
  | falsum => simp [BoundedFormulaω.mapLanguage, BoundedFormulaω.functionsIn]
  | equal t u =>
    simp [BoundedFormulaω.mapLanguage, BoundedFormulaω.functionsIn, Term.functionsIn_onTerm,
      Set.image_union]
  | rel R ts =>
    simp [BoundedFormulaω.mapLanguage, BoundedFormulaω.functionsIn, Term.functionsIn_onTerm,
      Set.image_iUnion]
  | imp φ ψ ihφ ihψ =>
    simp [BoundedFormulaω.mapLanguage, BoundedFormulaω.functionsIn, ihφ, ihψ, Set.image_union]
  | all φ ih => simp [BoundedFormulaω.mapLanguage, BoundedFormulaω.functionsIn, ih]
  | iSup φs ih =>
    simp [BoundedFormulaω.mapLanguage, BoundedFormulaω.functionsIn, ih, Set.image_iUnion]
  | iInf φs ih =>
    simp [BoundedFormulaω.mapLanguage, BoundedFormulaω.functionsIn, ih, Set.image_iUnion]

/-! ## `relationsIn` of a language-mapped formula (companion to `functionsIn_mapLanguage`) -/

theorem BoundedFormulaω.relationsIn_mapLanguage {L L' : Language} (g : L →ᴸ L') {α : Type} {n : ℕ}
    (φ : L.BoundedFormulaω α n) :
    (φ.mapLanguage g).relationsIn =
      (fun p : Σ n, L.Relations n => ⟨p.1, g.onRelation p.2⟩) '' φ.relationsIn := by
  induction φ with
  | falsum => simp [BoundedFormulaω.mapLanguage, BoundedFormulaω.relationsIn]
  | equal t u => simp [BoundedFormulaω.mapLanguage, BoundedFormulaω.relationsIn]
  | rel R ts => simp [BoundedFormulaω.mapLanguage, BoundedFormulaω.relationsIn]
  | imp φ ψ ihφ ihψ =>
    simp [BoundedFormulaω.mapLanguage, BoundedFormulaω.relationsIn, ihφ, ihψ, Set.image_union]
  | all φ ih => simp [BoundedFormulaω.mapLanguage, BoundedFormulaω.relationsIn, ih]
  | iSup φs ih =>
    simp [BoundedFormulaω.mapLanguage, BoundedFormulaω.relationsIn, ih, Set.image_iUnion]
  | iInf φs ih =>
    simp [BoundedFormulaω.mapLanguage, BoundedFormulaω.relationsIn, ih, Set.image_iUnion]

end FirstOrder.Language
