/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.ModelTheory.PCClass
import LeanPool.InfinitaryLogic.Methods.LopezEscobar.StandardModel
/-!
# The López–Escobar PC-class interface (issue #10, Unit 4 commit 1)

The base embedding `baseGraphEmb : L →ᴸ graphLanguage (KLang L)` (available because `L` is
relational), and the code compatibility theorem tying the abstract `PCMem` on `ℕ` to
membership in `codeReduct '' ModelsOf Θ`.  This freezes the PC-class interface independently
of López–Escobar's tree machinery.
-/

namespace FirstOrder.Language

open FirstOrder Structure Set

variable {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-- The base embedding of `L` into the relationalized `graphLanguage (KLang L)`: functions are
vacuous (`L` is relational), base relations go to their graph-language base image. -/
def baseGraphEmb : L →ᴸ graphLanguage (KLang L) where
  onFunction {_} f := isEmptyElim f
  onRelation {_} R := GraphRelation.base (Sum.inl R)

omit [Countable (Σ l, L.Relations l)] in
@[simp] theorem baseGraphEmb_onRelation {n : ℕ} (R : L.Relations n) :
    (baseGraphEmb (L := L)).onRelation R = GraphRelation.base (Sum.inl R) := rfl

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- The decoded structure of an encoded `graphLanguage (KLang L)`-structure is itself. -/
private theorem toStructure_ofStructure_graph (S' : (graphLanguage (KLang L)).Structure ℕ) :
    (StructureSpaceOn.ofStructure S').toStructure = S' := by
  apply Structure.ext
  · funext k f a; exact isEmptyElim f
  · funext k r a; exact propext (StructureSpaceOn.toStructure_ofStructure S' r a)

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- A `graphLanguage (KLang L)`-structure modelling `Θ` encodes to a code in `ModelsOf Θ`. -/
private theorem mem_modelsOf_ofStructure {Θ : (graphLanguage (KLang L)).Sentenceω}
    {S' : (graphLanguage (KLang L)).Structure ℕ}
    (h : @Sentenceω.Realize (graphLanguage (KLang L)) Θ ℕ S') :
    StructureSpaceOn.ofStructure S' ∈ ModelsOf Θ := by
  show @Sentenceω.Realize (graphLanguage (KLang L)) Θ ℕ (StructureSpaceOn.ofStructure S').toStructure
  rw [toStructure_ofStructure_graph]; exact h

omit [Countable (Σ l, L.Relations l)] in
/-- **Code compatibility**: a base code `c` is a base reduct of a model of `Θ` iff `ℕ` (as the
`L`-structure `c.toStructure`) is in the projective class of `Θ` along `baseGraphEmb`. -/
theorem pcMem_iff_mem_codeReduct_image (Θ : (graphLanguage (KLang L)).Sentenceω)
    (c : StructureSpace L) :
    c ∈ codeReduct '' ModelsOf Θ ↔
      @PCMem L (graphLanguage (KLang L)) baseGraphEmb Θ ℕ c.toStructure := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d.toStructure, @LHom.IsExpansionOn.mk L (graphLanguage (KLang L)) baseGraphEmb ℕ
      (codeReduct d).toStructure d.toStructure (fun {_} f _ => isEmptyElim f)
      (fun {_} R x => propext (codeReduct_toStructure (d := d) R x).symm), hd⟩
  · rintro ⟨S', hexp, hreal⟩
    let : L.Structure ℕ := c.toStructure
    refine ⟨StructureSpaceOn.ofStructure S', mem_modelsOf_ofStructure hreal, ?_⟩
    · funext q
      rw [Bool.eq_iff_iff]
      show (StructureSpaceOn.ofStructure S') ⟨⟨q.1.1, GraphRelation.base (Sum.inl q.1.2)⟩, q.2⟩
          = true ↔ c q = true
      rw [← StructureSpaceOn.relMap_toStructure (StructureSpaceOn.ofStructure S')
          (GraphRelation.base (Sum.inl q.1.2)) q.2, toStructure_ofStructure_graph,
        show @Structure.RelMap (graphLanguage (KLang L)) ℕ S' q.1.1
            (GraphRelation.base (Sum.inl q.1.2)) q.2
          = @Structure.RelMap L ℕ c.toStructure q.1.1 q.1.2 q.2
          from @LHom.IsExpansionOn.map_onRelation L (graphLanguage (KLang L)) baseGraphEmb ℕ
            c.toStructure S' hexp q.1.1 q.1.2 q.2]
      exact StructureSpace.relMap_toStructure c q.1.2 q.2

end FirstOrder.Language
