/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.LopezEscobar.PCMem
/-!
# Tagged-expansion gluing (issue #10, Unit 4 commit 2)

The critical semantic gate: two `PCMem` witnesses `Sl`, `Sr` for the two side sentences may
be *different* `graphLanguage (KLang L)`-structures on the same base model `M`.  The glued
structure uses `Sl` on the base-and-left symbols and `Sr` on the right-witness symbols; it
agrees with `Sl` on the left sentence's occurrence set and with `Sr` on the right's, so
`realize_congr_symbolsIn` transports both satisfactions to the single combined structure.

Endpoint (`pcMem_glue`): `PCMem ψleft M ∧ PCMem ψright M → ∃ S, Realize ψleft M ∧ Realize ψright M`,
the realizations using `S`.
-/

namespace FirstOrder.Language

open FirstOrder Structure Set

variable {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ l, L.Relations l)]
  {M : Type} [instL : L.Structure M]

/-- **The glued structure**: `Sr` on the right-witness symbols, `Sl` everywhere else. -/
@[reducible] def gluedStructure (Sl Sr : (graphLanguage (KLang L)).Structure M) :
    (graphLanguage (KLang L)).Structure M where
  funMap {_} f _ := isEmptyElim f
  RelMap {n} r x :=
    match r with
    | GraphRelation.base (Sum.inr (Sum.inr w)) =>
        @Structure.RelMap _ M Sr n (GraphRelation.base (Sum.inr (Sum.inr w))) x
    | GraphRelation.graph (Sum.inr (Sum.inr w)) =>
        @Structure.RelMap _ M Sr _ (GraphRelation.graph (Sum.inr (Sum.inr w))) x
    | r => @Structure.RelMap _ M Sl n r x

omit [Countable (Σ l, L.Relations l)] instL in
/-- On base-`L` and left-witness symbols the glue is `Sl` (definitionally). -/
private theorem gluedStructure_agree_left (Sl Sr : (graphLanguage (KLang L)).Structure M)
    {p : Σ n, GraphRelation (KLang L) n}
    (hp : p ∈ relSym (KLang L) (sideFunsSet L .left) (baseRels L ∪ leftRels L))
    (x : Fin p.1 → M) :
    @Structure.RelMap _ M Sl p.1 p.2 x
      ↔ @Structure.RelMap _ M (gluedStructure Sl Sr) p.1 p.2 x := by
  rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
  · rcases hq with ⟨r0, rfl⟩ | ⟨r0, rfl⟩ <;> exact Iff.rfl
  · rcases hq with ⟨f0, rfl⟩ | ⟨f0, rfl⟩
    · exact isEmptyElim f0.2
    · exact Iff.rfl

omit [Countable (Σ l, L.Relations l)] in
/-- On base-`L` and right-witness symbols the glue is `Sr` — using the shared base for the
`L`-relations (both `Sl` and `Sr` expand the same base). -/
private theorem gluedStructure_agree_right (Sl Sr : (graphLanguage (KLang L)).Structure M)
    (hSlExp : @LHom.IsExpansionOn L (graphLanguage (KLang L)) baseGraphEmb M instL Sl)
    (hSrExp : @LHom.IsExpansionOn L (graphLanguage (KLang L)) baseGraphEmb M instL Sr)
    {p : Σ n, GraphRelation (KLang L) n}
    (hp : p ∈ relSym (KLang L) (sideFunsSet L .right) (baseRels L ∪ rightRels L))
    (x : Fin p.1 → M) :
    @Structure.RelMap _ M Sr p.1 p.2 x
      ↔ @Structure.RelMap _ M (gluedStructure Sl Sr) p.1 p.2 x := by
  rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
  · rcases hq with ⟨r0, rfl⟩ | ⟨r0, rfl⟩
    · -- base `L`-relation: glue is `Sl`, and `Sl = Sr` on it via the shared base
      show @Structure.RelMap _ M Sr r0.1 (GraphRelation.base (Sum.inl r0.2)) x
        ↔ @Structure.RelMap _ M Sl r0.1 (GraphRelation.base (Sum.inl r0.2)) x
      rw [show @Structure.RelMap _ M Sr r0.1 (GraphRelation.base (Sum.inl r0.2)) x
          = @Structure.RelMap L M instL r0.1 r0.2 x from hSrExp.map_onRelation r0.2 x,
        show @Structure.RelMap _ M Sl r0.1 (GraphRelation.base (Sum.inl r0.2)) x
          = @Structure.RelMap L M instL r0.1 r0.2 x from hSlExp.map_onRelation r0.2 x]
    · exact Iff.rfl
  · rcases hq with ⟨f0, rfl⟩ | ⟨f0, rfl⟩
    · exact isEmptyElim f0.2
    · exact Iff.rfl

/-- **The gluing endpoint**: two same-base projective-class witnesses glue to a single model
of both side sentences. -/
theorem pcMem_glue (T₀ T₁ : (n : ℕ) → Set ((Fin n → Bool) × (Fin n → ℕ)))
    (hL : @PCMem L (graphLanguage (KLang L)) baseGraphEmb (pcSentence L .left T₀) M instL)
    (hR : @PCMem L (graphLanguage (KLang L)) baseGraphEmb (pcSentence L .right T₁) M instL) :
    ∃ S : (graphLanguage (KLang L)).Structure M,
      @Sentenceω.Realize (graphLanguage (KLang L)) (pcSentence L .left T₀) M S ∧
      @Sentenceω.Realize (graphLanguage (KLang L)) (pcSentence L .right T₁) M S := by
  obtain ⟨Sl, hSlExp, hSlReal⟩ := hL
  obtain ⟨Sr, hSrExp, hSrReal⟩ := hR
  refine ⟨gluedStructure Sl Sr, ?_, ?_⟩
  · exact (BoundedFormulaω.realize_congr_symbolsIn Sl (gluedStructure Sl Sr)
      (pcSentence L .left T₀)
      (fun p hp x => absurd hp (by rw [functionsIn_pcSentence]; exact Set.notMem_empty p))
      (fun p hp x => gluedStructure_agree_left Sl Sr
        (relationsIn_pcSentence .left T₀ hp) x)
      Empty.elim Fin.elim0).mp hSlReal
  · exact (BoundedFormulaω.realize_congr_symbolsIn Sr (gluedStructure Sl Sr)
      (pcSentence L .right T₁)
      (fun p hp x => absurd hp (by rw [functionsIn_pcSentence]; exact Set.notMem_empty p))
      (fun p hp x => gluedStructure_agree_right Sl Sr hSlExp hSrExp
        (relationsIn_pcSentence .right T₁ hp) x)
      Empty.elim Fin.elim0).mp hSrReal

end FirstOrder.Language
