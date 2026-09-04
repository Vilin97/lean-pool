/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.LopezEscobar.TaggedGlue
import LeanPool.InfinitaryLogic.Methods.LopezEscobar.CodeClass
import LeanPool.InfinitaryLogic.ModelTheory.FragmentLowenheimSkolem
import LeanPool.InfinitaryLogic.Lomega1omega.Entailment
import LeanPool.InfinitaryLogic.Descriptive.InvariantMeasurableSpace
/-!
# The sole Löwenheim–Skolem consumer (issue #10, Unit 4 commit 3)

`FragmentLowenheimSkolem` is imported **only** here.  From a glued model of both side
sentences, a countable fragment-elementary substructure models both; the tagged zero-ary
witness `c`'s graph-totality axiom bootstraps its nonemptiness; reconstruction plus
`numMap_bijective` make it infinite; transported to `ℕ` it yields a single code lying in both
`B` (`pcClass_eq` with `hinv`) and `Bᶜ` (`pcClass_eq` with `hinv.compl`) — a contradiction.

Endpoints: `pcMem_disjoint` and `pcSentences_entails_not`, the latter being exactly what
Unit 5 feeds to `craig_pcSeparation_relational`.
-/

namespace FirstOrder.Language

open FirstOrder Structure Set

variable {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

instance : Countable (Σ n, (graphLanguage (KLang L)).Functions n) := by
  have : IsEmpty (Σ n, (graphLanguage (KLang L)).Functions n) :=
    ⟨fun p => (graphLanguage_isRelational (KLang L) p.1).false p.2⟩
  infer_instance

/-- **Projective-class disjointness** (the sole `IsomorphismInvariant` × downward-LS consumer):
if `B`'s tree is `T₀` and `Bᶜ`'s is `T₁`, no base model is simultaneously in the projective
classes of the two side sentences. -/
theorem pcMem_disjoint {B : Set (StructureSpace L)}
    (T₀ T₁ : (n : ℕ) → Set ((Fin n → Bool) × (Fin n → ℕ)))
    (hT₀ : ∀ c : StructureSpace L, c ∈ B ↔ ∃ g : ℕ → ℕ,
      ∀ n, ((fun i : Fin n => queryCode c (i : ℕ)), (fun i : Fin n => g i)) ∈ T₀ n)
    (hT₁ : ∀ c : StructureSpace L, c ∈ Bᶜ ↔ ∃ g : ℕ → ℕ,
      ∀ n, ((fun i : Fin n => queryCode c (i : ℕ)), (fun i : Fin n => g i)) ∈ T₁ n)
    (hinv : IsomorphismInvariant B)
    (M : Type) [instL : L.Structure M] :
    ¬ (@PCMem L (graphLanguage (KLang L)) baseGraphEmb (pcSentence L .left T₀) M instL ∧
       @PCMem L (graphLanguage (KLang L)) baseGraphEmb (pcSentence L .right T₁) M instL) := by
  rintro ⟨hL, hR⟩
  obtain ⟨S, hSleft, hSright⟩ := pcMem_glue T₀ T₁ hL hR
  let : (graphLanguage (KLang L)).Structure M := S
  -- countable fragment-elementary substructure modelling both side sentences
  obtain ⟨N, -, hAe, hCount⟩ := exists_countable_aElementary_substructure
    (Fragment.generatedSentence ((pcSentence L .left T₀).and (pcSentence L .right T₁)))
    (X := (∅ : Set M)) Set.countable_empty (Fragment.generatedSentence_countable _)
  have := hCount
  have hNand : @Sentenceω.Realize (graphLanguage (KLang L))
      ((pcSentence L .left T₀).and (pcSentence L .right T₁)) ↥N _ :=
    (hAe.realize_sentence_iff (Fragment.mem_generatedSentence _)).mp
      ((BoundedFormulaω.realize_and _ _).mpr ⟨hSleft, hSright⟩)
  -- ascribed at the sentence level: `SentenceInf.Realize` is a plain definition upstream, so the
  -- unifier cannot solve `realize_pcSentence_iff`'s implicit arguments against a goal that is
  -- already unfolded to the bounded-formula level
  have hNleft : @Sentenceω.Realize (graphLanguage (KLang L)) (pcSentence L .left T₀) ↥N _ :=
    ((BoundedFormulaω.realize_and _ _).mp hNand).1
  have hNright : @Sentenceω.Realize (graphLanguage (KLang L)) (pcSentence L .right T₁) ↥N _ :=
    ((BoundedFormulaω.realize_and _ _).mp hNand).2
  obtain ⟨hAxN, hrelN⟩ := (realize_pcSentence_iff .left T₀).mp hNleft
  -- nonemptiness bootstrap from the graph-totality of the tagged zero-ary witness `c`
  have : Nonempty N := by
    have hc : (⟨0, Sum.inr (Sum.inl WitnessFun.c)⟩ : Σ n, (KLang L).Functions n)
        ∈ sideFunsSet L .left := Or.inr ⟨⟨0, WitnessFun.c⟩, rfl⟩
    have htot := ((realize_graphAxioms_iff (sideFunsSet L .left)).mp hAxN
      ⟨⟨0, Sum.inr (Sum.inl WitnessFun.c)⟩, hc⟩).1
    obtain ⟨y, -⟩ := (realize_graphTotality _).mp htot Fin.elim0
    exact ⟨y⟩
  -- reconstruct the functional structure and make `N` infinite
  let Kstar : (KLang L).Structure N := reconstructStructure (sideFunsSet L .left) hAxN
  let Mstar : (MidLang L).Structure N := (sideEmb L .left).reduct N
  have hM : @Sentenceω.Realize (MidLang L) (functionalTheta L T₀) N Mstar := by
    have h1 := reconstruct_realizes_functionalPCSentence .left T₀ hAxN hrelN
    rw [functionalPCSentence] at h1
    exact (BoundedFormulaω.realize_mapLanguage (sideEmb L .left) (functionalTheta L T₀)
      (Empty.elim : Empty → N) Fin.elim0).mp h1
  obtain ⟨homega, -⟩ := (realize_functionalTheta T₀).mp hM
  have hν := numMap_bijective homega
  have : Infinite N := Infinite.of_injective (numMap L N) hν.injective
  -- transport both side sentences to `ℕ`
  let e : N ≃ ℕ := (nonempty_equiv_of_countable (α := N) (β := ℕ)).some
  have hdleft : StructureSpaceOn.encodeViaEquiv e ∈ ModelsOf (pcSentence L .left T₀) :=
    StructureSpaceOn.encodeViaEquiv_models e hNleft
  have hdright : StructureSpaceOn.encodeViaEquiv e ∈ ModelsOf (pcSentence L .right T₁) :=
    StructureSpaceOn.encodeViaEquiv_models e hNright
  -- the base reduct lands in `B ∩ Bᶜ`
  have hInB : codeReduct (StructureSpaceOn.encodeViaEquiv e) ∈ B := by
    rw [← pcClass_eq .left T₀ hT₀ hinv]
    exact ⟨_, hdleft, rfl⟩
  have hInBc : codeReduct (StructureSpaceOn.encodeViaEquiv e) ∈ Bᶜ := by
    rw [← pcClass_eq .right T₁ hT₁ (IsomorphismInvariant.compl hinv)]
    exact ⟨_, hdright, rfl⟩
  exact hInBc hInB

/-- **The entailment endpoint** — exactly what Unit 5 feeds to Craig PC-separation: no model
satisfies both side sentences, so the left entails the negation of the right. -/
theorem pcSentences_entails_not {B : Set (StructureSpace L)}
    (T₀ T₁ : (n : ℕ) → Set ((Fin n → Bool) × (Fin n → ℕ)))
    (hT₀ : ∀ c : StructureSpace L, c ∈ B ↔ ∃ g : ℕ → ℕ,
      ∀ n, ((fun i : Fin n => queryCode c (i : ℕ)), (fun i : Fin n => g i)) ∈ T₀ n)
    (hT₁ : ∀ c : StructureSpace L, c ∈ Bᶜ ↔ ∃ g : ℕ → ℕ,
      ∀ n, ((fun i : Fin n => queryCode c (i : ℕ)), (fun i : Fin n => g i)) ∈ T₁ n)
    (hinv : IsomorphismInvariant B) :
    Sentenceω.Entails (pcSentence L .left T₀) (pcSentence L .right T₁).not := by
  intro M instM neM hmodel
  have hleft : @Sentenceω.Realize (graphLanguage (KLang L)) (pcSentence L .left T₀) M instM :=
    hmodel _ (Set.mem_singleton _)
  intro hright
  let Mbase : L.Structure M := (baseGraphEmb (L := L)).reduct M
  have : (baseGraphEmb (L := L)).IsExpansionOn M := LHom.isExpansionOn_reduct _ _
  exact pcMem_disjoint T₀ T₁ hT₀ hT₁ hinv M ⟨⟨instM, ‹_›, hleft⟩, ⟨instM, ‹_›, hright⟩⟩

end FirstOrder.Language
