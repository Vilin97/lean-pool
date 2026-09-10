/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.LocalSkolemUniversal
import LeanPool.InfinitaryLogic.Methods.SchemaTermTruth
/-!
# The schema term model as a local-EM source

The integration point of the schema route with the (now generic) local-EM truth-lemma chain: the
schema term model satisfies the FULL arbitrary-stage Skolem-universality mixin
`LocalSkolemUniversalForColim` — no weakening to successor stages is needed.

The subtle point is a raw-stage membership `⟨n, .all ψ⟩ ∈ Γlocal s₀ k`: the body `ψ` itself need
not lie in `Γlocal s₀ k` (stage `0` is not subformula closed), so the restricted truth lemma
cannot be applied to it directly. The route is `liftNegBody_mem_Γlocal_succ`: the lifted negated
body `(ψ.not).mapLanguage (LlocalHom s₀ k)` IS controlled one stage up. Truth of `ψ` at the
stage-`k` Skolem value (the class of `locSkWitnessTerm`) makes the lifted negated body false in
the quotient; completeness pins its negation in the completion; and if the universal sentence
were negative, one two-sentence Marker body would realize both signs — under the body's
interpretation, `locSkWitness_universal_constInterp_nat` turns the first fact into the universal,
a contradiction. The universal sentence is therefore positive, and the truth lemma reads it back
into the quotient.
-/

namespace FirstOrder.Language

open Cardinal

variable {s₀ : LocalStage} {M : Type} [s₀.Lang.Structure M]
  [Nonempty M] [LinearOrder M] [WellFoundedLT M]

omit [s₀.Lang.Structure M] [Nonempty M] in
private theorem schemaCompletionTheory_not_mem_iff_sentence
    [(localColim s₀).Structure M]
    (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M)
    (τ : ((localColim s₀)[[ℕ]])[[ℕ]].Sentenceω)
    (hτ : HasFiniteConstSupport (L'' := localColim s₀) τ)
    (hτu : (⟨τ, hτ⟩ : FSentence (L'' := localColim s₀) (J := ℕ)) ∈
      schemaFSentenceUniverse s₀) :
    τ.not ∈ schemaCompletionTheory (schemaEnumeration s₀) hM ↔
      τ ∉ schemaCompletionTheory (schemaEnumeration s₀) hM :=
  schemaCompletionTheory_not_mem_iff hM ⟨τ, hτ⟩ hτu

/-- **The schema term model satisfies the Skolem-universality mixin** — the full arbitrary-stage
form. This is what plugs the schema term model into the generic local-EM truth lemma
(`truthLemmaStage_of_skolemUniversal`) and the cross-source acceptance. -/
theorem schemaTerm_localSkolemUniversalForColim
    (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M) :
    letI : (localColim s₀).Structure M := localColimStructure s₀
    letI : (localColim s₀)[[ℕ]].Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
      schemaTermStructure hM
    letI : (localColim s₀).Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
      (lhomWithConstants (localColim s₀) ℕ).reduct _
    LocalSkolemUniversalForColim s₀ (M := SchemaTermCarrier (s₀ := s₀) (M := M) hM) := by
  let : (localColim s₀).Structure M := localColimStructure s₀
  let : (localColim s₀)[[ℕ]].Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
    schemaTermStructure hM
  let : (localColim s₀).Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
    (lhomWithConstants (localColim s₀) ℕ).reduct _
  have : (lhomWithConstants (localColim s₀) ℕ).IsExpansionOn
      (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
    LHom.isExpansionOn_reduct _ _
  refine ⟨?_⟩
  intro k n ψ h xs hψw
  classical
  let ts : Fin n → (localColim s₀)[[ℕ]].Term Empty := fun i => Quotient.out (xs i)
  have hxs : (fun i => SchemaTermCarrier.mk hM (ts i)) = xs := by
    funext i
    exact Quotient.out_eq (xs i)
  have hwval : Structure.funMap
        ((LlocalInclusion s₀ (k + 1)).onFunction
          (Sum.inr (skolemNeedSymbol h) : (Llocal s₀ (k + 1)).Functions n)) xs
      = SchemaTermCarrier.mk hM (locSkWitnessTerm s₀ ℕ h ts) := by
    rw [← hxs]
    change @Structure.funMap ((localColim s₀)[[ℕ]])
        (SchemaTermCarrier (s₀ := s₀) (M := M) hM) (schemaTermStructure hM) n
        ((lhomWithConstants (localColim s₀) ℕ).onFunction
          ((LlocalInclusion s₀ (k + 1)).onFunction
            (Sum.inr (skolemNeedSymbol h) : (Llocal s₀ (k + 1)).Functions n)))
        (fun i => SchemaTermCarrier.mk hM (ts i)) = _
    rw [schemaTerm_funMap_mk hM]
    rfl
  have hsnoc : Fin.snoc xs
        (Structure.funMap
          ((LlocalInclusion s₀ (k + 1)).onFunction
            (Sum.inr (skolemNeedSymbol h) : (Llocal s₀ (k + 1)).Functions n)) xs)
      = fun i => SchemaTermCarrier.mk hM
          ((Fin.snoc ts (locSkWitnessTerm s₀ ℕ h ts) :
            Fin (n + 1) → (localColim s₀)[[ℕ]].Term Empty) i) := by
    rw [hwval, ← hxs]
    exact (Fin.comp_snoc (SchemaTermCarrier.mk hM) ts (locSkWitnessTerm s₀ ℕ h ts)).symm
  rw [hsnoc] at hψw
  let negBody : (Llocal s₀ (k + 1)).BoundedFormulaω Empty (n + 1) :=
    (ψ.not).mapLanguage (LlocalHom s₀ k)
  let args : Fin (n + 1) → (localColim s₀)[[ℕ]].Term Empty :=
    Fin.snoc ts (locSkWitnessTerm s₀ ℕ h ts)
  let negSentence :=
    schemaFormulaSentence (negBody.mapLanguage (LlocalInclusion s₀ (k + 1))) args
  let allSentence :=
    schemaFormulaSentence ((BoundedFormulaω.all ψ).mapLanguage (LlocalInclusion s₀ k)) ts
  have hnegmem : (⟨n + 1, negBody⟩ : Σ n, (Llocal s₀ (k + 1)).BoundedFormulaω Empty n)
      ∈ Γlocal s₀ (k + 1) := liftNegBody_mem_Γlocal_succ s₀ h
  have hneg_not_mem : negSentence ∉ schemaCompletionTheory (schemaEnumeration s₀) hM := by
    intro hnegT
    change schemaFormulaSentence (negBody.mapLanguage (LlocalInclusion s₀ (k + 1))) args
      ∈ schemaCompletionTheory (schemaEnumeration s₀) hM at hnegT
    have hnegReal := (schemaTruthLemmaStage hM k negBody hnegmem args).mpr hnegT
    have hnegBase : (negBody.mapLanguage (LlocalInclusion s₀ (k + 1))).Realize
        (Empty.elim : Empty → SchemaTermCarrier (s₀ := s₀) (M := M) hM)
        (fun i => SchemaTermCarrier.mk hM (args i)) :=
      (BoundedFormulaω.realize_mapLanguage (lhomWithConstants (localColim s₀) ℕ)
        (negBody.mapLanguage (LlocalInclusion s₀ (k + 1)))
        (Empty.elim : Empty → SchemaTermCarrier (s₀ := s₀) (M := M) hM)
        (fun i => SchemaTermCarrier.mk hM (args i))).mp hnegReal
    change (((ψ.not).mapLanguage (LlocalHom s₀ k)).mapLanguage
        (LlocalInclusion s₀ (k + 1))).Realize _ _ at hnegBase
    rw [mapLanguage_LlocalInclusion_lift, BoundedFormulaω.mapLanguage_not,
      BoundedFormulaω.realize_not] at hnegBase
    exact hnegBase hψw
  have hnegSupport : HasFiniteConstSupport (L'' := localColim s₀) negSentence :=
    hasFiniteConstSupport_mapLanguage_templateSentence _ _
  have hnegUniverse :
      (⟨negSentence, hnegSupport⟩ : FSentence (L'' := localColim s₀) (J := ℕ)) ∈
        schemaFSentenceUniverse s₀ := by
    simpa only [negSentence] using schemaFormulaSentence_mem_universe
      (toLocalColimFormula_mem_ΓlocalColim s₀ hnegmem) args
  have hneg_not_T : negSentence.not ∈ schemaCompletionTheory (schemaEnumeration s₀) hM :=
    (schemaCompletionTheory_not_mem_iff_sentence hM negSentence hnegSupport hnegUniverse).mpr
      hneg_not_mem
  have hAllT : allSentence ∈ schemaCompletionTheory (schemaEnumeration s₀) hM := by
    rcases (schemaCompletionTheorySpec hM).complete_on_universe _
      (schemaFormulaSentence_mem_universe
        (toLocalColimFormula_mem_ΓlocalColim s₀ h) ts) with hpos | hneg
    · exact hpos
    · exfalso
      obtain ⟨σ, w', hbody⟩ := exists_body_of_subset hM
        {negSentence.not, allSentence.not}
        (fun τ hτ => by
          rw [Finset.mem_insert, Finset.mem_singleton] at hτ
          rcases hτ with rfl | rfl
          · exact hneg_not_T
          · exact hneg)
      have h1 := hbody _ (Finset.mem_insert_self _ _)
      have h2 := hbody _
        (by rw [Finset.mem_insert]
            exact Or.inr (Finset.mem_singleton_self _))
      rw [realizeWith_not, realize_schemaFormulaSentence_iff] at h1 h2
      change ¬ (((ψ.not).mapLanguage (LlocalHom s₀ k)).mapLanguage
        (LlocalInclusion s₀ (k + 1))).Realize _ _ at h1
      rw [mapLanguage_LlocalInclusion_lift, BoundedFormulaω.mapLanguage_not,
        BoundedFormulaω.realize_not] at h1
      let : (constantsOn ℕ).Structure M := constantsOn.structure σ
      have hψσ : (ψ.mapLanguage (LlocalInclusion s₀ k)).Realize (Empty.elim : Empty → M)
          (fun i => (args i).realize Empty.elim) := Classical.not_not.mp h1
      refine h2 ?_
      intro x
      refine locSkWitness_universal_constInterp_nat s₀ σ h ts ?_ x
      rw [show (Fin.snoc (fun i => (ts i).realize Empty.elim)
            ((locSkWitnessTerm s₀ ℕ h ts).realize Empty.elim) : Fin (n + 1) → M)
          = fun i => (args i).realize Empty.elim from
        (Fin.comp_snoc
          (fun t : (localColim s₀)[[ℕ]].Term Empty => t.realize (Empty.elim : Empty → M))
          ts (locSkWitnessTerm s₀ ℕ h ts)).symm]
      exact hψσ
  have hall := (schemaTruthLemmaStage_of_mem hM k (BoundedFormulaω.all ψ) h ts).mpr hAllT
  have hallBase : ((BoundedFormulaω.all ψ).mapLanguage (LlocalInclusion s₀ k)).Realize
      (Empty.elim : Empty → SchemaTermCarrier (s₀ := s₀) (M := M) hM)
      (fun i => SchemaTermCarrier.mk hM (ts i)) :=
    (BoundedFormulaω.realize_mapLanguage (lhomWithConstants (localColim s₀) ℕ)
      ((BoundedFormulaω.all ψ).mapLanguage (LlocalInclusion s₀ k))
      (Empty.elim : Empty → SchemaTermCarrier (s₀ := s₀) (M := M) hM)
      (fun i => SchemaTermCarrier.mk hM (ts i))).mp hall
  rw [show ((BoundedFormulaω.all ψ).mapLanguage (LlocalInclusion s₀ k))
      = BoundedFormulaω.all (ψ.mapLanguage (LlocalInclusion s₀ k)) from rfl,
    BoundedFormulaω.realize_all] at hallBase
  intro x
  have hx := hallBase x
  rw [hxs] at hx
  exact hx

/-! ## The arbitrary-order local-EM context over the schema term model

Section-9 scaffolding: for ANY target linear order `J`, the schema term model carries a
`LocalEMContext` whose sequence is `schemaSeq`, whose family is `ΓEMlocal`, and whose
Ω-completeness is exactly the discharged `TailTemplateOmegaWitnessed` — plus the seed-sentence
realization the Morley-seed agreement consumes. -/

/-- **The schema local-EM context** over an arbitrary target order `J`: sequence `schemaSeq`,
family `ΓEMlocal`, tail indiscernibility from the full (cutoff-`0`) indiscernibility, atoms by
the `ΓEMlocal` dischargers. -/
noncomputable def schemaTermLocalEMContext
    (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M) (J : Type) [LinearOrder J] :
    letI : (localColim s₀).Structure M := localColimStructure s₀
    letI : (localColim s₀)[[ℕ]].Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
      schemaTermStructure hM
    letI : (localColim s₀).Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
      (lhomWithConstants (localColim s₀) ℕ).reduct _
    LocalEMContext (localColim s₀) J (M := SchemaTermCarrier (s₀ := s₀) (M := M) hM) := by
  letI : (localColim s₀).Structure M := localColimStructure s₀
  letI : (localColim s₀)[[ℕ]].Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
    schemaTermStructure hM
  letI : (localColim s₀).Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
    (lhomWithConstants (localColim s₀) ℕ).reduct _
  exact {
    a := schemaSeq hM
    Γ := ΓEMlocal s₀
    hind := IsLomega1omegaIndiscernibleOn.isLomega1omegaIndiscernibleOnTail
      (schemaSeq_indiscernibleOn (s₀ := s₀) (M := M) hM)
    atom_mem := locDeEqAtom_mem_ΓEMlocal J s₀
    rel_mem := locDeRelAtom_mem_ΓEMlocal J s₀
  }

/-- **The schema context is Ω-complete** — the discharged `TailTemplateOmegaWitnessed`
(the completion's pinned `iSup`/negative-`iInf` witnesses) converted through the Layer-7a
bridge. -/
theorem schemaTermLocalEMContext_omegaCompleteForColim
    (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M) (J : Type) [LinearOrder J] :
    letI : (localColim s₀).Structure M := localColimStructure s₀
    letI : (localColim s₀)[[ℕ]].Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
      schemaTermStructure hM
    letI : (localColim s₀).Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
      (lhomWithConstants (localColim s₀) ℕ).reduct _
    LocalEMContext.OmegaCompleteForColim s₀ J
      (schemaTermLocalEMContext (s₀ := s₀) (M := M) hM J) := by
  let : (localColim s₀).Structure M := localColimStructure s₀
  let : (localColim s₀)[[ℕ]].Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
    schemaTermStructure hM
  let : (localColim s₀).Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
    (lhomWithConstants (localColim s₀) ℕ).reduct _
  exact (schemaSeq_tailTemplateOmegaWitnessed (s₀ := s₀) (M := M) hM)
    |>.omegaCompleteForColim (schemaTermLocalEMContext (s₀ := s₀) (M := M) hM J).hind
      (schemaTermLocalEMContext (s₀ := s₀) (M := M) hM J) rfl

/-- **Seed-sentence realization**: a stage-`0` family sentence true in the source `M` is realized
by the schema term model (in its seed-language reduct). The route: validity of its lifted
template under every body interpretation forces the positive sign; the sequence-realization
bridge reads it into the quotient; the seed reduct peels off `LlocalInclusion`. -/
theorem schemaTerm_realizes_stage0_sentence
    (hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M)
    (φ : s₀.Lang.Sentenceω)
    (hmem : (⟨0, φ⟩ : Σ n, (Llocal s₀ 0).BoundedFormulaω Empty n) ∈ Γlocal s₀ 0)
    (hreal : letI : (localColim s₀).Structure M := localColimStructure s₀
      Sentenceω.Realize φ M) :
    letI : (localColim s₀).Structure M := localColimStructure s₀
    letI : (localColim s₀)[[ℕ]].Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
      schemaTermStructure hM
    letI : (localColim s₀).Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
      (lhomWithConstants (localColim s₀) ℕ).reduct _
    letI : s₀.Lang.Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
      (LlocalInclusion s₀ 0).reduct _
    Sentenceω.Realize φ (SchemaTermCarrier (s₀ := s₀) (M := M) hM) := by
  let : (localColim s₀).Structure M := localColimStructure s₀
  let : (localColim s₀)[[ℕ]].Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
    schemaTermStructure hM
  let : (localColim s₀).Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
    (lhomWithConstants (localColim s₀) ℕ).reduct _
  let : s₀.Lang.Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
    (LlocalInclusion s₀ 0).reduct _
  let : (Llocal s₀ 0).Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
    (inferInstance : s₀.Lang.Structure (SchemaTermCarrier (s₀ := s₀) (M := M) hM))
  have : (LlocalInclusion s₀ 0).IsExpansionOn (SchemaTermCarrier (s₀ := s₀) (M := M) hM) :=
    LHom.isExpansionOn_reduct _ _
  let ψ : (localColim s₀).Sentenceω := φ.mapLanguage (LlocalInclusion s₀ 0)
  have hψ : (⟨0, ψ⟩ : Σ n, (localColim s₀).BoundedFormulaω Empty n) ∈ ΓEMlocal s₀ :=
    ΓlocalColim_subset_ΓEMlocal s₀ (toLocalColimFormula_mem_ΓlocalColim s₀ (k := 0) hmem)
  have hT : schemaLift ψ (stdTuple 0) ∈ schemaCompletionTheory (schemaEnumeration s₀) hM := by
    apply schemaLift_mem_of_valid hM hψ (stdTuple 0)
    intro σ w
    rw [schemaLift, realizeWith_templateSentence]
    have hv := (realize_map_LlocalInclusion s₀ 0 φ Empty.elim Fin.elim0).mpr hreal
    change BoundedFormulaω.Realize ψ Empty.elim (fun i => σ (stdTuple 0 i))
    change BoundedFormulaω.Realize ψ Empty.elim Fin.elim0 at hv
    convert hv using 1
  have hcolim : BoundedFormulaω.Realize ψ
      (Empty.elim : Empty → SchemaTermCarrier (s₀ := s₀) (M := M) hM)
      (fun i => schemaSeq (s₀ := s₀) (M := M) hM (stdTuple 0 i)) :=
    (schemaSeq_realize_iff_schemaLift_mem (s₀ := s₀) (M := M) hM ψ hψ (stdTuple 0)).mpr hT
  have hcolim' : (φ.mapLanguage (LlocalInclusion s₀ 0)).Realize
      (Empty.elim : Empty → SchemaTermCarrier (s₀ := s₀) (M := M) hM)
      (Fin.elim0 : Fin 0 → SchemaTermCarrier (s₀ := s₀) (M := M) hM) := by
    change BoundedFormulaω.Realize ψ Empty.elim Fin.elim0
    convert hcolim using 1
  exact (BoundedFormulaω.realize_mapLanguage (LlocalInclusion s₀ 0) φ
    Empty.elim Fin.elim0).mp hcolim'

/-! ## The Morley-seed tail-template model (the section-9 assembly)

The schema route's endpoint: for a sentence `φ` true in a source of size `≥ ℶ_{ω₁}` and ANY
target linear order `J`, the Morley-seed tail-template theory of any pairwise-distinct source
sequence has a model — the schema term model's quotient, through the cross-source acceptance.
No tail indiscernibility of the input sequence is consumed: the seed's template values are
absolute (`morleySeed_template_agreement_cross`), so the input sequence only contributes its
pairwise distinctness. This discharges the honest residual
`MorleySeedTailTemplateRealizable` (the source facts it carries are exactly these). -/

/-- **The Morley-seed tail-template theory has a model over every target order** — assembled
from: a well-ordering of the source (`exists_wellFoundedLT`), the schema completion over
`LocalStage.ofSeq L' (morleySeed φ)`, the schema context and its Ω-completeness, the seed
realization + pairwise distinctness feeding the cross-model seed agreement, and the cross-source
acceptance with the schema term model's Skolem-universality mixin. -/
theorem morleySeed_tailTemplate_model_of_schemaSource {L' : Language.{0, 0}}
    [Countable (Σ n, L'.Functions n)] [Countable (Σ n, L'.Relations n)]
    (φ : L'.Sentenceω) (M : Type) [L'.Structure M] (a : ℕ → M) (J : Type) [LinearOrder J]
    (hSize : Cardinal.mk M ≥ Cardinal.beth (Ordinal.omega 1))
    (hφ : Sentenceω.Realize φ M)
    (ha : ∀ i j : ℕ, i ≠ j → a i ≠ a j) :
    ∃ (N : Type) (_ : L'[[J]].Structure N),
      Theoryω.Model
        ((tailTemplateOfSeq a : Lomega1omegaTemplate L').templateTheoryOfSeq
          (morleySeed φ) J) N := by
  obtain ⟨instLO, instWF⟩ := exists_wellFoundedLT M
  let : LinearOrder M := instLO
  have : WellFoundedLT M := instWF
  have : Nonempty M := Cardinal.mk_ne_zero_iff.mp
    (((lt_of_lt_of_le Cardinal.aleph0_pos (Cardinal.aleph0_le_beth _)).trans_le hSize).ne')
  have hM : Cardinal.beth (Ordinal.omega 1) ≤ Cardinal.mk M := hSize
  let : (localColim (LocalStage.ofSeq L' (morleySeed φ))).Structure M :=
    localColimStructure (LocalStage.ofSeq L' (morleySeed φ))
  let : (localColim (LocalStage.ofSeq L' (morleySeed φ)))[[ℕ]].Structure
      (SchemaTermCarrier (s₀ := LocalStage.ofSeq L' (morleySeed φ)) (M := M) hM) :=
    schemaTermStructure hM
  let : (localColim (LocalStage.ofSeq L' (morleySeed φ))).Structure
      (SchemaTermCarrier (s₀ := LocalStage.ofSeq L' (morleySeed φ)) (M := M) hM) :=
    (lhomWithConstants (localColim (LocalStage.ofSeq L' (morleySeed φ))) ℕ).reduct _
  let : L'.Structure
      (SchemaTermCarrier (s₀ := LocalStage.ofSeq L' (morleySeed φ)) (M := M) hM) :=
    (LlocalInclusion (LocalStage.ofSeq L' (morleySeed φ)) 0).reduct _
  have hmem : (⟨0, φ⟩ : Σ n,
      (Llocal (LocalStage.ofSeq L' (morleySeed φ)) 0).BoundedFormulaω Empty n)
      ∈ Γlocal (LocalStage.ofSeq L' (morleySeed φ)) 0 := ⟨0, rfl⟩
  have hφN : Sentenceω.Realize φ
      (SchemaTermCarrier (s₀ := LocalStage.ofSeq L' (morleySeed φ)) (M := M) hM) :=
    schemaTerm_realizes_stage0_sentence (s₀ := LocalStage.ofSeq L' (morleySeed φ)) (M := M)
      hM φ hmem hφ
  have hb : ∀ i j : ℕ, i ≠ j →
      schemaSeq (s₀ := LocalStage.ofSeq L' (morleySeed φ)) (M := M) hM i ≠
        schemaSeq (s₀ := LocalStage.ofSeq L' (morleySeed φ)) (M := M) hM j :=
    fun _ _ hij => schemaSeq_pairwise_ne hM hij
  exact tailTemplateRealizable_of_localEMContext_cross (morleySeed φ) a
    (SchemaTermCarrier (s₀ := LocalStage.ofSeq L' (morleySeed φ)) (M := M) hM)
    (schemaTerm_localSkolemUniversalForColim hM) J
    (schemaTermLocalEMContext (s₀ := LocalStage.ofSeq L' (morleySeed φ)) (M := M) hM J)
    subset_rfl
    (schemaTermLocalEMContext_omegaCompleteForColim
      (s₀ := LocalStage.ofSeq L' (morleySeed φ)) (M := M) hM J)
    (morleySeed_template_agreement_cross φ hφ hφN ha hb)

end FirstOrder.Language
