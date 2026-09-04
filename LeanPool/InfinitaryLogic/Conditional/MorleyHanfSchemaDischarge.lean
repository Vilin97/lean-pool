/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Conditional.MorleyHanfTransfer
import LeanPool.InfinitaryLogic.Methods.SchemaLocalEMSource
import LeanPool.InfinitaryLogic.Methods.GeneratedSublanguage
/-!
# The Morley–Hanf theorem, discharged

The honest residual `MorleySeedTailTemplateRealizable` — the sole non-formal input of the
realizability-only Morley–Hanf endpoint `morley_hanf_of_tail_realizable` — is PROVED by the
schema route (`morleySeed_tailTemplate_model_of_schemaSource`): the ω-stage Marker/Henkin
completion of the schema sentence universe, its quotient term model with the restricted truth
lemma, the fully indiscernible sequence `schemaSeq` with pinned `iSup`/negative-`iInf` witnesses,
and the cross-source acceptance through the Skolem-universality mixin. In fact the schema route
consumes strictly LESS than the residual offers: the input sequence's tail indiscernibility is
not used (seed template values are absolute).

`morley_hanf_countable_symbols` is the transparent countable-symbol intermediate. The definitive
endpoint **`morley_hanf`** carries NO symbol-countability hypotheses: the construction runs in
the simultaneous symbol-generated sublanguage of `φ` (`symbSublang φ.functionsIn φ.relationsIn`,
both sorts countable because a formula mentions countably many symbols), and the resulting model
is expanded back to `L'[[J]]` — missing functions act arbitrarily, missing relations as `False`,
constants pass through; the degenerate `IsEmpty J` case is served by the source model itself.
So: **`ℶ_{ω₁}` is a Hanf bound for every `L_{ω₁ω}` sentence, unconditionally.**
-/

namespace FirstOrder.Language

open Cardinal

/-- **The honest Morley–Hanf residual, countable-symbol form**: the tail-template theory of the
Morley seed is realizable over every target order — by the schema-route construction, which does
not even consume the sequence's tail indiscernibility. The transparent intermediate; the
sublanguage reduction below removes the countability. -/
private theorem morleySeedTailTemplateRealizable_of_countable_symbols {L' : Language.{0, 0}}
    [Countable (Σ n, L'.Functions n)] [Countable (Σ n, L'.Relations n)] :
    MorleySeedTailTemplateRealizable (L' := L') := by
  intro φ M _ a J _ hSize hφ ha _
  exact morleySeed_tailTemplate_model_of_schemaSource φ M a J hSize hφ ha

/-- **The Morley–Hanf theorem for countable-symbol languages**: `ℶ_{ω₁}` is a Hanf bound for
every `L_{ω₁ω}` sentence over a language with countably many function and relation symbols, by
seed-template realizability (the schema construction) alone — no extraction is consumed (an
injective sequence is already seed-indiscernible, `morleySeed_indiscernibleOn`). The transparent
intermediate to the assumption-free `morley_hanf` below. -/
private theorem morley_hanf_countable_symbols {L' : Language.{0, 0}}
    [Countable (Σ n, L'.Functions n)] [Countable (Σ n, L'.Relations n)]
    (φ : L'.Sentenceω) :
    IsHanfBound φ (Cardinal.beth (Ordinal.omega 1)) :=
  morley_hanf_of_seed_realizable morleySeedTailTemplateRealizable_of_countable_symbols φ

/-! ## Removing symbol countability: the two-sorted sublanguage reduction -/

open Classical in
/-- **Expansion of a two-sorted sublanguage `[[J]]`-structure to the full language**: generating
function symbols act as before, missing functions act arbitrarily (hence `[Nonempty N]`);
generating relation symbols act as before, missing relations are `False`; constants pass
through. -/
@[reducible] noncomputable def expandSymbStructure {L : Language.{0, 0}}
    (F : Set (Σ n, L.Functions n)) (R : Set (Σ n, L.Relations n)) (J : Type) {N : Type}
    [Nonempty N] [instN : (symbSublang (L := L) F R)[[J]].Structure N] :
    L[[J]].Structure N where
  funMap := fun {m} f xs =>
    match f with
    | Sum.inl f' =>
      if h : (⟨m, f'⟩ : Σ n, L.Functions n) ∈ F then
        Structure.funMap (L := (symbSublang (L := L) F R)[[J]])
          (Sum.inl (⟨f', h⟩ : (symbSublang (L := L) F R).Functions m)) xs
      else Classical.arbitrary N
    | Sum.inr c => Structure.funMap (L := (symbSublang (L := L) F R)[[J]]) (Sum.inr c) xs
  RelMap := fun {m} r xs =>
    match r with
    | Sum.inl r' =>
      if h : (⟨m, r'⟩ : Σ n, L.Relations n) ∈ R then
        Structure.RelMap (L := (symbSublang (L := L) F R)[[J]])
          (Sum.inl (⟨r', h⟩ : (symbSublang (L := L) F R).Relations m)) xs
      else False
    | Sum.inr c => Structure.RelMap (L := (symbSublang (L := L) F R)[[J]]) (Sum.inr c) xs

/-- **Template sentences transfer along the two-sorted expansion** — the `symbSublang` analogue
of `realize_templateSentence_expand`: skeleton constants agree definitionally, and both symbol
sorts peel off through the expansion property (`dif_pos` on the generating sets). -/
private theorem realize_templateSentence_expandSymb {L : Language.{0, 0}}
    {F : Set (Σ n, L.Functions n)} {R : Set (Σ n, L.Relations n)}
    (J : Type) [LinearOrder J] {N : Type} [Nonempty N]
    [instN : (symbSublang (L := L) F R)[[J]].Structure N]
    {n : ℕ} (ψ₀ : (symbSublang (L := L) F R).BoundedFormulaω Empty n) (t : Fin n ↪o J) :
    letI : L[[J]].Structure N := expandSymbStructure F R J
    (Sentenceω.Realize
        (Lomega1omegaTemplate.templateSentence (ψ₀.mapLanguage (symbSublangIncl F R)) t) N ↔
      Sentenceω.Realize (Lomega1omegaTemplate.templateSentence ψ₀ t) N) := by
  classical
  let instE : L[[J]].Structure N := expandSymbStructure F R J
  refine (realize_templateSentence_of_structure (L := L) (J := J) (N := N)
    (ψ₀.mapLanguage (symbSublangIncl F R)) t).trans
    (Iff.trans ?_ (realize_templateSentence_of_structure (L := symbSublang (L := L) F R)
      (J := J) (N := N) ψ₀ t).symm)
  let : L.Structure N := (L.lhomWithConstants J).reduct N
  let : (symbSublang (L := L) F R).Structure N :=
    ((symbSublang (L := L) F R).lhomWithConstants J).reduct N
  have : (symbSublangIncl F R).IsExpansionOn N := by
    constructor
    · intro m f xs
      show (if h : (⟨m, f.1⟩ : Σ n, L.Functions n) ∈ F then
          Structure.funMap (L := (symbSublang (L := L) F R)[[J]])
            (Sum.inl (⟨f.1, h⟩ : (symbSublang (L := L) F R).Functions m)) xs
        else Classical.arbitrary N) = _
      rw [dite_eq_left f.2]
      rfl
    · intro m r xs
      show (if h : (⟨m, r.1⟩ : Σ n, L.Relations n) ∈ R then
          Structure.RelMap (L := (symbSublang (L := L) F R)[[J]])
            (Sum.inl (⟨r.1, h⟩ : (symbSublang (L := L) F R).Relations m)) xs
        else False) = _
      rw [dite_eq_left r.2]
      rfl
  have htup : (fun i => (Term.func (Sum.inr (t i) : L[[J]].Functions 0)
        Fin.elim0 : L[[J]].Term Empty).realize (Empty.elim : Empty → N))
      = (fun i => (Term.func (Sum.inr (t i) : (symbSublang (L := L) F R)[[J]].Functions 0)
          Fin.elim0 : (symbSublang (L := L) F R)[[J]].Term Empty).realize
          (Empty.elim : Empty → N)) := by
    funext i
    show Structure.funMap (L := L[[J]]) (Sum.inr (t i) : L[[J]].Functions 0)
        (fun j => ((Fin.elim0 : Fin 0 → L[[J]].Term Empty) j).realize
          (Empty.elim : Empty → N))
      = Structure.funMap (L := (symbSublang (L := L) F R)[[J]])
        (Sum.inr (t i) : (symbSublang (L := L) F R)[[J]].Functions 0)
        (fun j => ((Fin.elim0 : Fin 0 → (symbSublang (L := L) F R)[[J]].Term Empty) j).realize
          (Empty.elim : Empty → N))
    rw [show (fun j => ((Fin.elim0 : Fin 0 → L[[J]].Term Empty) j).realize
        (Empty.elim : Empty → N)) = (Fin.elim0 : Fin 0 → N) from funext fun j => j.elim0,
      show (fun j => ((Fin.elim0 : Fin 0 → (symbSublang (L := L) F R)[[J]].Term Empty) j).realize
        (Empty.elim : Empty → N)) = (Fin.elim0 : Fin 0 → N) from funext fun j => j.elim0]
    rfl
  rw [htup]
  exact BoundedFormulaω.realize_mapLanguage (symbSublangIncl F R) ψ₀ (Empty.elim : Empty → N) _

/-- **The honest Morley–Hanf residual holds — no symbol-countability assumptions**: the schema
construction runs in the simultaneous symbol-generated sublanguage of `φ` (both sorts countable,
proved not assumed) at an injective `ℕ`-sequence of the source, and its model expands back to
`L'[[J]]`; the degenerate `IsEmpty J` case is served by the source model itself. -/
theorem morleySeedTailTemplateRealizable_holds {L' : Language.{0, 0}} :
    MorleySeedTailTemplateRealizable (L' := L') := by
  intro φ M instM a J instJ hSize hφreal hPair _hTail
  have : Infinite M := by
    rw [Cardinal.infinite_iff]
    exact le_trans (Cardinal.aleph0_le_beth _) hSize
  have : Nonempty M := ⟨(Infinite.natEmbedding M) 0⟩
  rcases isEmpty_or_nonempty J with hJe | hJne
  · exact morleySeed_theory_model_of_isEmptyJ φ a J hφreal
  have : Countable (Σ n, (symbSublang (L := L') φ.functionsIn φ.relationsIn).Functions n) :=
    symbSublang_fun_countable φ.functionsIn_countable _
  have : Countable (Σ l, (symbSublang (L := L') φ.functionsIn φ.relationsIn).Relations l) :=
    symbSublang_rel_countable _ φ.relationsIn_countable
  let : (symbSublang (L := L') φ.functionsIn φ.relationsIn).Structure M :=
    (symbSublangIncl φ.functionsIn φ.relationsIn).reduct M
  have : (symbSublangIncl (L := L') φ.functionsIn φ.relationsIn).IsExpansionOn M :=
    LHom.isExpansionOn_reduct _ _
  have hφ₀map : (φ.restrictSymbols (subset_refl _) (subset_refl _)).mapLanguage
      (symbSublangIncl φ.functionsIn φ.relationsIn) = φ :=
    BoundedFormulaω.mapLanguage_restrictSymbols φ (subset_refl _) (subset_refl _)
  have hφ₀real : Sentenceω.Realize (φ.restrictSymbols (subset_refl _) (subset_refl _) :
      (symbSublang (L := L') φ.functionsIn φ.relationsIn).Sentenceω) M := by
    have h := BoundedFormulaω.realize_mapLanguage
      (symbSublangIncl φ.functionsIn φ.relationsIn)
      (φ.restrictSymbols (subset_refl _) (subset_refl _)) (Empty.elim : Empty → M) Fin.elim0
    rw [hφ₀map] at h
    exact h.mp hφreal
  set a₀ : ℕ → M := fun n => (Infinite.natEmbedding M) n with ha₀
  have ha₀Pair : ∀ i j : ℕ, i ≠ j → a₀ i ≠ a₀ j :=
    fun i j hij h => hij ((Infinite.natEmbedding M).injective h)
  obtain ⟨N, instN, hmodel⟩ := morleySeed_tailTemplate_model_of_schemaSource
    (L' := symbSublang (L := L') φ.functionsIn φ.relationsIn)
    (φ.restrictSymbols (subset_refl _) (subset_refl _)) M a₀ J hSize hφ₀real ha₀Pair
  have hposφ : ∀ t : Fin 0 ↪o J, Sentenceω.Realize
      (Lomega1omegaTemplate.templateSentence
        (φ.restrictSymbols (subset_refl _) (subset_refl _)) t) N :=
    fun t => hmodel _ ⟨0, φ.restrictSymbols (subset_refl _) (subset_refl _), t, ⟨0, rfl⟩,
      Or.inl ⟨(tailTemplateOfSeq_truth_sentence_iff a₀ _).mpr hφ₀real, rfl⟩⟩
  have hposd : ∀ t : Fin 2 ↪o J, Sentenceω.Realize
      (Lomega1omegaTemplate.templateSentence
        (disEqFormula : (symbSublang (L := L') φ.functionsIn φ.relationsIn).BoundedFormulaω
          Empty 2) t) N :=
    fun t => hmodel _ ⟨2, disEqFormula, t, ⟨1, rfl⟩,
      Or.inl ⟨tailTemplateOfSeq_truth_disEq ha₀Pair, rfl⟩⟩
  have : Nonempty J := hJne
  have : Nonempty N := ⟨(Term.func
    (Sum.inr (Classical.arbitrary J) :
      (symbSublang (L := L') φ.functionsIn φ.relationsIn)[[J]].Functions 0)
    Fin.elim0 :
      (symbSublang (L := L') φ.functionsIn φ.relationsIn)[[J]].Term Empty).realize
    (Empty.elim : Empty → N)⟩
  let instE : L'[[J]].Structure N := expandSymbStructure φ.functionsIn φ.relationsIn J
  refine ⟨N, instE, ?_⟩
  rintro σ ⟨n, ψ, t, ⟨k, hk⟩, hcase⟩
  match k, hk with
  | 0, hk =>
    cases hk
    rcases hcase with ⟨_, rfl⟩ | ⟨hnot, _⟩
    · have h := (realize_templateSentence_expandSymb (F := φ.functionsIn)
        (R := φ.relationsIn) J (φ.restrictSymbols (subset_refl _) (subset_refl _)) t).mpr
        (hposφ t)
      rwa [hφ₀map] at h
    · exact absurd ((tailTemplateOfSeq_truth_sentence_iff a φ).mpr hφreal) hnot
  | 1, hk =>
    cases hk
    rcases hcase with ⟨_, rfl⟩ | ⟨hnot, _⟩
    · have h := (realize_templateSentence_expandSymb (F := φ.functionsIn)
        (R := φ.relationsIn) J
        (disEqFormula : (symbSublang (L := L') φ.functionsIn φ.relationsIn).BoundedFormulaω
          Empty 2) t).mpr (hposd t)
      rwa [show ((disEqFormula :
          (symbSublang (L := L') φ.functionsIn φ.relationsIn).BoundedFormulaω
            Empty 2).mapLanguage (symbSublangIncl φ.functionsIn φ.relationsIn))
          = (disEqFormula : L'.BoundedFormulaω Empty 2) from rfl] at h
    · exact absurd (tailTemplateOfSeq_truth_disEq hPair) hnot
  | k + 2, hk =>
    cases hk
    rcases hcase with ⟨_, rfl⟩ | ⟨hnot, _⟩
    · have h := (realize_templateSentence_expandSymb (F := φ.functionsIn)
        (R := φ.relationsIn) J (φ.restrictSymbols (subset_refl _) (subset_refl _)) t).mpr
        (hposφ t)
      rwa [hφ₀map] at h
    · exact absurd ((tailTemplateOfSeq_truth_sentence_iff a φ).mpr hφreal) hnot

/-- **The Morley–Hanf theorem**: `ℶ_{ω₁}` is a Hanf bound for every `L_{ω₁ω}` sentence — over an
arbitrary language, with no countability or other side hypotheses. If an `L_{ω₁ω}` sentence has
a model of size at least `ℶ_{ω₁}`, it has models of arbitrarily large cardinality. -/
theorem morley_hanf {L' : Language.{0, 0}} (φ : L'.Sentenceω) :
    IsHanfBound φ (Cardinal.beth (Ordinal.omega 1)) :=
  morley_hanf_of_seed_realizable morleySeedTailTemplateRealizable_holds φ

end FirstOrder.Language
