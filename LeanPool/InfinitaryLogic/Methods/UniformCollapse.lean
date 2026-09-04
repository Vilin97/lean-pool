/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.GeneratedSublanguage
import LeanPool.InfinitaryLogic.Methods.LocalEMSmallModel
import LeanPool.InfinitaryLogic.ModelTheory.Hanf
import LeanPool.InfinitaryLogic.ModelTheory.InfinitaryTypes
/-!
# The uniform collapsing language (issue #11 unit 7b)

The arbitrary-language wrapper for the small-model theorem cannot expand a countable-language
model back to `L` with arbitrary interpretations — smallness does not ascend through arbitrary
expansions. The clean fix is a COLLAPSING LANGUAGE HOM: `uniformLanguage φ` is the two-sorted
generated sublanguage of `φ` plus one dummy function and one dummy relation at every arity, and
`uniformCollapse φ : L →ᴸ uniformLanguage φ` sends `φ`'s symbols to their genuine sublanguage
copies and every omitted symbol to the dummy. The final full-language structure is then
LITERALLY a reduct along `uniformCollapse φ`, so semantics for every full-language formula are
supplied generically (`realize_mapLanguage`) and smallness descends by
`Lomega1omegaSmall.of_expansion`. This file provides:

* the language, the hom, and countability of the target's symbols;
* the support-aware syntactic identity `mapLanguage_uniformCollapse_eq` — on formulas whose
  symbols lie in `φ`'s, the collapse agrees with sublanguage restriction followed by `sumInl`;
* the source-side semantics `hasArbLargeModels_mapLanguage_uniformCollapse`: models of `φ`
  (requested at size `≥ max μ ℵ₀`, so nonempty and the dummies are interpretable) become models
  of the collapsed sentence.
-/

namespace FirstOrder

namespace Language

variable {L : Language.{0, 0}}

/-- The dummy language: one function and one relation symbol at every arity. -/
def dummyLang : Language.{0, 0} :=
  ⟨fun _ => Unit, fun _ => Unit⟩

/-- The uniform countable target: `φ`'s generated sublanguage plus the dummies. -/
@[reducible] def uniformLanguage (φ : L.Sentenceω) : Language.{0, 0} :=
  (symbSublang (L := L) φ.functionsIn φ.relationsIn).sum dummyLang

open Classical in
/-- **The collapsing hom**: `φ`'s symbols to their sublanguage copies, every omitted function
and relation to the dummy of its arity. -/
noncomputable def uniformCollapse (φ : L.Sentenceω) : L →ᴸ uniformLanguage φ where
  onFunction {n} f :=
    if h : (⟨n, f⟩ : Σ n, L.Functions n) ∈ BoundedFormulaω.functionsIn φ then
      Sum.inl ⟨f, h⟩
    else Sum.inr ()
  onRelation {n} R :=
    if h : (⟨n, R⟩ : Σ n, L.Relations n) ∈ BoundedFormulaω.relationsIn φ then
      Sum.inl ⟨R, h⟩
    else Sum.inr ()

theorem countable_sigma_functions_uniformLanguage (φ : L.Sentenceω) :
    Countable (Σ n, (uniformLanguage φ).Functions n) := by
  have h1 : Countable (Σ n, (symbSublang (L := L) φ.functionsIn φ.relationsIn).Functions n) :=
    symbSublang_fun_countable (BoundedFormulaω.functionsIn_countable φ) _
  have h2 : Countable (Σ n, dummyLang.Functions n) :=
    inferInstanceAs (Countable (Σ _ : ℕ, Unit))
  exact Countable.of_equiv _ (Equiv.sigmaSumDistrib _ _).symm

theorem countable_sigma_relations_uniformLanguage (φ : L.Sentenceω) :
    Countable (Σ n, (uniformLanguage φ).Relations n) := by
  have h1 : Countable (Σ n, (symbSublang (L := L) φ.functionsIn φ.relationsIn).Relations n) :=
    symbSublang_rel_countable _ (BoundedFormulaω.relationsIn_countable φ)
  have h2 : Countable (Σ n, dummyLang.Relations n) :=
    inferInstanceAs (Countable (Σ _ : ℕ, Unit))
  exact Countable.of_equiv _ (Equiv.sigmaSumDistrib _ _).symm

/-- On terms supported in `φ`'s function symbols, the collapse agrees with sublanguage
restriction followed by `sumInl`. -/
theorem Term.onTerm_uniformCollapse_eq {φ : L.Sentenceω} {α : Type} :
    ∀ (t : L.Term α) (hF : t.functionsIn ⊆ BoundedFormulaω.functionsIn φ),
      (uniformCollapse φ).onTerm t
        = (LHom.sumInl :
              symbSublang (L := L) φ.functionsIn φ.relationsIn →ᴸ uniformLanguage φ).onTerm
            (t.restrictSymbols (BoundedFormulaω.relationsIn φ) hF)
  | .var x, _ => rfl
  | .func f ts, h => by
    show Term.func ((uniformCollapse φ).onFunction f)
        (fun i => (uniformCollapse φ).onTerm (ts i)) = _
    rw [show (uniformCollapse φ).onFunction f
        = Sum.inl ⟨f, h (Set.mem_insert _ _)⟩ from dite_eq_left (h (Set.mem_insert _ _))]
    exact congrArg _ (funext fun i => Term.onTerm_uniformCollapse_eq (ts i) _)

/-- **The support-aware collapse identity**: on formulas whose symbols lie in `φ`'s, the
collapse is sublanguage restriction followed by `sumInl`. -/
theorem BoundedFormulaω.mapLanguage_uniformCollapse_eq {φ : L.Sentenceω} {α : Type} :
    ∀ {n : ℕ} (ψ : L.BoundedFormulaω α n)
      (hF : ψ.functionsIn ⊆ BoundedFormulaω.functionsIn φ)
      (hR : ψ.relationsIn ⊆ BoundedFormulaω.relationsIn φ),
      ψ.mapLanguage (uniformCollapse φ)
        = ((ψ.restrictSymbols hF hR).mapLanguage (LHom.sumInl :
            symbSublang (L := L) φ.functionsIn φ.relationsIn →ᴸ uniformLanguage φ) :
              (uniformLanguage φ).BoundedFormulaω α n)
  | _, .falsum, _, _ => rfl
  | _, .equal t u, hF, _ => by
    show BoundedFormulaω.equal ((uniformCollapse φ).onTerm t) ((uniformCollapse φ).onTerm u) = _
    rw [Term.onTerm_uniformCollapse_eq t (fun _ hx => hF (Set.mem_union_left _ hx)),
      Term.onTerm_uniformCollapse_eq u (fun _ hx => hF (Set.mem_union_right _ hx))]
    rfl
  | _, .rel Rl ts, hF, hR => by
    show BoundedFormulaω.rel ((uniformCollapse φ).onRelation Rl)
        (fun i => (uniformCollapse φ).onTerm (ts i)) = _
    rw [show (uniformCollapse φ).onRelation Rl
        = Sum.inl ⟨Rl, hR rfl⟩ from dite_eq_left (hR rfl)]
    refine congrArg _ (funext fun i => ?_)
    exact Term.onTerm_uniformCollapse_eq (ts i)
      (fun _ hx => hF (Set.mem_iUnion.mpr ⟨i, hx⟩))
  | _, .imp ψ₁ ψ₂, hF, hR => by
    show BoundedFormulaω.imp (ψ₁.mapLanguage (uniformCollapse φ))
        (ψ₂.mapLanguage (uniformCollapse φ)) = _
    rw [BoundedFormulaω.mapLanguage_uniformCollapse_eq ψ₁
        (fun _ hx => hF (Set.mem_union_left _ hx))
        (fun _ hx => hR (Set.mem_union_left _ hx)),
      BoundedFormulaω.mapLanguage_uniformCollapse_eq ψ₂
        (fun _ hx => hF (Set.mem_union_right _ hx))
        (fun _ hx => hR (Set.mem_union_right _ hx))]
    rfl
  | _, .all ψ, hF, hR => by
    show BoundedFormulaω.all (ψ.mapLanguage (uniformCollapse φ)) = _
    rw [BoundedFormulaω.mapLanguage_uniformCollapse_eq ψ hF hR]
    rfl
  | _, .iSup ψs, hF, hR => by
    show BoundedFormulaω.iSup (fun i => (ψs i).mapLanguage (uniformCollapse φ)) = _
    refine congrArg _ (funext fun i => ?_)
    exact BoundedFormulaω.mapLanguage_uniformCollapse_eq (ψs i)
      (fun _ hx => hF (Set.mem_iUnion.mpr ⟨i, hx⟩))
      (fun _ hx => hR (Set.mem_iUnion.mpr ⟨i, hx⟩))
  | _, .iInf ψs, hF, hR => by
    show BoundedFormulaω.iInf (fun i => (ψs i).mapLanguage (uniformCollapse φ)) = _
    refine congrArg _ (funext fun i => ?_)
    exact BoundedFormulaω.mapLanguage_uniformCollapse_eq (ψs i)
      (fun _ hx => hF (Set.mem_iUnion.mpr ⟨i, hx⟩))
      (fun _ hx => hR (Set.mem_iUnion.mpr ⟨i, hx⟩))

/-- **Source-side semantics**: a model of `φ` becomes a model of the collapsed sentence —
sublanguage symbols genuinely, dummy functions constantly (the model is nonempty by the size
request), dummy relations as `False`. So the collapsed sentence inherits arbitrarily large
models. -/
theorem hasArbLargeModels_mapLanguage_uniformCollapse {φ : L.Sentenceω}
    (hφarb : HasArbLargeModels φ) :
    HasArbLargeModels (φ.mapLanguage (uniformCollapse φ)) := by
  intro μ
  obtain ⟨M, instM, hφM, hMsize⟩ := hφarb (max μ Cardinal.aleph0)
  have : Nonempty M := Cardinal.mk_ne_zero_iff.mp
    ((lt_of_lt_of_le Cardinal.aleph0_pos (le_trans (le_max_right μ _) hMsize)).ne')
  let : (symbSublang (L := L) φ.functionsIn φ.relationsIn).Structure M :=
    (symbSublangIncl _ _).reduct M
  let : dummyLang.Structure M :=
    ⟨fun _ _ => Classical.arbitrary M, fun _ _ => False⟩
  have : (symbSublangIncl (L := L) φ.functionsIn φ.relationsIn).IsExpansionOn M :=
    LHom.isExpansionOn_reduct _ _
  refine ⟨M, inferInstance, ?_, le_trans (le_max_left μ _) hMsize⟩
  have h0 : Sentenceω.Realize
      (φ.restrictSymbols (subset_refl _) (subset_refl _) :
        (symbSublang (L := L) φ.functionsIn φ.relationsIn).Sentenceω) M := by
    have h := BoundedFormulaω.realize_mapLanguage
      (symbSublangIncl (L := L) φ.functionsIn φ.relationsIn)
      (φ.restrictSymbols (subset_refl _) (subset_refl _))
      (Empty.elim : Empty → M) Fin.elim0
    rw [BoundedFormulaω.mapLanguage_restrictSymbols] at h
    exact h.mp hφM
  show BoundedFormulaω.Realize (φ.mapLanguage (uniformCollapse φ)) Empty.elim Fin.elim0
  rw [BoundedFormulaω.mapLanguage_uniformCollapse_eq φ (subset_refl _) (subset_refl _)]
  exact (BoundedFormulaω.realize_mapLanguage LHom.sumInl _ Empty.elim Fin.elim0).mpr h0

/-- **The small-model theorem** (Marker, Theorem 11.2), over an ARBITRARY language: a sentence
with arbitrarily large models has, at every infinite `κ`, a model of size exactly `κ` realizing
only countably many complete `L_{ω₁ω}`-types. The final structure is literally the reduct of
the countable-language small model along `uniformCollapse φ`, so satisfaction is generic
(`realize_mapLanguage`) and smallness descends (`Lomega1omegaSmall.of_expansion`); the carrier
and hence its cardinality are unchanged. -/
theorem exists_small_model_of_hasArbLargeModels {φ : L.Sentenceω}
    (hφarb : HasArbLargeModels φ) {κ : Cardinal.{0}} (hκ : Cardinal.aleph0 ≤ κ) :
    ∃ (N : Type) (_ : L.Structure N),
      Sentenceω.Realize φ N ∧ Cardinal.mk N = κ ∧ Lomega1omegaSmall (L := L) N := by
  have := countable_sigma_functions_uniformLanguage φ
  have := countable_sigma_relations_uniformLanguage φ
  obtain ⟨N, instN, hφ'N, hNcard, hNsmall⟩ :=
    exists_small_model_of_hasArbLargeModels_countable_symbols
      (hasArbLargeModels_mapLanguage_uniformCollapse hφarb) hκ
  let : L.Structure N := (uniformCollapse φ).reduct N
  have : (uniformCollapse φ).IsExpansionOn N := LHom.isExpansionOn_reduct _ _
  refine ⟨N, inferInstance, ?_, hNcard,
    Lomega1omegaSmall.of_expansion (uniformCollapse φ) hNsmall⟩
  exact (BoundedFormulaω.realize_mapLanguage (uniformCollapse φ) φ
    (Empty.elim : Empty → N) Fin.elim0).mp hφ'N

end Language

end FirstOrder
