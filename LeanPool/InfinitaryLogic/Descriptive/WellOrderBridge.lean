/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Descriptive.WellOrderClass
import LeanPool.InfinitaryLogic.ModelTheory.FragmentLowenheimSkolem
import LeanPool.InfinitaryLogic.Lomega1omega.InfiniteAxiom
/-!
# From coded well-orders to models: the defect bridge

A structure whose distinguished relation fails to be a well-order carries a **countable nonempty
seed** of witnesses; seeding a countable fragment-elementary substructure with it and transporting
that substructure to the carrier `ℕ` produces a *code* which is not a well-order.  Contrapositively,
if every code satisfying `φ` is a well-order then so is every model of `φ ⊓ infiniteAxiom`.

**Deliberately independent of López–Escobar.**  This file imports only the well-order class, the
fragment Löwenheim–Skolem machinery and the infiniteness axiom.  Two very different consumers need
the bridge and neither should have to drag in the other:

* `Descriptive/WellOrderNonBorel.lean` (#33) obtains its `φ` from López–Escobar applied to a
  hypothetically Borel `WO`;
* `Descriptive/AnalyticWellOrderBoundedness.lean` (#64) obtains its `φ` from the analytic-PC
  sandwich, where the reduct class is only *contained* in `WO`.

That second consumer is why `isWellOrder_of_realize_of_modelsOf_subset` is the primary form: a
`pcSentence`'s reduct class sits inside an invariant envelope and never equals a prescribed set.

## Main results

- `exists_countable_defect_seed`: a well-order failure has a countable nonempty witness set.
- `isWellOrder_of_realize_of_modelsOf_subset`: containment form of the bridge.
- `isWellOrder_of_realize`: the equality-form corollary.
-/

namespace FirstOrder.Language

open FirstOrder Structure Set

/-! ## The defect seed -/

section Defect

variable {M : Type} {r : M → M → Prop}

/-- A structure whose relation fails to be a well-order carries a **countable nonempty seed**
of witnesses: every subset containing the seed inherits the failure.  In this Mathlib a
well-order is trichotomy plus well-foundedness (transitivity is derived), so there are exactly
two cases: a two-element trichotomy failure, and the range of an infinite descending sequence. -/
theorem exists_countable_defect_seed (h : ¬ IsWellOrder M r) :
    ∃ X : Set M, X.Countable ∧ X.Nonempty ∧
      ∀ N : Set M, X ⊆ N → ¬ IsWellOrder ↥N fun x y : ↥N => r ↑x ↑y := by
  by_cases htri : Std.Trichotomous r
  · -- the relation must be ill-founded
    have hwf : ¬ IsWellFounded M r := fun hwf => h (@IsWellOrder.mk M r hwf htri)
    have hnwf : ¬ WellFounded r := fun hw => hwf ⟨hw⟩
    rw [wellFounded_iff_isEmpty_descending_chain, not_isEmpty_iff] at hnwf
    obtain ⟨f, hf⟩ := hnwf.some
    refine ⟨Set.range f, Set.countable_range f, ⟨f 0, 0, rfl⟩, fun N hXN hwo => ?_⟩
    exact (wellFounded_iff_isEmpty_descending_chain.mp hwo.toIsWellFounded.wf).false
      ⟨fun n => (⟨f n, hXN ⟨n, rfl⟩⟩ : ↥N), fun n => hf n⟩
  · -- trichotomy fails: a two-element seed
    have hex : ∃ a b : M, ¬ r a b ∧ ¬ r b a ∧ a ≠ b := by
      by_contra hc
      push Not at hc
      exact htri ⟨fun a b hab hba => hc a b hab hba⟩
    obtain ⟨a, b, hab, hba, hne⟩ := hex
    refine ⟨{a, b}, ((Set.finite_singleton b).insert a).countable,
      ⟨a, Set.mem_insert _ _⟩, fun N hXN hwo => ?_⟩
    have ha : a ∈ N := hXN (Set.mem_insert _ _)
    have hb : b ∈ N := hXN (Set.mem_insert_of_mem _ rfl)
    have := hwo
    exact hne (congrArg Subtype.val (Std.Trichotomous.trichotomous
      (r := fun x y : ↥N => r ↑x ↑y) ⟨a, ha⟩ ⟨b, hb⟩ hab hba))

end Defect

variable {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-! ## The bridge: coded definability forces every model to be well-ordered -/

omit [Countable (Σ l, L.Relations l)] in
/-- **The bridge** (#13's role in this argument), in containment form: if every *code* satisfying
`φ` is a well-order, then every model of `φ` **conjoined with the infiniteness axiom** interprets
the distinguished relation as a well-order.  A defect would survive into a countable
fragment-elementary substructure seeded with its witnesses, and that substructure — infinite by
the added conjunct — transports to a code of `ModelsOf φ` that is not a well-order.

Containment, not equality: the argument only ever pushes a *particular* code into
`wellOrderClass lt`, so nothing is lost, and this is the form the analytic-PC sandwich of #64
supplies — a `pcSentence` whose reduct class sits inside an invariant envelope, never exactly
equals a prescribed set.  `isWellOrder_of_realize` is the equality-form corollary. -/
private theorem isWellOrder_of_realize_of_modelsOf_subset (lt : L.Relations 2) {φ : L.Sentenceω}
    (hφ : ModelsOf φ ⊆ wellOrderClass lt) (M : Type) [instM : L.Structure M]
    (hM : Sentenceω.Realize (φ.and (infiniteAxiom L)) M) :
    IsWellOrder M fun x y : M => RelMap lt ![x, y] := by
  by_contra hwo
  obtain ⟨X, hXc, hXne, hXdefect⟩ := exists_countable_defect_seed hwo
  -- a countable fragment-elementary substructure containing the defect witnesses
  obtain ⟨N, hXN, hAe, hNc⟩ := exists_countable_aElementary_substructure (M := M)
    (Fragment.generatedSentence (φ.and (infiniteAxiom L))) hXc
    (Fragment.generatedSentence_countable _)
  obtain ⟨x₀, hx₀⟩ := hXne
  have : Nonempty ↥N := ⟨⟨x₀, hXN hx₀⟩⟩
  have hN : Sentenceω.Realize (φ.and (infiniteAxiom L)) ↥N :=
    (hAe.realize_sentence_iff (Fragment.mem_generatedSentence _)).mp hM
  obtain ⟨hNφ, hNinf⟩ := (BoundedFormulaω.realize_and _ _).mp hN
  -- re-ascribed at the sentence level: `SentenceInf.Realize` is a plain definition upstream, so
  -- `realize_infiniteAxiom`'s implicit arguments cannot be solved against the unfolded form
  have hNinfS : Sentenceω.Realize (infiniteAxiom L) ↥N := hNinf
  have : Infinite ↥N := realize_infiniteAxiom.mp hNinfS
  -- transport it to the carrier `ℕ`
  let e : ↥N ≃ ℕ := (nonempty_equiv_of_countable (α := ↥N) (β := ℕ)).some
  have hd : StructureSpaceOn.encodeViaEquiv e ∈ ModelsOf φ :=
    StructureSpaceOn.encodeViaEquiv_models e hNφ
  -- the ONLY use of the hypothesis: push this one code into the well-order class
  replace hd := hφ hd
  -- the code is a well-order, hence so is `N`
  have hrel : ∀ x y : ℕ, @Structure.RelMap L ℕ
      (StructureSpaceOn.encodeViaEquiv e).toStructure 2 lt ![x, y] ↔
        @Structure.RelMap L ↥N _ 2 lt ![e.symm x, e.symm y] := by
    intro x y
    rw [StructureSpaceOn.toStructure_encodeViaEquiv_eq, Equiv.inducedStructure_RelMap]
    rw [show (⇑e.symm ∘ ![x, y]) = ![e.symm x, e.symm y] from
      funext fun i => by fin_cases i <;> rfl]
  have hiso : (fun x y : ℕ => @Structure.RelMap L ℕ
      (StructureSpaceOn.encodeViaEquiv e).toStructure 2 lt ![x, y]) ≃r
        fun x y : ↥N => @Structure.RelMap L ↥N _ 2 lt ![x, y] :=
    ⟨e.symm, fun {a b} => (hrel a b).symm⟩
  have : IsWellOrder ℕ fun x y : ℕ => @Structure.RelMap L ℕ
      (StructureSpaceOn.encodeViaEquiv e).toStructure 2 lt ![x, y] := hd
  have hwoN : IsWellOrder ↥N fun x y : ↥N => @Structure.RelMap L ↥N _ 2 lt ![x, y] :=
    hiso.symm.toRelEmbedding.isWellOrder
  -- but the defect survived into `N`
  have hsub : ∀ x y : ↥N, (@Structure.RelMap L ↥N _ 2 lt ![x, y] ↔
      @Structure.RelMap L M instM 2 lt ![(x : M), (y : M)]) := by
    intro x y
    have h := N.subtype.map_rel lt ![x, y]
    rw [show (⇑N.subtype ∘ ![x, y]) = ![(x : M), (y : M)] from
      funext fun i => by fin_cases i <;> rfl] at h
    exact h.symm
  refine hXdefect (N : Set M) hXN (@IsWellOrder.mk _ _ ⟨?_⟩ ⟨?_⟩)
  · exact Subrelation.wf (fun {a b} hab => (hsub a b).mpr hab) hwoN.toIsWellFounded.wf
  · exact fun a b hab hba => Std.Trichotomous.trichotomous
      (r := fun x y : ↥N => @Structure.RelMap L ↥N _ 2 lt ![x, y]) a b
      (fun h => hab ((hsub a b).mp h)) (fun h => hba ((hsub b a).mp h))

omit [Countable (Σ l, L.Relations l)] in
/-- **The bridge**, equality form: if a sentence *defines* the well-order class on codes, then
every model of it conjoined with the infiniteness axiom is well-ordered.

The `ModelsOf φ = wellOrderClass lt` specialization of
`isWellOrder_of_realize_of_modelsOf_subset`; the defect-seed argument lives there and is not
repeated. -/
theorem isWellOrder_of_realize (lt : L.Relations 2) {φ : L.Sentenceω}
    (hφ : ModelsOf φ = wellOrderClass lt) (M : Type) [instM : L.Structure M]
    (hM : Sentenceω.Realize (φ.and (infiniteAxiom L)) M) :
    IsWellOrder M fun x y : M => RelMap lt ![x, y] :=
  isWellOrder_of_realize_of_modelsOf_subset lt hφ.subset M hM

end FirstOrder.Language
