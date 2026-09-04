/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.WellOrdering.SymbolCountability
import LeanPool.InfinitaryLogic.Methods.Interpolation.GraphReconstruction
/-!
# The arbitrary-language graph translation (issue #12, the final transport)

The `[L.IsRelational]` restriction removed through the Craig Layer-3 relationalization:

* the translated root is `relationalizeFormula φ ⊓ graphAxioms φ.functionsIn` over
  `graphLanguage L` (relational by construction; its symbol supply may be uncountable, which
  is exactly why the symbol-countability wrapper came first);
* the distinguished relation survives as `GraphRelation.base lt` — the graph expansion and
  the reconstruction both preserve base relations **definitionally**, so chains and the
  rational map transport with no computation;
* chains transfer along `graphExpansion` (which satisfies the axioms), the wrapped
  relational endpoint fires, and `reconstructStructure` turns the graph model back into an
  `L`-model realizing `φ` via the capstone `realize_relationalize_reconstruct`.

The four public **arbitrary-language** endpoints of issue #12 live here:
`exists_model_relPreserving` (Marker Theorem 4.26), `wellFounded_boundedness`,
`wellOrder_type_boundedness` (Marker Corollary 4.27), and `wellOrdering_undefinable`.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}}

/-- **Marker Theorem 4.26 (arbitrary language)**: if `φ` has models with `lt`-chains of
every countable length, then some nonempty model of `φ` carries a relation-preserving map
`f : ℚ → M` — the raw positive conclusion; injectivity is a corollary under irreflexivity
(`RelPreserving.injective_of_irreflexive`). -/
theorem exists_model_relPreserving (φ : L.Sentenceω) (lt : L.Relations 2)
    (h : HasWellOrderedChains φ lt) :
    ∃ (M : Type) (_ : L.Structure M) (_ : Nonempty M) (f : ℚ → M),
      Sentenceω.Realize φ M ∧ RelPreserving lt f := by
  classical
  have : Countable ↥φ.functionsIn := φ.functionsIn_countable.to_subtype
  have hchainsg : HasWellOrderedChains
      (relationalizeFormula φ ⊓ graphAxioms φ.functionsIn)
      (GraphRelation.base lt : (graphLanguage L).Relations 2) := by
    intro α hα
    obtain ⟨M, instM, ne, hreal, w, hchain⟩ := h α hα
    have := ne
    let instG : (graphLanguage L).Structure M := graphExpansion L M
    refine ⟨M, instG, ne, ?_, w, fun x y hxy => hchain x y hxy⟩
    refine (BoundedFormulaω.realize_inf _ _).mpr ⟨?_, ?_⟩
    · exact (realize_relationalizeFormula φ Empty.elim Fin.elim0).mpr hreal
    · exact graphExpansion_realizes_graphAxioms φ.functionsIn M
  obtain ⟨N, instNg, neN, f, hrealψ, hf⟩ :=
    exists_model_relPreserving_isRelational _ _ hchainsg
  let := instNg
  have := neN
  obtain ⟨hrelφ, hAx⟩ := (BoundedFormulaω.realize_inf _ _).mp hrealψ
  -- re-ascribed at the sentence level: `SentenceInf.Realize` is a plain definition upstream, so
  -- the consumers' implicit arguments cannot be solved against the unfolded form
  have hAxS : Sentenceω.Realize (graphAxioms φ.functionsIn) N := hAx
  let instN : L.Structure N := reconstructStructure φ.functionsIn hAxS
  refine ⟨N, instN, neN, f, ?_, fun q r hqr => hf q r hqr⟩
  exact (realize_relationalize_reconstruct hAxS φ (subset_refl _)
    Empty.elim Fin.elim0).mp hrelφ

/-- **Boundedness, well-founded form (arbitrary language)**: if every model of `φ`
interprets `lt` as a well-founded relation, some countable ordinal chains into no model. -/
private theorem wellFounded_boundedness (φ : L.Sentenceω) (lt : L.Relations 2)
    (hwf : ∀ (M : Type) (_ : L.Structure M), Sentenceω.Realize φ M →
      WellFounded fun x y : M => RelMap lt ![x, y]) :
    ∃ α : Ordinal.{0}, α < (Cardinal.aleph 1).ord ∧
      ∀ (M : Type) (_ : L.Structure M), Sentenceω.Realize φ M →
        ¬ ∃ w : α.ToType → M, RelChain lt α w := by
  by_contra hcon
  push Not at hcon
  have hchains : HasWellOrderedChains φ lt := by
    intro α hα
    rcases eq_or_ne α 0 with rfl | hne
    · obtain ⟨M, inst, hreal, w, -⟩ := hcon 1 (by
        have h1 := add_one_lt_omega1 hα
        rwa [zero_add] at h1)
      have : Nonempty (Ordinal.ToType 1) := Ordinal.nonempty_toType_iff.mpr one_ne_zero
      exact ⟨M, inst, ⟨w (Classical.arbitrary _)⟩, hreal,
        fun x => isEmptyElim x, fun x => isEmptyElim x⟩
    · obtain ⟨M, inst, hreal, w, hw⟩ := hcon α hα
      have : Nonempty α.ToType := Ordinal.nonempty_toType_iff.mpr hne
      exact ⟨M, inst, ⟨w (Classical.arbitrary _)⟩, hreal, w, hw⟩
  obtain ⟨M, instL, -, f, hφreal, hf⟩ := exists_model_relPreserving φ lt hchains
  exact not_relPreserving_of_wellFounded (hwf M instL hφreal) f hf

/-- **Boundedness, order-type form (Marker Corollary 4.27, arbitrary language)**: if every
model of `φ` interprets `lt` as a well-order, some countable ordinal strictly bounds every
model's order type. -/
theorem wellOrder_type_boundedness (φ : L.Sentenceω) (lt : L.Relations 2)
    (hwo : ∀ (M : Type) (_ : L.Structure M), Sentenceω.Realize φ M →
      IsWellOrder M fun x y : M => RelMap lt ![x, y]) :
    ∃ α : Ordinal.{0}, α < (Cardinal.aleph 1).ord ∧
      ∀ (M : Type) (inst : L.Structure M) (hreal : Sentenceω.Realize φ M),
        @Ordinal.type M (fun x y => RelMap lt ![x, y]) (hwo M inst hreal) < α := by
  obtain ⟨α, hα, hnochain⟩ := wellFounded_boundedness φ lt
    (fun M inst h => letI := hwo M inst h; IsWellFounded.wf)
  refine ⟨α, hα, fun M inst hreal => ?_⟩
  let := hwo M inst hreal
  by_contra hle
  rw [not_lt, ← Ordinal.type_toType α] at hle
  obtain ⟨g⟩ := Ordinal.type_le_iff'.mp hle
  exact hnochain M inst hreal ⟨g, fun x y hxy => g.map_rel_iff.mpr hxy⟩

/-- The comparison structure on an ordinal's type over an **arbitrary** language: every
binary relation symbol is the ordinal order, other relations are empty, and functions are
interpreted arbitrarily (the carrier must be nonempty — the undefinability proof uses
`α + 1`). -/
@[reducible] noncomputable def ordinalStructureFull (L : Language.{0, 0}) (α : Ordinal.{0})
    [Nonempty α.ToType] : L.Structure α.ToType where
  funMap _ _ := Classical.arbitrary _
  RelMap {n} _ v := ordRel α n v

/-- Any binary relation symbol of the full comparison structure is the ordinal order. -/
theorem ordinalStructureFull_relMap (L : Language.{0, 0}) (α : Ordinal.{0})
    [Nonempty α.ToType] (lt : L.Relations 2) (x y : α.ToType) :
    @RelMap L α.ToType (ordinalStructureFull L α) 2 lt ![x, y] ↔ x < y := by
  show ordRel α 2 ![x, y] ↔ x < y
  simp [ordRel, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **Undefinability of well-ordering (arbitrary language, weak form)**: no sentence has as
models exactly the structures whose interpreted relation is a well-order.  The comparison
structure on `α + 1` (nonempty, so functions can be interpreted) violates the uniform
order-type bound `α`. -/
theorem wellOrdering_undefinable (lt : L.Relations 2) :
    ¬ ∃ φ : L.Sentenceω, ∀ (M : Type) (_ : L.Structure M),
        (Sentenceω.Realize φ M ↔ IsWellOrder M fun x y : M => RelMap lt ![x, y]) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨α, hα, hbound⟩ := wellOrder_type_boundedness φ lt
    (fun M inst h => (hφ M inst).mp h)
  have : Nonempty (α + 1).ToType :=
    Ordinal.nonempty_toType_iff.mpr (zero_le.trans_lt (lt_add_one α)).ne'
  let instα : L.Structure (α + 1).ToType := ordinalStructureFull L (α + 1)
  have hrel : (fun x y : (α + 1).ToType => RelMap lt ![x, y]) = (· < ·) :=
    funext fun x => funext fun y => propext (ordinalStructureFull_relMap L (α + 1) lt x y)
  have hwo : IsWellOrder (α + 1).ToType (fun x y => RelMap lt ![x, y]) := by
    rw [hrel]; infer_instance
  have hreal : Sentenceω.Realize φ (α + 1).ToType := (hφ _ instα).mpr hwo
  have hb := hbound (α + 1).ToType instα hreal
  have hiso : (fun x y : (α + 1).ToType => RelMap lt ![x, y]) ≃r
      ((· < ·) : (α + 1).ToType → (α + 1).ToType → Prop) :=
    ⟨_root_.Equiv.refl _, fun {a b} => (ordinalStructureFull_relMap L (α + 1) lt a b).symm⟩
  rw [RelIso.ordinalType_congr hiso, Ordinal.type_toType] at hb
  exact absurd (hb.trans (lt_add_one α)) (lt_irrefl _)

end FirstOrder.Language
