/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.WellOrdering.ModelExtraction
import LeanPool.InfinitaryLogic.Methods.WellOrdering.Descent
/-!
# Boundedness of well-founded models (issue #12, step 6 layer 2)

Marker Corollary 4.27 in relational/countable form, via the step-5 theorem contrapositively:

* `wellFounded_boundedness_relational` — if every model of `φ` interprets `lt` as a
  well-founded relation, then some countable ordinal `α` chains into **no** model of `φ`:
  the step-5 relation-preserving map would otherwise contradict well-foundedness (layer 1).
* `wellOrder_type_boundedness_relational` — if every model of `φ` interprets `lt` as a
  well-**order**, the same `α` uniformly bounds the order types: an order type `≥ α` would
  re-embed the missing `α`-chain (`Ordinal.type_le_iff'` on `Ordinal.type_toType`).

Only the raw positive forms are consumed (`RelChain`, `RelPreserving`) — no injectivity is
needed anywhere: well-foundedness kills the descending sequence directly.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}} (φ : L.Sentenceω) (lt : L.Relations 2)

/-- **Boundedness, well-founded form** (relational/countable): if every model of `φ`
interprets `lt` as a well-founded relation, then some countable ordinal `α` admits an
`lt`-chain in no model of `φ`.  Contrapositive of the step-5 theorem: were every `α < ω₁`
realized by a chain, some model of `φ` would carry a relation-preserving map from `ℚ`,
contradicting well-foundedness through the descending negative rationals. -/
private theorem wellFounded_boundedness_relational [L.IsRelational]
    [Countable (Σ l, L.Relations l)]
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
    · -- the zero chain is vacuous; nonemptiness comes from the `α = 1` model
      obtain ⟨M, inst, hreal, w, -⟩ := hcon 1 (by
        have h1 := add_one_lt_omega1 hα
        rwa [zero_add] at h1)
      have : Nonempty (Ordinal.ToType 1) := Ordinal.nonempty_toType_iff.mpr one_ne_zero
      exact ⟨M, inst, ⟨w (Classical.arbitrary _)⟩, hreal,
        fun x => isEmptyElim x, fun x => isEmptyElim x⟩
    · obtain ⟨M, inst, hreal, w, hw⟩ := hcon α hα
      have : Nonempty α.ToType := Ordinal.nonempty_toType_iff.mpr hne
      exact ⟨M, inst, ⟨w (Classical.arbitrary _)⟩, hreal, w, hw⟩
  obtain ⟨M, instL, -, f, hφreal, hf⟩ := exists_model_relPreserving_relational φ lt hchains
  exact not_relPreserving_of_wellFounded (hwf M instL hφreal) f hf

/-- **Boundedness, order-type form** (Marker Corollary 4.27, relational/countable): if every
model of `φ` interprets `lt` as a well-order, then some countable ordinal `α` strictly
bounds the order type of every model's interpreted relation. -/
theorem wellOrder_type_boundedness_relational [L.IsRelational]
    [Countable (Σ l, L.Relations l)]
    (hwo : ∀ (M : Type) (_ : L.Structure M), Sentenceω.Realize φ M →
      IsWellOrder M fun x y : M => RelMap lt ![x, y]) :
    ∃ α : Ordinal.{0}, α < (Cardinal.aleph 1).ord ∧
      ∀ (M : Type) (inst : L.Structure M) (hreal : Sentenceω.Realize φ M),
        @Ordinal.type M (fun x y => RelMap lt ![x, y]) (hwo M inst hreal) < α := by
  obtain ⟨α, hα, hnochain⟩ := wellFounded_boundedness_relational φ lt
    (fun M inst h => letI := hwo M inst h; IsWellFounded.wf)
  refine ⟨α, hα, fun M inst hreal => ?_⟩
  let := hwo M inst hreal
  by_contra hle
  rw [not_lt, ← Ordinal.type_toType α] at hle
  obtain ⟨g⟩ := Ordinal.type_le_iff'.mp hle
  exact hnochain M inst hreal ⟨g, fun x y hxy => g.map_rel_iff.mpr hxy⟩

end FirstOrder.Language
