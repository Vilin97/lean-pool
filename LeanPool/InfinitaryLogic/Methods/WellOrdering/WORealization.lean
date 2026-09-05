/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.WellOrdering.StarCondition
import LeanPool.InfinitaryLogic.Methods.SchemaCompletion
import LeanPool.InfinitaryLogic.Methods.Interpolation.PairedInsepFamily
/-!
# Realization helpers for the closure fields (issue #12, commit 4b part 1)

The shared semantic tools the fifteen closure fields consume, isolated per review:

* `realize_lift_wc` — the constant-free lift bridge: `φ̂` holds at the controlled expansion
  iff `φ` holds in the base structure.
* `sentenceJConsts_lift_eq_empty` — the lift mentions no constants (its `functionsIn` image
  consists of `Sum.inl` symbols only).
* **The C0 helper** (`StarWitness.realize_base_of_opposite`): a base member whose opposite
  lies in the finite remainder is realized at level `1` — split into the lifted-root case
  (the bridge) and the positive-diagram case (the opponent's support + `mark_cover` +
  `realize_marked_atom`).  `C0_no_contradiction` then becomes a symmetric four-case
  base/remainder argument with no symbol/support bookkeeping inside the packaged field.
* **The repointing invariant** (`StarWitness.rem_realize_update`): updating the constant
  interpretation at an index absent from the remainder's support preserves remainder
  realization (`realize_congr_const`).  Reused by `eq_refl`, `all_inst`, and the fresh
  witness case.
* Shape/support facts about `baseDiagram` members (`mem_baseDiagram_elim`,
  `not_mem_baseDiagram_elim`, `sentenceJConsts_ratLtAtom`, `not_ne_self`,
  `lift_eq_falsum_reflect`).
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}}

/-! ## The constant-free lift -/

/-- The lift bridge: the lifted root holds at the controlled expansion iff the root holds in
the base structure. -/
theorem realize_lift_wc {M : Type} (base : L.Structure M) (h : ℕ → M) (φ : L.Sentenceω) :
    @Sentenceω.Realize L[[ℕ]] (φ.mapLanguage (L.lhomWithConstants ℕ)) M (wc base h) ↔
      Sentenceω.Realize φ M := by
  let := base
  let : (constantsOn ℕ).Structure M := constantsOn.structure h
  exact BoundedFormulaω.realize_mapLanguage (L.lhomWithConstants ℕ) φ _ _

/-- The lift mentions no constants. -/
theorem sentenceJConsts_lift_eq_empty (φ : L.Sentenceω) :
    sentenceJConsts (L' := L) (J := ℕ) (φ.mapLanguage (L.lhomWithConstants ℕ)) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro j hj
  rw [sentenceJConsts, Set.mem_ofPred_eq, BoundedFormulaω.functionsIn_mapLanguage] at hj
  obtain ⟨⟨l, f⟩, -, heq⟩ := hj
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp heq
  have h3 : (L.lhomWithConstants ℕ).onFunction f = Sum.inr j := eq_of_heq h2
  simp [Language.lhomWithConstants, LHom.sumInl] at h3

/-! ## Shape and support of base-diagram members -/

/-- A base-diagram member is the lifted root or a positive diagram atom. -/
theorem mem_baseDiagram_elim {φ : L.Sentenceω} {lt : L.Relations 2}
    {χ : L[[ℕ]].Sentenceω} (h : χ ∈ baseDiagram φ lt) :
    χ = φ.mapLanguage (L.lhomWithConstants ℕ) ∨ ∃ q r : ℚ, q < r ∧ χ = ratLtAtom lt q r := by
  rcases h with h | h
  · exact Or.inl h
  · obtain ⟨q, r, hqr, rfl⟩ := h
    exact Or.inr ⟨q, r, hqr, rfl⟩

/-- No formula equals its own negation. -/
theorem BoundedFormulaω.not_ne_self {L' : Language.{0, 0}} {α : Type} {n : ℕ}
    (φ : L'.BoundedFormulaω α n) : φ.not ≠ φ := by
  intro h
  have := congrArg sizeOf h
  simp only [BoundedFormulaω.not, BoundedFormulaInf.not] at this
  cases φ <;> simp_all <;> omega

/-- The constant support of a positive diagram atom. -/
theorem sentenceJConsts_ratLtAtom (lt : L.Relations 2) (q r : ℚ) :
    sentenceJConsts (L' := L) (J := ℕ) (ratLtAtom lt q r) =
      {ratConstIdx q, ratConstIdx r} := by
  rw [ratLtAtom, sentenceJConsts_relInst_eq]
  ext c
  simp [or_comm]

/-- The lift reflects `falsum`. -/
theorem lift_eq_falsum_reflect {φ : L.Sentenceω}
    (h : φ.mapLanguage (L.lhomWithConstants ℕ) =
      (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω)) : φ = BoundedFormulaω.falsum := by
  cases φ <;> simp_all [BoundedFormulaω.mapLanguage]

/-! ## The C0 helper -/

/-- **A base member whose opposite lies in the finite remainder is realized at level `1`**:
the lifted root through the bridge, a positive diagram atom through the opponent's support,
`mark_cover`, and the derived diagram. -/
theorem StarWitness.realize_base_of_opposite {φ : L.Sentenceω} {lt : L.Relations 2}
    {Γ : Set L[[ℕ]].Sentenceω} (W : StarWitness φ lt Γ 1) {χ : L[[ℕ]].Sentenceω}
    (hχ : χ ∈ baseDiagram φ lt) (hopp : χ.not ∈ Γ) :
    @Sentenceω.Realize L[[ℕ]] χ W.M (wc W.inst W.h) := by
  rcases mem_baseDiagram_elim hχ with rfl | ⟨q, r, hqr, rfl⟩
  · exact (realize_lift_wc W.inst W.h φ).mpr W.base_realize
  · -- the opponent mentions both rationals, so both are marked
    have hq : q ∈ ratSupport (L := L) Γ := by
      refine ⟨_, hopp, ?_⟩
      rw [sentenceJConsts_not, sentenceJConsts_ratLtAtom]
      exact Set.mem_insert _ _
    have hr : r ∈ ratSupport (L := L) Γ := by
      refine ⟨_, hopp, ?_⟩
      rw [sentenceJConsts_not, sentenceJConsts_ratLtAtom]
      exact Set.mem_insert_of_mem _ rfl
    obtain ⟨i, hi⟩ := W.mark_cover hq
    obtain ⟨j, hj⟩ := W.mark_cover hr
    have hij : i < j := by
      rw [← W.mark_mono.lt_iff_lt, hi, hj]
      exact hqr
    have := W.realize_marked_atom one_pos hij
    rwa [hi, hj] at this

/-! ## The repointing invariant -/

/-- **Repointing a constant absent from the remainder's support preserves remainder
realization** — the invariant behind every constant rule (`eq_refl`, `all_inst`, the fresh
witness). -/
theorem StarWitness.rem_realize_update {φ : L.Sentenceω} {lt : L.Relations 2}
    {Γ : Set L[[ℕ]].Sentenceω} {α : Ordinal.{0}} (W : StarWitness φ lt Γ α) {c : ℕ}
    (hc : ∀ χ ∈ Γ, c ∉ sentenceJConsts (L' := L) (J := ℕ) χ) (x : W.M) :
    ∀ χ ∈ Γ, @Sentenceω.Realize L[[ℕ]] χ W.M (wc W.inst (Function.update W.h c x)) := by
  intro χ hχ
  refine (BoundedFormulaω.realize_congr_const W.inst χ (fun k hk => ?_) _ _).mp
    (W.rem_realize χ hχ)
  have hkc : k ≠ c := fun hkc => hc χ hχ (by rw [← hkc]; exact hk)
  exact (Function.update_of_ne hkc x W.h).symm

end FirstOrder.Language
