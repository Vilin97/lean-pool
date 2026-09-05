/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.OrdinalUtil
import LeanPool.InfinitaryLogic.Descriptive.SatisfactionBorel
import LeanPool.InfinitaryLogic.Scott.BackAndForth
import Mathlib.SetTheory.Cardinal.Aleph
/-!
# BFEquiv is Borel on the Pair Space

This file proves that the back-and-forth equivalence relation `BFEquiv α` is
measurable (Borel) on the pair space `StructureSpace L × StructureSpace L`
for `α < ω₁`.

## Main Definitions

- `StructurePairSpace L`: The product `StructureSpace L × StructureSpace L`.
- `BFEquivSet`: The set of code pairs where `BFEquiv α n a b` holds.

## Main Results

- `bfEquivSet_measurableSet`: `BFEquivSet α n a b` is measurable for `α < ω₁`.

## Proof Strategy

Direct transfinite induction on `α` matching `BFEquiv`'s definition:
- **Zero**: `SameAtomicType a b` = countable intersection over `AtomicIdx`.
- **Successor β**: IH ∧ (∀ m, ∃ n', IH on snoc) ∧ (∀ n', ∃ m, IH on snoc).
- **Limit β**: `⋂_{γ < β} IH` — countable intersection (since `β < ω₁`).
-/

universe u v

namespace FirstOrder

namespace Language

open Structure MeasureTheory Ordinal Cardinal

variable {L : Language.{u, v}} [L.IsRelational]

/-- The pair space: two coded structures. -/
abbrev StructurePairSpace (L : Language.{u, v}) :=
  StructureSpace L × StructureSpace L

/-- The product measurable space on the pair space. -/
instance : MeasurableSpace (StructurePairSpace L) :=
  MeasurableSpace.prod inferInstance inferInstance

/-- The set of code pairs where `BFEquiv α n a b` holds. -/
def BFEquivSet (α : Ordinal.{0}) (n : ℕ)
    (a : Fin n → ℕ) (b : Fin n → ℕ) :
    Set (StructurePairSpace L) :=
  {p | @BFEquiv L ℕ p.1.toStructure ℕ p.2.toStructure α n a b}

/-- `SameAtomicType a b` on the pair space is measurable. -/
private theorem sameAtomicType_measurableSet
    [Countable (Σ l, L.Relations l)]
    (n : ℕ) (a : Fin n → ℕ) (b : Fin n → ℕ) :
    MeasurableSet {p : StructurePairSpace L |
      @SameAtomicType L ℕ p.1.toStructure n ℕ p.2.toStructure a b} := by
  -- SameAtomicType a b = ∀ idx, idx.holds a ↔ idx.holds b
  have : Countable (L.AtomicIdx n) := inferInstance
  have : Encodable (L.AtomicIdx n) := Encodable.ofCountable _
  -- Countable intersection over AtomicIdx
  have : {p : StructurePairSpace L |
      @SameAtomicType L ℕ p.1.toStructure n ℕ p.2.toStructure a b} =
    ⋂ (idx : L.AtomicIdx n), {p | @AtomicIdx.holds L ℕ p.1.toStructure n idx a ↔
      @AtomicIdx.holds L ℕ p.2.toStructure n idx b} := by
    ext p; simp only [SameAtomicType, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [this]
  apply MeasurableSet.iInter
  intro idx
  cases idx with
  | eq i j =>
    -- a i = a j ↔ b i = b j — decided by the tuples, not the codes
    simp only [AtomicIdx.holds]
    by_cases h₁ : a i = a j <;> by_cases h₂ : b i = b j <;> simp [h₁, h₂]
  | rel R f =>
    simp only [AtomicIdx.holds]
    -- Rewrite rel-map in terms of the code value
    have hset : {p : StructurePairSpace L |
        @Structure.RelMap L ℕ p.1.toStructure _ R (a ∘ f) ↔
        @Structure.RelMap L ℕ p.2.toStructure _ R (b ∘ f)} =
      {p | p.1 ⟨⟨_, R⟩, a ∘ f⟩ = true ↔ p.2 ⟨⟨_, R⟩, b ∘ f⟩ = true} := by
      ext p; simp
    rw [hset]
    -- The iff-set decomposes as (both true) ∪ (both false)
    have hdecomp : {p : StructurePairSpace L |
        p.1 ⟨⟨_, R⟩, a ∘ f⟩ = true ↔ p.2 ⟨⟨_, R⟩, b ∘ f⟩ = true} =
      ({p | p.1 ⟨⟨_, R⟩, a ∘ f⟩ = true} ∩ {p | p.2 ⟨⟨_, R⟩, b ∘ f⟩ = true}) ∪
      ({p | p.1 ⟨⟨_, R⟩, a ∘ f⟩ = true}ᶜ ∩ {p | p.2 ⟨⟨_, R⟩, b ∘ f⟩ = true}ᶜ) := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
      rcases Bool.eq_false_or_eq_true (p.1 ⟨⟨_, R⟩, a ∘ f⟩) with h1 | h1 <;>
        rcases Bool.eq_false_or_eq_true (p.2 ⟨⟨_, R⟩, b ∘ f⟩) with h2 | h2 <;>
        simp_all
    rw [hdecomp]
    set q₁ : RelQuery L := ⟨⟨_, R⟩, a ∘ f⟩
    set q₂ : RelQuery L := ⟨⟨_, R⟩, b ∘ f⟩
    exact ((measurable_fst (measurableSet_relHolds q₁)).inter
           (measurable_snd (measurableSet_relHolds q₂))).union
          ((measurable_fst (measurableSet_relHolds q₁)).compl.inter
           (measurable_snd (measurableSet_relHolds q₂)).compl)

/-- The main theorem: `BFEquivSet α n a b` is measurable for `α < ω₁`. -/
theorem bfEquivSet_measurableSet
    [Countable (Σ l, L.Relations l)]
    (α : Ordinal.{0}) (hα : α < Ordinal.omega 1)
    (n : ℕ) (a b : Fin n → ℕ) :
    MeasurableSet (BFEquivSet (L := L) α n a b) := by
  induction α using Ordinal.limitRecOn generalizing n a b with
  | zero =>
    -- BFEquiv 0 = SameAtomicType
    have : BFEquivSet (L := L) 0 n a b =
      {p | @SameAtomicType L ℕ p.1.toStructure n ℕ p.2.toStructure a b} := by
      ext p; exact @BFEquiv.zero L ℕ p.1.toStructure ℕ p.2.toStructure n a b
    rw [this]
    exact sameAtomicType_measurableSet n a b
  | add_one β ih =>
    rw [← Order.succ_eq_add_one] at hα ⊢
    have hβ : β < Ordinal.omega 1 := lt_trans (Order.lt_succ β) hα
    have : BFEquivSet (L := L) (Order.succ β) n a b =
      BFEquivSet β n a b ∩
      (⋂ (m : ℕ), ⋃ (n' : ℕ), BFEquivSet β (n + 1) (Fin.snoc a m) (Fin.snoc b n')) ∩
      (⋂ (n' : ℕ), ⋃ (m : ℕ), BFEquivSet β (n + 1) (Fin.snoc a m) (Fin.snoc b n')) := by
      ext p
      simp only [BFEquivSet, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_iUnion]
      rw [@BFEquiv.succ L ℕ p.1.toStructure ℕ p.2.toStructure n β a b]
      tauto
    rw [this]
    exact ((ih hβ n a b).inter
          (MeasurableSet.iInter fun m =>
            MeasurableSet.iUnion fun n' =>
              ih hβ (n + 1) (Fin.snoc a m) (Fin.snoc b n'))).inter
          (MeasurableSet.iInter fun n' =>
            MeasurableSet.iUnion fun m =>
              ih hβ (n + 1) (Fin.snoc a m) (Fin.snoc b n'))
  | limit β hβ_limit ih =>
    have : BFEquivSet (L := L) β n a b =
      ⋂ (γ : Set.Iio β), BFEquivSet (↑γ) n a b := by
      ext p
      simp only [BFEquivSet, Set.mem_ofPred_eq, Set.mem_iInter, Set.Iio, Subtype.forall]
      exact @BFEquiv.limit L ℕ p.1.toStructure ℕ p.2.toStructure n β hβ_limit a b
    rw [this]
    have := InfinitaryLogic.countable_Iio_of_lt_omega1 β hα
    exact MeasurableSet.iInter fun γ => ih γ.1 γ.2 (lt_trans γ.2 hα) n a b

end Language

end FirstOrder
