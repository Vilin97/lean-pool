/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Scott.AtomicDiagram
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Back-and-Forth Equivalence

This file defines the back-and-forth equivalence relation between tuples in structures,
indexed by ordinals. This is the semantic predicate that corresponds to Scott formulas.

## Main Definitions

- `BFEquiv`: The α-back-and-forth equivalence between tuples, indexed by ordinal α.

## Main Results

- `BFEquiv.zero_iff_sameAtomicType`: At level 0, BF-equivalence is atomic type equivalence.
- `BFEquiv.monotone`: BF-equivalence at higher ordinals implies equivalence at lower ordinals.
- `BFEquiv.forth`/`BFEquiv.back`: Extension properties at successor ordinals.
- `BFEquiv.symm`: BF-equivalence is symmetric.

## Implementation Notes

We use `Ordinal.limitRecOn` for the definition, which requires handling three cases:
- Zero: same atomic type
- Successor `Order.succ α`: equivalence at α plus forth and back conditions
- Limit (with `Order.IsSuccLimit`): equivalence at all smaller ordinals

## Known Limitation: ω-Level Coherence and Quantifier Swap

A natural approach to proving `BFEquiv_omega_implies_equiv` (BF-equivalence at ω implies
isomorphism) is to define a "strategy" type that carries explicit witnesses instead of
just existence claims. The inductive definition:

```
inductive BFStrategy : (k : ℕ) → ... → Type
  | zero : SameAtomicType a b → BFStrategy 0 n a b
  | succ : BFStrategy k n a b →
           (forth : (m : M) → Σ n', BFStrategy k (n+1) ...) → ...
```

fails Lean's nested-inductive check. However, we CAN define BFStrategy by recursion on k
(this compiles and avoids the kernel restriction). See `BFStrategy` below.

We then define `BFStrategyOmega n a b := ∀ k, BFStrategy k n a b`, a coherent family of
strategies at all finite levels. This is the "winning strategy in the ω-round EF game."

**The real mathematical issue**: Even with these definitions, we have:
- `BFStrategyOmega → isomorphism` is provable (the strategy gives coherent witnesses)
- `BFEquiv ω → BFStrategyOmega` is the open problem (possibly false without extra assumptions)

This is the standard model-theory distinction: "BFEquiv holds at all finite levels"
(∀ k, Duplicator wins the k-round game) does NOT imply "Duplicator has a winning strategy
in the ω-round game," even for countable structures.

The obstruction is the quantifier swap:

```
From BFEquiv ω: ∀ k, ∃ n'_k, BFEquiv k (snoc a m) (snoc b n'_k)
Need:          ∃ n', ∀ k, BFEquiv k (snoc a m) (snoc b n')
```

**Concrete counterexample** to such swaps: Let S_k = {n ∈ ℕ | n ≥ k}. Each S_k is non-empty,
and S_0 ⊇ S_1 ⊇ S_2 ⊇ ..., but ⋂_k S_k = ∅. The witnesses keep shifting as k grows.

In our setting, S_k = {n' ∈ N | BFEquiv k (snoc a m) (snoc b n')}. By monotonicity of
BFEquiv, these sets are decreasing. But without a stabilization property, their
intersection may be empty.

**Note on alternative approaches**:
- Dependent choice does NOT help: even with full AC, ∀ k, ∃ n'_k doesn't yield ∃ n', ∀ k
  when the sets strictly decrease to empty intersection.
- König's lemma would require finite branching or compactness; not available here since
  the "tree" of valid witnesses lacks the necessary finiteness properties.
- A game-theoretic formulation (strategy as function on finite plays) might help but
  still requires proving a winning strategy exists from BFEquiv ω.

**Resolution (in Sentence.lean)**: We use the stabilization approach:
1. `StabilizesForTuples M α n`: BFEquiv α ↔ BFEquiv (succ α) for n-tuples from M
2. `StabilizesCompletely M α`: All tuple sizes stabilize at α
3. `exists_complete_stabilization`: For countable M, such α < ω₁ exists
4. `BFEquiv_stabilization_implies_equiv`: At stabilization, BFEquiv → isomorphism

At a complete stabilization ordinal, forth/back witnesses stay at the same level,
so the standard back-and-forth closes without quantifier swap issues.

**Important**: BFEquiv ω is equivalent to elementary equivalence (winning all finite EF games),
which does NOT imply isomorphism. Potential counterexamples in relational languages include
equivalence relations with matching finite-class structure but different arrangements of
infinite classes.
-/

universe u v w w'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable {M : Type w} [L.Structure M]
variable {N : Type w'} [L.Structure N]

open FirstOrder Structure Fin Ordinal

/-- Back-and-forth equivalence at ordinal α between tuples a in M and b in N.

At level 0: same atomic type.
At successor α + 1: same atomic type, plus:
  - (forth) for every m in M, there exists n in N with BFEquiv α (snoc a m) (snoc b n)
  - (back) for every n in N, there exists m in M with BFEquiv α (snoc a m) (snoc b n)
At limit λ: BFEquiv β for all β < λ.
-/
noncomputable def BFEquiv (α : Ordinal) (n : ℕ) (a : Fin n → M) (b : Fin n → N) : Prop :=
  Ordinal.limitRecOn α
    -- Zero case: same atomic type
    (fun (k : ℕ) (a' : Fin k → M) (b' : Fin k → N) =>
      SameAtomicType (L := L) (M := M) (N := N) a' b')
    -- Successor case
    (fun _β ih (k : ℕ) (a' : Fin k → M) (b' : Fin k → N) =>
      ih k a' b' ∧
      (∀ m : M, ∃ n' : N, ih (k + 1) (snoc a' m) (snoc b' n')) ∧
      (∀ n' : N, ∃ m : M, ih (k + 1) (snoc a' m) (snoc b' n')))
    -- Limit case
    (fun _β _hβ ih (k : ℕ) (a' : Fin k → M) (b' : Fin k → N) =>
      ∀ γ (hγ : γ < _β), ih γ hγ k a' b')
    n a b

variable {n : ℕ}

omit [L.IsRelational] in
theorem BFEquiv.zero (a : Fin n → M) (b : Fin n → N) :
    BFEquiv (L := L) 0 n a b ↔ SameAtomicType (L := L) (M := M) (N := N) a b := by
  simp only [BFEquiv, Ordinal.limitRecOn_zero]

omit [L.IsRelational] in
theorem BFEquiv.zero_iff_sameAtomicType (a : Fin n → M) (b : Fin n → N) :
    BFEquiv (L := L) 0 n a b ↔ SameAtomicType (L := L) (M := M) (N := N) a b :=
  BFEquiv.zero a b

omit [L.IsRelational] in
theorem BFEquiv.succ (α : Ordinal) (a : Fin n → M) (b : Fin n → N) :
    BFEquiv (L := L) (Order.succ α) n a b ↔
      BFEquiv (L := L) α n a b ∧
      (∀ m : M, ∃ n' : N, BFEquiv (L := L) α (n + 1) (snoc a m) (snoc b n')) ∧
      (∀ n' : N, ∃ m : M, BFEquiv (L := L) α (n + 1) (snoc a m) (snoc b n')) := by
  simp only [BFEquiv, Order.succ_eq_add_one, Ordinal.limitRecOn_add_one]

omit [L.IsRelational] in
theorem BFEquiv.limit (α : Ordinal) (hα : Order.IsSuccLimit α) (a : Fin n → M) (b : Fin n → N) :
    BFEquiv (L := L) α n a b ↔ ∀ β, β < α → BFEquiv (L := L) β n a b := by
  unfold BFEquiv
  rw [Ordinal.limitRecOn_limit _ _ _ _ hα]

omit [L.IsRelational] in
/-- BF-equivalence at level α + 1 implies BF-equivalence at level α. -/
theorem BFEquiv.of_succ {α : Ordinal} {a : Fin n → M} {b : Fin n → N}
    (h : BFEquiv (L := L) (Order.succ α) n a b) : BFEquiv (L := L) α n a b :=
  ((BFEquiv.succ α a b).mp h).1

omit [L.IsRelational] in
/-- BF-equivalence is monotone: higher ordinals imply lower ordinals. -/
theorem BFEquiv.monotone {α β : Ordinal} (hαβ : α ≤ β)
    {a : Fin n → M} {b : Fin n → N} (h : BFEquiv (L := L) β n a b) :
    BFEquiv (L := L) α n a b := by
  induction β using Ordinal.limitRecOn generalizing n a b with
  | zero =>
    simp only [nonpos_iff_eq_zero] at hαβ
    rwa [hαβ]
  | add_one γ ih =>
    rw [← Order.succ_eq_add_one] at hαβ h
    rcases hαβ.lt_or_eq with hαβ' | rfl
    · rw [Order.lt_succ_iff] at hαβ'
      exact ih hαβ' (BFEquiv.of_succ h)
    · exact h
  | limit γ hγ _ih =>
    rcases hαβ.lt_or_eq with hαβ' | rfl
    · exact (BFEquiv.limit γ hγ a b).mp h α hαβ'
    · exact h

omit [L.IsRelational] in
/-- The "forth" property at a successor level. -/
theorem BFEquiv.forth {α : Ordinal} {a : Fin n → M} {b : Fin n → N}
    (h : BFEquiv (L := L) (Order.succ α) n a b) (m : M) :
    ∃ n' : N, BFEquiv (L := L) α (n + 1) (snoc a m) (snoc b n') :=
  ((BFEquiv.succ α a b).mp h).2.1 m

omit [L.IsRelational] in
/-- The "back" property at a successor level. -/
theorem BFEquiv.back {α : Ordinal} {a : Fin n → M} {b : Fin n → N}
    (h : BFEquiv (L := L) (Order.succ α) n a b) (n' : N) :
    ∃ m : M, BFEquiv (L := L) α (n + 1) (snoc a m) (snoc b n') :=
  ((BFEquiv.succ α a b).mp h).2.2 n'

omit [L.IsRelational] in
/-- BF-equivalence at level 0 is reflexive. -/
theorem BFEquiv.refl_zero (a : Fin n → M) :
    BFEquiv (L := L) (M := M) (N := M) (0 : Ordinal) n a a :=
  (BFEquiv.zero a a).mpr (SameAtomicType.refl a)

omit [L.IsRelational] in
/-- BF-equivalence is reflexive at all levels. -/
theorem BFEquiv.refl (α : Ordinal) (a : Fin n → M) :
    BFEquiv (L := L) (M := M) (N := M) α n a a := by
  induction α using Ordinal.limitRecOn generalizing n a with
  | zero => exact (BFEquiv.zero a a).mpr (SameAtomicType.refl a)
  | add_one β ih =>
    rw [← Order.succ_eq_add_one, BFEquiv.succ]
    exact ⟨ih a, fun m => ⟨m, ih (snoc a m)⟩, fun m => ⟨m, ih (snoc a m)⟩⟩
  | limit β hβ ih =>
    rw [BFEquiv.limit β hβ]
    exact fun γ hγ => ih γ hγ a

omit [L.IsRelational] in
/-- BF-equivalence is symmetric at all levels. -/
theorem BFEquiv.symm {α : Ordinal} {a : Fin n → M} {b : Fin n → N}
    (h : BFEquiv (L := L) α n a b) : BFEquiv (L := L) (M := N) (N := M) α n b a := by
  induction α using Ordinal.limitRecOn generalizing n a b with
  | zero =>
    rw [BFEquiv.zero] at h ⊢
    exact h.symm
  | add_one β ih =>
    rw [← Order.succ_eq_add_one, BFEquiv.succ] at h ⊢
    exact ⟨ih h.1, fun n' => let ⟨m, hm⟩ := h.2.2 n'; ⟨m, ih hm⟩,
           fun m => let ⟨n', hn'⟩ := h.2.1 m; ⟨n', ih hn'⟩⟩
  | limit β hβ ih =>
    rw [BFEquiv.limit β hβ] at h ⊢
    exact fun γ hγ => ih γ hγ (h γ hγ)

omit [L.IsRelational] in
/-- BF-equivalence is transitive at all levels.
If a and b are BF-equivalent, and b and c are BF-equivalent, then a and c are BF-equivalent.
Note that a, b, c may be tuples in different structures. -/
theorem BFEquiv.trans {P : Type*} [L.Structure P]
    {α : Ordinal} {a : Fin n → M} {b : Fin n → N} {c : Fin n → P}
    (hab : BFEquiv (L := L) α n a b) (hbc : BFEquiv (L := L) α n b c) :
    BFEquiv (L := L) α n a c := by
  induction α using Ordinal.limitRecOn generalizing n a b c with
  | zero =>
    rw [BFEquiv.zero] at hab hbc ⊢
    exact fun idx => (hab idx).trans (hbc idx)
  | add_one β ih =>
    rw [← Order.succ_eq_add_one, BFEquiv.succ] at hab hbc ⊢
    refine ⟨ih hab.1 hbc.1, fun m => ?_, fun p => ?_⟩
    · let ⟨nb, hnb⟩ := hab.2.1 m; let ⟨p, hp⟩ := hbc.2.1 nb; exact ⟨p, ih hnb hp⟩
    · let ⟨nb, hnb⟩ := hbc.2.2 p; let ⟨m, hm⟩ := hab.2.2 nb; exact ⟨m, ih hm hnb⟩
  | limit β hβ ih =>
    rw [BFEquiv.limit β hβ] at hab hbc ⊢
    exact fun γ hγ => ih γ hγ (hab γ hγ) (hbc γ hγ)

/-! ### BFStrategy: Explicit Witness Strategies

A back-and-forth strategy at level k provides explicit witnesses for extensions.
Unlike `BFEquiv` which only asserts existence, a strategy carries the actual witnesses.

The key insight is that `BFStrategy` can be defined by recursion on k (not as an
inductive type), avoiding Lean's nested-inductive check that blocks inductive definitions.

The open problem is `BFEquiv ω → BFStrategyOmega`: this is the quantifier swap obstruction.
Having a strategy implies BFEquiv, but the converse requires choosing coherent witnesses.

**Important**: `BFEquiv ω` (winning all finite games) does NOT imply isomorphism in general.
Winning all finite back-and-forth games does not give an ω-round strategy. The Type-valued
`BFStrategyT` below is genuinely stronger than `BFEquiv ω` because it carries witnesses. -/

/-- Type-valued back-and-forth strategy at level k. Carries actual witnesses for extensions.

At level 0: a proof that tuples have the same atomic type (as a subtype of Unit).
At level k+1: strategy at level k, plus witness FUNCTIONS (not just existence) for forth/back.

This is STRONGER than `BFEquiv k` because it provides computational witnesses, not just
existence proofs. The converse `BFEquiv k → BFStrategyT k` requires Choice and loses coherence.

We use a recursive `def` (not `inductive`) to avoid Lean's nested-inductive restrictions.
The base case uses `{ _ : Unit // SameAtomicType a b }` to lift Prop to Type in a universe-
polymorphic way (Subtype lives in the same universe as the carrier type). -/
def BFStrategyT (L : Language.{u, v}) [L.IsRelational] (M : Type w) (N : Type w')
    [L.Structure M] [L.Structure N] : ℕ → (n : ℕ) → (Fin n → M) → (Fin n → N) → Type (max w w') :=
  fun k => match k with
  | 0 => fun _n a b => Subtype (fun _ : PUnit.{max w w' + 1} => SameAtomicType (L := L) a b)
  | k + 1 => fun n a b =>
    (BFStrategyT L M N k n a b) ×
    (∀ m : M, (n' : N) × BFStrategyT L M N k (n + 1) (Fin.snoc a m) (Fin.snoc b n')) ×
    (∀ n' : N, (m : M) × BFStrategyT L M N k (n + 1) (Fin.snoc a m) (Fin.snoc b n'))

/-- A coherent family of Type-valued strategies at all finite levels.
This is the "winning strategy in the ω-round EF game" with actual witnesses.

This is STRONGER than `BFEquiv ω`. The existence of `BFStrategyOmegaT` implies isomorphism
(provable by standard back-and-forth), but `BFEquiv ω` alone does not. -/
def BFStrategyOmegaT (n : ℕ) (a : Fin n → M) (b : Fin n → N) : Type _ :=
  ∀ k : ℕ, BFStrategyT L M N k n a b

/-- A Type-valued strategy at level k implies BF-equivalence at level k.
This direction is straightforward: just forget the witnesses. -/
theorem BFStrategyT_implies_BFEquiv {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (k : ℕ) (strat : BFStrategyT L M N k n a b) :
    BFEquiv (L := L) (k : Ordinal.{0}) n a b := by
  induction k generalizing n a b with
  | zero =>
    simp only [Nat.cast_zero]
    rw [BFEquiv.zero]
    exact strat.property
  | succ k ih =>
    have hsucc : ((k + 1 : ℕ) : Ordinal.{0}) = Order.succ (k : Ordinal.{0}) := by
      rw [Order.succ_eq_add_one]; norm_cast
    rw [hsucc, BFEquiv.succ]
    obtain ⟨strat_k, forth, back⟩ := strat
    refine ⟨ih strat_k, ?_, ?_⟩
    · intro m
      obtain ⟨n', strat_ext⟩ := forth m
      exact ⟨n', ih strat_ext⟩
    · intro n'
      obtain ⟨m, strat_ext⟩ := back n'
      exact ⟨m, ih strat_ext⟩

/-- A coherent ω-strategy implies BF-equivalence at level ω. -/
theorem BFStrategyOmegaT_implies_BFEquiv_omega {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (hstrat : BFStrategyOmegaT (L := L) n a b) :
    BFEquiv (L := L) (ω : Ordinal.{0}) n a b := by
  rw [BFEquiv.limit ω Ordinal.isSuccLimit_omega0]
  intro γ hγ
  have ⟨k, hk⟩ := Ordinal.lt_omega0.mp hγ
  subst hk
  exact BFStrategyT_implies_BFEquiv k (hstrat k)

/-! ### Universe Lifting for BFEquiv

BFEquiv is defined by `Ordinal.limitRecOn`, which is universe-specific. These lemmas
transport BFEquiv between ordinal universes via `Ordinal.lift`. -/

omit [L.IsRelational] in
/-- Lift BFEquiv from `Ordinal.{0}` to `Ordinal.{w}` at a specific ordinal.
If `BFEquiv β n a b` holds at `β : Ordinal.{0}`, then it holds at
`Ordinal.lift β : Ordinal.{w}`. -/
theorem BFEquiv.ofOrdinalLift
    {M : Type w} [L.Structure M] {N : Type w} [L.Structure N]
    {β : Ordinal.{0}} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : BFEquiv.{u, v, w, w, 0} (L := L) β n a b) :
    BFEquiv.{u, v, w, w, w} (L := L) (Ordinal.lift.{w, 0} β) n a b := by
  induction β using Ordinal.limitRecOn generalizing n a b with
  | zero =>
    rw [Ordinal.lift_zero, BFEquiv.zero] at *; exact h
  | add_one γ ih =>
    rw [← Order.succ_eq_add_one, Ordinal.lift_succ, BFEquiv.succ] at *
    exact ⟨ih h.1,
           fun m => let ⟨n', hn'⟩ := h.2.1 m; ⟨n', ih hn'⟩,
           fun n' => let ⟨m, hm⟩ := h.2.2 n'; ⟨m, ih hm⟩⟩
  | limit γ hγ ih =>
    rw [BFEquiv.limit _ (Ordinal.isSuccLimit_lift.mpr hγ)]
    intro δ hδ
    obtain ⟨γ', hγ'lt, rfl⟩ := Ordinal.lt_lift_iff.mp hδ
    exact ih γ' hγ'lt ((BFEquiv.limit γ hγ a b).mp h γ' hγ'lt)

omit [L.IsRelational] in
/-- Lower BFEquiv from `Ordinal.{w}` back to `Ordinal.{0}` at a specific ordinal.
If `BFEquiv (Ordinal.lift β) n a b` holds at the lifted ordinal, then
`BFEquiv β n a b` holds at the original. -/
theorem BFEquiv.toOrdinalLift
    {M : Type w} [L.Structure M] {N : Type w} [L.Structure N]
    {β : Ordinal.{0}} {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : BFEquiv.{u, v, w, w, w} (L := L) (Ordinal.lift.{w, 0} β) n a b) :
    BFEquiv.{u, v, w, w, 0} (L := L) β n a b := by
  induction β using Ordinal.limitRecOn generalizing n a b with
  | zero =>
    rw [Ordinal.lift_zero, BFEquiv.zero] at *; exact h
  | add_one γ ih =>
    rw [← Order.succ_eq_add_one, Ordinal.lift_succ, BFEquiv.succ] at h
    rw [← Order.succ_eq_add_one, BFEquiv.succ]
    exact ⟨ih h.1,
           fun m => let ⟨n', hn'⟩ := h.2.1 m; ⟨n', ih hn'⟩,
           fun n' => let ⟨m, hm⟩ := h.2.2 n'; ⟨m, ih hm⟩⟩
  | limit γ hγ ih =>
    rw [BFEquiv.limit _ hγ]
    intro γ' hγ'lt
    apply ih γ' hγ'lt
    exact (BFEquiv.limit _ (Ordinal.isSuccLimit_lift.mpr hγ) a b).mp h
      (Ordinal.lift γ') (Ordinal.lift_lt.mpr hγ'lt)

end Language

end FirstOrder
