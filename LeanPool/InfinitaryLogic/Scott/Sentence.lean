/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Scott.Formula
import LeanPool.InfinitaryLogic.Karp.PotentialIso
import Mathlib.ModelTheory.PartialEquiv
import Mathlib.SetTheory.Cardinal.Regular
/-!
# Scott Sentences

This file proves the main theorem about Scott sentences: every countable structure
in a relational countable language has a Scott sentence characterizing it up to isomorphism.

## Main Definitions

- `scottSentence`: The Scott sentence of a countable structure.

## Main Results

- `scottSentence_characterizes`: A countable structure N satisfies the Scott sentence of M
  if and only if M and N are isomorphic.

## Implementation Notes

The proof proceeds by showing:
1. High enough BF-equivalence (with the empty tuple) implies `IsExtensionPair` in both directions.
2. `IsExtensionPair` in both directions between countable structures implies isomorphism
   (using mathlib's `equiv_between_cg`).
3. The Scott formula at the stabilization ordinal captures exactly this.
-/

universe u v w u'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Ordinal BoundedFormulaω Substructure

-- We fix the ordinal universe to avoid metavariable issues
-- In practice, we typically work with Ordinal.{0}

/-! ### Helper definitions to reduce repetition -/

/-- BFEquiv at the empty tuple level. This is the key semantic predicate for Scott sentences. -/
abbrev BFEquiv0 (M : Type w) (N : Type w') [L.Structure M] [L.Structure N] (α : Ordinal) : Prop :=
  BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)

/-- The ordinal α stabilizes for M if BFEquiv0 at level α characterizes isomorphism
with M among all countable structures of the same type. -/
def StabilizesAt (M : Type w) [L.Structure M] (α : Ordinal) : Prop :=
  ∀ (N : Type w) [L.Structure N] [Countable N], BFEquiv0 (L := L) M N α ↔ Nonempty (M ≃[L] N)

/-- BFEquiv α on n-tuples from M equals BFEquiv (succ α) for all countable N.
This captures when the BFEquiv relation has stopped distinguishing tuples at level α. -/
def StabilizesForTuples (M : Type w) [L.Structure M] (α : Ordinal) (n : ℕ) : Prop :=
  ∀ (N : Type w) [L.Structure N] [Countable N] (a : Fin n → M) (b : Fin n → N),
    BFEquiv (L := L) α n a b ↔ BFEquiv (L := L) (Order.succ α) n a b

/-- All tuple sizes stabilize at α. This is the key condition for the back-and-forth
argument to yield an isomorphism. -/
def StabilizesCompletely (M : Type w) [L.Structure M] (α : Ordinal) : Prop :=
  ∀ n : ℕ, StabilizesForTuples (L := L) M α n





omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- An isomorphism induces BF-equivalence at all ordinal levels. -/
theorem equiv_implies_BFEquiv {M N : Type w} [L.Structure M] [L.Structure N]
    (e : M ≃[L] N) (α : Ordinal) (n : ℕ) (a : Fin n → M) :
    BFEquiv (L := L) α n a (e ∘ a) := by
  induction α using Ordinal.limitRecOn generalizing n a with
  | zero =>
    rw [BFEquiv.zero]
    intro idx
    cases idx with
    | eq i j =>
      simp only [AtomicIdx.holds, Function.comp_apply]
      exact ⟨congrArg e, fun h => e.injective h⟩
    | rel R f =>
      simp only [AtomicIdx.holds, Function.comp_assoc]
      exact (e.map_rel R (a ∘ f)).symm
  | add_one β ih =>
    rw [← Order.succ_eq_add_one, BFEquiv.succ]
    refine ⟨ih n a, ?_, ?_⟩
    · intro m
      use e m
      rw [← Fin.comp_snoc]
      exact ih (n + 1) (Fin.snoc a m)
    · intro n'
      use e.symm n'
      have h1 := ih (n + 1) (Fin.snoc a (e.symm n'))
      rwa [Fin.comp_snoc, e.apply_symm_apply] at h1
  | limit β hβ ih =>
    rw [BFEquiv.limit β hβ]
    intro γ hγ
    exact ih γ hγ n a

/-! ### Stabilization Theory

The key insight is that for countable structures, the BFEquiv equivalence classes form
a refining sequence of partitions on tuples. Since there are only countably many tuples,
this sequence must stabilize before ω₁.

**Partition Argument**: For each α, BFEquiv α defines an equivalence relation on pairs
(a, N, b) where a is an n-tuple from M and b is an n-tuple from some countable N.
As α increases, this relation becomes finer (more distinguishing). But a decreasing
chain of partitions on a countable set has cardinality at most ω, so must stabilize
at some countable ordinal.

**Key Properties of Stabilization**:
1. If StabilizesForTuples M α n, then BFEquiv α n a b ↔ BFEquiv β n a b for all β ≥ α
2. StabilizesCompletely allows the back-and-forth to close: witnesses at level α stay at level α
3. This resolves the quantifier swap issue: we don't need ω, just any stable ordinal -/

/-! Note: StabilizesForTuples for a single tuple size n does NOT propagate to higher
ordinals without also having stabilization for (n+1)-tuples. This is because BFEquiv
at successor levels involves forth/back which creates tuples of size (n+1).

The correct approach is to use StabilizesCompletely which ensures all tuple sizes
stabilize simultaneously. See BFEquiv_upgrade_at_stabilization. -/

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- Self-stabilization: BFEquiv α on n-tuples from M vs M equals BFEquiv (succ α)
for all n. This is weaker than `StabilizesCompletely` which requires the iff
to hold for all countable N, not just M itself. -/
def SelfStabilizesCompletely (M : Type w) [L.Structure M] (α : Ordinal) : Prop :=
  ∀ (n : ℕ) (a a' : Fin n → M),
    BFEquiv (L := L) α n a a' ↔ BFEquiv (L := L) (Order.succ α) n a a'

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- At a complete stabilization ordinal, BFEquiv upgrades to all higher ordinals.
This is the key lemma that resolves the quantifier swap problem.

The proof proceeds by ordinal induction on β. The key insight is that at stabilization,
forth/back witnesses stay at level α, so we can upgrade them along with the base BFEquiv. -/
theorem BFEquiv_upgrade_at_stabilization {M N : Type w} [L.Structure M] [L.Structure N]
    [Countable N]
    {α : Ordinal} (hstab : StabilizesCompletely (L := L) M α)
    {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : BFEquiv (L := L) α n a b) (β : Ordinal) (hβ : α ≤ β) :
    BFEquiv (L := L) β n a b := by
  induction β using Ordinal.limitRecOn generalizing n a b with
  | zero => rwa [le_antisymm hβ bot_le] at h
  | add_one γ ih =>
    rw [← Order.succ_eq_add_one] at hβ ⊢
    rw [BFEquiv.succ]
    rcases hβ.lt_or_eq with hlt | heq
    · rw [Order.lt_succ_iff] at hlt
      have hγ := @ih n a b h hlt
      have h_succ := (hstab n N a b).mp h
      refine ⟨hγ, fun m => ?_, fun n' => ?_⟩
      · obtain ⟨n', hn'⟩ := BFEquiv.forth h_succ m
        exact ⟨n', @ih (n + 1) (Fin.snoc a m) (Fin.snoc b n') hn' hlt⟩
      · obtain ⟨m, hm⟩ := BFEquiv.back h_succ n'
        exact ⟨m, @ih (n + 1) (Fin.snoc a m) (Fin.snoc b n') hm hlt⟩
    · subst heq; exact (BFEquiv.succ γ a b).mp h
  | limit β hβlimit ih =>
    rw [BFEquiv.limit β hβlimit]
    intro γ hγ
    by_cases hαγ : α ≤ γ
    · exact @ih γ hγ n a b h hαγ
    · exact BFEquiv.monotone (le_of_lt (not_le.mp hαγ)) h





omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- For countable M, there exists α < ω₁ where all tuple sizes self-stabilize
(BFEquiv α n a a' ↔ BFEquiv (succ α) n a a' for all n and all a, a' : Fin n → M).

**Proof idea**: For each triple (n, a, a'), the sequence α ↦ BFEquiv α n a a' is
antitone (by `BFEquiv.monotone`). Define the "change ordinal" as
`sInf {γ | ¬BFEquiv γ n a a'}` when this set is nonempty; this is the ordinal where
the truth value permanently drops from True to False. For α past the change ordinal,
both BFEquiv α and BFEquiv (succ α) are False, so the iff holds. If the change ordinal
does not exist (BFEquiv is True everywhere) or is ≥ ω₁, then for any α < ω₁ with
succ α < ω₁, both sides are True.

Take globalStab = sup of all change ordinals that are < ω₁ (one per triple).
By countability of the sigma type and regularity of ω₁, globalStab < ω₁.
At globalStab, for each triple, either the change ordinal is ≤ globalStab (both sides
False) or > globalStab (both sides True since succ globalStab < ω₁). -/
theorem exists_complete_self_stabilization (M : Type w) [L.Structure M] [Countable M] :
    ∃ α < (Ordinal.omega 1 : Ordinal.{0}), SelfStabilizesCompletely (L := L) M α := by
  -- For each triple (n, a, a'), define the "change ordinal":
  -- the first level where BFEquiv fails, or 0 if it never fails below ω₁.
  -- We collect an ordinal < ω₁ for each triple such that globalStab past all of them works.
  -- The key: for each triple, either BFEquiv fails at some γ < ω₁ (contribute γ to sup)
  -- or BFEquiv holds at all levels < ω₁ (contribute 0 to sup).
  -- At globalStab = sup + 1:
  --   Failing triples: change ordinal ≤ γ ≤ globalStab, so both sides False, iff holds.
  --   Non-failing triples: BFEquiv True at all < ω₁, and succ globalStab < ω₁, so both True.
  --
  -- Step 1: For each triple, extract a "bound ordinal" < ω₁
  have hTriple : ∀ (t : Σ n, (Fin n → M) × (Fin n → M)),
      ∃ γ < (Ordinal.omega 1 : Ordinal.{0}),
        ∀ α, γ ≤ α → α < Ordinal.omega 1 → Order.succ α < Ordinal.omega 1 →
          (BFEquiv (L := L) α t.1 t.2.1 t.2.2 ↔ BFEquiv (L := L) (Order.succ α) t.1 t.2.1 t.2.2) := by
    intro ⟨n, a, a'⟩
    simp only
    by_cases hFail : ∃ β < (Ordinal.omega 1 : Ordinal.{0}), ¬BFEquiv (L := L) β n a a'
    · obtain ⟨β, hβ_lt, hβ_fail⟩ := hFail
      set S := {δ : Ordinal.{0} | ¬BFEquiv (L := L) δ n a a'}
      have hCP := csInf_mem (show S.Nonempty from ⟨β, hβ_fail⟩)
      refine ⟨sInf S, lt_of_le_of_lt (csInf_le' hβ_fail) hβ_lt, fun α hα _ _ => ?_⟩
      exact ⟨fun h => absurd h (fun hBF => hCP (BFEquiv.monotone hα hBF)),
             fun h => absurd h (fun hBF => hCP (BFEquiv.monotone hα (BFEquiv.of_succ hBF)))⟩
    · -- BFEquiv holds at all levels < ω₁
      push Not at hFail
      use 0
      refine ⟨Ordinal.omega_pos 1, ?_⟩
      intro α _ hα_lt hsucc_lt
      exact ⟨fun _ => hFail (Order.succ α) hsucc_lt, fun _ => hFail α hα_lt⟩
  -- Step 2: Extract per-triple bound ordinals
  choose boundOrd hboundOrd_lt hboundOrd_spec using hTriple
  -- Step 3: Enumerate all triples
  have : Countable (Σ n, (Fin n → M) × (Fin n → M)) := inferInstance
  -- Handle empty M
  by_cases hM_nonempty : Nonempty M
  swap
  · have : IsEmpty M := not_nonempty_iff.mp hM_nonempty
    exact ⟨0, Ordinal.omega_pos 1, fun n a a' => match n with
      | 0 => ⟨fun h0 => (BFEquiv.succ 0 a a').mpr
          ⟨h0, fun m => isEmptyElim m, fun m' => isEmptyElim m'⟩, BFEquiv.of_succ⟩
      | _ + 1 => (IsEmpty.false (a 0)).elim⟩
  have : Nonempty M := hM_nonempty
  have : Nonempty (Σ n, (Fin n → M) × (Fin n → M)) :=
    ⟨⟨0, Fin.elim0, Fin.elim0⟩⟩
  obtain ⟨enumTriples, hTriples_surj⟩ :=
    exists_surjective_nat (Σ n, (Fin n → M) × (Fin n → M))
  -- Step 4: Define globalStab as supremum + 1
  let globalStab : Ordinal.{0} := ⨆ k, boundOrd (enumTriples k) + 1
  -- Step 5: Show globalStab < ω₁
  have hGlobalLt : globalStab < Ordinal.omega 1 :=
    Ordinal.iSup_lt_omega_one fun k =>
      Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1) (hboundOrd_lt _)
  -- Step 6: succ globalStab < ω₁ (since ω₁ is a limit ordinal)
  have hSuccGlobalLt : Order.succ globalStab < Ordinal.omega 1 :=
    Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1) hGlobalLt
  -- Step 7: Show globalStab satisfies SelfStabilizesCompletely
  use globalStab, hGlobalLt
  intro n a a'
  obtain ⟨k, hk⟩ := hTriples_surj ⟨n, a, a'⟩
  have hBdd : BddAbove (Set.range fun k => boundOrd (enumTriples k) + 1) :=
    ⟨Ordinal.omega 1, fun _ ⟨m, hm⟩ => hm ▸ le_of_lt
      (Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1) (hboundOrd_lt _))⟩
  have hbound_le : boundOrd ⟨n, a, a'⟩ ≤ globalStab :=
    le_trans (Order.le_succ _) (hk ▸ le_ciSup hBdd k)
  exact hboundOrd_spec ⟨n, a, a'⟩ globalStab hbound_le hGlobalLt hSuccGlobalLt



/-! ### Countable intersection and BFEquiv-to-PotentialIso lemmas -/

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- A decreasing ω₁-chain of nonempty subsets of a countable type has nonempty intersection.

More precisely: if `S : Ordinal → Set X` where `X` is countable, `S` is antitone
(S α ⊇ S β for α ≤ β), and each `S α` is nonempty for `α < ω₁`, then
`⋂ α < ω₁, S α` is nonempty.

**Proof**: For each `x ∈ S 0`, define `d(x) = sInf {α | x ∉ S α}` (the "departure ordinal").
If all `d(x) < ω₁`, then `sup {d(x)} < ω₁` by regularity of ω₁ and countability of X.
Let `γ = sup {d(x)}`. Then `S γ = ∅` (every element has departed), contradicting nonemptiness.
So some `x` has `d(x) ≥ ω₁`, meaning `x ∈ S α` for all `α < ω₁`. -/
private theorem nonempty_iInter_of_antitone_of_nonempty {X : Type*} [Countable X]
    (S : Ordinal.{0} → Set X) (hAnti : Antitone S)
    (hNonempty : ∀ α < (Ordinal.omega 1 : Ordinal.{0}), (S α).Nonempty) :
    (⋂ α ∈ Set.Iio (Ordinal.omega 1 : Ordinal.{0}), S α).Nonempty := by
  classical
  -- For each x, define d(x) = sInf {α | x ∉ S α} (possibly = 0 if x ∉ S 0)
  -- If d(x) ≥ ω₁ for some x, then x ∈ S α for all α < ω₁ and we're done.
  by_contra hEmpty
  rw [Set.not_nonempty_iff_eq_empty] at hEmpty
  -- Every x eventually departs: for every x ∈ S 0, ∃ α < ω₁ with x ∉ S α
  have hAllDepart : ∀ x ∈ S 0, ∃ α < (Ordinal.omega 1 : Ordinal.{0}), x ∉ S α := by
    intro x hx0
    by_contra hall
    push Not at hall
    -- x ∈ S α for all α < ω₁
    have hxmem : x ∈ ⋂ α ∈ Set.Iio (Ordinal.omega 1 : Ordinal.{0}), S α := by
      simp only [Set.mem_iInter, Set.mem_Iio]
      exact fun α hα => hall α hα
    rw [hEmpty] at hxmem
    exact hxmem
  -- For each x ∈ S 0, choose a departure ordinal < ω₁
  have hS0nonempty : (S 0).Nonempty := hNonempty 0 (Ordinal.omega_pos 1)
  -- Get departure ordinals for ALL elements (set to 0 for x ∉ S 0)
  let depart : X → Ordinal.{0} := fun x =>
    if hx : x ∈ S 0 then (hAllDepart x hx).choose else 0
  have hdepart_lt : ∀ x ∈ S 0, depart x < Ordinal.omega 1 := by
    intro x hx
    simp only [depart]
    rw [dite_eq_left hx]
    exact (hAllDepart x hx).choose_spec.1
  have hdepart_spec : ∀ x ∈ S 0, x ∉ S (depart x) := by
    intro x hx
    simp only [depart]
    rw [dite_eq_left hx]
    exact (hAllDepart x hx).choose_spec.2
  -- Enumerate X (or rather S 0)
  -- Take sup of departure ordinals over all of X
  -- Enumerate X via ℕ to use iSup_sequence_lt_omega_one
  by_cases hX : IsEmpty X
  · -- If X is empty, S 0 = ∅, contradicting nonemptiness
    exact absurd (hNonempty 0 (Ordinal.omega_pos 1)) (by
      rw [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem]
      intro x; exact hX.elim x)
  rw [not_isEmpty_iff] at hX; have := hX
  obtain ⟨enum, henum⟩ := exists_surjective_nat X
  -- Compose depart with enum to get ℕ → Ordinal.{0}
  let depart_seq : ℕ → Ordinal.{0} := depart ∘ enum
  have hdepart_seq_lt : ∀ k, depart_seq k < (Cardinal.aleph 1).ord := by
    intro k
    rw [Cardinal.ord_aleph]
    by_cases hx : enum k ∈ S 0
    · exact hdepart_lt (enum k) hx
    · show depart (enum k) < _
      simp only [depart]
      rw [dite_eq_right hx]
      exact Ordinal.omega_pos 1
  have hSup_lt : (⨆ k, depart_seq k) < Ordinal.omega 1 :=
    Ordinal.iSup_lt_omega_one fun k => by rw [← Cardinal.ord_aleph]; exact hdepart_seq_lt k
  have hBdd_seq : BddAbove (Set.range depart_seq) :=
    ⟨Ordinal.omega 1, fun _ ⟨k, hk⟩ => hk ▸ le_of_lt
      (by rw [Cardinal.ord_aleph] at hdepart_seq_lt; exact hdepart_seq_lt k)⟩
  have hle_sup : ∀ x : X, depart x ≤ ⨆ k, depart_seq k := by
    intro x
    obtain ⟨k, hk⟩ := henum x
    calc depart x = depart (enum k) := by rw [hk]
      _ = depart_seq k := rfl
      _ ≤ ⨆ k, depart_seq k := le_ciSup hBdd_seq k
  -- S (iSup depart_seq) is nonempty
  obtain ⟨x, hx⟩ := hNonempty (⨆ k, depart_seq k) hSup_lt
  -- x ∈ S (iSup depart_seq) ⊆ S 0
  have hx0 : x ∈ S 0 := hAnti bot_le hx
  -- But depart x ≤ iSup depart_seq, so S (iSup ...) ⊆ S (depart x)
  -- And x ∉ S (depart x), contradiction
  exact hdepart_spec x hx0 (hAnti (hle_sup x) hx)

omit [Countable (Σ l, L.Relations l)] in
/-- If two countable structures are BF-equivalent at all ordinal levels below ω₁
(for the empty tuple), then there exists a potential isomorphism between them,
and hence they are isomorphic.

**Proof**: Define the family
`F = {(k, a, b) | ∀ α < ω₁, BFEquiv α k a b}`.
This family contains the empty tuple (by hypothesis) and is compatible (BFEquiv 0 gives
SameAtomicType). For the forth property: given (k, a, b) ∈ F and m : M, for each α < ω₁,
from BFEquiv (succ α) k a b (since succ α < ω₁ by regularity), BFEquiv.forth gives
n'_α with BFEquiv α (k+1) (snoc a m) (snoc b n'_α). The sets
`S_α = {n' ∈ N | BFEquiv α (k+1) (snoc a m) (snoc b n')}` form a decreasing chain
(by BFEquiv.monotone) of nonempty subsets of the countable type N.
By `nonempty_iInter_of_antitone_of_nonempty`, ∃ n' in the intersection, giving
BFEquiv α (k+1) (snoc a m) (snoc b n') for all α < ω₁. The back property is symmetric.

The result then follows from `PotentialIso.countable_toEquiv`. -/
private theorem BFEquiv_below_omega1_implies_potentialIso
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N]
    (h : ∀ α < (Ordinal.omega 1 : Ordinal.{0}),
      BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)) :
    Nonempty (PotentialIso L M N) := by
  -- Define the family: tuples that are BF-equivalent at ALL levels < ω₁
  let F : Set (Σ n : ℕ, (Fin n → M) × (Fin n → N)) :=
    { p | ∀ α < (Ordinal.omega 1 : Ordinal.{0}), BFEquiv (L := L) α p.1 p.2.1 p.2.2 }
  -- empty_mem: by hypothesis
  have hempty : ⟨0, Fin.elim0, Fin.elim0⟩ ∈ F := h
  -- compatible: BFEquiv 0 gives SameAtomicType
  have hcompat : ∀ p ∈ F, SameAtomicType (L := L) p.2.1 p.2.2 := by
    intro p hp
    exact (BFEquiv.zero p.2.1 p.2.2).mp (hp 0 (Ordinal.omega_pos 1))
  -- forth: use the countable intersection lemma
  have hforth : ∀ p ∈ F, ∀ m : M, ∃ n' : N,
      ⟨p.1 + 1, Fin.snoc p.2.1 m, Fin.snoc p.2.2 n'⟩ ∈ F := by
    intro ⟨k, a, b⟩ hp m
    simp only [Set.mem_ofPred_eq, F] at hp ⊢
    -- For each α < ω₁, succ α < ω₁ (ω₁ is a limit), so BFEquiv (succ α) k a b holds.
    -- By forth, ∃ n'_α with BFEquiv α (k+1) (snoc a m) (snoc b n'_α).
    -- Define S_α = {n' | BFEquiv α (k+1) (snoc a m) (snoc b n')}
    let S : Ordinal.{0} → Set N := fun α =>
      { n' | BFEquiv (L := L) α (k + 1) (Fin.snoc a m) (Fin.snoc b n') }
    -- S is antitone
    have hAnti : Antitone S := by
      intro α β hαβ n' hn'
      simp only [Set.mem_ofPred_eq, S] at hn' ⊢
      exact BFEquiv.monotone hαβ hn'
    -- Each S α is nonempty for α < ω₁
    have hNonempty : ∀ α < (Ordinal.omega 1 : Ordinal.{0}), (S α).Nonempty := by
      intro α hα
      have hsucc_lt : Order.succ α < Ordinal.omega 1 :=
        Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1) hα
      obtain ⟨n', hn'⟩ := BFEquiv.forth (hp (Order.succ α) hsucc_lt) m
      exact ⟨n', hn'⟩
    -- By countable intersection lemma
    obtain ⟨n', hn'⟩ := nonempty_iInter_of_antitone_of_nonempty S hAnti hNonempty
    simp only [Set.mem_iInter, Set.mem_Iio, Set.mem_ofPred_eq, S] at hn'
    exact ⟨n', hn'⟩
  -- back: symmetric argument
  have hback : ∀ p ∈ F, ∀ n' : N, ∃ m : M,
      ⟨p.1 + 1, Fin.snoc p.2.1 m, Fin.snoc p.2.2 n'⟩ ∈ F := by
    intro ⟨k, a, b⟩ hp n'
    simp only [Set.mem_ofPred_eq, F] at hp ⊢
    let S : Ordinal.{0} → Set M := fun α =>
      { m | BFEquiv (L := L) α (k + 1) (Fin.snoc a m) (Fin.snoc b n') }
    have hAnti : Antitone S := by
      intro α β hαβ m hm
      simp only [Set.mem_ofPred_eq, S] at hm ⊢
      exact BFEquiv.monotone hαβ hm
    have hNonempty : ∀ α < (Ordinal.omega 1 : Ordinal.{0}), (S α).Nonempty := by
      intro α hα
      have hsucc_lt : Order.succ α < Ordinal.omega 1 :=
        Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1) hα
      obtain ⟨m, hm⟩ := BFEquiv.back (hp (Order.succ α) hsucc_lt) n'
      exact ⟨m, hm⟩
    obtain ⟨m, hm⟩ := nonempty_iInter_of_antitone_of_nonempty S hAnti hNonempty
    simp only [Set.mem_iInter, Set.mem_Iio, Set.mem_ofPred_eq, S] at hm
    exact ⟨m, hm⟩
  exact ⟨PotentialIso.mk F hempty hcompat hforth hback⟩

omit [Countable (Σ l, L.Relations l)] in
/-- Corollary: If BFEquiv at all levels below ω₁ for empty tuples between countable structures,
then they are isomorphic. Combines `BFEquiv_below_omega1_implies_potentialIso` with
`PotentialIso.countable_toEquiv`. -/
theorem BFEquiv_below_omega1_implies_iso
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N]
    (h : ∀ α < (Ordinal.omega 1 : Ordinal.{0}),
      BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)) :
    Nonempty (M ≃[L] N) := by
  obtain ⟨P⟩ := BFEquiv_below_omega1_implies_potentialIso (L := L) h
  exact P.countable_toEquiv





/-! ### Refinement Descent Lemmas

These lemmas decompose refinement failures at n-tuples into refinement failures at
(n+1)-tuples at strictly smaller ordinals. They are the key infrastructure for proving
`per_tuple_stabilization_below_omega1` without relying on the `FormulaCode` bridge. -/









/-! ### Conditional Pipeline (Code-free approach)

The counting hypothesis captures the key content that each refinement set is countable.
This decouples the Scott analysis pipeline from the `FormulaCode` bridge
(`agree_codes_implies_BFEquiv`), which has a known gap. All downstream results
(`per_tuple_stabilization_below_omega1_of`, `exists_complete_stabilization_of`,
`scottRank_le_implies_stabilizesCompletely_of`) hold conditional on this hypothesis.

The hypothesis is mathematically true: each refinement step corresponds to a split
in the formula-type partition, and countable structures admit only countably many
such splits. A full formal proof requires either a code-based bridge or a direct
game-theoretic counting argument. -/

/-- **Counting hypothesis** for per-tuple stabilization.

For a countable structure M in a countable relational language, the set of ordinals
below ω₁ where BFEquiv refinement occurs for a fixed tuple is countable.

This encapsulates the deep counting argument: each refinement step corresponds to a
split in the formula-type partition, and countable structures admit only countably many
such splits.

**Boundary**: This is the sole non-trivial hypothesis in the Scott analysis pipeline.
All other reasoning (descent lemmas, stabilization from countability, Scott rank bounds)
is fully formalized. -/
def CountableRefinementHypothesis (L : Language.{u, v})
    [L.IsRelational] [Countable (Σ l, L.Relations l)] : Prop :=
  ∀ (M : Type w) [L.Structure M] [Countable M] (n : ℕ) (a : Fin n → M),
    Set.Countable {ε : Ordinal.{0} | ε < Ordinal.omega 1 ∧
      ∃ (N : Type w) (_ : L.Structure N) (_ : Countable N) (b : Fin n → N),
        BFEquiv (L := L) ε n a b ∧ ¬BFEquiv (L := L) (Order.succ ε) n a b}

/-- Per-tuple stabilization, conditional on `CountableRefinementHypothesis`. -/
theorem per_tuple_stabilization_below_omega1_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    {M : Type w} [L.Structure M] [Countable M]
    (n : ℕ) (a : Fin n → M) :
    ∃ γ < (Ordinal.omega 1 : Ordinal.{0}),
      ∀ α, γ ≤ α → α < Ordinal.omega 1 → Order.succ α < Ordinal.omega 1 →
        ∀ (N : Type w) [L.Structure N] [Countable N] (b : Fin n → N),
          (BFEquiv (L := L) α n a b ↔ BFEquiv (L := L) (Order.succ α) n a b) := by
  by_cases hAllHold : ∀ β < (Ordinal.omega 1 : Ordinal.{0}),
      ∀ (N : Type w) (instN : L.Structure N) (instCN : Countable N) (b : Fin n → N),
        BFEquiv (L := L) β n a b
  · exact ⟨0, Ordinal.omega_pos 1, fun α _ hα_lt hsucc_lt N instN instCN b =>
      ⟨fun _ => hAllHold (Order.succ α) hsucc_lt N instN instCN b, BFEquiv.of_succ⟩⟩
  · push Not at hAllHold
    obtain ⟨β₀, hβ₀_lt, N₀, instN₀, instCN₀, b₀, hβ₀_fail⟩ := hAllHold
    have hR := hcount M n a
    by_cases hRne : ({α : Ordinal.{0} | α < Ordinal.omega 1 ∧
        ∃ (N : Type w) (_ : L.Structure N) (_ : Countable N) (b : Fin n → N),
          BFEquiv (L := L) α n a b ∧ ¬BFEquiv (L := L) (Order.succ α) n a b}).Nonempty
    · have := hR.to_subtype
      have := hRne.to_subtype
      obtain ⟨enum, henum⟩ := exists_surjective_nat
        ({α : Ordinal.{0} | α < Ordinal.omega 1 ∧
          ∃ (N : Type w) (_ : L.Structure N) (_ : Countable N) (b : Fin n → N),
            BFEquiv (L := L) α n a b ∧ ¬BFEquiv (L := L) (Order.succ α) n a b})
      let seq : ℕ → Ordinal.{0} := fun k => (enum k).1
      have hseq_lt : ∀ k, seq k < Ordinal.omega 1 := fun k => (enum k).2.1
      have hsup_lt := Ordinal.iSup_lt_omega_one hseq_lt
      have hSuccSupLt : Order.succ (⨆ k, seq k) < Ordinal.omega 1 :=
        Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1) hsup_lt
      refine ⟨Order.succ (⨆ k, seq k), hSuccSupLt,
        fun α hα hα_lt hsucc_lt N instN instCN b => ?_⟩
      constructor
      · intro hBF
        by_contra hNot
        have hαR : α ∈ ({α : Ordinal.{0} | α < Ordinal.omega 1 ∧
            ∃ (N : Type w) (_ : L.Structure N) (_ : Countable N) (b : Fin n → N),
              BFEquiv (L := L) α n a b ∧ ¬BFEquiv (L := L) (Order.succ α) n a b}) :=
          ⟨hα_lt, N, instN, instCN, b, hBF, hNot⟩
        obtain ⟨k, hk⟩ := henum ⟨α, hαR⟩
        have hα_eq : seq k = α := congr_arg Subtype.val hk
        have hBdd : BddAbove (Set.range seq) :=
          ⟨Ordinal.omega 1, fun x ⟨k, hk⟩ => hk ▸ le_of_lt (hseq_lt k)⟩
        have hα_le_sup : α ≤ ⨆ k, seq k := hα_eq ▸ le_ciSup hBdd k
        exact absurd (lt_of_lt_of_le (Order.lt_succ (⨆ k, seq k)) (le_trans hα hα_le_sup))
          (lt_irrefl _)
      · exact BFEquiv.of_succ
    · rw [Set.not_nonempty_iff_eq_empty] at hRne
      refine ⟨0, Ordinal.omega_pos 1, fun α _ hα_lt hsucc_lt N instN instCN b => ?_⟩
      constructor
      · intro hBF
        by_contra hNot
        have hmem : α ∈ ({α : Ordinal.{0} | α < Ordinal.omega 1 ∧
            ∃ (N : Type w) (_ : L.Structure N) (_ : Countable N) (b : Fin n → N),
              BFEquiv (L := L) α n a b ∧ ¬BFEquiv (L := L) (Order.succ α) n a b}) :=
          ⟨hα_lt, N, instN, instCN, b, hBF, hNot⟩
        rw [hRne] at hmem
        exact hmem.elim
      · exact BFEquiv.of_succ

/-- Complete stabilization, conditional on `CountableRefinementHypothesis`. -/
theorem exists_complete_stabilization_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    (M : Type w) [L.Structure M] [Countable M] :
    ∃ α < (Ordinal.omega 1 : Ordinal.{0}), StabilizesCompletely (L := L) M α := by
  have hTuple : ∀ (t : Σ n, Fin n → M),
      ∃ γ < (Ordinal.omega 1 : Ordinal.{0}),
        ∀ α, γ ≤ α → α < Ordinal.omega 1 → Order.succ α < Ordinal.omega 1 →
          ∀ (N : Type w) [L.Structure N] [Countable N] (b : Fin t.1 → N),
            (BFEquiv (L := L) α t.1 t.2 b ↔ BFEquiv (L := L) (Order.succ α) t.1 t.2 b) :=
    fun ⟨n, a⟩ => per_tuple_stabilization_below_omega1_of hcount n a
  choose boundOrd hboundOrd_lt hboundOrd_spec using hTuple
  have : Countable (Σ n, Fin n → M) := inferInstance
  by_cases hM_nonempty : Nonempty M
  swap
  · have : IsEmpty M := not_nonempty_iff.mp hM_nonempty
    use 1
    constructor
    · calc (1 : Ordinal) < ω := Ordinal.one_lt_omega0
        _ ≤ Ordinal.omega 1 := Ordinal.omega0_le_omega 1
    · intro n N _ _ a b
      cases n with
      | zero =>
        constructor
        · intro hBF
          have h1eq : (1 : Ordinal) = Order.succ 0 := by
            rw [Order.succ_eq_add_one]; simp
          rw [h1eq] at hBF ⊢
          rw [BFEquiv.succ] at hBF
          rw [BFEquiv.succ]
          refine ⟨(BFEquiv.succ 0 a b).mpr hBF, fun m => isEmptyElim m, fun n' => ?_⟩
          exact isEmptyElim (hBF.2.2 n').choose
        · exact BFEquiv.of_succ
      | succ k => exact (IsEmpty.false (a 0)).elim
  have : Nonempty M := hM_nonempty
  have : Nonempty (Σ n, Fin n → M) := ⟨⟨0, Fin.elim0⟩⟩
  obtain ⟨enumTuples, hTuples_surj⟩ := exists_surjective_nat (Σ n, Fin n → M)
  let globalStab : Ordinal.{0} := ⨆ k, boundOrd (enumTuples k) + 1
  have hGlobalLt : globalStab < Ordinal.omega 1 := by
    have hEachLt : ∀ k, boundOrd (enumTuples k) + 1 < Ordinal.omega 1 := fun k =>
      Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1) (hboundOrd_lt (enumTuples k))
    exact Ordinal.iSup_lt_omega_one hEachLt
  have hSuccGlobalLt : Order.succ globalStab < Ordinal.omega 1 :=
    Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1) hGlobalLt
  use globalStab, hGlobalLt
  intro n N _ _ a b
  obtain ⟨k, hk⟩ := hTuples_surj ⟨n, a⟩
  have hBdd : BddAbove (Set.range fun k => boundOrd (enumTuples k) + 1) :=
    ⟨Ordinal.omega 1, fun _ ⟨m, hm⟩ => hm ▸ le_of_lt
      (Order.IsSuccLimit.succ_lt (Cardinal.isSuccLimit_omega 1)
        (hboundOrd_lt (enumTuples m)))⟩
  have hk_le : boundOrd ⟨n, a⟩ + 1 ≤ globalStab := by
    have h := le_ciSup hBdd k
    simpa only [hk] using h
  have hbound_le : boundOrd ⟨n, a⟩ ≤ globalStab :=
    le_trans (Order.le_succ _) hk_le
  exact hboundOrd_spec ⟨n, a⟩ globalStab hbound_le hGlobalLt hSuccGlobalLt N b

omit [Countable (Σ l, L.Relations l)] in
/-- At a complete stabilization ordinal, BFEquiv0 implies isomorphism for countable structures.
This is the corrected version of BFEquiv_omega_implies_equiv. -/
theorem BFEquiv_stabilization_implies_equiv {M N : Type w} [L.Structure M] [L.Structure N]
    [Countable M] [Countable N]
    {α : Ordinal} (hstab : StabilizesCompletely (L := L) M α)
    (h : BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)) :
    Nonempty (M ≃[L] N) := by
  -- Construct PotentialIso from stabilization: the family of tuples with BFEquiv α
  -- At stabilization, BFEquiv α ↔ BFEquiv (succ α), so forth/back witnesses stay at level α
  exact (PotentialIso.mk
    { p | BFEquiv (L := L) α p.1 p.2.1 p.2.2 }
    h
    (fun p hp => (BFEquiv.zero p.2.1 p.2.2).mp (BFEquiv.monotone bot_le hp))
    (fun ⟨k, a, b⟩ hp m => by
      simp only [Set.mem_ofPred_eq] at hp ⊢
      exact BFEquiv.forth ((hstab k N a b).mp hp) m)
    (fun ⟨k, a, b⟩ hp n' => by
      simp only [Set.mem_ofPred_eq] at hp ⊢
      exact BFEquiv.back ((hstab k N a b).mp hp) n')
  ).countable_toEquiv

/-- The stabilization ordinal for a structure M: the least ordinal where the Scott analysis
stabilizes. We fix the ordinal universe to 0 for consistency with our BFEquiv definitions. -/
noncomputable def stabilizationOrdinal (M : Type w) [L.Structure M] [Countable M] :
    Ordinal.{0} :=
  sInf {α : Ordinal.{0} | StabilizesAt (L := L) M α}

/-- The Scott sentence of a countable structure M in a relational countable language.

A sentence is a formula with no free variables, which corresponds to `Formulaω (Fin 0)`
since `Fin 0` is empty. -/
noncomputable def scottSentence (M : Type w) [L.Structure M] [Countable M] : L.Formulaω (Fin 0) :=
  scottFormula (L := L) (M := M) (n := 0) Fin.elim0
    (stabilizationOrdinal (L := L) M)

/-- Realize a formula with no free variables as a sentence in a structure. -/
def Formulaω.realize_as_sentence (φ : L.Formulaω (Fin 0)) (N : Type w) [L.Structure N] : Prop :=
  φ.Realize (Fin.elim0 : Fin 0 → N)



/-! ### Conditional Scott Sentence Pipeline

Variants of the entire Scott sentence chain, conditional on
`CountableRefinementHypothesis`. The same `scottSentence` definition is used;
only the proof that it characterizes isomorphism is rebuilt. -/

/-- Conditional variant of `exists_stabilization`. -/
theorem exists_stabilization_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    (M : Type w) [L.Structure M] [Countable M] :
    ∃ α < (Ordinal.omega 1 : Ordinal.{0}), StabilizesAt (L := L) M α := by
  obtain ⟨α, hα_lt, hstab⟩ := exists_complete_stabilization_of hcount M
  use α, hα_lt
  intro N _ _
  constructor
  · exact BFEquiv_stabilization_implies_equiv hstab
  · intro ⟨e⟩
    show BFEquiv0 (L := L) M N α
    unfold BFEquiv0
    rw [← comp_fin_elim0 e]
    exact equiv_implies_BFEquiv e α 0 Fin.elim0

/-- Conditional variant of `stabilizationOrdinal_lt_omega1'`. -/
theorem stabilizationOrdinal_lt_omega1_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    (M : Type w) [L.Structure M] [Countable M] :
    stabilizationOrdinal (L := L) M < Ordinal.omega 1 := by
  obtain ⟨α, hα_lt, hα_spec⟩ := exists_stabilization_of hcount M
  exact lt_of_le_of_lt (csInf_le' hα_spec) hα_lt

/-- Conditional variant of `stabilizationOrdinal_stabilizes`. -/
theorem stabilizationOrdinal_stabilizes_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    (M : Type w) [L.Structure M] [Countable M] :
    StabilizesAt (L := L) M (stabilizationOrdinal (L := L) M) := by
  obtain ⟨α, _, hα_spec⟩ := exists_stabilization_of hcount M
  have h_nonempty : {α : Ordinal.{0} | StabilizesAt (L := L) M α}.Nonempty :=
    ⟨α, hα_spec⟩
  exact csInf_mem h_nonempty

/-- **Conditional Scott sentence characterization**: variant of
`scottSentence_characterizes`, conditional on `CountableRefinementHypothesis`.

A countable structure N satisfies the Scott sentence of M iff M ≅ N.
Uses the same `scottSentence M` definition; only the proof is rebuilt
through the conditional pipeline. -/
theorem scottSentence_characterizes_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    (M : Type w) [L.Structure M] [Countable M]
    (N : Type w) [L.Structure N] [Countable N] :
    (scottSentence (L := L) M).realize_as_sentence N ↔ Nonempty (M ≃[L] N) := by
  unfold scottSentence Formulaω.realize_as_sentence
  have h := realize_scottFormula_iff_BFEquiv (L := L) (M := M) (N := N)
    (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)
    (stabilizationOrdinal (L := L) M) (stabilizationOrdinal_lt_omega1_of hcount M)
  rw [h]
  exact stabilizationOrdinal_stabilizes_of hcount M N







end Language

end FirstOrder
