/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Order.Hom.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Set.Finite.Basic

/-!
# Infinite Ramsey on `ℕ` for finite-arity `Bool` colorings

This file isolates the *pure* combinatorial residual consumed by the tail-weakened
Morley–Hanf extraction (`MorleyHanfExtractionTail`). The statement audit (2026-06-14)
established that the tail residual asks only for a **countable** sequence that is
**tail**-indiscernible for **countably many** finite-arity `Bool` colorings. That is an
*infinite Ramsey* fact on `ℕ` — **not** an `ℶ_{ω₁}` Erdős–Rado / partition-calculus theorem.
(The `ℶ_{ω₁}` beth schedule is a strictly stronger statement, needed only for full/uncountable
indiscernibility; it is not consumed by this bridge. See
`InfinitaryLogic/Conditional/MorleyHanfTransfer.lean`.)

## Main statement

* `infinite_ramsey_nat_arity` — single-coloring `n`-ary infinite Ramsey on `ℕ`: a `Bool`
  coloring of strictly-increasing `n`-tuples of `ℕ` has an order-embedding `f : ℕ ↪o ℕ` whose
  image is monochromatic. This is the genuine new combinatorics (to be proved by induction on
  the arity `n`, generalizing `infinite_ramsey_unary_nat`/`infinite_ramsey_pair_nat`).

The countable-family diagonal form `infinite_ramsey_nat_family` lives in
`InfiniteRamseyFamily.lean` and is derived from this single-coloring lemma. The model-side
extraction (`MorleyHanfExtractionTail`) is proved against the family form, verifying that the
cheap route discharges the conditional surface.
-/

universe u

open Set Classical in
/-- Prepend a head `a` to an `n`-tuple `w : Fin n ↪o ℕ` whose entries all exceed `a`,
producing the strictly-increasing `(n+1)`-tuple `(a, w 0, …, w (n-1))`. -/
private def consOEmb {n : ℕ} (a : ℕ) (w : Fin n ↪o ℕ) (h : ∀ k, a < w k) :
    Fin (n + 1) ↪o ℕ :=
  OrderEmbedding.ofStrictMono (Fin.cons a (w : Fin n → ℕ)) (by
    intro p q hpq
    induction p using Fin.cases with
    | zero => induction q using Fin.cases with
      | zero => exact absurd hpq (lt_irrefl _)
      | succ j => simpa only [Fin.cons_zero, Fin.cons_succ] using h j
    | succ i => induction q using Fin.cases with
      | zero => exact absurd hpq (by simp)
      | succ j =>
        simp only [Fin.cons_succ]; rw [w.lt_iff_lt]; exact (Fin.succ_lt_succ_iff).mp hpq)

open Classical in
/-- The `n`-ary coloring induced from an `(n+1)`-ary coloring `c` by fixing a head `a`:
on tuples whose entries all exceed `a` it returns `c` of the `cons`-extension, and is
otherwise junk (the junk values are never inspected). -/
private noncomputable def headColoring {n : ℕ} (c : (Fin (n + 1) ↪o ℕ) → Bool) (a : ℕ) :
    (Fin n ↪o ℕ) → Bool :=
  fun w => if h : ∀ k, a < w k then c (consOEmb a w h) else false

private lemma headColoring_spec {n : ℕ} (c : (Fin (n + 1) ↪o ℕ) → Bool) (a : ℕ)
    (w : Fin n ↪o ℕ) (h : ∀ k, a < w k) : headColoring c a w = c (consOEmb a w h) := by
  simp only [headColoring, dite_eq_left h]

open Set in
/-- Removing the least element of an infinite set of naturals (equivalently, intersecting
with the strictly-larger naturals) leaves an infinite set. -/
private lemma tailRegion_infinite {U : Set ℕ} (hU : U.Infinite) :
    (U ∩ {x | sInf U < x}).Infinite := by
  have hsub : U ∩ {x | sInf U < x} = U \ {sInf U} := by
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, mem_sdiff, mem_singleton_iff]
    constructor
    · rintro ⟨hxU, hlt⟩; exact ⟨hxU, by rintro rfl; exact absurd hlt (lt_irrefl _)⟩
    · rintro ⟨hxU, hne⟩
      refine ⟨hxU, ?_⟩
      rcases (Nat.sInf_le hxU).lt_or_eq with h | h
      · exact h
      · exact absurd h.symm hne
  rw [hsub]; exact hU.sdiff (Set.finite_singleton _)

open Classical in
/-- **Set-form finite-arity infinite Ramsey on `ℕ`** (the inductive core).

For any `Bool` coloring `c` of strictly-increasing `n`-tuples and any infinite `S ⊆ ℕ`,
there is an infinite `T ⊆ S` on which `c` is constant (every increasing `n`-tuple drawn
from `T` gets the same colour `b`). Proved by induction on the arity `n` via the classical
pre-homogeneous "reservoir" construction. -/
private theorem ramsey_infinite_subset :
    ∀ (n : ℕ) (c : (Fin n ↪o ℕ) → Bool) {S : Set ℕ}, S.Infinite →
    ∃ T ⊆ S, T.Infinite ∧ ∃ b, ∀ u : Fin n ↪o ℕ, (∀ k, u k ∈ T) → c u = b := by
  intro n
  induction n with
  | zero =>
    -- `Fin 0 ↪o ℕ` is a subsingleton, so any single colour works; take `T = S`.
    intro c S hS
    have hsub : Subsingleton (Fin 0 ↪o ℕ) :=
      ⟨fun u v => by apply RelEmbedding.ext; intro x; exact Fin.elim0 x⟩
    refine ⟨S, le_refl S, hS, c (Classical.choice ⟨OrderEmbedding.ofStrictMono Fin.elim0
      (fun p => Fin.elim0 p)⟩), ?_⟩
    intro u _
    rw [Subsingleton.elim u]
  | succ n IH =>
    intro c S hS
    -- Reservoir recursion: `R 0 = S`, and `R (k+1)` is the IH-homogeneous infinite subset
    -- of the tail-region of `R k` for the `n`-ary head-coloring at `a k = sInf (R k)`.
    let R : ℕ → {U : Set ℕ // U.Infinite} := fun k => Nat.rec ⟨S, hS⟩ (fun _ Rk =>
      ⟨(IH (headColoring c (sInf Rk.1)) (tailRegion_infinite Rk.2)).choose,
       (IH (headColoring c (sInf Rk.1)) (tailRegion_infinite Rk.2)).choose_spec.2.1⟩) k
    set a : ℕ → ℕ := fun k => sInf (R k).1 with ha_def
    set γ : ℕ → Bool := fun k =>
      (IH (headColoring c (sInf (R k).1)) (tailRegion_infinite (R k).2)).choose_spec.2.2.choose
      with hγ_def
    -- `R (k+1)` sits inside the tail-region of `R k`, and `c` of any head-`(a k)` extension
    -- of an `n`-tuple drawn from `R (k+1)` has the constant colour `γ k`.
    have hstep_sub : ∀ k, (R (k + 1)).1 ⊆ (R k).1 ∩ {x | a k < x} := fun k =>
      (IH (headColoring c (sInf (R k).1)) (tailRegion_infinite (R k).2)).choose_spec.1
    have hstep_homog : ∀ k (u : Fin n ↪o ℕ), (∀ j, u j ∈ (R (k + 1)).1) →
        headColoring c (a k) u = γ k := fun k u hu =>
      (IH (headColoring c (sInf (R k).1))
        (tailRegion_infinite (R k).2)).choose_spec.2.2.choose_spec u hu
    -- Nesting of reservoirs and monotonicity of the heads.
    have hnested : ∀ k, (R (k + 1)).1 ⊆ (R k).1 := fun k x hx => (hstep_sub k hx).1
    have hantitone : ∀ {i j : ℕ}, i ≤ j → (R j).1 ⊆ (R i).1 := by
      intro i j hij
      induction j with
      | zero => simp_all
      | succ k ih =>
        rcases Nat.lt_or_ge i (k + 1) with h | h
        · exact (hnested k).trans (ih (Nat.lt_succ_iff.mp h))
        · have : i = k + 1 := le_antisymm hij h
          subst this; rfl
    have ha_mem : ∀ k, a k ∈ (R k).1 := fun k => Nat.sInf_mem (R k).2.nonempty
    have ha_lt_succ : ∀ k, a k < a (k + 1) := fun k => (hstep_sub k (ha_mem (k + 1))).2
    have ha_mono : StrictMono a := strictMono_nat_of_lt_succ ha_lt_succ
    have ha_mem_res : ∀ {i j : ℕ}, i < j → a j ∈ (R (i + 1)).1 := fun {i j} hij =>
      hantitone hij (ha_mem j)
    -- Unary pigeonhole: the head-colour sequence `γ` is constant on an infinite index set.
    have hpigeon : ∃ (b : Bool) (I : Set ℕ), I.Infinite ∧ ∀ k ∈ I, γ k = b := by
      by_cases hT : {k | γ k = true}.Infinite
      · exact ⟨true, _, hT, fun k hk => hk⟩
      · refine ⟨false, {k | γ k = false}, ?_, fun k hk => hk⟩
        have hcover : {k | γ k = true} ∪ {k | γ k = false} = Set.univ := by
          ext k; cases γ k <;> simp
        have hunion : ({k | γ k = true} ∪ {k | γ k = false}).Infinite := by
          rw [hcover]; exact Set.infinite_univ
        exact (Set.infinite_union.mp hunion).resolve_left hT
    obtain ⟨b, I, hI_inf, hI_const⟩ := hpigeon
    refine ⟨a '' I, ?_, hI_inf.image (ha_mono.injective.injOn), b, ?_⟩
    · rintro _ ⟨k, _, rfl⟩
      exact hantitone (Nat.zero_le k) (ha_mem k)
    · -- Any increasing `(n+1)`-tuple `t` from `a '' I` is `(a (idx 0), …, a (idx n))` with
      -- `idx` strictly increasing and `idx 0 ∈ I`; its colour is `γ (idx 0) = b`.
      intro t ht
      have hidx : ∀ p, ∃ k ∈ I, a k = t p := fun p => ht p
      let idx : Fin (n + 1) → ℕ := fun p => (hidx p).choose
      have hidx_mem : ∀ p, idx p ∈ I := fun p => (hidx p).choose_spec.1
      have hidx_eq : ∀ p, a (idx p) = t p := fun p => (hidx p).choose_spec.2
      have hidx_mono : StrictMono idx := by
        intro p q hpq
        have : a (idx p) < a (idx q) := by rw [hidx_eq p, hidx_eq q]; exact t.lt_iff_lt.mpr hpq
        exact ha_mono.lt_iff_lt.mp this
      let w : Fin n ↪o ℕ := OrderEmbedding.ofStrictMono (fun j => t j.succ) (by
        intro p q hpq; exact t.lt_iff_lt.mpr (Fin.succ_lt_succ_iff.mpr hpq))
      have hw_lt : ∀ j, t 0 < w j := fun j => t.lt_iff_lt.mpr (Fin.succ_pos j)
      have ht_eq : t = consOEmb (t 0) w hw_lt := by
        apply RelEmbedding.ext
        intro p
        induction p using Fin.cases with
        | zero => rfl
        | succ j => rfl
      have h0 : t 0 = a (idx 0) := (hidx_eq 0).symm
      have hw_mem : ∀ j, w j ∈ (R (idx 0 + 1)).1 := by
        intro j
        show t j.succ ∈ (R (idx 0 + 1)).1
        rw [← hidx_eq j.succ]
        exact ha_mem_res (hidx_mono (Fin.succ_pos j))
      rw [ht_eq, ← headColoring_spec c (t 0) w hw_lt, h0]
      rw [hstep_homog (idx 0) w hw_mem]
      exact hI_const (idx 0) (hidx_mem 0)

/-- **Single-coloring finite-arity infinite Ramsey on `ℕ`.**

For any `Bool` coloring `c` of strictly-increasing `n`-tuples of `ℕ` (presented as order
embeddings `Fin n ↪o ℕ`), there is an order embedding `f : ℕ ↪o ℕ` such that `c` is constant on
all `n`-tuples drawn from the range of `f` (every such tuple has the form `u.trans f`).

This is the genuine combinatorial residual of the cheap Morley–Hanf route: it generalizes the
unary (`infinite_ramsey_unary_nat`) and pair (`infinite_ramsey_pair_nat`) cases in
`ErdosRado.lean` to all finite arities, and is provable by induction on `n`. It does **not**
require any beth/partition-calculus machinery. -/
theorem infinite_ramsey_nat_arity (n : ℕ) (c : (Fin n ↪o ℕ) → Bool) :
    ∃ f : ℕ ↪o ℕ, ∀ u v : Fin n ↪o ℕ, c (u.trans f) = c (v.trans f) := by
  -- Extract an infinite monochromatic `T ⊆ ℕ` from the set-form helper, then enumerate it.
  obtain ⟨T, -, hT_inf, b, hb⟩ := ramsey_infinite_subset n c (S := Set.univ) Set.infinite_univ
  let f : ℕ ↪o ℕ := OrderEmbedding.ofStrictMono (Nat.nth (· ∈ T)) (Nat.nth_strictMono hT_inf)
  have hf_mem : ∀ k, f k ∈ T := fun k => Nat.nth_mem_of_infinite hT_inf k
  refine ⟨f, fun u v => ?_⟩
  rw [hb (u.trans f) (fun k => hf_mem (u k)), hb (v.trans f) (fun k => hf_mem (v k))]
