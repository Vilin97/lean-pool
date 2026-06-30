/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Example43
import LeanPool.DomainTheory.Neighborhood.Exercise326
import LeanPool.DomainTheory.Neighborhood.Exercise511
import LeanPool.DomainTheory.Neighborhood.Theorem41
import LeanPool.DomainTheory.Neighborhood.ApproximableExercises
import Mathlib.Computability.PartrecBasis

/-!
# Theorem 5.6 (Scott 1981, PRG-19, §5) — the FULL closure: partial recursive ⟹
λ-definable

`Theorem56.lean` builds the constructive heart (strict starting functions, the
primitive-recursion
and μ combinators with their scheme equations). This file wires those pieces
together against
Mathlib's **arity-aware** inductive predicates `Nat.Primrec'`/`Nat.Partrec'` (over
`List.Vector ℕ n`),
whose constructors are *exactly* Scott's generation grammar:

* `Nat.Primrec'`: `zero`, `succ`, `get i` (projection), `comp`, `prec` (primitive
recursion);
* `Nat.Partrec'`: `prim`, `comp`, `rfind` (minimization).

We prove: every `Nat.Primrec'`/`Nat.Partrec'` function is denoted by an
approximable map
`φ : 𝒩 → N`, where `𝒩 := N^∞` (Exercise 3.16) is the **universal argument domain**
— a `k`-ary
function is realised by a single map that depends only on coordinates `0..k-1`.
The realisation is
*very strict* (Scott): `⊥` in any relevant coordinate forces `⊥`, which is what
makes composition and
minimisation compose. The capstone is `partrec_lamDef` and the 1-ary corollary
`partrec_one`.
-/

namespace Domain.Neighborhood.Theorem56Full

open Domain.Neighborhood NeighborhoodSystem ApproximableMap
open Domain.Neighborhood.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN)
open Domain.Neighborhood.Exercise326 (cond)
open Domain.Neighborhood.Exercise511 (head tail push)

/-- The universal argument domain `𝒩 = N^∞` (Exercise 3.16). All `k`-ary number
functions are
realised as approximable maps `𝒩 → N` depending only on coordinates `0..k-1`. -/
abbrev 𝒩 : NeighborhoodSystem (ℕ × ℕ) := iterSys N

/-- `T.bot = Example23.botElt` (both least); bridges `zeroMap_bot` (lands in
`T.bot`) with
`cond_bot`
(phrased with `Example23.botElt`). -/
theorem T_bot_eq : (Example43.T).bot = Example23.botElt :=
  le_antisymm ((Example43.T).bot_le _) (Example23.botElt_le _)

/-! ### Element builders. -/

/-- `none ↦ ⊥`, `some n ↦ n̂`. -/
def optElem : Option ℕ → N.Element
  | none => N.bot
  | some n => natElem n

/-- The argument element of `𝒩` whose first `n` coordinates are `optElem (a i)`
and the rest `⊥`. -/
def argElem {n : ℕ} (a : Fin n → Option ℕ) : 𝒩.Element :=
  ofSeq (fun i => if h : i < n then optElem (a ⟨i, h⟩) else N.bot)

/-- The argument element of `𝒩` carrying a `List.Vector ℕ n` in its first `n`
coordinates. -/
def vecElem {n : ℕ} (v : List.Vector ℕ n) : 𝒩.Element :=
  argElem (fun i => some (v.get i))

@[simp] theorem component_argElem {n : ℕ} (a : Fin n → Option ℕ) (i : ℕ) :
    component (argElem a) i = if h : i < n then optElem (a ⟨i, h⟩) else N.bot := by
  rw [argElem, component_ofSeq]

@[simp] theorem component_vecElem {n : ℕ} (v : List.Vector ℕ n) (i : ℕ) :
    component (vecElem v) i = if h : i < n then natElem (v.get ⟨i, h⟩) else N.bot := by
  rw [vecElem, component_argElem]; split <;> rfl

/-- Two `𝒩`-elements are equal iff all components agree. -/
theorem eq_of_component_eq {z z' : 𝒩.Element}
    (h : ∀ n, component z n = component z' n) : z = z' :=
  le_antisymm (le_of_component_le (fun n => (h n).le))
    (le_of_component_le (fun n => (h n).ge))

/-- A `𝒩`-element is *arg-like* if every coordinate is total or `⊥` (true of all
`argElem`). -/
def ArgLike (z : 𝒩.Element) : Prop := ∀ j, component z j = N.bot ∨ ∃ k, component z j = natElem k

theorem argElem_argLike {n : ℕ} (a : Fin n → Option ℕ) : ArgLike (argElem a) := by
  intro j
  rw [component_argElem]
  split
  · cases h : a _ with
    | none => exact Or.inl rfl
    | some k => exact Or.inr ⟨k, rfl⟩
  · exact Or.inl rfl

/-! ### Components through `push`. -/

theorem component_push_zero (x : N.Element) (s : 𝒩.Element) :
    component ((push N).toElementMap (pair x s)) 0 = x := by
  rw [← Exercise511.head_apply, Exercise511.head_push]

theorem component_push_succ (x : N.Element) (s : 𝒩.Element) (j : ℕ) :
    component ((push N).toElementMap (pair x s)) (j + 1) = component s j := by
  rw [← Exercise511.component_tail, Exercise511.tail_push]

/-! ### The strictifier `guard1`/`strictGuardN` (Scott's `cond(zero(x),·,·)`
device).

`guard1 j φ z = cond(zero(zⱼ), φ z, φ z)`: equals `φ z` when `zⱼ` is total, `⊥`
when `zⱼ = ⊥`.
Composing the guards for `j = 0..n-1` makes a map *very strict* in its first `n`
coordinates. -/

/-- Test coordinate `j`: `cond(zero(zⱼ), φ z, φ z)`. -/
def guard1 (j : ℕ) (φ : ApproximableMap 𝒩 N) : ApproximableMap 𝒩 N :=
  (cond N).comp (paired (zeroMap.comp (projN N j)) (paired φ φ))

theorem guard1_apply (j : ℕ) (φ : ApproximableMap 𝒩 N) (z : 𝒩.Element) :
    (guard1 j φ).toElementMap z =
      (cond N).toElementMap (pair (zeroMap.toElementMap (component z j))
        (pair (φ.toElementMap z) (φ.toElementMap z))) := by
  rw [guard1, toElementMap_comp]
  simp only [toElementMap_paired, toElementMap_comp, toElementMap_projN]

theorem guard1_total (j : ℕ) (φ : ApproximableMap 𝒩 N) (z : 𝒩.Element) {k : ℕ}
    (h : component z j = natElem k) : (guard1 j φ).toElementMap z = φ.toElementMap z := by
  rw [guard1_apply, h]
  cases k with
  | zero => rw [zeroMap_natElem_zero, Exercise326.cond_true]
  | succ m => rw [zeroMap_natElem_succ, Exercise326.cond_false]

theorem guard1_bot (j : ℕ) (φ : ApproximableMap 𝒩 N) (z : 𝒩.Element)
    (h : component z j = N.bot) : (guard1 j φ).toElementMap z = N.bot := by
  rw [guard1_apply, h, zeroMap_bot, T_bot_eq, Exercise326.cond_bot]

/-- If `φ z = ⊥` and `zⱼ` is total-or-`⊥`, the guard stays `⊥`. -/
theorem guard1_inner_bot (j : ℕ) (φ : ApproximableMap 𝒩 N) (z : 𝒩.Element)
    (hz : component z j = N.bot ∨ ∃ k, component z j = natElem k)
    (h : φ.toElementMap z = N.bot) : (guard1 j φ).toElementMap z = N.bot := by
  rcases hz with hb | ⟨k, hk⟩
  · exact guard1_bot j φ z hb
  · rw [guard1_apply, hk, h]
    cases k with
    | zero => rw [zeroMap_natElem_zero, Exercise326.cond_true]
    | succ m => rw [zeroMap_natElem_succ, Exercise326.cond_false]

/-- Test coordinates `0..n-1`. -/
def strictGuardN : ℕ → ApproximableMap 𝒩 N → ApproximableMap 𝒩 N
  | 0, φ => φ
  | n + 1, φ => guard1 n (strictGuardN n φ)

/-- On arguments whose first `n` coordinates are all total, the guard is
transparent. -/
theorem strictGuardN_total (n : ℕ) (φ : ApproximableMap 𝒩 N) (z : 𝒩.Element)
    (h : ∀ j, j < n → ∃ k, component z j = natElem k) :
    (strictGuardN n φ).toElementMap z = φ.toElementMap z := by
  induction n with
  | zero => rfl
  | succ m ih =>
    obtain ⟨k, hk⟩ := h m (Nat.lt_succ_self m)
    rw [strictGuardN, guard1_total m _ z hk]
    exact ih (fun j hj => h j (Nat.lt_succ_of_lt hj))

/-- If some coordinate `i < n` is `⊥` (and `z` is arg-like), the guard forces `⊥`. -/
theorem strictGuardN_strict (n : ℕ) (φ : ApproximableMap 𝒩 N) (z : 𝒩.Element)
    (hz : ArgLike z) {i : ℕ} (hi : i < n) (hb : component z i = N.bot) :
    (strictGuardN n φ).toElementMap z = N.bot := by
  induction n with
  | zero => exact absurd hi (Nat.not_lt_zero i)
  | succ m ih =>
    rw [strictGuardN]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · exact guard1_inner_bot m _ z (hz m) (ih hlt)
    · exact guard1_bot m _ z (heq ▸ hb)

/-! ### `tupleMap`: assemble `n` scalar maps into the first `n` coordinates of
`𝒩`. -/

/-- `⟨g₀, …, g_{n-1}⟩ : 𝒩 → 𝒩` placing `gᵢ` at coordinate `i` (`< n`) and `⊥`
beyond. -/
def tupleMap : (n : ℕ) → (Fin n → ApproximableMap 𝒩 N) → ApproximableMap 𝒩 𝒩
  | 0, _ => constMap 𝒩 𝒩.bot
  | n + 1, gs => (push N).comp (paired (gs 0) (tupleMap n (fun i => gs i.succ)))

theorem tupleMap_succ (n : ℕ) (gs : Fin (n + 1) → ApproximableMap 𝒩 N) :
    tupleMap (n + 1) gs = (push N).comp (paired (gs 0) (tupleMap n (fun i => gs i.succ))) := rfl

/-- Coordinate `i < n` of the tuple is exactly `gᵢ`. -/
theorem component_tupleMap : ∀ (n : ℕ) (gs : Fin n → ApproximableMap 𝒩 N) (z : 𝒩.Element)
    (i : ℕ) (hi : i < n),
    component ((tupleMap n gs).toElementMap z) i = (gs ⟨i, hi⟩).toElementMap z
  | 0, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, gs, z, 0, hi => by
      rw [tupleMap_succ, toElementMap_comp, toElementMap_paired, component_push_zero]
      exact congrArg (fun w => (gs w).toElementMap z) (Fin.ext (by simp))
  | n + 1, gs, z, i + 1, hi => by
      rw [tupleMap_succ, toElementMap_comp, toElementMap_paired, component_push_succ,
        component_tupleMap n (fun j => gs j.succ) z i (Nat.lt_of_succ_lt_succ hi)]
      rfl

/-! ### The λ-definability specification. -/

/-- `φ : 𝒩 → N` realises the `n`-ary partial function `f` (a *very strict*
λ-definition):
`φ` returns `f`'s value on total arguments, `⊥` where `f` is undefined, and `⊥` on
*any* arg-like
input with a `⊥` among its first `n` coordinates. -/
structure LamDef {n : ℕ} (φ : ApproximableMap 𝒩 N) (f : List.Vector ℕ n →. ℕ) : Prop where
  defined : ∀ (v : List.Vector ℕ n) (c : ℕ), c ∈ f v → φ.toElementMap (vecElem v) = natElem c
  undef : ∀ (v : List.Vector ℕ n), ¬ (f v).Dom → φ.toElementMap (vecElem v) = N.bot
  strict : ∀ (z : 𝒩.Element), ArgLike z → ∀ i, i < n → component z i = N.bot →
    φ.toElementMap z = N.bot

/-- Every coordinate `j < n` of `vecElem v` is the total `v.get j`. -/
theorem component_vecElem_lt {n : ℕ} (v : List.Vector ℕ n) {j : ℕ} (hj : j < n) :
    component (vecElem v) j = natElem (v.get ⟨j, hj⟩) := by
  rw [component_vecElem, dif_pos hj]

/-- `vecElem v` has total coordinates throughout its arity. -/
theorem vecElem_totals {n : ℕ} (v : List.Vector ℕ n) :
    ∀ j, j < n → ∃ k, component (vecElem v) j = natElem k :=
  fun j hj => ⟨v.get ⟨j, hj⟩, component_vecElem_lt v hj⟩

/-- A coordinate that an `argElem` sets to `none` is `⊥`. -/
theorem component_argElem_none {n : ℕ} (a : Fin n → Option ℕ) (i : Fin n) (hi : a i = none) :
    component (argElem a) (i : ℕ) = N.bot := by
  rw [component_argElem, dif_pos i.isLt, Fin.eta, hi]; rfl

/-- **Master constructor.** Wrapping an `inner` map (correct on total arguments)
in `strictGuardN n`
yields a full, very strict λ-definition. The `strict` clause is then automatic. -/
theorem lamDef_of_inner {n : ℕ} (inner : ApproximableMap 𝒩 N) (f : List.Vector ℕ n →. ℕ)
    (hdef : ∀ (v : List.Vector ℕ n) (c : ℕ), c ∈ f v → inner.toElementMap (vecElem v) = natElem c)
    (hundef : ∀ (v : List.Vector ℕ n), ¬ (f v).Dom → inner.toElementMap (vecElem v) = N.bot) :
    LamDef (strictGuardN n inner) f where
  defined v c hc := by
    rw [strictGuardN_total n inner (vecElem v) (vecElem_totals v)]; exact hdef v c hc
  undef v hv := by
    rw [strictGuardN_total n inner (vecElem v) (vecElem_totals v)]; exact hundef v hv
  strict z hz i hi hb := strictGuardN_strict n inner z hz hi hb

/-- The total-function specialisation of `lamDef_of_inner`. -/
theorem lamDef_total {n : ℕ} (ψ : ApproximableMap 𝒩 N) (g : List.Vector ℕ n → ℕ)
    (hval : ∀ v, ψ.toElementMap (vecElem v) = natElem (g v)) :
    LamDef (strictGuardN n ψ) (g : List.Vector ℕ n →. ℕ) :=
  lamDef_of_inner ψ _
    (fun v c hc => by rw [PFun.coe_val, Part.mem_some_iff] at hc; rw [hval, ← hc])
    (fun v hv => by rw [PFun.coe_val] at hv; exact absurd trivial hv)

/-! ### Primitive recursive base cases: `zero`, `succ`, `get`. -/

/-- `zero : Vector ℕ 0 → ℕ`, the constant `0` (nullary). -/
theorem lamDef_zero : LamDef (strictGuardN 0 (constMap 𝒩 (natElem 0)))
    ((fun _ => 0 : List.Vector ℕ 0 → ℕ) : List.Vector ℕ 0 →. ℕ) :=
  lamDef_total (constMap 𝒩 (natElem 0)) _ (fun v => by rw [toElementMap_constMap])

/-- `succ : Vector ℕ 1 → ℕ`, `v ↦ v.head + 1`. -/
theorem lamDef_succ : LamDef (strictGuardN 1 (succMap.comp (projN N 0)))
    ((fun v => Nat.succ v.head : List.Vector ℕ 1 → ℕ) : List.Vector ℕ 1 →. ℕ) :=
  lamDef_total _ _ (fun v => by
    rw [toElementMap_comp, toElementMap_projN, component_vecElem_lt v (by norm_num),
      succMap_natElem]
    congr 1
    simp [List.Vector.get_zero])

/-- `get i : Vector ℕ n → ℕ`, the `i`-th projection. -/
theorem lamDef_get {n : ℕ} (i : Fin n) :
    LamDef (strictGuardN n (projN N i))
      ((fun v => v.get i : List.Vector ℕ n → ℕ) : List.Vector ℕ n →. ℕ) :=
  lamDef_total _ _ (fun v => by
    rw [toElementMap_projN, component_vecElem_lt v i.isLt, Fin.eta])

/-- Transport a λ-definition along pointwise equality of the realised function. -/
theorem lamDef_congr {n : ℕ} {φ : ApproximableMap 𝒩 N} {f f' : List.Vector ℕ n →. ℕ}
    (h : ∀ v, f v = f' v) (hf : LamDef φ f) : LamDef φ f' where
  defined v c hc := hf.defined v c (by rw [h v]; exact hc)
  undef v hv := hf.undef v (by rw [h v]; exact hv)
  strict := hf.strict

/-- The value a realiser takes on a total argument is total-or-`⊥` (arg-like). -/
theorem realizer_value {n : ℕ} {φ : ApproximableMap 𝒩 N} {f : List.Vector ℕ n →. ℕ}
    (h : LamDef φ f) (v : List.Vector ℕ n) :
    φ.toElementMap (vecElem v) = N.bot ∨ ∃ k, φ.toElementMap (vecElem v) = natElem k := by
  by_cases hd : (f v).Dom
  · exact Or.inr ⟨(f v).get hd, h.defined v _ (Part.get_mem hd)⟩
  · exact Or.inl (h.undef v hd)

/-! ### Composition. -/

/-- Coordinates of the bottom stack are `⊥`. -/
theorem component_bot (i : ℕ) : component (𝒩.bot) i = N.bot := by
  have hbot : (𝒩.bot) = ofSeq (fun _ => N.bot) :=
    le_antisymm (𝒩.bot_le _)
      (le_of_component_le (fun i => by rw [component_ofSeq]; exact N.bot_le _))
  rw [hbot, component_ofSeq]

theorem tupleMap_zero (gs : Fin 0 → ApproximableMap 𝒩 N) :
    tupleMap 0 gs = constMap 𝒩 𝒩.bot := rfl

/-- Coordinates `≥ n` of the tuple are `⊥`. -/
theorem component_tupleMap_ge : ∀ (n : ℕ) (gs : Fin n → ApproximableMap 𝒩 N) (z : 𝒩.Element)
    (i : ℕ), n ≤ i → component ((tupleMap n gs).toElementMap z) i = N.bot
  | 0, gs, z, i, _ => by rw [tupleMap_zero, toElementMap_constMap, component_bot]
  | n + 1, gs, z, i, hi => by
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [tupleMap_succ, toElementMap_comp, toElementMap_paired, component_push_succ]
      exact component_tupleMap_ge n (fun k => gs k.succ) z j (by omega)

/-- The tuple of realisers, applied to a total argument, equals `vecElem w` where
`wᵢ = gᵢ(v)`. -/
theorem tupleMap_vecElem_eq {m nn : ℕ} (φg : Fin nn → ApproximableMap 𝒩 N)
    (g : Fin nn → List.Vector ℕ m →. ℕ) (hg : ∀ i, LamDef (φg i) (g i))
    (v : List.Vector ℕ m) (w : List.Vector ℕ nn) (hw : ∀ i, w.get i ∈ g i v) :
    (tupleMap nn φg).toElementMap (vecElem v) = vecElem w := by
  apply eq_of_component_eq
  intro i
  by_cases hi : i < nn
  · rw [component_tupleMap nn φg (vecElem v) i hi, component_vecElem_lt w hi]
    exact (hg ⟨i, hi⟩).defined v (w.get ⟨i, hi⟩) (hw ⟨i, hi⟩)
  · rw [component_tupleMap_ge nn φg (vecElem v) i (Nat.le_of_not_lt hi), component_vecElem,
      dif_neg hi]

/-- The tuple of realisers, applied to a total argument, is arg-like. -/
theorem tupleMap_argLike {m nn : ℕ} (φg : Fin nn → ApproximableMap 𝒩 N)
    (g : Fin nn → List.Vector ℕ m →. ℕ) (hg : ∀ i, LamDef (φg i) (g i)) (v : List.Vector ℕ m) :
    ArgLike ((tupleMap nn φg).toElementMap (vecElem v)) := by
  intro i
  by_cases hi : i < nn
  · rw [component_tupleMap nn φg (vecElem v) i hi]; exact realizer_value (hg ⟨i, hi⟩) v
  · rw [component_tupleMap_ge nn φg (vecElem v) i (Nat.le_of_not_lt hi)]; exact Or.inl rfl

/-- Membership in `mOfFn` (Part monad): a vector is produced iff each coordinate
is a value. -/
theorem mem_mOfFn : ∀ {n : ℕ} (p : Fin n → Part ℕ) (w : List.Vector ℕ n),
    w ∈ List.Vector.mOfFn p ↔ ∀ i, w.get i ∈ p i
  | 0, p, w => by
      constructor
      · intro _ i; exact i.elim0
      · intro _
        change w ∈ (pure List.Vector.nil : Part _)
        rw [Part.pure_eq_some, Part.mem_some_iff]
        exact List.Vector.eq_nil w
  | n + 1, p, w => by
      have hmof : List.Vector.mOfFn p
          = (p 0).bind (fun a => (List.Vector.mOfFn fun i => p i.succ).bind
              (fun u => Part.some (a ::ᵥ u))) := by
        simp only [List.Vector.mOfFn, Part.bind_eq_bind, Part.pure_eq_some]
      rw [hmof, Part.mem_bind_iff]
      constructor
      · rintro ⟨a, ha, hrest⟩
        rw [Part.mem_bind_iff] at hrest
        obtain ⟨u, hu, hw⟩ := hrest
        rw [Part.mem_some_iff] at hw
        subst hw
        have hu' := (mem_mOfFn (fun i => p i.succ) u).mp hu
        intro i
        refine Fin.cases ?_ ?_ i
        · simpa using ha
        · intro k; simpa using hu' k
      · intro hall
        refine ⟨w.head, ?_, ?_⟩
        · have := hall 0; rwa [List.Vector.get_zero] at this
        · rw [Part.mem_bind_iff]
          refine ⟨w.tail, (mem_mOfFn (fun i => p i.succ) w.tail).mpr (fun k => ?_), ?_⟩
          · have h := hall k.succ
            rwa [← List.Vector.get_tail_succ w k] at h
          · rw [Part.mem_some_iff]; exact (List.Vector.cons_head_tail w).symm

/-- **Composition** (Scott's multivariate composition). If `f` and each `gᵢ` are
λ-defined, so is
`v ↦ (⟨g₀ v, …, g_{nn-1} v⟩) >>= f`. -/
theorem lamDef_comp {m nn : ℕ} (f : List.Vector ℕ nn →. ℕ) (g : Fin nn → List.Vector ℕ m →. ℕ)
    (φf : ApproximableMap 𝒩 N) (hf : LamDef φf f)
    (φg : Fin nn → ApproximableMap 𝒩 N) (hg : ∀ i, LamDef (φg i) (g i)) :
    LamDef (strictGuardN m (φf.comp (tupleMap nn φg)))
      (fun v => (List.Vector.mOfFn fun i => g i v) >>= f) := by
  refine lamDef_of_inner (φf.comp (tupleMap nn φg)) _ ?_ ?_
  · intro v c hc
    rw [Part.bind_eq_bind, Part.mem_bind_iff] at hc
    obtain ⟨w, hw, hcw⟩ := hc
    rw [toElementMap_comp, tupleMap_vecElem_eq φg g hg v w ((mem_mOfFn _ w).mp hw)]
    exact hf.defined w c hcw
  · intro v hv
    rw [toElementMap_comp]
    by_cases hall : ∀ i, (g i v).Dom
    · set w : List.Vector ℕ nn := List.Vector.ofFn (fun i => (g i v).get (hall i)) with hw_def
      have hwget : ∀ i, w.get i ∈ g i v := by
        intro i; rw [hw_def, List.Vector.get_ofFn]; exact Part.get_mem (hall i)
      rw [tupleMap_vecElem_eq φg g hg v w hwget]
      refine hf.undef w (fun hfw => hv ?_)
      have hmem : (f w).get hfw ∈ (List.Vector.mOfFn fun i => g i v) >>= f := by
        rw [Part.bind_eq_bind, Part.mem_bind_iff]
        exact ⟨w, (mem_mOfFn _ w).mpr hwget, Part.get_mem hfw⟩
      exact Part.dom_iff_mem.mpr ⟨_, hmem⟩
    · rw [not_forall] at hall
      obtain ⟨j, hj⟩ := hall
      refine hf.strict ((tupleMap nn φg).toElementMap (vecElem v))
        (tupleMap_argLike φg g hg v) j j.isLt ?_
      rw [component_tupleMap nn φg (vecElem v) j j.isLt, Fin.eta]
      exact (hg j).undef v hj

/-- A realiser of a total function evaluates to its value. -/
theorem lamDef_coe_val {n : ℕ} {φ : ApproximableMap 𝒩 N} {g : List.Vector ℕ n → ℕ}
    (h : LamDef φ (g : List.Vector ℕ n →. ℕ)) (v : List.Vector ℕ n) :
    φ.toElementMap (vecElem v) = natElem (g v) :=
  h.defined v (g v) (by rw [PFun.coe_val]; exact Part.mem_some _)

/-- **Composition of total functions** (the `Nat.Primrec'.comp` shape). -/
theorem lamDef_primComp {m nn : ℕ} (f₀ : List.Vector ℕ nn → ℕ)
    (g₀ : Fin nn → List.Vector ℕ m → ℕ)
    (φf : ApproximableMap 𝒩 N) (hf : LamDef φf (f₀ : List.Vector ℕ nn →. ℕ))
    (φg : Fin nn → ApproximableMap 𝒩 N) (hg : ∀ i, LamDef (φg i) (g₀ i : List.Vector ℕ m →. ℕ)) :
    LamDef (strictGuardN m (φf.comp (tupleMap nn φg)))
      ((fun a => f₀ (List.Vector.ofFn fun i => g₀ i a) : List.Vector ℕ m → ℕ) :
        List.Vector ℕ m →. ℕ) := by
  refine lamDef_congr (fun v => ?_)
    (lamDef_comp (f₀ : _ →. ℕ) (fun i => (g₀ i : _ →. ℕ)) φf hf φg hg)
  simp only [PFun.coe_val, Vector.mOfFn_part_some, Part.bind_eq_bind, Part.bind_some]

/-! ### `vecElem` of a cons is a `push`. -/

theorem push_natElem_vecElem {n : ℕ} (a : ℕ) (u : List.Vector ℕ n) :
    (push N).toElementMap (pair (natElem a) (vecElem u)) = vecElem (a ::ᵥ u) := by
  apply eq_of_component_eq
  intro j
  cases j with
  | zero =>
    rw [component_push_zero, component_vecElem, dif_pos (Nat.succ_pos n)]
    exact congrArg natElem (List.Vector.get_cons_zero a u).symm
  | succ k =>
    rw [component_push_succ, component_vecElem, component_vecElem]
    by_cases hk : k < n
    · rw [dif_pos hk, dif_pos (show k + 1 < n + 1 by omega)]
      exact congrArg natElem (List.Vector.get_cons_succ a u ⟨k, hk⟩).symm
    · rw [dif_neg hk, dif_neg (show ¬ k + 1 < n + 1 by omega)]

/-! ### Primitive recursion.

The recursion lives over `prod (funSpace 𝒩 N) 𝒩`: `k` is the unknown, `z` the
argument stack whose
head is the recursion variable and whose tail carries the parameters. The body is
`M(k, z) = cond(zero(head z), f(tail z), g(⟨pred(head z), ⟨k(⟨pred(head z), tail
z⟩), tail z⟩⟩))`. -/

section Prec

variable (φf φg : ApproximableMap 𝒩 N)

/-- The primitive-recursion body. -/
def precBody : ApproximableMap (prod (funSpace 𝒩 N) 𝒩) N :=
  (cond N).comp
    (paired (zeroMap.comp ((head N).comp (proj₁ (funSpace 𝒩 N) 𝒩)))
      (paired (φf.comp ((tail N).comp (proj₁ (funSpace 𝒩 N) 𝒩)))
        (φg.comp
          ((push N).comp
            (paired (predMap.comp ((head N).comp (proj₁ (funSpace 𝒩 N) 𝒩)))
              ((push N).comp
                (paired
                  ((evalMap 𝒩 N).comp
                    (paired (proj₀ (funSpace 𝒩 N) 𝒩)
                      ((push N).comp
                        (paired (predMap.comp ((head N).comp (proj₁ (funSpace 𝒩 N) 𝒩)))
                          ((tail N).comp (proj₁ (funSpace 𝒩 N) 𝒩))))))
                  ((tail N).comp (proj₁ (funSpace 𝒩 N) 𝒩)))))))))

theorem precBody_apply (k : (funSpace 𝒩 N).Element) (z : 𝒩.Element) :
    (precBody φf φg).toElementMap (pair k z) =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap ((head N).toElementMap z))
          (pair (φf.toElementMap ((tail N).toElementMap z))
            (φg.toElementMap
              ((push N).toElementMap
                (pair (predMap.toElementMap ((head N).toElementMap z))
                  ((push N).toElementMap
                    (pair ((toApproxMap k).toElementMap
                            ((push N).toElementMap
                              (pair (predMap.toElementMap ((head N).toElementMap z))
                                ((tail N).toElementMap z))))
                      ((tail N).toElementMap z)))))))) := by
  rw [precBody, toElementMap_comp]
  simp only [toElementMap_paired, toElementMap_comp, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair, evalMap_apply]

/-- The primitive-recursion operator `R(k) = λz. …`. -/
def recOp : ApproximableMap (funSpace 𝒩 N) (funSpace 𝒩 N) := curry (precBody φf φg)

/-- `recMap : 𝒩 → N`, the least fixed point of `recOp` (before strictifying). -/
def recMap : ApproximableMap 𝒩 N := toApproxMap (recOp φf φg).fixElement

/-- The defining recursion equation. -/
theorem recMap_rec (z : 𝒩.Element) :
    (recMap φf φg).toElementMap z =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap ((head N).toElementMap z))
          (pair (φf.toElementMap ((tail N).toElementMap z))
            (φg.toElementMap
              ((push N).toElementMap
                (pair (predMap.toElementMap ((head N).toElementMap z))
                  ((push N).toElementMap
                    (pair ((recMap φf φg).toElementMap
                            ((push N).toElementMap
                              (pair (predMap.toElementMap ((head N).toElementMap z))
                                ((tail N).toElementMap z))))
                      ((tail N).toElementMap z)))))))) := by
  have hfix : (recOp φf φg).toElementMap (recOp φf φg).fixElement = (recOp φf φg).fixElement :=
    toElementMap_fixElement (recOp φf φg)
  have hval := toElementMap_curry_apply (precBody φf φg) (recOp φf φg).fixElement z
  rw [← recOp, hfix] at hval
  rw [recMap, hval, precBody_apply]

/-- **Primitive recursion computes.** `recMap(⟨d, u⟩) = (Nat.rec (f u) (g …) d)`. -/
theorem recMap_eval {n : ℕ} (f₀ : List.Vector ℕ n → ℕ) (g₀ : List.Vector ℕ (n + 2) → ℕ)
    (hf : LamDef φf (f₀ : List.Vector ℕ n →. ℕ)) (hg : LamDef φg (g₀ : List.Vector ℕ (n + 2) →. ℕ))
    (u : List.Vector ℕ n) (d : ℕ) :
    (recMap φf φg).toElementMap (vecElem (d ::ᵥ u))
      = natElem (Nat.rec (motive := fun _ => ℕ) (f₀ u)
          (fun y IH => g₀ (y ::ᵥ IH ::ᵥ u)) d) := by
  induction d with
  | zero =>
    rw [← push_natElem_vecElem, recMap_rec, Exercise511.head_push, Exercise511.tail_push,
      zeroMap_natElem_zero, Exercise326.cond_true]
    exact lamDef_coe_val hf u
  | succ d ih =>
    rw [← push_natElem_vecElem, recMap_rec, Exercise511.head_push, Exercise511.tail_push,
      zeroMap_natElem_succ, Exercise326.cond_false, predMap_natElem_succ, push_natElem_vecElem, ih,
      push_natElem_vecElem, push_natElem_vecElem]
    exact lamDef_coe_val hg _

/-- **Primitive recursion** (`Nat.Primrec'.prec` shape). -/
theorem lamDef_prec {n : ℕ} (f₀ : List.Vector ℕ n → ℕ) (g₀ : List.Vector ℕ (n + 2) → ℕ)
    (hf : LamDef φf (f₀ : List.Vector ℕ n →. ℕ))
    (hg : LamDef φg (g₀ : List.Vector ℕ (n + 2) →. ℕ)) :
    LamDef (strictGuardN (n + 1) (recMap φf φg))
      (((fun v : List.Vector ℕ (n + 1) =>
        v.head.rec (f₀ v.tail) fun y IH => g₀ (y ::ᵥ IH ::ᵥ v.tail)) :
        List.Vector ℕ (n + 1) → ℕ) : List.Vector ℕ (n + 1) →. ℕ) := by
  refine lamDef_of_inner (recMap φf φg) _ (fun v c hc => ?_)
    (fun v hv => by rw [PFun.coe_val] at hv; exact absurd trivial hv)
  rw [PFun.coe_val, Part.mem_some_iff] at hc
  subst hc
  obtain ⟨d, u, rfl⟩ := List.Vector.exists_eq_cons v
  rw [List.Vector.head_cons, List.Vector.tail_cons]
  exact recMap_eval φf φg f₀ g₀ hf hg u d

end Prec

/-! ### Closure of the primitive recursive functions. -/

/-- **Every `Nat.Primrec'` function is λ-definable** by a (very strict)
approximable map. -/
theorem primrec_lamDef {n : ℕ} {f : List.Vector ℕ n → ℕ} (h : Nat.Primrec' f) :
    ∃ φ : ApproximableMap 𝒩 N, LamDef φ (f : List.Vector ℕ n →. ℕ) := by
  induction h with
  | zero => exact ⟨_, lamDef_zero⟩
  | succ => exact ⟨_, lamDef_succ⟩
  | get i => exact ⟨_, lamDef_get i⟩
  | comp g _ _ ihf ihg =>
      obtain ⟨φf, hφf⟩ := ihf
      choose φg hφg using ihg
      exact ⟨_, lamDef_primComp _ g φf hφf φg hφg⟩
  | prec _ _ ihf ihg =>
      obtain ⟨φf, hφf⟩ := ihf
      obtain ⟨φg, hφg⟩ := ihg
      exact ⟨_, lamDef_prec φf φg _ _ hφf hφg⟩

/-! ### Minimisation (`rfind`).

The μ-operator searches *upward* for the least `k` with `f(k ::ᵥ v) = 0`. We carry
the counter in the
head coordinate of the stack. The search body over `prod (funSpace 𝒩 N) 𝒩` is

  `S(k, z) = cond(zero(f z), head z, k(push(succ(head z), tail z)))` :

if the current value `f z` is `0`, return the counter `head z`; otherwise recurse
with the counter
bumped by one. `searchMap` is the least fixed point, and `findMap` kicks the
search off at counter `0`.
The hard direction is **divergence**: when no `k` zeroes `f`, every finite
approximant `Sⁿ(⊥)` returns
`⊥` along the search trace, so the directed sup (Theorem 4.2(iii)) is `⊥` too. -/

section Rfind

variable (φf : ApproximableMap 𝒩 N)

/-- The search body `S(k, z) = cond(zero(f z), head z, k(push(succ(head z), tail
z)))`. -/
def findBody : ApproximableMap (prod (funSpace 𝒩 N) 𝒩) N :=
  (cond N).comp
    (paired (zeroMap.comp (φf.comp (proj₁ (funSpace 𝒩 N) 𝒩)))
      (paired ((head N).comp (proj₁ (funSpace 𝒩 N) 𝒩))
        ((evalMap 𝒩 N).comp
          (paired (proj₀ (funSpace 𝒩 N) 𝒩)
            ((push N).comp
              (paired (succMap.comp ((head N).comp (proj₁ (funSpace 𝒩 N) 𝒩)))
                ((tail N).comp (proj₁ (funSpace 𝒩 N) 𝒩))))))))

theorem findBody_apply (k : (funSpace 𝒩 N).Element) (z : 𝒩.Element) :
    (findBody φf).toElementMap (pair k z) =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap (φf.toElementMap z))
          (pair ((head N).toElementMap z)
            ((toApproxMap k).toElementMap
              ((push N).toElementMap
                (pair (succMap.toElementMap ((head N).toElementMap z))
                  ((tail N).toElementMap z)))))) := by
  rw [findBody, toElementMap_comp]
  simp only [toElementMap_paired, toElementMap_comp, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair, evalMap_apply]

/-- The search operator `S(k) = λz. …`, whose least fixed point is the running
search. -/
def findOp : ApproximableMap (funSpace 𝒩 N) (funSpace 𝒩 N) := curry (findBody φf)

/-- `searchMap : 𝒩 → N`, the least fixed point of `findOp` (the counter lives in
coordinate `0`). -/
def searchMap : ApproximableMap 𝒩 N := toApproxMap (findOp φf).fixElement

/-- The defining recursion equation of the search. -/
theorem searchMap_rec (z : 𝒩.Element) :
    (searchMap φf).toElementMap z =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap (φf.toElementMap z))
          (pair ((head N).toElementMap z)
            ((searchMap φf).toElementMap
              ((push N).toElementMap
                (pair (succMap.toElementMap ((head N).toElementMap z))
                  ((tail N).toElementMap z)))))) := by
  have hfix : (findOp φf).toElementMap (findOp φf).fixElement = (findOp φf).fixElement :=
    toElementMap_fixElement (findOp φf)
  have hval := toElementMap_curry_apply (findBody φf) (findOp φf).fixElement z
  rw [← findOp, hfix] at hval
  rw [searchMap, hval, findBody_apply]

/-- `findMap : 𝒩 → N` starts the search with counter `0`. -/
def findMap : ApproximableMap 𝒩 N :=
  (searchMap φf).comp ((push N).comp (paired (constMap 𝒩 (natElem 0)) (idMap 𝒩)))

theorem findMap_vecElem {n : ℕ} (v : List.Vector ℕ n) :
    (findMap φf).toElementMap (vecElem v) = (searchMap φf).toElementMap (vecElem (0 ::ᵥ v)) := by
  rw [findMap, toElementMap_comp, toElementMap_comp, toElementMap_paired, toElementMap_constMap,
    toElementMap_idMap, push_natElem_vecElem]

/-- **Search step (found).** If `f(k ::ᵥ v) = 0`, the search returns the counter
`k`. -/
theorem searchMap_step_found {n : ℕ} {f : List.Vector ℕ (n + 1) → ℕ}
    (hf : LamDef φf (f : List.Vector ℕ (n + 1) →. ℕ)) (v : List.Vector ℕ n) (k : ℕ)
    (h0 : f (k ::ᵥ v) = 0) :
    (searchMap φf).toElementMap (vecElem (k ::ᵥ v)) = natElem k := by
  rw [← push_natElem_vecElem, searchMap_rec, Exercise511.head_push, Exercise511.tail_push,
    push_natElem_vecElem, lamDef_coe_val hf (k ::ᵥ v), h0, zeroMap_natElem_zero,
    Exercise326.cond_true]

/-- **Search step (continue).** If `f(k ::ᵥ v) ≠ 0`, the search advances to
counter `k + 1`. -/
theorem searchMap_step_next {n : ℕ} {f : List.Vector ℕ (n + 1) → ℕ}
    (hf : LamDef φf (f : List.Vector ℕ (n + 1) →. ℕ)) (v : List.Vector ℕ n) (k : ℕ)
    (hne : f (k ::ᵥ v) ≠ 0) :
    (searchMap φf).toElementMap (vecElem (k ::ᵥ v)) =
      (searchMap φf).toElementMap (vecElem ((k + 1) ::ᵥ v)) := by
  obtain ⟨m, hm⟩ : ∃ m, f (k ::ᵥ v) = m + 1 := ⟨f (k ::ᵥ v) - 1, by omega⟩
  rw [← push_natElem_vecElem, searchMap_rec, Exercise511.head_push, Exercise511.tail_push,
    push_natElem_vecElem, lamDef_coe_val hf (k ::ᵥ v), hm, zeroMap_natElem_succ,
    Exercise326.cond_false, succMap_natElem, push_natElem_vecElem]

/-- **Capstone (least zero ⟹ value).** If `m` is a zero of `f(· ::ᵥ v)` and
nothing below it is,
then
starting from any counter `j ≤ m` the search returns `m`. (Downward induction on
`m - j`.) -/
theorem searchMap_climb {n : ℕ} {f : List.Vector ℕ (n + 1) → ℕ}
    (hf : LamDef φf (f : List.Vector ℕ (n + 1) →. ℕ)) (v : List.Vector ℕ n) (m : ℕ)
    (hm0 : f (m ::ᵥ v) = 0) (hmin : ∀ i, i < m → f (i ::ᵥ v) ≠ 0) :
    ∀ d j, j + d = m → (searchMap φf).toElementMap (vecElem (j ::ᵥ v)) = natElem m := by
  intro d
  induction d with
  | zero =>
    intro j hj
    have hjm : j = m := by omega
    rw [hjm]
    exact searchMap_step_found φf hf v m hm0
  | succ d ih =>
    intro j hj
    have hjm : j < m := by omega
    rw [searchMap_step_next φf hf v j (hmin j hjm)]
    exact ih (j + 1) (by omega)

/-! #### Divergence via the directed sup of approximants. -/

/-- The least map of the function space evaluates to `⊥` everywhere. -/
theorem toApproxMap_bot (z : 𝒩.Element) :
    (toApproxMap ((funSpace 𝒩 N).bot)).toElementMap z = N.bot := by
  refine le_antisymm ?_ (N.bot_le _)
  have h2 := (funSpaceEquiv 𝒩 N).monotone
    ((funSpace 𝒩 N).bot_le ((funSpaceEquiv 𝒩 N).symm (constMap 𝒩 N.bot)))
  rw [OrderIso.apply_symm_apply, funSpaceEquiv_apply] at h2
  have h3 := (le_iff_toElementMap_le.mp h2) z
  rwa [toElementMap_constMap] at h3

/-- `evalAt z` evaluates a function-space element at the fixed argument `z`. -/
def evalAt (z : 𝒩.Element) : ApproximableMap (funSpace 𝒩 N) N :=
  (evalMap 𝒩 N).comp (paired (idMap (funSpace 𝒩 N)) (constMap (funSpace 𝒩 N) z))

theorem evalAt_apply (z : 𝒩.Element) (φ : (funSpace 𝒩 N).Element) :
    (evalAt z).toElementMap φ = (toApproxMap φ).toElementMap z := by
  rw [evalAt, toElementMap_comp, toElementMap_paired, toElementMap_idMap, toElementMap_constMap,
    evalMap_apply]

/-- The `0`-th approximant `S⁰(⊥)` is the bottom map. -/
theorem findOp_iterElem_zero : (findOp φf).iterElem 0 = (funSpace 𝒩 N).bot := by
  rw [iterElem_eq_iterate, Function.iterate_zero_apply]

/-- Value of the `0`-th approximant: `⊥`. -/
theorem iterVal_zero (z : 𝒩.Element) :
    (toApproxMap ((findOp φf).iterElem 0)).toElementMap z = N.bot := by
  rw [findOp_iterElem_zero, toApproxMap_bot]

/-- Recursion equation for the approximant values: `S^{m+1}(⊥)` unfolds one search
step using
`Sᵐ(⊥)` as the continuation. -/
theorem iterVal_succ (m : ℕ) (z : 𝒩.Element) :
    (toApproxMap ((findOp φf).iterElem (m + 1))).toElementMap z =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap (φf.toElementMap z))
          (pair ((head N).toElementMap z)
            ((toApproxMap ((findOp φf).iterElem m)).toElementMap
              ((push N).toElementMap
                (pair (succMap.toElementMap ((head N).toElementMap z))
                  ((tail N).toElementMap z)))))) := by
  have h1 : (findOp φf).iterElem (m + 1) = (findOp φf).toElementMap ((findOp φf).iterElem m) := by
    rw [iterElem_eq_iterate, iterElem_eq_iterate, Function.iterate_succ', Function.comp_apply]
  rw [h1]
  have hval := toElementMap_curry_apply (findBody φf) ((findOp φf).iterElem m) z
  rw [← findOp] at hval
  rw [hval, findBody_apply]

/-- Along a *no-zero* trace, every finite approximant returns `⊥` (induction on
the approximant
index, with the counter universally quantified since the search advances it). -/
theorem iterVal_bot {n : ℕ} {f : List.Vector ℕ (n + 1) → ℕ}
    (hf : LamDef φf (f : List.Vector ℕ (n + 1) →. ℕ)) (v : List.Vector ℕ n)
    (hdiv : ∀ k, f (k ::ᵥ v) ≠ 0) :
    ∀ m k, (toApproxMap ((findOp φf).iterElem m)).toElementMap (vecElem (k ::ᵥ v)) = N.bot := by
  intro m
  induction m with
  | zero => intro k; exact iterVal_zero φf (vecElem (k ::ᵥ v))
  | succ m ih =>
    intro k
    have hne := hdiv k
    obtain ⟨j, hj⟩ : ∃ j, f (k ::ᵥ v) = j + 1 := ⟨f (k ::ᵥ v) - 1, by omega⟩
    rw [← push_natElem_vecElem, iterVal_succ, Exercise511.head_push, Exercise511.tail_push,
      push_natElem_vecElem, lamDef_coe_val hf (k ::ᵥ v), hj, zeroMap_natElem_succ,
      Exercise326.cond_false, succMap_natElem, push_natElem_vecElem]
    exact ih (k + 1)

/-- **Divergence.** If `f(· ::ᵥ v)` has no zero, the search is `⊥` from every
counter. The fixed
point
is the directed union of the approximants `Sᵐ(⊥)` (Theorem 4.2(iii)); pushing the
evaluation at
`vecElem (k ::ᵥ v)` through this sup (continuity, `toElementMap_iSupDirected`)
reduces the claim to
`iterVal_bot`. -/
theorem searchMap_diverge {n : ℕ} {f : List.Vector ℕ (n + 1) → ℕ}
    (hf : LamDef φf (f : List.Vector ℕ (n + 1) →. ℕ)) (v : List.Vector ℕ n)
    (hdiv : ∀ k, f (k ::ᵥ v) ≠ 0) (k : ℕ) :
    (searchMap φf).toElementMap (vecElem (k ::ᵥ v)) = N.bot := by
  refine le_antisymm ?_ (N.bot_le _)
  rw [searchMap, ← evalAt_apply, fixElement_eq_iSupDirected, toElementMap_iSupDirected]
  apply NeighborhoodSystem.iSupDirected_le
  intro m
  rw [evalAt_apply]
  exact le_of_eq (iterVal_bot φf hf v hdiv m k)

/-- **Minimisation** (`Nat.Partrec'.rfind` shape). Given a (very strict) realiser
of a total
`f : Vector ℕ (n+1) → ℕ`, `strictGuardN n (findMap φf)` λ-defines
`v ↦ μk. f(k ::ᵥ v) = 0`. -/
theorem lamDef_rfind {n : ℕ} {f : List.Vector ℕ (n + 1) → ℕ}
    (hf : LamDef φf (f : List.Vector ℕ (n + 1) →. ℕ)) :
    LamDef (strictGuardN n (findMap φf))
      (fun v : List.Vector ℕ n => Nat.rfind fun k => Part.some (decide (f (k ::ᵥ v) = 0))) := by
  refine lamDef_of_inner (findMap φf) _ ?_ ?_
  · intro v c hc
    rw [findMap_vecElem]
    rw [Nat.mem_rfind] at hc
    obtain ⟨hcs, hcm⟩ := hc
    have h0 : f (c ::ᵥ v) = 0 := of_decide_eq_true (Part.mem_some_iff.mp hcs).symm
    have hmin : ∀ i, i < c → f (i ::ᵥ v) ≠ 0 :=
      fun i hi => of_decide_eq_false (Part.mem_some_iff.mp (hcm hi)).symm
    exact searchMap_climb φf hf v c h0 hmin c 0 (by omega)
  · intro v hv
    rw [findMap_vecElem]
    have hdiv : ∀ k, f (k ::ᵥ v) ≠ 0 := by
      intro k h0
      refine hv ?_
      rw [Nat.rfind_dom]
      exact ⟨k, by rw [Part.mem_some_iff]; exact (decide_eq_true_iff.mpr h0).symm,
        fun {m} _ => trivial⟩
    exact searchMap_diverge φf hf v hdiv 0

end Rfind

/-! ### Closure of the partial recursive functions — the full meta-theorem. -/

/-- **Theorem 5.6 (Scott 1981, PRG-19) — every partial recursive function is
λ-definable.** For each
`Nat.Partrec'` function `f : Vector ℕ n →. ℕ` there is an approximable map `φ : 𝒩
→ N` that is a
*very strict* λ-definition of `f`: it returns `f`'s value on total arguments, `⊥`
where `f` is
undefined, and `⊥` on any arg-like input with a `⊥` among its first `n`
coordinates. -/
theorem partrec_lamDef {n : ℕ} {f : List.Vector ℕ n →. ℕ} (h : Nat.Partrec' f) :
    ∃ φ : ApproximableMap 𝒩 N, LamDef φ f := by
  induction h with
  | prim hp => exact primrec_lamDef hp
  | comp g _ _ ihf ihg =>
      obtain ⟨φf, hφf⟩ := ihf
      choose φg hφg using ihg
      exact ⟨_, lamDef_comp _ g φf hφf φg hφg⟩
  | rfind _ ih =>
      obtain ⟨φf, hφf⟩ := ih
      exact ⟨_, lamDef_rfind φf hφf⟩

/-! ### Scott's 1-ary statement.

Every partial recursive `h : ℕ →. ℕ` is realised by an approximable map `τ : N →
N` over the flat
naturals: `τ(n̂) = m̂` when `h n = m`, `τ(n̂) = ⊥` when `h n` diverges, and `τ(⊥)
= ⊥` (strictness). -/

/-- Inject `N → 𝒩` as the stack whose only nonzero coordinate is the head. -/
def oneArg : ApproximableMap N 𝒩 := (push N).comp (paired (idMap N) (constMap N 𝒩.bot))

theorem oneArg_natElem (a : ℕ) :
    (oneArg).toElementMap (natElem a) = vecElem (a ::ᵥ (List.Vector.nil : List.Vector ℕ 0)) := by
  rw [oneArg, toElementMap_comp, toElementMap_paired, toElementMap_idMap, toElementMap_constMap]
  rw [show 𝒩.bot = vecElem (List.Vector.nil : List.Vector ℕ 0) from ?_, push_natElem_vecElem]
  exact eq_of_component_eq (fun i => by rw [component_bot, component_vecElem, dif_neg (by omega)])

theorem oneArg_bot : (oneArg).toElementMap N.bot = 𝒩.bot := by
  rw [oneArg, toElementMap_comp, toElementMap_paired, toElementMap_idMap, toElementMap_constMap]
  apply eq_of_component_eq
  intro i
  cases i with
  | zero => rw [component_push_zero, component_bot]
  | succ k => rw [component_push_succ, component_bot, component_bot]

/-- **Scott's 1-ary meta-theorem.** A partial recursive `h : ℕ →. ℕ` (presented as
a unary
`Nat.Partrec'`) is denoted by a single approximable map `τ : N → N` that is
correct on values,
divergent where `h` diverges, and strict. -/
theorem partrec_one {h : ℕ →. ℕ}
    (H : Nat.Partrec' (fun v : List.Vector ℕ 1 => h v.head)) :
    ∃ τ : ApproximableMap N N,
      (∀ a m, m ∈ h a → τ.toElementMap (natElem a) = natElem m) ∧
      (∀ a, ¬ (h a).Dom → τ.toElementMap (natElem a) = N.bot) ∧
      τ.toElementMap N.bot = N.bot := by
  obtain ⟨φ, hφ⟩ := partrec_lamDef H
  refine ⟨φ.comp oneArg, ?_, ?_, ?_⟩
  · intro a m hm
    rw [toElementMap_comp, oneArg_natElem]
    refine hφ.defined (a ::ᵥ List.Vector.nil) m ?_
    rwa [List.Vector.head_cons]
  · intro a hdom
    rw [toElementMap_comp, oneArg_natElem]
    refine hφ.undef (a ::ᵥ List.Vector.nil) ?_
    rwa [List.Vector.head_cons]
  · rw [toElementMap_comp, oneArg_bot]
    refine hφ.strict 𝒩.bot (fun j => Or.inl (component_bot j)) 0 (by omega) (component_bot 0)

end Domain.Neighborhood.Theorem56Full
