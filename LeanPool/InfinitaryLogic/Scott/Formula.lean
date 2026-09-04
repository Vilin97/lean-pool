/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Scott.BackAndForth
import LeanPool.InfinitaryLogic.Util
import LeanPool.InfinitaryLogic.Lomega1omega.OpenBoundsSemantics
import Mathlib.SetTheory.Cardinal.Aleph

/-!
# Scott Formulas

This file defines Scott formulas, which are Lω₁ω formulas that capture back-and-forth
equivalence at each ordinal level.

## Main Definitions

- `scottFormula`: The Scott formula for a tuple at a given ordinal level.

## Main Results

- `realize_scottFormula_iff_BFEquiv`: A tuple b satisfies the Scott formula for a at level α
  if and only if a and b are BF-equivalent at level α.

## Implementation Notes

The Scott formula at ordinal α is defined by recursion on α:
- At 0: the atomic diagram of the tuple
- At successor α + 1: the formula at α, plus forth and back conditions
- At limit λ: the conjunction over all β < λ

For the forth and back conditions, we need to quantify over elements of M, which requires
`[Countable M]` to form the countable conjunction/disjunction.

The key technical challenge is handling the variable binding correctly. When we have
a formula φ(x₀,...,xₙ) with n+1 free variables and want to existentially quantify
over the last variable, we use `relabel` to move it into a bound position.
-/

universe u v w w'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable {M : Type w} [L.Structure M]
variable [Countable (Σ l, L.Relations l)]
variable [Countable M]

-- Derive Encodable from Countable for use in einf/esup
attribute [local instance] Encodable.ofCountable

open FirstOrder Structure Fin Ordinal BoundedFormulaω

/-- Existentially quantify over the last free variable of a formula. -/
def existsLastVar {n : ℕ} (φ : L.Formulaω (Fin (n + 1))) : L.Formulaω (Fin n) :=
  (φ.relabel insertLastBound).ex

/-- Universally quantify over the last free variable of a formula. -/
def forallLastVar {n : ℕ} (φ : L.Formulaω (Fin (n + 1))) : L.Formulaω (Fin n) :=
  (φ.relabel insertLastBound).all

section Semantics

variable {N : Type w'} [L.Structure N]

/-- Helper: snoc Fin.elim0 x evaluated at 0 gives x. -/
private theorem snoc_elim0_zero {α : Type*} (x : α) :
    (snoc (α := fun _ => α) Fin.elim0 x) 0 = x :=
  congrFun (Fin.snoc_elim0_eq x) 0

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- Semantics of existsLastVar: existentially quantifies over the last variable.

Uses `realize_relabel_insertLastBound_zero` to show that:
- `existsLastVar φ = (φ.relabel insertLastBound).ex`
- This quantifies existentially over the last (n-th) free variable
-/
theorem realize_existsLastVar {n : ℕ} (φ : L.Formulaω (Fin (n + 1))) (v : Fin n → N) :
    (existsLastVar φ).Realize v ↔ ∃ x : N, φ.Realize (snoc v x) := by
  -- keep the formula-level interface intact: apply the quantifier lemma at the empty tuple the
  -- sentence semantics actually supplies (`default`), rather than unfolding `Formulaω.Realize`
  have h := BoundedFormulaω.realize_ex (M := N) (v := v) (xs := (default : Fin 0 → N))
    (φ.relabel insertLastBound)
  refine h.trans (exists_congr fun x => ?_)
  have hz : (snoc (α := fun _ => N) (default : Fin 0 → N) x) 0 = x := snoc_elim0_zero x
  rw [realize_relabel_insertLastBound_zero, hz]

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- Semantics of forallLastVar: universally quantifies over the last variable. -/
theorem realize_forallLastVar {n : ℕ} (φ : L.Formulaω (Fin (n + 1))) (v : Fin n → N) :
    (forallLastVar φ).Realize v ↔ ∀ x : N, φ.Realize (snoc v x) := by
  have h := BoundedFormulaω.realize_all (M := N) (v := v) (xs := (default : Fin 0 → N))
    (φ.relabel insertLastBound)
  refine h.trans (forall_congr' fun x => ?_)
  have hz : (snoc (α := fun _ => N) (default : Fin 0 → N) x) 0 = x := snoc_elim0_zero x
  rw [realize_relabel_insertLastBound_zero, hz]

end Semantics

/-- The Scott formula for a tuple a at ordinal level α.

At level 0: the atomic diagram of a.
At successor α + 1: formula at α ∧ (forth condition) ∧ (back condition)
At limit λ: conjunction over all β < λ.

The formula has free variables indexed by `Fin n` (representing the positions in the tuple).
Requires `[Countable M]` to quantify over elements of M in the forth/back conditions.

The definition uses `Ordinal.limitRecOn` with a motive that is constant in the ordinal
(always `(n : ℕ) → (Fin n → M) → L.Formulaω (Fin n)`), allowing uniform treatment of
tuples of different lengths in the recursion.
-/
noncomputable def scottFormula {n : ℕ} (a : Fin n → M) (α : Ordinal) : L.Formulaω (Fin n) :=
  haveI : Encodable M := Encodable.ofCountable M
  Ordinal.limitRecOn (motive := fun _ => (k : ℕ) → (Fin k → M) → L.Formulaω (Fin k)) α
    -- Zero case: atomic diagram
    (fun k a' => atomicDiagram (L := L) a')
    -- Successor case: previous formula ∧ forth ∧ back
    (fun _β ih k a' =>
      ih k a' ⊓
      einf (fun m : M => existsLastVar (ih (k + 1) (snoc a' m))) ⊓
      forallLastVar (esup (fun m : M => ih (k + 1) (snoc a' m))))
    -- Limit case: conjunction over all smaller ordinals
    -- Note: This requires {γ // γ < β} to be encodable, which holds for β < ω₁.
    -- For Scott analysis, we only use ordinals < ω₁, so this is always valid.
    -- For β ≥ ω₁, we return a trivial formula (this case is never used in practice).
    (fun _β _hβ ih k a' =>
      if h_lt : _β < Ordinal.omega 1 then
        haveI : Countable {γ // γ < _β} := by
          -- β.ToType is countable for β < ω₁
          have : Countable _β.ToType := by
            rw [← Cardinal.mk_le_aleph0_iff]
            rw [Cardinal.mk_toType]
            have h_card : _β.card < Cardinal.aleph 1 := Cardinal.lt_omega_iff_card_lt.mp h_lt
            have h1 : Cardinal.aleph 1 = Order.succ (Cardinal.aleph 0) := by
              rw [Cardinal.succ_aleph, zero_add]
            rw [h1, Cardinal.aleph_zero] at h_card
            exact Order.lt_succ_iff.mp h_card
          -- Use equivalence Set.Iio β ≃ β.ToType
          exact Countable.of_equiv _β.ToType (Ordinal.ToType.mk).symm.toEquiv
        haveI : Encodable {γ // γ < _β} := Encodable.ofCountable _
        einf (fun (x : {γ // γ < _β}) => ih x.1 x.2 k a')
      else
        -- For β ≥ ω₁, return ⊤ (true). This case is never invoked for Scott analysis.
        ⊤)
    n a

omit [L.IsRelational] in
theorem scottFormula_zero {n : ℕ} (a : Fin n → M) :
    scottFormula (L := L) a 0 = atomicDiagram a := by
  simp only [scottFormula, Ordinal.limitRecOn_zero]

omit [L.IsRelational] in
theorem scottFormula_succ {n : ℕ} (a : Fin n → M) (α : Ordinal) :
    scottFormula (L := L) a (Order.succ α) =
      scottFormula a α ⊓
      einf (fun m : M => existsLastVar (scottFormula (snoc a m) α)) ⊓
      forallLastVar (esup (fun m : M => scottFormula (snoc a m) α)) := by
  have : Encodable M := Encodable.ofCountable M
  simp only [scottFormula, Order.succ_eq_add_one, Ordinal.limitRecOn_add_one]

omit [L.IsRelational] in
/-- The fundamental correspondence: a tuple b realizes the Scott formula for a at level α
if and only if a and b are BF-equivalent at level α.

**Important**: This theorem only holds for α < ω₁. For α ≥ ω₁, `scottFormula` returns ⊤
(which is always realized) while `BFEquiv` may fail, so the equivalence breaks down.
For Scott analysis of countable structures, we only use ordinals < ω₁.

The proof proceeds by ordinal induction using `limitRecOn`:
- Zero case: follows from `sameAtomicType_iff_realize_atomicDiagram`
- Successor case: uses `realize_existsLastVar` and `realize_forallLastVar`
- Limit case: uses `realize_einf`
-/
theorem realize_scottFormula_iff_BFEquiv
    {N : Type w'} [L.Structure N] {n : ℕ}
    (a : Fin n → M) (b : Fin n → N) (α : Ordinal) (hα : α < Ordinal.omega 1) :
    (scottFormula (L := L) a α).Realize b ↔ BFEquiv (L := L) α n a b := by
  induction α using Ordinal.limitRecOn generalizing n a b with
  | zero =>
    rw [scottFormula_zero, BFEquiv.zero]
    exact (sameAtomicType_iff_realize_atomicDiagram (L := L) (M := M) (N := N) a b).symm
  | add_one β ih =>
    rw [← Order.succ_eq_add_one] at hα ⊢
    have hβ : β < Ordinal.omega 1 := lt_of_lt_of_le (Order.lt_succ β) (le_of_lt hα)
    rw [scottFormula_succ, BFEquiv.succ]
    simp only [Formulaω.realize_inf]
    constructor
    · intro ⟨⟨hbase, hforth⟩, hback⟩
      simp only [Formulaω.realize_einf, realize_existsLastVar] at hforth
      simp only [realize_forallLastVar, Formulaω.realize_esup] at hback
      refine ⟨(ih a b hβ).mp hbase, fun m => ?_, fun n' => ?_⟩
      · let ⟨n', hn'⟩ := hforth m
        exact ⟨n', (ih (snoc a m) (snoc b n') hβ).mp hn'⟩
      · let ⟨m, hm⟩ := hback n'
        exact ⟨m, (ih (snoc a m) (snoc b n') hβ).mp hm⟩
    · intro ⟨hbase, hforth, hback⟩
      refine ⟨⟨(ih a b hβ).mpr hbase, ?_⟩, ?_⟩
      · rw [Formulaω.realize_einf]
        intro m
        rw [realize_existsLastVar]
        let ⟨n', hn'⟩ := hforth m
        exact ⟨n', (ih (snoc a m) (snoc b n') hβ).mpr hn'⟩
      · rw [realize_forallLastVar]
        intro n'
        rw [Formulaω.realize_esup]
        let ⟨m, hm⟩ := hback n'
        exact ⟨m, (ih (snoc a m) (snoc b n') hβ).mpr hm⟩
  | limit β hβlimit ih =>
    rw [BFEquiv.limit β hβlimit]
    unfold scottFormula
    rw [Ordinal.limitRecOn_limit _ _ _ _ hβlimit]
    -- do not unfold `Formulaω.Realize`: that exposes the raw ℕ-indexed `iInf` and loses the
    -- `Set.Iio`-style index type of the limit conjunction
    simp only [hα, dite_true, Formulaω.realize_einf]
    exact ⟨fun h γ hγ => (ih γ hγ a b (lt_trans hγ hα)).mp (h ⟨γ, hγ⟩),
           fun h ⟨γ, hγ⟩ => (ih γ hγ a b (lt_trans hγ hα)).mpr (h γ hγ)⟩

end Language

end FirstOrder
