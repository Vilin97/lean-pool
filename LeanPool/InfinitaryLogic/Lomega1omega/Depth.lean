/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Lomega1omega.Operations
import Mathlib.SetTheory.Ordinal.Family

/-!
# Ordinal-valued depth of `Lω₁ω` formulas

The well-founded measure for quantifier recursions over `BoundedFormulaω` (extracted from
`Methods/Henkin/Construction.lean`, where it was born as the `truthLemma` termination measure,
and re-derived privately by `Methods/Interpolation/QuotientTruthLemma.lean` — this neutral home
serves both).  `sizeOf` is inadequate: `sizeOf (φs k)` is unbounded while
`sizeOf (iSup φs) = 2`, and the `all` case recurses on `(φ.openBounds).subst t`, not a
structural subterm.  `depth` uses `Ordinal.iSup` at the countable connectives and is preserved
by `castLE`, `relabel`, `openBounds`, and `subst`, with strict decrease into every connective.
-/

universe u v

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

/-! ### Ordinal-valued depth for termination of truthLemma

The standard `sizeOf` measure is inadequate for `truthLemma` because:
- `sizeOf (fun k => φs k) = 1` for function types, so `sizeOf (iSup φs) = 2`,
  yet `sizeOf (φs k)` can be arbitrarily large.
- The `all` case recurses on `(φ.openBounds).subst t`, which is not a structural subterm.

We define an `Ordinal`-valued depth that uses `iSup` for `iSup`/`iInf` cases,
then prove it is preserved by `castLE`, `relabel`, `openBounds`, and `subst`. -/

/-- Ordinal-valued depth of a bounded formula. Uses `Ordinal.iSup` at `iSup`/`iInf` nodes
to ensure each component `φs k` has strictly smaller depth. -/
noncomputable def BoundedFormulaω.depth : L.BoundedFormulaω α n → Ordinal.{0}
  | .falsum => 0
  | .equal _ _ => 0
  | .rel _ _ => 0
  | .imp φ ψ => max φ.depth ψ.depth + 1
  | .all φ => φ.depth + 1
  | .iSup φs => (⨆ k, (φs k).depth) + 1
  | .iInf φs => (⨆ k, (φs k).depth) + 1

theorem depth_lt_imp_left {φ ψ : L.BoundedFormulaω α n} :
    φ.depth < (φ.imp ψ).depth := by
  simp only [BoundedFormulaω.depth]
  exact lt_of_le_of_lt (le_max_left _ _) (Order.lt_succ _)

theorem depth_lt_imp_right {φ ψ : L.BoundedFormulaω α n} :
    ψ.depth < (φ.imp ψ).depth := by
  simp only [BoundedFormulaω.depth]
  exact lt_of_le_of_lt (le_max_right _ _) (Order.lt_succ _)

theorem depth_lt_iSup {φs : ℕ → L.BoundedFormulaω α n} (k : ℕ) :
    (φs k).depth < (BoundedFormulaω.iSup φs).depth := by
  simp only [BoundedFormulaω.depth]
  exact lt_of_le_of_lt (Ordinal.le_iSup _ k) (Order.lt_succ _)

theorem depth_lt_iInf {φs : ℕ → L.BoundedFormulaω α n} (k : ℕ) :
    (φs k).depth < (BoundedFormulaω.iInf φs).depth := by
  simp only [BoundedFormulaω.depth]
  exact lt_of_le_of_lt (Ordinal.le_iSup _ k) (Order.lt_succ _)

theorem depth_lt_all {φ : L.BoundedFormulaω α (n + 1)} :
    φ.depth < (BoundedFormulaω.all φ).depth := by
  simp only [BoundedFormulaω.depth]
  exact Order.lt_succ _

private theorem depth_castLE (h : m ≤ n) (φ : L.BoundedFormulaω α m) :
    (φ.castLE h).depth = φ.depth := by
  induction φ generalizing n with
  | falsum => rfl
  | equal _ _ => rfl
  | rel _ _ => rfl
  | imp φ ψ ihφ ihψ =>
    simp only [BoundedFormulaω.castLE, BoundedFormulaω.depth, ihφ h, ihψ h]
  | all φ ih =>
    simp only [BoundedFormulaω.castLE, BoundedFormulaω.depth]
    rw [ih (Nat.succ_le_succ h)]
  | iSup φs ih =>
    simp only [BoundedFormulaω.castLE, BoundedFormulaω.depth]
    congr 1; exact iSup_congr (fun k => ih k h)
  | iInf φs ih =>
    simp only [BoundedFormulaω.castLE, BoundedFormulaω.depth]
    congr 1; exact iSup_congr (fun k => ih k h)

private theorem depth_relabel (g : α → β ⊕ Fin p)
    (φ : L.BoundedFormulaω α n) : (φ.relabel g).depth = φ.depth := by
  induction φ with
  | falsum => rfl
  | equal _ _ => rfl
  | rel _ _ => rfl
  | imp φ ψ ihφ ihψ => simp only [BoundedFormulaω.relabel, BoundedFormulaω.depth, ihφ, ihψ]
  | all φ ih =>
    simp only [BoundedFormulaω.relabel, BoundedFormulaω.depth]
    rw [depth_castLE _ _, ih]
  | iSup φs ih =>
    simp only [BoundedFormulaω.relabel, BoundedFormulaω.depth]
    congr 1; exact iSup_congr (fun k => ih k)
  | iInf φs ih =>
    simp only [BoundedFormulaω.relabel, BoundedFormulaω.depth]
    congr 1; exact iSup_congr (fun k => ih k)

theorem depth_openBounds (φ : L.BoundedFormulaω Empty n) :
    φ.openBounds.depth = φ.depth := by
  induction φ with
  | falsum => rfl
  | equal _ _ => rfl
  | rel _ _ => rfl
  | imp φ ψ ihφ ihψ =>
    simp only [BoundedFormulaω.openBounds, BoundedFormulaω.depth, ihφ, ihψ]
  | all φ ih =>
    simp only [BoundedFormulaω.openBounds, BoundedFormulaω.depth]
    rw [depth_relabel]; exact congr_arg (· + 1) ih
  | iSup φs ih =>
    simp only [BoundedFormulaω.openBounds, BoundedFormulaω.depth]
    congr 1; exact iSup_congr (fun k => ih k)
  | iInf φs ih =>
    simp only [BoundedFormulaω.openBounds, BoundedFormulaω.depth]
    congr 1; exact iSup_congr (fun k => ih k)

theorem depth_subst (φ : L.BoundedFormulaω α n) (tf : α → L.Term β) :
    (φ.subst tf).depth = φ.depth := by
  induction φ with
  | falsum => rfl
  | equal _ _ => rfl
  | rel _ _ => rfl
  | imp φ ψ ihφ ihψ => simp only [BoundedFormulaω.subst, BoundedFormulaω.depth, ihφ, ihψ]
  | all φ ih => simp only [BoundedFormulaω.subst, BoundedFormulaω.depth, ih]
  | iSup φs ih =>
    simp only [BoundedFormulaω.subst, BoundedFormulaω.depth]
    congr 1; exact iSup_congr (fun k => ih k)
  | iInf φs ih =>
    simp only [BoundedFormulaω.subst, BoundedFormulaω.depth]
    congr 1; exact iSup_congr (fun k => ih k)

/-- `depth (openBounds φ).subst t < depth (all φ)` for the truthLemma termination proof. -/
theorem depth_openBounds_subst_lt
    {φ : L.BoundedFormulaω Empty (n + 1)} (tf : Fin (n + 1) → L.Term β) :
    (φ.openBounds.subst tf).depth < (BoundedFormulaω.all φ).depth := by
  rw [depth_subst, depth_openBounds]
  exact depth_lt_all

end Language

end FirstOrder
