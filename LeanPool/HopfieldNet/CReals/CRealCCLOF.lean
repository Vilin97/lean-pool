/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.CReals.CRealRealEquiv
import Mathlib.Algebra.Field.MinimalAxioms
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.CompleteField

/-!
Modern “CCLOF” module: classical complete linear ordered field structure on `Computable.CReal`.

This file is intentionally **noncomputable**: it equips `CReal` with classical instances
(`LinearOrder`, `Field`, and conditional completeness) by transporting along the denotation
map `toReal : CReal → ℝ` and the (noncomputable) map `ofReal : ℝ → CReal`.
-/

namespace Computable
namespace CReal

open CauSeq
open CauSeq.Completion

-- `abs` is already taken by `Computable.CReal.abs`; use the rational absolute value explicitly.
local notation "absℚ" => (_root_.abs : ℚ → ℚ)

open scoped Classical

namespace Pre

/--
Uniform near-bound: the real denotation of a regular pre-real is within `2^{-(n+1)}` of its
`(n+1)`-th rational approximant.
-/
theorem abs_toReal_sub_approx_le (x : CReal.Pre) (n : ℕ) :
    |Pre.toReal x - (x.approx (n + 1) : ℝ)| ≤ (1 : ℝ) / (2 ^ (n + 1)) := by
  -- `toReal x = Real.mk (toCauSeq x)`, and `toCauSeq x` uses `x.approx`.
  dsimp [Pre.toReal]
  -- Apply the general `mk_near` lemma with witness index `n+1`.
  refine Real.mk_near_of_forall_near (f := Pre.toCauSeq x) (x := (x.approx (n + 1) : ℝ))
    (ε := (1 : ℝ) / (2 ^ (n + 1))) ?_
  refine ⟨n + 1, ?_⟩
  intro j hj
  -- Unfold the underlying `CauSeq` function and reduce to regularity in `ℚ`, then cast.
  change |((x.approx j : ℚ) : ℝ) - (x.approx (n + 1) : ℝ)| ≤ (1 : ℝ) / (2 ^ (n + 1))
  -- regularity gives `|x_{n+1} - x_j| ≤ 2^{-(n+1)}` for `n+1 ≤ j`
  have hreg : |x.approx (n + 1) - x.approx j| ≤ (1 : ℚ) / (2 ^ (n + 1)) :=
    x.is_regular (n + 1) j hj
  have hcast :
      |((x.approx (n + 1) - x.approx j : ℚ) : ℝ)| ≤ ((1 : ℚ) / (2 ^ (n + 1)) : ℝ) := by
    exact_mod_cast hreg
  -- rewrite into the required orientation
  simpa [Pre.toCauSeq, abs_sub_comm] using hcast

/--
Order reflection at the pre-level: if `toReal x ≤ toReal y` in `ℝ`, then `x ≤ y` in the
computable order.
-/
theorem le_of_toReal_le {x y : CReal.Pre} (h : Pre.toReal x ≤ Pre.toReal y) : Pre.le x y := by
  intro n
  -- Use near-bounds at index `n+1`.
  have hx :
      |Pre.toReal x - (x.approx (n + 1) : ℝ)| ≤ (1 : ℝ) / (2 ^ (n + 1)) :=
    abs_toReal_sub_approx_le x n
  have hy :
      |Pre.toReal y - (y.approx (n + 1) : ℝ)| ≤ (1 : ℝ) / (2 ^ (n + 1)) :=
    abs_toReal_sub_approx_le y n
  have hx' := (abs_sub_le_iff).1 hx
  have hy' := (abs_sub_le_iff).1 hy
  -- `x_{n+1} ≤ toReal x + δ ≤ toReal y + δ ≤ y_{n+1} + 2δ = y_{n+1} + 2^{-n}`
  have h1 : (x.approx (n + 1) : ℝ) ≤ Pre.toReal x + (1 : ℝ) / (2 ^ (n + 1)) := by
    linarith [hx'.2]
  have h2 : Pre.toReal y ≤ (y.approx (n + 1) : ℝ) + (1 : ℝ) / (2 ^ (n + 1)) := by
    linarith [hy'.2]
  have hxy : (x.approx (n + 1) : ℝ) ≤ (y.approx (n + 1) : ℝ) + (1 : ℝ) / (2 ^ n) := by
    -- chain and simplify the power-of-two term
    have : (x.approx (n + 1) : ℝ)
        ≤ (y.approx (n + 1) : ℝ) + ((2 : ℝ) / (2 ^ (n + 1))) := by
      calc
        (x.approx (n + 1) : ℝ)
            ≤ Pre.toReal x + (1 : ℝ) / (2 ^ (n + 1)) := h1
        _ ≤ Pre.toReal y + (1 : ℝ) / (2 ^ (n + 1)) := by linarith [h]
        _ ≤ (y.approx (n + 1) : ℝ) + (1 : ℝ) / (2 ^ (n + 1)) + (1 : ℝ) / (2 ^ (n + 1)) := by
              linarith [h2]
        _ = (y.approx (n + 1) : ℝ) + ((2 : ℝ) / (2 ^ (n + 1))) := by ring
    -- rewrite `2 / 2^(n+1) = 1 / 2^n`
    have htwo : (2 : ℝ) / (2 ^ (n + 1)) = (1 : ℝ) / (2 ^ n) := by
      field_simp [pow_succ]
      ring
    simpa [htwo] using this
  -- cast back to ℚ (the definition of `Pre.le` is in ℚ)
  -- rewrite the RHS as the cast of a rational expression, then use `Rat.cast_le`.
  have hxy' :
      ((x.approx (n + 1) : ℚ) : ℝ) ≤ ((y.approx (n + 1) + (1 : ℚ) / (2 ^ n) : ℚ) : ℝ) := by
    simpa using hxy
  exact (Rat.cast_le (K := ℝ)).1 hxy'

/--
Monotonicity at the pre-level: if `x ≤ y` in the computable order, then `toReal x ≤ toReal y` in `ℝ`.
-/
theorem toReal_mono {x y : CReal.Pre} (hxy : Pre.le x y) : Pre.toReal x ≤ Pre.toReal y := by
  -- use `le_of_forall_pos_le_add` on `ℝ`
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  -- Pick `N` so that `2 / 2^N < ε`.
  have one_lt_two : (1 : ℝ) < 2 := by norm_num
  have hxpos : 0 < (2 : ℝ) / ε := div_pos (by norm_num) hε
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (2 : ℝ) / ε < (2 : ℝ) ^ N :=
    pow_unbounded_of_one_lt (R := ℝ) (x := (2 : ℝ) / ε) one_lt_two
  have hpowpos : 0 < (2 : ℝ) ^ N := pow_pos (by norm_num) N
  have hsmall : (2 : ℝ) / (2 ^ N) < ε := by
    -- from `(2/ε) < 2^N`, multiply by `ε` and divide by `2^N`
    have : (2 : ℝ) < (2 : ℝ) ^ N * ε := by
      have := (mul_lt_mul_of_pos_right hN hε)
      -- `(2/ε) * ε = 2`
      simpa [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ (ne_of_gt hε), one_mul] using this
    -- divide both sides by `2^N > 0`
    -- use the commutative variant so the RHS is `2^N * ε`
    have := (div_lt_iff₀' hpowpos).2 this
    -- `2^N` as a Nat power equals `(2:ℝ)^N`
    simpa [div_eq_mul_inv] using this
  -- Prove `toReal x ≤ toReal y + 2/2^N`, then use `hsmall`.
  have hx_near := abs_toReal_sub_approx_le x N
  have hy_near := abs_toReal_sub_approx_le y N
  have hx' := (abs_sub_le_iff).1 hx_near
  have hy' := (abs_sub_le_iff).1 hy_near
  have h_step : Pre.toReal x ≤ Pre.toReal y + (2 : ℝ) / (2 ^ N) := by
    -- `toReal x ≤ x_{N+1} + δ`
    have hx_up : Pre.toReal x ≤ (x.approx (N + 1) : ℝ) + (1 : ℝ) / (2 ^ (N + 1)) := by
      linarith [hx'.1]
    -- `x_{N+1} ≤ y_{N+1} + 1/2^N` (cast to ℝ)
    have hxyN : (x.approx (N + 1) : ℝ) ≤ (y.approx (N + 1) : ℝ) + (1 : ℝ) / (2 ^ N) := by
      -- cast the `ℚ`-inequality `hxy N` into `ℝ`
      have : (x.approx (N + 1) : ℚ) ≤ y.approx (N + 1) + (1 : ℚ) / (2 ^ N) := hxy N
      have : ((x.approx (N + 1) : ℚ) : ℝ) ≤ ((y.approx (N + 1) + (1 : ℚ) / (2 ^ N) : ℚ) : ℝ) :=
        (Rat.cast_le (K := ℝ)).2 this
      simpa using this
    -- `y_{N+1} ≤ toReal y + δ`
    have hy_up : (y.approx (N + 1) : ℝ) ≤ Pre.toReal y + (1 : ℝ) / (2 ^ (N + 1)) := by
      linarith [hy'.2]
    -- combine and simplify `(1/2^N) + 2*(1/2^(N+1)) = 2/2^N`
    have htwo : ((2 ^ N : ℝ)⁻¹) + (2 : ℝ) / (2 ^ (N + 1)) = (2 : ℝ) / (2 ^ N) := by
      field_simp [pow_succ]
      ring
    calc
      Pre.toReal x
          ≤ (x.approx (N + 1) : ℝ) + (1 : ℝ) / (2 ^ (N + 1)) := hx_up
      _ ≤ (y.approx (N + 1) : ℝ) + (1 : ℝ) / (2 ^ N) + (1 : ℝ) / (2 ^ (N + 1)) := by
            linarith [hxyN]
      _ ≤ Pre.toReal y + (1 : ℝ) / (2 ^ (N + 1)) + (1 : ℝ) / (2 ^ N) + (1 : ℝ) / (2 ^ (N + 1)) := by
            linarith [hy_up]
      _ = Pre.toReal y + (((2 ^ N : ℝ)⁻¹) + (2 : ℝ) / (2 ^ (N + 1))) := by
            -- normalize divisions, then rearrange
            simp [div_eq_mul_inv, add_left_comm, add_comm]
            ring
      _ = Pre.toReal y + (2 : ℝ) / (2 ^ N) := by simp [htwo]
  have : Pre.toReal x ≤ Pre.toReal y + ε := by
    have : Pre.toReal x ≤ Pre.toReal y + (2 : ℝ) / (2 ^ N) := h_step
    linarith [hsmall]
  exact this

end Pre

/-! ### Order transfer: `CReal` vs `ℝ` -/

theorem le_of_toReal_le {x y : CReal} (h : toReal x ≤ toReal y) : x ≤ y := by
  refine Quotient.inductionOn₂ x y (fun a b hab => ?_) h
  -- unfold both sides and use the pre-level reflection lemma
  simpa using (Pre.le_of_toReal_le (x := a) (y := b) hab)

theorem toReal_mono {x y : CReal} (h : x ≤ y) : toReal x ≤ toReal y := by
  refine Quotient.inductionOn₂ x y (fun a b hab => ?_) h
  simpa using (Pre.toReal_mono (x := a) (y := b) hab)

theorem toReal_le_iff {x y : CReal} : toReal x ≤ toReal y ↔ x ≤ y :=
  ⟨le_of_toReal_le, toReal_mono⟩

theorem toReal_lt_iff {x y : CReal} : toReal x < toReal y ↔ x < y := by
  constructor
  · intro h
    have hle : x ≤ y := (toReal_le_iff).1 (le_of_lt h)
    have hnot : ¬ y ≤ x := by
      intro hyx
      have : toReal y ≤ toReal x := toReal_mono hyx
      exact not_le_of_gt h this
    exact (lt_iff_le_not_ge).2 ⟨hle, hnot⟩
  · intro h
    refine (lt_iff_le_not_ge).2 ?_
    refine ⟨toReal_mono (le_of_lt h), ?_⟩
    intro hyx
    have : y ≤ x := (toReal_le_iff).1 hyx
    exact (not_le_of_gt h) this

theorem le_total (x y : CReal) : x ≤ y ∨ y ≤ x := by
  -- totality comes from `ℝ` via `toReal_le_iff`
  have h := _root_.le_total (toReal x) (toReal y)
  exact h.imp (fun hxy => (toReal_le_iff).1 hxy) (fun hyx => (toReal_le_iff).1 hyx)

noncomputable instance : Min CReal := ⟨fun a b => if a ≤ b then a else b⟩
noncomputable instance : Max CReal := ⟨fun a b => if a ≤ b then b else a⟩
noncomputable instance : Ord CReal := ⟨fun a b => compareOfLessAndEq a b⟩

/-- Classical linear order on `CReal` (extending the existing `≤`). -/
noncomputable instance : LinearOrder CReal := by
  classical
  -- Use the existing `PartialOrder` and our `le_total`.
  refine LinearOrder.mk (α := CReal)
    (le_total := le_total)
    (toDecidableLE := fun a b => Classical.decRel (fun x y : CReal => x ≤ y) a b)
    (toDecidableEq := Classical.decEq CReal)
    (toDecidableLT := fun a b => Classical.decRel (fun x y : CReal => x < y) a b)
    (min_def := by intro a b; rfl)
    (max_def := by intro a b; rfl)

/-! ### `toReal` is an order embedding -/

theorem toReal_injective : Function.Injective toReal := by
  intro x y hxy
  apply le_antisymm
  · exact (toReal_le_iff).1 (by simp [hxy])
  · exact (toReal_le_iff).1 (by simp [hxy])

/-! ### `toReal (ofReal r) = r` -/

namespace FromReal

open Real

-- Cauchy equivalence between the original sequence and its regularization subsequence.
theorem toCauSeq_preOfCauSeq_equiv (f : CauSeq ℚ absℚ) : Pre.toCauSeq (preOfCauSeq f) ≈ f := by
  -- show `LimZero (toCauSeq (preOfCauSeq f) - f)`
  intro ε hε
  have hpos : 0 < (1 : ℚ) / ε := one_div_pos.mpr hε
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 : ℚ) / ε < (2 : ℚ) ^ N :=
    Computable.exists_pow_gt (x := (1 : ℚ) / ε) hpos
  have hpowpos : 0 < (2 : ℚ) ^ N := pow_pos (by norm_num) N
  have hN' : (1 : ℚ) / (2 : ℚ) ^ N < ε := (one_div_lt hpowpos hε).2 hN
  -- work with the modulus for precision `2^{-N}`
  let I : ℕ := max (idxMono f N) N
  refine ⟨I, ?_⟩
  intro j hj
  have hjI₁ : idxMono f N ≤ j := _root_.le_trans (le_max_left _ _) hj
  have hjI₂ : N ≤ j := _root_.le_trans (le_max_right _ _) hj
  have hidx : idx f N ≤ idxMono f N := idx_le_idxMono f N
  have hj_ge : idx f N ≤ j := _root_.le_trans hidx hjI₁
  have hj2_geN : N ≤ j + 2 := _root_.le_trans hjI₂ (Nat.le_add_right _ _)
  have hmono : idxMono f N ≤ idxMono f (j + 2) := idxMono_mono f hj2_geN
  have hj2_ge : idx f N ≤ idxMono f (j + 2) := _root_.le_trans hidx hmono
  have hspec := idx_spec f N j hj_ge (idxMono f (j + 2)) hj2_ge
  -- unfold the regularized sequence `preOfCauSeq`
  -- `(preOfCauSeq f).approx (j+1) = f (idxMono f (j+3))`, but `toCauSeq` uses `approx`.
  -- Here we need the value at index `j`.
  -- `Pre.toCauSeq (preOfCauSeq f) j = (preOfCauSeq f).approx j = f (idxMono f (j+2))`.
  have : |(Pre.toCauSeq (preOfCauSeq f) - f : CauSeq ℚ absℚ) j| < ε := by
    -- `(toCauSeq ... - f) j = (toCauSeq ...) j - f j`
    -- and `(toCauSeq ...) j = f (idxMono f (j+2))`
    have : |f (idxMono f (j + 2)) - f j| < ε := by
      -- `idx_spec` gives `|f j - f (idxMono ...) | < 1/2^N`, flip with `abs_sub_comm`
      have hlt : |f j - f (idxMono f (j + 2))| < (1 : ℚ) / (2 ^ N) := by
        simpa using hspec
      have hlt' : |f (idxMono f (j + 2)) - f j| < (1 : ℚ) / (2 ^ N) := by
        simpa [abs_sub_comm] using hlt
      exact lt_trans hlt' (by
        -- rewrite `(2:ℚ)^N` to `2^N`
        -- and use the chosen `N` with `1/2^N < ε`
        simpa [one_div, div_eq_mul_inv] using hN')
    -- now rewrite in terms of `toCauSeq (preOfCauSeq f)`
    simpa [Pre.toCauSeq, preOfCauSeq, CauSeq.sub_apply, abs_sub_comm] using this
  simpa using this

theorem toReal_ofReal (x : ℝ) : CReal.toReal (ofReal x) = x := by
  -- reduce to the case `x = Real.mk f`
  refine Real.ind_mk x (fun f => ?_)
  -- Definitional reduction: `toReal (ofReal (Real.mk f)) = Real.mk (toCauSeq (preOfCauSeq f))`.
  change Real.mk (Pre.toCauSeq (preOfCauSeq f)) = Real.mk f
  -- Use `Real.mk_eq` and the Cauchy equivalence lemma.
  exact (Real.mk_eq).2 (toCauSeq_preOfCauSeq_equiv (f := f))

end FromReal

theorem toReal_ofReal (x : ℝ) : toReal (FromReal.ofReal x) = x :=
  FromReal.toReal_ofReal x

theorem ofReal_toReal (x : CReal) : FromReal.ofReal (toReal x) = x := by
  -- left inverse from injectivity
  apply toReal_injective
  simp [toReal_ofReal]

/-! ### Classical field structure via `ofReal`/`toReal` -/

noncomputable instance : Inv CReal := ⟨fun x => FromReal.ofReal ((toReal x)⁻¹)⟩

theorem toReal_inv (x : CReal) : toReal x⁻¹ = (toReal x)⁻¹ := by
  simp [Inv.inv, toReal_ofReal]

noncomputable instance : Field CReal := by
  classical
  -- Build a `Field` structure using Mathlib's minimal-axioms constructor, keeping the existing
  -- ring operations and supplying the inverse axioms via `toReal`.
  refine
    Field.ofMinimalAxioms CReal
      (add_assoc := by intro a b c; exact _root_.add_assoc a b c)
      (zero_add := by intro a; exact _root_.zero_add a)
      (neg_add_cancel := by intro a; exact _root_.neg_add_cancel a)
      (mul_assoc := by intro a b c; exact _root_.mul_assoc a b c)
      (mul_comm := by intro a b; exact _root_.mul_comm a b)
      (one_mul := by intro a; exact _root_.one_mul a)
      (mul_inv_cancel := ?_)
      (inv_zero := ?_)
      (left_distrib := by intro a b c; exact _root_.mul_add a b c)
      (exists_pair_ne := ⟨0, 1, zero_ne_one⟩)
  · intro a ha
    apply toReal_injective
    have ha' : toReal a ≠ (0 : ℝ) := by
      intro h0
      have : a = 0 := by
        apply toReal_injective
        -- goal is `toReal a = toReal 0`, which is `toReal a = 0`
        simpa using h0
      exact ha this
    calc
      toReal (a * a⁻¹) = toReal a * toReal a⁻¹ := by
        simpa using (toReal_mul a a⁻¹)
      _ = toReal a * (toReal a)⁻¹ := by simp [toReal_inv]
      _ = (1 : ℝ) := by simpa using mul_inv_cancel₀ ha'
      _ = toReal (1 : CReal) := by simp
  · apply toReal_injective
    calc
      toReal ((0 : CReal)⁻¹) = (toReal (0 : CReal))⁻¹ := by simp [toReal_inv]
      _ = toReal (0 : CReal) := by simp

/-! ### Conditional completeness (transported from `ℝ`) -/

noncomputable instance : SupSet CReal := ⟨fun s => FromReal.ofReal (sSup (toReal '' s))⟩
noncomputable instance : InfSet CReal := ⟨fun s => FromReal.ofReal (sInf (toReal '' s))⟩

theorem bddAbove_image_toReal_iff (s : Set CReal) : BddAbove (toReal '' s) ↔ BddAbove s := by
  constructor
  · intro hs
    rcases hs with ⟨r, hr⟩
    refine ⟨FromReal.ofReal r, ?_⟩
    intro x hx
    have : toReal x ≤ r := hr (a := toReal x) ⟨x, hx, rfl⟩
    -- reflect back
    have : toReal x ≤ toReal (FromReal.ofReal r) := by simpa [toReal_ofReal] using this
    exact (toReal_le_iff).1 this
  · intro hs
    rcases hs with ⟨a, ha⟩
    refine ⟨toReal a, ?_⟩
    intro r hr
    rcases hr with ⟨x, hx, rfl⟩
    exact toReal_mono (ha hx)

theorem bddBelow_image_toReal_iff (s : Set CReal) : BddBelow (toReal '' s) ↔ BddBelow s := by
  constructor
  · intro hs
    rcases hs with ⟨r, hr⟩
    refine ⟨FromReal.ofReal r, ?_⟩
    intro x hx
    have : r ≤ toReal x := hr (a := toReal x) ⟨x, hx, rfl⟩
    have : toReal (FromReal.ofReal r) ≤ toReal x := by simpa [toReal_ofReal] using this
    exact (toReal_le_iff).1 this
  · intro hs
    rcases hs with ⟨a, ha⟩
    refine ⟨toReal a, ?_⟩
    intro r hr
    rcases hr with ⟨x, hx, rfl⟩
    exact toReal_mono (ha hx)

noncomputable instance : ConditionallyCompleteLattice CReal := by
  classical
  refine ConditionallyCompleteLattice.mk (α := CReal) ?_ ?_ ?_ ?_
  · -- le_csSup
    intro s a hs ha
    have hs' : BddAbove (toReal '' s) := (bddAbove_image_toReal_iff s).2 hs
    have hℝ : toReal a ≤ sSup (toReal '' s) :=
      ConditionallyCompleteLattice.le_csSup (s := toReal '' s) (a := toReal a) hs' ⟨a, ha, rfl⟩
    have : toReal a ≤ toReal (sSup s) := by
      simpa [SupSet.sSup, toReal_ofReal] using hℝ
    exact (toReal_le_iff).1 this
  · -- csSup_le
    intro s a hs ha
    have hs' : Set.Nonempty (toReal '' s) := hs.image toReal
    have hub : toReal a ∈ upperBounds (toReal '' s) := by
      intro r hr
      rcases hr with ⟨x, hx, rfl⟩
      exact toReal_mono (ha hx)
    have hℝ : sSup (toReal '' s) ≤ toReal a :=
      ConditionallyCompleteLattice.csSup_le (s := toReal '' s) (a := toReal a) hs' hub
    have : toReal (sSup s) ≤ toReal a := by
      simpa [SupSet.sSup, toReal_ofReal] using hℝ
    exact (toReal_le_iff).1 this
  · -- csInf_le
    intro s a hs ha
    have hs' : BddBelow (toReal '' s) := (bddBelow_image_toReal_iff s).2 hs
    have hℝ : sInf (toReal '' s) ≤ toReal a :=
      ConditionallyCompleteLattice.csInf_le (s := toReal '' s) (a := toReal a) hs' ⟨a, ha, rfl⟩
    have : toReal (sInf s) ≤ toReal a := by
      simpa [InfSet.sInf, toReal_ofReal] using hℝ
    exact (toReal_le_iff).1 this
  · -- le_csInf
    intro s a hs ha
    have hs' : Set.Nonempty (toReal '' s) := hs.image toReal
    have hlb : toReal a ∈ lowerBounds (toReal '' s) := by
      intro r hr
      rcases hr with ⟨x, hx, rfl⟩
      exact toReal_mono (ha hx)
    have hℝ : toReal a ≤ sInf (toReal '' s) :=
      ConditionallyCompleteLattice.le_csInf (s := toReal '' s) (a := toReal a) hs' hlb
    have : toReal a ≤ toReal (sInf s) := by
      simpa [InfSet.sInf, toReal_ofReal] using hℝ
    exact (toReal_le_iff).1 this

noncomputable instance : ConditionallyCompleteLinearOrder CReal := by
  classical
  refine ConditionallyCompleteLinearOrder.mk (α := CReal)
    (le_total := le_total)
    (toDecidableLE := fun a b => Classical.decRel (fun x y : CReal => x ≤ y) a b)
    (toDecidableEq := Classical.decEq CReal)
    (toDecidableLT := fun a b => Classical.decRel (fun x y : CReal => x < y) a b)
    (csSup_of_not_bddAbove := ?_)
    (csInf_of_not_bddBelow := ?_)
  · intro s hs
    apply toReal_injective
    have hs' : ¬ BddAbove (toReal '' s) := by
      intro h
      exact hs ((bddAbove_image_toReal_iff s).1 h)
    simpa [SupSet.sSup, toReal_ofReal] using
      (csSup_of_not_bddAbove (α := ℝ) (s := toReal '' s) hs')
  · intro s hs
    apply toReal_injective
    have hs' : ¬ BddBelow (toReal '' s) := by
      intro h
      exact hs ((bddBelow_image_toReal_iff s).1 h)
    simpa [InfSet.sInf, toReal_ofReal] using
      (csInf_of_not_bddBelow (α := ℝ) (s := toReal '' s) hs')

noncomputable instance : IsOrderedAddMonoid CReal :=
  IsOrderedAddMonoid.mk
    (fun a b hab c => by
      -- use the existing `add_le_add_left` lemma (stated with `c + _`)
      simpa [add_comm] using (Computable.CReal.add_le_add_left a b hab c))
    (fun a b hab c => by
      simpa using (Computable.CReal.add_le_add_left a b hab c))

noncomputable instance : IsOrderedCancelAddMonoid CReal := by
  classical
  refine IsOrderedCancelAddMonoid.mk (α := CReal) ?_ ?_
  · intro a b c h
    have hℝ : toReal a + toReal b ≤ toReal a + toReal c := by
      simpa [toReal_add] using toReal_mono h
    have : toReal b ≤ toReal c := _root_.le_of_add_le_add_left hℝ
    exact (toReal_le_iff).1 this
  · intro a b c h
    have hℝ : toReal b + toReal a ≤ toReal c + toReal a := by
      simpa [toReal_add] using toReal_mono h
    have : toReal b ≤ toReal c := _root_.le_of_add_le_add_right hℝ
    exact (toReal_le_iff).1 this

noncomputable instance : PosMulStrictMono CReal := by
  classical
  refine PosMulStrictMono.mk (α := CReal) ?_
  intro a ha b c hbc
  refine (toReal_lt_iff).1 ?_
  have haℝ : (0 : ℝ) < toReal a := by
    simpa using (toReal_lt_iff (x := (0 : CReal)) (y := a)).2 ha
  have hbcℝ : toReal b < toReal c := (toReal_lt_iff (x := b) (y := c)).2 hbc
  -- transport strict monotonicity from `ℝ`
  simpa [toReal_mul] using (mul_lt_mul_of_pos_left hbcℝ haℝ)

noncomputable instance : MulPosStrictMono CReal := by
  classical
  refine MulPosStrictMono.mk (α := CReal) ?_
  intro c hc a b hab
  refine (toReal_lt_iff).1 ?_
  have hcℝ : (0 : ℝ) < toReal c := by
    simpa using (toReal_lt_iff (x := (0 : CReal)) (y := c)).2 hc
  have habℝ : toReal a < toReal b := (toReal_lt_iff (x := a) (y := b)).2 hab
  simpa [toReal_mul] using (mul_lt_mul_of_pos_right habℝ hcℝ)

noncomputable instance : IsStrictOrderedRing CReal := by
  classical
  -- all required mixins are now available
  exact IsStrictOrderedRing.mk

noncomputable instance : ConditionallyCompleteLinearOrderedField CReal := by
  classical
  exact
    { (inferInstance : Field CReal), (inferInstance : ConditionallyCompleteLinearOrder CReal),
      (inferInstance : IsStrictOrderedRing CReal) with }

end CReal
end Computable
