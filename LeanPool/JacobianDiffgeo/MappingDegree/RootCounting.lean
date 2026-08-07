/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

/-
Blueprint unit: mapping-degree. Planar root counting: total multiplicity of `z ↦ z ^ k` is `k`.
-/
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Card

/-!
# Planar root counting (mapping-degree, planar layer)

Everything about the roots of `z ^ k = w` in `ℂ` that the surface-level fiber count needs:

* `RS.exists_pow_eq` — `k`-th roots exist (via `exp`/`log`, avoiding the FTA import);
* `RS.setOf_pow_eq_finite`, `RS.ncard_setOf_pow_eq` — the root set is finite, of cardinality `k`
  when `w ≠ 0`;
* `RS.norm_lt_of_pow_eq` — roots are trapped in the ball whose `k`-th power ball contains `w`;
* `RS.analyticOrderAt_pow_zero`, `RS.analyticOrderAt_pow_sub_pow` — vanishing orders of
  `z ↦ z ^ k` (order `k` at `0`) and `z ↦ z ^ k - ζ ^ k` (order `1` at `ζ ≠ 0`);
* `RS.sum_toNat_analyticOrderAt_pow_sub` — **THE planar counting identity**: the total
  multiplicity of `z ↦ z ^ k` over any `w : ℂ` is `k`, uniformly in `w` (no
  branched/unbranched case split for consumers).

This file has zero project imports; `LocalConstancy.lean` bridges `analyticOrderAt` to
`RS.multiplicity` via local-multiplicity's chart invariance.
-/

open Filter Set Polynomial
open scoped Topology

namespace RS

/-- `k`-th roots exist in `ℂ` (via `exp`/`log`; deliberately avoids
`IsAlgClosed.exists_pow_nat_eq`, whose instance would drag in the FTA import). -/
theorem exists_pow_eq {k : ℕ} (hk : k ≠ 0) {w : ℂ} (hw : w ≠ 0) : ∃ α : ℂ, α ^ k = w := by
  refine ⟨Complex.exp (Complex.log w / k), ?_⟩
  rw [← Complex.exp_nat_mul]
  have h : (k : ℂ) * (Complex.log w / k) = Complex.log w := by
    rw [mul_div_assoc']
    exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hk)
  rw [h, Complex.exp_log hw]

theorem setOf_pow_eq_zero {k : ℕ} (hk : k ≠ 0) : {z : ℂ | z ^ k = 0} = {0} := by
  ext z
  simp [pow_eq_zero_iff hk]

/-- The root set of `z ^ k = w`, as the coercion of the `nthRoots` finset. -/
theorem setOf_pow_eq_coe_toFinset {k : ℕ} (hk : k ≠ 0) (w : ℂ) :
    {z : ℂ | z ^ k = w} = ↑(nthRoots k w).toFinset := by
  ext z
  simp [Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hk)]

theorem setOf_pow_eq_finite {k : ℕ} (hk : k ≠ 0) (w : ℂ) : {z : ℂ | z ^ k = w}.Finite := by
  rw [setOf_pow_eq_coe_toFinset hk w]
  exact (nthRoots k w).toFinset.finite_toSet

theorem card_nthRoots_toFinset {k : ℕ} (hk : k ≠ 0) {w : ℂ} (hw : w ≠ 0) :
    (nthRoots k w).toFinset.card = k := by
  have hprim := Complex.isPrimitiveRoot_exp k hk
  rw [Multiset.toFinset_card_of_nodup (hprim.nthRoots_nodup hw), hprim.card_nthRoots,
    if_pos (exists_pow_eq hk hw)]

theorem ncard_setOf_pow_eq {k : ℕ} (hk : k ≠ 0) {w : ℂ} (hw : w ≠ 0) :
    {z : ℂ | z ^ k = w}.ncard = k := by
  rw [setOf_pow_eq_coe_toFinset hk w, Set.ncard_coe_finset]
  exact card_nthRoots_toFinset hk hw

/-- Roots are trapped in the ball whose `k`-th power ball contains `w`. -/
theorem norm_lt_of_pow_eq {k : ℕ} (hk : k ≠ 0) {z w : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : z ^ k = w) (hw : ‖w‖ < ρ ^ k) : ‖z‖ < ρ := by
  have h1 : ‖z‖ ^ k < ρ ^ k := by rw [← norm_pow, h]; exact hw
  exact (pow_lt_pow_iff_left₀ (norm_nonneg z) hρ hk).mp h1

theorem analyticOrderAt_pow_zero (k : ℕ) :
    analyticOrderAt (fun z : ℂ ↦ z ^ k) 0 = (k : ℕ∞) := by
  have ha : AnalyticAt ℂ (fun z : ℂ ↦ z ^ k) 0 := by fun_prop
  rw [ha.analyticOrderAt_eq_natCast]
  exact ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero, Eventually.of_forall fun z ↦ by simp⟩

theorem analyticOrderAt_pow_sub_pow {k : ℕ} (hk : k ≠ 0) {ζ : ℂ} (hζ : ζ ≠ 0) :
    analyticOrderAt (fun z : ℂ ↦ z ^ k - ζ ^ k) ζ = 1 := by
  have hpow : AnalyticAt ℂ (fun z : ℂ ↦ z ^ k) ζ := by fun_prop
  have hder : deriv (fun z : ℂ ↦ z ^ k) ζ ≠ 0 := by
    rw [deriv_pow_field]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hk) (pow_ne_zero _ hζ)
  simpa using hpow.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hder

/-- **THE planar counting identity**: the total multiplicity of `z ↦ z ^ k` over any `w` is `k`
(one root of order `k` when `w = 0`; `k` simple roots otherwise). Uniform in `w`, so surface
consumers need no branched/unbranched case split. -/
theorem sum_toNat_analyticOrderAt_pow_sub {k : ℕ} (hk : k ≠ 0) (w : ℂ) :
    ∑ᶠ ζ ∈ {z : ℂ | z ^ k = w}, (analyticOrderAt (fun z : ℂ ↦ z ^ k - w) ζ).toNat = k := by
  rcases eq_or_ne w 0 with rfl | hw
  · -- one root of full order `k`
    rw [setOf_pow_eq_zero hk, finsum_mem_singleton]
    simp only [sub_zero]
    rw [analyticOrderAt_pow_zero k]
    exact ENat.toNat_natCast k
  · -- `k` simple roots
    have h1 : ∀ ζ ∈ {z : ℂ | z ^ k = w},
        (analyticOrderAt (fun z : ℂ ↦ z ^ k - w) ζ).toNat = 1 := by
      intro ζ hζ
      have hζw : ζ ^ k = w := hζ
      have hζ0 : ζ ≠ 0 := by
        rintro rfl
        rw [zero_pow hk] at hζw
        exact hw hζw.symm
      rw [← hζw, analyticOrderAt_pow_sub_pow hk hζ0]
      rfl
    calc ∑ᶠ ζ ∈ {z : ℂ | z ^ k = w}, (analyticOrderAt (fun z : ℂ ↦ z ^ k - w) ζ).toNat
        = ∑ᶠ ζ ∈ {z : ℂ | z ^ k = w}, (1 : ℕ) := finsum_mem_congr rfl h1
      _ = ∑ ζ ∈ (nthRoots k w).toFinset, (1 : ℕ) := by
          rw [setOf_pow_eq_coe_toFinset hk w, finsum_mem_coe_finset]
      _ = (nthRoots k w).toFinset.card := by
          rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ = k := card_nthRoots_toFinset hk hw

end RS
