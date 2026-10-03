/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTinyTransfer
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesTwistie1Flow

/-! # Weighted pointwise bound for `∇ ∇·(B ∇T)`

`sc_gradDiv_vecNormSq_le` loses the factor `r²` on every term of the Leibniz expansion.
Here the coefficient of order `p` is weighted by `L^{|p|}` and the corresponding word of `T` of
    order
`2 - |p|` keeps the weight `L^{2-|p|}`, so that with the `T` jets at the same rate `L` the total
    loss
is a single factor `L²` (the source gets `ε_{m-1}^{-2-γ}` from `∇³ T`, `∇² T ∇B`, `∇T ∇²B`). -/

@[expose] public section

open Homogenization
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5 AVenhance.Infra.Section4

/-- The weighted word sum. -/
def seWordSum (L : ℝ) (v : Vec 2 → ℝ) (x : Vec 2) : ℝ :=
  ∑ w ∈ scWords2, L ^ (2 - w.length) *
    Real.sqrt (vecNormSq (spaceGrad (iterateSpatialWord w v) x))

theorem se_flux_term_abs_le {A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : Vec 2 → ℝ} (x : Vec 2)
    {D L : ℝ} (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hAj : ∀ p : List (Fin 2), p.length ≤ 2 → ∀ j k,
      |iterateMatrixWord A p x j k| ≤ D * (p.length.factorial : ℝ) * L ^ p.length)
    (w : List (Fin 2)) (hw : w.length = 2) {p : List (Fin 2) × List (Fin 2)}
    (hp : p ∈ iterateSpatialSplits w) (k j : Fin 2) :
    |iterateSpatialWord p.1 (fun y => A y k j) x * spaceGrad (iterateSpatialWord p.2 v) x j| ≤
      2 * D * seWordSum L v x := by
  have hord := iterateSpatialSplits_orders w hp
  have h1 : p.1.length ≤ 2 := by omega
  have h2 : p.2.length ≤ 2 := by omega
  have hcoef := hAj p.1 h1 k j
  have hfac : (p.1.length.factorial : ℝ) ≤ 2 := by
    interval_cases hl : p.1.length <;> norm_num [Nat.factorial]
  have hcoef' : |iterateSpatialWord p.1 (fun y => A y k j) x| ≤ 2 * D * L ^ p.1.length := by
    refine hcoef.trans ?_
    have hf0 : (0 : ℝ) ≤ (p.1.length.factorial : ℝ) := Nat.cast_nonneg _
    calc D * (p.1.length.factorial : ℝ) * L ^ p.1.length ≤ D * 2 * L ^ p.1.length := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfac hD) (by positivity)
      _ = 2 * D * L ^ p.1.length := by ring
  have hgrad : |spaceGrad (iterateSpatialWord p.2 v) x j| ≤
      Real.sqrt (vecNormSq (spaceGrad (iterateSpatialWord p.2 v) x)) :=
    RelativeError.abs_apply_le_sqrt_vecNormSq _ j
  have hexp : p.1.length = 2 - p.2.length := by omega
  have hterm : L ^ (2 - p.2.length) *
      Real.sqrt (vecNormSq (spaceGrad (iterateSpatialWord p.2 v) x)) ≤ seWordSum L v x := by
    unfold seWordSum
    exact Finset.single_le_sum (f := fun w' => L ^ (2 - w'.length) *
      Real.sqrt (vecNormSq (spaceGrad (iterateSpatialWord w' v) x)))
      (fun _ _ => by positivity) (mem_scWords2 h2)
  rw [abs_mul]
  calc _ ≤ (2 * D * L ^ p.1.length) *
        Real.sqrt (vecNormSq (spaceGrad (iterateSpatialWord p.2 v) x)) :=
        mul_le_mul hcoef' hgrad (abs_nonneg _) (by positivity)
    _ = 2 * D * (L ^ (2 - p.2.length) *
        Real.sqrt (vecNormSq (spaceGrad (iterateSpatialWord p.2 v) x))) := by
        rw [hexp]; ring
    _ ≤ 2 * D * seWordSum L v x := mul_le_mul_of_nonneg_left hterm (by positivity)

theorem se_gradDiv_abs_le {A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : Vec 2 → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hv : ContDiff ℝ (⊤ : ℕ∞) v) (x : Vec 2)
    {D L : ℝ} (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hAj : ∀ p : List (Fin 2), p.length ≤ 2 → ∀ j k,
      |iterateMatrixWord A p x j k| ≤ D * (p.length.factorial : ℝ) * L ^ p.length)
    (i : Fin 2) :
    |spaceGrad (vecDiv (fun y => (A y).mulVec (spaceGrad v y))) x i| ≤
      32 * D * seWordSum L v x := by
  set S : ℝ := seWordSum L v x with hS
  have hterm : ∀ k : Fin 2, |iterateWordFlux A v [k, i] x k| ≤ 16 * D * S := by
    intro k
    unfold iterateWordFlux
    have hj : ∀ j : Fin 2, |((iterateSpatialSplits [k, i]).map (fun p =>
        iterateSpatialWord p.1 (fun y => A y k j) x *
          spaceGrad (iterateSpatialWord p.2 v) x j)).sum| ≤ 8 * D * S := by
      intro j
      have hlen : (iterateSpatialSplits [k, i]).length = 4 := by
        simpa using iterateSpatialSplits_length [k, i]
      have h := sc_list_abs_sum_le (iterateSpatialSplits [k, i]) (fun p =>
        iterateSpatialWord p.1 (fun y => A y k j) x *
          spaceGrad (iterateSpatialWord p.2 v) x j) (2 * D * S)
        (fun p hp => se_flux_term_abs_le x hD hL hAj [k, i] rfl hp k j)
      rw [hlen] at h
      calc _ ≤ ((4 : ℕ) : ℝ) * (2 * D * S) := h
        _ = 8 * D * S := by push_cast; ring
    calc _ ≤ |((iterateSpatialSplits [k, i]).map (fun p =>
          iterateSpatialWord p.1 (fun y => A y k 0) x *
            spaceGrad (iterateSpatialWord p.2 v) x 0)).sum| +
        |((iterateSpatialSplits [k, i]).map (fun p =>
          iterateSpatialWord p.1 (fun y => A y k 1) x *
            spaceGrad (iterateSpatialWord p.2 v) x 1)).sum| := by
          rw [Fin.sum_univ_two]; exact abs_add_le _ _
      _ ≤ 8 * D * S + 8 * D * S := add_le_add (hj 0) (hj 1)
      _ = 16 * D * S := by ring
  rw [sc_gradDiv_flux_eq hA hv x i]
  calc _ ≤ |iterateWordFlux A v [0, i] x 0| + |iterateWordFlux A v [1, i] x 1| := by
        rw [Fin.sum_univ_two]; exact abs_add_le _ _
    _ ≤ 16 * D * S + 16 * D * S := add_le_add (hterm 0) (hterm 1)
    _ = 32 * D * S := by ring

/-- **Weighted pointwise bound**:
`|∇ ∇·(A ∇v)|² ≤ 14336 D² ∑_{|w| ≤ 2} L^{2(2-|w|)} |∇ ∂^w v|²`. -/
theorem se_gradDiv_vecNormSq_le {A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : Vec 2 → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hv : ContDiff ℝ (⊤ : ℕ∞) v) (x : Vec 2)
    {D L : ℝ} (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hAj : ∀ p : List (Fin 2), p.length ≤ 2 → ∀ j k,
      |iterateMatrixWord A p x j k| ≤ D * (p.length.factorial : ℝ) * L ^ p.length) :
    vecNormSq (spaceGrad (vecDiv (fun y => (A y).mulVec (spaceGrad v y))) x) ≤
      14336 * D ^ 2 * ∑ w ∈ scWords2, (L ^ (2 - w.length)) ^ 2 *
        vecNormSq (spaceGrad (iterateSpatialWord w v) x) := by
  set S : ℝ := seWordSum L v x with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  have hcs : S ^ 2 ≤ 7 * ∑ w ∈ scWords2, (L ^ (2 - w.length)) ^ 2 *
      vecNormSq (spaceGrad (iterateSpatialWord w v) x) := by
    have h := sq_sum_le_card_mul_sum_sq (s := scWords2)
      (f := fun w => L ^ (2 - w.length) *
        Real.sqrt (vecNormSq (spaceGrad (iterateSpatialWord w v) x)))
    rw [sc_card_scWords2] at h
    have hsq : ∀ w ∈ scWords2, (L ^ (2 - w.length) *
        Real.sqrt (vecNormSq (spaceGrad (iterateSpatialWord w v) x))) ^ 2 =
        (L ^ (2 - w.length)) ^ 2 * vecNormSq (spaceGrad (iterateSpatialWord w v) x) :=
      fun w _ => by rw [mul_pow, Real.sq_sqrt (vecNormSq_nonneg _)]
    rw [Finset.sum_congr rfl hsq] at h
    exact_mod_cast h
  have hb := fun i => se_gradDiv_abs_le hA hv x hD hL hAj i
  rw [sc_vecNormSq_eq]
  have h0 := hb 0
  have h1 := hb 1
  have e0 : spaceGrad (vecDiv (fun y => (A y).mulVec (spaceGrad v y))) x 0 *
      spaceGrad (vecDiv (fun y => (A y).mulVec (spaceGrad v y))) x 0 ≤
      (32 * D * S) ^ 2 := by
    rw [← sq]; exact sq_le_sq' (by linarith [abs_le.mp h0]) (abs_le.mp h0).2
  have e1 : spaceGrad (vecDiv (fun y => (A y).mulVec (spaceGrad v y))) x 1 *
      spaceGrad (vecDiv (fun y => (A y).mulVec (spaceGrad v y))) x 1 ≤
      (32 * D * S) ^ 2 := by
    rw [← sq]; exact sq_le_sq' (by linarith [abs_le.mp h1]) (abs_le.mp h1).2
  calc _ ≤ 2 * (32 * D * S) ^ 2 := by linarith
    _ = 2048 * D ^ 2 * S ^ 2 := by ring
    _ ≤ 2048 * D ^ 2 * (7 * ∑ w ∈ scWords2, (L ^ (2 - w.length)) ^ 2 *
          vecNormSq (spaceGrad (iterateSpatialWord w v) x)) := by
        apply mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = _ := by ring

end AVenhance.Infra.Section5.Contracts
end
