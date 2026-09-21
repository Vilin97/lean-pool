/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/

import LeanPool.LiCriterion.Hadamard.Basic
import LeanPool.LiCriterion.Hadamard.OrderOne.CofiniteControl

/-!
Local-uniform convergence (and hence holomorphy) of the genus‑1 Weierstrass product
`∏' i, weierstrassE 1 (s / z i)` under the standard hypothesis `∑ 1/‖z i‖² < ∞`
and a nonzero condition on the `z i`.
-/

open Complex Filter
open scoped BigOperators

namespace Hadamard
namespace OrderOne

theorem hasProdLocallyUniformlyOn_weierstrass_E_one_of_summable_inv_norm_sq {ι : Type} {z : ι → ℂ}
    (hz0 : ∀ i, z i ≠ 0)
    (h : Summable (fun i : ι => (1 : ℝ) / ‖z i‖ ^ 2)) :
    HasProdLocallyUniformlyOn (fun i (w : ℂ) => weierstrassE 1 (w / z i))
      (fun w : ℂ => ∏' i : ι, weierstrassE 1 (w / z i)) (Set.univ : Set ℂ) := by
  classical
  refine hasProdLocallyUniformlyOn_of_forall_compact (β := ℂ)
      (f := fun i (w : ℂ) => weierstrassE 1 (w / z i))
      (g := fun w : ℂ => ∏' i : ι, weierstrassE 1 (w / z i))
      isOpen_univ ?_
  intro K hKsub hK
  -- Compact sets are bounded, hence contained in some closed ball.
  obtain ⟨R0, hKR0⟩ := (hK.isBounded.subset_closedBall (0 : ℂ))
  -- Use `R = max R0 1` to ensure `R > 0`.
  let R : ℝ := max R0 1
  have hRpos : 0 < R := by
    have : (0 : ℝ) < 1 := by norm_num
    exact lt_of_lt_of_le this (le_max_right R0 1)
  have hKnorm : ∀ w ∈ K, ‖w‖ ≤ R := by
    intro w hw
    have hw' : w ∈ Metric.closedBall (0 : ℂ) R0 := hKR0 hw
    have hwR0 : ‖w‖ ≤ R0 := by
      have : dist w 0 ≤ R0 := by
        simpa [Metric.mem_closedBall] using hw'
      simpa [dist_eq_norm] using this
    exact le_trans hwR0 (le_max_left R0 1)
  -- Exclude finitely many indices with `‖z i‖ ≤ 2R`.
  let S : Set ι := {i : ι | ‖z i‖ ≤ (2 : ℝ) * R}
  have hSfinite : S.Finite :=
    finite_norm_le_of_summable_inv_norm_sq (z := z) hz0 h (R := (2 : ℝ) * R) (by nlinarith [hRpos])
  have hnotS : ∀ᶠ i in (cofinite : Filter ι), i ∉ S := by
    have : (Sᶜ : Set ι) ∈ (cofinite : Filter ι) := by
      exact Filter.mem_cofinite.2 (by simpa using hSfinite)
    simpa using this
  -- A summable comparison series on `K`.
  let u : ι → ℝ := fun i => (4 * R ^ 2) * ((1 : ℝ) / ‖z i‖ ^ 2)
  have hu : Summable u := by
    simpa [u] using h.mul_left (4 * R ^ 2)
  -- Eventual bound by `u` on `K`.
  have hbound :
      ∀ᶠ i in (cofinite : Filter ι), ∀ w ∈ K,
        ‖(weierstrassE 1 (w / z i) - 1 : ℂ)‖ ≤ u i := by
    filter_upwards [hnotS] with i hi w hwK
    have hwR : ‖w‖ ≤ R := hKnorm w hwK
    have hz_gt : (2 : ℝ) * R < ‖z i‖ := by
      have : ¬‖z i‖ ≤ (2 : ℝ) * R := by simpa [S] using hi
      exact lt_of_not_ge this
    have hz_pos : 0 < ‖z i‖ := norm_pos_iff.2 (hz0 i)
    have hw_le : ‖w‖ ≤ (1 / 2 : ℝ) * ‖z i‖ := by
      have hz_ge : (2 : ℝ) * R ≤ ‖z i‖ := le_of_lt hz_gt
      have hRle : R ≤ (1 / 2 : ℝ) * ‖z i‖ := by linarith [hz_ge]
      exact le_trans hwR hRle
    have hw_div : ‖w‖ / ‖z i‖ ≤ (1 / 2 : ℝ) := (div_le_iff₀ hz_pos).2 hw_le
    have hw_div' : ‖w / z i‖ ≤ (1 / 2 : ℝ) := by simpa [norm_div] using hw_div
    have hE :
        ‖(weierstrassE 1 (w / z i) - 1 : ℂ)‖ ≤ 4 * ‖w / z i‖ ^ 2 := by
      have hE' := weierstrass_E_small_disk_norm_sub_one_le (h := 1) (z := w / z i) hw_div'
      simpa using hE'
    have hw2 : ‖w‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg w) hwR 2
    have hzterm_nonneg : 0 ≤ (1 : ℝ) / ‖z i‖ ^ 2 := by positivity
    have hmul' :
        (4 * ‖w‖ ^ 2) * ((1 : ℝ) / ‖z i‖ ^ 2) ≤ (4 * R ^ 2) * ((1 : ℝ) / ‖z i‖ ^ 2) := by
      have hw2' :
          (‖w‖ ^ 2) * ((1 : ℝ) / ‖z i‖ ^ 2) ≤ (R ^ 2) * ((1 : ℝ) / ‖z i‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hw2 hzterm_nonneg
      have :=
          mul_le_mul_of_nonneg_left hw2' (by norm_num : 0 ≤ (4 : ℝ))
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    have hrewrite : 4 * ‖w / z i‖ ^ 2 = (4 * ‖w‖ ^ 2) * ((1 : ℝ) / ‖z i‖ ^ 2) := by
      simp [pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    calc
      ‖(weierstrassE 1 (w / z i) - 1 : ℂ)‖ ≤ 4 * ‖w / z i‖ ^ 2 := hE
      _ = (4 * ‖w‖ ^ 2) * ((1 : ℝ) / ‖z i‖ ^ 2) := hrewrite
      _ ≤ (4 * R ^ 2) * ((1 : ℝ) / ‖z i‖ ^ 2) := hmul'
      _ = u i := by simp [u]
  have hcts :
      ∀ i, ContinuousOn (fun w : ℂ => (weierstrassE 1 (w / z i) - 1 : ℂ)) K := by
    intro i
    have hE : Continuous (fun w : ℂ => weierstrassE 1 (w / z i)) :=
      (weierstrass_E_continuous 1).comp (by fun_prop)
    exact (hE.sub continuous_const).continuousOn
  have hprod :
      HasProdUniformlyOn
        (fun i (w : ℂ) => (1 : ℂ) + (weierstrassE 1 (w / z i) - 1))
        (fun w : ℂ => ∏' i : ι, ((1 : ℂ) + (weierstrassE 1 (w / z i) - 1))) K := by
    simpa using
      (Summable.hasProdUniformlyOn_one_add (α := ℂ) (R := ℂ) (K := K) hK hu hbound hcts)
  -- Rewrite `1 + (E - 1) = E`.
  simpa using hprod

theorem differentiableOn_tprod_weierstrass_E_one_of_summable_inv_norm_sq {ι : Type} {z : ι → ℂ}
    (hz0 : ∀ i, z i ≠ 0)
    (h : Summable (fun i : ι => (1 : ℝ) / ‖z i‖ ^ 2)) :
    DifferentiableOn ℂ (fun w : ℂ => ∏' i : ι, weierstrassE 1 (w / z i)) (Set.univ : Set ℂ) := by
  classical
  have hprod :
      HasProdLocallyUniformlyOn (fun i (w : ℂ) => weierstrassE 1 (w / z i))
        (fun w : ℂ => ∏' i : ι, weierstrassE 1 (w / z i)) (Set.univ : Set ℂ) :=
    hasProdLocallyUniformlyOn_weierstrass_E_one_of_summable_inv_norm_sq (z := z) hz0 h
  have hseq :
      TendstoLocallyUniformlyOn
        (fun s (w : ℂ) => ∏ i ∈ s, weierstrassE 1 (w / z i))
        (fun w : ℂ => ∏' i : ι, weierstrassE 1 (w / z i))
        (atTop : Filter (Finset ι)) (Set.univ : Set ℂ) := by
    simpa [HasProdLocallyUniformlyOn] using hprod
  have hdiff :
      ∀ᶠ s in (atTop : Filter (Finset ι)),
        DifferentiableOn ℂ
          (fun w : ℂ => ∏ i ∈ s, weierstrassE 1 (w / z i))
          (Set.univ : Set ℂ) := by
    refine Filter.Eventually.of_forall ?_
    intro s
    have hfun :
        DifferentiableOn ℂ
          (∏ i ∈ s, (fun w : ℂ => weierstrassE 1 (w / z i)))
          (Set.univ : Set ℂ) := by
      refine DifferentiableOn.finsetProd (𝕜 := ℂ) (𝔸' := ℂ) ?_
      intro i hi
      have hE : Differentiable ℂ (weierstrassE 1) := weierstrass_E_differentiable 1
      have hdiv : Differentiable ℂ (fun w : ℂ => w / z i) := by fun_prop
      exact (hE.comp hdiv).differentiableOn
    simpa [Finset.prod_fn] using hfun
  simpa using hseq.differentiableOn hdiff isOpen_univ

/-- **Rank-`p` analogue of
`hasProdLocallyUniformlyOn_weierstrass_E_one_of_summable_inv_norm_sq`.** -/
theorem hasProdLocallyUniformlyOn_weierstrass_E_of_summable_inv_norm_pow
    {ι : Type*} {z : ι → ℂ} {p : ℕ}
    (hz0 : ∀ i, z i ≠ 0)
    (h : Summable (fun i : ι => (1 : ℝ) / ‖z i‖ ^ (p + 1))) :
    HasProdLocallyUniformlyOn (fun i (w : ℂ) => weierstrassE p (w / z i))
      (fun w : ℂ => ∏' i : ι, weierstrassE p (w / z i)) (Set.univ : Set ℂ) := by
  classical
  refine hasProdLocallyUniformlyOn_of_forall_compact (β := ℂ)
      (f := fun i (w : ℂ) => weierstrassE p (w / z i))
      (g := fun w : ℂ => ∏' i : ι, weierstrassE p (w / z i))
      isOpen_univ ?_
  intro K hKsub hK
  obtain ⟨R0, hKR0⟩ := (hK.isBounded.subset_closedBall (0 : ℂ))
  let R : ℝ := max R0 1
  have hRpos : 0 < R := by
    have : (0 : ℝ) < 1 := by norm_num
    exact lt_of_lt_of_le this (le_max_right R0 1)
  have hKnorm : ∀ w ∈ K, ‖w‖ ≤ R := by
    intro w hw
    have hw' : w ∈ Metric.closedBall (0 : ℂ) R0 := hKR0 hw
    have hwR0 : ‖w‖ ≤ R0 := by
      have : dist w 0 ≤ R0 := by
        simpa [Metric.mem_closedBall] using hw'
      simpa [dist_eq_norm] using this
    exact le_trans hwR0 (le_max_left R0 1)
  -- Exclude finitely many indices with `‖z i‖ ≤ 2R`.
  let S : Set ι := {i : ι | ‖z i‖ ≤ (2 : ℝ) * R}
  have hSfinite : S.Finite :=
    finite_norm_le_of_summable_inv_norm_pow (z := z) (p := p) hz0 h
      (R := (2 : ℝ) * R) (by nlinarith [hRpos])
  have hnotS : ∀ᶠ i in (cofinite : Filter ι), i ∉ S := by
    have : (Sᶜ : Set ι) ∈ (cofinite : Filter ι) := by
      exact Filter.mem_cofinite.2 (by simpa using hSfinite)
    simpa using this
  -- Summable majorant on `K`.
  let u : ι → ℝ := fun i => (4 * R ^ (p + 1)) * ((1 : ℝ) / ‖z i‖ ^ (p + 1))
  have hu : Summable u := by
    simpa [u] using h.mul_left (4 * R ^ (p + 1))
  -- Eventual bound by `u` on `K`.
  have hbound :
      ∀ᶠ i in (cofinite : Filter ι), ∀ w ∈ K,
        ‖(weierstrassE p (w / z i) - 1 : ℂ)‖ ≤ u i := by
    filter_upwards [hnotS] with i hi w hwK
    have hwR : ‖w‖ ≤ R := hKnorm w hwK
    have hz_gt : (2 : ℝ) * R < ‖z i‖ := by
      have : ¬‖z i‖ ≤ (2 : ℝ) * R := by simpa [S] using hi
      exact lt_of_not_ge this
    have hz_pos : 0 < ‖z i‖ := norm_pos_iff.2 (hz0 i)
    have hw_le : ‖w‖ ≤ (1 / 2 : ℝ) * ‖z i‖ := by
      have hz_ge : (2 : ℝ) * R ≤ ‖z i‖ := le_of_lt hz_gt
      have hRle : R ≤ (1 / 2 : ℝ) * ‖z i‖ := by linarith [hz_ge]
      exact le_trans hwR hRle
    have hw_div : ‖w‖ / ‖z i‖ ≤ (1 / 2 : ℝ) := (div_le_iff₀ hz_pos).2 hw_le
    have hw_div' : ‖w / z i‖ ≤ (1 / 2 : ℝ) := by simpa [norm_div] using hw_div
    have hE :
        ‖(weierstrassE p (w / z i) - 1 : ℂ)‖ ≤ 4 * ‖w / z i‖ ^ (p + 1) :=
      weierstrass_E_small_disk_norm_sub_one_le (h := p) (z := w / z i) hw_div'
    have hw_pow : ‖w‖ ^ (p + 1) ≤ R ^ (p + 1) :=
      pow_le_pow_left₀ (norm_nonneg w) hwR (p + 1)
    have hzterm_nonneg : 0 ≤ (1 : ℝ) / ‖z i‖ ^ (p + 1) := by positivity
    have hmul' :
        (4 * ‖w‖ ^ (p + 1)) * ((1 : ℝ) / ‖z i‖ ^ (p + 1)) ≤
          (4 * R ^ (p + 1)) * ((1 : ℝ) / ‖z i‖ ^ (p + 1)) := by
      have hw2' :
          (‖w‖ ^ (p + 1)) * ((1 : ℝ) / ‖z i‖ ^ (p + 1)) ≤
            (R ^ (p + 1)) * ((1 : ℝ) / ‖z i‖ ^ (p + 1)) :=
        mul_le_mul_of_nonneg_right hw_pow hzterm_nonneg
      have :=
        mul_le_mul_of_nonneg_left hw2' (by norm_num : 0 ≤ (4 : ℝ))
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    have hrewrite :
        4 * ‖w / z i‖ ^ (p + 1) = (4 * ‖w‖ ^ (p + 1)) * ((1 : ℝ) / ‖z i‖ ^ (p + 1)) := by
      rw [norm_div, div_pow]
      field_simp
    calc
      ‖(weierstrassE p (w / z i) - 1 : ℂ)‖ ≤ 4 * ‖w / z i‖ ^ (p + 1) := hE
      _ = (4 * ‖w‖ ^ (p + 1)) * ((1 : ℝ) / ‖z i‖ ^ (p + 1)) := hrewrite
      _ ≤ (4 * R ^ (p + 1)) * ((1 : ℝ) / ‖z i‖ ^ (p + 1)) := hmul'
      _ = u i := by simp [u]
  have hcts :
      ∀ i, ContinuousOn (fun w : ℂ => (weierstrassE p (w / z i) - 1 : ℂ)) K := by
    intro i
    have hE : Continuous (fun w : ℂ => weierstrassE p (w / z i)) :=
      (weierstrass_E_continuous p).comp (by fun_prop)
    exact (hE.sub continuous_const).continuousOn
  have hprod :
      HasProdUniformlyOn
        (fun i (w : ℂ) => (1 : ℂ) + (weierstrassE p (w / z i) - 1))
        (fun w : ℂ => ∏' i : ι, ((1 : ℂ) + (weierstrassE p (w / z i) - 1))) K := by
    simpa using
      (Summable.hasProdUniformlyOn_one_add (α := ℂ) (R := ℂ) (K := K) hK hu hbound hcts)
  simpa using hprod

/-- **Rank-`p` analogue of `differentiableOn_tprod_weierstrass_E_one_of_summable_inv_norm_sq`.** -/
theorem differentiableOn_tprod_weierstrass_E_of_summable_inv_norm_pow
    {ι : Type*} {z : ι → ℂ} {p : ℕ}
    (hz0 : ∀ i, z i ≠ 0)
    (h : Summable (fun i : ι => (1 : ℝ) / ‖z i‖ ^ (p + 1))) :
    DifferentiableOn ℂ (fun w : ℂ => ∏' i : ι, weierstrassE p (w / z i)) (Set.univ : Set ℂ) := by
  classical
  have hprod :
      HasProdLocallyUniformlyOn (fun i (w : ℂ) => weierstrassE p (w / z i))
        (fun w : ℂ => ∏' i : ι, weierstrassE p (w / z i)) (Set.univ : Set ℂ) :=
    hasProdLocallyUniformlyOn_weierstrass_E_of_summable_inv_norm_pow (z := z) (p := p) hz0 h
  have hseq :
      TendstoLocallyUniformlyOn
        (fun s (w : ℂ) => ∏ i ∈ s, weierstrassE p (w / z i))
        (fun w : ℂ => ∏' i : ι, weierstrassE p (w / z i))
        (atTop : Filter (Finset ι)) (Set.univ : Set ℂ) := by
    simpa [HasProdLocallyUniformlyOn] using hprod
  have hdiff :
      ∀ᶠ s in (atTop : Filter (Finset ι)),
        DifferentiableOn ℂ
          (fun w : ℂ => ∏ i ∈ s, weierstrassE p (w / z i))
          (Set.univ : Set ℂ) := by
    refine Filter.Eventually.of_forall ?_
    intro s
    have hfun :
        DifferentiableOn ℂ
          (∏ i ∈ s, (fun w : ℂ => weierstrassE p (w / z i)))
          (Set.univ : Set ℂ) := by
      refine DifferentiableOn.finsetProd (𝕜 := ℂ) (𝔸' := ℂ) ?_
      intro i hi
      have hE : Differentiable ℂ (weierstrassE p) := weierstrass_E_differentiable p
      have hdiv : Differentiable ℂ (fun w : ℂ => w / z i) := by fun_prop
      exact (hE.comp hdiv).differentiableOn
    simpa [Finset.prod_fn] using hfun
  simpa using hseq.differentiableOn hdiff isOpen_univ

/-- **Entire rank-`p` canonical product.** The `Differentiable` (globally) form. -/
theorem differentiable_tprod_weierstrass_E_of_summable_inv_norm_pow
    {ι : Type*} {z : ι → ℂ} {p : ℕ}
    (hz0 : ∀ i, z i ≠ 0)
    (h : Summable (fun i : ι => (1 : ℝ) / ‖z i‖ ^ (p + 1))) :
    Differentiable ℂ (fun w : ℂ => ∏' i : ι, weierstrassE p (w / z i)) := by
  have hOn :
      DifferentiableOn ℂ (fun w : ℂ => ∏' i : ι, weierstrassE p (w / z i)) (Set.univ : Set ℂ) :=
    differentiableOn_tprod_weierstrass_E_of_summable_inv_norm_pow (z := z) (p := p) hz0 h
  intro w
  exact
    (hOn w (Set.mem_univ w)).differentiableAt
      (IsOpen.mem_nhds isOpen_univ (Set.mem_univ w))

end OrderOne
end Hadamard
