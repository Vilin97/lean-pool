/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Sobolev
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real

/-!
# Sobolev Products
-/

@[expose] public section

noncomputable section

namespace EulerSobolevProducts

open MeasureTheory FourierTransform EulerSobolev
open scoped SchwartzMap ENNReal ContDiff LineDeriv

theorem sobolevNorm_zero (d : ℕ) (f : 𝓢(Domain d, ℂ)) :
    sobolevNorm d 0 f = ‖f.toLp 2‖ := by
  have he : weightedFourier d 0 f = 𝓕 f := by
    ext ξ
    simp [weightedFourier_apply, besselWeight]
  simp [sobolevNorm, he]

theorem besselWeight_mono (d : ℕ) {s t : ℝ} (hst : s ≤ t) (ξ : Domain d) :
    besselWeight d s ξ ≤ besselWeight d t ξ := by
  apply Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖ξ‖])
  exact div_le_div_of_nonneg_right hst (by norm_num)

theorem sobolevNorm_mono (d : ℕ) {s t : ℝ} (hst : s ≤ t) (f : 𝓢(Domain d, ℂ)) :
    sobolevNorm d s f ≤ sobolevNorm d t f := by
  unfold sobolevNorm
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(weightedFourier d s f).coeFn_toLp 2,
    (weightedFourier d t f).coeFn_toLp 2] with ξ hs ht
  rw [hs, ht, weightedFourier_apply, weightedFourier_apply, norm_smul, norm_smul,
    Real.norm_of_nonneg (besselWeight_pos d s ξ).le,
    Real.norm_of_nonneg (besselWeight_pos d t ξ).le]
  exact mul_le_mul_of_nonneg_right (besselWeight_mono d hst ξ) (norm_nonneg _)

/-- Repeated differentiation in one fixed direction, as a Schwartz function. -/
noncomputable def directional (d n : ℕ) (v : Domain d) (f : 𝓢(Domain d, ℂ)) :
    𝓢(Domain d, ℂ) := ∂^{fun _ : Fin n => v} f

theorem directional_eq_iteratedDeriv (d n : ℕ) (v x : Domain d)
    (f : 𝓢(Domain d, ℂ)) :
    directional d n v f x = iteratedDeriv n (fun t : ℝ => f (x + t • v)) 0 := by
  rw [directional, SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv,
    iteratedDeriv_eq_iteratedFDeriv]
  let L : ℝ →L[ℝ] Domain d := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  have hC : ContDiff ℝ ∞ (fun z => f (x + z)) := f.smooth'.comp (contDiff_const.add contDiff_id)
  have he := L.iteratedFDeriv_comp_right hC (0 : ℝ) (by simp : (n : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  change iteratedFDeriv ℝ n f x (fun _ => v) = _
  change _ = iteratedFDeriv ℝ n ((fun z => f (x + z)) ∘ L) 0 (fun _ => 1)
  rw [he]
  simp [L, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_comp_add_left]

/-- Pointwise multiplication of two complex Schwartz functions. -/
noncomputable def product (d : ℕ) (f g : 𝓢(Domain d, ℂ)) : 𝓢(Domain d, ℂ) :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f g

@[simp] theorem product_apply (d : ℕ) (f g : 𝓢(Domain d, ℂ)) (x : Domain d) :
    product d f g x = f x * g x := rfl

theorem directional_product (d n : ℕ) (v : Domain d) (f g : 𝓢(Domain d, ℂ)) :
    directional d n v (product d f g) =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℂ) •
        product d (directional d j v f) (directional d (n-j) v g) := by
  ext x
  simp only [directional_eq_iteratedDeriv, product_apply, sum_apply,
    smul_apply, smul_eq_mul]
  have hf : ContDiff ℝ ∞ (fun t : ℝ => f (x + t • v)) :=
    f.smooth'.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hg : ContDiff ℝ ∞ (fun t : ℝ => g (x + t • v)) :=
    g.smooth'.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  simpa only [Pi.mul_apply, mul_assoc] using iteratedDeriv_fun_mul
    (hf.of_le (by simp)).contDiffAt (hg.of_le (by simp)).contDiffAt

theorem directional_L2_le (d n : ℕ) (v : Domain d) (f : 𝓢(Domain d, ℂ)) :
    ‖(directional d n v f).toLp 2‖ ≤
      (2 * Real.pi) ^ n * ‖v‖ ^ n * sobolevNorm d n f := by
  rw [← sobolevNorm_zero]
  simpa [directional] using sobolevNorm_iteratedLineDeriv_le d n 0 f (fun _ => v)

theorem besselWeight_six_le_pure_six (d : ℕ) (ξ : Domain d) :
    besselWeight d 6 ξ ≤ ((d : ℝ) + 1) ^ 2 * (1 + ∑ i, ‖ξ i‖ ^ 6) := by
  let a : Option (Fin d) → ℝ := fun i => match i with
    | none => 1
    | some i => ‖ξ i‖ ^ 2
  have ha : ∀ i ∈ (Finset.univ : Finset (Option (Fin d))), 0 ≤ a i := by
    intro i _
    cases i <;> simp only [a] <;> positivity
  have h := pow_sum_le_card_mul_sum_pow ha 2
  have he : besselWeight d 6 ξ = (1 + ∑ i, ‖ξ i‖ ^ 2) ^ 3 := by
    norm_num [besselWeight, EuclideanSpace.norm_sq_eq]
  rw [he]
  have hp (i : Fin d) : ‖ξ i‖ ^ 6 = (ξ i) ^ 6 := by
    exact (by decide : Even 6).pow_abs (ξ i)
  simp only [hp]
  simpa [a, Fintype.sum_option, ← pow_mul, Nat.mul_comm] using h

theorem fourier_directional_norm (d n : ℕ) (v : Domain d)
    (f : 𝓢(Domain d, ℂ)) (ξ : Domain d) :
    ‖𝓕 (directional d n v f) ξ‖ =
      (2 * Real.pi) ^ n * ‖inner ℝ ξ v‖ ^ n * ‖𝓕 f ξ‖ := by
  induction n with
  | zero => simp [directional]
  | succ n ih =>
    have ht : (fun ξ : Domain d => inner ℝ ξ v).HasTemperateGrowth :=
      ((innerSL ℝ).flip v).hasTemperateGrowth
    have hd : directional d (n+1) v f = ∂_{v} (directional d n v f) := rfl
    rw [hd, SchwartzMap.fourier_lineDerivOp_eq]
    simp only [smul_apply,
      SchwartzMap.smulLeftCLM_apply_apply ht, norm_smul]
    have hc : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
      simp [Real.pi_pos.le]
    rw [hc, ih, pow_succ, pow_succ]
    ring

/-- The pointwise norm of a Schwartz function, represented in the real `L²` space. -/
noncomputable def normLp (d : ℕ) (f : 𝓢(Domain d, ℂ)) :
    Lp ℝ 2 (volume : Measure (Domain d)) :=
  (f.memLp 2 volume).norm.toLp (fun x => ‖f x‖)

theorem norm_normLp (d : ℕ) (f : 𝓢(Domain d, ℂ)) :
    ‖normLp d f‖ = ‖f.toLp 2‖ := by
  simp only [normLp, Lp.norm_toLp, eLpNorm_norm, SchwartzMap.norm_toLp]

theorem coe_normLp (d : ℕ) (f : 𝓢(Domain d, ℂ)) :
    (normLp d f : Domain d → ℝ) =ᵐ[volume] (fun x => ‖f x‖) :=
  (f.memLp 2 volume).norm.coeFn_toLp

theorem normLp_le_sum {ι : Type*} [Fintype ι] (d : ℕ) (f : 𝓢(Domain d, ℂ))
    (g : ι → 𝓢(Domain d, ℂ)) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x, ‖f x‖ ≤ C * ∑ i, ‖g i x‖) :
    ‖f.toLp 2‖ ≤ C * ∑ i, ‖(g i).toLp 2‖ := by
  have hs : ∀ᵐ x ∂(volume : Measure (Domain d)), ∀ i, normLp d (g i) x = ‖g i x‖ :=
    Filter.eventually_all.2 (fun i => coe_normLp d (g i))
  have hb : ‖f.toLp 2‖ ≤ C * ‖∑ i, normLp d (g i)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [f.coeFn_toLp 2, Lp.coeFn_finsetSum Finset.univ (fun i => normLp d (g i)), hs]
      with x hf hsum hx
    rw [hf, hsum]
    simp only [Finset.sum_apply, hx, Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg (fun i _ => norm_nonneg _))]
    exact h x
  refine hb.trans ?_
  calc
    _ ≤ C * ∑ i, ‖normLp d (g i)‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hC
    _ = _ := by simp only [norm_normLp]

theorem sobolevNorm_six_le_pure_derivatives (d : ℕ) (f : 𝓢(Domain d, ℂ)) :
    sobolevNorm d 6 f ≤ ((d : ℝ) + 1) ^ 2 *
      (‖f.toLp 2‖ + (2 * Real.pi) ^ (-6 : ℤ) *
        ∑ i : Fin d, ‖(directional d 6 (EuclideanSpace.single i 1) f).toLp 2‖) := by
  let g : Option (Fin d) → 𝓢(Domain d, ℂ) := fun i => match i with
    | none => 𝓕 f
    | some i => ((2 * Real.pi) ^ (-6 : ℤ) : ℝ) •
        𝓕 (directional d 6 (EuclideanSpace.single i 1) f)
  have hpoint (ξ : Domain d) :
      ‖weightedFourier d 6 f ξ‖ ≤ ((d : ℝ) + 1) ^ 2 * ∑ i, ‖g i ξ‖ := by
    rw [weightedFourier_apply, norm_smul, Real.norm_of_nonneg (besselWeight_pos d 6 ξ).le]
    have hg : ∑ i, ‖g i ξ‖ = (1 + ∑ i, ‖ξ i‖ ^ 6) * ‖𝓕 f ξ‖ := by
      rw [Fintype.sum_option]
      simp only [g, smul_apply, norm_smul,
        Real.norm_of_nonneg (by positivity : 0 ≤ (2 * Real.pi) ^ (-6 : ℤ)),
        fourier_directional_norm, EuclideanSpace.inner_single_right,
        starRingEnd_apply, star_trivial]
      have hp : (2 * Real.pi) ^ (-6 : ℤ) * (2 * Real.pi) ^ (6 : ℕ) = 1 := by
        rw [show (-6 : ℤ) = -(6 : ℤ) from rfl, zpow_neg]
        exact inv_mul_cancel₀ (by positivity)
      simp_rw [← mul_assoc, hp, one_mul]
      rw [add_mul, one_mul, Finset.sum_mul]
    rw [hg]
    nlinarith [mul_le_mul_of_nonneg_right (besselWeight_six_le_pure_six d ξ) (norm_nonneg (𝓕 f ξ))]
  have h := normLp_le_sum d (weightedFourier d 6 f) g (((d : ℝ) + 1) ^ 2)
    (sq_nonneg _) hpoint
  have hnorm : ∑ i, ‖(g i).toLp 2‖ = ‖f.toLp 2‖ +
      (2 * Real.pi) ^ (-6 : ℤ) * ∑ i : Fin d,
        ‖(directional d 6 (EuclideanSpace.single i 1) f).toLp 2‖ := by
    rw [Fintype.sum_option]
    simp only [g]
    change ‖(𝓕 f).toLp 2‖ + ∑ i,
      ‖SchwartzMap.toLpCLM ℝ ℂ 2 volume (((2 * Real.pi) ^ (-6 : ℤ)) •
        𝓕 (directional d 6 (EuclideanSpace.single i 1) f))‖ = _
    simp only [map_smul, norm_smul,
      Real.norm_of_nonneg (by positivity : 0 ≤ (2 * Real.pi) ^ (-6 : ℤ)),
      SchwartzMap.toLpCLM_apply, SchwartzMap.norm_fourier_toL2_eq, Finset.mul_sum]
  rw [hnorm] at h
  exact h

theorem product_L2_le_of_sup (d : ℕ) (f g : 𝓢(Domain d, ℂ)) (A : ℝ)
    (hA : ∀ x, ‖f x‖ ≤ A) : ‖(product d f g).toLp 2‖ ≤ A * ‖g.toLp 2‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(product d f g).coeFn_toLp 2, g.coeFn_toLp 2] with x hp hg
  rw [hp, hg, product_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right (hA x) (norm_nonneg _)

theorem directional_sup_le_H6 (d j : ℕ) (hd : (d : ℝ) < 2 * 3) (hj : j ≤ 3)
    (v : Domain d) (hv : ‖v‖ ≤ 1) (f : 𝓢(Domain d, ℂ)) (x : Domain d) :
    ‖directional d j v f x‖ ≤
      embeddingConstant d 3 hd * (2 * Real.pi) ^ j * sobolevNorm d 6 f := by
  have hC : 0 ≤ embeddingConstant d 3 hd := norm_nonneg _
  have hS : 0 ≤ sobolevNorm d (3+j) f := norm_nonneg _
  have hb := sobolevNorm_iteratedLineDeriv_le d j 3 f (fun _ : Fin j => v)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hb
  have hvp : ‖v‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg _) hv
  have hs : sobolevNorm d (3 + j) f ≤ sobolevNorm d 6 f :=
    sobolevNorm_mono d (by exact_mod_cast (show 3 + j ≤ 6 by omega)) f
  calc
    _ ≤ embeddingConstant d 3 hd * sobolevNorm d 3 (directional d j v f) :=
      norm_apply_le_sobolevNorm d 3 hd _ x
    _ ≤ embeddingConstant d 3 hd *
        ((2 * Real.pi) ^ j * ‖v‖ ^ j * sobolevNorm d (3 + j) f) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ ≤ embeddingConstant d 3 hd * ((2 * Real.pi) ^ j * 1 * sobolevNorm d 6 f) := by
      gcongr
    _ = _ := by ring

theorem directional_L2_le_H6 (d j : ℕ) (hj : j ≤ 6) (v : Domain d) (hv : ‖v‖ ≤ 1)
    (f : 𝓢(Domain d, ℂ)) :
    ‖(directional d j v f).toLp 2‖ ≤ (2 * Real.pi) ^ j * sobolevNorm d 6 f := by
  have hvp : ‖v‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg _) hv
  have hS : 0 ≤ sobolevNorm d j f := norm_nonneg _
  have hmono : sobolevNorm d j f ≤ sobolevNorm d 6 f :=
    sobolevNorm_mono d (s := (j : ℝ)) (t := 6) (by exact_mod_cast hj) f
  calc
    _ ≤ (2 * Real.pi) ^ j * ‖v‖ ^ j * sobolevNorm d j f := directional_L2_le d j v f
    _ ≤ (2 * Real.pi) ^ j * 1 * sobolevNorm d 6 f := by
      gcongr
    _ = _ := by ring

attribute [local irreducible] sobolevNorm embeddingConstant

theorem product_directional_L2_le_left (d j k : ℕ) (hd : (d : ℝ) < 2 * 3)
    (hj : j ≤ 3) (hk : k ≤ 6) (v : Domain d) (hv : ‖v‖ ≤ 1)
    (f g : 𝓢(Domain d, ℂ)) :
    ‖(product d (directional d j v f) (directional d k v g)).toLp 2‖ ≤
      embeddingConstant d 3 hd * (2 * Real.pi) ^ (j+k) *
        sobolevNorm d 6 f * sobolevNorm d 6 g := by
  have hC : 0 ≤ embeddingConstant d 3 hd := by unfold embeddingConstant; exact norm_nonneg _
  have hS : 0 ≤ sobolevNorm d 6 f := by unfold sobolevNorm; exact norm_nonneg _
  have hA := product_L2_le_of_sup d (directional d j v f) (directional d k v g)
    (embeddingConstant d 3 hd * (2 * Real.pi) ^ j * sobolevNorm d 6 f)
    (directional_sup_le_H6 d j hd hj v hv f)
  have hB := mul_le_mul_of_nonneg_left (directional_L2_le_H6 d k hk v hv g)
    (mul_nonneg (mul_nonneg hC (by positivity : 0 ≤ (2 * Real.pi) ^ j)) hS)
  have harith (A B C p : ℝ) : (C * p ^ j * A) * (p ^ k * B) =
      C * p ^ (j+k) * A * B := by rw [pow_add]; ring
  exact hA.trans (hB.trans_eq (harith _ _ _ _))

theorem product_directional_L2_le (d j k : ℕ) (hd : (d : ℝ) < 2 * 3) (hjk : j + k ≤ 6)
    (v : Domain d) (hv : ‖v‖ ≤ 1) (f g : 𝓢(Domain d, ℂ)) :
    ‖(product d (directional d j v f) (directional d k v g)).toLp 2‖ ≤
      embeddingConstant d 3 hd * (2 * Real.pi) ^ (j+k) *
        sobolevNorm d 6 f * sobolevNorm d 6 g := by
  by_cases hj : j ≤ 3
  · exact product_directional_L2_le_left d j k hd hj (by omega) v hv f g
  · have he : product d (directional d j v f) (directional d k v g) =
        product d (directional d k v g) (directional d j v f) := by
      ext x
      simp [mul_comm]
    rw [he]
    have h := product_directional_L2_le_left d k j hd (by omega) (by omega) v hv g f
    rw [Nat.add_comm k j] at h
    convert h using 1; ring

theorem directional_product_L2_le (d n : ℕ) (hd : (d : ℝ) < 2 * 3) (hn : n ≤ 6)
    (v : Domain d) (hv : ‖v‖ ≤ 1) (f g : 𝓢(Domain d, ℂ)) :
    ‖(directional d n v (product d f g)).toLp 2‖ ≤
      2 ^ n * (embeddingConstant d 3 hd * (2 * Real.pi) ^ n *
        sobolevNorm d 6 f * sobolevNorm d 6 g) := by
  rw [directional_product]
  change ‖SchwartzMap.toLpCLM ℂ ℂ 2 volume
    (∑ j ∈ Finset.range (n+1), (n.choose j : ℂ) •
      product d (directional d j v f) (directional d (n-j) v g))‖ ≤ _
  rw [map_sum]
  calc
    _ ≤ ∑ j ∈ Finset.range (n+1),
        ‖SchwartzMap.toLpCLM ℂ ℂ 2 volume ((n.choose j : ℂ) •
          product d (directional d j v f) (directional d (n-j) v g))‖ := norm_sum_le _ _
    _ = ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) *
        ‖(product d (directional d j v f) (directional d (n-j) v g)).toLp 2‖ := by
      simp only [map_smul, norm_smul, Complex.norm_natCast, SchwartzMap.toLpCLM_apply]
    _ ≤ ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) *
        (embeddingConstant d 3 hd * (2 * Real.pi) ^ n *
          sobolevNorm d 6 f * sobolevNorm d 6 g) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn : j ≤ n := by simpa using (Finset.mem_range.1 hj)
      have h := product_directional_L2_le d j (n-j) hd (by omega) v hv f g
      rw [Nat.add_sub_of_le hjn] at h
      exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
    _ = _ := by
      rw [← Finset.sum_mul]
      congr 1
      exact_mod_cast Nat.sum_range_choose n

/-- A concrete algebra constant, obtained by Leibniz, Plancherel and the Sobolev embedding. -/
theorem sobolevNorm_six_product (d : ℕ) (hd : (d : ℝ) < 2 * 3) (f g : 𝓢(Domain d, ℂ)) :
    sobolevNorm d 6 (product d f g) ≤
      (((d : ℝ) + 1) ^ 2 * (1 + 64 * d) * embeddingConstant d 3 hd) *
        sobolevNorm d 6 f * sobolevNorm d 6 g := by
  have hzero : ‖(product d f g).toLp 2‖ ≤
      embeddingConstant d 3 hd * sobolevNorm d 6 f * sobolevNorm d 6 g := by
    simpa only [directional, LineDeriv.iteratedLineDerivOp_fin_zero, pow_zero, one_mul,
      mul_one] using directional_product_L2_le d 0 hd (by omega)
      0 (by simp) f g
  have hsix (i : Fin d) :
      ‖(directional d 6 (EuclideanSpace.single i 1) (product d f g)).toLp 2‖ ≤
        64 * (embeddingConstant d 3 hd * (2 * Real.pi) ^ 6 *
          sobolevNorm d 6 f * sobolevNorm d 6 g) := by
    have h := directional_product_L2_le d 6 hd (by omega)
      (EuclideanSpace.single i 1) (by simp) f g
    rw [show (2 : ℝ) ^ 6 = 64 by norm_num] at h
    exact h
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => hsix i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hp : (2 * Real.pi) ^ (-6 : ℤ) * (2 * Real.pi) ^ (6 : ℕ) = 1 := by
    rw [show (-6 : ℤ) = -(6 : ℤ) from rfl, zpow_neg]
    exact inv_mul_cancel₀ (by positivity)
  have harith (D C A B p r : ℝ) (hpr : r * p = 1) :
      (D + 1) ^ 2 * (C*A*B + r*(D*(64*(C*p*A*B)))) =
      ((D + 1) ^ 2 * (1 + 64*D) * C) * A * B := by
    linear_combination ((D + 1) ^ 2 * (64*D) * C * A * B) * hpr
  have hA := sobolevNorm_six_le_pure_derivatives d (product d f g)
  have hB := mul_le_mul_of_nonneg_left
    (add_le_add hzero (mul_le_mul_of_nonneg_left hsum
      (by positivity : 0 ≤ (2 * Real.pi) ^ (-6 : ℤ))))
    (sq_nonneg ((d : ℝ) + 1))
  exact hA.trans (hB.trans_eq (harith _ _ _ _ _ _ hp))

/-- The fixed four-dimensional `H⁶` algebra estimate used in the packet energy argument. -/
theorem four_dimensional_H6_algebra (f g : 𝓢(Domain 4, ℂ)) :
    sobolevNorm 4 6 (product 4 f g) ≤
      (6425 * embeddingConstant 4 3 (by norm_num)) *
        sobolevNorm 4 6 f * sobolevNorm 4 6 g := by
  convert sobolevNorm_six_product 4 (by norm_num) f g using 1; norm_num

end EulerSobolevProducts

end

-- Component: SobolevTransport.lean

section

/-!
The fixed-order transport commutator estimate.
-/

namespace EulerSobolevTransport

open MeasureTheory FourierTransform EulerSobolev EulerSobolevProducts
open scoped SchwartzMap ENNReal ContDiff LineDeriv


theorem directional_sup_le_H5 (d j : ℕ) (hd : (d : ℝ) < 2 * 3) (hj : j ≤ 2)
    (v : Domain d) (hv : ‖v‖ ≤ 1) (f : 𝓢(Domain d, ℂ)) (x : Domain d) :
    ‖directional d j v f x‖ ≤
      embeddingConstant d 3 hd * (2 * Real.pi) ^ j * sobolevNorm d 5 f := by
  have hC : 0 ≤ embeddingConstant d 3 hd := norm_nonneg _
  have hS : 0 ≤ sobolevNorm d (3+j) f := norm_nonneg _
  have hb := sobolevNorm_iteratedLineDeriv_le d j 3 f (fun _ : Fin j => v)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hb
  have hvp : ‖v‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg _) hv
  have hs : sobolevNorm d (3 + j) f ≤ sobolevNorm d 5 f :=
    sobolevNorm_mono d (by exact_mod_cast (show 3 + j ≤ 5 by omega)) f
  calc
    _ ≤ embeddingConstant d 3 hd * sobolevNorm d 3 (directional d j v f) :=
      norm_apply_le_sobolevNorm d 3 hd _ x
    _ ≤ embeddingConstant d 3 hd *
        ((2 * Real.pi) ^ j * ‖v‖ ^ j * sobolevNorm d (3 + j) f) :=
      mul_le_mul_of_nonneg_left hb hC
    _ ≤ embeddingConstant d 3 hd * ((2 * Real.pi) ^ j * 1 * sobolevNorm d 5 f) := by
      gcongr
    _ = _ := by ring

theorem directional_L2_le_H5 (d j : ℕ) (hj : j ≤ 5) (v : Domain d) (hv : ‖v‖ ≤ 1)
    (f : 𝓢(Domain d, ℂ)) :
    ‖(directional d j v f).toLp 2‖ ≤ (2 * Real.pi) ^ j * sobolevNorm d 5 f := by
  have hvp : ‖v‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg _) hv
  have hS : 0 ≤ sobolevNorm d j f := norm_nonneg _
  have hmono : sobolevNorm d j f ≤ sobolevNorm d 5 f :=
    sobolevNorm_mono d (s := (j : ℝ)) (t := 5) (by exact_mod_cast hj) f
  calc
    _ ≤ (2 * Real.pi) ^ j * ‖v‖ ^ j * sobolevNorm d j f := directional_L2_le d j v f
    _ ≤ (2 * Real.pi) ^ j * 1 * sobolevNorm d 5 f := by gcongr
    _ = _ := by ring

attribute [local irreducible] sobolevNorm embeddingConstant

theorem product_directional_L2_H5_left (d j k : ℕ) (hd : (d : ℝ) < 2 * 3)
    (hj : j ≤ 2) (hk : k ≤ 5) (v : Domain d) (hv : ‖v‖ ≤ 1)
    (f g : 𝓢(Domain d, ℂ)) :
    ‖(product d (directional d j v f) (directional d k v g)).toLp 2‖ ≤
      embeddingConstant d 3 hd * (2 * Real.pi) ^ (j+k) *
        sobolevNorm d 5 f * sobolevNorm d 5 g := by
  have hC : 0 ≤ embeddingConstant d 3 hd := by unfold embeddingConstant; exact norm_nonneg _
  have hS : 0 ≤ sobolevNorm d 5 f := by unfold sobolevNorm; exact norm_nonneg _
  have hA := product_L2_le_of_sup d (directional d j v f) (directional d k v g)
    (embeddingConstant d 3 hd * (2 * Real.pi) ^ j * sobolevNorm d 5 f)
    (directional_sup_le_H5 d j hd hj v hv f)
  have hB := mul_le_mul_of_nonneg_left (directional_L2_le_H5 d k hk v hv g)
    (mul_nonneg (mul_nonneg hC (by positivity : 0 ≤ (2 * Real.pi) ^ j)) hS)
  have harith (A B C p : ℝ) : (C * p ^ j * A) * (p ^ k * B) =
      C * p ^ (j+k) * A * B := by rw [pow_add]; ring
  exact hA.trans (hB.trans_eq (harith _ _ _ _))

theorem product_directional_L2_H5 (d j k : ℕ) (hd : (d : ℝ) < 2 * 3) (hjk : j + k ≤ 5)
    (v : Domain d) (hv : ‖v‖ ≤ 1) (f g : 𝓢(Domain d, ℂ)) :
    ‖(product d (directional d j v f) (directional d k v g)).toLp 2‖ ≤
      embeddingConstant d 3 hd * (2 * Real.pi) ^ (j+k) *
        sobolevNorm d 5 f * sobolevNorm d 5 g := by
  by_cases hj : j ≤ 2
  · exact product_directional_L2_H5_left d j k hd hj (by omega) v hv f g
  · have he : product d (directional d j v f) (directional d k v g) =
        product d (directional d k v g) (directional d j v f) := by
      ext x
      simp [mul_comm]
    rw [he]
    have h := product_directional_L2_H5_left d k j hd (by omega) (by omega) v hv g f
    rw [Nat.add_comm k j] at h
    convert h using 1; ring

/-- The actual commutator of an iterated directional derivative with multiplication. -/
noncomputable def commutator (d n : ℕ) (v : Domain d) (b h : 𝓢(Domain d, ℂ)) :
    𝓢(Domain d, ℂ) :=
  directional d n v (product d b h) - product d b (directional d n v h)

theorem directional_succ_right (d n : ℕ) (v : Domain d) (f : 𝓢(Domain d, ℂ)) :
    directional d (n+1) v f = directional d n v (directional d 1 v f) := by
  simp [directional, LineDeriv.iteratedLineDerivOp_succ_right, Fin.init_def]

theorem commutator_expansion (d n : ℕ) (v : Domain d) (b h : 𝓢(Domain d, ℂ)) :
    commutator d n v b h = ∑ j ∈ Finset.range n, (n.choose (j+1) : ℂ) •
      product d (directional d j v (directional d 1 v b)) (directional d (n-(j+1)) v h) := by
  unfold commutator
  rw [directional_product, Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, directional,
    LineDeriv.iteratedLineDerivOp_fin_zero, Nat.sub_zero, one_smul, add_sub_cancel_right]
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  exact directional_succ_right d j v b

theorem sum_choose_successors_le (n : ℕ) :
    (∑ j ∈ Finset.range n, (n.choose (j+1) : ℝ)) ≤ 2 ^ n := by
  have h : (∑ j ∈ Finset.range (n+1), (n.choose j : ℝ)) = 2 ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  rw [Finset.sum_range_succ'] at h
  simp only [Nat.choose_zero_right, Nat.cast_one] at h
  linarith

/--
No derivative is lost in the fixed-order transport commutator: after removing
the top term, one derivative falls on `b`, leaving a total of at most five.
-/
theorem transport_commutator_L2 (d n : ℕ) (hd : (d : ℝ) < 2 * 3) (hn : n ≤ 6)
    (v : Domain d) (hv : ‖v‖ ≤ 1) (b h : 𝓢(Domain d, ℂ)) :
    ‖(commutator d n v b h).toLp 2‖ ≤
      2 ^ n * (embeddingConstant d 3 hd * (2 * Real.pi) ^ (n-1) *
        sobolevNorm d 5 (directional d 1 v b) * sobolevNorm d 5 h) := by
  rw [commutator_expansion]
  change ‖SchwartzMap.toLpCLM ℂ ℂ 2 volume
    (∑ j ∈ Finset.range n, (n.choose (j+1) : ℂ) •
      product d (directional d j v (directional d 1 v b)) (directional d (n-(j+1)) v h))‖ ≤ _
  rw [map_sum]
  calc
    _ ≤ ∑ j ∈ Finset.range n,
        ‖SchwartzMap.toLpCLM ℂ ℂ 2 volume ((n.choose (j+1) : ℂ) •
          product d (directional d j v (directional d 1 v b))
            (directional d (n-(j+1)) v h))‖ := norm_sum_le _ _
    _ = ∑ j ∈ Finset.range n, (n.choose (j+1) : ℝ) *
        ‖(product d (directional d j v (directional d 1 v b))
          (directional d (n-(j+1)) v h)).toLp 2‖ := by
      simp only [map_smul, norm_smul, Complex.norm_natCast, SchwartzMap.toLpCLM_apply]
    _ ≤ ∑ j ∈ Finset.range n, (n.choose (j+1) : ℝ) *
        (embeddingConstant d 3 hd * (2 * Real.pi) ^ (n-1) *
          sobolevNorm d 5 (directional d 1 v b) * sobolevNorm d 5 h) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn : j < n := Finset.mem_range.1 hj
      have he : j + (n-(j+1)) = n-1 := by omega
      have hbound := product_directional_L2_H5 d j (n-(j+1)) hd (by omega) v hv
        (directional d 1 v b) h
      rw [he] at hbound
      exact mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _)
    _ ≤ _ := by
      rw [← Finset.sum_mul]
      apply mul_le_mul_of_nonneg_right (sum_choose_successors_le n)
      unfold embeddingConstant sobolevNorm
      positivity

end EulerSobolevTransport
