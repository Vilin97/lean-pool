/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.LimitFieldConvergence
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Construction.StreamAdmissible
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! Spatial differentiability and velocity estimates for the limit stream. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Infra.Construction

theorem LimitFieldRegularity.limitStreamSeq_slice_contDiff {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsStreamSeq I Φ)
    (m : ℕ) (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (Φ m t) := by
  have hm := (streamSeq_isAdmissible hseq m).1
  exact hm.comp (contDiff_const.prodMk contDiff_id)

theorem LimitFieldRegularity.vec_basis_decomp (v : Vec 2) :
    v = v 0 • basisVec 0 + v 1 • basisVec 1 := by
  ext i
  fin_cases i <;> simp [basisVec]

theorem LimitFieldRegularity.clm_norm_le_two_basis {L : Vec 2 →L[ℝ] ℝ} {B : ℝ}
    (hB : 0 ≤ B)
    (h0 : ‖L (basisVec 0)‖ ≤ B) (h1 : ‖L (basisVec 1)‖ ≤ B) :
    ‖L‖ ≤ 2 * B := by
  apply L.opNorm_le_bound (by positivity)
  intro v
  calc
    ‖L v‖ = ‖L (v 0 • basisVec 0 + v 1 • basisVec 1)‖ := by
      exact congrArg (fun w : Vec 2 => ‖L w‖) (LimitFieldRegularity.vec_basis_decomp v)
    _ =
        ‖L (v 0 • basisVec 0) + L (v 1 • basisVec 1)‖ := by rw [map_add]
    _ ≤ ‖L (v 0 • basisVec 0)‖ + ‖L (v 1 • basisVec 1)‖ := norm_add_le _ _
    _ = |v 0| * ‖L (basisVec 0)‖ + |v 1| * ‖L (basisVec 1)‖ := by
      rw [map_smul, map_smul]
      simp [Real.norm_eq_abs, basisVec]
    _ ≤ |v 0| * B + |v 1| * B := by gcongr
    _ ≤ (‖v‖ + ‖v‖) * B := by
      have hvsum : |v 0| + |v 1| ≤ 2 * ‖v‖ := by
        have hv0 : |v 0| ≤ ‖v‖ := by
          simpa [Real.norm_eq_abs] using norm_le_pi_norm v (0 : Fin 2)
        have hv1 : |v 1| ≤ ‖v‖ := by
          simpa [Real.norm_eq_abs] using norm_le_pi_norm v (1 : Fin 2)
        linarith
      calc
        |v 0| * B + |v 1| * B = (|v 0| + |v 1|) * B := by ring
        _ ≤ (2 * ‖v‖) * B := mul_le_mul_of_nonneg_right hvsum hB
        _ = (‖v‖ + ‖v‖) * B := by ring
    _ = (2 * B) * ‖v‖ := by ring

theorem LimitFieldRegularity.streamFDeriv_increment_norm_le {β : ℝ} {C : ℝ}
    {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ)
    {m : ℕ} (hm : 1 ≤ m) (t : ℝ) (x : Vec 2) :
    ‖fderiv ℝ (Φ m t) x - fderiv ℝ (Φ (m - 1) t) x‖ ≤
      640 * epsilon β I.Λ m ^ (β - 1) := by
  have hslice (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (Φ j t) := by
    have hj := (streamSeq_isAdmissible hseq j).1
    have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) :=
      contDiff_const.prodMk contDiff_id
    change ContDiff ℝ (⊤ : ℕ∞) (fun x => Function.uncurry (Φ j) (t, x))
    exact hj.comp hmap
  have hprev := hslice (m - 1)
  have hcur := hslice m
  have h0 := streamIncrement_deriv_coordinate_le hseq hreg hm t x (0 : Fin 2)
  have h1 := streamIncrement_deriv_coordinate_le hseq hreg hm t x (1 : Fin 2)
  have hderiv : fderiv ℝ (Φ m t - Φ (m - 1) t) x =
      fderiv ℝ (Φ m t) x - fderiv ℝ (Φ (m - 1) t) x :=
    fderiv_sub (hcur.differentiable (by simp) x) (hprev.differentiable (by simp) x)
  rw [hderiv] at h0 h1
  have hc0 : ‖(fderiv ℝ (Φ m t) x - fderiv ℝ (Φ (m - 1) t) x) (basisVec 0)‖ ≤
      320 * epsilon β I.Λ m ^ (β - 1) := h0
  have hc1 : ‖(fderiv ℝ (Φ m t) x - fderiv ℝ (Φ (m - 1) t) x) (basisVec 1)‖ ≤
      320 * epsilon β I.Λ m ^ (β - 1) := h1
  have he := AVenhance.Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
    I.two_pow_seven_le (m := m)
  have hB : 0 ≤ 320 * epsilon β I.Λ m ^ (β - 1) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg he.le _)
  have := LimitFieldRegularity.clm_norm_le_two_basis hB hc0 hc1
  calc
    ‖fderiv ℝ (Φ m t) x - fderiv ℝ (Φ (m - 1) t) x‖ ≤
        2 * (320 * epsilon β I.Λ m ^ (β - 1)) := this
    _ = 640 * epsilon β I.Λ m ^ (β - 1) := by ring

theorem LimitFieldRegularity.streamFDeriv_telescope {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (m k : ℕ) (t : ℝ) (x : Vec 2) :
    fderiv ℝ (Φ (m + k) t) x - fderiv ℝ (Φ m t) x =
      ∑ j ∈ Finset.range k,
        (fderiv ℝ (Φ (m + j + 1) t) x - fderiv ℝ (Φ (m + j) t) x) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      simp only [Nat.add_succ]
      rw [← ih]
      abel

/-- Geometric-tail constant for the stream derivative convergence estimate. -/
def LimitFieldRegularity.streamDerivativeTailConstant {β : ℝ} (I : Ingredients β) : ℝ :=
  640 / (1 - (I.Λ : ℝ) ^ (-(β - 1)))

theorem LimitFieldRegularity.streamDerivativeTailConstant_pos {β : ℝ} (I : Ingredients β) :
    0 < LimitFieldRegularity.streamDerivativeTailConstant I := by
  have hs : 0 < β - 1 := by linarith [I.one_lt_beta]
  have hq := inverse_lambda_rpow_lt_one I hs
  have hden : 0 < 1 - (I.Λ : ℝ) ^ (-(β - 1)) := by linarith
  exact div_pos (by norm_num) hden

theorem LimitFieldRegularity.streamFDeriv_tail_le {β : ℝ} {C : ℝ}
    {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ)
    (m k : ℕ) (t : ℝ) (x : Vec 2) :
    ‖fderiv ℝ (Φ (m + k) t) x - fderiv ℝ (Φ m t) x‖ ≤
      LimitFieldRegularity.streamDerivativeTailConstant I * epsilon β I.Λ (m + 1) ^ (β - 1) := by
  rw [LimitFieldRegularity.streamFDeriv_telescope m k t x]
  calc
    ‖∑ j ∈ Finset.range k,
        (fderiv ℝ (Φ (m + j + 1) t) x - fderiv ℝ (Φ (m + j) t) x)‖ ≤
        ∑ j ∈ Finset.range k,
          ‖fderiv ℝ (Φ (m + j + 1) t) x - fderiv ℝ (Φ (m + j) t) x‖ :=
      norm_sum_le _ _
    _ ≤ 640 * ∑ j ∈ Finset.range k,
          epsilon β I.Λ (m + j + 1) ^ (β - 1) := by
      calc
        _ ≤ ∑ j ∈ Finset.range k,
              (640 * epsilon β I.Λ (m + j + 1) ^ (β - 1)) :=
          Finset.sum_le_sum fun j hj => by
            have hjm : 1 ≤ m + j + 1 := by omega
            have h := LimitFieldRegularity.streamFDeriv_increment_norm_le hseq hreg hjm t x
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
        _ = 640 * ∑ j ∈ Finset.range k,
              epsilon β I.Λ (m + j + 1) ^ (β - 1) := by rw [Finset.mul_sum]
    _ ≤ LimitFieldRegularity.streamDerivativeTailConstant I * epsilon β I.Λ (m + 1) ^ (β - 1) := by
      have hs : 0 < β - 1 := by linarith [I.one_lt_beta]
      have hsum := epsilon_rpow_sum_bound I hs (m + 1) k
      have hscale : (∑ j ∈ Finset.range k,
          epsilon β I.Λ ((m + 1) + j) ^ (β - 1)) ≤
            epsilon β I.Λ (m + 1) ^ (β - 1) /
              (1 - (I.Λ : ℝ) ^ (-(β - 1))) := by
        simpa [Nat.add_assoc] using hsum
      have h640 := mul_le_mul_of_nonneg_left hscale (by norm_num : (0 : ℝ) ≤ 640)
      simpa [LimitFieldRegularity.streamDerivativeTailConstant, div_eq_mul_inv, mul_assoc,
        mul_comm, mul_left_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h640

theorem LimitFieldRegularity.streamFDeriv_cauchySeq {β : ℝ} {C : ℝ}
    {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ)
    (t : ℝ) (x : Vec 2) : CauchySeq (fun m => fderiv ℝ (Φ m t) x) := by
  rw [Metric.cauchySeq_iff']
  intro r hr
  have hs : 0 < β - 1 := by linarith [I.one_lt_beta]
  have hD : 0 < LimitFieldRegularity.streamDerivativeTailConstant I :=
      LimitFieldRegularity.streamDerivativeTailConstant_pos I
  have htend : Tendsto (fun n => LimitFieldRegularity.streamDerivativeTailConstant I *
      epsilon β I.Λ (n + 1) ^ (β - 1)) atTop (𝓝 0) := by
    have he := epsilon_rpow_tendsto_zero I hs
    have heShift := he.comp (tendsto_add_atTop_nat 1)
    simpa [mul_comm] using heShift.const_mul (LimitFieldRegularity.streamDerivativeTailConstant I)
  obtain ⟨N, hN⟩ := (eventually_atTop.1 (htend.eventually (Iio_mem_nhds hr)))
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  calc
    dist (fderiv ℝ (Φ (N + k) t) x) (fderiv ℝ (Φ N t) x) =
        ‖fderiv ℝ (Φ (N + k) t) x - fderiv ℝ (Φ N t) x‖ := by rw [dist_eq_norm]
    _ ≤ LimitFieldRegularity.streamDerivativeTailConstant I * epsilon β I.Λ (N + 1) ^ (β - 1) :=
      LimitFieldRegularity.streamFDeriv_tail_le hseq hreg N k t x
    _ < r := hN N (le_rfl : N ≤ N)

/-- Limit of the spatial Fréchet derivatives of the stream sequence. -/
def LimitFieldRegularity.streamFDerivLimit {β : ℝ} {C : ℝ}
    {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ)
    (t : ℝ) (x : Vec 2) : Vec 2 →L[ℝ] ℝ :=
  Classical.choose (cauchySeq_tendsto_of_complete (LimitFieldRegularity.streamFDeriv_cauchySeq
      hseq hreg t x))

theorem LimitFieldRegularity.streamFDerivLimit_tendsto {β : ℝ} {C : ℝ}
    {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ)
    (t : ℝ) (x : Vec 2) :
    Tendsto (fun m => fderiv ℝ (Φ m t) x) atTop
      (𝓝 (LimitFieldRegularity.streamFDerivLimit hseq hreg t x)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete
    (LimitFieldRegularity.streamFDeriv_cauchySeq hseq hreg t x))

theorem LimitFieldRegularity.streamFDerivLimit_uniformlyOn {β : ℝ} {C : ℝ}
    {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ) (t : ℝ) :
    TendstoUniformlyOn (fun m x => fderiv ℝ (Φ m t) x)
      (LimitFieldRegularity.streamFDerivLimit hseq hreg t) atTop Set.univ := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro r hr
  have hs : 0 < β - 1 := by linarith [I.one_lt_beta]
  have hD : 0 < LimitFieldRegularity.streamDerivativeTailConstant I :=
      LimitFieldRegularity.streamDerivativeTailConstant_pos I
  have htend : Tendsto (fun n => LimitFieldRegularity.streamDerivativeTailConstant I *
      epsilon β I.Λ (n + 1) ^ (β - 1)) atTop (𝓝 0) := by
    have he := epsilon_rpow_tendsto_zero I hs
    have heShift := he.comp (tendsto_add_atTop_nat 1)
    simpa [mul_comm] using heShift.const_mul (LimitFieldRegularity.streamDerivativeTailConstant I)
  obtain ⟨N, hN⟩ := (eventually_atTop.1
    (htend.eventually (Iio_mem_nhds (half_pos hr))))
  filter_upwards [eventually_atTop.2 ⟨N, fun n hn => hn⟩] with n hn
  intro x hx
  let B := LimitFieldRegularity.streamDerivativeTailConstant I * epsilon β I.Λ (N + 1) ^ (β - 1)
  have hbound : ∀ᶠ j : ℕ in atTop,
      dist (fderiv ℝ (Φ j t) x) (fderiv ℝ (Φ N t) x) ≤ B := by
    refine eventually_atTop.2 ⟨N, ?_⟩
    intro j hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [dist_eq_norm]
    exact LimitFieldRegularity.streamFDeriv_tail_le hseq hreg N k t x
  have hlimit : dist (LimitFieldRegularity.streamFDerivLimit hseq hreg t x)
      (fderiv ℝ (Φ N t) x) ≤ B := by
    have ht := (continuous_dist.tendsto
      (LimitFieldRegularity.streamFDerivLimit hseq hreg t x, fderiv ℝ (Φ N t) x)).comp
        ((LimitFieldRegularity.streamFDerivLimit_tendsto hseq hreg t x).prodMk_nhds
            tendsto_const_nhds)
    exact le_of_tendsto ht hbound
  have hnBound : dist (fderiv ℝ (Φ n t) x) (fderiv ℝ (Φ N t) x) ≤ B := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [dist_eq_norm]
    exact LimitFieldRegularity.streamFDeriv_tail_le hseq hreg N k t x
  calc
    dist (LimitFieldRegularity.streamFDerivLimit hseq hreg t x) (fderiv ℝ (Φ n t) x) ≤
        dist (LimitFieldRegularity.streamFDerivLimit hseq hreg t x) (fderiv ℝ (Φ N t) x) +
          dist (fderiv ℝ (Φ N t) x) (fderiv ℝ (Φ n t) x) := dist_triangle _ _ _
    _ ≤ B + B := add_le_add hlimit (by simpa [dist_comm] using hnBound)
    _ < r := by dsimp [B]; linarith [hN N le_rfl]

theorem LimitFieldRegularity.streamFDerivLimit_uniformlyOn_spaceTime {β : ℝ} {C : ℝ}
    {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ) :
    TendstoUniformlyOn (fun m (p : ℝ × Vec 2) => fderiv ℝ (Φ m p.1) p.2)
      (fun (p : ℝ × Vec 2) => LimitFieldRegularity.streamFDerivLimit hseq hreg p.1 p.2) atTop
          Set.univ := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro r hr
  have hs : 0 < β - 1 := by linarith [I.one_lt_beta]
  have hD : 0 < LimitFieldRegularity.streamDerivativeTailConstant I :=
      LimitFieldRegularity.streamDerivativeTailConstant_pos I
  have htend : Tendsto (fun n => LimitFieldRegularity.streamDerivativeTailConstant I *
      epsilon β I.Λ (n + 1) ^ (β - 1)) atTop (𝓝 0) := by
    have he := epsilon_rpow_tendsto_zero I hs
    have heShift := he.comp (tendsto_add_atTop_nat 1)
    simpa [mul_comm] using heShift.const_mul (LimitFieldRegularity.streamDerivativeTailConstant I)
  obtain ⟨N, hN⟩ := (eventually_atTop.1
    (htend.eventually (Iio_mem_nhds (half_pos hr))))
  filter_upwards [eventually_atTop.2 ⟨N, fun n hn => hn⟩] with n hn
  intro (p : ℝ × Vec 2) hp
  let B := LimitFieldRegularity.streamDerivativeTailConstant I * epsilon β I.Λ (N + 1) ^ (β - 1)
  have hbound : ∀ᶠ j : ℕ in atTop,
      dist (fderiv ℝ (Φ j p.1) p.2) (fderiv ℝ (Φ N p.1) p.2) ≤ B := by
    refine eventually_atTop.2 ⟨N, ?_⟩
    intro j hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [dist_eq_norm]
    have htail := LimitFieldRegularity.streamFDeriv_tail_le (β := β) (C := C) (I := I) (Φ := Φ)
      hseq hreg N k p.1 p.2
    simpa [B] using htail
  have hlimit : dist (LimitFieldRegularity.streamFDerivLimit hseq hreg p.1 p.2)
      (fderiv ℝ (Φ N p.1) p.2) ≤ B := by
    have ht := (continuous_dist.tendsto
      (LimitFieldRegularity.streamFDerivLimit hseq hreg p.1 p.2, fderiv ℝ (Φ N p.1) p.2)).comp
        ((LimitFieldRegularity.streamFDerivLimit_tendsto hseq hreg p.1 p.2).prodMk_nhds
            tendsto_const_nhds)
    exact le_of_tendsto ht hbound
  have hnBound : dist (fderiv ℝ (Φ n p.1) p.2) (fderiv ℝ (Φ N p.1) p.2) ≤ B := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [dist_eq_norm]
    have htail := LimitFieldRegularity.streamFDeriv_tail_le (β := β) (C := C) (I := I) (Φ := Φ)
      hseq hreg N k p.1 p.2
    simpa [B] using htail
  calc
    dist (LimitFieldRegularity.streamFDerivLimit hseq hreg p.1 p.2) (fderiv ℝ (Φ n p.1) p.2) ≤
        dist (LimitFieldRegularity.streamFDerivLimit hseq hreg p.1 p.2) (fderiv ℝ (Φ N p.1) p.2) +
          dist (fderiv ℝ (Φ N p.1) p.2) (fderiv ℝ (Φ n p.1) p.2) := dist_triangle _ _ _
    _ ≤ B + B := add_le_add hlimit (by simpa [dist_comm] using hnBound)
    _ < r := by dsimp [B]; linarith [hN N le_rfl]

/-- Rotate a scalar spatial differential by a quarter turn to obtain a velocity. -/
def LimitFieldRegularity.rotateFDeriv (L : Vec 2 →L[ℝ] ℝ) : Vec 2 :=
  ![-L (basisVec 1), L (basisVec 0)]

theorem LimitFieldRegularity.norm_rotateFDeriv_sub_le (L K : Vec 2 →L[ℝ] ℝ) :
    ‖LimitFieldRegularity.rotateFDeriv L - LimitFieldRegularity.rotateFDeriv K‖ ≤ ‖L - K‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  fin_cases i
  · have h := (L - K).le_opNorm (basisVec 1)
    have he : ‖basisVec (1 : Fin 2)‖ = 1 := by simp [basisVec, Pi.norm_single]
    calc
      ‖(LimitFieldRegularity.rotateFDeriv L - LimitFieldRegularity.rotateFDeriv K) 0‖ = ‖(L - K)
          (basisVec 1)‖ := by
        change ‖-L (basisVec 1) - -(K (basisVec 1))‖ = ‖(L - K) (basisVec 1)‖
        calc
          _ = ‖-(L (basisVec 1) - K (basisVec 1))‖ := by congr 1; ring
          _ = ‖L (basisVec 1) - K (basisVec 1)‖ := norm_neg _
          _ = ‖(L - K) (basisVec 1)‖ := by simp
      _ ≤ ‖L - K‖ * ‖basisVec 1‖ := h
      _ = ‖L - K‖ := by rw [he, mul_one]
  · have h := (L - K).le_opNorm (basisVec 0)
    have he : ‖basisVec (0 : Fin 2)‖ = 1 := by simp [basisVec, Pi.norm_single]
    calc
      ‖(LimitFieldRegularity.rotateFDeriv L - LimitFieldRegularity.rotateFDeriv K) 1‖ = ‖(L - K)
          (basisVec 0)‖ := by
        change ‖L (basisVec 0) - K (basisVec 0)‖ = ‖(L - K) (basisVec 0)‖
        simp
      _ ≤ ‖L - K‖ * ‖basisVec 0‖ := h
      _ = ‖L - K‖ := by rw [he, mul_one]

theorem LimitFieldRegularity.streamVel_eq_rotateFDeriv (ψ : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) :
    streamVel ψ t x = LimitFieldRegularity.rotateFDeriv (fderiv ℝ (ψ t) x) := by
  ext i
  fin_cases i <;>
    simp [streamVel, LimitFieldRegularity.rotateFDeriv, spaceGrad, sigmaMat, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]

theorem LimitFieldRegularity.fderiv_gradient_component_eq_hessian
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i j : Fin 2) (x : Vec 2) :
    fderiv ℝ (fun y => fderiv ℝ f y (basisVec i)) x (basisVec j) =
      iteratedFDeriv ℝ 2 f x (fun k => basisVec (if k = 0 then j else i)) := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) (by simp)).differentiable (by simp)) x
  have hc : DifferentiableAt ℝ (fun _ : Vec 2 => basisVec i) x :=
    differentiableAt_const _
  have h := fderiv_clm_apply hdf hc
  have heval := congrArg (fun L : Vec 2 →L[ℝ] ℝ => L (basisVec j)) h
  simpa [iteratedFDeriv_two_apply] using heval

theorem LimitFieldRegularity.streamVel_increment_spatial_lipschitz
    {β : ℝ} {C : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ)
    {m : ℕ} (hm : 1 ≤ m) (t : ℝ) (x y : Vec 2) :
    ‖(streamVel (Φ m) t x - streamVel (Φ (m - 1)) t x) -
        (streamVel (Φ m) t y - streamVel (Φ (m - 1)) t y)‖ ≤
      2 ^ 18 * epsilon β I.Λ m ^ (β - 2) * ‖x - y‖ := by
  let f : Vec 2 → ℝ := Φ m t - Φ (m - 1) t
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    (LimitFieldRegularity.limitStreamSeq_slice_contDiff hseq m t).sub
      (LimitFieldRegularity.limitStreamSeq_slice_contDiff hseq (m - 1) t)
  have hcomp (i : Fin 2) : Differentiable ℝ
      (fun z : Vec 2 => fderiv ℝ f z (basisVec i)) := by
    have hc : ContDiff ℝ 1 (fun _ : Vec 2 => basisVec i) := contDiff_const
    have h := (hf.fderiv_right (m := 1) (by simp)).clm_apply hc
    exact h.differentiable (by simp)
  have hcoord (i : Fin 2) (z : Vec 2) :
      ‖fderiv ℝ (fun w : Vec 2 => fderiv ℝ f w (basisVec i)) z‖ ≤
        2 * (2 ^ 16 * epsilon β I.Λ m ^ (β - 2)) := by
    have h0 := LimitFieldRegularity.fderiv_gradient_component_eq_hessian hf i 0 z
    have h1 := LimitFieldRegularity.fderiv_gradient_component_eq_hessian hf i 1 z
    have hH0 := streamIncrement_secondCoordinate_le hseq hreg hm t z
      (fun k => if k = 0 then (0 : Fin 2) else i)
    have hH1 := streamIncrement_secondCoordinate_le hseq hreg hm t z
      (fun k => if k = 0 then (1 : Fin 2) else i)
    have hb0 : ‖fderiv ℝ (fun w : Vec 2 => fderiv ℝ f w (basisVec i)) z
        (basisVec 0)‖ ≤ 2 ^ 16 * epsilon β I.Λ m ^ (β - 2) := by
      rw [h0]
      simpa [f, iteratedFDeriv_two_apply] using hH0
    have hb1 : ‖fderiv ℝ (fun w : Vec 2 => fderiv ℝ f w (basisVec i)) z
        (basisVec 1)‖ ≤ 2 ^ 16 * epsilon β I.Λ m ^ (β - 2) := by
      rw [h1]
      simpa [f, iteratedFDeriv_two_apply] using hH1
    have he := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le (m := m)
    have hnonneg : 0 ≤ 2 ^ 16 * epsilon β I.Λ m ^ (β - 2) :=
      mul_nonneg (by positivity) (Real.rpow_nonneg he.le _)
    exact LimitFieldRegularity.clm_norm_le_two_basis hnonneg hb0 hb1
  have heps := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
    I.two_pow_seven_le (m := m)
  have hcoef : 0 ≤ 2 * (2 ^ 16 * epsilon β I.Λ m ^ (β - 2)) :=
    mul_nonneg (by norm_num) (mul_nonneg (by positivity)
      (Real.rpow_nonneg heps.le _))
  have hL (i : Fin 2) : LipschitzWith
      (2 * (2 ^ 16 * epsilon β I.Λ m ^ (β - 2))).toNNReal
      (fun z : Vec 2 => fderiv ℝ f z (basisVec i)) := by
    apply lipschitzWith_of_nnnorm_fderiv_le (hcomp i)
    intro z
    apply NNReal.coe_le_coe.mp
    rw [coe_nnnorm, Real.coe_toNNReal _ hcoef]
    exact hcoord i z
  have hvel (z : Vec 2) :
      streamVel (Φ m) t z - streamVel (Φ (m - 1)) t z =
        LimitFieldRegularity.rotateFDeriv (fderiv ℝ f z) := by
    have hsub : fderiv ℝ f z =
        fderiv ℝ (Φ m t) z - fderiv ℝ (Φ (m - 1) t) z := by
      dsimp [f]
      exact fderiv_sub
        ((LimitFieldRegularity.limitStreamSeq_slice_contDiff hseq m t).differentiable (by simp) z)
        ((LimitFieldRegularity.limitStreamSeq_slice_contDiff hseq (m - 1) t).differentiable (by
            simp) z)
    rw [LimitFieldRegularity.streamVel_eq_rotateFDeriv,
        LimitFieldRegularity.streamVel_eq_rotateFDeriv, hsub]
    ext k
    fin_cases k
    · simp [LimitFieldRegularity.rotateFDeriv]
      ring
    · simp [LimitFieldRegularity.rotateFDeriv]
  rw [hvel x, hvel y]
  apply (pi_norm_le_iff_of_nonneg (show 0 ≤
      2 ^ 18 * epsilon β I.Λ m ^ (β - 2) * ‖x - y‖ by positivity)).2
  intro i
  fin_cases i
  · have h := (hL 1).dist_le_mul x y
    have h' : |fderiv ℝ f x (basisVec 1) - fderiv ℝ f y (basisVec 1)| ≤
        (2 * (2 ^ 16 * epsilon β I.Λ m ^ (β - 2))) * ‖x - y‖ := by
      rw [dist_eq_norm, Real.norm_eq_abs] at h
      rw [Real.coe_toNNReal _ hcoef] at h
      exact h
    have he := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le (m := m)
    have hc : 2 * (2 ^ 16 * epsilon β I.Λ m ^ (β - 2)) ≤
        2 ^ 18 * epsilon β I.Λ m ^ (β - 2) := by
      have hp : 0 ≤ epsilon β I.Λ m ^ (β - 2) := Real.rpow_nonneg he.le _
      norm_num only [pow_succ, Nat.reducePow]
      nlinarith [mul_nonneg hp (by norm_num : (0 : ℝ) ≤ 1)]
    have h'' := le_trans h' (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
    change ‖-(fderiv ℝ f x (basisVec 1)) -
      (-(fderiv ℝ f y (basisVec 1)))‖ ≤ _
    have hnorm : ‖-(fderiv ℝ f x (basisVec 1)) -
        (-(fderiv ℝ f y (basisVec 1)))‖ =
        |fderiv ℝ f x (basisVec 1) - fderiv ℝ f y (basisVec 1)| := by
      rw [show -(fderiv ℝ f x (basisVec 1)) -
          (-(fderiv ℝ f y (basisVec 1))) =
          -(fderiv ℝ f x (basisVec 1) - fderiv ℝ f y (basisVec 1)) by ring,
        norm_neg, Real.norm_eq_abs]
    rw [hnorm]
    exact h''
  · have h := (hL 0).dist_le_mul x y
    have h' : |fderiv ℝ f x (basisVec 0) - fderiv ℝ f y (basisVec 0)| ≤
        (2 * (2 ^ 16 * epsilon β I.Λ m ^ (β - 2))) * ‖x - y‖ := by
      rw [dist_eq_norm, Real.norm_eq_abs] at h
      rw [Real.coe_toNNReal _ hcoef] at h
      exact h
    have he := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le (m := m)
    have hc : 2 * (2 ^ 16 * epsilon β I.Λ m ^ (β - 2)) ≤
        2 ^ 18 * epsilon β I.Λ m ^ (β - 2) := by
      have hp : 0 ≤ epsilon β I.Λ m ^ (β - 2) := Real.rpow_nonneg he.le _
      norm_num only [pow_succ, Nat.reducePow]
      nlinarith [mul_nonneg hp (by norm_num : (0 : ℝ) ≤ 1)]
    have h'' := le_trans h' (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
    change ‖fderiv ℝ f x (basisVec 0) - fderiv ℝ f y (basisVec 0)‖ ≤ _
    simpa [Real.norm_eq_abs] using h''

theorem LimitFieldRegularity.scale_interpolation
    {α s e d A B q : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (he : 0 < e) (hd : 0 ≤ d) (hq : 0 ≤ q) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hamp : q ≤ A * e ^ s) (hlinear : q ≤ B * e ^ (s - 1) * d) :
    q ≤ (A + B) * e ^ (s - α) * d ^ α := by
  have hρ : 0 < 1 - α := by linarith
  by_cases hdz : d = 0
  · have hq0 : q ≤ 0 := by simpa [hdz] using hlinear
    have hqeq : q = 0 := le_antisymm hq0 hq
    simp [hqeq, hdz, Real.zero_rpow (ne_of_gt hα)]
  · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hdz)
    by_cases hde : d ≤ e
    · have hrpow : d ^ (1 - α) ≤ e ^ (1 - α) :=
        Real.rpow_le_rpow hd hde hρ.le
      have hd1 : d = d ^ α * d ^ (1 - α) := by
        calc
          d = d ^ (1 : ℝ) := (Real.rpow_one d).symm
          _ = d ^ (α + (1 - α)) := by congr 1; ring
          _ = d ^ α * d ^ (1 - α) := Real.rpow_add hdpos _ _
      have heexp : e ^ (s - α) = e ^ (s - 1) * e ^ (1 - α) := by
        rw [show s - α = (s - 1) + (1 - α) by ring, Real.rpow_add he]
      have hscale : e ^ (s - 1) * d ≤ e ^ (s - α) * d ^ α := by
        calc
          e ^ (s - 1) * d = e ^ (s - 1) * (d ^ α * d ^ (1 - α)) :=
            congrArg (fun z : ℝ => e ^ (s - 1) * z) hd1
          _ = (e ^ (s - 1) * d ^ α) * d ^ (1 - α) := by ring
          _ ≤ (e ^ (s - 1) * d ^ α) * e ^ (1 - α) :=
            mul_le_mul_of_nonneg_left hrpow (by positivity)
          _ = e ^ (s - α) * d ^ α := by rw [heexp]; ring
      calc
        q ≤ B * e ^ (s - 1) * d := hlinear
        _ = B * (e ^ (s - 1) * d) := by ring
        _ ≤ B * (e ^ (s - α) * d ^ α) := by
          exact mul_le_mul_of_nonneg_left hscale hB
        _ ≤ (A + B) * (e ^ (s - α) * d ^ α) :=
          mul_le_mul_of_nonneg_right (by linarith : B ≤ A + B) (by positivity)
        _ = (A + B) * e ^ (s - α) * d ^ α := by ring
    · have hed : e ≤ d := le_of_not_ge hde
      have hrpow : e ^ α ≤ d ^ α := Real.rpow_le_rpow he.le hed hα.le
      have heexp : e ^ s = e ^ (s - α) * e ^ α := by
        calc
          e ^ s = e ^ ((s - α) + α) := by congr 1; ring
          _ = e ^ (s - α) * e ^ α := Real.rpow_add he _ _
      have hscale : e ^ s ≤ e ^ (s - α) * d ^ α := by
        rw [heexp]
        exact mul_le_mul_of_nonneg_left hrpow (Real.rpow_nonneg (le_of_lt he) _)
      calc
        q ≤ A * e ^ s := hamp
        _ ≤ A * (e ^ (s - α) * d ^ α) := mul_le_mul_of_nonneg_left hscale hA
        _ ≤ (A + B) * (e ^ (s - α) * d ^ α) :=
          mul_le_mul_of_nonneg_right (by linarith : A ≤ A + B) (by positivity)
        _ = (A + B) * e ^ (s - α) * d ^ α := by ring

theorem LimitFieldRegularity.streamVel_increment_norm_le
    {β : ℝ} {C : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ)
    {m : ℕ} (hm : 1 ≤ m) (t : ℝ) (x : Vec 2) :
    ‖streamVel (Φ m) t x - streamVel (Φ (m - 1)) t x‖ ≤
      640 * epsilon β I.Λ m ^ (β - 1) := by
  rw [LimitFieldRegularity.streamVel_eq_rotateFDeriv,
      LimitFieldRegularity.streamVel_eq_rotateFDeriv]
  have hrotate_sub (L K : Vec 2 →L[ℝ] ℝ) :
      LimitFieldRegularity.rotateFDeriv L - LimitFieldRegularity.rotateFDeriv K =
          LimitFieldRegularity.rotateFDeriv (L - K) := by
    ext i
    fin_cases i
    · simp [LimitFieldRegularity.rotateFDeriv]
      ring
    · simp [LimitFieldRegularity.rotateFDeriv]
  rw [hrotate_sub]
  have hrot_le (L : Vec 2 →L[ℝ] ℝ) : ‖LimitFieldRegularity.rotateFDeriv L‖ ≤ ‖L‖ := by
    have h := LimitFieldRegularity.norm_rotateFDeriv_sub_le L 0
    simpa [LimitFieldRegularity.rotateFDeriv] using h
  calc
    ‖LimitFieldRegularity.rotateFDeriv (fderiv ℝ (Φ m t) x - fderiv ℝ (Φ (m - 1) t) x)‖ ≤
        ‖fderiv ℝ (Φ m t) x - fderiv ℝ (Φ (m - 1) t) x‖ := hrot_le _
    _ ≤ 640 * epsilon β I.Λ m ^ (β - 1) :=
      LimitFieldRegularity.streamFDeriv_increment_norm_le hseq hreg hm t x

theorem LimitFieldRegularity.streamVel_increment_spatial_holder
    {β : ℝ} {C : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ)
    {α : ℝ} (hα : 0 < α) (hαβ : α < β - 1)
    {m : ℕ} (hm : 1 ≤ m) (t : ℝ) (x y : Vec 2) :
    ‖(streamVel (Φ m) t x - streamVel (Φ (m - 1)) t x) -
        (streamVel (Φ m) t y - streamVel (Φ (m - 1)) t y)‖ ≤
      (1280 + 2 ^ 18) * epsilon β I.Λ m ^ (β - 1 - α) * ‖x - y‖ ^ α := by
  have hs : 0 < β - 1 := by linarith [I.one_lt_beta]
  have hα1 : α < 1 := by linarith [I.beta_lt]
  have he := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
    I.two_pow_seven_le (m := m)
  have hamp : ‖(streamVel (Φ m) t x - streamVel (Φ (m - 1)) t x) -
      (streamVel (Φ m) t y - streamVel (Φ (m - 1)) t y)‖ ≤
      1280 * epsilon β I.Λ m ^ (β - 1) := by
    calc
      _ ≤ ‖streamVel (Φ m) t x - streamVel (Φ (m - 1)) t x‖ +
          ‖streamVel (Φ m) t y - streamVel (Φ (m - 1)) t y‖ := norm_sub_le _ _
      _ ≤ 640 * epsilon β I.Λ m ^ (β - 1) +
          640 * epsilon β I.Λ m ^ (β - 1) := add_le_add
        (LimitFieldRegularity.streamVel_increment_norm_le hseq hreg hm t x)
        (LimitFieldRegularity.streamVel_increment_norm_le hseq hreg hm t y)
      _ = 1280 * epsilon β I.Λ m ^ (β - 1) := by ring
  have hlinear :
      ‖(streamVel (Φ m) t x - streamVel (Φ (m - 1)) t x) -
          (streamVel (Φ m) t y - streamVel (Φ (m - 1)) t y)‖ ≤
        (2 ^ 18) * epsilon β I.Λ m ^ ((β - 1) - 1) * ‖x - y‖ := by
    simpa only [show β - 2 = (β - 1) - 1 by ring] using
      LimitFieldRegularity.streamVel_increment_spatial_lipschitz hseq hreg hm t x y
  exact LimitFieldRegularity.scale_interpolation (α := α) (s := β - 1) (e := epsilon β I.Λ m)
    (d := ‖x - y‖) (A := 1280) (B := 2 ^ 18)
    (q := ‖(streamVel (Φ m) t x - streamVel (Φ (m - 1)) t x) -
      (streamVel (Φ m) t y - streamVel (Φ (m - 1)) t y)‖)
    hα hα1 he (norm_nonneg _) (norm_nonneg _) (by norm_num) (by norm_num) hamp hlinear

theorem LimitFieldRegularity.streamVelocity_time_constant_nonneg
    {β : ℝ} {A : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (htime : StreamVelocityTimeIncrementBound A I Φ) : 0 ≤ A := by
  have he := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
    I.two_pow_seven_le (m := 1)
  have h := htime 1 (by omega) 0 1 (fun _ => 0)
  have hnonneg : 0 ≤ A * epsilon β I.Λ 1 ^ (β - 2) := by
    have hnorm := norm_nonneg
      ((streamVel (Φ 1) 0 (fun _ => 0) - streamVel (Φ 0) 0 (fun _ => 0)) -
        (streamVel (Φ 1) 1 (fun _ => 0) - streamVel (Φ 0) 1 (fun _ => 0)))
    have h' := hnorm.trans h
    simpa using h'
  by_contra hA
  have hneg : A < 0 := lt_of_not_ge hA
  have hprod : 0 < -A * epsilon β I.Λ 1 ^ (β - 2) :=
    mul_pos (neg_pos.mpr hneg) (Real.rpow_pos_of_pos he _)
  nlinarith

theorem LimitFieldRegularity.streamVel_increment_time_holder
    {β A C : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ)
    (htime : StreamVelocityTimeIncrementBound A I Φ)
    {α : ℝ} (hα : 0 < α) (hαβ : α < β - 1)
    {m : ℕ} (hm : 1 ≤ m) (s t : ℝ) (x : Vec 2) :
    ‖(streamVel (Φ m) s x - streamVel (Φ (m - 1)) s x) -
        (streamVel (Φ m) t x - streamVel (Φ (m - 1)) t x)‖ ≤
      (1280 + A) * epsilon β I.Λ m ^ (β - 1 - α) * |s - t| ^ α := by
  have hs : 0 < β - 1 := by linarith [I.one_lt_beta]
  have hα1 : α < 1 := by linarith [I.beta_lt]
  have hA := LimitFieldRegularity.streamVelocity_time_constant_nonneg htime
  have he := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
    I.two_pow_seven_le (m := m)
  have hamp : ‖(streamVel (Φ m) s x - streamVel (Φ (m - 1)) s x) -
      (streamVel (Φ m) t x - streamVel (Φ (m - 1)) t x)‖ ≤
      1280 * epsilon β I.Λ m ^ (β - 1) := by
    calc
      _ ≤ ‖streamVel (Φ m) s x - streamVel (Φ (m - 1)) s x‖ +
          ‖streamVel (Φ m) t x - streamVel (Φ (m - 1)) t x‖ := norm_sub_le _ _
      _ ≤ 640 * epsilon β I.Λ m ^ (β - 1) +
          640 * epsilon β I.Λ m ^ (β - 1) := add_le_add
        (LimitFieldRegularity.streamVel_increment_norm_le hseq hreg hm s x)
        (LimitFieldRegularity.streamVel_increment_norm_le hseq hreg hm t x)
      _ = 1280 * epsilon β I.Λ m ^ (β - 1) := by ring
  have hlinear :
      ‖(streamVel (Φ m) s x - streamVel (Φ (m - 1)) s x) -
          (streamVel (Φ m) t x - streamVel (Φ (m - 1)) t x)‖ ≤
        A * epsilon β I.Λ m ^ ((β - 1) - 1) * |s - t| := by
    simpa only [show β - 2 = (β - 1) - 1 by ring] using htime m hm s t x
  exact LimitFieldRegularity.scale_interpolation (α := α) (s := β - 1) (e := epsilon β I.Λ m)
    (d := |s - t|) (A := 1280) (B := A)
    (q := ‖(streamVel (Φ m) s x - streamVel (Φ (m - 1)) s x) -
      (streamVel (Φ m) t x - streamVel (Φ (m - 1)) t x)‖)
    hα hα1 he (abs_nonneg _) (norm_nonneg _) (by norm_num) hA hamp hlinear

theorem LimitFieldRegularity.streamVel_uniformlyOn {β : ℝ} {C : ℝ}
    {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ)
    : TendstoUniformlyOn (fun M (p : ℝ × Vec 2) => streamVel (Φ M) p.1 p.2)
      (fun (p : ℝ × Vec 2) => LimitFieldRegularity.rotateFDeriv
          (LimitFieldRegularity.streamFDerivLimit hseq hreg p.1 p.2))
      atTop (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro r hr
  have hD := LimitFieldRegularity.streamFDerivLimit_uniformlyOn_spaceTime hseq hreg
  have hsmall := (Metric.tendstoUniformlyOn_iff.mp hD) r hr
  filter_upwards [hsmall] with M hM
  intro (p : ℝ × Vec 2) hp
  have hcoord : dist (LimitFieldRegularity.streamFDerivLimit hseq hreg p.1 p.2)
      (fderiv ℝ (Φ M p.1) p.2) < r := by
    exact hM (p.1, p.2) (Set.mem_univ _)
  have hrot := LimitFieldRegularity.norm_rotateFDeriv_sub_le
    (LimitFieldRegularity.streamFDerivLimit hseq hreg p.1 p.2) (fderiv ℝ (Φ M p.1) p.2)
  have hcoord' : ‖LimitFieldRegularity.streamFDerivLimit hseq hreg p.1 p.2 -
      fderiv ℝ (Φ M p.1) p.2‖ < r := by simpa [dist_eq_norm] using hcoord
  have hrot' : ‖LimitFieldRegularity.rotateFDeriv (LimitFieldRegularity.streamFDerivLimit hseq
      hreg p.1 p.2) -
      LimitFieldRegularity.rotateFDeriv (fderiv ℝ (Φ M p.1) p.2)‖ < r := lt_of_le_of_lt hrot hcoord'
  have hfinite : streamVel (Φ M) p.1 p.2 =
      LimitFieldRegularity.rotateFDeriv (fderiv ℝ (Φ M p.1) p.2) :=
    LimitFieldRegularity.streamVel_eq_rotateFDeriv (Φ M) p.1 p.2
  rw [hfinite]
  rw [dist_eq_norm]
  exact hrot'

theorem LimitFieldRegularity.streamLimit_hasFDerivAt {β : ℝ} {C : ℝ}
    {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ} {φ : ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ)
    (hlim : ∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x))) (t : ℝ)
    (x : Vec 2) : HasFDerivAt (φ t) (LimitFieldRegularity.streamFDerivLimit hseq hreg t x) x := by
  have hslice (m : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (Φ m t) := by
    have hm := (streamSeq_isAdmissible hseq m).1
    exact hm.comp (contDiff_const.prodMk contDiff_id)
  have hderiv := hasFDerivAt_of_tendstoUniformlyOn isOpen_univ
    (LimitFieldRegularity.streamFDerivLimit_uniformlyOn hseq hreg t)
    (fun m y hy => (hslice m).differentiable (by simp) y |>.hasFDerivAt)
    (fun y hy => hlim t y) (Set.mem_univ x)
  exact hderiv

theorem LimitFieldRegularity.streamLimit_differentiable {β : ℝ} {C : ℝ}
    {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ} {φ : ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ)
    (hlim : ∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x))) (t : ℝ) :
    Differentiable ℝ (φ t) := by
  intro x
  exact (LimitFieldRegularity.streamLimit_hasFDerivAt hseq hreg hlim t x).differentiableAt

theorem LimitFieldRegularity.streamLimit_velocity_eq {β : ℝ} {C : ℝ}
    {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ} {φ : ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ)
    (hlim : ∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x)))
    (t : ℝ) (x : Vec 2) :
    streamVel φ t x = LimitFieldRegularity.rotateFDeriv (LimitFieldRegularity.streamFDerivLimit
        hseq hreg t x) := by
  rw [LimitFieldRegularity.streamVel_eq_rotateFDeriv,
    (LimitFieldRegularity.streamLimit_hasFDerivAt hseq hreg hlim t x).fderiv]

theorem LimitFieldRegularity.streamVelocity_tendsto {β : ℝ} {C : ℝ}
    {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ} {φ : ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ)
    (hlim : ∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x)))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (x : Vec 2) :
    Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (streamVel φ t x)) := by
  have hrot := (LimitFieldRegularity.streamVel_uniformlyOn hseq hreg).tendsto_at
    (x := (t, x)) ⟨ht, Set.mem_univ x⟩
  rw [LimitFieldRegularity.streamLimit_velocity_eq hseq hreg hlim t x]
  exact hrot

theorem LimitFieldRegularity.streamVel_zero_from_seq
    {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (t : ℝ) (x : Vec 2) :
    streamVel (Φ 0) t x = 0 := by
  rw [LimitFieldRegularity.streamVel_eq_rotateFDeriv, hseq.1]
  simp [LimitFieldRegularity.rotateFDeriv]

theorem LimitFieldRegularity.sequence_telescope {G : Type*} [AddCommGroup G]
    (v : ℕ → G) (h0 : v 0 = 0) (M : ℕ) :
    v M = ∑ j ∈ Finset.range M, (v (j + 1) - v j) := by
  induction M with
  | zero => simp [h0]
  | succ M ih =>
      rw [Finset.sum_range_succ]
      simp only [Nat.add_succ]
      rw [← ih]
      abel

theorem LimitFieldRegularity.epsilon_holder_series_bound {β ρ : ℝ} (I : Ingredients β)
    (hρ : 0 < ρ) (M : ℕ) :
    (∑ j ∈ Finset.range M, epsilon β I.Λ (j + 1) ^ ρ) ≤
      epsilon β I.Λ 1 ^ ρ / (1 - (I.Λ : ℝ) ^ (-ρ)) := by
  simpa [Nat.add_comm] using epsilon_rpow_sum_bound I hρ 1 M

theorem LimitFieldRegularity.streamVelocity_spatial_partial_sum_bound
    {β C : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ)
    {α ρ : ℝ} (hα : 0 < α) (hαβ : α < β - 1)
    (hρ : ρ = β - 1 - α) (M : ℕ) (t : ℝ) (x y : Vec 2) :
    ‖streamVel (Φ M) t x - streamVel (Φ M) t y‖ ≤
      (1280 + 2 ^ 18) * ‖x - y‖ ^ α *
        ∑ j ∈ Finset.range M, epsilon β I.Λ (j + 1) ^ ρ := by
  let q : ℕ → Vec 2 := fun n => streamVel (Φ n) t x - streamVel (Φ n) t y
  have hq0 : q 0 = 0 := by
    dsimp [q]
    rw [LimitFieldRegularity.streamVel_zero_from_seq hseq,
        LimitFieldRegularity.streamVel_zero_from_seq hseq]
    simp
  have htel := LimitFieldRegularity.sequence_telescope q hq0 M
  change ‖q M‖ ≤ _
  rw [htel]
  calc
    ‖∑ j ∈ Finset.range M,
        (q (j + 1) - q j)‖ ≤
        ∑ j ∈ Finset.range M,
          ‖q (j + 1) - q j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range M,
          ((1280 + 2 ^ 18) * epsilon β I.Λ (j + 1) ^ ρ * ‖x - y‖ ^ α) :=
        Finset.sum_le_sum fun j hj => by
          have hqeq : q (j + 1) - q j =
              (streamVel (Φ (j + 1)) t x - streamVel (Φ j) t x) -
                (streamVel (Φ (j + 1)) t y - streamVel (Φ j) t y) := by
            dsimp [q]
            abel
          rw [hqeq]
          simpa [hρ] using LimitFieldRegularity.streamVel_increment_spatial_holder hseq hreg hα hαβ
            (m := j + 1) (by omega) t x y
    _ = (1280 + 2 ^ 18) * ‖x - y‖ ^ α *
          ∑ j ∈ Finset.range M, epsilon β I.Λ (j + 1) ^ ρ := by
        calc
          _ = ∑ j ∈ Finset.range M,
                ((1280 + 2 ^ 18) * ‖x - y‖ ^ α * epsilon β I.Λ (j + 1) ^ ρ) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
          _ = (1280 + 2 ^ 18) * ‖x - y‖ ^ α *
                ∑ j ∈ Finset.range M, epsilon β I.Λ (j + 1) ^ ρ := by
              rw [Finset.mul_sum]

theorem LimitFieldRegularity.streamVelocity_spatial_finite_bound
    {β C : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ)
    {α ρ : ℝ} (hα : 0 < α) (hαβ : α < β - 1)
    (hρ : ρ = β - 1 - α) (hρpos : 0 < ρ) (M : ℕ) (t : ℝ) (x y : Vec 2) :
    ‖streamVel (Φ M) t x - streamVel (Φ M) t y‖ ≤
      (1280 + 2 ^ 18) * ‖x - y‖ ^ α *
        (epsilon β I.Λ 1 ^ ρ / (1 - (I.Λ : ℝ) ^ (-ρ))) := by
  have hsum := LimitFieldRegularity.epsilon_holder_series_bound I hρpos M
  calc
    ‖streamVel (Φ M) t x - streamVel (Φ M) t y‖ ≤
        (1280 + 2 ^ 18) * ‖x - y‖ ^ α *
          ∑ j ∈ Finset.range M, epsilon β I.Λ (j + 1) ^ ρ :=
      LimitFieldRegularity.streamVelocity_spatial_partial_sum_bound hseq hreg hα hαβ hρ M t x y
    _ ≤ (1280 + 2 ^ 18) * ‖x - y‖ ^ α *
          (epsilon β I.Λ 1 ^ ρ / (1 - (I.Λ : ℝ) ^ (-ρ))) :=
      mul_le_mul_of_nonneg_left hsum
        (mul_nonneg (by norm_num) (Real.rpow_nonneg (norm_nonneg _) _))

theorem LimitFieldRegularity.streamVelocity_time_partial_sum_bound
    {β A C : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ)
    (htime : StreamVelocityTimeIncrementBound A I Φ)
    {α ρ : ℝ} (hα : 0 < α) (hαβ : α < β - 1)
    (hρ : ρ = β - 1 - α) (M : ℕ) (s t : ℝ) (x : Vec 2) :
    ‖streamVel (Φ M) s x - streamVel (Φ M) t x‖ ≤
      (1280 + A) * |s - t| ^ α *
        ∑ j ∈ Finset.range M, epsilon β I.Λ (j + 1) ^ ρ := by
  let q : ℕ → Vec 2 := fun n => streamVel (Φ n) s x - streamVel (Φ n) t x
  have hq0 : q 0 = 0 := by
    dsimp [q]
    rw [LimitFieldRegularity.streamVel_zero_from_seq hseq,
        LimitFieldRegularity.streamVel_zero_from_seq hseq]
    simp
  have htel := LimitFieldRegularity.sequence_telescope q hq0 M
  change ‖q M‖ ≤ _
  rw [htel]
  calc
    ‖∑ j ∈ Finset.range M,
        (q (j + 1) - q j)‖ ≤
        ∑ j ∈ Finset.range M,
            ‖q (j + 1) - q j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range M,
          ((1280 + A) * epsilon β I.Λ (j + 1) ^ ρ * |s - t| ^ α) :=
        Finset.sum_le_sum fun j hj => by
          have hqeq : q (j + 1) - q j =
              (streamVel (Φ (j + 1)) s x - streamVel (Φ j) s x) -
                (streamVel (Φ (j + 1)) t x - streamVel (Φ j) t x) := by
            dsimp [q]
            abel
          rw [hqeq]
          simpa [hρ] using LimitFieldRegularity.streamVel_increment_time_holder hseq hreg htime hα
              hαβ
            (m := j + 1) (by omega) s t x
    _ = (1280 + A) * |s - t| ^ α *
          ∑ j ∈ Finset.range M, epsilon β I.Λ (j + 1) ^ ρ := by
        calc
          _ = ∑ j ∈ Finset.range M,
                ((1280 + A) * |s - t| ^ α * epsilon β I.Λ (j + 1) ^ ρ) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
          _ = (1280 + A) * |s - t| ^ α *
                ∑ j ∈ Finset.range M, epsilon β I.Λ (j + 1) ^ ρ := by
              rw [Finset.mul_sum]

theorem LimitFieldRegularity.streamVelocity_time_finite_bound
    {β A C : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ)
    (htime : StreamVelocityTimeIncrementBound A I Φ)
    {α ρ : ℝ} (hα : 0 < α) (hαβ : α < β - 1)
    (hρ : ρ = β - 1 - α) (hρpos : 0 < ρ) (M : ℕ) (s t : ℝ) (x : Vec 2) :
    ‖streamVel (Φ M) s x - streamVel (Φ M) t x‖ ≤
      (1280 + A) * |s - t| ^ α *
        (epsilon β I.Λ 1 ^ ρ / (1 - (I.Λ : ℝ) ^ (-ρ))) := by
  have hsum := LimitFieldRegularity.epsilon_holder_series_bound I hρpos M
  calc
    ‖streamVel (Φ M) s x - streamVel (Φ M) t x‖ ≤
        (1280 + A) * |s - t| ^ α *
          ∑ j ∈ Finset.range M, epsilon β I.Λ (j + 1) ^ ρ :=
      LimitFieldRegularity.streamVelocity_time_partial_sum_bound hseq hreg htime hα hαβ hρ M s t x
    _ ≤ (1280 + A) * |s - t| ^ α *
          (epsilon β I.Λ 1 ^ ρ / (1 - (I.Λ : ℝ) ^ (-ρ))) :=
      mul_le_mul_of_nonneg_left hsum
        (mul_nonneg (by linarith [LimitFieldRegularity.streamVelocity_time_constant_nonneg htime])
          (Real.rpow_nonneg (abs_nonneg _) _))

theorem LimitFieldRegularity.streamVelocity_spatial_holder
    {β C : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ)
    {φ : ℝ → Vec 2 → ℝ}
    (hlim : ∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x)))
    {α : ℝ} (hα : 0 < α) (hαβ : α < β - 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x y,
      ‖streamVel φ t x - streamVel φ t y‖ ≤ K * ‖x - y‖ ^ α := by
  let ρ : ℝ := β - 1 - α
  let K : ℝ := (1280 + 2 ^ 18) *
    (epsilon β I.Λ 1 ^ ρ / (1 - (I.Λ : ℝ) ^ (-ρ)))
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hqcontract : (I.Λ : ℝ) ^ (-ρ) < 1 := inverse_lambda_rpow_lt_one I hρ
  have hden : 0 < 1 - (I.Λ : ℝ) ^ (-ρ) := by linarith
  have hK : 0 ≤ K := by
    dsimp [K]
    have hquot : 0 ≤ epsilon β I.Λ 1 ^ ρ / (1 - (I.Λ : ℝ) ^ (-ρ)) :=
      div_nonneg (Real.rpow_nonneg (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
        I.two_pow_seven_le (m := 1)).le _) hden.le
    exact mul_nonneg (by norm_num) hquot
  refine ⟨K, hK, ?_⟩
  intro t ht x y
  have htx := LimitFieldRegularity.streamVelocity_tendsto hseq hreg hlim t ht x
  have hty := LimitFieldRegularity.streamVelocity_tendsto hseq hreg hlim t ht y
  have hdiff := htx.sub hty
  have hnorm := hdiff.norm
  have hfinite (M : ℕ) :
      ‖streamVel (Φ M) t x - streamVel (Φ M) t y‖ ≤
        K * ‖x - y‖ ^ α := by
    have hρeq : ρ = β - 1 - α := rfl
    calc
      _ ≤ (1280 + 2 ^ 18) * ‖x - y‖ ^ α *
            (epsilon β I.Λ 1 ^ ρ / (1 - (I.Λ : ℝ) ^ (-ρ))) :=
        LimitFieldRegularity.streamVelocity_spatial_finite_bound hseq hreg hα hαβ hρeq hρ M t x y
      _ = K * ‖x - y‖ ^ α := by dsimp [K]; ring
  exact le_of_tendsto hnorm (Filter.Eventually.of_forall hfinite)

theorem LimitFieldRegularity.streamVelocity_time_holder
    {β A C : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ)
    (htime : StreamVelocityTimeIncrementBound A I Φ)
    {φ : ℝ → Vec 2 → ℝ}
    (hlim : ∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x)))
    {α : ℝ} (hα : 0 < α) (hαβ : α < β - 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x,
      ‖streamVel φ s x - streamVel φ t x‖ ≤ K * |s - t| ^ α := by
  let ρ : ℝ := β - 1 - α
  let K : ℝ := (1280 + A) *
    (epsilon β I.Λ 1 ^ ρ / (1 - (I.Λ : ℝ) ^ (-ρ)))
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hqcontract : (I.Λ : ℝ) ^ (-ρ) < 1 := inverse_lambda_rpow_lt_one I hρ
  have hden : 0 < 1 - (I.Λ : ℝ) ^ (-ρ) := by linarith
  have hK : 0 ≤ K := by
    dsimp [K]
    have hquot : 0 ≤ epsilon β I.Λ 1 ^ ρ / (1 - (I.Λ : ℝ) ^ (-ρ)) :=
      div_nonneg (Real.rpow_nonneg (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
        I.two_pow_seven_le (m := 1)).le _) hden.le
    have hA := LimitFieldRegularity.streamVelocity_time_constant_nonneg htime
    exact mul_nonneg (by linarith only [hA]) hquot
  refine ⟨K, hK, ?_⟩
  intro s hs t ht x
  have hts := LimitFieldRegularity.streamVelocity_tendsto hseq hreg hlim s hs x
  have htt := LimitFieldRegularity.streamVelocity_tendsto hseq hreg hlim t ht x
  have hdiff := hts.sub htt
  have hnorm := hdiff.norm
  have hfinite (M : ℕ) :
      ‖streamVel (Φ M) s x - streamVel (Φ M) t x‖ ≤ K * |s - t| ^ α := by
    have hρeq : ρ = β - 1 - α := rfl
    calc
      _ ≤ (1280 + A) * |s - t| ^ α *
            (epsilon β I.Λ 1 ^ ρ / (1 - (I.Λ : ℝ) ^ (-ρ))) :=
        LimitFieldRegularity.streamVelocity_time_finite_bound hseq hreg htime hα hαβ hρeq hρ M s t x
      _ = K * |s - t| ^ α := by dsimp [K]; ring
  exact le_of_tendsto hnorm (Filter.Eventually.of_forall hfinite)

theorem LimitFieldRegularity.limitField_holder_class
    {β A C : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ)
    (htime : StreamVelocityTimeIncrementBound A I Φ)
    {φ : ℝ → Vec 2 → ℝ}
    (hlim : ∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x)))
    (hvelUniform : TendstoUniformlyOn
      (fun M (p : ℝ × Vec 2) => streamVel (Φ M) p.1 p.2)
      (fun p => streamVel φ p.1 p.2) atTop (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ))
    {α : ℝ} (hα : 0 < α) (hαβ : α < β - 1) : IsHolderClass α (streamVel φ) := by
  have hspace := LimitFieldRegularity.streamVelocity_spatial_holder hseq hreg hlim hα hαβ
  have htimeHolder := LimitFieldRegularity.streamVelocity_time_holder hseq hreg htime hlim hα hαβ
  have hcontinuous : ContinuousOn (fun p : ℝ × Vec 2 => streamVel φ p.1 p.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
    apply hvelUniform.continuousOn
    apply Filter.Frequently.of_forall
    intro M
    exact (smoothPeriodic_streamVel (streamSeq_isAdmissible hseq M)).smooth.continuous.continuousOn
  have hbounded : ∃ B : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x,
      ‖streamVel φ t x‖ ≤ B := by
    let B : ℝ := LimitFieldRegularity.streamDerivativeTailConstant I * epsilon β I.Λ 1 ^ (β - 1)
    have hB : 0 ≤ B := by
      dsimp [B]
      exact mul_nonneg (LimitFieldRegularity.streamDerivativeTailConstant_pos I).le
        (Real.rpow_nonneg (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
          I.two_pow_seven_le (m := 1)).le _)
    refine ⟨B, ?_⟩
    intro t ht x
    have hlimderiv := LimitFieldRegularity.streamFDerivLimit_tendsto hseq hreg t x
    have hboundM (M : ℕ) :
        ‖fderiv ℝ (Φ M t) x‖ ≤ B := by
      have h0 : fderiv ℝ (Φ 0 t) x = 0 := by
        rw [hseq.1]
        simp
      have htail := LimitFieldRegularity.streamFDeriv_tail_le hseq hreg 0 M t x
      simpa [B, h0] using htail
    have hboundLimit :
        ‖LimitFieldRegularity.streamFDerivLimit hseq hreg t x‖ ≤ B :=
      le_of_tendsto hlimderiv.norm (Filter.Eventually.of_forall hboundM)
    have hrot : ‖LimitFieldRegularity.rotateFDeriv (LimitFieldRegularity.streamFDerivLimit hseq
        hreg t x)‖ ≤ B := by
      have hboundLimit' : ‖LimitFieldRegularity.streamFDerivLimit hseq hreg t x - 0‖ ≤ B := by
        simpa using hboundLimit
      have hcontract := LimitFieldRegularity.norm_rotateFDeriv_sub_le
        (LimitFieldRegularity.streamFDerivLimit hseq hreg t x) 0
      simpa [LimitFieldRegularity.rotateFDeriv] using hcontract.trans hboundLimit'
    rw [LimitFieldRegularity.streamLimit_velocity_eq hseq hreg hlim t x]
    exact hrot
  rcases hspace with ⟨Ks, hKs, hspatial⟩
  rcases htimeHolder with ⟨Kt, hKt, htemporal⟩
  refine ⟨?_, hcontinuous, hbounded, ⟨Ks, hspatial⟩, ⟨Kt, htemporal⟩⟩
  intro t ht n x
  have hfinite (M : ℕ) :
      streamVel (Φ M) t (x + latticeShift n) = streamVel (Φ M) t x := by
    have h := (smoothPeriodic_streamVel (streamSeq_isAdmissible hseq M)).periodic
      0 n t x
    simpa using h
  have hleft := LimitFieldRegularity.streamVelocity_tendsto hseq hreg hlim t ht (x + latticeShift n)
  have hleft' := hleft.congr' (Filter.Eventually.of_forall hfinite)
  have hright := LimitFieldRegularity.streamVelocity_tendsto hseq hreg hlim t ht x
  exact tendsto_nhds_unique hleft' hright

theorem LimitFieldRegularity.smoothPartial {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (v : Vec 2) : ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ ψ x v) := by
  exact (hψ.fderiv_right (by simp)).clm_apply contDiff_const

theorem LimitFieldRegularity.partial_fderiv_eq_second {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (v w : Vec 2) (x : Vec 2) :
    fderiv ℝ (fun y => fderiv ℝ ψ y v) x w =
      fderiv ℝ (fderiv ℝ ψ) x w v := by
  have hc : DifferentiableAt ℝ (fderiv ℝ ψ) x :=
    (hψ.fderiv_right (m := 1) (by simp)).differentiable (by simp) x
  have hu : DifferentiableAt ℝ (fun _ : Vec 2 => v) x := differentiableAt_const v
  rw [fderiv_clm_apply hc hu]
  simp

theorem LimitFieldRegularity.limitPotential_divFree_at_time {φ : ℝ → Vec 2 → ℝ} (t : ℝ)
    (hφ : Differentiable ℝ (φ t))
    (hvel : Continuous (fun x => streamVel φ t x)) :
    ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ x, vecDot (streamVel φ t x) (spaceGrad ψ x) = 0 := by
  intro ψ hψ hψcompact
  let g : Vec 2 → ℝ := φ t
  let f0 : Vec 2 → ℝ := fun x => fderiv ℝ ψ x (basisVec 0)
  let f1 : Vec 2 → ℝ := fun x => fderiv ℝ ψ x (basisVec 1)
  let d0g : Vec 2 → ℝ := fun x => fderiv ℝ g x (basisVec 0)
  let d1g : Vec 2 → ℝ := fun x => fderiv ℝ g x (basisVec 1)
  let d1f0 : Vec 2 → ℝ := fun x => fderiv ℝ f0 x (basisVec 1)
  let d0f1 : Vec 2 → ℝ := fun x => fderiv ℝ f1 x (basisVec 0)
  have hgcont : Continuous g := by
    simpa [g] using hφ.continuous
  have hd0cont : Continuous d0g := by
    have heq : (fun x => (streamVel φ t x) 1) = d0g := by
      funext x
      simp [g, d0g, streamVel, sigmaMat, Matrix.mulVec, dotProduct,
        spaceGrad, Fin.sum_univ_two]
    rw [← heq]
    exact (continuous_apply 1).comp hvel
  have hd1cont : Continuous d1g := by
    have heq : (fun x => (streamVel φ t x) 0) = fun x => -d1g x := by
      funext x
      simp [g, d1g, streamVel, sigmaMat, Matrix.mulVec, dotProduct,
        spaceGrad, Fin.sum_univ_two]
    have hneg : Continuous (fun x => -d1g x) := by
      rw [← heq]
      exact (continuous_apply 0).comp hvel
    convert hneg.neg using 1
    ext x
    simp
  have hf0 : ContDiff ℝ (⊤ : ℕ∞) f0 := by
    exact LimitFieldRegularity.smoothPartial hψ (basisVec 0)
  have hf1 : ContDiff ℝ (⊤ : ℕ∞) f1 := by
    exact LimitFieldRegularity.smoothPartial hψ (basisVec 1)
  have hf0cont : Continuous f0 := hf0.continuous
  have hf1cont : Continuous f1 := hf1.continuous
  have hd1f0cont : Continuous d1f0 := by
    have h := LimitFieldRegularity.smoothPartial hf0 (basisVec 1)
    exact h.continuous
  have hd0f1cont : Continuous d0f1 := by
    have h := LimitFieldRegularity.smoothPartial hf1 (basisVec 0)
    exact h.continuous
  have hf0compact : HasCompactSupport f0 := by
    dsimp [f0]
    exact hψcompact.fderiv_apply ℝ (basisVec 0)
  have hf1compact : HasCompactSupport f1 := by
    dsimp [f1]
    exact hψcompact.fderiv_apply ℝ (basisVec 1)
  have hd1f0compact : HasCompactSupport d1f0 := by
    dsimp [d1f0, f0]
    exact (hψcompact.fderiv_apply ℝ (basisVec 0)).fderiv_apply ℝ (basisVec 1)
  have hd0f1compact : HasCompactSupport d0f1 := by
    dsimp [d0f1, f1]
    exact (hψcompact.fderiv_apply ℝ (basisVec 1)).fderiv_apply ℝ (basisVec 0)
  have h_int_d1f0_g : Integrable (fun x => d1f0 x * g x) := by
    apply (hd1f0cont.mul hgcont).integrable_of_hasCompactSupport
    exact hd1f0compact.mul_right
  have h_int_f0_d1g : Integrable (fun x => f0 x * d1g x) := by
    apply (hf0cont.mul hd1cont).integrable_of_hasCompactSupport
    exact hf0compact.mul_right
  have h_int_f0_g : Integrable (fun x => f0 x * g x) := by
    apply (hf0cont.mul hgcont).integrable_of_hasCompactSupport
    exact hf0compact.mul_right
  have h_int_d0f1_g : Integrable (fun x => d0f1 x * g x) := by
    apply (hd0f1cont.mul hgcont).integrable_of_hasCompactSupport
    exact hd0f1compact.mul_right
  have h_int_f1_d0g : Integrable (fun x => f1 x * d0g x) := by
    apply (hf1cont.mul hd0cont).integrable_of_hasCompactSupport
    exact hf1compact.mul_right
  have h_int_f1_g : Integrable (fun x => f1 x * g x) := by
    apply (hf1cont.mul hgcont).integrable_of_hasCompactSupport
    exact hf1compact.mul_right
  have h_ibp1 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    h_int_d1f0_g h_int_f0_d1g h_int_f0_g
    (fun x _ => (hf0.differentiable (by simp)) x) (fun x _ => hφ x)
  have h_ibp0 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    h_int_d0f1_g h_int_f1_d0g h_int_f1_g
    (fun x _ => (hf1.differentiable (by simp)) x) (fun x _ => hφ x)
  have hsecond (x : Vec 2) : d1f0 x = d0f1 x := by
    have hs := (hψ.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
    change fderiv ℝ (fun y => fderiv ℝ ψ y (basisVec 0)) x (basisVec 1) =
      fderiv ℝ (fun y => fderiv ℝ ψ y (basisVec 1)) x (basisVec 0)
    rw [LimitFieldRegularity.partial_fderiv_eq_second hψ (basisVec 0) (basisVec 1) x,
      LimitFieldRegularity.partial_fderiv_eq_second hψ (basisVec 1) (basisVec 0) x]
    exact hs (basisVec 1) (basisVec 0)
  have hcancel : (∫ x, d1f0 x * g x) - (∫ x, d0f1 x * g x) = 0 := by
    rw [show (fun x => d1f0 x * g x) = (fun x => d0f1 x * g x) by
      funext x; rw [hsecond x]]
    ring
  have hpoint (x : Vec 2) :
      vecDot (streamVel φ t x) (spaceGrad ψ x) =
        -(d1g x * f0 x) + d0g x * f1 x := by
      simp [g, d0g, d1g, f0, f1, streamVel, sigmaMat, Matrix.mulVec, dotProduct,
      vecDot, spaceGrad, Fin.sum_univ_two]
  have h_int_d1g_f0 : Integrable (fun x => d1g x * f0 x) := by
    apply (hd1cont.mul hf0cont).integrable_of_hasCompactSupport
    exact hf0compact.mul_left
  have h_int_d0g_f1 : Integrable (fun x => d0g x * f1 x) := by
    apply (hd0cont.mul hf1cont).integrable_of_hasCompactSupport
    exact hf1compact.mul_left
  calc
    ∫ x, vecDot (streamVel φ t x) (spaceGrad ψ x) =
        ∫ x, (-(d1g x * f0 x) + d0g x * f1 x) := by
          apply integral_congr_ae
          filter_upwards with x
          exact hpoint x
    _ = -(∫ x, f0 x * d1g x) + (∫ x, f1 x * d0g x) := by
          calc
            ∫ x, (-(d1g x * f0 x) + d0g x * f1 x) =
                (∫ x, -(d1g x * f0 x)) + ∫ x, d0g x * f1 x :=
              integral_add (h_int_d1g_f0.neg) h_int_d0g_f1
            _ = -(∫ x, f0 x * d1g x) + (∫ x, f1 x * d0g x) := by
              congr 1
              · calc
                  (∫ x, -(d1g x * f0 x)) = ∫ x, -(f0 x * d1g x) := by
                    apply integral_congr_ae
                    filter_upwards with x
                    ring
                  _ = -(∫ x, f0 x * d1g x) := integral_neg _
              · apply integral_congr_ae
                filter_upwards with x
                ring
    _ = (∫ x, d1f0 x * g x) - (∫ x, d0f1 x * g x) := by
          rw [h_ibp1, h_ibp0]
          ring
    _ = 0 := hcancel

/-- The pointwise limit, tail, differentiability, and uniform velocity limit
consequences of the stream-regularity increment estimates. -/
theorem limitField_pointwise_tail_differentiable_velocity {β : ℝ} {C : ℝ}
    {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ) :
    ∃ φ : ℝ → Vec 2 → ℝ,
      (∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x))) ∧
      (∀ M t x, |φ t x - Φ M t x| ≤ 11 * epsilon β I.Λ (M + 1) ^ β) ∧
      (∀ t, Differentiable ℝ (φ t)) ∧
      TendstoUniformlyOn (fun M (p : ℝ × Vec 2) => streamVel (Φ M) p.1 p.2)
        (fun p => streamVel φ p.1 p.2) atTop
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
  obtain ⟨φ, hlim⟩ := exists_streamLimit hseq hreg
  refine ⟨φ, hlim, ?_, ?_, ?_⟩
  · intro M t x
    exact streamLimit_tail_bound_uniform hseq hreg hlim M t x
  · intro t
    exact LimitFieldRegularity.streamLimit_differentiable hseq hreg hlim t
  · rw [Metric.tendstoUniformlyOn_iff]
    intro r hr
    have hrot := (Metric.tendstoUniformlyOn_iff.mp
      (LimitFieldRegularity.streamVel_uniformlyOn hseq hreg)) r hr
    filter_upwards [hrot] with M hM
    intro p hp
    have hderiv : fderiv ℝ (φ p.1) p.2 = LimitFieldRegularity.streamFDerivLimit hseq hreg p.1 p.2 :=
      (LimitFieldRegularity.streamLimit_hasFDerivAt hseq hreg hlim p.1 p.2).fderiv
    have heq : streamVel φ p.1 p.2 =
        LimitFieldRegularity.rotateFDeriv (LimitFieldRegularity.streamFDerivLimit hseq hreg p.1
            p.2) := by
      rw [LimitFieldRegularity.streamVel_eq_rotateFDeriv, hderiv]
    rw [heq]
    exact hM p hp

/-- Conditional limit-field regularity in the form used for the limit field.  The
additional `htime` input is the time-increment estimate needed for temporal
Hölder regularity; all other conclusions follow from the explicit stream-regularity bounds. -/
theorem limitField_regular_conditional {β A C α : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : IsStreamSeq I Φ) (hreg : StreamRegularityBounds C I Φ)
    (htime : StreamVelocityTimeIncrementBound A I Φ)
    (hα : 0 < α) (hαβ : α < β - 1) :
    ∃ φ : ℝ → Vec 2 → ℝ,
      (∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x))) ∧
      (∀ M t x, |φ t x - Φ M t x| ≤ 11 * epsilon β I.Λ (M + 1) ^ β) ∧
      (∀ t, Differentiable ℝ (φ t)) ∧
      TendstoUniformlyOn (fun M (p : ℝ × Vec 2) => streamVel (Φ M) p.1 p.2)
        (fun p => streamVel φ p.1 p.2) atTop
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) ∧
      IsHolderClass α (streamVel φ) ∧ IsDivFree (streamVel φ) := by
  obtain ⟨φ, hlim, htail, hdiff, hvelUniform⟩ :=
    limitField_pointwise_tail_differentiable_velocity hseq hreg
  have hclass := LimitFieldRegularity.limitField_holder_class hseq hreg htime hlim hvelUniform hα
      hαβ
  have hdivfree : IsDivFree (streamVel φ) := by
    intro t ht ψ hψ hψcompact
    have hcont : ContinuousOn
        (fun p : ℝ × Vec 2 => streamVel φ p.1 p.2)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := hclass.2.1
    have hslice : Continuous (fun x => streamVel φ t x) := by
      apply continuousOn_univ.mp
      have hmaps : ∀ x : Vec 2, x ∈ Set.univ →
          (t, x) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.univ := by
        intro x _
        exact ⟨ht, Set.mem_univ x⟩
      change ContinuousOn
        ((fun p : ℝ × Vec 2 => streamVel φ p.1 p.2) ∘ fun x => (t, x)) Set.univ
      exact hcont.comp (continuous_const.prodMk continuous_id).continuousOn hmaps
    exact LimitFieldRegularity.limitPotential_divFree_at_time t (hdiff t) hslice ψ hψ hψcompact
  exact ⟨φ, hlim, htail, hdiff, hvelUniform, hclass, hdivfree⟩

end AVenhance.Infra.Construction

end
