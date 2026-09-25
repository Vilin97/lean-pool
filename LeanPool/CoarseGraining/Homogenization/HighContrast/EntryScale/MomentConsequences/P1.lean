/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.NNReal.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Order.Interval.Finset.Nat
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.GeometrySeries.DescendantCardinality
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincare.Setup.HarmonicAndData
public import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicPartition
public import LeanPool.CoarseGraining.Homogenization.HighContrast.EntryScale.Inputs

/-! # P1 -/

@[expose] public section

open scoped BigOperators
open scoped Topology
open Filter


/-!
# Consequences of the high centered moment hypothesis

Planned home for the union-bound and terminal fluctuation steps derived from
Assumption `a.HM`.
-/


namespace Homogenization.HighContrast.EntryScale

/--
Source labels `a.HM`, `e.Q.large`, and `p.HC.CR`: the high moment exponent
dominates the finite Holder exponent needed for the bad-event square.
-/
theorem highCenteredMoment_two_mul_p4_xi_le_Q
    {d : ℕ} [NeZero d] {P : Homogenization.Book.Ch04.RestrictionCoeffLaw d}
    {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    (hP4 : Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticity P)
    (hparams : hP4.params = hm.p4Params) :
    2 * (hP4.xi : ℝ) ≤ hm.Q :=
  by
    have hxi : hP4.xi = hm.p4Params.xi :=
      congrArg
        Homogenization.Book.Ch05.QuantitativeCoarseGrainedEllipticityParams.xi
        hparams
    simpa [hxi] using hm.two_mul_p4_xi_le_Q

/--
Source labels `a.HM`, `e.Q.large`, `l.union.bound`: the high-moment exponent
is strictly positive.
-/
theorem highCenteredMoment_Q_pos {d : ℕ} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc) :
    0 < hm.Q := by
  linarith [hm.two_le_Q]

/--
Source label `l.union.bound`: `Q rho_M > d + 4` implies the positive
union-bound decay exponent `Q rho_M - d`.
-/
theorem highCenteredMoment_Q_mul_rhoM_sub_dim_pos
    {d : ℕ} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc) :
    0 < hm.Q * hc.rhoM - (d : ℝ) := by
  linarith [hm.Q_mul_rhoM_gt]

/--
Source label `l.union.bound`: positivity of the convolution decay exponent
`c_Q = min {Q rho_M - d, Q gamma}`.
-/
theorem highCenteredMoment_min_decay_pos {d : ℕ} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc) :
    0 < min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma) := by
  have hleft : 0 < hm.Q * hc.rhoM - (d : ℝ) :=
    highCenteredMoment_Q_mul_rhoM_sub_dim_pos hm
  have hright : 0 < hm.Q * hm.gamma :=
    mul_pos (highCenteredMoment_Q_pos hm) hm.gamma_pos
  exact lt_min hleft hright

/--
Source label `l.union.bound`: the linear prefactor in
`(1 + m - N) 3^{-c(m-N)}` is absorbed by the exponential decay.
-/
theorem tendsto_linear_mul_rpow_three_neg_atTop_nhds_zero {c : ℝ}
    (hc : 0 < c) :
    Tendsto (fun n : ℕ =>
      (((n : ℝ) + 1) * (3 : ℝ) ^ (-c * (n : ℝ)))) atTop (𝓝 (0 : ℝ)) := by
  have hlog_pos : 0 < c * Real.log 3 := by
    exact mul_pos hc (Real.log_pos (by norm_num : (1 : ℝ) < 3))
  have hmain_real :
      Tendsto (fun x : ℝ =>
        (x + 1) * Real.exp (-(c * Real.log 3) * x)) atTop (𝓝 (0 : ℝ)) := by
    have hlin :
        Tendsto (fun x : ℝ =>
          x ^ (1 : ℝ) * Real.exp (-(c * Real.log 3) * x))
          atTop (𝓝 (0 : ℝ)) :=
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        (1 : ℝ) (c * Real.log 3) hlog_pos
    have hexp :
        Tendsto (fun x : ℝ => Real.exp (-(c * Real.log 3) * x))
          atTop (𝓝 (0 : ℝ)) := by
      have harg :
          Tendsto (fun x : ℝ => -(c * Real.log 3) * x) atTop atBot :=
        tendsto_id.const_mul_atTop_of_neg (by linarith)
      exact Real.tendsto_exp_atBot.comp harg
    have hsum :
        Tendsto (fun x : ℝ =>
          x ^ (1 : ℝ) * Real.exp (-(c * Real.log 3) * x) +
            Real.exp (-(c * Real.log 3) * x)) atTop (𝓝 (0 : ℝ)) := by
      simpa using hlin.add hexp
    simpa [Real.rpow_one, add_mul] using hsum
  have hnat :
      Tendsto (fun n : ℕ =>
        (((n : ℝ) + 1) * Real.exp (-(c * Real.log 3) * (n : ℝ))))
        atTop (𝓝 (0 : ℝ)) :=
    hmain_real.comp tendsto_natCast_atTop_atTop
  refine hnat.congr' ?_
  filter_upwards with n
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring_nf

/--
Source label `l.union.bound`: a concrete threshold after which
`C (n+1) 3^{-c n}` is smaller than any prescribed positive tolerance.
-/
theorem exists_forall_ge_const_mul_linear_rpow_three_neg_le
    {C c η : ℝ} (hc : 0 < c) (hη : 0 < η) :
    ∃ K : ℕ, ∀ n : ℕ, K ≤ n →
      C * (((n : ℝ) + 1) * (3 : ℝ) ^ (-c * (n : ℝ))) ≤ η := by
  have hlim :
      Tendsto (fun n : ℕ =>
        C * (((n : ℝ) + 1) * (3 : ℝ) ^ (-c * (n : ℝ))))
        atTop (𝓝 (0 : ℝ)) := by
    simpa using
      tendsto_const_nhds.mul (tendsto_linear_mul_rpow_three_neg_atTop_nhds_zero hc)
  have hsmall :
      ∀ᶠ n : ℕ in atTop,
        C * (((n : ℝ) + 1) * (3 : ℝ) ^ (-c * (n : ℝ))) ≤ η :=
    hlim (Iic_mem_nhds hη)
  rcases eventually_atTop.1 hsmall with ⟨K, hK⟩
  exact ⟨K, hK⟩

/--
Source label `l.union.bound`: the logarithmic buffer turns the polynomial
contrast factor `(2+T)^A` into half of the geometric decay.
-/
theorem buffered_polynomial_geometric_envelope_le_linear_geometric
    {C A c B T : ℝ} {n : ℕ}
    (hC : 0 ≤ C) (hc : 0 < c) (hT : 1 ≤ T)
    (hBlarge : 2 * A ≤ c * B)
    (hbuf : B * Real.logb 3 (2 + T) ≤ (n : ℝ)) :
    C * (((2 + T : ℝ) ^ A) *
        (((n : ℝ) + 1) * (3 : ℝ) ^ (-c * (n : ℝ)))) ≤
      C * (((n : ℝ) + 1) * (3 : ℝ) ^ (-(c / 2) * (n : ℝ))) := by
  let L : ℝ := Real.logb 3 (2 + T)
  have hbase_pos : 0 < 2 + T := by linarith
  have hL_nonneg : 0 ≤ L := by
    exact Real.logb_nonneg (by norm_num : (1 : ℝ) < 3) (by linarith : 1 ≤ 2 + T)
  have hL_ge_one : 1 ≤ L := by
    have hlog_mono :
        Real.logb 3 3 ≤ Real.logb 3 (2 + T) :=
      Real.logb_le_logb_of_le
        (by norm_num : (1 : ℝ) < 3)
        (by norm_num : (0 : ℝ) < 3)
        (by linarith : (3 : ℝ) ≤ 2 + T)
    rwa [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 3)] at hlog_mono
  have hdelta_nonneg : 0 ≤ c / 2 := by positivity
  have hA_le_deltaB : A ≤ (c / 2) * B := by nlinarith
  have hAL_le_delta_n : A * L ≤ (c / 2) * (n : ℝ) := by
    have hleft : A * L ≤ ((c / 2) * B) * L :=
      mul_le_mul_of_nonneg_right hA_le_deltaB hL_nonneg
    have hright : (c / 2) * (B * L) ≤ (c / 2) * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hbuf hdelta_nonneg
    nlinarith
  have hexp_le :
      A * L + (-c * (n : ℝ)) ≤ -(c / 2) * (n : ℝ) := by
    nlinarith
  have hpoly_decay :
      ((2 + T : ℝ) ^ A) * (3 : ℝ) ^ (-c * (n : ℝ)) ≤
        (3 : ℝ) ^ (-(c / 2) * (n : ℝ)) := by
    calc
      ((2 + T : ℝ) ^ A) * (3 : ℝ) ^ (-c * (n : ℝ))
          = (3 : ℝ) ^ (A * L) * (3 : ℝ) ^ (-c * (n : ℝ)) := by
            have hpow_eq :
                (2 + T : ℝ) ^ A = (3 : ℝ) ^ (A * L) := by
              calc
                (2 + T : ℝ) ^ A
                    = ((3 : ℝ) ^ L) ^ A := by
                      rw [Real.rpow_logb (by norm_num : (0 : ℝ) < 3)
                        (by norm_num : (3 : ℝ) ≠ 1) hbase_pos]
                _ = (3 : ℝ) ^ (L * A) := by
                      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
                _ = (3 : ℝ) ^ (A * L) := by ring_nf
            rw [hpow_eq]
      _ = (3 : ℝ) ^ (A * L + (-c * (n : ℝ))) := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      _ ≤ (3 : ℝ) ^ (-(c / 2) * (n : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le
              (by norm_num : (1 : ℝ) ≤ 3) hexp_le
  have hlin_nonneg : 0 ≤ (n : ℝ) + 1 := by positivity
  calc
    C * (((2 + T : ℝ) ^ A) *
        (((n : ℝ) + 1) * (3 : ℝ) ^ (-c * (n : ℝ))))
        = C * (((n : ℝ) + 1) *
            (((2 + T : ℝ) ^ A) * (3 : ℝ) ^ (-c * (n : ℝ)))) := by
          ring
    _ ≤ C * (((n : ℝ) + 1) * (3 : ℝ) ^ (-(c / 2) * (n : ℝ))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hpoly_decay hlin_nonneg) hC

/--
Source label `l.union.bound`: after choosing the buffer exponent large enough,
the manuscript envelope `C (2+T)^A (n+1) 3^{-c n}` is uniformly small for
`n >= B log_3(2+T)` and `T >= 1`.
-/
theorem exists_bufferExponent_for_polynomial_geometric_envelope_le
    {C A c η : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hη : 0 < η) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ {T : ℝ} {n : ℕ}, 1 ≤ T →
      B * Real.logb 3 (2 + T) ≤ (n : ℝ) →
        C * (((2 + T : ℝ) ^ A) *
          (((n : ℝ) + 1) * (3 : ℝ) ^ (-c * (n : ℝ)))) ≤ η := by
  obtain ⟨K, hK⟩ :=
    exists_forall_ge_const_mul_linear_rpow_three_neg_le
      (C := C) (c := c / 2) (η := η) (by positivity) hη
  let B : ℝ := max ((K : ℝ) + 1) (max 1 ((2 * A) / c))
  have hB_ge_one : 1 ≤ B := by
    exact le_trans (le_max_left 1 ((2 * A) / c)) (le_max_right ((K : ℝ) + 1) _)
  refine ⟨B, hB_ge_one, ?_⟩
  intro T n hT hbuf
  have hL_ge_one : 1 ≤ Real.logb 3 (2 + T) := by
    have hlog_mono :
        Real.logb 3 3 ≤ Real.logb 3 (2 + T) :=
      Real.logb_le_logb_of_le
        (by norm_num : (1 : ℝ) < 3)
        (by norm_num : (0 : ℝ) < 3)
        (by linarith : (3 : ℝ) ≤ 2 + T)
    rwa [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 3)] at hlog_mono
  have hB_nonneg : 0 ≤ B := le_trans zero_le_one hB_ge_one
  have hB_le_n : B ≤ (n : ℝ) := by
    calc
      B ≤ B * Real.logb 3 (2 + T) :=
        le_mul_of_one_le_right hB_nonneg hL_ge_one
      _ ≤ (n : ℝ) := hbuf
  have hK_le_n_real : (K : ℝ) ≤ (n : ℝ) := by
    have hK_lt_B : (K : ℝ) < B := by
      calc
        (K : ℝ) < (K : ℝ) + 1 := by linarith
        _ ≤ B := le_max_left ((K : ℝ) + 1) (max 1 ((2 * A) / c))
    exact le_of_lt (lt_of_lt_of_le hK_lt_B hB_le_n)
  have hK_le_n : K ≤ n := by exact_mod_cast hK_le_n_real
  have hBlarge : 2 * A ≤ c * B := by
    have hdiv_le_B : (2 * A) / c ≤ B :=
      (le_max_right 1 ((2 * A) / c)).trans
        (le_max_right ((K : ℝ) + 1) (max 1 ((2 * A) / c)))
    have hc_nonneg : 0 ≤ c := le_of_lt hc
    have hmul := mul_le_mul_of_nonneg_left hdiv_le_B hc_nonneg
    field_simp [hc.ne'] at hmul
    exact hmul
  calc
    C * (((2 + T : ℝ) ^ A) *
        (((n : ℝ) + 1) * (3 : ℝ) ^ (-c * (n : ℝ))))
        ≤ C * (((n : ℝ) + 1) * (3 : ℝ) ^ (-(c / 2) * (n : ℝ))) :=
          buffered_polynomial_geometric_envelope_le_linear_geometric
            hC hc hT hBlarge hbuf
    _ ≤ η := hK n hK_le_n

/--
Source label `l.union.bound`: variant of the logarithmic-buffer absorption
without the harmless linear prefactor.
-/
theorem exists_bufferExponent_for_polynomial_geometric_envelope_no_linear_le
    {C A c η : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hη : 0 < η) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ {T : ℝ} {n : ℕ}, 1 ≤ T →
      B * Real.logb 3 (2 + T) ≤ (n : ℝ) →
        C * (((2 + T : ℝ) ^ A) *
          (3 : ℝ) ^ (-c * (n : ℝ))) ≤ η := by
  obtain ⟨B, hB_one, hB⟩ :=
    exists_bufferExponent_for_polynomial_geometric_envelope_le
      (C := C) (A := A) (c := c) (η := η) hC hc hη
  refine ⟨B, hB_one, ?_⟩
  intro T n hT hbuf
  have hmain := hB hT hbuf
  have hpoly_nonneg : 0 ≤ (2 + T : ℝ) ^ A := by
    exact Real.rpow_nonneg (by linarith : 0 ≤ (2 + T : ℝ)) A
  have hdecay_nonneg : 0 ≤ (3 : ℝ) ^ (-c * (n : ℝ)) := by
    positivity
  have hlinear_ge_one : 1 ≤ (n : ℝ) + 1 := by
    have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    linarith
  have hdecay_le_linear :
      (3 : ℝ) ^ (-c * (n : ℝ)) ≤
        ((n : ℝ) + 1) * (3 : ℝ) ^ (-c * (n : ℝ)) := by
    calc
      (3 : ℝ) ^ (-c * (n : ℝ))
          = 1 * (3 : ℝ) ^ (-c * (n : ℝ)) := by rw [one_mul]
      _ ≤ ((n : ℝ) + 1) * (3 : ℝ) ^ (-c * (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hlinear_ge_one hdecay_nonneg
  have hleft_le :
      C * (((2 + T : ℝ) ^ A) *
          (3 : ℝ) ^ (-c * (n : ℝ))) ≤
        C * (((2 + T : ℝ) ^ A) *
          (((n : ℝ) + 1) * (3 : ℝ) ^ (-c * (n : ℝ)))) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hdecay_le_linear hpoly_nonneg) hC
  exact hleft_le.trans hmain

/--
Source labels `a.HM.subthreshold` and `l.union.bound`: the old polynomial
subthreshold bound is killed by the same logarithmic buffer, with squared
weak-norm decay `3^{-2 rho_M (m-N)}`.
-/
theorem exists_bufferExponent_subthresholdPolynomialMomentEnvelope_le
    {d : ℕ} (hc : HighContrastExponents d)
    (sub : SubthresholdPolynomialMomentParameters) {η : ℝ} (hη : 0 < η) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ {T : ℝ} {n : ℕ}, 1 ≤ T →
      B * Real.logb 3 (2 + T) ≤ (n : ℝ) →
        subthresholdPolynomialMomentEnvelope hc sub T n ≤ ENNReal.ofReal η := by
  obtain ⟨B, hB_one, hB⟩ :=
    exists_bufferExponent_for_polynomial_geometric_envelope_no_linear_le
      (C := sub.C_sub) (A := sub.A_sub) (c := 2 * hc.rhoM)
      (η := η) sub.C_sub_nonneg (by nlinarith [hc.rhoM_pos]) hη
  refine ⟨B, hB_one, ?_⟩
  intro T n hT hbuf
  exact ENNReal.ofReal_le_ofReal (hB hT hbuf)

/--
Source labels `e.Nstar`, `a.HM.subthreshold`, and `l.union.bound`: manuscript
form of the subthreshold polynomial-envelope absorption with
`m >= N + ceil(B log_3(2+T))`.
-/
theorem exists_bufferExponent_subthresholdPolynomialMomentEnvelope_le_of_Nstar
    {d : ℕ} (hc : HighContrastExponents d)
    (sub : SubthresholdPolynomialMomentParameters) {η : ℝ} (hη : 0 < η) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ {T : ℝ} {N m : ℕ}, 1 ≤ T →
      N + Nat.ceil (B * Real.logb 3 (2 + T)) ≤ m →
        subthresholdPolynomialMomentEnvelope hc sub T (m - N) ≤
          ENNReal.ofReal η := by
  obtain ⟨B, hB_one, hB⟩ :=
    exists_bufferExponent_subthresholdPolynomialMomentEnvelope_le hc sub hη
  refine ⟨B, hB_one, ?_⟩
  intro T N m hT hNstar
  have hceil_gap :
      Nat.ceil (B * Real.logb 3 (2 + T)) ≤ m - N := by
    omega
  have hbuf :
      B * Real.logb 3 (2 + T) ≤ ((m - N : ℕ) : ℝ) :=
    (Nat.ceil_le).mp hceil_gap
  exact hB hT hbuf

/--
Source labels `M_m^{<N}`, `a.HM.subthreshold`, and `l.union.bound`: once the
source-facing old polynomial subthreshold estimate is available, the
logarithmic buffer makes its second moment smaller than `η`.
-/
theorem exists_bufferExponent_lintegral_enorm_rpow_two_subthresholdMax_le_of_Nstar
    {d : ℕ} (hc : HighContrastExponents d)
    (sub : SubthresholdPolynomialMomentParameters) {η : ℝ} (hη : 0 < η) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω]
        (μ : MeasureTheory.Measure Ω) {T : ℝ} {N m : ℕ}, 1 ≤ T →
          N + Nat.ceil (B * Real.logb 3 (2 + T)) ≤ m →
            ∀ {M_sub : ℕ → Ω → ℝ},
              SubthresholdPolynomialMomentEstimate hc sub μ T N M_sub →
                ∫⁻ ω, ‖M_sub m ω‖ₑ ^ (2 : ℝ) ∂ μ ≤ ENNReal.ofReal η := by
  obtain ⟨B, hB_one, hB⟩ :=
    exists_bufferExponent_subthresholdPolynomialMomentEnvelope_le_of_Nstar
      hc sub hη
  refine ⟨B, hB_one, ?_⟩
  intro Ω _ μ T N m hT hNstar M_sub hsub
  have hNm : N ≤ m := by omega
  exact (hsub.moment_le hNm).trans (hB hT hNstar)

/--
Source label `e.Nstar`: increasing the buffer exponent preserves the
manuscript lower bound `m >= N + ceil(B log_3(2+T))`.
-/
theorem nstar_le_of_bufferExponent_le {B₀ B T : ℝ} {N m : ℕ}
    (hB₀B : B₀ ≤ B) (hT : 1 ≤ T)
    (hNstar : N + Nat.ceil (B * Real.logb 3 (2 + T)) ≤ m) :
    N + Nat.ceil (B₀ * Real.logb 3 (2 + T)) ≤ m := by
  let L : ℝ := Real.logb 3 (2 + T)
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact Real.logb_nonneg (by norm_num : (1 : ℝ) < 3) (by linarith : 1 ≤ 2 + T)
  have hmul : B₀ * L ≤ B * L :=
    mul_le_mul_of_nonneg_right hB₀B hL_nonneg
  have hceil : Nat.ceil (B₀ * L) ≤ Nat.ceil (B * L) :=
    Nat.ceil_mono hmul
  have hNstarL : N + Nat.ceil (B * L) ≤ m := by
    simpa [L] using hNstar
  have htarget : N + Nat.ceil (B₀ * L) ≤ m := by
    omega
  simpa [L] using htarget

/--
Source label `l.union.bound`: the terminal high-moment tolerance can be chosen
so that the `2 / Q` moment conversion lands exactly on half of the final
second-moment budget.
-/
theorem ofReal_highCenteredMoment_halfBudget_rpow_eq
    {d : ℕ} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc) {η : ℝ} (hη : 0 < η) :
    (ENNReal.ofReal ((η / 2) ^ (hm.Q / 2))) ^ ((2 : ℝ) / hm.Q) =
      ENNReal.ofReal (η / 2) := by
  have hQ_pos : 0 < hm.Q := highCenteredMoment_Q_pos hm
  have hhalf_nonneg : 0 ≤ η / 2 := by linarith
  have hQhalf_nonneg : 0 ≤ hm.Q / 2 := by linarith
  have hbase :
      ENNReal.ofReal ((η / 2) ^ (hm.Q / 2)) =
        (ENNReal.ofReal (η / 2)) ^ (hm.Q / 2) :=
    (ENNReal.ofReal_rpow_of_nonneg hhalf_nonneg hQhalf_nonneg).symm
  have hprod : hm.Q / 2 * ((2 : ℝ) / hm.Q) = 1 := by
    field_simp [(ne_of_gt hQ_pos)]
  calc
    (ENNReal.ofReal ((η / 2) ^ (hm.Q / 2))) ^ ((2 : ℝ) / hm.Q)
        = ((ENNReal.ofReal (η / 2)) ^ (hm.Q / 2)) ^ ((2 : ℝ) / hm.Q) := by
          rw [hbase]
    _ = (ENNReal.ofReal (η / 2)) ^ (hm.Q / 2 * ((2 : ℝ) / hm.Q)) := by
          rw [← ENNReal.rpow_mul]
    _ = ENNReal.ofReal (η / 2) := by
          rw [hprod, ENNReal.rpow_one]

/--
Source label `l.union.bound`: high-moment specialization of the buffer
smallness statement for the convolution envelope
`C_Q (2+T)^Q (n+1) 3^{-c_Q n}`.
-/
theorem exists_bufferExponent_highCenteredMoment_convolutionEnvelope_le
    {d : ℕ} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc) {η : ℝ} (hη : 0 < η) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ {T : ℝ} {n : ℕ}, 1 ≤ T →
      B * Real.logb 3 (2 + T) ≤ (n : ℝ) →
        hm.C_Q * (((2 + T : ℝ) ^ hm.Q) *
          (((n : ℝ) + 1) *
            (3 : ℝ) ^
              (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                (n : ℝ)))) ≤ η := by
  exact
    exists_bufferExponent_for_polynomial_geometric_envelope_le
      (C := hm.C_Q) (A := hm.Q)
      (c := min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma))
      hm.C_Q_nonneg (highCenteredMoment_min_decay_pos hm) hη

/--
Source label `l.union.bound`: a single term in the two-scale convolution is
controlled by the minimum decay exponent.  Here `α` represents
`Q ρ_M - d`, `β` represents `Q γ`, and `c` will be their minimum.
-/
theorem rpow_three_two_scale_decay_le_min_decay
    {α β c : ℝ} {N j m : ℕ}
    (hNj : N ≤ j) (hjm : j ≤ m)
    (hcα : c ≤ α) (hcβ : c ≤ β) :
    (3 : ℝ) ^ (-α * ((m - j : ℕ) : ℝ)) *
        (3 : ℝ) ^ (-β * ((j - N : ℕ) : ℝ)) ≤
      (3 : ℝ) ^ (-c * ((m - N : ℕ) : ℝ)) := by
  let leftGap : ℝ := ((m - j : ℕ) : ℝ)
  let rightGap : ℝ := ((j - N : ℕ) : ℝ)
  change
    (3 : ℝ) ^ (-α * leftGap) * (3 : ℝ) ^ (-β * rightGap) ≤
      (3 : ℝ) ^ (-c * ((m - N : ℕ) : ℝ))
  have h3_pos : 0 < (3 : ℝ) := by norm_num
  have h3_one : (1 : ℝ) ≤ 3 := by norm_num
  have hleft_nonneg : 0 ≤ leftGap := by positivity
  have hright_nonneg : 0 ≤ rightGap := by positivity
  have hgap :
      ((m - N : ℕ) : ℝ) = leftGap + rightGap := by
    have hnat : m - N = (m - j) + (j - N) := by omega
    simpa [leftGap, rightGap, Nat.cast_add] using
      congrArg (fun n : ℕ => (n : ℝ)) hnat
  have hexp :
      -α * leftGap + -β * rightGap ≤
        -c * ((m - N : ℕ) : ℝ) := by
    have hα : c * leftGap ≤ α * leftGap :=
      mul_le_mul_of_nonneg_right hcα hleft_nonneg
    have hβ : c * rightGap ≤ β * rightGap :=
      mul_le_mul_of_nonneg_right hcβ hright_nonneg
    rw [hgap]
    nlinarith
  calc
    (3 : ℝ) ^ (-α * leftGap) * (3 : ℝ) ^ (-β * rightGap)
        = (3 : ℝ) ^ (-α * leftGap + -β * rightGap) := by
          rw [← Real.rpow_add h3_pos]
    _ ≤ (3 : ℝ) ^ (-c * ((m - N : ℕ) : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le h3_one hexp

/--
Source label `l.union.bound`: finite convolution bound for the two decay
mechanisms before substituting the high-moment exponents.
-/
theorem sum_Icc_rpow_three_two_scale_decay_le_card_mul_min_decay
    {α β c : ℝ} {N m : ℕ}
    (hcα : c ≤ α) (hcβ : c ≤ β) :
    (∑ j ∈ Finset.Icc N m,
      (3 : ℝ) ^ (-α * ((m - j : ℕ) : ℝ)) *
        (3 : ℝ) ^ (-β * ((j - N : ℕ) : ℝ))) ≤
      ((Finset.Icc N m).card : ℝ) *
        (3 : ℝ) ^ (-c * ((m - N : ℕ) : ℝ)) := by
  let envelope : ℝ := (3 : ℝ) ^ (-c * ((m - N : ℕ) : ℝ))
  calc
    (∑ j ∈ Finset.Icc N m,
      (3 : ℝ) ^ (-α * ((m - j : ℕ) : ℝ)) *
        (3 : ℝ) ^ (-β * ((j - N : ℕ) : ℝ))) ≤
        ∑ _j ∈ Finset.Icc N m, envelope := by
          refine Finset.sum_le_sum ?_
          intro j hj
          exact rpow_three_two_scale_decay_le_min_decay
            (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 hcα hcβ
    _ = ((Finset.Icc N m).card : ℝ) *
        (3 : ℝ) ^ (-c * ((m - N : ℕ) : ℝ)) := by
          rw [Finset.sum_const]
          simp [envelope, nsmul_eq_mul]

/--
Source label `l.union.bound`: finite convolution bound in the manuscript's
`(1 + m - N) 3^{-c_Q(m-N)}` form.
-/
theorem sum_Icc_rpow_three_two_scale_decay_le_length_mul_min_decay
    {α β c : ℝ} {N m : ℕ}
    (hNm : N ≤ m) (hcα : c ≤ α) (hcβ : c ≤ β) :
    (∑ j ∈ Finset.Icc N m,
      (3 : ℝ) ^ (-α * ((m - j : ℕ) : ℝ)) *
        (3 : ℝ) ^ (-β * ((j - N : ℕ) : ℝ))) ≤
      ((m - N + 1 : ℕ) : ℝ) *
        (3 : ℝ) ^ (-c * ((m - N : ℕ) : ℝ)) := by
  have hcard : (Finset.Icc N m).card = m - N + 1 := by
    rw [Nat.card_Icc]
    omega
  calc
    (∑ j ∈ Finset.Icc N m,
      (3 : ℝ) ^ (-α * ((m - j : ℕ) : ℝ)) *
        (3 : ℝ) ^ (-β * ((j - N : ℕ) : ℝ))) ≤
        ((Finset.Icc N m).card : ℝ) *
          (3 : ℝ) ^ (-c * ((m - N : ℕ) : ℝ)) :=
          sum_Icc_rpow_three_two_scale_decay_le_card_mul_min_decay hcα hcβ
    _ = ((m - N + 1 : ℕ) : ℝ) *
        (3 : ℝ) ^ (-c * ((m - N : ℕ) : ℝ)) := by
          rw [hcard]

/--
Source labels `l.union.bound`, `a.HM`: high-moment specialization of the
two-scale convolution estimate appearing in the stochastic maximal union bound.
-/
theorem sum_Icc_rpow_three_highCenteredMoment_convolution_le
    {d : ℕ} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc) {N m : ℕ} (hNm : N ≤ m) :
    (∑ j ∈ Finset.Icc N m,
      (3 : ℝ) ^
          (-(hm.Q * hc.rhoM - (d : ℝ)) * ((m - j : ℕ) : ℝ)) *
        (3 : ℝ) ^ (-(hm.Q * hm.gamma) * ((j - N : ℕ) : ℝ))) ≤
      ((m - N + 1 : ℕ) : ℝ) *
        (3 : ℝ) ^
          (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
            ((m - N : ℕ) : ℝ)) :=
  sum_Icc_rpow_three_two_scale_decay_le_length_mul_min_decay
    (α := hm.Q * hc.rhoM - (d : ℝ)) (β := hm.Q * hm.gamma)
    (c := min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma))
    hNm
    (min_le_left (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma))
    (min_le_right (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma))

/--
Source label `l.union.bound`: the deterministic `Q`-moment envelope for the
product of the terminal-normalization cost and the weak-norm scale weight
`3^{-rho_M(m-j)}`.
-/
noncomputable def terminalWeakMomentWeight {d : ℕ} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc) (terminalCost : ENNReal)
    (m j : ℕ) : ENNReal :=
  terminalCost ^ hm.Q *
    ENNReal.ofReal
      ((3 : ℝ) ^ (-(hm.Q * hc.rhoM) * ((m - j : ℕ) : ℝ)))

/--
Source label `l.union.bound`: if the deterministic multiplier is bounded by
`terminalCost * 3^{-rho_M(m-j)}`, then its `Q`-moment is bounded by the
factorized terminal weak-moment envelope used in the descendant sum.
-/
theorem rpow_le_terminalWeakMomentWeight_of_le
    {d : ℕ} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc) {terminalCost : ENNReal} {m j : ℕ}
    {w : Homogenization.TriadicCube d → ENNReal}
    {R : Homogenization.TriadicCube d}
    (hw :
      w R ≤ terminalCost *
        ENNReal.ofReal ((3 : ℝ) ^ (-hc.rhoM * ((m - j : ℕ) : ℝ)))) :
    w R ^ hm.Q ≤ terminalWeakMomentWeight hm terminalCost m j := by
  have hq_nonneg : 0 ≤ hm.Q := le_of_lt (highCenteredMoment_Q_pos hm)
  have h3_nonneg : 0 ≤ (3 : ℝ) := by norm_num
  have hweak_nonneg :
      0 ≤ (3 : ℝ) ^ (-hc.rhoM * ((m - j : ℕ) : ℝ)) := by
    positivity
  have hweak_rpow :
      (ENNReal.ofReal ((3 : ℝ) ^ (-hc.rhoM * ((m - j : ℕ) : ℝ)))) ^ hm.Q =
        ENNReal.ofReal
          ((3 : ℝ) ^ (-(hm.Q * hc.rhoM) * ((m - j : ℕ) : ℝ))) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hweak_nonneg hq_nonneg]
    congr 1
    calc
      ((3 : ℝ) ^ (-hc.rhoM * ((m - j : ℕ) : ℝ))) ^ hm.Q
          = (3 : ℝ) ^
              ((-hc.rhoM * ((m - j : ℕ) : ℝ)) * hm.Q) := by
            rw [← Real.rpow_mul h3_nonneg]
      _ = (3 : ℝ) ^ (-(hm.Q * hc.rhoM) * ((m - j : ℕ) : ℝ)) := by
            ring_nf
  calc
    w R ^ hm.Q
        ≤ (terminalCost *
            ENNReal.ofReal ((3 : ℝ) ^ (-hc.rhoM * ((m - j : ℕ) : ℝ)))) ^
            hm.Q :=
          ENNReal.rpow_le_rpow hw hq_nonneg
    _ = terminalCost ^ hm.Q *
        (ENNReal.ofReal ((3 : ℝ) ^ (-hc.rhoM * ((m - j : ℕ) : ℝ)))) ^ hm.Q := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hq_nonneg]
    _ = terminalWeakMomentWeight hm terminalCost m j := by
          rw [hweak_rpow]
          rfl

/--
Source label `l.union.bound`: real algebra turning descendant counting and
the two decay weights into the manuscript's convolution summand.
-/
theorem real_descendant_count_mul_highCenteredMoment_decay_eq
    {d : ℕ} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc) {N m j : ℕ} :
    (((((3 ^ d) ^ (m - j) : ℕ) : ℝ) *
        (3 : ℝ) ^ (-(hm.Q * hc.rhoM) * ((m - j : ℕ) : ℝ))) *
      (hm.C_Q * (3 : ℝ) ^ (-(hm.Q * hm.gamma) * ((j - N : ℕ) : ℝ)))) =
      hm.C_Q *
        ((3 : ℝ) ^
            (-(hm.Q * hc.rhoM - (d : ℝ)) * ((m - j : ℕ) : ℝ)) *
          (3 : ℝ) ^ (-(hm.Q * hm.gamma) * ((j - N : ℕ) : ℝ))) := by
  let leftGap : ℝ := ((m - j : ℕ) : ℝ)
  let rightGap : ℝ := ((j - N : ℕ) : ℝ)
  have h3_pos : 0 < (3 : ℝ) := by norm_num
  have hcount :
      (((3 ^ d) ^ (m - j) : ℕ) : ℝ) =
        (3 : ℝ) ^ ((d : ℝ) * leftGap) := by
    rw [Nat.cast_pow, Nat.cast_pow]
    norm_num only [Nat.cast_ofNat]
    rw [← pow_mul, ← Real.rpow_natCast]
    congr 1
    simp [leftGap, Nat.cast_mul]
  change
    (((((3 ^ d) ^ (m - j) : ℕ) : ℝ) *
        (3 : ℝ) ^ (-(hm.Q * hc.rhoM) * leftGap)) *
      (hm.C_Q * (3 : ℝ) ^ (-(hm.Q * hm.gamma) * rightGap))) =
      hm.C_Q *
        ((3 : ℝ) ^ (-(hm.Q * hc.rhoM - (d : ℝ)) * leftGap) *
          (3 : ℝ) ^ (-(hm.Q * hm.gamma) * rightGap))
  calc
    (((((3 ^ d) ^ (m - j) : ℕ) : ℝ) *
        (3 : ℝ) ^ (-(hm.Q * hc.rhoM) * leftGap)) *
      (hm.C_Q * (3 : ℝ) ^ (-(hm.Q * hm.gamma) * rightGap)))
        =
      (((3 : ℝ) ^ ((d : ℝ) * leftGap) *
        (3 : ℝ) ^ (-(hm.Q * hc.rhoM) * leftGap)) *
      (hm.C_Q * (3 : ℝ) ^ (-(hm.Q * hm.gamma) * rightGap))) := by
        rw [hcount]
    _ =
      ((3 : ℝ) ^ (((d : ℝ) * leftGap) + (-(hm.Q * hc.rhoM) * leftGap)) *
      (hm.C_Q * (3 : ℝ) ^ (-(hm.Q * hm.gamma) * rightGap))) := by
        rw [← Real.rpow_add h3_pos]
    _ =
      ((3 : ℝ) ^ (-(hm.Q * hc.rhoM - (d : ℝ)) * leftGap) *
      (hm.C_Q * (3 : ℝ) ^ (-(hm.Q * hm.gamma) * rightGap))) := by
        congr 2
        ring
    _ =
      hm.C_Q *
        ((3 : ℝ) ^ (-(hm.Q * hc.rhoM - (d : ℝ)) * leftGap) *
          (3 : ℝ) ^ (-(hm.Q * hm.gamma) * rightGap)) := by
        ring

/--
Source label `l.union.bound`: the explicit `ENNReal` summand produced by
the terminal/weak bridge and `a.HM` is exactly the `C_Q` multiple of the real
two-scale convolution summand, times the terminal normalization cost.
-/
theorem terminalWeak_highCenteredMoment_summand_eq_convolution
    {d : ℕ} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc) (terminalCost : ENNReal)
    {N m j : ℕ} :
    (((3 ^ d) ^ (m - j) : ℕ) : ENNReal) *
        (terminalWeakMomentWeight hm terminalCost m j *
          highCenteredMomentEnvelope hm N j) =
      terminalCost ^ hm.Q *
        ENNReal.ofReal
          (hm.C_Q *
            ((3 : ℝ) ^
                (-(hm.Q * hc.rhoM - (d : ℝ)) * ((m - j : ℕ) : ℝ)) *
              (3 : ℝ) ^ (-(hm.Q * hm.gamma) * ((j - N : ℕ) : ℝ)))) := by
  let count : ℝ := (((3 ^ d) ^ (m - j) : ℕ) : ℝ)
  let weakDecay : ℝ :=
    (3 : ℝ) ^ (-(hm.Q * hc.rhoM) * ((m - j : ℕ) : ℝ))
  let momentDecay : ℝ :=
    (3 : ℝ) ^ (-(hm.Q * hm.gamma) * ((j - N : ℕ) : ℝ))
  have hcount_nonneg : 0 ≤ count := by
    dsimp [count]
    positivity
  have hweak_nonneg : 0 ≤ weakDecay := by
    dsimp [weakDecay]
    positivity
  have hmoment_nonneg : 0 ≤ hm.C_Q * momentDecay := by
    dsimp [momentDecay]
    exact mul_nonneg hm.C_Q_nonneg (by positivity)
  have hcount_coe :
      (((3 ^ d) ^ (m - j) : ℕ) : ENNReal) = ENNReal.ofReal count := by
    simp [count]
  have hreal :=
    real_descendant_count_mul_highCenteredMoment_decay_eq
      (d := d) (hc := hc) hm (N := N) (m := m) (j := j)
  calc
    (((3 ^ d) ^ (m - j) : ℕ) : ENNReal) *
        (terminalWeakMomentWeight hm terminalCost m j *
          highCenteredMomentEnvelope hm N j)
        =
      terminalCost ^ hm.Q *
        ((ENNReal.ofReal count * ENNReal.ofReal weakDecay) *
          ENNReal.ofReal (hm.C_Q * momentDecay)) := by
        rw [terminalWeakMomentWeight, highCenteredMomentEnvelope, hcount_coe]
        dsimp [weakDecay, momentDecay]
        ac_rfl
    _ =
      terminalCost ^ hm.Q *
        ENNReal.ofReal ((count * weakDecay) * (hm.C_Q * momentDecay)) := by
        rw [← ENNReal.ofReal_mul hcount_nonneg]
        rw [← ENNReal.ofReal_mul (mul_nonneg hcount_nonneg hweak_nonneg)]
    _ =
      terminalCost ^ hm.Q *
        ENNReal.ofReal
          (hm.C_Q *
            ((3 : ℝ) ^
                (-(hm.Q * hc.rhoM - (d : ℝ)) * ((m - j : ℕ) : ℝ)) *
              (3 : ℝ) ^ (-(hm.Q * hm.gamma) * ((j - N : ℕ) : ℝ)))) := by
        rw [hreal]

/--
Source label `l.union.bound`: after substituting `a.HM`, terminal normalization,
weak weights, and the library's descendant counting, the finite `ENNReal` sum is bounded
by the real convolution envelope from the paper.
-/
theorem sum_Icc_terminalWeak_highCenteredMomentEnvelope_le_convolution
    {d : ℕ} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc) (terminalCost : ENNReal)
    {N m : ℕ} (hNm : N ≤ m) :
    (∑ j ∈ Finset.Icc N m,
      (((3 ^ d) ^ (m - j) : ℕ) : ENNReal) *
        (terminalWeakMomentWeight hm terminalCost m j *
          highCenteredMomentEnvelope hm N j)) ≤
      terminalCost ^ hm.Q *
        ENNReal.ofReal
          (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
            (3 : ℝ) ^
              (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                ((m - N : ℕ) : ℝ)))) := by
  let convTerm : ℕ → ℝ := fun j =>
    (3 : ℝ) ^
        (-(hm.Q * hc.rhoM - (d : ℝ)) * ((m - j : ℕ) : ℝ)) *
      (3 : ℝ) ^ (-(hm.Q * hm.gamma) * ((j - N : ℕ) : ℝ))
  have hterm_nonneg :
      ∀ j, j ∈ Finset.Icc N m → 0 ≤ hm.C_Q * convTerm j := by
    intro j _hj
    dsimp [convTerm]
    exact mul_nonneg hm.C_Q_nonneg (mul_nonneg (by positivity) (by positivity))
  have hconv :=
    sum_Icc_rpow_three_highCenteredMoment_convolution_le hm hNm
  have hscaled :
      hm.C_Q * (∑ j ∈ Finset.Icc N m, convTerm j) ≤
        hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
          (3 : ℝ) ^
            (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
              ((m - N : ℕ) : ℝ))) := by
    exact mul_le_mul_of_nonneg_left hconv hm.C_Q_nonneg
  calc
    (∑ j ∈ Finset.Icc N m,
      (((3 ^ d) ^ (m - j) : ℕ) : ENNReal) *
        (terminalWeakMomentWeight hm terminalCost m j *
          highCenteredMomentEnvelope hm N j))
        =
      ∑ j ∈ Finset.Icc N m,
        terminalCost ^ hm.Q * ENNReal.ofReal (hm.C_Q * convTerm j) := by
        refine Finset.sum_congr rfl ?_
        intro j _hj
        exact terminalWeak_highCenteredMoment_summand_eq_convolution
          (d := d) (hc := hc) hm terminalCost (N := N) (m := m) (j := j)
    _ =
      terminalCost ^ hm.Q *
        (∑ j ∈ Finset.Icc N m, ENNReal.ofReal (hm.C_Q * convTerm j)) := by
        rw [Finset.mul_sum]
    _ =
      terminalCost ^ hm.Q *
        ENNReal.ofReal (∑ j ∈ Finset.Icc N m, hm.C_Q * convTerm j) := by
        rw [ENNReal.ofReal_sum_of_nonneg hterm_nonneg]
    _ =
      terminalCost ^ hm.Q *
        ENNReal.ofReal (hm.C_Q * (∑ j ∈ Finset.Icc N m, convTerm j)) := by
        rw [Finset.mul_sum]
    _ ≤
      terminalCost ^ hm.Q *
        ENNReal.ofReal
          (hm.C_Q * (((m - N + 1 : ℕ) : ℝ) *
            (3 : ℝ) ^
              (-(min (hm.Q * hc.rhoM - (d : ℝ)) (hm.Q * hm.gamma)) *
                ((m - N : ℕ) : ℝ)))) := by
        exact mul_le_mul_right (ENNReal.ofReal_le_ofReal hscaled)
          (terminalCost ^ hm.Q)

/--
Source label `l.union.bound`: once the terminal-normalization multiplier is
bounded by `(2+T)^A`, its `Q`-moment contribution is bounded by
`(2+T)^{A Q}`.
-/
theorem terminalCost_rpow_le_polynomial_of_le
    {d : ℕ} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    {terminalCost : ENNReal} {T A : ℝ}
    (hT : 1 ≤ T)
    (hcost : terminalCost ≤ ENNReal.ofReal ((2 + T : ℝ) ^ A)) :
    terminalCost ^ hm.Q ≤ ENNReal.ofReal ((2 + T : ℝ) ^ (A * hm.Q)) := by
  have hq_nonneg : 0 ≤ hm.Q := le_of_lt (highCenteredMoment_Q_pos hm)
  have hbase_nonneg : 0 ≤ (2 + T : ℝ) := by linarith
  have hpoly_nonneg : 0 ≤ (2 + T : ℝ) ^ A :=
    Real.rpow_nonneg hbase_nonneg A
  calc
    terminalCost ^ hm.Q
        ≤ (ENNReal.ofReal ((2 + T : ℝ) ^ A)) ^ hm.Q :=
          ENNReal.rpow_le_rpow hcost hq_nonneg
    _ = ENNReal.ofReal (((2 + T : ℝ) ^ A) ^ hm.Q) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hpoly_nonneg hq_nonneg]
    _ = ENNReal.ofReal ((2 + T : ℝ) ^ (A * hm.Q)) := by
          rw [← Real.rpow_mul hbase_nonneg]

/--
Source label `l.S.and.J`: Lyapunov monotonicity from the high `Q` moment to
the second moment on a probability space.
-/
theorem eLpNorm_two_le_eLpNorm_of_two_le_real_exponent
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ] {X : Ω → ℝ} {Q : ℝ}
    (hQ : (2 : ℝ) ≤ Q)
    (hX : MeasureTheory.AEStronglyMeasurable X μ) :
    MeasureTheory.eLpNorm X (2 : ENNReal) μ ≤
      MeasureTheory.eLpNorm X (ENNReal.ofReal Q) μ := by
  have hQenn : (2 : ENNReal) ≤ ENNReal.ofReal Q := by
    calc
      (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by norm_num
      _ ≤ ENNReal.ofReal Q := ENNReal.ofReal_le_ofReal hQ
  exact MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le hQenn hX

/--
Source label `l.union.bound`: the manuscript step "Taking the power `2 / Q`"
from a `Q`-moment estimate to a second-moment estimate.
-/
theorem lintegral_enorm_rpow_two_le_lintegral_enorm_rpow_rpow_of_two_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ] {X : Ω → ℝ} {Q : ℝ} {B : ENNReal}
    (hQ : (2 : ℝ) ≤ Q)
    (hX : MeasureTheory.AEStronglyMeasurable X μ)
    (hB : ∫⁻ ω, ‖X ω‖ₑ ^ Q ∂ μ ≤ B) :
    ∫⁻ ω, ‖X ω‖ₑ ^ (2 : ℝ) ∂ μ ≤ B ^ ((2 : ℝ) / Q) := by
  have hQ_pos : 0 < Q := by linarith
  have hQ_nonneg : 0 ≤ Q := le_of_lt hQ_pos
  have hQ_ne_zero : Q ≠ 0 := ne_of_gt hQ_pos
  have hQenn_ne_zero : ENNReal.ofReal Q ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le_of_gt hQ_pos]
  have hQenn_ne_top : ENNReal.ofReal Q ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have htwo_ne_zero : (2 : ENNReal) ≠ 0 := by norm_num
  have htwo_ne_top : (2 : ENNReal) ≠ ⊤ := by norm_num
  have hnorm :
      (∫⁻ ω, ‖X ω‖ₑ ^ (2 : ℝ) ∂ μ) ^ (1 / (2 : ℝ)) ≤
        (∫⁻ ω, ‖X ω‖ₑ ^ Q ∂ μ) ^ (1 / Q) := by
    have hmono :=
      eLpNorm_two_le_eLpNorm_of_two_le_real_exponent
        (μ := μ) (X := X) hQ hX
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
        (p := (2 : ENNReal)) htwo_ne_zero htwo_ne_top,
      MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
        (p := ENNReal.ofReal Q) hQenn_ne_zero hQenn_ne_top] at hmono
    simpa [ENNReal.toReal_ofReal hQ_nonneg] using hmono
  have hpow := ENNReal.rpow_le_rpow hnorm (by norm_num : 0 ≤ (2 : ℝ))
  have hleft :
      ((∫⁻ ω, ‖X ω‖ₑ ^ (2 : ℝ) ∂ μ) ^ (1 / (2 : ℝ))) ^ (2 : ℝ) =
        ∫⁻ ω, ‖X ω‖ₑ ^ (2 : ℝ) ∂ μ := by
    rw [← ENNReal.rpow_mul]
    norm_num
  have hright :
      ((∫⁻ ω, ‖X ω‖ₑ ^ Q ∂ μ) ^ (1 / Q)) ^ (2 : ℝ) =
        (∫⁻ ω, ‖X ω‖ₑ ^ Q ∂ μ) ^ ((2 : ℝ) / Q) := by
    rw [← ENNReal.rpow_mul]
    congr 1
    field_simp [hQ_ne_zero]
  have hmoment :
      ∫⁻ ω, ‖X ω‖ₑ ^ (2 : ℝ) ∂ μ ≤
        (∫⁻ ω, ‖X ω‖ₑ ^ Q ∂ μ) ^ ((2 : ℝ) / Q) := by
    calc
      ∫⁻ ω, ‖X ω‖ₑ ^ (2 : ℝ) ∂ μ
          = ((∫⁻ ω, ‖X ω‖ₑ ^ (2 : ℝ) ∂ μ) ^
              (1 / (2 : ℝ))) ^ (2 : ℝ) := hleft.symm
      _ ≤ ((∫⁻ ω, ‖X ω‖ₑ ^ Q ∂ μ) ^ (1 / Q)) ^ (2 : ℝ) := hpow
      _ = (∫⁻ ω, ‖X ω‖ₑ ^ Q ∂ μ) ^ ((2 : ℝ) / Q) := hright
  exact hmoment.trans <|
    ENNReal.rpow_le_rpow hB (div_nonneg (by norm_num) hQ_nonneg)

/--
Source labels `a.HM`, `l.union.bound`: high-moment-parameter specialization
of the `2 / Q` power conversion for stochastic maximal variables.
-/
theorem lintegral_enorm_rpow_two_le_lintegral_enorm_rpow_rpow_highCenteredMoment
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ] {X : Ω → ℝ}
    {d : ℕ} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    (hX : MeasureTheory.AEStronglyMeasurable X μ) {B : ENNReal}
    (hB : ∫⁻ ω, ‖X ω‖ₑ ^ hm.Q ∂ μ ≤ B) :
    ∫⁻ ω, ‖X ω‖ₑ ^ (2 : ℝ) ∂ μ ≤ B ^ ((2 : ℝ) / hm.Q) :=
  lintegral_enorm_rpow_two_le_lintegral_enorm_rpow_rpow_of_two_le
    hm.two_le_Q hX hB

/--
Source label `M_m^st`: the coercion from an ENNReal finite maximum to the real
maximum is harmless for upper bounds by the original ENNReal quantity.
-/
theorem enorm_ennreal_toReal_le (x : ENNReal) : ‖x.toReal‖ₑ ≤ x := by
  rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_toReal_le

/--
Source labels `l.union.bound`, `M_m^st`: an ENNReal envelope controlling the
`Q`-th power of a real stochastic maximum also controls its second moment.
-/
theorem lintegral_enorm_rpow_two_le_of_lintegral_ennreal_envelope_highCenteredMoment
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ] {X : Ω → ℝ} {Z : Ω → ENNReal}
    {d : ℕ} {hc : HighContrastExponents d}
    (hm : HighCenteredMomentParameters d hc)
    (hX : MeasureTheory.AEStronglyMeasurable X μ) {B : ENNReal}
    (hpoint : ∀ ω, ‖X ω‖ₑ ^ hm.Q ≤ Z ω)
    (hB : ∫⁻ ω, Z ω ∂ μ ≤ B) :
    ∫⁻ ω, ‖X ω‖ₑ ^ (2 : ℝ) ∂ μ ≤ B ^ ((2 : ℝ) / hm.Q) := by
  have hQ :
      ∫⁻ ω, ‖X ω‖ₑ ^ hm.Q ∂ μ ≤ B :=
    (MeasureTheory.lintegral_mono hpoint).trans hB
  exact
    lintegral_enorm_rpow_two_le_lintegral_enorm_rpow_rpow_highCenteredMoment
      hm hX hQ

end Homogenization.HighContrast.EntryScale
