/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Order.Interval.Set.Union
import LeanPool.PhaseRetrieval.DimdPoly.Internal.ImportedAnalyticInputs
import LeanPool.PhaseRetrieval.Constant.Internal.HighFreqBandEstimate

/-! # FiniteBaseCircleEstimate -/


noncomputable section

namespace DimdPolyLEAN

/-!
# FiniteBaseCircleEstimate

Finite Fourier-side scaffold for the one-dimensional circle estimate with
explicit support and gap parameters.
-/

/-- `lowPoly`: low Poly. -/
noncomputable def lowPoly {D : Nat} (q : Fin (D + 1) -> ℂ) :
    AddCircle (2 * Real.pi) -> ℂ :=
  fun t => ∑ n : Fin (D + 1), q n * circleChar n.1 t

/-- `bandPoly`: band Poly. -/
noncomputable def bandPoly (N : Nat) {L : Nat} (p : Fin L -> ℂ) :
    AddCircle (2 * Real.pi) -> ℂ :=
  fun t => ∑ m : Fin L, p m * circleChar (N + m.1) t

private noncomputable def slowBandPoly {L : Nat} (p : Fin L -> ℂ) :
    AddCircle (2 * Real.pi) -> ℂ :=
  fun t => ∑ m : Fin L, p m * circleChar m.1 t

private theorem bandPoly_eq_fast_mul_slow
    (N : Nat) {L : Nat} (p : Fin L -> ℂ) (x : Circle) :
    bandPoly N p x = circleChar N x * slowBandPoly p x := by
  simp [bandPoly, slowBandPoly, circleChar_eq_zeta_pow, pow_add,
    Finset.mul_sum, mul_left_comm]

private theorem bandPoly_sub_fast_mul_slow_sub
    (N : Nat) {L : Nat} (p : Fin L -> ℂ) (u : ℂ) (x : Circle) :
    bandPoly N p x - circleChar N x * u =
      circleChar N x * (slowBandPoly p x - u) := by
  rw [bandPoly_eq_fast_mul_slow]
  ring_nf

private theorem norm_circleChar_wip (n : Nat) (x : Circle) :
    ‖circleChar n x‖ = 1 := by
  simp [circleChar, norm_zeta]

private theorem circleChar_mk_wip (n : Nat) (theta : ℝ) :
    circleChar n (QuotientAddGroup.mk theta : Circle) =
      Complex.exp (Complex.I * (n : ℂ) * theta) := by
  simp only [circleChar, zeta, AddCircle.toCircle, ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero,
    Real.pi_ne_zero, or_self, not_false_eq_true, div_self, one_mul, Function.Periodic.lift_coe,
    Circle.coe_exp]
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

private theorem norm_bandPoly_sub_fast_mul
    (N : Nat) {L : Nat} (p : Fin L -> ℂ) (u : ℂ) (x : Circle) :
    ‖bandPoly N p x - circleChar N x * u‖ =
      ‖slowBandPoly p x - u‖ := by
  rw [bandPoly_sub_fast_mul_slow_sub]
  simp [norm_circleChar_wip]

private theorem norm_pow_sub_pow_le_nat_mul_norm_sub
    {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    ∀ n : Nat, ‖z ^ n - w ^ n‖ <= (n : ℝ) * ‖z - w‖
  | 0 => by simp
  | n + 1 => by
      have hprev := norm_pow_sub_pow_le_nat_mul_norm_sub (z := z) (w := w) hz hw n
      have hdecomp : z ^ (n + 1) - w ^ (n + 1) =
          z ^ n * (z - w) + (z ^ n - w ^ n) * w := by
        ring
      calc
        ‖z ^ (n + 1) - w ^ (n + 1)‖
            = ‖z ^ n * (z - w) + (z ^ n - w ^ n) * w‖ := by
                rw [hdecomp]
        _ <= ‖z ^ n * (z - w)‖ + ‖(z ^ n - w ^ n) * w‖ :=
            norm_add_le _ _
        _ = ‖z - w‖ + ‖z ^ n - w ^ n‖ := by
            rw [norm_mul, norm_mul, norm_pow, hz, one_pow, one_mul, hw, mul_one]
        _ <= ‖z - w‖ + (n : ℝ) * ‖z - w‖ := by
            nlinarith
        _ = ((n + 1 : Nat) : ℝ) * ‖z - w‖ := by
            norm_num
            ring

private theorem norm_circleChar_sub_le
    (n : Nat) (x y : Circle) :
    ‖circleChar n x - circleChar n y‖ <=
      (n : ℝ) * ‖zeta x - zeta y‖ := by
  simpa [circleChar_eq_zeta_pow] using
    norm_pow_sub_pow_le_nat_mul_norm_sub
      (z := zeta x) (w := zeta y) (norm_zeta x) (norm_zeta y) n

private theorem norm_lowPoly_sub_le_chord {D : Nat}
    (q : Fin (D + 1) -> ℂ) (x y : Circle) :
    ‖lowPoly q x - lowPoly q y‖ <=
      (∑ n : Fin (D + 1), ‖q n‖ * (n.1 : ℝ)) * ‖zeta x - zeta y‖ := by
  have hsum :
      lowPoly q x - lowPoly q y =
        ∑ n : Fin (D + 1),
          q n * (circleChar n.1 x - circleChar n.1 y) := by
    simp [lowPoly, Finset.sum_sub_distrib, mul_sub]
  calc
    ‖lowPoly q x - lowPoly q y‖
        = ‖∑ n : Fin (D + 1),
            q n * (circleChar n.1 x - circleChar n.1 y)‖ := by
            rw [hsum]
    _ <= ∑ n : Fin (D + 1),
        ‖q n * (circleChar n.1 x - circleChar n.1 y)‖ :=
        norm_sum_le _ _
    _ <= ∑ n : Fin (D + 1),
        ‖q n‖ * ((n.1 : ℝ) * ‖zeta x - zeta y‖) := by
        refine Finset.sum_le_sum ?_
        intro n hn
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          (norm_circleChar_sub_le n.1 x y) (norm_nonneg (q n))
    _ = (∑ n : Fin (D + 1), ‖q n‖ * (n.1 : ℝ)) *
        ‖zeta x - zeta y‖ := by
        rw [Finset.sum_mul]
        congr
        ext n
        ring

private theorem lowPoly_slope_nonneg {D : Nat} (q : Fin (D + 1) -> ℂ) :
    0 <= ∑ n : Fin (D + 1), ‖q n‖ * (n.1 : ℝ) := by
  exact Finset.sum_nonneg fun n hn =>
    mul_nonneg (norm_nonneg (q n)) (by exact_mod_cast Nat.zero_le n.1)

private theorem norm_slowBandPoly_sub_le_chord {L : Nat}
    (p : Fin L -> ℂ) (x y : Circle) :
    ‖slowBandPoly p x - slowBandPoly p y‖ <=
      (∑ m : Fin L, ‖p m‖ * (m.1 : ℝ)) * ‖zeta x - zeta y‖ := by
  have hsum :
      slowBandPoly p x - slowBandPoly p y =
        ∑ m : Fin L,
          p m * (circleChar m.1 x - circleChar m.1 y) := by
    simp [slowBandPoly, Finset.sum_sub_distrib, mul_sub]
  calc
    ‖slowBandPoly p x - slowBandPoly p y‖
        = ‖∑ m : Fin L,
            p m * (circleChar m.1 x - circleChar m.1 y)‖ := by
            rw [hsum]
    _ <= ∑ m : Fin L,
        ‖p m * (circleChar m.1 x - circleChar m.1 y)‖ :=
        norm_sum_le _ _
    _ <= ∑ m : Fin L,
        ‖p m‖ * ((m.1 : ℝ) * ‖zeta x - zeta y‖) := by
        refine Finset.sum_le_sum ?_
        intro m hm
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          (norm_circleChar_sub_le m.1 x y) (norm_nonneg (p m))
    _ = (∑ m : Fin L, ‖p m‖ * (m.1 : ℝ)) *
        ‖zeta x - zeta y‖ := by
        rw [Finset.sum_mul]
        congr
        ext m
        ring

private theorem slowBandPoly_slope_nonneg {L : Nat} (p : Fin L -> ℂ) :
    0 <= ∑ m : Fin L, ‖p m‖ * (m.1 : ℝ) := by
  exact Finset.sum_nonneg fun m hm =>
    mul_nonneg (norm_nonneg (p m)) (by exact_mod_cast Nat.zero_le m.1)

private theorem bandPoly_eq_fourier_sum
    (N : Nat) {L : Nat} (p : Fin L -> ℂ) :
    bandPoly N p =
      fun t => ∑ m : Fin L, p m * fourier ((N + m.1 : Nat) : Int) t := by
  ext t
  simp [bandPoly, circleChar_eq_fourier_nat]

private theorem continuous_circleChar (n : Nat) : Continuous (circleChar n) := by
  unfold circleChar zeta
  continuity

private theorem continuous_slowBandPoly {L : Nat} (p : Fin L -> ℂ) :
    Continuous (slowBandPoly p) := by
  unfold slowBandPoly
  exact continuous_finsetSum _ fun m hm =>
    continuous_const.mul (continuous_circleChar m.1)

private noncomputable def slowBandPolyDerivCircle {L : Nat}
    (p : Fin L -> ℂ) : Circle -> ℂ :=
  fun x => ∑ m : Fin L,
    p m * ((2 * Real.pi * Complex.I * (m.1 : ℤ) /
      ((2 * Real.pi : ℝ) : ℂ)) *
        fourier (m.1 : ℤ) x)

private noncomputable def slowBandPolyDeriv {L : Nat} (p : Fin L -> ℂ) :
    ℝ -> ℂ :=
  fun t => slowBandPolyDerivCircle p (QuotientAddGroup.mk t : Circle)

private theorem continuous_slowBandPolyDerivCircle {L : Nat}
    (p : Fin L -> ℂ) :
    Continuous (slowBandPolyDerivCircle p) := by
  unfold slowBandPolyDerivCircle
  exact continuous_finsetSum _ fun m hm =>
    continuous_const.mul (continuous_const.mul (fourier (m.1 : ℤ)).continuous)

private theorem continuous_slowBandPolyDeriv {L : Nat} (p : Fin L -> ℂ) :
    Continuous (slowBandPolyDeriv p) := by
  unfold slowBandPolyDeriv
  exact (continuous_slowBandPolyDerivCircle p).comp
    (AddCircle.continuous_mk' (2 * Real.pi))

private theorem hasDerivAt_slowBandPoly_mk {L : Nat}
    (p : Fin L -> ℂ) (t : ℝ) :
    HasDerivAt (fun y : ℝ => slowBandPoly p (QuotientAddGroup.mk y : Circle))
      (slowBandPolyDeriv p t) t := by
  unfold slowBandPoly slowBandPolyDeriv
  unfold slowBandPolyDerivCircle
  simpa [circleChar_eq_fourier_nat, mul_assoc] using
    (HasDerivAt.fun_sum
      (u := Finset.univ)
      (x := t)
      (A := fun (m : Fin L) y =>
        p m * fourier (m.1 : ℤ) (QuotientAddGroup.mk y : Circle))
      (A' := fun (m : Fin L) =>
        p m * ((2 * Real.pi * Complex.I * (m.1 : ℤ) /
          ((2 * Real.pi : ℝ) : ℂ)) *
            fourier (m.1 : ℤ) (QuotientAddGroup.mk t : Circle)))
      (by
        intro m hm
        exact (hasDerivAt_fourier (T := 2 * Real.pi)
          (m.1 : ℤ) t).const_mul (p m)))

private theorem hasDerivAt_slowBandPoly_shift {L : Nat}
    (p : Fin L -> ℂ) (a x : ℝ) :
    HasDerivAt
      (fun y : ℝ => slowBandPoly p (QuotientAddGroup.mk (y + a) : Circle))
      (slowBandPolyDeriv p (x + a)) x := by
  have h :=
    HasDerivAt.scomp (x := x)
      (hasDerivAt_slowBandPoly_mk p (x + a))
      ((hasDerivAt_id x).add (hasDerivAt_const x a))
  simp only [Function.comp_def, Pi.add_apply, id_eq, add_zero, one_smul] at h
  exact h

private theorem continuous_lowPoly {D : Nat} (q : Fin (D + 1) -> ℂ) :
    Continuous (lowPoly q) := by
  unfold lowPoly
  exact continuous_finsetSum _ fun n hn =>
    continuous_const.mul (continuous_circleChar n.1)

private theorem continuous_bandPoly (N : Nat) {L : Nat} (p : Fin L -> ℂ) :
    Continuous (bandPoly N p) := by
  unfold bandPoly
  exact continuous_finsetSum _ fun m hm =>
    continuous_const.mul (continuous_circleChar (N + m.1))

/-- `circleL2Sq`: circle L2 Sq. -/
noncomputable def circleL2Sq (f : AddCircle (2 * Real.pi) -> ℂ) : ℝ :=
  ∫ t, ‖f t‖ ^ 2 ∂ AddCircle.haarAddCircle

/-- `defectSq`: defect Sq. -/
noncomputable def defectSq
    (Q P : AddCircle (2 * Real.pi) -> ℂ) : ℝ :=
  ∫ t, (‖Q t + P t‖ - ‖Q t‖) ^ 2 ∂ AddCircle.haarAddCircle

private theorem defectSq_nonneg (Q P : Circle -> ℂ) :
    0 <= defectSq Q P := by
  unfold defectSq
  exact MeasureTheory.integral_nonneg fun x => sq_nonneg _

private theorem safe_square
    {a b c : ℝ} (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c)
    (h : b - c <= a) :
    (1 / 2) * b ^ 2 - c ^ 2 <= a ^ 2 := by
  by_cases hbc : b <= c
  · have hnonpos : (1 / 2) * b ^ 2 - c ^ 2 <= 0 := by
      nlinarith [sq_nonneg b, sq_nonneg c]
    exact hnonpos.trans (sq_nonneg a)
  · have hbc_pos : 0 <= b - c := by
      linarith
    have hsq_to_a : (b - c) ^ 2 <= a ^ 2 := by
      nlinarith
    have hsq_from_bc : (1 / 2) * b ^ 2 - c ^ 2 <= (b - c) ^ 2 := by
      nlinarith [sq_nonneg (b - 2 * c)]
    exact hsq_from_bc.trans hsq_to_a

private theorem norm_sq_le_two_base_sq_add_two_diff_sq (z u : ℂ) :
    ‖z‖ ^ 2 <= 2 * ‖u‖ ^ 2 + 2 * ‖z - u‖ ^ 2 := by
  have htri : ‖z‖ <= ‖u‖ + ‖z - u‖ := by
    calc
      ‖z‖ = ‖u + (z - u)‖ := by
        congr 1
        ring
      _ <= ‖u‖ + ‖z - u‖ := norm_add_le _ _
  have hz_nonneg : 0 <= ‖z‖ := norm_nonneg _
  have hsum_nonneg : 0 <= ‖u‖ + ‖z - u‖ := by positivity
  have hsq :
      ‖z‖ ^ 2 <= (‖u‖ + ‖z - u‖) ^ 2 := by
    nlinarith
  have hsum :
      (‖u‖ + ‖z - u‖) ^ 2 <=
        2 * ‖u‖ ^ 2 + 2 * ‖z - u‖ ^ 2 := by
    nlinarith [sq_nonneg (‖u‖ - ‖z - u‖)]
  exact hsq.trans hsum

private theorem defect_pointwise_safe_carrier_average
    (Q : Circle -> ℂ) (N : Nat) {L : Nat} (p : Fin L -> ℂ)
    (u : ℂ) (x : Circle) :
    (1 / 2) *
        (‖Q x + circleChar N x * u‖ - ‖Q x‖) ^ 2 -
        ‖slowBandPoly p x - u‖ ^ 2 <=
      (‖Q x + bandPoly N p x‖ - ‖Q x‖) ^ 2 := by
  let a : ℝ := |‖Q x + bandPoly N p x‖ - ‖Q x‖|
  let b : ℝ := |‖Q x + circleChar N x * u‖ - ‖Q x‖|
  let c : ℝ := ‖slowBandPoly p x - u‖
  have hba : b - a <= c := by
    have h_abs :
        |b - a| <=
          |(‖Q x + circleChar N x * u‖ - ‖Q x‖) -
            (‖Q x + bandPoly N p x‖ - ‖Q x‖)| := by
      simpa [a, b, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        using abs_abs_sub_abs_le_abs_sub
          (‖Q x + circleChar N x * u‖ - ‖Q x‖)
          (‖Q x + bandPoly N p x‖ - ‖Q x‖)
    have h_norm :
        |(‖Q x + circleChar N x * u‖ - ‖Q x‖) -
            (‖Q x + bandPoly N p x‖ - ‖Q x‖)| <= c := by
      calc
        |(‖Q x + circleChar N x * u‖ - ‖Q x‖) -
            (‖Q x + bandPoly N p x‖ - ‖Q x‖)|
            = |‖Q x + circleChar N x * u‖ -
                ‖Q x + bandPoly N p x‖| := by ring_nf
        _ <= ‖(Q x + circleChar N x * u) -
              (Q x + bandPoly N p x)‖ :=
            abs_norm_sub_norm_le _ _
        _ = ‖circleChar N x * u - bandPoly N p x‖ := by
            congr 1
            ring_nf
        _ = ‖bandPoly N p x - circleChar N x * u‖ := by
            rw [← norm_neg]
            congr 1
            ring_nf
        _ = c := by
            simp [c, norm_bandPoly_sub_fast_mul]
    exact (le_abs_self (b - a)).trans (h_abs.trans h_norm)
  have hmain : b - c <= a := by linarith
  have hsafe := safe_square
    (a := a) (b := b) (c := c)
    (abs_nonneg _) (abs_nonneg _) (norm_nonneg _) hmain
  simpa [a, b, c, sq_abs] using hsafe

private theorem carrierAverage_constCenter_sq_le_defect
    {N : Nat} (k : Fin N) {L : Nat} (p : Fin L -> ℂ)
    {c : ℂ} (hc : c ≠ 0) :
    arcLength (carrierArc N k) *
        ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 <=
      Crot *
        arcIntegral (carrierArc N k)
          (fun x =>
            (‖c + circleChar N x *
              carrierAverage (N := N) k (slowBandPoly p)‖ - ‖c‖) ^ 2) := by
  exact constantCenter_fastRotate_carrierArc_sq_le_defectSq
    (N := N) k (c := c) (u := carrierAverage (N := N) k (slowBandPoly p)) hc

private theorem defectSq_safe_carrier_average_global
    (Q : Circle -> ℂ) (hQ : Continuous Q)
    (N : Nat) {L : Nat} (p : Fin L -> ℂ) (u : ℂ) :
    (1 / 2) *
        ∫ x : Circle,
          (‖Q x + circleChar N x * u‖ - ‖Q x‖) ^ 2 ∂ μCircle -
        ∫ x : Circle, ‖slowBandPoly p x - u‖ ^ 2 ∂ μCircle
      <= defectSq Q (bandPoly N p) := by
  have hband : Continuous (bandPoly N p) := continuous_bandPoly N p
  have hslow : Continuous (slowBandPoly p) := continuous_slowBandPoly p
  have hfast_const : Continuous fun x : Circle => circleChar N x * u :=
    (continuous_circleChar N).mul continuous_const
  have havg_cont : Continuous fun x : Circle =>
      (‖Q x + circleChar N x * u‖ - ‖Q x‖) ^ 2 :=
    (((hQ.add hfast_const).norm).sub hQ.norm).pow 2
  have hvar_cont : Continuous fun x : Circle =>
      ‖slowBandPoly p x - u‖ ^ 2 :=
    ((hslow.sub continuous_const).norm).pow 2
  have hactual_cont : Continuous fun x : Circle =>
      (‖Q x + bandPoly N p x‖ - ‖Q x‖) ^ 2 :=
    (((hQ.add hband).norm).sub hQ.norm).pow 2
  have havg_int :
      MeasureTheory.Integrable
        (fun x : Circle =>
          (‖Q x + circleChar N x * u‖ - ‖Q x‖) ^ 2) μCircle := by
    simpa [μCircle] using
      havg_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hvar_int :
      MeasureTheory.Integrable
        (fun x : Circle => ‖slowBandPoly p x - u‖ ^ 2) μCircle := by
    simpa [μCircle] using
      hvar_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hactual_int :
      MeasureTheory.Integrable
        (fun x : Circle =>
          (‖Q x + bandPoly N p x‖ - ‖Q x‖) ^ 2) μCircle := by
    simpa [μCircle] using
      hactual_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcombo_int :
      MeasureTheory.Integrable
        (fun x : Circle =>
          (1 / 2) *
            (‖Q x + circleChar N x * u‖ - ‖Q x‖) ^ 2 -
            ‖slowBandPoly p x - u‖ ^ 2) μCircle :=
    (havg_int.const_mul (1 / 2)).sub hvar_int
  have hmono :
      (∫ x : Circle,
          (1 / 2) *
            (‖Q x + circleChar N x * u‖ - ‖Q x‖) ^ 2 -
            ‖slowBandPoly p x - u‖ ^ 2 ∂ μCircle)
        <=
      ∫ x : Circle,
        (‖Q x + bandPoly N p x‖ - ‖Q x‖) ^ 2 ∂ μCircle := by
    refine MeasureTheory.integral_mono_ae hcombo_int hactual_int ?_
    filter_upwards with x
    exact defect_pointwise_safe_carrier_average Q N p u x
  calc
    (1 / 2) *
        ∫ x : Circle,
          (‖Q x + circleChar N x * u‖ - ‖Q x‖) ^ 2 ∂ μCircle -
        ∫ x : Circle, ‖slowBandPoly p x - u‖ ^ 2 ∂ μCircle
        =
      ∫ x : Circle,
          (1 / 2) *
            (‖Q x + circleChar N x * u‖ - ‖Q x‖) ^ 2 -
            ‖slowBandPoly p x - u‖ ^ 2 ∂ μCircle := by
          rw [MeasureTheory.integral_sub (havg_int.const_mul (1 / 2)) hvar_int,
            MeasureTheory.integral_const_mul]
    _ <= ∫ x : Circle,
        (‖Q x + bandPoly N p x‖ - ‖Q x‖) ^ 2 ∂ μCircle := hmono
    _ = defectSq Q (bandPoly N p) := by
          simp [defectSq, μCircle]

private theorem defect_setIntegral_safe_carrier_average
    (s : Set Circle) (Q : Circle -> ℂ) (hQ : Continuous Q)
    (N : Nat) {L : Nat} (p : Fin L -> ℂ) (u : ℂ) :
    (1 / 2) *
        ∫ x in s,
          (‖Q x + circleChar N x * u‖ - ‖Q x‖) ^ 2 ∂ μCircle -
        ∫ x in s, ‖slowBandPoly p x - u‖ ^ 2 ∂ μCircle
      <=
        ∫ x in s,
          (‖Q x + bandPoly N p x‖ - ‖Q x‖) ^ 2 ∂ μCircle := by
  have hband : Continuous (bandPoly N p) := continuous_bandPoly N p
  have hslow : Continuous (slowBandPoly p) := continuous_slowBandPoly p
  have hfast_const : Continuous fun x : Circle => circleChar N x * u :=
    (continuous_circleChar N).mul continuous_const
  have havg_cont : Continuous fun x : Circle =>
      (‖Q x + circleChar N x * u‖ - ‖Q x‖) ^ 2 :=
    (((hQ.add hfast_const).norm).sub hQ.norm).pow 2
  have hvar_cont : Continuous fun x : Circle =>
      ‖slowBandPoly p x - u‖ ^ 2 :=
    ((hslow.sub continuous_const).norm).pow 2
  have hactual_cont : Continuous fun x : Circle =>
      (‖Q x + bandPoly N p x‖ - ‖Q x‖) ^ 2 :=
    (((hQ.add hband).norm).sub hQ.norm).pow 2
  have havg_int :
      MeasureTheory.Integrable
        (fun x : Circle =>
          (‖Q x + circleChar N x * u‖ - ‖Q x‖) ^ 2) μCircle := by
    simpa [μCircle] using
      havg_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hvar_int :
      MeasureTheory.Integrable
        (fun x : Circle => ‖slowBandPoly p x - u‖ ^ 2) μCircle := by
    simpa [μCircle] using
      hvar_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hactual_int :
      MeasureTheory.Integrable
        (fun x : Circle =>
          (‖Q x + bandPoly N p x‖ - ‖Q x‖) ^ 2) μCircle := by
    simpa [μCircle] using
      hactual_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcombo_int :
      MeasureTheory.Integrable
        (fun x : Circle =>
          (1 / 2) *
            (‖Q x + circleChar N x * u‖ - ‖Q x‖) ^ 2 -
            ‖slowBandPoly p x - u‖ ^ 2) μCircle :=
    (havg_int.const_mul (1 / 2)).sub hvar_int
  have hmono :
      (∫ x in s,
          (1 / 2) *
            (‖Q x + circleChar N x * u‖ - ‖Q x‖) ^ 2 -
            ‖slowBandPoly p x - u‖ ^ 2 ∂ μCircle)
        <=
      ∫ x in s,
        (‖Q x + bandPoly N p x‖ - ‖Q x‖) ^ 2 ∂ μCircle := by
    refine MeasureTheory.integral_mono_ae hcombo_int.restrict hactual_int.restrict ?_
    filter_upwards with x
    exact defect_pointwise_safe_carrier_average Q N p u x
  calc
    (1 / 2) *
        ∫ x in s,
          (‖Q x + circleChar N x * u‖ - ‖Q x‖) ^ 2 ∂ μCircle -
        ∫ x in s, ‖slowBandPoly p x - u‖ ^ 2 ∂ μCircle
        =
      ∫ x in s,
          (1 / 2) *
            (‖Q x + circleChar N x * u‖ - ‖Q x‖) ^ 2 -
            ‖slowBandPoly p x - u‖ ^ 2 ∂ μCircle := by
          rw [MeasureTheory.integral_sub (havg_int.const_mul (1 / 2)).restrict
            hvar_int.restrict, MeasureTheory.integral_const_mul]
    _ <= ∫ x in s,
        (‖Q x + bandPoly N p x‖ - ‖Q x‖) ^ 2 ∂ μCircle := hmono

private theorem carrierAverage_mass_le_defect_plus_variance
    {N : Nat} (k : Fin N) {L : Nat} (p : Fin L -> ℂ)
    {c : ℂ} (hc : c ≠ 0) :
    arcLength (carrierArc N k) *
        ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 <=
      2 * Crot *
          arcIntegral (carrierArc N k)
            (fun x => (‖c + bandPoly N p x‖ - ‖c‖) ^ 2) +
        2 * Crot *
          arcIntegral (carrierArc N k)
            (fun x =>
              ‖slowBandPoly p x -
                carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2) := by
  let u : ℂ := carrierAverage (N := N) k (slowBandPoly p)
  let I : CircleArc := carrierArc N k
  let A : ℝ := arcIntegral I
    (fun x => (‖c + circleChar N x * u‖ - ‖c‖) ^ 2)
  let Dint : ℝ := arcIntegral I
    (fun x => (‖c + bandPoly N p x‖ - ‖c‖) ^ 2)
  let V : ℝ := arcIntegral I
    (fun x => ‖slowBandPoly p x - u‖ ^ 2)
  have hrot : arcLength I * ‖u‖ ^ 2 <= Crot * A := by
    simpa [I, A, u] using carrierAverage_constCenter_sq_le_defect
      (N := N) k p hc
  have hsafe :
      (1 / 2) * A - V <= Dint := by
    have h :=
      defect_setIntegral_safe_carrier_average
        (arcSet I) (fun _ : Circle => c) continuous_const N p u
    exact h
  have hA : A <= 2 * Dint + 2 * V := by
    nlinarith
  calc
    arcLength (carrierArc N k) *
        ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2
        <= Crot * A := by simpa [I, u] using hrot
    _ <= Crot * (2 * Dint + 2 * V) :=
        mul_le_mul_of_nonneg_left hA (le_of_lt Crot_pos)
    _ =
        2 * Crot *
            arcIntegral (carrierArc N k)
              (fun x => (‖c + bandPoly N p x‖ - ‖c‖) ^ 2) +
          2 * Crot *
            arcIntegral (carrierArc N k)
              (fun x =>
                ‖slowBandPoly p x -
                  carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2) := by
        simp [Dint, V, u, I]
        ring

private theorem carrierPoint_mass_le_defect_plus_variance
    {N : Nat} (k : Fin N) {L : Nat} (p : Fin L -> ℂ)
    {c u : ℂ} (hc : c ≠ 0) :
    arcLength (carrierArc N k) * ‖u‖ ^ 2 <=
      2 * Crot *
          arcIntegral (carrierArc N k)
            (fun x => (‖c + bandPoly N p x‖ - ‖c‖) ^ 2) +
        2 * Crot *
          arcIntegral (carrierArc N k)
            (fun x => ‖slowBandPoly p x - u‖ ^ 2) := by
  let I : CircleArc := carrierArc N k
  let A : ℝ := arcIntegral I
    (fun x => (‖c + circleChar N x * u‖ - ‖c‖) ^ 2)
  let Dint : ℝ := arcIntegral I
    (fun x => (‖c + bandPoly N p x‖ - ‖c‖) ^ 2)
  let V : ℝ := arcIntegral I
    (fun x => ‖slowBandPoly p x - u‖ ^ 2)
  have hrot : arcLength I * ‖u‖ ^ 2 <= Crot * A := by
    simpa [I, A] using
      constantCenter_fastRotate_carrierArc_sq_le_defectSq
        (N := N) k (c := c) (u := u) hc
  have hsafe :
      (1 / 2) * A - V <= Dint := by
    have h :=
      defect_setIntegral_safe_carrier_average
        (arcSet I) (fun _ : Circle => c) continuous_const N p u
    exact h
  have hA : A <= 2 * Dint + 2 * V := by
    nlinarith
  calc
    arcLength (carrierArc N k) * ‖u‖ ^ 2
        <= Crot * A := by simpa [I] using hrot
    _ <= Crot * (2 * Dint + 2 * V) :=
        mul_le_mul_of_nonneg_left hA (le_of_lt Crot_pos)
    _ =
        2 * Crot *
            arcIntegral (carrierArc N k)
              (fun x => (‖c + bandPoly N p x‖ - ‖c‖) ^ 2) +
          2 * Crot *
            arcIntegral (carrierArc N k)
              (fun x => ‖slowBandPoly p x - u‖ ^ 2) := by
        simp [Dint, V, I]
        ring

private theorem const_center_abs_defect_eq_norm_mul_rho
    {c w : ℂ} (hc : c ≠ 0) :
    |‖c + w‖ - ‖c‖| = ‖c‖ * FockSPR.rho (c⁻¹ * w) := by
  have hfactor : c + w = c * ((1 : ℂ) + c⁻¹ * w) := by
    field_simp [hc]
  calc
    |‖c + w‖ - ‖c‖|
        = |‖c‖ * ‖(1 : ℂ) + c⁻¹ * w‖ - ‖c‖| := by
            rw [hfactor, norm_mul]
    _ = |‖c‖ * (‖(1 : ℂ) + c⁻¹ * w‖ - 1)| := by
            ring_nf
    _ = ‖c‖ * |‖(1 : ℂ) + c⁻¹ * w‖ - 1| := by
            rw [abs_mul, abs_of_nonneg (norm_nonneg c)]
    _ = ‖c‖ * FockSPR.rho (c⁻¹ * w) := rfl

private theorem abs_norm_sub_one_le_norm_sub_one (lam : ℂ) :
    |‖lam‖ - 1| <= ‖lam - 1‖ := by
  simpa [norm_one] using abs_norm_sub_norm_le lam (1 : ℂ)

private theorem abs_rho_sub_rho_le_norm_sub (w z : ℂ) :
    |FockSPR.rho w - FockSPR.rho z| <= ‖w - z‖ := by
  have h := FockSPR.rho_lipschitz.dist_le_mul w z
  rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm] at h
  simpa [Real.dist_eq] using h

private theorem const_center_multiplicative_stability
    {c lam u : ℂ} (hc : c ≠ 0) (hlam : lam ≠ 0)
    (hinv_norm : ‖lam⁻¹‖ <= 2)
    (hinv_sub : ‖lam⁻¹ - 1‖ <= 2 * ‖lam - 1‖) :
    |(|‖lam * c + u‖ - ‖lam * c‖| -
        |‖c + u‖ - ‖c‖|)|
      <= 4 * ‖lam - 1‖ * ‖u‖ := by
  let w : ℂ := c⁻¹ * u
  let R : ℝ := FockSPR.rho (lam⁻¹ * w)
  let S : ℝ := FockSPR.rho w
  let d : ℝ := ‖lam - 1‖
  have hlamc : lam * c ≠ 0 := mul_ne_zero hlam hc
  have harg : (lam * c)⁻¹ * u = lam⁻¹ * w := by
    dsimp [w]
    field_simp [hlam, hc]
  have hcw : ‖c‖ * ‖w‖ = ‖u‖ := by
    dsimp [w]
    rw [norm_mul, norm_inv]
    have hcn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
    field_simp [hcn]
  have hR_nonneg : 0 <= R := by
    dsimp [R, FockSPR.rho]
    exact abs_nonneg _
  have hR_le : R <= 2 * ‖w‖ := by
    calc
      R <= ‖lam⁻¹ * w‖ := by
        exact FockSPR.rho_le_norm (lam⁻¹ * w)
      _ = ‖lam⁻¹‖ * ‖w‖ := norm_mul _ _
      _ <= 2 * ‖w‖ :=
        mul_le_mul_of_nonneg_right hinv_norm (norm_nonneg w)
  have hRS_le : |R - S| <= 2 * d * ‖w‖ := by
    calc
      |R - S| <= ‖lam⁻¹ * w - w‖ := by
        simpa [R, S] using abs_rho_sub_rho_le_norm_sub (lam⁻¹ * w) w
      _ = ‖(lam⁻¹ - 1) * w‖ := by
        congr 1
        ring
      _ = ‖lam⁻¹ - 1‖ * ‖w‖ := norm_mul _ _
      _ <= (2 * d) * ‖w‖ :=
        mul_le_mul_of_nonneg_right hinv_sub (norm_nonneg w)
  have hcore : |‖lam‖ * R - S| <= 4 * d * ‖w‖ := by
    calc
      |‖lam‖ * R - S|
          = |(‖lam‖ - 1) * R + (R - S)| := by ring_nf
      _ <= |(‖lam‖ - 1) * R| + |R - S| := by
        simpa [Real.norm_eq_abs] using
          norm_add_le ((‖lam‖ - 1) * R) (R - S)
      _ = |‖lam‖ - 1| * R + |R - S| := by
        rw [abs_mul, abs_of_nonneg hR_nonneg]
      _ <= d * R + |R - S| := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right
            (abs_norm_sub_one_le_norm_sub_one lam) hR_nonneg) le_rfl
      _ <= d * (2 * ‖w‖) + 2 * d * ‖w‖ := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hR_le (norm_nonneg (lam - 1)))
          hRS_le
      _ = 4 * d * ‖w‖ := by ring
  have hrewrite :
      |(|‖lam * c + u‖ - ‖lam * c‖| -
          |‖c + u‖ - ‖c‖|)| =
        ‖c‖ * |‖lam‖ * R - S| := by
    rw [const_center_abs_defect_eq_norm_mul_rho hlamc,
      const_center_abs_defect_eq_norm_mul_rho hc, harg]
    dsimp [R, S]
    rw [norm_mul]
    calc
      |‖lam‖ * ‖c‖ * FockSPR.rho (lam⁻¹ * w) -
          ‖c‖ * FockSPR.rho w|
          =
        |‖c‖ * (‖lam‖ * FockSPR.rho (lam⁻¹ * w) -
          FockSPR.rho w)| := by ring_nf
      _ = ‖c‖ * |‖lam‖ * FockSPR.rho (lam⁻¹ * w) -
          FockSPR.rho w| := by
            rw [abs_mul, abs_of_nonneg (norm_nonneg c)]
  calc
    |(|‖lam * c + u‖ - ‖lam * c‖| -
        |‖c + u‖ - ‖c‖|)|
        = ‖c‖ * |‖lam‖ * R - S| := hrewrite
    _ <= ‖c‖ * (4 * d * ‖w‖) :=
        mul_le_mul_of_nonneg_left hcore (norm_nonneg c)
    _ = 4 * ‖lam - 1‖ * ‖u‖ := by
        dsimp [d]
        rw [← hcw]
        ring

private theorem norm_inv_le_two_of_norm_sub_one_le_half {lam : ℂ}
    (hclose : ‖lam - 1‖ <= 1 / 2) :
    ‖lam⁻¹‖ <= 2 := by
  have habs := abs_norm_sub_one_le_norm_sub_one lam
  have hlower : (1 / 2 : ℝ) <= ‖lam‖ := by
    have hneg : 1 - ‖lam‖ <= |‖lam‖ - 1| := by
      rw [show 1 - ‖lam‖ = -(‖lam‖ - 1) by ring]
      exact neg_le_abs _
    linarith
  have hpos : 0 < ‖lam‖ := by linarith
  rw [norm_inv]
  rw [inv_le_comm₀ hpos (by norm_num : (0 : ℝ) < 2)]
  nlinarith

private theorem norm_inv_sub_one_le_two_mul_norm_sub_one_of_close {lam : ℂ}
    (hclose : ‖lam - 1‖ <= 1 / 2) :
    ‖lam⁻¹ - 1‖ <= 2 * ‖lam - 1‖ := by
  have hinv : ‖lam⁻¹‖ <= 2 :=
    norm_inv_le_two_of_norm_sub_one_le_half hclose
  have hrepr : lam⁻¹ - 1 = -(lam⁻¹ * (lam - 1)) := by
    have habs := abs_norm_sub_one_le_norm_sub_one lam
    have hlower : (1 / 2 : ℝ) <= ‖lam‖ := by
      have hneg : 1 - ‖lam‖ <= |‖lam‖ - 1| := by
        rw [show 1 - ‖lam‖ = -(‖lam‖ - 1) by ring]
        exact neg_le_abs _
      linarith
    have hlam : lam ≠ 0 := by
      intro hzero
      subst lam
      norm_num at hlower
    field_simp [hlam]
    ring
  calc
    ‖lam⁻¹ - 1‖ = ‖lam⁻¹ * (lam - 1)‖ := by
      rw [hrepr, norm_neg]
    _ = ‖lam⁻¹‖ * ‖lam - 1‖ := norm_mul _ _
    _ <= 2 * ‖lam - 1‖ :=
      mul_le_mul_of_nonneg_right hinv (norm_nonneg _)

private theorem const_center_multiplicative_stability_of_close
    {c lam u : ℂ} (hc : c ≠ 0)
    (hclose : ‖lam - 1‖ <= 1 / 2) :
    |(|‖lam * c + u‖ - ‖lam * c‖| -
        |‖c + u‖ - ‖c‖|)|
      <= 4 * ‖lam - 1‖ * ‖u‖ := by
  have hlam : lam ≠ 0 := by
    intro hzero
    subst lam
    norm_num at hclose
  exact const_center_multiplicative_stability hc hlam
    (norm_inv_le_two_of_norm_sub_one_le_half hclose)
    (norm_inv_sub_one_le_two_mul_norm_sub_one_of_close hclose)

private theorem defect_pointwise_const_center_compare_of_close
    {c lam u : ℂ} (hc : c ≠ 0)
    (hclose : ‖lam - 1‖ <= 1 / 2) :
    (1 / 2) * (‖c + u‖ - ‖c‖) ^ 2 -
        (4 * ‖lam - 1‖ * ‖u‖) ^ 2 <=
      (‖lam * c + u‖ - ‖lam * c‖) ^ 2 := by
  let a : ℝ := |‖lam * c + u‖ - ‖lam * c‖|
  let b : ℝ := |‖c + u‖ - ‖c‖|
  let e : ℝ := 4 * ‖lam - 1‖ * ‖u‖
  have hstab : |a - b| <= e := by
    simpa [a, b, e, abs_sub_comm] using
      const_center_multiplicative_stability_of_close
        (c := c) (lam := lam) (u := u) hc hclose
  have hba : b - e <= a := by
    have hle : b - a <= |a - b| := by
      rw [show b - a = -(a - b) by ring]
      exact neg_le_abs _
    linarith
  have he_nonneg : 0 <= e := by
    dsimp [e]
    positivity
  have hsafe := safe_square
    (a := a) (b := b) (c := e)
    (abs_nonneg _) (abs_nonneg _) he_nonneg hba
  simpa [a, b, e, sq_abs] using hsafe

private theorem defect_pointwise_const_center_compare_fast_of_close
    (N : Nat) (x : Circle) {c lam u : ℂ} (hc : c ≠ 0)
    (hclose : ‖lam - 1‖ <= 1 / 2) :
    (1 / 2) * (‖c + circleChar N x * u‖ - ‖c‖) ^ 2 -
        (4 * ‖lam - 1‖ * ‖u‖) ^ 2 <=
      (‖lam * c + circleChar N x * u‖ - ‖lam * c‖) ^ 2 := by
  have h := defect_pointwise_const_center_compare_of_close
    (c := c) (lam := lam) (u := circleChar N x * u) hc hclose
  simpa [norm_mul, norm_circleChar_wip] using h

private theorem exists_factor_close_of_norm_sub_le
    {Qx c : ℂ} {theta : ℝ} (hc : c ≠ 0)
    (hclose : ‖Qx - c‖ <= theta * ‖c‖) :
    ∃ lam : ℂ, Qx = lam * c ∧ ‖lam - 1‖ <= theta := by
  refine ⟨Qx * c⁻¹, ?_, ?_⟩
  · field_simp [hc]
  · have hc_norm_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have hrewrite : Qx * c⁻¹ - 1 = (Qx - c) * c⁻¹ := by
      field_simp [hc]
    calc
      ‖Qx * c⁻¹ - 1‖ = ‖(Qx - c) * c⁻¹‖ := by rw [hrewrite]
      _ = ‖Qx - c‖ * ‖c⁻¹‖ := norm_mul _ _
      _ = ‖Qx - c‖ / ‖c‖ := by rw [norm_inv]; ring
      _ <= theta := by
        rw [div_le_iff₀ hc_norm_pos]
        simpa [mul_comm] using hclose

private theorem defect_setIntegral_const_center_compare_fast
    (s : Set Circle) (hs : MeasurableSet s)
    (Q : Circle -> ℂ) (hQ : Continuous Q)
    (N : Nat) {c u : ℂ} {theta : ℝ}
    (hc : c ≠ 0) (htheta_nonneg : 0 <= theta)
    (htheta_le : theta <= 1 / 2)
    (hfactor : ∀ x ∈ s,
      ∃ lam : ℂ, Q x = lam * c ∧ ‖lam - 1‖ <= theta) :
    (1 / 2) *
        ∫ x in s,
          (‖c + circleChar N x * u‖ - ‖c‖) ^ 2 ∂ μCircle -
        ∫ _ in s, (4 * theta * ‖u‖) ^ 2 ∂ μCircle
      <=
        ∫ x in s,
          (‖Q x + circleChar N x * u‖ - ‖Q x‖) ^ 2 ∂ μCircle := by
  have hfast_const : Continuous fun x : Circle => circleChar N x * u :=
    (continuous_circleChar N).mul continuous_const
  have hconst_cont : Continuous fun x : Circle =>
      (‖c + circleChar N x * u‖ - ‖c‖) ^ 2 :=
    (((continuous_const.add hfast_const).norm).sub continuous_const).pow 2
  have hactual_cont : Continuous fun x : Circle =>
      (‖Q x + circleChar N x * u‖ - ‖Q x‖) ^ 2 :=
    (((hQ.add hfast_const).norm).sub hQ.norm).pow 2
  have hconst_int :
      MeasureTheory.Integrable
        (fun x : Circle =>
          (‖c + circleChar N x * u‖ - ‖c‖) ^ 2) μCircle := by
    simpa [μCircle] using
      hconst_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  haveI : MeasureTheory.IsFiniteMeasure μCircle := by
    dsimp [μCircle]
    infer_instance
  have herr_int :
      MeasureTheory.Integrable
        (fun _ : Circle => (4 * theta * ‖u‖) ^ 2) μCircle :=
    MeasureTheory.integrable_const _
  have hactual_int :
      MeasureTheory.Integrable
        (fun x : Circle =>
          (‖Q x + circleChar N x * u‖ - ‖Q x‖) ^ 2) μCircle := by
    simpa [μCircle] using
      hactual_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcombo_int :
      MeasureTheory.Integrable
        (fun x : Circle =>
          (1 / 2) *
            (‖c + circleChar N x * u‖ - ‖c‖) ^ 2 -
            (4 * theta * ‖u‖) ^ 2) μCircle :=
    (hconst_int.const_mul (1 / 2)).sub herr_int
  have hmono :
      (∫ x in s,
          (1 / 2) *
            (‖c + circleChar N x * u‖ - ‖c‖) ^ 2 -
            (4 * theta * ‖u‖) ^ 2 ∂ μCircle)
        <=
      ∫ x in s,
        (‖Q x + circleChar N x * u‖ - ‖Q x‖) ^ 2 ∂ μCircle := by
    refine MeasureTheory.integral_mono_ae hcombo_int.restrict hactual_int.restrict ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hs] with x hx
    rcases hfactor x hx with ⟨lam, hQx, hclose⟩
    have hclose_half : ‖lam - 1‖ <= 1 / 2 := hclose.trans htheta_le
    have hpoint :=
      defect_pointwise_const_center_compare_fast_of_close
        N x (c := c) (lam := lam) (u := u) hc hclose_half
    have herr :
        (4 * ‖lam - 1‖ * ‖u‖) ^ 2 <= (4 * theta * ‖u‖) ^ 2 := by
      have hleft_nonneg : 0 <= 4 * ‖lam - 1‖ * ‖u‖ := by positivity
      have hright_nonneg : 0 <= 4 * theta * ‖u‖ := by positivity
      have hmul : 4 * ‖lam - 1‖ * ‖u‖ <= 4 * theta * ‖u‖ := by
        nlinarith [norm_nonneg (lam - 1), norm_nonneg u]
      nlinarith
    calc
      (1 / 2) * (‖c + circleChar N x * u‖ - ‖c‖) ^ 2 -
          (4 * theta * ‖u‖) ^ 2
          <=
        (1 / 2) * (‖c + circleChar N x * u‖ - ‖c‖) ^ 2 -
          (4 * ‖lam - 1‖ * ‖u‖) ^ 2 := by
            nlinarith
      _ <= (‖lam * c + circleChar N x * u‖ - ‖lam * c‖) ^ 2 := hpoint
      _ = (‖Q x + circleChar N x * u‖ - ‖Q x‖) ^ 2 := by
            rw [hQx]
  calc
    (1 / 2) *
        ∫ x in s,
          (‖c + circleChar N x * u‖ - ‖c‖) ^ 2 ∂ μCircle -
        ∫ _ in s, (4 * theta * ‖u‖) ^ 2 ∂ μCircle
        =
      ∫ x in s,
          (1 / 2) *
            (‖c + circleChar N x * u‖ - ‖c‖) ^ 2 -
            (4 * theta * ‖u‖) ^ 2 ∂ μCircle := by
          rw [MeasureTheory.integral_sub (hconst_int.const_mul (1 / 2)).restrict
            herr_int.restrict, MeasureTheory.integral_const_mul]
    _ <= ∫ x in s,
        (‖Q x + circleChar N x * u‖ - ‖Q x‖) ^ 2 ∂ μCircle := hmono

private theorem defect_setIntegral_const_center_compare
    (s : Set Circle) (hs : MeasurableSet s)
    (Q P : Circle -> ℂ) (hQ : Continuous Q) (hP : Continuous P)
    {c : ℂ} {theta : ℝ}
    (hc : c ≠ 0) (htheta_nonneg : 0 <= theta)
    (htheta_le : theta <= 1 / 2)
    (hfactor : ∀ x ∈ s,
      ∃ lam : ℂ, Q x = lam * c ∧ ‖lam - 1‖ <= theta) :
    (1 / 2) *
        ∫ x in s, (‖c + P x‖ - ‖c‖) ^ 2 ∂ μCircle -
        ∫ x in s, (4 * theta * ‖P x‖) ^ 2 ∂ μCircle
      <=
        ∫ x in s, (‖Q x + P x‖ - ‖Q x‖) ^ 2 ∂ μCircle := by
  have hconst_cont : Continuous fun x : Circle =>
      (‖c + P x‖ - ‖c‖) ^ 2 :=
    (((continuous_const.add hP).norm).sub continuous_const).pow 2
  have herr_cont : Continuous fun x : Circle =>
      (4 * theta * ‖P x‖) ^ 2 :=
    (((hP.norm).const_mul (4 * theta)).pow 2)
  have hactual_cont : Continuous fun x : Circle =>
      (‖Q x + P x‖ - ‖Q x‖) ^ 2 :=
    (((hQ.add hP).norm).sub hQ.norm).pow 2
  have hconst_int :
      MeasureTheory.Integrable
        (fun x : Circle => (‖c + P x‖ - ‖c‖) ^ 2) μCircle := by
    simpa [μCircle] using
      hconst_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have herr_int :
      MeasureTheory.Integrable
        (fun x : Circle => (4 * theta * ‖P x‖) ^ 2) μCircle := by
    simpa [μCircle] using
      herr_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hactual_int :
      MeasureTheory.Integrable
        (fun x : Circle => (‖Q x + P x‖ - ‖Q x‖) ^ 2) μCircle := by
    simpa [μCircle] using
      hactual_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcombo_int :
      MeasureTheory.Integrable
        (fun x : Circle =>
          (1 / 2) * (‖c + P x‖ - ‖c‖) ^ 2 -
            (4 * theta * ‖P x‖) ^ 2) μCircle :=
    (hconst_int.const_mul (1 / 2)).sub herr_int
  have hmono :
      (∫ x in s,
          (1 / 2) * (‖c + P x‖ - ‖c‖) ^ 2 -
            (4 * theta * ‖P x‖) ^ 2 ∂ μCircle)
        <=
      ∫ x in s, (‖Q x + P x‖ - ‖Q x‖) ^ 2 ∂ μCircle := by
    refine MeasureTheory.integral_mono_ae hcombo_int.restrict hactual_int.restrict ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hs] with x hx
    rcases hfactor x hx with ⟨lam, hQx, hclose⟩
    have hclose_half : ‖lam - 1‖ <= 1 / 2 := hclose.trans htheta_le
    have hpoint :=
      defect_pointwise_const_center_compare_of_close
        (c := c) (lam := lam) (u := P x) hc hclose_half
    have herr :
        (4 * ‖lam - 1‖ * ‖P x‖) ^ 2 <=
          (4 * theta * ‖P x‖) ^ 2 := by
      have hleft_nonneg : 0 <= 4 * ‖lam - 1‖ * ‖P x‖ := by positivity
      have hright_nonneg : 0 <= 4 * theta * ‖P x‖ := by
        nlinarith [htheta_nonneg, norm_nonneg (P x)]
      have hmul : 4 * ‖lam - 1‖ * ‖P x‖ <=
          4 * theta * ‖P x‖ := by
        nlinarith [norm_nonneg (lam - 1), norm_nonneg (P x)]
      nlinarith
    calc
      (1 / 2) * (‖c + P x‖ - ‖c‖) ^ 2 -
          (4 * theta * ‖P x‖) ^ 2
          <=
        (1 / 2) * (‖c + P x‖ - ‖c‖) ^ 2 -
          (4 * ‖lam - 1‖ * ‖P x‖) ^ 2 := by
            nlinarith
      _ <= (‖lam * c + P x‖ - ‖lam * c‖) ^ 2 := hpoint
      _ = (‖Q x + P x‖ - ‖Q x‖) ^ 2 := by
            rw [hQx]
  calc
    (1 / 2) *
        ∫ x in s, (‖c + P x‖ - ‖c‖) ^ 2 ∂ μCircle -
        ∫ x in s, (4 * theta * ‖P x‖) ^ 2 ∂ μCircle
        =
      ∫ x in s,
          (1 / 2) * (‖c + P x‖ - ‖c‖) ^ 2 -
            (4 * theta * ‖P x‖) ^ 2 ∂ μCircle := by
          rw [MeasureTheory.integral_sub (hconst_int.const_mul (1 / 2)).restrict
            herr_int.restrict, MeasureTheory.integral_const_mul]
    _ <= ∫ x in s, (‖Q x + P x‖ - ‖Q x‖) ^ 2 ∂ μCircle := hmono

private theorem defect_setIntegral_const_center_compare_band
    (s : Set Circle) (hs : MeasurableSet s)
    (Q : Circle -> ℂ) (hQ : Continuous Q)
    (N : Nat) {L : Nat} (p : Fin L -> ℂ)
    {c : ℂ} {theta : ℝ}
    (hc : c ≠ 0) (htheta_nonneg : 0 <= theta)
    (htheta_le : theta <= 1 / 2)
    (hfactor : ∀ x ∈ s,
      ∃ lam : ℂ, Q x = lam * c ∧ ‖lam - 1‖ <= theta) :
    (1 / 2) *
        ∫ x in s, (‖c + bandPoly N p x‖ - ‖c‖) ^ 2 ∂ μCircle -
        ∫ x in s, (4 * theta * ‖bandPoly N p x‖) ^ 2 ∂ μCircle
      <=
        ∫ x in s,
          (‖Q x + bandPoly N p x‖ - ‖Q x‖) ^ 2 ∂ μCircle := by
  exact defect_setIntegral_const_center_compare
    s hs Q (bandPoly N p) hQ (continuous_bandPoly N p)
    hc htheta_nonneg htheta_le hfactor

/-- `circleBadConst`: circle Bad Const. -/
def circleBadConst (D : Nat) : Nat :=
  max 1 (max (82 * D) (2 ^ D - 1))

/-- `circleGoodBudget`: circle Good Budget. -/
def circleGoodBudget (D : Nat) : Nat :=
  64 * circleBadConst D

/-- `circleGap`: circle Gap. -/
def circleGap (D : Nat) : Nat :=
  max 37 (2 * circleBadConst D * circleGoodBudget D)

/-- `circleConst`: circle Const. -/
def circleConst (D : Nat) : ℝ := 64 * ((circleGap D : Nat) : ℝ) ^ 2

theorem circleBadConst_pos (D : Nat) : 1 <= circleBadConst D := by
  unfold circleBadConst
  exact le_max_left 1 (max (82 * D) (2 ^ D - 1))

private theorem circleBadConst_ge_succ_of_pos {D : Nat} (hD : 0 < D) :
    D + 1 <= circleBadConst D := by
  have hsucc_le : D + 1 <= 82 * D := by
    nlinarith
  have hbad_inner : 82 * D <= max (82 * D) (2 ^ D - 1) :=
    le_max_left (82 * D) (2 ^ D - 1)
  have hbad : 82 * D <= circleBadConst D := by
    unfold circleBadConst
    exact hbad_inner.trans (le_max_right 1 (max (82 * D) (2 ^ D - 1)))
  exact hsucc_le.trans hbad

theorem circleGoodBudget_pos (D : Nat) : 1 <= circleGoodBudget D := by
  unfold circleGoodBudget
  have hbad : 1 <= circleBadConst D := circleBadConst_pos D
  omega

theorem circleGap_ge_37 (D : Nat) : 37 <= circleGap D := by
  unfold circleGap
  exact le_max_left 37 (2 * circleBadConst D * circleGoodBudget D)

theorem circleGap_ge_bad_budget (D : Nat) :
    2 * circleBadConst D * circleGoodBudget D <= circleGap D := by
  unfold circleGap
  exact le_max_right 37 (2 * circleBadConst D * circleGoodBudget D)

theorem circleGap_pos (D : Nat) : 1 <= circleGap D := by
  exact (by norm_num : 1 <= 37).trans (circleGap_ge_37 D)

theorem circleConst_pos (D : Nat) : 0 < circleConst D := by
  dsimp [circleConst]
  have hgap : (0 : ℝ) < ((circleGap D : Nat) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 37) (circleGap_ge_37 D))
  positivity

theorem circleConst_ge_one (D : Nat) : 1 <= circleConst D := by
  dsimp [circleConst]
  have hgap : (1 : ℝ) <= ((circleGap D : Nat) : ℝ) := by
    exact_mod_cast circleGap_pos D
  nlinarith [sq_nonneg (((circleGap D : Nat) : ℝ) - 1)]

theorem thirty_two_le_circleConst (D : Nat) : (32 : ℝ) <= circleConst D := by
  dsimp [circleConst]
  have hgap : (1 : ℝ) <= ((circleGap D : Nat) : ℝ) := by
    exact_mod_cast circleGap_pos D
  nlinarith [sq_nonneg (((circleGap D : Nat) : ℝ) - 1)]

private theorem one_thousand_twenty_four_le_circleConst (D : Nat) :
    (1024 : ℝ) <= circleConst D := by
  dsimp [circleConst]
  have hgap : (37 : ℝ) <= ((circleGap D : Nat) : ℝ) := by
    exact_mod_cast circleGap_ge_37 D
  have hsq : (16 : ℝ) <= ((circleGap D : Nat) : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (((circleGap D : Nat) : ℝ) - 37)]
  nlinarith

private theorem Crot_le_circleConst_of_pos {D : Nat} (hD : 0 < D) :
    Crot <= circleConst D := by
  let _ := hD
  dsimp [Crot, circleConst]
  have hgap : (37 : ℝ) <= ((circleGap D : Nat) : ℝ) := by
    exact_mod_cast circleGap_ge_37 D
  have hsq : (4 : ℝ) <= ((circleGap D : Nat) : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (((circleGap D : Nat) : ℝ) - 37)]
  have hpi : Real.pi <= 4 := le_of_lt Real.pi_lt_four
  nlinarith

private noncomputable def polyOfCoeff {D : Nat} (q : Fin (D + 1) -> ℂ) :
    Polynomial ℂ :=
  ∑ n : Fin (D + 1), Polynomial.C (q n) * Polynomial.X ^ n.1

private theorem lowPoly_eq_polyOnCircle {D : Nat}
    (q : Fin (D + 1) -> ℂ) (x : Circle) :
    lowPoly q x = Polynomial.eval (zeta x) (polyOfCoeff q) := by
  simp [lowPoly, polyOfCoeff, circleChar_eq_zeta_pow,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow]

private theorem natDegree_polyOfCoeff_le {D : Nat}
    (q : Fin (D + 1) -> ℂ) :
    (polyOfCoeff q).natDegree <= D := by
  unfold polyOfCoeff
  refine Polynomial.natDegree_sum_le_of_forall_le
    (Finset.univ : Finset (Fin (D + 1)))
    (fun n : Fin (D + 1) => Polynomial.C (q n) * Polynomial.X ^ n.1) ?_
  intro n hn
  exact (Polynomial.natDegree_C_mul_X_pow_le (q n) n.1).trans
    (Nat.le_of_lt_succ n.2)

private theorem roots_card_polyOfCoeff_le {D : Nat}
    (q : Fin (D + 1) -> ℂ) :
    (polyOfCoeff q).roots.card <= D :=
  (Polynomial.card_roots' (polyOfCoeff q)).trans (natDegree_polyOfCoeff_le q)

private theorem roots_card_polyOfCoeff_eq_natDegree {D : Nat}
    (q : Fin (D + 1) -> ℂ) :
    (polyOfCoeff q).roots.card = (polyOfCoeff q).natDegree := by
  exact ((IsAlgClosed.splits (k := ℂ) (polyOfCoeff q)).natDegree_eq_card_roots).symm

private theorem coeff_polyOfCoeff {D : Nat}
    (q : Fin (D + 1) -> ℂ) (n : Fin (D + 1)) :
    (polyOfCoeff q).coeff n.1 = q n := by
  simp only [polyOfCoeff, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single n]
  · simp
  · intro b hb hbn
    have hne : n.1 ≠ b.1 := by
      intro hval
      exact hbn (Fin.ext hval.symm)
    simp [hne]
  · intro hn
    simp at hn

private theorem polyOfCoeff_ne_zero_of_ne_zero {D : Nat}
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) :
    polyOfCoeff q ≠ 0 := by
  intro hpoly
  apply hq
  funext n
  have hcoeff := congrArg (fun p : Polynomial ℂ => p.coeff n.1) hpoly
  simpa [coeff_polyOfCoeff q n] using hcoeff

private theorem leadingCoeff_polyOfCoeff_ne_zero_of_ne_zero {D : Nat}
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) :
    (polyOfCoeff q).leadingCoeff ≠ 0 := by
  exact Polynomial.leadingCoeff_ne_zero.mpr (polyOfCoeff_ne_zero_of_ne_zero hq)

private theorem natDegree_polyOfCoeff_pos_of_nonconst {D : Nat}
    {q : Fin (D + 1) -> ℂ}
    (hnonconst_coeff : ∃ n : Fin (D + 1), n.1 ≠ 0 ∧ q n ≠ 0) :
    0 < (polyOfCoeff q).natDegree := by
  rcases hnonconst_coeff with ⟨n, hn_pos, hnq⟩
  have hcoeff : (polyOfCoeff q).coeff n.1 ≠ 0 := by
    simpa [coeff_polyOfCoeff q n] using hnq
  exact lt_of_lt_of_le (Nat.pos_of_ne_zero hn_pos)
    (Polynomial.le_natDegree_of_ne_zero hcoeff)

private theorem exists_mem_roots_polyOfCoeff_of_nonconst {D : Nat}
    {q : Fin (D + 1) -> ℂ}
    (hnonconst_coeff : ∃ n : Fin (D + 1), n.1 ≠ 0 ∧ q n ≠ 0) :
    ∃ ζ : ℂ, ζ ∈ (polyOfCoeff q).roots := by
  have hdeg : 0 < (polyOfCoeff q).natDegree :=
    natDegree_polyOfCoeff_pos_of_nonconst hnonconst_coeff
  have hcard : 0 < (polyOfCoeff q).roots.card := by
    simpa [roots_card_polyOfCoeff_eq_natDegree q] using hdeg
  exact Multiset.card_pos_iff_exists_mem.mp hcard

private theorem norm_leadingCoeff_polyOfCoeff_pos_of_ne_zero {D : Nat}
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) :
    0 < ‖(polyOfCoeff q).leadingCoeff‖ := by
  exact norm_pos_iff.mpr (leadingCoeff_polyOfCoeff_ne_zero_of_ne_zero hq)

private theorem lowPoly_eq_leadingCoeff_mul_roots {D : Nat}
    (q : Fin (D + 1) -> ℂ) (x : Circle) :
    lowPoly q x =
      (polyOfCoeff q).leadingCoeff *
        ((polyOfCoeff q).roots.map fun ζ => zeta x - ζ).prod := by
  rw [lowPoly_eq_polyOnCircle]
  exact (IsAlgClosed.splits (k := ℂ) (polyOfCoeff q)).eval_eq_prod_roots (zeta x)

private theorem norm_lowPoly_eq_leadingCoeff_mul_roots {D : Nat}
    (q : Fin (D + 1) -> ℂ) (x : Circle) :
    ‖lowPoly q x‖ =
      ‖(polyOfCoeff q).leadingCoeff‖ *
        ((polyOfCoeff q).roots.map fun ζ => ‖zeta x - ζ‖).prod := by
  rw [lowPoly_eq_leadingCoeff_mul_roots q x, norm_mul]
  congr 1
  induction (polyOfCoeff q).roots using Multiset.induction_on with
  | empty =>
      simp
  | cons ζ roots ih =>
      simp [ih]

private theorem complex_multiset_prod_norm_le_perturbed
    (s : Multiset ℂ) (a b : ℂ -> ℂ) {eps : ℝ} (heps : 0 <= eps)
    (h : ∀ ζ ∈ s, ‖b ζ - a ζ‖ <= eps * ‖a ζ‖) :
    ‖(s.map b).prod‖ <=
      (1 + eps) ^ s.card * (s.map fun ζ => ‖a ζ‖).prod := by
  induction s using Multiset.induction_on with
  | empty =>
      simp
  | cons ζ s ih =>
      have hζ : ‖b ζ - a ζ‖ <= eps * ‖a ζ‖ := h ζ (by simp)
      have hs : ∀ ξ ∈ s, ‖b ξ - a ξ‖ <= eps * ‖a ξ‖ := by
        intro ξ hξ
        exact h ξ (by simp [hξ])
      have ih' := ih hs
      have hbζ : ‖b ζ‖ <= (1 + eps) * ‖a ζ‖ := by
        calc
          ‖b ζ‖ = ‖a ζ + (b ζ - a ζ)‖ := by
            congr 1
            ring
          _ <= ‖a ζ‖ + ‖b ζ - a ζ‖ := norm_add_le _ _
          _ <= ‖a ζ‖ + eps * ‖a ζ‖ := by nlinarith
          _ = (1 + eps) * ‖a ζ‖ := by ring
      have hprod_nonneg : 0 <= ‖(s.map b).prod‖ := norm_nonneg _
      have hcoef_nonneg : 0 <= (1 + eps) * ‖a ζ‖ := by positivity
      calc
        ‖((ζ ::ₘ s).map b).prod‖ =
            ‖b ζ‖ * ‖(s.map b).prod‖ := by
          simp [Multiset.prod_cons]
        _ <=
            ((1 + eps) * ‖a ζ‖) *
              ((1 + eps) ^ s.card *
                (s.map fun ζ => ‖a ζ‖).prod) := by
          exact mul_le_mul hbζ ih' hprod_nonneg hcoef_nonneg
        _ =
            (1 + eps) ^ (ζ ::ₘ s).card *
              (((ζ ::ₘ s).map fun ζ => ‖a ζ‖).prod) := by
          simp [Multiset.prod_cons]
          ring

private theorem complex_multiset_prod_sub_norm_le_perturbed
    (s : Multiset ℂ) (a b : ℂ -> ℂ) {eps : ℝ} (heps : 0 <= eps)
    (h : ∀ ζ ∈ s, ‖b ζ - a ζ‖ <= eps * ‖a ζ‖) :
    ‖(s.map b).prod - (s.map a).prod‖ <=
      ((1 + eps) ^ s.card - 1) *
        (s.map fun ζ => ‖a ζ‖).prod := by
  induction s using Multiset.induction_on with
  | empty =>
      simp
  | cons ζ s ih =>
      have hζ : ‖b ζ - a ζ‖ <= eps * ‖a ζ‖ := h ζ (by simp)
      have hs : ∀ ξ ∈ s, ‖b ξ - a ξ‖ <= eps * ‖a ξ‖ := by
        intro ξ hξ
        exact h ξ (by simp [hξ])
      have ih' := ih hs
      have hprod_b := complex_multiset_prod_norm_le_perturbed s a b heps hs
      let A : ℝ := (s.map fun ζ => ‖a ζ‖).prod
      let r : ℝ := 1 + eps
      have hr_nonneg : 0 <= r := by dsimp [r]; linarith
      have hA_nonneg : 0 <= A := by
        dsimp [A]
        refine Multiset.prod_nonneg
          (s := s.map (fun ζ : ℂ => ‖a ζ‖)) ?_
        intro x hx
        rcases Multiset.mem_map.mp hx with ⟨ζ, _hζs, rfl⟩
        exact norm_nonneg (a ζ)
      have hpow_ge_one : 1 <= r ^ s.card := by
        have hr_ge_one : 1 <= r := by dsimp [r]; linarith
        exact one_le_pow₀ (n := s.card) hr_ge_one
      have hdecomp :
          ((ζ ::ₘ s).map b).prod - ((ζ ::ₘ s).map a).prod =
            (b ζ - a ζ) * (s.map b).prod +
              a ζ * ((s.map b).prod - (s.map a).prod) := by
        simp [Multiset.prod_cons]
        ring
      calc
        ‖((ζ ::ₘ s).map b).prod - ((ζ ::ₘ s).map a).prod‖
            =
              ‖(b ζ - a ζ) * (s.map b).prod +
                a ζ * ((s.map b).prod - (s.map a).prod)‖ := by
          rw [hdecomp]
        _ <=
            ‖(b ζ - a ζ) * (s.map b).prod‖ +
              ‖a ζ * ((s.map b).prod - (s.map a).prod)‖ :=
          norm_add_le _ _
        _ =
            ‖b ζ - a ζ‖ * ‖(s.map b).prod‖ +
              ‖a ζ‖ *
                ‖(s.map b).prod - (s.map a).prod‖ := by
          rw [norm_mul, norm_mul]
        _ <=
            (eps * ‖a ζ‖) * (r ^ s.card * A) +
              ‖a ζ‖ * ((r ^ s.card - 1) * A) := by
          have hterm1_nonneg : 0 <= ‖(s.map b).prod‖ := norm_nonneg _
          have hepsa_nonneg : 0 <= eps * ‖a ζ‖ := by positivity
          have hmul1 :
              ‖b ζ - a ζ‖ * ‖(s.map b).prod‖ <=
                (eps * ‖a ζ‖) * (r ^ s.card * A) :=
            mul_le_mul hζ (by simpa [A, r] using hprod_b)
              hterm1_nonneg hepsa_nonneg
          have hmul2 :
              ‖a ζ‖ *
                  ‖(s.map b).prod - (s.map a).prod‖ <=
                ‖a ζ‖ * ((r ^ s.card - 1) * A) :=
            mul_le_mul_of_nonneg_left
              (by simpa [A, r] using ih') (norm_nonneg _)
          nlinarith
        _ =
            ((1 + eps) ^ (ζ ::ₘ s).card - 1) *
              (((ζ ::ₘ s).map fun ζ => ‖a ζ‖).prod) := by
          simp [Multiset.prod_cons, A, r]
          ring

private theorem lowPoly_relative_oscillation_of_root_factor_bound
    {D : Nat} (q : Fin (D + 1) -> ℂ) (x y : Circle)
    {eps theta : ℝ} (heps : 0 <= eps)
    (htheta :
      (1 + eps) ^ (polyOfCoeff q).roots.card - 1 <= theta)
    (hroot : ∀ ζ ∈ (polyOfCoeff q).roots,
      ‖(zeta x - ζ) - (zeta y - ζ)‖ <=
        eps * ‖zeta y - ζ‖) :
    ‖lowPoly q x - lowPoly q y‖ <= theta * ‖lowPoly q y‖ := by
  let roots := (polyOfCoeff q).roots
  let lc := (polyOfCoeff q).leadingCoeff
  let a : ℂ -> ℂ := fun ζ => zeta y - ζ
  let b : ℂ -> ℂ := fun ζ => zeta x - ζ
  have hprod :
      ‖(roots.map b).prod - (roots.map a).prod‖ <=
        ((1 + eps) ^ roots.card - 1) *
          (roots.map fun ζ => ‖a ζ‖).prod := by
    exact complex_multiset_prod_sub_norm_le_perturbed
      roots a b heps (by simpa [roots, a, b] using hroot)
  have hprod_nonneg :
      0 <= (roots.map fun ζ => ‖a ζ‖).prod := by
    refine Multiset.prod_nonneg
      (s := roots.map fun ζ : ℂ => ‖a ζ‖) ?_
    intro r hr
    rcases Multiset.mem_map.mp hr with ⟨ζ, _hζ, rfl⟩
    exact norm_nonneg (a ζ)
  have htheta_mul :
      ((1 + eps) ^ roots.card - 1) *
          (roots.map fun ζ => ‖a ζ‖).prod <=
        theta * (roots.map fun ζ => ‖a ζ‖).prod :=
    mul_le_mul_of_nonneg_right (by simpa [roots] using htheta) hprod_nonneg
  have hdiff :
      lowPoly q x - lowPoly q y =
        lc * ((roots.map b).prod - (roots.map a).prod) := by
    simp [roots, lc, a, b, lowPoly_eq_leadingCoeff_mul_roots]
    ring
  calc
    ‖lowPoly q x - lowPoly q y‖
        = ‖lc‖ * ‖(roots.map b).prod - (roots.map a).prod‖ := by
          rw [hdiff, norm_mul]
    _ <=
        ‖lc‖ *
          (((1 + eps) ^ roots.card - 1) *
            (roots.map fun ζ => ‖a ζ‖).prod) :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ <= ‖lc‖ * (theta * (roots.map fun ζ => ‖a ζ‖).prod) :=
        mul_le_mul_of_nonneg_left htheta_mul (norm_nonneg _)
    _ = theta * ‖lowPoly q y‖ := by
        rw [norm_lowPoly_eq_leadingCoeff_mul_roots q y]
        simp [roots, lc, a]
        ring

private theorem one_add_eps_pow_le_one_add_two_nat_mul
    {eps : ℝ} (heps : 0 <= eps) :
    ∀ n : Nat, 2 * (n : ℝ) * eps <= 1 ->
      (1 + eps) ^ n <= 1 + 2 * (n : ℝ) * eps
  | 0, _ => by simp
  | n + 1, hsmall => by
      have hnsmall : 2 * (n : ℝ) * eps <= 1 := by
        have hnle : (n : ℝ) <= (n + 1 : Nat) := by
          exact_mod_cast Nat.le_succ n
        nlinarith [mul_le_mul_of_nonneg_right hnle heps]
      have ih := one_add_eps_pow_le_one_add_two_nat_mul heps n hnsmall
      have hfac_nonneg : 0 <= 1 + eps := by linarith
      calc
        (1 + eps) ^ (n + 1) = (1 + eps) ^ n * (1 + eps) := by
          rw [pow_succ]
        _ <= (1 + 2 * (n : ℝ) * eps) * (1 + eps) :=
          mul_le_mul_of_nonneg_right ih hfac_nonneg
        _ = 1 + (2 * (n : ℝ) + 1) * eps +
              2 * (n : ℝ) * eps ^ 2 := by
          ring
        _ <= 1 + (2 * (n : ℝ) + 2) * eps := by
          have hquad : 2 * (n : ℝ) * eps ^ 2 <= eps := by
            calc
              2 * (n : ℝ) * eps ^ 2 =
                  (2 * (n : ℝ) * eps) * eps := by
                ring
              _ <= 1 * eps := mul_le_mul_of_nonneg_right hnsmall heps
              _ = eps := by ring
          linarith [hquad]
        _ = 1 + 2 * ((n + 1 : Nat) : ℝ) * eps := by
          rw [Nat.cast_add, Nat.cast_one]
          ring

private theorem one_add_eps_pow_sub_one_le_two_nat_mul
    {eps : ℝ} (heps : 0 <= eps) {n : Nat}
    (hsmall : 2 * (n : ℝ) * eps <= 1) :
    (1 + eps) ^ n - 1 <= 2 * (n : ℝ) * eps := by
  have h := one_add_eps_pow_le_one_add_two_nat_mul heps n hsmall
  linarith

private theorem one_add_eps_pow_sub_one_le_of_nat_le
    {m D : Nat} {eps theta : ℝ} (heps : 0 <= eps) (hmD : m <= D)
    (hsmallD : 2 * (D : ℝ) * eps <= 1)
    (hthetaD : 2 * (D : ℝ) * eps <= theta) :
    (1 + eps) ^ m - 1 <= theta := by
  have hmDreal : (m : ℝ) <= (D : ℝ) := by exact_mod_cast hmD
  have hmleD : 2 * (m : ℝ) * eps <= 2 * (D : ℝ) * eps := by
    nlinarith [mul_le_mul_of_nonneg_right hmDreal heps]
  have hsmallm : 2 * (m : ℝ) * eps <= 1 := hmleD.trans hsmallD
  have hmtheta : 2 * (m : ℝ) * eps <= theta := hmleD.trans hthetaD
  exact (one_add_eps_pow_sub_one_le_two_nat_mul heps hsmallm).trans hmtheta

private theorem one_add_degree_eps_pow_sub_one_le_one_div_sixtyfour
    {m D : Nat} (hmD : m <= D) :
    (1 + (1 / (128 * ((D + 1 : Nat) : ℝ)))) ^ m - 1 <=
      (1 / 64 : ℝ) := by
  let eps : ℝ := 1 / (128 * ((D + 1 : Nat) : ℝ))
  have hD1pos : 0 < ((D + 1 : Nat) : ℝ) := by
    exact_mod_cast Nat.succ_pos D
  have heps : 0 <= eps := by
    dsimp [eps]
    positivity
  have hDleD1 : (D : ℝ) <= ((D + 1 : Nat) : ℝ) := by
    exact_mod_cast Nat.le_succ D
  have hthetaD : 2 * (D : ℝ) * eps <= (1 / 64 : ℝ) := by
    dsimp [eps]
    field_simp [hD1pos.ne']
    nlinarith
  have hsmallD : 2 * (D : ℝ) * eps <= 1 := by
    have h : (1 / 64 : ℝ) <= 1 := by norm_num
    exact hthetaD.trans h
  simpa [eps] using
    one_add_eps_pow_sub_one_le_of_nat_le (m := m) (D := D)
      (eps := eps) (theta := (1 / 64 : ℝ)) heps hmD hsmallD hthetaD

private theorem root_product_theta_bound_one_div_sixtyfour {D : Nat}
    (q : Fin (D + 1) -> ℂ) :
    (1 + (1 / (128 * ((D + 1 : Nat) : ℝ)))) ^
        (polyOfCoeff q).roots.card - 1 <= (1 / 64 : ℝ) := by
  exact one_add_degree_eps_pow_sub_one_le_one_div_sixtyfour
    (roots_card_polyOfCoeff_le q)

private theorem lowPoly_norm_ge_of_roots_dist_ge {D : Nat}
    (q : Fin (D + 1) -> ℂ) (x : Circle) {delta : ℝ}
    (hdelta : 0 <= delta)
    (hdist : ∀ ζ ∈ (polyOfCoeff q).roots, delta <= ‖zeta x - ζ‖) :
    ‖(polyOfCoeff q).leadingCoeff‖ *
        delta ^ (polyOfCoeff q).roots.card <= ‖lowPoly q x‖ := by
  rw [norm_lowPoly_eq_leadingCoeff_mul_roots q x]
  have hprod :
      ((polyOfCoeff q).roots.map fun _ : ℂ => delta).prod <=
        ((polyOfCoeff q).roots.map fun ζ => ‖zeta x - ζ‖).prod := by
    exact Multiset.prod_map_le_prod_map₀
      (s := (polyOfCoeff q).roots)
      (f := fun _ : ℂ => delta)
      (g := fun ζ => ‖zeta x - ζ‖)
      (by intro ζ hζ; exact hdelta)
      (by intro ζ hζ; exact hdist ζ hζ)
  have hpow :
      ((polyOfCoeff q).roots.map fun _ : ℂ => delta).prod =
        delta ^ (polyOfCoeff q).roots.card := by
    simp
  exact mul_le_mul_of_nonneg_left (by simpa [hpow] using hprod) (norm_nonneg _)

private noncomputable def badCarrierIndices
    (N : Nat) (roots : Multiset ℂ) (delta : ℝ) : Finset (Fin N) :=
  by
    classical
    exact Finset.univ.filter fun k : Fin N =>
      ∃ ζ : ℂ, ζ ∈ roots ∧
        ∃ x : Circle, x ∈ arcSet (carrierArc N k) ∧ ‖zeta x - ζ‖ < delta

private noncomputable def badCarrierIndicesForRoot
    (N : Nat) (ζ : ℂ) (delta : ℝ) : Finset (Fin N) :=
  by
    classical
    exact Finset.univ.filter fun k : Fin N =>
      ∃ x : Circle, x ∈ arcSet (carrierArc N k) ∧ ‖zeta x - ζ‖ < delta

private noncomputable def goodCarrierIndices
    (N : Nat) (roots : Multiset ℂ) (delta : ℝ) : Finset (Fin N) :=
  (Finset.univ : Finset (Fin N)) \ badCarrierIndices N roots delta

private theorem mem_goodCarrierIndices
    {N : Nat} {roots : Multiset ℂ} {delta : ℝ} {k : Fin N} :
    k ∈ goodCarrierIndices N roots delta ↔
      k ∉ badCarrierIndices N roots delta := by
  classical
  simp [goodCarrierIndices]

private theorem goodCarrierIndices_not_bad
    {N : Nat} {roots : Multiset ℂ} {delta : ℝ}
    {k : Fin N} (hk : k ∈ goodCarrierIndices N roots delta) :
    k ∉ badCarrierIndices N roots delta :=
  mem_goodCarrierIndices.mp hk

private theorem goodCarrier_root_distance_ge
    {N : Nat} {roots : Multiset ℂ} {delta : ℝ} {k : Fin N}
    (hgood : k ∉ badCarrierIndices N roots delta) :
    ∀ ζ ∈ roots, ∀ x ∈ arcSet (carrierArc N k),
      delta <= ‖zeta x - ζ‖ := by
  classical
  intro ζ hζ x hx
  by_contra hnot
  have hlt : ‖zeta x - ζ‖ < delta := lt_of_not_ge hnot
  have hbad : k ∈ badCarrierIndices N roots delta := by
    classical
    unfold badCarrierIndices
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ k, ⟨ζ, hζ, x, hx, hlt⟩⟩
  exact hgood hbad

private theorem badCarrierIndices_card_le
    (N : Nat) (roots : Multiset ℂ) (delta : ℝ) :
    (badCarrierIndices N roots delta).card <= N := by
  classical
  calc
    (badCarrierIndices N roots delta).card <=
        (Finset.univ : Finset (Fin N)).card := by
          unfold badCarrierIndices
          exact Finset.card_filter_le _ _
    _ = N := by simp

private theorem card_biUnion_le_sum_card
    {α β : Type} [DecidableEq β]
    (s : Finset α) (t : α -> Finset β) :
    (s.biUnion t).card <= ∑ a ∈ s, (t a).card := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      exact (Finset.card_union_le (t a) (s.biUnion t)).trans
        (Nat.add_le_add_left ih (t a).card)

private theorem badCarrierIndices_subset_roots_biUnion
    (N : Nat) (roots : Multiset ℂ) (delta : ℝ) :
    badCarrierIndices N roots delta ⊆
      roots.toFinset.biUnion
        (fun ζ => badCarrierIndicesForRoot N ζ delta) := by
  classical
  intro k hk
  unfold badCarrierIndices at hk
  rcases Finset.mem_filter.mp hk with ⟨_hk_univ, ζ, hζ, x, hx_arc, hx_close⟩
  rw [Finset.mem_biUnion]
  refine ⟨ζ, ?_, ?_⟩
  · simpa using hζ
  · unfold badCarrierIndicesForRoot
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ k, ⟨x, hx_arc, hx_close⟩⟩

private theorem badCarrierIndices_card_le_roots_card_mul
    (N : Nat) (roots : Multiset ℂ) (delta : ℝ) (M : Nat)
    (hM : ∀ ζ ∈ roots, (badCarrierIndicesForRoot N ζ delta).card <= M) :
    (badCarrierIndices N roots delta).card <= roots.card * M := by
  classical
  have hsub := badCarrierIndices_subset_roots_biUnion N roots delta
  have hcard_union :
      (roots.toFinset.biUnion
        (fun ζ => badCarrierIndicesForRoot N ζ delta)).card <=
        ∑ ζ ∈ roots.toFinset, (badCarrierIndicesForRoot N ζ delta).card :=
    card_biUnion_le_sum_card roots.toFinset
      (fun ζ => badCarrierIndicesForRoot N ζ delta)
  have hsum :
      ∑ ζ ∈ roots.toFinset, (badCarrierIndicesForRoot N ζ delta).card <=
        ∑ _ζ ∈ roots.toFinset, M := by
    refine Finset.sum_le_sum ?_
    intro ζ hζ
    exact hM ζ (by simpa using hζ)
  have htoFinset : roots.toFinset.card <= roots.card :=
    Multiset.toFinset_card_le roots
  calc
    (badCarrierIndices N roots delta).card <=
        (roots.toFinset.biUnion
          (fun ζ => badCarrierIndicesForRoot N ζ delta)).card :=
      Finset.card_le_card hsub
    _ <= ∑ ζ ∈ roots.toFinset, (badCarrierIndicesForRoot N ζ delta).card :=
      hcard_union
    _ <= ∑ _ζ ∈ roots.toFinset, M := hsum
    _ = roots.toFinset.card * M := by
      rw [Finset.sum_const, nsmul_eq_mul]
      rfl
    _ <= roots.card * M := Nat.mul_le_mul_right M htoFinset

private theorem badCarrierIndices_card_le_of_forall_root_card_le
    {D N B : Nat} {roots : Multiset ℂ} {delta : ℝ}
    (hroots : roots.card <= D)
    (hroot : ∀ ζ ∈ roots,
      (badCarrierIndicesForRoot N ζ delta).card <= 82 * B) :
    (badCarrierIndices N roots delta).card <= circleBadConst D * B := by
  have hglobal :=
    badCarrierIndices_card_le_roots_card_mul
      N roots delta (82 * B) hroot
  have hmul_roots : roots.card * (82 * B) <= D * (82 * B) :=
    Nat.mul_le_mul_right (82 * B) hroots
  have hrewrite : D * (82 * B) = (82 * D) * B := by ring
  have hbad_inner : 82 * D <= max (82 * D) (2 ^ D - 1) :=
    le_max_left (82 * D) (2 ^ D - 1)
  have hbad : 82 * D <= circleBadConst D := by
    unfold circleBadConst
    exact hbad_inner.trans (le_max_right 1 (max (82 * D) (2 ^ D - 1)))
  have hmul_bad : (82 * D) * B <= circleBadConst D * B :=
    Nat.mul_le_mul_right B hbad
  calc
    (badCarrierIndices N roots delta).card <= roots.card * (82 * B) :=
      hglobal
    _ <= D * (82 * B) := hmul_roots
    _ = (82 * D) * B := hrewrite
    _ <= circleBadConst D * B := hmul_bad

private def carrierBase {N : Nat} (k : Fin N) : Circle :=
  arcParam (carrierArc N k) 0

private theorem carrierBase_mem {N : Nat} (k : Fin N) :
    carrierBase k ∈ arcSet (carrierArc N k) := by
  dsimp [carrierBase]
  exact intervalParam_mem_arc (carrierArc N k) 0
    ⟨le_rfl, by norm_num⟩

private theorem badCarrierIndices_eq_univ_of_unit_root_of_two_lt_delta
    {N : Nat} {roots : Multiset ℂ} {delta : ℝ} {ζ : ℂ}
    (hζ : ζ ∈ roots) (hζnorm : ‖ζ‖ = 1) (hdelta : 2 < delta) :
    badCarrierIndices N roots delta = (Finset.univ : Finset (Fin N)) := by
  classical
  ext k
  constructor
  · intro _
    exact Finset.mem_univ k
  · intro _
    unfold badCarrierIndices
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ k, ?_⟩
    refine ⟨ζ, hζ, carrierBase k, carrierBase_mem k, ?_⟩
    calc
      ‖zeta (carrierBase k) - ζ‖ <=
          ‖zeta (carrierBase k)‖ + ‖ζ‖ := norm_sub_le _ _
      _ = 2 := by
          rw [norm_zeta, hζnorm]
          norm_num
      _ < delta := hdelta

private theorem carrierArc_length_pos_wip {N : Nat} (k : Fin N) :
    0 < arcLength (carrierArc N k) := by
  rw [carrierArc_length k]
  have hNnat : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le k.1) k.2
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNnat
  positivity

private theorem carrierArc_left_nonneg_wip {N : Nat} (k : Fin N) :
    0 <= (carrierArc N k).left := by
  unfold carrierArc
  positivity

private theorem carrierArc_right_le_period_wip {N : Nat} (k : Fin N) :
    (carrierArc N k).right <= 2 * Real.pi := by
  unfold carrierArc
  have hNnat : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le k.1) k.2
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNnat
  have hle : ((k.1 + 1 : Nat) : ℝ) <= (N : ℝ) := by
    exact_mod_cast k.2
  have hT_nonneg : 0 <= (2 * Real.pi : ℝ) := by positivity
  calc
    (2 * Real.pi) * ((k.1 + 1 : Nat) : ℝ) / (N : ℝ)
        <= (2 * Real.pi) * (N : ℝ) / (N : ℝ) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hle hT_nonneg) (le_of_lt hNpos)
    _ = 2 * Real.pi := by
      field_simp [ne_of_gt hNpos]

private theorem carrierArc_left_lt_right_wip {N : Nat} (k : Fin N) :
    (carrierArc N k).left < (carrierArc N k).right := by
  have hlen := carrierArc_length_pos_wip k
  dsimp [arcLength] at hlen
  linarith

private theorem carrierArc_arcSet_eq_mk_image_Icc_wip {N : Nat} (k : Fin N) :
    arcSet (carrierArc N k) =
      QuotientAddGroup.mk ''
        Set.Icc ((carrierArc N k).left) ((carrierArc N k).right) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨t, ht, rfl⟩
    refine ⟨(carrierArc N k).left + t * arcLength (carrierArc N k), ?_, rfl⟩
    have hlen_nonneg : 0 <= arcLength (carrierArc N k) :=
      le_of_lt (carrierArc_length_pos_wip k)
    constructor
    · dsimp [arcLength] at hlen_nonneg ⊢
      nlinarith [ht.1, hlen_nonneg]
    · dsimp [arcLength] at hlen_nonneg ⊢
      nlinarith [ht.2, hlen_nonneg]
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    let t : ℝ := (y - (carrierArc N k).left) / arcLength (carrierArc N k)
    refine ⟨t, ?_, ?_⟩
    · have hlen_pos : 0 < arcLength (carrierArc N k) :=
        carrierArc_length_pos_wip k
      constructor
      · dsimp [t]
        exact div_nonneg (sub_nonneg.mpr hy.1) (le_of_lt hlen_pos)
      · dsimp [t]
        rw [div_le_one hlen_pos]
        dsimp [arcLength]
        linarith [hy.2]
    · dsimp [arcParam, t]
      have hlen_pos : 0 < arcLength (carrierArc N k) :=
        carrierArc_length_pos_wip k
      apply congrArg (fun r : ℝ => (QuotientAddGroup.mk r : Circle))
      field_simp [ne_of_gt hlen_pos]
      ring_nf

private theorem circle_dist_mk_le_abs_sub (a b : ℝ) :
    dist ((QuotientAddGroup.mk a : Circle)) (QuotientAddGroup.mk b) <= |a - b| := by
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
  have h : ‖((a - b : ℝ) : Circle)‖ <= ‖a - b‖ :=
    QuotientAddGroup.norm_mk_le_norm
  simpa [Real.norm_eq_abs] using h

private theorem addCircle_norm_mk_le_pi_div_two_chord (theta : ℝ) :
    ‖((QuotientAddGroup.mk theta : Circle))‖ <=
      (Real.pi / 2) * ‖Complex.exp (Complex.I * theta) - 1‖ := by
  let m : ℤ := round (((2 * Real.pi) : ℝ)⁻¹ * theta)
  let phi : ℝ := theta - (m : ℝ) * (2 * Real.pi)
  have hnorm : ‖((QuotientAddGroup.mk theta : Circle))‖ = |phi| := by
    simpa [Circle, phi, m] using
      (AddCircle.norm_eq (2 * Real.pi) (x := theta))
  have hTpos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hround := abs_sub_round (((2 * Real.pi) : ℝ)⁻¹ * theta)
  have hphi_scale :
      phi = (2 * Real.pi) * (((2 * Real.pi) : ℝ)⁻¹ * theta - (m : ℝ)) := by
    dsimp [phi, m]
    field_simp [hTpos.ne']
  have hphi_le_pi : |phi| <= Real.pi := by
    calc
      |phi| =
          (2 * Real.pi) * |((2 * Real.pi) : ℝ)⁻¹ * theta - (m : ℝ)| := by
        rw [hphi_scale, abs_mul, abs_of_pos hTpos]
      _ <= (2 * Real.pi) * (1 / 2 : ℝ) := by
        exact mul_le_mul_of_nonneg_left (by simpa [m] using hround) (le_of_lt hTpos)
      _ = Real.pi := by ring
  have hhalf : |phi / 2| <= Real.pi / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hphi_le_pi]
  have h_abs_half : |phi / 2| = |phi| / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hjordan := Real.mul_abs_le_abs_sin hhalf
  have hsin_bound : |phi| <= Real.pi * |Real.sin (phi / 2)| := by
    have hj' : (2 / Real.pi) * (|phi| / 2) <= |Real.sin (phi / 2)| := by
      simpa [h_abs_half] using hjordan
    have hjmul := mul_le_mul_of_nonneg_right hj' (le_of_lt Real.pi_pos)
    have hleft : ((2 / Real.pi) * (|phi| / 2)) * Real.pi = |phi| := by
      field_simp [Real.pi_ne_zero]
    have hright :
        |Real.sin (phi / 2)| * Real.pi =
          Real.pi * |Real.sin (phi / 2)| := by ring
    simpa [hleft, hright] using hjmul
  have hchord_phi :
      ‖Complex.exp (Complex.I * phi) - 1‖ = 2 * |Real.sin (phi / 2)| := by
    rw [Complex.norm_exp_I_mul_ofReal_sub_one]
    rw [Real.norm_eq_abs]
    simp [abs_mul]
  have hperiod : Complex.exp (phi * Complex.I) = Complex.exp (theta * Complex.I) := by
    have hperiod0 :
        Complex.exp ((theta - m • (2 * Real.pi)) * Complex.I) =
          Complex.exp (theta * Complex.I) :=
      Complex.exp_mul_I_periodic.sub_zsmul_eq m
    simpa [phi, m, zsmul_eq_mul] using hperiod0
  have hchord_eq :
      ‖Complex.exp (Complex.I * theta) - 1‖ =
        ‖Complex.exp (Complex.I * phi) - 1‖ := by
    rw [mul_comm Complex.I theta, mul_comm Complex.I phi, hperiod]
  rw [hnorm, hchord_eq, hchord_phi]
  nlinarith [hsin_bound]

private theorem zeta_mk_wip (theta : ℝ) :
    zeta (QuotientAddGroup.mk theta : Circle) = Complex.exp (Complex.I * theta) := by
  unfold zeta
  rw [AddCircle.toCircle_apply_mk]
  have hT : (2 * Real.pi) / (2 * Real.pi) = (1 : ℝ) := by
    field_simp [Real.pi_ne_zero]
  rw [hT, one_mul, Circle.coe_exp]
  rw [mul_comm]

private theorem zeta_mk_sub_norm_eq (a b : ℝ) :
    ‖zeta (QuotientAddGroup.mk a : Circle) -
        zeta (QuotientAddGroup.mk b : Circle)‖ =
      ‖Complex.exp (Complex.I * (a - b)) - 1‖ := by
  rw [zeta_mk_wip a, zeta_mk_wip b]
  have hdiff :
      Complex.exp (Complex.I * (a : ℂ)) - Complex.exp (Complex.I * (b : ℂ)) =
        (Complex.exp (Complex.I * ((a : ℂ) - (b : ℂ))) - 1) *
          Complex.exp (Complex.I * (b : ℂ)) := by
    rw [show Complex.I * (a : ℂ) =
        Complex.I * ((a : ℂ) - (b : ℂ)) + Complex.I * (b : ℂ) by ring]
    rw [Complex.exp_add]
    ring
  rw [hdiff, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]

private theorem circle_dist_le_pi_div_two_mul_chord (x y : Circle) :
    dist x y <= (Real.pi / 2) * ‖zeta x - zeta y‖ := by
  induction x using QuotientAddGroup.induction_on
  induction y using QuotientAddGroup.induction_on
  rename_i a b
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
  have hbase := addCircle_norm_mk_le_pi_div_two_chord (a - b)
  rw [zeta_mk_sub_norm_eq a b]
  simpa using hbase

private theorem carrierArc_dist_le_length {N : Nat} (k : Fin N) :
    ∀ x ∈ arcSet (carrierArc N k), ∀ y ∈ arcSet (carrierArc N k),
      dist x y <= arcLength (carrierArc N k) := by
  intro x hx y hy
  rw [carrierArc_arcSet_eq_mk_image_Icc_wip k] at hx hy
  rcases hx with ⟨a, ha, rfl⟩
  rcases hy with ⟨b, hb, rfl⟩
  have hdist := circle_dist_mk_le_abs_sub a b
  have habs : |a - b| <= arcLength (carrierArc N k) := by
    dsimp [arcLength]
    apply abs_le.mpr
    constructor
    · linarith [ha.1, hb.2]
    · linarith [ha.2, hb.1]
  exact hdist.trans habs

private theorem carrierArc_arcSet_eq_mk_image_Ioc_union_left_wip
    {N : Nat} (k : Fin N) :
    arcSet (carrierArc N k) =
      (QuotientAddGroup.mk ''
        Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)) ∪
        {(QuotientAddGroup.mk ((carrierArc N k).left) : Circle)} := by
  rw [carrierArc_arcSet_eq_mk_image_Icc_wip k]
  have hIcc :
      Set.Icc ((carrierArc N k).left) ((carrierArc N k).right) =
        Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right) ∪
          {((carrierArc N k).left)} := by
    ext y
    constructor
    · intro hy
      by_cases hleft : y = (carrierArc N k).left
      · exact Or.inr hleft
      · exact Or.inl ⟨lt_of_le_of_ne hy.1 (Ne.symm hleft), hy.2⟩
    · intro hy
      rcases hy with hy | hy
      · exact ⟨le_of_lt hy.1, hy.2⟩
      · rw [Set.mem_singleton_iff.mp hy]
        exact ⟨le_rfl, le_of_lt (carrierArc_left_lt_right_wip k)⟩
  rw [hIcc, Set.image_union, Set.image_singleton]

private theorem quotient_mk_injOn_Ioc_zero_period_wip :
    Set.InjOn (fun t : ℝ => (QuotientAddGroup.mk t : Circle))
      (Set.Ioc (0 : ℝ) (2 * Real.pi)) := by
  intro x hx y hy hxy
  have hx0 : x ∈ Set.Ioc (0 : ℝ) (0 + 2 * Real.pi) := by
    simpa using hx
  have hy0 : y ∈ Set.Ioc (0 : ℝ) (0 + 2 * Real.pi) := by
    simpa using hy
  have hx' :
      AddCircle.equivIoc (2 * Real.pi) (0 : ℝ)
          (QuotientAddGroup.mk x : Circle) = ⟨x, hx0⟩ :=
    AddCircle.equivIoc_coe_eq hx0
  have hy' :
      AddCircle.equivIoc (2 * Real.pi) (0 : ℝ)
          (QuotientAddGroup.mk y : Circle) = ⟨y, hy0⟩ :=
    AddCircle.equivIoc_coe_eq hy0
  have h := congrArg (AddCircle.equivIoc (2 * Real.pi) (0 : ℝ)) hxy
  rw [hx', hy'] at h
  exact Subtype.ext_iff.mp h

private theorem carrierArc_mk_preimage_image_Ioc_inter_fundamental_wip
    {N : Nat} (k : Fin N) :
    ((fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ⁻¹'
        ((fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ''
          Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)) ∩
      Set.Ioc (0 : ℝ) (2 * Real.pi)) =
        Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right) := by
  ext x
  constructor
  · intro hx
    rcases hx.1 with ⟨y, hy, hyx⟩
    have hy_fund : y ∈ Set.Ioc (0 : ℝ) (2 * Real.pi) := by
      exact ⟨lt_of_le_of_lt (carrierArc_left_nonneg_wip k) hy.1,
        le_trans hy.2 (carrierArc_right_le_period_wip k)⟩
    have hxy : y = x :=
      quotient_mk_injOn_Ioc_zero_period_wip hy_fund hx.2 hyx
    rwa [← hxy]
  · intro hx
    constructor
    · exact ⟨x, hx, rfl⟩
    · exact ⟨lt_of_le_of_lt (carrierArc_left_nonneg_wip k) hx.1,
        le_trans hx.2 (carrierArc_right_le_period_wip k)⟩

private theorem volume_singleton_circle_wip (x : Circle) :
    MeasureTheory.volume ({x} : Set Circle) = 0 := by
  have h := AddCircle.volume_closedBall (T := 2 * Real.pi) (x := x) (ε := 0)
  simpa using h

private theorem μCircle_singleton_wip (x : Circle) :
    μCircle ({x} : Set Circle) = 0 := by
  have hvol : MeasureTheory.volume ({x} : Set Circle) = 0 :=
    volume_singleton_circle_wip x
  rw [AddCircle.volume_eq_smul_haarAddCircle, MeasureTheory.Measure.smul_apply] at hvol
  rw [smul_eq_mul] at hvol
  have hcoef : ENNReal.ofReal (2 * Real.pi) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, Real.pi_pos]
  simpa [μCircle] using (mul_eq_zero.mp hvol).resolve_left hcoef

private theorem carrierArc_arcSet_ae_eq_mk_image_Ioc_wip {N : Nat} (k : Fin N) :
    arcSet (carrierArc N k) =ᵐ[μCircle]
      QuotientAddGroup.mk ''
        Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right) := by
  rw [carrierArc_arcSet_eq_mk_image_Ioc_union_left_wip k]
  let A : Set Circle :=
    QuotientAddGroup.mk ''
      Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)
  let e : Circle := QuotientAddGroup.mk ((carrierArc N k).left)
  change (Set.union A ({e} : Set Circle)) =ᵐ[μCircle] A
  rw [MeasureTheory.ae_eq_set]
  constructor
  · refine MeasureTheory.measure_mono_null (μ := μCircle) (t := {e}) ?_
      (μCircle_singleton_wip e)
    intro x hx
    rcases hx.1 with hxIoc | hxleft
    · exact False.elim (hx.2 hxIoc)
    · exact hxleft
  · refine MeasureTheory.measure_mono_null (μ := μCircle) (t := (∅ : Set Circle)) ?_ ?_
    · intro x hx
      exact False.elim (hx.2 (Or.inl hx.1))
    · simp

private theorem carrierArc_arcSet_ae_eq_mk_image_Ioc_volume_wip
    {N : Nat} (k : Fin N) :
    arcSet (carrierArc N k) =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure Circle)]
      QuotientAddGroup.mk ''
        Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right) := by
  rw [carrierArc_arcSet_eq_mk_image_Ioc_union_left_wip k]
  let A : Set Circle :=
    QuotientAddGroup.mk ''
      Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)
  let e : Circle := QuotientAddGroup.mk ((carrierArc N k).left)
  change (Set.union A ({e} : Set Circle)) =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure
      Circle)] A
  rw [MeasureTheory.ae_eq_set]
  constructor
  · refine MeasureTheory.measure_mono_null
      (μ := (MeasureTheory.volume : MeasureTheory.Measure Circle)) (t := {e}) ?_
      (volume_singleton_circle_wip e)
    intro x hx
    rcases hx.1 with hxIoc | hxleft
    · exact False.elim (hx.2 hxIoc)
    · exact hxleft
  · refine MeasureTheory.measure_mono_null
      (μ := (MeasureTheory.volume : MeasureTheory.Measure Circle)) (t := (∅ : Set Circle)) ?_ ?_
    · intro x hx
      exact False.elim (hx.2 (Or.inl hx.1))
    · simp

private theorem volume_mk_image_carrierArc_Ioc_wip {N : Nat} (k : Fin N) :
    MeasureTheory.volume
        ((fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ''
          Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)) =
      ENNReal.ofReal (arcLength (carrierArc N k)) := by
  let S : Set Circle :=
    (fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ''
      Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)
  have hS_null :
      MeasureTheory.NullMeasurableSet S
        (MeasureTheory.volume : MeasureTheory.Measure Circle) := by
    exact (measurableSet_arcSet (carrierArc N k)).nullMeasurableSet.congr
      (carrierArc_arcSet_ae_eq_mk_image_Ioc_volume_wip k)
  have hpre :=
    (AddCircle.measurePreserving_mk (T := 2 * Real.pi) (t := 0)).measure_preimage hS_null
  rw [MeasureTheory.Measure.restrict_apply' measurableSet_Ioc] at hpre
  change MeasureTheory.volume
      (((fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ⁻¹' S) ∩
        Set.Ioc (0 : ℝ) (0 + 2 * Real.pi)) =
      MeasureTheory.volume S at hpre
  have hpre_set :
      ((fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ⁻¹' S) ∩
        Set.Ioc (0 : ℝ) (0 + 2 * Real.pi) =
          Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right) := by
    simpa [S] using carrierArc_mk_preimage_image_Ioc_inter_fundamental_wip k
  rw [hpre_set, Real.volume_Ioc] at hpre
  dsimp [arcLength]
  symm
  rw [← hpre]

private theorem period_smul_μCircle_mk_image_carrierArc_Ioc_wip
    {N : Nat} (k : Fin N) :
    ENNReal.ofReal (2 * Real.pi) *
        μCircle
          ((fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ''
            Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)) =
      ENNReal.ofReal (arcLength (carrierArc N k)) := by
  let S : Set Circle :=
    (fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ''
      Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)
  have hmeasure := congrArg (fun μ : MeasureTheory.Measure Circle => μ S)
    (AddCircle.volume_eq_smul_haarAddCircle (T := 2 * Real.pi))
  change MeasureTheory.volume S =
    ENNReal.ofReal (2 * Real.pi) * μCircle S at hmeasure
  rw [← hmeasure]
  exact volume_mk_image_carrierArc_Ioc_wip k

private theorem period_smul_μCircle_carrierArc_wip {N : Nat} (k : Fin N) :
    ENNReal.ofReal (2 * Real.pi) *
        μCircle (arcSet (carrierArc N k)) =
      ENNReal.ofReal (arcLength (carrierArc N k)) := by
  rw [MeasureTheory.measure_congr (carrierArc_arcSet_ae_eq_mk_image_Ioc_wip k)]
  exact period_smul_μCircle_mk_image_carrierArc_Ioc_wip k

private theorem carrierArc_mu_real_eq_length_div_period
    {N : Nat} (k : Fin N) :
    μCircle.real (arcSet (carrierArc N k)) =
      arcLength (carrierArc N k) / (2 * Real.pi) := by
  have h := congrArg ENNReal.toReal (period_smul_μCircle_carrierArc_wip k)
  have hT_nonneg : 0 <= (2 * Real.pi : ℝ) := by positivity
  have hell_nonneg : 0 <= arcLength (carrierArc N k) :=
    arcLength_nonneg (carrierArc N k)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hT_nonneg,
    ENNReal.toReal_ofReal hell_nonneg] at h
  have hT_pos : 0 < (2 * Real.pi : ℝ) := by positivity
  rw [MeasureTheory.measureReal_def, eq_div_iff hT_pos.ne']
  simpa [mul_comm] using h

private theorem carrierArc_mu_real_eq_inv_nat
    {N : Nat} (k : Fin N) :
    μCircle.real (arcSet (carrierArc N k)) = (N : ℝ)⁻¹ := by
  rw [carrierArc_mu_real_eq_length_div_period k, carrierArc_length k]
  have hT_pos : 0 < (2 * Real.pi : ℝ) := by positivity
  have hNnat : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le k.1) k.2
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNnat
  field_simp [hT_pos.ne', hNpos.ne']

private def carrierIocImage {N : Nat} (k : Fin N) : Set Circle :=
  QuotientAddGroup.mk ''
    Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)

private theorem carrierIocImage_subset_arcSet {N : Nat} (k : Fin N) :
    carrierIocImage k ⊆ arcSet (carrierArc N k) := by
  unfold carrierIocImage
  rw [carrierArc_arcSet_eq_mk_image_Icc_wip k]
  exact Set.image_mono Set.Ioc_subset_Icc_self

private theorem carrierIocImage_subset_closedBall_of_arc_mem
    {N : Nat} (k : Fin N) {x0 : Circle}
    (hx0 : x0 ∈ arcSet (carrierArc N k)) :
    carrierIocImage k ⊆ Metric.closedBall x0 (arcLength (carrierArc N k)) := by
  intro x hx
  have hx_arc : x ∈ arcSet (carrierArc N k) :=
    carrierIocImage_subset_arcSet k hx
  exact carrierArc_dist_le_length k x hx_arc x0 hx0

private theorem carrierIocImage_subset_closedBall_of_badCarrierForRoot
    {N : Nat} {ζ : ℂ} {delta : ℝ} {k : Fin N}
    (hk : k ∈ badCarrierIndicesForRoot N ζ delta) :
    ∃ x : Circle,
      x ∈ arcSet (carrierArc N k) ∧ ‖zeta x - ζ‖ < delta ∧
        carrierIocImage k ⊆ Metric.closedBall x (arcLength (carrierArc N k)) := by
  classical
  unfold badCarrierIndicesForRoot at hk
  rcases Finset.mem_filter.mp hk with ⟨_hk_univ, x, hx_arc, hx_close⟩
  exact ⟨x, hx_arc, hx_close,
    carrierIocImage_subset_closedBall_of_arc_mem k hx_arc⟩

private theorem badCarrierForRoot_union_subset_closedBall_of_center
    {N : Nat} {ζ : ℂ} {delta : ℝ} {x0 : Circle}
    (_hdelta : 0 <= delta)
    (hx0_close : ‖zeta x0 - ζ‖ < delta) :
    (⋃ k ∈ badCarrierIndicesForRoot N ζ delta, carrierIocImage k) ⊆
      Metric.closedBall x0 (Real.pi * delta + (2 * Real.pi) / (N : ℝ)) := by
  classical
  intro y hy
  rw [Set.mem_iUnion] at hy
  rcases hy with ⟨k, hy⟩
  rw [Set.mem_iUnion] at hy
  rcases hy with ⟨hk_bad, hy_ioc⟩
  rcases carrierIocImage_subset_closedBall_of_badCarrierForRoot hk_bad with
    ⟨x, hx_arc, hx_close, _hcarrier_ball⟩
  have hy_arc : y ∈ arcSet (carrierArc N k) :=
    carrierIocImage_subset_arcSet k hy_ioc
  have hx0_close' : ‖ζ - zeta x0‖ < delta := by
    rw [← norm_neg, neg_sub]
    exact hx0_close
  have hchord_le : ‖zeta x - zeta x0‖ <= 2 * delta := by
    calc
      ‖zeta x - zeta x0‖ =
          ‖(zeta x - ζ) + (ζ - zeta x0)‖ := by
            congr 1
            ring
      _ <= ‖zeta x - ζ‖ + ‖ζ - zeta x0‖ := norm_add_le _ _
      _ <= delta + delta := by
            exact add_le_add (le_of_lt hx_close) (le_of_lt hx0_close')
      _ = 2 * delta := by ring
  have hdist_x_x0 : dist x x0 <= Real.pi * delta := by
    have hdist := circle_dist_le_pi_div_two_mul_chord x x0
    calc
      dist x x0 <= (Real.pi / 2) * ‖zeta x - zeta x0‖ := hdist
      _ <= (Real.pi / 2) * (2 * delta) := by
            exact mul_le_mul_of_nonneg_left hchord_le (by positivity)
      _ = Real.pi * delta := by ring
  have hdist_y_x : dist y x <= arcLength (carrierArc N k) :=
    carrierArc_dist_le_length k y hy_arc x hx_arc
  calc
    dist y x0 <= dist y x + dist x x0 := dist_triangle y x x0
    _ <= arcLength (carrierArc N k) + Real.pi * delta := by
          exact add_le_add hdist_y_x hdist_x_x0
    _ = Real.pi * delta + (2 * Real.pi) / (N : ℝ) := by
          rw [carrierArc_length k]
          ring

private theorem carrierArc_setIntegral_eq_iocImage_wip
    {N : Nat} (k : Fin N) (f : Circle -> ℝ) :
    (∫ x in arcSet (carrierArc N k), f x ∂ μCircle) =
      ∫ x in carrierIocImage k, f x ∂ μCircle := by
  unfold carrierIocImage
  rw [MeasureTheory.Measure.restrict_congr_set
    (carrierArc_arcSet_ae_eq_mk_image_Ioc_wip k)]

private theorem carrierIocImage_mu_real_eq_inv_nat {N : Nat} (k : Fin N) :
    μCircle.real (carrierIocImage k) = (N : ℝ)⁻¹ := by
  have h := carrierArc_setIntegral_eq_iocImage_wip k (fun _ : Circle => (1 : ℝ))
  rw [MeasureTheory.setIntegral_const, MeasureTheory.setIntegral_const] at h
  simpa [carrierArc_mu_real_eq_inv_nat k] using h.symm

private theorem carrierArc_setIntegral_eq_iocImage_complex_wip
    {N : Nat} (k : Fin N) (f : Circle -> ℂ) :
    (∫ x in arcSet (carrierArc N k), f x ∂ μCircle) =
      ∫ x in carrierIocImage k, f x ∂ μCircle := by
  unfold carrierIocImage
  rw [MeasureTheory.Measure.restrict_congr_set
    (carrierArc_arcSet_ae_eq_mk_image_Ioc_wip k)]

private theorem carrierIocImage_nullMeasurable_wip {N : Nat} (k : Fin N) :
    MeasureTheory.NullMeasurableSet (carrierIocImage k) μCircle := by
  unfold carrierIocImage
  exact (measurableSet_arcSet (carrierArc N k)).nullMeasurableSet.congr
    (carrierArc_arcSet_ae_eq_mk_image_Ioc_wip k)

private theorem carrierIocImage_nullMeasurable_volume_wip {N : Nat} (k : Fin N) :
    MeasureTheory.NullMeasurableSet (carrierIocImage k)
      (MeasureTheory.volume : MeasureTheory.Measure Circle) := by
  unfold carrierIocImage
  exact (measurableSet_arcSet (carrierArc N k)).nullMeasurableSet.congr
    (carrierArc_arcSet_ae_eq_mk_image_Ioc_volume_wip k)

private theorem carrierIocImage_indicator_preimage_eq_wip
    {N : Nat} {E : Type*} [Zero E] (k : Fin N) (f : Circle -> E) :
    (Set.Ioc (0 : ℝ) (2 * Real.pi)).indicator
        (fun t : ℝ => (carrierIocImage k).indicator f (QuotientAddGroup.mk t : Circle)) =
      (Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)).indicator
        (fun t : ℝ => f (QuotientAddGroup.mk t : Circle)) := by
  funext t
  by_cases ht : t ∈ Set.Ioc (0 : ℝ) (2 * Real.pi)
  · have hmem : (QuotientAddGroup.mk t : Circle) ∈ carrierIocImage k ↔
        t ∈ Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right) := by
      have hset := carrierArc_mk_preimage_image_Ioc_inter_fundamental_wip k
      have htiff := congrArg (fun s : Set ℝ => t ∈ s) hset
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_image, Set.mem_Ioc, ht, and_true,
        eq_iff_iff] at htiff
      exact htiff
    by_cases hs : (QuotientAddGroup.mk t : Circle) ∈ carrierIocImage k
    · simp [Set.indicator_of_mem, ht, hs, hmem.mp hs]
    · have hnot : t ∉ Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right) := by
        exact fun h => hs (hmem.mpr h)
      simp [Set.indicator_of_notMem, ht, hs, hnot]
  · have hnot : t ∉ Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right) := by
      intro htc
      have hsubset : Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right) ⊆
          Set.Ioc (0 : ℝ) (2 * Real.pi) := by
        intro y hy
        exact ⟨lt_of_le_of_lt (carrierArc_left_nonneg_wip k) hy.1,
          le_trans hy.2 (carrierArc_right_le_period_wip k)⟩
      exact ht (hsubset htc)
    simp [Set.indicator_of_notMem, ht, hnot]

private theorem carrierIocImage_volume_setIntegral_eq_real_Ioc
    {N : Nat} (k : Fin N) (f : Circle -> ℝ) :
    (∫ x in carrierIocImage k, f x ∂ (MeasureTheory.volume : MeasureTheory.Measure Circle)) =
      ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
        f (QuotientAddGroup.mk t : Circle) ∂
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  let S : Set Circle := carrierIocImage k
  let g : Circle -> ℝ := S.indicator f
  have hpre := AddCircle.integral_preimage (T := 2 * Real.pi) (t := 0) g
  change (∫ a in Set.Ioc (0 : ℝ) (0 + 2 * Real.pi),
      g (QuotientAddGroup.mk a : Circle) ∂
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) =
    ∫ b : Circle, g b ∂
      (MeasureTheory.volume : MeasureTheory.Measure Circle) at hpre
  have hrhs : (∫ b : Circle, g b ∂
      (MeasureTheory.volume : MeasureTheory.Measure Circle)) =
      ∫ x in S, f x ∂ (MeasureTheory.volume : MeasureTheory.Measure Circle) := by
    simpa [g, S] using
      (MeasureTheory.integral_indicator₀
        (μ := (MeasureTheory.volume : MeasureTheory.Measure Circle))
        (f := f) (s := S) (carrierIocImage_nullMeasurable_volume_wip k))
  have hlhs : (∫ a in Set.Ioc (0 : ℝ) (0 + 2 * Real.pi),
      g (QuotientAddGroup.mk a : Circle) ∂
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) =
      ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
        f (QuotientAddGroup.mk t : Circle) ∂
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
    rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
    have hfun := carrierIocImage_indicator_preimage_eq_wip k f
    simpa [g, S, zero_add] using congrArg
      (fun h : ℝ -> ℝ =>
        ∫ t, h t ∂ (MeasureTheory.volume : MeasureTheory.Measure ℝ)) hfun
  rw [← hrhs, ← hpre]
  exact hlhs

private theorem carrierIocImage_haar_setIntegral_eq_real_Ioc
    {N : Nat} (k : Fin N) (f : Circle -> ℝ) :
    (∫ x in carrierIocImage k, f x ∂ μCircle) =
      (1 / (2 * Real.pi)) *
        ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
          f (QuotientAddGroup.mk t : Circle) ∂
            (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  let S : Set Circle := carrierIocImage k
  have hvol_smul :
      (∫ x in S, f x ∂ (MeasureTheory.volume : MeasureTheory.Measure Circle)) =
        (2 * Real.pi) * ∫ x in S, f x ∂ μCircle := by
    rw [AddCircle.volume_eq_smul_haarAddCircle (T := 2 * Real.pi)]
    rw [MeasureTheory.Measure.restrict_smul]
    rw [MeasureTheory.integral_smul_measure]
    rw [ENNReal.toReal_ofReal]
    · simp [smul_eq_mul, μCircle]
    · positivity
  have hbridge := carrierIocImage_volume_setIntegral_eq_real_Ioc k f
  have hperiod_pos : 0 < (2 * Real.pi : ℝ) := by positivity
  calc
    (∫ x in carrierIocImage k, f x ∂ μCircle)
        = (1 / (2 * Real.pi)) *
          ((2 * Real.pi) * ∫ x in carrierIocImage k, f x ∂ μCircle) := by
          field_simp [ne_of_gt hperiod_pos]
    _ = (1 / (2 * Real.pi)) *
        ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
          f (QuotientAddGroup.mk t : Circle) ∂
            (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
          rw [← hvol_smul, hbridge]

private theorem carrierIocImage_haar_setIntegral_eq_intervalIntegral
    {N : Nat} (k : Fin N) (f : Circle -> ℝ) :
    (∫ x in carrierIocImage k, f x ∂ μCircle) =
      (1 / (2 * Real.pi)) *
        ∫ t in (carrierArc N k).left..(carrierArc N k).right,
          f (QuotientAddGroup.mk t : Circle) := by
  rw [carrierIocImage_haar_setIntegral_eq_real_Ioc]
  rw [← intervalIntegral.integral_of_le
    (le_of_lt (carrierArc_left_lt_right_wip k))]

private theorem carrierArc_setIntegral_eq_intervalIntegral_wip
    {N : Nat} (k : Fin N) (f : Circle -> ℝ) :
    (∫ x in arcSet (carrierArc N k), f x ∂ μCircle) =
      (1 / (2 * Real.pi)) *
        ∫ t in (carrierArc N k).left..(carrierArc N k).right,
          f (QuotientAddGroup.mk t : Circle) := by
  rw [carrierArc_setIntegral_eq_iocImage_wip,
    carrierIocImage_haar_setIntegral_eq_intervalIntegral]

private theorem carrierIocImage_volume_setIntegral_eq_real_Ioc_complex
    {N : Nat} (k : Fin N) (f : Circle -> ℂ) :
    (∫ x in carrierIocImage k, f x ∂ (MeasureTheory.volume : MeasureTheory.Measure Circle)) =
      ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
        f (QuotientAddGroup.mk t : Circle) ∂
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  let S : Set Circle := carrierIocImage k
  let g : Circle -> ℂ := S.indicator f
  have hpre := AddCircle.integral_preimage (T := 2 * Real.pi) (t := 0) g
  change (∫ a in Set.Ioc (0 : ℝ) (0 + 2 * Real.pi),
      g (QuotientAddGroup.mk a : Circle) ∂
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) =
    ∫ b : Circle, g b ∂
      (MeasureTheory.volume : MeasureTheory.Measure Circle) at hpre
  have hrhs : (∫ b : Circle, g b ∂
      (MeasureTheory.volume : MeasureTheory.Measure Circle)) =
      ∫ x in S, f x ∂ (MeasureTheory.volume : MeasureTheory.Measure Circle) := by
    simpa [g, S] using
      (MeasureTheory.integral_indicator₀
        (μ := (MeasureTheory.volume : MeasureTheory.Measure Circle))
        (f := f) (s := S) (carrierIocImage_nullMeasurable_volume_wip k))
  have hlhs : (∫ a in Set.Ioc (0 : ℝ) (0 + 2 * Real.pi),
      g (QuotientAddGroup.mk a : Circle) ∂
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) =
      ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
        f (QuotientAddGroup.mk t : Circle) ∂
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
    rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
    have hfun := carrierIocImage_indicator_preimage_eq_wip k f
    simpa [g, S, zero_add] using congrArg
      (fun h : ℝ -> ℂ =>
        ∫ t, h t ∂ (MeasureTheory.volume : MeasureTheory.Measure ℝ)) hfun
  rw [← hrhs, ← hpre]
  exact hlhs

private theorem carrierIocImage_haar_setIntegral_eq_real_Ioc_complex
    {N : Nat} (k : Fin N) (f : Circle -> ℂ) :
    (∫ x in carrierIocImage k, f x ∂ μCircle) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
          f (QuotientAddGroup.mk t : Circle) ∂
            (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  let S : Set Circle := carrierIocImage k
  have hvol_smul :
      (∫ x in S, f x ∂ (MeasureTheory.volume : MeasureTheory.Measure Circle)) =
        (2 * Real.pi : ℝ) • ∫ x in S, f x ∂ μCircle := by
    rw [AddCircle.volume_eq_smul_haarAddCircle (T := 2 * Real.pi)]
    rw [MeasureTheory.Measure.restrict_smul]
    rw [MeasureTheory.integral_smul_measure]
    rw [ENNReal.toReal_ofReal (by positivity)]
    simp only [μCircle, Complex.real_smul]
  have hbridge := carrierIocImage_volume_setIntegral_eq_real_Ioc_complex k f
  have hperiod_pos : 0 < (2 * Real.pi : ℝ) := by positivity
  calc
    (∫ x in carrierIocImage k, f x ∂ μCircle)
        = (1 / (2 * Real.pi) : ℝ) •
          ((2 * Real.pi : ℝ) • ∫ x in carrierIocImage k, f x ∂ μCircle) := by
          have hcoeff_real :
              (1 / (2 * Real.pi) : ℝ) * (2 * Real.pi) = 1 := by
            field_simp [ne_of_gt hperiod_pos]
          have hcoeff_complex :
              ((1 / (2 * Real.pi) : ℝ) : ℂ) *
                ((2 * Real.pi : ℝ) : ℂ) = 1 := by
            exact_mod_cast hcoeff_real
          rw [Complex.real_smul, Complex.real_smul]
          rw [← mul_assoc, hcoeff_complex, one_mul]
    _ = (1 / (2 * Real.pi) : ℝ) •
        ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
          f (QuotientAddGroup.mk t : Circle) ∂
            (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
          rw [← hvol_smul, hbridge]

private theorem carrierIocImage_haar_setIntegral_eq_intervalIntegral_complex
    {N : Nat} (k : Fin N) (f : Circle -> ℂ) :
    (∫ x in carrierIocImage k, f x ∂ μCircle) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ t in (carrierArc N k).left..(carrierArc N k).right,
          f (QuotientAddGroup.mk t : Circle) := by
  rw [carrierIocImage_haar_setIntegral_eq_real_Ioc_complex]
  rw [← intervalIntegral.integral_of_le
    (le_of_lt (carrierArc_left_lt_right_wip k))]

private theorem carrierArc_setIntegral_eq_intervalIntegral_complex_wip
    {N : Nat} (k : Fin N) (f : Circle -> ℂ) :
    (∫ x in arcSet (carrierArc N k), f x ∂ μCircle) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ t in (carrierArc N k).left..(carrierArc N k).right,
          f (QuotientAddGroup.mk t : Circle) := by
  rw [carrierArc_setIntegral_eq_iocImage_complex_wip,
    carrierIocImage_haar_setIntegral_eq_intervalIntegral_complex]

private theorem carrierAverage_eq_interval_average
    {N : Nat} (k : Fin N) (f : Circle -> ℂ) :
    carrierAverage (N := N) k f =
      ((arcLength (carrierArc N k))⁻¹ : ℝ) •
        ∫ t in (carrierArc N k).left..(carrierArc N k).right,
          f (QuotientAddGroup.mk t : Circle) := by
  rw [carrierAverage, carrierArc_setIntegral_eq_intervalIntegral_complex_wip]
  have hNnat : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le k.1) k.2
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNnat
  have hTpos : 0 < (2 * Real.pi : ℝ) := by positivity
  have hcoeff_real :
      (N : ℝ) * (1 / (2 * Real.pi)) =
        (arcLength (carrierArc N k))⁻¹ := by
    rw [carrierArc_length]
    field_simp [ne_of_gt hNpos, ne_of_gt hTpos]
  have hcoeff :
      (N : ℂ) * ((1 / (2 * Real.pi) : ℝ) : ℂ) =
        (((arcLength (carrierArc N k))⁻¹ : ℝ) : ℂ) := by
    exact_mod_cast hcoeff_real
  let I : ℂ :=
    ∫ t in (carrierArc N k).left..(carrierArc N k).right,
      f (QuotientAddGroup.mk t : Circle)
  change (N : ℂ) * ((1 / (2 * Real.pi) : ℝ) • I) =
    ((arcLength (carrierArc N k))⁻¹ : ℝ) • I
  calc
    (N : ℂ) * ((1 / (2 * Real.pi) : ℝ) • I)
        = ((N : ℂ) * ((1 / (2 * Real.pi) : ℝ) : ℂ)) * I := by
          rw [Complex.real_smul]
          ring
    _ = (((arcLength (carrierArc N k))⁻¹ : ℝ) : ℂ) * I := by
          rw [hcoeff]
    _ = ((arcLength (carrierArc N k))⁻¹ : ℝ) • I := by
          rw [Complex.real_smul]

private theorem intervalIntegral_shift_wip {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ -> E) (a h : ℝ) :
    ∫ t in a..a + h, g t =
      ∫ x in (0 : ℝ)..h, g (x + a) := by
  have key := (intervalIntegral.integral_comp_add_right
    g a (a := (0 : ℝ)) (b := h)).symm
  simp only [zero_add] at key
  rwa [add_comm h a] at key

private theorem carrierArc_left_add_length_eq_right_wip
    {N : Nat} (k : Fin N) :
    (carrierArc N k).left + arcLength (carrierArc N k) =
      (carrierArc N k).right := by
  dsimp [arcLength]
  ring

private theorem carrierAverage_variance_interval_le_derivative
    {N L : Nat} (k : Fin N) (p : Fin L -> ℂ) :
    (∫ t in (carrierArc N k).left..(carrierArc N k).right,
      ‖slowBandPoly p (QuotientAddGroup.mk t : Circle) -
        carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2) <=
      arcLength (carrierArc N k) ^ 2 *
        ∫ t in (carrierArc N k).left..(carrierArc N k).right,
          ‖slowBandPolyDeriv p t‖ ^ 2 := by
  let Q : Circle -> ℂ := slowBandPoly p
  let a : ℝ := (carrierArc N k).left
  let h : ℝ := arcLength (carrierArc N k)
  let avg : ℂ := carrierAverage (N := N) k Q
  let f : ℝ -> ℂ := fun x => Q (QuotientAddGroup.mk (x + a) : Circle)
  let f' : ℝ -> ℂ := fun x => slowBandPolyDeriv p (x + a)
  have hh_pos : 0 < h := by
    simpa [h] using carrierArc_length_pos_wip k
  have hright : a + h = (carrierArc N k).right := by
    simpa [a, h] using carrierArc_left_add_length_eq_right_wip k
  have hf_deriv : ∀ x ∈ Set.Icc (0 : ℝ) h, HasDerivAt f (f' x) x := by
    intro x hx
    simpa [f, f'] using hasDerivAt_slowBandPoly_shift p a x
  have hf_cont : ContinuousOn f (Set.Icc (0 : ℝ) h) := by
    exact (((continuous_slowBandPoly p).comp
      ((AddCircle.continuous_mk' (2 * Real.pi)).comp
        (continuous_id.add continuous_const))).continuousOn)
  have hf'_cont : ContinuousOn f' (Set.Icc (0 : ℝ) h) := by
    exact (((continuous_slowBandPolyDeriv p).comp
      (continuous_id.add continuous_const)).continuousOn)
  have h_mean :
      h⁻¹ • ∫ x in (0 : ℝ)..h, f x = avg := by
    have hshift :=
      (intervalIntegral_shift_wip
        (fun t : ℝ => Q (QuotientAddGroup.mk t : Circle)) a h).symm
    change h⁻¹ •
      (∫ x in (0 : ℝ)..h, Q (QuotientAddGroup.mk (x + a) : Circle)) = avg
    rw [hshift, hright]
    simpa [avg, Q, h] using
      (carrierAverage_eq_interval_average (N := N) k Q).symm
  have hp := FockSPR.MissingMathlib.poincare_interval
    hh_pos hf_deriv hf_cont hf'_cont
  simp only [one_div] at hp
  rw [h_mean] at hp
  have hshift_lhs :
      (∫ t in a..(carrierArc N k).right,
        ‖Q (QuotientAddGroup.mk t : Circle) - avg‖ ^ 2) =
        ∫ x in (0 : ℝ)..h, ‖f x - avg‖ ^ 2 := by
    rw [← hright]
    simpa [f] using
      intervalIntegral_shift_wip
        (fun t : ℝ => ‖Q (QuotientAddGroup.mk t : Circle) - avg‖ ^ 2) a h
  have hshift_rhs :
      (∫ t in a..(carrierArc N k).right, ‖slowBandPolyDeriv p t‖ ^ 2) =
        ∫ x in (0 : ℝ)..h, ‖f' x‖ ^ 2 := by
    rw [← hright]
    simpa [f'] using
      intervalIntegral_shift_wip
        (fun t : ℝ => ‖slowBandPolyDeriv p t‖ ^ 2) a h
  simpa [Q, a, h, avg, hshift_lhs, hshift_rhs] using hp

private theorem carrierAverage_variance_carrier_le_derivative_interval
    {N L : Nat} (k : Fin N) (p : Fin L -> ℂ) :
    (∫ x in arcSet (carrierArc N k),
      ‖slowBandPoly p x -
        carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 ∂ μCircle) <=
      (1 / (2 * Real.pi)) *
        (arcLength (carrierArc N k) ^ 2 *
          ∫ t in (carrierArc N k).left..(carrierArc N k).right,
            ‖slowBandPolyDeriv p t‖ ^ 2) := by
  let f : Circle -> ℝ := fun x =>
    ‖slowBandPoly p x -
      carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2
  rw [carrierArc_setIntegral_eq_intervalIntegral_wip (k := k) (f := f)]
  exact mul_le_mul_of_nonneg_left
    (carrierAverage_variance_interval_le_derivative (N := N) k p)
    (by positivity)

private theorem carrierArc_right_le_left_of_lt_wip
    {N : Nat} {k l : Fin N} (hkl : k.1 < l.1) :
    (carrierArc N k).right <= (carrierArc N l).left := by
  unfold carrierArc
  have hNnat : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le k.1) k.2
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNnat
  have hsucc : ((k.1 + 1 : Nat) : ℝ) <= (l.1 : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hkl
  have hT_nonneg : 0 <= (2 * Real.pi : ℝ) := by positivity
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsucc hT_nonneg) (le_of_lt hNpos)

private theorem carrierIocImage_disjoint_wip
    {N : Nat} {k l : Fin N} (hkl : k ≠ l) :
    Disjoint (carrierIocImage k) (carrierIocImage l) := by
  rw [Set.disjoint_left]
  intro x hxk hxl
  unfold carrierIocImage at hxk hxl
  rcases hxk with ⟨a, ha, hax⟩
  rcases hxl with ⟨b, hb, hbx⟩
  have ha_fund : a ∈ Set.Ioc (0 : ℝ) (2 * Real.pi) :=
    ⟨lt_of_le_of_lt (carrierArc_left_nonneg_wip k) ha.1,
      le_trans ha.2 (carrierArc_right_le_period_wip k)⟩
  have hb_fund : b ∈ Set.Ioc (0 : ℝ) (2 * Real.pi) :=
    ⟨lt_of_le_of_lt (carrierArc_left_nonneg_wip l) hb.1,
      le_trans hb.2 (carrierArc_right_le_period_wip l)⟩
  have hab : a = b :=
    quotient_mk_injOn_Ioc_zero_period_wip ha_fund hb_fund (hax.trans hbx.symm)
  subst b
  by_cases hklt : k.1 < l.1
  · have hle := carrierArc_right_le_left_of_lt_wip (N := N) (k := k) (l := l) hklt
    exact (not_lt_of_ge (le_trans ha.2 hle)) hb.1
  · have hlk : l.1 < k.1 := by
      have hle : l.1 <= k.1 := Nat.le_of_not_gt hklt
      have hne : l.1 ≠ k.1 := by
        intro hval
        apply hkl
        ext
        exact hval.symm
      exact lt_of_le_of_ne hle hne
    have hle := carrierArc_right_le_left_of_lt_wip (N := N) (k := l) (l := k) hlk
    exact (not_lt_of_ge (le_trans hb.2 hle)) ha.1

private theorem carrierIocImage_setIntegral_biUnion_finset_wip
    {N : Nat} (K : Finset (Fin N)) (f : Circle -> ℝ)
    (hf : ∀ k ∈ K, MeasureTheory.IntegrableOn f (carrierIocImage k) μCircle) :
    (∫ x in ⋃ k ∈ K, carrierIocImage k, f x ∂ μCircle) =
      ∑ k ∈ K, ∫ x in carrierIocImage k, f x ∂ μCircle := by
  classical
  induction K using Finset.induction_on with
  | empty =>
      simp
  | insert a K haK ih =>
      have hdisj :
          MeasureTheory.AEDisjoint μCircle (carrierIocImage a)
            (⋃ k ∈ K, carrierIocImage k) := by
        refine (Set.disjoint_iUnion_right.2 ?_).aedisjoint
        intro k
        rw [Set.disjoint_iUnion_right]
        intro hk
        exact carrierIocImage_disjoint_wip (k := a) (l := k) (by
          intro hak
          apply haK
          simpa [← hak] using hk)
      have hnull_union :
          MeasureTheory.NullMeasurableSet
            (⋃ k ∈ K, carrierIocImage k) μCircle := by
        exact K.nullMeasurableSet_biUnion
          (fun k hk => carrierIocImage_nullMeasurable_wip k)
      have hfa : MeasureTheory.IntegrableOn f (carrierIocImage a) μCircle :=
        hf a (Finset.mem_insert_self a K)
      have hfunion :
          MeasureTheory.IntegrableOn f (⋃ k ∈ K, carrierIocImage k) μCircle := by
        exact MeasureTheory.integrableOn_finset_iUnion.2
          (fun k hk => hf k (Finset.mem_insert_of_mem hk))
      have hrec :
          (∫ x in ⋃ k ∈ K, carrierIocImage k, f x ∂ μCircle) =
            ∑ k ∈ K, ∫ x in carrierIocImage k, f x ∂ μCircle :=
        ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))
      rw [Finset.set_biUnion_insert]
      rw [MeasureTheory.setIntegral_union₀ hdisj hnull_union hfa hfunion]
      rw [hrec, Finset.sum_insert haK]

private theorem carrierIocImage_union_mu_real_eq_card_inv_nat
    {N : Nat} (K : Finset (Fin N)) :
    μCircle.real (⋃ k ∈ K, carrierIocImage k) =
      (K.card : ℝ) * (N : ℝ)⁻¹ := by
  classical
  haveI : MeasureTheory.IsFiniteMeasure μCircle := by
    dsimp [μCircle]
    infer_instance
  let U : Set Circle := ⋃ k ∈ K, carrierIocImage k
  have hf :
      ∀ k ∈ K,
        MeasureTheory.IntegrableOn (fun _ : Circle => (1 : ℝ))
          (carrierIocImage k) μCircle := by
    intro k _hk
    exact MeasureTheory.integrableOn_const
      (MeasureTheory.measure_ne_top μCircle (carrierIocImage k))
  have hsum := carrierIocImage_setIntegral_biUnion_finset_wip
    (N := N) K (fun _ : Circle => (1 : ℝ)) hf
  have hleft :
      (∫ x in U, (1 : ℝ) ∂ μCircle) = μCircle.real U := by
    rw [MeasureTheory.setIntegral_const]
    simp
  have hright :
      (∑ k ∈ K, ∫ x in carrierIocImage k, (1 : ℝ) ∂ μCircle) =
        ∑ k ∈ K, (N : ℝ)⁻¹ := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [MeasureTheory.setIntegral_const]
    simp [carrierIocImage_mu_real_eq_inv_nat k]
  calc
    μCircle.real U = ∫ x in U, (1 : ℝ) ∂ μCircle := hleft.symm
    _ = ∑ k ∈ K, ∫ x in carrierIocImage k, (1 : ℝ) ∂ μCircle := hsum
    _ = ∑ _k ∈ K, (N : ℝ)⁻¹ := hright
    _ = (K.card : ℝ) * (N : ℝ)⁻¹ := by
      rw [Finset.sum_const, nsmul_eq_mul]

private theorem μCircle_real_closedBall_eq_min_div_period
    (x : Circle) {R : ℝ} (hR : 0 <= R) :
    μCircle.real (Metric.closedBall x R) =
      min (2 * Real.pi) (2 * R) / (2 * Real.pi) := by
  let S : Set Circle := Metric.closedBall x R
  have hmeasure := congrArg (fun μ : MeasureTheory.Measure Circle => μ S)
    (AddCircle.volume_eq_smul_haarAddCircle (T := 2 * Real.pi))
  change MeasureTheory.volume S =
    ENNReal.ofReal (2 * Real.pi) * μCircle S at hmeasure
  rw [AddCircle.volume_closedBall] at hmeasure
  have h := congrArg ENNReal.toReal hmeasure
  have hT_nonneg : 0 <= (2 * Real.pi : ℝ) := by positivity
  have hmin_nonneg : 0 <= min (2 * Real.pi) (2 * R) := by
    exact le_min hT_nonneg (mul_nonneg (by norm_num) hR)
  rw [ENNReal.toReal_ofReal hmin_nonneg, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hT_nonneg] at h
  have hT_pos : 0 < (2 * Real.pi : ℝ) := by positivity
  rw [MeasureTheory.measureReal_def, eq_div_iff hT_pos.ne']
  simpa [S, mul_comm] using h.symm

private theorem carrierIocImage_card_invNat_le_closedBall_ratio
    {N : Nat} (K : Finset (Fin N)) {x0 : Circle} {R : ℝ}
    (hR : 0 <= R)
    (hsub : (⋃ k ∈ K, carrierIocImage k) ⊆ Metric.closedBall x0 R) :
    (K.card : ℝ) * (N : ℝ)⁻¹ <=
      min (2 * Real.pi) (2 * R) / (2 * Real.pi) := by
  classical
  haveI : MeasureTheory.IsFiniteMeasure μCircle := by
    dsimp [μCircle]
    infer_instance
  let U : Set Circle := ⋃ k ∈ K, carrierIocImage k
  have hμmono :
      μCircle.real U <= μCircle.real (Metric.closedBall x0 R) :=
    MeasureTheory.measureReal_mono hsub
  calc
    (K.card : ℝ) * (N : ℝ)⁻¹ = μCircle.real U := by
      rw [carrierIocImage_union_mu_real_eq_card_inv_nat K]
    _ <= μCircle.real (Metric.closedBall x0 R) := hμmono
    _ = min (2 * Real.pi) (2 * R) / (2 * Real.pi) :=
      μCircle_real_closedBall_eq_min_div_period x0 hR

private theorem nat_card_le_of_real_invNat_le
    {N M : Nat} (hN : 0 < N) {c : Nat}
    (h : (c : ℝ) * (N : ℝ)⁻¹ <= (M : ℝ) * (N : ℝ)⁻¹) :
    c <= M := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hmul := mul_le_mul_of_nonneg_right h (le_of_lt hNpos)
  have hc :
      ((c : ℝ) * (N : ℝ)⁻¹) * (N : ℝ) = (c : ℝ) := by
    field_simp [hNpos.ne']
  have hM :
      ((M : ℝ) * (N : ℝ)⁻¹) * (N : ℝ) = (M : ℝ) := by
    field_simp [hNpos.ne']
  have hreal : (c : ℝ) <= (M : ℝ) := by
    simpa [hc, hM] using hmul
  exact_mod_cast hreal

private theorem carrierIocImage_card_le_of_closedBall_ratio_le
    {N M : Nat} (hN : 0 < N) (K : Finset (Fin N)) {x0 : Circle} {R : ℝ}
    (hR : 0 <= R)
    (hsub : (⋃ k ∈ K, carrierIocImage k) ⊆ Metric.closedBall x0 R)
    (hratio : min (2 * Real.pi) (2 * R) / (2 * Real.pi) <=
      (M : ℝ) * (N : ℝ)⁻¹) :
    K.card <= M := by
  exact nat_card_le_of_real_invNat_le hN
    ((carrierIocImage_card_invNat_le_closedBall_ratio K hR hsub).trans hratio)

private theorem badCarrierIndicesForRoot_card_le_of_delta_eq
    {N B : Nat} {ζ : ℂ} {delta : ℝ}
    (hN : 0 < N) (hB : 1 <= B)
    (hdelta : delta = 16 * (B : ℝ) / (N : ℝ)) :
    (badCarrierIndicesForRoot N ζ delta).card <= 82 * B := by
  classical
  let K : Finset (Fin N) := badCarrierIndicesForRoot N ζ delta
  by_cases hKempty : K = ∅
  · simp [K, hKempty]
  · have hKnonempty : K.Nonempty := Finset.nonempty_iff_ne_empty.mpr hKempty
    rcases hKnonempty with ⟨k0, hk0⟩
    rcases carrierIocImage_subset_closedBall_of_badCarrierForRoot
        (N := N) (ζ := ζ) (delta := delta) (k := k0) (by simpa [K] using hk0) with
      ⟨x0, _hx0_arc, hx0_close, _hcarrier_ball⟩
    have hNpos_real : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hdelta_nonneg : 0 <= delta := by
      rw [hdelta]
      positivity
    let R : ℝ := Real.pi * delta + (2 * Real.pi) / (N : ℝ)
    have hR_nonneg : 0 <= R := by
      dsimp [R]
      positivity
    have hsub :
        (⋃ k ∈ K, carrierIocImage k) ⊆ Metric.closedBall x0 R := by
      simpa [K, R] using
        badCarrierForRoot_union_subset_closedBall_of_center
          (N := N) (ζ := ζ) (delta := delta) (x0 := x0)
          hdelta_nonneg hx0_close
    have hratio :
        min (2 * Real.pi) (2 * R) / (2 * Real.pi) <=
          ((82 * B : Nat) : ℝ) * (N : ℝ)⁻¹ := by
      have hTpos : (0 : ℝ) < 2 * Real.pi := by positivity
      have hBreal : (1 : ℝ) <= (B : ℝ) := by exact_mod_cast hB
      calc
        min (2 * Real.pi) (2 * R) / (2 * Real.pi)
            <= (2 * R) / (2 * Real.pi) := by
              exact div_le_div_of_nonneg_right
                (min_le_right (2 * Real.pi) (2 * R)) (le_of_lt hTpos)
        _ = R / Real.pi := by ring
        _ = delta + 2 / (N : ℝ) := by
              dsimp [R]
              field_simp [Real.pi_ne_zero]
        _ = (16 * (B : ℝ) + 2) / (N : ℝ) := by
              rw [hdelta]
              field_simp [hNpos_real.ne']
        _ <= (82 * (B : ℝ)) / (N : ℝ) := by
              have hnum : 16 * (B : ℝ) + 2 <= 82 * (B : ℝ) := by
                nlinarith
              exact div_le_div_of_nonneg_right hnum (le_of_lt hNpos_real)
        _ = ((82 * B : Nat) : ℝ) * (N : ℝ)⁻¹ := by
              norm_num
              ring
    simpa [K] using
      carrierIocImage_card_le_of_closedBall_ratio_le
        (N := N) (M := 82 * B) hN K hR_nonneg hsub hratio

private theorem badCarrierIndices_card_le_of_delta_eq
    {D N B : Nat} {roots : Multiset ℂ} {delta : ℝ}
    (hroots : roots.card <= D) (hN : 0 < N) (hB : 1 <= B)
    (hdelta : delta = 16 * (B : ℝ) / (N : ℝ)) :
    (badCarrierIndices N roots delta).card <= circleBadConst D * B := by
  exact badCarrierIndices_card_le_of_forall_root_card_le hroots
    (fun ζ _hζ => badCarrierIndicesForRoot_card_le_of_delta_eq hN hB hdelta)

private theorem carrierArc_length_le_canonical_delta
    {D N : Nat} (hD : 0 < D) (k : Fin N) :
    arcLength (carrierArc N k) <=
      (1 / (128 * ((D + 1 : Nat) : ℝ))) *
        (16 * (circleGoodBudget D : ℝ) / (N : ℝ)) := by
  have hNnat : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le k.1) k.2
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNnat
  have hsucc_pos : (0 : ℝ) < ((D + 1 : Nat) : ℝ) := by positivity
  have hbad_ge : (D + 1 : Nat) <= circleBadConst D :=
    circleBadConst_ge_succ_of_pos hD
  have hbad_ge_real : (((D + 1 : Nat) : ℝ) <= (circleBadConst D : ℝ)) := by
    exact_mod_cast hbad_ge
  rw [carrierArc_length k]
  have htwo_pi_le_eight : (2 * Real.pi : ℝ) <= 8 := by
    nlinarith [Real.pi_le_four]
  have hscale :
      8 <= 8 * ((circleBadConst D : ℝ) / ((D + 1 : Nat) : ℝ)) := by
    have hratio : (1 : ℝ) <= (circleBadConst D : ℝ) / ((D + 1 : Nat) : ℝ) := by
      rw [le_div_iff₀ hsucc_pos]
      simpa using hbad_ge_real
    nlinarith
  calc
    (2 * Real.pi) / (N : ℝ) <= 8 / (N : ℝ) := by
      exact div_le_div_of_nonneg_right htwo_pi_le_eight (le_of_lt hNpos)
    _ <= (8 * ((circleBadConst D : ℝ) / ((D + 1 : Nat) : ℝ))) / (N : ℝ) := by
      exact div_le_div_of_nonneg_right hscale (le_of_lt hNpos)
    _ =
        (1 / (128 * ((D + 1 : Nat) : ℝ))) *
          (16 * (circleGoodBudget D : ℝ) / (N : ℝ)) := by
      unfold circleGoodBudget
      field_simp [hNpos.ne', hsucc_pos.ne']
      norm_num
      ring

private theorem real_Ioc_zero_period_subset_iUnion_carrierIoc_wip
    {N : Nat} (hN : 0 < N) :
    Set.Ioc (0 : ℝ) (2 * Real.pi) ⊆
      ⋃ k : Fin N,
        Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right) := by
  intro t ht
  let a : Nat -> ℝ := fun i => (2 * Real.pi) * (i : ℝ) / (N : ℝ)
  have hsub := Ioc_subset_biUnion_Ioc N a
  have ht0N : t ∈ Set.Ioc (a 0) (a N) := by
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    simpa [a, hNpos.ne'] using ht
  have htunion :
      t ∈ ⋃ i ∈ Finset.range N, Set.Ioc (a i) (a (i + 1)) :=
    hsub ht0N
  rcases Set.mem_iUnion.mp htunion with ⟨i, hi_mem⟩
  rcases Set.mem_iUnion.mp hi_mem with ⟨hi_range, hti⟩
  have hi_lt : i < N := Finset.mem_range.mp hi_range
  refine Set.mem_iUnion.mpr ⟨⟨i, hi_lt⟩, ?_⟩
  simpa [a, carrierArc] using hti

private theorem carrierIocImage_iUnion_univ_wip
    {N : Nat} (hN : 0 < N) :
    (⋃ k : Fin N, carrierIocImage k) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hfull :
      ((fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ''
          Set.Ioc (0 : ℝ) (0 + 2 * Real.pi)) = Set.univ := by
    simpa using
      (AddCircle.coe_image_Ioc_eq (p := 2 * Real.pi) (a := (0 : ℝ)))
  have hxfull : x ∈
      (fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ''
        Set.Ioc (0 : ℝ) (0 + 2 * Real.pi) := by
    rw [hfull]
    trivial
  rcases hxfull with ⟨t, ht, rfl⟩
  have ht' : t ∈ Set.Ioc (0 : ℝ) (2 * Real.pi) := by
    simpa using ht
  have htc :=
    real_Ioc_zero_period_subset_iUnion_carrierIoc_wip (N := N) hN ht'
  rcases Set.mem_iUnion.mp htc with ⟨k, htk⟩
  refine Set.mem_iUnion.mpr ⟨k, ?_⟩
  unfold carrierIocImage
  exact ⟨t, htk, rfl⟩

private theorem carrierIocImage_setIntegral_univ_wip
    {N : Nat} (hN : 0 < N) (f : Circle -> ℝ)
    (hf : MeasureTheory.Integrable f μCircle) :
    (∫ x, f x ∂ μCircle) =
      ∑ k : Fin N, ∫ x in carrierIocImage k, f x ∂ μCircle := by
  classical
  have hsum :
      (∫ x in ⋃ k ∈ (Finset.univ : Finset (Fin N)),
          carrierIocImage k, f x ∂ μCircle) =
        ∑ k ∈ (Finset.univ : Finset (Fin N)),
          ∫ x in carrierIocImage k, f x ∂ μCircle :=
    carrierIocImage_setIntegral_biUnion_finset_wip
      (N := N) (Finset.univ : Finset (Fin N)) f
      (fun k hk => hf.integrableOn)
  have hunion :
      (⋃ k ∈ (Finset.univ : Finset (Fin N)), carrierIocImage k) =
        Set.univ := by
    simpa using carrierIocImage_iUnion_univ_wip (N := N) hN
  rw [hunion, MeasureTheory.setIntegral_univ] at hsum
  simpa using hsum

private theorem carrierArc_setIntegral_univ_wip
    {N : Nat} (hN : 0 < N) (f : Circle -> ℝ)
    (hf : MeasureTheory.Integrable f μCircle) :
    (∫ x, f x ∂ μCircle) =
      ∑ k : Fin N, ∫ x in arcSet (carrierArc N k), f x ∂ μCircle := by
  classical
  calc
    (∫ x, f x ∂ μCircle)
        = ∑ k : Fin N, ∫ x in carrierIocImage k, f x ∂ μCircle :=
          carrierIocImage_setIntegral_univ_wip (N := N) hN f hf
    _ = ∑ k : Fin N,
          ∫ x in arcSet (carrierArc N k), f x ∂ μCircle := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          exact (carrierArc_setIntegral_eq_iocImage_wip k f).symm

private theorem carrierAverage_sub_mean_integral_zero
    {N : Nat} (k : Fin N) (f : Circle -> ℂ)
    (hf : MeasureTheory.Integrable f μCircle) :
    (∫ x in arcSet (carrierArc N k),
        f x - carrierAverage (N := N) k f ∂ μCircle) = 0 := by
  let s : Set Circle := arcSet (carrierArc N k)
  have hNnat : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le k.1) k.2
  have hNneR : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hNnat)
  have hmu : (μCircle.restrict s).real Set.univ = (N : ℝ)⁻¹ := by
    rw [MeasureTheory.Measure.real]
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
    simp only [Set.univ_inter]
    change μCircle.real s = (N : ℝ)⁻¹
    simpa [s] using carrierArc_mu_real_eq_inv_nat k
  haveI : MeasureTheory.IsFiniteMeasure μCircle := by
    dsimp [μCircle]
    infer_instance
  haveI : MeasureTheory.IsFiniteMeasure (μCircle.restrict s) :=
    MeasureTheory.isFiniteMeasureRestrict μCircle s
  have hconst :
      MeasureTheory.Integrable
        (fun _x : Circle => carrierAverage (N := N) k f)
        (μCircle.restrict s) := by
    exact MeasureTheory.integrable_const _
  rw [MeasureTheory.integral_sub hf.restrict hconst]
  rw [MeasureTheory.integral_const]
  simp only [hmu, carrierAverage, s]
  change (∫ x in arcSet (carrierArc N k), f x ∂ μCircle) -
      ((N : ℝ)⁻¹ •
        ((N : ℂ) * ∫ x in arcSet (carrierArc N k), f x ∂ μCircle)) = 0
  rw [show ((N : ℝ)⁻¹ •
        ((N : ℂ) * ∫ x in arcSet (carrierArc N k), f x ∂ μCircle)) =
      ∫ x in arcSet (carrierArc N k), f x ∂ μCircle by
    rw [Complex.real_smul]
    have hcoef : (((N : ℝ)⁻¹ : ℝ) : ℂ) * (N : ℂ) = 1 := by
      norm_cast
      field_simp [hNneR]
    rw [← mul_assoc, hcoef, one_mul]]
  ring

private theorem setIntegral_bias_variance_of_mean_zero
    {α : Type} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    [MeasureTheory.IsFiniteMeasure μ]
    (s : Set α) (f : α -> ℂ) (c : ℂ)
    (hf : MeasureTheory.Integrable f μ)
    (hfsq : MeasureTheory.Integrable (fun x => ‖f x‖ ^ 2) μ)
    (hgc_sq : MeasureTheory.Integrable (fun x => ‖f x - c‖ ^ 2) μ)
    (hmean : (∫ x in s, f x - c ∂ μ) = 0) :
    (∫ x in s, ‖f x‖ ^ 2 ∂ μ) =
      μ.real s * ‖c‖ ^ 2 +
        ∫ x in s, ‖f x - c‖ ^ 2 ∂ μ := by
  haveI : MeasureTheory.IsFiniteMeasure (μ.restrict s) :=
    MeasureTheory.isFiniteMeasureRestrict μ s
  have hconst : MeasureTheory.Integrable (fun _x : α => c) μ := by
    exact MeasureTheory.integrable_const _
  have hgc : MeasureTheory.Integrable (fun x => f x - c) μ :=
    hf.sub hconst
  have hcross :
      ∫ x in s, @inner ℝ ℂ _ c (f x - c) ∂ μ = 0 := by
    have key : ∀ x, @inner ℝ ℂ _ c (f x - c) =
        (innerSL ℝ c) (f x - c) := by
      intro x
      simp [innerSL_apply_apply]
    simp_rw [key]
    rw [ContinuousLinearMap.integral_comp_comm (innerSL ℝ c) hgc.restrict]
    rw [hmean]
    simp
  have hpw : ∀ x, ‖f x‖ ^ 2 - ‖f x - c‖ ^ 2 =
      2 * @inner ℝ ℂ _ c (f x - c) + ‖c‖ ^ 2 := by
    intro x
    have h := norm_add_sq_real c (f x - c)
    simp only [add_sub_cancel] at h
    linarith
  have h1 :
      ∫ x in s, (‖f x‖ ^ 2 - ‖f x - c‖ ^ 2) ∂ μ =
        ∫ x in s,
          (2 * @inner ℝ ℂ _ c (f x - c) + ‖c‖ ^ 2) ∂ μ := by
    congr 1
    ext x
    exact hpw x
  have hsplit :
      ∫ x in s, (‖f x‖ ^ 2 - ‖f x - c‖ ^ 2) ∂ μ =
        (∫ x in s, ‖f x‖ ^ 2 ∂ μ) -
          ∫ x in s, ‖f x - c‖ ^ 2 ∂ μ := by
    exact MeasureTheory.integral_sub hfsq.restrict hgc_sq.restrict
  have hicross :
      MeasureTheory.Integrable
        (fun x => @inner ℝ ℂ _ c (f x - c)) μ := by
    have key : ∀ x, @inner ℝ ℂ _ c (f x - c) =
        (innerSL ℝ c) (f x - c) := by
      intro x
      simp [innerSL_apply_apply]
    rw [show (fun x => @inner ℝ ℂ _ c (f x - c)) =
        fun x => (innerSL ℝ c) (f x - c) by
      funext x
      exact key x]
    exact (innerSL ℝ c).integrable_comp hgc
  have hi2cross :
      MeasureTheory.Integrable
        (fun x => 2 * @inner ℝ ℂ _ c (f x - c)) μ :=
    hicross.const_mul 2
  have hrhs :
      ∫ x in s,
          (2 * @inner ℝ ℂ _ c (f x - c) + ‖c‖ ^ 2) ∂ μ =
        2 * (∫ x in s, @inner ℝ ℂ _ c (f x - c) ∂ μ) +
          μ.real s * ‖c‖ ^ 2 := by
    rw [MeasureTheory.integral_add hi2cross.restrict
      (MeasureTheory.integrable_const _)]
    rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_const]
    simp [MeasureTheory.Measure.real, mul_comm]
  linarith [h1, hsplit, hrhs, hcross]

private theorem carrierAverage_bias_variance
    {N : Nat} (k : Fin N) {L : Nat} (p : Fin L -> ℂ) :
    (∫ x in arcSet (carrierArc N k),
        ‖slowBandPoly p x‖ ^ 2 ∂ μCircle) =
      μCircle.real (arcSet (carrierArc N k)) *
          ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 +
        ∫ x in arcSet (carrierArc N k),
          ‖slowBandPoly p x -
            carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 ∂ μCircle := by
  let f : Circle -> ℂ := slowBandPoly p
  let c : ℂ := carrierAverage (N := N) k f
  have hf_cont : Continuous f := by
    simpa [f] using continuous_slowBandPoly p
  have hfsq_cont : Continuous fun x : Circle => ‖f x‖ ^ 2 :=
    hf_cont.norm.pow 2
  have hgc_sq_cont : Continuous fun x : Circle => ‖f x - c‖ ^ 2 :=
    (hf_cont.sub continuous_const).norm.pow 2
  haveI : MeasureTheory.IsFiniteMeasure μCircle := by
    dsimp [μCircle]
    infer_instance
  have hf : MeasureTheory.Integrable f μCircle := by
    simpa [f, μCircle] using
      hf_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfsq : MeasureTheory.Integrable (fun x : Circle => ‖f x‖ ^ 2) μCircle := by
    simpa [f, μCircle] using
      hfsq_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hgc_sq :
      MeasureTheory.Integrable (fun x : Circle => ‖f x - c‖ ^ 2) μCircle := by
    simpa [f, c, μCircle] using
      hgc_sq_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmean :
      (∫ x in arcSet (carrierArc N k), f x - c ∂ μCircle) = 0 := by
    simpa [f, c] using carrierAverage_sub_mean_integral_zero k f hf
  simpa [f, c] using
    setIntegral_bias_variance_of_mean_zero
      (μ := μCircle) (s := arcSet (carrierArc N k)) f c
      hf hfsq hgc_sq hmean

private theorem carrierAverage_fast_theta_error_le_half_mass_plus_variance
    {N L : Nat} (k : Fin N) (p : Fin L -> ℂ)
    {theta : ℝ} (htheta_nonneg : 0 <= theta)
    (htheta_le_small : theta <= 1 / 64) :
    4 * Crot *
        ∫ x in arcSet (carrierArc N k),
          (4 * theta * ‖bandPoly N p x‖) ^ 2 ∂ μCircle
      <=
        (1 / 2) *
          (arcLength (carrierArc N k) *
            ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2) +
        4 * Crot * (4 * theta) ^ 2 *
          ∫ x in arcSet (carrierArc N k),
            ‖slowBandPoly p x -
              carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 ∂ μCircle := by
  let X : ℝ :=
    arcLength (carrierArc N k) *
      ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2
  let V : ℝ :=
    ∫ x in arcSet (carrierArc N k),
      ‖slowBandPoly p x -
        carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 ∂ μCircle
  have hbv := carrierAverage_bias_variance (N := N) k p
  rw [carrierArc_mu_real_eq_length_div_period k] at hbv
  have hslow_eq :
      (∫ x in arcSet (carrierArc N k),
          ‖slowBandPoly p x‖ ^ 2 ∂ μCircle) =
        (1 / (2 * Real.pi)) * X + V := by
    calc
      (∫ x in arcSet (carrierArc N k),
          ‖slowBandPoly p x‖ ^ 2 ∂ μCircle)
          =
        arcLength (carrierArc N k) / (2 * Real.pi) *
            ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 +
          ∫ x in arcSet (carrierArc N k),
            ‖slowBandPoly p x -
              carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 ∂ μCircle := by
            simpa using hbv
      _ = (1 / (2 * Real.pi)) * X + V := by
            simp [X, V]
            ring
  have hband_eq :
      (∫ x in arcSet (carrierArc N k),
          (4 * theta * ‖bandPoly N p x‖) ^ 2 ∂ μCircle) =
        (4 * theta) ^ 2 *
          ∫ x in arcSet (carrierArc N k),
            ‖slowBandPoly p x‖ ^ 2 ∂ μCircle := by
    calc
      (∫ x in arcSet (carrierArc N k),
          (4 * theta * ‖bandPoly N p x‖) ^ 2 ∂ μCircle)
          =
        ∫ x in arcSet (carrierArc N k),
          (4 * theta) ^ 2 * ‖slowBandPoly p x‖ ^ 2 ∂ μCircle := by
            congr
            ext x
            have hnorm :
                ‖bandPoly N p x‖ = ‖slowBandPoly p x‖ := by
              rw [bandPoly_eq_fast_mul_slow]
              simp [norm_circleChar_wip]
            rw [hnorm]
            ring
      _ =
        (4 * theta) ^ 2 *
          ∫ x in arcSet (carrierArc N k),
            ‖slowBandPoly p x‖ ^ 2 ∂ μCircle := by
            rw [MeasureTheory.integral_const_mul]
  have hcoef :
      4 * Crot * (4 * theta) ^ 2 * (1 / (2 * Real.pi)) <=
        (1 / 2 : ℝ) := by
    unfold Crot
    have htheta_sq : theta ^ 2 <= (1 / 64 : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (theta - 1 / 64)]
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    field_simp [ne_of_gt hpi_pos]
    nlinarith
  have hX_nonneg : 0 <= X := by
    have hell : 0 <= arcLength (carrierArc N k) :=
      arcLength_nonneg (carrierArc N k)
    exact mul_nonneg hell (sq_nonneg _)
  calc
    4 * Crot *
        ∫ x in arcSet (carrierArc N k),
          (4 * theta * ‖bandPoly N p x‖) ^ 2 ∂ μCircle
        =
      4 * Crot * ((4 * theta) ^ 2 *
        ((1 / (2 * Real.pi)) * X + V)) := by
          rw [hband_eq, hslow_eq]
    _ =
      (4 * Crot * (4 * theta) ^ 2 * (1 / (2 * Real.pi))) * X +
        4 * Crot * (4 * theta) ^ 2 * V := by
          ring
    _ <=
      (1 / 2) * X +
        4 * Crot * (4 * theta) ^ 2 * V := by
          have hmul :=
            mul_le_mul_of_nonneg_right hcoef hX_nonneg
          nlinarith
    _ =
      (1 / 2) *
          (arcLength (carrierArc N k) *
            ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2) +
        4 * Crot * (4 * theta) ^ 2 *
          ∫ x in arcSet (carrierArc N k),
            ‖slowBandPoly p x -
              carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 ∂ μCircle := by
        simp [X, V]

private theorem slowBandPoly_l2_eq_average_mass_plus_variance
    {N L : Nat} (hN : 0 < N) (p : Fin L -> ℂ) :
    circleL2Sq (slowBandPoly p) =
      (1 / (2 * Real.pi)) *
          (∑ k : Fin N,
            arcLength (carrierArc N k) *
              ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2) +
        ∑ k : Fin N,
          ∫ x in arcSet (carrierArc N k),
            ‖slowBandPoly p x -
              carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 ∂ μCircle := by
  let f : Circle -> ℝ := fun x => ‖slowBandPoly p x‖ ^ 2
  let Avg : Fin N -> ℝ := fun k =>
    arcLength (carrierArc N k) *
      ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2
  let Var : Fin N -> ℝ := fun k =>
    ∫ x in arcSet (carrierArc N k),
      ‖slowBandPoly p x -
        carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 ∂ μCircle
  have hf_cont : Continuous f :=
    (continuous_slowBandPoly p).norm.pow 2
  have hf_int : MeasureTheory.Integrable f μCircle := by
    simpa [f, μCircle] using
      hf_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hdecomp :
      (∫ x, f x ∂ μCircle) =
        ∑ k : Fin N, ∫ x in arcSet (carrierArc N k), f x ∂ μCircle :=
    carrierArc_setIntegral_univ_wip (N := N) hN f hf_int
  have hlocal :
      ∀ k : Fin N,
        (∫ x in arcSet (carrierArc N k), f x ∂ μCircle) =
          (1 / (2 * Real.pi)) * Avg k + Var k := by
    intro k
    have hbv := carrierAverage_bias_variance (N := N) k p
    rw [carrierArc_mu_real_eq_length_div_period k] at hbv
    calc
      (∫ x in arcSet (carrierArc N k), f x ∂ μCircle)
          =
        arcLength (carrierArc N k) / (2 * Real.pi) *
            ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 +
          ∫ x in arcSet (carrierArc N k),
            ‖slowBandPoly p x -
              carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 ∂ μCircle := by
            simpa [f] using hbv
      _ = (1 / (2 * Real.pi)) * Avg k + Var k := by
            simp [Avg, Var]
            ring
  calc
    circleL2Sq (slowBandPoly p)
        = ∫ x, f x ∂ μCircle := by rfl
    _ = ∑ k : Fin N, ∫ x in arcSet (carrierArc N k), f x ∂ μCircle :=
        hdecomp
    _ = ∑ k : Fin N, ((1 / (2 * Real.pi)) * Avg k + Var k) := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        exact hlocal k
    _ = (1 / (2 * Real.pi)) * (∑ k : Fin N, Avg k) +
          ∑ k : Fin N, Var k := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ =
      (1 / (2 * Real.pi)) *
          (∑ k : Fin N,
            arcLength (carrierArc N k) *
              ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2) +
        ∑ k : Fin N,
          ∫ x in arcSet (carrierArc N k),
            ‖slowBandPoly p x -
              carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 ∂ μCircle := by
        rfl

private theorem zeta_arcParam (I : CircleArc) (t : ℝ) :
    zeta (arcParam I t) =
      Complex.exp (Complex.I * (I.left + t * arcLength I)) := by
  have h := circleChar_mk_wip 1 (I.left + t * arcLength I)
  simpa [circleChar, arcParam, mul_assoc] using h

private theorem carrierArc_chord_le_length {N : Nat} (k : Fin N) :
    ∀ x ∈ arcSet (carrierArc N k),
      ‖zeta x - zeta (carrierBase k)‖ <= arcLength (carrierArc N k) := by
  intro x hx
  rcases hx with ⟨t, ht, htx⟩
  subst x
  let I : CircleArc := carrierArc N k
  have hlen_nonneg : 0 <= arcLength I := arcLength_nonneg I
  have ht_nonneg : 0 <= t := ht.1
  have ht_le : t <= 1 := ht.2
  have hrewrite :
      zeta (arcParam I t) - zeta (carrierBase k) =
        Complex.exp (Complex.I * I.left) *
          (Complex.exp (Complex.I * (t * arcLength I)) - 1) := by
    dsimp [I, carrierBase]
    rw [zeta_arcParam I t, zeta_arcParam I 0]
    have hsum :
        Complex.I * (↑I.left + ↑t * ↑(arcLength I)) =
          Complex.I * ↑I.left + Complex.I * (↑t * ↑(arcLength I)) := by
      ring
    rw [hsum, Complex.exp_add]
    simp [I]
    ring
  calc
    ‖zeta (arcParam I t) - zeta (carrierBase k)‖
        = ‖Complex.exp (Complex.I * I.left) *
          (Complex.exp (Complex.I * (t * arcLength I)) - 1)‖ := by
            rw [hrewrite]
    _ = ‖Complex.exp (Complex.I * (t * arcLength I)) - 1‖ := by
          rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
    _ <= ‖t * arcLength I‖ := by
          simpa [Complex.ofReal_mul] using
            (Real.norm_exp_I_mul_ofReal_sub_one_le (x := t * arcLength I))
    _ = t * arcLength I := by
          rw [Real.norm_of_nonneg (mul_nonneg ht_nonneg hlen_nonneg)]
    _ <= arcLength I := by
          nlinarith

private theorem slowBandPoly_sub_carrierBase_le_slope_length
    {N L : Nat} (k : Fin N) (p : Fin L -> ℂ) :
    ∀ x ∈ arcSet (carrierArc N k),
      ‖slowBandPoly p x - slowBandPoly p (carrierBase k)‖ <=
        (∑ m : Fin L, ‖p m‖ * (m.1 : ℝ)) *
          arcLength (carrierArc N k) := by
  intro x hx
  have hchord := carrierArc_chord_le_length k x hx
  let S : ℝ := ∑ m : Fin L, ‖p m‖ * (m.1 : ℝ)
  have hS_nonneg : 0 <= S := by
    simpa [S] using slowBandPoly_slope_nonneg p
  have hosc := norm_slowBandPoly_sub_le_chord p x (carrierBase k)
  have hmul : S * ‖zeta x - zeta (carrierBase k)‖ <=
      S * arcLength (carrierArc N k) :=
    mul_le_mul_of_nonneg_left hchord hS_nonneg
  exact hosc.trans (by simpa [S] using hmul)

private theorem lowPoly_norm_lower_on_goodCarrier {D N : Nat}
    (q : Fin (D + 1) -> ℂ) {delta : ℝ} (hdelta : 0 <= delta)
    {k : Fin N} (hgood :
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta)
    {x : Circle} (hx : x ∈ arcSet (carrierArc N k)) :
    ‖(polyOfCoeff q).leadingCoeff‖ *
        delta ^ (polyOfCoeff q).roots.card <= ‖lowPoly q x‖ := by
  exact lowPoly_norm_ge_of_roots_dist_ge q x hdelta
    (fun ζ hζ => goodCarrier_root_distance_ge hgood ζ hζ x hx)

private theorem lowPoly_ne_zero_on_goodCarrier {D N : Nat}
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0)
    {delta : ℝ} (hdelta_pos : 0 < delta)
    {k : Fin N} (hgood :
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta)
    {x : Circle} (hx : x ∈ arcSet (carrierArc N k)) :
    lowPoly q x ≠ 0 := by
  have hlower :=
    lowPoly_norm_lower_on_goodCarrier q (le_of_lt hdelta_pos) hgood hx
  have hlead_pos : 0 < ‖(polyOfCoeff q).leadingCoeff‖ :=
    norm_leadingCoeff_polyOfCoeff_pos_of_ne_zero hq
  have hpow_pos : 0 < delta ^ (polyOfCoeff q).roots.card :=
    pow_pos hdelta_pos _
  have hnorm_pos : 0 < ‖lowPoly q x‖ := by
    nlinarith [mul_pos hlead_pos hpow_pos]
  exact norm_pos_iff.mp hnorm_pos

private theorem lowPoly_ne_zero_at_goodCarrierBase {D N : Nat}
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0)
    {delta : ℝ} (hdelta_pos : 0 < delta)
    {k : Fin N} (hgood :
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta) :
    lowPoly q (carrierBase k) ≠ 0 :=
  lowPoly_ne_zero_on_goodCarrier hq hdelta_pos hgood (carrierBase_mem k)

private theorem goodCarrier_factor_of_relative_oscillation {D N : Nat}
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0)
    {delta theta : ℝ} (hdelta_pos : 0 < delta)
    {k : Fin N} (hgood :
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta)
    (hosc : ∀ x ∈ arcSet (carrierArc N k),
      ‖lowPoly q x - lowPoly q (carrierBase k)‖ <=
        theta * ‖lowPoly q (carrierBase k)‖) :
    ∀ x ∈ arcSet (carrierArc N k),
      ∃ lam : ℂ,
        lowPoly q x = lam * lowPoly q (carrierBase k) ∧
          ‖lam - 1‖ <= theta := by
  intro x hx
  exact exists_factor_close_of_norm_sub_le
    (lowPoly_ne_zero_at_goodCarrierBase hq hdelta_pos hgood) (hosc x hx)

private theorem goodCarrier_relative_oscillation_of_absolute_bound
    {D N : Nat} (q : Fin (D + 1) -> ℂ)
    {delta theta : ℝ} (hdelta_pos : 0 < delta) (htheta_nonneg : 0 <= theta)
    {k : Fin N} (hgood :
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta)
    (habs : ∀ x ∈ arcSet (carrierArc N k),
      ‖lowPoly q x - lowPoly q (carrierBase k)‖ <=
        theta *
          (‖(polyOfCoeff q).leadingCoeff‖ *
            delta ^ (polyOfCoeff q).roots.card)) :
    ∀ x ∈ arcSet (carrierArc N k),
      ‖lowPoly q x - lowPoly q (carrierBase k)‖ <=
        theta * ‖lowPoly q (carrierBase k)‖ := by
  intro x hx
  have hbase_lower :=
    lowPoly_norm_lower_on_goodCarrier q (le_of_lt hdelta_pos) hgood
      (carrierBase_mem k)
  have hmul :
      theta *
          (‖(polyOfCoeff q).leadingCoeff‖ *
            delta ^ (polyOfCoeff q).roots.card) <=
        theta * ‖lowPoly q (carrierBase k)‖ :=
    mul_le_mul_of_nonneg_left hbase_lower htheta_nonneg
  exact (habs x hx).trans hmul

private theorem goodCarrier_relative_oscillation_of_root_product_chord_bound
    {D N : Nat} (q : Fin (D + 1) -> ℂ)
    {delta eps theta : ℝ} (heps : 0 <= eps)
    (htheta :
      (1 + eps) ^ (polyOfCoeff q).roots.card - 1 <= theta)
    {k : Fin N} (hgood :
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta)
    (hchord : ∀ x ∈ arcSet (carrierArc N k),
      ‖zeta x - zeta (carrierBase k)‖ <= eps * delta) :
    ∀ x ∈ arcSet (carrierArc N k),
      ‖lowPoly q x - lowPoly q (carrierBase k)‖ <=
        theta * ‖lowPoly q (carrierBase k)‖ := by
  intro x hx
  refine lowPoly_relative_oscillation_of_root_factor_bound
    q x (carrierBase k) heps htheta ?_
  intro ζ hζ
  have hbase :
      delta <= ‖zeta (carrierBase k) - ζ‖ :=
    goodCarrier_root_distance_ge hgood ζ hζ
      (carrierBase k) (carrierBase_mem k)
  have hdelta_to_root :
      eps * delta <= eps * ‖zeta (carrierBase k) - ζ‖ :=
    mul_le_mul_of_nonneg_left hbase heps
  calc
    ‖(zeta x - ζ) - (zeta (carrierBase k) - ζ)‖
        = ‖zeta x - zeta (carrierBase k)‖ := by
          congr 1
          ring
    _ <= eps * delta := hchord x hx
    _ <= eps * ‖zeta (carrierBase k) - ζ‖ := hdelta_to_root

private theorem goodCarrier_relative_oscillation_of_root_product_arcLength_bound
    {D N : Nat} (q : Fin (D + 1) -> ℂ)
    {delta eps theta : ℝ} (heps : 0 <= eps)
    (htheta :
      (1 + eps) ^ (polyOfCoeff q).roots.card - 1 <= theta)
    {k : Fin N} (hgood :
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta)
    (harc : arcLength (carrierArc N k) <= eps * delta) :
    ∀ x ∈ arcSet (carrierArc N k),
      ‖lowPoly q x - lowPoly q (carrierBase k)‖ <=
        theta * ‖lowPoly q (carrierBase k)‖ := by
  exact goodCarrier_relative_oscillation_of_root_product_chord_bound
    q heps htheta hgood
    (fun x hx => (carrierArc_chord_le_length k x hx).trans harc)

private theorem goodCarrier_absolute_oscillation_of_chord_bound
    {D N : Nat} (q : Fin (D + 1) -> ℂ)
    {delta theta R : ℝ} {k : Fin N}
    (hchord : ∀ x ∈ arcSet (carrierArc N k),
      ‖zeta x - zeta (carrierBase k)‖ <= R)
    (hslope :
      (∑ n : Fin (D + 1), ‖q n‖ * (n.1 : ℝ)) * R <=
        theta *
          (‖(polyOfCoeff q).leadingCoeff‖ *
            delta ^ (polyOfCoeff q).roots.card)) :
    ∀ x ∈ arcSet (carrierArc N k),
      ‖lowPoly q x - lowPoly q (carrierBase k)‖ <=
        theta *
          (‖(polyOfCoeff q).leadingCoeff‖ *
            delta ^ (polyOfCoeff q).roots.card) := by
  intro x hx
  let S : ℝ := ∑ n : Fin (D + 1), ‖q n‖ * (n.1 : ℝ)
  have hS_nonneg : 0 <= S := by
    simpa [S] using lowPoly_slope_nonneg q
  have hosc := norm_lowPoly_sub_le_chord q x (carrierBase k)
  have hSR : S * ‖zeta x - zeta (carrierBase k)‖ <= S * R :=
    mul_le_mul_of_nonneg_left (hchord x hx) hS_nonneg
  exact hosc.trans (hSR.trans (by simpa [S] using hslope))

private theorem goodCarrier_defect_compare_band {D N L : Nat}
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) (p : Fin L -> ℂ)
    {delta theta : ℝ} (hdelta_pos : 0 < delta)
    (htheta_nonneg : 0 <= theta) (htheta_le : theta <= 1 / 2)
    {k : Fin N} (hgood :
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta)
    (hosc : ∀ x ∈ arcSet (carrierArc N k),
      ‖lowPoly q x - lowPoly q (carrierBase k)‖ <=
        theta * ‖lowPoly q (carrierBase k)‖) :
    (1 / 2) *
        ∫ x in arcSet (carrierArc N k),
          (‖lowPoly q (carrierBase k) + bandPoly N p x‖ -
            ‖lowPoly q (carrierBase k)‖) ^ 2 ∂ μCircle -
        ∫ x in arcSet (carrierArc N k),
          (4 * theta * ‖bandPoly N p x‖) ^ 2 ∂ μCircle
      <=
        ∫ x in arcSet (carrierArc N k),
          (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle := by
  exact defect_setIntegral_const_center_compare_band
    (arcSet (carrierArc N k)) (measurableSet_arcSet (carrierArc N k))
    (lowPoly q) (continuous_lowPoly q) N p
    (lowPoly_ne_zero_at_goodCarrierBase hq hdelta_pos hgood)
    htheta_nonneg htheta_le
    (goodCarrier_factor_of_relative_oscillation hq hdelta_pos hgood hosc)

private theorem goodCarrier_defect_compare_band_of_absolute_bound {D N L : Nat}
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) (p : Fin L -> ℂ)
    {delta theta : ℝ} (hdelta_pos : 0 < delta)
    (htheta_nonneg : 0 <= theta) (htheta_le : theta <= 1 / 2)
    {k : Fin N} (hgood :
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta)
    (habs : ∀ x ∈ arcSet (carrierArc N k),
      ‖lowPoly q x - lowPoly q (carrierBase k)‖ <=
        theta *
          (‖(polyOfCoeff q).leadingCoeff‖ *
            delta ^ (polyOfCoeff q).roots.card)) :
    (1 / 2) *
        ∫ x in arcSet (carrierArc N k),
          (‖lowPoly q (carrierBase k) + bandPoly N p x‖ -
            ‖lowPoly q (carrierBase k)‖) ^ 2 ∂ μCircle -
        ∫ x in arcSet (carrierArc N k),
          (4 * theta * ‖bandPoly N p x‖) ^ 2 ∂ μCircle
      <=
        ∫ x in arcSet (carrierArc N k),
          (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle := by
  exact goodCarrier_defect_compare_band (q := q) hq p
    hdelta_pos htheta_nonneg htheta_le hgood
    (goodCarrier_relative_oscillation_of_absolute_bound q
      hdelta_pos htheta_nonneg hgood habs)

private theorem goodCarrier_defect_compare_band_of_chord_bound {D N L : Nat}
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) (p : Fin L -> ℂ)
    {delta theta R : ℝ} (hdelta_pos : 0 < delta)
    (htheta_nonneg : 0 <= theta) (htheta_le : theta <= 1 / 2)
    {k : Fin N} (hgood :
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta)
    (hchord : ∀ x ∈ arcSet (carrierArc N k),
      ‖zeta x - zeta (carrierBase k)‖ <= R)
    (hslope :
      (∑ n : Fin (D + 1), ‖q n‖ * (n.1 : ℝ)) * R <=
        theta *
          (‖(polyOfCoeff q).leadingCoeff‖ *
            delta ^ (polyOfCoeff q).roots.card)) :
    (1 / 2) *
        ∫ x in arcSet (carrierArc N k),
          (‖lowPoly q (carrierBase k) + bandPoly N p x‖ -
            ‖lowPoly q (carrierBase k)‖) ^ 2 ∂ μCircle -
        ∫ x in arcSet (carrierArc N k),
          (4 * theta * ‖bandPoly N p x‖) ^ 2 ∂ μCircle
      <=
        ∫ x in arcSet (carrierArc N k),
          (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle := by
  exact goodCarrier_defect_compare_band_of_absolute_bound
    (q := q) hq p hdelta_pos htheta_nonneg htheta_le hgood
    (goodCarrier_absolute_oscillation_of_chord_bound q hchord hslope)

private theorem goodCarrier_defect_compare_band_of_arcLength_slope {D N L : Nat}
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) (p : Fin L -> ℂ)
    {delta theta : ℝ} (hdelta_pos : 0 < delta)
    (htheta_nonneg : 0 <= theta) (htheta_le : theta <= 1 / 2)
    {k : Fin N} (hgood :
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta)
    (hslope :
      (∑ n : Fin (D + 1), ‖q n‖ * (n.1 : ℝ)) *
          arcLength (carrierArc N k) <=
        theta *
          (‖(polyOfCoeff q).leadingCoeff‖ *
            delta ^ (polyOfCoeff q).roots.card)) :
    (1 / 2) *
        ∫ x in arcSet (carrierArc N k),
          (‖lowPoly q (carrierBase k) + bandPoly N p x‖ -
            ‖lowPoly q (carrierBase k)‖) ^ 2 ∂ μCircle -
        ∫ x in arcSet (carrierArc N k),
          (4 * theta * ‖bandPoly N p x‖) ^ 2 ∂ μCircle
      <=
        ∫ x in arcSet (carrierArc N k),
          (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle := by
  exact goodCarrier_defect_compare_band_of_chord_bound
    (q := q) hq p hdelta_pos htheta_nonneg htheta_le hgood
    (carrierArc_chord_le_length k) hslope

private theorem goodCarrier_base_mass_le_actual_defect_plus_fast_variance_error
    {D N L : Nat}
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) (p : Fin L -> ℂ)
    {delta theta : ℝ} (hdelta_pos : 0 < delta)
    (htheta_nonneg : 0 <= theta) (htheta_le : theta <= 1 / 2)
    {k : Fin N} (hgood :
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta)
    (hosc : ∀ x ∈ arcSet (carrierArc N k),
      ‖lowPoly q x - lowPoly q (carrierBase k)‖ <=
        theta * ‖lowPoly q (carrierBase k)‖) :
    arcLength (carrierArc N k) *
        ‖slowBandPoly p (carrierBase k)‖ ^ 2 <=
      4 * Crot *
          ∫ x in arcSet (carrierArc N k),
            (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle +
        4 * Crot *
          ∫ x in arcSet (carrierArc N k),
            ‖slowBandPoly p x - slowBandPoly p (carrierBase k)‖ ^ 2 ∂ μCircle +
        2 * Crot *
          ∫ _x in arcSet (carrierArc N k),
            (4 * theta * ‖slowBandPoly p (carrierBase k)‖) ^ 2 ∂ μCircle := by
  let s : Set Circle := arcSet (carrierArc N k)
  let c : ℂ := lowPoly q (carrierBase k)
  let u : ℂ := slowBandPoly p (carrierBase k)
  let A : ℝ :=
    ∫ x in s, (‖c + circleChar N x * u‖ - ‖c‖) ^ 2 ∂ μCircle
  let B : ℝ :=
    ∫ x in s,
      (‖lowPoly q x + circleChar N x * u‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle
  let Dint : ℝ :=
    ∫ x in s,
      (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle
  let V : ℝ :=
    ∫ x in s, ‖slowBandPoly p x - u‖ ^ 2 ∂ μCircle
  let E : ℝ :=
    ∫ _x in s, (4 * theta * ‖u‖) ^ 2 ∂ μCircle
  have hc : c ≠ 0 := by
    dsimp [c]
    exact lowPoly_ne_zero_at_goodCarrierBase hq hdelta_pos hgood
  have hrot :
      arcLength (carrierArc N k) * ‖u‖ ^ 2 <= Crot * A := by
    simpa [A, c, u, s, arcIntegral] using
      constantCenter_fastRotate_carrierArc_sq_le_defectSq
        (N := N) k (c := c) (u := u) hc
  have hfast_compare :
      (1 / 2) * A - E <= B := by
    have h :=
      defect_setIntegral_const_center_compare_fast
        s (measurableSet_arcSet (carrierArc N k))
        (lowPoly q) (continuous_lowPoly q) N
        (c := c) (u := u) (theta := theta)
        hc htheta_nonneg htheta_le
        (goodCarrier_factor_of_relative_oscillation hq hdelta_pos hgood hosc)
    simpa [A, B, E, c, u, s] using h
  have hsafe :
      (1 / 2) * B - V <= Dint := by
    have h :=
      defect_setIntegral_safe_carrier_average
        s (lowPoly q) (continuous_lowPoly q) N p u
    simpa [B, Dint, V, u, s] using h
  have hA : A <= 4 * Dint + 4 * V + 2 * E := by
    nlinarith
  have hmul : Crot * A <= Crot * (4 * Dint + 4 * V + 2 * E) :=
    mul_le_mul_of_nonneg_left hA (le_of_lt Crot_pos)
  calc
    arcLength (carrierArc N k) *
        ‖slowBandPoly p (carrierBase k)‖ ^ 2
        <= Crot * A := by
          simpa [u] using hrot
    _ <= Crot * (4 * Dint + 4 * V + 2 * E) := hmul
    _ =
      4 * Crot *
          ∫ x in arcSet (carrierArc N k),
            (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle +
        4 * Crot *
          ∫ x in arcSet (carrierArc N k),
            ‖slowBandPoly p x - slowBandPoly p (carrierBase k)‖ ^ 2 ∂ μCircle +
        2 * Crot *
          ∫ _x in arcSet (carrierArc N k),
            (4 * theta * ‖slowBandPoly p (carrierBase k)‖) ^ 2 ∂ μCircle := by
          simp [Dint, V, E, u, s]
          ring

private theorem goodCarrier_base_mass_le_actual_defect_plus_fast_variance_error_of_arcLength_slope
    {D N L : Nat}
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) (p : Fin L -> ℂ)
    {delta theta : ℝ} (hdelta_pos : 0 < delta)
    (htheta_nonneg : 0 <= theta) (htheta_le : theta <= 1 / 2)
    {k : Fin N} (hgood :
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta)
    (hslope :
      (∑ n : Fin (D + 1), ‖q n‖ * (n.1 : ℝ)) *
          arcLength (carrierArc N k) <=
        theta *
          (‖(polyOfCoeff q).leadingCoeff‖ *
            delta ^ (polyOfCoeff q).roots.card)) :
    arcLength (carrierArc N k) *
        ‖slowBandPoly p (carrierBase k)‖ ^ 2 <=
      4 * Crot *
          ∫ x in arcSet (carrierArc N k),
            (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle +
        4 * Crot *
          ∫ x in arcSet (carrierArc N k),
            ‖slowBandPoly p x - slowBandPoly p (carrierBase k)‖ ^ 2 ∂ μCircle +
        2 * Crot *
          ∫ _x in arcSet (carrierArc N k),
            (4 * theta * ‖slowBandPoly p (carrierBase k)‖) ^ 2 ∂ μCircle := by
  exact goodCarrier_base_mass_le_actual_defect_plus_fast_variance_error
    (q := q) hq p hdelta_pos htheta_nonneg htheta_le hgood
    (goodCarrier_relative_oscillation_of_absolute_bound q
      hdelta_pos htheta_nonneg hgood
      (goodCarrier_absolute_oscillation_of_chord_bound q
        (carrierArc_chord_le_length k) hslope))

private theorem carrier_fast_theta_error_le_half_base
    {N L : Nat} (k : Fin N) (p : Fin L -> ℂ)
    {theta : ℝ} (htheta_nonneg : 0 <= theta)
    (htheta_le_small : theta <= 1 / 64) :
    2 * Crot *
        ∫ _x in arcSet (carrierArc N k),
          (4 * theta * ‖slowBandPoly p (carrierBase k)‖) ^ 2 ∂ μCircle
      <=
        (1 / 2) *
          (arcLength (carrierArc N k) *
            ‖slowBandPoly p (carrierBase k)‖ ^ 2) := by
  let u : ℂ := slowBandPoly p (carrierBase k)
  let s : Set Circle := arcSet (carrierArc N k)
  haveI : MeasureTheory.IsFiniteMeasure μCircle := by
    dsimp [μCircle]
    infer_instance
  have hconst :
      (∫ _x in s, (4 * theta * ‖u‖) ^ 2 ∂ μCircle) =
        (4 * theta * ‖u‖) ^ 2 * μCircle.real s := by
    rw [MeasureTheory.integral_const]
    simp [MeasureTheory.Measure.real, mul_comm]
  have htheta_sq : theta ^ 2 <= (1 / 64 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (theta - 1 / 64)]
  have hell_nonneg : 0 <= arcLength (carrierArc N k) :=
    arcLength_nonneg (carrierArc N k)
  have hnorm_sq : 0 <= ‖u‖ ^ 2 := sq_nonneg ‖u‖
  rw [show
      (∫ _x in arcSet (carrierArc N k),
          (4 * theta * ‖slowBandPoly p (carrierBase k)‖) ^ 2 ∂ μCircle) =
        (∫ _x in s, (4 * theta * ‖u‖) ^ 2 ∂ μCircle) by
        simp [s, u]]
  rw [hconst, carrierArc_mu_real_eq_length_div_period k]
  unfold Crot
  have hpi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hu_norm :
      ‖u‖ ^ 2 = ‖slowBandPoly p (carrierBase k)‖ ^ 2 := by
    rfl
  have hcoef : 2 * 64 * 4 ^ 2 * theta ^ 2 <= (1 : ℝ) := by
    nlinarith
  have hcoefprod :
      2 * 64 * 4 ^ 2 * theta ^ 2 * ‖u‖ ^ 2 *
          arcLength (carrierArc N k) <=
        arcLength (carrierArc N k) *
          ‖slowBandPoly p (carrierBase k)‖ ^ 2 := by
    have hprod_nonneg : 0 <= ‖u‖ ^ 2 * arcLength (carrierArc N k) :=
      mul_nonneg hnorm_sq hell_nonneg
    have hmul :
        (2 * 64 * 4 ^ 2 * theta ^ 2) *
            (‖u‖ ^ 2 * arcLength (carrierArc N k)) <=
          1 * (‖u‖ ^ 2 * arcLength (carrierArc N k)) :=
      mul_le_mul_of_nonneg_right hcoef hprod_nonneg
    calc
      2 * 64 * 4 ^ 2 * theta ^ 2 * ‖u‖ ^ 2 *
          arcLength (carrierArc N k)
          =
        (2 * 64 * 4 ^ 2 * theta ^ 2) *
            (‖u‖ ^ 2 * arcLength (carrierArc N k)) := by ring
      _ <= 1 * (‖u‖ ^ 2 * arcLength (carrierArc N k)) := hmul
      _ =
        arcLength (carrierArc N k) *
          ‖slowBandPoly p (carrierBase k)‖ ^ 2 := by
          rw [hu_norm]
          ring
  field_simp [hpi_ne]
  linarith

private theorem
    goodCarrier_base_mass_le_actual_defect_plus_fast_variance_absorbed_of_arcLength_slope
    {D N L : Nat}
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) (p : Fin L -> ℂ)
    {delta theta : ℝ} (hdelta_pos : 0 < delta)
    (htheta_nonneg : 0 <= theta) (htheta_le : theta <= 1 / 2)
    (htheta_le_small : theta <= 1 / 64)
    {k : Fin N} (hgood :
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta)
    (hslope :
      (∑ n : Fin (D + 1), ‖q n‖ * (n.1 : ℝ)) *
          arcLength (carrierArc N k) <=
        theta *
          (‖(polyOfCoeff q).leadingCoeff‖ *
            delta ^ (polyOfCoeff q).roots.card)) :
    arcLength (carrierArc N k) *
        ‖slowBandPoly p (carrierBase k)‖ ^ 2 <=
      8 * Crot *
          ∫ x in arcSet (carrierArc N k),
            (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle +
        8 * Crot *
          ∫ x in arcSet (carrierArc N k),
            ‖slowBandPoly p x - slowBandPoly p (carrierBase k)‖ ^ 2 ∂ μCircle := by
  let X : ℝ :=
    arcLength (carrierArc N k) *
      ‖slowBandPoly p (carrierBase k)‖ ^ 2
  let Dint : ℝ :=
    ∫ x in arcSet (carrierArc N k),
      (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle
  let V : ℝ :=
    ∫ x in arcSet (carrierArc N k),
      ‖slowBandPoly p x - slowBandPoly p (carrierBase k)‖ ^ 2 ∂ μCircle
  let E : ℝ :=
    2 * Crot *
      ∫ _x in arcSet (carrierArc N k),
        (4 * theta * ‖slowBandPoly p (carrierBase k)‖) ^ 2 ∂ μCircle
  have hraw :
      X <= 4 * Crot * Dint + 4 * Crot * V + E := by
    simpa [X, Dint, V, E] using
      goodCarrier_base_mass_le_actual_defect_plus_fast_variance_error_of_arcLength_slope
        (q := q) hq p hdelta_pos htheta_nonneg htheta_le hgood hslope
  have hE : E <= (1 / 2) * X := by
    simpa [X, E] using
      carrier_fast_theta_error_le_half_base (N := N) (L := L) k p
        htheta_nonneg htheta_le_small
  calc
    X <= 4 * Crot * Dint + 4 * Crot * V + E := hraw
    _ <= 4 * Crot * Dint + 4 * Crot * V + (1 / 2) * X := by
      nlinarith
    _ <= 8 * Crot * Dint + 8 * Crot * V := by
      nlinarith

private theorem goodCarrier_base_mass_le_actual_defect_plus_fast_variance_absorbed
    {D N L : Nat}
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) (p : Fin L -> ℂ)
    {delta theta : ℝ} (hdelta_pos : 0 < delta)
    (htheta_nonneg : 0 <= theta) (htheta_le : theta <= 1 / 2)
    (htheta_le_small : theta <= 1 / 64)
    {k : Fin N} (hgood :
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta)
    (hosc : ∀ x ∈ arcSet (carrierArc N k),
      ‖lowPoly q x - lowPoly q (carrierBase k)‖ <=
        theta * ‖lowPoly q (carrierBase k)‖) :
    arcLength (carrierArc N k) *
        ‖slowBandPoly p (carrierBase k)‖ ^ 2 <=
      8 * Crot *
          ∫ x in arcSet (carrierArc N k),
            (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle +
        8 * Crot *
          ∫ x in arcSet (carrierArc N k),
            ‖slowBandPoly p x - slowBandPoly p (carrierBase k)‖ ^ 2 ∂ μCircle := by
  let X : ℝ :=
    arcLength (carrierArc N k) *
      ‖slowBandPoly p (carrierBase k)‖ ^ 2
  let Dint : ℝ :=
    ∫ x in arcSet (carrierArc N k),
      (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle
  let V : ℝ :=
    ∫ x in arcSet (carrierArc N k),
      ‖slowBandPoly p x - slowBandPoly p (carrierBase k)‖ ^ 2 ∂ μCircle
  let E : ℝ :=
    2 * Crot *
      ∫ _x in arcSet (carrierArc N k),
        (4 * theta * ‖slowBandPoly p (carrierBase k)‖) ^ 2 ∂ μCircle
  have hraw :
      X <= 4 * Crot * Dint + 4 * Crot * V + E := by
    simpa [X, Dint, V, E] using
      goodCarrier_base_mass_le_actual_defect_plus_fast_variance_error
        (q := q) hq p hdelta_pos htheta_nonneg htheta_le hgood hosc
  have hE : E <= (1 / 2) * X := by
    simpa [X, E] using
      carrier_fast_theta_error_le_half_base (N := N) (L := L) k p
        htheta_nonneg htheta_le_small
  calc
    X <= 4 * Crot * Dint + 4 * Crot * V + E := hraw
    _ <= 4 * Crot * Dint + 4 * Crot * V + (1 / 2) * X := by
      nlinarith
    _ <= 8 * Crot * Dint + 8 * Crot * V := by
      nlinarith

private theorem
    goodCarrier_base_mass_le_actual_defect_plus_fast_variance_absorbed_of_root_product_arcLength
    {D N L : Nat}
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) (p : Fin L -> ℂ)
    {delta eps theta : ℝ} (hdelta_pos : 0 < delta)
    (heps : 0 <= eps)
    (htheta_bound :
      (1 + eps) ^ (polyOfCoeff q).roots.card - 1 <= theta)
    (htheta_nonneg : 0 <= theta) (htheta_le : theta <= 1 / 2)
    (htheta_le_small : theta <= 1 / 64)
    {k : Fin N} (hgood :
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta)
    (harc : arcLength (carrierArc N k) <= eps * delta) :
    arcLength (carrierArc N k) *
        ‖slowBandPoly p (carrierBase k)‖ ^ 2 <=
      8 * Crot *
          ∫ x in arcSet (carrierArc N k),
            (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle +
        8 * Crot *
          ∫ x in arcSet (carrierArc N k),
            ‖slowBandPoly p x - slowBandPoly p (carrierBase k)‖ ^ 2 ∂ μCircle := by
  exact goodCarrier_base_mass_le_actual_defect_plus_fast_variance_absorbed
    (q := q) hq p hdelta_pos htheta_nonneg htheta_le htheta_le_small
    hgood
    (goodCarrier_relative_oscillation_of_root_product_arcLength_bound
      q heps htheta_bound hgood harc)

private theorem goodCarrier_average_mass_le_actual_defect_plus_errors
    {D N L : Nat}
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) (p : Fin L -> ℂ)
    {delta theta : ℝ} (hdelta_pos : 0 < delta)
    (htheta_nonneg : 0 <= theta) (htheta_le : theta <= 1 / 2)
    {k : Fin N} (hgood :
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta)
    (hosc : ∀ x ∈ arcSet (carrierArc N k),
      ‖lowPoly q x - lowPoly q (carrierBase k)‖ <=
        theta * ‖lowPoly q (carrierBase k)‖) :
    arcLength (carrierArc N k) *
        ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 <=
      4 * Crot *
          ∫ x in arcSet (carrierArc N k),
            (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle +
        4 * Crot *
          ∫ x in arcSet (carrierArc N k),
            (4 * theta * ‖bandPoly N p x‖) ^ 2 ∂ μCircle +
        2 * Crot *
          arcIntegral (carrierArc N k)
            (fun x =>
              ‖slowBandPoly p x -
                carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2) := by
  let c : ℂ := lowPoly q (carrierBase k)
  let A : ℝ :=
    ∫ x in arcSet (carrierArc N k),
      (‖c + bandPoly N p x‖ - ‖c‖) ^ 2 ∂ μCircle
  let Dint : ℝ :=
    ∫ x in arcSet (carrierArc N k),
      (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle
  let E : ℝ :=
    ∫ x in arcSet (carrierArc N k),
      (4 * theta * ‖bandPoly N p x‖) ^ 2 ∂ μCircle
  let V : ℝ :=
    arcIntegral (carrierArc N k)
      (fun x =>
        ‖slowBandPoly p x -
          carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact lowPoly_ne_zero_at_goodCarrierBase hq hdelta_pos hgood
  have havg :
      arcLength (carrierArc N k) *
          ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 <=
        2 * Crot * A + 2 * Crot * V := by
    exact carrierAverage_mass_le_defect_plus_variance (N := N) k p hc
  have hcompare :
      (1 / 2) * A - E <= Dint := by
    simpa [A, Dint, E, c] using
      goodCarrier_defect_compare_band
        (q := q) hq p hdelta_pos htheta_nonneg htheta_le hgood hosc
  have hA : A <= 2 * Dint + 2 * E := by
    nlinarith
  calc
    arcLength (carrierArc N k) *
        ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2
        <= 2 * Crot * A + 2 * Crot * V := havg
    _ <= 2 * Crot * (2 * Dint + 2 * E) + 2 * Crot * V := by
      have hcoef_nonneg : 0 <= 2 * Crot := by
        nlinarith [Crot_pos]
      have hmul :
          2 * Crot * A <= 2 * Crot * (2 * Dint + 2 * E) :=
        mul_le_mul_of_nonneg_left hA hcoef_nonneg
      nlinarith
    _ =
      4 * Crot *
          ∫ x in arcSet (carrierArc N k),
            (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle +
        4 * Crot *
          ∫ x in arcSet (carrierArc N k),
            (4 * theta * ‖bandPoly N p x‖) ^ 2 ∂ μCircle +
        2 * Crot *
          arcIntegral (carrierArc N k)
            (fun x =>
              ‖slowBandPoly p x -
                carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2) := by
          simp [Dint, E, V]
          ring

private theorem goodCarrier_average_mass_le_actual_defect_plus_fast_variance_absorbed
    {D N L : Nat}
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) (p : Fin L -> ℂ)
    {delta theta : ℝ} (hdelta_pos : 0 < delta)
    (htheta_nonneg : 0 <= theta) (htheta_le : theta <= 1 / 2)
    (htheta_le_small : theta <= 1 / 64)
    {k : Fin N} (hgood :
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta)
    (hosc : ∀ x ∈ arcSet (carrierArc N k),
      ‖lowPoly q x - lowPoly q (carrierBase k)‖ <=
        theta * ‖lowPoly q (carrierBase k)‖) :
    arcLength (carrierArc N k) *
        ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 <=
      8 * Crot *
          ∫ x in arcSet (carrierArc N k),
            (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle +
        (8 * Crot * (4 * theta) ^ 2 + 4 * Crot) *
          ∫ x in arcSet (carrierArc N k),
            ‖slowBandPoly p x -
              carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 ∂ μCircle := by
  let X : ℝ :=
    arcLength (carrierArc N k) *
      ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2
  let Dint : ℝ :=
    ∫ x in arcSet (carrierArc N k),
      (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle
  let E : ℝ :=
    ∫ x in arcSet (carrierArc N k),
      (4 * theta * ‖bandPoly N p x‖) ^ 2 ∂ μCircle
  let V : ℝ :=
    ∫ x in arcSet (carrierArc N k),
      ‖slowBandPoly p x -
        carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 ∂ μCircle
  have hraw :
      X <= 4 * Crot * Dint + 4 * Crot * E + 2 * Crot * V := by
    exact goodCarrier_average_mass_le_actual_defect_plus_errors
      (q := q) hq p hdelta_pos htheta_nonneg htheta_le hgood hosc
  have hE :
      4 * Crot * E <= (1 / 2) * X +
        4 * Crot * (4 * theta) ^ 2 * V := by
    simpa [X, E, V] using
      carrierAverage_fast_theta_error_le_half_mass_plus_variance
        (N := N) (L := L) k p htheta_nonneg htheta_le_small
  calc
    X <= 4 * Crot * Dint + 4 * Crot * E + 2 * Crot * V := hraw
    _ <=
        4 * Crot * Dint +
          ((1 / 2) * X + 4 * Crot * (4 * theta) ^ 2 * V) +
          2 * Crot * V := by
          nlinarith
    _ <=
        8 * Crot * Dint +
          (8 * Crot * (4 * theta) ^ 2 + 4 * Crot) * V := by
          nlinarith
    _ =
      8 * Crot *
          ∫ x in arcSet (carrierArc N k),
            (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle +
        (8 * Crot * (4 * theta) ^ 2 + 4 * Crot) *
          ∫ x in arcSet (carrierArc N k),
            ‖slowBandPoly p x -
              carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 ∂ μCircle := by
        simp [Dint, V]

private theorem
    goodCarrier_average_mass_le_actual_defect_plus_fast_variance_absorbed_of_root_product_arcLength
    {D N L : Nat}
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) (p : Fin L -> ℂ)
    {delta eps theta : ℝ} (hdelta_pos : 0 < delta)
    (heps : 0 <= eps)
    (htheta_bound :
      (1 + eps) ^ (polyOfCoeff q).roots.card - 1 <= theta)
    (htheta_nonneg : 0 <= theta) (htheta_le : theta <= 1 / 2)
    (htheta_le_small : theta <= 1 / 64)
    {k : Fin N} (hgood :
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta)
    (harc : arcLength (carrierArc N k) <= eps * delta) :
    arcLength (carrierArc N k) *
        ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 <=
      8 * Crot *
          ∫ x in arcSet (carrierArc N k),
            (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle +
        (8 * Crot * (4 * theta) ^ 2 + 4 * Crot) *
          ∫ x in arcSet (carrierArc N k),
            ‖slowBandPoly p x -
              carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 ∂ μCircle := by
  exact
    goodCarrier_average_mass_le_actual_defect_plus_fast_variance_absorbed
      (q := q) hq p hdelta_pos htheta_nonneg htheta_le htheta_le_small
      hgood
      (goodCarrier_relative_oscillation_of_root_product_arcLength_bound
        q heps htheta_bound hgood harc)

private theorem goodCarrier_base_mass_le_actual_defect_plus_errors
    {D N L : Nat}
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) (p : Fin L -> ℂ)
    {delta theta : ℝ} (hdelta_pos : 0 < delta)
    (htheta_nonneg : 0 <= theta) (htheta_le : theta <= 1 / 2)
    {k : Fin N} (hgood :
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta)
    (hosc : ∀ x ∈ arcSet (carrierArc N k),
      ‖lowPoly q x - lowPoly q (carrierBase k)‖ <=
        theta * ‖lowPoly q (carrierBase k)‖) :
    arcLength (carrierArc N k) *
        ‖slowBandPoly p (carrierBase k)‖ ^ 2 <=
      4 * Crot *
          ∫ x in arcSet (carrierArc N k),
            (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle +
        4 * Crot *
          ∫ x in arcSet (carrierArc N k),
            (4 * theta * ‖bandPoly N p x‖) ^ 2 ∂ μCircle +
        2 * Crot *
          arcIntegral (carrierArc N k)
            (fun x =>
              ‖slowBandPoly p x - slowBandPoly p (carrierBase k)‖ ^ 2) := by
  let c : ℂ := lowPoly q (carrierBase k)
  let u : ℂ := slowBandPoly p (carrierBase k)
  let A : ℝ :=
    ∫ x in arcSet (carrierArc N k),
      (‖c + bandPoly N p x‖ - ‖c‖) ^ 2 ∂ μCircle
  let Dint : ℝ :=
    ∫ x in arcSet (carrierArc N k),
      (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle
  let E : ℝ :=
    ∫ x in arcSet (carrierArc N k),
      (4 * theta * ‖bandPoly N p x‖) ^ 2 ∂ μCircle
  let V : ℝ :=
    arcIntegral (carrierArc N k)
      (fun x => ‖slowBandPoly p x - u‖ ^ 2)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact lowPoly_ne_zero_at_goodCarrierBase hq hdelta_pos hgood
  have hbase :
      arcLength (carrierArc N k) * ‖u‖ ^ 2 <=
        2 * Crot * A + 2 * Crot * V := by
    exact carrierPoint_mass_le_defect_plus_variance (N := N) k p (u := u) hc
  have hcompare :
      (1 / 2) * A - E <= Dint := by
    simpa [A, Dint, E, c] using
      goodCarrier_defect_compare_band
        (q := q) hq p hdelta_pos htheta_nonneg htheta_le hgood hosc
  have hA : A <= 2 * Dint + 2 * E := by
    nlinarith
  calc
    arcLength (carrierArc N k) *
        ‖slowBandPoly p (carrierBase k)‖ ^ 2
        <= 2 * Crot * A + 2 * Crot * V := by simpa [u] using hbase
    _ <= 2 * Crot * (2 * Dint + 2 * E) + 2 * Crot * V := by
      have hcoef_nonneg : 0 <= 2 * Crot := by
        nlinarith [Crot_pos]
      have hmul :
          2 * Crot * A <= 2 * Crot * (2 * Dint + 2 * E) :=
        mul_le_mul_of_nonneg_left hA hcoef_nonneg
      nlinarith
    _ =
      4 * Crot *
          ∫ x in arcSet (carrierArc N k),
            (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle +
        4 * Crot *
          ∫ x in arcSet (carrierArc N k),
            (4 * theta * ‖bandPoly N p x‖) ^ 2 ∂ μCircle +
        2 * Crot *
          arcIntegral (carrierArc N k)
            (fun x =>
              ‖slowBandPoly p x - slowBandPoly p (carrierBase k)‖ ^ 2) := by
          simp [Dint, E, V, u]
          ring

private theorem goodCarrier_average_mass_le_actual_defect_plus_errors_of_absolute_bound
    {D N L : Nat}
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) (p : Fin L -> ℂ)
    {delta theta : ℝ} (hdelta_pos : 0 < delta)
    (htheta_nonneg : 0 <= theta) (htheta_le : theta <= 1 / 2)
    {k : Fin N} (hgood :
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta)
    (habs : ∀ x ∈ arcSet (carrierArc N k),
      ‖lowPoly q x - lowPoly q (carrierBase k)‖ <=
        theta *
          (‖(polyOfCoeff q).leadingCoeff‖ *
            delta ^ (polyOfCoeff q).roots.card)) :
    arcLength (carrierArc N k) *
        ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 <=
      4 * Crot *
          ∫ x in arcSet (carrierArc N k),
            (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle +
        4 * Crot *
          ∫ x in arcSet (carrierArc N k),
            (4 * theta * ‖bandPoly N p x‖) ^ 2 ∂ μCircle +
        2 * Crot *
          arcIntegral (carrierArc N k)
            (fun x =>
              ‖slowBandPoly p x -
                carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2) := by
  exact goodCarrier_average_mass_le_actual_defect_plus_errors
    (q := q) hq p hdelta_pos htheta_nonneg htheta_le hgood
    (goodCarrier_relative_oscillation_of_absolute_bound q
      hdelta_pos htheta_nonneg hgood habs)

private theorem goodCarrier_average_mass_le_actual_defect_plus_errors_of_chord_bound
    {D N L : Nat}
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) (p : Fin L -> ℂ)
    {delta theta R : ℝ} (hdelta_pos : 0 < delta)
    (htheta_nonneg : 0 <= theta) (htheta_le : theta <= 1 / 2)
    {k : Fin N} (hgood :
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta)
    (hchord : ∀ x ∈ arcSet (carrierArc N k),
      ‖zeta x - zeta (carrierBase k)‖ <= R)
    (hslope :
      (∑ n : Fin (D + 1), ‖q n‖ * (n.1 : ℝ)) * R <=
        theta *
          (‖(polyOfCoeff q).leadingCoeff‖ *
            delta ^ (polyOfCoeff q).roots.card)) :
    arcLength (carrierArc N k) *
        ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 <=
      4 * Crot *
          ∫ x in arcSet (carrierArc N k),
            (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle +
        4 * Crot *
          ∫ x in arcSet (carrierArc N k),
            (4 * theta * ‖bandPoly N p x‖) ^ 2 ∂ μCircle +
        2 * Crot *
          arcIntegral (carrierArc N k)
            (fun x =>
              ‖slowBandPoly p x -
                carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2) := by
  exact goodCarrier_average_mass_le_actual_defect_plus_errors_of_absolute_bound
    (q := q) hq p hdelta_pos htheta_nonneg htheta_le hgood
    (goodCarrier_absolute_oscillation_of_chord_bound q hchord hslope)

private theorem goodCarrier_average_mass_le_actual_defect_plus_errors_of_arcLength_slope
    {D N L : Nat}
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) (p : Fin L -> ℂ)
    {delta theta : ℝ} (hdelta_pos : 0 < delta)
    (htheta_nonneg : 0 <= theta) (htheta_le : theta <= 1 / 2)
    {k : Fin N} (hgood :
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta)
    (hslope :
      (∑ n : Fin (D + 1), ‖q n‖ * (n.1 : ℝ)) *
          arcLength (carrierArc N k) <=
        theta *
          (‖(polyOfCoeff q).leadingCoeff‖ *
            delta ^ (polyOfCoeff q).roots.card)) :
    arcLength (carrierArc N k) *
        ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 <=
      4 * Crot *
          ∫ x in arcSet (carrierArc N k),
            (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle +
        4 * Crot *
          ∫ x in arcSet (carrierArc N k),
            (4 * theta * ‖bandPoly N p x‖) ^ 2 ∂ μCircle +
        2 * Crot *
          arcIntegral (carrierArc N k)
            (fun x =>
              ‖slowBandPoly p x -
                carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2) := by
  exact goodCarrier_average_mass_le_actual_defect_plus_errors_of_chord_bound
    (q := q) hq p hdelta_pos htheta_nonneg htheta_le hgood
    (carrierArc_chord_le_length k) hslope

private theorem lowPoly_ne_zero_of_forall_roots_ne {D : Nat}
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) (x : Circle)
    (hroots : ∀ ζ ∈ (polyOfCoeff q).roots, zeta x - ζ ≠ 0) :
    lowPoly q x ≠ 0 := by
  rw [lowPoly_eq_leadingCoeff_mul_roots q x]
  refine mul_ne_zero (leadingCoeff_polyOfCoeff_ne_zero_of_ne_zero hq) ?_
  intro hprod
  rw [Multiset.prod_eq_zero_iff] at hprod
  rcases Multiset.mem_map.mp hprod with ⟨ζ, hζ, hζzero⟩
  exact hroots ζ hζ hζzero

private theorem circleL2Sq_nonneg
    (f : AddCircle (2 * Real.pi) -> ℂ) :
    0 <= circleL2Sq f := by
  unfold circleL2Sq
  exact MeasureTheory.integral_nonneg fun x => sq_nonneg _

private theorem parseval_fin_fourier {L : Nat} (c : Fin L -> ℂ) :
    circleL2Sq (fun t : Circle =>
      ∑ m : Fin L, c m * fourier (m.val : ℤ) t) =
    ∑ m : Fin L, ‖c m‖ ^ 2 := by
  let E := Finset.range L
  let b' : Nat -> ℂ := fun n =>
    if h : n < L then c ⟨n, h⟩ else 0
  have h_func_eq :
      (fun t : Circle =>
        ∑ m : Fin L, c m * fourier (↑↑m : ℤ) t) =
      fun t => ∑ n ∈ E, b' n * fourier (↑n : ℤ) t := by
    ext t
    simp only [E]
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl fun n hn => ?_
    simp [b', Finset.mem_range.mp hn]
  rw [h_func_eq]
  let Pcont : C(Circle, ℂ) :=
    ∑ n ∈ E, b' n • fourier (n : ℤ)
  let PLp :=
    (ContinuousMap.toLp (α := Circle) 2 AddCircle.haarAddCircle ℂ) Pcont
  let E' :=
    E.map ⟨(Nat.cast : Nat -> ℤ), Nat.cast_injective⟩
  let d : ℤ -> ℂ := fun k => b' (Int.toNat k)
  have hPLp : PLp = ∑ k ∈ E', d k • fourierLp 2 k := by
    simp only [PLp, Pcont, E', d, fourierLp, map_sum, map_smul]
    rw [Finset.sum_map]
    simp
  have hinner_orth :
      @inner ℂ _ _ PLp PLp =
        Complex.ofReal (∑ n ∈ E, ‖b' n‖ ^ 2) := by
    rw [hPLp, orthonormal_fourier.inner_sum d d E',
      show E' = E.map ⟨(Nat.cast : Nat -> ℤ), Nat.cast_injective⟩ from rfl,
      Finset.sum_map, Complex.ofReal_sum]
    congr 1
    ext n
    simp only [Function.Embedding.coeFn_mk, d, Int.toNat_natCast]
    rw [mul_comm, Complex.mul_conj]
    congr 1
    exact (Complex.sq_norm (b' n)).symm
  have hcombine :=
    (MeasureTheory.L2.inner_def (𝕜 := ℂ) PLp PLp).symm.trans hinner_orth
  have hae := ContinuousMap.coeFn_toLp
    (μ := AddCircle.haarAddCircle) (𝕜 := ℂ) (p := 2) Pcont
  have hPcont_eq :
      ∀ t : Circle, (Pcont : Circle -> ℂ) t =
        ∑ n ∈ E, b' n * (fourier (n : ℤ)) t := by
    intro t
    simp [Pcont, ContinuousMap.coe_sum, ContinuousMap.coe_smul, smul_eq_mul]
  have h_sum_eq :
      ∑ n ∈ E, ‖b' n‖ ^ 2 = ∑ m : Fin L, ‖c m‖ ^ 2 := by
    simp only [E]
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl fun n hn => ?_
    simp [b', Finset.mem_range.mp hn]
  calc
    circleL2Sq (fun t => ∑ n ∈ E, b' n * (fourier (↑n : ℤ)) t)
        = ∫ t : Circle, ‖(↑↑PLp : Circle -> ℂ) t‖ ^ 2
            ∂ AddCircle.haarAddCircle := by
          unfold circleL2Sq
          symm
          apply MeasureTheory.integral_congr_ae
          filter_upwards [hae] with t ht
          rw [show (↑↑PLp : Circle -> ℂ) t = Pcont t from ht, hPcont_eq t]
    _ = (∫ t : Circle,
          @inner ℂ ℂ _
            ((↑↑PLp : Circle -> ℂ) t)
            ((↑↑PLp : Circle -> ℂ) t)
            ∂ AddCircle.haarAddCircle).re := by
          have hint := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) PLp PLp
          symm
          calc
            _ = Complex.reCLM (∫ t,
                  @inner ℂ ℂ _
                    ((↑↑PLp : Circle -> ℂ) t)
                    ((↑↑PLp : Circle -> ℂ) t)
                    ∂ AddCircle.haarAddCircle) := rfl
            _ = ∫ t, Complex.reCLM
                  (@inner ℂ ℂ _
                    ((↑↑PLp : Circle -> ℂ) t)
                    ((↑↑PLp : Circle -> ℂ) t))
                  ∂ AddCircle.haarAddCircle := by
                exact (ContinuousLinearMap.integral_comp_comm _ hint).symm
            _ = _ := by
                congr 1
                ext t
                exact @inner_self_eq_norm_sq ℂ ℂ _ _ _
                  ((↑↑PLp : Circle -> ℂ) t)
    _ = ∑ m : Fin L, ‖c m‖ ^ 2 := by
          rw [show (∫ t : Circle,
              @inner ℂ ℂ _
                ((↑↑PLp : Circle -> ℂ) t)
                ((↑↑PLp : Circle -> ℂ) t)
                ∂ AddCircle.haarAddCircle) =
              Complex.ofReal (∑ n ∈ E, ‖b' n‖ ^ 2)
            from hcombine, Complex.ofReal_re, h_sum_eq]

private theorem circleL2Sq_slowBandPoly {L : Nat} (p : Fin L -> ℂ) :
    circleL2Sq (slowBandPoly p) = ∑ m : Fin L, ‖p m‖ ^ 2 := by
  rw [show slowBandPoly p =
      fun t : Circle => ∑ m : Fin L, p m * fourier (m.val : ℤ) t by
    ext t
    simp [slowBandPoly, circleChar_eq_fourier_nat]]
  exact parseval_fin_fourier p

private theorem circleL2Sq_slowBandPolyDerivCircle {L : Nat}
    (p : Fin L -> ℂ) :
    circleL2Sq (slowBandPolyDerivCircle p) =
      ∑ m : Fin L,
        ‖p m * (2 * Real.pi * Complex.I * (m.1 : ℤ) /
          ((2 * Real.pi : ℝ) : ℂ))‖ ^ 2 := by
  rw [show slowBandPolyDerivCircle p =
      fun t : Circle => ∑ m : Fin L,
        (p m * (2 * Real.pi * Complex.I * (m.1 : ℤ) /
          ((2 * Real.pi : ℝ) : ℂ))) *
          fourier (m.val : ℤ) t by
    ext t
    unfold slowBandPolyDerivCircle
    refine Finset.sum_congr rfl ?_
    intro m hm
    ring]
  exact parseval_fin_fourier
    (fun m : Fin L => p m * (2 * Real.pi * Complex.I * (m.1 : ℤ) /
      ((2 * Real.pi : ℝ) : ℂ)))

private theorem slowBandPolyDerivCircle_l2_le {L : Nat}
    (p : Fin L -> ℂ) :
    circleL2Sq (slowBandPolyDerivCircle p) <=
      ((L : ℝ) - 1) ^ 2 * circleL2Sq (slowBandPoly p) := by
  rw [circleL2Sq_slowBandPolyDerivCircle, circleL2Sq_slowBandPoly]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro m hm
  have hT_ne : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by positivity : (0 : ℝ) < 2 * Real.pi))
  have h_coeff_norm :
      ‖p m * (2 * Real.pi * Complex.I * (m.1 : ℤ) /
          ((2 * Real.pi : ℝ) : ℂ))‖ ^ 2 =
        (m.1 : ℝ) ^ 2 * ‖p m‖ ^ 2 := by
    have hsimpl :
        (2 * Real.pi * Complex.I * (m.1 : ℤ) /
            ((2 * Real.pi : ℝ) : ℂ)) =
          Complex.I * (m.1 : ℂ) := by
      push_cast
      field_simp [hT_ne]
    rw [hsimpl, norm_mul, norm_mul, Complex.norm_I,
      one_mul, Complex.norm_natCast]
    ring
  rw [h_coeff_norm]
  have hm_le : (m.1 : ℝ) <= (L : ℝ) - 1 := by
    have hmlt : m.1 < L := m.2
    exact_mod_cast (show (m.1 : ℤ) <= (L : ℤ) - 1 by omega)
  have hm_nonneg : 0 <= (m.1 : ℝ) := by exact_mod_cast Nat.zero_le m.1
  have hm_lower : -((L : ℝ) - 1) <= (m.1 : ℝ) := by
    linarith
  exact mul_le_mul_of_nonneg_right
    (sq_le_sq' hm_lower hm_le) (sq_nonneg _)

private theorem slowBandPolyDeriv_interval_sum_eq_circleL2Sq
    {N L : Nat} (hN : 1 <= N) (p : Fin L -> ℂ) :
    (1 / (2 * Real.pi)) *
        ∑ k : Fin N,
          ∫ t in (carrierArc N k).left..(carrierArc N k).right,
            ‖slowBandPolyDeriv p t‖ ^ 2 =
      circleL2Sq (slowBandPolyDerivCircle p) := by
  let f : Circle -> ℝ := fun x => ‖slowBandPolyDerivCircle p x‖ ^ 2
  have hNpos : 0 < N := Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hf_cont : Continuous f := by
    simpa [f] using (continuous_slowBandPolyDerivCircle p).norm.pow 2
  have hf_int : MeasureTheory.Integrable f μCircle := by
    simpa [f, μCircle] using
      hf_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpart :
      (∫ x, f x ∂ μCircle) =
        ∑ k : Fin N, ∫ x in arcSet (carrierArc N k), f x ∂ μCircle :=
    carrierArc_setIntegral_univ_wip (N := N) hNpos f hf_int
  have hinterval : ∀ k : Fin N,
      (∫ x in arcSet (carrierArc N k), f x ∂ μCircle) =
        (1 / (2 * Real.pi)) *
          ∫ t in (carrierArc N k).left..(carrierArc N k).right,
            ‖slowBandPolyDeriv p t‖ ^ 2 := by
    intro k
    simpa [f, slowBandPolyDeriv] using
      carrierArc_setIntegral_eq_intervalIntegral_wip (k := k) (f := f)
  calc
    (1 / (2 * Real.pi)) *
        ∑ k : Fin N,
          ∫ t in (carrierArc N k).left..(carrierArc N k).right,
            ‖slowBandPolyDeriv p t‖ ^ 2
        = ∑ k : Fin N,
            (1 / (2 * Real.pi)) *
              ∫ t in (carrierArc N k).left..(carrierArc N k).right,
                ‖slowBandPolyDeriv p t‖ ^ 2 := by
          rw [Finset.mul_sum]
    _ = ∑ k : Fin N, ∫ x in arcSet (carrierArc N k), f x ∂ μCircle := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          exact (hinterval k).symm
    _ = ∫ x, f x ∂ μCircle := hpart.symm
    _ = circleL2Sq (slowBandPolyDerivCircle p) := by
          simp [circleL2Sq, f, μCircle]

private theorem sum_carrierAverage_variance_le_global
    {N L : Nat} (hN : 1 <= N) (p : Fin L -> ℂ) :
    (∑ k : Fin N,
      ∫ x in arcSet (carrierArc N k),
        ‖slowBandPoly p x -
          carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 ∂ μCircle) <=
      (4 * Real.pi ^ 2 * ((L : ℝ) - 1) ^ 2 / (N : ℝ) ^ 2) *
        circleL2Sq (slowBandPoly p) := by
  let I : Fin N -> ℝ := fun k =>
    ∫ t in (carrierArc N k).left..(carrierArc N k).right,
      ‖slowBandPolyDeriv p t‖ ^ 2
  let c : ℝ := (2 * Real.pi / (N : ℝ)) ^ 2
  have hlocal : ∀ k : Fin N,
      (∫ x in arcSet (carrierArc N k),
        ‖slowBandPoly p x -
          carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 ∂ μCircle) <=
        (1 / (2 * Real.pi)) * (c * I k) := by
    intro k
    have h :=
      carrierAverage_variance_carrier_le_derivative_interval
        (N := N) (L := L) k p
    simpa [I, c, carrierArc_length] using h
  have hsum_local :
      (∑ k : Fin N,
        ∫ x in arcSet (carrierArc N k),
          ‖slowBandPoly p x -
            carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 ∂ μCircle) <=
        ∑ k : Fin N, (1 / (2 * Real.pi)) * (c * I k) := by
    exact Finset.sum_le_sum (fun k hk => hlocal k)
  have hsum_eq :
      (∑ k : Fin N, (1 / (2 * Real.pi)) * (c * I k)) =
        c * ((1 / (2 * Real.pi)) * ∑ k : Fin N, I k) := by
    calc
      (∑ k : Fin N, (1 / (2 * Real.pi)) * (c * I k))
          = ∑ k : Fin N, c * ((1 / (2 * Real.pi)) * I k) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            ring
      _ = c * ∑ k : Fin N, ((1 / (2 * Real.pi)) * I k) := by
            rw [Finset.mul_sum]
      _ = c * ((1 / (2 * Real.pi)) * ∑ k : Fin N, I k) := by
            congr 1
            rw [Finset.mul_sum]
  have hderiv_le :
      (1 / (2 * Real.pi)) * ∑ k : Fin N, I k <=
        ((L : ℝ) - 1) ^ 2 * circleL2Sq (slowBandPoly p) := by
    rw [show (1 / (2 * Real.pi)) * ∑ k : Fin N, I k =
        circleL2Sq (slowBandPolyDerivCircle p) by
      simpa [I] using slowBandPolyDeriv_interval_sum_eq_circleL2Sq
        (N := N) (L := L) hN p]
    exact slowBandPolyDerivCircle_l2_le p
  have hc_nonneg : 0 <= c := by
    dsimp [c]
    positivity
  calc
    (∑ k : Fin N,
      ∫ x in arcSet (carrierArc N k),
        ‖slowBandPoly p x -
          carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 ∂ μCircle)
        <= ∑ k : Fin N, (1 / (2 * Real.pi)) * (c * I k) := hsum_local
    _ = c * ((1 / (2 * Real.pi)) * ∑ k : Fin N, I k) := hsum_eq
    _ <= c * (((L : ℝ) - 1) ^ 2 * circleL2Sq (slowBandPoly p)) := by
          exact mul_le_mul_of_nonneg_left hderiv_le hc_nonneg
    _ = (4 * Real.pi ^ 2 * ((L : ℝ) - 1) ^ 2 / (N : ℝ) ^ 2) *
        circleL2Sq (slowBandPoly p) := by
          simp [c]
          ring

private theorem slowBandPoly_slope_sq_le_L_cubed_l2 {L : Nat}
    (p : Fin L -> ℂ) :
    (∑ m : Fin L, ‖p m‖ * (m.1 : ℝ)) ^ 2 <=
      (L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p) := by
  let S : Finset (Fin L) := Finset.univ
  have hcs :
      (∑ m : Fin L, ‖p m‖ * (m.1 : ℝ)) ^ 2 <=
        (L : ℝ) *
          ∑ m : Fin L, (‖p m‖ * (m.1 : ℝ)) ^ 2 := by
    have h :=
      (sq_sum_le_card_mul_sum_sq
        (s := S)
        (f := fun m : Fin L => ‖p m‖ * (m.1 : ℝ)) : _)
    simpa [S] using h
  have hsum :
      ∑ m : Fin L, (‖p m‖ * (m.1 : ℝ)) ^ 2 <=
        (L : ℝ) ^ 2 * ∑ m : Fin L, ‖p m‖ ^ 2 := by
    calc
      ∑ m : Fin L, (‖p m‖ * (m.1 : ℝ)) ^ 2
          = ∑ m : Fin L, ‖p m‖ ^ 2 * (m.1 : ℝ) ^ 2 := by
              congr
              ext m
              ring
      _ <= ∑ m : Fin L, ‖p m‖ ^ 2 * (L : ℝ) ^ 2 := by
          refine Finset.sum_le_sum ?_
          intro m hm
          have hmL : (m.1 : ℝ) <= (L : ℝ) := by
            exact_mod_cast Nat.le_of_lt m.2
          have hm_nonneg : 0 <= (m.1 : ℝ) := by
            exact_mod_cast Nat.zero_le m.1
          have hL_nonneg : 0 <= (L : ℝ) := by
            exact_mod_cast Nat.zero_le L
          have hsq : (m.1 : ℝ) ^ 2 <= (L : ℝ) ^ 2 := by
            nlinarith [hm_nonneg, hL_nonneg, hmL]
          exact mul_le_mul_of_nonneg_left hsq (sq_nonneg ‖p m‖)
      _ = (L : ℝ) ^ 2 * ∑ m : Fin L, ‖p m‖ ^ 2 := by
          rw [Finset.mul_sum]
          congr
          ext m
          ring
  have hL_nonneg : 0 <= (L : ℝ) := by
    exact_mod_cast Nat.zero_le L
  calc
    (∑ m : Fin L, ‖p m‖ * (m.1 : ℝ)) ^ 2
        <= (L : ℝ) *
          ∑ m : Fin L, (‖p m‖ * (m.1 : ℝ)) ^ 2 := hcs
    _ <= (L : ℝ) * ((L : ℝ) ^ 2 * ∑ m : Fin L, ‖p m‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsum hL_nonneg
    _ = (L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p) := by
        rw [circleL2Sq_slowBandPoly]
        ring

private theorem slowBandPoly_sub_carrierBase_sq_le_L_cubed_l2_length_sq
    {N L : Nat} (k : Fin N) (p : Fin L -> ℂ) :
    ∀ x ∈ arcSet (carrierArc N k),
      ‖slowBandPoly p x - slowBandPoly p (carrierBase k)‖ ^ 2 <=
        ((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) *
          arcLength (carrierArc N k) ^ 2 := by
  intro x hx
  let S : ℝ := ∑ m : Fin L, ‖p m‖ * (m.1 : ℝ)
  let ell : ℝ := arcLength (carrierArc N k)
  have hosc :
      ‖slowBandPoly p x - slowBandPoly p (carrierBase k)‖ <= S * ell := by
    simpa [S, ell] using
      slowBandPoly_sub_carrierBase_le_slope_length k p x hx
  have hnorm_nonneg :
      0 <= ‖slowBandPoly p x - slowBandPoly p (carrierBase k)‖ :=
    norm_nonneg _
  have hS_nonneg : 0 <= S := by
    simpa [S] using slowBandPoly_slope_nonneg p
  have hell_nonneg : 0 <= ell := by
    simpa [ell] using arcLength_nonneg (carrierArc N k)
  have hmul_nonneg : 0 <= S * ell := mul_nonneg hS_nonneg hell_nonneg
  have hsquare :
      ‖slowBandPoly p x - slowBandPoly p (carrierBase k)‖ ^ 2 <=
        (S * ell) ^ 2 := by
    nlinarith
  have hSsq : S ^ 2 <= (L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p) := by
    simpa [S] using slowBandPoly_slope_sq_le_L_cubed_l2 p
  have hellsq_nonneg : 0 <= ell ^ 2 := sq_nonneg ell
  calc
    ‖slowBandPoly p x - slowBandPoly p (carrierBase k)‖ ^ 2
        <= (S * ell) ^ 2 := hsquare
    _ = S ^ 2 * ell ^ 2 := by ring
    _ <= ((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) * ell ^ 2 :=
        mul_le_mul_of_nonneg_right hSsq hellsq_nonneg
    _ =
        ((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) *
          arcLength (carrierArc N k) ^ 2 := by
        simp [ell]

private theorem slowBandPoly_carrier_variance_le_measure
    {N L : Nat} (k : Fin N) (p : Fin L -> ℂ) :
    (∫ x in arcSet (carrierArc N k),
        ‖slowBandPoly p x - slowBandPoly p (carrierBase k)‖ ^ 2 ∂ μCircle) <=
      (((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) *
          arcLength (carrierArc N k) ^ 2) *
        μCircle.real (arcSet (carrierArc N k)) := by
  let C : ℝ :=
    ((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) *
      arcLength (carrierArc N k) ^ 2
  have hpoint :
      ∀ x ∈ arcSet (carrierArc N k),
        ‖(‖slowBandPoly p x - slowBandPoly p (carrierBase k)‖ ^ 2 : ℝ)‖ <=
          C := by
    intro x hx
    rw [Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg ‖slowBandPoly p x - slowBandPoly p (carrierBase k)‖)]
    simpa [C] using
      slowBandPoly_sub_carrierBase_sq_le_L_cubed_l2_length_sq k p x hx
  haveI : MeasureTheory.IsFiniteMeasure μCircle := by
    dsimp [μCircle]
    infer_instance
  have hsfin : μCircle (arcSet (carrierArc N k)) < ⊤ := by
    exact MeasureTheory.measure_lt_top μCircle (arcSet (carrierArc N k))
  have hbound :=
    MeasureTheory.norm_setIntegral_le_of_norm_le_const
      (μ := μCircle) (s := arcSet (carrierArc N k))
      (f := fun x : Circle =>
        ‖slowBandPoly p x - slowBandPoly p (carrierBase k)‖ ^ 2)
      hsfin hpoint
  have hnonneg :
      0 <= ∫ x in arcSet (carrierArc N k),
          ‖slowBandPoly p x - slowBandPoly p (carrierBase k)‖ ^ 2 ∂ μCircle := by
    exact MeasureTheory.integral_nonneg fun x => sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg] at hbound
  simpa [C] using hbound

private theorem slowBandPoly_carrier_mass_le_base_plus_variance
    {N L : Nat} (k : Fin N) (p : Fin L -> ℂ) :
    (∫ x in arcSet (carrierArc N k),
        ‖slowBandPoly p x‖ ^ 2 ∂ μCircle) <=
      (1 / Real.pi) *
          (arcLength (carrierArc N k) *
            ‖slowBandPoly p (carrierBase k)‖ ^ 2) +
        2 *
          ∫ x in arcSet (carrierArc N k),
            ‖slowBandPoly p x - slowBandPoly p (carrierBase k)‖ ^ 2
              ∂ μCircle := by
  let s : Set Circle := arcSet (carrierArc N k)
  let b : ℂ := slowBandPoly p (carrierBase k)
  let v : Circle -> ℝ := fun x => ‖slowBandPoly p x - b‖ ^ 2
  let g : Circle -> ℝ := fun x => 2 * ‖b‖ ^ 2 + 2 * v x
  have hmass_cont : Continuous fun x : Circle => ‖slowBandPoly p x‖ ^ 2 :=
    (continuous_slowBandPoly p).norm.pow 2
  have hv_cont : Continuous v := by
    dsimp [v, b]
    exact ((continuous_slowBandPoly p).sub continuous_const).norm.pow 2
  have hg_cont : Continuous g := by
    dsimp [g]
    exact continuous_const.add (continuous_const.mul hv_cont)
  have hmass_int :
      MeasureTheory.Integrable
        (fun x : Circle => ‖slowBandPoly p x‖ ^ 2) μCircle := by
    simpa [μCircle] using
      hmass_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hv_int : MeasureTheory.Integrable v μCircle := by
    simpa [μCircle] using
      hv_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  haveI : MeasureTheory.IsFiniteMeasure μCircle := by
    dsimp [μCircle]
    infer_instance
  have hg_int : MeasureTheory.Integrable g μCircle := by
    have hconst : MeasureTheory.Integrable (fun _ : Circle => 2 * ‖b‖ ^ 2) μCircle :=
      MeasureTheory.integrable_const _
    have h := hconst.add (hv_int.const_mul 2)
    refine h.congr ?_
    filter_upwards with x
    rfl
  have hmono :
      (∫ x in s, ‖slowBandPoly p x‖ ^ 2 ∂ μCircle) <=
        ∫ x in s, g x ∂ μCircle := by
    refine MeasureTheory.integral_mono_ae hmass_int.restrict hg_int.restrict ?_
    filter_upwards with x
    simpa [g, v, b] using
      norm_sq_le_two_base_sq_add_two_diff_sq
        (slowBandPoly p x) (slowBandPoly p (carrierBase k))
  have hg_eq :
      (∫ x in s, g x ∂ μCircle) =
        (1 / Real.pi) *
            (arcLength (carrierArc N k) *
              ‖slowBandPoly p (carrierBase k)‖ ^ 2) +
          2 *
            ∫ x in s,
              ‖slowBandPoly p x - slowBandPoly p (carrierBase k)‖ ^ 2
                ∂ μCircle := by
    calc
      (∫ x in s, g x ∂ μCircle)
          =
        (∫ x in s, 2 * ‖b‖ ^ 2 ∂ μCircle) +
          ∫ x in s, 2 * v x ∂ μCircle := by
            rw [MeasureTheory.integral_add]
            · exact MeasureTheory.integrable_const _
            · exact (hv_int.const_mul 2).restrict
      _ =
        (2 * ‖b‖ ^ 2) * μCircle.real s +
          2 * ∫ x in s, v x ∂ μCircle := by
            rw [MeasureTheory.integral_const, MeasureTheory.integral_const_mul]
            simp [MeasureTheory.Measure.real, mul_comm]
      _ =
        (1 / Real.pi) *
            (arcLength (carrierArc N k) *
              ‖slowBandPoly p (carrierBase k)‖ ^ 2) +
          2 *
            ∫ x in s,
              ‖slowBandPoly p x - slowBandPoly p (carrierBase k)‖ ^ 2
                ∂ μCircle := by
            rw [carrierArc_mu_real_eq_length_div_period k]
            have hpi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
            field_simp [s, b, v, hpi_ne]
            ring
  exact hmono.trans_eq hg_eq

private theorem goodCarrier_base_mass_le_actual_defect_plus_measure_errors
    {D N L : Nat}
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) (p : Fin L -> ℂ)
    {delta theta : ℝ} (hdelta_pos : 0 < delta)
    (htheta_nonneg : 0 <= theta) (htheta_le : theta <= 1 / 2)
    {k : Fin N} (hgood :
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta)
    (hosc : ∀ x ∈ arcSet (carrierArc N k),
      ‖lowPoly q x - lowPoly q (carrierBase k)‖ <=
        theta * ‖lowPoly q (carrierBase k)‖) :
    arcLength (carrierArc N k) *
        ‖slowBandPoly p (carrierBase k)‖ ^ 2 <=
      4 * Crot *
          ∫ x in arcSet (carrierArc N k),
            (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle +
        4 * Crot *
          ∫ x in arcSet (carrierArc N k),
            (4 * theta * ‖bandPoly N p x‖) ^ 2 ∂ μCircle +
        2 * Crot *
          ((((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) *
              arcLength (carrierArc N k) ^ 2) *
            μCircle.real (arcSet (carrierArc N k))) := by
  let A : ℝ :=
    4 * Crot *
      ∫ x in arcSet (carrierArc N k),
        (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle
  let E : ℝ :=
    4 * Crot *
      ∫ x in arcSet (carrierArc N k),
        (4 * theta * ‖bandPoly N p x‖) ^ 2 ∂ μCircle
  let V : ℝ :=
    arcIntegral (carrierArc N k)
      (fun x =>
        ‖slowBandPoly p x - slowBandPoly p (carrierBase k)‖ ^ 2)
  let Vbd : ℝ :=
    (((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) *
        arcLength (carrierArc N k) ^ 2) *
      μCircle.real (arcSet (carrierArc N k))
  have hmain :
      arcLength (carrierArc N k) *
          ‖slowBandPoly p (carrierBase k)‖ ^ 2 <=
        A + E + 2 * Crot * V := by
    simpa [A, E, V] using
      goodCarrier_base_mass_le_actual_defect_plus_errors
        (q := q) hq p hdelta_pos htheta_nonneg htheta_le hgood hosc
  have hvar : V <= Vbd := by
    simpa [V, Vbd, arcIntegral] using
      slowBandPoly_carrier_variance_le_measure k p
  have hcoef_nonneg : 0 <= 2 * Crot := by
    nlinarith [Crot_pos]
  have hmul : 2 * Crot * V <= 2 * Crot * Vbd :=
    mul_le_mul_of_nonneg_left hvar hcoef_nonneg
  calc
    arcLength (carrierArc N k) *
        ‖slowBandPoly p (carrierBase k)‖ ^ 2
        <= A + E + 2 * Crot * V := hmain
    _ <= A + E + 2 * Crot * Vbd := by
          nlinarith
    _ =
      4 * Crot *
          ∫ x in arcSet (carrierArc N k),
            (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle +
        4 * Crot *
          ∫ x in arcSet (carrierArc N k),
            (4 * theta * ‖bandPoly N p x‖) ^ 2 ∂ μCircle +
        2 * Crot *
          ((((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) *
              arcLength (carrierArc N k) ^ 2) *
            μCircle.real (arcSet (carrierArc N k))) := by
          simp [A, E, Vbd]

private theorem goodCarrier_base_mass_le_actual_defect_plus_measure_errors_of_arcLength_slope
    {D N L : Nat}
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) (p : Fin L -> ℂ)
    {delta theta : ℝ} (hdelta_pos : 0 < delta)
    (htheta_nonneg : 0 <= theta) (htheta_le : theta <= 1 / 2)
    {k : Fin N} (hgood :
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta)
    (hslope :
      (∑ n : Fin (D + 1), ‖q n‖ * (n.1 : ℝ)) *
          arcLength (carrierArc N k) <=
        theta *
          (‖(polyOfCoeff q).leadingCoeff‖ *
            delta ^ (polyOfCoeff q).roots.card)) :
    arcLength (carrierArc N k) *
        ‖slowBandPoly p (carrierBase k)‖ ^ 2 <=
      4 * Crot *
          ∫ x in arcSet (carrierArc N k),
            (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle +
        4 * Crot *
          ∫ x in arcSet (carrierArc N k),
            (4 * theta * ‖bandPoly N p x‖) ^ 2 ∂ μCircle +
        2 * Crot *
          ((((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) *
              arcLength (carrierArc N k) ^ 2) *
            μCircle.real (arcSet (carrierArc N k))) := by
  exact goodCarrier_base_mass_le_actual_defect_plus_measure_errors
    (q := q) hq p hdelta_pos htheta_nonneg htheta_le hgood
    (goodCarrier_relative_oscillation_of_absolute_bound q
      hdelta_pos htheta_nonneg hgood
      (goodCarrier_absolute_oscillation_of_chord_bound q
        (carrierArc_chord_le_length k) hslope))

private theorem norm_slowBandPoly_le_sum_norm {L : Nat}
    (p : Fin L -> ℂ) (x : Circle) :
    ‖slowBandPoly p x‖ <= ∑ m : Fin L, ‖p m‖ := by
  calc
    ‖slowBandPoly p x‖ =
        ‖∑ m : Fin L, p m * circleChar m.1 x‖ := by
          rfl
    _ <= ∑ m : Fin L, ‖p m * circleChar m.1 x‖ := by
          exact norm_sum_le _ _
    _ = ∑ m : Fin L, ‖p m‖ := by
          congr
          ext m
          simp [norm_circleChar_wip]

private theorem slowBandPoly_norm_sq_le_L_circleL2Sq {L : Nat}
    (p : Fin L -> ℂ) (x : Circle) :
    ‖slowBandPoly p x‖ ^ 2 <= (L : ℝ) * circleL2Sq (slowBandPoly p) := by
  have hnorm := norm_slowBandPoly_le_sum_norm p x
  have hsum_nonneg : 0 <= ∑ m : Fin L, ‖p m‖ :=
    Finset.sum_nonneg fun m hm => norm_nonneg (p m)
  have hsquare :
      ‖slowBandPoly p x‖ ^ 2 <= (∑ m : Fin L, ‖p m‖) ^ 2 := by
    nlinarith [norm_nonneg (slowBandPoly p x), hsum_nonneg, hnorm]
  have hcs :
      (∑ m : Fin L, ‖p m‖) ^ 2 <=
        ((Finset.univ : Finset (Fin L)).card : ℝ) *
          ∑ m : Fin L, ‖p m‖ ^ 2 := by
    simpa using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (Fin L)))
        (f := fun m : Fin L => ‖p m‖) : _)
  calc
    ‖slowBandPoly p x‖ ^ 2
        <= (∑ m : Fin L, ‖p m‖) ^ 2 := hsquare
    _ <= ((Finset.univ : Finset (Fin L)).card : ℝ) *
          ∑ m : Fin L, ‖p m‖ ^ 2 := hcs
    _ = (L : ℝ) * circleL2Sq (slowBandPoly p) := by
          rw [circleL2Sq_slowBandPoly]
          simp

private theorem circleL2Sq_bandPoly
    (N : Nat) {L : Nat} (p : Fin L -> ℂ) :
    circleL2Sq (bandPoly N p) = ∑ m : Fin L, ‖p m‖ ^ 2 := by
  calc
    circleL2Sq (bandPoly N p) = circleL2Sq (slowBandPoly p) := by
      unfold circleL2Sq
      congr 1
      ext t
      rw [bandPoly_eq_fast_mul_slow]
      simp [norm_circleChar_wip]
    _ = ∑ m : Fin L, ‖p m‖ ^ 2 := circleL2Sq_slowBandPoly p

private theorem bandPoly_norm_sq_le_L_circleL2Sq
    (N : Nat) {L : Nat} (p : Fin L -> ℂ) (x : Circle) :
    ‖bandPoly N p x‖ ^ 2 <= (L : ℝ) * circleL2Sq (bandPoly N p) := by
  have hnorm :
      ‖bandPoly N p x‖ = ‖slowBandPoly p x‖ := by
    rw [bandPoly_eq_fast_mul_slow]
    simp [norm_circleChar_wip]
  calc
    ‖bandPoly N p x‖ ^ 2 = ‖slowBandPoly p x‖ ^ 2 := by rw [hnorm]
    _ <= (L : ℝ) * circleL2Sq (slowBandPoly p) :=
      slowBandPoly_norm_sq_le_L_circleL2Sq p x
    _ = (L : ℝ) * circleL2Sq (bandPoly N p) := by
      rw [circleL2Sq_bandPoly, circleL2Sq_slowBandPoly]

private theorem bandPoly_setIntegral_norm_sq_le_measure
    (s : Set Circle) (N : Nat) {L : Nat} (p : Fin L -> ℂ) :
    (∫ x in s, ‖bandPoly N p x‖ ^ 2 ∂ μCircle) <=
      ((L : ℝ) * circleL2Sq (bandPoly N p)) * μCircle.real s := by
  let C : ℝ := (L : ℝ) * circleL2Sq (bandPoly N p)
  have hpoint :
      ∀ x ∈ s, ‖(‖bandPoly N p x‖ ^ 2 : ℝ)‖ <= C := by
    intro x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖bandPoly N p x‖)]
    exact bandPoly_norm_sq_le_L_circleL2Sq N p x
  haveI : MeasureTheory.IsFiniteMeasure μCircle := by
    dsimp [μCircle]
    infer_instance
  have hsfin : μCircle s < ⊤ := by
    exact MeasureTheory.measure_lt_top μCircle s
  have hbound :=
    MeasureTheory.norm_setIntegral_le_of_norm_le_const
      (μ := μCircle) (s := s)
      (f := fun x : Circle => ‖bandPoly N p x‖ ^ 2) hsfin hpoint
  have hnonneg : 0 <= ∫ x in s, ‖bandPoly N p x‖ ^ 2 ∂ μCircle := by
    exact MeasureTheory.integral_nonneg fun x => sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg] at hbound
  simpa [C] using hbound

private theorem bandPoly_setIntegral_theta_error_le_measure
    (s : Set Circle) (N : Nat) {L : Nat} (p : Fin L -> ℂ) {theta : ℝ} :
    (∫ x in s, (4 * theta * ‖bandPoly N p x‖) ^ 2 ∂ μCircle) <=
      (4 * theta) ^ 2 *
        (((L : ℝ) * circleL2Sq (bandPoly N p)) * μCircle.real s) := by
  have hmass := bandPoly_setIntegral_norm_sq_le_measure s N p
  have hcoef_nonneg : 0 <= (4 * theta) ^ 2 := sq_nonneg _
  calc
    (∫ x in s, (4 * theta * ‖bandPoly N p x‖) ^ 2 ∂ μCircle)
        =
      ∫ x in s, (4 * theta) ^ 2 * ‖bandPoly N p x‖ ^ 2 ∂ μCircle := by
        congr
        ext x
        ring
    _ =
      (4 * theta) ^ 2 *
        ∫ x in s, ‖bandPoly N p x‖ ^ 2 ∂ μCircle := by
        rw [MeasureTheory.integral_const_mul]
    _ <=
      (4 * theta) ^ 2 *
        (((L : ℝ) * circleL2Sq (bandPoly N p)) * μCircle.real s) :=
        mul_le_mul_of_nonneg_left hmass hcoef_nonneg

private theorem carrierAverage_mass_le_slow_l2
    {N L : Nat} (k : Fin N) (p : Fin L -> ℂ) :
    arcLength (carrierArc N k) *
        ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 <=
      (2 * Real.pi) *
        ∫ x in arcSet (carrierArc N k),
          ‖slowBandPoly p x‖ ^ 2 ∂ μCircle := by
  have hbv := carrierAverage_bias_variance (N := N) k p
  rw [carrierArc_mu_real_eq_length_div_period k] at hbv
  have hvar_nonneg :
      0 <=
        ∫ x in arcSet (carrierArc N k),
          ‖slowBandPoly p x -
            carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 ∂ μCircle := by
    exact MeasureTheory.integral_nonneg fun x => sq_nonneg _
  have hle :
      arcLength (carrierArc N k) / (2 * Real.pi) *
          ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 <=
        ∫ x in arcSet (carrierArc N k),
          ‖slowBandPoly p x‖ ^ 2 ∂ μCircle := by
    nlinarith
  have hperiod_nonneg : 0 <= (2 * Real.pi : ℝ) := by positivity
  have hmul :=
    mul_le_mul_of_nonneg_left hle hperiod_nonneg
  have hpi_ne : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt (by positivity)
  calc
    arcLength (carrierArc N k) *
        ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2
        =
      (2 * Real.pi) *
        (arcLength (carrierArc N k) / (2 * Real.pi) *
          ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2) := by
        field_simp [hpi_ne]
    _ <=
      (2 * Real.pi) *
        ∫ x in arcSet (carrierArc N k),
          ‖slowBandPoly p x‖ ^ 2 ∂ μCircle := hmul

private theorem carrierAverage_mass_le_L_l2
    {N L : Nat} (k : Fin N) (p : Fin L -> ℂ) :
    arcLength (carrierArc N k) *
        ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 <=
      ((2 * Real.pi) / (N : ℝ)) *
        ((L : ℝ) * circleL2Sq (bandPoly N p)) := by
  let s : Set Circle := arcSet (carrierArc N k)
  have hmass := carrierAverage_mass_le_slow_l2 (N := N) (L := L) k p
  have hband :
      (∫ x in s, ‖slowBandPoly p x‖ ^ 2 ∂ μCircle) =
        ∫ x in s, ‖bandPoly N p x‖ ^ 2 ∂ μCircle := by
    congr
    ext x
    have hnorm : ‖bandPoly N p x‖ = ‖slowBandPoly p x‖ := by
      rw [bandPoly_eq_fast_mul_slow]
      simp [norm_circleChar_wip]
    rw [hnorm]
  have hband_bound :
      (∫ x in s, ‖bandPoly N p x‖ ^ 2 ∂ μCircle) <=
        ((L : ℝ) * circleL2Sq (bandPoly N p)) * (N : ℝ)⁻¹ := by
    have h := bandPoly_setIntegral_norm_sq_le_measure s N p
    rw [carrierArc_mu_real_eq_inv_nat k] at h
    simpa [s] using h
  have hperiod_nonneg : 0 <= (2 * Real.pi : ℝ) := by positivity
  have hmul :
      (2 * Real.pi) *
          (∫ x in s, ‖slowBandPoly p x‖ ^ 2 ∂ μCircle) <=
        (2 * Real.pi) *
          (((L : ℝ) * circleL2Sq (bandPoly N p)) * (N : ℝ)⁻¹) := by
    rw [hband]
    exact mul_le_mul_of_nonneg_left hband_bound hperiod_nonneg
  calc
    arcLength (carrierArc N k) *
        ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2
        <=
      (2 * Real.pi) *
        ∫ x in arcSet (carrierArc N k),
          ‖slowBandPoly p x‖ ^ 2 ∂ μCircle := hmass
    _ <=
      (2 * Real.pi) *
        (((L : ℝ) * circleL2Sq (bandPoly N p)) * (N : ℝ)⁻¹) := by
        simpa [s] using hmul
    _ =
      ((2 * Real.pi) / (N : ℝ)) *
        ((L : ℝ) * circleL2Sq (bandPoly N p)) := by
        ring

private theorem sum_carrier_average_mass_le_card_L_l2
    {N L : Nat} (K : Finset (Fin N)) (p : Fin L -> ℂ) :
    ∑ k ∈ K,
        arcLength (carrierArc N k) *
          ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 <=
      (K.card : ℝ) *
        (((2 * Real.pi) / (N : ℝ)) *
          ((L : ℝ) * circleL2Sq (bandPoly N p))) := by
  have hpoint :
      ∀ k ∈ K,
        arcLength (carrierArc N k) *
            ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 <=
          ((2 * Real.pi) / (N : ℝ)) *
            ((L : ℝ) * circleL2Sq (bandPoly N p)) := by
    intro k hk
    exact carrierAverage_mass_le_L_l2 (N := N) (L := L) k p
  calc
    ∑ k ∈ K,
        arcLength (carrierArc N k) *
          ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2
        <= ∑ _k ∈ K,
          ((2 * Real.pi) / (N : ℝ)) *
            ((L : ℝ) * circleL2Sq (bandPoly N p)) :=
          Finset.sum_le_sum hpoint
    _ =
      (K.card : ℝ) *
        (((2 * Real.pi) / (N : ℝ)) *
          ((L : ℝ) * circleL2Sq (bandPoly N p))) := by
        rw [Finset.sum_const, nsmul_eq_mul]

private theorem sum_badCarrier_average_mass_le_card_L_l2
    {D N L : Nat} (q : Fin (D + 1) -> ℂ) (p : Fin L -> ℂ)
    {delta : ℝ} :
    ∑ k ∈ badCarrierIndices N (polyOfCoeff q).roots delta,
        arcLength (carrierArc N k) *
          ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 <=
      ((badCarrierIndices N (polyOfCoeff q).roots delta).card : ℝ) *
        (((2 * Real.pi) / (N : ℝ)) *
          ((L : ℝ) * circleL2Sq (bandPoly N p))) := by
  exact sum_carrier_average_mass_le_card_L_l2
    (badCarrierIndices N (polyOfCoeff q).roots delta) p

private theorem goodCarrier_base_mass_le_actual_defect_plus_l2_measure_errors_of_arcLength_slope
    {D N L : Nat}
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) (p : Fin L -> ℂ)
    {delta theta : ℝ} (hdelta_pos : 0 < delta)
    (htheta_nonneg : 0 <= theta) (htheta_le : theta <= 1 / 2)
    {k : Fin N} (hgood :
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta)
    (hslope :
      (∑ n : Fin (D + 1), ‖q n‖ * (n.1 : ℝ)) *
          arcLength (carrierArc N k) <=
        theta *
          (‖(polyOfCoeff q).leadingCoeff‖ *
            delta ^ (polyOfCoeff q).roots.card)) :
    arcLength (carrierArc N k) *
        ‖slowBandPoly p (carrierBase k)‖ ^ 2 <=
      4 * Crot *
          ∫ x in arcSet (carrierArc N k),
            (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle +
        4 * Crot *
          ((4 * theta) ^ 2 *
            (((L : ℝ) * circleL2Sq (bandPoly N p)) *
              μCircle.real (arcSet (carrierArc N k)))) +
        2 * Crot *
          ((((L : ℝ) ^ 3 * circleL2Sq (bandPoly N p)) *
              arcLength (carrierArc N k) ^ 2) *
            μCircle.real (arcSet (carrierArc N k))) := by
  let s : Set Circle := arcSet (carrierArc N k)
  let A : ℝ :=
    4 * Crot *
      ∫ x in s,
        (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle
  let E : ℝ :=
    ∫ x in s, (4 * theta * ‖bandPoly N p x‖) ^ 2 ∂ μCircle
  let Ebd : ℝ :=
    (4 * theta) ^ 2 *
      (((L : ℝ) * circleL2Sq (bandPoly N p)) * μCircle.real s)
  let Vslow : ℝ :=
    (((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) *
        arcLength (carrierArc N k) ^ 2) *
      μCircle.real s
  let Vbd : ℝ :=
    (((L : ℝ) ^ 3 * circleL2Sq (bandPoly N p)) *
        arcLength (carrierArc N k) ^ 2) *
      μCircle.real s
  have hbase :
      arcLength (carrierArc N k) *
          ‖slowBandPoly p (carrierBase k)‖ ^ 2 <=
        A + 4 * Crot * E + 2 * Crot * Vslow := by
    simpa [A, E, Vslow, s] using
      goodCarrier_base_mass_le_actual_defect_plus_measure_errors_of_arcLength_slope
        (q := q) hq p hdelta_pos htheta_nonneg htheta_le hgood hslope
  have hE : E <= Ebd := by
    simpa [E, Ebd, s] using
      bandPoly_setIntegral_theta_error_le_measure s N p (theta := theta)
  have hcoef4_nonneg : 0 <= 4 * Crot := by
    nlinarith [Crot_pos]
  have hEmul : 4 * Crot * E <= 4 * Crot * Ebd :=
    mul_le_mul_of_nonneg_left hE hcoef4_nonneg
  have hslow_eq : circleL2Sq (slowBandPoly p) = circleL2Sq (bandPoly N p) := by
    rw [circleL2Sq_bandPoly, circleL2Sq_slowBandPoly]
  have hV : Vslow = Vbd := by
    simp [Vslow, Vbd, hslow_eq]
  calc
    arcLength (carrierArc N k) *
        ‖slowBandPoly p (carrierBase k)‖ ^ 2
        <= A + 4 * Crot * E + 2 * Crot * Vslow := hbase
    _ <= A + 4 * Crot * Ebd + 2 * Crot * Vbd := by
          nlinarith
    _ =
      4 * Crot *
          ∫ x in arcSet (carrierArc N k),
            (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle +
        4 * Crot *
          ((4 * theta) ^ 2 *
            (((L : ℝ) * circleL2Sq (bandPoly N p)) *
              μCircle.real (arcSet (carrierArc N k)))) +
        2 * Crot *
          ((((L : ℝ) ^ 3 * circleL2Sq (bandPoly N p)) *
              arcLength (carrierArc N k) ^ 2) *
            μCircle.real (arcSet (carrierArc N k))) := by
          simp [A, Ebd, Vbd, s]

private theorem goodCarrier_base_mass_le_actual_defect_plus_l2_invN_errors_of_arcLength_slope
    {D N L : Nat}
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) (p : Fin L -> ℂ)
    {delta theta : ℝ} (hdelta_pos : 0 < delta)
    (htheta_nonneg : 0 <= theta) (htheta_le : theta <= 1 / 2)
    {k : Fin N} (hgood :
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta)
    (hslope :
      (∑ n : Fin (D + 1), ‖q n‖ * (n.1 : ℝ)) *
          arcLength (carrierArc N k) <=
        theta *
          (‖(polyOfCoeff q).leadingCoeff‖ *
            delta ^ (polyOfCoeff q).roots.card)) :
    arcLength (carrierArc N k) *
        ‖slowBandPoly p (carrierBase k)‖ ^ 2 <=
      4 * Crot *
          ∫ x in arcSet (carrierArc N k),
            (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle +
        4 * Crot *
          ((4 * theta) ^ 2 *
            (((L : ℝ) * circleL2Sq (bandPoly N p)) * (N : ℝ)⁻¹)) +
        2 * Crot *
          ((((L : ℝ) ^ 3 * circleL2Sq (bandPoly N p)) *
              arcLength (carrierArc N k) ^ 2) * (N : ℝ)⁻¹) := by
  simpa [carrierArc_mu_real_eq_inv_nat k] using
    goodCarrier_base_mass_le_actual_defect_plus_l2_measure_errors_of_arcLength_slope
      (q := q) hq p hdelta_pos htheta_nonneg htheta_le hgood hslope

private theorem sum_const_invNat_le
    {N : Nat} (hN : 0 < N) (K : Finset (Fin N)) {a : ℝ}
    (ha : 0 <= a) :
    Finset.sum K (fun _k => a * (N : ℝ)⁻¹) <= a := by
  have hKle_nat : K.card <= N := by
    simpa using (Finset.card_le_univ K)
  have hKle : (K.card : ℝ) <= (N : ℝ) := by
    exact_mod_cast hKle_nat
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hfrac : (K.card : ℝ) * (N : ℝ)⁻¹ <= 1 := by
    rw [inv_eq_one_div, mul_one_div]
    exact div_le_one_of_le₀ hKle (le_of_lt hNpos)
  calc
    Finset.sum K (fun _k => a * (N : ℝ)⁻¹)
        = (K.card : ℝ) * (a * (N : ℝ)⁻¹) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = a * ((K.card : ℝ) * (N : ℝ)⁻¹) := by ring
    _ <= a * 1 := mul_le_mul_of_nonneg_left hfrac ha
    _ = a := by ring

private theorem sum_carrier_length_sq_invNat_le
    {N : Nat} (hN : 0 < N) (K : Finset (Fin N)) :
    ∑ k ∈ K, arcLength (carrierArc N k) ^ 2 * (N : ℝ)⁻¹ <=
      ((2 * Real.pi) / (N : ℝ)) ^ 2 := by
  calc
    ∑ k ∈ K, arcLength (carrierArc N k) ^ 2 * (N : ℝ)⁻¹
        = ∑ k ∈ K, ((2 * Real.pi) / (N : ℝ)) ^ 2 * (N : ℝ)⁻¹ := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [carrierArc_length k]
    _ <= ((2 * Real.pi) / (N : ℝ)) ^ 2 :=
      sum_const_invNat_le hN K (sq_nonneg _)

private theorem sum_slowBandPoly_carrier_variance_le_global
    {N L : Nat} (hN : 0 < N) (p : Fin L -> ℂ) :
    ∑ k : Fin N,
        ∫ x in arcSet (carrierArc N k),
          ‖slowBandPoly p x - slowBandPoly p (carrierBase k)‖ ^ 2
            ∂ μCircle
      <=
        ((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) *
          ((2 * Real.pi) / (N : ℝ)) ^ 2 := by
  let b : ℝ := (L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)
  have hb : 0 <= b := by
    have hL : 0 <= (L : ℝ) ^ 3 := by positivity
    have hmass : 0 <= circleL2Sq (slowBandPoly p) :=
      circleL2Sq_nonneg (slowBandPoly p)
    exact mul_nonneg hL hmass
  have hpoint :
      ∀ k : Fin N,
        (∫ x in arcSet (carrierArc N k),
          ‖slowBandPoly p x - slowBandPoly p (carrierBase k)‖ ^ 2
            ∂ μCircle) <=
        b * (arcLength (carrierArc N k) ^ 2 * (N : ℝ)⁻¹) := by
    intro k
    have h :=
      slowBandPoly_carrier_variance_le_measure (N := N) (L := L) k p
    rw [carrierArc_mu_real_eq_inv_nat k] at h
    simpa [b, mul_assoc, mul_left_comm, mul_comm] using h
  have hsum :=
    Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N)))
      (fun k hk => hpoint k)
  have hlen :=
    sum_carrier_length_sq_invNat_le (N := N) hN
      (Finset.univ : Finset (Fin N))
  calc
    ∑ k : Fin N,
        ∫ x in arcSet (carrierArc N k),
          ‖slowBandPoly p x - slowBandPoly p (carrierBase k)‖ ^ 2
            ∂ μCircle
        <=
      ∑ k : Fin N,
        b * (arcLength (carrierArc N k) ^ 2 * (N : ℝ)⁻¹) := by
          simpa using hsum
    _ =
      b * ∑ k : Fin N,
        arcLength (carrierArc N k) ^ 2 * (N : ℝ)⁻¹ := by
          rw [Finset.mul_sum]
    _ <= b * ((2 * Real.pi) / (N : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left (by simpa using hlen) hb
    _ =
      ((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) *
        ((2 * Real.pi) / (N : ℝ)) ^ 2 := by
        rfl

private theorem slowBandPoly_l2_le_sampled_base_mass_plus_variance_error
    {N L : Nat} (hN : 0 < N) (p : Fin L -> ℂ) :
    circleL2Sq (slowBandPoly p) <=
      (1 / Real.pi) *
          (∑ k : Fin N,
            arcLength (carrierArc N k) *
              ‖slowBandPoly p (carrierBase k)‖ ^ 2) +
        2 *
          (((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) *
            ((2 * Real.pi) / (N : ℝ)) ^ 2) := by
  let f : Circle -> ℝ := fun x => ‖slowBandPoly p x‖ ^ 2
  let V : Fin N -> ℝ := fun k =>
    ∫ x in arcSet (carrierArc N k),
      ‖slowBandPoly p x - slowBandPoly p (carrierBase k)‖ ^ 2 ∂ μCircle
  let B : Fin N -> ℝ := fun k =>
    arcLength (carrierArc N k) *
      ‖slowBandPoly p (carrierBase k)‖ ^ 2
  have hf_cont : Continuous f :=
    (continuous_slowBandPoly p).norm.pow 2
  have hf_int : MeasureTheory.Integrable f μCircle := by
    simpa [f, μCircle] using
      hf_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hdecomp :
      (∫ x, f x ∂ μCircle) =
        ∑ k : Fin N, ∫ x in arcSet (carrierArc N k), f x ∂ μCircle :=
    carrierArc_setIntegral_univ_wip (N := N) hN f hf_int
  have hlocal :
      ∑ k : Fin N, ∫ x in arcSet (carrierArc N k), f x ∂ μCircle <=
        ∑ k : Fin N, ((1 / Real.pi) * B k + 2 * V k) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    simpa [f, B, V] using
      slowBandPoly_carrier_mass_le_base_plus_variance (N := N) (L := L) k p
  have hsplit :
      ∑ k : Fin N, ((1 / Real.pi) * B k + 2 * V k) =
        (1 / Real.pi) * (∑ k : Fin N, B k) +
          2 * (∑ k : Fin N, V k) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have hvar :
      ∑ k : Fin N, V k <=
        ((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) *
          ((2 * Real.pi) / (N : ℝ)) ^ 2 := by
    simpa [V] using
      sum_slowBandPoly_carrier_variance_le_global (N := N) (L := L) hN p
  calc
    circleL2Sq (slowBandPoly p)
        = ∫ x, f x ∂ μCircle := by rfl
    _ = ∑ k : Fin N, ∫ x in arcSet (carrierArc N k), f x ∂ μCircle :=
      hdecomp
    _ <= ∑ k : Fin N, ((1 / Real.pi) * B k + 2 * V k) :=
      hlocal
    _ =
      (1 / Real.pi) * (∑ k : Fin N, B k) +
        2 * (∑ k : Fin N, V k) := hsplit
    _ <=
      (1 / Real.pi) * (∑ k : Fin N, B k) +
        2 *
          (((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) *
            ((2 * Real.pi) / (N : ℝ)) ^ 2) := by
          nlinarith
    _ =
      (1 / Real.pi) *
          (∑ k : Fin N,
            arcLength (carrierArc N k) *
              ‖slowBandPoly p (carrierBase k)‖ ^ 2) +
        2 *
          (((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) *
            ((2 * Real.pi) / (N : ℝ)) ^ 2) := by
        rfl

private theorem sum_theta_l2_invNat_error_le
    {N L : Nat} (hN : 0 < N) (K : Finset (Fin N))
    (p : Fin L -> ℂ) {theta : ℝ} :
    Finset.sum K (fun _k =>
        4 * Crot *
          ((4 * theta) ^ 2 *
            (((L : ℝ) * circleL2Sq (bandPoly N p)) * (N : ℝ)⁻¹))) <=
      4 * Crot *
        ((4 * theta) ^ 2 *
          ((L : ℝ) * circleL2Sq (bandPoly N p))) := by
  let a : ℝ :=
    4 * Crot *
      ((4 * theta) ^ 2 * ((L : ℝ) * circleL2Sq (bandPoly N p)))
  have ha : 0 <= a := by
    have hC : 0 <= 4 * Crot := by nlinarith [Crot_pos]
    have htheta : 0 <= (4 * theta) ^ 2 := sq_nonneg _
    have hL : 0 <= (L : ℝ) := by exact_mod_cast Nat.zero_le L
    have hmass : 0 <= circleL2Sq (bandPoly N p) :=
      circleL2Sq_nonneg (bandPoly N p)
    exact mul_nonneg hC (mul_nonneg htheta (mul_nonneg hL hmass))
  calc
    Finset.sum K (fun _k =>
        4 * Crot *
          ((4 * theta) ^ 2 *
            (((L : ℝ) * circleL2Sq (bandPoly N p)) * (N : ℝ)⁻¹)))
        = Finset.sum K (fun _k => a * (N : ℝ)⁻¹) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          simp [a]
          ring
    _ <= a := sum_const_invNat_le hN K ha
    _ =
      4 * Crot *
        ((4 * theta) ^ 2 *
          ((L : ℝ) * circleL2Sq (bandPoly N p))) := by rfl

private theorem sum_slow_variance_l2_invNat_error_le
    {N L : Nat} (hN : 0 < N) (K : Finset (Fin N))
    (p : Fin L -> ℂ) :
    ∑ k ∈ K,
        2 * Crot *
          ((((L : ℝ) ^ 3 * circleL2Sq (bandPoly N p)) *
              arcLength (carrierArc N k) ^ 2) * (N : ℝ)⁻¹) <=
      2 * Crot *
        (((L : ℝ) ^ 3 * circleL2Sq (bandPoly N p)) *
          ((2 * Real.pi) / (N : ℝ)) ^ 2) := by
  let b : ℝ := 2 * Crot * ((L : ℝ) ^ 3 * circleL2Sq (bandPoly N p))
  have hb : 0 <= b := by
    have hC : 0 <= 2 * Crot := by nlinarith [Crot_pos]
    have hL : 0 <= (L : ℝ) ^ 3 := by positivity
    have hmass : 0 <= circleL2Sq (bandPoly N p) :=
      circleL2Sq_nonneg (bandPoly N p)
    exact mul_nonneg hC (mul_nonneg hL hmass)
  have hsum := sum_carrier_length_sq_invNat_le hN K
  calc
    ∑ k ∈ K,
        2 * Crot *
          ((((L : ℝ) ^ 3 * circleL2Sq (bandPoly N p)) *
              arcLength (carrierArc N k) ^ 2) * (N : ℝ)⁻¹)
        = b * ∑ k ∈ K,
            arcLength (carrierArc N k) ^ 2 * (N : ℝ)⁻¹ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro k hk
          simp [b]
          ring
    _ <= b * ((2 * Real.pi) / (N : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsum hb
    _ =
      2 * Crot *
        (((L : ℝ) ^ 3 * circleL2Sq (bandPoly N p)) *
          ((2 * Real.pi) / (N : ℝ)) ^ 2) := by
        simp [b]
        ring

private theorem sum_goodCarrier_base_mass_le_defect_plus_l2_errors
    {D N L : Nat} (hN : 0 < N)
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) (p : Fin L -> ℂ)
    {delta theta : ℝ} (hdelta_pos : 0 < delta)
    (htheta_nonneg : 0 <= theta) (htheta_le : theta <= 1 / 2)
    (K : Finset (Fin N))
    (hgood : ∀ k ∈ K,
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta)
    (hslope : ∀ k ∈ K,
      (∑ n : Fin (D + 1), ‖q n‖ * (n.1 : ℝ)) *
          arcLength (carrierArc N k) <=
        theta *
          (‖(polyOfCoeff q).leadingCoeff‖ *
            delta ^ (polyOfCoeff q).roots.card)) :
    ∑ k ∈ K,
        arcLength (carrierArc N k) *
          ‖slowBandPoly p (carrierBase k)‖ ^ 2 <=
      4 * Crot *
          (∑ k ∈ K,
            ∫ x in arcSet (carrierArc N k),
              (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle) +
        4 * Crot *
          ((4 * theta) ^ 2 *
            ((L : ℝ) * circleL2Sq (bandPoly N p))) +
        2 * Crot *
          (((L : ℝ) ^ 3 * circleL2Sq (bandPoly N p)) *
            ((2 * Real.pi) / (N : ℝ)) ^ 2) := by
  let Dterm : Fin N -> ℝ := fun k =>
    4 * Crot *
      ∫ x in arcSet (carrierArc N k),
        (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle
  let Tterm : ℝ :=
    4 * Crot *
      ((4 * theta) ^ 2 *
        (((L : ℝ) * circleL2Sq (bandPoly N p)) * (N : ℝ)⁻¹))
  let Vterm : Fin N -> ℝ := fun k =>
    2 * Crot *
      ((((L : ℝ) ^ 3 * circleL2Sq (bandPoly N p)) *
          arcLength (carrierArc N k) ^ 2) * (N : ℝ)⁻¹)
  have hlocal :
      ∑ k ∈ K,
          arcLength (carrierArc N k) *
            ‖slowBandPoly p (carrierBase k)‖ ^ 2 <=
        ∑ k ∈ K, (Dterm k + Tterm + Vterm k) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    have h :=
      goodCarrier_base_mass_le_actual_defect_plus_l2_invN_errors_of_arcLength_slope
        (q := q) hq p hdelta_pos htheta_nonneg htheta_le
        (hgood k hk) (hslope k hk)
    simpa [Dterm, Tterm, Vterm, add_assoc] using h
  have hsplit :
      ∑ k ∈ K, (Dterm k + Tterm + Vterm k) =
        (∑ k ∈ K, Dterm k) +
          (Finset.sum K fun _k => Tterm) +
          (∑ k ∈ K, Vterm k) := by
    simp [Finset.sum_add_distrib, add_comm, add_left_comm]
  have htheta :
      Finset.sum K (fun _k => Tterm) <=
        4 * Crot *
          ((4 * theta) ^ 2 *
            ((L : ℝ) * circleL2Sq (bandPoly N p))) := by
    simpa [Tterm] using
      sum_theta_l2_invNat_error_le (N := N) (L := L) hN K p (theta := theta)
  have hvar :
      ∑ k ∈ K, Vterm k <=
        2 * Crot *
          (((L : ℝ) ^ 3 * circleL2Sq (bandPoly N p)) *
            ((2 * Real.pi) / (N : ℝ)) ^ 2) := by
    simpa [Vterm] using
      sum_slow_variance_l2_invNat_error_le (N := N) (L := L) hN K p
  calc
    ∑ k ∈ K,
        arcLength (carrierArc N k) *
          ‖slowBandPoly p (carrierBase k)‖ ^ 2
        <= ∑ k ∈ K, (Dterm k + Tterm + Vterm k) := hlocal
    _ =
        (∑ k ∈ K, Dterm k) +
          (Finset.sum K fun _k => Tterm) +
          (∑ k ∈ K, Vterm k) := hsplit
    _ <=
      (∑ k ∈ K, Dterm k) +
        4 * Crot *
          ((4 * theta) ^ 2 *
            ((L : ℝ) * circleL2Sq (bandPoly N p))) +
        2 * Crot *
          (((L : ℝ) ^ 3 * circleL2Sq (bandPoly N p)) *
            ((2 * Real.pi) / (N : ℝ)) ^ 2) := by
          nlinarith
    _ =
      4 * Crot *
          (∑ k ∈ K,
            ∫ x in arcSet (carrierArc N k),
              (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle) +
        4 * Crot *
          ((4 * theta) ^ 2 *
            ((L : ℝ) * circleL2Sq (bandPoly N p))) +
        2 * Crot *
          (((L : ℝ) ^ 3 * circleL2Sq (bandPoly N p)) *
            ((2 * Real.pi) / (N : ℝ)) ^ 2) := by
          simp [Dterm, Finset.mul_sum]

private theorem sum_carrier_defect_integrals_le_global_defectSq
    {D N L : Nat} (K : Finset (Fin N))
    (q : Fin (D + 1) -> ℂ) (p : Fin L -> ℂ) :
    ∑ k ∈ K,
        ∫ x in arcSet (carrierArc N k),
          (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle
      <= defectSq (lowPoly q) (bandPoly N p) := by
  let f : Circle -> ℝ := fun x =>
    (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2
  have hcont : Continuous f :=
    (((continuous_lowPoly q).add (continuous_bandPoly N p)).norm.sub
      (continuous_lowPoly q).norm).pow 2
  have hf_int : MeasureTheory.Integrable f μCircle := by
    simpa [μCircle] using
      hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hf_nonneg : 0 ≤ᵐ[μCircle] f := by
    filter_upwards with x
    exact sq_nonneg _
  have hsum_ioc :
      (∫ x in ⋃ k ∈ K, carrierIocImage k, f x ∂ μCircle) =
        ∑ k ∈ K, ∫ x in carrierIocImage k, f x ∂ μCircle :=
    carrierIocImage_setIntegral_biUnion_finset_wip K f
      (fun k hk => hf_int.integrableOn)
  have hsum_arc :
      ∑ k ∈ K,
          ∫ x in arcSet (carrierArc N k), f x ∂ μCircle =
        ∑ k ∈ K, ∫ x in carrierIocImage k, f x ∂ μCircle := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    exact carrierArc_setIntegral_eq_iocImage_wip k f
  have hunion_le :
      (∫ x in ⋃ k ∈ K, carrierIocImage k, f x ∂ μCircle) <=
        ∫ x, f x ∂ μCircle :=
    MeasureTheory.setIntegral_le_integral hf_int hf_nonneg
  calc
    ∑ k ∈ K,
        ∫ x in arcSet (carrierArc N k),
          (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle
        = ∑ k ∈ K, ∫ x in arcSet (carrierArc N k), f x ∂ μCircle := by
          rfl
    _ = ∑ k ∈ K, ∫ x in carrierIocImage k, f x ∂ μCircle := hsum_arc
    _ = ∫ x in ⋃ k ∈ K, carrierIocImage k, f x ∂ μCircle := hsum_ioc.symm
    _ <= ∫ x, f x ∂ μCircle := hunion_le
    _ = defectSq (lowPoly q) (bandPoly N p) := by
          simp [f, defectSq, μCircle]

private theorem
    sum_goodCarrier_average_mass_le_global_defect_plus_variance_of_root_product_canonical
    {D N L : Nat}
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) (p : Fin L -> ℂ)
    {delta : ℝ} (hdelta_pos : 0 < delta)
    (K : Finset (Fin N))
    (hgood : ∀ k ∈ K,
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta)
    (harc : ∀ k ∈ K,
      arcLength (carrierArc N k) <=
        (1 / (128 * ((D + 1 : Nat) : ℝ))) * delta) :
    ∑ k ∈ K,
        arcLength (carrierArc N k) *
          ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 <=
      8 * Crot * defectSq (lowPoly q) (bandPoly N p) +
        (8 * Crot * (4 * (1 / 64 : ℝ)) ^ 2 + 4 * Crot) *
          ∑ k ∈ K,
            ∫ x in arcSet (carrierArc N k),
              ‖slowBandPoly p x -
                carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 ∂ μCircle := by
  let eps : ℝ := 1 / (128 * ((D + 1 : Nat) : ℝ))
  let theta : ℝ := (1 / 64 : ℝ)
  let Dterm : Fin N -> ℝ := fun k =>
    ∫ x in arcSet (carrierArc N k),
      (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle
  let Vterm : Fin N -> ℝ := fun k =>
    ∫ x in arcSet (carrierArc N k),
      ‖slowBandPoly p x -
        carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 ∂ μCircle
  have heps : 0 <= eps := by
    dsimp [eps]
    positivity
  have htheta_nonneg : 0 <= theta := by
    dsimp [theta]
    norm_num
  have htheta_le : theta <= 1 / 2 := by
    dsimp [theta]
    norm_num
  have htheta_le_small : theta <= 1 / 64 := by
    dsimp [theta]
    rfl
  have htheta_bound :
      (1 + eps) ^ (polyOfCoeff q).roots.card - 1 <= theta := by
    simpa [eps, theta] using root_product_theta_bound_one_div_sixtyfour q
  have hlocal :
      ∑ k ∈ K,
          arcLength (carrierArc N k) *
            ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 <=
        ∑ k ∈ K,
          (8 * Crot * Dterm k +
            (8 * Crot * (4 * theta) ^ 2 + 4 * Crot) * Vterm k) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    have h :=
     goodCarrier_average_mass_le_actual_defect_plus_fast_variance_absorbed_of_root_product_arcLength
        (q := q) hq p hdelta_pos
        (eps := eps) (theta := theta)
        heps htheta_bound htheta_nonneg htheta_le htheta_le_small
        (hgood k hk) (by simpa [eps] using harc k hk)
    simpa [Dterm, Vterm, theta] using h
  have hsplit :
      ∑ k ∈ K,
          (8 * Crot * Dterm k +
            (8 * Crot * (4 * theta) ^ 2 + 4 * Crot) * Vterm k) =
        8 * Crot * (∑ k ∈ K, Dterm k) +
          (8 * Crot * (4 * theta) ^ 2 + 4 * Crot) *
            (∑ k ∈ K, Vterm k) := by
    simp [Finset.sum_add_distrib, Finset.mul_sum]
  have hD :
      ∑ k ∈ K, Dterm k <= defectSq (lowPoly q) (bandPoly N p) := by
    simpa [Dterm] using sum_carrier_defect_integrals_le_global_defectSq K q p
  have hcoefD : 0 <= 8 * Crot := by
    nlinarith [Crot_pos]
  have hDmul :
      8 * Crot * (∑ k ∈ K, Dterm k) <=
        8 * Crot * defectSq (lowPoly q) (bandPoly N p) :=
    mul_le_mul_of_nonneg_left hD hcoefD
  calc
    ∑ k ∈ K,
        arcLength (carrierArc N k) *
          ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2
        <=
      ∑ k ∈ K,
        (8 * Crot * Dterm k +
          (8 * Crot * (4 * theta) ^ 2 + 4 * Crot) * Vterm k) :=
        hlocal
    _ =
      8 * Crot * (∑ k ∈ K, Dterm k) +
        (8 * Crot * (4 * theta) ^ 2 + 4 * Crot) *
          (∑ k ∈ K, Vterm k) := hsplit
    _ <=
      8 * Crot * defectSq (lowPoly q) (bandPoly N p) +
        (8 * Crot * (4 * theta) ^ 2 + 4 * Crot) *
          (∑ k ∈ K, Vterm k) := by
        nlinarith
    _ =
      8 * Crot * defectSq (lowPoly q) (bandPoly N p) +
        (8 * Crot * (4 * (1 / 64 : ℝ)) ^ 2 + 4 * Crot) *
          ∑ k ∈ K,
            ∫ x in arcSet (carrierArc N k),
              ‖slowBandPoly p x -
                carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 ∂ μCircle := by
        simp [theta, Vterm]

private theorem sum_goodCarrier_base_mass_le_global_defect_plus_fast_variance_of_oscillation
    {D N L : Nat} (hN : 0 < N)
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) (p : Fin L -> ℂ)
    {delta theta : ℝ} (hdelta_pos : 0 < delta)
    (htheta_nonneg : 0 <= theta) (htheta_le : theta <= 1 / 2)
    (htheta_le_small : theta <= 1 / 64)
    (K : Finset (Fin N))
    (hgood : ∀ k ∈ K,
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta)
    (hosc : ∀ k ∈ K, ∀ x ∈ arcSet (carrierArc N k),
      ‖lowPoly q x - lowPoly q (carrierBase k)‖ <=
        theta * ‖lowPoly q (carrierBase k)‖) :
    ∑ k ∈ K,
        arcLength (carrierArc N k) *
          ‖slowBandPoly p (carrierBase k)‖ ^ 2 <=
      8 * Crot * defectSq (lowPoly q) (bandPoly N p) +
        8 * Crot *
          (((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) *
            ((2 * Real.pi) / (N : ℝ)) ^ 2) := by
  let Dterm : Fin N -> ℝ := fun k =>
    ∫ x in arcSet (carrierArc N k),
      (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle
  let Vterm : Fin N -> ℝ := fun k =>
    ∫ x in arcSet (carrierArc N k),
      ‖slowBandPoly p x - slowBandPoly p (carrierBase k)‖ ^ 2 ∂ μCircle
  have hlocal :
      ∑ k ∈ K,
          arcLength (carrierArc N k) *
            ‖slowBandPoly p (carrierBase k)‖ ^ 2 <=
        ∑ k ∈ K, (8 * Crot * Dterm k + 8 * Crot * Vterm k) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    have h :=
      goodCarrier_base_mass_le_actual_defect_plus_fast_variance_absorbed
        (q := q) hq p hdelta_pos htheta_nonneg htheta_le htheta_le_small
        (hgood k hk) (hosc k hk)
    simpa [Dterm, Vterm] using h
  have hsplit :
      ∑ k ∈ K, (8 * Crot * Dterm k + 8 * Crot * Vterm k) =
        8 * Crot * (∑ k ∈ K, Dterm k) +
          8 * Crot * (∑ k ∈ K, Vterm k) := by
    simp [Finset.sum_add_distrib, Finset.mul_sum]
  have hD :
      ∑ k ∈ K, Dterm k <= defectSq (lowPoly q) (bandPoly N p) := by
    simpa [Dterm] using sum_carrier_defect_integrals_le_global_defectSq K q p
  have hVsubset :
      ∑ k ∈ K, Vterm k <= ∑ k : Fin N, Vterm k := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ K) ?_
    intro k hk_univ hk_not
    exact MeasureTheory.integral_nonneg fun x => sq_nonneg _
  have hVglobal :
      ∑ k : Fin N, Vterm k <=
        ((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) *
          ((2 * Real.pi) / (N : ℝ)) ^ 2 := by
    simpa [Vterm] using
      sum_slowBandPoly_carrier_variance_le_global (N := N) (L := L) hN p
  have hV :
      ∑ k ∈ K, Vterm k <=
        ((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) *
          ((2 * Real.pi) / (N : ℝ)) ^ 2 :=
    hVsubset.trans hVglobal
  have hcoef_nonneg : 0 <= 8 * Crot := by
    nlinarith [Crot_pos]
  have hDmul :
      8 * Crot * (∑ k ∈ K, Dterm k) <=
        8 * Crot * defectSq (lowPoly q) (bandPoly N p) :=
    mul_le_mul_of_nonneg_left hD hcoef_nonneg
  have hVmul :
      8 * Crot * (∑ k ∈ K, Vterm k) <=
        8 * Crot *
          (((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) *
            ((2 * Real.pi) / (N : ℝ)) ^ 2) :=
    mul_le_mul_of_nonneg_left hV hcoef_nonneg
  calc
    ∑ k ∈ K,
        arcLength (carrierArc N k) *
          ‖slowBandPoly p (carrierBase k)‖ ^ 2
        <= ∑ k ∈ K, (8 * Crot * Dterm k + 8 * Crot * Vterm k) :=
          hlocal
    _ =
      8 * Crot * (∑ k ∈ K, Dterm k) +
        8 * Crot * (∑ k ∈ K, Vterm k) := hsplit
    _ <=
      8 * Crot * defectSq (lowPoly q) (bandPoly N p) +
        8 * Crot *
          (((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) *
            ((2 * Real.pi) / (N : ℝ)) ^ 2) := by
          nlinarith

private theorem
    sum_goodCarrier_base_mass_le_global_defect_plus_fast_variance_of_root_product_arcLength
    {D N L : Nat} (hN : 0 < N)
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) (p : Fin L -> ℂ)
    {delta eps theta : ℝ} (hdelta_pos : 0 < delta)
    (heps : 0 <= eps)
    (htheta_bound :
      (1 + eps) ^ (polyOfCoeff q).roots.card - 1 <= theta)
    (htheta_nonneg : 0 <= theta) (htheta_le : theta <= 1 / 2)
    (htheta_le_small : theta <= 1 / 64)
    (K : Finset (Fin N))
    (hgood : ∀ k ∈ K,
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta)
    (harc : ∀ k ∈ K, arcLength (carrierArc N k) <= eps * delta) :
    ∑ k ∈ K,
        arcLength (carrierArc N k) *
          ‖slowBandPoly p (carrierBase k)‖ ^ 2 <=
      8 * Crot * defectSq (lowPoly q) (bandPoly N p) +
        8 * Crot *
          (((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) *
            ((2 * Real.pi) / (N : ℝ)) ^ 2) := by
  exact
    sum_goodCarrier_base_mass_le_global_defect_plus_fast_variance_of_oscillation
      (D := D) (N := N) (L := L) hN (q := q) hq p
      hdelta_pos htheta_nonneg htheta_le htheta_le_small K hgood
      (fun k hk =>
        goodCarrier_relative_oscillation_of_root_product_arcLength_bound
          q heps htheta_bound (hgood k hk) (harc k hk))

private theorem
    sum_goodCarrier_base_mass_le_global_defect_plus_fast_variance_of_root_product_canonical
    {D N L : Nat} (hN : 0 < N)
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) (p : Fin L -> ℂ)
    {delta : ℝ} (hdelta_pos : 0 < delta)
    (K : Finset (Fin N))
    (hgood : ∀ k ∈ K,
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta)
    (harc : ∀ k ∈ K,
      arcLength (carrierArc N k) <=
        (1 / (128 * ((D + 1 : Nat) : ℝ))) * delta) :
    ∑ k ∈ K,
        arcLength (carrierArc N k) *
          ‖slowBandPoly p (carrierBase k)‖ ^ 2 <=
      8 * Crot * defectSq (lowPoly q) (bandPoly N p) +
        8 * Crot *
          (((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) *
            ((2 * Real.pi) / (N : ℝ)) ^ 2) := by
  let eps : ℝ := 1 / (128 * ((D + 1 : Nat) : ℝ))
  have heps : 0 <= eps := by
    dsimp [eps]
    positivity
  have htheta_nonneg : 0 <= (1 / 64 : ℝ) := by norm_num
  have htheta_le : (1 / 64 : ℝ) <= 1 / 2 := by norm_num
  have htheta_le_small : (1 / 64 : ℝ) <= 1 / 64 := le_rfl
  have htheta_bound :
      (1 + eps) ^ (polyOfCoeff q).roots.card - 1 <= (1 / 64 : ℝ) := by
    simpa [eps] using root_product_theta_bound_one_div_sixtyfour q
  exact
    sum_goodCarrier_base_mass_le_global_defect_plus_fast_variance_of_root_product_arcLength
      (D := D) (N := N) (L := L) hN (q := q) hq p hdelta_pos
      (eps := eps) (theta := (1 / 64 : ℝ))
      heps htheta_bound htheta_nonneg htheta_le htheta_le_small K hgood
      (by simpa [eps] using harc)

private theorem sum_goodCarrier_base_mass_le_global_defect_plus_fast_variance
    {D N L : Nat} (hN : 0 < N)
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) (p : Fin L -> ℂ)
    {delta theta : ℝ} (hdelta_pos : 0 < delta)
    (htheta_nonneg : 0 <= theta) (htheta_le : theta <= 1 / 2)
    (htheta_le_small : theta <= 1 / 64)
    (K : Finset (Fin N))
    (hgood : ∀ k ∈ K,
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta)
    (hslope : ∀ k ∈ K,
      (∑ n : Fin (D + 1), ‖q n‖ * (n.1 : ℝ)) *
          arcLength (carrierArc N k) <=
        theta *
          (‖(polyOfCoeff q).leadingCoeff‖ *
            delta ^ (polyOfCoeff q).roots.card)) :
    ∑ k ∈ K,
        arcLength (carrierArc N k) *
          ‖slowBandPoly p (carrierBase k)‖ ^ 2 <=
      8 * Crot * defectSq (lowPoly q) (bandPoly N p) +
        8 * Crot *
          (((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) *
            ((2 * Real.pi) / (N : ℝ)) ^ 2) := by
  let Dterm : Fin N -> ℝ := fun k =>
    ∫ x in arcSet (carrierArc N k),
      (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle
  let Vterm : Fin N -> ℝ := fun k =>
    ∫ x in arcSet (carrierArc N k),
      ‖slowBandPoly p x - slowBandPoly p (carrierBase k)‖ ^ 2 ∂ μCircle
  have hlocal :
      ∑ k ∈ K,
          arcLength (carrierArc N k) *
            ‖slowBandPoly p (carrierBase k)‖ ^ 2 <=
        ∑ k ∈ K, (8 * Crot * Dterm k + 8 * Crot * Vterm k) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    have h :=
      goodCarrier_base_mass_le_actual_defect_plus_fast_variance_absorbed_of_arcLength_slope
        (q := q) hq p hdelta_pos htheta_nonneg htheta_le htheta_le_small
        (hgood k hk) (hslope k hk)
    simpa [Dterm, Vterm] using h
  have hsplit :
      ∑ k ∈ K, (8 * Crot * Dterm k + 8 * Crot * Vterm k) =
        8 * Crot * (∑ k ∈ K, Dterm k) +
          8 * Crot * (∑ k ∈ K, Vterm k) := by
    simp [Finset.sum_add_distrib, Finset.mul_sum]
  have hD :
      ∑ k ∈ K, Dterm k <= defectSq (lowPoly q) (bandPoly N p) := by
    simpa [Dterm] using sum_carrier_defect_integrals_le_global_defectSq K q p
  have hVsubset :
      ∑ k ∈ K, Vterm k <= ∑ k : Fin N, Vterm k := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ K) ?_
    intro k hk_univ hk_not
    exact MeasureTheory.integral_nonneg fun x => sq_nonneg _
  have hVglobal :
      ∑ k : Fin N, Vterm k <=
        ((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) *
          ((2 * Real.pi) / (N : ℝ)) ^ 2 := by
    simpa [Vterm] using
      sum_slowBandPoly_carrier_variance_le_global (N := N) (L := L) hN p
  have hV :
      ∑ k ∈ K, Vterm k <=
        ((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) *
          ((2 * Real.pi) / (N : ℝ)) ^ 2 :=
    hVsubset.trans hVglobal
  have hcoef_nonneg : 0 <= 8 * Crot := by
    nlinarith [Crot_pos]
  have hDmul :
      8 * Crot * (∑ k ∈ K, Dterm k) <=
        8 * Crot * defectSq (lowPoly q) (bandPoly N p) :=
    mul_le_mul_of_nonneg_left hD hcoef_nonneg
  have hVmul :
      8 * Crot * (∑ k ∈ K, Vterm k) <=
        8 * Crot *
          (((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) *
            ((2 * Real.pi) / (N : ℝ)) ^ 2) :=
    mul_le_mul_of_nonneg_left hV hcoef_nonneg
  calc
    ∑ k ∈ K,
        arcLength (carrierArc N k) *
          ‖slowBandPoly p (carrierBase k)‖ ^ 2
        <= ∑ k ∈ K, (8 * Crot * Dterm k + 8 * Crot * Vterm k) :=
          hlocal
    _ =
      8 * Crot * (∑ k ∈ K, Dterm k) +
        8 * Crot * (∑ k ∈ K, Vterm k) := hsplit
    _ <=
      8 * Crot * defectSq (lowPoly q) (bandPoly N p) +
        8 * Crot *
          (((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) *
            ((2 * Real.pi) / (N : ℝ)) ^ 2) := by
          nlinarith

private theorem sum_goodCarrierIndices_base_mass_le_global_defect_plus_fast_variance
    {D N L : Nat} (hN : 0 < N)
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) (p : Fin L -> ℂ)
    {delta theta : ℝ} (hdelta_pos : 0 < delta)
    (htheta_nonneg : 0 <= theta) (htheta_le : theta <= 1 / 2)
    (htheta_le_small : theta <= 1 / 64)
    (hslope : ∀ k ∈ goodCarrierIndices N (polyOfCoeff q).roots delta,
      (∑ n : Fin (D + 1), ‖q n‖ * (n.1 : ℝ)) *
          arcLength (carrierArc N k) <=
        theta *
          (‖(polyOfCoeff q).leadingCoeff‖ *
            delta ^ (polyOfCoeff q).roots.card)) :
    ∑ k ∈ goodCarrierIndices N (polyOfCoeff q).roots delta,
        arcLength (carrierArc N k) *
          ‖slowBandPoly p (carrierBase k)‖ ^ 2 <=
      8 * Crot * defectSq (lowPoly q) (bandPoly N p) +
        8 * Crot *
          (((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) *
            ((2 * Real.pi) / (N : ℝ)) ^ 2) := by
  exact sum_goodCarrier_base_mass_le_global_defect_plus_fast_variance
    (D := D) (N := N) (L := L) hN (q := q) hq p
    hdelta_pos htheta_nonneg htheta_le htheta_le_small
    (goodCarrierIndices N (polyOfCoeff q).roots delta)
    (fun k hk => goodCarrierIndices_not_bad hk) hslope

private theorem sum_goodCarrier_base_mass_le_global_defect_plus_l2_errors
    {D N L : Nat} (hN : 0 < N)
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) (p : Fin L -> ℂ)
    {delta theta : ℝ} (hdelta_pos : 0 < delta)
    (htheta_nonneg : 0 <= theta) (htheta_le : theta <= 1 / 2)
    (K : Finset (Fin N))
    (hgood : ∀ k ∈ K,
      k ∉ badCarrierIndices N (polyOfCoeff q).roots delta)
    (hslope : ∀ k ∈ K,
      (∑ n : Fin (D + 1), ‖q n‖ * (n.1 : ℝ)) *
          arcLength (carrierArc N k) <=
        theta *
          (‖(polyOfCoeff q).leadingCoeff‖ *
            delta ^ (polyOfCoeff q).roots.card)) :
    ∑ k ∈ K,
        arcLength (carrierArc N k) *
          ‖slowBandPoly p (carrierBase k)‖ ^ 2 <=
      4 * Crot * defectSq (lowPoly q) (bandPoly N p) +
        4 * Crot *
          ((4 * theta) ^ 2 *
            ((L : ℝ) * circleL2Sq (bandPoly N p))) +
        2 * Crot *
          (((L : ℝ) ^ 3 * circleL2Sq (bandPoly N p)) *
            ((2 * Real.pi) / (N : ℝ)) ^ 2) := by
  have hsum :=
    sum_goodCarrier_base_mass_le_defect_plus_l2_errors
      (D := D) (N := N) (L := L) hN (q := q) hq p
      hdelta_pos htheta_nonneg htheta_le K hgood hslope
  have hdef :=
    sum_carrier_defect_integrals_le_global_defectSq K q p
  have hcoef_nonneg : 0 <= 4 * Crot := by
    nlinarith [Crot_pos]
  have hdefmul :
      4 * Crot *
          (∑ k ∈ K,
            ∫ x in arcSet (carrierArc N k),
              (‖lowPoly q x + bandPoly N p x‖ - ‖lowPoly q x‖) ^ 2 ∂ μCircle)
        <= 4 * Crot * defectSq (lowPoly q) (bandPoly N p) :=
    mul_le_mul_of_nonneg_left hdef hcoef_nonneg
  nlinarith

private theorem sum_goodCarrierIndices_base_mass_le_global_defect_plus_l2_errors
    {D N L : Nat} (hN : 0 < N)
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) (p : Fin L -> ℂ)
    {delta theta : ℝ} (hdelta_pos : 0 < delta)
    (htheta_nonneg : 0 <= theta) (htheta_le : theta <= 1 / 2)
    (hslope : ∀ k ∈ goodCarrierIndices N (polyOfCoeff q).roots delta,
      (∑ n : Fin (D + 1), ‖q n‖ * (n.1 : ℝ)) *
          arcLength (carrierArc N k) <=
        theta *
          (‖(polyOfCoeff q).leadingCoeff‖ *
            delta ^ (polyOfCoeff q).roots.card)) :
    ∑ k ∈ goodCarrierIndices N (polyOfCoeff q).roots delta,
        arcLength (carrierArc N k) *
          ‖slowBandPoly p (carrierBase k)‖ ^ 2 <=
      4 * Crot * defectSq (lowPoly q) (bandPoly N p) +
        4 * Crot *
          ((4 * theta) ^ 2 *
            ((L : ℝ) * circleL2Sq (bandPoly N p))) +
        2 * Crot *
          (((L : ℝ) ^ 3 * circleL2Sq (bandPoly N p)) *
            ((2 * Real.pi) / (N : ℝ)) ^ 2) := by
  exact sum_goodCarrier_base_mass_le_global_defect_plus_l2_errors
    (D := D) (N := N) (L := L) hN (q := q) hq p
    hdelta_pos htheta_nonneg htheta_le
    (goodCarrierIndices N (polyOfCoeff q).roots delta)
    (fun k hk => goodCarrierIndices_not_bad hk) hslope

private theorem sum_carrier_base_mass_le_card_L_l2
    {N L : Nat} (K : Finset (Fin N)) (p : Fin L -> ℂ) :
    ∑ k ∈ K,
        arcLength (carrierArc N k) *
          ‖slowBandPoly p (carrierBase k)‖ ^ 2 <=
      (K.card : ℝ) *
        (((2 * Real.pi) / (N : ℝ)) *
          ((L : ℝ) * circleL2Sq (bandPoly N p))) := by
  have hpoint :
      ∀ k ∈ K,
        arcLength (carrierArc N k) *
            ‖slowBandPoly p (carrierBase k)‖ ^ 2 <=
          ((2 * Real.pi) / (N : ℝ)) *
            ((L : ℝ) * circleL2Sq (bandPoly N p)) := by
    intro k hk
    have hNnat : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le k.1) k.2
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNnat
    have hlen_nonneg : 0 <= (2 * Real.pi) / (N : ℝ) := by positivity
    have hbase := slowBandPoly_norm_sq_le_L_circleL2Sq p (carrierBase k)
    have hmass_eq : circleL2Sq (slowBandPoly p) = circleL2Sq (bandPoly N p) := by
      rw [circleL2Sq_bandPoly, circleL2Sq_slowBandPoly]
    calc
      arcLength (carrierArc N k) *
          ‖slowBandPoly p (carrierBase k)‖ ^ 2
          = ((2 * Real.pi) / (N : ℝ)) *
              ‖slowBandPoly p (carrierBase k)‖ ^ 2 := by
            rw [carrierArc_length k]
      _ <= ((2 * Real.pi) / (N : ℝ)) *
            ((L : ℝ) * circleL2Sq (slowBandPoly p)) :=
          mul_le_mul_of_nonneg_left hbase hlen_nonneg
      _ = ((2 * Real.pi) / (N : ℝ)) *
            ((L : ℝ) * circleL2Sq (bandPoly N p)) := by
          rw [hmass_eq]
  calc
    ∑ k ∈ K,
        arcLength (carrierArc N k) *
          ‖slowBandPoly p (carrierBase k)‖ ^ 2
        <= ∑ _k ∈ K,
          ((2 * Real.pi) / (N : ℝ)) *
            ((L : ℝ) * circleL2Sq (bandPoly N p)) :=
          Finset.sum_le_sum hpoint
    _ =
      (K.card : ℝ) *
        (((2 * Real.pi) / (N : ℝ)) *
          ((L : ℝ) * circleL2Sq (bandPoly N p))) := by
        rw [Finset.sum_const, nsmul_eq_mul]

private theorem sum_badCarrier_base_mass_le_card_L_l2
    {D N L : Nat} (q : Fin (D + 1) -> ℂ) (p : Fin L -> ℂ)
    {delta : ℝ} :
    ∑ k ∈ badCarrierIndices N (polyOfCoeff q).roots delta,
        arcLength (carrierArc N k) *
          ‖slowBandPoly p (carrierBase k)‖ ^ 2 <=
      ((badCarrierIndices N (polyOfCoeff q).roots delta).card : ℝ) *
        (((2 * Real.pi) / (N : ℝ)) *
          ((L : ℝ) * circleL2Sq (bandPoly N p))) := by
  exact sum_carrier_base_mass_le_card_L_l2
    (badCarrierIndices N (polyOfCoeff q).roots delta) p

private theorem sum_univ_eq_sdiff_add
    {α : Type} [Fintype α] [DecidableEq α]
    (bad : Finset α) (f : α -> ℝ) :
    ∑ x : α, f x =
      ∑ x ∈ (Finset.univ \ bad), f x + ∑ x ∈ bad, f x := by
  let good : Finset α := Finset.univ \ bad
  have hdisj : Disjoint good bad := by
    rw [Finset.disjoint_left]
    intro x hx hb
    exact (Finset.mem_sdiff.mp hx).2 hb
  have hunion : good ∪ bad = (Finset.univ : Finset α) := by
    ext x
    by_cases hx : x ∈ bad <;> simp [good, hx]
  have hfirst : ∑ x : α, f x = ∑ x ∈ good ∪ bad, f x := by
    rw [hunion]
  have hsecond :
      ∑ x ∈ good ∪ bad, f x =
        ∑ x ∈ good, f x + ∑ x ∈ bad, f x := by
    exact Finset.sum_union hdisj
  calc
    ∑ x : α, f x = ∑ x ∈ good ∪ bad, f x := hfirst
    _ = ∑ x ∈ good, f x + ∑ x ∈ bad, f x := hsecond
    _ = ∑ x ∈ (Finset.univ \ bad), f x + ∑ x ∈ bad, f x := by
      rfl

private theorem sum_carrier_base_mass_eq_good_add_bad
    {D N L : Nat} (q : Fin (D + 1) -> ℂ) (p : Fin L -> ℂ)
    {delta : ℝ} :
    ∑ k : Fin N,
        arcLength (carrierArc N k) *
          ‖slowBandPoly p (carrierBase k)‖ ^ 2 =
      ∑ k ∈ goodCarrierIndices N (polyOfCoeff q).roots delta,
        arcLength (carrierArc N k) *
          ‖slowBandPoly p (carrierBase k)‖ ^ 2 +
      ∑ k ∈ badCarrierIndices N (polyOfCoeff q).roots delta,
        arcLength (carrierArc N k) *
          ‖slowBandPoly p (carrierBase k)‖ ^ 2 := by
  classical
  change
    ∑ k : Fin N,
        arcLength (carrierArc N k) *
          ‖slowBandPoly p (carrierBase k)‖ ^ 2 =
      ∑ k ∈ ((Finset.univ : Finset (Fin N)) \
          badCarrierIndices N (polyOfCoeff q).roots delta),
        arcLength (carrierArc N k) *
          ‖slowBandPoly p (carrierBase k)‖ ^ 2 +
      ∑ k ∈ badCarrierIndices N (polyOfCoeff q).roots delta,
        arcLength (carrierArc N k) *
          ‖slowBandPoly p (carrierBase k)‖ ^ 2
  exact
    sum_univ_eq_sdiff_add
      (badCarrierIndices N (polyOfCoeff q).roots delta)
      (fun k : Fin N =>
        arcLength (carrierArc N k) *
          ‖slowBandPoly p (carrierBase k)‖ ^ 2)

private theorem sum_carrier_average_mass_eq_good_add_bad
    {D N L : Nat} (q : Fin (D + 1) -> ℂ) (p : Fin L -> ℂ)
    {delta : ℝ} :
    ∑ k : Fin N,
        arcLength (carrierArc N k) *
          ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 =
      ∑ k ∈ goodCarrierIndices N (polyOfCoeff q).roots delta,
        arcLength (carrierArc N k) *
          ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 +
      ∑ k ∈ badCarrierIndices N (polyOfCoeff q).roots delta,
        arcLength (carrierArc N k) *
          ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 := by
  classical
  change
    ∑ k : Fin N,
        arcLength (carrierArc N k) *
          ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 =
      ∑ k ∈ ((Finset.univ : Finset (Fin N)) \
          badCarrierIndices N (polyOfCoeff q).roots delta),
        arcLength (carrierArc N k) *
          ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 +
      ∑ k ∈ badCarrierIndices N (polyOfCoeff q).roots delta,
        arcLength (carrierArc N k) *
          ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2
  exact
    sum_univ_eq_sdiff_add
      (badCarrierIndices N (polyOfCoeff q).roots delta)
      (fun k : Fin N =>
        arcLength (carrierArc N k) *
          ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2)

private theorem slowBandPoly_l2_le_good_bad_average_defect_variance
    {D N L : Nat} (hN : 0 < N)
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) (p : Fin L -> ℂ)
    {delta : ℝ} (hdelta_pos : 0 < delta)
    (harc : ∀ k ∈ goodCarrierIndices N (polyOfCoeff q).roots delta,
      arcLength (carrierArc N k) <=
        (1 / (128 * ((D + 1 : Nat) : ℝ))) * delta) :
    circleL2Sq (slowBandPoly p) <=
      (1 / (2 * Real.pi)) *
        (8 * Crot * defectSq (lowPoly q) (bandPoly N p) +
          (8 * Crot * (4 * (1 / 64 : ℝ)) ^ 2 + 4 * Crot) *
            (∑ k : Fin N,
              ∫ x in arcSet (carrierArc N k),
                ‖slowBandPoly p x -
                  carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2
                    ∂ μCircle) +
          ((badCarrierIndices N (polyOfCoeff q).roots delta).card : ℝ) *
            (((2 * Real.pi) / (N : ℝ)) *
              ((L : ℝ) * circleL2Sq (bandPoly N p)))) +
        ∑ k : Fin N,
          ∫ x in arcSet (carrierArc N k),
            ‖slowBandPoly p x -
              carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 ∂ μCircle := by
  let G : Finset (Fin N) :=
    goodCarrierIndices N (polyOfCoeff q).roots delta
  let B : Finset (Fin N) :=
    badCarrierIndices N (polyOfCoeff q).roots delta
  let Avg : Fin N -> ℝ := fun k =>
    arcLength (carrierArc N k) *
      ‖carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2
  let V : Fin N -> ℝ := fun k =>
    ∫ x in arcSet (carrierArc N k),
      ‖slowBandPoly p x -
        carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 ∂ μCircle
  let Cvar : ℝ := 8 * Crot * (4 * (1 / 64 : ℝ)) ^ 2 + 4 * Crot
  let BadBd : ℝ :=
    (B.card : ℝ) *
      (((2 * Real.pi) / (N : ℝ)) *
        ((L : ℝ) * circleL2Sq (bandPoly N p)))
  have hdecomp :
      circleL2Sq (slowBandPoly p) =
        (1 / (2 * Real.pi)) * (∑ k : Fin N, Avg k) +
          ∑ k : Fin N, V k := by
    simpa [Avg, V] using
      slowBandPoly_l2_eq_average_mass_plus_variance
        (N := N) (L := L) hN p
  have hsplit :
      ∑ k : Fin N, Avg k = ∑ k ∈ G, Avg k + ∑ k ∈ B, Avg k := by
    simpa [G, B, Avg] using
      sum_carrier_average_mass_eq_good_add_bad
        (D := D) (N := N) (L := L) q p (delta := delta)
  have hgood :
      ∑ k ∈ G, Avg k <=
        8 * Crot * defectSq (lowPoly q) (bandPoly N p) +
          Cvar * (∑ k ∈ G, V k) := by
    simpa [G, Avg, V, Cvar] using
      sum_goodCarrier_average_mass_le_global_defect_plus_variance_of_root_product_canonical
        (D := D) (N := N) (L := L) (q := q) hq p
        hdelta_pos G
        (fun k hk => goodCarrierIndices_not_bad hk)
        (by simpa [G] using harc)
  have hbad :
      ∑ k ∈ B, Avg k <= BadBd := by
    simpa [B, Avg, BadBd] using
      sum_badCarrier_average_mass_le_card_L_l2
        (D := D) (N := N) (L := L) q p (delta := delta)
  have hVsubset :
      ∑ k ∈ G, V k <= ∑ k : Fin N, V k := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ G) ?_
    intro k hk_univ hk_not
    exact MeasureTheory.integral_nonneg fun x => sq_nonneg _
  have hCvar_nonneg : 0 <= Cvar := by
    have hC : 0 <= Crot := le_of_lt Crot_pos
    have hs : 0 <= (4 * (1 / 64 : ℝ)) ^ 2 := sq_nonneg _
    dsimp [Cvar]
    nlinarith
  have hVmul :
      Cvar * (∑ k ∈ G, V k) <= Cvar * (∑ k : Fin N, V k) :=
    mul_le_mul_of_nonneg_left hVsubset hCvar_nonneg
  have hsum_bound :
      ∑ k : Fin N, Avg k <=
        8 * Crot * defectSq (lowPoly q) (bandPoly N p) +
          Cvar * (∑ k : Fin N, V k) + BadBd := by
    rw [hsplit]
    nlinarith
  have hcoef_nonneg : 0 <= (1 / (2 * Real.pi) : ℝ) := by positivity
  have hmul :
      (1 / (2 * Real.pi)) * (∑ k : Fin N, Avg k) <=
        (1 / (2 * Real.pi)) *
          (8 * Crot * defectSq (lowPoly q) (bandPoly N p) +
            Cvar * (∑ k : Fin N, V k) + BadBd) :=
    mul_le_mul_of_nonneg_left hsum_bound hcoef_nonneg
  calc
    circleL2Sq (slowBandPoly p)
        = (1 / (2 * Real.pi)) * (∑ k : Fin N, Avg k) +
          ∑ k : Fin N, V k := hdecomp
    _ <=
      (1 / (2 * Real.pi)) *
          (8 * Crot * defectSq (lowPoly q) (bandPoly N p) +
            Cvar * (∑ k : Fin N, V k) + BadBd) +
        ∑ k : Fin N, V k := by
        nlinarith
    _ =
      (1 / (2 * Real.pi)) *
        (8 * Crot * defectSq (lowPoly q) (bandPoly N p) +
          (8 * Crot * (4 * (1 / 64 : ℝ)) ^ 2 + 4 * Crot) *
            (∑ k : Fin N,
              ∫ x in arcSet (carrierArc N k),
                ‖slowBandPoly p x -
                  carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2
                    ∂ μCircle) +
          ((badCarrierIndices N (polyOfCoeff q).roots delta).card : ℝ) *
            (((2 * Real.pi) / (N : ℝ)) *
              ((L : ℝ) * circleL2Sq (bandPoly N p)))) +
        ∑ k : Fin N,
          ∫ x in arcSet (carrierArc N k),
            ‖slowBandPoly p x -
              carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 ∂ μCircle := by
        simp [Cvar, BadBd, B, V]

private theorem slowBandPoly_l2_le_good_bad_average_defect_poincare
    {D N L : Nat} (hN : 0 < N)
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) (p : Fin L -> ℂ)
    {delta : ℝ} (hdelta_pos : 0 < delta)
    (harc : ∀ k ∈ goodCarrierIndices N (polyOfCoeff q).roots delta,
      arcLength (carrierArc N k) <=
        (1 / (128 * ((D + 1 : Nat) : ℝ))) * delta) :
    circleL2Sq (slowBandPoly p) <=
      (1 / (2 * Real.pi)) *
        (8 * Crot * defectSq (lowPoly q) (bandPoly N p) +
          (8 * Crot * (4 * (1 / 64 : ℝ)) ^ 2 + 4 * Crot) *
            ((4 * Real.pi ^ 2 * ((L : ℝ) - 1) ^ 2 / (N : ℝ) ^ 2) *
              circleL2Sq (slowBandPoly p)) +
          ((badCarrierIndices N (polyOfCoeff q).roots delta).card : ℝ) *
            (((2 * Real.pi) / (N : ℝ)) *
              ((L : ℝ) * circleL2Sq (bandPoly N p)))) +
        (4 * Real.pi ^ 2 * ((L : ℝ) - 1) ^ 2 / (N : ℝ) ^ 2) *
          circleL2Sq (slowBandPoly p) := by
  let V : ℝ :=
    ∑ k : Fin N,
      ∫ x in arcSet (carrierArc N k),
        ‖slowBandPoly p x -
          carrierAverage (N := N) k (slowBandPoly p)‖ ^ 2 ∂ μCircle
  let R : ℝ :=
    (4 * Real.pi ^ 2 * ((L : ℝ) - 1) ^ 2 / (N : ℝ) ^ 2) *
      circleL2Sq (slowBandPoly p)
  let Cvar : ℝ := 8 * Crot * (4 * (1 / 64 : ℝ)) ^ 2 + 4 * Crot
  let BadBd : ℝ :=
    ((badCarrierIndices N (polyOfCoeff q).roots delta).card : ℝ) *
      (((2 * Real.pi) / (N : ℝ)) *
        ((L : ℝ) * circleL2Sq (bandPoly N p)))
  have hbase :
      circleL2Sq (slowBandPoly p) <=
        (1 / (2 * Real.pi)) *
          (8 * Crot * defectSq (lowPoly q) (bandPoly N p) +
            Cvar * V + BadBd) + V := by
    simpa [V, Cvar, BadBd] using
      slowBandPoly_l2_le_good_bad_average_defect_variance
        (D := D) (N := N) (L := L) hN (q := q) hq p
        hdelta_pos harc
  have hN1 : 1 <= N := Nat.succ_le_of_lt hN
  have hV : V <= R := by
    simpa [V, R] using
      sum_carrierAverage_variance_le_global (N := N) (L := L) hN1 p
  have hCvar_nonneg : 0 <= Cvar := by
    have hC : 0 <= Crot := le_of_lt Crot_pos
    have hs : 0 <= (4 * (1 / 64 : ℝ)) ^ 2 := sq_nonneg _
    dsimp [Cvar]
    nlinarith
  have hcoef_nonneg : 0 <= (1 / (2 * Real.pi) : ℝ) := by positivity
  have hinside :
      8 * Crot * defectSq (lowPoly q) (bandPoly N p) +
          Cvar * V + BadBd <=
        8 * Crot * defectSq (lowPoly q) (bandPoly N p) +
          Cvar * R + BadBd := by
    have hmul := mul_le_mul_of_nonneg_left hV hCvar_nonneg
    nlinarith
  have hmainmul :
      (1 / (2 * Real.pi)) *
        (8 * Crot * defectSq (lowPoly q) (bandPoly N p) +
          Cvar * V + BadBd) <=
      (1 / (2 * Real.pi)) *
        (8 * Crot * defectSq (lowPoly q) (bandPoly N p) +
          Cvar * R + BadBd) :=
    mul_le_mul_of_nonneg_left hinside hcoef_nonneg
  calc
    circleL2Sq (slowBandPoly p)
        <= (1 / (2 * Real.pi)) *
          (8 * Crot * defectSq (lowPoly q) (bandPoly N p) +
            Cvar * V + BadBd) + V := hbase
    _ <= (1 / (2 * Real.pi)) *
          (8 * Crot * defectSq (lowPoly q) (bandPoly N p) +
            Cvar * R + BadBd) + R := by
          nlinarith
    _ =
      (1 / (2 * Real.pi)) *
        (8 * Crot * defectSq (lowPoly q) (bandPoly N p) +
          (8 * Crot * (4 * (1 / 64 : ℝ)) ^ 2 + 4 * Crot) *
            ((4 * Real.pi ^ 2 * ((L : ℝ) - 1) ^ 2 / (N : ℝ) ^ 2) *
              circleL2Sq (slowBandPoly p)) +
          ((badCarrierIndices N (polyOfCoeff q).roots delta).card : ℝ) *
            (((2 * Real.pi) / (N : ℝ)) *
              ((L : ℝ) * circleL2Sq (bandPoly N p)))) +
        (4 * Real.pi ^ 2 * ((L : ℝ) - 1) ^ 2 / (N : ℝ) ^ 2) *
          circleL2Sq (slowBandPoly p) := by
          simp [Cvar, R, BadBd]

private theorem slowBandPoly_l2_le_good_bad_defect_variance
    {D N L : Nat} (hN : 0 < N)
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0) (p : Fin L -> ℂ)
    {delta : ℝ} (hdelta_pos : 0 < delta)
    (harc : ∀ k ∈ goodCarrierIndices N (polyOfCoeff q).roots delta,
      arcLength (carrierArc N k) <=
        (1 / (128 * ((D + 1 : Nat) : ℝ))) * delta) :
    circleL2Sq (slowBandPoly p) <=
      (1 / Real.pi) *
        (8 * Crot * defectSq (lowPoly q) (bandPoly N p) +
          8 * Crot *
            (((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) *
              ((2 * Real.pi) / (N : ℝ)) ^ 2) +
          ((badCarrierIndices N (polyOfCoeff q).roots delta).card : ℝ) *
            (((2 * Real.pi) / (N : ℝ)) *
              ((L : ℝ) * circleL2Sq (bandPoly N p)))) +
        2 *
          (((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) *
            ((2 * Real.pi) / (N : ℝ)) ^ 2) := by
  let G : Finset (Fin N) :=
    goodCarrierIndices N (polyOfCoeff q).roots delta
  let B : Finset (Fin N) :=
    badCarrierIndices N (polyOfCoeff q).roots delta
  let Base : Fin N -> ℝ := fun k =>
    arcLength (carrierArc N k) *
      ‖slowBandPoly p (carrierBase k)‖ ^ 2
  let Err : ℝ :=
    ((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) *
      ((2 * Real.pi) / (N : ℝ)) ^ 2
  let BadBd : ℝ :=
    (B.card : ℝ) *
      (((2 * Real.pi) / (N : ℝ)) *
        ((L : ℝ) * circleL2Sq (bandPoly N p)))
  have hsample :
      circleL2Sq (slowBandPoly p) <=
        (1 / Real.pi) * (∑ k : Fin N, Base k) + 2 * Err := by
    simpa [Base, Err] using
      slowBandPoly_l2_le_sampled_base_mass_plus_variance_error
        (N := N) (L := L) hN p
  have hsplit :
      ∑ k : Fin N, Base k =
        ∑ k ∈ G, Base k + ∑ k ∈ B, Base k := by
    simpa [G, B, Base] using
      sum_carrier_base_mass_eq_good_add_bad
        (D := D) (N := N) (L := L) q p (delta := delta)
  have hgood :
      ∑ k ∈ G, Base k <=
        8 * Crot * defectSq (lowPoly q) (bandPoly N p) +
          8 * Crot * Err := by
    simpa [G, Base, Err] using
      sum_goodCarrier_base_mass_le_global_defect_plus_fast_variance_of_root_product_canonical
        (D := D) (N := N) (L := L) hN (q := q) hq p
        hdelta_pos G
        (fun k hk => goodCarrierIndices_not_bad hk)
        (by simpa [G] using harc)
  have hbad :
      ∑ k ∈ B, Base k <= BadBd := by
    simpa [B, Base, BadBd] using
      sum_badCarrier_base_mass_le_card_L_l2
        (D := D) (N := N) (L := L) q p (delta := delta)
  have hsum_bound :
      ∑ k : Fin N, Base k <=
        8 * Crot * defectSq (lowPoly q) (bandPoly N p) +
          8 * Crot * Err + BadBd := by
    rw [hsplit]
    linarith
  have hcoef_nonneg : 0 <= 1 / Real.pi := by positivity
  calc
    circleL2Sq (slowBandPoly p)
        <= (1 / Real.pi) * (∑ k : Fin N, Base k) + 2 * Err :=
      hsample
    _ <=
        (1 / Real.pi) *
            (8 * Crot * defectSq (lowPoly q) (bandPoly N p) +
              8 * Crot * Err + BadBd) +
          2 * Err := by
      have hmul := mul_le_mul_of_nonneg_left hsum_bound hcoef_nonneg
      nlinarith
    _ =
      (1 / Real.pi) *
        (8 * Crot * defectSq (lowPoly q) (bandPoly N p) +
          8 * Crot *
            (((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) *
              ((2 * Real.pi) / (N : ℝ)) ^ 2) +
          ((badCarrierIndices N (polyOfCoeff q).roots delta).card : ℝ) *
            (((2 * Real.pi) / (N : ℝ)) *
              ((L : ℝ) * circleL2Sq (bandPoly N p)))) +
        2 *
          (((L : ℝ) ^ 3 * circleL2Sq (slowBandPoly p)) *
            ((2 * Real.pi) / (N : ℝ)) ^ 2) := by
      simp [Err, BadBd, B]

private theorem circleL2Sq_bandPoly_pos_of_ne_zero
    (N : Nat) {L : Nat} {p : Fin L -> ℂ} (hp : p ≠ 0) :
    0 < circleL2Sq (bandPoly N p) := by
  rw [circleL2Sq_bandPoly]
  classical
  have hex : ∃ m : Fin L, p m ≠ 0 := by
    by_contra hnone
    apply hp
    funext m
    by_contra hm
    exact hnone ⟨m, hm⟩
  rcases hex with ⟨m0, hm0⟩
  exact Finset.sum_pos' (fun m hm => sq_nonneg _) ⟨m0, Finset.mem_univ _, by
    have hnorm_pos : 0 < ‖p m0‖ := norm_pos_iff.mpr hm0
    nlinarith⟩

private theorem circleL2Sq_bandPoly_eq_zero_iff
    (N : Nat) {L : Nat} (p : Fin L -> ℂ) :
    circleL2Sq (bandPoly N p) = 0 ↔ p = 0 := by
  rw [circleL2Sq_bandPoly]
  constructor
  · intro hsum
    funext m
    have hterm_le : ‖p m‖ ^ 2 <= ∑ m : Fin L, ‖p m‖ ^ 2 := by
      exact Finset.single_le_sum
        (fun x hx => (sq_nonneg (‖p x‖) : 0 <= ‖p x‖ ^ 2))
        (Finset.mem_univ m)
    have hterm_zero : ‖p m‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg (‖p m‖)]
    have hnorm_zero : ‖p m‖ = 0 := by
      nlinarith [sq_nonneg (‖p m‖)]
    exact norm_eq_zero.mp hnorm_zero
  · intro hp
    subst p
    simp

private theorem lowPoly_zero_case {D L N : Nat}
    {q : Fin (D + 1) -> ℂ} (p : Fin L -> ℂ)
    (hzero : q = 0) :
    defectSq (lowPoly q) (bandPoly N p) =
      circleL2Sq (bandPoly N p) := by
  subst q
  unfold defectSq circleL2Sq lowPoly
  congr
  funext x
  simp

private theorem lowPoly_zero_degree_eq_const
    (q : Fin (0 + 1) -> ℂ) :
    lowPoly q = fun _ => q 0 := by
  ext x
  simp [lowPoly, circleChar]

private theorem zero_degree_coeff_ne_zero
    {q : Fin (0 + 1) -> ℂ} (hq : q ≠ 0) :
    q 0 ≠ 0 := by
  intro hc
  apply hq
  funext n
  fin_cases n
  simpa using hc

private theorem lowPoly_eq_const_of_tail_zero {D : Nat}
    (q : Fin (D + 1) -> ℂ)
    (htail : ∀ n : Fin (D + 1), n.1 ≠ 0 -> q n = 0) :
    lowPoly q = fun _ => q (0 : Fin (D + 1)) := by
  ext x
  unfold lowPoly
  rw [Finset.sum_eq_single (0 : Fin (D + 1))]
  · simp [circleChar]
  · intro b hb hbne
    have hbval : b.1 ≠ 0 := by
      intro hval
      exact hbne (Fin.ext hval)
    simp [htail b hbval]
  · intro hnot
    simp at hnot

private theorem constant_coeff_ne_zero_of_tail_zero {D : Nat}
    {q : Fin (D + 1) -> ℂ} (hq : q ≠ 0)
    (htail : ∀ n : Fin (D + 1), n.1 ≠ 0 -> q n = 0) :
    q (0 : Fin (D + 1)) ≠ 0 := by
  intro h0
  apply hq
  funext n
  by_cases hn : n.1 = 0
  · have hn0 : n = 0 := Fin.ext hn
    simpa [hn0] using h0
  · exact htail n hn

private theorem bandPoly_const_mul
    (N : Nat) {L : Nat} (c : ℂ) (p : Fin L -> ℂ) :
    bandPoly N (fun m => c * p m) = fun x => c * bandPoly N p x := by
  ext x
  simp [bandPoly, Finset.mul_sum, mul_assoc]

private theorem circleL2Sq_const_mul
    (c : ℂ) (P : Circle -> ℂ) :
    circleL2Sq (fun x => c * P x) = ‖c‖ ^ 2 * circleL2Sq P := by
  unfold circleL2Sq
  calc
    ∫ x : Circle, ‖c * P x‖ ^ 2 ∂AddCircle.haarAddCircle =
        ∫ x : Circle, ‖c‖ ^ 2 * ‖P x‖ ^ 2 ∂AddCircle.haarAddCircle := by
      congr
      ext x
      rw [norm_mul, mul_pow]
    _ = ‖c‖ ^ 2 * ∫ x : Circle, ‖P x‖ ^ 2 ∂AddCircle.haarAddCircle := by
      rw [MeasureTheory.integral_const_mul]

private theorem defectSq_const_mul_eq_rho
    (c : ℂ) (P : Circle -> ℂ) :
    defectSq (fun _ => c) (fun x => c * P x) =
      ‖c‖ ^ 2 *
        ∫ x : Circle, (FockSPR.rho (P x)) ^ 2 ∂AddCircle.haarAddCircle := by
  unfold defectSq FockSPR.rho
  calc
    ∫ x : Circle, (‖c + c * P x‖ - ‖c‖) ^ 2 ∂AddCircle.haarAddCircle =
        ∫ x : Circle, (‖c‖ * (‖(1 : ℂ) + P x‖ - 1)) ^ 2 ∂AddCircle.haarAddCircle := by
      congr
      ext x
      have hnorm :
          ‖c + c * P x‖ = ‖c‖ * ‖(1 : ℂ) + P x‖ := by
        have hmul : c + c * P x = c * ((1 : ℂ) + P x) := by
          ring
        rw [hmul, norm_mul]
      rw [hnorm]
      ring
    _ =
        ∫ x : Circle, ‖c‖ ^ 2 * |‖(1 : ℂ) + P x‖ - 1| ^ 2
          ∂AddCircle.haarAddCircle := by
      congr
      ext x
      rw [mul_pow, sq_abs]
    _ =
        ‖c‖ ^ 2 *
          ∫ x : Circle, |‖(1 : ℂ) + P x‖ - 1| ^ 2 ∂AddCircle.haarAddCircle := by
      rw [MeasureTheory.integral_const_mul]

private theorem high_freq_band_estimate_wip
    {N L : Nat} (hN : 1 <= N) (hL : 1 <= L)
    (hNL : 1343 * L ^ 2 <= N ^ 2)
    (b : Fin L -> ℂ) :
    circleL2Sq (bandPoly N b) <=
      32 *
        ∫ x : Circle, (FockSPR.rho (bandPoly N b x)) ^ 2 ∂AddCircle.haarAddCircle := by
  have h :=
    FockSPR.high_freq_band_estimate
      (N := N) (L := L) hN hL hNL b (bandPoly N b)
      (by
        ext t
        simp only [bandPoly, circleChar_eq_fourier_nat]
        refine Finset.sum_congr rfl ?_
        intro m hm
        rw [Nat.cast_add]
        rfl)
  simp only [circleL2Sq, FockSPR.circleNormSq, FockSPR.T] at h ⊢
  exact h

private theorem finite_base_circle_estimate_degree_zero
    {L N : Nat} (hL : 1 <= L)
    (hsep : circleGap 0 * L <= N)
    (q : Fin (0 + 1) -> ℂ) (p : Fin L -> ℂ) (hq : q ≠ 0) :
    circleL2Sq (bandPoly N p) <=
      circleConst 0 * defectSq (lowPoly q) (bandPoly N p) := by
  let c : ℂ := q 0
  have hc : c ≠ 0 := by
    simpa [c] using zero_degree_coeff_ne_zero hq
  let b : Fin L -> ℂ := fun m => c⁻¹ * p m
  have hsep37 : 37 * L <= N := by
    have hmul : 37 * L <= circleGap 0 * L :=
      Nat.mul_le_mul_right L (circleGap_ge_37 0)
    exact hmul.trans hsep
  have hN : 1 <= N := by
    nlinarith
  have hNL : 1343 * L ^ 2 <= N ^ 2 := by
    nlinarith
  have hP : bandPoly N p = fun x => c * bandPoly N b x := by
    ext x
    simp [b, bandPoly, Finset.mul_sum, mul_assoc, hc]
  set I : ℝ :=
    ∫ x : Circle, (FockSPR.rho (bandPoly N b x)) ^ 2 ∂AddCircle.haarAddCircle
  have hhigh : circleL2Sq (bandPoly N b) <= 32 * I := by
    simpa [I] using high_freq_band_estimate_wip hN hL hNL b
  have hleft :
      circleL2Sq (bandPoly N p) = ‖c‖ ^ 2 * circleL2Sq (bandPoly N b) := by
    rw [hP]
    exact circleL2Sq_const_mul c (bandPoly N b)
  have hdef :
      defectSq (lowPoly q) (bandPoly N p) = ‖c‖ ^ 2 * I := by
    rw [lowPoly_zero_degree_eq_const q, hP]
    simpa [I, c] using defectSq_const_mul_eq_rho c (bandPoly N b)
  have hscaled : circleL2Sq (bandPoly N p) <= 32 * defectSq (lowPoly q) (bandPoly N p) := by
    calc
      circleL2Sq (bandPoly N p) = ‖c‖ ^ 2 * circleL2Sq (bandPoly N b) := hleft
      _ <= ‖c‖ ^ 2 * (32 * I) :=
        mul_le_mul_of_nonneg_left hhigh (sq_nonneg ‖c‖)
      _ = 32 * defectSq (lowPoly q) (bandPoly N p) := by
        rw [hdef]
        ring
  have hconst : (32 : ℝ) <= circleConst 0 :=
    thirty_two_le_circleConst 0
  exact hscaled.trans
    (mul_le_mul_of_nonneg_right hconst (defectSq_nonneg (lowPoly q) (bandPoly N p)))

private theorem finite_base_circle_estimate_constant_low
    {D L N : Nat} (hL : 1 <= L)
    (hsep : circleGap D * L <= N)
    (q : Fin (D + 1) -> ℂ) (p : Fin L -> ℂ) (hq : q ≠ 0)
    (htail : ∀ n : Fin (D + 1), n.1 ≠ 0 -> q n = 0) :
    circleL2Sq (bandPoly N p) <=
      circleConst D * defectSq (lowPoly q) (bandPoly N p) := by
  let c : ℂ := q (0 : Fin (D + 1))
  have hc : c ≠ 0 := by
    simpa [c] using constant_coeff_ne_zero_of_tail_zero hq htail
  let b : Fin L -> ℂ := fun m => c⁻¹ * p m
  have hN : 1 <= N := by
    have hgap : 1 <= circleGap D := circleGap_pos D
    nlinarith
  have hsep37 : 37 * L <= N := by
    have hmul : 37 * L <= circleGap D * L :=
      Nat.mul_le_mul_right L (circleGap_ge_37 D)
    exact hmul.trans hsep
  have hNL : 1343 * L ^ 2 <= N ^ 2 := by
    nlinarith
  have hP : bandPoly N p = fun x => c * bandPoly N b x := by
    ext x
    simp [b, bandPoly, Finset.mul_sum, mul_assoc, hc]
  set I : ℝ :=
    ∫ x : Circle, (FockSPR.rho (bandPoly N b x)) ^ 2 ∂AddCircle.haarAddCircle
  have hhigh : circleL2Sq (bandPoly N b) <= 32 * I := by
    simpa [I] using high_freq_band_estimate_wip hN hL hNL b
  have hleft :
      circleL2Sq (bandPoly N p) = ‖c‖ ^ 2 * circleL2Sq (bandPoly N b) := by
    rw [hP]
    exact circleL2Sq_const_mul c (bandPoly N b)
  have hdef :
      defectSq (lowPoly q) (bandPoly N p) = ‖c‖ ^ 2 * I := by
    rw [lowPoly_eq_const_of_tail_zero q htail, hP]
    simpa [I, c] using defectSq_const_mul_eq_rho c (bandPoly N b)
  have hscaled : circleL2Sq (bandPoly N p) <=
      32 * defectSq (lowPoly q) (bandPoly N p) := by
    calc
      circleL2Sq (bandPoly N p) = ‖c‖ ^ 2 * circleL2Sq (bandPoly N b) := hleft
      _ <= ‖c‖ ^ 2 * (32 * I) :=
        mul_le_mul_of_nonneg_left hhigh (sq_nonneg ‖c‖)
      _ = 32 * defectSq (lowPoly q) (bandPoly N p) := by
        rw [hdef]
        ring
  have hconst : (32 : ℝ) <= circleConst D := by
    exact thirty_two_le_circleConst D
  exact hscaled.trans
    (mul_le_mul_of_nonneg_right hconst (defectSq_nonneg (lowPoly q) (bandPoly N p)))

private theorem badCarrier_term_le_half_l2
    {D N L B : Nat} {q : Fin (D + 1) -> ℂ} (p : Fin L -> ℂ)
    {delta : ℝ}
    (hN : 0 < N)
    (hcard :
      (badCarrierIndices N (polyOfCoeff q).roots delta).card <=
        circleBadConst D * B)
    (hsep : 2 * circleBadConst D * B * L <= N) :
    (1 / (2 * Real.pi)) *
        (((badCarrierIndices N (polyOfCoeff q).roots delta).card : ℝ) *
          (((2 * Real.pi) / (N : ℝ)) *
            ((L : ℝ) * circleL2Sq (bandPoly N p)))) <=
      (1 / 2) * circleL2Sq (bandPoly N p) := by
  let C : ℝ := ((badCarrierIndices N (polyOfCoeff q).roots delta).card : ℝ)
  let A : ℝ := ((circleBadConst D * B : Nat) : ℝ)
  let M : ℝ := circleL2Sq (bandPoly N p)
  have hC_le_A : C <= A := by
    dsimp [C, A]
    exact_mod_cast hcard
  have hsep_real' :
      ((2 * circleBadConst D * B * L : Nat) : ℝ) <= (N : ℝ) := by
    exact_mod_cast hsep
  have hsep_real : 2 * A * (L : ℝ) <= (N : ℝ) := by
    simpa [A, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using
      hsep_real'
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast hN
  have hM_nonneg : 0 <= M := by
    dsimp [M]
    exact circleL2Sq_nonneg (bandPoly N p)
  have hratio : C * (L : ℝ) / (N : ℝ) <= (1 / 2 : ℝ) := by
    have hL_nonneg : 0 <= (L : ℝ) := by exact_mod_cast Nat.zero_le L
    have hCL : C * (L : ℝ) <= A * (L : ℝ) :=
      mul_le_mul_of_nonneg_right hC_le_A hL_nonneg
    have htwo : 2 * (C * (L : ℝ)) <= (N : ℝ) := by
      nlinarith
    rw [div_le_iff₀ hNpos]
    nlinarith
  have hrearrange :
      (1 / (2 * Real.pi)) *
          (C * (((2 * Real.pi) / (N : ℝ)) * ((L : ℝ) * M))) =
        (C * (L : ℝ) / (N : ℝ)) * M := by
    field_simp [Real.pi_ne_zero, hNpos.ne']
  calc
    (1 / (2 * Real.pi)) *
        (((badCarrierIndices N (polyOfCoeff q).roots delta).card : ℝ) *
          (((2 * Real.pi) / (N : ℝ)) *
            ((L : ℝ) * circleL2Sq (bandPoly N p))))
        = (C * (L : ℝ) / (N : ℝ)) * M := by
          simpa [C, M] using hrearrange
    _ <= (1 / 2) * M :=
      mul_le_mul_of_nonneg_right hratio hM_nonneg

private theorem circle_variance_ratio_le_one_div_520
    {D L N : Nat} (hD : 0 < D) (hL : 1 <= L)
    (hsep : 2 * circleBadConst D * circleGoodBudget D * L <= N) :
    4 * Real.pi ^ 2 * ((L : ℝ) - 1) ^ 2 / (N : ℝ) ^ 2 <=
      (1 / 520 : ℝ) := by
  have hA82_nat : 82 <= circleBadConst D := by
    have hD_one : 1 <= D := Nat.succ_le_iff.mpr hD
    have h82D : 82 <= 82 * D := by omega
    have hinner : 82 * D <= max (82 * D) (2 ^ D - 1) :=
      le_max_left (82 * D) (2 ^ D - 1)
    have hbad : 82 * D <= circleBadConst D := by
      unfold circleBadConst
      exact hinner.trans (le_max_right 1 (max (82 * D) (2 ^ D - 1)))
    exact h82D.trans hbad
  let A : ℝ := (circleBadConst D : ℝ)
  let K : ℝ := 128 * (82 : ℝ) ^ 2
  have hA_ge : (82 : ℝ) <= A := by
    dsimp [A]
    exact_mod_cast hA82_nat
  have hsep_real :
      2 * (circleBadConst D : ℝ) * (circleGoodBudget D : ℝ) *
          (L : ℝ) <= (N : ℝ) := by
    exact_mod_cast hsep
  have hNlargeA : 128 * A ^ 2 * (L : ℝ) <= (N : ℝ) := by
    have htmp : 2 * A * (64 * A) * (L : ℝ) <= (N : ℝ) := by
      simpa [A, circleGoodBudget, mul_assoc, mul_left_comm, mul_comm] using
        hsep_real
    have hrewrite : 128 * A ^ 2 * (L : ℝ) =
        2 * A * (64 * A) * (L : ℝ) := by
      ring
    rw [hrewrite]
    exact htmp
  have hKpos : 0 < K := by
    norm_num [K]
  have hLpos : (0 : ℝ) < (L : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL)
  have hK_le_A : K * (L : ℝ) <= 128 * A ^ 2 * (L : ℝ) := by
    have hsq : ((82 : ℝ) ^ 2) <= A ^ 2 := by
      nlinarith [hA_ge]
    have hcoef : 128 * ((82 : ℝ) ^ 2) <= 128 * A ^ 2 := by
      nlinarith
    have hL_nonneg : 0 <= (L : ℝ) := le_of_lt hLpos
    exact mul_le_mul_of_nonneg_right (by simpa [K] using hcoef) hL_nonneg
  have hNlarge : K * (L : ℝ) <= (N : ℝ) :=
    hK_le_A.trans hNlargeA
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    nlinarith
  have hLm1sq : ((L : ℝ) - 1) ^ 2 <= (L : ℝ) ^ 2 := by
    have hLm1_nonneg : 0 <= (L : ℝ) - 1 := by
      exact sub_nonneg.mpr (by exact_mod_cast hL)
    nlinarith [sq_nonneg (1 : ℝ)]
  have hratio :
      (L : ℝ) ^ 2 / (N : ℝ) ^ 2 <= (1 : ℝ) / K ^ 2 := by
    field_simp [sq_pos_of_pos hNpos, sq_pos_of_pos hKpos]
    nlinarith [hNlarge, sq_nonneg ((N : ℝ) - K * (L : ℝ))]
  have hsmall :
      ((L : ℝ) - 1) ^ 2 / (N : ℝ) ^ 2 <=
        (L : ℝ) ^ 2 / (N : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right hLm1sq (sq_nonneg (N : ℝ))
  have hpi_sq : Real.pi ^ 2 <= (16 : ℝ) := by
    nlinarith [le_of_lt Real.pi_pos, le_of_lt Real.pi_lt_four]
  have hcoef : 4 * Real.pi ^ 2 <= (64 : ℝ) := by
    nlinarith
  have hratio_nonneg :
      0 <= (L : ℝ) ^ 2 / (N : ℝ) ^ 2 :=
    div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hmul₁ :
      4 * Real.pi ^ 2 *
          (((L : ℝ) - 1) ^ 2 / (N : ℝ) ^ 2) <=
        4 * Real.pi ^ 2 * ((L : ℝ) ^ 2 / (N : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hsmall (by positivity)
  have hmul₂ :
      4 * Real.pi ^ 2 * ((L : ℝ) ^ 2 / (N : ℝ) ^ 2) <=
        64 * ((1 : ℝ) / K ^ 2) :=
    mul_le_mul hcoef hratio hratio_nonneg (by norm_num)
  have hnum : 64 * ((1 : ℝ) / K ^ 2) <= (1 / 520 : ℝ) := by
    norm_num [K]
  calc
    4 * Real.pi ^ 2 * ((L : ℝ) - 1) ^ 2 / (N : ℝ) ^ 2
        = 4 * Real.pi ^ 2 *
            (((L : ℝ) - 1) ^ 2 / (N : ℝ) ^ 2) := by
          ring
    _ <= 4 * Real.pi ^ 2 * ((L : ℝ) ^ 2 / (N : ℝ) ^ 2) := hmul₁
    _ <= 64 * ((1 : ℝ) / K ^ 2) := hmul₂
    _ <= (1 / 520 : ℝ) := hnum

private theorem circle_variance_error_le_quarter_l2
    {R M : ℝ} (hR_le : R <= (1 / 520 : ℝ)) (hM : 0 <= M) :
    (1 / (2 * Real.pi)) *
        ((8 * Crot * (4 * (1 / 64 : ℝ)) ^ 2 + 4 * Crot) * (R * M)) +
      R * M <= (1 / 4) * M := by
  have hcoef :
      (1 / (2 * Real.pi)) *
          (8 * Crot * (4 * (1 / 64 : ℝ)) ^ 2 + 4 * Crot) + 1 =
        130 := by
    unfold Crot
    field_simp [Real.pi_ne_zero]
    ring
  have hrearrange :
      (1 / (2 * Real.pi)) *
          ((8 * Crot * (4 * (1 / 64 : ℝ)) ^ 2 + 4 * Crot) * (R * M)) +
        R * M =
      (((1 / (2 * Real.pi)) *
          (8 * Crot * (4 * (1 / 64 : ℝ)) ^ 2 + 4 * Crot) + 1) * R) * M := by
    ring
  have hbound : 130 * R <= 130 * (1 / 520 : ℝ) :=
    mul_le_mul_of_nonneg_left hR_le (by norm_num)
  calc
    (1 / (2 * Real.pi)) *
        ((8 * Crot * (4 * (1 / 64 : ℝ)) ^ 2 + 4 * Crot) * (R * M)) +
      R * M
        = (130 * R) * M := by
          rw [hrearrange, hcoef]
    _ <= (130 * (1 / 520 : ℝ)) * M :=
      mul_le_mul_of_nonneg_right hbound hM
    _ = (1 / 4) * M := by
      norm_num

theorem finite_base_circle_estimate
    (D : Nat) :
    ∀ {L N : Nat}, 1 <= L ->
      circleGap D * L <= N ->
      ∀ (q : Fin (D + 1) -> ℂ) (p : Fin L -> ℂ),
        circleL2Sq (bandPoly N p) <=
          circleConst D * defectSq (lowPoly q) (bandPoly N p) := by
  /-
  Scaffolding contract:
  the circle theorem remains completely finite-Fourier. The constants
  `circleGap D` and `circleConst D` are the executable witnesses for the
  scaffolding note's existential `A_D` and `C_D`.
  -/
  intro L N hL hsep q p
  by_cases hzero : q = 0
  · rw [lowPoly_zero_case (N := N) (p := p) hzero]
    have hmass_nonneg : 0 <= circleL2Sq (bandPoly N p) :=
      circleL2Sq_nonneg (bandPoly N p)
    have hconst_ge_one : 1 <= circleConst D := by
      exact circleConst_ge_one D
    nlinarith
  · have hpoly_ne : polyOfCoeff q ≠ 0 :=
      polyOfCoeff_ne_zero_of_ne_zero hzero
    have hlead_ne : (polyOfCoeff q).leadingCoeff ≠ 0 :=
      leadingCoeff_polyOfCoeff_ne_zero_of_ne_zero hzero
    have hlead_norm_pos : 0 < ‖(polyOfCoeff q).leadingCoeff‖ :=
      norm_leadingCoeff_polyOfCoeff_pos_of_ne_zero hzero
    by_cases hD : D = 0
    · subst D
      exact finite_base_circle_estimate_degree_zero hL hsep q p hzero
    by_cases htail : ∀ n : Fin (D + 1), n.1 ≠ 0 -> q n = 0
    · exact finite_base_circle_estimate_constant_low hL hsep q p hzero htail
    have hD_pos : 0 < D := Nat.pos_of_ne_zero hD
    have hCrot_le_const : Crot <= circleConst D :=
      Crot_le_circleConst_of_pos hD_pos
    have hnonconst_coeff :
        ∃ n : Fin (D + 1), n.1 ≠ 0 ∧ q n ≠ 0 := by
      classical
      by_contra hnone
      apply htail
      intro n hn
      by_contra hnq
      exact hnone ⟨n, hn, hnq⟩
    have hpoly_natDegree_pos : 0 < (polyOfCoeff q).natDegree :=
      natDegree_polyOfCoeff_pos_of_nonconst hnonconst_coeff
    have hroots_card_pos : 0 < (polyOfCoeff q).roots.card := by
      simpa [roots_card_polyOfCoeff_eq_natDegree q] using hpoly_natDegree_pos
    have hroot_exists : ∃ ζ : ℂ, ζ ∈ (polyOfCoeff q).roots :=
      exists_mem_roots_polyOfCoeff_of_nonconst hnonconst_coeff
    have hroots_le : (polyOfCoeff q).roots.card <= D :=
      roots_card_polyOfCoeff_le q
    have hfactor :
        ∀ x : Circle,
          lowPoly q x =
            (polyOfCoeff q).leadingCoeff *
              ((polyOfCoeff q).roots.map fun ζ => zeta x - ζ).prod :=
      lowPoly_eq_leadingCoeff_mul_roots q
    by_cases hpzero : p = 0
    · subst p
      simp [bandPoly, circleL2Sq, defectSq]
    · have hmass_pos : 0 < circleL2Sq (bandPoly N p) :=
        circleL2Sq_bandPoly_pos_of_ne_zero N hpzero
      have hN : 1 <= N := by
        have hgap : 1 <= circleGap D := circleGap_pos D
        nlinarith
      have hsep37 : 37 * L <= N := by
        have hmul : 37 * L <= circleGap D * L :=
          Nat.mul_le_mul_right L (circleGap_ge_37 D)
        exact hmul.trans hsep
      have hNL : 1343 * L ^ 2 <= N ^ 2 := by
        nlinarith
      have hbad_budget_sep :
          2 * circleBadConst D * circleGoodBudget D * L <= N := by
        have hmul :
            (2 * circleBadConst D * circleGoodBudget D) * L <=
              circleGap D * L :=
          Nat.mul_le_mul_right L (circleGap_ge_bad_budget D)
        exact hmul.trans hsep
      let B : Nat := circleGoodBudget D
      let delta : ℝ := 16 * (B : ℝ) / (N : ℝ)
      have hB_pos : 1 <= B := by
        simpa [B] using circleGoodBudget_pos D
      have hN_pos_nat : 0 < N := Nat.succ_le_iff.mp hN
      have hN_pos_real : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos_nat
      have hB_pos_real : (0 : ℝ) < (B : ℝ) := by
        have hB_nat : 0 < B := lt_of_lt_of_le Nat.zero_lt_one hB_pos
        exact_mod_cast hB_nat
      have hdelta_pos : 0 < delta := by
        dsimp [delta]
        exact div_pos (mul_pos (by norm_num) hB_pos_real) hN_pos_real
      have hbad_card :
          (badCarrierIndices N (polyOfCoeff q).roots delta).card <=
            circleBadConst D * B := by
        exact badCarrierIndices_card_le_of_delta_eq
          (D := D) (N := N) (B := B)
          (roots := (polyOfCoeff q).roots) (delta := delta)
          hroots_le hN_pos_nat hB_pos rfl
      have harc :
          ∀ k ∈ goodCarrierIndices N (polyOfCoeff q).roots delta,
            arcLength (carrierArc N k) <=
              (1 / (128 * ((D + 1 : Nat) : ℝ))) * delta := by
        intro k _hk
        simpa [delta, B] using
          carrierArc_length_le_canonical_delta (D := D) hD_pos k
      let M : ℝ := circleL2Sq (bandPoly N p)
      let Def : ℝ := defectSq (lowPoly q) (bandPoly N p)
      let R : ℝ :=
        4 * Real.pi ^ 2 * ((L : ℝ) - 1) ^ 2 / (N : ℝ) ^ 2
      let Cvar : ℝ := 8 * Crot * (4 * (1 / 64 : ℝ)) ^ 2 + 4 * Crot
      let DefTerm : ℝ := (1 / (2 * Real.pi)) * (8 * Crot * Def)
      let VarTerm : ℝ := (1 / (2 * Real.pi)) * (Cvar * (R * M)) + R * M
      let BadTerm : ℝ :=
        (1 / (2 * Real.pi)) *
          (((badCarrierIndices N (polyOfCoeff q).roots delta).card : ℝ) *
            (((2 * Real.pi) / (N : ℝ)) * ((L : ℝ) * M)))
      have hslow_eq : circleL2Sq (slowBandPoly p) = M := by
        dsimp [M]
        rw [circleL2Sq_bandPoly, circleL2Sq_slowBandPoly]
      have hraw :
          M <=
            (1 / (2 * Real.pi)) *
              (8 * Crot * Def + Cvar * (R * M) +
                ((badCarrierIndices N (polyOfCoeff q).roots delta).card : ℝ) *
                  (((2 * Real.pi) / (N : ℝ)) * ((L : ℝ) * M))) +
              R * M := by
        have h :=
          slowBandPoly_l2_le_good_bad_average_defect_poincare
            (D := D) (N := N) (L := L) hN_pos_nat
            (q := q) hzero p hdelta_pos harc
        simpa [M, Def, R, Cvar, hslow_eq] using h
      have hbase : M <= DefTerm + VarTerm + BadTerm := by
        calc
          M <=
            (1 / (2 * Real.pi)) *
              (8 * Crot * Def + Cvar * (R * M) +
                ((badCarrierIndices N (polyOfCoeff q).roots delta).card : ℝ) *
                  (((2 * Real.pi) / (N : ℝ)) * ((L : ℝ) * M))) +
              R * M := hraw
          _ = DefTerm + VarTerm + BadTerm := by
            simp [DefTerm, VarTerm, BadTerm]
            ring
      have hDefTerm : DefTerm = 256 * Def := by
        dsimp [DefTerm]
        unfold Crot
        field_simp [Real.pi_ne_zero]
        ring
      have hM_nonneg : 0 <= M := by
        dsimp [M]
        exact circleL2Sq_nonneg (bandPoly N p)
      have hR_le : R <= (1 / 520 : ℝ) := by
        simpa [R] using
          circle_variance_ratio_le_one_div_520
            (D := D) (L := L) (N := N) hD_pos hL hbad_budget_sep
      have hVarTerm : VarTerm <= (1 / 4) * M := by
        simpa [VarTerm, Cvar] using
          circle_variance_error_le_quarter_l2
            (R := R) (M := M) hR_le hM_nonneg
      have hbad_budget_sep_B : 2 * circleBadConst D * B * L <= N := by
        simpa [B] using hbad_budget_sep
      have hBadTerm : BadTerm <= (1 / 2) * M := by
        simpa [BadTerm, M] using
          badCarrier_term_le_half_l2
            (D := D) (N := N) (L := L) (B := B)
            (q := q) (delta := delta) p hN_pos_nat hbad_card
            hbad_budget_sep_B
      have hmain : M <= 256 * Def + (3 / 4) * M := by
        nlinarith
      have hM_le : M <= 1024 * Def := by
        nlinarith
      have hconst : (1024 : ℝ) <= circleConst D :=
        one_thousand_twenty_four_le_circleConst D
      have hDef_nonneg : 0 <= Def := by
        dsimp [Def]
        exact defectSq_nonneg (lowPoly q) (bandPoly N p)
      calc
        circleL2Sq (bandPoly N p) = M := rfl
        _ <= 1024 * Def := hM_le
        _ <= circleConst D * Def :=
          mul_le_mul_of_nonneg_right hconst hDef_nonneg
        _ = circleConst D * defectSq (lowPoly q) (bandPoly N p) := rfl

theorem finite_base_circle_estimate_exists (D : Nat) :
    ∃ A : Nat, 1 <= A ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ {L N : Nat}, 1 <= L ->
          A * L <= N ->
          ∀ (q : Fin (D + 1) -> ℂ) (p : Fin L -> ℂ),
            circleL2Sq (bandPoly N p) <=
              C * defectSq (lowPoly q) (bandPoly N p) := by
  refine ⟨circleGap D, circleGap_pos D, circleConst D, circleConst_pos D, ?_⟩
  intro L N hL hsep q p
  exact finite_base_circle_estimate D hL hsep q p

end DimdPolyLEAN
