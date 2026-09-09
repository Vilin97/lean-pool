/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceScaleActual
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Scale
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketScaleActivation
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.GCD

/-! Numerical guard consequences for the literal scale sequences. -/

@[expose] public section


noncomputable section


namespace EulerPacketSourceScaleGuards

open Real Filter EulerScale EulerPacketScaleActivation
  EulerPacketSourceScales EulerPacketSourceTime EulerPacketSourceScaleChoice
  EulerPacketSourceScaleSequence EulerPacketSourceScaleActual

open scoped Topology

theorem actualTimeRatio_le (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (hX : 0 < X)
    (hbase : X ^ 1000 ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 7)) (n : ℕ) :
    timeWidth J X (n+1)/timeWidth J X n ≤ sourceTimeRatio J (scaleSequence J X) n := by
  apply (div_le_iff₀ (timeWidth_pos J hJ hX n)).mpr
  rw [timeWidth_succ_eq, source_time_ratio_identity]
  apply mul_le_mul_of_nonneg_left (sourceTimeWidth_le J hJ X hX hbase n)
  unfold sourceTimeRatio
  positivity

theorem actualExtraTime_le (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (hX : 0 < X)
    (hbase : X ^ 1000 ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 7)) (n : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    2*sqrt (a*previousShear J X n)*timeWidth J X (n+1) ≤
      2*sqrt (a*exp (scaleSequence J X n/((J-1+n:ℕ):ℝ)^7)) *
        sourceNextTimeWidth J (scaleSequence J X) n := by
  have hh := sqrt_le_sqrt (mul_le_mul_of_nonneg_left (previousShear_le_normal J hJ X hbase n) ha)
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 2))
    (timeWidth_pos J hJ hX (n+1)).le
  simpa only [timeWidth_succ_eq] using hm

theorem actualParentRatio_le (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (hX : 0 < X)
    (hbase : X ^ 1000 ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 7)) (n : ℕ) :
    previousShear J X n^2/shear J X n ≤ parentSquareRatio J (scaleSequence J X) n := by
  have hh := pow_le_pow_left₀ (previousShear_pos J hX n).le (previousShear_le_normal J hJ X hbase
      n) 2
  have he : exp (scaleSequence J X n/((J-1+n:ℕ):ℝ)^7)^2 =
      exp (2*scaleSequence J X n/((J-1+n:ℕ):ℝ)^7) := by
    rw [pow_two, ← exp_add]
    congr 1
    ring
  rw [he] at hh
  exact div_le_div_of_nonneg_right hh (exp_pos _).le

theorem actualGoodCost_le (J : ℕ) (hJ : 1 ≤ J) (X : ℝ)
    (hbase : X ^ 1000 ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 7)) (n : ℕ) :
    spike J X n*shear J X n*previousShear J X n ≤ goodCost J (scaleSequence J X) n := by
  exact mul_le_mul_of_nonneg_left (previousShear_le_normal J hJ X hbase n)
    (mul_nonneg (exp_pos _).le (exp_pos _).le)

/-- Actual extra time, given by `2*sqrt (a*previousShear J X n)*timeWidth J X (n+1)`. -/
def actualExtraTime (J : ℕ) (X a : ℝ) (n : ℕ) : ℝ :=
  2*sqrt (a*previousShear J X n)*timeWidth J X (n+1)

theorem actualExtraTime_small (J D : ℕ) (hJ : 3 ≤ J) (C c X δ : ℝ)
    (hC : 1 ≤ C) (hX : 8 ≤ X) (hb : ActualBounds J D C c X δ)
    (n : ℕ) (a : ℝ) (ha : 0 ≤ a) (ha₂ : a ≤ 2) :
    actualExtraTime J X a n * sourceTheta J C (scaleSequence J X) n^60 ≤ δ := by
  have hx1 := quadratic_growth_one_le J (by
      omega) (scaleSequence J X) (by change 1 ≤ X; linarith only [hX])
    (scaleSequence_succ J X)
  have hθ : 0 ≤ sourceTheta J C (scaleSequence J X) n :=
    le_trans zero_le_one (sourceTheta_bounds (by omega : 1 ≤ J) hC hx1 n).1
  have hfirst := mul_le_mul_of_nonneg_right
    (actualExtraTime_le J (by omega) X (by linarith only [hX]) hb.initial_shear n a ha)
    (pow_nonneg hθ 60)
  exact hfirst.trans ((hb.normal.extraTime (fun _ => a) (fun _ => ha) (fun _ => ha₂)).term_le n)

theorem actualWidths_contract (J D : ℕ) (hJ : 3 ≤ J) (C c X δ : ℝ)
    (hX : 8 ≤ X) (hb : ActualBounds J D C c X δ) (hδ : δ ≤ 1 / 2) (n : ℕ) :
    timeWidth J X (n+1) ≤ timeWidth J X n/2 := by
  have hh := (actualTimeRatio_le J (by omega) X (by linarith only [hX]) hb.initial_shear n).trans
    ((hb.normal.width.term_le n).trans hδ)
  have hmul := (div_le_iff₀ (timeWidth_pos J (by omega) (by linarith only [hX]) n)).mp hh
  nlinarith only [hmul]

theorem coefficient_small (J D : ℕ) (hJ : 3 ≤ J) (C c X δ : ℝ)
    (hC : 1 ≤ C) (hX : 8 ≤ X) (hb : ActualBounds J D C c X δ)
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ha₂ : ∀ n, a n ≤ 2)
    (A : ℕ) (hA : A ≤ 60) (n : ℕ) :
    geometryError J D C c X a n * sourceTheta J C (scaleSequence J X) n^A ≤ δ := by
  have hx1 := quadratic_growth_one_le J (by
      omega) (scaleSequence J X) (by change 1 ≤ X; linarith only [hX])
    (scaleSequence_succ J X)
  have hθ := (sourceTheta_bounds (by omega : 1 ≤ J) hC hx1 n).1
  have hh := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hθ hA)
    (geometryError_nonneg J D C c X a n (le_trans zero_le_one hC) (by linarith only [hX]))
  exact hh.trans ((hb.coefficient a ha ha₂).term_le n)

/-- The strong coefficient-error guard already implies compression
domination; no independent scale choice is required for it. -/
theorem compression_of_error_small {a ε Θ target G d : ℝ}
    (ha : 1 / 2 ≤ a) (hε : 0 ≤ ε) (hΘ : 0 ≤ Θ) (htarget : target ≤ Θ)
    (hG : 1 ≤ G) (hd : 0 ≤ d)
    (herr : 16 * (ε * Θ * (4 * G) ^ 2 + d) ≤ 1) : 60*(G+d)*target*ε < a := by
  have hprod : 0 ≤ ε*Θ*G^2 := mul_nonneg (mul_nonneg hε hΘ) (sq_nonneg G)
  have hd1 : d ≤ 1 := by nlinarith only [herr, hprod]
  have hG₀ : 0 ≤ G := le_trans zero_le_one hG
  have hGsq : G+d ≤ 2*G^2 := by nlinarith only [hG, hd1, sq_nonneg (G-1)]
  have htargetmul := mul_le_mul_of_nonneg_right htarget hε
  have hfull := mul_le_mul_of_nonneg_left htargetmul (show 0 ≤ 60*(G+d) by positivity)
  have hscale := mul_le_mul_of_nonneg_right hGsq (mul_nonneg hΘ hε)
  nlinarith only [herr, hd, hfull, hscale, ha]

theorem scaleSequence_ge_initial (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (hX : 0 ≤ X) (n : ℕ) :
    X ≤ scaleSequence J X n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have hj : (1:ℝ) ≤ (J+n:ℕ) := by exact_mod_cast (show 1 ≤ J+n by omega)
    rw [scaleSequence_succ]
    exact ih.trans (le_mul_of_one_le_left (hX.trans ih) (one_le_pow₀ hj))

/-- Target time, given by `scaleSequence J X (n+1)/sqrt β`. -/
def targetTime (J : ℕ) (X β : ℝ) (n : ℕ) : ℝ := scaleSequence J X (n+1)/sqrt β

/-- Horizon, given by `targetTime J X β n+actualExtraTime J X a n`. -/
def horizon (J : ℕ) (X a β : ℝ) (n : ℕ) : ℝ := targetTime J X β n+actualExtraTime J X a n

/-- Stage guards data, collecting `epsilon_pos`, `epsilon_small`, `sigma_pos`, `sigma_small`,
`reciprocal_pos`, `reciprocal_small` and their compatibility conditions. -/
structure StageGuards (J D : ℕ) (C c X K : ℝ) (a β : ℕ → ℝ) (n : ℕ) : Prop where
  epsilon_pos : 0 < epsilon J X (a n) n
  epsilon_small : epsilon J X (a n) n ≤ 1
  sigma_pos : 0 < sqrt (β n)
  sigma_small : sqrt (β n) ≤ 1/4
  reciprocal_pos : 0 < (scaleSequence J X (n+1))⁻¹
  reciprocal_small : (scaleSequence J X (n+1))⁻¹ ≤ 1/2
  target_from_sigma : 1/sqrt (β n) ≤ targetTime J X (β n) n
  target_le_horizon : targetTime J X (β n) n ≤ horizon J X (a n) (β n) n
  horizon_le_Theta : horizon J X (a n) (β n) n ≤ sourceTheta J C (scaleSequence J X) n
  extra_time : horizon J X (a n) (β n) n-targetTime J X (β n) n ≤
    1/sourceTheta J C (scaleSequence J X) n^60
  next_width : timeWidth J X (n+1) ≤ timeWidth J X n/2
  geometry_small : 1000000*K*geometryError J D C c X a n*sourceTheta J C (scaleSequence J X) n^40 ≤
      1
  compression : 60*((1+olderShear J X n)+(priorError J D X n+neighborError J D X c n)) *
    targetTime J X (β n) n*epsilon J X (a n) n < a n

theorem stage_guards (J D : ℕ) (hJ : 3 ≤ J) (C c X K δ : ℝ)
    (hC : 4 ≤ C) (hX : 8 ≤ X) (hK : 1 ≤ K) (hδ : δ ≤ 1 / 2)
    (hδK : 1000000 * K * δ ≤ 1) (hb : ActualBounds J D C c X δ)
    (a β : ℕ → ℝ) (ha : ∀ n, 1 / 2 ≤ a n) (ha₂ : ∀ n, a n ≤ 2)
    (hβ : ∀ n, 1 / 2 ≤ β n * scaleSequence J X n ^ 2)
    (hβ₂ : ∀ n, β n * scaleSequence J X n ^ 2 ≤ 2) (n : ℕ) :
    StageGuards J D C c X K a β n := by
  have hJ1 : 1 ≤ J := by omega
  have hC1 : 1 ≤ C := by linarith only [hC]
  have hXp : 0 < X := by linarith only [hX]
  have hxn : 8 ≤ scaleSequence J X n := hX.trans (scaleSequence_ge_initial J hJ1 X hXp.le n)
  have hj : (3:ℝ) ≤ (J+n:ℕ) := by exact_mod_cast (show 3 ≤ J+n by omega)
  have hact := source_activation_ode_guards hj hxn (hβ n) (hβ₂ n)
  have ht : targetTime J X (β n) n ≤ 2*((J+n:ℕ):ℝ)^2*scaleSequence J X n^2 := by
    simpa only [targetTime, scaleSequence_succ] using hact.2.2.2.2.2.1
  have hx1 : ∀ m, 1 ≤ scaleSequence J X m := fun m =>
    (by linarith only [hX] : 1 ≤ X).trans (scaleSequence_ge_initial J hJ1 X hXp.le m)
  have hθ := (sourceTheta_bounds hJ1 hC1 hx1 n).1
  have hθp : 0 < sourceTheta J C (scaleSequence J X) n := lt_of_lt_of_le zero_lt_one hθ
  have ha₀ : ∀ m, 0 ≤ a m := fun m => by linarith only [ha m]
  have heps : 0 < epsilon J X (a n) n :=
    sqrt_pos.mpr (div_pos (by linarith only [ha n]) (previousShear_pos J hXp n))
  have hextra₀ : 0 ≤ actualExtraTime J X (a n) n := by
    exact mul_nonneg (mul_nonneg (by norm_num) (sqrt_nonneg _)) (timeWidth_pos J hJ1 hXp (n+1)).le
  have hextra := actualExtraTime_small J D hJ C c X δ hC1 hX hb n (a n) (ha₀ n) (ha₂ n)
  have hextra1 : actualExtraTime J X (a n) n ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (one_le_pow₀ hθ : 1 ≤ sourceTheta J C (scaleSequence J X)
        n^60) hextra₀
    nlinarith only [hh, hextra, hδ]
  have hpow : 0 < sourceTheta J C (scaleSequence J X) n^60 := pow_pos hθp 60
  have hextraSharp : actualExtraTime J X (a n) n ≤ 1/sourceTheta J C (scaleSequence J X) n^60 :=
    (le_div_iff₀ hpow).mpr (hextra.trans (by linarith only [hδ]))
  have hg : 1 ≤ 1+olderShear J X n := by
    cases n with
    | zero => norm_num [olderShear]
    | succ m =>
      change 1 ≤ 1+previousShear J X m
      linarith only [previousShear_pos J hXp m]
  have hd : 0 ≤ priorError J D X n+neighborError J D X c n := by
    have hp := (previousShear_pos J hXp n).le
    have hk := (previousFrequency_pos J D hXp n).le
    unfold priorError neighborError supportScale
    positivity
  have he0 : geometryError J D C c X a n ≤ 1 := by
    have hh := coefficient_small J D hJ C c X δ hC1 hX hb a ha₀ ha₂ 0 (by omega) n
    norm_num only [pow_zero, mul_one] at hh
    linarith only [hh, hδ]
  have heps1 : epsilon J X (a n) n ≤ 1 := by
    have hG : 1 ≤ (4*(1+olderShear J X n))^2 := by
        nlinarith only [hg, sq_nonneg (1+olderShear J X n-1)]
    have htG : 1 ≤ sourceTheta J C (scaleSequence J X) n*(4*(1+olderShear J X n))^2 :=
      one_le_mul_of_one_le_of_one_le hθ hG
    have hh := mul_le_mul_of_nonneg_left htG heps.le
    unfold geometryError at he0
    nlinarith only [he0, hh, hd]
  have htθ : targetTime J X (β n) n ≤ sourceTheta J C (scaleSequence J X) n := by
    have hnonneg : 0 ≤ ((J+n:ℕ):ℝ)^2*scaleSequence J X n^2 := by positivity
    have hm := mul_le_mul_of_nonneg_right hC (by
        linarith only [hnonneg] : 0 ≤ 1+((J+n:ℕ):ℝ)^2*scaleSequence J X n^2)
    unfold sourceTheta
    nlinarith only [hm, hnonneg, ht]
  refine ⟨heps, heps1, hact.2.2.1, hact.2.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_,
    actualWidths_contract J D hJ C c X δ hX hb hδ n, ?_, ?_⟩
  · simpa only [one_div, scaleSequence_succ] using hact.2.2.2.2.2.2.1
  · simpa only [one_div, scaleSequence_succ] using hact.2.2.2.2.2.2.2
  · simpa only [targetTime, scaleSequence_succ] using hact.2.2.2.2.1
  · exact le_add_of_nonneg_right hextra₀
  · have hnonneg : 0 ≤ ((J+n:ℕ):ℝ)^2*scaleSequence J X n^2 := by positivity
    have hm := mul_le_mul_of_nonneg_right hC (by
        linarith only [hnonneg] : 0 ≤ 1+((J+n:ℕ):ℝ)^2*scaleSequence J X n^2)
    unfold horizon sourceTheta
    nlinarith only [hm, hnonneg, ht, hextra1]
  · simpa only [horizon, add_sub_cancel_left] using hextraSharp
  · have hh := mul_le_mul_of_nonneg_left
      (coefficient_small J D hJ C c X δ hC1 hX hb a ha₀ ha₂ 40 (by omega) n)
      (show 0 ≤ 1000000*K by positivity)
    nlinarith only [hh, hδK]
  · exact compression_of_error_small (ha n) heps.le hθp.le htθ hg hd
      (by simpa only [geometryError, add_assoc] using he0)

/-- All numerical geometry guards are achieved by one fixed stage, then one
base scale, uniformly over every frame satisfying the induction invariants. -/
theorem exists_guarded_sequence (D : ℕ) (hD : 1000 ≤ D) (C c K : ℝ)
    (hC : 4 ≤ C) (hc : 0 ≤ c) (hK : 1 ≤ K) :
    ∃ J : ℕ, 3 ≤ J ∧ ∀ η : ℝ, 0 < η → ∃ X₀ δ : ℝ, 8 ≤ X₀ ∧ 0 < δ ∧ δ ≤ η ∧
      ∀ X : ℝ, X₀ ≤ X → ActualBounds J D C c X δ ∧
        ∀ a β : ℕ → ℝ, (∀ n, 1/2 ≤ a n) → (∀ n, a n ≤ 2) →
          (∀ n, 1/2 ≤ β n*scaleSequence J X n^2) →
          (∀ n, β n*scaleSequence J X n^2 ≤ 2) →
          ∀ n, StageGuards J D C c X K a β n := by
  obtain ⟨J, hJ, hchoice⟩ := actual_uniform_choice D hD C c (by linarith only [hC]) hc
  refine ⟨J, hJ, ?_⟩
  intro η hη
  let δ : ℝ := min η (min (1/2) (1/(1000000*K)))
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hδη : δ ≤ η := min_le_left _ _
  have hδhalf : δ ≤ 1/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδinv : δ ≤ 1/(1000000*K) := (min_le_right _ _).trans (min_le_right _ _)
  have hδK : 1000000*K*δ ≤ 1 := by
    have hh := (le_div_iff₀ (show 0 < 1000000*K by positivity)).mp hδinv
    nlinarith only [hh]
  obtain ⟨X₀, hX₀, hX⟩ := hchoice δ hδpos
  refine ⟨X₀, δ, hX₀, hδpos, hδη, ?_⟩
  intro X hXX
  have hb := hX X hXX
  exact ⟨hb, fun a β ha ha₂ hβ hβ₂ n => stage_guards J D hJ C c X K δ hC (hX₀.trans hXX)
    hK hδhalf hδK hb a β ha ha₂ hβ hβ₂ n⟩

/-- Equation (39) gives the actual packet power inequality for the
constructed sequence, for every fixed polynomial degree and positive
frequency exponent. The aggregate includes any fixed base constants. -/
theorem parameter_packet_bound_eventually (J : ℕ) (hJ : 3 ≤ J) (X Cbase Cstar : ℝ)
    (hX : 1 ≤ X) (hCbase : 1 ≤ Cbase) (hCstar : 0 ≤ Cstar)
    (Q : ℕ) (θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ n in atTop,
      sourceParameterAggregate J Cbase Cstar (scaleSequence J X) n^Q ≤ frequency J X n^θ := by
  have hlim := (source_parameters_separated J (by omega) Cbase Cstar hCbase hCstar
    (scaleSequence J X) hX (scaleSequence_succ J X)).const_mul (Q:ℝ)
  simp only [mul_zero] at hlim
  have hxp := quadratic_growth_pos J (by omega) (scaleSequence J X)
    (show 0 < scaleSequence J X 0 from lt_of_lt_of_le zero_lt_one hX) (scaleSequence_succ J X)
  filter_upwards [hlim.eventually_le_const hθ] with n hn
  have hj : (0:ℝ) < (J+n:ℕ) := by exact_mod_cast (show 0 < J+n by omega)
  have hscale : 0 < scaleSequence J X n/((J+n:ℕ):ℝ)^2 := div_pos (hxp n) (pow_pos hj 2)
  have hq : ((Q:ℝ)*log (sourceParameterAggregate J Cbase Cstar (scaleSequence J X) n))/
      (scaleSequence J X n/((J+n:ℕ):ℝ)^2) ≤ θ := by
    convert! hn using 1
    ring
  have hb := (div_le_iff₀ hscale).mp hq
  have hP : 0 < sourceParameterAggregate J Cbase Cstar (scaleSequence J X) n :=
    Finset.sum_pos (fun i _ => exp_pos _) Finset.univ_nonempty
  calc
    _ = exp ((Q:ℝ)*log (sourceParameterAggregate J Cbase Cstar (scaleSequence J X) n)) := by
      rw [exp_nat_mul, exp_log hP]
    _ ≤ exp (θ*(scaleSequence J X n/((J+n:ℕ):ℝ)^2)) := exp_le_exp.mpr hb
    _ = _ := by
      unfold frequency
      rw [← exp_mul]
      congr 1
      ring

end EulerPacketSourceScaleGuards
