/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceScaleSequence
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketBaseScales
import LeanPool.NavierStokesAndEuler.Euler.Foundations.Scale
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.GCD

/-!
The geometry error for the literal scale sequences, including the initial
polynomial shear and frequency.  Comparison with the normal-form costs is
proved here, rather than imposed at the two exceptional starting stages.
-/

@[expose] public section


noncomputable section


namespace EulerPacketSourceScaleActual

open Real Filter EulerScale EulerPacketSourceScales EulerPacketSourceTime
  EulerPacketSourceScaleBounds EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence
  EulerPacketBaseScales

open scoped Topology

/-- Epsilon, given by `sqrt (a/previousShear J X n)`. -/
def epsilon (J : ℕ) (X a : ℝ) (n : ℕ) : ℝ := sqrt (a/previousShear J X n)

/-- Prior error, given by `previousFrequency J D X n ^ (-(1/4 : ℝ))`. -/
def priorError (J D : ℕ) (X : ℝ) (n : ℕ) : ℝ := previousFrequency J D X n ^ (-(1/4 : ℝ))

/-- Neighbor error, given by `supportScale J X n * previousFrequency J D X n^c * previousShear J
X n^c`. -/
def neighborError (J D : ℕ) (X c : ℝ) (n : ℕ) : ℝ :=
  supportScale J X n * previousFrequency J D X n^c * previousShear J X n^c

/-- Geometry error as an element of `ℝ`. -/
def geometryError (J D : ℕ) (C c X : ℝ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  16*(epsilon J X (a n) n*sourceTheta J C (scaleSequence J X) n*(4*(1+olderShear J X n))^2 +
    priorError J D X n+neighborError J D X c n)

/-- Base error cost, given by `16*(128*X^(-500 : ℝ)*sourceTheta J C (scaleSequence J X)
0+X^(-(D:ℝ)/4)) * sourceTheta J C (scaleSequence J X) 0^60`. -/
def baseErrorCost (J D : ℕ) (C X : ℝ) : ℝ :=
  16*(128*X^(-500 : ℝ)*sourceTheta J C (scaleSequence J X) 0+X^(-(D:ℝ)/4)) *
    sourceTheta J C (scaleSequence J X) 0^60

/-- Geometry error cost, given by `geometryError J D C c X a n * sourceTheta J C (scaleSequence
J X) n^60`. -/
def geometryErrorCost (J D : ℕ) (C c X : ℝ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  geometryError J D C c X a n * sourceTheta J C (scaleSequence J X) n^60

theorem epsilon_succ_le (J : ℕ) (hJ : 1 ≤ J) (X a : ℝ)
    (ha : 0 ≤ a) (ha₂ : a ≤ 2) (n : ℕ) :
    epsilon J X a (n+1) ≤ sourceEpsilon J (scaleSequence J X) (n+1) := by
  unfold epsilon sourceEpsilon
  rw [previousShear_succ_eq J hJ X n]
  have hh := epsilon_of_shear_bound (L := scaleSequence J X (n+1)/((J-1+(n+1) : ℕ) : ℝ)^7) ha ha₂
  convert! hh using 1
  congr 2
  ring

theorem epsilon_zero_le (J : ℕ) {X a : ℝ} (hX : 0 < X) (ha : 0 ≤ a) (ha₂ : a ≤ 2) :
    epsilon J X a 0 ≤ 2*X^(-500 : ℝ) := by
  have hp : X^1000 = exp ((1000:ℝ)*log X) := by
    simpa only [Nat.cast_ofNat, exp_log hX] using (exp_nat_mul (log X) 1000).symm
  have hh := epsilon_of_shear_bound (L := 1000*log X) ha ha₂
  change sqrt (a/X^1000) ≤ _
  rw [hp]
  refine hh.trans_eq ?_
  rw [rpow_def_of_pos hX]
  congr 2
  ring

theorem priorError_succ_eq (J D : ℕ) (hJ : 1 ≤ J) (X : ℝ) (n : ℕ) :
    priorError J D X (n+1) = sourcePriorError J (scaleSequence J X) (n+1) := by
  unfold priorError
  rw [previousFrequency_succ_eq J D hJ X n, ← exp_mul]
  unfold sourcePriorError
  congr 1
  ring

theorem priorError_zero_eq (J D : ℕ) {X : ℝ} (hX : 0 < X) :
    priorError J D X 0 = X^(-(D:ℝ)/4) := by
  unfold priorError previousFrequency
  rw [← rpow_natCast, ← rpow_mul hX.le]
  congr 1
  ring

theorem neighborError_le (J D : ℕ) (hJ : 1 ≤ J) (X c : ℝ) (hX : 0 < X) (hc : 0 ≤ c)
    (hbaseH : X ^ 1000 ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 7))
    (hbaseK : X ^ D ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 4)) (n : ℕ) :
    neighborError J D X c n ≤ sourceNeighborError J c (scaleSequence J X) n := by
  have hK := rpow_le_rpow (previousFrequency_pos J D hX n).le
    (previousFrequency_le_normal J D hJ X hbaseK n) hc
  have hH := rpow_le_rpow (previousShear_pos J hX n).le
    (previousShear_le_normal J hJ X hbaseH n) hc
  have hs : 0 ≤ supportScale J X n := (exp_pos _).le
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left hK hs) hH
    (rpow_nonneg (previousShear_pos J hX n).le c) (by positivity)
  change neighborError J D X c n ≤
    supportScale J X n * exp (scaleSequence J X n/((J-1+n : ℕ) : ℝ)^4)^c *
      exp (scaleSequence J X n/((J-1+n : ℕ) : ℝ)^7)^c at hh
  refine hh.trans_eq ?_
  rw [← exp_mul, ← exp_mul]
  unfold supportScale sourceNeighborError
  rw [← exp_add, ← exp_add]
  congr 1
  ring

theorem geometryError_nonneg (J D : ℕ) (C c X : ℝ) (a : ℕ → ℝ) (n : ℕ)
    (hC : 0 ≤ C) (hX : 0 < X) : 0 ≤ geometryError J D C c X a n := by
  have hH := (previousShear_pos J hX n).le
  have hK := (previousFrequency_pos J D hX n).le
  unfold geometryError epsilon sourceTheta priorError neighborError supportScale
  positivity

theorem geometryError_succ_le (J D : ℕ) (hJ : 3 ≤ J) (C c X : ℝ) (hC : 1 ≤ C)
    (hX : 1 ≤ X) (hc : 0 ≤ c) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ha₂ : ∀ n, a n ≤ 2)
    (hbaseH : X ^ 1000 ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 7))
    (hbaseK : X ^ D ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 4)) (n : ℕ) :
    geometryError J D C c X a (n+1) ≤ 16*sourceCoefficientError J C c (scaleSequence J X) (n+1) :=
        by
  have hJ1 : 1 ≤ J := by omega
  have hXp : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hx1 := quadratic_growth_one_le J hJ1 (scaleSequence J X) hX (scaleSequence_succ J X)
  have hθ : 0 ≤ sourceTheta J C (scaleSequence J X) (n+1) :=
    le_trans zero_le_one (sourceTheta_bounds hJ1 hC hx1 (n+1)).1
  have he := epsilon_succ_le J hJ1 X (a (n+1)) (ha (n+1)) (ha₂ (n+1)) n
  have hg := olderShear_le_normal J hJ X hXp.le hbaseH (n+1)
  have hg₀ : 0 ≤ 1+olderShear J X (n+1) := by
    change 0 ≤ 1+previousShear J X n
    linarith only [previousShear_pos J hXp n]
  have hprod := mul_le_mul (mul_le_mul_of_nonneg_right he hθ)
    (pow_le_pow_left₀ hg₀ hg 2) (sq_nonneg _)
    (mul_nonneg (show 0 ≤ sourceEpsilon J (scaleSequence J X) (n+1) by
        unfold sourceEpsilon; positivity) hθ)
  have hn := neighborError_le J D hJ1 X c hXp hc hbaseH hbaseK (n+1)
  have hp₀ : 0 ≤ sourcePriorError J (scaleSequence J X) (n+1) := (exp_pos _).le
  have hn₀ : 0 ≤ sourceNeighborError J c (scaleSequence J X) (n+1) := (exp_pos _).le
  unfold geometryError sourceCoefficientError
  rw [priorError_succ_eq J D hJ1 X n]
  nlinarith only [hprod, hn, hp₀, hn₀]

theorem geometryError_zero_le (J D : ℕ) (hJ : 3 ≤ J) (C c X : ℝ) (hC : 1 ≤ C)
    (hX : 1 ≤ X) (hc : 0 ≤ c) (a : ℕ → ℝ) (ha : 0 ≤ a 0) (ha₂ : a 0 ≤ 2)
    (hbaseH : X ^ 1000 ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 7))
    (hbaseK : X ^ D ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 4)) :
    geometryError J D C c X a 0 ≤
      16*(128*X^(-500 : ℝ)*sourceTheta J C (scaleSequence J X) 0+X^(-(D:ℝ)/4)) +
        sourceCoefficientError J C c (scaleSequence J X) 0 := by
  have hJ1 : 1 ≤ J := by omega
  have hXp : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hx1 := quadratic_growth_one_le J hJ1 (scaleSequence J X) hX (scaleSequence_succ J X)
  have hθ : 0 ≤ sourceTheta J C (scaleSequence J X) 0 :=
    le_trans zero_le_one (sourceTheta_bounds hJ1 hC hx1 0).1
  have he := mul_le_mul_of_nonneg_right (epsilon_zero_le J hXp ha ha₂) hθ
  have hn := neighborError_le J D hJ1 X c hXp hc hbaseH hbaseK 0
  have hp₀ : 0 ≤ sourcePriorError J (scaleSequence J X) 0 := (exp_pos _).le
  have hs₀ : 0 ≤ sourceEpsilon J (scaleSequence J X) 0*sourceTheta J C (scaleSequence J X) 0 *
      sourceOlderGradient J (scaleSequence J X) 0^2 := by
    unfold sourceEpsilon
    positivity
  unfold geometryError sourceCoefficientError
  rw [priorError_zero_eq J D hXp]
  norm_num only [olderShear]
  nlinarith only [he, hn, hp₀, hs₀]

theorem geometryErrorCost_bound (J D : ℕ) (hJ : 3 ≤ J) (C c X : ℝ) (hC : 1 ≤ C)
    (hX : 1 ≤ X) (hc : 0 ≤ c) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ha₂ : ∀ n, a n ≤ 2)
    (hbaseH : X ^ 1000 ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 7))
    (hbaseK : X ^ D ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 4)) (n : ℕ) :
    geometryErrorCost J D C c X a n ≤
      16*coefficientCost J C c 60 (scaleSequence J X) n + if n=0 then baseErrorCost J D C X else 0
          := by
  have hx1 := quadratic_growth_one_le J (by omega) (scaleSequence J X) hX (scaleSequence_succ J X)
  have hθ : 0 ≤ sourceTheta J C (scaleSequence J X) n :=
    le_trans zero_le_one (sourceTheta_bounds (by omega : 1 ≤ J) hC hx1 n).1
  cases n with
  | zero =>
    have hh := mul_le_mul_of_nonneg_right
      (geometryError_zero_le J D hJ C c X hC hX hc a (ha 0) (ha₂ 0) hbaseH hbaseK)
      (pow_nonneg hθ 60)
    have he₀ : 0 ≤ sourceCoefficientError J C c (scaleSequence J X) 0 := by
      unfold sourceCoefficientError sourceEpsilon sourcePriorError sourceNeighborError
      positivity
    have hc₀ := mul_nonneg he₀ (pow_nonneg hθ 60)
    simp only [ite_true]
    unfold geometryErrorCost coefficientCost baseErrorCost
    nlinarith only [hh, hc₀]
  | succ n =>
    have hh := mul_le_mul_of_nonneg_right
      (geometryError_succ_le J D hJ C c X hC hX hc a ha ha₂ hbaseH hbaseK n)
      (pow_nonneg hθ 60)
    simpa only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, add_zero,
      geometryErrorCost, coefficientCost, mul_assoc] using hh

theorem baseErrorCost_nonneg (J D : ℕ) (C X : ℝ) (hC : 0 ≤ C) (hX : 0 ≤ X) :
    0 ≤ baseErrorCost J D C X := by
  unfold baseErrorCost sourceTheta
  positivity

/-- The two genuinely exceptional polynomial terms are small with the
specified D₀=1000 and any base frequency power D≥1000. -/
theorem baseErrorCost_tendsto_zero (J D : ℕ) (hJ : 1 ≤ J) (hD : 1000 ≤ D)
    (C : ℝ) (hC : 1 ≤ C) : Tendsto (baseErrorCost J D C) atTop (𝓝 0) := by
  let T : ℝ := 2*C*(J:ℝ)^2
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hDr : (1000:ℝ) ≤ D := by exact_mod_cast hD
  have h₁ := (base_power_decay T (-500) 61 0 (by norm_num)).const_mul 128
  have h₂ := base_power_decay T (-(D:ℝ)/4) 60 0 (by norm_num; linarith only [hDr])
  have hh := (h₁.add h₂).const_mul 16
  simp only [mul_zero, add_zero] at hh
  have hlim : Tendsto (fun X : ℝ =>
      16*(128*X^(-500 : ℝ)*(T*X^2)+X^(-(D:ℝ)/4))*(T*X^2)^60) atTop (𝓝 0) := by
    convert! hh using 1
    ext X
    simp only [pow_zero, mul_one]
    rw [show (61:ℕ) = 60+1 from rfl, pow_succ]
    ring
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with X hX
    exact baseErrorCost_nonneg J D C X (le_trans zero_le_one hC) hX
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with X hX
    have hx1 := quadratic_growth_one_le J hJ (scaleSequence J X) hX (scaleSequence_succ J X)
    have hθ₀ : 0 ≤ sourceTheta J C (scaleSequence J X) 0 :=
      le_trans zero_le_one (sourceTheta_bounds hJ hC hx1 0).1
    have hθ : sourceTheta J C (scaleSequence J X) 0 ≤ T*X^2 := by
      simpa only [T, Nat.add_zero, scaleSequence_zero] using (sourceTheta_bounds hJ hC hx1 0).2
    have hinner : 16*(128*X^(-500 : ℝ)*sourceTheta J C (scaleSequence J X) 0+X^(-(D:ℝ)/4)) ≤
        16*(128*X^(-500 : ℝ)*(T*X^2)+X^(-(D:ℝ)/4)) := by
      gcongr
    exact mul_le_mul hinner (pow_le_pow_left₀ hθ₀ hθ 60) (pow_nonneg hθ₀ 60) (by positivity)

/-- Actual bounds data, collecting `normal`, `initial_shear`, `initial_frequency`,
`coefficient`. -/
structure ActualBounds (J D : ℕ) (C c X δ : ℝ) : Prop where
  normal : UniformBounds J C c 60 (scaleSequence J X) δ
  initial_shear : X^1000 ≤ exp (X/((J-1 : ℕ) : ℝ)^7)
  initial_frequency : X^D ≤ exp (X/((J-1 : ℕ) : ℝ)^4)
  coefficient : ∀ a : ℕ → ℝ, (∀ n, 0 ≤ a n) → (∀ n, a n ≤ 2) →
    SmallSeries (geometryErrorCost J D C c X a) δ

/-- The actual sequence, with both polynomial starting scales, has one
choice of J followed by x₀ making every geometry error uniformly and
summably small.  This is uniform over the allowed frame coefficient a. -/
theorem actual_uniform_choice (D : ℕ) (hD : 1000 ≤ D) (C c : ℝ)
    (hC : 1 ≤ C) (hc : 0 ≤ c) :
    ∃ J : ℕ, 3 ≤ J ∧ ∀ δ : ℝ, 0 < δ → ∃ X₀ : ℝ, 8 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X → ActualBounds J D C c X δ := by
  obtain ⟨J, hJ, hchoice⟩ := explicit_sequence_uniform_choice C c hC hc 60
  refine ⟨J, hJ, ?_⟩
  intro δ hδ
  obtain ⟨Y₀, hY₀, hY⟩ := hchoice (δ/32) (by positivity)
  have hp : (0:ℝ) < (J-1:ℕ) := by exact_mod_cast (show 0 < J-1 by omega)
  have hall : ∀ᶠ X : ℝ in atTop,
      X^1000 ≤ exp (X/((J-1:ℕ):ℝ)^7) ∧
      X^D ≤ exp (X/((J-1:ℕ):ℝ)^4) ∧ baseErrorCost J D C X ≤ δ/2 :=
    (eventually_pow_le_exp 1000 (pow_pos hp 7)).and
      ((eventually_pow_le_exp D (pow_pos hp 4)).and
        ((baseErrorCost_tendsto_zero J D (by omega) hD C hC).eventually_le_const (by positivity)))
  obtain ⟨Y₁, hY₁⟩ := eventually_atTop.1 hall
  refine ⟨max Y₀ Y₁, hY₀.trans (le_max_left _ _), ?_⟩
  intro X hX
  have hXY₀ : Y₀ ≤ X := (le_max_left _ _).trans hX
  have hXY₁ : Y₁ ≤ X := (le_max_right _ _).trans hX
  have hX8 : 8 ≤ X := hY₀.trans hXY₀
  have hX1 : 1 ≤ X := by linarith only [hX8]
  have hXp : 0 < X := by linarith only [hX8]
  have hbase := hY₁ X hXY₁
  have hn := hY X hXY₀
  have hw : δ/32 ≤ δ := by linarith only [hδ]
  refine ⟨⟨hn.coefficient.weaken hw, fun a ha ha₂ => (hn.extraTime a ha ha₂).weaken hw,
    hn.width.weaken hw, hn.parent.weaken hw, hn.good.weaken hw⟩, hbase.1, hbase.2.1, ?_⟩
  intro a ha ha₂
  let f : ℕ → ℝ := fun n => 16*coefficientCost J C c 60 (scaleSequence J X) n
  let z : ℕ → ℝ := fun n => if n=0 then baseErrorCost J D C X else 0
  have hf : SmallSeries f (δ/2) := by
    refine ⟨fun n => mul_nonneg (by norm_num) (hn.coefficient.nonneg n),
      hn.coefficient.summable.mul_left 16, ?_⟩
    change (∑' n, 16*coefficientCost J C c 60 (scaleSequence J X) n) ≤ δ/2
    rw [tsum_mul_left]
    nlinarith only [hn.coefficient.total_le]
  have hz : SmallSeries z (δ/2) := by
    refine ⟨?_, (hasSum_ite_eq 0 (baseErrorCost J D C X)).summable, ?_⟩
    · intro n
      exact ite_nonneg (baseErrorCost_nonneg J D C X (le_trans zero_le_one hC) hXp.le) le_rfl
    · change (∑' n : ℕ, if n=0 then baseErrorCost J D C X else 0) ≤ δ/2
      rw [tsum_ite_eq]
      exact hbase.2.2
  have hsum : SmallSeries (fun n => f n+z n) δ := by
    refine ⟨fun n => add_nonneg (hf.nonneg n) (hz.nonneg n), hf.summable.add hz.summable, ?_⟩
    rw [hf.summable.tsum_add hz.summable]
    linarith only [hf.total_le, hz.total_le]
  apply hsum.mono
  · intro n
    unfold geometryErrorCost
    exact mul_nonneg (geometryError_nonneg J D C c X a n (le_trans zero_le_one hC) hXp)
      (pow_nonneg (by unfold sourceTheta; positivity) 60)
  · intro n
    exact geometryErrorCost_bound J D hJ C c X hC hX1 hc a ha ha₂ hbase.1 hbase.2.1 n

end EulerPacketSourceScaleActual
