/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Real.Sqrt

/-!
# Exact moment algebra for the true-cone loop construction

This file proves the finite-distribution form of the averaging and rephasing
identities in Lemma 6.1 of the candidate manuscript. The formulas are algebraic;
no existence, smoothness, or invertibility of a circle reparametrization is
asserted here. The hypotheses of `rephased_moments` are ordinary mass, mean,
and variance constraints, not an assumption that a desired loop exists.

The final lemmas give explicit two-point distributions with prescribed variance.
They establish finite moment feasibility, including a one-sided support bound.
-/

@[expose] public section


namespace NavierStokes.LoopMoments

open scoped BigOperators

noncomputable section

variable {ι : Type*}

/-- A finite weighted average. We retain the weights explicitly, so no
probabilistic or analytic existence assertion is hidden in the notation. -/
def avg (s : Finset ι) (w f : ι → ℝ) : ℝ :=
  ∑ i ∈ s, w i * f i

theorem avg_add (s : Finset ι) (w f g : ι → ℝ) :
    avg s w (fun i => f i + g i) = avg s w f + avg s w g := by
  simp only [avg, mul_add, Finset.sum_add_distrib]

theorem avg_sub (s : Finset ι) (w f g : ι → ℝ) :
    avg s w (fun i => f i - g i) = avg s w f - avg s w g := by
  simp only [avg, mul_sub, Finset.sum_sub_distrib]

theorem avg_const_mul (s : Finset ι) (w f : ι → ℝ) (c : ℝ) :
    avg s w (fun i => c * f i) = c * avg s w f := by
  simp only [avg, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem avg_const (s : Finset ι) (w : ι → ℝ) (c : ℝ)
    (hmass : ∑ i ∈ s, w i = 1) :
    avg s w (fun _ => c) = c := by
  simp only [avg, ← Finset.sum_mul, hmass, one_mul]

theorem avg_nonneg (s : Finset ι) (w f : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hf : ∀ i ∈ s, 0 ≤ f i) :
    0 ≤ avg s w f := by
  exact Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (hf i hi))

/-- The standard variance expansion, with mass and first moment explicit. -/
theorem variance_identity (s : Finset ι) (w t : ι → ℝ) (m : ℝ)
    (hmass : ∑ i ∈ s, w i = 1) (hmean : avg s w t = m) :
    avg s w (fun i => (t i - m) ^ 2) = avg s w (fun i => t i ^ 2) - m ^ 2 := by
  calc
    avg s w (fun i => (t i - m) ^ 2) =
        avg s w (fun i => t i ^ 2 - (2 * m) * t i + m ^ 2) := by
          congr 1
          funext i
          ring
    _ = avg s w (fun i => t i ^ 2) - (2 * m) * avg s w t + m ^ 2 := by
          rw [avg_add, avg_sub, avg_const_mul, avg_const s w (m ^ 2) hmass]
    _ = avg s w (fun i => t i ^ 2) - m ^ 2 := by rw [hmean]; ring

/-- This is `a ⟨1+t²⟩ = a(1+m²) + ρ` from the manuscript. -/
theorem energy_moment (s : Finset ι) (w t : ι → ℝ) (a m ρ : ℝ)
    (ha : a ≠ 0) (hmass : ∑ i ∈ s, w i = 1)
    (hmean : avg s w t = m)
    (hvar : avg s w (fun i => (t i - m) ^ 2) = ρ / a) :
    a * avg s w (fun i => 1 + t i ^ 2) = a * (1 + m ^ 2) + ρ := by
  have hsecond : avg s w (fun i => t i ^ 2) = m ^ 2 + ρ / a := by
    have := variance_identity s w t m hmass hmean
    linarith
  rw [avg_add, avg_const s w 1 hmass, hsecond]
  field_simp; ring

/-- A nonnegative weighted variance cannot decrease the nominal speed. -/
theorem variance_nonneg (s : Finset ι) (w t : ι → ℝ) (m : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    0 ≤ avg s w (fun i => (t i - m) ^ 2) := by
  exact avg_nonneg s w _ hw (fun i _ => sq_nonneg (t i - m))

theorem required_variance_nonneg (s : Finset ι) (w t : ι → ℝ) (a m ρ : ℝ)
    (ha : 0 < a) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hvar : avg s w (fun i => (t i - m) ^ 2) = ρ / a) :
    0 ≤ ρ := by
  have h := variance_nonneg s w t m hw
  rw [hvar] at h
  have hmul := mul_nonneg h (le_of_lt ha)
  simpa only [div_mul_cancel₀ _ (ne_of_gt ha)] using hmul

/-- The rephasing density relative to the old averaging parameter. -/
def phaseDensity (a v t : ℝ) : ℝ := a * (1 + t ^ 2) / v

/-- The positive first component of the loop shear. -/
def loopA (v t : ℝ) : ℝ := v / (1 + t ^ 2)

/-- The signed second component; this corresponds to `-b_L`. -/
def loopC (v t : ℝ) : ℝ := v * t / (1 + t ^ 2)

theorem one_add_sq_pos (t : ℝ) : 0 < 1 + t ^ 2 := by
  nlinarith [sq_nonneg t]

theorem loopA_pos (v t : ℝ) (hv : 0 < v) : 0 < loopA v t := by
  exact div_pos hv (one_add_sq_pos t)

theorem phaseDensity_pos (a v t : ℝ) (ha : 0 < a) (hv : 0 < v) :
    0 < phaseDensity a v t := by
  exact div_pos (mul_pos ha (one_add_sq_pos t)) hv

theorem loop_speed (v t : ℝ) : loopA v t * (1 + t ^ 2) = v := by
  unfold loopA
  exact div_mul_cancel₀ v (ne_of_gt (one_add_sq_pos t))

theorem loop_slope (v t : ℝ) (hv : v ≠ 0) : loopC v t / loopA v t = t := by
  unfold loopC loopA
  field_simp

theorem density_times_loopA (a v t : ℝ) (hv : v ≠ 0) :
    phaseDensity a v t * loopA v t = a := by
  unfold phaseDensity loopA
  field_simp

theorem density_times_loopC (a v t : ℝ) (hv : v ≠ 0) :
    phaseDensity a v t * loopC v t = a * t := by
  unfold phaseDensity loopC
  field_simp

/-- Reweighting by the manuscript's density has total mass one. -/
theorem rephased_mass (s : Finset ι) (w t : ι → ℝ) (a m ρ v : ℝ)
    (ha : a ≠ 0) (hv : v ≠ 0) (hmass : ∑ i ∈ s, w i = 1)
    (hmean : avg s w t = m)
    (hvar : avg s w (fun i => (t i - m) ^ 2) = ρ / a)
    (hspeed : v = a * (1 + m ^ 2) + ρ) :
    ∑ i ∈ s, w i * phaseDensity a v (t i) = 1 := by
  have he := energy_moment s w t a m ρ ha hmass hmean hvar
  rw [← hspeed] at he
  calc
    (∑ i ∈ s, w i * phaseDensity a v (t i)) =
        (a * avg s w (fun i => 1 + t i ^ 2)) / v := by
          simp only [phaseDensity, avg, div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = 1 := by rw [he, div_self hv]

/-- The radial shear has the original mean after rephasing. -/
theorem rephased_meanA (s : Finset ι) (w t : ι → ℝ) (a v : ℝ)
    (hv : v ≠ 0) (hmass : ∑ i ∈ s, w i = 1) :
    avg s (fun i => w i * phaseDensity a v (t i)) (fun i => loopA v (t i)) = a := by
  calc
    avg s (fun i => w i * phaseDensity a v (t i)) (fun i => loopA v (t i)) =
        avg s w (fun _ => a) := by
          unfold avg
          apply Finset.sum_congr rfl
          intro i hi
          rw [mul_assoc, density_times_loopA a v (t i) hv]
    _ = a := avg_const s w a hmass

/-- The signed axial shear has the original mean after rephasing. -/
theorem rephased_meanC (s : Finset ι) (w t : ι → ℝ) (a v m : ℝ)
    (hv : v ≠ 0) (hmean : avg s w t = m) :
    avg s (fun i => w i * phaseDensity a v (t i)) (fun i => loopC v (t i)) = a * m := by
  calc
    avg s (fun i => w i * phaseDensity a v (t i)) (fun i => loopC v (t i)) =
        avg s w (fun i => a * t i) := by
          unfold avg
          apply Finset.sum_congr rfl
          intro i hi
          rw [mul_assoc, density_times_loopC a v (t i) hv]
    _ = a * m := by rw [avg_const_mul, hmean]

/-- With `m = -b/a`, the two rephased means are exactly `(a,-b)`. -/
theorem rephased_moments (s : Finset ι) (w t : ι → ℝ) (a b ρ v : ℝ)
    (ha : 0 < a) (hρ : 0 ≤ ρ) (hmass : ∑ i ∈ s, w i = 1)
    (hmean : avg s w t = -b / a)
    (hvar : avg s w (fun i => (t i - (-b / a)) ^ 2) = ρ / a)
    (hspeed : v = a * (1 + (-b / a) ^ 2) + ρ) :
    (∑ i ∈ s, w i * phaseDensity a v (t i) = 1) ∧
      avg s (fun i => w i * phaseDensity a v (t i)) (fun i => loopA v (t i)) = a ∧
      avg s (fun i => w i * phaseDensity a v (t i)) (fun i => loopC v (t i)) = -b := by
  have hvpos : 0 < v := by
    rw [hspeed]
    exact add_pos_of_pos_of_nonneg (mul_pos ha (one_add_sq_pos (-b / a))) hρ
  have hv := ne_of_gt hvpos
  refine ⟨rephased_mass s w t a (-b / a) ρ v (ne_of_gt ha) hv hmass hmean hvar hspeed,
    rephased_meanA s w t a v hv hmass, ?_⟩
  rw [rephased_meanC s w t a v (-b / a) hv hmean]
  field_simp

/-- A two-point probability law. This is a concrete finite object, without
any hypothesis asserting the existence of the manuscript's smooth loop. -/
structure TwoPoint where
  /-- Left weight of `TwoPoint`, of type `ℝ`. -/
  leftWeight : ℝ
  /-- Right weight of `TwoPoint`, of type `ℝ`. -/
  rightWeight : ℝ
  /-- Left value of `TwoPoint`, of type `ℝ`. -/
  leftValue : ℝ
  /-- Right value of `TwoPoint`, of type `ℝ`. -/
  rightValue : ℝ

/-- Mean, given by `q.leftWeight * q.leftValue + q.rightWeight * q.rightValue`. -/
def TwoPoint.mean (q : TwoPoint) : ℝ :=
  q.leftWeight * q.leftValue + q.rightWeight * q.rightValue

/-- Centered second, given by `q.leftWeight * (q.leftValue - m) ^ 2 + q.rightWeight *
(q.rightValue - m) ^ 2`. -/
def TwoPoint.centeredSecond (q : TwoPoint) (m : ℝ) : ℝ :=
  q.leftWeight * (q.leftValue - m) ^ 2 + q.rightWeight * (q.rightValue - m) ^ 2

/-- Is probability, given by `0 ≤ q.leftWeight ∧ 0 ≤ q.rightWeight ∧ q.leftWeight +
q.rightWeight = 1`. -/
def TwoPoint.IsProbability (q : TwoPoint) : Prop :=
  0 ≤ q.leftWeight ∧ 0 ≤ q.rightWeight ∧ q.leftWeight + q.rightWeight = 1

/-- For any nonnegative variance, equal masses at `m ± √V` realize it. -/
def symmetricPair (m V : ℝ) : TwoPoint :=
  ⟨1 / 2, 1 / 2, m - Real.sqrt V, m + Real.sqrt V⟩

theorem symmetricPair_probability (m V : ℝ) : (symmetricPair m V).IsProbability := by
  norm_num [TwoPoint.IsProbability, symmetricPair]

theorem symmetricPair_mean (m V : ℝ) : (symmetricPair m V).mean = m := by
  dsimp [TwoPoint.mean, symmetricPair]
  ring

theorem symmetricPair_variance (m V : ℝ) (hV : 0 ≤ V) :
    (symmetricPair m V).centeredSecond m = V := by
  dsimp [TwoPoint.centeredSecond, symmetricPair]
  have hsq := Real.sq_sqrt hV
  nlinarith

/-- An asymmetric law preserves a lower bound on the projection `p*t`,
while allowing any nonnegative variance. For `p = 0`, use `symmetricPair`.
The lower projected deviation is `-d`, and the upper one is `V*p²/d`. -/
def oneSidedPair (m p d V : ℝ) : TwoPoint :=
  ⟨V * p ^ 2 / (d ^ 2 + V * p ^ 2), d ^ 2 / (d ^ 2 + V * p ^ 2),
    m - d / p, m + V * p / d⟩

theorem oneSidedPair_denom_pos (p d V : ℝ) (hd : 0 < d) (hV : 0 ≤ V) :
    0 < d ^ 2 + V * p ^ 2 := by
  have hprod := mul_nonneg hV (sq_nonneg p)
  nlinarith

theorem oneSidedPair_probability (m p d V : ℝ) (hd : 0 < d) (hV : 0 ≤ V) :
    (oneSidedPair m p d V).IsProbability := by
  have hden := oneSidedPair_denom_pos p d V hd hV
  dsimp [TwoPoint.IsProbability, oneSidedPair]
  refine ⟨div_nonneg (mul_nonneg hV (sq_nonneg p)) (le_of_lt hden),
    div_nonneg (sq_nonneg d) (le_of_lt hden), ?_⟩
  field_simp; ring

theorem oneSidedPair_mean (m p d V : ℝ) (hp : p ≠ 0) (hd : 0 < d) (hV : 0 ≤ V) :
    (oneSidedPair m p d V).mean = m := by
  have hden := ne_of_gt (oneSidedPair_denom_pos p d V hd hV)
  have hdne := ne_of_gt hd
  dsimp [TwoPoint.mean, oneSidedPair]
  field_simp; ring

theorem oneSidedPair_variance (m p d V : ℝ)
    (hp : p ≠ 0) (hd : 0 < d) (hV : 0 ≤ V) :
    (oneSidedPair m p d V).centeredSecond m = V := by
  have hden := ne_of_gt (oneSidedPair_denom_pos p d V hd hV)
  have hdne := ne_of_gt hd
  dsimp [TwoPoint.centeredSecond, oneSidedPair]
  field_simp; ring

theorem oneSidedPair_lower_projection (m p d V : ℝ) (hp : p ≠ 0) :
    p * ((oneSidedPair m p d V).leftValue - m) = -d := by
  dsimp [oneSidedPair]
  field_simp; ring

theorem oneSidedPair_upper_projection (m p d V : ℝ) :
    p * ((oneSidedPair m p d V).rightValue - m) = V * p ^ 2 / d := by
  dsimp [oneSidedPair]
  ring

/-- Every mean whose stress projection is strictly above `2` has a finite
two-point distribution with any prescribed nonnegative variance, with both
support points still strictly above that same projection threshold. This is
a feasibility statement for the tilt moments, not the full true-cone test. -/
theorem exists_projected_twoPoint (p₁ p₂ m V : ℝ)
    (hP : 2 < p₁ + p₂ * m) (hV : 0 ≤ V) :
    ∃ q : TwoPoint, q.IsProbability ∧ q.mean = m ∧ q.centeredSecond m = V ∧
      2 < p₁ + p₂ * q.leftValue ∧ 2 < p₁ + p₂ * q.rightValue := by
  by_cases hp : p₂ = 0
  · refine ⟨symmetricPair m V, symmetricPair_probability m V,
      symmetricPair_mean m V, symmetricPair_variance m V hV, ?_, ?_⟩ <;>
      simpa only [hp, zero_mul, add_zero] using hP
  · let d := (p₁ + p₂ * m - 2) / 2
    have hd : 0 < d := by dsimp [d]; linarith
    refine ⟨oneSidedPair m p₂ d V, oneSidedPair_probability m p₂ d V hd hV,
      oneSidedPair_mean m p₂ d V hp hd hV,
      oneSidedPair_variance m p₂ d V hp hd hV, ?_, ?_⟩
    · have hleft := oneSidedPair_lower_projection m p₂ d V hp
      dsimp [d] at hleft
      linarith
    · have hright := oneSidedPair_upper_projection m p₂ d V
      have hinc : 0 ≤ V * p₂ ^ 2 / d :=
        div_nonneg (mul_nonneg hV (sq_nonneg p₂)) (le_of_lt hd)
      linarith

/-- The cutoff correction used by the manuscript remains between the old
speed and the target speed whenever the old speed is below that target. -/
theorem corrected_speed_bounds (v₀ vstar ζ : ℝ)
    (hz₀ : 0 ≤ ζ) (hz₁ : ζ ≤ 1) (hv : v₀ ≤ vstar) :
    v₀ ≤ v₀ + ζ ^ 2 * (vstar - v₀) ∧
      v₀ + ζ ^ 2 * (vstar - v₀) ≤ vstar := by
  have hs : ζ ^ 2 ≤ 1 := by nlinarith
  have hlow := mul_nonneg (sq_nonneg ζ) (sub_nonneg.mpr hv)
  have hupp := mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hv)
  constructor <;> nlinarith

end

end NavierStokes.LoopMoments
