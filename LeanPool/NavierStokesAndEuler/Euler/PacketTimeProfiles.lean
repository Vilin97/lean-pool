/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketTimeProfileArithmetic
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.NatFactorial

/-! The actual continuous time weights for the high and mean packet grades. -/

@[expose] public section


noncomputable section

namespace EulerPacketTimeProfile

open Set

variable (K : Type*) [TopologicalSpace K]

/-- Scales data, collecting `growth`, `growth_pos`, `H0`, `H0_one_le`, `growth_le`. -/
structure Scales where
  /-- Growth of `Scales`, of type `C(K,ℝ)`. -/
  growth : C(K,ℝ)
  growth_pos : ∀ t, 0 < growth t
  /-- H0 of `Scales`, of type `ℝ`. -/
  H0 : ℝ
  H0_one_le : 1 ≤ H0
  growth_le : ∀ t, growth t ≤ H0

namespace Scales

variable {K}

/-- Compactness supplies the single grade-independent upper scale. -/
def ofGrowth [CompactSpace K] (g : C(K, ℝ)) (hg : ∀ t, 0 < g t) : Scales K where
  growth := g
  growth_pos := hg
  H0 := max 1 ‖g‖
  H0_one_le := le_max_left _ _
  growth_le t := (le_trans (le_abs_self (g t))
    (by simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm t)).trans (le_max_right _ _)

variable (S : Scales K)

/-- Mean, given by `ContinuousMap.const K (meanScale S.H0 p)`. -/
def mean (p : ℕ) : C(K,ℝ) := ContinuousMap.const K (meanScale S.H0 p)
/-- High, given by `S.growth*S.mean p`. -/
def high (p : ℕ) : C(K,ℝ) := S.growth*S.mean p

@[simp] theorem mean_apply (p : ℕ) (t : K) : S.mean p t = meanScale S.H0 p := rfl
@[simp] theorem high_apply (p : ℕ) (t : K) : S.high p t = highScale (S.growth t) S.H0 p := rfl

theorem H0_pos : 0 < S.H0 := zero_lt_one.trans_le S.H0_one_le
theorem mean_pos (p : ℕ) (t : K) : 0 < S.mean p t := meanScale_pos S.H0 S.H0_pos p
theorem high_pos (p : ℕ) (t : K) : 0 < S.high p t :=
  highScale_pos (S.growth t) S.H0 (S.growth_pos t) S.H0_pos p

theorem mean_mono {i j : ℕ} (hij : i ≤ j) (t : K) : S.mean i t ≤ S.mean j t :=
  meanScale_mono S.H0 S.H0_one_le hij

theorem high_mono {i j : ℕ} (hij : i ≤ j) (t : K) : S.high i t ≤ S.high j t :=
  highScale_mono (S.growth t) S.H0 (S.growth_pos t).le S.H0_one_le hij

theorem high_one (t : K) : S.high 1 t = S.growth t := by
  simp only [high_apply,highScale,meanScale,show 2*1-2=0 by omega,pow_zero,mul_one]

theorem slow_mean_mean_bound (i j p : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) (t : K) :
    S.mean i t*S.mean j t ≤ S.mean p t := slow_mean_mean S.H0 S.H0_one_le i j p hi hj hp

theorem slow_high_high_mean_bound (i j p : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) (t : K) :
    S.high i t*S.high j t ≤ S.mean p t :=
  slow_high_high_mean (S.growth t) S.H0 (S.growth_pos t).le (S.growth_le t) S.H0_one_le i j p hi hj
      hp

theorem slow_high_high_high_bound (i j p : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) (t : K) :
    S.high i t*S.high j t ≤ S.high p t :=
  slow_high_high_high (S.growth t) S.H0 (S.growth_pos t).le (S.growth_le t) S.H0_one_le i j p hi hj
      hp

theorem slow_mean_high_mean_bound (i j p : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) (t : K) :
    S.mean i t*S.high j t ≤ S.mean p t :=
  slow_mean_high_mean (S.growth t) S.H0 (S.growth_pos t).le (S.growth_le t) S.H0_one_le i j p hi hj
      hp

theorem slow_mean_high_high_bound (i j p : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p) (t : K) :
    S.mean i t*S.high j t ≤ S.high p t :=
  slow_mean_high_high (S.growth t) S.H0 (S.growth_pos t).le S.H0_one_le i j p hi hj hp

theorem fast_mean_high_bound (i j p : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hp : i + j = p + 1) (t : K) :
    S.mean i t*S.high j t = S.high p t :=
  fast_mean_high (S.growth t) S.H0 i j p hi hj hp

theorem fast_corrector_high_mean_bound (i j p : ℕ) (hi : 2 ≤ i) (hj : 1 ≤ j)
    (hp : i + j = p + 1) (t : K) : S.high (i-1) t*S.high j t ≤ S.mean p t :=
  fast_corrector_high_mean (S.growth t) S.H0 (S.growth_pos t).le (S.growth_le t)
    S.H0_one_le i j p hi hj hp

theorem fast_corrector_high_high_bound (i j p : ℕ) (hi : 2 ≤ i) (hj : 1 ≤ j)
    (hp : i + j = p + 1) (t : K) : S.high (i-1) t*S.high j t ≤ S.high p t :=
  fast_corrector_high_high (S.growth t) S.H0 (S.growth_pos t).le (S.growth_le t)
    S.H0_one_le i j p hi hj hp

theorem fast_corrector_corrector_mean_bound (i j p : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j)
    (hp : i + j = p + 1) (t : K) : S.high (i-1) t*S.high (j-1) t ≤ S.mean p t :=
  fast_corrector_corrector_mean (S.growth t) S.H0 (S.growth_pos t).le (S.growth_le t)
    S.H0_one_le i j p hi hj hp

theorem fast_corrector_corrector_high_bound (i j p : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j)
    (hp : i + j = p + 1) (t : K) : S.high (i-1) t*S.high (j-1) t ≤ S.high p t :=
  fast_corrector_corrector_high (S.growth t) S.H0 (S.growth_pos t).le (S.growth_le t)
    S.H0_one_le i j p hi hj hp

theorem previous_linear_mean_bound (p : ℕ) (hp : 2 ≤ p) (t : K) : S.high (p-1) t ≤ S.mean p t :=
  previous_linear_mean (S.growth t) S.H0 (S.growth_pos t).le (S.growth_le t) S.H0_one_le p hp

end Scales
end EulerPacketTimeProfile
