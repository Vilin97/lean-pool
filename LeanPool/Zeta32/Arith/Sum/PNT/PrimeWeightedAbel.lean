/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Arith.Sum.PNT.PrimeThetaInterval
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Zeta32 — Arith — Sum — PNT — PrimeWeightedAbel. -/

-- adapted from
-- dtq1997/li2-half-irrationality@d5d8206:Li2Unified/Modular/Base/PrimeWeightedAbel.lean
-- (namespace Li2 -> Zeta32.ArithSum, imports renamed; proof and style updated for Lean Pool)

public section

open Finset Filter Topology MeasureTheory Set Real Asymptotics
namespace Zeta32.ArithSum.PrimeSums
noncomputable section

export Zeta5Irrational (wsum wsum_eq theta_eventually_close)

lemma theta_eq_sum_Icc_cPrime (t : ℝ) :
    Chebyshev.theta t = ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, cPrime k :=
  Zeta5Irrational.theta_eq_sum_cPrime t

lemma integral_theta_bounds {a b ε : ℝ} (hab : a ≤ b)
    (h : ∀ y ∈ Set.Icc a b, |Chebyshev.theta y - y| ≤ ε * y) :
    |(∫ t in Set.Ioc a b, Chebyshev.theta t)-(b^2-a^2)/2| ≤ ε*(b^2-a^2)/2 := by
  have hint : IntegrableOn Chebyshev.theta (Set.Ioc a b) :=
    (Chebyshev.theta_mono.intervalIntegrable (μ := volume) (a := a) (b := b)).1
  have hsub : IntegrableOn (fun t : ℝ => t) (Set.Ioc a b) :=
    (continuous_id.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hid : ∫ t in Set.Ioc a b, t = (b^2-a^2)/2 := by
    rw [← intervalIntegral.integral_of_le hab, integral_id]
  have hε : IntegrableOn (fun t : ℝ => ε*t) (Set.Ioc a b) := hsub.const_mul ε
  calc
    |(∫ t in Set.Ioc a b, Chebyshev.theta t)-(b^2-a^2)/2| =
        ‖∫ t in Set.Ioc a b, (Chebyshev.theta t-t)‖ := by
      rw [← hid, ← integral_sub hint hsub, Real.norm_eq_abs]
    _ ≤ ∫ t in Set.Ioc a b, ‖Chebyshev.theta t-t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Set.Ioc a b, ε*t := by
      refine setIntegral_mono_on (hint.sub hsub).norm hε measurableSet_Ioc fun t ht => ?_
      rw [Real.norm_eq_abs]
      exact h t (Ioc_subset_Icc_self ht)
    _ = ε*(b^2-a^2)/2 := by rw [integral_const_mul, hid]; ring

lemma wsum_close {a b η : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hη : 0 ≤ η)
    (h : ∀ y ∈ Set.Icc a b, |Chebyshev.theta y - y| ≤ η * y) :
    |wsum a b - (b ^ 2 - a ^ 2) / 2| ≤ 2 * η * b ^ 2 :=
  Zeta5Irrational.wsum_close ha hab hη h

end
end Zeta32.ArithSum.PrimeSums

end
