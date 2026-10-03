/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.AveragedCompositionEstimate

/-! Appendix C composition in L1 and L2, retaining the same averaged norm.
Only the L2 input includes order zero. -/

@[expose] public section

noncomputable section
open scoped ContDiff ENNReal
open MeasureTheory Homogenization AVenhance.FaaDiBruno AVenhance.Infra.Torus
namespace AVenhance.Infra.Ergodic

theorem spatialJet_eLpNorm_two_eq {d n : ℕ} {f : Vec d → ℂ}
    (hf : ContDiff ℝ ∞ f) (w : Fin n → Fin d) :
    eLpNorm (spatialJet n f w) 2 (volume.restrict (unitCell d)) =
      ENNReal.ofReal ((∫ x in unitCell d, ‖spatialJet n f w x‖ ^ 2) ^ (1 / 2 : ℝ)) := by
  have hm := continuous_unitCell_memLp (spatialJet_continuous hf w) 2
  rw [hm.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, one_div]

/-- Full mixed L2 input, including zero, gives the composed L2
predicate without any pointwise bound on the outer function. -/
theorem hasCoordinateAnalyticL2Bounds_comp_of_mixed_bounds {d : ℕ} (hd : 0 < d)
    (X : PeriodicVolumePreservingDiffeomorphism d) {Cf r CX R : ℝ}
    (hCf : 0 ≤ Cf) (hr : 0 < r) (hCX : 0 < CX) (hR : 0 < R)
    {f : Vec d → ℂ} (hf : ContDiff ℝ ∞ f) (hper : IsZdPeriodic f)
    (hfbound : ∀ n (w : Fin n → Fin d),
      (∫ x in unitCell d, ‖spatialJet n f w x‖ ^ 2) ^ (1 / 2 : ℝ) ≤
        Cf * n.factorial / r ^ n)
    (hXbound : ∀ n (w : Fin n → Fin d), 0 < n → ∀ x j,
      |(spatialJet n X.toFun w x) j| ≤ CX * n.factorial * R ^ n) :
    HasCoordinateAnalyticL2Bounds (f ∘ X.toFun) Cf
      (r / (R * (r + (d : ℝ) * CX))) := by
  intro i n
  have hdim : 0 ≤ (d : ℝ) := by exact_mod_cast hd.le
  have hrad : 0 < r / (R * (r + (d : ℝ) * CX)) := by positivity
  have hb : ∀ k (w : Fin k → Fin d),
      eLpNorm (spatialJet k f w) 2 (volume.restrict (unitCell d)) ≤
        ENNReal.ofReal (Cf * k.factorial / r ^ k) := by
    intro k w
    rw [spatialJet_eLpNorm_two_eq hf w]
    exact ENNReal.ofReal_le_ofReal (hfbound k w)
  have hh : eLpNorm (spatialJet n (f ∘ X.toFun) (fun _ => i)) 2
      (volume.restrict (unitCell d)) ≤
      ENNReal.ofReal (Cf * n.factorial /
        (r / (R * (r + (d : ℝ) * CX))) ^ n) := by
    by_cases hn : n = 0
    · subst n
      have hzero : spatialJet 0 f (fun i => Fin.elim0 i) = f := by
        funext x
        rfl
      have hzeroComp : spatialJet 0 (f ∘ X.toFun) (fun _ => i) = f ∘ X.toFun := by
        funext x
        rfl
      rw [hzeroComp]
      simpa only [Nat.factorial_zero, Nat.cast_one, pow_zero, mul_one, div_one] using
        (eLpNorm_comp_flow_eq hf.continuous hper X (p := 2) (by norm_num) (by norm_num)).le.trans
          (by simpa only [hzero, Nat.factorial_zero, Nat.cast_one, pow_zero, mul_one, div_one]
            using hb 0 (fun i => Fin.elim0 i))
    · exact spatialJet_comp_eLpNorm_le (Nat.pos_of_ne_zero hn) X hf hper hCf hr hCX.le hR.le
        (p := 2) (by norm_num) (by norm_num) (fun k w _ => hb k w) hXbound (fun _ => i)
  rw [spatialJet_eLpNorm_two_eq (hf.comp X.contDiff_toFun),
    spatialJet_const_eq_coordDerivIter (hf.comp X.contDiff_toFun)] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity :
    0 ≤ Cf * n.factorial / (r / (R * (r + (d : ℝ) * CX))) ^ n)).mp hh

end AVenhance.Infra.Ergodic
