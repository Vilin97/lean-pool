/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SlowFactorBoundsSums
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.ErgodicParams

/-! From the actual Amnr spatial word calculus to the Appendix C predicates. -/

@[expose] public section

noncomputable section
open scoped ContDiff ENNReal
open MeasureTheory Homogenization AVenhance.FaaDiBruno
open AVenhance.Infra.Section4 AVenhance.Infra.Ergodic AVenhance.Infra.Torus
namespace AVenhance.Infra.Section5

theorem slowFactor_word_ofFn_eq_spatialJet {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ ∞ f) (n : ℕ) (w : Fin n → Fin 2) :
    amnrSpaceWord (List.ofFn w) f = spatialJet n f w := by
  induction n with
  | zero => funext x; rfl
  | succ n ih =>
    rw [List.ofFn_succ, amnrSpaceWord, ih]
    funext x
    have hd := hf.differentiable_iteratedFDeriv (m := n)
      (by exact_mod_cast ENat.natCast_lt_top n) x
    rw [spatialJet, hd.iteratedFDeriv_succ_apply_left']
    rfl

theorem slowFactor_spatialJet_realCast {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ ∞ f) (n : ℕ) (w : Fin n → Fin 2) (x : Vec 2) :
    spatialJet n (fun y => (f y : ℂ)) w x = (spatialJet (F := ℝ) n f w x : ℂ) := by
  have hh := Complex.ofRealCLM.iteratedFDeriv_comp_left (hf.contDiffAt (x := x))
    (i := n) (by simp)
  change iteratedFDeriv ℝ n (Complex.ofRealCLM ∘ f) x _ = _
  rw [hh]
  rfl

/-- Full mixed bounds, rather than the weaker pure-coordinate predicate,
feed the sharp averaged composition theorem. -/
theorem slowFactor_hasCoordinateAnalyticL2Bounds_comp
    (X : PeriodicVolumePreservingDiffeomorphism 2) {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ ∞ f) (hper : IsZPeriodic f)
    {F L CX R : ℝ} (hF : 0 ≤ F) (hL : 0 < L) (hCX : 0 < CX) (hR : 0 < R)
    (hb : ∀ w, eLpNorm (amnrSpaceWord w f) 2 (volume.restrict (unitCell 2)) ≤
      ENNReal.ofReal (F * w.length.factorial * L ^ w.length))
    (hX : ∀ n (w : Fin n → Fin 2), 0 < n → ∀ x j,
      |(spatialJet n X.toFun w x) j| ≤ CX * n.factorial * R ^ n) :
    HasCoordinateAnalyticL2Bounds (fun x => (f (X.toFun x) : ℂ)) F
      (L⁻¹ / (R * (L⁻¹ + 2 * CX))) := by
  have hfc : ContDiff ℝ ∞ (fun x => (f x : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hpc : IsZdPeriodic (fun x => (f x : ℂ)) := by
    intro k x
    exact congrArg (fun a : ℝ => (a : ℂ)) (hper x k)
  apply hasCoordinateAnalyticL2Bounds_comp_of_mixed_bounds (by norm_num) X
    hF (inv_pos.mpr hL) hCX hR hfc hpc _ hX
  intro n w
  have he : eLpNorm (spatialJet n (fun x => (f x : ℂ)) w) 2
      (volume.restrict (unitCell 2)) =
      eLpNorm (amnrSpaceWord (List.ofFn w) f) 2 (volume.restrict (unitCell 2)) := by
    apply eLpNorm_congr_norm_ae
      (spatialJet_continuous hfc w).aestronglyMeasurable.restrict
      (slowWord_smooth hf (List.ofFn w)).continuous.aestronglyMeasurable.restrict
    apply Filter.Eventually.of_forall
    intro x
    rw [slowFactor_spatialJet_realCast hf, slowFactor_word_ofFn_eq_spatialJet hf]
    exact Complex.norm_real _
  have hh := hb (List.ofFn w)
  rw [← he, spatialJet_eLpNorm_two_eq hfc] at hh
  simp only [List.length_ofFn] at hh
  have ht := (ENNReal.ofReal_le_ofReal_iff (by positivity :
    0 ≤ F * n.factorial * L ^ n)).mp hh
  simpa only [inv_pow, div_inv_eq_mul] using ht

end AVenhance.Infra.Section5
