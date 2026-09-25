/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Minkowski

/-! # Component bounds for Euclidean vector-source Morrey norms

The Euclidean norm is bounded by the sum of the three absolute coordinate
values. The scalar triangle inequality transfers this comparison to the
Morrey norm without changing either exponent.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

noncomputable section
namespace CKN.Core.Endgame

/-- The scalar Morrey triangle inequality for any integrability exponent at
least one. No restriction on the outer exponent is needed. -/
theorem morrey_norm_add_le {P τ : ℝ} (hP : 1 ≤ P)
    {f g : ParabolicPoint → ℝ}
    (hf : AEMeasurable f volume) (hg : AEMeasurable g volume) :
    morreyNorm P τ (fun z => f z + g z) ≤ morreyNorm P τ f + morreyNorm P τ g := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hPne : ENNReal.ofReal P ≠ 0 := (ENNReal.ofReal_pos.mpr hP0).ne'
  unfold morreyNorm
  refine iSup_le fun z => iSup_le fun r => ?_
  let μ := volume.restrict (parabolicCylinder z.1 z.2 r.1)
  have hfμ : AEStronglyMeasurable f μ := hf.aestronglyMeasurable.restrict
  have hgμ : AEStronglyMeasurable g μ := hg.aestronglyMeasurable.restrict
  have hsum := eLpNorm_add_le (μ := μ) (f := f) (g := g) (p := ENNReal.ofReal P)
    (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hP)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hPne ENNReal.ofReal_ne_top (hfμ.add hgμ),
    eLpNorm_eq_lintegral_rpow_enorm_toReal hPne ENNReal.ofReal_ne_top hfμ,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hPne ENNReal.ofReal_ne_top hgμ] at hsum
  have hsum' : cylinderPowerIntegral P (fun w => f w + g w) z r.1 ^ (1 / P) ≤
      cylinderPowerIntegral P f z r.1 ^ (1 / P) +
        cylinderPowerIntegral P g z r.1 ^ (1 / P) := by
    simpa only [ENNReal.toReal_ofReal hP0.le, Real.enorm_eq_ofReal_abs,
      Pi.add_apply, one_div, μ, cylinderPowerIntegral] using hsum
  have hcell : morreyCell P τ (fun w => f w + g w) z r.1 ≤
      morreyCell P τ f z r.1 + morreyCell P τ g z r.1 := by
    unfold morreyCell
    rw [← mul_add]
    exact mul_le_mul_right hsum' _
  exact hcell.trans (add_le_add
    (le_iSup_of_le z (le_iSup (fun s : {s : ℝ // 0 < s} => morreyCell P τ f z s.1) r))
    (le_iSup_of_le z (le_iSup (fun s : {s : ℝ // 0 < s} => morreyCell P τ g z s.1) r)))

private theorem norm_le_sum_abs (v : Vec3) : vec3EuclideanNorm v ≤ ∑ i, |v i| := by
  rw [vec3EuclideanNorm]
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact Finset.sum_nonneg fun i _ => abs_nonneg _
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change v 0 ^ 2 + (v 1 ^ 2 + v 2 ^ 2) ≤
      (|v 0| + (|v 1| + |v 2|)) ^ 2
    nlinarith only [sq_abs (v 0), sq_abs (v 1), sq_abs (v 2),
      mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 1)),
      mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 2)),
      mul_nonneg (abs_nonneg (v 1)) (abs_nonneg (v 2))]

private theorem morrey_norm_abs (P τ : ℝ) (f : ParabolicPoint → ℝ) :
    morreyNorm P τ (fun z => |f z|) = morreyNorm P τ f := by
  simp only [morreyNorm, morreyCell, cylinderPowerIntegral, abs_abs]

/-- The Euclidean norm of a three-component source is bounded in Morrey norm
by the sum of its component Morrey norms, with constant one. -/
theorem morrey_norm_euclidean_le_sum_components {P τ : ℝ} (hP : 1 ≤ P)
    {g : ParabolicPoint → Vec3}
    (hg : ∀ i, AEMeasurable (fun z => g z i) volume) :
    morreyNorm P τ (fun z => vec3EuclideanNorm (g z)) ≤
      ∑ i, morreyNorm P τ (fun z => g z i) := by
  let f : Fin 3 → ParabolicPoint → ℝ := fun i z => |g z i|
  have hf : ∀ i, AEMeasurable (f i) volume := fun i =>
    continuous_abs.measurable.comp_aemeasurable (hg i)
  have h12 := morrey_norm_add_le (τ := τ) hP (hf 1) (hf 2)
  have hsum := (morrey_norm_add_le (τ := τ) hP (hf 0) ((hf 1).add (hf 2))).trans
    (add_le_add_right h12 (morreyNorm P τ (f 0)))
  have hmono : morreyNorm P τ (fun z => vec3EuclideanNorm (g z)) ≤
      morreyNorm P τ (fun z => ∑ i, |g z i|) := by
    apply morreyNorm_mono (zero_le_one.trans hP)
    intro z
    rw [abs_of_nonneg (vec3EuclideanNorm_nonneg _),
      abs_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)]
    exact norm_le_sum_abs _
  apply hmono.trans
  have habs : ∀ i, morreyNorm P τ (f i) = morreyNorm P τ (fun z => g z i) :=
    fun i => morrey_norm_abs P τ _
  simpa [Fin.sum_univ_succ, Pi.add_apply, habs, f] using hsum

/-- Finite component Morrey norms give a finite Euclidean norm-source
Morrey norm at the same exponents. -/
theorem morrey_norm_euclidean_lt_top_of_components {P τ : ℝ} (hP : 1 ≤ P)
    {g : ParabolicPoint → Vec3}
    (hg : ∀ i, AEMeasurable (fun z => g z i) volume)
    (hN : ∀ i, morreyNorm P τ (fun z => g z i) < ∞) :
    morreyNorm P τ (fun z => vec3EuclideanNorm (g z)) < ∞ := by
  exact (morrey_norm_euclidean_le_sum_components hP hg).trans_lt
    (ENNReal.sum_lt_top.mpr fun i _ => hN i)

end CKN.Core.Endgame
