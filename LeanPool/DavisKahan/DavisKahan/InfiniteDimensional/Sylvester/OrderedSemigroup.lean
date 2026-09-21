/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.Sylvester.FourierSemigroup
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SpectralOrder
import Mathlib.MeasureTheory.Integral.ExpDecay
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic


/-!
# Ordered-spectrum Sylvester reconstruction

For bounded self-adjoint complex operators whose spectra are ordered by a
positive gap, the Sylvester solution is the Laplace integral

`X = integral over t >= 0 of exp(-t A) C exp(t B)`.

The proof differentiates `exp(-t A) X exp(t B)`, integrates on a finite
interval, and lets the endpoint tend to infinity.  The spectral order gives
exponential decay.  This is the constant-one branch of the Sylvester theory;
it is logically different from the two-sided Fourier branch, whose universal
constant is `pi/2`.
-/

namespace TauCeti

open TauCeti
namespace DavisKahan.Sylvester

open TauCeti.DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open MeasureTheory Set Filter
open scoped InnerProductSpace Topology

noncomputable section

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- A common cut between two compact ordered spectra. -/
theorem exists_common_cut_of_orderedSeparation
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    (_hA : A.IsSymmetric) (_hB : B.IsSymmetric)
    {d : ℝ} (_hd : 0 < d)
    (hsep : OrderedSpectraSeparated B ⊤ A ⊤ d) :
    ∃ c : ℝ,
      realSpectrum B ⊆ Set.Iic c ∧
      realSpectrum A ⊆ Set.Ici (c + d) := by
  obtain ⟨hInvB, hInvA, hord⟩ := hsep
  have hkey : ∀ b ∈ realSpectrum B, ∀ a ∈ realSpectrum A, b + d ≤ a := by
    intro b hb a ha
    exact hord b ⟨hInvB, (ContinuousLinearMap.spectrum_restrict_top B hInvB).symm.subset hb⟩
      a ⟨hInvA, (ContinuousLinearMap.spectrum_restrict_top A hInvA).symm.subset ha⟩
  rcases (realSpectrum B).eq_empty_or_nonempty with hB0 | hBne
  · rcases (realSpectrum A).eq_empty_or_nonempty with hA0 | hAne
    · exact ⟨0, by simp [hB0], by simp [hA0]⟩
    · refine ⟨sInf (realSpectrum A) - d, by simp [hB0], fun a ha => ?_⟩
      have hbdd : BddBelow (realSpectrum A) := (realSpectrum_isCompact A).bddBelow
      have := csInf_le hbdd ha
      simp only [Set.mem_Ici]
      linarith
  · refine ⟨sSup (realSpectrum B), fun b hb => ?_, fun a ha => ?_⟩
    · exact le_csSup (realSpectrum_isCompact B).bddAbove hb
    · have hsup : sSup (realSpectrum B) ≤ a - d :=
        csSup_le hBne fun b hb => by linarith [hkey b hb a ha]
      simp only [Set.mem_Ici]
      linarith
/-- Functional-calculus formula for the bounded exponential group. -/
theorem semigroup_eq_cfc
    (T : E →L[ℂ] E) (hT : T.IsSymmetric) (t : ℝ) :
    semigroup T t = cfc (fun z : ℂ => Complex.exp (t * z)) T := by
  have hsa : IsSelfAdjoint T :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT
  have hst : IsStarNormal T := hsa.isStarNormal
  have hsmul : IsSelfAdjoint ((t : ℂ) • T) := by
    rw [isSelfAdjoint_iff, star_smul, hsa.star_eq, Complex.star_def,
      Complex.conj_ofReal]
  rw [cfc_comp_const_mul (t : ℂ) Complex.exp T
      Complex.continuous_exp.continuousOn hst,
    CFC.complex_exp_eq_normedSpace_exp hsmul.isStarNormal]
  rfl
/-- Upper spectral bound for a self-adjoint exponential. -/
theorem norm_semigroup_le_of_spectrum_subset_Iic
    (T : E →L[ℂ] E) (hT : T.IsSymmetric)
    {c t : ℝ} (ht : 0 ≤ t)
    (hσ : realSpectrum T ⊆ Set.Iic c) :
    ‖semigroup T t‖ ≤ Real.exp (t * c) := by
  rw [semigroup_eq_cfc T hT t]
  have hsa : IsSelfAdjoint T :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT
  refine norm_cfc_le (Real.exp_pos _).le fun z hz => ?_
  have hzre : z = z.re := hsa.mem_spectrum_eq_re hz
  have hmem : z.re ∈ realSpectrum T := by
    show ((z.re : ℝ) : ℂ) ∈ spectrum ℂ T
    rw [← hzre]
    exact hz
  have hle : z.re ≤ c := hσ hmem
  calc
    ‖Complex.exp (t * z)‖ = Real.exp ((↑t * z).re) := Complex.norm_exp _
    _ = Real.exp (t * z.re) := by
        rw [Complex.mul_re]
        simp
    _ ≤ Real.exp (t * c) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hle ht)

/-- Lower spectral bound, written as decay of `exp(-t T)`. -/
theorem norm_semigroup_neg_le_of_spectrum_subset_Ici
    (T : E →L[ℂ] E) (hT : T.IsSymmetric)
    {c t : ℝ} (ht : 0 ≤ t)
    (hσ : realSpectrum T ⊆ Set.Ici c) :
    ‖semigroup (-T) t‖ ≤ Real.exp (-t * c) := by
  have hsa : IsSelfAdjoint T :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT
  have hTneg : (-T).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa.neg
  have hσneg : realSpectrum (-T) ⊆ Set.Iic (-c) := by
    intro r hr
    have hmem : (-r) ∈ realSpectrum T := by
      show ((-r : ℝ) : ℂ) ∈ spectrum ℂ T
      have h1 : ((r : ℝ) : ℂ) ∈ -spectrum ℂ T := by
        rw [spectrum.neg_eq]
        exact hr
      have h2 : -((r : ℝ) : ℂ) ∈ spectrum ℂ T := Set.mem_neg.mp h1
      simpa using h2
    have hcr : c ≤ -r := hσ hmem
    exact Set.mem_Iic.mpr (by linarith)
  have := norm_semigroup_le_of_spectrum_subset_Iic (-T) hTneg ht hσneg
  calc
    ‖semigroup (-T) t‖ ≤ Real.exp (t * -c) := this
    _ = Real.exp (-t * c) := by ring_nf

/-- The ordered semigroup integrand has the sharp exponential majorant. -/
theorem orderedSemigroup_integrand_bound
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {d : ℝ} (hd : 0 < d)
    (hsep : OrderedSpectraSeparated B ⊤ A ⊤ d)
    (C : E →L[ℂ] F) :
    ∀ t ≥ 0,
      ‖semigroup (-A) t ∘L C ∘L semigroup B t‖ ≤
        Real.exp (-d * t) * ‖C‖ := by
  obtain ⟨c, hBc, hAc⟩ :=
    exists_common_cut_of_orderedSeparation hA hB hd hsep
  intro t ht
  have hleft := norm_semigroup_neg_le_of_spectrum_subset_Ici A hA ht hAc
  have hright := norm_semigroup_le_of_spectrum_subset_Iic B hB ht hBc
  calc
    ‖semigroup (-A) t ∘L C ∘L semigroup B t‖
        ≤ ‖semigroup (-A) t‖ * ‖C‖ * ‖semigroup B t‖ := by
          refine ((semigroup (-A) t).opNorm_comp_le (C ∘L semigroup B t)).trans ?_
          rw [mul_assoc]
          gcongr
          exact C.opNorm_comp_le (semigroup B t)
    _ ≤ Real.exp (-t * (c + d)) * ‖C‖ * Real.exp (t * c) := by
      gcongr
    _ = Real.exp (-d * t) * ‖C‖ := by
      rw [mul_right_comm, ← Real.exp_add,
        show -t * (c + d) + t * c = -d * t from by ring]

/-- Bochner integrability of the ordered semigroup formula on the half
line. -/
theorem orderedSylvester_integrableOn
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {d : ℝ} (hd : 0 < d)
    (hsep : OrderedSpectraSeparated B ⊤ A ⊤ d)
    (C : E →L[ℂ] F) :
    IntegrableOn
      (fun t : ℝ => semigroup (-A) t ∘L C ∘L semigroup B t) (Set.Ici 0) := by
  have hcont : Continuous fun t : ℝ => semigroup (-A) t ∘L C ∘L semigroup B t :=
    (continuous_semigroup (-A)).clm_comp
      (continuous_const.clm_comp (continuous_semigroup B))
  have hmaj := orderedSemigroup_integrand_bound hA hB hd hsep C
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-d * t)) (Set.Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact exp_neg_integrableOn_Ioi 0 hd
  have hgint : IntegrableOn (fun t : ℝ => Real.exp (-d * t) * ‖C‖)
      (Set.Ici 0) := hexp.mul_const ‖C‖
  refine hgint.mono' hcont.aestronglyMeasurable.restrict ?_
  refine (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mpr ?_
  filter_upwards with t ht
  exact hmaj t ht

/-- Bochner integrability of the ordered semigroup formula. -/
theorem orderedSylvester_integrable
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {d : ℝ} (hd : 0 < d)
    (hsep : OrderedSpectraSeparated B ⊤ A ⊤ d)
    (C : E →L[ℂ] F) :
    Integrable fun t : ℝ => Set.indicator (Set.Ici 0)
      (fun t => semigroup (-A) t ∘L C ∘L semigroup B t) t := by
  have h2 : @IntegrableOn ℝ (E →L[ℂ] F) _ _
      ESeminormedAddMonoid.toContinuousENorm
      (fun t => semigroup (-A) t ∘L C ∘L semigroup B t) (Set.Ici 0) volume :=
    orderedSylvester_integrableOn hA hB hd hsep C
  exact h2.integrable_indicator measurableSet_Ici

/-- Derivative of the conjugated solution orbit. -/
theorem hasDerivAt_ordered_solution_orbit
    (A : F →L[ℂ] F) (B : E →L[ℂ] E) (X C : E →L[ℂ] F)
    (hEq : A ∘L X - X ∘L B = C) (t : ℝ) :
    HasDerivAt
      (fun s => semigroup (-A) s ∘L X ∘L semigroup B s)
      (-(semigroup (-A) t ∘L C ∘L semigroup B t)) t := by
  have hU : HasDerivAt (fun s : ℝ => semigroup (-A) s)
      ((-A) ∘L semigroup (-A) t) t := hasDerivAt_semigroup (-A) t
  have hW : HasDerivAt (fun s : ℝ => X ∘L semigroup B s)
      ((ContinuousLinearMap.restrictScalars ℝ
        (ContinuousLinearMap.compL ℂ E E F X)) (B ∘L semigroup B t)) t := by
    have h_clm : HasFDerivAt (fun S : E →L[ℂ] E => X.comp S)
        (ContinuousLinearMap.compL ℂ E E F X) (semigroup B t) :=
      (ContinuousLinearMap.compL ℂ E E F X).hasFDerivAt
    exact (h_clm.restrictScalars ℝ).comp_hasDerivAt t (hasDerivAt_semigroup B t)
  have hb : IsBoundedBilinearMap ℂ
      (fun p : (F →L[ℂ] F) × (E →L[ℂ] F) => p.1.comp p.2) :=
    isBoundedBilinearMap_comp
  have hfd := ((hb.hasFDerivAt
      (semigroup (-A) t, X ∘L semigroup B t)).restrictScalars ℝ).comp_hasDerivAt t
    (hU.prodMk hW)
  have hpt : ∀ w, (-A) ((semigroup (-A) t) w) = (semigroup (-A) t) ((-A) w) := by
    intro w
    have h := (commute_semigroup (-A) t).eq
    exact congrFun (congrArg DFunLike.coe h) w
  have hfd' : HasDerivAt (fun s => semigroup (-A) s ∘L X ∘L semigroup B s)
      ((ContinuousLinearMap.restrictScalars ℝ
          (hb.deriv (semigroup (-A) t, X ∘L semigroup B t)))
        ((-A) ∘L semigroup (-A) t,
          (ContinuousLinearMap.restrictScalars ℝ
            (ContinuousLinearMap.compL ℂ E E F X)) (B ∘L semigroup B t))) t := hfd
  have hval : ((ContinuousLinearMap.restrictScalars ℝ
          (hb.deriv (semigroup (-A) t, X ∘L semigroup B t)))
        ((-A) ∘L semigroup (-A) t,
          (ContinuousLinearMap.restrictScalars ℝ
            (ContinuousLinearMap.compL ℂ E E F X)) (B ∘L semigroup B t))) =
      -(semigroup (-A) t ∘L C ∘L semigroup B t) := by
    rw [← hEq]
    ext v
    show (semigroup (-A) t) (X (B ((semigroup B t) v))) +
        (-A) ((semigroup (-A) t) (X ((semigroup B t) v))) =
      -((semigroup (-A) t) ((A ∘L X - X ∘L B) ((semigroup B t) v)))
    have h1 : (-A) ((semigroup (-A) t) (X ((semigroup B t) v))) =
        -((semigroup (-A) t) (A (X ((semigroup B t) v)))) := by
      rw [hpt]
      simp
    rw [h1]
    simp only [sub_apply, ContinuousLinearMap.comp_apply,
      map_sub]
    abel
  exact hval ▸ hfd'

/-- Finite-interval fundamental theorem for the ordered orbit. -/
theorem ordered_orbit_sub_eq_integral
    (A : F →L[ℂ] F) (B : E →L[ℂ] E) (X C : E →L[ℂ] F)
    (hEq : A ∘L X - X ∘L B = C) {T : ℝ} (hT : 0 ≤ T) :
    X - semigroup (-A) T ∘L X ∘L semigroup B T =
      ∫ t in Set.Icc (0 : ℝ) T,
        semigroup (-A) t ∘L C ∘L semigroup B t := by
  have hcont : Continuous fun s : ℝ => semigroup (-A) s ∘L C ∘L semigroup B s :=
    (continuous_semigroup (-A)).clm_comp
      (continuous_const.clm_comp (continuous_semigroup B))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s => semigroup (-A) s ∘L X ∘L semigroup B s)
    (f' := fun s => -(semigroup (-A) s ∘L C ∘L semigroup B s))
    (a := 0) (b := T)
    (fun s _ => hasDerivAt_ordered_solution_orbit A B X C hEq s)
    (hcont.neg.intervalIntegrable 0 T)
  rw [intervalIntegral.integral_neg] at hftc
  have hzero : semigroup (-A) 0 ∘L X ∘L semigroup B 0 = X := by
    rw [semigroup_zero, semigroup_zero]
    ext v
    rfl
  rw [hzero] at hftc
  have hval : (∫ s in (0 : ℝ)..T, semigroup (-A) s ∘L C ∘L semigroup B s) =
      X - semigroup (-A) T ∘L X ∘L semigroup B T := by
    have := congrArg Neg.neg hftc
    simpa [neg_sub] using this
  rw [← hval, intervalIntegral.integral_of_le hT,
    MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- The conjugated endpoint tends to zero under an ordered gap. -/
theorem tendsto_ordered_solution_orbit_zero
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {d : ℝ} (hd : 0 < d)
    (hsep : OrderedSpectraSeparated B ⊤ A ⊤ d)
    (X : E →L[ℂ] F) :
    Tendsto (fun t : ℝ => semigroup (-A) t ∘L X ∘L semigroup B t)
      atTop (nhds 0) := by
  have hbound := orderedSemigroup_integrand_bound hA hB hd hsep X
  have hev : ∀ᶠ t in (atTop : Filter ℝ),
      ‖semigroup (-A) t ∘L X ∘L semigroup B t‖ ≤ Real.exp (-d * t) * ‖X‖ := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    exact hbound t ht
  refine squeeze_zero_norm' hev ?_
  have h1 : Tendsto (fun t : ℝ => Real.exp (-d * t)) atTop (nhds 0) := by
    have h2 : Tendsto (fun t : ℝ => d * t) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hd tendsto_id
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp h2
    simpa [Function.comp_def, neg_mul] using this
  simpa using h1.mul_const ‖X‖

/-- Exact ordered-spectrum reconstruction. -/
theorem orderedSylvester_reconstruction
    {A : F →L[ℂ] F} {B : E →L[ℂ] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {d : ℝ} (hd : 0 < d)
    (hsep : OrderedSpectraSeparated B ⊤ A ⊤ d)
    {X C : E →L[ℂ] F}
    (hEq : A ∘L X - X ∘L B = C) :
    X = ∫ t : ℝ, Set.indicator (Set.Ici 0)
      (fun t => semigroup (-A) t ∘L C ∘L semigroup B t) t := by
  have hIci := orderedSylvester_integrableOn hA hB hd hsep C
  have hIoi : IntegrableOn
      (fun t : ℝ => semigroup (-A) t ∘L C ∘L semigroup B t) (Set.Ioi 0) :=
    hIci.mono_set Set.Ioi_subset_Ici_self
  have hlim1 : Tendsto
      (fun T : ℝ => ∫ t in (0 : ℝ)..T, semigroup (-A) t ∘L C ∘L semigroup B t)
      atTop (nhds (∫ t in Set.Ioi 0, semigroup (-A) t ∘L C ∘L semigroup B t)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0 hIoi tendsto_id
  have hlim2 : Tendsto
      (fun T : ℝ => ∫ t in (0 : ℝ)..T, semigroup (-A) t ∘L C ∘L semigroup B t)
      atTop (nhds X) := by
    have horb : Tendsto
        (fun T : ℝ => X - semigroup (-A) T ∘L X ∘L semigroup B T)
        atTop (nhds X) := by
      have := tendsto_const_nhds (x := X) (f := (atTop : Filter ℝ)) |>.sub
        (tendsto_ordered_solution_orbit_zero hA hB hd hsep X)
      simpa using this
    refine horb.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with T hT
    rw [intervalIntegral.integral_of_le hT,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    exact ordered_orbit_sub_eq_integral A B X C hEq hT
  have hX : (∫ t in Set.Ioi 0, semigroup (-A) t ∘L C ∘L semigroup B t) = X :=
    tendsto_nhds_unique hlim1 hlim2
  rw [MeasureTheory.integral_indicator measurableSet_Ici,
    MeasureTheory.integral_Ici_eq_integral_Ioi, hX]

end

end DavisKahan.Sylvester
end TauCeti
