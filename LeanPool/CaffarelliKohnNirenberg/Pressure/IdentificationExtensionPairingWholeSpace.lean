/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionPairingExterior
public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionPairingSlice
public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationWholeSpace

/-!
# The whole-space distributional identity for the leading pressure term

The localized identity for `p₁` tests against spatial test functions supported in
the solution domain.  Splitting an arbitrary compactly supported smooth test
function `ψ` with an auxiliary cut-off `χ` that equals one on a neighbourhood of
`tsupport η` and is supported in the domain writes `ψ = χψ + (1 - χ)ψ`: the first
piece is admissible for the localized identity, and the second piece vanishes on
a neighbourhood of `tsupport η`, so both sides of the identity vanish on it.
The result is the identity tested against every compactly supported smooth `ψ`,
which is the form the Liouville identification consumes.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- A compact set inside an open set carries a smooth compactly supported cut-off
that is identically one on an open neighbourhood of the compact set and is
supported in the open set. -/
theorem exists_cutoff_eqOn_one_of_isCompact {K U : Set Vec3}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : Vec3 → ℝ, ∃ V : Set Vec3,
      ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
        IsOpen V ∧ K ⊆ V ∧ Set.EqOn χ (fun _ => (1 : ℝ)) V := by
  obtain ⟨V, hVopen, hKV, hVU, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨W, hWopen, hVW, hWU, hWc⟩ :=
    exists_open_between_and_isCompact_closure hVc hU hVU
  obtain ⟨χ, hχsmooth, _hχrange, hχsupport, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hWopen isClosed_closure hVW
  have hts : tsupport χ = closure W := by rw [tsupport, hχsupport]
  refine ⟨χ, V, hχsmooth, ?_, ?_, hVopen, hKV, ?_⟩
  · rw [HasCompactSupport, hts]
    exact hWc
  · rw [hts]
    exact hWU
  · intro x hx
    exact (hχone x).mp (subset_closure hx)

/-- Additivity of the first spatial derivative on smooth functions. -/
theorem spatialDeriv_add_smooth {F G : Vec3 → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (i : Fin 3) :
    spatialDeriv (fun y => F y + G y) i =
      fun x => spatialDeriv F i x + spatialDeriv G i x := by
  funext x
  exact spatialDeriv_add (hF.differentiable (by simp) x)
    (hG.differentiable (by simp) x) i

/-- Additivity of the mixed second spatial derivative on smooth functions. -/
theorem mixedSecond_add_smooth {F G : Vec3 → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (i j : Fin 3) (x : Vec3) :
    mixedSecond (fun y => F y + G y) i j x =
      mixedSecond F i j x + mixedSecond G i j x := by
  have hstep := spatialDeriv_add_smooth hF hG j
  simp only [mixedSecond]
  rw [hstep]
  exact spatialDeriv_add
    ((contDiff_spatialDeriv_smooth hF j).differentiable (by simp) x)
    ((contDiff_spatialDeriv_smooth hG j).differentiable (by simp) x) i

/-- Additivity of the spatial Laplacian on smooth functions. -/
theorem spatialLaplacian_add_smooth {F G : Vec3 → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (x : Vec3) :
    spatialLaplacian (fun y => F y + G y) x =
      spatialLaplacian F x + spatialLaplacian G x := by
  have h : ∀ i : Fin 3, spatialDeriv (spatialDeriv (fun y => F y + G y) i) i x =
      spatialDeriv (spatialDeriv F i) i x + spatialDeriv (spatialDeriv G i) i x :=
    fun i => mixedSecond_add_smooth hF hG i i x
  simp only [spatialLaplacian]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => h i

/-- The tensor pairing integrand is integrable on each admissible time slice. -/
theorem pressureCutoff_tensorPairing_integrable
    {η : Vec3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {s : ℝ}
    (hU : ∀ i j : Fin 3, IntegrableOn
      (fun y : Vec3 => pressureUTensor u c (y, s) i j) (tsupport η) volume)
    {φ : Vec3 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    Integrable (fun x => ∑ i, ∑ j, η x * pressureUTensor u c (x, s) i j *
      mixedSecond φ i j x) volume := by
  have hterm : ∀ i j : Fin 3, Integrable (fun x : Vec3 =>
      η x * pressureUTensor u c (x, s) i j * mixedSecond φ i j x) volume := by
    intro i j
    have hbase : Integrable
        (fun y : Vec3 => η y * pressureUTensor u c (y, s) i j) volume :=
      pressureCutoff_integrable_mul_of_tsupport_subset hη.continuous hηc
        (subset_refl _) (hU i j)
    obtain ⟨C, hC⟩ := (pressureCutoff_hasCompactSupport_mixedSecond hφc i j
      ).exists_bound_of_continuous (contDiff_mixedSecond_smooth hφ i j).continuous
    exact hbase.mul_bdd
      (contDiff_mixedSecond_smooth hφ i j).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => hC y)
  have hsum : ∀ i : Fin 3, Integrable (fun x : Vec3 => ∑ j, η x *
      pressureUTensor u c (x, s) i j * mixedSecond φ i j x) volume := by
    intro i
    simpa only [Finset.sum_apply] using
      MeasureTheory.integrable_finsetSum (Finset.univ : Finset (Fin 3))
        (fun j _ => hterm i j)
  simpa only [Finset.sum_apply] using
    MeasureTheory.integrable_finsetSum (Finset.univ : Finset (Fin 3))
      (fun i _ => hsum i)

/-- The whole-space distributional identity for the leading local pressure.  For
almost every time the pairing of `p₁(·, s)` against `Δψ` equals the tensor
pairing of `η U(·, s)` against the Hessian of `ψ`, now for an arbitrary smooth
compactly supported spatial test function `ψ`, with no support restriction. -/
theorem pressureP1_wholeSpace_pairing_ae_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {η : Vec3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηΩ : tsupport η ⊆ Ω) (c : ℝ → Vec3)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∀ᵐ s ∂volume.restrict I,
      ∫ x, pressureP1 η u c p f s x * spatialLaplacian ψ x =
        ∫ x, ∑ i, ∑ j, η x * pressureUTensor u c (x, s) i j *
          mixedSecond ψ i j x := by
  obtain ⟨χ, V, hχ, hχc, hχΩ, hVopen, hηV, hχV⟩ :=
    exists_cutoff_eqOn_one_of_isCompact hηc.isCompact hsol.1 hηΩ
  have hψ₁ : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => χ y * ψ y) := hχ.mul hψ
  have hψ₁c : HasCompactSupport (fun y : Vec3 => χ y * ψ y) :=
    hχc.mul_right (f' := ψ)
  have hψ₁Ω : tsupport (fun y : Vec3 => χ y * ψ y) ⊆ Ω :=
    (tsupport_mul_subset_left (f := χ) (g := ψ)).trans hχΩ
  have hψ₂ : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => ψ y - χ y * ψ y) := hψ.sub hψ₁
  have hψ₂c : HasCompactSupport (fun y : Vec3 => ψ y - χ y * ψ y) := by
    refine HasCompactSupport.intro hψc.isCompact fun x hx => ?_
    rw [image_eq_zero_of_notMem_tsupport hx]
    ring
  have hψ₂V : Set.EqOn (fun y : Vec3 => ψ y - χ y * ψ y)
      (fun _ => (0 : ℝ)) V := by
    intro y hy
    simp [hχV hy]
  have hsumfun : (fun y : Vec3 => χ y * ψ y + (ψ y - χ y * ψ y)) = ψ := by
    funext y
    ring
  have hL : ∀ x : Vec3, spatialLaplacian ψ x =
      spatialLaplacian (fun y : Vec3 => χ y * ψ y) x +
        spatialLaplacian (fun y : Vec3 => ψ y - χ y * ψ y) x := by
    intro x
    have hadd := spatialLaplacian_add_smooth hψ₁ hψ₂ x
    rw [hsumfun] at hadd
    exact hadd
  have hM : ∀ (i j : Fin 3), ∀ x : Vec3, mixedSecond ψ i j x =
      mixedSecond (fun y : Vec3 => χ y * ψ y) i j x +
        mixedSecond (fun y : Vec3 => ψ y - χ y * ψ y) i j x := by
    intro i j x
    have hadd := mixedSecond_add_smooth hψ₁ hψ₂ i j x
    rw [hsumfun] at hadd
    exact hadd
  have hid1 := pressureP1_distributional_identity_of_sws hsol hη hηc hηΩ (c := c)
    hψ₁ hψ₁c hψ₁Ω
  have hslice := pressureCutoff_slice_data_ae_of_sws hsol hηc hηΩ c
  filter_upwards [hid1, hslice] with s h1 hdata
  have hp₁loc : LocallyIntegrable (pressureP1 η u c p f s) volume :=
    pressureP1_slice_locallyIntegrable hη hηc hdata.1 hdata.2.1 hdata.2.2
  have hmulInt : ∀ {φ : Vec3 → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      Integrable (fun x => pressureP1 η u c p f s x * spatialLaplacian φ x)
        volume := by
    intro φ hφ hφc
    simpa only [smul_eq_mul] using
      hp₁loc.integrable_smul_right_of_hasCompactSupport
        (contDiff_spatialLaplacian_smooth hφ).continuous
        (CKN.Foundation.Heat.laplacian_compact_support_global hφc)
  have hext := pressureP1_pairing_eq_zero_of_eqOn_zero hη hηc hdata.1 hdata.2.1
    hdata.2.2 hψ₂ hψ₂c hVopen hηV hψ₂V
  have hexttensor := pressureCutoff_tensorPairing_eq_zero_of_eqOn_zero
    (η := η) (u := u) (c := c) (s := s) hVopen hηV hψ₂V
  have hLHS : ∫ x, pressureP1 η u c p f s x * spatialLaplacian ψ x =
      ∫ x, pressureP1 η u c p f s x *
        spatialLaplacian (fun y : Vec3 => χ y * ψ y) x := by
    have hpt : ∀ x : Vec3, pressureP1 η u c p f s x * spatialLaplacian ψ x =
        pressureP1 η u c p f s x *
            spatialLaplacian (fun y : Vec3 => χ y * ψ y) x +
          pressureP1 η u c p f s x *
            spatialLaplacian (fun y : Vec3 => ψ y - χ y * ψ y) x := by
      intro x
      rw [hL x]
      ring
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
      MeasureTheory.integral_add (hmulInt hψ₁ hψ₁c) (hmulInt hψ₂ hψ₂c), hext]
    ring
  have hRHS : ∫ x, ∑ i, ∑ j, η x * pressureUTensor u c (x, s) i j *
        mixedSecond ψ i j x =
      ∫ x, ∑ i, ∑ j, η x * pressureUTensor u c (x, s) i j *
        mixedSecond (fun y : Vec3 => χ y * ψ y) i j x := by
    have hpt : ∀ x : Vec3, (∑ i, ∑ j, η x * pressureUTensor u c (x, s) i j *
        mixedSecond ψ i j x) =
        (∑ i, ∑ j, η x * pressureUTensor u c (x, s) i j *
          mixedSecond (fun y : Vec3 => χ y * ψ y) i j x) +
        (∑ i, ∑ j, η x * pressureUTensor u c (x, s) i j *
          mixedSecond (fun y : Vec3 => ψ y - χ y * ψ y) i j x) := by
      intro x
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hM i j x]
      ring
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
      MeasureTheory.integral_add
        (pressureCutoff_tensorPairing_integrable hη hηc hdata.1 hψ₁ hψ₁c)
        (pressureCutoff_tensorPairing_integrable hη hηc hdata.1 hψ₂ hψ₂c),
      hexttensor]
    ring
  rw [hLHS, hRHS]
  exact h1

end CKN

end
