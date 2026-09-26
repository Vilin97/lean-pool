/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionPairingSwap
public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionPairingWholeSpace
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Identification

/-!
# The identification data for the leading pressure term

The Calderón--Zygmund bound for the leading local pressure `p₁` consumes two
facts about a fixed time slice: the whole-space distributional identity pairing
`p₁(·, s)` with `Δψ` against the tensor source `η U(·, s)`, and the integrability
of that pairing, both for *every* compactly supported smooth spatial test
function `ψ`.  The identity produced by the pressure decomposition holds, for
each fixed `ψ`, only for almost every time, with an exceptional set depending on
`ψ`.  Testing against the countable family of mollifier bumps removes that
dependence, and the two facts below hold, for almost every time, simultaneously
for every test function.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- The residual matrix field whose second-order pairing measures the failure of
the whole-space identity: the diagonal carries `p₁(·, s)` and the full matrix
carries the tensor source `η U(·, s)`. -/
def pressureP1Residual (η : Vec3 → ℝ) (u : ParabolicPoint → Vec3)
    (c : ℝ → Vec3) (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (s : ℝ) (i j : Fin 3) : Vec3 → ℝ := fun x =>
  (if i = j then pressureP1 η u c p f s x else 0) -
    η x * pressureUTensor u c (x, s) i j

private theorem pressureP1Residual_pairing_pointwise
    {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3} {s : ℝ}
    (ψ : Vec3 → ℝ) (x : Vec3) :
    (∑ i, ∑ j, pressureP1Residual η u c p f s i j x * mixedSecond ψ i j x) =
      pressureP1 η u c p f s x * spatialLaplacian ψ x -
        ∑ i, ∑ j, η x * pressureUTensor u c (x, s) i j * mixedSecond ψ i j x := by
  classical
  have hsplit : ∀ i j : Fin 3,
      pressureP1Residual η u c p f s i j x * mixedSecond ψ i j x =
        (if i = j then pressureP1 η u c p f s x * mixedSecond ψ i j x else 0) -
          η x * pressureUTensor u c (x, s) i j * mixedSecond ψ i j x := by
    intro i j
    simp only [pressureP1Residual, sub_mul, ite_mul, zero_mul]
  simp only [hsplit, Finset.sum_sub_distrib]
  have hdiag : ∀ i : Fin 3,
      (∑ j, if i = j then pressureP1 η u c p f s x * mixedSecond ψ i j x else 0) =
        pressureP1 η u c p f s x * mixedSecond ψ i i x := by
    intro i
    simp
  simp only [hdiag]
  have hlap : (∑ i, pressureP1 η u c p f s x * mixedSecond ψ i i x) =
      pressureP1 η u c p f s x * spatialLaplacian ψ x := by
    rw [← Finset.mul_sum]
    rfl
  rw [hlap]

private theorem pressureP1Residual_locallyIntegrable
    {η : Vec3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} {s : ℝ}
    (hU : ∀ i j : Fin 3, IntegrableOn
      (fun y : Vec3 => pressureUTensor u c (y, s) i j) (tsupport η) volume)
    (hp : IntegrableOn (fun y : Vec3 => p (y, s)) (tsupport η) volume)
    (hf : ∀ j : Fin 3, IntegrableOn
      (fun y : Vec3 => f (y, s) j) (tsupport η) volume) (i j : Fin 3) :
    LocallyIntegrable (pressureP1Residual η u c p f s i j) volume := by
  classical
  have htensor : LocallyIntegrable
      (fun x : Vec3 => η x * pressureUTensor u c (x, s) i j) volume :=
    (pressureCutoff_integrable_mul_of_tsupport_subset hη.continuous hηc
      (subset_refl _) (hU i j)).locallyIntegrable
  by_cases hij : i = j
  · have hdiag : pressureP1Residual η u c p f s i j =
        pressureP1 η u c p f s -
          (fun x : Vec3 => η x * pressureUTensor u c (x, s) i j) := by
      funext x
      simp only [pressureP1Residual, Pi.sub_apply, hij]
      simp
    rw [hdiag]
    exact (pressureP1_slice_locallyIntegrable hη hηc hU hp hf).sub htensor
  · have hoff : pressureP1Residual η u c p f s i j =
        (fun _ : Vec3 => (0 : ℝ)) -
          (fun x : Vec3 => η x * pressureUTensor u c (x, s) i j) := by
      funext x
      simp only [pressureP1Residual, Pi.sub_apply, hij, reduceIte]
    rw [hoff]
    exact (MeasureTheory.locallyIntegrable_const (0 : ℝ)).sub htensor

/-- The Calderón--Zygmund identification data for the leading local pressure.
For almost every time the whole-space distributional identity and the
integrability of the pairing hold simultaneously for every compactly supported
smooth spatial test function; the tensor source is `η U(·, s)`. -/
theorem pressureP1_cz_identification_data_ae_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {η : Vec3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηΩ : tsupport η ⊆ Ω) (c : ℝ → Vec3) :
    ∀ᵐ s ∂volume.restrict I,
      (∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          Integrable (fun x => pressureP1 η u c p f s x *
            spatialLaplacian ψ x) volume →
          ∫ x, pressureP1 η u c p f s x * spatialLaplacian ψ x =
            pressureSecondPairing
              (fun i j x => η x * pressureUTensor u c (x, s) i j) ψ) ∧
        ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          Integrable (fun x => pressureP1 η u c p f s x *
            spatialLaplacian ψ x) volume := by
  classical
  have hslice := pressureCutoff_slice_data_ae_of_sws hsol hηc hηΩ c
  have hloc : ∀ᵐ s ∂volume.restrict I, ∀ i j : Fin 3,
      LocallyIntegrable (pressureP1Residual η u c p f s i j) volume := by
    filter_upwards [hslice] with s hdata i j
    exact pressureP1Residual_locallyIntegrable hη hηc hdata.1 hdata.2.1
      hdata.2.2 i j
  have hzero : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∀ᵐ s ∂volume.restrict I, ∫ x, ∑ i, ∑ j,
        pressureP1Residual η u c p f s i j x * mixedSecond ψ i j x = 0 := by
    intro ψ hψ hψc
    filter_upwards [pressureP1_wholeSpace_pairing_ae_of_sws hsol hη hηc hηΩ c
      hψ hψc, hslice] with s hid hdata
    have hp₁loc : LocallyIntegrable (pressureP1 η u c p f s) volume :=
      pressureP1_slice_locallyIntegrable hη hηc hdata.1 hdata.2.1 hdata.2.2
    have hInt1 : Integrable (fun x => pressureP1 η u c p f s x *
        spatialLaplacian ψ x) volume := by
      simpa only [smul_eq_mul] using
        hp₁loc.integrable_smul_right_of_hasCompactSupport
          (contDiff_spatialLaplacian_smooth hψ).continuous
          (CKN.Foundation.Heat.laplacian_compact_support_global hψc)
    have hInt2 := pressureCutoff_tensorPairing_integrable hη hηc hdata.1 hψ hψc
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall
      (fun x => pressureP1Residual_pairing_pointwise (η := η) (u := u) (c := c)
        (p := p) (f := f) (s := s) ψ x)),
      MeasureTheory.integral_sub hInt1 hInt2, hid, sub_self]
  filter_upwards [ae_slice_second_pairing_zero_of_forall_test hloc hzero, hslice]
    with s hs hdata
  have hp₁loc : LocallyIntegrable (pressureP1 η u c p f s) volume :=
    pressureP1_slice_locallyIntegrable hη hηc hdata.1 hdata.2.1 hdata.2.2
  have hInt : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      Integrable (fun x => pressureP1 η u c p f s x *
        spatialLaplacian ψ x) volume := by
    intro ψ hψ hψc
    simpa only [smul_eq_mul] using
      hp₁loc.integrable_smul_right_of_hasCompactSupport
        (contDiff_spatialLaplacian_smooth hψ).continuous
        (CKN.Foundation.Heat.laplacian_compact_support_global hψc)
  refine ⟨fun ψ hψ hψc _hInt => ?_, hInt⟩
  have hres := hs ψ hψ hψc
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall
    (fun x => pressureP1Residual_pairing_pointwise (η := η) (u := u) (c := c)
      (p := p) (f := f) (s := s) ψ x)),
    MeasureTheory.integral_sub (hInt ψ hψ hψc)
      (pressureCutoff_tensorPairing_integrable hη hηc hdata.1 hψ hψc)] at hres
  rw [pressureSecondPairing]
  linarith only [hres]

/-- The whole-space pairing identity in the exact binder shape consumed by the
pressure Calderón--Zygmund estimate. -/
theorem pressureP1_cz_hP1_ae_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {η : Vec3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηΩ : tsupport η ⊆ Ω) (c : ℝ → Vec3) :
    ∀ᵐ s ∂volume.restrict I,
      ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        Integrable (fun x => pressureP1 η u c p f s x *
          spatialLaplacian ψ x) volume →
        ∫ x, pressureP1 η u c p f s x * spatialLaplacian ψ x =
          pressureSecondPairing
            (fun i j x => η x * pressureUTensor u c (x, s) i j) ψ := by
  filter_upwards [pressureP1_cz_identification_data_ae_of_sws hsol hη hηc hηΩ c]
    with s hs using hs.1

/-- The test-pairing integrability in the exact binder shape consumed by the
pressure Calderón--Zygmund estimate. -/
theorem pressureP1_cz_hP1Int_ae_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {η : Vec3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηΩ : tsupport η ⊆ Ω) (c : ℝ → Vec3) :
    ∀ᵐ s ∂volume.restrict I,
      ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        Integrable (fun x => pressureP1 η u c p f s x *
          spatialLaplacian ψ x) volume := by
  filter_upwards [pressureP1_cz_identification_data_ae_of_sws hsol hη hηc hηΩ c]
    with s hs using hs.2

end CKN

end
