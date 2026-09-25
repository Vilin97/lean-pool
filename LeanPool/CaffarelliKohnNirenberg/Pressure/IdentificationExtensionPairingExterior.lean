/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionPairingSource

/-!
# The leading pressure term away from the cut-off

The leading local pressure `p₁ = ηp - (p₂ + ⋯ + p₈)` is built from `ηp` and from
Newtonian potentials whose sources all vanish outside `tsupport η`.  Consequently
`p₁` is harmonic in the sense of distributions outside `tsupport η`: a test
function vanishing on an open neighbourhood of the cut-off support pairs to zero
against `Δp₁`.  This is the exterior half of the whole-space distributional
identity for `p₁`; the interior half is the localized identity of the pressure
decomposition.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- A smooth function vanishing on an open set has vanishing first spatial
derivatives there. -/
theorem pressureCutoff_spatialDeriv_eqOn_zero {ψ : Vec3 → ℝ} {V : Set Vec3}
    (hV : IsOpen V) (hψV : Set.EqOn ψ (fun _ => (0 : ℝ)) V) (i : Fin 3) :
    Set.EqOn (spatialDeriv ψ i) (fun _ => (0 : ℝ)) V := by
  intro x hx
  have hloc : ψ =ᶠ[nhds x] fun _ : Vec3 => (0 : ℝ) := by
    filter_upwards [hV.mem_nhds hx] with y hy using hψV hy
  have hfd := hloc.fderiv_eq (𝕜 := ℝ)
  simp only [spatialDeriv, hfd]
  simp

/-- A smooth function vanishing on an open set has vanishing mixed second spatial
derivatives there. -/
theorem pressureCutoff_mixedSecond_eqOn_zero {ψ : Vec3 → ℝ} {V : Set Vec3}
    (hV : IsOpen V) (hψV : Set.EqOn ψ (fun _ => (0 : ℝ)) V) (i j : Fin 3) :
    Set.EqOn (mixedSecond ψ i j) (fun _ => (0 : ℝ)) V :=
  pressureCutoff_spatialDeriv_eqOn_zero hV
    (pressureCutoff_spatialDeriv_eqOn_zero hV hψV j) i

/-- A smooth function vanishing on an open set has vanishing spatial Laplacian
there. -/
theorem pressureCutoff_spatialLaplacian_eqOn_zero {ψ : Vec3 → ℝ} {V : Set Vec3}
    (hV : IsOpen V) (hψV : Set.EqOn ψ (fun _ => (0 : ℝ)) V) :
    Set.EqOn (spatialLaplacian ψ) (fun _ => (0 : ℝ)) V := by
  intro x hx
  have h : ∀ i : Fin 3, spatialDeriv (spatialDeriv ψ i) i x = 0 := fun i =>
    pressureCutoff_mixedSecond_eqOn_zero hV hψV i i hx
  simp only [spatialLaplacian]
  simpa using Finset.sum_eq_zero (fun i _ => h i)

/-- The leading local pressure is locally integrable on every time slice for
which the velocity tensor, the pressure and the force are integrable on the
cut-off support. -/
theorem pressureP1_slice_locallyIntegrable
    {η : Vec3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} {s : ℝ}
    (hU : ∀ i j : Fin 3, IntegrableOn
      (fun y : Vec3 => pressureUTensor u c (y, s) i j) (tsupport η) volume)
    (hp : IntegrableOn (fun y : Vec3 => p (y, s)) (tsupport η) volume)
    (hf : ∀ j : Fin 3, IntegrableOn
      (fun y : Vec3 => f (y, s) j) (tsupport η) volume) :
    LocallyIntegrable (pressureP1 η u c p f s) volume := by
  have h1 : LocallyIntegrable (fun x : Vec3 => η x * p (x, s)) volume :=
    (pressureCutoff_cutoffPressure_integrable hη hηc hp).locallyIntegrable
  have h2 : LocallyIntegrable (pressureP2 η u c s) volume :=
    pressureP2_locallyIntegrable
      (pressureCutoff_hessianTensor_integrable hη hηc hU)
      (pressureCutoff_hessianTensor_hasCompactSupport hηc)
  have h3 : LocallyIntegrable (pressureP3 η u c s) volume :=
    pressureP3_locallyIntegrable
      (pressureCutoff_tensorGradientFirst_integrable hη hηc hU)
      (pressureCutoff_tensorGradientFirst_hasCompactSupport hηc)
  have h4 : LocallyIntegrable (pressureP4 η u c s) volume :=
    pressureP4_locallyIntegrable
      (pressureCutoff_tensorGradientSecond_integrable hη hηc hU)
      (pressureCutoff_tensorGradientSecond_hasCompactSupport hηc)
  have h5 : LocallyIntegrable (pressureP5 η p s) volume :=
    pressureP5_locallyIntegrable
      (pressureCutoff_pressureLaplacian_integrable hη hηc hp)
      (pressureCutoff_pressureLaplacian_hasCompactSupport hηc)
  have h6 : LocallyIntegrable (pressureP6 η p s) volume :=
    pressureP6_locallyIntegrable
      (pressureCutoff_pressureGradient_integrable hη hηc hp)
      (pressureCutoff_pressureGradient_hasCompactSupport hηc)
  have h7 : LocallyIntegrable (pressureP7 η f s) volume :=
    pressureP7_locallyIntegrable
      (pressureCutoff_forceCutoff_integrable hη hηc hf)
      (pressureCutoff_forceCutoff_hasCompactSupport hηc)
  have h8 : LocallyIntegrable (pressureP8 η f s) volume :=
    pressureP8_locallyIntegrable
      (pressureCutoff_forceGradient_integrable hη hηc hf)
      (pressureCutoff_forceGradient_hasCompactSupport hηc)
  have hsum : LocallyIntegrable (fun x : Vec3 => pressureP2 η u c s x +
      pressureP3 η u c s x + pressureP4 η u c s x + pressureP5 η p s x +
      pressureP6 η p s x + pressureP7 η f s x + pressureP8 η f s x) volume :=
    ((((((h2.add h3).add h4).add h5).add h6).add h7).add h8)
  have hrw : pressureP1 η u c p f s =
      (fun x : Vec3 => η x * p (x, s)) - (fun x : Vec3 => pressureP2 η u c s x +
        pressureP3 η u c s x + pressureP4 η u c s x + pressureP5 η p s x +
        pressureP6 η p s x + pressureP7 η f s x + pressureP8 η f s x) := by
    funext x
    simp only [pressureP1, Pi.sub_apply]
  rw [hrw]
  exact h1.sub hsum

/-- The tensor side of the whole-space identity vanishes against a test function
supported away from the cut-off. -/
theorem pressureCutoff_tensorPairing_eq_zero_of_eqOn_zero
    {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {s : ℝ}
    {ψ : Vec3 → ℝ} {V : Set Vec3} (hV : IsOpen V) (hηV : tsupport η ⊆ V)
    (hψV : Set.EqOn ψ (fun _ => (0 : ℝ)) V) :
    ∫ x, ∑ i, ∑ j, η x * pressureUTensor u c (x, s) i j *
      mixedSecond ψ i j x = 0 := by
  have hpt : ∀ x : Vec3, ∑ i, ∑ j, η x * pressureUTensor u c (x, s) i j *
      mixedSecond ψ i j x = 0 := by
    intro x
    by_cases hx : x ∈ tsupport η
    · refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      rw [pressureCutoff_mixedSecond_eqOn_zero hV hψV i j (hηV hx), mul_zero]
    · refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
  simp only [hpt]
  simp

/-- The leading local pressure is weakly harmonic outside the support of the
cut-off: a smooth compactly supported test function vanishing on an open
neighbourhood of `tsupport η` pairs to zero against `Δp₁`. -/
theorem pressureP1_pairing_eq_zero_of_eqOn_zero
    {η : Vec3 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} {s : ℝ}
    (hU : ∀ i j : Fin 3, IntegrableOn
      (fun y : Vec3 => pressureUTensor u c (y, s) i j) (tsupport η) volume)
    (hp : IntegrableOn (fun y : Vec3 => p (y, s)) (tsupport η) volume)
    (hf : ∀ j : Fin 3, IntegrableOn
      (fun y : Vec3 => f (y, s) j) (tsupport η) volume)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    {V : Set Vec3} (hV : IsOpen V) (hηV : tsupport η ⊆ V)
    (hψV : Set.EqOn ψ (fun _ => (0 : ℝ)) V) :
    ∫ x, pressureP1 η u c p f s x * spatialLaplacian ψ x = 0 := by
  have hψ0 : ∀ x ∈ tsupport η, ψ x = 0 := fun x hx => hψV (hηV hx)
  have hdψ0 : ∀ (i : Fin 3), ∀ x ∈ tsupport η, spatialDeriv ψ i x = 0 :=
    fun i x hx => pressureCutoff_spatialDeriv_eqOn_zero hV hψV i (hηV hx)
  have hΔψ0 : ∀ x ∈ tsupport η, spatialLaplacian ψ x = 0 :=
    fun x hx => pressureCutoff_spatialLaplacian_eqOn_zero hV hψV (hηV hx)
  have hmulInt : ∀ {F : Vec3 → ℝ}, LocallyIntegrable F volume →
      Integrable (fun x => F x * spatialLaplacian ψ x) volume := by
    intro F hF
    simpa only [smul_eq_mul] using
      hF.integrable_smul_right_of_hasCompactSupport
        (contDiff_spatialLaplacian_smooth hψ).continuous
        (CKN.Foundation.Heat.laplacian_compact_support_global hψc)
  have hstep : ∀ {F G : Vec3 → ℝ},
      (Integrable (fun x => F x * spatialLaplacian ψ x) volume ∧
        ∫ x, F x * spatialLaplacian ψ x = 0) →
      (Integrable (fun x => G x * spatialLaplacian ψ x) volume ∧
        ∫ x, G x * spatialLaplacian ψ x = 0) →
      (Integrable (fun x => (F x + G x) * spatialLaplacian ψ x) volume ∧
        ∫ x, (F x + G x) * spatialLaplacian ψ x = 0) := by
    rintro F G ⟨hF, hF0⟩ ⟨hG, hG0⟩
    have hpt : ∀ x : Vec3, (F x + G x) * spatialLaplacian ψ x =
        F x * spatialLaplacian ψ x + G x * spatialLaplacian ψ x :=
      fun x => by ring
    refine ⟨(hF.add hG).congr (Filter.Eventually.of_forall fun x => (hpt x).symm), ?_⟩
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
      MeasureTheory.integral_add hF hG, hF0, hG0]
    ring
  have h2 : Integrable (fun x => pressureP2 η u c s x *
      spatialLaplacian ψ x) volume ∧
      ∫ x, pressureP2 η u c s x * spatialLaplacian ψ x = 0 := by
    refine ⟨hmulInt (pressureP2_locallyIntegrable
      (pressureCutoff_hessianTensor_integrable hη hηc hU)
      (pressureCutoff_hessianTensor_hasCompactSupport hηc)), ?_⟩
    rw [pressureP2_distributional_pairing
      (pressureCutoff_hessianTensor_integrable hη hηc hU)
      (pressureCutoff_hessianTensor_hasCompactSupport hηc) hψ hψc]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    have hpt : ∀ y : Vec3, mixedSecond η i j y *
        pressureUTensor u c (y, s) i j * ψ y = 0 := by
      intro y
      by_cases hy : y ∈ tsupport η
      · rw [hψ0 y hy, mul_zero]
      · rw [image_eq_zero_of_notMem_tsupport (f := mixedSecond η i j)
          (fun h => hy (pressureCutoff_tsupport_mixedSecond_subset η i j h)),
          zero_mul, zero_mul]
    simp only [hpt]
    simp
  have h3 : Integrable (fun x => pressureP3 η u c s x *
      spatialLaplacian ψ x) volume ∧
      ∫ x, pressureP3 η u c s x * spatialLaplacian ψ x = 0 := by
    refine ⟨hmulInt (pressureP3_locallyIntegrable
      (pressureCutoff_tensorGradientFirst_integrable hη hηc hU)
      (pressureCutoff_tensorGradientFirst_hasCompactSupport hηc)), ?_⟩
    rw [pressureP3_distributional_pairing
      (pressureCutoff_tensorGradientFirst_integrable hη hηc hU)
      (pressureCutoff_tensorGradientFirst_hasCompactSupport hηc) hψ hψc]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    have hpt : ∀ y : Vec3, pressureUTensor u c (y, s) i j *
        spatialDeriv η i y * spatialDeriv ψ j y = 0 := by
      intro y
      by_cases hy : y ∈ tsupport η
      · rw [hdψ0 j y hy, mul_zero]
      · rw [image_eq_zero_of_notMem_tsupport (f := spatialDeriv η i)
          (fun h => hy (pressureCutoff_tsupport_spatialDeriv_subset η i h)),
          mul_zero, zero_mul]
    simp only [hpt]
    simp
  have h4 : Integrable (fun x => pressureP4 η u c s x *
      spatialLaplacian ψ x) volume ∧
      ∫ x, pressureP4 η u c s x * spatialLaplacian ψ x = 0 := by
    refine ⟨hmulInt (pressureP4_locallyIntegrable
      (pressureCutoff_tensorGradientSecond_integrable hη hηc hU)
      (pressureCutoff_tensorGradientSecond_hasCompactSupport hηc)), ?_⟩
    rw [pressureP4_distributional_pairing
      (pressureCutoff_tensorGradientSecond_integrable hη hηc hU)
      (pressureCutoff_tensorGradientSecond_hasCompactSupport hηc) hψ hψc]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    have hpt : ∀ y : Vec3, pressureUTensor u c (y, s) i j *
        spatialDeriv η j y * spatialDeriv ψ i y = 0 := by
      intro y
      by_cases hy : y ∈ tsupport η
      · rw [hdψ0 i y hy, mul_zero]
      · rw [image_eq_zero_of_notMem_tsupport (f := spatialDeriv η j)
          (fun h => hy (pressureCutoff_tsupport_spatialDeriv_subset η j h)),
          mul_zero, zero_mul]
    simp only [hpt]
    simp
  have h5 : Integrable (fun x => pressureP5 η p s x *
      spatialLaplacian ψ x) volume ∧
      ∫ x, pressureP5 η p s x * spatialLaplacian ψ x = 0 := by
    refine ⟨hmulInt (pressureP5_locallyIntegrable
      (pressureCutoff_pressureLaplacian_integrable hη hηc hp)
      (pressureCutoff_pressureLaplacian_hasCompactSupport hηc)), ?_⟩
    rw [pressureP5_distributional_pairing
      (pressureCutoff_pressureLaplacian_integrable hη hηc hp)
      (pressureCutoff_pressureLaplacian_hasCompactSupport hηc) hψ hψc]
    have hpt : ∀ y : Vec3, p (y, s) * spatialLaplacian η y * ψ y = 0 := by
      intro y
      by_cases hy : y ∈ tsupport η
      · rw [hψ0 y hy, mul_zero]
      · rw [image_eq_zero_of_notMem_tsupport (f := spatialLaplacian η)
          (fun h => hy (pressureCutoff_tsupport_spatialLaplacian_subset η h)),
          mul_zero, zero_mul]
    simp only [hpt]
    simp
  have h6 : Integrable (fun x => pressureP6 η p s x *
      spatialLaplacian ψ x) volume ∧
      ∫ x, pressureP6 η p s x * spatialLaplacian ψ x = 0 := by
    refine ⟨hmulInt (pressureP6_locallyIntegrable
      (pressureCutoff_pressureGradient_integrable hη hηc hp)
      (pressureCutoff_pressureGradient_hasCompactSupport hηc)), ?_⟩
    rw [pressureP6_distributional_pairing
      (pressureCutoff_pressureGradient_integrable hη hηc hp)
      (pressureCutoff_pressureGradient_hasCompactSupport hηc) hψ hψc]
    have hzero : ∀ j : Fin 3, ∫ y : Vec3, spatialDeriv η j y * p (y, s) *
        spatialDeriv ψ j y = 0 := by
      intro j
      have hpt : ∀ y : Vec3, spatialDeriv η j y * p (y, s) *
          spatialDeriv ψ j y = 0 := by
        intro y
        by_cases hy : y ∈ tsupport η
        · rw [hdψ0 j y hy, mul_zero]
        · rw [image_eq_zero_of_notMem_tsupport (f := spatialDeriv η j)
            (fun h => hy (pressureCutoff_tsupport_spatialDeriv_subset η j h)),
            zero_mul, zero_mul]
      simp only [hpt]
      simp
    simp only [hzero]
    simp
  have h7 : Integrable (fun x => pressureP7 η f s x *
      spatialLaplacian ψ x) volume ∧
      ∫ x, pressureP7 η f s x * spatialLaplacian ψ x = 0 := by
    refine ⟨hmulInt (pressureP7_locallyIntegrable
      (pressureCutoff_forceCutoff_integrable hη hηc hf)
      (pressureCutoff_forceCutoff_hasCompactSupport hηc)), ?_⟩
    rw [pressureP7_distributional_pairing
      (pressureCutoff_forceCutoff_integrable hη hηc hf)
      (pressureCutoff_forceCutoff_hasCompactSupport hηc) hψ hψc]
    have hzero : ∀ j : Fin 3, ∫ y : Vec3, η y * f (y, s) j *
        spatialDeriv ψ j y = 0 := by
      intro j
      have hpt : ∀ y : Vec3, η y * f (y, s) j * spatialDeriv ψ j y = 0 := by
        intro y
        by_cases hy : y ∈ tsupport η
        · rw [hdψ0 j y hy, mul_zero]
        · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul, zero_mul]
      simp only [hpt]
      simp
    simp only [hzero]
    simp
  have h8 : Integrable (fun x => pressureP8 η f s x *
      spatialLaplacian ψ x) volume ∧
      ∫ x, pressureP8 η f s x * spatialLaplacian ψ x = 0 := by
    refine ⟨hmulInt (pressureP8_locallyIntegrable
      (pressureCutoff_forceGradient_integrable hη hηc hf)
      (pressureCutoff_forceGradient_hasCompactSupport hηc)), ?_⟩
    rw [pressureP8_distributional_pairing
      (pressureCutoff_forceGradient_integrable hη hηc hf)
      (pressureCutoff_forceGradient_hasCompactSupport hηc) hψ hψc]
    have hzero : ∀ j : Fin 3, ∫ y : Vec3, spatialDeriv η j y * f (y, s) j *
        ψ y = 0 := by
      intro j
      have hpt : ∀ y : Vec3, spatialDeriv η j y * f (y, s) j * ψ y = 0 := by
        intro y
        by_cases hy : y ∈ tsupport η
        · rw [hψ0 y hy, mul_zero]
        · rw [image_eq_zero_of_notMem_tsupport (f := spatialDeriv η j)
            (fun h => hy (pressureCutoff_tsupport_spatialDeriv_subset η j h)),
            zero_mul, zero_mul]
      simp only [hpt]
      simp
    simp only [hzero]
    simp
  have hA : Integrable (fun x : Vec3 => η x * p (x, s) *
      spatialLaplacian ψ x) volume ∧
      ∫ x : Vec3, η x * p (x, s) * spatialLaplacian ψ x = 0 := by
    refine ⟨hmulInt
      (pressureCutoff_cutoffPressure_integrable hη hηc hp).locallyIntegrable, ?_⟩
    have hpt : ∀ x : Vec3, η x * p (x, s) * spatialLaplacian ψ x = 0 := by
      intro x
      by_cases hx : x ∈ tsupport η
      · rw [hΔψ0 x hx, mul_zero]
      · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
    simp only [hpt]
    simp
  have hsum := hstep (hstep (hstep (hstep (hstep (hstep h2 h3) h4) h5) h6) h7) h8
  have hsplit : ∀ x : Vec3, pressureP1 η u c p f s x * spatialLaplacian ψ x =
      η x * p (x, s) * spatialLaplacian ψ x -
        (pressureP2 η u c s x + pressureP3 η u c s x + pressureP4 η u c s x +
          pressureP5 η p s x + pressureP6 η p s x + pressureP7 η f s x +
          pressureP8 η f s x) * spatialLaplacian ψ x := by
    intro x
    simp only [pressureP1]
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsplit),
    MeasureTheory.integral_sub hA.1 hsum.1, hA.2, hsum.2]
  ring

end CKN

end
