/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientCentredSourceTensorDef
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientProduct
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Lin34CentredCorrection

/-!
# Slice Selected Gradient Centred Source Tensor

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Core.Step4

/-!
# Pairing identity for the force-free centred source

The weak product rule converts the centred cutoff source into the second
pressure pairing, with the divergence-free trace term cancelling after summing
the spatial indices.
-/

private theorem centred_tensor_pair_memLp_integrable
    {U : Set Vec3} (hU : IsOpen U)
    {a b : Vec3 → ℝ} (ha : MemLp a 2 (volume.restrict U))
    (hb : MemLp b 2 (volume.restrict U)) {φ : Vec3 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) :
    IntegrableOn (fun x => a x * b x * φ x) U volume := by
  letI : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 :=
    ENNReal.HolderConjugate.instTwoTwo
  have hab : MemLp (fun x => a x * b x) 1 (volume.restrict U) := ha.mul hb
  have habLoc : LocallyIntegrableOn (fun x => a x * b x) U volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict
      (hab.locallyIntegrable (by norm_num))
  have hmulLoc : LocallyIntegrableOn (fun x => a x * b x * φ x) U volume :=
    habLoc.mul_continuousOn hφ.continuous.continuousOn hU.isLocallyClosed
  have hmulK := hmulLoc.integrableOn_compact_subset hφU hφc.isCompact
  exact hmulK.integrable_of_forall_notMem_eq_zero (by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (f := φ) (fun hxt => hx hxt)]
    simp) |>.integrableOn

private theorem centred_tensor_single_memLp_integrable
    {U : Set Vec3} (hU : IsOpen U) {a : Vec3 → ℝ}
    (ha : MemLp a 2 (volume.restrict U)) {φ : Vec3 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) :
    IntegrableOn (fun x => a x * φ x) U volume := by
  have haLoc : LocallyIntegrableOn a U volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict
      (ha.locallyIntegrable (by norm_num))
  have hmulLoc : LocallyIntegrableOn (fun x => a x * φ x) U volume :=
    haLoc.mul_continuousOn hφ.continuous.continuousOn hU.isLocallyClosed
  have hmulK := hmulLoc.integrableOn_compact_subset hφU hφc.isCompact
  exact hmulK.integrable_of_forall_notMem_eq_zero (by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (f := φ) (fun hxt => hx hxt)]
    simp) |>.integrableOn

/-- The force-free centred cutoff source pairs against a test gradient as the
second pressure pairing of the cutoff centred tensor. -/
theorem pressureDivergenceCutoffSourceCentredTensor_pairing_of_weak_data
    {U : Set Vec3} (hU : IsOpen U)
    {η : Vec3 → ℝ} {dη : Fin 3 → Vec3 → ℝ}
    {u : Vec3 → Vec3} {Du : Vec3 → Fin 3 → Fin 3 → ℝ} {c : Vec3}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ U)
    (hdη : ∀ j : Fin 3, dη j = spatialDeriv η j)
    (hUfinite : (volume.restrict U) Set.univ < ⊤)
    (hu : ∀ i : Fin 3, MemLp (fun x => u x i) 2 (volume.restrict U))
    (hDu : ∀ i j : Fin 3, MemLp (fun x => Du x i j) 2 (volume.restrict U))
    (hweak : ∀ i : Fin 3,
      HasWeakGradientOn U (fun x => u x i) (fun x => Du x i))
    (htrace : (fun x => ∑ i, Du x i i) =ᵐ[volume.restrict U] 0)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    (∑ i : Fin 3, ∫ x,
      pressureDivergenceCutoffSourceCentredTensor η dη u Du c x i *
        spatialDeriv ψ i x) =
      pressureSecondPairing
        (fun i j x => η x * (-(u x i) * (u x j - c j))) ψ := by
  letI : IsFiniteMeasure (volume.restrict U) := ⟨hUfinite⟩
  let v : Vec3 → Vec3 := fun x j => u x j - c j
  have hηd (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv η j) :=
    contDiff_spatialDeriv_smooth hη j
  have hηdc (j : Fin 3) : HasCompactSupport (spatialDeriv η j) :=
    hηc.fderiv_apply (𝕜 := ℝ) (basisVec j)
  have hdηd (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (dη j) := by
    rw [hdη j]
    exact hηd j
  have hdηc (j : Fin 3) : HasCompactSupport (dη j) := by
    rw [hdη j]
    exact hηdc j
  have hψd (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv ψ i) :=
    contDiff_spatialDeriv_smooth hψ i
  have hψm (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (mixedSecond ψ i j) :=
    contDiff_mixedSecond_smooth hψ i j
  have hv (j : Fin 3) : MemLp (fun x => v x j) 2 (volume.restrict U) := by
    exact (hu j).sub (memLp_const (μ := volume.restrict U) (c j))
  have hvweak (j : Fin 3) : HasWeakGradientOn U
      (fun x => v x j) (fun x k => Du x j k) := by
    intro k φ hφ hφc hφU
    have hφd : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv φ k) :=
      contDiff_spatialDeriv_smooth hφ k
    have hφdc : HasCompactSupport (spatialDeriv φ k) :=
      hφc.fderiv_apply (𝕜 := ℝ) (basisVec k)
    have hφdU : tsupport (spatialDeriv φ k) ⊆ U :=
      (tsupport_fderiv_apply_subset ℝ (basisVec k)).trans hφU
    have hleft : IntegrableOn (fun x => u x j * spatialDeriv φ k x) U volume :=
      centred_tensor_single_memLp_integrable hU (hu j) hφd hφdc hφdU
    have hconst : IntegrableOn (fun x => c j * spatialDeriv φ k x) U volume :=
      centred_tensor_single_memLp_integrable hU
        (memLp_const (μ := volume.restrict U) (c j)) hφd hφdc hφdU
    have hright : IntegrableOn (fun x => Du x j k * φ x) U volume :=
      centred_tensor_single_memLp_integrable hU (hDu j k) hφ hφc hφU
    have hderivFull : ∫ x, spatialDeriv φ k x = 0 :=
      lin34_integral_spatialDeriv_eq_zero hφ hφc k
    have hderivU : ∫ x in U, spatialDeriv φ k x = 0 := by
      rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
      · exact hderivFull
      · intro x hx
        have hxφ : x ∉ tsupport φ := fun hxφ => hx (hφU hxφ)
        exact image_eq_zero_of_notMem_tsupport
          (fun hx' => hxφ ((tsupport_fderiv_apply_subset ℝ (basisVec k)) hx'))
    have hwu := hweak j k φ hφ hφc hφU
    have hwu' : ∫ x in U, u x j * spatialDeriv φ k x =
        -∫ x in U, Du x j k * φ x := by
      simpa only [spatialDeriv] using hwu
    calc
      ∫ x in U, v x j * spatialDeriv φ k x =
          (∫ x in U, u x j * spatialDeriv φ k x) -
            ∫ x in U, c j * spatialDeriv φ k x := by
              have heq : (fun x => v x j * spatialDeriv φ k x) =
                  (fun x => u x j * spatialDeriv φ k x) -
                    (fun x => c j * spatialDeriv φ k x) := by
                funext x
                simp only [Pi.sub_apply, v]
                ring
              rw [heq]
              exact integral_sub hleft hconst
      _ = -∫ x in U, Du x j k * φ x := by
        rw [hwu', integral_const_mul, hderivU]
        simp
  have hprod (i j : Fin 3) : HasWeakGradientOn U
      (fun x => u x i * v x j)
      (fun x k => Du x i k * v x j + u x i * Du x j k) :=
    HasWeakGradientOn.mul_of_memLp_two hU (hu i) (hv j)
      (fun k => hDu i k) (fun k => hDu j k) (hweak i) (hvweak j)
  have hφ (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => η x * spatialDeriv ψ i x) := hη.mul (hψd i)
  have hφc (i : Fin 3) : HasCompactSupport
      (fun x => η x * spatialDeriv ψ i x) :=
    hηc.mul_right (f' := spatialDeriv ψ i)
  have hφU (i : Fin 3) : tsupport (fun x => η x * spatialDeriv ψ i x) ⊆ U :=
    (tsupport_mul_subset_left (f := η) (g := spatialDeriv ψ i)).trans hηU
  have hderiv (i j : Fin 3) (x : Vec3) :
      spatialDeriv (fun y => η y * spatialDeriv ψ i y) j x =
        dη j x * spatialDeriv ψ i x + η x * mixedSecond ψ i j x := by
    rw [spatialDeriv_mul (hη.differentiable (by simp) x)
      ((hψd i).differentiable (by simp) x) j, hdη j]
    change spatialDeriv η j x * spatialDeriv ψ i x +
        η x * mixedSecond ψ j i x = _
    rw [mixedSecond_swap hψ j i x]
  have hηψpart (i j : Fin 3) :
      ContDiff ℝ (⊤ : ℕ∞) (fun x => η x * spatialDeriv ψ i x) := hφ i
  have hηψsupp (i j : Fin 3) :
      HasCompactSupport (fun x => η x * spatialDeriv ψ i x) := hφc i
  have hηψU (i j : Fin 3) :
      tsupport (fun x => η x * spatialDeriv ψ i x) ⊆ U := hφU i
  have hdηU (j : Fin 3) : tsupport (dη j) ⊆ U := by
    rw [hdη j]
    exact (tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηU
  have hpairFactor (i j : Fin 3) :
      IntegrableOn (fun x => Du x i j * v x j *
        (η x * spatialDeriv ψ i x)) U volume :=
    centred_tensor_pair_memLp_integrable hU (hDu i j) (hv j)
      (hφ i) (hφc i) (hφU i)
  have htraceFactor (i j : Fin 3) :
      IntegrableOn (fun x => u x i * Du x j j *
        (η x * spatialDeriv ψ i x)) U volume :=
    centred_tensor_pair_memLp_integrable hU (hu i) (hDu j j)
      (hφ i) (hφc i) (hφU i)
  have hleftDη (i j : Fin 3) :
      IntegrableOn (fun x => u x i * v x j *
        (dη j x * spatialDeriv ψ i x)) U volume := by
    exact centred_tensor_pair_memLp_integrable hU (hu i) (hv j)
      ((hdηd j).mul (hψd i)) ((hdηc j).mul_right (f' := spatialDeriv ψ i))
      ((tsupport_mul_subset_left (f := dη j) (g := spatialDeriv ψ i)).trans
        (hdηU j))
  have hleftEtaMixed (i j : Fin 3) :
      IntegrableOn (fun x => u x i * v x j *
        (η x * mixedSecond ψ i j x)) U volume := by
    exact centred_tensor_pair_memLp_integrable hU (hu i) (hv j)
      (hη.mul (hψm i j)) (hηc.mul_right (f' := mixedSecond ψ i j))
      ((tsupport_mul_subset_left (f := η) (g := mixedSecond ψ i j)).trans hηU)
  have hsourceEta (i j : Fin 3) :
      IntegrableOn (fun x => η x * Du x i j * v x j *
        spatialDeriv ψ i x) U volume := by
    exact (centred_tensor_pair_memLp_integrable hU (hDu i j) (hv j)
      (hη.mul (hψd i)) (hηc.mul_right (f' := spatialDeriv ψ i))
      ((tsupport_mul_subset_left (f := η) (g := spatialDeriv ψ i)).trans hηU)).congr
        (Filter.Eventually.of_forall fun x => by ring)
  have hsourceDη (i j : Fin 3) :
      IntegrableOn (fun x => dη j x * u x i * v x j *
        spatialDeriv ψ i x) U volume := by
    exact centred_tensor_pair_memLp_integrable hU (hu i) (hv j)
      ((hdηd j).mul (hψd i))
      ((hdηc j).mul_right (f' := spatialDeriv ψ i))
      ((tsupport_mul_subset_left (f := dη j) (g := spatialDeriv ψ i)).trans
        (hdηU j)) |>.congr (Filter.Eventually.of_forall fun x => by ring)
  have hprodTest (i j : Fin 3) :
      ∫ x in U, u x i * v x j *
        spatialDeriv (fun y => η y * spatialDeriv ψ i y) j x =
      -∫ x in U,
        (Du x i j * v x j + u x i * Du x j j) *
          (η x * spatialDeriv ψ i x) := by
    simpa only [spatialDeriv] using
      hprod i j j (fun x => η x * spatialDeriv ψ i x)
        (hφ i) (hφc i) (hφU i)
  have hleftSplit (i j : Fin 3) :
      ∫ x in U, u x i * v x j *
          spatialDeriv (fun y => η y * spatialDeriv ψ i y) j x =
        (∫ x in U, u x i * v x j *
            (dη j x * spatialDeriv ψ i x)) +
          ∫ x in U, u x i * v x j *
            (η x * mixedSecond ψ i j x) := by
    have heq : (fun x => u x i * v x j *
          spatialDeriv (fun y => η y * spatialDeriv ψ i y) j x) =
        (fun x => u x i * v x j * (dη j x * spatialDeriv ψ i x)) +
          (fun x => u x i * v x j * (η x * mixedSecond ψ i j x)) := by
      funext x
      rw [hderiv i j x]
      simp only [Pi.add_apply]
      ring
    calc
      _ = ∫ x in U,
          (u x i * v x j * (dη j x * spatialDeriv ψ i x) +
            u x i * v x j * (η x * mixedSecond ψ i j x)) := by
              exact congrArg (fun g : Vec3 → ℝ => ∫ x in U, g x) heq
      _ = _ := integral_add (hleftDη i j) (hleftEtaMixed i j)
  have hrightSplit (i j : Fin 3) :
      ∫ x in U,
        (Du x i j * v x j + u x i * Du x j j) *
          (η x * spatialDeriv ψ i x) =
        (∫ x in U, Du x i j * v x j *
          (η x * spatialDeriv ψ i x)) +
        ∫ x in U, u x i * Du x j j *
          (η x * spatialDeriv ψ i x) := by
    have heq : (fun x =>
        (Du x i j * v x j + u x i * Du x j j) *
          (η x * spatialDeriv ψ i x)) =
        (fun x => Du x i j * v x j * (η x * spatialDeriv ψ i x)) +
          (fun x => u x i * Du x j j * (η x * spatialDeriv ψ i x)) := by
      funext x
      simp only [Pi.add_apply]
      ring
    calc
      _ = ∫ x in U,
          (Du x i j * v x j * (η x * spatialDeriv ψ i x) +
            u x i * Du x j j * (η x * spatialDeriv ψ i x)) := by
              exact congrArg (fun g : Vec3 → ℝ => ∫ x in U, g x) heq
      _ = _ := integral_add (hpairFactor i j) (htraceFactor i j)
  have hsourceTerm (i j : Fin 3) :
      ∫ x in U,
        (η x * Du x i j * v x j + dη j x * u x i * v x j) *
          spatialDeriv ψ i x =
        (-(∫ x in U, η x * u x i * v x j * mixedSecond ψ i j x)) -
          (∫ x in U, u x i * Du x j j *
            (η x * spatialDeriv ψ i x)) := by
    have htest := hprodTest i j
    rw [hleftSplit i j, hrightSplit i j] at htest
    have hmixedTerm :
        ∫ x in U, u x i * v x j * (η x * mixedSecond ψ i j x) =
          ∫ x in U, η x * u x i * v x j * mixedSecond ψ i j x := by
      apply MeasureTheory.setIntegral_congr_fun hU.measurableSet
      intro x hx
      ring
    have hsourceSplit :
        ∫ x in U,
          (η x * Du x i j * v x j + dη j x * u x i * v x j) *
            spatialDeriv ψ i x =
        (∫ x in U, η x * Du x i j * v x j * spatialDeriv ψ i x) +
          ∫ x in U, dη j x * u x i * v x j * spatialDeriv ψ i x := by
      have heq : (fun x =>
          (η x * Du x i j * v x j + dη j x * u x i * v x j) *
            spatialDeriv ψ i x) =
            (fun x => η x * Du x i j * v x j * spatialDeriv ψ i x) +
            (fun x => dη j x * u x i * v x j * spatialDeriv ψ i x) := by
          funext x
          simp only [Pi.add_apply]
          ring
      calc
        _ = ∫ x in U,
            (η x * Du x i j * v x j * spatialDeriv ψ i x +
              dη j x * u x i * v x j * spatialDeriv ψ i x) := by
                exact congrArg (fun g : Vec3 → ℝ => ∫ x in U, g x) heq
        _ = _ := integral_add (hsourceEta i j) (hsourceDη i j)
    have hfactorA :
        ∫ x in U, η x * Du x i j * v x j * spatialDeriv ψ i x =
        ∫ x in U, Du x i j * v x j * (η x * spatialDeriv ψ i x) := by
      apply MeasureTheory.setIntegral_congr_fun hU.measurableSet
      intro x hx
      ring
    have hfactorB :
        ∫ x in U, dη j x * u x i * v x j * spatialDeriv ψ i x =
        ∫ x in U, u x i * v x j *
          (dη j x * spatialDeriv ψ i x) := by
      apply MeasureTheory.setIntegral_congr_fun hU.measurableSet
      intro x hx
      ring
    rw [hmixedTerm] at htest
    rw [hsourceSplit, hfactorA, hfactorB]
    have hzero :
        (∫ x in U, Du x i j * v x j * (η x * spatialDeriv ψ i x)) +
        (∫ x in U, u x i * v x j * (dη j x * spatialDeriv ψ i x)) +
        (∫ x in U, η x * u x i * v x j * mixedSecond ψ i j x) +
        (∫ x in U, u x i * Du x j j * (η x * spatialDeriv ψ i x)) = 0 := by
      calc
        _ =
          ((∫ x in U, u x i * v x j * (dη j x * spatialDeriv ψ i x)) +
            (∫ x in U, η x * u x i * v x j * mixedSecond ψ i j x)) +
          ((∫ x in U, Du x i j * v x j * (η x * spatialDeriv ψ i x)) +
            (∫ x in U, u x i * Du x j j * (η x * spatialDeriv ψ i x))) := by abel
        _ = 0 := by rw [htest]; simp
    have hzero' :
        ((∫ x in U, Du x i j * v x j * (η x * spatialDeriv ψ i x)) +
          (∫ x in U, u x i * v x j * (dη j x * spatialDeriv ψ i x))) +
        ((∫ x in U, η x * u x i * v x j * mixedSecond ψ i j x) +
          (∫ x in U, u x i * Du x j j * (η x * spatialDeriv ψ i x))) = 0 := by
      calc
        _ =
          (∫ x in U, Du x i j * v x j * (η x * spatialDeriv ψ i x)) +
          (∫ x in U, u x i * v x j * (dη j x * spatialDeriv ψ i x)) +
          (∫ x in U, η x * u x i * v x j * mixedSecond ψ i j x) +
          (∫ x in U, u x i * Du x j j * (η x * spatialDeriv ψ i x)) := by ring
        _ = 0 := hzero
    have hgoal :
        (∫ x in U, Du x i j * v x j * (η x * spatialDeriv ψ i x)) +
          (∫ x in U, u x i * v x j * (dη j x * spatialDeriv ψ i x)) =
        -((∫ x in U, η x * u x i * v x j * mixedSecond ψ i j x) +
          (∫ x in U, u x i * Du x j j * (η x * spatialDeriv ψ i x))) :=
      eq_neg_iff_add_eq_zero.mpr hzero'
    calc
      _ = _ := hgoal
      _ = _ := by
        rw [neg_add]
        exact (sub_eq_add_neg
          (-(∫ x in U, η x * u x i * v x j * mixedSecond ψ i j x))
          (∫ x in U, u x i * Du x j j *
            (η x * spatialDeriv ψ i x))).symm
  have htraceZero :
      ∑ i : Fin 3, ∑ j : Fin 3,
        ∫ x in U, u x i * Du x j j *
          (η x * spatialDeriv ψ i x) = 0 := by
    have hterm (i j : Fin 3) : IntegrableOn
        (fun x => u x i * Du x j j *
          (η x * spatialDeriv ψ i x)) U volume := htraceFactor i j
    have hsum :
        ∑ i : Fin 3, ∑ j : Fin 3,
          ∫ x in U, u x i * Du x j j *
            (η x * spatialDeriv ψ i x) =
        ∫ x in U, ∑ i : Fin 3, ∑ j : Fin 3,
          u x i * Du x j j * (η x * spatialDeriv ψ i x) := by
      rw [integral_finsetSum]
      · congr 1
        funext i
        rw [integral_finsetSum]
        intro j hj
        exact hterm i j
      · intro i hi
        exact integrable_finsetSum' (Finset.univ : Finset (Fin 3))
          (fun j _ => hterm i j)
    rw [hsum]
    apply integral_eq_zero_of_ae
    filter_upwards [htrace] with x hx
    have hdiag : ∑ j : Fin 3, Du x j j = 0 := by simpa using hx
    have heq (x : Vec3) : (∑ i : Fin 3, ∑ j : Fin 3,
        u x i * Du x j j * (η x * spatialDeriv ψ i x)) =
        ∑ i : Fin 3, u x i * (η x * spatialDeriv ψ i x) *
          (∑ j : Fin 3, Du x j j) := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        ∑ j : Fin 3, u x i * Du x j j * (η x * spatialDeriv ψ i x) =
            ∑ j : Fin 3, (u x i * (η x * spatialDeriv ψ i x)) * Du x j j := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
        _ = u x i * (η x * spatialDeriv ψ i x) *
            (∑ j : Fin 3, Du x j j) := by rw [Finset.mul_sum]
    rw [heq x, hdiag]
    simp
  have hsourceIntegrable (i : Fin 3) : IntegrableOn
      (fun x => pressureDivergenceCutoffSourceCentredTensor η dη u Du c x i *
        spatialDeriv ψ i x) U volume := by
    have hterms : ∀ j : Fin 3, IntegrableOn
        (fun x => (η x * Du x i j * v x j + dη j x * u x i * v x j) *
          spatialDeriv ψ i x) U volume := by
      intro j
      exact ((hsourceEta i j).add (hsourceDη i j)).congr
        (Filter.Eventually.of_forall fun x => by
          simp only [Pi.add_apply]
          ring)
    have hsum := integrable_finsetSum' (Finset.univ : Finset (Fin 3))
      (fun j _ => hterms j)
    have heq : (fun x => pressureDivergenceCutoffSourceCentredTensor
        η dη u Du c x i * spatialDeriv ψ i x) =
        fun x => ∑ j, (η x * Du x i j * v x j +
          dη j x * u x i * v x j) * spatialDeriv ψ i x := by
      funext x
      simp [pressureDivergenceCutoffSourceCentredTensor, v, Finset.sum_mul]
    rw [heq]
    exact hsum
  have hsourceSum :
      (∑ i : Fin 3, ∫ x in U,
        pressureDivergenceCutoffSourceCentredTensor η dη u Du c x i *
          spatialDeriv ψ i x) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        ∫ x in U,
          (η x * Du x i j * v x j + dη j x * u x i * v x j) *
            spatialDeriv ψ i x := by
    apply Finset.sum_congr rfl
    intro i hi
    calc
      ∫ x in U,
          pressureDivergenceCutoffSourceCentredTensor η dη u Du c x i *
            spatialDeriv ψ i x =
        ∫ x in U, ∑ j : Fin 3,
          (η x * Du x i j * v x j + dη j x * u x i * v x j) *
            spatialDeriv ψ i x := by
              apply integral_congr_ae
              filter_upwards [] with x
              simp [pressureDivergenceCutoffSourceCentredTensor, v, Finset.sum_mul]
      _ = ∑ j : Fin 3, ∫ x in U,
          (η x * Du x i j * v x j + dη j x * u x i * v x j) *
            spatialDeriv ψ i x := by
              rw [integral_finsetSum (s := Finset.univ)]
              intro j hj
              exact ((hsourceEta i j).add (hsourceDη i j)).congr
                (Filter.Eventually.of_forall fun x => by
                  simp only [Pi.add_apply]
                  ring)
  have hmain :
      (∑ i : Fin 3, ∫ x in U,
        pressureDivergenceCutoffSourceCentredTensor η dη u Du c x i *
          spatialDeriv ψ i x) =
      -∑ i : Fin 3, ∑ j : Fin 3,
        ∫ x in U, η x * u x i * v x j * mixedSecond ψ i j x := by
    rw [hsourceSum]
    have hsumInner (i : Fin 3) :
        (∑ j : Fin 3,
          ((-∫ x in U, η x * u x i * v x j * mixedSecond ψ i j x) -
            (∫ x in U, u x i * Du x j j *
              (η x * spatialDeriv ψ i x)))) =
          -(∑ j : Fin 3,
            ∫ x in U, η x * u x i * v x j * mixedSecond ψ i j x) -
          ∑ j : Fin 3,
            ∫ x in U, u x i * Du x j j *
              (η x * spatialDeriv ψ i x) := by
      calc
        _ = ∑ j : Fin 3,
            ((-∫ x in U, η x * u x i * v x j * mixedSecond ψ i j x) +
              -(∫ x in U, u x i * Du x j j *
                (η x * spatialDeriv ψ i x))) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  exact sub_eq_add_neg
                    (-∫ x in U, η x * u x i * v x j * mixedSecond ψ i j x)
                    (∫ x in U, u x i * Du x j j *
                      (η x * spatialDeriv ψ i x))
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_neg_distrib,
            Finset.sum_neg_distrib]
          exact (sub_eq_add_neg
            (-(∑ j : Fin 3,
              ∫ x in U, η x * u x i * v x j * mixedSecond ψ i j x))
            (∑ j : Fin 3,
              ∫ x in U, u x i * Du x j j *
                (η x * spatialDeriv ψ i x))).symm
    have hsumOuter :
        (∑ i : Fin 3,
          (-(∑ j : Fin 3,
              ∫ x in U, η x * u x i * v x j * mixedSecond ψ i j x) -
            ∑ j : Fin 3,
              ∫ x in U, u x i * Du x j j *
                (η x * spatialDeriv ψ i x))) =
          -(∑ i : Fin 3, ∑ j : Fin 3,
            ∫ x in U, η x * u x i * v x j * mixedSecond ψ i j x) -
          ∑ i : Fin 3, ∑ j : Fin 3,
            ∫ x in U, u x i * Du x j j *
              (η x * spatialDeriv ψ i x) := by
      calc
        _ = ∑ i : Fin 3,
            ((-(∑ j : Fin 3,
                ∫ x in U, η x * u x i * v x j * mixedSecond ψ i j x)) -
              (∑ j : Fin 3,
                ∫ x in U, u x i * Du x j j *
                  (η x * spatialDeriv ψ i x))) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    exact sub_eq_add_neg _ _
        _ = _ := by
          rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    calc
      _ = ∑ i : Fin 3, ∑ j : Fin 3,
          ((-∫ x in U, η x * u x i * v x j * mixedSecond ψ i j x) -
            (∫ x in U, u x i * Du x j j *
              (η x * spatialDeriv ψ i x))) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          exact hsourceTerm i j
      _ = -(∑ i : Fin 3, ∑ j : Fin 3,
          ∫ x in U, η x * u x i * v x j * mixedSecond ψ i j x) -
          ∑ i : Fin 3, ∑ j : Fin 3,
            ∫ x in U, u x i * Du x j j *
              (η x * spatialDeriv ψ i x) := by
          calc
            _ = ∑ i : Fin 3,
                (-(∑ j : Fin 3,
                    ∫ x in U, η x * u x i * v x j * mixedSecond ψ i j x) -
                  (∑ j : Fin 3,
                    ∫ x in U, u x i * Du x j j *
                      (η x * spatialDeriv ψ i x))) := by
                        apply Finset.sum_congr rfl
                        intro i hi
                        exact hsumInner i
            _ = _ := hsumOuter
      _ = -∑ i : Fin 3, ∑ j : Fin 3,
          ∫ x in U, η x * u x i * v x j * mixedSecond ψ i j x := by
          rw [htraceZero]
          simp
  have htargetIntegrable (i j : Fin 3) : IntegrableOn
      (fun x => η x * (-(u x i) * v x j) * mixedSecond ψ i j x)
      U volume := by
    exact (centred_tensor_pair_memLp_integrable hU (hu i) (hv j)
      (hη.mul (hψm i j)) (hηc.mul_right (f' := mixedSecond ψ i j))
      ((tsupport_mul_subset_left (f := η) (g := mixedSecond ψ i j)).trans hηU)).neg.congr
      (Filter.Eventually.of_forall fun x => by
        simp only [Pi.neg_apply]
        ring)
  have htargetSum :
      ∫ x in U, ∑ i : Fin 3, ∑ j : Fin 3,
        η x * (-(u x i) * v x j) * mixedSecond ψ i j x =
      ∑ i : Fin 3, ∑ j : Fin 3,
        ∫ x in U, η x * (-(u x i) * v x j) * mixedSecond ψ i j x := by
    rw [integral_finsetSum]
    · congr 1
      funext i
      rw [integral_finsetSum]
      intro j hj
      exact htargetIntegrable i j
    · intro i hi
      exact integrable_finsetSum' (Finset.univ : Finset (Fin 3))
        (fun j _ => htargetIntegrable i j)
  have htargetOutside : ∀ x ∉ U, ∑ i : Fin 3, ∑ j : Fin 3,
      η x * (-(u x i) * v x j) * mixedSecond ψ i j x = 0 := by
    intro x hx
    have hηzero : η x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hxη => hx (hηU hxη))
    simp [hηzero]
  have hpair :
      pressureSecondPairing
        (fun i j x => η x * (-(u x i) * v x j)) ψ =
      -∑ i : Fin 3, ∑ j : Fin 3,
        ∫ x in U, η x * u x i * v x j * mixedSecond ψ i j x := by
    unfold pressureSecondPairing
    calc
      ∫ x, ∑ i : Fin 3, ∑ j : Fin 3,
          η x * (-(u x i) * v x j) * mixedSecond ψ i j x =
        ∫ x in U, ∑ i : Fin 3, ∑ j : Fin 3,
          η x * (-(u x i) * v x j) * mixedSecond ψ i j x := by
            symm
            exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
              (s := U) htargetOutside
      _ = ∑ i : Fin 3, ∑ j : Fin 3,
          ∫ x in U, η x * (-(u x i) * v x j) * mixedSecond ψ i j x := htargetSum
      _ = -∑ i : Fin 3, ∑ j : Fin 3,
          ∫ x in U, η x * u x i * v x j * mixedSecond ψ i j x := by
            calc
              ∑ i : Fin 3, ∑ j : Fin 3,
                  ∫ x in U, η x * (-(u x i) * v x j) * mixedSecond ψ i j x =
                ∑ i : Fin 3, ∑ j : Fin 3,
                  -(∫ x in U, η x * u x i * v x j * mixedSecond ψ i j x) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    apply Finset.sum_congr rfl
                    intro j hj
                    rw [← integral_neg]
                    apply integral_congr_ae
                    filter_upwards [] with x
                    ring
              _ = -∑ i : Fin 3, ∑ j : Fin 3,
                    ∫ x in U, η x * u x i * v x j * mixedSecond ψ i j x := by
                      simp only [Finset.sum_neg_distrib]
  have hsourceOutside (i : Fin 3) :
      ∀ x ∉ U, pressureDivergenceCutoffSourceCentredTensor η dη u Du c x i *
        spatialDeriv ψ i x = 0 := by
    intro x hx
    have hηzero : η x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hxη => hx (hηU hxη))
    have hdηzero (j : Fin 3) : dη j x = 0 := by
      have hsup : tsupport (dη j) ⊆ tsupport η := by
        rw [hdη j]
        exact tsupport_fderiv_apply_subset ℝ (basisVec j)
      exact image_eq_zero_of_notMem_tsupport (fun hxd => hx (hηU (hsup hxd)))
    simp [pressureDivergenceCutoffSourceCentredTensor, hηzero, hdηzero]
  have hsourceGlobal :
      (∑ i : Fin 3, ∫ x,
        pressureDivergenceCutoffSourceCentredTensor η dη u Du c x i *
          spatialDeriv ψ i x) =
      ∑ i : Fin 3, ∫ x in U,
        pressureDivergenceCutoffSourceCentredTensor η dη u Du c x i *
          spatialDeriv ψ i x := by
    apply Finset.sum_congr rfl
    intro i hi
    symm
    exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := U) (hsourceOutside i)
  rw [hsourceGlobal, hmain, hpair]

end CKN.Core.Step4
