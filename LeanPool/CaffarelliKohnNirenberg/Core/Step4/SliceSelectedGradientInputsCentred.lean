/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientCentredSourceTensorDef
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientSWSFinal
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientInputs
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.CZUnconditional
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Slice

/-!
# Slice Selected Gradient Inputs Centred

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
open CKN.Foundation.Euclidean CKN.Foundation.Heat

noncomputable section

namespace CKN.Core.Step4

/-- The spatial velocity mean used in the centred source at each time. -/
@[expose]
def sourceSliceCentredMean (x : Vec3) (ρ : ℝ)
    (u : ParabolicPoint → Vec3) : ℝ → Vec3 :=
  fun s j => average (volume.restrict (vec3Ball x ρ))
    (fun y : Vec3 => u (y, s) j)

/-- The centred velocity component is bounded by its mean absolute value. -/
theorem centred_source_average_component_bound
    {x : Vec3} {ρ s : ℝ} {u : ParabolicPoint → Vec3} (j : Fin 3) :
    ‖sourceSliceCentredMean x ρ u s j‖ ≤
      ⨍ y in vec3Ball x ρ, |u (y, s) j| := by
  have havg : average (volume.restrict (vec3Ball x ρ))
      (fun y : Vec3 => u (y, s) j) =
      spatialAverage x ρ s (fun z : ParabolicPoint => u z j) := by
    rw [MeasureTheory.average_eq (μ := volume.restrict (vec3Ball x ρ))]
    simp only [MeasureTheory.measureReal_restrict_apply_univ]
    rw [spatialAverage_eq_toReal_inv_smul]
    rfl
  change ‖average (volume.restrict (vec3Ball x ρ))
      (fun y : Vec3 => u (y, s) j)‖ ≤
    ⨍ y in vec3Ball x ρ, |u (y, s) j|
  rw [havg, Real.norm_eq_abs]
  exact spatialAverage_abs_le

/-- The force-free centred source is estimated by the full uncentred source,
the constant-mean correction, and the force term which removes `−η f`. -/
theorem sourceMorreyCutoffVCentredTensor_slice_bound_of_uncentred
    {B : Set Vec3} {η : Vec3 → ℝ} {dη : Fin 3 → Vec3 → ℝ}
    {u : Vec3 → Vec3} {Du : Vec3 → Fin 3 → Vec3} {f : Vec3 → Vec3}
    {c : Vec3} {i : Fin 3} {Cη Cdη Cc : ℝ}
    {KU KD Kunc Kforce : ℝ≥0∞}
    (hCη : 0 ≤ Cη) (hCdη : 0 ≤ Cdη) (hCc : 0 ≤ Cc)
    (hη : AEStronglyMeasurable η (volume.restrict B))
    (hdη : ∀ j : Fin 3,
      AEStronglyMeasurable (dη j) (volume.restrict B))
    (hηbound : ∀ᵐ x ∂(volume.restrict B), ‖η x‖ ≤ Cη)
    (hdηbound : ∀ j : Fin 3,
      ∀ᵐ x ∂(volume.restrict B), ‖dη j x‖ ≤ Cdη)
    (hc : ∀ j : Fin 3, ‖c j‖ ≤ Cc)
    (hUmeas : AEStronglyMeasurable (fun x => u x i)
      (volume.restrict B))
    (hDmeas : ∀ j : Fin 3,
      AEStronglyMeasurable (fun x => Du x i j) (volume.restrict B))
    (hU : eLpNorm (fun x => u x i) (ENNReal.ofReal (6 / 5 : ℝ))
      (volume.restrict B) ≤ KU)
    (hD : ∀ j : Fin 3,
      eLpNorm (fun x => Du x i j) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict B) ≤ KD)
    (hunc : eLpNorm
      (fun x => pressureDivergenceCutoffSource η dη u Du f x i)
      (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B) ≤ Kunc)
    (hforce : eLpNorm (fun x => η x * f x i)
      (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B) ≤ Kforce) :
    eLpNorm
        (fun x => sourceMorreyCutoffVCentredTensor η dη u Du c x i)
        (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B) ≤
      Kunc + ENNReal.ofReal Cc *
        (∑ _j : Fin 3, (ENNReal.ofReal Cη * KD +
          ENNReal.ofReal Cdη * KU)) + Kforce := by
  have hcent := sourceMorreyCutoffVCentred_slice_bound_of_uncentred
    hCη hCdη hCc hη hdη hηbound hdηbound hc hUmeas hDmeas hU hD hunc
  exact (sourceMorreyCutoffVCentredTensor_slice_bound_le_full_add_force
    (B := B) (η := η) (dη := dη) (u := u) (Du := Du) (f := f)
    (c := c) (i := i) (p := ENNReal.ofReal (6 / 5 : ℝ)) (by norm_num)).trans
    (add_le_add hcent hforce)

/-- Slice estimate for the force-free centred source, with the centring
constant bounded by the sum of the mean absolute velocities.  The input
`hsourceBound` is the vector-valued uncentred estimate supplied by
`sourceMorreyCutoffV_slice_bound`. -/
theorem sourceMorreyCutoffVCentredTensor_slice_bound_of_sourceMorrey
    {B : Set Vec3} {x : Vec3} {ρ s : ℝ}
    {η : Vec3 → ℝ} {dη : Fin 3 → Vec3 → ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {f : ParabolicPoint → Vec3} {Cη Cdη : ℝ}
    {KU KD Kunc : ℝ≥0∞} {Kforce : Fin 3 → ℝ≥0∞}
    (hCη : 0 ≤ Cη) (hCdη : 0 ≤ Cdη)
    (hη : AEStronglyMeasurable η (volume.restrict B))
    (hdη : ∀ j : Fin 3,
      AEStronglyMeasurable (dη j) (volume.restrict B))
    (hηbound : ∀ᵐ y ∂(volume.restrict B), ‖η y‖ ≤ Cη)
    (hdηbound : ∀ j : Fin 3,
      ∀ᵐ y ∂(volume.restrict B), ‖dη j y‖ ≤ Cdη)
    (hUmeas : ∀ j : Fin 3,
      AEStronglyMeasurable (fun y => u (y, s) j) (volume.restrict B))
    (hDmeas : ∀ i j : Fin 3,
      AEStronglyMeasurable (fun y => Du (y, s) i j)
        (volume.restrict B))
    (hU : ∀ j : Fin 3,
      eLpNorm (fun y => u (y, s) j) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict B) ≤ KU)
    (hD : ∀ i j : Fin 3,
      eLpNorm (fun y => Du (y, s) i j) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict B) ≤ KD)
    (hsourceMeas : AEStronglyMeasurable
      (fun y => sourceMorreyCutoffV η dη
        (fun y => u (y, s)) (fun y i j => Du (y, s) i j)
        (fun y => f (y, s)) y) (volume.restrict B))
    (hsourceBound : eLpNorm
      (fun y => sourceMorreyCutoffV η dη
        (fun y => u (y, s)) (fun y i j => Du (y, s) i j)
        (fun y => f (y, s)) y)
      (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B) ≤ Kunc)
    (hforce : ∀ i : Fin 3,
      eLpNorm (fun y => η y * f (y, s) i)
        (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B) ≤ Kforce i) :
    ∀ i : Fin 3,
      eLpNorm (fun y => sourceMorreyCutoffVCentredTensor η dη
        (fun y => u (y, s)) (fun y i j => Du (y, s) i j)
        (sourceSliceCentredMean x ρ u s) y i)
        (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B) ≤
      Kunc + ENNReal.ofReal
          (∑ j : Fin 3, ⨍ y in vec3Ball x ρ, |u (y, s) j|) *
        (∑ _j : Fin 3, (ENNReal.ofReal Cη * KD +
          ENNReal.ofReal Cdη * KU)) + Kforce i := by
  let Cc : ℝ := ∑ j : Fin 3, ⨍ y in vec3Ball x ρ, |u (y, s) j|
  have hmeanNonneg (j : Fin 3) :
      0 ≤ ⨍ y in vec3Ball x ρ, |u (y, s) j| := by
    apply setAverage_nonneg_of_ae
    exact Filter.Eventually.of_forall fun _ => abs_nonneg _
  have hCc : 0 ≤ Cc := by
    dsimp [Cc]
    exact Finset.sum_nonneg fun j hj => hmeanNonneg j
  have hc : ∀ j : Fin 3, ‖sourceSliceCentredMean x ρ u s j‖ ≤ Cc := by
    intro j
    calc
      ‖sourceSliceCentredMean x ρ u s j‖ ≤
          ⨍ y in vec3Ball x ρ, |u (y, s) j| :=
        centred_source_average_component_bound j
      _ ≤ Cc := by
        dsimp [Cc]
        exact Finset.single_le_sum
          (fun k hk => hmeanNonneg k) (Finset.mem_univ j)
  have hsourceComponent : ∀ i : Fin 3,
      eLpNorm (fun y => sourceMorreyCutoffV η dη
        (fun y => u (y, s)) (fun y a j => Du (y, s) a j)
        (fun y => f (y, s)) y i)
        (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B) ≤ Kunc := by
    intro i
    have hmono := eLpNorm_mono_ae
      (f := fun y => sourceMorreyCutoffV η dη
        (fun y => u (y, s)) (fun y a j => Du (y, s) a j)
        (fun y => f (y, s)) y i)
      (g := fun y => sourceMorreyCutoffV η dη
        (fun y => u (y, s)) (fun y a j => Du (y, s) a j)
        (fun y => f (y, s)) y)
      (μ := volume.restrict B) (p := ENNReal.ofReal (6 / 5 : ℝ))
      ((ContinuousLinearMap.proj (R := ℝ) i).continuous.comp_aestronglyMeasurable
        hsourceMeas)
      (Filter.Eventually.of_forall fun y =>
        norm_le_pi_norm
          (sourceMorreyCutoffV η dη (fun y => u (y, s))
            (fun y a j => Du (y, s) a j) (fun y => f (y, s)) y) i)
    exact hmono.trans hsourceBound
  intro i
  have hcomponent := sourceMorreyCutoffVCentredTensor_slice_bound_of_uncentred
    hCη hCdη hCc hη hdη hηbound hdηbound hc (hUmeas i) (hDmeas i)
    (hU i) (hD i) (hsourceComponent i) (hforce i)
  simpa only [Cc] using hcomponent

private theorem centred_tensor_source_zero_outside_input
    {U : Set Vec3} {η : Vec3 → ℝ} {dη : Fin 3 → Vec3 → ℝ}
    {u : Vec3 → Vec3} {Du : Vec3 → Fin 3 → Vec3} {c : Vec3}
    (hηsupport : tsupport η ⊆ U)
    (hdηsupport : ∀ j : Fin 3, tsupport (dη j) ⊆ U)
    {x : Vec3} (hx : x ∉ U) :
    sourceMorreyCutoffVCentredTensor η dη u Du c x = 0 := by
  have hηzero : η x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hηx => hx (hηsupport hηx))
  have hdηzero : ∀ j : Fin 3, dη j x = 0 := by
    intro j
    exact image_eq_zero_of_notMem_tsupport
      (fun hdηx => hx (hdηsupport j hdηx))
  funext i
  simp [sourceMorreyCutoffVCentredTensor,
    pressureDivergenceCutoffSourceCentredTensor, hηzero, hdηzero]

/-- Local slice membership and the cutoff support give the global `hV`
predicate for the force-free centred source. -/
theorem slice_selected_gradient_hV_of_centred_tensor_source
    {J : Set ℝ} {U : Set Vec3} {η : Vec3 → ℝ}
    {dη : Fin 3 → Vec3 → ℝ} {c : ℝ → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hUmeas : MeasurableSet U)
    (hηsupport : tsupport η ⊆ U)
    (hdηsupport : ∀ j : Fin 3, tsupport (dη j) ⊆ U)
    (hUcompact : IsCompact U)
    (hlocal : ∀ᵐ s ∂(volume.restrict J), ∀ i : Fin 3,
      MemLp (fun x => sourceMorreyCutoffVCentredTensor η dη
        (fun y => u (y, s)) (fun y i j => Du (y, s) i j) (c s) x i)
        (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict U)) :
    ∀ᵐ s ∂(volume.restrict J),
      (∀ i : Fin 3, MemLp (fun x =>
        sourceMorreyCutoffVCentredTensorSpacetime η dη u Du c (x, s) i)
        (ENNReal.ofReal (6 / 5 : ℝ)) volume) ∧
      (∀ i : Fin 3, HasCompactSupport (fun x =>
        sourceMorreyCutoffVCentredTensorSpacetime η dη u Du c (x, s) i)) := by
  filter_upwards [hlocal] with s hs
  refine ⟨?_, ?_⟩
  · intro i
    have hind : MemLp (U.indicator (fun x =>
        sourceMorreyCutoffVCentredTensor η dη
          (fun y => u (y, s)) (fun y a j => Du (y, s) a j) (c s) x i))
        (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
      (memLp_indicator_iff_restrict hUmeas).2 (hs i)
    have heq : (fun x => sourceMorreyCutoffVCentredTensor η dη
        (fun y => u (y, s)) (fun y a j => Du (y, s) a j) (c s) x i) =
        U.indicator (fun x => sourceMorreyCutoffVCentredTensor η dη
          (fun y => u (y, s)) (fun y a j => Du (y, s) a j) (c s) x i) := by
      funext x
      by_cases hx : x ∈ U
      · simp only [indicator_of_mem hx]
      · simp only [indicator_of_notMem hx]
        exact congrFun
          (centred_tensor_source_zero_outside_input hηsupport hdηsupport hx) i
    rw [show (fun x => sourceMorreyCutoffVCentredTensorSpacetime
        η dη u Du c (x, s) i) =
        (fun x => sourceMorreyCutoffVCentredTensor η dη
          (fun y => u (y, s)) (fun y a j => Du (y, s) a j) (c s) x i) by
          rfl]
    rw [heq]
    exact hind
  · intro i
    simpa only [sourceMorreyCutoffVCentredTensorSpacetime] using
      sourceMorreyCutoffVCentredTensor_hasCompactSupport
        hηsupport hdηsupport hUcompact i

/-- The centred-source consumer uses the force-potential input supplied by
the same solution-level wrapper as the uncentred-source selector. -/
theorem slice_selected_gradient_hP78_input_of_sws_centred
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall z.1 (13 * ρ / 20))) ∧
      lpNorm (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall z.1 (13 * ρ / 20))) ≤
        harmonicRemainderForceBound z hρ f s := by
  exact slice_selected_gradient_hP78_input_of_sws hsol hρ hsub

/-- The unconditional slice selector consumes the force-free centred source
and its tested pairing. -/
theorem slice_selected_gradient_of_sws_centred_source
    (C₁₇ C₁₁ C₈ : ℝ)
    (hC₁₇ : 1000 * harmonicInteriorDisplayConstant ≤ C₁₇)
    (hC₈ : sliceForceGradientConstant ≤ C₈)
    {E : ℝ → ℝ}
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hC₁₁ : 0 ≤ C₁₁) (hE : ∀ s, 0 ≤ E s)
    (hCZ_p1 : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp (pressureP1 (mollifiedBallCutoff z.1 hρ) u
        (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
          (fun y : Vec3 => u (y, t) j)) p f s)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
      lpNorm (pressureP1 (mollifiedBallCutoff z.1 hρ) u
        (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
          (fun y : Vec3 => u (y, t) j)) p f s)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤ C₁₁ * (E s) ^ (2 / 3 : ℝ))
    {η : Vec3 → ℝ} {dη : Fin 3 → Vec3 → ℝ} {U : Set Vec3}
    (hUmeas : MeasurableSet U)
    (hηsupport : tsupport η ⊆ U)
    (hdηsupport : ∀ j : Fin 3, tsupport (dη j) ⊆ U)
    (hUcompact : IsCompact U)
    (hlocal : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ∀ i : Fin 3, MemLp (fun x =>
        sourceMorreyCutoffVCentredTensor η dη
          (fun y => u (y, s)) (fun y i j => Du (y, s) i j)
          (sourceSliceCentredMean z.1 ρ u s) x i)
        (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict U))
    (hVpair : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        (∑ i : Fin 3, ∫ x,
          sourceMorreyCutoffVCentredTensorSpacetime η dη u Du
            (sourceSliceCentredMean z.1 ρ u) (x, s) i * spatialDeriv ψ i x) =
          pressureSecondPairing
            (fun i j x => mollifiedBallCutoff z.1 hρ x *
              pressureUTensor u
                (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
                  (fun y : Vec3 => u (y, t) j)) (x, s) i j) ψ) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ∃ D : Vec3 → Vec3,
        (∀ k : Fin 3, LocallyIntegrableOn (fun x => D x k)
          (euclideanBall z.1 (ρ / 2)) volume) ∧
        MemLp D (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall z.1 (ρ / 2))) ∧
        (∀ k : Fin 3, HasWeakPartialDerivOn
          (euclideanBall z.1 (ρ / 2)) k (fun x => p (x, s))
          (fun x => D x k)) ∧
        (∀ k : Fin 3,
          eLpNorm (fun x => D x k) (ENNReal.ofReal (6 / 5 : ℝ))
            (volume.restrict (euclideanBall z.1 (ρ / 2))) ≤
          ENNReal.ofReal czGradientOperatorConstant *
              (∑ i : Fin 3, eLpNorm (fun x =>
                sourceMorreyCutoffVCentredTensorSpacetime η dη u Du
                  (sourceSliceCentredMean z.1 ρ u) (x, s) i)
                (ENNReal.ofReal (6 / 5 : ℝ)) volume) +
            ENNReal.ofReal (C₁₇ *
              (lpNorm (fun x : Vec3 => p (x, s))
                  (ENNReal.ofReal (3 / 2 : ℝ))
                  (volume.restrict (euclideanBall z.1 ρ)) +
                C₁₁ * (E s) ^ (2 / 3 : ℝ) +
                harmonicRemainderForceBound z hρ f s) *
                  ρ ^ (-1 / 2 : ℝ)) +
            ENNReal.ofReal (sliceForceGradientBound czGradientOperatorConstant
              C₈ z.1 hρ f s)) := by
  have hV := slice_selected_gradient_hV_of_centred_tensor_source
    hUmeas hηsupport hdηsupport hUcompact hlocal
  have hP78 := slice_selected_gradient_hP78_input_of_sws_centred hsol hρ hsub
  have hForceBound : ∀ s, 0 ≤ harmonicRemainderForceBound z hρ f s := by
    intro s
    exact le_max_right _ _
  have hselected := slice_selected_gradient_ae_of_sws_of_source_data_unconditional
    C₁₇ C₁₁ C₈ hC₁₇ hC₈ hsol hρ hsub hC₁₁ hE hForceBound
    hCZ_p1 hP78 hV hVpair
  exact hselected

end CKN.Core.Step4
