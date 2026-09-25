/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTCentredSourceCorrection
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTSuitableIdentification
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginClauseDoubling

/-! # Identification of the prescribed weak pressure gradient on clipped cells

The pressure gradient is the one supplied by the consumer. Uniqueness of
locally integrable weak derivatives identifies it on the intersection of
the consumer carrier and the local pressure ball, on one common time set.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Foundation.Heat
noncomputable section
namespace CKN.Core.Step4

/-- The actual prescribed weak pressure gradient has the fixed signed
centred-source decomposition on each clipped cell and time intersection. -/
theorem ae_actual_pressure_eq_centred_decomposition_on_clipped_cell
    {Ω : Set Vec3} {I : Set ℝ} {q R₁ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f Dp : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hDp : ∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
      LocallyIntegrableOn (fun y => Dp (y,s) i) (vec3Ball (0 : Vec3) R₁) volume ∧
      HasWeakPartialDerivOn (vec3Ball (0 : Vec3) R₁) i
        (fun y => p (y,s)) (fun y => Dp (y,s) i))
    (J : Set ℝ) :
    let η := mollifiedBallCutoff z.1 hρ
    let c := sourceSliceCentredMean z.1 ρ u
    let V := sourceMorreyCutoffVCentredTensorSpacetime η (spatialDeriv η) u Du c
    ∀ᵐ s ∂volume.restrict (Ioc (z.2-ρ^2) z.2 ∩ J), ∀ i : Fin 3,
      (fun y => Dp (y,s) i) =ᵐ[volume.restrict (vec3Ball z.1 (ρ/2) ∩ vec3Ball (0 : Vec3) R₁)]
      fun x => -(∑ j, rieszSecondGradientExtensionOperator
        (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i) (fun y => V (y,s) j) x) +
        classicalGradient (harmonicPressurePart η u c p s + pressureP8 η f s) x i +
        ∑ j, rieszSecondGradientExtensionOperator
          (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i) (fun y => η y * f (y,s) j) x := by
  dsimp only
  have htime : Ioc (z.2-ρ^2) z.2 ⊆ I := by
    intro s hs
    have hx : z.1 ∈ vec3Ball z.1 ρ := by
      simp only [mem_vec3Ball, sub_self, vec3EuclideanNorm_zero]
      exact hρ
    exact (hsub (subset_closure (show (z.1,s) ∈ parabolicCylinder z.1 z.2 ρ from ⟨hx, hs⟩))).2
  have hlocal := centredSWS_selected_gradient_ae
    (1000 * harmonicInteriorDisplayConstant) (max czP1OperatorConstant 0)
    sliceForceGradientConstant le_rfl (le_max_right _ _) (le_max_left _ _) le_rfl
    hsol hρ hsub
  have hid := ae_weak_pressure_derivative_eq_fixed_riesz_of_sws hsol hρ hsub
  have heq : euclideanBall z.1 (ρ/2) = vec3Ball z.1 (ρ/2) :=
    CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball (by positivity)
  have hA : IsOpen (vec3Ball z.1 (ρ/2) ∩ vec3Ball (0 : Vec3) R₁) :=
    (isOpen_vec3Ball _ _).inter (isOpen_vec3Ball _ _)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hlocal,
    ae_restrict_of_ae_restrict_of_subset inter_subset_left hid,
    ae_restrict_of_ae_restrict_of_subset (inter_subset_left.trans htime) hDp] with s hs hi hd
  obtain ⟨g, hgl, _hgm, hgw, _hgb⟩ := hs
  rw [heq] at hgl hgw
  intro i
  have hident := hi i (fun y => g y i) (hgl i) (hgw i)
  have huniq := HasWeakPartialDerivOn.ae_eq hA
    ((hd i).1.mono_set inter_subset_right) ((hgl i).mono_set inter_subset_left)
    ((hd i).2.restrict hA inter_subset_right) ((hgw i).restrict hA inter_subset_left)
  exact huniq.trans (ae_restrict_of_ae_restrict_of_subset inter_subset_left hident)

/-- Suitability supplies the raw localized divergence source's operator-domain
regularity on almost every slice of its cylinder. -/
theorem raw_divergence_source_memLp_ae_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2-ρ^2) z.2), ∀ j : Fin 3,
      MemLp ((vec3Ball z.1 ρ).indicator
        (fun y => (∑ k, Du (y,s) j k * u (y,s) k) - f (y,s) j))
        (ENNReal.ofReal (6/5 : ℝ)) volume := by
  let _ : IsFiniteMeasure (volume.restrict (vec3Ball z.1 ρ)) :=
    isFiniteMeasure_restrict.mpr Integration.volume_vec3Ball_lt_top.ne
  let _ : ENNReal.HolderTriple (2 : ℝ≥0∞) 3 (ENNReal.ofReal (6/5 : ℝ)) := by
    have h : (2 : ℝ).HolderTriple 3 (6/5 : ℝ) := by rw [Real.holderTriple_iff]; norm_num
    convert h.ennrealOfReal using 1 <;> norm_num
  filter_upwards [centredSWS_slice_data hsol hρ hsub] with s hs
  intro j
  apply (memLp_indicator_iff_restrict (vec3Ball_measurable _ _)).mpr
  have hp : MemLp (fun y => ∑ k, Du (y,s) j k * u (y,s) k)
      (ENNReal.ofReal (6/5 : ℝ)) (volume.restrict (vec3Ball z.1 ρ)) :=
    memLp_finsetSum' Finset.univ (fun k _ => ((hs.2.1.eval j).eval k).mul (hs.1.eval k))
  exact hp.sub ((hs.2.2.1.eval j).mono_exponent
    (ENNReal.ofReal_le_ofReal (by linarith only [hsol.2.2.2.1] : (6/5 : ℝ) ≤ q)))

/-- The explicit complementary gradient after replacing the centred source
by the raw source on the outer origin ball. -/
def rawCorrectedPressureRemainder
    (R₀ : ℝ) (z : ParabolicPoint) {ρ : ℝ} (hρ : 0 < ρ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (i : Fin 3) (w : ParabolicPoint) : ℝ :=
  let η := mollifiedBallCutoff z.1 hρ
  let c := sourceSliceCentredMean z.1 ρ u
  classicalGradient (harmonicPressurePart η u c p w.2 + pressureP8 η f w.2) w.1 i -
    ∑ j, rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
      (rieszSecondL2_weak_type j i)
      (centredRawSourceCorrection (vec3Ball (0 : Vec3) R₀) η (spatialDeriv η)
        (fun y => u (y,w.2)) (fun y => f (y,w.2)) (fun y => Du (y,w.2)) (c w.2) j) w.1

/-- The consumer's actual weak pressure gradient equals the selected raw
Riesz field plus the explicit complementary gradient on almost every slice
of each clipped cell. No quantitative estimate or choice of `Dp` is assumed. -/
theorem ae_actual_pressure_eq_raw_riesz_corrected_on_clipped_cell
    (R₀ R₁ : ℝ) (hR₁ : 0 < R₁) (hR₁₀ : R₁ ≤ R₀) (hR₀one : R₀ ≤ 1)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f Dp : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hDp : ∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
      LocallyIntegrableOn (fun y => Dp (y,s) i) (vec3Ball (0 : Vec3) R₁) volume ∧
      HasWeakPartialDerivOn (vec3Ball (0 : Vec3) R₁) i
        (fun y => p (y,s)) (fun y => Dp (y,s) i))
    (T : Fin 3 → Fin 3 → ParabolicPoint → ℝ)
    (hT : ∀ j i, ∀ᵐ s ∂volume, (fun y => T j i (y,s)) =ᵐ[volume]
      rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
        (rieszSecondL2_weak_type j i)
        (fun y => (parabolicCylinder (0 : Vec3) 0 R₀).indicator
          (fun w => (∑ k, Du w j k * u w k) - f w j) (y,s)))
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2-(ρ/2)^2) z.2 ∩ Ioc (-(R₁^2)) 0), ∀ i : Fin 3,
      (fun y => Dp (y,s) i) =ᵐ[volume.restrict (vec3Ball z.1 (ρ/2) ∩ vec3Ball (0 : Vec3) R₁)]
      fun x => -(∑ j, T j i (x,s)) + rawCorrectedPressureRemainder R₀ z hρ u Du p f i (x,s) := by
  classical
  let η := mollifiedBallCutoff z.1 hρ
  let c := sourceSliceCentredMean z.1 ρ u
  let W := Ioc (z.2-(ρ/2)^2) z.2 ∩ Ioc (-(R₁^2)) 0
  let A := vec3Ball z.1 (ρ/2) ∩ vec3Ball (0 : Vec3) R₁
  have hR₀ : 0 < R₀ := hR₁.trans_le hR₁₀
  have hout : closure (parabolicCylinder (0 : Vec3) 0 R₀) ⊆ spaceTimeSet Ω I :=
    (closure_mono (parabolicCylinder_mono hR₀.le hR₀one)).trans hdom
  have htime : W ⊆ Ioc (z.2-ρ^2) z.2 := by
    intro s hs
    exact ⟨by dsimp [W] at hs; nlinarith only [hs.1.1, sq_nonneg ρ], hs.1.2⟩
  have houter : W ⊆ Ioc (0-R₀^2) 0 := by
    intro s hs
    exact ⟨by dsimp [W] at hs; nlinarith only [hs.2.1, hR₁, hR₁₀], hs.2.2⟩
  have ht : ∀ᵐ s ∂volume, ∀ j i, (fun y => T j i (y,s)) =ᵐ[volume]
      rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
        (rieszSecondL2_weak_type j i)
        (fun y => (parabolicCylinder (0 : Vec3) 0 R₀).indicator
          (fun w => (∑ k, Du w j k * u w k) - f w j) (y,s)) := by
    simp only [ae_all_iff]
    exact hT
  have hfixed := ae_actual_pressure_eq_centred_decomposition_on_clipped_cell hsol hρ hsub hDp
    (Ioc (-(R₁^2)) 0)
  have hV := centredSWS_source_data_ae (z := z) hsol hρ hsub c
  have hF := slice_force_source_data_ae_of_sws (z := z) hsol hρ hsub
  have hG := raw_divergence_source_memLp_ae_of_sws (z := ((0 : Vec3), 0)) hsol hR₀ hout
  filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (show W ⊆ Ioc (z.2-ρ^2) z.2 ∩ Ioc (-(R₁^2)) 0 from fun s hs => ⟨htime hs, hs.2⟩) hfixed,
    ae_restrict_of_ae_restrict_of_subset htime hV,
    ae_restrict_of_ae_restrict_of_subset htime hF,
    ae_restrict_of_ae_restrict_of_subset houter hG,
    ae_restrict_of_ae ht, ae_restrict_mem (measurableSet_Ioc.inter measurableSet_Ioc)]
    with s hds hvs hfs hgs hts hsW
  intro i
  have hcorr := signed_centred_riesz_eq_raw_corrected_ae (vec3Ball (0 : Vec3) R₀) A
    η (spatialDeriv η) (fun y => u (y,s)) (fun y => f (y,s)) (fun y => Du (y,s)) (c s) i
    hvs.1 hfs.2.1 hgs
  have hts' (j : Fin 3) : (fun y => T j i (y,s)) =ᵐ[volume]
      rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
        (rieszSecondL2_weak_type j i)
        ((vec3Ball (0 : Vec3) R₀).indicator (fun y => (∑ k, Du (y,s) j k*u (y,s) k)-f (y,s) j)) :=
          by
    have hj := hts j i
    have heq : (fun y => (parabolicCylinder (0 : Vec3) 0 R₀).indicator
        (fun w => (∑ k, Du w j k*u w k)-f w j) (y,s)) =
        (vec3Ball (0 : Vec3) R₀).indicator (fun y => (∑ k, Du (y,s) j k*u (y,s) k)-f (y,s) j) := by
      funext y
      have hs : s ∈ Ioc (0-R₀^2) 0 := houter hsW
      by_cases hy : y ∈ vec3Ball (0 : Vec3) R₀
      · exact (Set.indicator_of_mem (α := ParabolicPoint)
          (show ((y,s) : ParabolicPoint) ∈ parabolicCylinder (0 : Vec3) 0 R₀ from ⟨hy, hs⟩) _).trans
          (Set.indicator_of_mem hy (fun y => (∑ k, Du (y,s) j k*u (y,s) k)-f (y,s) j)).symm
      · exact (Set.indicator_of_notMem (α := ParabolicPoint)
          (show ((y,s) : ParabolicPoint) ∉ parabolicCylinder (0 : Vec3) 0 R₀ from fun h => hy h.1)
            _).trans
          (Set.indicator_of_notMem hy (fun y => (∑ k, Du (y,s) j k*u (y,s) k)-f (y,s) j)).symm
    simpa only [heq] using hj
  have hall : ∀ᵐ x ∂volume.restrict A, ∀ j : Fin 3,
      T j i (x,s) = rieszSecondGradientExtensionOperator (rieszSecondL2Input j i)
        (rieszSecondL2_weak_type j i)
        ((vec3Ball (0 : Vec3) R₀).indicator (fun y => (∑ k, Du (y,s) j k*u (y,s) k)-f (y,s) j)) x
          := by
    rw [ae_all_iff]
    exact fun j => ae_restrict_of_ae (hts' j)
  filter_upwards [hds i, hcorr, hall] with x hx hc htj
  have hsum := Finset.sum_congr (rfl : (Finset.univ : Finset (Fin 3)) = Finset.univ) (fun j _ =>
    htj j)
  dsimp only [rawCorrectedPressureRemainder]
  rw [hsum]
  change Dp (x,s) i = _ at hx
  dsimp only [η, c, sourceMorreyCutoffVCentredTensorSpacetime,
    sourceMorreyCutoffVCentredTensor] at hx hc
  linarith only [hx, hc]

end CKN.Core.Step4
