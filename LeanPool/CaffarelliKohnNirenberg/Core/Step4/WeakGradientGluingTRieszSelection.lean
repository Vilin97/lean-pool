/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakGradientGluingTGlobalSelection
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.ConcreteRieszConsumption
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.LpExtensionPairingMain
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientPotential

/-! # Jointly measurable representatives of the completed Riesz operator

The first potential is jointly measurable. Its spatial weak derivatives are
the negatives of the completed Riesz operator, so measurable derivative
selection gives representatives of that operator with the correct sign.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Foundation.Heat

noncomputable section
namespace CKN.Core.Step4

/-- The first Newtonian derivative potential of jointly measurable data is
jointly measurable in space and time. -/
theorem measurable_spacetime_newtonian_derivative_potential (j : Fin 3)
    {F : Vec3 × ℝ → ℝ} (hF : Measurable F) :
    Measurable (fun z : Vec3 × ℝ =>
      pressureNewtonianDerivativePotential j (fun y => F (y, z.2)) z.1) := by
  have hK : Measurable (spatialDeriv newtonianKernel j) :=
    measurable_fderiv_apply_const ℝ newtonianKernel (basisVec j)
  have hInt : StronglyMeasurable (fun q : (Vec3 × ℝ) × Vec3 =>
      spatialDeriv newtonianKernel j (q.1.1 - q.2) * F (q.2, q.1.2)) :=
    ((hK.comp ((measurable_fst.comp measurable_fst).sub measurable_snd)).mul
      (hF.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))).stronglyMeasurable
  exact (hInt.integral_prod_right' (ν := (volume : Measure Vec3))).measurable

/-- Compactly supported `L^{6/5}` slices admit one jointly measurable
representative of the completed indexed Riesz operator, with equality on
almost every spatial slice over the whole time axis. -/
theorem exists_measurable_riesz_extension_field (j i : Fin 3)
    {F : Vec3 × ℝ → ℝ} (hF : Measurable F)
    (hFs : ∀ᵐ s ∂volume,
      MemLp (fun y => F (y, s)) (ENNReal.ofReal (6 / 5 : ℝ)) volume ∧
      HasCompactSupport (fun y => F (y, s))) :
    ∃ T : Vec3 × ℝ → ℝ, Measurable T ∧
      ∀ᵐ s ∂volume, (fun y => T (y, s)) =ᵐ[volume]
        rieszSecondGradientExtensionOperator
          (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i) (fun y => F (y, s)) := by
  let P : Vec3 × ℝ → ℝ := fun z =>
    pressureNewtonianDerivativePotential j (fun y => F (y, z.2)) z.1
  let G : ℝ → Vec3 → ℝ := fun s y =>
    -(rieszSecondGradientExtensionOperator
      (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i) (fun y => F (y, s)) y)
  have hPmeas : Measurable P := measurable_spacetime_newtonian_derivative_potential j hF
  have hPloc : ∀ᵐ s ∂volume, LocallyIntegrable (fun y => P (y, s)) volume := by
    filter_upwards [hFs] with s hs
    exact pressureNewtonianDerivativePotential_locallyIntegrable j
      (memLp_six_fifths_integrable_of_hasCompactSupport hs.1 hs.2) hs.2
  have hG : ∀ᵐ s ∂volume, LocallyIntegrable (G s) volume ∧
      HasWeakPartialDerivOn univ i (fun y => P (y, s)) (G s) := by
    filter_upwards [hFs] with s hs
    have hmem := rieszSecondGradientExtension_memLp
      (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i) hs.1 hs.2
    refine ⟨hmem.neg.locallyIntegrable (by norm_num), ?_⟩
    intro ψ hψ hψc _hψs
    simp only [Measure.restrict_univ]
    have hpair := pressureNewtonianDerivativePotential_gradient_extension_pairing
      (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i) hs.1 hs.2 hψ hψc
    simpa only [P, G, spatialDeriv, neg_mul, integral_neg, neg_neg] using hpair
  obtain ⟨D, hD, hid⟩ := exists_measurable_global_slice_derivative i hPmeas hPloc
    (hG.mono (fun s hs => ⟨G s, hs⟩))
  refine ⟨fun z => -D z, hD.neg, ?_⟩
  filter_upwards [hid, hG] with s hs hg
  filter_upwards [hs (G s) hg.1 hg.2] with y hy
  simp only [hy, G, neg_neg]

/-- Almost-everywhere measurable sources with a fixed compact spatial support
have jointly measurable completed Riesz representatives. The spatial support
is imposed on the measurable source representative pointwise. -/
theorem exists_measurable_riesz_extension_field_of_aemeasurable (j i : Fin 3)
    {F : Vec3 × ℝ → ℝ} (hF : AEMeasurable F volume)
    {K : Set Vec3} (hK : IsCompact K)
    (hsupport : ∀ y s, y ∉ K → F (y, s) = 0)
    (hFs : ∀ᵐ s ∂volume,
      MemLp (fun y => F (y, s)) (ENNReal.ofReal (6 / 5 : ℝ)) volume) :
    ∃ T : Vec3 × ℝ → ℝ, Measurable T ∧
      ∀ᵐ s ∂volume, (fun y => T (y, s)) =ᵐ[volume]
        rieszSecondGradientExtensionOperator
          (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i) (fun y => F (y, s)) := by
  let F₀ : Vec3 × ℝ → ℝ := (K ×ˢ (univ : Set ℝ)).indicator (hF.mk F)
  have hm : Measurable F₀ := hF.measurable_mk.indicator (hK.measurableSet.prod MeasurableSet.univ)
  have heq : F =ᵐ[volume] F₀ := by
    filter_upwards [hF.ae_eq_mk] with z hz
    by_cases hx : z.1 ∈ K
    · exact hz.trans (Set.indicator_of_mem (show z ∈ K ×ˢ (univ : Set ℝ) from
        ⟨hx, mem_univ _⟩) (hF.mk F)).symm
    · rw [hsupport z.1 z.2 hx]
      exact (Set.indicator_of_notMem (fun h => hx h.1) (hF.mk F)).symm
  have hs : ∀ᵐ s ∂volume, (fun y => F (y, s)) =ᵐ[volume] (fun y => F₀ (y, s)) := by
    have heq' := heq
    rw [volume_eq_prod] at heq'
    exact ae_ae_of_ae_prod_snd heq'
  have hcompact (s : ℝ) : HasCompactSupport (fun y => F₀ (y, s)) := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    intro y hy
    by_contra hyK
    exact hy (Set.indicator_of_notMem (fun h => hyK h.1) (hF.mk F))
  have hF₀s : ∀ᵐ s ∂volume,
      MemLp (fun y => F₀ (y, s)) (ENNReal.ofReal (6 / 5 : ℝ)) volume ∧
      HasCompactSupport (fun y => F₀ (y, s)) := by
    filter_upwards [hs, hFs] with s he hf
    exact ⟨hf.ae_eq he, hcompact s⟩
  obtain ⟨T, hT, hid⟩ := exists_measurable_riesz_extension_field j i hm hF₀s
  refine ⟨T, hT, ?_⟩
  filter_upwards [hid, hs, hFs, hF₀s] with s ht he hf hf₀
  apply ht.trans
  let _ : Fact (1 ≤ ENNReal.ofReal (6 / 5 : ℝ)) := ⟨by norm_num⟩
  exact lpExtensionRepresentative_congr_ae (by norm_num)
    (rieszSecondGradientExtensionInput (rieszSecondL2Input j i)
      (rieszSecondL2_weak_type j i)) hf₀.1 hf he.symm

end CKN.Core.Step4
