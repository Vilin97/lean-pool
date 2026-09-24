/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.CaccioppoliRHS
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Caccioppoli Energy Tools

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
open CKN.Foundation.Heat


noncomputable section

namespace CKN

lemma caccioppoli_timePartial_zero_of_not_mem_tsupport
    {F : Vec3 × ℝ → ℝ} (_ : ContDiff ℝ (⊤ : ℕ∞) F)
    {z : Vec3 × ℝ} (hz : z ∉ tsupport F) : timePartial F z = 0 := by
  change (fderiv ℝ (fun s : ℝ => F (z.1, s)) z.2) 1 = 0
  have hopen : (tsupport F)ᶜ ∈ 𝓝 z :=
    (isClosed_tsupport F).isOpen_compl.mem_nhds hz
  have hmap : Continuous (fun s : ℝ => (z.1, s)) :=
    Continuous.prodMk continuous_const continuous_id
  have hev : (fun s : ℝ => F (z.1, s)) =ᶠ[𝓝 z.2] (fun _ => (0 : ℝ)) := by
    filter_upwards [hmap.continuousAt.preimage_mem_nhds hopen] with s hs
    by_contra hne
    exact hs (subset_tsupport (f := F) (Function.mem_support.mpr hne))
  rw [hev.fderiv_eq, fderiv_const_apply]
  simp

lemma caccioppoli_spatialPartial_zero_of_not_mem_tsupport
    {F : Vec3 × ℝ → ℝ} (_ : ContDiff ℝ (⊤ : ℕ∞) F)
    {z : Vec3 × ℝ} (hz : z ∉ tsupport F) (i : Fin 3) :
    spatialPartial F i z = 0 := by
  change (fderiv ℝ (fun x : Vec3 => F (x, z.2)) z.1) (basisVec i) = 0
  have hopen : (tsupport F)ᶜ ∈ 𝓝 z :=
    (isClosed_tsupport F).isOpen_compl.mem_nhds hz
  have hmap : Continuous (fun x : Vec3 => (x, z.2)) :=
    Continuous.prodMk continuous_id continuous_const
  have hev : (fun x : Vec3 => F (x, z.2)) =ᶠ[𝓝 z.1] (fun _ => (0 : ℝ)) := by
    filter_upwards [hmap.continuousAt.preimage_mem_nhds hopen] with x hx
    by_contra hne
    exact hx (subset_tsupport (f := F) (Function.mem_support.mpr hne))
  rw [hev.fderiv_eq, fderiv_const_apply]
  simp

lemma caccioppoli_terms_zero_ae_outside_cylinder
    {Ω : Set Vec3} {x₀ : Vec3} {t₀ ρ ε : ℝ}
    (hρ : 0 < ρ)
    (hΩ : MeasurableSet Ω)
    {F : Vec3 × ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupp : tsupport F ⊆ euclideanClosedBall x₀ (3 * ρ / 4) ×ˢ
        Icc (t₀ - ρ ^ 2) (t₀ + ε))
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} {t : ℝ}
    (ht : t ≤ t₀) :
    ∀ᵐ z ∂(volume.restrict (Ω ×ˢ Iio t)),
      z ∈ parabolicCylinder x₀ t₀ ρ ∨
      ((vec3EuclideanNorm (u z)) ^ 2 *
          (timePartial F z + ∑ i, spatialSecondPartial F i i z) = 0 ∧
        (vec3EuclideanNorm (u z)) ^ 2 *
          (∑ i, u z i * spatialPartial F i z) = 0 ∧
        2 * (p z - 0) * (∑ i, u z i * spatialPartial F i z) = 0 ∧
        2 * (∑ i, f z i * u z i) * F z = 0 ∧
        (∑ i, u z i * spatialPartial F i z) = 0) := by
  let N : Set ParabolicPoint := show Set ParabolicPoint from
    (euclideanClosedBall x₀ (3 * ρ / 4) ×ˢ {t₀ - ρ ^ 2})
  have hN : volume N = 0 := by
    dsimp [N]
    rw [volume_parabolicPoint_eq_prod]
    change (volume.prod volume)
      (euclideanClosedBall x₀ (3 * ρ / 4) ×ˢ {t₀ - ρ ^ 2}) = 0
    rw [Measure.prod_prod]
    simp
  have hS : MeasurableSet (Ω ×ˢ Iio t) := hΩ.prod measurableSet_Iio
  have hNaeS : ∀ᵐ z ∂(volume.restrict (Ω ×ˢ Iio t)), z ∉ N := by
    apply ae_iff.2
    simp only [not_not, Set.ofPred_mem_eq]
    exact nonpos_iff_eq_zero.mp (calc
      (volume.restrict (Ω ×ˢ Iio t)) N ≤ volume N :=
        (Measure.restrict_le_self : volume.restrict (Ω ×ˢ Iio t) ≤ volume) N
      _ = 0 := hN)
  filter_upwards [ae_restrict_mem hS, hNaeS]
    with z hzS hzN
  by_cases hzQ : z ∈ parabolicCylinder x₀ t₀ ρ
  · exact Or.inl hzQ
  right
  have hzF : (show Vec3 × ℝ from z) ∉ tsupport F := by
    intro hzFs
    have hzbox := hFsupp hzFs
    rcases z with ⟨x, s⟩
    have hxs : vec3EuclideanNorm (x - x₀) ≤ 3 * ρ / 4 := by
      have hxs' := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
        (by positivity : (0 : ℝ) ≤ 3 * ρ / 4)).1 hzbox.1
      simpa [vec3EuclideanNorm, CKN.vecEuclideanNorm, vecNormSq, vecDot,
        pow_two] using hxs'
    have hxslt : vec3EuclideanNorm (x - x₀) < ρ := by
      linarith only [hxs, hρ]
    have hstlow : t₀ - ρ ^ 2 ≤ s := hzbox.2.1
    have hst : s ≤ t₀ := (lt_of_lt_of_le hzS.2 ht).le
    have hstlow' : t₀ - ρ ^ 2 < s := by
      by_contra hnot
      have : s = t₀ - ρ ^ 2 := le_antisymm (le_of_not_gt hnot) hstlow
      exact hzN (by
        change x ∈ euclideanClosedBall x₀ (3 * ρ / 4) ∧
          s ∈ ({t₀ - ρ ^ 2} : Set ℝ)
        have hxs' : vecEuclideanNorm (x - x₀) ≤ 3 * ρ / 4 := by
          simpa [vec3EuclideanNorm, CKN.vecEuclideanNorm, vecNormSq, vecDot,
            pow_two] using hxs
        exact ⟨(mem_euclideanClosedBall_iff_vecEuclideanNorm_le
            (by positivity)).2 hxs', by simp [this]⟩)
    apply hzQ
    exact ⟨hxslt, hstlow', hst⟩
  have h0 : F z = 0 := by
    simpa only using image_eq_zero_of_notMem_tsupport hzF
  have ht0 := caccioppoli_timePartial_zero_of_not_mem_tsupport hF hzF
  have hs0 : ∀ i : Fin 3, spatialPartial F i z = 0 := fun i =>
    caccioppoli_spatialPartial_zero_of_not_mem_tsupport hF hzF i
  have hss0 : ∀ i j : Fin 3, spatialSecondPartial F i j z = 0 := by
    intro i j
    exact spatialSecondPartial_zero_of_not_mem_tsupport_public hF hzF i j
  simp [h0, ht0, hs0, hss0]

lemma caccioppoli_integrable_of_lintegral_abs_ne_top
    {Q : Set ParabolicPoint} {g : ParabolicPoint → ℝ}
    (hg : AEMeasurable g (volume.restrict Q))
    (hfin : (∫⁻ z in Q, ENNReal.ofReal |g z|) ≠ ∞) :
    IntegrableOn g Q volume := by
  have hnonneg : 0 ≤ᵐ[volume.restrict Q] fun z => |g z| :=
    Filter.Eventually.of_forall (fun z => abs_nonneg _)
  have hnorm := (lintegral_ofReal_ne_top_iff_integrable
    hg.norm.aestronglyMeasurable hnonneg).mp hfin
  exact (integrable_norm_iff hg.aestronglyMeasurable).mp hnorm

lemma caccioppoli_integral_term_le_raw
    {S Q : Set ParabolicPoint} {g : ParabolicPoint → ℝ}
    (hS : MeasurableSet S) (_ : MeasurableSet Q)
    (hg : IntegrableOn g Q volume)
    (hzero : ∀ᵐ z ∂(volume.restrict S), z ∈ Q ∨ g z = 0) :
    ∫ z in S, g z ≤ (∫⁻ z in Q, ENNReal.ofReal |g z|).toReal := by
  have hzero' : ∀ᵐ z ∂volume, z ∈ S → z ∈ Q ∨ g z = 0 :=
    (ae_restrict_iff' hS).mp hzero
  have hEq : ∫ z in S, g z = ∫ z in S ∩ Q, g z := by
    apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hS.nullMeasurableSet
      inter_subset_left
    filter_upwards [hzero'] with z hz
    intro hz'
    exact (hz hz'.1).resolve_left (fun hq => hz'.2 ⟨hz'.1, hq⟩)
  rw [hEq]
  exact caccioppoli_setIntegral_le_toReal_lintegral_abs inter_subset_right hg

lemma caccioppoli_integrable_term_on
    {S Q : Set ParabolicPoint} {g : ParabolicPoint → ℝ}
    (hS : MeasurableSet S) (hg : IntegrableOn g Q volume)
    (hzero : ∀ᵐ z ∂(volume.restrict S), z ∈ Q ∨ g z = 0) :
    IntegrableOn g S volume := by
  have hzero' : ∀ᵐ z ∂volume, z ∈ S → z ∈ Q ∨ g z = 0 :=
    (ae_restrict_iff' hS).mp hzero
  apply hg.of_ae_sdiff_eq_zero hS.nullMeasurableSet
  filter_upwards [hzero'] with z hz
  intro hz'
  exact (hz hz'.1).resolve_left hz'.2

theorem caccioppoli_energy_nested_integral_eq
    {Ω : Set Vec3} {T : Set ℝ} {g : ParabolicPoint → ℝ}
    (hg : IntegrableOn g (Ω ×ˢ T) ((volume : Measure Vec3).prod volume)) :
    ∫ s in T, ∫ x in Ω, g (x, s) =
      ∫ z in Ω ×ˢ T, g z ∂((volume : Measure Vec3).prod volume) := by
  exact _root_.CKN.caccioppoli_nested_integral_eq hg

lemma caccioppoli_pairing_zero_to_slice_integral
    {Ω K : Set Vec3} {s : ℝ} {F : Vec3 × ℝ → ℝ}
    {u : ParabolicPoint → Vec3}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupp : tsupport F ⊆ K ×ˢ (Set.univ : Set ℝ))
    (hUs : IntegrableOn (fun x : Vec3 => u (x, s)) K volume)
    (hpair : parametricPairing
        (fun s y => F (y, s)) (fun _ : Vec3 => 0) (fun y => u (y, s))
        (fun _ => 0) s = 0) :
    Integrable (fun x : Vec3 =>
      ∑ i, u (x, s) i * spatialPartial F i (x, s)) volume ∧
      ∫ x in Ω, ∑ i, u (x, s) i * spatialPartial F i (x, s) = 0 := by
  have hKclosed : IsClosed K := hK.isClosed
  have hderivcont : ∀ i : Fin 3,
      Continuous (fun x : Vec3 => spatialPartial F i (x, s)) := by
    intro i
    have hmap : Continuous (fun x : Vec3 => (x, s)) :=
      continuous_id.prodMk continuous_const
    exact (spatialPartial_contDiff hF i).continuous.comp hmap
  have hK₁ : ∀ i : Fin 3, ∀ x ∉ K,
      spatialPartial F i (x, s) = 0 := by
    intro i x hx
    have hnear : ∀ᶠ y in 𝓝 x, y ∉ K := hKclosed.isOpen_compl.mem_nhds hx
    have hzero : (fun y : Vec3 => F (y, s)) =ᶠ[𝓝 x]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [hnear] with y hy
      by_contra hne
      apply hy
      have hm : (y, s) ∈ tsupport F :=
        subset_tsupport (f := F) (Function.mem_support.mpr hne)
      exact (hFsupp hm).1
    change (fderiv ℝ (fun y : Vec3 => F (y, s)) x) (basisVec i) = 0
    rw [hzero.fderiv_eq, fderiv_const_apply]
    simp
  have hprod : ∀ i : Fin 3, Integrable (fun x : Vec3 =>
      u (x, s) i * spatialPartial F i (x, s)) volume := by
    intro i
    have hui : Integrable (fun x : Vec3 => u (x, s) i)
        (volume.restrict K) :=
      (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ).integrableOn_comp hUs
    have hcontK : ContinuousOn
        (fun x : Vec3 => ‖spatialPartial F i (x, s)‖) K :=
      (hderivcont i).norm.continuousOn
    obtain ⟨C, hCbound⟩ := bddAbove_def.mp (hK.bddAbove_image hcontK)
    have hbound : ∀ᵐ x ∂volume.restrict K,
        ‖spatialPartial F i (x, s)‖ ≤ max C 0 := by
      filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
      exact le_max_of_le_left (hCbound _ ⟨x, hx, rfl⟩)
    have hprodK : Integrable (fun x : Vec3 =>
        u (x, s) i * spatialPartial F i (x, s))
        (volume.restrict K) :=
      hui.mul_bdd (hderivcont i).aestronglyMeasurable hbound
    apply (integrableOn_iff_integrable_of_support_subset (μ := volume)
      (s := K) (by
        intro x hx
        by_contra hnot
        apply hx
        rw [mul_eq_zero]
        right
        exact hK₁ i x hnot)).mp
    exact hprodK
  have hsum : ∫ x, ∑ i, u (x, s) i * spatialPartial F i (x, s) =
      ∑ i, ∫ x, u (x, s) i * spatialPartial F i (x, s) := by
    simpa only [Finset.sum_apply] using
      (integral_finsetSum (s := (Finset.univ : Finset (Fin 3)))
        (fun i _ => hprod i))
  have hzeroΩ : ∀ x ∉ Ω, ∑ i, u (x, s) i * spatialPartial F i (x, s) = 0 := by
    intro x hx
    apply Finset.sum_eq_zero
    intro i hi
    exact mul_eq_zero.mpr (Or.inr (hK₁ i x (fun hmem => hx (hKΩ hmem))))
  have hset := setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := (volume : Measure Vec3)) hzeroΩ
  have hpair' : (∑ i, ∫ x, u (x, s) i *
      spatialDeriv (fun y => F (y, s)) i x) = 0 := by
    simpa [parametricPairing] using hpair
  have hpair'' : (∫ x, ∑ i, u (x, s) i *
      spatialPartial F i (x, s)) = 0 := by
    rw [hsum]
    simpa only [spatialDeriv, spatialPartial] using hpair'
  have hsumInt : Integrable (fun x : Vec3 =>
      ∑ i, u (x, s) i * spatialPartial F i (x, s)) volume := by
    exact integrable_finsetSum (s := (Finset.univ : Finset (Fin 3)))
      (fun i _ => hprod i)
  exact ⟨hsumInt, by
    rw [hset]
    exact hpair''⟩

theorem caccioppoli_rhs_integral_sum_bound
    {Ω : Set Vec3} {u : ParabolicPoint → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    {S : Set ParabolicPoint} {T : Set ℝ} {F : Vec3 × ℝ → ℝ}
    {g₁ g₂ g₃ g₄ : ParabolicPoint → ℝ} {I₁ I₂ I₃ I₄ : ℝ}
    (hR_eq : (∫ z in S, localEnergyRhs u p f F z) =
      ∫ z in S, (g₁ z + g₂ z + g₃ z + g₄ z))
    (hnestR : (∫ s in T, ∫ x in Ω, localEnergyRhs u p f F (x, s)) =
      ∫ z in S, localEnergyRhs u p f F z)
    (hi₁ : IntegrableOn g₁ S volume) (hi₂ : IntegrableOn g₂ S volume)
    (hi₃ : IntegrableOn g₃ S volume) (hi₄ : IntegrableOn g₄ S volume)
    (hterm₁ : ∫ z in S, g₁ z ≤ I₁)
    (hterm₂ : ∫ z in S, g₂ z ≤ I₂)
    (hterm₃ : ∫ z in S, g₃ z ≤ I₃)
    (hterm₄ : ∫ z in S, g₄ z ≤ I₄) :
    (∫ s in T, ∫ x in Ω, localEnergyRhs u p f F (x, s)) ≤
      I₁ + I₂ + I₃ + I₄ := by
  have hsum_eq : ∫ z in S, (g₁ z + g₂ z + g₃ z + g₄ z) =
      (∫ z in S, g₁ z) + (∫ z in S, g₂ z) +
        (∫ z in S, g₃ z) + (∫ z in S, g₄ z) := by
    have h34 : ∫ z in S, (g₁ z + g₂ z + g₃ z) + g₄ z =
        (∫ z in S, (g₁ z + g₂ z + g₃ z)) + ∫ z in S, g₄ z :=
      integral_add (((hi₁.add hi₂).add hi₃).integrable) hi₄.integrable
    have h23 : ∫ z in S, (g₁ z + g₂ z) + g₃ z =
        (∫ z in S, (g₁ z + g₂ z)) + ∫ z in S, g₃ z :=
      integral_add (hi₁.add hi₂).integrable hi₃.integrable
    have h12 : ∫ z in S, g₁ z + g₂ z =
        (∫ z in S, g₁ z) + ∫ z in S, g₂ z :=
      integral_add hi₁.integrable hi₂.integrable
    calc
      ∫ z in S, (g₁ z + g₂ z + g₃ z + g₄ z) =
          (∫ z in S, (g₁ z + g₂ z + g₃ z)) + ∫ z in S, g₄ z := by
        simpa only [add_assoc] using h34
      _ = ((∫ z in S, (g₁ z + g₂ z)) + ∫ z in S, g₃ z) +
          ∫ z in S, g₄ z := by
        rw [h23]
      _ = (((∫ z in S, g₁ z) + ∫ z in S, g₂ z) +
          ∫ z in S, g₃ z) + ∫ z in S, g₄ z := by
        rw [h12]
  rw [hnestR, hR_eq, hsum_eq]
  exact add_le_add (add_le_add (add_le_add hterm₁ hterm₂) hterm₃) hterm₄


end CKN
