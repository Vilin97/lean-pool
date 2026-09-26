/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Statements.ParabolicHolderVecNormLE
public import LeanPool.CaffarelliKohnNirenberg.Statements.RegularPoint
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.MetricSpace.Holder

/-!
# Quantitative gluing of parabolic Hölder representatives

Representatives equal almost everywhere on overlapping open sets agree
pointwise. A common local Hölder bound then gives a quantitative bound on
a region whenever sufficiently close pairs lie in a common member of the cover.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN.Core.Endgame

/-- Restriction preserves a quantitative Hölder bound. -/
theorem holder_norm_mono {U V : Set ParabolicPoint} {g : ParabolicPoint → Vec3}
    {γ C : ℝ} (h : ParabolicHolderVecNormLE U g γ C) (hVU : V ⊆ U) :
    ParabolicHolderVecNormLE V g γ C := by
  obtain ⟨B, K, hB, hK, hC, hb, hk⟩ := h
  exact ⟨B, K, hB, hK, hC, fun z hz => hb z (hVU hz),
    fun z hz w hw => hk z (hVU hz) w (hVU hw)⟩

/-- Forgetting the numerical bound gives the qualitative Hölder predicate. -/
theorem holder_on_of_norm {U : Set ParabolicPoint} {g : ParabolicPoint → Vec3}
    {γ C : ℝ} (h : ParabolicHolderVecNormLE U g γ C) :
    ParabolicHolderVecOn U g γ := by
  obtain ⟨B, K, hB, hK, _, hb, hk⟩ := h
  exact ⟨B, K, hB, hK, hb, hk⟩


private instance : Measure.IsOpenPosMeasure (volume : Measure ParabolicPoint) where
  open_pos U hU hne := by
    have ho : IsOpen (parabolicHomeomorph.symm ⁻¹' U) :=
      hU.preimage parabolicHomeomorph.symm.continuous
    have hn : (parabolicHomeomorph.symm ⁻¹' U).Nonempty := by
      obtain ⟨z, hz⟩ := hne
      exact ⟨parabolicHomeomorph z, hz⟩
    exact ho.measure_ne_zero (volume : Measure (Vec3 × ℝ)) hn

/-- Positive-exponent parabolic Hölder representatives are continuous. -/
theorem holder_on_continuousOn {U : Set ParabolicPoint} {g : ParabolicPoint → Vec3}
    {γ : ℝ} (hγ : 0 < γ) (h : ParabolicHolderVecOn U g γ) : ContinuousOn g U := by
  obtain ⟨B, K, _hB, hK, _hb, hk⟩ := h
  let C : ℝ≥0 := ⟨K, hK⟩
  have hh : HolderOnWith C ⟨γ, hγ.le⟩ (fun z => WithLp.toLp 2 (g z)) U := by
    intro z hz w hw
    have hd := hk z hz w hw
    rw [vec3EuclideanNorm_eq_l2, WithLp.toLp_sub, ← dist_eq_norm,
      ← dist_eq_parabolicDist] at hd
    have he := ENNReal.ofReal_le_ofReal hd
    change edist (WithLp.toLp 2 (g z)) (WithLp.toLp 2 (g w)) ≤
      (C : ℝ≥0∞) * edist z w ^ γ
    have hc : (C : ℝ≥0∞) = ENNReal.ofReal K :=
      ENNReal.ofReal_coe_nnreal.symm
    rw [hc, edist_dist, edist_dist,
      ENNReal.ofReal_rpow_of_nonneg dist_nonneg hγ.le, ← ENNReal.ofReal_mul hK]
    exact he
  exact (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)).comp_continuousOn
    (hh.continuousOn hγ)

/-- Almost-everywhere representatives agree at every point of their open overlap. -/
theorem holder_representatives_eqOn_overlap
    {U V : Set ParabolicPoint} {u g h : ParabolicPoint → Vec3} {γ δ : ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hγ : 0 < γ) (hδ : 0 < δ)
    (hg : ParabolicHolderVecOn U g γ) (hh : ParabolicHolderVecOn V h δ)
    (hgu : g =ᵐ[volume.restrict U] u) (hhu : h =ᵐ[volume.restrict V] u) :
    EqOn g h (U ∩ V) := by
  have hgu' : g =ᵐ[volume.restrict (U ∩ V)] u :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_left hgu
  have hhu' : h =ᵐ[volume.restrict (U ∩ V)] u :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_right hhu
  have he : g =ᵐ[volume.restrict (U ∩ V)] h := hgu'.trans hhu'.symm
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq he (hU.inter hV)
    ((holder_on_continuousOn hγ hg).mono inter_subset_left)
    ((holder_on_continuousOn hδ hh).mono inter_subset_right)

/-- A Hölder representative on an open neighborhood proves regularity there. -/
theorem regular_point_of_holder_on_open
    {Ω : Set Vec3} {I : Set ℝ} {U : Set ParabolicPoint}
    {u w : ParabolicPoint → Vec3} {z : ParabolicPoint} {γ : ℝ}
    (hU : IsOpen U) (hz : z ∈ U) (hUΩ : U ⊆ spaceTimeSet Ω I)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hwu : w =ᵐ[volume.restrict U] u) (hw : ParabolicHolderVecOn U w γ) :
    IsRegularPoint Ω I u z :=
  ⟨hUΩ hz, U, hU, hz, hUΩ, γ, hγ, hγ1, w, hwu, hw⟩

/-- Restrict a representative to an open subregion to obtain regular points. -/
theorem regular_point_of_holder_norm
    {Ω : Set Vec3} {I : Set ℝ} {U V : Set ParabolicPoint}
    {u w : ParabolicPoint → Vec3} {z : ParabolicPoint} {γ C : ℝ}
    (hV : IsOpen V) (hz : z ∈ V) (hVU : V ⊆ U)
    (hVΩ : V ⊆ spaceTimeSet Ω I) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hwu : w =ᵐ[volume.restrict U] u) (hw : ParabolicHolderVecNormLE U w γ C) :
    IsRegularPoint Ω I u z := by
  exact regular_point_of_holder_on_open hV hz hVΩ hγ hγ1
    (ae_restrict_of_ae_restrict_of_subset hVU hwu)
    (holder_on_of_norm (holder_norm_mono hw hVU))

/-- A countable open cover admits a single representative agreeing with every
local positive-exponent Hölder representative pointwise on its domain. -/
theorem exists_holder_gluing {ι : Type*} [Countable ι]
    (U : ι → Set ParabolicPoint) (w : ι → ParabolicPoint → Vec3)
    {u : ParabolicPoint → Vec3} {γ : ℝ} (hγ : 0 < γ)
    (hU : ∀ i, IsOpen (U i)) (hw : ∀ i, ParabolicHolderVecOn (U i) (w i) γ)
    (hae : ∀ i, w i =ᵐ[volume.restrict (U i)] u) :
    ∃ g : ParabolicPoint → Vec3,
      (∀ i, EqOn g (w i) (U i)) ∧ g =ᵐ[volume.restrict (⋃ i, U i)] u := by
  classical
  let g : ParabolicPoint → Vec3 := fun z =>
    if hz : z ∈ ⋃ i, U i then w (Classical.choose (mem_iUnion.mp hz)) z else 0
  have hg : ∀ i, EqOn g (w i) (U i) := by
    intro i z hz
    have hzU : z ∈ ⋃ i, U i := mem_iUnion.mpr ⟨i, hz⟩
    dsimp only [g]
    rw [dite_eq_left hzU]
    have hchosen := Classical.choose_spec (mem_iUnion.mp hzU)
    exact holder_representatives_eqOn_overlap (hU _) (hU i) hγ hγ
      (hw _) (hw i) (hae _) (hae i) ⟨hchosen, hz⟩
  refine ⟨g, hg, (ae_restrict_iUnion_iff U _).mpr ?_⟩
  intro i
  have hgi : g =ᵐ[volume.restrict (U i)] w i :=
    (ae_restrict_mem (hU i).measurableSet).mono (fun z hz => hg i hz)
  exact hgi.trans (hae i)

private theorem euclidean_norm_sub_le (a b : Vec3) :
    vec3EuclideanNorm (a - b) ≤ vec3EuclideanNorm a + vec3EuclideanNorm b := by
  simp only [vec3EuclideanNorm_eq_l2, WithLp.toLp_sub]
  exact norm_sub_le _ _

/-- Quantitative gluing with a uniform cover radius. The radius hypothesis is
pure geometry: every sufficiently close pair in the target region lies in
one common cover member. No global representative or global estimate is assumed. -/
theorem exists_holder_norm_gluing {ι : Type*} [Countable ι]
    (U : ι → Set ParabolicPoint) (w : ι → ParabolicPoint → Vec3)
    {u : ParabolicPoint → Vec3} {V : Set ParabolicPoint} {γ C δ : ℝ}
    (hγ : 0 < γ) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hU : ∀ i, IsOpen (U i))
    (hw : ∀ i, ParabolicHolderVecNormLE (U i) (w i) γ C)
    (hae : ∀ i, w i =ᵐ[volume.restrict (U i)] u)
    (hVU : V ⊆ ⋃ i, U i)
    (hclose : ∀ x ∈ V, ∀ y ∈ V, parabolicDist x y < δ →
      ∃ i, x ∈ U i ∧ y ∈ U i) :
    ∃ g : ParabolicPoint → Vec3, g =ᵐ[volume.restrict V] u ∧
      ParabolicHolderVecNormLE V g γ (C + max C (2 * C / δ ^ γ)) ∧
      ∀ i, EqOn g (w i) (U i) := by
  obtain ⟨g, hg, hgu⟩ := exists_holder_gluing U w hγ hU
    (fun i => holder_on_of_norm (hw i)) hae
  have hsup : ∀ x ∈ V, vec3EuclideanNorm (g x) ≤ C := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hVU hx)
    obtain ⟨B, K, _hB, hK, hBK, hb, _hk⟩ := hw i
    rw [hg i hi]
    exact (hb x hi).trans (by linarith only [hK, hBK])
  refine ⟨g, ae_restrict_of_ae_restrict_of_subset hVU hgu, ?_, hg⟩
  refine ⟨C, max C (2 * C / δ ^ γ), hC, hC.trans (le_max_left _ _), le_rfl,
    hsup, ?_⟩
  intro x hx y hy
  have hd : 0 ≤ parabolicDist x y := by rw [← dist_eq_parabolicDist]; exact dist_nonneg
  have hdpow : 0 ≤ parabolicDist x y ^ γ := Real.rpow_nonneg hd _
  by_cases hxy : parabolicDist x y < δ
  · obtain ⟨i, hxi, hyi⟩ := hclose x hx y hy hxy
    obtain ⟨B, K, hB, _hK, hBK, _hb, hk⟩ := hw i
    rw [hg i hxi, hg i hyi]
    exact (hk x hxi y hyi).trans (mul_le_mul_of_nonneg_right
      ((show K ≤ C by linarith only [hB, hBK]).trans (le_max_left _ _)) hdpow)
  · have hfar : δ ≤ parabolicDist x y := le_of_not_gt hxy
    have hδpow : 0 < δ ^ γ := Real.rpow_pos_of_pos hδ _
    calc
      vec3EuclideanNorm (g x - g y) ≤
          vec3EuclideanNorm (g x) + vec3EuclideanNorm (g y) := euclidean_norm_sub_le _ _
      _ ≤ 2 * C := by linarith only [hsup x hx, hsup y hy]
      _ = (2 * C / δ ^ γ) * δ ^ γ := (div_mul_cancel₀ _ hδpow.ne').symm
      _ ≤ (2 * C / δ ^ γ) * parabolicDist x y ^ γ :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hδ.le hfar hγ.le)
          (div_nonneg (mul_nonneg (by norm_num) hC) hδpow.le)
      _ ≤ max C (2 * C / δ ^ γ) * parabolicDist x y ^ γ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hdpow

end CKN.Core.Endgame
