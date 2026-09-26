/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.CubeEmbedding.Fold
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Fold Norm -/

@[expose] public section

namespace Homogenization

open MeasureTheory Homogenization
open scoped ENNReal NNReal BigOperators

/-!
# Norm transport under the even fold

The coordinatewise even fold `Fold lo hi : Vec d → Vec d` maps the tripled open
box `Box3 lo hi` onto the box `Box lo hi` in a `3`-to-`1`, piecewise-affine,
measure-preserving way.  The load-bearing consequence is the `lintegral`
transport identity

  `∫⁻ x in Box3, g (Fold lo hi x) = 3 ^ d * ∫⁻ x in Box, g x`

for measurable `g`, and its `L²` corollary

  `eLpNorm (v ∘ Fold) 2 (vol Box3) = (3 ^ d) ^ (1/2) * eLpNorm v 2 (vol Box)`.

The proof factors through the product structure: each coordinate fold pushes the
restricted Lebesgue measure on the tripled interval forward to `3` copies of the
restricted Lebesgue measure on the base interval, and `Measure.pi_map_pi`
assembles the coordinatewise pushforwards.
-/

noncomputable section

variable {d : ℕ}

/-- The open axis box `∏ᵢ (loᵢ, hiᵢ)`. -/
def Box (lo hi : Vec d) : Set (Vec d) := Set.univ.pi fun k => Set.Ioo (lo k) (hi k)

/-- The tripled open axis box `∏ᵢ (2loᵢ − hiᵢ, 2hiᵢ − loᵢ)`, i.e. the base box
enlarged by its own side length on each face. -/
def Box3 (lo hi : Vec d) : Set (Vec d) :=
  Set.univ.pi fun k => Set.Ioo (2 * lo k - hi k) (2 * hi k - lo k)

theorem measurableSet_Box (lo hi : Vec d) : MeasurableSet (Box lo hi) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

theorem measurableSet_Box3 (lo hi : Vec d) : MeasurableSet (Box3 lo hi) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

/-! ## One-dimensional pushforward -/

/-- Reflection `t ↦ c − t` preimage of an open interval. -/
private theorem preimage_reflect_Ioo (c lo hi : ℝ) :
    (fun t => c - t) ⁻¹' Set.Ioo lo hi = Set.Ioo (c - hi) (c - lo) := by
  ext t
  simp only [Set.mem_preimage, Set.mem_Ioo]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-- **1-D fold pushforward.**  The scalar fold pushes the restricted Lebesgue
measure on the tripled interval forward to `3` copies of the restricted
Lebesgue measure on the base interval. -/
theorem map_foldR_restrict (lo hi : ℝ) (h : lo < hi) :
    (volume.restrict (Set.Ioo (2 * lo - hi) (2 * hi - lo))).map (foldR lo hi)
      = (3 : ℝ≥0∞) • volume.restrict (Set.Ioo lo hi) := by
  have hfold_meas : Measurable (foldR lo hi) := (continuous_foldR lo hi h.le).measurable
  -- the tripled interval agrees a.e. with the union of the three affine branches
  have hdisjLM : Disjoint (Set.Ioo (2 * lo - hi) lo) (Set.Ioo lo hi) := by
    rw [Set.disjoint_left]; rintro t ⟨_, ht2⟩ ⟨ht3, _⟩; exact absurd ht3 (not_lt.mpr ht2.le)
  have hdisjMR : Disjoint (Set.Ioo lo hi) (Set.Ioo hi (2 * hi - lo)) := by
    rw [Set.disjoint_left]; rintro t ⟨_, ht2⟩ ⟨ht3, _⟩; exact absurd ht3 (not_lt.mpr ht2.le)
  have hdisjLMR : Disjoint (Set.Ioo (2 * lo - hi) lo ∪ Set.Ioo lo hi)
      (Set.Ioo hi (2 * hi - lo)) := by
    rw [Set.disjoint_union_left]
    refine ⟨?_, hdisjMR⟩
    rw [Set.disjoint_left]; rintro t ⟨_, ht2⟩ ⟨ht3, _⟩; linarith
  have hset : Set.Ioo (2 * lo - hi) (2 * hi - lo)
      =ᵐ[volume] ((Set.Ioo (2 * lo - hi) lo ∪ Set.Ioo lo hi ∪ Set.Ioo hi (2 * hi - lo)) : Set ℝ) := by
    have hsub1 : (Set.Ioo (2 * lo - hi) lo ∪ Set.Ioo lo hi ∪ Set.Ioo hi (2 * hi - lo))
        ⊆ Set.Ioo (2 * lo - hi) (2 * hi - lo) := by
      intro t ht
      rcases ht with (h' | h') | h'
      · exact ⟨h'.1, by have := h'.2; linarith⟩
      · exact ⟨by have := h'.1; linarith, by have := h'.2; linarith⟩
      · exact ⟨by have := h'.1; linarith, h'.2⟩
    have hsub2 : Set.Ioo (2 * lo - hi) (2 * hi - lo)
        \ (Set.Ioo (2 * lo - hi) lo ∪ Set.Ioo lo hi ∪ Set.Ioo hi (2 * hi - lo))
        ⊆ ({lo, hi} : Set ℝ) := by
      intro t ht
      obtain ⟨⟨htL, htR⟩, htn⟩ := ht
      simp only [Set.mem_union, not_or] at htn
      obtain ⟨⟨hnL, hnM⟩, hnR⟩ := htn
      simp only [Set.mem_Ioo, not_and_or, not_lt] at hnL hnM hnR
      rcases hnM with hM | hM
      · rcases hnL with hL | hL
        · exact absurd hL (not_le.mpr htL)
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; left; linarith
      · rcases hnR with hR | hR
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; right; linarith
        · exact absurd hR (not_le.mpr htR)
    refine (MeasureTheory.ae_eq_set.2 ⟨?_, ?_⟩).symm
    · have hemp : (Set.Ioo (2 * lo - hi) lo ∪ Set.Ioo lo hi ∪ Set.Ioo hi (2 * hi - lo))
          \ Set.Ioo (2 * lo - hi) (2 * hi - lo) = ∅ := Set.sdiff_eq_empty.2 hsub1
      rw [hemp]; simp
    · exact measure_mono_null hsub2
        (Set.Finite.measure_zero ((Set.finite_singleton hi).insert lo) volume)
  have hrestrict : volume.restrict (Set.Ioo (2 * lo - hi) (2 * hi - lo))
      = volume.restrict (Set.Ioo (2 * lo - hi) lo) + volume.restrict (Set.Ioo lo hi)
        + volume.restrict (Set.Ioo hi (2 * hi - lo)) := by
    rw [Measure.restrict_congr_set hset,
      Measure.restrict_union hdisjLMR measurableSet_Ioo,
      Measure.restrict_union hdisjLM measurableSet_Ioo]
  -- fold agrees with the affine branch on each piece
  have hcongrL : (volume.restrict (Set.Ioo (2 * lo - hi) lo)).map (foldR lo hi)
      = (volume.restrict (Set.Ioo (2 * lo - hi) lo)).map (fun t => 2 * lo - t) := by
    refine Measure.map_congr ((MeasureTheory.ae_restrict_iff' measurableSet_Ioo).2
      (Filter.Eventually.of_forall ?_))
    intro t ht; unfold foldR; rw [if_pos ht.2]
  have hcongrM : (volume.restrict (Set.Ioo lo hi)).map (foldR lo hi)
      = (volume.restrict (Set.Ioo lo hi)).map id := by
    refine Measure.map_congr ((MeasureTheory.ae_restrict_iff' measurableSet_Ioo).2
      (Filter.Eventually.of_forall ?_))
    intro t ht; simp only [id]; exact foldR_of_mem ht.1.le ht.2.le
  have hcongrR : (volume.restrict (Set.Ioo hi (2 * hi - lo))).map (foldR lo hi)
      = (volume.restrict (Set.Ioo hi (2 * hi - lo))).map (fun t => 2 * hi - t) := by
    refine Measure.map_congr ((MeasureTheory.ae_restrict_iff' measurableSet_Ioo).2
      (Filter.Eventually.of_forall ?_))
    intro t ht; unfold foldR
    rw [if_neg (not_lt.mpr (le_of_lt (lt_trans h ht.1))), if_pos ht.1]
  -- each affine branch maps onto the base interval
  have hmpL : Measure.map (fun t => 2 * lo - t) volume = volume :=
    (volume.measurePreserving_sub_left (2 * lo)).map_eq
  have hmpR : Measure.map (fun t => 2 * hi - t) volume = volume :=
    (volume.measurePreserving_sub_left (2 * hi)).map_eq
  have hmeasL : Measurable (fun t : ℝ => 2 * lo - t) := by fun_prop
  have hmeasR : Measurable (fun t : ℝ => 2 * hi - t) := by fun_prop
  have hbranchL : (volume.restrict (Set.Ioo (2 * lo - hi) lo)).map (fun t => 2 * lo - t)
      = volume.restrict (Set.Ioo lo hi) := by
    have hpre : (fun t => 2 * lo - t) ⁻¹' Set.Ioo lo hi = Set.Ioo (2 * lo - hi) lo := by
      rw [preimage_reflect_Ioo]
      congr
      all_goals ring
    calc (volume.restrict (Set.Ioo (2 * lo - hi) lo)).map (fun t => 2 * lo - t)
        = (volume.restrict ((fun t => 2 * lo - t) ⁻¹' Set.Ioo lo hi)).map (fun t => 2 * lo - t) := by
          rw [hpre]
      _ = (volume.map (fun t => 2 * lo - t)).restrict (Set.Ioo lo hi) :=
          (Measure.restrict_map hmeasL measurableSet_Ioo).symm
      _ = volume.restrict (Set.Ioo lo hi) := by rw [hmpL]
  have hbranchR : (volume.restrict (Set.Ioo hi (2 * hi - lo))).map (fun t => 2 * hi - t)
      = volume.restrict (Set.Ioo lo hi) := by
    have hpre : (fun t => 2 * hi - t) ⁻¹' Set.Ioo lo hi = Set.Ioo hi (2 * hi - lo) := by
      rw [preimage_reflect_Ioo]
      congr
      all_goals ring
    calc (volume.restrict (Set.Ioo hi (2 * hi - lo))).map (fun t => 2 * hi - t)
        = (volume.restrict ((fun t => 2 * hi - t) ⁻¹' Set.Ioo lo hi)).map (fun t => 2 * hi - t) := by
          rw [hpre]
      _ = (volume.map (fun t => 2 * hi - t)).restrict (Set.Ioo lo hi) :=
          (Measure.restrict_map hmeasR measurableSet_Ioo).symm
      _ = volume.restrict (Set.Ioo lo hi) := by rw [hmpR]
  have hbranchM : (volume.restrict (Set.Ioo lo hi)).map id = volume.restrict (Set.Ioo lo hi) := by
    rw [Measure.map_id]
  rw [hrestrict, Measure.map_add _ _ hfold_meas, Measure.map_add _ _ hfold_meas,
    hcongrL, hcongrM, hcongrR, hbranchL, hbranchM, hbranchR,
    show (3 : ℝ≥0∞) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul]

/-! ## Product assembly -/

/-- Scaling each factor of a finite product measure by `c` scales the product by
`c ^ card`. -/
theorem pi_smul_const {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] (ρ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (ρ i)]
    {c : ℝ≥0∞} [∀ i, SigmaFinite (c • ρ i)] :
    Measure.pi (fun i => c • ρ i) = c ^ (Fintype.card ι) • Measure.pi ρ := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.pi_pi]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ]

/-- **`d`-dimensional fold pushforward.**  The coordinatewise fold pushes the
restricted Lebesgue measure on the tripled box forward to `3 ^ d` copies of the
restricted Lebesgue measure on the base box. -/
theorem map_Fold_restrict (lo hi : Vec d) (hlt : ∀ k, lo k < hi k) :
    (volume.restrict (Box3 lo hi)).map (Fold lo hi)
      = (3 : ℝ≥0∞) ^ d • volume.restrict (Box lo hi) := by
  have hvol : (volume : Measure (Vec d)) = Measure.pi fun _ => volume := volume_pi
  have hFoldEq : Fold lo hi = (fun (x : Vec d) k => foldR (lo k) (hi k) (x k)) := rfl
  have hσ3 : ∀ k : Fin d, SigmaFinite ((3 : ℝ≥0∞) • volume.restrict (Set.Ioo (lo k) (hi k))) :=
    fun k => by
      have : IsFiniteMeasure ((3 : ℝ≥0∞) • volume.restrict (Set.Ioo (lo k) (hi k))) :=
        ⟨by rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ, Real.volume_Ioo]
            exact ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top⟩
      infer_instance
  have hσmap : ∀ k : Fin d, SigmaFinite
      ((volume.restrict (Set.Ioo (2 * lo k - hi k) (2 * hi k - lo k))).map (foldR (lo k) (hi k))) :=
    fun k => by rw [map_foldR_restrict (lo k) (hi k) (hlt k)]; exact hσ3 k
  have hfam : (fun k => (volume.restrict
        (Set.Ioo (2 * lo k - hi k) (2 * hi k - lo k))).map (foldR (lo k) (hi k)))
      = (fun k => (3 : ℝ≥0∞) • volume.restrict (Set.Ioo (lo k) (hi k))) := by
    funext k; exact map_foldR_restrict (lo k) (hi k) (hlt k)
  calc (volume.restrict (Box3 lo hi)).map (Fold lo hi)
      = (Measure.pi (fun k => volume.restrict (Set.Ioo (2 * lo k - hi k) (2 * hi k - lo k)))).map
          (fun (x : Vec d) k => foldR (lo k) (hi k) (x k)) := by
        rw [Box3, hvol, Measure.restrict_pi_pi, hFoldEq]
    _ = Measure.pi (fun k => (volume.restrict
          (Set.Ioo (2 * lo k - hi k) (2 * hi k - lo k))).map (foldR (lo k) (hi k))) :=
        Measure.pi_map_pi (f := fun k => foldR (lo k) (hi k))
          (fun k => (continuous_foldR (lo k) (hi k) (hlt k).le).measurable.aemeasurable)
    _ = (3 : ℝ≥0∞) ^ d • Measure.pi (fun k => volume.restrict (Set.Ioo (lo k) (hi k))) := by
        rw [hfam, pi_smul_const, Fintype.card_fin]
    _ = (3 : ℝ≥0∞) ^ d • volume.restrict (Box lo hi) := by
        rw [Box, hvol, Measure.restrict_pi_pi]

/-! ## `lintegral` and `eLpNorm` transport -/

/-- **`lintegral` fold transport.** -/
theorem lintegral_foldComp {g : Vec d → ℝ≥0∞} (hg : Measurable g)
    (lo hi : Vec d) (hlt : ∀ k, lo k < hi k) :
    ∫⁻ x in Box3 lo hi, g (Fold lo hi x)
      = (3 : ℝ≥0∞) ^ d * ∫⁻ x in Box lo hi, g x := by
  have hfold_meas : Measurable (Fold lo hi) :=
    (continuous_Fold lo hi (fun k => (hlt k).le)).measurable
  calc ∫⁻ x in Box3 lo hi, g (Fold lo hi x)
      = ∫⁻ y, g y ∂((volume.restrict (Box3 lo hi)).map (Fold lo hi)) :=
        (lintegral_map hg hfold_meas).symm
    _ = ∫⁻ y, g y ∂((3 : ℝ≥0∞) ^ d • volume.restrict (Box lo hi)) := by
        rw [map_Fold_restrict lo hi hlt]
    _ = (3 : ℝ≥0∞) ^ d * ∫⁻ x in Box lo hi, g x := lintegral_smul_measure _ _

/-- **`L²` fold transport.**  The `L²(Box3)` norm of `v ∘ Fold` equals
`(3 ^ d) ^ (1/2)` times the `L²(Box)` norm of `v`. -/
theorem eLpNorm_foldComp {v : Vec d → ℝ} (hv : Measurable v)
    (lo hi : Vec d) (hlt : ∀ k, lo k < hi k) :
    eLpNorm (fun x => v (Fold lo hi x)) 2 (volume.restrict (Box3 lo hi))
      = ((3 : ℝ≥0∞) ^ d) ^ ((1 : ℝ) / 2) * eLpNorm v 2 (volume.restrict (Box lo hi)) := by
  have hcomp : AEStronglyMeasurable (fun x => v (Fold lo hi x))
      (volume.restrict (Box3 lo hi)) :=
    (hv.comp (continuous_Fold lo hi (fun k => (hlt k).le)).measurable).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hcomp,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hv.aestronglyMeasurable]
  have hpt : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [hpt]
  have hgmeas : Measurable (fun x : Vec d => ‖v x‖ₑ ^ (2 : ℝ)) :=
    (ENNReal.continuous_rpow_const).measurable.comp hv.enorm
  have htrans : ∫⁻ x in Box3 lo hi, ‖v (Fold lo hi x)‖ₑ ^ (2 : ℝ)
      = (3 : ℝ≥0∞) ^ d * ∫⁻ x in Box lo hi, ‖v x‖ₑ ^ (2 : ℝ) :=
    lintegral_foldComp (g := fun x => ‖v x‖ₑ ^ (2 : ℝ)) hgmeas lo hi hlt
  rw [htrans, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]

end

end Homogenization
