/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/
module

public import LeanPool.CarlsonFunctions.StdSimplexMeasure.Integral.Basic

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import LeanPool.CarlsonFunctions.StdSimplexMeasure.Measure
public import LeanPool.CarlsonFunctions.Pochhammer.BetaIntegral
public import LeanPool.CarlsonFunctions.StdSimplexMeasure.PositiveSimplex

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import LeanPool.CarlsonFunctions.StdSimplexMeasure.EuclideanCrossSection
import all LeanPool.CarlsonFunctions.StdSimplexMeasure.Measure.Basic

/-! # Slicing and scaling standard-simplex integrals -/

open Fintype (card)

public noncomputable section StdSimplexIntegral

namespace MeasureTheory

open Measure MeasureTheory

universe u

variable {ι : Type u} [Fintype ι]


open scoped Classical in
/-- Splitting one coordinate from a finite real coordinate space preserves product Lebesgue
measure. -/
theorem volume_preserving_funSplitAt (i : ι) :
    MeasurePreserving (Homeomorph.funSplitAt ℝ i) volume (volume.prod volume) := by
  let eidx : Unit ⊕ {j : ι // j ≠ i} ≃ ι :=
    { toFun := fun q => Sum.elim (fun _ => i) Subtype.val q
      invFun := fun j => if h : j = i then Sum.inl () else Sum.inr ⟨j, h⟩
      left_inv := by
        rintro (_ | j)
        · simp
        · simp [j.property]
      right_inv := by
        intro j
        dsimp
        split_ifs with h
        · exact h.symm
        · rfl }
  let ec := MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) eidx
  let es := MeasurableEquiv.sumPiEquivProdPi (fun _ : Unit ⊕ {j : ι // j ≠ i} => ℝ)
  let eu := MeasurableEquiv.prodCongr
    (MeasurableEquiv.funUnique Unit ℝ)
    (MeasurableEquiv.refl ({j : ι // j ≠ i} → ℝ))
  have hc := (volume_measurePreserving_piCongrLeft (fun _ : ι => ℝ) eidx).symm
  have hs := volume_measurePreserving_sumPiEquivProdPi
    (fun _ : Unit ⊕ {j : ι // j ≠ i} => ℝ)
  have hu : MeasurePreserving eu volume (volume.prod volume) := by
    rw [Measure.volume_eq_prod]
    exact (volume_preserving_funUnique Unit ℝ).prod (MeasurePreserving.id volume)
  have h := hu.comp (hs.comp hc)
  convert h using 1
  funext x
  apply Prod.ext
  · change x i = x (eidx (Sum.inl ()))
    rfl
  · funext j
    change x j = x (eidx (Sum.inr j))
    rfl

open scoped Classical in
/-- In a free-coordinate chart omitting `j`, separating the coordinate corresponding to
`i ≠ j` turns the chart domain into the standard product-coordinate simplex slices. -/
private theorem image_stdSimplexFreeCoords_funSplitAt (i j : ι) (hij : i ≠ j) :
    let ii : {q : ι // q ≠ j} := ⟨i, hij⟩
    Homeomorph.funSplitAt ℝ ii '' stdSimplexFreeCoords j = posSimplexSlices ii 1 := by
  dsimp only
  let ii : {q : ι // q ≠ j} := ⟨i, hij⟩
  change Homeomorph.funSplitAt ℝ ii '' posSimplex {q : ι // q ≠ j} 1 =
    posSimplexSlices ii 1
  exact image_posSimplex_funSplitAt (⟨i, hij⟩ : {q : ι // q ≠ j}) 1

/-- Reindexing the coordinates left after deleting two distinct indices in opposite orders. -/
def stdSimplexDoubleComplementEquiv (i j : ι) (hij : i ≠ j) :
    {q : {q : ι // q ≠ i} // q ≠ ⟨j, hij.symm⟩} ≃
      {q : {q : ι // q ≠ j} // q ≠ ⟨i, hij⟩} where
  toFun q := ⟨⟨q.val.val, fun h => q.property (Subtype.ext h)⟩,
    fun h => q.val.property (congrArg Subtype.val h)⟩
  invFun q := ⟨⟨q.val.val, fun h => q.property (Subtype.ext h)⟩,
    fun h => q.val.property (congrArg Subtype.val h)⟩
  left_inv q := by ext; rfl
  right_inv q := by ext; rfl

open scoped Classical in
/-- Reindexing by `stdSimplexDoubleComplementEquiv` preserves finite coordinate sums. -/
private theorem sum_stdSimplexDoubleComplementEquiv (i j : ι) (hij : i ≠ j)
    (x : {q : {q : ι // q ≠ i} // q ≠ ⟨j, hij.symm⟩} → ℝ) :
    (∑ q : {q : {q : ι // q ≠ i} // q ≠ ⟨j, hij.symm⟩}, x q) =
      ∑ q : {q : {q : ι // q ≠ j} // q ≠ ⟨i, hij⟩},
        x ((stdSimplexDoubleComplementEquiv i j hij).symm q) := by
  rw [Equiv.sum_comp]

open scoped Classical in
/-- The double-complement reindexing sends the unit positive simplex onto itself. -/
private theorem image_posSimplex_stdSimplexDoubleComplementEquiv
    (i j : ι) (hij : i ≠ j) :
    let D := {q : {q : ι // q ≠ i} // q ≠ ⟨j, hij.symm⟩}
    let C := {q : {q : ι // q ≠ j} // q ≠ ⟨i, hij⟩}
    let T := MeasurableEquiv.piCongrLeft (fun _ : C => ℝ)
      (stdSimplexDoubleComplementEquiv i j hij)
    T '' posSimplex D 1 = posSimplex C 1 := by
  dsimp only
  let e := stdSimplexDoubleComplementEquiv i j hij
  let T := MeasurableEquiv.piCongrLeft (fun _ : _ => ℝ) e
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨hx0, hxs⟩
    refine ⟨?_, ?_⟩
    · intro q
      change 0 ≤ x (e.symm q)
      exact hx0 (e.symm q)
    · change (∑ q, x (e.symm q)) ≤ 1
      rw [← sum_stdSimplexDoubleComplementEquiv i j hij]
      exact hxs
  · intro hy
    refine ⟨T.symm y, ?_, T.apply_symm_apply y⟩
    rcases hy with ⟨hy0, hys⟩
    refine ⟨?_, ?_⟩
    · intro q
      change 0 ≤ y (e q)
      exact hy0 (e q)
    · change (∑ q, y (e q)) ≤ 1
      rw [Equiv.sum_comp]
      exact hys

open scoped Classical in
/-- Integrals over the two double-complement coordinate spaces agree after reindexing. -/
private theorem integral_posSimplex_stdSimplexDoubleComplementEquiv
    (i j : ι) (hij : i ≠ j)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ({q : {q : ι // q ≠ j} // q ≠ ⟨i, hij⟩} → ℝ) → E) :
    let D := {q : {q : ι // q ≠ i} // q ≠ ⟨j, hij.symm⟩}
    let C := {q : {q : ι // q ≠ j} // q ≠ ⟨i, hij⟩}
    let T := MeasurableEquiv.piCongrLeft (fun _ : C => ℝ)
      (stdSimplexDoubleComplementEquiv i j hij)
    ∫ y in posSimplex C 1, g y = ∫ x in posSimplex D 1, g (T x) := by
  dsimp only
  let T := MeasurableEquiv.piCongrLeft
    (fun _ : {q : {q : ι // q ≠ j} // q ≠ ⟨i, hij⟩} => ℝ)
    (stdSimplexDoubleComplementEquiv i j hij)
  have hT := volume_measurePreserving_piCongrLeft
    (fun _ : {q : {q : ι // q ≠ j} // q ≠ ⟨i, hij⟩} => ℝ)
    (stdSimplexDoubleComplementEquiv i j hij)
  rw [← image_posSimplex_stdSimplexDoubleComplementEquiv i j hij]
  exact hT.setIntegral_image_emb T.measurableEmbedding g _

open scoped Classical in
/-- Nonnegative integrals over the two double-complement coordinate spaces agree after
reindexing. -/
private theorem lintegral_posSimplex_stdSimplexDoubleComplementEquiv
    (i j : ι) (hij : i ≠ j)
    (g : ({q : {q : ι // q ≠ j} // q ≠ ⟨i, hij⟩} → ℝ) → ENNReal) :
    let D := {q : {q : ι // q ≠ i} // q ≠ ⟨j, hij.symm⟩}
    let C := {q : {q : ι // q ≠ j} // q ≠ ⟨i, hij⟩}
    let T := MeasurableEquiv.piCongrLeft (fun _ : C => ℝ)
      (stdSimplexDoubleComplementEquiv i j hij)
    ∫⁻ y in posSimplex C 1, g y = ∫⁻ x in posSimplex D 1, g (T x) := by
  dsimp only
  let T := MeasurableEquiv.piCongrLeft
    (fun _ : {q : {q : ι // q ≠ j} // q ≠ ⟨i, hij⟩} => ℝ)
    (stdSimplexDoubleComplementEquiv i j hij)
  have hT := volume_measurePreserving_piCongrLeft
    (fun _ : {q : {q : ι // q ≠ j} // q ≠ ⟨i, hij⟩} => ℝ)
    (stdSimplexDoubleComplementEquiv i j hij)
  rw [← image_posSimplex_stdSimplexDoubleComplementEquiv i j hij]
  exact ((hT.restrict_image_emb T.measurableEmbedding
    (posSimplex {q : {q : ι // q ≠ i} // q ≠ ⟨j, hij.symm⟩} 1)).lintegral_comp_emb
      T.measurableEmbedding g).symm

open scoped Classical in
/-- Fubini disintegration of a positive simplex after separating one coordinate. -/
private theorem integral_posSimplex_split
    {α : Type*} [Fintype α] (i : α)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : (α → ℝ) → E) (hg : IntegrableOn g (posSimplex α 1)) :
    ∫ x in posSimplex α 1, g x =
      ∫ t in Set.Icc (0 : ℝ) 1,
        ∫ y in posSimplex {j : α // j ≠ i} (1 - t),
          g ((Homeomorph.funSplitAt ℝ i).symm (t, y)) := by
  let e := Homeomorph.funSplitAt ℝ i
  let G : ℝ × ({j : α // j ≠ i} → ℝ) → E := fun p => g (e.symm p)
  have hmp := volume_preserving_funSplitAt i
  have hset : e '' posSimplex α 1 = posSimplexSlices i 1 :=
    image_posSimplex_funSplitAt i 1
  have hGI : IntegrableOn G (posSimplexSlices i 1) (volume.prod volume) := by
    rw [← hset]
    change Integrable G ((volume.prod volume).restrict (e '' posSimplex α 1))
    rw [← (hmp.restrict_image_emb e.measurableEmbedding
      (posSimplex α 1)).integrable_comp_emb e.measurableEmbedding]
    have heq : G ∘ e = g := by
      funext x
      exact congrArg g (e.symm_apply_apply x)
    rw [heq]
    exact hg
  calc
    ∫ x in posSimplex α 1, g x = ∫ p in posSimplexSlices i 1, G p ∂volume.prod volume := by
      rw [← hset]
      convert (hmp.setIntegral_image_emb e.measurableEmbedding G
        (posSimplex α 1)).symm using 1
      apply integral_congr_ae
      filter_upwards [] with x
      exact congrArg g (e.symm_apply_apply x).symm
    _ = ∫ t, ∫ y, (posSimplexSlices i 1).indicator G (t, y) := by
      rw [← integral_indicator (measurableSet_posSimplexSlices i 1)]
      exact integral_prod _ (hGI.integrable_indicator (measurableSet_posSimplexSlices i 1))
    _ = ∫ t in Set.Icc (0 : ℝ) 1,
        ∫ y in posSimplex {j : α // j ≠ i} (1 - t),
          g (e.symm (t, y)) := by
      rw [← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards [] with t
      by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
      · rw [Set.indicator_of_mem ht]
        rw [← integral_indicator (measurableSet_posSimplex _ _)]
        apply integral_congr_ae
        filter_upwards [] with y
        have hy : ((t, y) ∈ posSimplexSlices i 1 ↔
            y ∈ posSimplex {j : α // j ≠ i} (1 - t)) := by
          exact Set.ext_iff.mp (preimage_posSimplexSlices_of_mem i 1 t ht) y
        simp only [Set.indicator_apply]
        simp [hy, G]
      · simp only [Set.indicator_apply, ht, ↓reduceIte]
        rw [integral_eq_zero_of_ae]
        filter_upwards [] with y
        have hy : (t, y) ∉ posSimplexSlices i 1 := by
          intro hmem
          have : y ∈ Prod.mk t ⁻¹' posSimplexSlices i 1 := hmem
          rw [preimage_posSimplexSlices_eq_empty_of_not_mem i 1 t ht] at this
          exact this
        simp [hy]

open scoped Classical in
/-- Tonelli disintegration of a positive simplex after separating one coordinate. Unlike the
Bochner-integral version, this statement requires no prior integrability assumption. -/
private theorem lintegral_posSimplex_split
    {α : Type*} [Fintype α] (i : α) (g : (α → ℝ) → ENNReal) (hg : Measurable g) :
    ∫⁻ x in posSimplex α 1, g x =
      ∫⁻ t in Set.Icc (0 : ℝ) 1,
        ∫⁻ y in posSimplex {j : α // j ≠ i} (1 - t),
          g ((Homeomorph.funSplitAt ℝ i).symm (t, y)) := by
  let e := Homeomorph.funSplitAt ℝ i
  let G : ℝ × ({j : α // j ≠ i} → ℝ) → ENNReal := fun p => g (e.symm p)
  have hmp := volume_preserving_funSplitAt i
  have hset : e '' posSimplex α 1 = posSimplexSlices i 1 :=
    image_posSimplex_funSplitAt i 1
  calc
    ∫⁻ x in posSimplex α 1, g x =
        ∫⁻ p in posSimplexSlices i 1, G p ∂volume.prod volume := by
      rw [← hset]
      convert (hmp.restrict_image_emb e.measurableEmbedding
        (posSimplex α 1)).lintegral_comp_emb e.measurableEmbedding G using 1
      apply lintegral_congr
      intro x
      exact congrArg g (e.symm_apply_apply x).symm
    _ = ∫⁻ t, ∫⁻ y, (posSimplexSlices i 1).indicator G (t, y) := by
      rw [← lintegral_indicator (measurableSet_posSimplexSlices i 1)]
      exact lintegral_prod _ ((hg.comp e.symm.measurable).indicator
        (measurableSet_posSimplexSlices i 1)).aemeasurable
    _ = ∫⁻ t in Set.Icc (0 : ℝ) 1,
        ∫⁻ y in posSimplex {j : α // j ≠ i} (1 - t),
          g (e.symm (t, y)) := by
      rw [← lintegral_indicator measurableSet_Icc]
      apply lintegral_congr
      intro t
      by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
      · rw [Set.indicator_of_mem ht]
        rw [← lintegral_indicator (measurableSet_posSimplex _ _)]
        apply lintegral_congr
        intro y
        have hy : ((t, y) ∈ posSimplexSlices i 1 ↔
            y ∈ posSimplex {j : α // j ≠ i} (1 - t)) := by
          exact Set.ext_iff.mp (preimage_posSimplexSlices_of_mem i 1 t ht) y
        simp only [Set.indicator_apply]
        simp [hy, G]
      · simp only [Set.indicator_apply, ht, ↓reduceIte]
        apply lintegral_eq_zero_of_ae_eq_zero
        filter_upwards [] with y
        have hy : (t, y) ∉ posSimplexSlices i 1 := by
          intro hmem
          have : y ∈ Prod.mk t ⁻¹' posSimplexSlices i 1 := hmem
          rw [preimage_posSimplexSlices_eq_empty_of_not_mem i 1 t ht] at this
          exact this
        simp [hy]

open scoped Classical in
/-- Scaling a positive-simplex slice produces the expected power of its radius. -/
private theorem integral_posSimplex_scale
    {α : Type*} [Fintype α] (i : α)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (hc : 0 < c) (g : ({j : α // j ≠ i} → ℝ) → E) :
    ∫ y in posSimplex {j : α // j ≠ i} c, g y =
      (c ^ (Fintype.card α - 1)) •
        ∫ x in posSimplex {j : α // j ≠ i} 1, g (c • x) := by
  let h : ({j : α // j ≠ i} → ℝ) → E :=
    (posSimplex {j : α // j ≠ i} c).indicator g
  have hs : ∀ x : {j : α // j ≠ i} → ℝ,
      x ∈ posSimplex {j : α // j ≠ i} 1 ↔
        c • x ∈ posSimplex {j : α // j ≠ i} c := by
    intro x
    simp only [posSimplex, Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul]
    constructor
    · rintro ⟨hx, hsum⟩
      refine ⟨fun q => mul_nonneg hc.le (hx q), ?_⟩
      rw [← Finset.mul_sum]
      nlinarith
    · rintro ⟨hx, hsum⟩
      refine ⟨fun q => nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hx q) hc, ?_⟩
      rw [← Finset.mul_sum] at hsum
      nlinarith
  have hi := integral_smul_free_coords i c hc h
  rw [integral_indicator (measurableSet_posSimplex _ _)] at hi
  have hil : (∫ x, h (c • x)) =
      ∫ x in posSimplex {j : α // j ≠ i} 1, g (c • x) := by
    rw [← integral_indicator (measurableSet_posSimplex _ _)]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [h, Set.indicator_apply]
    rw [if_congr (hs x).symm rfl rfl]
  rw [hil] at hi
  have hc_pow : c ^ (Fintype.card α - 1) ≠ 0 := pow_ne_zero _ hc.ne'
  symm
  rw [hi, smul_inv_smul₀ hc_pow]

open scoped Classical in
/-- Scaling a positive-simplex slice in the nonnegative integral. -/
theorem lintegral_posSimplex_scale
    {α : Type*} [Fintype α] (i : α) (c : ℝ) (hc : 0 < c)
    (g : ({j : α // j ≠ i} → ℝ) → ENNReal) :
    ∫⁻ y in posSimplex {j : α // j ≠ i} c, g y =
      ENNReal.ofReal (c ^ (Fintype.card α - 1)) *
        ∫⁻ x in posSimplex {j : α // j ≠ i} 1, g (c • x) := by
  let e : ({j : α // j ≠ i} → ℝ) ≃ᵐ ({j : α // j ≠ i} → ℝ) :=
    (Homeomorph.smulOfNeZero c hc.ne').toMeasurableEquiv
  let h : ({j : α // j ≠ i} → ℝ) → ENNReal :=
    (posSimplex {j : α // j ≠ i} c).indicator g
  have hs : ∀ x : {j : α // j ≠ i} → ℝ,
      x ∈ posSimplex {j : α // j ≠ i} 1 ↔
        c • x ∈ posSimplex {j : α // j ≠ i} c := by
    intro x
    simp only [posSimplex, Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul]
    constructor
    · rintro ⟨hx, hsum⟩
      refine ⟨fun q => mul_nonneg hc.le (hx q), ?_⟩
      rw [← Finset.mul_sum]
      nlinarith
    · rintro ⟨hx, hsum⟩
      refine ⟨fun q => nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hx q) hc, ?_⟩
      rw [← Finset.mul_sum] at hsum
      nlinarith
  let A : ENNReal := ENNReal.ofReal (c ^ (Fintype.card α - 1))
  have hmap : Measure.map e volume = A⁻¹ • volume := by
    rw [show A⁻¹ = ENNReal.ofReal (c ^ (Fintype.card α - 1))⁻¹ by
      exact (ENNReal.ofReal_inv_of_pos (pow_pos hc _)).symm]
    simpa [e] using volume_map_smul_free_coords i c hc
  have hi : (∫⁻ x, h (c • x)) = A⁻¹ * ∫⁻ x, h x := by
    change (∫⁻ x, h (e x)) = _
    rw [← e.measurableEmbedding.lintegral_map h, hmap, lintegral_smul_measure]
    rfl
  have hA0 : A ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (pow_pos hc _)
  have hAtop : A ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [← lintegral_indicator (measurableSet_posSimplex _ _)]
  have hil : (∫⁻ x, h (c • x)) =
      ∫⁻ x in posSimplex {j : α // j ≠ i} 1, g (c • x) := by
    rw [← lintegral_indicator (measurableSet_posSimplex _ _)]
    apply lintegral_congr
    intro x
    simp only [h, Set.indicator_apply]
    rw [if_congr (hs x).symm rfl rfl]
  rw [← hil, hi, ← mul_assoc, ENNReal.mul_inv_cancel hA0 hAtop, one_mul]

/- Helper theorems towards integral_stdSimplex_split_at -/

open scoped Classical in
/-- Equivalence of the nested-slice coordinate map and the directly scaled coordinate map. -/
theorem stdSimplexCoordMap_split_eq (i j : ι) (hij : i ≠ j)
    (t : ℝ) (v : {q : ι // q ≠ i} → ℝ) (h_sum : ∑ q, v q = 1) :
    let C := {q : {q : ι // q ≠ j} // q ≠ ⟨i, hij⟩}
    let e := stdSimplexDoubleComplementEquiv i j hij
    stdSimplexCoordMap j ((Homeomorph.funSplitAt ℝ ⟨i, hij⟩).symm
      (t, fun q : C ↦ (1 - t) * v (e.symm q))) =
    stdSimplexCoordMap i (fun q ↦ (1 - t) * v q) := by
  dsimp only
  let ii : {q : ι // q ≠ j} := ⟨i, hij⟩
  let jj : {q : ι // q ≠ i} := ⟨j, hij.symm⟩
  let e := stdSimplexDoubleComplementEquiv i j hij
  let y : {q : {q : ι // q ≠ j} // q ≠ ii} → ℝ :=
    fun q => (1 - t) * v (e.symm q)
  let z := (Homeomorph.funSplitAt ℝ ii).symm (t, y)
  have hz : (Homeomorph.funSplitAt ℝ ii) z = (t, y) :=
    (Homeomorph.funSplitAt ℝ ii).apply_symm_apply (t, y)
  have hzself : z ii = t := congrArg Prod.fst hz
  have hzrest : (fun q : {q : {q : ι // q ≠ j} // q ≠ ii} => z q) = y :=
    congrArg Prod.snd hz
  have hsum_rest : (∑ q : {q : {q : ι // q ≠ i} // q ≠ jj}, v q) = 1 - v jj := by
    have h := Fintype.sum_eq_add_sum_subtype_ne v jj
    rw [h_sum] at h
    linarith
  ext q
  by_cases hqi : q = i
  · subst q
    rw [stdSimplexCoordMap_apply_of_ne j i hij, stdSimplexCoordMap_apply_self]
    change z ii = 1 - ∑ q, (1 - t) * v q
    rw [hzself, ← Finset.mul_sum, h_sum]
    ring
  by_cases hqj : q = j
  · subst q
    rw [stdSimplexCoordMap_apply_self, stdSimplexCoordMap_apply_of_ne i j hij.symm]
    change 1 - ∑ q, z q = (1 - t) * v jj
    rw [Fintype.sum_eq_add_sum_subtype_ne z ii, hzself, hzrest]
    simp only [y, ← Finset.mul_sum]
    have hreindex : (∑ q, v (e.symm q)) =
        ∑ q : {q : {q : ι // q ≠ i} // q ≠ jj}, v q := by
      exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
    rw [hreindex, hsum_rest]
    ring
  · rw [stdSimplexCoordMap_apply_of_ne j q hqj,
      stdSimplexCoordMap_apply_of_ne i q hqi]
    change z ⟨q, hqj⟩ = (1 - t) * v ⟨q, hqi⟩
    have hne : (⟨q, hqj⟩ : {q : ι // q ≠ j}) ≠ ii := by
      intro h
      exact hqi (congrArg Subtype.val h)
    rw [congrFun hzrest ⟨⟨q, hqj⟩, hne⟩]
    rfl

open scoped Classical in
/-- Evaluates the inner sliced integral by reindexing the double-complement and scaling. -/
theorem integral_posSimplex_inner_slice
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i j : ι) (hij : i ≠ j) (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) (f : (ι → ℝ) → E) :
    let C := {q : {q : ι // q ≠ j} // q ≠ ⟨i, hij⟩}
    ∫ y in posSimplex C (1 - t),
      f (stdSimplexCoordMap j ((Homeomorph.funSplitAt ℝ ⟨i, hij⟩).symm (t, y))) =
    ((1 - t) ^ (Fintype.card ι - 2)) •
      ∫ v in Convexity.StdSimplex.coordinateSet ℝ {q : ι // q ≠ i},
        f (stdSimplexCoordMap i (fun q ↦ (1 - t) * v q)) ∂stdSimplexMeasure := by
  dsimp only
  let jj : {q : ι // q ≠ i} := ⟨j, hij.symm⟩
  have hc : 0 < 1 - t := sub_pos.mpr ht.2
  have hs := integral_posSimplex_scale
    (⟨i, hij⟩ : {q : ι // q ≠ j}) (1 - t) hc
    (fun y => f (stdSimplexCoordMap j
      ((Homeomorph.funSplitAt ℝ ⟨i, hij⟩).symm (t, y))))
  convert hs using 1
  · congr <;> funext q <;> apply Subsingleton.elim
  · have hcard : Fintype.card {q : ι // q ≠ j} - 1 = Fintype.card ι - 2 := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
      omega
    rw [hcard]
    congr 1
    symm
    have hr := integral_posSimplex_stdSimplexDoubleComplementEquiv i j hij
      (fun y => f (stdSimplexCoordMap j
        ((Homeomorph.funSplitAt ℝ ⟨i, hij⟩).symm (t, (1 - t) • y))))
    convert hr using 1
    · congr <;> funext q <;> apply Subsingleton.elim
    · let _ : Nonempty {q : ι // q ≠ i} := ⟨jj⟩
      rw [integral_stdSimplex_eq_integral_freeCoords jj]
      convert MeasureTheory.integral_congr_ae (μ := volume.restrict (stdSimplexFreeCoords jj)) ?_ using 1
      · congr <;> funext q <;> apply Subsingleton.elim
      filter_upwards [] with x
      apply congrArg f
      symm
      have hfun :
          (1 - t) • (MeasurableEquiv.piCongrLeft (fun _ => ℝ)
            (stdSimplexDoubleComplementEquiv i j hij)) x =
            fun q => (1 - t) * stdSimplexCoordMap jj x
              ((stdSimplexDoubleComplementEquiv i j hij).symm q) := by
        funext q
        rw [stdSimplexCoordMap_apply_of_ne jj _
          ((stdSimplexDoubleComplementEquiv i j hij).symm q).property]
        rfl
      rw [hfun]
      exact stdSimplexCoordMap_split_eq i j hij t (stdSimplexCoordMap jj x)
        (sum_stdSimplexCoordMap jj x)

open scoped Classical in
/-- Evaluates a nonnegative inner sliced integral by reindexing the double complement and
scaling. -/
theorem lintegral_posSimplex_inner_slice
    (i j : ι) (hij : i ≠ j) (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (f : (ι → ℝ) → ENNReal) :
    let C := {q : {q : ι // q ≠ j} // q ≠ ⟨i, hij⟩}
    ∫⁻ y in posSimplex C (1 - t),
      f (stdSimplexCoordMap j ((Homeomorph.funSplitAt ℝ ⟨i, hij⟩).symm (t, y))) =
    ENNReal.ofReal ((1 - t) ^ (Fintype.card ι - 2)) *
      ∫⁻ v in Convexity.StdSimplex.coordinateSet ℝ {q : ι // q ≠ i},
        f (stdSimplexCoordMap i (fun q ↦ (1 - t) * v q)) ∂stdSimplexMeasure := by
  dsimp only
  let jj : {q : ι // q ≠ i} := ⟨j, hij.symm⟩
  have hc : 0 < 1 - t := sub_pos.mpr ht.2
  have hs := lintegral_posSimplex_scale
    (⟨i, hij⟩ : {q : ι // q ≠ j}) (1 - t) hc
    (fun y => f (stdSimplexCoordMap j
      ((Homeomorph.funSplitAt ℝ ⟨i, hij⟩).symm (t, y))))
  convert hs using 1
  · congr <;> funext q <;> apply Subsingleton.elim
  · have hcard : Fintype.card {q : ι // q ≠ j} - 1 = Fintype.card ι - 2 := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
      omega
    rw [hcard]
    congr 1
    symm
    have hr := lintegral_posSimplex_stdSimplexDoubleComplementEquiv i j hij
      (fun y => f (stdSimplexCoordMap j
        ((Homeomorph.funSplitAt ℝ ⟨i, hij⟩).symm (t, (1 - t) • y))))
    convert hr using 1
    · congr <;> funext q <;> apply Subsingleton.elim
    · let _ : Nonempty {q : ι // q ≠ i} := ⟨jj⟩
      rw [lintegral_stdSimplex_eq_lintegral_freeCoords jj]
      convert MeasureTheory.lintegral_congr (μ :=
        volume.restrict (stdSimplexFreeCoords jj)) ?_ using 1
      · congr <;> funext q <;> apply Subsingleton.elim
      intro x
      apply congrArg f
      symm
      have hfun :
          (1 - t) • (MeasurableEquiv.piCongrLeft (fun _ => ℝ)
            (stdSimplexDoubleComplementEquiv i j hij)) x =
            fun q => (1 - t) * stdSimplexCoordMap jj x
              ((stdSimplexDoubleComplementEquiv i j hij).symm q) := by
        funext q
        rw [stdSimplexCoordMap_apply_of_ne jj _
          ((stdSimplexDoubleComplementEquiv i j hij).symm q).property]
        rfl
      rw [hfun]
      exact stdSimplexCoordMap_split_eq i j hij t (stdSimplexCoordMap jj x)
        (sum_stdSimplexCoordMap jj x)

open scoped Classical in
/-- Tonelli reduction of a nonnegative integral over the standard simplex after separating one
coordinate. Unlike `integral_stdSimplex_split_at`, no integrability hypothesis is required. -/
public theorem lintegral_stdSimplex_split_at
    (i : ι) [Nontrivial ι] (f : (ι → ℝ) → ENNReal) (hf : Measurable f) :
    ∫⁻ u in Convexity.StdSimplex.coordinateSet ℝ ι, f u ∂stdSimplexMeasure =
      ∫⁻ t in Set.Icc (0 : ℝ) 1,
        ENNReal.ofReal ((1 - t) ^ (card ι - 2)) *
          ∫⁻ v in Convexity.StdSimplex.coordinateSet ℝ {j // j ≠ i},
            f (stdSimplexCoordMap i (fun j ↦ (1 - t) * v j)) ∂stdSimplexMeasure := by
  obtain ⟨j, hji⟩ := exists_ne i
  rw [lintegral_stdSimplex_eq_lintegral_freeCoords j]
  change (∫⁻ x in posSimplex {q : ι // q ≠ j} 1,
    f (stdSimplexCoordMap j x)) = _
  rw [lintegral_posSimplex_split (⟨i, hji.symm⟩ : {q : ι // q ≠ j})]
  · apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae
        (Ico_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := 1)),
      ae_restrict_mem (μ := volume) measurableSet_Icc] with t heq htIcc
    have htIco : t ∈ Set.Ico (0 : ℝ) 1 := by
      exact heq.mpr htIcc
    convert lintegral_posSimplex_inner_slice i j hji.symm t htIco f using 1
    congr
    funext q
    apply Subsingleton.elim
    funext q
    apply Subsingleton.elim
    funext y
    congr
    funext a b
    apply Subsingleton.elim
  · exact hf.comp (continuous_stdSimplexCoordMap j).measurable

open scoped Classical in
/-- Evaluates an integral over the standard simplex by separating out the `i`-th coordinate.
This theorem provides the standard Fubini reduction (integration by slices) for the simplex.
It expresses the integral of a function `f` over the $(k-1)$-simplex (where $k$ is `card ι`)
as an iterated integral:
1. An outer 1D integral over the isolated coordinate $t \in [0, 1]$.
2. An inner integral over the $(k-2)$-simplex of the remaining coordinates $v$.
Because the remaining coordinates are subject to the constraint $\sum v = 1 - t$, they are
scaled by $(1 - t)$ to map them back to a standard unit $(k-1)$-simplex.
This change of variables introduces a Jacobian determinant factor of $(1 - t)^{k - 2}$. -/
public theorem integral_stdSimplex_split_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : ι) [Nontrivial ι]
    (f : (ι → ℝ) → E)
    (hf : IntegrableOn f (Convexity.StdSimplex.coordinateSet ℝ ι) stdSimplexMeasure) :
  ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, f u ∂stdSimplexMeasure =
    ∫ t in Set.Icc (0 : ℝ) 1,
      ((1 - t) ^ (card ι - 2)) •
      ∫ v in Convexity.StdSimplex.coordinateSet ℝ {j // j ≠ i}, f (stdSimplexCoordMap i (fun j ↦ (1 - t) * v j))
        ∂stdSimplexMeasure := by
  obtain ⟨j, hji⟩ := exists_ne i
  have hg : IntegrableOn (fun x => f (stdSimplexCoordMap j x))
      (stdSimplexFreeCoords j) := by
    have hfm := hf
    change Integrable f (stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι)) at hfm
    rw [stdSimplexMeasure_restrict_stdSimplex j] at hfm
    change Integrable (fun x => f (stdSimplexCoordMap j x))
      (volume.restrict (stdSimplexFreeCoords j))
    exact (isClosedEmbedding_stdSimplexCoordMap j).measurableEmbedding.integrable_map_iff.mp hfm
  rw [integral_stdSimplex_eq_integral_freeCoords j]
  change (∫ x in posSimplex {q : ι // q ≠ j} 1, f (stdSimplexCoordMap j x)) = _
  rw [integral_posSimplex_split (⟨i, hji.symm⟩ : {q : ι // q ≠ j}) _ hg]
  simp_rw [integral_Icc_eq_integral_Ico]
  have h_inner : ∀ᵐ t ∂(volume.restrict (Set.Ico (0 : ℝ) 1)),
      (∫ y in posSimplex {q : {q : ι // q ≠ j} // q ≠ ⟨i, hji.symm⟩} (1 - t),
        f (stdSimplexCoordMap j ((Homeomorph.funSplitAt ℝ ⟨i, hji.symm⟩).symm (t, y)))) =
      ((1 - t) ^ (card ι - 2)) •
        ∫ v in Convexity.StdSimplex.coordinateSet ℝ {j // j ≠ i},
          f (stdSimplexCoordMap i (fun j ↦ (1 - t) * v j)) ∂stdSimplexMeasure := by
    filter_upwards [self_mem_ae_restrict (μ := volume) measurableSet_Ico] with t ht
    exact integral_posSimplex_inner_slice i j hji.symm t ht f
  -- The displayed nested subtype types differ only in synthesized decidability data.
  convert MeasureTheory.integral_congr_ae h_inner using 1
  congr
  funext t
  congr
  · funext q
    apply Subsingleton.elim
  · funext q
    apply Subsingleton.elim
  · funext y
    congr
    funext a b
    apply Subsingleton.elim

end MeasureTheory

end StdSimplexIntegral
