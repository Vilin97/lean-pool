/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.StdSimplexMeasure.Integral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Finite-coordinate simplex integrals

The last barycentric coordinate is reconstructed from the other coordinates. Separating
the last free coordinate gives the one-dimensional slices used by the simplex FTC.
-/

open MeasureTheory MeasureTheory.Measure

@[expose] public noncomputable section

namespace MeasureTheory

/-- Reconstruct the last barycentric coordinate. -/
def finSimplexPoint (v : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc v (1 - ∑ k, v k)

theorem continuous_finSimplexPoint : Continuous (finSimplexPoint (n := n)) := by
  unfold finSimplexPoint
  fun_prop

theorem finSimplexPoint_mem {v : Fin n → ℝ} (hv : v ∈ posSimplexFin n 1) :
    finSimplexPoint v ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 1)) := by
  constructor
  · intro k
    refine Fin.lastCases ?_ (fun l => ?_) k
    · simpa [finSimplexPoint] using sub_nonneg.mpr hv.2
    · simpa [finSimplexPoint] using hv.1 l
  · simp [finSimplexPoint, Fin.sum_univ_castSucc]

theorem isCompact_posSimplexFin_one (n : ℕ) : IsCompact (posSimplexFin n 1) := by
  have hclosed : IsClosed (posSimplexFin n 1) := by
    change IsClosed ({v : Fin n → ℝ | ∀ k, 0 ≤ v k} ∩ {v | ∑ k, v k ≤ 1})
    simp only [Set.ofPred_forall]
    exact (isClosed_iInter fun k => isClosed_le continuous_const (continuous_apply k)).inter
      (isClosed_le (show Continuous (fun v : Fin n → ℝ => ∑ k, v k) by fun_prop) continuous_const)
  apply isCompact_Icc.of_isClosed_subset hclosed (s := Set.Icc (fun _ => 0) (fun _ => 1))
  intro v hv
  refine ⟨hv.1, fun k => ?_⟩
  exact (Finset.single_le_sum (fun l _ => hv.1 l) (Finset.mem_univ k)).trans hv.2

/-- The standard-simplex integral in the chart omitting its last coordinate. -/
theorem integral_stdSimplex_fin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : (Fin (n + 1) → ℝ) → E) :
    ∫ u in Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 1)), g u ∂stdSimplexMeasure =
      ∫ v in posSimplexFin n 1, g (finSimplexPoint v) := by
  classical
  -- Match the complement's instance used internally by the simplex chart.
  let : Fintype {k : Fin (n + 1) // k ≠ Fin.last n} :=
    @Subtype.fintype _ _ (fun k => @instDecidableNot _ (Classical.propDecidable _)) _
  let e := finSuccAboveEquiv (Fin.last n)
  let T := MeasurableEquiv.piCongrLeft (fun _ : {k : Fin (n + 1) // k ≠ Fin.last n} => ℝ) e
  have hT := volume_measurePreserving_piCongrLeft
    (fun _ : {k : Fin (n + 1) // k ≠ Fin.last n} => ℝ) e
  have happ (v : Fin n → ℝ) (k : {k : Fin (n + 1) // k ≠ Fin.last n}) :
      T v k = v (e.symm k) := by
    simpa only [Equiv.apply_symm_apply] using
      (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝ) e v (e.symm k))
  have hsum (v : Fin n → ℝ) : ∑ k, T v k = ∑ k, v k := by
    simp_rw [happ]
    exact Equiv.sum_comp e.symm v
  have hset : T ⁻¹' stdSimplexFreeCoords (Fin.last n) = posSimplexFin n 1 := by
    ext v
    simp only [Set.mem_preimage, stdSimplexFreeCoords, Set.mem_ofPred_eq]
    simp_rw [hsum, happ]
    constructor
    · intro h
      exact ⟨fun k => by simpa using h.1 (e k), h.2⟩
    · intro h
      exact ⟨fun k => h.1 (e.symm k), h.2⟩
  have hpoint (v : Fin n → ℝ) : stdSimplexCoordMap (Fin.last n) (T v) = finSimplexPoint v := by
    ext k
    refine Fin.lastCases ?_ (fun l => ?_) k
    · rw [stdSimplexCoordMap_apply_self, hsum]
      simp [finSimplexPoint]
    · rw [stdSimplexCoordMap_apply_of_ne _ _ (Fin.castSucc_ne_last l)]
      rw [happ]
      simp [e, finSimplexPoint, finSuccAboveEquiv_symm_apply_last]
  rw [integral_stdSimplex_eq_integral_freeCoords (Fin.last n)]
  have H := hT.setIntegral_preimage_emb T.measurableEmbedding
    (fun v => g (stdSimplexCoordMap (Fin.last n) v)) (stdSimplexFreeCoords (Fin.last n))
  rw [hset] at H
  refine H.symm.trans ?_
  apply setIntegral_congr_fun (measurableSet_posSimplexFin _ _)
  intro v _
  exact congrArg g (hpoint v)

/-- Fubini with the last free coordinate integrated first. -/
theorem integral_posSimplexFin_snoc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : (Fin (n + 1) → ℝ) → E) (hg : IntegrableOn g (posSimplexFin (n + 1) 1)) :
    ∫ v in posSimplexFin (n + 1) 1, g v =
      ∫ v in posSimplexFin n 1, ∫ t in Set.Icc 0 (1 - ∑ k, v k), g (Fin.snoc v t) := by
  classical
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
  have he (t : ℝ) (v : Fin n → ℝ) : e.symm (t, v) = Fin.snoc v t := by
    ext k
    refine Fin.lastCases ?_ (fun l => ?_) k <;> simp [e, MeasurableEquiv.piFinSuccAbove]
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
  let G := (posSimplexFin (n + 1) 1).indicator g
  have hG : Integrable G := hg.integrable_indicator (measurableSet_posSimplexFin _ _)
  have hGe : Integrable (G ∘ e.symm) (volume.prod volume) :=
    (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).mpr hG
  rw [← integral_indicator (measurableSet_posSimplexFin _ _)]
  change (∫ v, G v) = _
  rw [← hmp.symm.integral_comp' G]
  change (∫ p, (G ∘ e.symm) p ∂volume.prod volume) = _
  rw [integral_prod_symm _ hGe]
  rw [← integral_indicator (measurableSet_posSimplexFin _ _)]
  apply integral_congr_ae
  filter_upwards with v
  by_cases hv : v ∈ posSimplexFin n 1
  · rw [Set.indicator_of_mem hv, ← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with t
    have hmem : Fin.snoc v t ∈ posSimplexFin (n + 1) 1 ↔ t ∈ Set.Icc 0 (1 - ∑ k, v k) := by
      simp only [posSimplexFin, Set.mem_ofPred_eq, Fin.sum_univ_castSucc,
        Fin.snoc_castSucc, Fin.snoc_last]
      constructor
      · intro h
        exact ⟨by simpa using h.1 (Fin.last n), by simpa using (show t ≤ 1 - ∑ k, v k by linarith
          [h.2])⟩
      · intro h
        refine ⟨?_, by simpa using (show (∑ k, v k) + t ≤ 1 by linarith [h.2])⟩
        intro k
        refine Fin.lastCases ?_ (fun l => ?_) k <;> simp [hv.1, h.1]
    simp [G, he, Set.indicator_apply, hmem]
  · rw [Set.indicator_of_notMem hv]
    apply integral_eq_zero_of_ae
    filter_upwards with t
    have hnot : Fin.snoc v t ∉ posSimplexFin (n + 1) 1 := by
      intro h
      apply hv
      refine ⟨fun k => by simpa using h.1 k.castSucc, ?_⟩
      have ht : 0 ≤ t := by simpa using h.1 (Fin.last n)
      have hs := h.2
      simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last] at hs
      linarith
    simp [G, he, Set.indicator_of_notMem hnot]

open scoped Classical in
/-- The same Fubini decomposition, with the separated coordinate integrated last. -/
theorem integral_posSimplexFin_snoc_outer {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : (Fin (n + 1) → ℝ) → E) (hg : IntegrableOn g (posSimplexFin (n + 1) 1)) :
    ∫ v in posSimplexFin (n + 1) 1, g v =
      ∫ t in Set.Icc (0 : ℝ) 1, ∫ v in posSimplexFin n (1 - t), g (Fin.snoc v t) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
  have he (t : ℝ) (v : Fin n → ℝ) : e.symm (t, v) = Fin.snoc v t := by
    ext k
    refine Fin.lastCases ?_ (fun l => ?_) k <;> simp [e, MeasurableEquiv.piFinSuccAbove]
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
  let G := (posSimplexFin (n + 1) 1).indicator g
  have hG : Integrable G := hg.integrable_indicator (measurableSet_posSimplexFin _ _)
  have hGe : Integrable (G ∘ e.symm) (volume.prod volume) :=
    (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).mpr hG
  rw [← integral_indicator (measurableSet_posSimplexFin _ _)]
  change (∫ v, G v) = _
  rw [← hmp.symm.integral_comp' G]
  change (∫ p, (G ∘ e.symm) p ∂volume.prod volume) = _
  rw [integral_prod _ hGe, ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
  · rw [Set.indicator_of_mem ht, ← integral_indicator (measurableSet_posSimplexFin _ _)]
    apply integral_congr_ae
    filter_upwards with v
    have hmem : Fin.snoc v t ∈ posSimplexFin (n + 1) 1 ↔ v ∈ posSimplexFin n (1 - t) := by
      constructor
      · intro h
        refine ⟨fun k => by simpa using h.1 k.castSucc, ?_⟩
        have hs := h.2
        simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last] at hs
        linarith
      · intro h
        constructor
        · intro k
          refine Fin.lastCases ?_ (fun l => ?_) k <;> simp [h.1, ht.1]
        · simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
          linarith [h.2]
    simp [G, he, Set.indicator_apply, hmem]
  · rw [Set.indicator_of_notMem ht]
    apply integral_eq_zero_of_ae
    filter_upwards with v
    have hnot : Fin.snoc v t ∉ posSimplexFin (n + 1) 1 := by
      intro h
      apply ht
      have ht0 : 0 ≤ t := by simpa using h.1 (Fin.last n)
      have hs0 : 0 ≤ ∑ k, v k := Finset.sum_nonneg fun k _ => by simpa using h.1 k.castSucc
      have hs := h.2
      simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last] at hs
      exact ⟨ht0, by linarith⟩
    simp [G, he, Set.indicator_of_notMem hnot]

open scoped Classical in
/-- Dilation of the solid simplex. -/
theorem integral_posSimplexFin_scale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : (Fin n → ℝ) → E) {r : ℝ} (hr : 0 < r) :
    ∫ v in posSimplexFin n r, g v =
      r ^ n • ∫ v in posSimplexFin n 1, g (r • v) := by
  let G := (posSimplexFin n r).indicator g
  have hmem (v : Fin n → ℝ) : r • v ∈ posSimplexFin n r ↔ v ∈ posSimplexFin n 1 := by
    simp only [posSimplexFin, Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    constructor
    · intro h
      exact ⟨fun k => by nlinarith [h.1 k], by nlinarith [h.2]⟩
    · intro h
      exact ⟨fun k => mul_nonneg hr.le (h.1 k), by nlinarith [h.2]⟩
  have H := Measure.integral_comp_smul_of_nonneg (volume : Measure (Fin n → ℝ)) G r (hR := hr.le)
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at H
  have heq : (fun v => G (r • v)) = (posSimplexFin n 1).indicator (fun v => g (r • v)) := by
    funext v
    simp [G, Set.indicator_apply, hmem]
  rw [heq, integral_indicator (measurableSet_posSimplexFin _ _)] at H
  rw [H, smul_inv_smul₀ (pow_ne_zero n hr.ne')]
  exact (integral_indicator (measurableSet_posSimplexFin _ _)).symm

end MeasureTheory
