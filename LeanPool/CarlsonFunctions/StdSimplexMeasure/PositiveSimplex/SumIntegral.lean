/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.StdSimplexMeasure.PositiveSimplex.Basic

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

public import LeanPool.CarlsonFunctions.StdSimplexMeasure.ProdSlices

/-! # Solid simplex integration by coordinate sum -/

open MeasureTheory

@[expose] public noncomputable section

/-- Tonelli's theorem on the triangle `0 ≤ t ≤ s ≤ r`. -/
lemma lintegral_Icc_triangle_swap (r : ℝ) (_hr : 0 ≤ r)
    (F : ℝ → ℝ → ENNReal) (hF : Measurable (Function.uncurry F)) :
    ∫⁻ t in Set.Icc (0 : ℝ) r, ∫⁻ s in Set.Icc t r, F t s =
      ∫⁻ s in Set.Icc (0 : ℝ) r, ∫⁻ t in Set.Icc (0 : ℝ) s, F t s := by
  let S : Set (ℝ × ℝ) := {p | p.1 ∈ Set.Icc (0 : ℝ) r ∧ p.2 ∈ Set.Icc p.1 r}
  have hS : MeasurableSet S :=
    measurableSet_region_between_cc measurable_id measurable_const
      (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) r))
  have hG : Measurable (S.indicator fun p => F p.1 p.2) := hF.indicator hS
  have hcond (t s : ℝ) :
      t ∈ Set.Icc (0 : ℝ) r ∧ s ∈ Set.Icc t r ↔
        s ∈ Set.Icc (0 : ℝ) r ∧ t ∈ Set.Icc (0 : ℝ) s := by
    simp only [Set.mem_Icc]
    constructor
    · intro ⟨⟨ht0, _htr⟩, ⟨hts, hsr⟩⟩
      exact ⟨⟨le_trans ht0 hts, hsr⟩, ⟨ht0, hts⟩⟩
    · intro ⟨⟨_hs0, hsr⟩, ⟨ht0, hts⟩⟩
      exact ⟨⟨ht0, le_trans hts hsr⟩, ⟨hts, hsr⟩⟩
  have hleft :
      ∫⁻ t in Set.Icc (0 : ℝ) r, ∫⁻ s in Set.Icc t r, F t s =
        ∫⁻ t, ∫⁻ s, S.indicator (fun p => F p.1 p.2) (t, s) := by
    rw [← lintegral_indicator measurableSet_Icc]
    apply lintegral_congr
    intro t
    by_cases ht : t ∈ Set.Icc (0 : ℝ) r
    · rw [Set.indicator_of_mem ht, ← lintegral_indicator measurableSet_Icc]
      apply lintegral_congr
      intro s
      by_cases hs : s ∈ Set.Icc t r
      · simp [Set.indicator_of_mem hs, Set.indicator_of_mem (show (t, s) ∈ S from ⟨ht, hs⟩)]
      · simp [Set.indicator_of_notMem hs,
          Set.indicator_of_notMem (show (t, s) ∉ S from fun h => hs h.2)]
    · rw [Set.indicator_of_notMem ht]
      refine Eq.symm (lintegral_eq_zero_of_ae_eq_zero ?_)
      exact Filter.Eventually.of_forall fun s =>
        Set.indicator_of_notMem (fun h : (t, s) ∈ S => ht h.1)
          (fun p => F p.1 p.2)
  have hright :
      ∫⁻ s in Set.Icc (0 : ℝ) r, ∫⁻ t in Set.Icc (0 : ℝ) s, F t s =
        ∫⁻ s, ∫⁻ t, S.indicator (fun p => F p.1 p.2) (t, s) := by
    rw [← lintegral_indicator measurableSet_Icc]
    apply lintegral_congr
    intro s
    by_cases hs : s ∈ Set.Icc (0 : ℝ) r
    · rw [Set.indicator_of_mem hs, ← lintegral_indicator measurableSet_Icc]
      apply lintegral_congr
      intro t
      by_cases ht : t ∈ Set.Icc (0 : ℝ) s
      · have hmem : (t, s) ∈ S := (hcond t s).2 ⟨hs, ht⟩
        simp [Set.indicator_of_mem ht, Set.indicator_of_mem hmem]
      · have hnmem : (t, s) ∉ S := fun h => ht ((hcond t s).1 h).2
        simp [Set.indicator_of_notMem ht, Set.indicator_of_notMem hnmem]
    · rw [Set.indicator_of_notMem hs]
      refine Eq.symm (lintegral_eq_zero_of_ae_eq_zero ?_)
      exact Filter.Eventually.of_forall fun t =>
        Set.indicator_of_notMem (fun h : (t, s) ∈ S => hs ((hcond t s).1 h).1)
          (fun p => F p.1 p.2)
  rw [hleft, hright]
  exact lintegral_lintegral_swap hG.aemeasurable

/-- Pushing the positive `Fin n`-simplex forward under the coordinate-sum map. -/
theorem lintegral_posSimplexFin_comp_sum (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : 0 ≤ r)
    (g : ℝ → ENNReal) (hg : Measurable g) :
    ∫⁻ x in posSimplexFin n r, g (∑ i, x i) =
      ∫⁻ s in Set.Icc (0 : ℝ) r,
        g s * (ENNReal.ofReal s ^ (n - 1) / Nat.factorial (n - 1)) := by
  induction n generalizing r g with
  | zero =>
      exact (Nat.not_lt_zero _ hn).elim
  | succ n ih =>
      let e : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
      let T := posSimplexFinSuccSlices n r
      have hT : MeasurableSet T := measurableSet_posSimplexFinSuccSlices n r
      have he : e '' posSimplexFin (n + 1) r = T :=
        image_posSimplexFin_piFinSuccAbove n r
      have hpre : e ⁻¹' T = posSimplexFin (n + 1) r := by
        exact (Set.preimage_eq_iff_eq_image e.bijective).2 he.symm
      have hmp := volume_preserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => ℝ) 0
      have hgT : Measurable fun p : ℝ × (Fin n → ℝ) => g (p.1 + ∑ i, p.2 i) := by
        fun_prop
      have hsum_e (p : ℝ × (Fin n → ℝ)) :
          ∑ i, e.symm p i = p.1 + ∑ i, p.2 i := by
        have hp := e.apply_symm_apply p
        have hp1 : e.symm p 0 = p.1 := congrArg Prod.fst hp
        have hp2 : (fun i => e.symm p (Fin.succ i)) = p.2 := congrArg Prod.snd hp
        rw [Fin.sum_univ_succ, hp1, hp2]
      calc
        ∫⁻ x in posSimplexFin (n + 1) r, g (∑ i, x i) =
            ∫⁻ x in e ⁻¹' T, g (∑ i, x i) := by rw [hpre]
        _ = ∫⁻ p in T, g (∑ i, e.symm p i) := by
          refine Eq.trans ?_
            (hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding
              (fun p => g (∑ i, e.symm p i)) T)
          apply setLIntegral_congr_fun (hpre ▸ measurableSet_posSimplexFin (n + 1) r)
          intro x _
          congr 1
          exact (e.symm_apply_apply x).symm
        _ = ∫⁻ p in T, g (p.1 + ∑ i, p.2 i) := by
          apply setLIntegral_congr_fun hT
          intro p _
          exact congrArg g (hsum_e p)
        _ = ∫⁻ t, ∫⁻ y in Prod.mk t ⁻¹' T, g (t + ∑ i, y i) := by
          rw [Measure.volume_eq_prod]
          exact setLIntegral_prod_slices T hT _ hgT.aemeasurable
        _ = ∫⁻ t in Set.Icc (0 : ℝ) r,
              ∫⁻ y in posSimplexFin n (r - t), g (t + ∑ i, y i) := by
          rw [← lintegral_indicator measurableSet_Icc]
          apply lintegral_congr
          intro t
          by_cases ht : t ∈ Set.Icc (0 : ℝ) r
          · rw [Set.indicator_of_mem ht, preimage_posSimplexFinSuccSlices_of_mem n r t ht]
          · rw [Set.indicator_of_notMem ht,
              preimage_posSimplexFinSuccSlices_eq_empty_of_not_mem n r t ht, setLIntegral_empty]
        _ = ∫⁻ s in Set.Icc (0 : ℝ) r,
              g s * (ENNReal.ofReal s ^ n / Nat.factorial n) := by
          cases n with
          | zero =>
              have hinner (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) r) :
                  ∫⁻ y in posSimplexFin 0 (r - t), g (t + ∑ i, y i) = g t := by
                have hr't : 0 ≤ r - t := sub_nonneg.mpr ht.2
                have huniv : posSimplexFin 0 (r - t) = Set.univ := by
                  ext y
                  simp [posSimplexFin, hr't]
                rw [huniv, Measure.restrict_univ, Measure.volume_pi_eq_dirac, lintegral_dirac]
                simp
              apply setLIntegral_congr_fun measurableSet_Icc
              intro t ht
              change ∫⁻ y in posSimplexFin 0 (r - t), g (t + ∑ i, y i) =
                g t * (ENNReal.ofReal t ^ 0 / Nat.factorial 0)
              rw [hinner t ht]
              simp
          | succ m =>
              have hn' : 0 < m + 1 := Nat.succ_pos _
              have hinner (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) r) :
                  ∫⁻ y in posSimplexFin (m + 1) (r - t), g (t + ∑ i, y i) =
                    ∫⁻ σ in Set.Icc (0 : ℝ) (r - t),
                      g (t + σ) *
                        (ENNReal.ofReal σ ^ m / Nat.factorial m) := by
                have hr't : 0 ≤ r - t := sub_nonneg.mpr ht.2
                simpa using ih hn' (r - t) hr't (fun σ => g (t + σ)) (by fun_prop)
              have hshift (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) r) :
                  ∫⁻ σ in Set.Icc (0 : ℝ) (r - t),
                      g (t + σ) *
                        (ENNReal.ofReal σ ^ m / Nat.factorial m) =
                    ∫⁻ s in Set.Icc t r,
                      g s *
                        (ENNReal.ofReal (s - t) ^ m / Nat.factorial m) := by
                have hr't : 0 ≤ r - t := sub_nonneg.mpr ht.2
                have hmp' := measurePreserving_add_left (volume : Measure ℝ) t
                have hpre : (fun σ : ℝ => t + σ) ⁻¹' Set.Icc t r =
                    Set.Icc (0 : ℝ) (r - t) := by
                  ext σ
                  constructor
                  · intro h
                    simp only [Set.mem_preimage, Set.mem_Icc] at h ⊢
                    exact ⟨by linarith, by linarith⟩
                  · intro h
                    simp only [Set.mem_preimage, Set.mem_Icc] at h ⊢
                    exact ⟨by linarith, by linarith⟩
                have := hmp'.setLIntegral_comp_preimage (s := Set.Icc t r)
                  measurableSet_Icc (f := fun s =>
                    g s * (ENNReal.ofReal (s - t) ^ m / Nat.factorial m)) (by fun_prop)
                simpa [hpre] using this
              trans ∫⁻ t in Set.Icc (0 : ℝ) r, ∫⁻ s in Set.Icc t r,
                  g s * (ENNReal.ofReal (s - t) ^ m / Nat.factorial m)
              · apply setLIntegral_congr_fun measurableSet_Icc
                intro t ht
                exact (hinner t ht).trans (hshift t ht)
              · have hF : Measurable (Function.uncurry fun t s : ℝ =>
                    g s * (ENNReal.ofReal (s - t) ^ m / Nat.factorial m)) := by
                  fun_prop
                rw [lintegral_Icc_triangle_swap r hr _ hF]
                apply setLIntegral_congr_fun measurableSet_Icc
                intro s hs
                have hs0 : 0 ≤ s := hs.1
                have hinter := lintegral_Icc_sub_pow_div_factorial m s hs0
                calc
                  ∫⁻ t in Set.Icc (0 : ℝ) s,
                      g s * (ENNReal.ofReal (s - t) ^ m / Nat.factorial m) =
                      g s * ∫⁻ t in Set.Icc (0 : ℝ) s,
                        ENNReal.ofReal (s - t) ^ m / Nat.factorial m := by
                    rw [lintegral_const_mul]
                    fun_prop
                  _ = g s * (ENNReal.ofReal s ^ (m + 1) / Nat.factorial (m + 1)) := by
                    rw [hinter]

/-- Pushing an arbitrary finite-dimensional positive simplex forward under the coordinate-sum
map. Requires a nonempty index type so that the exponent `card α - 1` is well-defined. -/
theorem lintegral_posSimplex_comp_sum {α : Type*} [Fintype α] [Nonempty α]
    (r : ℝ) (hr : 0 ≤ r) (g : ℝ → ENNReal) (hg : Measurable g) :
    ∫⁻ x in posSimplex α r, g (∑ i, x i) =
      ∫⁻ s in Set.Icc (0 : ℝ) r,
        g s * (ENNReal.ofReal s ^ (Fintype.card α - 1) /
          Nat.factorial (Fintype.card α - 1)) := by
  let σ : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  let e : (Fin (Fintype.card α) → ℝ) ≃ᵐ (α → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : α => ℝ) σ
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : α => ℝ) σ
  have hn : 0 < Fintype.card α := Fintype.card_pos
  have hsum (y : Fin (Fintype.card α) → ℝ) :
      ∑ j, e y j = ∑ i, y i := by
    calc
      ∑ j, e y j = ∑ i, e y (σ i) := (σ.sum_comp _).symm
      _ = ∑ i, y i := by
          apply Finset.sum_congr rfl
          intro i _
          exact Equiv.piCongrLeft_apply_apply (P := fun _ : α => ℝ) σ y i
  have himage : e ⁻¹' posSimplex α r = posSimplexFin (Fintype.card α) r := by
    ext y
    constructor
    · intro hy
      have hy' : e y ∈ posSimplex α r := hy
      rcases hy' with ⟨hy0, hys⟩
      refine ⟨?_, ?_⟩
      · intro i
        have := hy0 (σ i)
        simpa [e, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft] using this
      · simpa [hsum] using hys
    · intro hy
      rcases hy with ⟨hy0, hys⟩
      refine ⟨?_, ?_⟩
      · intro j
        simpa [e, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft] using hy0 (σ.symm j)
      · simpa [hsum] using hys
  calc
    ∫⁻ x in posSimplex α r, g (∑ i, x i) =
        ∫⁻ y in e ⁻¹' posSimplex α r, g (∑ j, e y j) :=
      (hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding _ _).symm
    _ = ∫⁻ y in posSimplexFin (Fintype.card α) r, g (∑ i, y i) := by
      rw [himage]
      apply setLIntegral_congr_fun (measurableSet_posSimplexFin _ _)
      intro y _
      exact congrArg g (hsum y)
    _ = _ := lintegral_posSimplexFin_comp_sum (Fintype.card α) hn r hr g hg
