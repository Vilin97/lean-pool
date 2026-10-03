/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Contracts.TermSourcesFluxL2
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.HMinusTools

/-! # Time transfer for the centered `HDot⁻¹` bounds

If at every `t ∈ (0,1)` the `HDot⁻¹` norm of a slice is bounded by an affine combination of the
    slice
energies `‖V_j(t)‖_{L²_x}` of three fields continuous on `[0,1] × ℝ²`, then the time-`L²(HDot⁻¹)`
norm is bounded by the same combination of the space-time norms (with a factor `2`). -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.Section5.Contracts

open AVenhance AVenhance.Infra.Section5

theorem sd_sq4 (a b c d : ℝ) : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (c - d)]

theorem sd_time_transfer {f : ℝ → Vec 2 → ℝ} {V : Fin 3 → ℝ → Vec 2 → Vec 2} {P : Fin 3 → ℝ}
    {P₂ : ℝ} (hP : ∀ j, 0 ≤ P j) (hP₂ : 0 ≤ P₂)
    (hV : ∀ j (i : Fin 2), ContinuousOn (fun p : ℝ × Vec 2 => V j p.1 p.2 i)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ))
    (hpt : ∀ t ∈ Set.Ioo (0 : ℝ) 1, hMinusOneNorm (f t) ≤
      ENNReal.ofReal (∑ j, P j * Real.sqrt (gradNormSq (V j t)) + P₂)) :
    timeHMinusOneNorm f ≤
      ENNReal.ofReal (2 * (∑ j, P j * Real.sqrt (spaceTimeGradNormSq (V j)) + P₂)) := by
  have hgcont (j : Fin 3) := sa_sliceEnergy_continuousOn (hV j)
  have hgint (j : Fin 3) : IntegrableOn (fun t => gradNormSq (V j t)) (Set.Ioo (0 : ℝ) 1) :=
    ((hgcont j).integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
  set W : ℝ → ℝ := fun t => 4 * (∑ j, P j ^ 2 * gradNormSq (V j t) + P₂ ^ 2) with hW
  have hWint : IntegrableOn W (Set.Ioo (0 : ℝ) 1) := by
    have h1 : IntegrableOn (fun t => ∑ j, P j ^ 2 * gradNormSq (V j t)) (Set.Ioo (0 : ℝ) 1) :=
      integrable_finsetSum _ fun j _ => (hgint j).const_mul (P j ^ 2)
    exact (h1.add (integrableOn_const (by simp))).const_mul 4
  have hWnn : ∀ t, 0 ≤ W t := fun t => by
    have : 0 ≤ ∑ j, P j ^ 2 * gradNormSq (V j t) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (sa_gradNormSq_nonneg _)
    simp only [hW]
    positivity
  have hZ : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      (∑ j, P j * Real.sqrt (gradNormSq (V j t)) + P₂) ^ 2 ≤ W t := by
    intro t ht
    have hsq (j : Fin 3) : (P j * Real.sqrt (gradNormSq (V j t))) ^ 2 =
        P j ^ 2 * gradNormSq (V j t) := by
      rw [mul_pow, Real.sq_sqrt (sa_gradNormSq_nonneg _)]
    simp only [hW, Fin.sum_univ_three]
    refine (sd_sq4 _ _ _ _).trans_eq ?_
    rw [hsq 0, hsq 1, hsq 2]
  have hbound := timeHMinusOneNorm_le_of_bound
    (f := f) (B := fun t => ENNReal.ofReal
      (∑ j, P j * Real.sqrt (gradNormSq (V j t)) + P₂)) hpt
  have hZnn : ∀ t, 0 ≤ ∑ j, P j * Real.sqrt (gradNormSq (V j t)) + P₂ := fun t =>
    add_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (hP j) (Real.sqrt_nonneg _)) hP₂
  have hlin : (∫⁻ t in Set.Ioo (0 : ℝ) 1,
      ENNReal.ofReal (∑ j, P j * Real.sqrt (gradNormSq (V j t)) + P₂) ^ 2) ≤
      ENNReal.ofReal (∫ t in Set.Ioo (0 : ℝ) 1, W t) := by
    rw [ofReal_integral_eq_lintegral_ofReal hWint (ae_of_all _ hWnn)]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [← ENNReal.ofReal_pow (hZnn t)]
    exact ENNReal.ofReal_le_ofReal (hZ t ht)
  have hint : ∫ t in Set.Ioo (0 : ℝ) 1, W t =
      4 * (∑ j, P j ^ 2 * spaceTimeGradNormSq (V j) + P₂ ^ 2) := by
    simp only [hW]
    rw [integral_const_mul]
    congr 1
    rw [integral_add (integrable_finsetSum _ fun j _ => (hgint j).const_mul (P j ^ 2))
      (integrableOn_const (by simp)), integral_finsetSum _ fun j _ => (hgint j).const_mul _]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul, sa_spaceTime_eq_integral (hV j)]
    · simp
  have hXnn : ∀ j, 0 ≤ spaceTimeGradNormSq (V j) := fun j => sa_spaceTimeGradNormSq_nonneg _
  have hSnn : 0 ≤ ∑ j, P j ^ 2 * spaceTimeGradNormSq (V j) + P₂ ^ 2 :=
    add_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (hXnn j)) (sq_nonneg _)
  refine hbound.trans ?_
  calc _ ≤ (ENNReal.ofReal (∫ t in Set.Ioo (0 : ℝ) 1, W t)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hlin (by norm_num)
    _ = ENNReal.ofReal ((4 * (∑ j, P j ^ 2 * spaceTimeGradNormSq (V j) + P₂ ^ 2)) ^
          (1 / 2 : ℝ)) := by
        rw [hint]
        exact ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num)]
        have h4 : Real.sqrt 4 = 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
          exact Real.sqrt_sq (by norm_num)
        rw [h4]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.sqrt_le_iff.2
        refine ⟨add_nonneg (Finset.sum_nonneg fun j _ =>
          mul_nonneg (hP j) (Real.sqrt_nonneg _)) hP₂, ?_⟩
        have hsq (j : Fin 3) : (P j * Real.sqrt (spaceTimeGradNormSq (V j))) ^ 2 =
            P j ^ 2 * spaceTimeGradNormSq (V j) := by
          rw [mul_pow, Real.sq_sqrt (hXnn j)]
        simp only [Fin.sum_univ_three]
        have p0 := mul_nonneg (hP 0) (Real.sqrt_nonneg (spaceTimeGradNormSq (V 0)))
        have p1 := mul_nonneg (hP 1) (Real.sqrt_nonneg (spaceTimeGradNormSq (V 1)))
        have p2 := mul_nonneg (hP 2) (Real.sqrt_nonneg (spaceTimeGradNormSq (V 2)))
        rw [← hsq 0, ← hsq 1, ← hsq 2]
        nlinarith [mul_nonneg p0 p1, mul_nonneg p0 p2, mul_nonneg p1 p2, mul_nonneg p0 hP₂,
          mul_nonneg p1 hP₂, mul_nonneg p2 hP₂]

end AVenhance.Infra.Section5.Contracts
end
