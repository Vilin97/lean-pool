/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Beta.Real
public import LeanPool.CarlsonFunctions.StdSimplexMeasure.Integral

import all LeanPool.CarlsonFunctions.StdSimplexMeasure.Measure.Basic

/-!
# Real Dirichlet monomial integrals

Shared analytic foundations for the real probability distribution and complex Dirichlet
integrals. No Dirichlet probability measure is constructed or imported here.
The historical `ProbabilityTheory` declaration names are retained for compatibility.
-/

open Real MeasureTheory MeasureTheory.Measure
open scoped ENNReal Classical

@[expose] public noncomputable section

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- Scaling the free coordinates in a simplex slice separates a Dirichlet monomial into its
distinguished-coordinate factor, radial factor, and lower-dimensional monomial. -/
private theorem prod_rpow_stdSimplexCoordMap_scale
    (i : ι) (b : ι → ℝ) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1)
    {v : {j : ι // j ≠ i} → ℝ} (hv : v ∈ Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i}) :
    (∏ j, (stdSimplexCoordMap i (fun q ↦ (1 - t) * v q) j) ^ (b j - 1)) =
      t ^ (b i - 1) *
        (1 - t) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1)) *
          ∏ q : {j : ι // j ≠ i}, v q ^ (b q - 1) := by
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
  have hsum : ∑ q, (1 - t) * v q = 1 - t := by
    rw [← Finset.mul_sum, hv.2, mul_one]
  rw [stdSimplexCoordMap_apply_self, hsum]
  have hone : 1 - (1 - t) = t := by ring
  rw [hone]
  have hprod :
      (∏ q : {j : ι // j ≠ i},
        (stdSimplexCoordMap i (fun q ↦ (1 - t) * v q) q) ^ (b q - 1)) =
      ∏ q : {j : ι // j ≠ i}, ((1 - t) * v q) ^ (b q - 1) := by
    apply Finset.prod_congr rfl
    intro q _
    rw [stdSimplexCoordMap_apply_of_ne i q q.property]
  rw [hprod]
  have ht' : 0 ≤ 1 - t := (sub_pos.mpr ht.2).le
  simp_rw [Real.mul_rpow ht' (hv.1 _)]
  rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos (sub_pos.mpr ht.2)]
  ring



/-- The nonnegative Dirichlet monomial integral, used to establish integrability before passing
to the Bochner integral. -/
theorem lintegral_dirichletMonomial_eq_mvRealBeta {b : ι → ℝ}
    (hb : b ∈ mvRealBetaDomain) :
    ∫⁻ u in Convexity.StdSimplex.coordinateSet ℝ ι, ENNReal.ofReal (∏ i, u i ^ (b i - 1)) ∂stdSimplexMeasure =
      ENNReal.ofReal (mvRealBeta b) := by
  classical
  induction hn : Fintype.card ι using Nat.strong_induction_on generalizing ι with
  | h n ih =>
      cases isEmpty_or_nonempty ι with
      | inl hι =>
          let _ := hι
          simp [mvRealBeta, stdSimplexMeasure_empty]
      | inr hι =>
          let _ := hι
          cases subsingleton_or_nontrivial ι with
          | inl hsub =>
              let : Unique ι :=
                ⟨⟨Classical.choice hι⟩, fun a => hsub.elim _ _⟩
              rw [stdSimplexMeasure_unique, MeasureTheory.setLIntegral_dirac]
              have hG : Gamma (b default) ≠ 0 := ne_of_gt (Gamma_pos_of_pos (hb default))
              simp [mvRealBeta, hG, Convexity.StdSimplex.coordinateSet]
          | inr hnontrivial =>
              let _ := hnontrivial
              let i : ι := Classical.choice hι
              let b' : {j : ι // j ≠ i} → ℝ := fun j => b j
              have hb' : b' ∈ mvRealBetaDomain := fun j => hb j
              have hcard : Fintype.card {j : ι // j ≠ i} < n := by
                rw [← hn, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
                exact Nat.sub_one_lt (Fintype.card_pos_iff.mpr hι).ne'
              have hih := ih _ hcard (ι := {j : ι // j ≠ i}) hb'
              rw [lintegral_stdSimplex_split_at i _ (by fun_prop)]
              have hinner : ∀ t ∈ Set.Ico (0 : ℝ) 1,
                  (∫⁻ v in Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i},
                    ENNReal.ofReal
                      (∏ k, stdSimplexCoordMap i (fun q ↦ (1 - t) * v q) k ^
                        (b k - 1)) ∂stdSimplexMeasure) =
                    ENNReal.ofReal
                      (t ^ (b i - 1) *
                        (1 - t) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1))) *
                      ENNReal.ofReal (mvRealBeta b') := by
                intro t ht
                calc
                  _ = ∫⁻ v in Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i},
                      ENNReal.ofReal
                        ((t ^ (b i - 1) *
                          (1 - t) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1))) *
                            ∏ q : {j : ι // j ≠ i}, v q ^ (b q - 1))
                          ∂stdSimplexMeasure := by
                        apply setLIntegral_congr_fun (Convexity.StdSimplex.isClosed_coordinateSet ℝ _).measurableSet
                        intro v hv
                        change ENNReal.ofReal
                          (∏ k, stdSimplexCoordMap i (fun q ↦ (1 - t) * v q) k ^
                            (b k - 1)) = _
                        rw [prod_rpow_stdSimplexCoordMap_scale i b ht hv]
                  _ = ENNReal.ofReal
                        (t ^ (b i - 1) *
                          (1 - t) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1))) *
                      ∫⁻ v in Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i},
                        ENNReal.ofReal (∏ q, v q ^ (b q - 1))
                          ∂stdSimplexMeasure := by
                        rw [← lintegral_const_mul]
                        · apply lintegral_congr
                          intro v
                          rw [← ENNReal.ofReal_mul (mul_nonneg
                            (Real.rpow_nonneg ht.1 _) (Real.rpow_nonneg (sub_nonneg.mpr ht.2.le) _))]
                        · fun_prop
                  _ = _ := by rw [hih rfl]
              have hrest_nonempty : Nonempty {j : ι // j ≠ i} := by
                obtain ⟨j, hji⟩ := exists_ne i
                exact ⟨⟨j, hji⟩⟩
              let c : ℝ := ∑ q : {j : ι // j ≠ i}, b q
              have hc : 0 < c := Finset.sum_pos (fun q _ => hb q) Finset.univ_nonempty
              have houter : ∀ᵐ t ∂volume.restrict (Set.Icc (0 : ℝ) 1),
                  ENNReal.ofReal ((1 - t) ^ (Fintype.card ι - 2)) *
                      (∫⁻ v in Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i},
                        ENNReal.ofReal
                          (∏ k, stdSimplexCoordMap i (fun q ↦ (1 - t) * v q) k ^
                            (b k - 1)) ∂stdSimplexMeasure) =
                    ENNReal.ofReal (t ^ (b i - 1) * (1 - t) ^ (c - 1)) *
                      ENNReal.ofReal (mvRealBeta b') := by
                filter_upwards [ae_restrict_of_ae
                    (Ico_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := 1)),
                  ae_restrict_mem (μ := volume) measurableSet_Icc] with t heq htIcc
                have ht : t ∈ Set.Ico (0 : ℝ) 1 := heq.mpr htIcc
                rw [hinner t ht]
                have hcard_rest : Fintype.card {j : ι // j ≠ i} = Fintype.card ι - 1 := by
                  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
                have hcard_two : 2 ≤ Fintype.card ι := Fintype.one_lt_card
                have hexp : (Fintype.card ι - 2 : ℝ) +
                    (∑ q : {j : ι // j ≠ i}, (b q - 1)) = c - 1 := by
                  have hcast_rest : (Fintype.card {j : ι // j ≠ i} : ℝ) =
                      (Fintype.card ι : ℝ) - 1 := by
                    rw [hcard_rest, Nat.cast_sub (by omega)]
                    norm_num
                  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
                    nsmul_eq_mul, mul_one, c]
                  rw [hcast_rest]
                  ring
                have hcast_d : ((Fintype.card ι - 2 : ℕ) : ℝ) =
                    (Fintype.card ι : ℝ) - 2 := by
                  rw [Nat.cast_sub hcard_two]
                  norm_num
                rw [← mul_assoc,
                  ← ENNReal.ofReal_mul (pow_nonneg (sub_nonneg.mpr ht.2.le) _)]
                congr 1
                apply congrArg ENNReal.ofReal
                calc
                  (1 - t) ^ (Fintype.card ι - 2) *
                      (t ^ (b i - 1) *
                        (1 - t) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1))) =
                      t ^ (b i - 1) *
                        ((1 - t) ^ (Fintype.card ι - 2) *
                          (1 - t) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1))) := by ring
                  _ = t ^ (b i - 1) *
                      (1 - t) ^ ((Fintype.card ι - 2 : ℕ) +
                        (∑ q : {j : ι // j ≠ i}, (b q - 1))) := by
                        rw [← Real.rpow_natCast,
                          ← Real.rpow_add (sub_pos.mpr ht.2)]
                  _ = _ := by rw [hcast_d, hexp]
              rw [lintegral_congr_ae houter]
              simp_rw [mul_comm _ (ENNReal.ofReal (mvRealBeta b'))]
              rw [lintegral_const_mul' (ENNReal.ofReal (mvRealBeta b')) _ ENNReal.ofReal_ne_top]
              rw [← ofReal_integral_eq_lintegral_ofReal
                (integrableOn_Icc_rpow_mul_one_sub_rpow (hb i) hc)]
              · rw [integral_Icc_rpow_mul_one_sub_rpow (hb i) hc]
                rw [mul_comm, ← ENNReal.ofReal_mul (le_of_lt (beta_pos (hb i) hc))]
                congr 1
                dsimp only [mvRealBeta, b', c]
                rw [Fintype.prod_eq_mul_prod_subtype_ne _ i,
                  Fintype.sum_eq_add_sum_subtype_ne b i]
                rw [beta]
                have hGc : Gamma (∑ q : {j : ι // j ≠ i}, b q) ≠ 0 :=
                  ne_of_gt (Gamma_pos_of_pos hc)
                field_simp
              · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with t ht
                exact mul_nonneg (Real.rpow_nonneg ht.1 _)
                  (Real.rpow_nonneg (sub_nonneg.mpr ht.2) _)

/-- The integral representation of `mvRealBeta`. -/
theorem mvRealBeta_eq_integral {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) :
    mvRealBeta b =
      ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, ∏ i, u i ^ (b i - 1) ∂stdSimplexMeasure := by
  symm
  rw [integral_eq_lintegral_of_nonneg_ae]
  · rw [lintegral_dirichletMonomial_eq_mvRealBeta hb]
    apply ENNReal.toReal_ofReal
    cases isEmpty_or_nonempty ι with
    | inl hι =>
        let _ := hι
        simp [mvRealBeta]
    | inr hι =>
        let _ := hι
        exact (mvRealBeta_pos hb).le
  · filter_upwards [ae_restrict_mem (μ := stdSimplexMeasure)
      (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet] with u hu
    exact Finset.prod_nonneg fun j _ => Real.rpow_nonneg (hu.1 j) _
  · let g : (ι → ℝ) → ℝ := fun u =>
      ∏ i, ((ENNReal.ofReal (u i)) ^ (b i - 1)).toReal
    have hg : AEStronglyMeasurable g
        (stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι)) := by
      apply Measurable.aestronglyMeasurable
      dsimp only [g]
      fun_prop
    refine hg.congr ?_
    filter_upwards [ae_restrict_mem (μ := stdSimplexMeasure)
        (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet] with u hu
    apply Finset.prod_congr rfl
    intro i _
    rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (hu.1 i)]

/-- A real Dirichlet monomial is integrable at positive parameters, including when the
index type is empty. This is the shared majorant for complex Dirichlet integrals. -/
theorem integrableOn_mvRealBetaMonomial {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) :
    IntegrableOn (fun u : ι → ℝ ↦ ∏ i, u i ^ (b i - 1))
      (Convexity.StdSimplex.coordinateSet ℝ ι) stdSimplexMeasure := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let _ := hι
      simp [stdSimplexMeasure_empty]
  | inr hι =>
      let _ := hι
      apply Integrable.of_integral_ne_zero
      rw [← mvRealBeta_eq_integral hb]
      exact ne_of_gt (mvRealBeta_pos hb)

end ProbabilityTheory

end
