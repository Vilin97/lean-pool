/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Integral.Real
public import LeanPool.CarlsonFunctions.Dirichlet.Beta.Complex

/-!
# Absolutely convergent complex Dirichlet monomial integrals

Real monomial integrability supplies the majorants for the complex beta integral and its
logarithmic moments. This module imports neither the Dirichlet probability measure nor
several-complex-variable analyticity or continuation.
-/

open Complex Fintype Filter MeasureTheory MeasureTheory.Measure
open scoped Topology Classical

@[expose] public noncomputable section

namespace Complex

variable {ι : Type*} [Fintype ι]

/-- The complex Dirichlet monomial is integrable on the simplex whenever every parameter
has positive real part. -/
theorem integrableOn_mvBetaMonomial
    (b : ι → ℂ) (hb : b ∈ mvBetaConvergent) :
    IntegrableOn (fun u : ι → ℝ ↦ ∏ i, (u i : ℂ) ^ (b i - 1))
      (Convexity.StdSimplex.coordinateSet ℝ ι) stdSimplexMeasure := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let _ := hι
      simp [stdSimplexMeasure_empty]
  | inr hι =>
      let _ := hι
      let a : ι → ℝ := fun i ↦ (b i).re
      have ha : a ∈ ProbabilityTheory.mvRealBetaDomain := fun i => hb i
      have hreal : IntegrableOn (fun u : ι → ℝ ↦ ∏ i, u i ^ (a i - 1))
          (Convexity.StdSimplex.coordinateSet ℝ ι) stdSimplexMeasure :=
        ProbabilityTheory.integrableOn_mvRealBetaMonomial ha
      let P : Set (ι → ℝ) := {u | ∀ i, 0 < u i}
      have hPopen : IsOpen P := by
        rw [show P = ⋂ i, {u : ι → ℝ | 0 < u i} by ext u; simp [P]]
        exact isOpen_iInter_of_finite fun i ↦
          isOpen_lt continuous_const (continuous_apply i)
      have hrealP := hreal.mono_set (Set.inter_subset_left :
        Convexity.StdSimplex.coordinateSet ℝ ι ∩ P ⊆ Convexity.StdSimplex.coordinateSet ℝ ι)
      have hcomplexP : IntegrableOn (fun u : ι → ℝ ↦ ∏ i, (u i : ℂ) ^ (b i - 1))
          (Convexity.StdSimplex.coordinateSet ℝ ι ∩ P) stdSimplexMeasure := by
        apply Integrable.mono hrealP
        · apply ContinuousOn.aestronglyMeasurable
          · apply continuousOn_finsetProd
            intro i _
            exact (Complex.continuous_ofReal.comp (continuous_apply i)).continuousOn.cpow_const
              (fun _ hu ↦ ofReal_mem_slitPlane.2 (hu.2 i))
          · exact (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet.inter hPopen.measurableSet
        · filter_upwards [self_mem_ae_restrict (μ := stdSimplexMeasure)
              ((Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet.inter hPopen.measurableSet)] with u hu
          simp only [Set.mem_inter_iff] at hu
          simp only [norm_prod]
          apply le_of_eq
          apply Finset.prod_congr rfl
          intro i _
          rw [norm_cpow_eq_rpow_re_of_pos (hu.2 i)]
          simp [a, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (hu.2 i) _)]
      apply hcomplexP.congr_set_ae
      have hae : ∀ᵐ u ∂stdSimplexMeasure,
          u ∈ Convexity.StdSimplex.coordinateSet ℝ ι → ∀ i, 0 < u i :=
        (ae_restrict_iff' (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet).mp
          (ae_zero_lt_of_mem_stdSimplex (ι := ι))
      filter_upwards [hae] with u hu
      apply propext
      constructor
      · intro hus
        exact ⟨hus, hu hus⟩
      · exact fun hus ↦ hus.1

/-- Multiplying one factor of a convergent Dirichlet monomial by the logarithm of its
coordinate preserves integrability.  This is the basic domination estimate needed when
differentiating a simplex Mellin integral with respect to a parameter. -/
theorem integrableOn_mvBetaMonomial_mul_log
    (b : ι → ℂ) (hb : b ∈ mvBetaConvergent) (i : ι) :
    IntegrableOn
      (fun u : ι → ℝ ↦
        (∏ j, (u j : ℂ) ^ (b j - 1)) * Complex.log (u i : ℂ))
      (Convexity.StdSimplex.coordinateSet ℝ ι) stdSimplexMeasure := by
  let _ : Nonempty ι := ⟨i⟩
  let δ : ℝ := (b i).re / 2
  have hδ : 0 < δ := half_pos (hb i)
  let b' : ι → ℂ := fun j ↦ b j - if j = i then δ else 0
  have hb' : b' ∈ mvBetaConvergent := by
    intro j
    by_cases hji : j = i
    · subst j
      simp [b', δ]
      linarith [hb i]
    · simpa [b', hji] using hb j
  have hdom := (integrableOn_mvBetaMonomial b' hb').norm.const_mul (1 / δ)
  apply Integrable.mono hdom
  · have hmono := (integrableOn_mvBetaMonomial b hb).aestronglyMeasurable
    have hlog : AEStronglyMeasurable
        (fun u : ι → ℝ ↦ Complex.log (u i : ℂ))
        (stdSimplexMeasure.restrict (Convexity.StdSimplex.coordinateSet ℝ ι)) := by
      exact (Complex.measurable_log.comp
        (Complex.measurable_ofReal.comp (measurable_pi_apply i))).aestronglyMeasurable
    exact hmono.mul hlog
  · have hpos := ae_zero_lt_of_mem_stdSimplex (ι := ι)
    filter_upwards [self_mem_ae_restrict (s := Convexity.StdSimplex.coordinateSet ℝ ι)
        (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet, hpos] with u hu hupos
    have hui : 0 < u i := hupos i
    have hui1 : u i ≤ 1 := (hu.2.symm ▸ Finset.single_le_sum (fun j _ ↦ hu.1 j) (Finset.mem_univ i))
    simp only [norm_mul, norm_prod]
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i,
      Fintype.prod_eq_mul_prod_subtype_ne _ i]
    have hnorm (j : ι) :
        ‖(u j : ℂ) ^ (b j - 1)‖ = u j ^ ((b j).re - 1) := by
      rw [norm_cpow_eq_rpow_re_of_pos (hupos j)]
      simp
    have hnorm' (j : ι) :
        ‖(u j : ℂ) ^ (b' j - 1)‖ = u j ^ ((b' j).re - 1) := by
      rw [norm_cpow_eq_rpow_re_of_pos (hupos j)]
      simp
    rw [hnorm i, hnorm' i]
    simp_rw [hnorm, hnorm']
    have hrest :
        (∏ j : {j : ι // j ≠ i}, u j ^ ((b j).re - 1)) =
          ∏ j : {j : ι // j ≠ i}, u j ^ ((b' j).re - 1) := by
      apply Finset.prod_congr rfl
      intro j _
      simp [b', j.property]
    rw [hrest]
    rw [← Complex.ofReal_log hui.le]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    have hlog := Real.abs_log_mul_self_rpow_lt (u i) δ hui hui1 hδ
    have hpow : u i ^ ((b i).re - 1) =
        u i ^ (((b i).re - δ - 1) + δ) := by
      congr 1
      ring
    rw [hpow, Real.rpow_add hui]
    have hbi' : (b' i).re - 1 = (b i).re - δ - 1 := by simp [b']
    rw [hbi']
    rw [abs_of_pos (one_div_pos.mpr hδ)]
    simp_rw [abs_of_pos (Real.rpow_pos_of_pos (hupos _) _)]
    have hnonneg : 0 ≤ u i ^ ((b i).re - δ - 1) *
        ∏ j : {j : ι // j ≠ i}, u j ^ ((b' j).re - 1) :=
      mul_nonneg (Real.rpow_nonneg (hu.1 i) _)
        (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hu.1 j) _)
    calc
      (u i ^ ((b i).re - δ - 1) * u i ^ δ) *
          (∏ j : {j : ι // j ≠ i}, u j ^ ((b' j).re - 1)) * |Real.log (u i)| =
          (u i ^ δ * |Real.log (u i)|) *
            (u i ^ ((b i).re - δ - 1) *
              ∏ j : {j : ι // j ≠ i}, u j ^ ((b' j).re - 1)) := by ring
      _ ≤ (1 / δ) *
            (u i ^ ((b i).re - δ - 1) *
              ∏ j : {j : ι // j ≠ i}, u j ^ ((b' j).re - 1)) := by
        gcongr
        simpa [abs_mul, mul_comm,
          abs_of_pos (Real.rpow_pos_of_pos hui _)] using hlog.le

/-- A simplex slice separates a complex Dirichlet monomial into its distinguished-coordinate,
radial, and lower-dimensional factors. -/
theorem prod_cpow_stdSimplexCoordMap_scale
    (i : ι) (b : ι → ℂ) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1)
    {v : {j : ι // j ≠ i} → ℝ} (hv : v ∈ Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i}) :
    (∏ j, ((stdSimplexCoordMap i (fun q ↦ (1 - t) * v q) j : ℝ) : ℂ) ^ (b j - 1)) =
      (t : ℂ) ^ (b i - 1) *
        (1 - t : ℂ) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1)) *
          ∏ q : {j : ι // j ≠ i}, (v q : ℂ) ^ (b q - 1) := by
  classical
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
  have hsum : ∑ q, (1 - t) * v q = 1 - t := by
    rw [← Finset.mul_sum, hv.2, mul_one]
  rw [stdSimplexCoordMap_apply_self, hsum]
  have hone : 1 - (1 - t) = t := by ring
  rw [hone]
  have hprod :
      (∏ q : {j : ι // j ≠ i},
        ((stdSimplexCoordMap i (fun q ↦ (1 - t) * v q) q : ℝ) : ℂ) ^ (b q - 1)) =
      ∏ q : {j : ι // j ≠ i},
        (((1 - t : ℝ) : ℂ) * (v q : ℂ)) ^ (b q - 1) := by
    apply Finset.prod_congr rfl
    intro q _
    rw [stdSimplexCoordMap_apply_of_ne i q q.property, Complex.ofReal_mul]
  rw [hprod]
  have ht' : 0 ≤ 1 - t := (sub_pos.mpr ht.2).le
  simp_rw [Complex.mul_cpow_ofReal_nonneg ht' (hv.1 _)]
  rw [Finset.prod_mul_distrib]
  have hbase : ((1 - t : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr ht.2.ne')
  have hpow : (∏ q : {j : ι // j ≠ i}, ((1 - t : ℝ) : ℂ) ^ (b q - 1)) =
      ((1 - t : ℝ) : ℂ) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1)) := by
    induction (Finset.univ : Finset {j : ι // j ≠ i}) using Finset.induction_on with
    | empty => simp
    | @insert q s hqs ih =>
        rw [Finset.prod_insert hqs, Finset.sum_insert hqs, Complex.cpow_add _ _ hbase, ih]
  rw [hpow]
  push_cast
  ring

/-- The absolutely convergent simplex integral representation of the multivariate Beta
function. -/
theorem mvBeta_eq_integral {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    mvBeta b = ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, ∏ i, (u i : ℂ) ^ (b i - 1) ∂stdSimplexMeasure := by
  classical
  induction hn : Fintype.card ι using Nat.strong_induction_on generalizing ι with
  | h n ih =>
      cases isEmpty_or_nonempty ι with
      | inl hι =>
          let _ := hι
          simp [mvBeta, stdSimplexMeasure_empty]
      | inr hι =>
          let _ := hι
          cases subsingleton_or_nontrivial ι with
          | inl hsub =>
              let : Unique ι :=
                ⟨⟨Classical.choice hι⟩, fun a => hsub.elim _ _⟩
              rw [mvBeta, stdSimplexMeasure_unique, MeasureTheory.setIntegral_dirac]
              have hG : Gamma (b default) ≠ 0 := Gamma_ne_zero_of_re_pos (hb default)
              simp [hG, Convexity.StdSimplex.coordinateSet]
          | inr hnontrivial =>
              let _ := hnontrivial
              let i : ι := Classical.choice hι
              let b' : {j : ι // j ≠ i} → ℂ := fun j => b j
              have hb' : b' ∈ mvBetaConvergent := fun j => hb j
              have hcard : Fintype.card {j : ι // j ≠ i} < n := by
                rw [← hn, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
                exact Nat.sub_one_lt (Fintype.card_pos_iff.mpr hι).ne'
              have hih := ih _ hcard (ι := {j : ι // j ≠ i}) hb'
              rw [integral_stdSimplex_split_at i _ (integrableOn_mvBetaMonomial b hb)]
              let c : ℂ := ∑ q : {j : ι // j ≠ i}, b q
              have hrest_nonempty : Nonempty {j : ι // j ≠ i} := by
                obtain ⟨j, hji⟩ := exists_ne i
                exact ⟨⟨j, hji⟩⟩
              have hc : 0 < c.re := by
                dsimp only [c]
                change 0 < Complex.reCLM (∑ q : {j : ι // j ≠ i}, b q)
                rw [map_sum Complex.reCLM b' Finset.univ]
                exact Finset.sum_pos (fun q _ => hb q) Finset.univ_nonempty
              have hinner : ∀ t ∈ Set.Ico (0 : ℝ) 1,
                  (∫ v in Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i},
                    ∏ k, ((stdSimplexCoordMap i (fun q ↦ (1 - t) * v q) k : ℝ) : ℂ) ^
                      (b k - 1) ∂stdSimplexMeasure) =
                    (t : ℂ) ^ (b i - 1) *
                      (1 - t : ℂ) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1)) * mvBeta b' := by
                intro t ht
                calc
                  _ = ∫ v in Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i},
                      ((t : ℂ) ^ (b i - 1) *
                        (1 - t : ℂ) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1))) *
                        ∏ q, (v q : ℂ) ^ (b q - 1) ∂stdSimplexMeasure := by
                          apply setIntegral_congr_fun (Convexity.StdSimplex.isClosed_coordinateSet ℝ _).measurableSet
                          intro v hv
                          exact prod_cpow_stdSimplexCoordMap_scale i b ht hv
                  _ = ((t : ℂ) ^ (b i - 1) *
                        (1 - t : ℂ) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1))) *
                      ∫ v in Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i},
                        ∏ q, (v q : ℂ) ^ (b q - 1) ∂stdSimplexMeasure := by
                          rw [MeasureTheory.integral_const_mul]
                  _ = _ := by rw [← hih rfl]
              have hcard_rest : Fintype.card {j : ι // j ≠ i} = Fintype.card ι - 1 := by
                rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
              have hcard_two : 2 ≤ Fintype.card ι := Fintype.one_lt_card
              have hexp : ((Fintype.card ι - 2 : ℕ) : ℂ) +
                  (∑ q : {j : ι // j ≠ i}, (b q - 1)) = c - 1 := by
                have hcast_rest : (Fintype.card {j : ι // j ≠ i} : ℂ) =
                    (Fintype.card ι : ℂ) - 1 := by
                  rw [hcard_rest, Nat.cast_sub (by omega)]
                  norm_num
                have hcast_two : ((Fintype.card ι - 2 : ℕ) : ℂ) =
                    (Fintype.card ι : ℂ) - 2 := by
                  rw [Nat.cast_sub hcard_two]
                  norm_num
                simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
                  nsmul_eq_mul, mul_one, c]
                rw [hcast_rest, hcast_two]
                ring
              have houter : ∀ᵐ t ∂volume.restrict (Set.Icc (0 : ℝ) 1),
                  ((1 - t) ^ (Fintype.card ι - 2)) •
                      (∫ v in Convexity.StdSimplex.coordinateSet ℝ {j : ι // j ≠ i},
                        ∏ k, ((stdSimplexCoordMap i
                          (fun q ↦ (1 - t) * v q) k : ℝ) : ℂ) ^ (b k - 1)
                          ∂stdSimplexMeasure) =
                    ((t : ℂ) ^ (b i - 1) * (1 - t : ℂ) ^ (c - 1)) * mvBeta b' := by
                filter_upwards [ae_restrict_of_ae
                    (Ico_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := 1)),
                  ae_restrict_mem (μ := volume) measurableSet_Icc] with t heq htIcc
                have ht : t ∈ Set.Ico (0 : ℝ) 1 := heq.mpr htIcc
                rw [hinner t ht]
                have hbase : ((1 - t : ℝ) : ℂ) ≠ 0 :=
                  Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr ht.2.ne')
                have hbase' : (1 - (t : ℂ)) ≠ 0 := by
                  intro hz
                  apply ht.2.ne
                  exact_mod_cast (sub_eq_zero.mp hz).symm
                rw [Complex.real_smul, Complex.ofReal_pow, ← Complex.cpow_natCast]
                push_cast
                calc
                  ((1 - t : ℂ) ^ ((Fintype.card ι - 2 : ℕ) : ℂ) *
                      (((t : ℂ) ^ (b i - 1) *
                        (1 - t : ℂ) ^ (∑ q : {j : ι // j ≠ i}, (b q - 1))) *
                          mvBeta b')) =
                      (t : ℂ) ^ (b i - 1) *
                        ((1 - t : ℂ) ^ ((Fintype.card ι - 2 : ℕ) : ℂ) *
                          (1 - t : ℂ) ^
                            (∑ q : {j : ι // j ≠ i}, (b q - 1))) * mvBeta b' := by ring
                  _ = _ := by
                    rw [← Complex.cpow_add _ _ hbase', hexp]
              rw [integral_congr_ae houter]
              rw [integral_mul_const]
              have hbeta :
                  (∫ t in Set.Icc (0 : ℝ) 1,
                    (t : ℂ) ^ (b i - 1) * (1 - t : ℂ) ^ (c - 1)) =
                    betaIntegral (b i) c := by
                rw [betaIntegral, intervalIntegral.integral_of_le zero_le_one,
                  integral_Icc_eq_integral_Ioc]
              rw [hbeta, betaIntegral_eq_Gamma_mul_div _ _ (hb i) hc]
              have hGc : Gamma c ≠ 0 := Gamma_ne_zero_of_re_pos hc
              have hGsum : Gamma (b i + c) ≠ 0 :=
                Gamma_ne_zero_of_re_pos (by simpa using add_pos (hb i) hc)
              have hGc' : Gamma (∑ q : {j : ι // j ≠ i}, b q) ≠ 0 := by
                simpa [c] using hGc
              have hGsum' : Gamma (b i + ∑ q : {j : ι // j ≠ i}, b q) ≠ 0 := by
                simpa [c] using hGsum
              dsimp only [mvBeta, b', c]
              rw [Fintype.prod_eq_mul_prod_subtype_ne _ i,
                Fintype.sum_eq_add_sum_subtype_ne b i]
              field_simp [hGc', hGsum']

end Complex

end
