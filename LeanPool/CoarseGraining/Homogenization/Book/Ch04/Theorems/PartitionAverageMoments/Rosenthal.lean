/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.PartitionAverageFluctuations
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Internal.PartitionAverageMomentHelpers

/-! # Rosenthal -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch04

/-!
# Restriction-local partition-average moment estimates: Rosenthal bounds
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Rosenthal's `L^p` bound on a single scale-color class of descendants under
the restriction-unit-range and restriction-local-random-variable assumptions. -/
theorem integral_abs_finsetSum_pow_rpow_inv_le_rosenthal_uniform_descendantsAtScaleScaleColorClass_of_restrictionUnitRangeDependentLaw
    {d : ℕ} {Q : TriadicCube d} {k : ℤ} {c : ScaleColor d k}
    {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {p : ℕ} {K : ℝ}
    (hP : RestrictionUnitRangeDependentLaw P)
    (hp : 2 ≤ p) (hK_nonneg : 0 ≤ K)
    (X : TriadicCube d → RegCoeffField d → ℝ)
    (hX_local :
      ∀ R ∈ descendantsAtScaleScaleColorClass Q k c,
        IsRestrictionLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) (X R))
    (hX_aemeas :
      ∀ R ∈ descendantsAtScaleScaleColorClass Q k c, AEMeasurable (X R) P)
    (hLp_int :
      ∀ R ∈ descendantsAtScaleScaleColorClass Q k c,
        Integrable (fun a => |X R a| ^ p) P)
    (h_mean :
      ∀ R ∈ descendantsAtScaleScaleColorClass Q k c, ∫ a, X R a ∂P = 0)
    (hK :
      ∀ R ∈ descendantsAtScaleScaleColorClass Q k c,
        (∫ a, |X R a| ^ p ∂P) ^ (1 / (p : ℝ)) ≤ K) :
    (∫ a, |∑ R ∈ descendantsAtScaleScaleColorClass Q k c, X R a| ^ p ∂P) ^
        (1 / (p : ℝ)) ≤
      2 * (p : ℝ) *
          (((descendantsAtScaleScaleColorClass Q k c).card : ℝ) ^ (1 / (p : ℝ)) * K) +
        4 * rosenthalBennettIntegralConst *
          (Real.sqrt p *
            (Real.sqrt ((descendantsAtScaleScaleColorClass Q k c).card : ℝ) * K)) := by
  have hp_nat_ne_zero : p ≠ 0 := by omega
  let S : Finset (TriadicCube d) := descendantsAtScaleScaleColorClass Q k c
  by_cases hS : S.Nonempty
  · let Y : {R : TriadicCube d // R ∈ S} → RegCoeffField d → ℝ :=
      fun R => X R.1
    have h_indep : ProbabilityTheory.iIndepFun Y P := by
      exact iIndepFun_descendantsAtScaleScaleColorClass_of_restrictionUnitRangeDependentLaw
        (Q := Q) (k := k) (c := c) (P := P) hP
        (fun R => hX_local R.1 R.2)
    have hLp_int' :
        ∀ R ∈ S.attach, Integrable (fun a => |Y R a| ^ p) P := by
      intro R _hR
      exact hLp_int R.1 R.2
    have h_mean' : ∀ R ∈ S.attach, ∫ a, Y R a ∂P = 0 := by
      intro R _hR
      exact h_mean R.1 R.2
    have hK' :
        ∀ R ∈ S.attach,
          (∫ a, |Y R a| ^ p ∂P) ^ (1 / (p : ℝ)) ≤ K := by
      intro R _hR
      exact hK R.1 R.2
    have hS_attach : S.attach.Nonempty := by
      simpa using hS
    have hsum_eq :
        (fun a => ∑ R ∈ S.attach, Y R a) =
          fun a => ∑ R ∈ S, X R a := by
      funext a
      simpa [Y] using
        (Finset.sum_attach (s := S) (f := fun R => X R a))
    have hmain :=
      integral_abs_finsetSum_pow_rpow_inv_le_rosenthal_uniform_polynomial_of_iIndepFun_of_integral_eq_zero_aemeasurable
        (μ := P) (X := Y) (s := S.attach) (K := K)
        hS_attach hp hK_nonneg h_indep
        (fun R => hX_aemeas R.1 R.2) hLp_int' h_mean' hK'
    have hleft :
        (∫ ω, |∑ i ∈ S.attach, Y i ω| ^ p ∂P) =
          ∫ a, |∑ R ∈ S, X R a| ^ p ∂P := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun a => by
        have hpoint := congrArg (fun f : RegCoeffField d → ℝ => |f a| ^ p) hsum_eq
        simpa using hpoint
    rw [hleft] at hmain
    simpa [S, rosenthalBennettIntegralConst] using hmain
  · have hS_empty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hleft_zero :
        (∫ a, |∑ R ∈ S, X R a| ^ p ∂P) ^ (1 / (p : ℝ)) = 0 := by
      have hpow_zero : (0 : ℝ) ^ p = 0 := by simp [hp_nat_ne_zero]
      calc
        (∫ a, |∑ R ∈ S, X R a| ^ p ∂P) ^ (1 / (p : ℝ))
            = ((0 : ℝ) ^ p) ^ (1 / (p : ℝ)) := by
                simp [hS_empty]
        _ = 0 := by
              rw [hpow_zero, Real.zero_rpow (by positivity : (1 / (p : ℝ)) ≠ 0)]
    have hrhs_nonneg : 0 ≤
        2 * (p : ℝ) * (0 ^ ((p : ℝ)⁻¹) * K) := by
      refine mul_nonneg ?_ ?_
      · positivity
      · exact mul_nonneg (Real.zero_rpow_nonneg _) hK_nonneg
    rw [hleft_zero]
    simpa [S, hS_empty, one_div] using hrhs_nonneg

private lemma rosenthal_scaleColor_cardinality_bounds
    {d : ℕ} {Q : TriadicCube d} {k : ℤ} {p : ℕ} {K : ℝ}
    (hp : 2 ≤ p) (hK_nonneg : 0 ≤ K) :
    (∑ c ∈ (descendantsAtScale Q k).image (cubeScaleColor k),
      2 * (p : ℝ) *
        (((descendantsAtScaleScaleColorClass Q k c).card : ℝ) ^
          (1 / (p : ℝ)) * K) ≤
      rosenthalDescendantsAtScaleLpConst d k p *
        ((descendantsAtScale Q k).card : ℝ) ^ (1 / (p : ℝ)) * K) ∧
    (∑ c ∈ (descendantsAtScale Q k).image (cubeScaleColor k),
      4 * rosenthalBennettIntegralConst *
        (Real.sqrt p *
          (Real.sqrt ((descendantsAtScaleScaleColorClass Q k c).card : ℝ) * K)) ≤
      rosenthalDescendantsAtScaleSqrtConst d k p *
        Real.sqrt ((descendantsAtScale Q k).card : ℝ) * K) := by
  let s : Finset (ScaleColor d k) := (descendantsAtScale Q k).image (cubeScaleColor k)
  have hsum_card_eq :
      ∑ c ∈ s, ((descendantsAtScaleScaleColorClass Q k c).card : ℝ) =
        ((descendantsAtScale Q k).card : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast (card_descendantsAtScale_eq_sum_card_scaleColorClass_image Q k).symm
  have hs_card_le :
      (s.card : ℝ) ≤ ((((scaleColorPeriod k) ^ d : ℕ) : ℝ)) := by
    exact_mod_cast (card_image_cubeScaleColor_descendantsAtScale_le Q k)
  have hs_card_rpow_le :
      (s.card : ℝ) ^ (1 - 1 / (p : ℝ)) ≤
        ((((scaleColorPeriod k) ^ d : ℕ) : ℝ)) ^ (1 - 1 / (p : ℝ)) := by
    have hexp_nonneg : 0 ≤ 1 - 1 / (p : ℝ) := by
      have hp_one : (1 : ℝ) ≤ p := by
        exact_mod_cast (show 1 ≤ p by omega)
      have hpinv_le_one : 1 / (p : ℝ) ≤ 1 := by
        simpa using (one_div_le_one_div_of_le zero_lt_one hp_one)
      linarith
    exact Real.rpow_le_rpow (by positivity) hs_card_le hexp_nonneg
  have hsqrt_card_le :
      Real.sqrt (s.card : ℝ) ≤ Real.sqrt ((((scaleColorPeriod k) ^ d : ℕ) : ℝ)) := by
    exact Real.sqrt_le_sqrt hs_card_le
  have hsum_rpow_le :
      ∑ c ∈ s, ((descendantsAtScaleScaleColorClass Q k c).card : ℝ) ^
          (1 / (p : ℝ)) ≤
        ((((scaleColorPeriod k) ^ d : ℕ) : ℝ)) ^ (1 - 1 / (p : ℝ)) *
          ((descendantsAtScale Q k).card : ℝ) ^ (1 / (p : ℝ)) := by
    have hbase :=
      sum_rpow_inv_le_card_rpow_mul_rpow_sum
        (s := s) (p := p)
        (f := fun c => ((descendantsAtScaleScaleColorClass Q k c).card : ℝ))
        (show 1 ≤ p by omega)
        (fun c hc => by positivity)
    rw [hsum_card_eq] at hbase
    exact hbase.trans <| mul_le_mul_of_nonneg_right hs_card_rpow_le (by positivity)
  have hsqrt_sum_le :
      ∑ c ∈ s, Real.sqrt ((descendantsAtScaleScaleColorClass Q k c).card : ℝ) ≤
        Real.sqrt ((((scaleColorPeriod k) ^ d : ℕ) : ℝ)) *
          Real.sqrt ((descendantsAtScale Q k).card : ℝ) := by
    have hbase :
        ∑ c ∈ s, Real.sqrt ((descendantsAtScaleScaleColorClass Q k c).card : ℝ) ≤
          Real.sqrt (s.card : ℝ) *
            Real.sqrt ((descendantsAtScale Q k).card : ℝ) := by
      simpa [hsum_card_eq] using
        (Real.sum_sqrt_mul_sqrt_le
          (s := s)
          (f := fun _ => (1 : ℝ))
          (g := fun c => ((descendantsAtScaleScaleColorClass Q k c).card : ℝ))
          (hf := by intro c; positivity)
          (hg := by intro c; positivity))
    exact hbase.trans <|
      mul_le_mul_of_nonneg_right hsqrt_card_le (by positivity)
  have hA_sum :
      ∑ c ∈ s,
        2 * (p : ℝ) *
          (((descendantsAtScaleScaleColorClass Q k c).card : ℝ) ^
            (1 / (p : ℝ)) * K) ≤
        rosenthalDescendantsAtScaleLpConst d k p *
          ((descendantsAtScale Q k).card : ℝ) ^ (1 / (p : ℝ)) * K := by
    calc
      ∑ c ∈ s,
          2 * (p : ℝ) *
            (((descendantsAtScaleScaleColorClass Q k c).card : ℝ) ^
              (1 / (p : ℝ)) * K)
          = (2 * (p : ℝ) * K) *
              ∑ c ∈ s, ((descendantsAtScaleScaleColorClass Q k c).card : ℝ) ^
                (1 / (p : ℝ)) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl ?_
                intro c hc
                ring
      _ ≤ 2 * (p : ℝ) *
            ((((scaleColorPeriod k) ^ d : ℕ) : ℝ) ^ (1 - 1 / (p : ℝ)) *
              ((descendantsAtScale Q k).card : ℝ) ^ (1 / (p : ℝ)) * K) := by
              have hconst_nonneg : 0 ≤ 2 * (p : ℝ) * K := by positivity
              have hmul := mul_le_mul_of_nonneg_left hsum_rpow_le hconst_nonneg
              simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      _ = rosenthalDescendantsAtScaleLpConst d k p *
            ((descendantsAtScale Q k).card : ℝ) ^ (1 / (p : ℝ)) * K := by
              simp [rosenthalDescendantsAtScaleLpConst]
              ring
  have hB_sum :
      ∑ c ∈ s,
        4 * rosenthalBennettIntegralConst *
          (Real.sqrt p *
            (Real.sqrt ((descendantsAtScaleScaleColorClass Q k c).card : ℝ) * K)) ≤
        rosenthalDescendantsAtScaleSqrtConst d k p *
          Real.sqrt ((descendantsAtScale Q k).card : ℝ) * K := by
    have hRB_nonneg : 0 ≤ rosenthalBennettIntegralConst := by
      dsimp [rosenthalBennettIntegralConst, IndependentSums.rosenthalBennettIntegralConst]
      positivity
    calc
      ∑ c ∈ s,
          4 * rosenthalBennettIntegralConst *
            (Real.sqrt p *
              (Real.sqrt ((descendantsAtScaleScaleColorClass Q k c).card : ℝ) * K))
          = (4 * rosenthalBennettIntegralConst * Real.sqrt p * K) *
              ∑ c ∈ s,
                Real.sqrt ((descendantsAtScaleScaleColorClass Q k c).card : ℝ) := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl ?_
                  intro c hc
                  ring
      _ ≤ 4 * rosenthalBennettIntegralConst *
            (Real.sqrt p *
              ((Real.sqrt ((((scaleColorPeriod k) ^ d : ℕ) : ℝ)) *
                Real.sqrt ((descendantsAtScale Q k).card : ℝ)) * K)) := by
              have hconst_nonneg :
                  0 ≤ 4 * rosenthalBennettIntegralConst * Real.sqrt p * K := by
                have htmp : 0 ≤ 4 * rosenthalBennettIntegralConst * Real.sqrt p := by
                  exact mul_nonneg (mul_nonneg (by positivity) hRB_nonneg) (by positivity)
                exact mul_nonneg htmp hK_nonneg
              have hmul := mul_le_mul_of_nonneg_left hsqrt_sum_le hconst_nonneg
              simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      _ = rosenthalDescendantsAtScaleSqrtConst d k p *
            Real.sqrt ((descendantsAtScale Q k).card : ℝ) * K := by
              simp [rosenthalDescendantsAtScaleSqrtConst]
              ring
  exact ⟨hA_sum, hB_sum⟩

/-- Rosenthal's `L^p` bound for sums over all descendants at a fixed scale,
using the restriction-local and restriction-unit-range interfaces. -/
theorem integral_abs_finsetSum_pow_rpow_inv_le_rosenthal_uniform_descendantsAtScale_of_restrictionUnitRangeDependentLaw
    {d : ℕ} {Q : TriadicCube d} {k : ℤ}
    {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {p : ℕ} {K : ℝ}
    (hP : RestrictionUnitRangeDependentLaw P)
    (hp : 2 ≤ p) (hK_nonneg : 0 ≤ K)
    (X : TriadicCube d → RegCoeffField d → ℝ)
    (hX_local :
      ∀ R ∈ descendantsAtScale Q k, IsRestrictionLocalRandomVariable (cubeSet R) (measurableSet_cubeSet R) (X R))
    (hX_aemeas : ∀ R ∈ descendantsAtScale Q k, AEMeasurable (X R) P)
    (hLp_int :
      ∀ R ∈ descendantsAtScale Q k, Integrable (fun a => |X R a| ^ p) P)
    (h_mean :
      ∀ R ∈ descendantsAtScale Q k, ∫ a, X R a ∂P = 0)
    (hK :
      ∀ R ∈ descendantsAtScale Q k,
        (∫ a, |X R a| ^ p ∂P) ^ (1 / (p : ℝ)) ≤ K) :
    (∫ a, |∑ R ∈ descendantsAtScale Q k, X R a| ^ p ∂P) ^ (1 / (p : ℝ)) ≤
      rosenthalDescendantsAtScaleLpConst d k p *
          ((descendantsAtScale Q k).card : ℝ) ^ (1 / (p : ℝ)) * K +
        rosenthalDescendantsAtScaleSqrtConst d k p *
          Real.sqrt ((descendantsAtScale Q k).card : ℝ) * K := by
  have hp_nat_ne_zero : p ≠ 0 := by omega
  have hp_ennreal_ne_zero : (p : ENNReal) ≠ 0 := by
    simpa using hp_nat_ne_zero
  have hp_ennreal_top : (p : ENNReal) ≠ ⊤ := by simp
  let s : Finset (ScaleColor d k) := (descendantsAtScale Q k).image (cubeScaleColor k)
  by_cases hs : s.Nonempty
  · let Y : ScaleColor d k → RegCoeffField d → ℝ :=
      fun c a => ∑ R ∈ descendantsAtScaleScaleColorClass Q k c, X R a
    have h_aemeas : ∀ c ∈ s, AEMeasurable (Y c) P := by
      intro c hc
      have hsum : AEMeasurable
          (∑ R ∈ descendantsAtScaleScaleColorClass Q k c, X R) P :=
        Finset.aemeasurable_sum _ fun R hR =>
        hX_aemeas R (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1
      convert hsum using 1
      ext a
      simp [Y]
    have hLp_int_color :
        ∀ c ∈ s, Integrable (fun a => |Y c a| ^ p) P := by
      intro c hc
      have h_attach_int :
          ∀ R ∈ (descendantsAtScaleScaleColorClass Q k c).attach,
            Integrable (fun a => |X R.1 a| ^ p) P := by
        intro R _hR
        exact hLp_int R.1 (mem_descendantsAtScaleScaleColorClass_iff.mp R.2).1
      have h_sum :=
        memLp_finsetSum
          ((descendantsAtScaleScaleColorClass Q k c).attach)
          (fun R hR =>
            (integrable_norm_rpow_iff
              ((hX_aemeas R.1
                (mem_descendantsAtScaleScaleColorClass_iff.mp R.2).1).aestronglyMeasurable)
              hp_ennreal_ne_zero hp_ennreal_top).1
                (by simpa [Real.norm_eq_abs] using h_attach_int R hR))
      have h_sum_int :
          Integrable
            (fun a =>
              |∑ R ∈ (descendantsAtScaleScaleColorClass Q k c).attach, X R.1 a| ^ p) P := by
        simpa [Real.norm_eq_abs] using h_sum.integrable_norm_pow
          (Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le zero_lt_one (show 1 ≤ p by omega)))
      have hsum_eq_attach :
          (fun a => ∑ R ∈ (descendantsAtScaleScaleColorClass Q k c).attach, X R.1 a) =
            Y c := by
        funext a
        simpa [Y] using
          (Finset.sum_attach (s := descendantsAtScaleScaleColorClass Q k c)
            (f := fun R => X R a))
      have hpow_eq :
          (fun a => |Y c a| ^ p) =
            (fun a => |∑ R ∈ (descendantsAtScaleScaleColorClass Q k c).attach,
              X R.1 a| ^ p) := by
        funext a
        rw [← hsum_eq_attach]
      rw [hpow_eq]
      exact h_sum_int
    have hY :
        ∀ c ∈ s,
          (∫ a, |Y c a| ^ p ∂P) ^ (1 / (p : ℝ)) ≤
            2 * (p : ℝ) *
                (((descendantsAtScaleScaleColorClass Q k c).card : ℝ) ^
                  (1 / (p : ℝ)) * K) +
              4 * rosenthalBennettIntegralConst *
                (Real.sqrt p *
                  (Real.sqrt ((descendantsAtScaleScaleColorClass Q k c).card : ℝ) * K)) := by
      intro c hc
      exact
        integral_abs_finsetSum_pow_rpow_inv_le_rosenthal_uniform_descendantsAtScaleScaleColorClass_of_restrictionUnitRangeDependentLaw
          (d := d) (Q := Q) (k := k) (c := c) hP hp hK_nonneg X
          (fun R hR => hX_local R (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1)
          (fun R hR => hX_aemeas R (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1)
          (fun R hR => hLp_int R (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1)
          (fun R hR => h_mean R (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1)
          (fun R hR => hK R (mem_descendantsAtScaleScaleColorClass_iff.mp hR).1)
    have hsum :
        (∫ a, |∑ c ∈ s, Y c a| ^ p ∂P) ^ (1 / (p : ℝ)) ≤
          ∑ c ∈ s, (∫ a, |Y c a| ^ p ∂P) ^ (1 / (p : ℝ)) := by
      exact _root_.Homogenization.integral_abs_finsetSum_pow_rpow_inv_le_sum_aemeasurable
        (μ := P) (show 1 ≤ p by omega) h_aemeas hLp_int_color
    have hsum_eq :
        (fun a => ∑ c ∈ s, Y c a) =
          fun a => ∑ R ∈ descendantsAtScale Q k, X R a := by
      funext a
      calc
        ∑ c ∈ s, Y c a =
            ∑ c ∈ s, ∑ i ∈ descendantsAtScaleScaleColorClass Q k c, X i a := by
              refine Finset.sum_congr rfl ?_
              intro c hc
              simp [Y]
        _ =
            ∑ i ∈ s.biUnion (descendantsAtScaleScaleColorClass Q k), X i a := by
              symm
              exact Finset.sum_biUnion (by
                intro c hc c' hc' hneq
                exact disjoint_descendantsAtScaleScaleColorClass_of_ne Q k hneq)
        _ = ∑ i ∈ descendantsAtScale Q k, X i a := by
              rw [descendantsAtScale_eq_biUnion_image_cubeScaleColor Q k]
    obtain ⟨hA_sum, hB_sum⟩ :=
      rosenthal_scaleColor_cardinality_bounds (Q := Q) (k := k) hp hK_nonneg
    calc
      (∫ a, |∑ R ∈ descendantsAtScale Q k, X R a| ^ p ∂P) ^ (1 / (p : ℝ))
          = (∫ a, |∑ c ∈ s, Y c a| ^ p ∂P) ^ (1 / (p : ℝ)) := by
              congr 1
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun a => by
                have hpoint := congrArg (fun f : RegCoeffField d → ℝ => |f a| ^ p) hsum_eq
                simpa using hpoint.symm
      _ ≤ ∑ c ∈ s, (∫ a, |Y c a| ^ p ∂P) ^ (1 / (p : ℝ)) := hsum
      _ ≤ ∑ c ∈ s,
            (2 * (p : ℝ) *
                (((descendantsAtScaleScaleColorClass Q k c).card : ℝ) ^
                  (1 / (p : ℝ)) * K) +
              4 * rosenthalBennettIntegralConst *
                (Real.sqrt p *
                  (Real.sqrt ((descendantsAtScaleScaleColorClass Q k c).card : ℝ) * K))) := by
              exact Finset.sum_le_sum fun c hc => hY c hc
      _ = (∑ c ∈ s,
            2 * (p : ℝ) *
              (((descendantsAtScaleScaleColorClass Q k c).card : ℝ) ^
                (1 / (p : ℝ)) * K)) +
            (∑ c ∈ s,
              4 * rosenthalBennettIntegralConst *
                (Real.sqrt p *
                  (Real.sqrt ((descendantsAtScaleScaleColorClass Q k c).card : ℝ) * K))) := by
              rw [Finset.sum_add_distrib]
      _ ≤ rosenthalDescendantsAtScaleLpConst d k p *
              ((descendantsAtScale Q k).card : ℝ) ^ (1 / (p : ℝ)) * K +
            rosenthalDescendantsAtScaleSqrtConst d k p *
              Real.sqrt ((descendantsAtScale Q k).card : ℝ) * K := by
              exact add_le_add hA_sum hB_sum
  · have hs_empty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have hdesc_empty : descendantsAtScale Q k = ∅ := by
      calc
        descendantsAtScale Q k =
            s.biUnion (descendantsAtScaleScaleColorClass Q k) := by
              rw [show s = (descendantsAtScale Q k).image (cubeScaleColor k) by rfl]
              symm
              exact descendantsAtScale_eq_biUnion_image_cubeScaleColor Q k
        _ = ∅ := by
              simp [hs_empty]
    have hleft_zero :
        (∫ a, |∑ R ∈ descendantsAtScale Q k, X R a| ^ p ∂P) ^ (1 / (p : ℝ)) = 0 := by
      have hpow_zero : (0 : ℝ) ^ p = 0 := by simp [hp_nat_ne_zero]
      calc
        (∫ a, |∑ R ∈ descendantsAtScale Q k, X R a| ^ p ∂P) ^ (1 / (p : ℝ))
            = ((0 : ℝ) ^ p) ^ (1 / (p : ℝ)) := by
                simp [hdesc_empty]
        _ = 0 := by
              rw [hpow_zero, Real.zero_rpow (by positivity : (1 / (p : ℝ)) ≠ 0)]
    have hconst_nonneg : 0 ≤ rosenthalDescendantsAtScaleLpConst d k p := by
      simp [rosenthalDescendantsAtScaleLpConst]
      positivity
    have hrhs_nonneg :
        0 ≤ rosenthalDescendantsAtScaleLpConst d k p * 0 ^ ((p : ℝ)⁻¹) * K := by
      exact mul_nonneg (mul_nonneg hconst_nonneg (Real.zero_rpow_nonneg _)) hK_nonneg
    rw [hleft_zero]
    simpa [hdesc_empty, one_div] using hrhs_nonneg

end

end Ch04
end Book
end Homogenization
