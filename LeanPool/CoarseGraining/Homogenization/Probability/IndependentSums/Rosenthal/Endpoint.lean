/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.Rosenthal.ProductDifference

/-! # Endpoint -/

@[expose] public section

namespace Homogenization
namespace IndependentSums

open MeasureTheory ProbabilityTheory
open Set
open scoped Topology

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- Rosenthal bound for the symmetrized difference sum on the product
probability space. -/
theorem integral_abs_symmetrizedFinsetSum_pow_le_rosenthal
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p : ℕ}
    (hp : 2 ≤ p)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_sq_int : ∀ i ∈ s, Integrable (fun ω => X i ω ^ (2 : ℕ)) μ)
    (hmax_int : Integrable (fun ω => (s.sup' hs (fun i => |X i ω|)) ^ p) μ) :
    ∫ ω : Ω × Ω, |symmetrizedFinsetSum X s ω| ^ p ∂(μ.prod μ) ≤
      ((p : ℝ) ^ p * (2 : ℝ) ^ p) * ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ +
        2 *
          (2 * rosenthalBennettIntegralConst *
            (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ))) ^ p := by
  classical
  let : Nonempty ↥s := ⟨⟨hs.choose, hs.choose_spec⟩⟩
  let Y : ↥s → Ω × Ω → ℝ := fun i ω => X i ω.1 - X i ω.2
  have hs_univ : (Finset.univ : Finset ↥s).Nonempty := Finset.univ_nonempty
  have hp_real : 2 ≤ (p : ℝ) := by exact_mod_cast hp
  have hp_one : 1 ≤ p := by omega
  have h_indep_sub : iIndepFun (fun i : ↥s => X i) μ := by
    simpa using h_indep.precomp (g := ((↑) : ↥s → ι)) Subtype.val_injective
  have h_meas_sub : ∀ i : ↥s, Measurable (X i) := by
    intro i
    exact h_meas i
  have h_indepY : iIndepFun Y (μ.prod μ) := by
    simpa [Y] using
      iIndepFun_sub_comp_fst_comp_snd_prod
        (μ := μ) (X := fun i : ↥s => X i) h_indep_sub h_meas_sub
  have h_sq_intY :
      ∀ i ∈ (Finset.univ : Finset ↥s),
        Integrable (fun ω => Y i ω ^ (2 : ℕ)) (μ.prod μ) := by
    intro i hi
    simpa [Y] using integrable_pow_two_sub_comp_fst_comp_snd
      (μ := μ) (h_meas i) (h_sq_int i i.property)
  have h_symmY :
      ∀ i ∈ (Finset.univ : Finset ↥s),
        IdentDistrib (Y i) (fun ω => -Y i ω) (μ.prod μ) (μ.prod μ) := by
    intro i hi
    simpa [Y] using identDistrib_sub_comp_fst_comp_snd_prod_neg
      (μ := μ) (h_meas i)
  have hmax_int_sub :
      Integrable (fun ω => ((Finset.univ.sup' hs_univ fun i : ↥s => |X i ω|) ^ p)) μ := by
    convert hmax_int using 1
    ext ω
    rw [sup'_univ_subtype_eq_sup' (hs := hs) (hs_univ := hs_univ) (f := fun i => |X i ω|)]
  have hmax_intY_nat :
      Integrable
        (fun ω : Ω × Ω => ((Finset.univ.sup' hs_univ fun i : ↥s => |Y i ω|) ^ p)) (μ.prod μ) := by
    simpa [Y] using
      integrable_sup'_abs_sub_pow_of_integrable_sup'_abs_pow
        (μ := μ) (X := fun i : ↥s => X i) (s := Finset.univ) hs_univ h_meas_sub hmax_int_sub
  have hmax_intY :
      Integrable
        (fun ω : Ω × Ω => (Finset.univ.sup' hs_univ fun i : ↥s => |Y i ω|) ^ (p : ℝ)) (μ.prod μ) := by
    simpa [Real.rpow_natCast, Y] using hmax_intY_nat
  have hlin :=
    integral_abs_finsetSum_rpow_le_rosenthal_of_identDistrib_neg
      (μ := μ.prod μ) (X := Y) (s := Finset.univ) hs_univ hp_real h_indepY
      (fun i => by simpa [Y] using! ((h_meas i).comp measurable_fst).sub ((h_meas i).comp measurable_snd))
      h_sq_intY h_symmY hmax_intY
  have hmax_bound :
      ∫ ω : Ω × Ω, ((Finset.univ.sup' hs_univ fun i : ↥s => |Y i ω|) ^ p) ∂(μ.prod μ) ≤
        (2 : ℝ) ^ p * ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ := by
    have hmax_bound_univ :
        ∫ ω : Ω × Ω, ((Finset.univ.sup' hs_univ fun i : ↥s => |Y i ω|) ^ p) ∂(μ.prod μ) ≤
          (2 : ℝ) ^ p * ∫ ω, ((Finset.univ.sup' hs_univ fun i : ↥s => |X i ω|) ^ p) ∂μ := by
      simpa [Y] using
        (integral_sup'_abs_sub_pow_le_two_pow_mul_integral_sup'_abs_pow
          (μ := μ) (X := fun i : ↥s => X i) (s := Finset.univ) hs_univ hp_one h_meas_sub
            hmax_int_sub)
    have hmax_int_eq :
        ∫ ω, ((Finset.univ.sup' hs_univ fun i : ↥s => |X i ω|) ^ p) ∂μ =
          ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        change ((Finset.univ.sup' hs_univ fun i : ↥s => |X i ω|) ^ p) =
          ((s.sup' hs fun i => |X i ω|) ^ p)
        rw [sup'_univ_subtype_eq_sup' (hs := hs) (hs_univ := hs_univ) (f := fun i => |X i ω|)]
    calc
      ∫ ω : Ω × Ω, ((Finset.univ.sup' hs_univ fun i : ↥s => |Y i ω|) ^ p) ∂(μ.prod μ)
          ≤ (2 : ℝ) ^ p * ∫ ω, ((Finset.univ.sup' hs_univ fun i : ↥s => |X i ω|) ^ p) ∂μ :=
            hmax_bound_univ
      _ = (2 : ℝ) ^ p * ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ := by
            rw [hmax_int_eq]
  have hSigma_le :
      ∑ i ∈ (Finset.univ : Finset ↥s), ProbabilityTheory.moment (Y i) 2 (μ.prod μ) ≤
        4 * ∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ := by
    calc
      ∑ i ∈ (Finset.univ : Finset ↥s), ProbabilityTheory.moment (Y i) 2 (μ.prod μ)
          ≤ ∑ i ∈ (Finset.univ : Finset ↥s), 4 * ProbabilityTheory.moment (X i) 2 μ := by
              refine Finset.sum_le_sum ?_
              intro i hi
              simpa [Y] using moment_sub_comp_fst_comp_snd_le_four_mul
                (μ := μ) (h_meas i) (h_sq_int i i.property)
      _ = 4 * ∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ := by
            simpa [Finset.univ_eq_attach, Finset.mul_sum] using
              (s.sum_attach (fun i => 4 * ProbabilityTheory.moment (X i) 2 μ))
  have hSigma_nonneg : 0 ≤ ∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ := by
    refine Finset.sum_nonneg ?_
    intro i hi
    simp [ProbabilityTheory.moment]
    positivity
  have hsqrt_le :
      Real.sqrt (∑ i ∈ (Finset.univ : Finset ↥s), ProbabilityTheory.moment (Y i) 2 (μ.prod μ)) ≤
        2 * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ) := by
    have hsqrt_eq :
        Real.sqrt (4 * ∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ) =
          2 * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ) := by
      have hsq :
          4 * ∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ =
            (2 * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)) ^ 2 := by
        calc
          4 * ∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ
              = 4 * (Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)) ^ 2 := by
                  rw [Real.sq_sqrt hSigma_nonneg]
          _ = (2 * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)) ^ 2 := by
                ring
      rw [hsq, Real.sqrt_sq (by positivity)]
    calc
      Real.sqrt (∑ i ∈ (Finset.univ : Finset ↥s), ProbabilityTheory.moment (Y i) 2 (μ.prod μ))
          ≤ Real.sqrt (4 * ∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ) := by
              exact Real.sqrt_le_sqrt hSigma_le
      _ = 2 * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ) := hsqrt_eq
  have hRB_nonneg : 0 ≤ rosenthalBennettIntegralConst := by
    dsimp [rosenthalBennettIntegralConst]
    positivity
  have hpow_le :
      (rosenthalBennettIntegralConst *
          (Real.sqrt p *
            Real.sqrt (∑ i ∈ (Finset.univ : Finset ↥s), ProbabilityTheory.moment (Y i) 2 (μ.prod μ)))) ^ p
        ≤
      (2 * rosenthalBennettIntegralConst *
          (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ))) ^ p := by
    have hbase_le :
        rosenthalBennettIntegralConst *
            (Real.sqrt p *
              Real.sqrt
                (∑ i ∈ (Finset.univ : Finset ↥s), ProbabilityTheory.moment (Y i) 2 (μ.prod μ)))
          ≤
        2 * rosenthalBennettIntegralConst *
          (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)) := by
      calc
        rosenthalBennettIntegralConst *
            (Real.sqrt p *
              Real.sqrt
                (∑ i ∈ (Finset.univ : Finset ↥s), ProbabilityTheory.moment (Y i) 2 (μ.prod μ)))
            ≤
          rosenthalBennettIntegralConst *
            (Real.sqrt p * (2 * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ))) := by
              refine mul_le_mul_of_nonneg_left ?_ hRB_nonneg
              refine mul_le_mul_of_nonneg_left hsqrt_le (Real.sqrt_nonneg _)
        _ = 2 * rosenthalBennettIntegralConst *
              (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)) := by
              ring
    have hbase_nonneg :
        0 ≤ rosenthalBennettIntegralConst *
          (Real.sqrt p *
            Real.sqrt (∑ i ∈ (Finset.univ : Finset ↥s), ProbabilityTheory.moment (Y i) 2 (μ.prod μ))) := by
      refine mul_nonneg hRB_nonneg ?_
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    exact pow_le_pow_left₀ hbase_nonneg hbase_le p
  have hmax_term_le :
      (p : ℝ) ^ p * ∫ ω : Ω × Ω, ((Finset.univ.sup' hs_univ fun i : ↥s => |Y i ω|) ^ p) ∂(μ.prod μ) ≤
        (p : ℝ) ^ p * ((2 : ℝ) ^ p * ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ) := by
    exact mul_le_mul_of_nonneg_left hmax_bound (by positivity)
  have htail_term_le :
      2 *
          (rosenthalBennettIntegralConst *
            (Real.sqrt p *
              Real.sqrt (∑ i ∈ (Finset.univ : Finset ↥s), ProbabilityTheory.moment (Y i) 2 (μ.prod μ)))) ^ p
        ≤
      2 *
          (2 * rosenthalBennettIntegralConst *
            (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ))) ^ p := by
    exact mul_le_mul_of_nonneg_left hpow_le (by positivity)
  have hsum_eq :
      ∀ ω : Ω × Ω, ∑ i ∈ (Finset.univ : Finset ↥s), Y i ω = symmetrizedFinsetSum X s ω := by
    intro ω
    simpa [Y] using sum_univ_subtype_eq_symmetrizedFinsetSum (X := X) (s := s) ω
  calc
    ∫ ω : Ω × Ω, |symmetrizedFinsetSum X s ω| ^ p ∂(μ.prod μ)
        = ∫ ω : Ω × Ω, |∑ i ∈ (Finset.univ : Finset ↥s), Y i ω| ^ p ∂(μ.prod μ) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun ω => by
              change |symmetrizedFinsetSum X s ω| ^ p =
                |∑ i ∈ (Finset.univ : Finset ↥s), Y i ω| ^ p
              rw [← hsum_eq ω]
    _ ≤ (p : ℝ) ^ p *
          ∫ ω : Ω × Ω, ((Finset.univ.sup' hs_univ fun i : ↥s => |Y i ω|) ^ p) ∂(μ.prod μ) +
            2 *
              (rosenthalBennettIntegralConst *
                (Real.sqrt p *
                  Real.sqrt
                    (∑ i ∈ (Finset.univ : Finset ↥s), ProbabilityTheory.moment (Y i) 2 (μ.prod μ)))) ^ p := by
            simpa [Real.rpow_natCast] using hlin
    _ ≤ (p : ℝ) ^ p * ((2 : ℝ) ^ p * ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ) +
            2 *
              (rosenthalBennettIntegralConst *
                (Real.sqrt p *
                  Real.sqrt
                    (∑ i ∈ (Finset.univ : Finset ↥s), ProbabilityTheory.moment (Y i) 2 (μ.prod μ)))) ^ p := by
            exact add_le_add hmax_term_le le_rfl
    _ ≤ ((p : ℝ) ^ p * (2 : ℝ) ^ p) * ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ +
            2 *
              (2 * rosenthalBennettIntegralConst *
                (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ))) ^ p := by
            have hmul :
                (p : ℝ) ^ p * ((2 : ℝ) ^ p * ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ) =
                  ((p : ℝ) ^ p * (2 : ℝ) ^ p) * ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ := by
                ring_nf
            rw [hmul]
            exact add_le_add le_rfl htail_term_le

/-- Integrability of the symmetrized sum under the Rosenthal assumptions. -/
theorem integrable_abs_symmetrizedFinsetSum_pow_of_rosenthal
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p : ℕ}
    (hp : 2 ≤ p)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_sq_int : ∀ i ∈ s, Integrable (fun ω => X i ω ^ (2 : ℕ)) μ)
    (hmax_int : Integrable (fun ω => (s.sup' hs (fun i => |X i ω|)) ^ p) μ) :
    Integrable (fun ω : Ω × Ω => |symmetrizedFinsetSum X s ω| ^ p) (μ.prod μ) := by
  classical
  let : Nonempty ↥s := ⟨⟨hs.choose, hs.choose_spec⟩⟩
  let Y : ↥s → Ω × Ω → ℝ := fun i ω => X i ω.1 - X i ω.2
  have hs_univ : (Finset.univ : Finset ↥s).Nonempty := Finset.univ_nonempty
  have hp_real : 2 ≤ (p : ℝ) := by exact_mod_cast hp
  have h_indep_sub : iIndepFun (fun i : ↥s => X i) μ := by
    simpa using h_indep.precomp (g := ((↑) : ↥s → ι)) Subtype.val_injective
  have h_meas_sub : ∀ i : ↥s, Measurable (X i) := by
    intro i
    exact h_meas i
  have h_indepY : iIndepFun Y (μ.prod μ) := by
    simpa [Y] using
      iIndepFun_sub_comp_fst_comp_snd_prod
        (μ := μ) (X := fun i : ↥s => X i) h_indep_sub h_meas_sub
  have h_sq_intY :
      ∀ i ∈ (Finset.univ : Finset ↥s),
        Integrable (fun ω => Y i ω ^ (2 : ℕ)) (μ.prod μ) := by
    intro i hi
    simpa [Y] using integrable_pow_two_sub_comp_fst_comp_snd
      (μ := μ) (h_meas i) (h_sq_int i i.property)
  have h_symmY :
      ∀ i ∈ (Finset.univ : Finset ↥s),
        IdentDistrib (Y i) (fun ω => -Y i ω) (μ.prod μ) (μ.prod μ) := by
    intro i hi
    simpa [Y] using identDistrib_sub_comp_fst_comp_snd_prod_neg
      (μ := μ) (h_meas i)
  have hmax_int_sub :
      Integrable (fun ω => ((Finset.univ.sup' hs_univ fun i : ↥s => |X i ω|) ^ p)) μ := by
    convert hmax_int using 1
    ext ω
    rw [sup'_univ_subtype_eq_sup' (hs := hs) (hs_univ := hs_univ) (f := fun i => |X i ω|)]
  have hmax_intY_nat :
      Integrable
        (fun ω : Ω × Ω => ((Finset.univ.sup' hs_univ fun i : ↥s => |Y i ω|) ^ p)) (μ.prod μ) := by
    simpa [Y] using
      integrable_sup'_abs_sub_pow_of_integrable_sup'_abs_pow
        (μ := μ) (X := fun i : ↥s => X i) (s := Finset.univ) hs_univ h_meas_sub hmax_int_sub
  have hmax_intY :
      Integrable
        (fun ω : Ω × Ω => (Finset.univ.sup' hs_univ fun i : ↥s => |Y i ω|) ^ (p : ℝ)) (μ.prod μ) := by
    simpa [Real.rpow_natCast, Y] using hmax_intY_nat
  have hint :=
    integrable_abs_finsetSum_rpow_of_identDistrib_neg
      (μ := μ.prod μ) (X := Y) (s := Finset.univ) hs_univ hp_real h_indepY
      (fun i => by simpa [Y] using! ((h_meas i).comp measurable_fst).sub ((h_meas i).comp measurable_snd))
      h_sq_intY h_symmY hmax_intY
  have hsum_eq :
      ∀ ω : Ω × Ω, ∑ i ∈ (Finset.univ : Finset ↥s), Y i ω = symmetrizedFinsetSum X s ω := by
    intro ω
    simpa [Y] using sum_univ_subtype_eq_symmetrizedFinsetSum (X := X) (s := s) ω
  convert hint using 1
  ext ω
  rw [show |symmetrizedFinsetSum X s ω| ^ p = |symmetrizedFinsetSum X s ω| ^ (p : ℝ) by
    rw [Real.rpow_natCast]]
  rw [← hsum_eq ω]

/-- Rosenthal bound for the centered finite sum on the original probability
space. -/
theorem integral_abs_centeredFinsetSum_pow_le_rosenthal
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p : ℕ}
    (hp : 2 ≤ p)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i ∈ s, Integrable (X i) μ)
    (h_sq_int : ∀ i ∈ s, Integrable (fun ω => X i ω ^ (2 : ℕ)) μ)
    (hmax_int : Integrable (fun ω => (s.sup' hs (fun i => |X i ω|)) ^ p) μ) :
    ∫ ω, |centeredFinsetSum X μ s ω| ^ p ∂μ ≤
      ((p : ℝ) ^ p * (2 : ℝ) ^ p) * ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ +
        2 *
          (2 * rosenthalBennettIntegralConst *
            (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ))) ^ p := by
  have hsymm_int :
      Integrable (fun ω : Ω × Ω => |symmetrizedFinsetSum X s ω| ^ p) (μ.prod μ) := by
    exact integrable_abs_symmetrizedFinsetSum_pow_of_rosenthal
      (μ := μ) (X := X) (s := s) hs hp h_indep h_meas h_sq_int hmax_int
  exact
    (integral_abs_centeredFinsetSum_pow_le_integral_abs_symmetrizedFinsetSum_pow
      (μ := μ) (X := X) (s := s) (p := p) (by omega) h_int hsymm_int).trans
      (integral_abs_symmetrizedFinsetSum_pow_le_rosenthal
        (μ := μ) (X := X) (s := s) hs hp h_indep h_meas h_sq_int hmax_int)

/-- Note-facing `L^p`-scale form of Rosenthal's inequality: taking the
`1 / p` power of the moment estimate yields the standard sum of the maximal
`L^p` term and the square-function term. -/
theorem integral_abs_centeredFinsetSum_pow_rpow_inv_le_rosenthal
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p : ℕ}
    (hp : 2 ≤ p)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i ∈ s, Integrable (X i) μ)
    (h_sq_int : ∀ i ∈ s, Integrable (fun ω => X i ω ^ (2 : ℕ)) μ)
    (hmax_int : Integrable (fun ω => (s.sup' hs (fun i => |X i ω|)) ^ p) μ) :
    (∫ ω, |centeredFinsetSum X μ s ω| ^ p ∂μ) ^ (1 / (p : ℝ)) ≤
      2 * (p : ℝ) * (∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ) ^ (1 / (p : ℝ)) +
        4 * rosenthalBennettIntegralConst *
          (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)) := by
  let L : ℝ := ∫ ω, |centeredFinsetSum X μ s ω| ^ p ∂μ
  let M : ℝ := ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ
  let σ : ℝ := ∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ
  let V : ℝ := Real.sqrt p * Real.sqrt σ
  have hp_one : 1 ≤ p := by omega
  have hp_ne_zero : p ≠ 0 := by omega
  have hp_real_one : (1 : ℝ) ≤ p := by exact_mod_cast hp_one
  have hp_inv_nonneg : 0 ≤ 1 / (p : ℝ) := by positivity
  have hp_inv_le_one : 1 / (p : ℝ) ≤ 1 := by
    simpa [one_div] using (inv_le_one_of_one_le₀ hp_real_one)
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    positivity
  have hsup_nonneg : ∀ ω, 0 ≤ s.sup' hs (fun i => |X i ω|) := by
    intro ω
    have hnonneg : 0 ≤ |X hs.choose ω| := abs_nonneg _
    exact le_trans hnonneg (Finset.le_sup' (f := fun i => |X i ω|) hs.choose_spec)
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact integral_nonneg fun ω => by
      exact pow_nonneg (hsup_nonneg ω) _
  have hσ_nonneg : 0 ≤ σ := by
    dsimp [σ]
    refine Finset.sum_nonneg ?_
    intro i hi
    simp [ProbabilityTheory.moment]
    positivity
  have hV_nonneg : 0 ≤ V := by
    dsimp [V]
    positivity
  have hRB_nonneg : 0 ≤ rosenthalBennettIntegralConst := by
    dsimp [rosenthalBennettIntegralConst]
    positivity
  have hbase_nonneg : 0 ≤ 2 * rosenthalBennettIntegralConst * V := by
    dsimp [V]
    positivity
  have hmoment :
      L ≤ ((p : ℝ) ^ p * (2 : ℝ) ^ p) * M +
        2 * (2 * rosenthalBennettIntegralConst * V) ^ p := by
    simpa [L, M, σ, V] using
      integral_abs_centeredFinsetSum_pow_le_rosenthal
        (μ := μ) (X := X) (s := s) hs hp h_indep h_meas h_int h_sq_int hmax_int
  have hroot :
      L ^ (1 / (p : ℝ)) ≤
        ((((p : ℝ) ^ p * (2 : ℝ) ^ p) * M) +
          2 * (2 * rosenthalBennettIntegralConst * V) ^ p) ^ (1 / (p : ℝ)) := by
    exact Real.rpow_le_rpow hL_nonneg hmoment hp_inv_nonneg
  have hfirst_root :
      ((((p : ℝ) ^ p * (2 : ℝ) ^ p) * M) ^ (1 / (p : ℝ))) =
        2 * (p : ℝ) * M ^ (1 / (p : ℝ)) := by
    rw [show (1 / (p : ℝ)) = (p⁻¹ : ℝ) by rw [one_div]]
    rw [Real.mul_rpow (by positivity) hM_nonneg]
    rw [show (p : ℝ) ^ p * (2 : ℝ) ^ p = ((p : ℝ) * 2) ^ p by rw [← mul_pow]]
    rw [Real.pow_rpow_inv_natCast (by positivity) hp_ne_zero]
    ring
  have htwo_rpow_le : (2 : ℝ) ^ (1 / (p : ℝ)) ≤ 2 := by
    have hpow :
        (2 : ℝ) ^ (1 / (p : ℝ)) ≤ (2 : ℝ) ^ (1 : ℝ) := by
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hp_inv_le_one
    simpa using hpow
  have hsecond_root :
      (2 * (2 * rosenthalBennettIntegralConst * V) ^ p) ^ (1 / (p : ℝ)) ≤
        4 * rosenthalBennettIntegralConst * V := by
    have htwo_rpow_le' : (2 : ℝ) ^ (p⁻¹ : ℝ) ≤ 2 := by
      simpa [one_div] using htwo_rpow_le
    rw [show (1 / (p : ℝ)) = (p⁻¹ : ℝ) by rw [one_div]]
    calc
      (2 * (2 * rosenthalBennettIntegralConst * V) ^ p) ^ (p⁻¹ : ℝ)
          = (2 : ℝ) ^ (p⁻¹ : ℝ) *
              ((2 * rosenthalBennettIntegralConst * V) ^ p) ^ (p⁻¹ : ℝ) := by
                rw [Real.mul_rpow (by positivity) (by positivity)]
      _ = (2 : ℝ) ^ (p⁻¹ : ℝ) * (2 * rosenthalBennettIntegralConst * V) := by
            rw [Real.pow_rpow_inv_natCast hbase_nonneg hp_ne_zero]
      _ ≤ 2 * (2 * rosenthalBennettIntegralConst * V) := by
            refine mul_le_mul_of_nonneg_right htwo_rpow_le' hbase_nonneg
      _ = 4 * rosenthalBennettIntegralConst * V := by ring
  calc
    L ^ (1 / (p : ℝ))
        ≤ ((((p : ℝ) ^ p * (2 : ℝ) ^ p) * M) +
            2 * (2 * rosenthalBennettIntegralConst * V) ^ p) ^ (1 / (p : ℝ)) := hroot
    _ ≤ ((((p : ℝ) ^ p * (2 : ℝ) ^ p) * M) ^ (1 / (p : ℝ))) +
          (2 * (2 * rosenthalBennettIntegralConst * V) ^ p) ^ (1 / (p : ℝ)) := by
            refine Real.rpow_add_le_add_rpow ?_ ?_ hp_inv_nonneg hp_inv_le_one
            · positivity
            · positivity
    _ ≤ 2 * (p : ℝ) * M ^ (1 / (p : ℝ)) +
          4 * rosenthalBennettIntegralConst * V := by
            rw [hfirst_root]
            exact add_le_add le_rfl hsecond_root
    _ = 2 * (p : ℝ) * (∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ) ^ (1 / (p : ℝ)) +
          4 * rosenthalBennettIntegralConst *
            (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)) := by
            simp [M, V, σ]

/-- Real-exponent Rosenthal bound for the symmetrized difference sum on the
product probability space. -/
theorem integral_abs_symmetrizedFinsetSum_rpow_le_rosenthal
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p : ℝ}
    (hp : 2 ≤ p)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_sq_int : ∀ i ∈ s, Integrable (fun ω => X i ω ^ (2 : ℕ)) μ)
    (hmax_int : Integrable (fun ω => (s.sup' hs (fun i => |X i ω|)) ^ p) μ) :
    ∫ ω : Ω × Ω, |symmetrizedFinsetSum X s ω| ^ p ∂(μ.prod μ) ≤
      (p ^ p * (2 : ℝ) ^ p) * ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ +
        2 *
          (2 * rosenthalBennettIntegralConst *
            (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ))) ^ p := by
  classical
  let : Nonempty ↥s := ⟨⟨hs.choose, hs.choose_spec⟩⟩
  let Y : ↥s → Ω × Ω → ℝ := fun i ω => X i ω.1 - X i ω.2
  have hs_univ : (Finset.univ : Finset ↥s).Nonempty := Finset.univ_nonempty
  have hp_one : 1 ≤ p := le_trans (by norm_num) hp
  have hp_nonneg : 0 ≤ p := le_trans zero_le_one hp_one
  have h_indep_sub : iIndepFun (fun i : ↥s => X i) μ := by
    simpa using h_indep.precomp (g := ((↑) : ↥s → ι)) Subtype.val_injective
  have h_meas_sub : ∀ i : ↥s, Measurable (X i) := fun i => h_meas i
  have h_indepY : iIndepFun Y (μ.prod μ) := by
    simpa [Y] using
      iIndepFun_sub_comp_fst_comp_snd_prod
        (μ := μ) (X := fun i : ↥s => X i) h_indep_sub h_meas_sub
  have h_sq_intY :
      ∀ i ∈ (Finset.univ : Finset ↥s),
        Integrable (fun ω => Y i ω ^ (2 : ℕ)) (μ.prod μ) := by
    intro i hi
    simpa [Y] using integrable_pow_two_sub_comp_fst_comp_snd
      (μ := μ) (h_meas i) (h_sq_int i i.property)
  have h_symmY :
      ∀ i ∈ (Finset.univ : Finset ↥s),
        IdentDistrib (Y i) (fun ω => -Y i ω) (μ.prod μ) (μ.prod μ) := by
    intro i hi
    simpa [Y] using identDistrib_sub_comp_fst_comp_snd_prod_neg
      (μ := μ) (h_meas i)
  have hmax_int_sub :
      Integrable (fun ω => (Finset.univ.sup' hs_univ fun i : ↥s => |X i ω|) ^ p) μ := by
    convert hmax_int using 1
    ext ω
    rw [sup'_univ_subtype_eq_sup' (hs := hs) (hs_univ := hs_univ) (f := fun i => |X i ω|)]
  have hmax_intY :
      Integrable
        (fun ω : Ω × Ω => (Finset.univ.sup' hs_univ fun i : ↥s => |Y i ω|) ^ p) (μ.prod μ) := by
    simpa [Y] using
      integrable_sup'_abs_sub_rpow_of_integrable_sup'_abs_rpow
        (μ := μ) (X := fun i : ↥s => X i) (s := Finset.univ) hs_univ hp_one h_meas_sub hmax_int_sub
  have hlin :=
    integral_abs_finsetSum_rpow_le_rosenthal_of_identDistrib_neg
      (μ := μ.prod μ) (X := Y) (s := Finset.univ) hs_univ hp h_indepY
      (fun i => by simpa [Y] using! ((h_meas i).comp measurable_fst).sub ((h_meas i).comp measurable_snd))
      h_sq_intY h_symmY hmax_intY
  have hmax_bound :
      ∫ ω : Ω × Ω, (Finset.univ.sup' hs_univ fun i : ↥s => |Y i ω|) ^ p ∂(μ.prod μ) ≤
        (2 : ℝ) ^ p * ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ := by
    have hmax_bound_univ :
        ∫ ω : Ω × Ω, (Finset.univ.sup' hs_univ fun i : ↥s => |Y i ω|) ^ p ∂(μ.prod μ) ≤
          (2 : ℝ) ^ p *
            ∫ ω, (Finset.univ.sup' hs_univ fun i : ↥s => |X i ω|) ^ p ∂μ := by
      simpa [Y] using
        (integral_sup'_abs_sub_rpow_le_two_rpow_mul_integral_sup'_abs_rpow
          (μ := μ) (X := fun i : ↥s => X i) (s := Finset.univ) hs_univ hp_one h_meas_sub
            hmax_int_sub)
    have hmax_int_eq :
        ∫ ω, (Finset.univ.sup' hs_univ fun i : ↥s => |X i ω|) ^ p ∂μ =
          ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        change (Finset.univ.sup' hs_univ fun i : ↥s => |X i ω|) ^ p =
          (s.sup' hs fun i => |X i ω|) ^ p
        rw [sup'_univ_subtype_eq_sup' (hs := hs) (hs_univ := hs_univ) (f := fun i => |X i ω|)]
    calc
      ∫ ω : Ω × Ω, (Finset.univ.sup' hs_univ fun i : ↥s => |Y i ω|) ^ p ∂(μ.prod μ)
          ≤ (2 : ℝ) ^ p *
              ∫ ω, (Finset.univ.sup' hs_univ fun i : ↥s => |X i ω|) ^ p ∂μ := hmax_bound_univ
      _ = (2 : ℝ) ^ p * ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ := by rw [hmax_int_eq]
  have hSigma_le :
      ∑ i ∈ (Finset.univ : Finset ↥s), ProbabilityTheory.moment (Y i) 2 (μ.prod μ) ≤
        4 * ∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ := by
    calc
      ∑ i ∈ (Finset.univ : Finset ↥s), ProbabilityTheory.moment (Y i) 2 (μ.prod μ)
          ≤ ∑ i ∈ (Finset.univ : Finset ↥s), 4 * ProbabilityTheory.moment (X i) 2 μ := by
              refine Finset.sum_le_sum ?_
              intro i hi
              simpa [Y] using moment_sub_comp_fst_comp_snd_le_four_mul
                (μ := μ) (h_meas i) (h_sq_int i i.property)
      _ = 4 * ∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ := by
            simpa [Finset.univ_eq_attach, Finset.mul_sum] using
              (s.sum_attach (fun i => 4 * ProbabilityTheory.moment (X i) 2 μ))
  have hSigma_nonneg : 0 ≤ ∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ := by
    refine Finset.sum_nonneg ?_
    intro i hi
    simp [ProbabilityTheory.moment]
    positivity
  have hsqrt_le :
      Real.sqrt (∑ i ∈ (Finset.univ : Finset ↥s), ProbabilityTheory.moment (Y i) 2 (μ.prod μ)) ≤
        2 * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ) := by
    have hsqrt_eq :
        Real.sqrt (4 * ∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ) =
          2 * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ) := by
      have hsq :
          4 * ∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ =
            (2 * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)) ^ 2 := by
        calc
          4 * ∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ =
              4 * (Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)) ^ 2 := by
                rw [Real.sq_sqrt hSigma_nonneg]
          _ = (2 * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)) ^ 2 := by ring
      rw [hsq, Real.sqrt_sq (by positivity)]
    exact (Real.sqrt_le_sqrt hSigma_le).trans_eq hsqrt_eq
  have hRB_nonneg : 0 ≤ rosenthalBennettIntegralConst := by
    dsimp [rosenthalBennettIntegralConst]
    positivity
  have hbase_le :
      rosenthalBennettIntegralConst *
          (Real.sqrt p *
            Real.sqrt (∑ i ∈ (Finset.univ : Finset ↥s), ProbabilityTheory.moment (Y i) 2 (μ.prod μ))) ≤
        2 * rosenthalBennettIntegralConst *
          (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)) := by
    calc
      rosenthalBennettIntegralConst *
          (Real.sqrt p *
            Real.sqrt (∑ i ∈ (Finset.univ : Finset ↥s), ProbabilityTheory.moment (Y i) 2 (μ.prod μ)))
          ≤ rosenthalBennettIntegralConst *
              (Real.sqrt p * (2 * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ))) := by
                refine mul_le_mul_of_nonneg_left ?_ hRB_nonneg
                exact mul_le_mul_of_nonneg_left hsqrt_le (Real.sqrt_nonneg _)
      _ = 2 * rosenthalBennettIntegralConst *
            (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)) := by ring
  have hbase_nonneg :
      0 ≤ rosenthalBennettIntegralConst *
        (Real.sqrt p *
          Real.sqrt (∑ i ∈ (Finset.univ : Finset ↥s), ProbabilityTheory.moment (Y i) 2 (μ.prod μ))) := by
    positivity
  have hpow_le :
      (rosenthalBennettIntegralConst *
          (Real.sqrt p *
            Real.sqrt (∑ i ∈ (Finset.univ : Finset ↥s), ProbabilityTheory.moment (Y i) 2 (μ.prod μ)))) ^ p ≤
        (2 * rosenthalBennettIntegralConst *
          (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ))) ^ p := by
    exact Real.rpow_le_rpow hbase_nonneg hbase_le hp_nonneg
  have hmax_term_le :
      p ^ p * ∫ ω : Ω × Ω, (Finset.univ.sup' hs_univ fun i : ↥s => |Y i ω|) ^ p ∂(μ.prod μ) ≤
        p ^ p * ((2 : ℝ) ^ p * ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ) := by
    exact mul_le_mul_of_nonneg_left hmax_bound (Real.rpow_nonneg hp_nonneg _)
  have htail_term_le :
      2 *
          (rosenthalBennettIntegralConst *
            (Real.sqrt p *
              Real.sqrt (∑ i ∈ (Finset.univ : Finset ↥s), ProbabilityTheory.moment (Y i) 2 (μ.prod μ)))) ^ p ≤
        2 *
          (2 * rosenthalBennettIntegralConst *
            (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ))) ^ p := by
    exact mul_le_mul_of_nonneg_left hpow_le (by positivity)
  have hsum_eq :
      ∀ ω : Ω × Ω, ∑ i ∈ (Finset.univ : Finset ↥s), Y i ω = symmetrizedFinsetSum X s ω := by
    intro ω
    simpa [Y] using sum_univ_subtype_eq_symmetrizedFinsetSum (X := X) (s := s) ω
  calc
    ∫ ω : Ω × Ω, |symmetrizedFinsetSum X s ω| ^ p ∂(μ.prod μ)
        = ∫ ω : Ω × Ω, |∑ i ∈ (Finset.univ : Finset ↥s), Y i ω| ^ p ∂(μ.prod μ) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun ω => by
              change |symmetrizedFinsetSum X s ω| ^ p =
                |∑ i ∈ (Finset.univ : Finset ↥s), Y i ω| ^ p
              rw [← hsum_eq ω]
    _ ≤ p ^ p *
          ∫ ω : Ω × Ω, (Finset.univ.sup' hs_univ fun i : ↥s => |Y i ω|) ^ p ∂(μ.prod μ) +
            2 *
              (rosenthalBennettIntegralConst *
                (Real.sqrt p *
                  Real.sqrt
                    (∑ i ∈ (Finset.univ : Finset ↥s), ProbabilityTheory.moment (Y i) 2 (μ.prod μ)))) ^ p := hlin
    _ ≤ p ^ p * ((2 : ℝ) ^ p * ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ) +
            2 *
              (rosenthalBennettIntegralConst *
                (Real.sqrt p *
                  Real.sqrt
                    (∑ i ∈ (Finset.univ : Finset ↥s), ProbabilityTheory.moment (Y i) 2 (μ.prod μ)))) ^ p :=
            add_le_add hmax_term_le le_rfl
    _ ≤ (p ^ p * (2 : ℝ) ^ p) * ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ +
            2 *
              (2 * rosenthalBennettIntegralConst *
                (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ))) ^ p := by
            rw [show p ^ p * ((2 : ℝ) ^ p * ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ) =
              (p ^ p * (2 : ℝ) ^ p) * ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ by ring]
            exact add_le_add le_rfl htail_term_le

/-- Integrability of the symmetrized real-exponent sum under the Rosenthal
assumptions. -/
theorem integrable_abs_symmetrizedFinsetSum_rpow_of_rosenthal
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p : ℝ}
    (hp : 2 ≤ p)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_sq_int : ∀ i ∈ s, Integrable (fun ω => X i ω ^ (2 : ℕ)) μ)
    (hmax_int : Integrable (fun ω => (s.sup' hs (fun i => |X i ω|)) ^ p) μ) :
    Integrable (fun ω : Ω × Ω => |symmetrizedFinsetSum X s ω| ^ p) (μ.prod μ) := by
  classical
  let : Nonempty ↥s := ⟨⟨hs.choose, hs.choose_spec⟩⟩
  let Y : ↥s → Ω × Ω → ℝ := fun i ω => X i ω.1 - X i ω.2
  have hs_univ : (Finset.univ : Finset ↥s).Nonempty := Finset.univ_nonempty
  have hp_one : 1 ≤ p := le_trans (by norm_num) hp
  have h_indep_sub : iIndepFun (fun i : ↥s => X i) μ := by
    simpa using h_indep.precomp (g := ((↑) : ↥s → ι)) Subtype.val_injective
  have h_meas_sub : ∀ i : ↥s, Measurable (X i) := fun i => h_meas i
  have h_indepY : iIndepFun Y (μ.prod μ) := by
    simpa [Y] using
      iIndepFun_sub_comp_fst_comp_snd_prod
        (μ := μ) (X := fun i : ↥s => X i) h_indep_sub h_meas_sub
  have h_sq_intY :
      ∀ i ∈ (Finset.univ : Finset ↥s),
        Integrable (fun ω => Y i ω ^ (2 : ℕ)) (μ.prod μ) := by
    intro i hi
    simpa [Y] using integrable_pow_two_sub_comp_fst_comp_snd
      (μ := μ) (h_meas i) (h_sq_int i i.property)
  have h_symmY :
      ∀ i ∈ (Finset.univ : Finset ↥s),
        IdentDistrib (Y i) (fun ω => -Y i ω) (μ.prod μ) (μ.prod μ) := by
    intro i hi
    simpa [Y] using identDistrib_sub_comp_fst_comp_snd_prod_neg
      (μ := μ) (h_meas i)
  have hmax_int_sub :
      Integrable (fun ω => (Finset.univ.sup' hs_univ fun i : ↥s => |X i ω|) ^ p) μ := by
    convert hmax_int using 1
    ext ω
    rw [sup'_univ_subtype_eq_sup' (hs := hs) (hs_univ := hs_univ) (f := fun i => |X i ω|)]
  have hmax_intY :
      Integrable
        (fun ω : Ω × Ω => (Finset.univ.sup' hs_univ fun i : ↥s => |Y i ω|) ^ p) (μ.prod μ) := by
    simpa [Y] using
      integrable_sup'_abs_sub_rpow_of_integrable_sup'_abs_rpow
        (μ := μ) (X := fun i : ↥s => X i) (s := Finset.univ) hs_univ hp_one h_meas_sub hmax_int_sub
  have hint :=
    integrable_abs_finsetSum_rpow_of_identDistrib_neg
      (μ := μ.prod μ) (X := Y) (s := Finset.univ) hs_univ hp h_indepY
      (fun i => by simpa [Y] using! ((h_meas i).comp measurable_fst).sub ((h_meas i).comp measurable_snd))
      h_sq_intY h_symmY hmax_intY
  have hsum_eq :
      ∀ ω : Ω × Ω, ∑ i ∈ (Finset.univ : Finset ↥s), Y i ω = symmetrizedFinsetSum X s ω := by
    intro ω
    simpa [Y] using sum_univ_subtype_eq_symmetrizedFinsetSum (X := X) (s := s) ω
  simpa only [hsum_eq] using hint

/-- Real-exponent Rosenthal bound for the centered finite sum on the original
probability space. -/
theorem integral_abs_centeredFinsetSum_rpow_le_rosenthal
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p : ℝ}
    (hp : 2 ≤ p)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i ∈ s, Integrable (X i) μ)
    (h_sq_int : ∀ i ∈ s, Integrable (fun ω => X i ω ^ (2 : ℕ)) μ)
    (hmax_int : Integrable (fun ω => (s.sup' hs (fun i => |X i ω|)) ^ p) μ) :
    ∫ ω, |centeredFinsetSum X μ s ω| ^ p ∂μ ≤
      (p ^ p * (2 : ℝ) ^ p) * ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ +
        2 *
          (2 * rosenthalBennettIntegralConst *
            (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ))) ^ p := by
  have hsymm_int :
      Integrable (fun ω : Ω × Ω => |symmetrizedFinsetSum X s ω| ^ p) (μ.prod μ) :=
    integrable_abs_symmetrizedFinsetSum_rpow_of_rosenthal
      (μ := μ) (X := X) (s := s) hs hp h_indep h_meas h_sq_int hmax_int
  exact
    (integral_abs_centeredFinsetSum_rpow_le_integral_abs_symmetrizedFinsetSum_rpow
      (μ := μ) (X := X) (s := s) (p := p) (le_trans (by norm_num) hp) h_int hsymm_int).trans
      (integral_abs_symmetrizedFinsetSum_rpow_le_rosenthal
        (μ := μ) (X := X) (s := s) hs hp h_indep h_meas h_sq_int hmax_int)

/-- Real-exponent `L^p`-scale Rosenthal bound for the centered finite sum. -/
theorem integral_abs_centeredFinsetSum_rpow_rpow_inv_le_rosenthal
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} (hs : s.Nonempty) {p : ℝ}
    (hp : 2 ≤ p)
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    (h_int : ∀ i ∈ s, Integrable (X i) μ)
    (h_sq_int : ∀ i ∈ s, Integrable (fun ω => X i ω ^ (2 : ℕ)) μ)
    (hmax_int : Integrable (fun ω => (s.sup' hs (fun i => |X i ω|)) ^ p) μ) :
    (∫ ω, |centeredFinsetSum X μ s ω| ^ p ∂μ) ^ (1 / p) ≤
      2 * p * (∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ) ^ (1 / p) +
        4 * rosenthalBennettIntegralConst *
          (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)) := by
  let L : ℝ := ∫ ω, |centeredFinsetSum X μ s ω| ^ p ∂μ
  let M : ℝ := ∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ
  let σ : ℝ := ∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ
  let V : ℝ := Real.sqrt p * Real.sqrt σ
  have hp_one : 1 ≤ p := le_trans (by norm_num) hp
  have hp_nonneg : 0 ≤ p := le_trans zero_le_one hp_one
  have hp_ne_zero : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp_one)
  have hp_inv_nonneg : 0 ≤ 1 / p := by positivity
  have hp_inv_le_one : 1 / p ≤ 1 := by
    simpa [one_div] using inv_le_one_of_one_le₀ hp_one
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _
  have hsup_nonneg : ∀ ω, 0 ≤ s.sup' hs (fun i => |X i ω|) := by
    intro ω
    exact le_trans (abs_nonneg _) (Finset.le_sup' (f := fun i => |X i ω|) hs.choose_spec)
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact integral_nonneg fun ω => Real.rpow_nonneg (hsup_nonneg ω) _
  have hσ_nonneg : 0 ≤ σ := by
    dsimp [σ]
    refine Finset.sum_nonneg fun i hi => ?_
    simp [ProbabilityTheory.moment]
    positivity
  have hV_nonneg : 0 ≤ V := by
    dsimp [V]
    positivity
  have hRB_nonneg : 0 ≤ rosenthalBennettIntegralConst := by
    dsimp [rosenthalBennettIntegralConst]
    positivity
  have hbase_nonneg : 0 ≤ 2 * rosenthalBennettIntegralConst * V := by positivity
  have hmoment :
      L ≤ (p ^ p * (2 : ℝ) ^ p) * M +
        2 * (2 * rosenthalBennettIntegralConst * V) ^ p := by
    simpa [L, M, σ, V] using
      integral_abs_centeredFinsetSum_rpow_le_rosenthal
        (μ := μ) (X := X) (s := s) hs hp h_indep h_meas h_int h_sq_int hmax_int
  have hroot :
      L ^ (1 / p) ≤
        ((p ^ p * (2 : ℝ) ^ p) * M +
          2 * (2 * rosenthalBennettIntegralConst * V) ^ p) ^ (1 / p) :=
    Real.rpow_le_rpow hL_nonneg hmoment hp_inv_nonneg
  have hfirst_root :
      ((p ^ p * (2 : ℝ) ^ p) * M) ^ (1 / p) = 2 * p * M ^ (1 / p) := by
    rw [show (1 / p) = p⁻¹ by rw [one_div]]
    rw [show p ^ p * (2 : ℝ) ^ p = (p * 2) ^ p by
      rw [Real.mul_rpow hp_nonneg (by norm_num)]]
    rw [Real.mul_rpow (Real.rpow_nonneg (mul_nonneg hp_nonneg (by norm_num)) _) hM_nonneg]
    rw [Real.rpow_rpow_inv (mul_nonneg hp_nonneg (by norm_num)) hp_ne_zero]
    ring
  have htwo_rpow_le : (2 : ℝ) ^ (1 / p) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hp_inv_le_one
  have hsecond_root :
      (2 * (2 * rosenthalBennettIntegralConst * V) ^ p) ^ (1 / p) ≤
        4 * rosenthalBennettIntegralConst * V := by
    rw [show (1 / p) = p⁻¹ by rw [one_div]]
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hbase_nonneg _)]
    rw [Real.rpow_rpow_inv hbase_nonneg hp_ne_zero]
    calc
      (2 : ℝ) ^ p⁻¹ * (2 * rosenthalBennettIntegralConst * V)
          ≤ 2 * (2 * rosenthalBennettIntegralConst * V) := by
              exact mul_le_mul_of_nonneg_right (by simpa using htwo_rpow_le) hbase_nonneg
      _ = 4 * rosenthalBennettIntegralConst * V := by ring
  calc
    L ^ (1 / p)
        ≤ ((p ^ p * (2 : ℝ) ^ p) * M +
            2 * (2 * rosenthalBennettIntegralConst * V) ^ p) ^ (1 / p) := hroot
    _ ≤ ((p ^ p * (2 : ℝ) ^ p) * M) ^ (1 / p) +
          (2 * (2 * rosenthalBennettIntegralConst * V) ^ p) ^ (1 / p) := by
            exact Real.rpow_add_le_add_rpow (by positivity) (by positivity) hp_inv_nonneg hp_inv_le_one
    _ ≤ 2 * p * M ^ (1 / p) + 4 * rosenthalBennettIntegralConst * V := by
          rw [hfirst_root]
          exact add_le_add le_rfl hsecond_root
    _ = 2 * p * (∫ ω, (s.sup' hs (fun i => |X i ω|)) ^ p ∂μ) ^ (1 / p) +
          4 * rosenthalBennettIntegralConst *
            (Real.sqrt p * Real.sqrt (∑ i ∈ s, ProbabilityTheory.moment (X i) 2 μ)) := by
            simp [M, V, σ]


end
end IndependentSums
end Homogenization
