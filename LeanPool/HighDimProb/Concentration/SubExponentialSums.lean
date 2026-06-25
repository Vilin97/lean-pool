/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Concentration.SubGaussianSums
import LeanPool.HighDimProb.Concentration.MaxScale

/-!
# Independent finite sums of centered subExponential variables

This file starts the Bernstein/subExponential finite-sum branch.  The existing
`CenteredSubExponentialMGF` predicate is an expectation-level local MGF bound;
the `LIntegral` auxiliary below is the proof-facing form used by Chernoff
tail arguments.

Verified Wikipedia references:
* Heavy-tailed distribution:
  https://en.wikipedia.org/wiki/Heavy-tailed_distribution
* Moment-generating function:
  https://en.wikipedia.org/wiki/Moment-generating_function
-/

namespace HighDimProb

open MeasureTheory ProbabilityTheory

noncomputable section

open scoped BigOperators ENNReal

/--
Proof-friendly centered subExponential MGF formulation using `lintegral`.

The lambda domain is local: the bound is available only when
`|lambda| <= 1 / K`.

Formula reference: subExponential control is represented here through a local
exponential-moment/MGF bound, contrasting with heavy-tailed variables whose
moment-generating functions may fail globally; see
https://en.wikipedia.org/wiki/Heavy-tailed_distribution and
https://en.wikipedia.org/wiki/Moment-generating_function
-/
def CenteredSubExponentialMGFLIntegral {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) (X : RealRandomVariable Omega) (K : Real) : Prop :=
  IsRealRandomVariable P X ∧
    0 < K ∧
      ∀ lambda : Real, |lambda| <= 1 / K →
        (∫⁻ omega, ENNReal.ofReal (Real.exp (lambda * X omega)) ∂P) <=
          ENNReal.ofReal (Real.exp (K ^ 2 * lambda ^ 2))

/--
The proof-facing lintegral subExponential MGF predicate implies the raw
expectation-level predicate.

Formula reference: this converts the `lintegral` bound
`int exp(lambda X) <= exp(K^2 lambda^2)` on `|lambda| <= 1 / K` back to the
expectation/MGF form; see
https://en.wikipedia.org/wiki/Moment-generating_function
-/
theorem centeredSubExponentialMGF_of_centeredSubExponentialMGFLIntegral
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X : RealRandomVariable Omega} {K : Real}
    (hMGF : CenteredSubExponentialMGFLIntegral P X K) :
    CenteredSubExponentialMGF P X K := by
  rcases hMGF with ⟨hX, hK, hbound⟩
  refine ⟨hK, ?_⟩
  intro lambda hlambda
  let f : RealRandomVariable Omega := fun omega => Real.exp (lambda * X omega)
  have hf_nonneg : 0 ≤ᵐ[P] f := ae_of_all P fun omega => (Real.exp_pos _).le
  have hf_meas : AEStronglyMeasurable f P := by
    have h_real : Measurable f := (hX.const_mul lambda).exp
    exact h_real.aestronglyMeasurable
  have hf_lintegral_ne_top :
      (∫⁻ omega, ENNReal.ofReal (f omega) ∂P) ≠ ∞ := by
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound lambda hlambda)
  have hf_int : Integrable f P := by
    exact
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
        hf_meas hf_nonneg).mp hf_lintegral_ne_top
  have h_lintegral :
      ENNReal.ofReal (expect P f) =
        (∫⁻ omega, ENNReal.ofReal (f omega) ∂P) := by
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf_int hf_nonneg
  have h_ofReal :
      ENNReal.ofReal (expect P f) <=
        ENNReal.ofReal (Real.exp (K ^ 2 * lambda ^ 2)) := by
    rw [h_lintegral]
    exact hbound lambda hlambda
  exact
    (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).mp h_ofReal

-- Formula reference: products of exponentials convert to an exponential of a
-- sum, matching finite independent MGF multiplication; see
-- https://en.wikipedia.org/wiki/Moment-generating_function
private theorem finset_prod_exp_eq_exp_sum {ι : Type*} (s : Finset ι)
    (f : ι → Real) :
    s.prod (fun i => Real.exp (f i)) = Real.exp (s.sum f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, Real.exp_add]

/--
Raw local MGF product bound for independent centered subExponential variables.

The domain is expressed with an explicit `Kmax`, matching the Bernstein
abstraction where the variance proxy is `sum_i K_i^2` and the local lambda
domain is controlled by the largest individual scale.

Formula reference: independent MGFs multiply, so local subExponential proxies
add as `sum_i K_i^2`, while the admissible lambda range is governed by a
largest scale `Kmax`; see
https://en.wikipedia.org/wiki/Moment-generating_function
-/
theorem centeredSubExponentialMGF_finset_sum_mgf_bound_of_iIndepFun
    {Omega ι : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {s : Finset ι}
    {X : ι → RealRandomVariable Omega} {K : ι → Real} {Kmax : Real}
    (_hKmax : 0 < Kmax)
    (hKle : ∀ i, i ∈ s → K i <= Kmax)
    (hX : ∀ i : ι, IsRealRandomVariable P (X i))
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hMGF : ∀ i, i ∈ s → CenteredSubExponentialMGF P (X i) (K i)) :
    ∀ lambda : Real, |lambda| <= 1 / Kmax →
      expect P (fun omega => Real.exp (lambda * s.sum (fun i => X i omega))) <=
        Real.exp ((s.sum (fun i => (K i) ^ 2)) * lambda ^ 2) := by
  intro lambda hlambda
  have hdomain : ∀ i, i ∈ s → |lambda| <= 1 / K i := by
    intro i hi
    exact hlambda.trans (one_div_le_one_div_of_le (hMGF i hi).1 (hKle i hi))
  have hmgf_sum :
      ProbabilityTheory.mgf (fun omega => s.sum (fun i => X i omega)) P lambda =
        s.prod (fun i => ProbabilityTheory.mgf (X i) P lambda) := by
    have hsum_eq :
        (∑ i ∈ s, X i) = (fun omega => s.sum (fun i => X i omega)) := by
      funext omega
      simp only [Finset.sum_apply]
    rw [← hsum_eq]
    exact hIndep.mgf_sum (μ := P) (t := lambda) (fun i => hX i) s
  calc
    expect P (fun omega => Real.exp (lambda * s.sum (fun i => X i omega)))
        = ProbabilityTheory.mgf (fun omega => s.sum (fun i => X i omega)) P lambda := rfl
    _ = s.prod (fun i => ProbabilityTheory.mgf (X i) P lambda) := hmgf_sum
    _ <= s.prod (fun i => Real.exp ((K i) ^ 2 * lambda ^ 2)) := by
          refine Finset.prod_le_prod ?_ ?_
          · intro i _hi
            exact ProbabilityTheory.mgf_nonneg
          · intro i hi
            exact (hMGF i hi).2 lambda (hdomain i hi)
    _ = Real.exp (s.sum (fun i => (K i) ^ 2 * lambda ^ 2)) :=
          finset_prod_exp_eq_exp_sum s (fun i => (K i) ^ 2 * lambda ^ 2)
    _ = Real.exp ((s.sum (fun i => (K i) ^ 2)) * lambda ^ 2) := by
          congr 1
          exact (Finset.sum_mul s (fun i => (K i) ^ 2) (lambda ^ 2)).symm

/--
Fintype-facing raw local MGF product bound.

Formula reference: finite-index version of the product-MGF formula
`E exp(lambda sum_i X_i) <= exp((sum_i K_i^2) * lambda^2)` under the domain
`|lambda| <= 1 / Kmax`; see
https://en.wikipedia.org/wiki/Moment-generating_function
-/
theorem centeredSubExponentialMGF_sum_mgf_bound_of_iIndepFun
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {X : ι → RealRandomVariable Omega} {K : ι → Real} {Kmax : Real}
    (hKmax : 0 < Kmax)
    (hKle : ∀ i : ι, K i <= Kmax)
    (hX : ∀ i : ι, IsRealRandomVariable P (X i))
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hMGF : ∀ i : ι, CenteredSubExponentialMGF P (X i) (K i)) :
    ∀ lambda : Real, |lambda| <= 1 / Kmax →
      expect P (fun omega => Real.exp (lambda * ∑ i : ι, X i omega)) <=
        Real.exp ((∑ i : ι, (K i) ^ 2) * lambda ^ 2) := by
  intro lambda hlambda
  exact
    centeredSubExponentialMGF_finset_sum_mgf_bound_of_iIndepFun
      (P := P) (s := Finset.univ) (X := X) (K := K) (Kmax := Kmax)
      hKmax (fun i _hi => hKle i) hX hIndep (fun i _hi => hMGF i)
      lambda hlambda

/--
Fintype-facing raw local MGF bound normalized to the deterministic
`maxScale` and `varianceProxy` vocabulary.

Formula reference: `varianceProxy` records `sum_i K_i^2`, while `maxScale`
records the local-MGF radius via `1 / max_i K_i`; see
https://en.wikipedia.org/wiki/Moment-generating_function
-/
theorem centeredSubExponentialMGF_sum_mgf_bound_of_iIndepFun_maxScale
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {X : ι → RealRandomVariable Omega} {K : ι → Real}
    (hKmax : 0 < maxScale K)
    (hX : ∀ i : ι, IsRealRandomVariable P (X i))
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hMGF : ∀ i : ι, CenteredSubExponentialMGF P (X i) (K i)) :
    ∀ lambda : Real, |lambda| <= 1 / maxScale K →
      expect P (fun omega => Real.exp (lambda * ∑ i : ι, X i omega)) <=
        Real.exp (varianceProxy K * lambda ^ 2) := by
  intro lambda hlambda
  change
    expect P (fun omega => Real.exp (lambda * ∑ i : ι, X i omega)) <=
      Real.exp ((∑ i : ι, (K i) ^ 2) * lambda ^ 2)
  exact
    centeredSubExponentialMGF_sum_mgf_bound_of_iIndepFun
      (P := P) (X := X) (K := K) (Kmax := maxScale K)
      hKmax (fun i => le_maxScale K i (le_of_lt (hMGF i).1))
      hX hIndep hMGF lambda hlambda

/--
Fintype-facing lintegral local MGF bound for independent finite sums,
normalized to `maxScale` and `varianceProxy`.

This is the bridge needed by later Bernstein-style Chernoff arguments: the
lambda domain is controlled by the largest individual scale, while the
quadratic term is controlled by the sum of squared scales.

Formula reference: lintegral version of
`int exp(lambda sum_i X_i) <= exp(varianceProxy K * lambda^2)`, where
`varianceProxy K = sum_i K_i^2` and `|lambda| <= 1 / maxScale K`; see
https://en.wikipedia.org/wiki/Moment-generating_function
-/
theorem centeredSubExponentialMGFLIntegral_sum_mgf_bound_of_iIndepFun_maxScale
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {X : ι → RealRandomVariable Omega} {K : ι → Real}
    (hKmax : 0 < maxScale K)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hMGF : ∀ i : ι, CenteredSubExponentialMGFLIntegral P (X i) (K i)) :
    ∀ lambda : Real, |lambda| <= 1 / maxScale K →
      (∫⁻ omega,
          ENNReal.ofReal (Real.exp (lambda * (∑ i : ι, X i omega))) ∂P) <=
        ENNReal.ofReal (Real.exp (varianceProxy K * lambda ^ 2)) := by
  intro lambda hlambda
  let S : RealRandomVariable Omega := fun omega => ∑ i : ι, X i omega
  let f : RealRandomVariable Omega := fun omega => Real.exp (lambda * S omega)
  have h_raw_mgf :
      expect P (fun omega => Real.exp (lambda * ∑ i : ι, X i omega)) <=
        Real.exp (varianceProxy K * lambda ^ 2) := by
    exact
      centeredSubExponentialMGF_sum_mgf_bound_of_iIndepFun_maxScale
        (P := P) (X := X) (K := K) hKmax
        (fun i => (hMGF i).1) hIndep
        (fun i => centeredSubExponentialMGF_of_centeredSubExponentialMGFLIntegral
          (P := P) (X := X i) (K := K i) (hMGF i))
        lambda hlambda
  have h_each_int :
      ∀ i : ι, i ∈ (Finset.univ : Finset ι) →
        Integrable (fun omega => Real.exp (lambda * X i omega)) P := by
    intro i _hi
    have hKi : 0 < K i := (hMGF i).2.1
    have hdomain_i : |lambda| <= 1 / K i :=
      abs_le_inv_of_le_inv_maxScale K i hKi
        (le_maxScale K i hKi.le) hlambda
    have hfi_nonneg :
        0 ≤ᵐ[P] fun omega => Real.exp (lambda * X i omega) :=
      ae_of_all P fun omega => (Real.exp_pos _).le
    have hfi_meas :
        AEStronglyMeasurable (fun omega => Real.exp (lambda * X i omega)) P := by
      exact ((hMGF i).1.const_mul lambda).exp.aestronglyMeasurable
    have hfi_lintegral_ne_top :
        (∫⁻ omega, ENNReal.ofReal (Real.exp (lambda * X i omega)) ∂P) ≠ ∞ := by
      exact
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top
          ((hMGF i).2.2 lambda hdomain_i)
    exact
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
        hfi_meas hfi_nonneg).mp hfi_lintegral_ne_top
  have hf_int : Integrable f P := by
    have hsum_int :
        Integrable
          (fun omega =>
            Real.exp (lambda * ((∑ i ∈ (Finset.univ : Finset ι), X i) omega))) P := by
      exact
        hIndep.integrable_exp_mul_sum
          (t := lambda) (s := (Finset.univ : Finset ι))
          (fun i => (hMGF i).1) h_each_int
    change Integrable (fun omega => Real.exp (lambda * (∑ i : ι, X i omega))) P
    simpa only [Finset.sum_apply, Finset.mem_univ, true_and] using hsum_int
  have hf_nonneg : 0 ≤ᵐ[P] f :=
    ae_of_all P fun omega => (Real.exp_pos _).le
  change (∫⁻ omega, ENNReal.ofReal (f omega) ∂P) <=
    ENNReal.ofReal (Real.exp (varianceProxy K * lambda ^ 2))
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf_int hf_nonneg]
  exact ENNReal.ofReal_le_ofReal h_raw_mgf

/--
Local MGF bound for a deterministic scalar multiple under the raw
subExponential MGF predicate.  The domain is stated as
`|lambda * c| <= 1 / K` so zero scalar multiples remain explicit.

Formula reference: multiplying a random variable by `c` changes the MGF input
from `lambda` to `lambda * c` and the proxy to `c^2 * K^2`; see
https://en.wikipedia.org/wiki/Moment-generating_function
-/
theorem centeredSubExponentialMGF_const_mul_mgf_bound
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X : RealRandomVariable Omega} {K c lambda : Real}
    (hMGF : CenteredSubExponentialMGF P X K)
    (hdomain : |lambda * c| <= 1 / K) :
    expect P (fun omega => Real.exp (lambda * (c * X omega))) <=
      Real.exp ((c ^ 2 * K ^ 2) * lambda ^ 2) := by
  have h := hMGF.2 (lambda * c) hdomain
  calc
    expect P (fun omega => Real.exp (lambda * (c * X omega)))
        = expect P (fun omega => Real.exp ((lambda * c) * X omega)) := by
            congr 1
            funext omega
            congr 1
            ring
    _ <= Real.exp (K ^ 2 * (lambda * c) ^ 2) := h
    _ = Real.exp ((c ^ 2 * K ^ 2) * lambda ^ 2) := by
            congr 1
            ring

/--
Local lintegral MGF bound for a deterministic scalar multiple under the
proof-facing subExponential MGF predicate.  This is a bound, not a packaged
`CenteredSubExponentialMGFLIntegral` predicate, so the zero-weight case is not
hidden behind a strictly positive scale.

Formula reference: lintegral version of the deterministic scaling formula
with proxy `c^2 * K^2`; see
https://en.wikipedia.org/wiki/Moment-generating_function
-/
theorem centeredSubExponentialMGFLIntegral_const_mul_mgf_bound
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X : RealRandomVariable Omega} {K c lambda : Real}
    (hMGF : CenteredSubExponentialMGFLIntegral P X K)
    (hdomain : |lambda * c| <= 1 / K) :
    (∫⁻ omega, ENNReal.ofReal (Real.exp (lambda * (c * X omega))) ∂P) <=
      ENNReal.ofReal (Real.exp ((c ^ 2 * K ^ 2) * lambda ^ 2)) := by
  have h := hMGF.2.2 (lambda * c) hdomain
  calc
    (∫⁻ omega, ENNReal.ofReal (Real.exp (lambda * (c * X omega))) ∂P)
        = (∫⁻ omega, ENNReal.ofReal (Real.exp ((lambda * c) * X omega)) ∂P) := by
            congr 1
            funext omega
            congr 2
            ring
    _ <= ENNReal.ofReal (Real.exp (K ^ 2 * (lambda * c) ^ 2)) := h
    _ = ENNReal.ofReal (Real.exp ((c ^ 2 * K ^ 2) * lambda ^ 2)) := by
            congr 2
            ring_nf

/--
Fintype-facing lintegral local MGF bound for independent deterministic
weighted sums, normalized to `weightedMaxScale` and `weightedVarianceProxy`.

The domain transfer handles zero weights explicitly; only the original
subExponential scales `K_i` are required to be positive through the input
`CenteredSubExponentialMGFLIntegral` assumptions.

Formula reference: weighted finite sums add proxies
`sum_i c_i^2 K_i^2`, and their local domain is controlled by
`weightedMaxScale`; see
https://en.wikipedia.org/wiki/Moment-generating_function
-/
theorem centeredSubExponentialMGFLIntegral_weighted_sum_mgf_bound_of_iIndepFun_maxScale
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {X : ι -> RealRandomVariable Omega} {K c : ι -> Real}
    (_hB : 0 < weightedMaxScale c K)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hMGF : ∀ i : ι, CenteredSubExponentialMGFLIntegral P (X i) (K i)) :
    ∀ lambda : Real, |lambda| <= 1 / weightedMaxScale c K ->
      (∫⁻ omega,
          ENNReal.ofReal
            (Real.exp (lambda * (∑ i : ι, c i * X i omega))) ∂P) <=
        ENNReal.ofReal
          (Real.exp (weightedVarianceProxy c K * lambda ^ 2)) := by
  intro lambda hlambda
  let Y : ι -> RealRandomVariable Omega := fun i omega => c i * X i omega
  let S : RealRandomVariable Omega := fun omega => ∑ i : ι, c i * X i omega
  let f : RealRandomVariable Omega := fun omega => Real.exp (lambda * S omega)
  have hweightedIndep : ProbabilityTheory.iIndepFun Y P := by
    exact iIndepFun_weighted_of_iIndepFun (P := P) (X := X) c hIndep
  have h_raw_mgf :
      expect P (fun omega => Real.exp (lambda * (∑ i : ι, c i * X i omega))) <=
        Real.exp (weightedVarianceProxy c K * lambda ^ 2) := by
    have hmgf_sum :
        ProbabilityTheory.mgf (fun omega => ∑ i : ι, c i * X i omega) P lambda =
          ∏ i : ι, ProbabilityTheory.mgf (fun omega => c i * X i omega) P lambda := by
      have hsum_eq :
          (∑ i : ι, (fun omega : Omega => c i * X i omega)) =
            (fun omega : Omega => ∑ i : ι, c i * X i omega) := by
        funext omega
        simp only [Finset.sum_apply]
      rw [← hsum_eq]
      exact
        hweightedIndep.mgf_sum (μ := P) (t := lambda)
          (fun i => (hMGF i).1.const_mul (c i)) Finset.univ
    calc
      expect P (fun omega => Real.exp (lambda * (∑ i : ι, c i * X i omega)))
          = ProbabilityTheory.mgf (fun omega => ∑ i : ι, c i * X i omega) P lambda := rfl
      _ = ∏ i : ι, ProbabilityTheory.mgf (fun omega => c i * X i omega) P lambda :=
          hmgf_sum
      _ <= ∏ i : ι, Real.exp (((c i) ^ 2 * (K i) ^ 2) * lambda ^ 2) := by
          refine Finset.prod_le_prod ?_ ?_
          · intro i _hi
            exact ProbabilityTheory.mgf_nonneg
          · intro i _hi
            have hdomain_i : |lambda * c i| <= 1 / K i :=
              abs_mul_le_inv_of_le_weightedMaxScale c K i (hMGF i).2.1 hlambda
            exact
              centeredSubExponentialMGF_const_mul_mgf_bound
                (P := P) (X := X i) (K := K i)
                (c := c i) (lambda := lambda)
                (centeredSubExponentialMGF_of_centeredSubExponentialMGFLIntegral
                  (P := P) (X := X i) (K := K i) (hMGF i))
                hdomain_i
      _ = Real.exp
          (∑ i : ι, ((c i) ^ 2 * (K i) ^ 2) * lambda ^ 2) :=
          finset_prod_exp_eq_exp_sum Finset.univ
            (fun i => ((c i) ^ 2 * (K i) ^ 2) * lambda ^ 2)
      _ = Real.exp (weightedVarianceProxy c K * lambda ^ 2) := by
          congr 1
          exact
            (Finset.sum_mul Finset.univ
              (fun i => (c i) ^ 2 * (K i) ^ 2) (lambda ^ 2)).symm
  have h_each_int :
      ∀ i : ι, i ∈ (Finset.univ : Finset ι) ->
        Integrable (fun omega => Real.exp (lambda * (Y i omega))) P := by
    intro i _hi
    have hdomain_i : |lambda * c i| <= 1 / K i :=
      abs_mul_le_inv_of_le_weightedMaxScale c K i (hMGF i).2.1 hlambda
    have hfi_nonneg :
        0 ≤ᵐ[P] fun omega => Real.exp (lambda * (Y i omega)) :=
      ae_of_all P fun omega => (Real.exp_pos _).le
    have hfi_meas :
        AEStronglyMeasurable (fun omega => Real.exp (lambda * (Y i omega))) P := by
      exact (((hMGF i).1.const_mul (c i)).const_mul lambda).exp.aestronglyMeasurable
    have hfi_lintegral_ne_top :
        (∫⁻ omega, ENNReal.ofReal (Real.exp (lambda * (Y i omega))) ∂P) ≠ ∞ := by
      exact
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top
          (centeredSubExponentialMGFLIntegral_const_mul_mgf_bound
            (P := P) (X := X i) (K := K i)
            (c := c i) (lambda := lambda) (hMGF i) hdomain_i)
    exact
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
        hfi_meas hfi_nonneg).mp hfi_lintegral_ne_top
  have hf_int : Integrable f P := by
    have hsum_int :
        Integrable
          (fun omega => Real.exp (lambda *
            ((∑ i ∈ (Finset.univ : Finset ι), Y i) omega))) P := by
      exact
        hweightedIndep.integrable_exp_mul_sum
          (t := lambda) (s := (Finset.univ : Finset ι))
          (fun i => (hMGF i).1.const_mul (c i)) h_each_int
    change Integrable (fun omega => Real.exp (lambda * (∑ i : ι, c i * X i omega))) P
    simpa only [Y, Finset.sum_apply, Finset.mem_univ, true_and] using hsum_int
  have hf_nonneg : 0 ≤ᵐ[P] f :=
    ae_of_all P fun omega => (Real.exp_pos _).le
  change (∫⁻ omega, ENNReal.ofReal (f omega) ∂P) <=
    ENNReal.ofReal (Real.exp (weightedVarianceProxy c K * lambda ^ 2))
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf_int hf_nonneg]
  exact ENNReal.ofReal_le_ofReal h_raw_mgf

/--
Conservative packaged finite-sum closure for the existing raw predicate.

The resulting scale is `sqrt (sum_i K_i^2)`, so the inherited lambda domain is
`1 / sqrt (sum_i K_i^2)`.  This is stronger than the eventual Bernstein domain
`1 / max_i K_i`, but it fits the current single-scale predicate exactly.

Formula reference: this packages the local MGF proxy `sum_i K_i^2` into the
single scale `sqrt (sum_i K_i^2)`, which forces the stricter domain
`|lambda| <= 1 / sqrt (sum_i K_i^2)`; see
https://en.wikipedia.org/wiki/Moment-generating_function
-/
theorem centeredSubExponentialMGF_finset_sum_of_iIndepFun_of_pos
    {Omega ι : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {s : Finset ι}
    {X : ι → RealRandomVariable Omega} {K : ι → Real}
    (hpos : 0 < s.sum (fun i => (K i) ^ 2))
    (hX : ∀ i : ι, IsRealRandomVariable P (X i))
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hMGF : ∀ i, i ∈ s → CenteredSubExponentialMGF P (X i) (K i)) :
    CenteredSubExponentialMGF P
      (fun omega => s.sum (fun i => X i omega))
      (Real.sqrt (s.sum (fun i => (K i) ^ 2))) := by
  refine ⟨Real.sqrt_pos.2 hpos, ?_⟩
  intro lambda hlambda
  have hsum_nonneg : 0 <= s.sum (fun i => (K i) ^ 2) := by
    exact Finset.sum_nonneg (fun i _hi => sq_nonneg (K i))
  have hKle : ∀ i, i ∈ s → K i <= Real.sqrt (s.sum (fun j => (K j) ^ 2)) := by
    intro i hi
    have hKi_sq_le : (K i) ^ 2 <= s.sum (fun j => (K j) ^ 2) := by
      exact Finset.single_le_sum (fun j _hj => sq_nonneg (K j)) hi
    exact Real.le_sqrt_of_sq_le hKi_sq_le
  have hbound :=
    centeredSubExponentialMGF_finset_sum_mgf_bound_of_iIndepFun
      (P := P) (s := s) (X := X) (K := K)
      (Kmax := Real.sqrt (s.sum (fun i => (K i) ^ 2)))
      (Real.sqrt_pos.2 hpos) hKle hX hIndep hMGF lambda hlambda
  rw [Real.sq_sqrt hsum_nonneg]
  exact hbound

/--
Fintype-facing conservative packaged finite-sum closure.

Formula reference: finite-index version of the packaged scale
`K_sum = sqrt (sum_i K_i^2)` for `sum_i X_i`; see
https://en.wikipedia.org/wiki/Moment-generating_function
-/
theorem centeredSubExponentialMGF_sum_of_iIndepFun_of_pos
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {X : ι → RealRandomVariable Omega} {K : ι → Real}
    (hpos : 0 < ∑ i : ι, (K i) ^ 2)
    (hX : ∀ i : ι, IsRealRandomVariable P (X i))
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hMGF : ∀ i : ι, CenteredSubExponentialMGF P (X i) (K i)) :
    CenteredSubExponentialMGF P
      (fun omega => ∑ i : ι, X i omega)
      (Real.sqrt (∑ i : ι, (K i) ^ 2)) := by
  exact
    centeredSubExponentialMGF_finset_sum_of_iIndepFun_of_pos
      (P := P) (s := Finset.univ) (X := X) (K := K)
      hpos hX hIndep (fun i _hi => hMGF i)

/--
Typed target for the proof-friendly lintegral finite-sum theorem.

This records the intended future bridge: finite independent variables satisfying
`CenteredSubExponentialMGFLIntegral` should yield the same local product bound
under a `Kmax` domain.  It is a `Prop` specification, not a theorem.

Formula reference: the specification is the local product-MGF statement with
domain `|lambda| <= 1 / Kmax` and proxy `sum_i K_i^2`; see
https://en.wikipedia.org/wiki/Moment-generating_function
-/
abbrev centeredSubExponentialMGFLIntegralSumOfIIndepFunStatement
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι]
    (P : Measure Omega)
    (X : ι → RealRandomVariable Omega) (K : ι → Real) (Kmax : Real) : Prop :=
  0 < Kmax →
    (∀ i : ι, K i <= Kmax) →
      ProbabilityTheory.iIndepFun X P →
        (∀ i : ι, CenteredSubExponentialMGFLIntegral P (X i) (K i)) →
          ∀ lambda : Real, |lambda| <= 1 / Kmax →
            (∫⁻ omega,
                ENNReal.ofReal (Real.exp (lambda * (∑ i : ι, X i omega))) ∂P) <=
              ENNReal.ofReal
                (Real.exp ((∑ i : ι, (K i) ^ 2) * lambda ^ 2))

end

end HighDimProb
