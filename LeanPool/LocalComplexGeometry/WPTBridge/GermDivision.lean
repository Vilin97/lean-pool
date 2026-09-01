/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.Germs.Coordinates
import LeanPool.LocalComplexGeometry.WPTBridge.DivisionUniqueness
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Span

/-!
# Weierstrass division on holomorphic germs

This file packages the function-level division and uniqueness theorems as a
canonical operation on the standard germ ring.  A fixed family `a` represents
the coefficients of the prepared divisor; its coefficients are analytic and
vanish at the origin.
-/

open Filter
open scoped BigOperators Topology

namespace LocalComplexGeometry.WPTBridge

open ClassicalComplexWPT

noncomputable section


/-- The prepared polynomial, written in the standard `Fin (n + 1) -> C`
coordinate model used by `HolomorphicGerm`. -/
def preparedPolynomialFunction {n d : ℕ}
    (a : Fin d → Base n → ℂ) : ComplexEuclidean (n + 1) → ℂ :=
  fun x ↦ preparedPolynomial d a (wptAmbientEquiv n x)

theorem analyticAt_preparedPolynomialFunction {n d : ℕ}
    (a : Fin d → Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0) :
    AnalyticAt ℂ (preparedPolynomialFunction a) 0 := by
  have hP : AnalyticAt ℂ (preparedPolynomial d a) 0 := by
    unfold preparedPolynomial
    apply AnalyticAt.add
    · exact analyticAt_snd.pow d
    · refine Finset.analyticAt_fun_sum Finset.univ fun i _ ↦ ?_
      have hai : AnalyticAt ℂ (fun x : Ambient n ↦ a i x.1) 0 :=
        AnalyticAt.comp (g := a i) (f := fun x : Ambient n ↦ x.1)
          (ha i) analyticAt_fst
      exact hai.mul (analyticAt_snd.pow (i : ℕ))
  change AnalyticAt ℂ (preparedPolynomial d a ∘ (wptAmbientEquiv n)) 0
  simpa using
    hP.compContinuousLinearMap (u := (wptAmbientEquiv n :
      ComplexEuclidean (n + 1) →L[ℂ] Ambient n)) (x := 0)

/-- The germ of a fixed prepared polynomial. -/
def preparedPolynomialGerm {n d : ℕ}
    (a : Fin d → Base n → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) 0) :
    HolomorphicGerm (n + 1) :=
  HolomorphicGerm.ofFunction (preparedPolynomialFunction a)
    (analyticAt_preparedPolynomialFunction a ha)

/-- The degree-`< d` polynomial germ with a prescribed coefficient vector. -/
def remainderPolynomialGerm {n d : ℕ}
    (r : Fin d → HolomorphicGerm n) : HolomorphicGerm (n + 1) :=
  ∑ i : Fin d,
    lowerDimensionalInclusion n (r i) * lastCoordinateGerm n ^ (i : ℕ)

/-- A quotient and coefficient vector satisfy Weierstrass division at the
level of germs. -/
def IsPreparedGermDivision {n d : ℕ}
    (a : Fin d → Base n → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (h q : HolomorphicGerm (n + 1)) (r : Fin d → HolomorphicGerm n) : Prop :=
  h = q * preparedPolynomialGerm a ha + remainderPolynomialGerm r

private theorem functionGerm_coe_fin_sum {m d : ℕ}
    (f : Fin d → ComplexEuclidean m → ℂ) :
    (((∑ i : Fin d, f i) : ComplexEuclidean m → ℂ) : FunctionGerm m) =
      ∑ i : Fin d, (f i : FunctionGerm m) := by
  exact map_sum (Filter.Germ.coeRingHom
    (𝓝 (0 : ComplexEuclidean m))) f Finset.univ

/-- Coercion of a polynomial assembled from analytic coefficient
representatives agrees with its pointwise polynomial function. -/
theorem coe_remainderPolynomialGerm_ofFunction {n d : ℕ}
    (r : Fin d → Base n → ℂ) (hr : ∀ i, AnalyticAt ℂ (r i) 0) :
    (remainderPolynomialGerm
        (fun i ↦ HolomorphicGerm.ofFunction (r i) (hr i)) :
      FunctionGerm (n + 1)) =
      ((fun x ↦ ∑ i : Fin d,
        r i (baseProjectionCLM n x) * lastCoordinateCLM n x ^ (i : ℕ)) :
        FunctionGerm (n + 1)) := by
  simp only [remainderPolynomialGerm, Subring.coe_mul, Subring.coe_pow,
    AddSubmonoidClass.coe_finsetSum, holomorphicGermPullbackHom_coe,
    lowerDimensionalInclusion]
  simp_rw [show ∀ i,
    ((HolomorphicGerm.ofFunction (r i) (hr i) : HolomorphicGerm n) :
      FunctionGerm n) = r i from fun _ ↦ rfl]
  simp only [functionGermPullbackHom_coe]
  rw [show (lastCoordinateGerm n : FunctionGerm (n + 1)) =
    lastCoordinateCLM n from rfl]
  let terms : Fin d → ComplexEuclidean (n + 1) → ℂ :=
    fun i ↦ (r i ∘ baseProjectionCLM n) * (lastCoordinateCLM n) ^ (i : ℕ)
  calc
    ∑ i : Fin d,
        ((r i ∘ baseProjectionCLM n) : FunctionGerm (n + 1)) *
          (lastCoordinateCLM n : FunctionGerm (n + 1)) ^ (i : ℕ) =
      ∑ i : Fin d, (terms i : FunctionGerm (n + 1)) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [terms, Filter.Germ.coe_mul, Filter.Germ.coe_pow]
        congr 1
    _ = ((∑ i : Fin d, terms i) :
        ComplexEuclidean (n + 1) → ℂ) :=
      (functionGerm_coe_fin_sum terms).symm
    _ = ((fun x ↦ ∑ i : Fin d,
        r i (baseProjectionCLM n x) * lastCoordinateCLM n x ^ (i : ℕ)) :
        FunctionGerm (n + 1)) := by
      apply congrArg Filter.Germ.ofFun
      funext x
      simp [terms]

/-- Coercion of the full quotient-plus-remainder expression assembled from
analytic representatives. -/
theorem coe_preparedDivisionExpression_ofFunction {n d : ℕ}
    (a : Fin d → Base n → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (q : ComplexEuclidean (n + 1) → ℂ) (hq : AnalyticAt ℂ q 0)
    (r : Fin d → Base n → ℂ) (hr : ∀ i, AnalyticAt ℂ (r i) 0) :
    ((HolomorphicGerm.ofFunction q hq * preparedPolynomialGerm a ha +
        remainderPolynomialGerm
          (fun i ↦ HolomorphicGerm.ofFunction (r i) (hr i)) :
      HolomorphicGerm (n + 1)) : FunctionGerm (n + 1)) =
      ((fun x ↦ q x * preparedPolynomialFunction a x +
        ∑ i : Fin d,
          r i (baseProjectionCLM n x) * lastCoordinateCLM n x ^ (i : ℕ)) :
        FunctionGerm (n + 1)) := by
  simp only [Subring.coe_add, Subring.coe_mul]
  rw [show ((HolomorphicGerm.ofFunction q hq : HolomorphicGerm (n + 1)) :
    FunctionGerm (n + 1)) = q from rfl]
  rw [show (preparedPolynomialGerm a ha : FunctionGerm (n + 1)) =
    preparedPolynomialFunction a from rfl]
  rw [coe_remainderPolynomialGerm_ofFunction r hr]
  rw [← Filter.Germ.coe_mul, ← Filter.Germ.coe_add]
  apply congrArg Filter.Germ.ofFun
  rfl

/-- Every holomorphic germ admits a quotient and degree-`< d` remainder by a
fixed prepared polynomial. -/
theorem exists_preparedGermDivision {n d : ℕ}
    (a : Fin d → Base n → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0) (h : HolomorphicGerm (n + 1)) :
    ∃ (q : HolomorphicGerm (n + 1)) (r : Fin d → HolomorphicGerm n),
      IsPreparedGermDivision a ha h q r := by
  obtain ⟨f, hf, hrep⟩ := HolomorphicGerm.exists_rep h
  let fWPT : Ambient n → ℂ := fun x ↦ f ((wptAmbientEquiv n).symm x)
  have hfWPT : AnalyticAt ℂ fWPT 0 := by
    change AnalyticAt ℂ (f ∘ (wptAmbientEquiv n).symm) 0
    have hf' : AnalyticAt ℂ f ((wptAmbientEquiv n).symm 0) := by
      rw [map_zero]
      exact hf
    simpa using hf'.compContinuousLinearMap
      (u := ((wptAmbientEquiv n).symm :
        Ambient n →L[ℂ] ComplexEuclidean (n + 1))) (x := 0)
  obtain ⟨q, r, hq, hr, hfactor⟩ :=
    exists_analyticWeierstrassDivision fWPT hfWPT a ha ha0
  let qStandard : ComplexEuclidean (n + 1) → ℂ :=
    fun x ↦ q (wptAmbientEquiv n x)
  have hqStandard : AnalyticAt ℂ qStandard 0 := by
    change AnalyticAt ℂ (q ∘ (wptAmbientEquiv n)) 0
    simpa using hq.compContinuousLinearMap
      (u := (wptAmbientEquiv n :
        ComplexEuclidean (n + 1) →L[ℂ] Ambient n)) (x := 0)
  let qGerm : HolomorphicGerm (n + 1) :=
    HolomorphicGerm.ofFunction qStandard hqStandard
  let rGerm : Fin d → HolomorphicGerm n :=
    fun i ↦ HolomorphicGerm.ofFunction (r i) (hr i)
  have hequiv : Tendsto (wptAmbientEquiv n) (𝓝 0) (𝓝 0) := by
    have hc : Tendsto (wptAmbientEquiv n) (𝓝 0)
        (𝓝 (wptAmbientEquiv n 0)) :=
      (wptAmbientEquiv n).continuous.continuousAt
    rw [map_zero] at hc
    exact hc
  have hfactorStandard : f =ᶠ[𝓝 0] fun x ↦
      qStandard x * preparedPolynomialFunction a x +
        ∑ i : Fin d, r i (wptAmbientEquiv n x).1 *
          (wptAmbientEquiv n x).2 ^ (i : ℕ) := by
    have hfactor' := hfactor.comp_tendsto hequiv
    filter_upwards [hfactor'] with x hx
    change f ((wptAmbientEquiv n).symm (wptAmbientEquiv n x)) =
      qStandard x * preparedPolynomialFunction a x +
        ∑ i : Fin d, r i (wptAmbientEquiv n x).1 *
          (wptAmbientEquiv n x).2 ^ (i : ℕ) at hx
    rw [(wptAmbientEquiv n).symm_apply_apply] at hx
    exact hx
  refine ⟨qGerm, rGerm, ?_⟩
  unfold IsPreparedGermDivision
  apply Subtype.ext
  rw [← hrep]
  simp only [remainderPolynomialGerm, Subring.coe_add, Subring.coe_mul,
    Subring.coe_pow, AddSubmonoidClass.coe_finsetSum]
  change (f : FunctionGerm (n + 1)) =
    (qGerm : FunctionGerm (n + 1)) *
      (preparedPolynomialGerm a ha : FunctionGerm (n + 1)) +
      ∑ i : Fin d,
        (lowerDimensionalInclusion n (rGerm i) : FunctionGerm (n + 1)) *
          (lastCoordinateGerm n : FunctionGerm (n + 1)) ^ (i : ℕ)
  rw [show (qGerm : FunctionGerm (n + 1)) = qStandard from rfl]
  rw [show (preparedPolynomialGerm a ha : FunctionGerm (n + 1)) =
    preparedPolynomialFunction a from rfl]
  simp only [holomorphicGermPullbackHom_coe, lowerDimensionalInclusion]
  simp_rw [show ∀ i, (rGerm i : FunctionGerm n) = r i from fun _ ↦ rfl]
  simp only [functionGermPullbackHom_coe]
  rw [show (lastCoordinateGerm n : FunctionGerm (n + 1)) =
    lastCoordinateCLM n from rfl]
  have hfactorStandard' : f =ᶠ[𝓝 0]
      qStandard * preparedPolynomialFunction a +
        ∑ i : Fin d,
          (r i ∘ baseProjectionCLM n) * (lastCoordinateCLM n) ^ (i : ℕ) := by
    filter_upwards [hfactorStandard] with x hx
    simpa using hx
  have hgerm := Filter.Germ.coe_eq.mpr hfactorStandard'
  have hsum :
      (((∑ i : Fin d,
          (r i ∘ baseProjectionCLM n) * (lastCoordinateCLM n) ^ (i : ℕ)) :
          ComplexEuclidean (n + 1) → ℂ) : FunctionGerm (n + 1)) =
        ∑ i : Fin d,
          ((r i ∘ baseProjectionCLM n) : FunctionGerm (n + 1)) *
            ((lastCoordinateCLM n : ComplexEuclidean (n + 1) → ℂ) :
              FunctionGerm (n + 1)) ^ (i : ℕ) := by
    calc
      _ = ∑ i : Fin d,
          (((r i ∘ baseProjectionCLM n) *
            (lastCoordinateCLM n) ^ (i : ℕ) :
              ComplexEuclidean (n + 1) → ℂ) : FunctionGerm (n + 1)) := by
          exact map_sum (Filter.Germ.coeRingHom
            (𝓝 (0 : ComplexEuclidean (n + 1))))
              (fun i : Fin d ↦
                (r i ∘ baseProjectionCLM n) *
                  (lastCoordinateCLM n) ^ (i : ℕ)) Finset.univ
      _ = _ := by
        simp only [Filter.Germ.coe_mul, Filter.Germ.coe_pow]
  simp only [Filter.Germ.coe_add, Filter.Germ.coe_mul] at hgerm
  rw [hsum] at hgerm
  convert hgerm using 1
  congr 1

/-- Germ-level uniqueness.  In particular, the quotient and coefficient
germs do not depend on any analytic representatives used to construct them. -/
theorem preparedGermDivision_unique {n d : ℕ}
    (a : Fin d → Base n → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0)
    (h q q' : HolomorphicGerm (n + 1))
    (r r' : Fin d → HolomorphicGerm n)
    (hdivision : IsPreparedGermDivision a ha h q r)
    (hdivision' : IsPreparedGermDivision a ha h q' r') :
    q = q' ∧ r = r' := by
  obtain ⟨qf, hqf, hqrep⟩ := HolomorphicGerm.exists_rep q
  obtain ⟨qf', hqf', hqrep'⟩ := HolomorphicGerm.exists_rep q'
  choose rf hrf hrfrep using fun i ↦ HolomorphicGerm.exists_rep (r i)
  choose rf' hrf' hrfrep' using fun i ↦ HolomorphicGerm.exists_rep (r' i)
  have hqGerm : HolomorphicGerm.ofFunction qf hqf = q := by
    apply Subtype.ext
    exact hqrep
  have hqGerm' : HolomorphicGerm.ofFunction qf' hqf' = q' := by
    apply Subtype.ext
    exact hqrep'
  have hrGerm : (fun i ↦ HolomorphicGerm.ofFunction (rf i) (hrf i)) = r := by
    funext i
    apply Subtype.ext
    exact hrfrep i
  have hrGerm' : (fun i ↦ HolomorphicGerm.ofFunction (rf' i) (hrf' i)) = r' := by
    funext i
    apply Subtype.ext
    exact hrfrep' i
  have hdecomposition :
      q * preparedPolynomialGerm a ha + remainderPolynomialGerm r =
        q' * preparedPolynomialGerm a ha + remainderPolynomialGerm r' :=
    hdivision.symm.trans hdivision'
  rw [← hqGerm, ← hqGerm', ← hrGerm, ← hrGerm'] at hdecomposition
  have hdecompositionCoe := congrArg
    (fun g : HolomorphicGerm (n + 1) ↦ (g : FunctionGerm (n + 1)))
    hdecomposition
  rw [coe_preparedDivisionExpression_ofFunction a ha qf hqf rf hrf,
    coe_preparedDivisionExpression_ofFunction a ha qf' hqf' rf' hrf']
      at hdecompositionCoe
  have hstandard := Filter.Germ.coe_eq.mp hdecompositionCoe
  let qWPT : Ambient n → ℂ := fun x ↦ qf ((wptAmbientEquiv n).symm x)
  let qWPT' : Ambient n → ℂ := fun x ↦ qf' ((wptAmbientEquiv n).symm x)
  have hqWPT : AnalyticAt ℂ qWPT 0 := by
    change AnalyticAt ℂ (qf ∘ (wptAmbientEquiv n).symm) 0
    have hqf0 : AnalyticAt ℂ qf ((wptAmbientEquiv n).symm 0) := by
      rw [map_zero]
      exact hqf
    simpa using hqf0.compContinuousLinearMap
      (u := ((wptAmbientEquiv n).symm :
        Ambient n →L[ℂ] ComplexEuclidean (n + 1))) (x := 0)
  have hqWPT' : AnalyticAt ℂ qWPT' 0 := by
    change AnalyticAt ℂ (qf' ∘ (wptAmbientEquiv n).symm) 0
    have hqf0 : AnalyticAt ℂ qf' ((wptAmbientEquiv n).symm 0) := by
      rw [map_zero]
      exact hqf'
    simpa using hqf0.compContinuousLinearMap
      (u := ((wptAmbientEquiv n).symm :
        Ambient n →L[ℂ] ComplexEuclidean (n + 1))) (x := 0)
  have hequivSymm : Tendsto (wptAmbientEquiv n).symm (𝓝 0) (𝓝 0) := by
    have hc : Tendsto (wptAmbientEquiv n).symm (𝓝 0)
        (𝓝 ((wptAmbientEquiv n).symm 0)) :=
      (wptAmbientEquiv n).symm.continuous.continuousAt
    rw [map_zero] at hc
    exact hc
  have hWPT : (fun x : Ambient n ↦
      qWPT x * preparedPolynomial d a x +
        ∑ i : Fin d, rf i x.1 * x.2 ^ (i : ℕ)) =ᶠ[𝓝 0]
      fun x ↦ qWPT' x * preparedPolynomial d a x +
        ∑ i : Fin d, rf' i x.1 * x.2 ^ (i : ℕ) := by
    have hstandard' := hstandard.comp_tendsto hequivSymm
    filter_upwards [hstandard'] with x hx
    change
      qf ((wptAmbientEquiv n).symm x) *
          preparedPolynomialFunction a ((wptAmbientEquiv n).symm x) +
          ∑ i : Fin d,
            rf i (baseProjectionCLM n ((wptAmbientEquiv n).symm x)) *
              lastCoordinateCLM n ((wptAmbientEquiv n).symm x) ^ (i : ℕ) =
        qf' ((wptAmbientEquiv n).symm x) *
          preparedPolynomialFunction a ((wptAmbientEquiv n).symm x) +
          ∑ i : Fin d,
            rf' i (baseProjectionCLM n ((wptAmbientEquiv n).symm x)) *
              lastCoordinateCLM n ((wptAmbientEquiv n).symm x) ^ (i : ℕ) at hx
    simpa [qWPT, qWPT', preparedPolynomialFunction, baseProjectionCLM,
      lastCoordinateCLM] using hx
  let dividend : Ambient n → ℂ := fun x ↦
    qWPT x * preparedPolynomial d a x +
      ∑ i : Fin d, rf i x.1 * x.2 ^ (i : ℕ)
  have hunique := analyticWeierstrassDivision_unique
    dividend qWPT qWPT' rf rf' a hqWPT hqWPT' hrf hrf' ha ha0
    (Filter.Eventually.of_forall fun _ ↦ rfl) hWPT
  have hequiv : Tendsto (wptAmbientEquiv n) (𝓝 0) (𝓝 0) := by
    have hc : Tendsto (wptAmbientEquiv n) (𝓝 0)
        (𝓝 (wptAmbientEquiv n 0)) :=
      (wptAmbientEquiv n).continuous.continuousAt
    rw [map_zero] at hc
    exact hc
  constructor
  · have hqStandard := hunique.1.comp_tendsto hequiv
    have hqFunctions : qf =ᶠ[𝓝 0] qf' := by
      filter_upwards [hqStandard] with x hx
      change qf ((wptAmbientEquiv n).symm (wptAmbientEquiv n x)) =
        qf' ((wptAmbientEquiv n).symm (wptAmbientEquiv n x)) at hx
      rw [(wptAmbientEquiv n).symm_apply_apply] at hx
      exact hx
    have hchosen :
        HolomorphicGerm.ofFunction qf hqf =
          HolomorphicGerm.ofFunction qf' hqf' :=
      Subtype.ext (Filter.Germ.coe_eq.mpr hqFunctions)
    exact hqGerm.symm.trans (hchosen.trans hqGerm')
  · apply funext
    intro i
    have hrFunctions := hunique.2 i
    have hchosen :
        HolomorphicGerm.ofFunction (rf i) (hrf i) =
          HolomorphicGerm.ofFunction (rf' i) (hrf' i) :=
      Subtype.ext (Filter.Germ.coe_eq.mpr hrFunctions)
    exact (congrFun hrGerm i).symm.trans (hchosen.trans (congrFun hrGerm' i))

/-! ## Canonical quotient and remainder -/

/-- The canonical quotient, chosen from existence and made intrinsic by
`preparedGermDivision_unique`. -/
def preparedGermDivisionQuotient {n d : ℕ}
    (a : Fin d → Base n → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0) (h : HolomorphicGerm (n + 1)) :
    HolomorphicGerm (n + 1) :=
  Classical.choose (exists_preparedGermDivision a ha ha0 h)

/-- The canonical coefficient vector of the degree-`< d` remainder. -/
def preparedGermDivisionRemainder {n d : ℕ}
    (a : Fin d → Base n → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0) (h : HolomorphicGerm (n + 1)) :
    Fin d → HolomorphicGerm n :=
  Classical.choose
    (Classical.choose_spec (exists_preparedGermDivision a ha ha0 h))

theorem preparedGermDivision_spec {n d : ℕ}
    (a : Fin d → Base n → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0) (h : HolomorphicGerm (n + 1)) :
    IsPreparedGermDivision a ha h
      (preparedGermDivisionQuotient a ha ha0 h)
      (preparedGermDivisionRemainder a ha ha0 h) :=
  Classical.choose_spec
    (Classical.choose_spec (exists_preparedGermDivision a ha ha0 h))

theorem preparedGermDivision_eq_of_isDivision {n d : ℕ}
    (a : Fin d → Base n → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0) (h q : HolomorphicGerm (n + 1))
    (r : Fin d → HolomorphicGerm n)
    (hdivision : IsPreparedGermDivision a ha h q r) :
    preparedGermDivisionQuotient a ha ha0 h = q ∧
      preparedGermDivisionRemainder a ha ha0 h = r :=
  preparedGermDivision_unique a ha ha0 h _ _ _ _
    (preparedGermDivision_spec a ha ha0 h) hdivision

@[simp]
theorem remainderPolynomialGerm_zero {n d : ℕ} :
    remainderPolynomialGerm (0 : Fin d → HolomorphicGerm n) = 0 := by
  simp [remainderPolynomialGerm]

theorem remainderPolynomialGerm_add {n d : ℕ}
    (r s : Fin d → HolomorphicGerm n) :
    remainderPolynomialGerm (r + s) =
      remainderPolynomialGerm r + remainderPolynomialGerm s := by
  simp only [remainderPolynomialGerm, Pi.add_apply, map_add, add_mul,
    Finset.sum_add_distrib]

theorem remainderPolynomialGerm_smul {n d : ℕ}
    (c : HolomorphicGerm n) (r : Fin d → HolomorphicGerm n) :
    remainderPolynomialGerm (c • r) = c • remainderPolynomialGerm r := by
  simp only [remainderPolynomialGerm, Pi.smul_apply, smul_eq_mul,
    map_mul, holomorphicGermSucc_smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

@[simp]
theorem preparedGermDivisionRemainder_zero {n d : ℕ}
    (a : Fin d → Base n → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0) :
    preparedGermDivisionRemainder a ha ha0 0 = 0 := by
  have hzero : IsPreparedGermDivision a ha (0 : HolomorphicGerm (n + 1)) 0
      (0 : Fin d → HolomorphicGerm n) := by
    simp [IsPreparedGermDivision]
  exact (preparedGermDivision_eq_of_isDivision a ha ha0 0 0 0 hzero).2

theorem preparedGermDivisionRemainder_add {n d : ℕ}
    (a : Fin d → Base n → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0) (h k : HolomorphicGerm (n + 1)) :
    preparedGermDivisionRemainder a ha ha0 (h + k) =
      preparedGermDivisionRemainder a ha ha0 h +
        preparedGermDivisionRemainder a ha ha0 k := by
  let qh := preparedGermDivisionQuotient a ha ha0 h
  let qk := preparedGermDivisionQuotient a ha ha0 k
  let rh := preparedGermDivisionRemainder a ha ha0 h
  let rk := preparedGermDivisionRemainder a ha ha0 k
  have hh := preparedGermDivision_spec a ha ha0 h
  have hk := preparedGermDivision_spec a ha ha0 k
  have hadd : IsPreparedGermDivision a ha (h + k) (qh + qk) (rh + rk) := by
    unfold IsPreparedGermDivision at hh hk ⊢
    rw [hh, hk, remainderPolynomialGerm_add]
    ring
  exact (preparedGermDivision_eq_of_isDivision a ha ha0 (h + k)
    (qh + qk) (rh + rk) hadd).2

theorem preparedGermDivisionRemainder_smul {n d : ℕ}
    (a : Fin d → Base n → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0) (c : HolomorphicGerm n)
    (h : HolomorphicGerm (n + 1)) :
    preparedGermDivisionRemainder a ha ha0 (c • h) =
      c • preparedGermDivisionRemainder a ha ha0 h := by
  let q := preparedGermDivisionQuotient a ha ha0 h
  let r := preparedGermDivisionRemainder a ha ha0 h
  have hh := preparedGermDivision_spec a ha ha0 h
  have hsmul : IsPreparedGermDivision a ha (c • h) (c • q) (c • r) := by
    unfold IsPreparedGermDivision at hh ⊢
    rw [hh, remainderPolynomialGerm_smul]
    simp only [holomorphicGermSucc_smul_eq_mul]
    ring
  exact (preparedGermDivision_eq_of_isDivision a ha ha0 (c • h)
    (c • q) (c • r) hsmul).2

/-- The base-linear coefficient-remainder map supplied by analytic
Weierstrass division. -/
def preparedGermDivisionRemainderLinearMap {n d : ℕ}
    (a : Fin d → Base n → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0) :
    HolomorphicGerm (n + 1) →ₗ[HolomorphicGerm n]
      (Fin d → HolomorphicGerm n) where
  toFun := preparedGermDivisionRemainder a ha ha0
  map_add' := preparedGermDivisionRemainder_add a ha ha0
  map_smul' := preparedGermDivisionRemainder_smul a ha ha0

/-! ## Kernel and principal divisibility -/

theorem preparedGermDivisionRemainder_eq_zero_iff {n d : ℕ}
    (a : Fin d → Base n → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0) (h : HolomorphicGerm (n + 1)) :
    preparedGermDivisionRemainder a ha ha0 h = 0 ↔
      ∃ q : HolomorphicGerm (n + 1),
        h = q * preparedPolynomialGerm a ha := by
  constructor
  · intro hremainder
    refine ⟨preparedGermDivisionQuotient a ha ha0 h, ?_⟩
    have hspec := preparedGermDivision_spec a ha ha0 h
    unfold IsPreparedGermDivision at hspec
    rw [hremainder, remainderPolynomialGerm_zero, add_zero] at hspec
    exact hspec
  · rintro ⟨q, hq⟩
    have hdivision : IsPreparedGermDivision a ha h q
        (0 : Fin d → HolomorphicGerm n) := by
      unfold IsPreparedGermDivision
      rw [hq, remainderPolynomialGerm_zero, add_zero]
    exact (preparedGermDivision_eq_of_isDivision a ha ha0 h q 0 hdivision).2

theorem preparedGermDivisionRemainder_eq_zero_iff_mem_span {n d : ℕ}
    (a : Fin d → Base n → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0) (h : HolomorphicGerm (n + 1)) :
    preparedGermDivisionRemainder a ha ha0 h = 0 ↔
      h ∈ Ideal.span ({preparedPolynomialGerm a ha} :
        Set (HolomorphicGerm (n + 1))) := by
  rw [preparedGermDivisionRemainder_eq_zero_iff a ha ha0 h,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, hq.symm⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, hq.symm⟩

/-- The exact kernel statement needed by Rückert's remainder-module
induction: the kernel is the principal ideal generated by the prepared
polynomial, viewed as a module over lower-dimensional germs. -/
theorem preparedGermDivisionRemainderLinearMap_ker {n d : ℕ}
    (a : Fin d → Base n → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0) :
    LinearMap.ker (preparedGermDivisionRemainderLinearMap a ha ha0) =
      (Ideal.span ({preparedPolynomialGerm a ha} :
        Set (HolomorphicGerm (n + 1)))).restrictScalars (HolomorphicGerm n) := by
  ext h
  change preparedGermDivisionRemainder a ha ha0 h = 0 ↔
    h ∈ Ideal.span ({preparedPolynomialGerm a ha} :
      Set (HolomorphicGerm (n + 1)))
  exact preparedGermDivisionRemainder_eq_zero_iff_mem_span a ha ha0 h

theorem preparedGermDivisionRemainderLinearMap_ker_le {n d : ℕ}
    (a : Fin d → Base n → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0) :
    LinearMap.ker (preparedGermDivisionRemainderLinearMap a ha ha0) ≤
      (Ideal.span ({preparedPolynomialGerm a ha} :
        Set (HolomorphicGerm (n + 1)))).restrictScalars (HolomorphicGerm n) :=
  (preparedGermDivisionRemainderLinearMap_ker a ha ha0).le

/-- Every coefficient vector already is the remainder of its degree-`< d`
polynomial germ. -/
theorem preparedGermDivisionRemainderLinearMap_surjective {n d : ℕ}
    (a : Fin d → Base n → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0) :
    Function.Surjective (preparedGermDivisionRemainderLinearMap a ha ha0) := by
  intro r
  refine ⟨remainderPolynomialGerm r, ?_⟩
  have hdivision : IsPreparedGermDivision a ha (remainderPolynomialGerm r)
      0 r := by
    simp [IsPreparedGermDivision]
  exact (preparedGermDivision_eq_of_isDivision a ha ha0
    (remainderPolynomialGerm r) 0 r hdivision).2

end

end LocalComplexGeometry.WPTBridge
