/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveSupportDeterminant
public import Mathlib.Tactic

/-!
# The logarithmic Gauss direction of a plane curve

The logarithmic partial `X_i * ∂_i f` has exactly the same monomial
support as a subpolynomial of `f`.  Consequently a scalar relation between
the two logarithmic partials forces every support exponent to lie on one
affine line in the constant field.

If the support has a nonzero rank-two determinant and the characteristic is
larger than the public Euler budget, that determinant stays nonzero in the
constant field.  Hence the logarithmic Gauss ratio cannot be constant on the
curve.  This isolates the high-characteristic input needed by the
logarithmic-Gauss route to the powered-image index bound.
-/

@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section

/-- The logarithmic partial derivative `X_i * ∂_i f`. -/
def planeCurveLogarithmicPDeriv {K : Type*} [Field K]
    (i : Fin 2) (f : MvPolynomial (Fin 2) K) :=
  MvPolynomial.X i * MvPolynomial.pderiv i f

theorem coeff_planeCurveLogarithmicPDeriv
    {K : Type*} [Field K] (i : Fin 2)
    (f : MvPolynomial (Fin 2) K) (m : Fin 2 →₀ ℕ) :
    (planeCurveLogarithmicPDeriv i f).coeff m =
      (m i : K) * f.coeff m := by
  induction f using MvPolynomial.induction_on' with
  | add p q hp hq =>
      simp only [planeCurveLogarithmicPDeriv, map_add, mul_add,
        AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
      change (planeCurveLogarithmicPDeriv i p).coeff m +
          (planeCurveLogarithmicPDeriv i q).coeff m = _
      rw [hp, hq]
  | monomial n a =>
      rw [planeCurveLogarithmicPDeriv,
        MvPolynomial.X_mul_pderiv_monomial]
      simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial]
      split_ifs with h
      · subst n
        simp [nsmul_eq_mul]
      · simp

/-- A constant linear combination of the two logarithmic partials. -/
def planeCurveLogarithmicDirection {K : Type*} [Field K]
    (a b : K) (f : MvPolynomial (Fin 2) K) :=
  MvPolynomial.C a * planeCurveLogarithmicPDeriv 0 f +
    MvPolynomial.C b * planeCurveLogarithmicPDeriv 1 f

theorem coeff_planeCurveLogarithmicDirection
    {K : Type*} [Field K] (a b : K)
    (f : MvPolynomial (Fin 2) K) (m : Fin 2 →₀ ℕ) :
    (planeCurveLogarithmicDirection a b f).coeff m =
      (a * (m 0 : K) + b * (m 1 : K)) * f.coeff m := by
  simp only [planeCurveLogarithmicDirection, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    MvPolynomial.coeff_C_mul, coeff_planeCurveLogarithmicPDeriv]
  ring

theorem support_planeCurveLogarithmicDirection_subset
    {K : Type*} [Field K] (a b : K)
    (f : MvPolynomial (Fin 2) K) :
    (planeCurveLogarithmicDirection a b f).support ⊆ f.support := by
  intro m hm
  rw [MvPolynomial.mem_support_iff] at hm ⊢
  rw [coeff_planeCurveLogarithmicDirection] at hm
  exact right_ne_zero_of_mul hm

theorem degreeOf_planeCurveLogarithmicDirection_le
    {K : Type*} [Field K] (a b : K)
    (f : MvPolynomial (Fin 2) K) (i : Fin 2) :
    MvPolynomial.degreeOf i (planeCurveLogarithmicDirection a b f) ≤
      MvPolynomial.degreeOf i f := by
  rw [MvPolynomial.degreeOf_le_iff]
  intro m hm
  exact MvPolynomial.le_degreeOf_of_mem_support i
    (support_planeCurveLogarithmicDirection_subset a b f hm)

private theorem eq_C_coeff_zero_of_degreeOf_zero
    {K : Type*} [Field K] (g : MvPolynomial (Fin 2) K)
    (h0 : MvPolynomial.degreeOf 0 g = 0)
    (h1 : MvPolynomial.degreeOf 1 g = 0) :
    g = MvPolynomial.C (g.coeff 0) := by
  ext m
  by_cases hm : m = 0
  · subst m
    simp
  · have hcoordinate : m 0 ≠ 0 ∨ m 1 ≠ 0 := by
      by_contra h
      push Not at h
      apply hm
      ext i
      fin_cases i <;> simp_all
    have hmnot : m ∉ g.support := by
      intro hmem
      rcases hcoordinate with hm0 | hm1
      · have := MvPolynomial.le_degreeOf_of_mem_support 0 hmem
        omega
      · have := MvPolynomial.le_degreeOf_of_mem_support 1 hmem
        omega
    rw [MvPolynomial.notMem_support_iff.mp hmnot]
    have hm' : (0 : Fin 2 →₀ ℕ) ≠ m := Ne.symm hm
    simp [hm']

/-- A nonzero logarithmic direction divisible by `f` is only a constant
multiple of `f`; the coordinate degree bounds force the quotient to be
constant. -/
theorem planeCurveLogarithmicDirection_eq_C_mul_of_dvd
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hf : f ≠ 0) (a b : K)
    (hQ : planeCurveLogarithmicDirection a b f ≠ 0)
    (hdvd : f ∣ planeCurveLogarithmicDirection a b f) :
    ∃ d : K, planeCurveLogarithmicDirection a b f = MvPolynomial.C d * f := by
  obtain ⟨g, hg⟩ := hdvd
  have hg0 : g ≠ 0 := by
    intro hzero
    apply hQ
    rw [hg, hzero, mul_zero]
  have hdegree0 := degreeOf_planeCurveLogarithmicDirection_le a b f 0
  have hdegree1 := degreeOf_planeCurveLogarithmicDirection_le a b f 1
  rw [hg, MvPolynomial.degreeOf_mul_eq hf hg0] at hdegree0 hdegree1
  have hgDegree0 : MvPolynomial.degreeOf 0 g = 0 := by omega
  have hgDegree1 : MvPolynomial.degreeOf 1 g = 0 := by omega
  let d := g.coeff 0
  have hgC : g = MvPolynomial.C d :=
    eq_C_coeff_zero_of_degreeOf_zero g hgDegree0 hgDegree1
  refine ⟨d, ?_⟩
  rw [hg, hgC, mul_comm]

private theorem supportDifferenceDet_cast_eq_zero_of_logWeights_eq
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    {r s t : Fin 2 →₀ ℕ} (_hr : r ∈ f.support)
    (hs : s ∈ f.support) (ht : t ∈ f.support)
    (c : K)
    (hweights : ∀ m ∈ f.support,
      (m 0 : K) - c * (m 1 : K) =
        (r 0 : K) - c * (r 1 : K)) :
    (planeCurveSupportDifferenceDet r s t : K) = 0 := by
  have hs' := hweights s hs
  have ht' := hweights t ht
  dsimp only [planeCurveSupportDifferenceDet]
  push_cast
  linear_combination
    ((t 1 : K) - (r 1 : K)) * hs' -
      ((s 1 : K) - (r 1 : K)) * ht'

private theorem logWeights_eq_of_logarithmicPDeriv_eq
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (c d : K)
    (hrelation : planeCurveLogarithmicPDeriv 0 f =
      MvPolynomial.C c * planeCurveLogarithmicPDeriv 1 f +
        MvPolynomial.C d * f) :
    ∀ m ∈ f.support,
      (m 0 : K) - c * (m 1 : K) = d := by
  intro m hm
  have hcoeff := congrArg (fun p ↦ p.coeff m) hrelation
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_C_mul,
    coeff_planeCurveLogarithmicPDeriv] at hcoeff
  have hm0 : f.coeff m ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hm
  apply (mul_right_cancel₀ hm0)
  linear_combination hcoeff

theorem planeCurveSupportDifferenceDet_cast_ne_zero_of_lt_char
    {K : Type*} [Field K] {p : ℕ} [CharP K p]
    {r s t : Fin 2 →₀ ℕ}
    (hdet : planeCurveSupportDifferenceDet r s t ≠ 0)
    (hlt : (planeCurveSupportDifferenceDet r s t).natAbs < p) :
    (planeCurveSupportDifferenceDet r s t : K) ≠ 0 := by
  intro hzero
  have hdvd : (p : ℤ) ∣ planeCurveSupportDifferenceDet r s t :=
    (CharP.intCast_eq_zero_iff K p _).mp hzero
  have hp0 : (p : ℤ) ≠ 0 := by
    intro hp
    have : p = 0 := by exact_mod_cast hp
    subst p
    simp at hlt
  have hle := Int.natAbs_le_of_dvd_ne_zero hdvd hdet
  simpa using (hle.trans_lt hlt)

/-- Rank-two support excludes a scalar logarithmic-Gauss relation in
characteristic larger than the support determinant budget. -/
theorem no_logarithmicPDeriv_scalar_relation_of_supportRankTwo
    {K : Type*} [Field K] {p : ℕ} [CharP K p]
    {f : MvPolynomial (Fin 2) K}
    (hrank : PlaneCurveSupportHasRankTwo f)
    (hlarge : 2 * MvPolynomial.degreeOf 0 f *
      MvPolynomial.degreeOf 1 f < p) :
    ¬ ∃ c d : K, planeCurveLogarithmicPDeriv 0 f =
      MvPolynomial.C c * planeCurveLogarithmicPDeriv 1 f +
        MvPolynomial.C d * f := by
  rintro ⟨c, d, hrelation⟩
  obtain ⟨r, s, t, hr, hs, ht, hdet⟩ := hrank
  have hweights := logWeights_eq_of_logarithmicPDeriv_eq c d hrelation
  have hcastZero : (planeCurveSupportDifferenceDet r s t : K) = 0 :=
    supportDifferenceDet_cast_eq_zero_of_logWeights_eq hr hs ht c
      (by
        intro m hm
        rw [hweights m hm, hweights r hr])
  have hdetBound :=
    natAbs_planeCurveSupportDifferenceDet_le_twice_bidegree hr hs ht
  have hcastNe : (planeCurveSupportDifferenceDet r s t : K) ≠ 0 :=
    planeCurveSupportDifferenceDet_cast_ne_zero_of_lt_char hdet
      (hdetBound.trans_lt hlarge)
  exact hcastNe hcastZero

/-- On an irreducible curve with rank-two support, no constant can be the
logarithmic Gauss ratio in the high-characteristic range. -/
theorem eval_planeCurveLogarithmicDirection_ne_zero_of_supportRankTwo
    {K : Type*} [Field K] {p : ℕ} [CharP K p]
    {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f)
    (hrank : PlaneCurveSupportHasRankTwo f)
    (hlarge : 2 * MvPolynomial.degreeOf 0 f *
      MvPolynomial.degreeOf 1 f < p)
    (c : K) :
    letI := planeCurveCoordinateRing_isDomain hf
    MvPolynomial.eval₂ (algebraMap K (PlaneCurveFunctionField f))
      (planeCurveFunction f)
      (planeCurveLogarithmicDirection 1 (-c) f) ≠ 0 := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let Q := planeCurveLogarithmicDirection 1 (-c) f
  have hno := no_logarithmicPDeriv_scalar_relation_of_supportRankTwo
    hrank hlarge
  have hQ : Q ≠ 0 := by
    intro hzero
    apply hno
    refine ⟨c, 0, ?_⟩
    have hzero' : planeCurveLogarithmicPDeriv 0 f -
        MvPolynomial.C c * planeCurveLogarithmicPDeriv 1 f = 0 := by
      simpa [Q, planeCurveLogarithmicDirection, sub_eq_add_neg] using hzero
    simpa using sub_eq_zero.mp hzero'
  intro heval
  have hquotient : planeCurveQuotientMap f Q = 0 := by
    apply IsFractionRing.injective
      (PlaneCurveCoordinateRing f) (PlaneCurveFunctionField f)
    rw [map_zero]
    change ((algebraMap (PlaneCurveCoordinateRing f)
      (PlaneCurveFunctionField f)).comp (planeCurveQuotientMap f)) Q = 0
    rw [← eval₂_planeCurveFunction f]
    exact heval
  have hdvd : f ∣ Q :=
    Ideal.mem_span_singleton.mp
      (Ideal.Quotient.eq_zero_iff_mem.mp hquotient)
  obtain ⟨d, hd⟩ :=
    planeCurveLogarithmicDirection_eq_C_mul_of_dvd hf.ne_zero
      1 (-c) hQ hdvd
  apply hno
  refine ⟨c, d, ?_⟩
  have hd' : planeCurveLogarithmicPDeriv 0 f -
      MvPolynomial.C c * planeCurveLogarithmicPDeriv 1 f =
        MvPolynomial.C d * f := by
    simpa [Q, planeCurveLogarithmicDirection, sub_eq_add_neg] using hd
  calc
    planeCurveLogarithmicPDeriv 0 f =
        (planeCurveLogarithmicPDeriv 0 f -
          MvPolynomial.C c * planeCurveLogarithmicPDeriv 1 f) +
            MvPolynomial.C c * planeCurveLogarithmicPDeriv 1 f := by abel
    _ = MvPolynomial.C d * f +
        MvPolynomial.C c * planeCurveLogarithmicPDeriv 1 f := by rw [hd']
    _ = MvPolynomial.C c * planeCurveLogarithmicPDeriv 1 f +
        MvPolynomial.C d * f := add_comm _ _

end
end BGS.CorvajaZannier
