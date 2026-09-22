/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.TorusCharacterKernelBound
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveLogarithmicGauss
import Mathlib.Tactic

namespace BGS.CorvajaZannier
noncomputable section

/-- Scale the two variables of a bivariate polynomial by a pair of units. -/
def diagonalScale {F : Type*} [Field F]
    (z : Fˣ × Fˣ) (f : MvPolynomial (Fin 2) F) :=
  f.support.sum fun m =>
    MvPolynomial.monomial m
      (f.coeff m * (z.1 : F) ^ m 0 * (z.2 : F) ^ m 1)

theorem coeff_diagonalScale {F : Type*} [Field F]
    (z : Fˣ × Fˣ) (f : MvPolynomial (Fin 2) F)
    (m : Fin 2 →₀ ℕ) :
    (diagonalScale z f).coeff m =
      f.coeff m * (z.1 : F) ^ m 0 * (z.2 : F) ^ m 1 := by
  classical
  by_cases hm : m ∈ f.support
  · simp [diagonalScale, MvPolynomial.coeff_sum,
      MvPolynomial.coeff_monomial, hm]
  · have hcoeff : f.coeff m = 0 :=
      MvPolynomial.notMem_support_iff.mp hm
    simp [diagonalScale, MvPolynomial.coeff_sum,
      MvPolynomial.coeff_monomial, hm, hcoeff]

theorem support_diagonalScale {F : Type*} [Field F]
    (z : Fˣ × Fˣ) (f : MvPolynomial (Fin 2) F) :
    (diagonalScale z f).support = f.support := by
  ext m
  simp only [MvPolynomial.mem_support_iff, coeff_diagonalScale]
  constructor
  · exact fun h => left_ne_zero_of_mul (left_ne_zero_of_mul h)
  · intro h
    exact mul_ne_zero
      (mul_ne_zero h (pow_ne_zero _ (Units.ne_zero z.1)))
      (pow_ne_zero _ (Units.ne_zero z.2))

theorem eval₂_diagonalScale {F L : Type*} [Field F] [Field L]
    (φ : F →+* L) (z : Fˣ × Fˣ)
    (x y : L) (f : MvPolynomial (Fin 2) F) :
    MvPolynomial.eval₂ φ ![x, y] (diagonalScale z f) =
      MvPolynomial.eval₂ φ ![φ z.1 * x, φ z.2 * y] f := by
  classical
  change (MvPolynomial.eval₂Hom φ ![x, y]) (diagonalScale z f) =
    (MvPolynomial.eval₂Hom φ ![φ z.1 * x, φ z.2 * y]) f
  rw [diagonalScale, map_sum]
  conv_rhs => rw [f.as_sum, map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hprod (v : Fin 2 → L) :
      m.prod (fun i k => v i ^ k) = v 0 ^ m 0 * v 1 ^ m 1 := by
    rw [m.prod_fintype (fun i k => v i ^ k) (fun _ => pow_zero _),
      Fin.prod_univ_two]
  simp only [MvPolynomial.eval₂Hom_monomial, map_mul, map_pow,
    hprod, Matrix.cons_val_zero, Matrix.cons_val_one, mul_pow]
  ring

private theorem eq_C_coeff_zero_of_bidegree_zero
    {F : Type*} [Field F] (g : MvPolynomial (Fin 2) F)
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

/-- A diagonal scaling divisible by the original polynomial differs from it by
a scalar.  Equality of supports is what rules out a nonconstant quotient. -/
theorem diagonalScale_eq_C_mul_of_dvd
    {F : Type*} [Field F] {f : MvPolynomial (Fin 2) F}
    (hf : f ≠ 0) (z : Fˣ × Fˣ)
    (hdvd : f ∣ diagonalScale z f) :
    ∃ c : F, diagonalScale z f = MvPolynomial.C c * f := by
  obtain ⟨g, hg⟩ := hdvd
  have hscale : diagonalScale z f ≠ 0 := by
    intro h
    have hs := support_diagonalScale z f
    rw [h, MvPolynomial.support_zero] at hs
    exact hf (MvPolynomial.support_eq_empty.mp hs.symm)
  have hg0 : g ≠ 0 := by
    intro h
    apply hscale
    rw [hg, h, mul_zero]
  have hdegree (i : Fin 2) :
      MvPolynomial.degreeOf i (diagonalScale z f) =
        MvPolynomial.degreeOf i f := by
    apply le_antisymm <;> rw [MvPolynomial.degreeOf_le_iff]
    · intro m hm
      exact MvPolynomial.le_degreeOf_of_mem_support i
        (support_diagonalScale z f ▸ hm)
    · intro m hm
      exact MvPolynomial.le_degreeOf_of_mem_support i
        (support_diagonalScale z f ▸ hm)
  have hgDegree0 : MvPolynomial.degreeOf 0 g = 0 := by
    have h := hdegree 0
    rw [hg, MvPolynomial.degreeOf_mul_eq hf hg0] at h
    omega
  have hgDegree1 : MvPolynomial.degreeOf 1 g = 0 := by
    have h := hdegree 1
    rw [hg, MvPolynomial.degreeOf_mul_eq hf hg0] at h
    omega
  let c := g.coeff 0
  have hgC : g = MvPolynomial.C c :=
    eq_C_coeff_zero_of_bidegree_zero g hgDegree0 hgDegree1
  refine ⟨c, ?_⟩
  rw [hg, hgC, mul_comm]

/-- If a diagonal scaling of an irreducible plane curve vanishes at its generic
point, the scaling lies in the character stabilizer detected by its support. -/
theorem planeCurveSupportCharacterStabilizer_of_diagonalScale_eval_zero
    {F : Type*} [Field F] {f : MvPolynomial (Fin 2) F}
    (hf : Irreducible f) (z : Fˣ × Fˣ)
    (heval :
      letI := planeCurveCoordinateRing_isDomain hf
      MvPolynomial.eval₂ (algebraMap F (PlaneCurveFunctionField f))
        (planeCurveFunction f) (diagonalScale z f) = 0) :
    ∀ r ∈ f.support, ∀ s ∈ f.support,
      z.1 ^ ((s 0 : ℤ) - (r 0 : ℤ)) *
        z.2 ^ ((s 1 : ℤ) - (r 1 : ℤ)) = 1 := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  have hquotient : planeCurveQuotientMap f (diagonalScale z f) = 0 := by
    apply IsFractionRing.injective
      (PlaneCurveCoordinateRing f) (PlaneCurveFunctionField f)
    rw [map_zero]
    change ((algebraMap (PlaneCurveCoordinateRing f)
      (PlaneCurveFunctionField f)).comp (planeCurveQuotientMap f))
        (diagonalScale z f) = 0
    rw [← eval₂_planeCurveFunction f]
    exact heval
  have hdvd : f ∣ diagonalScale z f :=
    Ideal.mem_span_singleton.mp
      (Ideal.Quotient.eq_zero_iff_mem.mp hquotient)
  obtain ⟨c, hc⟩ := diagonalScale_eq_C_mul_of_dvd hf.ne_zero z hdvd
  intro r hr s hs
  have hweight (m : Fin 2 →₀ ℕ) (hm : m ∈ f.support) :
      (z.1 : F) ^ m 0 * (z.2 : F) ^ m 1 = c := by
    have hcoeff := congrArg (fun p ↦ p.coeff m) hc
    rw [coeff_diagonalScale] at hcoeff
    simp only [MvPolynomial.coeff_C_mul] at hcoeff
    have hm0 : f.coeff m ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hm
    exact mul_left_cancel₀ hm0
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hcoeff)
  have hwField :
      (z.1 : F) ^ s 0 * (z.2 : F) ^ s 1 =
        (z.1 : F) ^ r 0 * (z.2 : F) ^ r 1 := by
    rw [hweight s hs, hweight r hr]
  have hwUnits : z.1 ^ s 0 * z.2 ^ s 1 = z.1 ^ r 0 * z.2 ^ r 1 := by
    apply Units.ext
    exact hwField
  calc
    z.1 ^ ((s 0 : ℤ) - (r 0 : ℤ)) *
        z.2 ^ ((s 1 : ℤ) - (r 1 : ℤ)) =
      (z.1 ^ s 0 * z.2 ^ s 1) *
        (z.1 ^ r 0 * z.2 ^ r 1)⁻¹ := by
      simp only [zpow_sub, zpow_natCast, mul_inv_rev]
      ac_rfl
    _ = 1 := by rw [hwUnits]; simp

end
end BGS.CorvajaZannier
