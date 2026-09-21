/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Incidence.CoordinateRing

/-!
# A primitive quartic for a biquadratic extension

If `f`, `g`, and `f * g` are nonsquares in a field of characteristic different
from two, then `sqrt f + sqrt g` generates the corresponding biquadratic
extension.  Its minimal polynomial is

`(X^2 - (f + g))^2 - 4 * f * g`.

This file packages that calculation as a reusable irreducibility theorem.
-/

namespace BGS.Markoff

open Polynomial

noncomputable section

variable {F : Type*} [Field F]

private lemma sum_of_square_roots_power_sum
    {R : Type*} [CommRing R] (a b f g c0 c1 c2 c3 : R)
    (ha : a ^ 2 = f) (hb : b ^ 2 = g) :
    (c0 + c2 * (f + g)) +
          (c1 + c3 * (f + 3 * g)) * a +
          (c1 + c3 * (3 * f + g)) * b +
          (2 * c2) * a * b =
      c0 * 1 + c1 * (a + b) + c2 * (a + b) ^ 2 + c3 * (a + b) ^ 3 := by
  rw [← ha, ← hb]
  ring

private lemma sum_of_square_roots_quartic_relation
    {R : Type*} [CommRing R] (a b f g : R)
    (ha : a ^ 2 = f) (hb : b ^ 2 = g) :
    ((a + b) ^ 2 - (f + g)) ^ 2 - 4 * f * g = 0 := by
  rw [← ha, ← hb]
  ring

private lemma finFour_power_relation
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (c : Fin 4 → R) (z : S)
    (h : ∑ i : Fin 4, c i • z ^ (i : ℕ) = 0) :
    algebraMap R S (c 0) * 1 + algebraMap R S (c 1) * z +
        algebraMap R S (c 2) * z ^ 2 + algebraMap R S (c 3) * z ^ 3 = 0 := by
  simpa [Fin.sum_univ_four, Algebra.smul_def] using h

private lemma regroup_quadratic_tower_coefficients
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (r : S) (s : T) (A0 A1 B0 B1 : R) :
    algebraMap R T A0 + algebraMap R T A1 * algebraMap S T r +
          algebraMap R T B0 * s + algebraMap R T B1 * algebraMap S T r * s =
      algebraMap S T (algebraMap R S A0 + algebraMap R S A1 * r) +
        algebraMap S T (algebraMap R S B0 + algebraMap R S B1 * r) * s := by
  simp only [map_add, map_mul, IsScalarTower.algebraMap_apply R S T]
  ring

/-- The minimal-polynomial candidate for `sqrt f + sqrt g`. -/
def biquadraticPrimitiveQuartic (f g : F) : F[X] :=
  (X ^ 2 - C (f + g)) ^ 2 - C (4 * f * g)

lemma biquadraticPrimitiveQuartic_monic (f g : F) :
    (biquadraticPrimitiveQuartic f g).Monic := by
  have hquadratic : IsMonicOfDegree (X ^ 2 - C (f + g) : F[X]) 2 :=
    (isMonicOfDegree_X_pow F 2).sub (by simp)
  exact ((hquadratic.pow 2).sub (by
    have hpos : 0 < 2 * 2 := by norm_num
    simpa only [← C_mul, natDegree_C] using hpos)).monic

lemma biquadraticPrimitiveQuartic_degree (f g : F) :
    (biquadraticPrimitiveQuartic f g).degree = 4 := by
  have hquadratic : IsMonicOfDegree (X ^ 2 - C (f + g) : F[X]) 2 :=
    (isMonicOfDegree_X_pow F 2).sub (by simp)
  have hquartic : IsMonicOfDegree (biquadraticPrimitiveQuartic f g) 4 := by
    simpa [biquadraticPrimitiveQuartic] using
      (hquadratic.pow 2).sub (by
        have hpos : 0 < 2 * 2 := by norm_num
        simpa only [← C_mul, natDegree_C] using hpos)
  rw [degree_eq_natDegree hquartic.ne_zero, hquartic.natDegree_eq]
  norm_num

/-- Three independent square classes give the irreducible primitive quartic
of the associated biquadratic extension. -/
theorem biquadraticPrimitiveQuartic_irreducible
    (h2 : (2 : F) ≠ 0) {f g : F}
    (hf : ¬ IsSquare f) (hg : ¬ IsSquare g)
    (hfg : ¬ IsSquare (f * g)) :
    Irreducible (biquadraticPrimitiveQuartic f g) := by
  let qf : F[X] := adjoinSquarePolynomial f
  have hqfIrreducible : Irreducible qf := by
    simpa [qf] using adjoinSquarePolynomial_irreducible_of_not_isSquare hf
  letI : Fact (Irreducible qf) := ⟨hqfIrreducible⟩
  let E := AdjoinRoot qf
  let gE : E := algebraMap F E g
  have hgE : ¬ IsSquare gE := by
    exact not_isSquare_algebraMap_adjoinSquare_of_independent h2 hf hg hfg
  let qg : E[X] := adjoinSquarePolynomial gE
  have hqgIrreducible : Irreducible qg := by
    simpa [qg] using adjoinSquarePolynomial_irreducible_of_not_isSquare hgE
  letI : Fact (Irreducible qg) := ⟨hqgIrreducible⟩
  let L := AdjoinRoot qg
  let a : L := algebraMap E L (AdjoinRoot.root qf)
  let b : L := AdjoinRoot.root qg
  let z : L := a + b
  have hqfMonic : qf.Monic := by
    simpa [qf] using adjoinSquarePolynomial_monic f
  have hqgMonic : qg.Monic := by
    simpa [qg] using adjoinSquarePolynomial_monic gE
  have hqfDegree : qf.natDegree = 2 := by
    simpa [qf] using adjoinSquarePolynomial_natDegree f
  have hqgDegree : qg.natDegree = 2 := by
    simpa [qg] using adjoinSquarePolynomial_natDegree gE
  have ha_sq : a ^ 2 = algebraMap F L f := by
    change (algebraMap E L (AdjoinRoot.root qf)) ^ 2 = algebraMap F L f
    rw [← map_pow, show (AdjoinRoot.root qf) ^ 2 = algebraMap F E f by
      simpa only [E, qf, AdjoinRoot.algebraMap_eq] using adjoinSquareRoot_sq f]
    exact IsScalarTower.algebraMap_apply F E L f
  have hb_sq : b ^ 2 = algebraMap F L g := by
    change (AdjoinRoot.root qg) ^ 2 = algebraMap F L g
    rw [show (AdjoinRoot.root qg) ^ 2 = algebraMap E L gE by
      simpa only [L, qg, AdjoinRoot.algebraMap_eq] using adjoinSquareRoot_sq gE]
    exact IsScalarTower.algebraMap_apply F E L g
  have hfg_ne : f ≠ g := by
    intro heq
    apply hfg
    refine ⟨f, ?_⟩
    rw [heq]
  let firstBasis : Module.Basis (Fin qf.natDegree) F E :=
    (AdjoinRoot.powerBasis' hqfMonic).basis
  let secondBasis : Module.Basis (Fin qg.natDegree) E L :=
    (AdjoinRoot.powerBasis' hqgMonic).basis
  let firstZero : Fin qf.natDegree := ⟨0, by rw [hqfDegree]; norm_num⟩
  let firstOne : Fin qf.natDegree := ⟨1, by rw [hqfDegree]; norm_num⟩
  let secondZero : Fin qg.natDegree := ⟨0, by rw [hqgDegree]; norm_num⟩
  let secondOne : Fin qg.natDegree := ⟨1, by rw [hqgDegree]; norm_num⟩
  have hfirst_ne : firstZero ≠ firstOne := by
    intro h
    have := congrArg Fin.val h
    norm_num [firstZero, firstOne] at this
  have hsecond_ne : secondZero ≠ secondOne := by
    intro h
    have := congrArg Fin.val h
    norm_num [secondZero, secondOne] at this
  have hfirst0 : firstBasis firstZero = 1 := by
    change (AdjoinRoot.powerBasis' hqfMonic).basis firstZero = 1
    simp only [PowerBasis.coe_basis]
    change AdjoinRoot.root qf ^ 0 = 1
    exact pow_zero _
  have hfirst1 : firstBasis firstOne = AdjoinRoot.root qf := by
    change (AdjoinRoot.powerBasis' hqfMonic).basis firstOne = AdjoinRoot.root qf
    simp only [PowerBasis.coe_basis]
    change AdjoinRoot.root qf ^ 1 = AdjoinRoot.root qf
    exact pow_one _
  have hsecond0 : secondBasis secondZero = 1 := by
    change (AdjoinRoot.powerBasis' hqgMonic).basis secondZero = 1
    simp only [PowerBasis.coe_basis]
    change AdjoinRoot.root qg ^ 0 = 1
    exact pow_zero _
  have hsecond1 : secondBasis secondOne = AdjoinRoot.root qg := by
    change (AdjoinRoot.powerBasis' hqgMonic).basis secondOne = AdjoinRoot.root qg
    simp only [PowerBasis.coe_basis]
    change AdjoinRoot.root qg ^ 1 = AdjoinRoot.root qg
    exact pow_one _
  have hpowers : LinearIndependent F (fun i : Fin 4 ↦ z ^ (i : ℕ)) := by
    refine Fintype.linearIndependent_iff.mpr ?_
    intro c hc i
    have hcExpanded := finFour_power_relation c z hc
    have hrelation :
        algebraMap F L (c 0 + c 2 * (f + g)) +
            algebraMap F L (c 1 + c 3 * (f + 3 * g)) * a +
            algebraMap F L (c 1 + c 3 * (3 * f + g)) * b +
            algebraMap F L (2 * c 2) * a * b = 0 := by
      calc
        algebraMap F L (c 0 + c 2 * (f + g)) +
              algebraMap F L (c 1 + c 3 * (f + 3 * g)) * a +
              algebraMap F L (c 1 + c 3 * (3 * f + g)) * b +
              algebraMap F L (2 * c 2) * a * b =
            algebraMap F L (c 0) * 1 +
              algebraMap F L (c 1) * z +
              algebraMap F L (c 2) * z ^ 2 +
              algebraMap F L (c 3) * z ^ 3 := by
                simpa only [z, map_add, map_mul, map_ofNat] using
                  sum_of_square_roots_power_sum a b
                    (algebraMap F L f) (algebraMap F L g)
                    (algebraMap F L (c 0)) (algebraMap F L (c 1))
                    (algebraMap F L (c 2)) (algebraMap F L (c 3)) ha_sq hb_sq
        _ = 0 := hcExpanded
    let constantCoefficient : E :=
      algebraMap F E (c 0 + c 2 * (f + g)) +
        algebraMap F E (c 1 + c 3 * (f + 3 * g)) * AdjoinRoot.root qf
    let rootCoefficient : E :=
      algebraMap F E (c 1 + c 3 * (3 * f + g)) +
        algebraMap F E (2 * c 2) * AdjoinRoot.root qf
    have hregroup :
        algebraMap E L constantCoefficient +
            algebraMap E L rootCoefficient * b = 0 := by
      rw [← hrelation]
      simpa only [constantCoefficient, rootCoefficient, a] using
        (regroup_quadratic_tower_coefficients
          (R := F) (S := E) (T := L) (AdjoinRoot.root qf) b
          (c 0 + c 2 * (f + g))
          (c 1 + c 3 * (f + 3 * g))
          (c 1 + c 3 * (3 * f + g)) (2 * c 2)).symm
    have hsecondRelation :
        constantCoefficient • secondBasis secondZero +
          rootCoefficient • secondBasis secondOne = 0 := by
      simpa only [hsecond0, hsecond1, Algebra.smul_def, b, mul_one] using hregroup
    have hconstant := congrArg (secondBasis.coord secondZero) hsecondRelation
    have hroot := congrArg (secondBasis.coord secondOne) hsecondRelation
    have hconstant_zero : constantCoefficient = 0 := by
      simpa [hsecond_ne] using hconstant
    have hroot_zero : rootCoefficient = 0 := by
      simpa [hsecond_ne] using hroot
    have hconstantFirstRelation :
        (c 0 + c 2 * (f + g)) • firstBasis firstZero +
          (c 1 + c 3 * (f + 3 * g)) • firstBasis firstOne = 0 := by
      simpa [constantCoefficient, hfirst0, hfirst1, Algebra.smul_def] using
        hconstant_zero
    have hrootFirstRelation :
        (c 1 + c 3 * (3 * f + g)) • firstBasis firstZero +
          (2 * c 2) • firstBasis firstOne = 0 := by
      simpa [rootCoefficient, hfirst0, hfirst1, Algebra.smul_def] using hroot_zero
    have hc0c2 := congrArg (firstBasis.coord firstZero) hconstantFirstRelation
    have hc1c3Left := congrArg (firstBasis.coord firstOne) hconstantFirstRelation
    have hc1c3Right := congrArg (firstBasis.coord firstZero) hrootFirstRelation
    have hc2two := congrArg (firstBasis.coord firstOne) hrootFirstRelation
    have hc2 : c 2 = 0 := by
      have : (2 : F) * c 2 = 0 := by simpa [hfirst_ne] using hc2two
      exact (mul_eq_zero.mp this).resolve_left h2
    have hc0 : c 0 = 0 := by
      simpa [hfirst_ne, hc2] using hc0c2
    have hc3 : c 3 = 0 := by
      have hsub : c 3 * (2 * (g - f)) = 0 := by
        have hleft : c 1 + c 3 * (f + 3 * g) = 0 := by
          simpa [hfirst_ne] using hc1c3Left
        have hright : c 1 + c 3 * (3 * f + g) = 0 := by
          simpa [hfirst_ne] using hc1c3Right
        calc
          c 3 * (2 * (g - f)) =
              (c 1 + c 3 * (f + 3 * g)) -
                (c 1 + c 3 * (3 * f + g)) := by ring
          _ = 0 := by rw [hleft, hright]; ring
      apply (mul_eq_zero.mp hsub).resolve_right
      exact mul_ne_zero h2 (sub_ne_zero.mpr hfg_ne.symm)
    have hc1 : c 1 = 0 := by
      simpa [hfirst_ne, hc3] using hc1c3Left
    fin_cases i <;> assumption
  have hzRoot : (biquadraticPrimitiveQuartic f g).aeval z = 0 := by
    simp only [biquadraticPrimitiveQuartic, map_sub, map_pow, aeval_X, aeval_C]
    simpa only [z, map_add, map_mul, map_ofNat] using
      sum_of_square_roots_quartic_relation a b
        (algebraMap F L f) (algebraMap F L g) ha_sq hb_sq
  have hminpoly : minpoly F z = biquadraticPrimitiveQuartic f g :=
    minpoly.eq_of_linearIndependent
      F z (biquadraticPrimitiveQuartic_monic f g) hzRoot 4
      (biquadraticPrimitiveQuartic_degree f g) hpowers
  have hzIntegral : IsIntegral F z :=
    ⟨biquadraticPrimitiveQuartic f g,
      biquadraticPrimitiveQuartic_monic f g, hzRoot⟩
  rw [← hminpoly]
  exact minpoly.irreducible hzIntegral

end

end BGS.Markoff
