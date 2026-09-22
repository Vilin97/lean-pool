/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.PoweredImageFrobeniusRelation
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PoweredCoordinateRelation
import Mathlib.Tactic

/-!
# The powered-image auxiliary family with exchanged coordinates

The existing powered-image theorem orients the auxiliary family as
`(x^m,y^n)`.  Proposition 2 is applied with the smaller source height first,
so this module supplies the equally canonical orientation `(y^n,x^m)`.
It uses the untransposed powered-image equation and the first-coordinate
Frobenius power basis.
-/

open scoped Polynomial

namespace BGS.CorvajaZannier

open Polynomial

noncomputable section


variable {K : Type*} [Field K] [PerfectField K]
variable {p : ℕ} [Fact p.Prime] [CharP K p]

/-- Proposition 1 for the powered coordinates in the exchanged orientation.
The relation degrees are those of the untransposed powered-image equation. -/
theorem poweredCoordinateFrobeniusImage_auxiliaryFamily_linearIndependent_swapped
    {f : MvPolynomial (Fin 2) K}
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmPrime : ¬ p ∣ m)
    (h k : ℕ) (hh : 0 < h) (hk : 0 < k)
    (hsize :
      letI := planeCurveCoordinateRing_isDomain hf
      letI : CharP (PlaneCurveFunctionField f) p :=
        charP_of_injective_algebraMap
          (algebraMap K (PlaneCurveFunctionField f)).injective p
      let F := frobeniusSubfield (PlaneCurveFunctionField f) p
      let ι : K →+* F := perfectConstantsToFrobeniusSubfield
        (K := K) (L := PlaneCurveFunctionField f) (p := p)
      let g := (poweredCoordinateImageRelation hf hpartialSecond m hm n).map
        (Polynomial.mapRingHom ι)
      g.natDegree * h + (transposeBivariate g).natDegree * k < p)
    (hexcluded :
      letI := planeCurveCoordinateRing_isDomain hf
      letI : CharP (PlaneCurveFunctionField f) p :=
        charP_of_injective_algebraMap
          (algebraMap K (PlaneCurveFunctionField f)).injective p
      let F := frobeniusSubfield (PlaneCurveFunctionField f) p
      let ι : K →+* F := perfectConstantsToFrobeniusSubfield
        (K := K) (L := PlaneCurveFunctionField f) (p := p)
      let g := (poweredCoordinateImageRelation hf hpartialSecond m hm n).map
        (Polynomial.mapRingHom ι)
      ¬ (g.natDegree ≤ k ∧ (transposeBivariate g).natDegree ≤ h)) :
    letI := planeCurveCoordinateRing_isDomain hf
    letI : CharP (PlaneCurveFunctionField f) p :=
      charP_of_injective_algebraMap
        (algebraMap K (PlaneCurveFunctionField f)).injective p
    LinearIndependent
      (frobeniusSubfield (PlaneCurveFunctionField f) p)
      (auxiliaryFamily ((planeCurveFunction f 1) ^ n)
        ((planeCurveFunction f 0) ^ m) h k) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let L := PlaneCurveFunctionField f
  let : CharP L p := charP_of_injective_algebraMap
    (algebraMap K L).injective p
  let F := frobeniusSubfield L p
  let ι : K →+* F :=
    perfectConstantsToFrobeniusSubfield (K := K) (L := L) (p := p)
  let : Algebra K F := ι.toAlgebra
  let : IsScalarTower K F L := by
    apply IsScalarTower.of_algebraMap_eq'
    ext c
    exact (coe_perfectConstantsToFrobeniusSubfield
      (K := K) (L := L) (p := p) c).symm
  let gK := poweredCoordinateImageRelation hf hpartialSecond m hm n
  let g : Polynomial (Polynomial F) :=
    gK.map (Polynomial.mapRingHom ι)
  have hι : Function.Injective ι :=
    perfectConstantsToFrobeniusSubfield_injective
      (K := K) (L := L) (p := p)
  have hmap : Function.Injective (Polynomial.mapRingHom ι) :=
    Polynomial.map_injective ι hι
  have hg : Irreducible g := by
    dsimp only [g, gK]
    exact poweredCoordinateImageRelation_irreducible_map
      (E := F) habsolute hf hpartialSecond m hm n
  have hdegreeG : g.natDegree = gK.natDegree := by
    dsimp only [g]
    exact Polynomial.natDegree_map_eq_of_injective hmap _
  have ha : 0 < g.natDegree := by
    rw [hdegreeG]
    exact poweredCoordinateImageRelation_natDegree_pos
      hf hpartialSecond m hm n
  have hdegreeTranspose : (transposeBivariate g).natDegree =
      (transposeBivariate gK).natDegree := by
    dsimp only [g]
    rw [transposeBivariate_map]
    exact Polynomial.natDegree_map_eq_of_injective hmap _
  have hb : 0 < (transposeBivariate g).natDegree := by
    rw [hdegreeTranspose]
    exact poweredCoordinateImageRelation_transpose_natDegree_pos
      hf hpartialFirst hpartialSecond m hm n hn
  have hcoeff : ∀ i, (g.coeff i).natDegree ≤
      (transposeBivariate g).natDegree := by
    intro i
    have hcoeffK := poweredCoordinateImageRelation_coeff_natDegree_le
      hf hpartialSecond m hm n i
    have hcoeffDegree : (g.coeff i).natDegree = (gK.coeff i).natDegree := by
      dsimp only [g]
      rw [Polynomial.coeff_map]
      exact Polynomial.natDegree_map_eq_of_injective hι _
    rw [hcoeffDegree, hdegreeTranspose]
    exact hcoeffK
  have hzero : evalBivariate
      ((planeCurveFunction f 0) ^ m)
      ((planeCurveFunction f 1) ^ n) g = 0 := by
    dsimp only [g]
    change evalBivariate
      ((planeCurveFunction f 0) ^ m)
      ((planeCurveFunction f 1) ^ n)
      (gK.map (Polynomial.mapRingHom (algebraMap K F))) = 0
    rw [evalBivariate_map_mapRingHom]
    exact evalBivariate_poweredCoordinateImageRelation_eq_zero
      hf hpartialSecond m hm n
  have hminpoly :
      (minpoly F ((planeCurveFunction f 0) ^ m)).natDegree = p :=
    minpoly_firstCoordinatePow_natDegree_eq_char
      hf hpartialSecond m hmPrime
  have hxTrans : Transcendental K (planeCurveFunction f 0) :=
    firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  have hxmTrans : Transcendental K ((planeCurveFunction f 0) ^ m) :=
    hxTrans.pow hm
  have hxmOne : (planeCurveFunction f 0) ^ m ≠ 1 := by
    intro hxm
    apply hxmTrans
    rw [hxm]
    exact isAlgebraic_one
  exact auxiliaryFamily_linearIndependent_of_irreducible_bidegree
    g g.natDegree (transposeBivariate g).natDegree h k p
      ha hh hk hg rfl rfl hcoeff
      ((planeCurveFunction f 1) ^ n) ((planeCurveFunction f 0) ^ m)
      hxmOne hminpoly hzero hsize hexcluded

end

end BGS.CorvajaZannier
