/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.Refinement.CompleteGermRefinement
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.TruncationIntegerPartPrimal

import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.ArchimedeanBallBase
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# The fraction-field condition for truncation integer parts

Let `K` be a field of characteristic zero, let `G` be an ordered exponent group that is Cauchy
complete with no least nonzero Archimedean magnitude, and let `Z` be a subring of `K`. If the
generalised-power-series integer part `Z + K((G^{<0}))` has the refinement property, then `K` is
the fraction field of `Z`.

The proof uses the polynomial presentation of the germ ring. A cofinal series shows that the
polynomial algebra has a variable. Translating a representative of that variable by its constant
coefficient gives an irreducible germ with constant coefficient zero. Primality of this series in
the integer part, applied to its scalar multiples by `x` and `x⁻¹`, writes every `x : K` as a
fraction of elements of `Z`.
-/

open Set
open scoped HahnSeries

universe u v

public noncomputable section

namespace HahnSeries.Nonpositive

variable {G : Type u} {K : Type v}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [DenselyOrdered G] [NoMinOrder G] [NoMaxOrder G]
  [NoMaxOrder (FiniteArchimedeanClass G)]
  [Field K] [CharZero K]

private def cofinalNegativeExponent (i : ArchimedeanClass.CofinalIndex G) : G :=
  -|ArchimedeanClass.CofinalIndex.representative i|

omit [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G]
  [CompleteSpace G] [DenselyOrdered G] [NoMinOrder G] [NoMaxOrder G]
  [NoMaxOrder (FiniteArchimedeanClass G)] in
private theorem cofinalNegativeExponent_lt_zero (i : ArchimedeanClass.CofinalIndex G) :
    cofinalNegativeExponent i < 0 := by
  apply neg_lt_zero.mpr
  apply abs_pos.mpr
  exact ArchimedeanClass.CofinalIndex.representative_ne_zero i

omit [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G]
  [CompleteSpace G] [DenselyOrdered G] [NoMinOrder G] [NoMaxOrder G]
  [NoMaxOrder (FiniteArchimedeanClass G)] in
private theorem cofinalNegativeExponent_strictMono :
    StrictMono (cofinalNegativeExponent (G := G)) := by
  intro i j hij
  apply neg_lt_neg
  have hclass :
      ArchimedeanClass.mk (ArchimedeanClass.CofinalIndex.representative i) <
        ArchimedeanClass.mk (ArchimedeanClass.CofinalIndex.representative j) := by
    simpa only [ArchimedeanClass.CofinalIndex.mk_representative] using
      ArchimedeanClass.CofinalIndex.underlyingClass_lt_of_lt hij
  simpa using (ArchimedeanClass.mk_lt_mk.mp hclass 1)

omit [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G]
  [CompleteSpace G] [DenselyOrdered G] [NoMinOrder G] [NoMaxOrder G]
  [NoMaxOrder (FiniteArchimedeanClass G)] in
private theorem cofinalNegativeExponent_isPWO :
    (Set.range (cofinalNegativeExponent (G := G))).IsPWO := by
  rw [show Set.range (cofinalNegativeExponent (G := G)) =
    cofinalNegativeExponent (G := G) '' Set.univ by ext; simp]
  exact (Set.IsPWO.of_linearOrder
    (Set.univ : Set (ArchimedeanClass.CofinalIndex G))).image_of_monotone
      cofinalNegativeExponent_strictMono.monotone

private def cofinalGermSeries : HahnSeries G K := by
  classical
  exact HahnSeries.mk
    (fun g => if g ∈ Set.range (cofinalNegativeExponent (G := G)) then 1 else 0)
    (by
      rw [show Function.support
        (fun g => if g ∈ Set.range (cofinalNegativeExponent (G := G)) then
          (1 : K) else 0) = Set.range (cofinalNegativeExponent (G := G)) by
        ext g
        simp [Function.mem_support]]
      exact cofinalNegativeExponent_isPWO)

omit [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G]
  [CompleteSpace G] [DenselyOrdered G] [NoMinOrder G] [NoMaxOrder G]
  [NoMaxOrder (FiniteArchimedeanClass G)] in
private theorem support_cofinalGermSeries :
    (cofinalGermSeries (G := G) (K := K)).support =
      Set.range (cofinalNegativeExponent (G := G)) := by
  classical
  ext g
  simp [cofinalGermSeries]

private def cofinalGermNonpositive : Nonpositive G K :=
  ⟨cofinalGermSeries (G := G) (K := K), by
    intro g hg
    rw [support_cofinalGermSeries] at hg
    obtain ⟨i, rfl⟩ := hg
    exact (cofinalNegativeExponent_lt_zero i).le⟩

omit [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G]
  [CompleteSpace G] [DenselyOrdered G] [NoMinOrder G] [NoMaxOrder G]
  [NoMaxOrder (FiniteArchimedeanClass G)] in
private theorem constantCoeff_cofinalGermNonpositive :
    constantCoeff (cofinalGermNonpositive (G := G) (K := K)) = 0 := by
  classical
  rw [constantCoeff_apply]
  change (cofinalGermSeries (G := G) (K := K)).coeff 0 = 0
  rw [cofinalGermSeries]
  change (if 0 ∈ Set.range (cofinalNegativeExponent (G := G)) then 1 else 0) = 0
  rw [ite_eq_right]
  rintro ⟨i, hi⟩
  exact (cofinalNegativeExponent_lt_zero i).ne hi

omit [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G]
  [CompleteSpace G] [DenselyOrdered G] [NoMinOrder G] [NoMaxOrder G]
  [NoMaxOrder (FiniteArchimedeanClass G)] in
private theorem cofinalIndex_exists_ge (c : FiniteArchimedeanClass G) :
    ∃ i : ArchimedeanClass.CofinalIndex G,
      c ≤ ArchimedeanClass.CofinalIndex.archimedeanClass i := by
  have hcof := ArchimedeanClass.CofinalIndex.isCofinal_range_archimedeanClass (G := G)
  obtain ⟨d, ⟨i, rfl⟩, hci⟩ := hcof c
  exact ⟨i, hci⟩

omit [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G]
  [CompleteSpace G] [DenselyOrdered G] [NoMinOrder G] [NoMaxOrder G] in
private theorem exists_cofinalNegativeExponent_gt (e : G) (he : e < 0) :
    ∃ i : ArchimedeanClass.CofinalIndex G,
      e < cofinalNegativeExponent (G := G) i := by
  obtain ⟨i, hi⟩ := ArchimedeanClass.exists_cofinalBallBase_subset_Ioo (-e) (neg_pos.mpr he)
  obtain ⟨d, hid⟩ :=
    exists_gt (ArchimedeanClass.CofinalIndex.archimedeanClass i)
  obtain ⟨j, hdj⟩ := cofinalIndex_exists_ge (G := G) d
  have hijClass : ArchimedeanClass.CofinalIndex.archimedeanClass i <
      ArchimedeanClass.CofinalIndex.archimedeanClass j := hid.trans_le hdj
  have hij : i < j :=
    ArchimedeanClass.CofinalIndex.lt_iff_archimedeanClass_lt.mpr hijClass
  have hjball : cofinalNegativeExponent (G := G) j ∈
      ArchimedeanClass.cofinalBallBase i := by
    apply (ArchimedeanClass.mem_cofinalBallBase_iff i _).mpr
    simpa [cofinalNegativeExponent,
      ArchimedeanClass.CofinalIndex.mk_representative] using
        ArchimedeanClass.CofinalIndex.underlyingClass_lt_of_lt hij
  have hjinterval := hi hjball
  exact ⟨j, by simpa using hjinterval.1⟩

omit [DenselyOrdered G] [NoMinOrder G] [NoMaxOrder G] in
private theorem cofinalGermNonpositive_germ_ne_zero :
    Ideal.Quotient.mk (cantorBendixsonValuation (G := G) (R := K)).supp
      (cofinalGermNonpositive (G := G) (K := K)) ≠ 0 := by
  intro hzero
  have heq : Ideal.Quotient.mk (cantorBendixsonValuation (G := G) (R := K)).supp
      (cofinalGermNonpositive (G := G) (K := K)) =
      Ideal.Quotient.mk (cantorBendixsonValuation (G := G) (R := K)).supp 0 := by
    simpa using hzero
  obtain ⟨e, he, hcoeff⟩ :=
    (cantorBendixson_germ_eq_iff (cofinalGermNonpositive (G := G) (K := K)) 0).mp heq
  obtain ⟨i, hei⟩ := exists_cofinalNegativeExponent_gt (G := G) e he
  have h := hcoeff (cofinalNegativeExponent (G := G) i) hei
  simp [cofinalGermNonpositive, cofinalGermSeries] at h

omit [DenselyOrdered G] [NoMinOrder G] [NoMaxOrder G]
  [NoMaxOrder (FiniteArchimedeanClass G)] in
private theorem cofinalGermNonpositive_germ_not_isUnit :
    ¬ IsUnit (Ideal.Quotient.mk (cantorBendixsonValuation (G := G) (R := K)).supp
      (cofinalGermNonpositive (G := G) (K := K))) := by
  intro hunit
  exact (constantCoeff_ne_zero_of_isUnit_cantorBendixson_germ hunit)
    constantCoeff_cofinalGermNonpositive

/-- There is a series with zero constant coefficient whose germ at zero is irreducible. -/
@[blueprint "lem:irreducible-zero-constant-germ"
  (phase := "Refinement over Archimedean classes")
  (title := "An irreducible germ with zero constant coefficient")
  (statement := /--
    Let $K$ be a field of characteristic zero and let $G$ be a nontrivial,
    densely ordered abelian group with no least or greatest element and no
    least nonzero Archimedean magnitude.  Assume that $G$ is Cauchy complete
    for its additive uniformity.
    Then some series $p\in K((G^{\le0}))$ has constant coefficient zero and
    irreducible image in the germ ring at zero.
  -/)
  (proof := /--
    Choose a well-ordered support cofinal at $0$ that meets a cofinal family
    of nonzero Archimedean classes.  The resulting series has a nonzero,
    nonunit germ. Hence \ref{thm:complete-hahn-germ-polynomial-algebra} has
    a nonempty index set. Choose a
    polynomial variable $X_i$ and a series $p$ representing it.  Subtracting
    the constant coefficient $r$ of $p$ gives a representative with constant
    coefficient zero and germ corresponding to $X_i-r$, which is irreducible.
  -/)]
theorem exists_irreducible_cantorBendixson_germ_with_constantCoeff_zero :
    ∃ p : Nonpositive G K,
      constantCoeff p = 0 ∧
      Irreducible
        (Ideal.Quotient.mk (cantorBendixsonValuation (G := G) (R := K)).supp p) := by
  let J := (cantorBendixsonValuation (G := G) (R := K)).supp
  obtain ⟨ι, ⟨equiv⟩⟩ := exists_mvPolynomial_algEquiv_germ (G := G) (K := K)
  have hι : Nonempty ι := by
    by_contra h
    letI : IsEmpty ι := not_nonempty_iff.mp h
    let q : MvPolynomial ι K :=
      equiv.symm (Ideal.Quotient.mk J (cofinalGermNonpositive (G := G) (K := K)))
    have hq0 : q ≠ 0 := by
      intro hq
      apply cofinalGermNonpositive_germ_ne_zero (G := G) (K := K)
      have heq := congrArg equiv hq
      simpa only [q, equiv.apply_symm_apply, map_zero] using heq
    have hqcoeff : q.coeff 0 ≠ 0 := by
      intro hcoeff
      apply hq0
      rw [MvPolynomial.eq_C_of_isEmpty q, hcoeff, map_zero]
    have hqunit : IsUnit q := by
      rw [MvPolynomial.eq_C_of_isEmpty q]
      exact (isUnit_iff_ne_zero.mpr hqcoeff).map MvPolynomial.C
    apply cofinalGermNonpositive_germ_not_isUnit (G := G) (K := K)
    simpa [q] using hqunit.map equiv.toMulEquiv
  let i : ι := hι.some
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (equiv (MvPolynomial.X i))
  let r : K := constantCoeff p
  let p₀ : Nonpositive G K := p - C r
  have hp₀coeff : constantCoeff p₀ = 0 := by
    simp [p₀, r]
  have hpoly : Irreducible (MvPolynomial.X i - MvPolynomial.C r) := by
    simpa [sub_eq_add_neg] using
      (MvPolynomial.irreducible_mul_X_add (1 : MvPolynomial ι K)
        (-MvPolynomial.C r) i (by simp) (by simp) (by simp) isRelPrime_one_left)
  have hgerm :
      Ideal.Quotient.mk J p₀ = equiv (MvPolynomial.X i - MvPolynomial.C r) := by
    have hconst : Ideal.Quotient.mk J (C r) = equiv (MvPolynomial.C r) := by
      change Ideal.Quotient.mk J (algebraMap K (Nonpositive G K) r) =
        equiv (algebraMap K (MvPolynomial ι K) r)
      rw [Ideal.Quotient.mk_algebraMap]
      exact (equiv.commutes r).symm
    dsimp [p₀]
    rw [map_sub, hp, hconst, map_sub]
  refine ⟨p₀, hp₀coeff, ?_⟩
  rw [hgerm]
  exact hpoly.map equiv.toMulEquiv

/-- If `Z + K((G^{<0}))` has the refinement property, then `K` is the fraction field of `Z`. -/
@[blueprint "thm:refinement-forces-coefficient-fraction-field"
  (phase := "Refinement over Archimedean classes")
  (title := "Refinement forces $K=\\operatorname{Frac}(Z)$")
  (statement := /--
    Let $K$ be a field of characteristic zero and let $G$ satisfy the
    hypotheses of \ref{lem:irreducible-zero-constant-germ}.  If
    \[
      Z+K((G^{<0}))
    \]
    has the refinement property for a subring $Z\subseteq K$, then
    $K=\operatorname{Frac}(Z)$.
  -/)
  (proof := /--
    Identify the integer part with the inverse image of $Z$ under the
    constant-coefficient map.  By
    \ref{lem:irreducible-zero-constant-germ}, it contains a series $p$ whose
    constant coefficient is zero and whose germ is irreducible.  Every
    representative of a unit germ has nonzero constant coefficient, and the
    refinement property makes $p$ primal.  The scalar argument in
    \ref{lem:primal-zero-residue-fraction-field} therefore gives
    $K=\operatorname{Frac}(Z)$.
  -/)]
theorem fracSubring_eq_top_of_hasFourFactorRefinement_truncationIntegerPart
    (Z : Subring K) (h : HasFourFactorRefinement (truncationIntegerPart G Z)) :
    Subring.fracSubring Z = ⊤ := by
  let pi := constantCoeffAlgHom (G := G) (L := K)
  let J := (cantorBendixsonValuation (G := G) (R := K)).supp
  let phi : Nonpositive G K →+* Nonpositive G K ⧸ J := Ideal.Quotient.mk J
  let e := truncationIntegerPartEquivResidueSubring (G := G) (L := K) Z
  have hrefinement : HasFourFactorRefinement (Subring.residueSubring pi Z) :=
    h.map_mulEquiv e.toMulEquiv
  obtain ⟨p, hpcoeff, hpIrr⟩ :=
    exists_irreducible_cantorBendixson_germ_with_constantCoeff_zero (G := G) (K := K)
  have hpπ : pi p = 0 := by
    simpa [pi, constantCoeffAlgHom_apply] using hpcoeff
  exact Subring.fracSubring_eq_top_of_isPrimal_of_irreducible_map phi
    (p := p) (S := Z) (π := pi) hpπ
    (by simpa [phi, J] using hpIrr)
    (fun a ha ↦ by
      simpa [pi, phi, J, constantCoeffAlgHom_apply] using
        (constantCoeff_ne_zero_of_isUnit_cantorBendixson_germ ha))
    (hrefinement.isPrimal ⟨p, by simp [hpπ]⟩)

end HahnSeries.Nonpositive
