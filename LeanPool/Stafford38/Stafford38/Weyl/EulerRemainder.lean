/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Ore.Associativity
import LeanPool.Stafford38.Stafford38.Weyl.EulerSubring
import LeanPool.Stafford38.Stafford38.Weyl.EulerResidue
import LeanPool.Stafford38.Stafford38.Weyl.OuterOreMonic

/-!
# Positive outer-Ore remainders

An element whose outer momentum support is strictly below `N` acquires a
right coordinate factor after multiplication by `x^N` on either side.  The
cofactors remain in the concrete Euler subring.
-/

namespace Stafford38.WeylEulerRemainder

open Polynomial
open Stafford
open AlgebraicAnalysis
open AlgebraicAnalysis.OreDivision
open AlgebraicAnalysis.OreAssociativity
open Stafford38.OreCoordinateStage
open Stafford38.OrePairStage
open Stafford38.WeylEulerSubring
open Stafford38.WeylEulerResidue
open Stafford38.EulerSurjectivity

noncomputable section


variable (B : Type*) [Ring B] [Algebra ℚ B]

local instance : Algebra ℚ (CoordinateStage (B := B)) :=
  coordinateStageAlgebra

local instance : Algebra ℚ (PairStage (B := B)) :=
  pairStageAlgebra

/-- Both products by `x^N` have a right `x` factor with cofactor in the Euler
subring. -/
def HasPositiveCoordinateFactor (N : ℕ) (z : PairStage (B := B)) : Prop :=
  ∃ U V : pairEulerSubring B,
    z * pairCoordinate ^ N = (U : PairStage (B := B)) * pairCoordinate ∧
    pairCoordinate ^ N * z = (V : PairStage (B := B)) * pairCoordinate

omit [Algebra ℚ B] in
lemma hasPositiveCoordinateFactor_zero (N : ℕ) :
    HasPositiveCoordinateFactor B N 0 := by
  exact ⟨0, 0, by simp, by simp⟩

omit [Algebra ℚ B] in
lemma hasPositiveCoordinateFactor_add {N : ℕ} {z w : PairStage (B := B)}
    (hz : HasPositiveCoordinateFactor B N z)
    (hw : HasPositiveCoordinateFactor B N w) :
    HasPositiveCoordinateFactor B N (z + w) := by
  obtain ⟨Uz, Vz, hz₁, hz₂⟩ := hz
  obtain ⟨Uw, Vw, hw₁, hw₂⟩ := hw
  refine ⟨Uz + Uw, Vz + Vw, ?_, ?_⟩
  · simpa only [add_mul, Subring.coe_add] using congrArg₂ (· + ·) hz₁ hw₁
  · simpa only [mul_add, add_mul, Subring.coe_add] using congrArg₂ (· + ·) hz₂ hw₂

omit [Algebra ℚ B] in
lemma pairCoordinate_pow_mul_coefficient (b : B) : ∀ N : ℕ,
    pairCoordinate ^ N * pairCoefficient b =
      pairCoefficient b * pairCoordinate ^ N
  | 0 => by simp
  | N + 1 => by
      calc
        pairCoordinate ^ (N + 1) * pairCoefficient b =
            (pairCoordinate ^ N * pairCoordinate) * pairCoefficient b := by
              rw [pow_succ]
        _ = pairCoordinate ^ N * (pairCoordinate * pairCoefficient b) := by
              rw [mul_assoc]
        _ = pairCoordinate ^ N * (pairCoefficient b * pairCoordinate) := by
              rw [pairCoordinate_mul_coefficient]
        _ = (pairCoordinate ^ N * pairCoefficient b) * pairCoordinate := by
              rw [mul_assoc]
        _ = pairCoefficient b * pairCoordinate ^ (N + 1) := by
              rw [pairCoordinate_pow_mul_coefficient b N, pow_succ, mul_assoc]

/-- A single ordered monomial with outer momentum exponent below `N` has the
two required positive factorizations. -/
theorem pairOrderedMonomial_hasPositiveCoordinateFactor
    (b : B) (a j N : ℕ) (hjN : j < N) :
    HasPositiveCoordinateFactor B N
      (pairCoefficient b * pairCoordinate ^ a * pairMomentum ^ j) := by
  obtain ⟨f, hf⟩ := exists_eulerPolynomial_d_pow_mul_x_pow
    (A := PairStage (B := B)) pairCoordinate pairMomentum
    pairMomentum_mul_coordinate j
  have hpoly : eulerPolynomialEval pairCoordinate pairMomentum f ∈
      pairEulerSubring B :=
    eulerPolynomialEval_mem_eulerSubring (pairOldSubring B)
      pairCoordinate pairMomentum (rational_mem_pairOldSubring B) f
  have hb : pairCoefficient b ∈ pairEulerSubring B :=
    coefficient_mem_eulerSubring (pairOldSubring B)
      pairCoordinate pairMomentum ⟨pairCoefficient b, ⟨b, rfl⟩⟩
  have hxa : pairCoordinate ^ a ∈ pairEulerSubring B :=
    (pairEulerSubring B).pow_mem
      (coordinate_mem_eulerSubring (pairOldSubring B)
        pairCoordinate pairMomentum) a
  have hxleft : pairCoordinate ^ (N - j - 1) ∈ pairEulerSubring B :=
    (pairEulerSubring B).pow_mem
      (coordinate_mem_eulerSubring (pairOldSubring B)
        pairCoordinate pairMomentum) (N - j - 1)
  let U : pairEulerSubring B :=
    ⟨pairCoefficient b * pairCoordinate ^ a *
        eulerPolynomialEval pairCoordinate pairMomentum f *
          pairCoordinate ^ (N - j - 1),
      (pairEulerSubring B).mul_mem
        ((pairEulerSubring B).mul_mem
          ((pairEulerSubring B).mul_mem hb hxa) hpoly) hxleft⟩
  obtain ⟨V, hV⟩ :=
    pairOrderedMonomial_eq_eulerSubring_mul_coordinate B b (N + a) j
      (by omega)
  refine ⟨U, V, ?_, ?_⟩
  · have hpowN : (pairCoordinate (B := B)) ^ N =
        pairCoordinate ^ j * pairCoordinate ^ (N - j) := by
      rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hjN)]
    have hpowDiff : (pairCoordinate (B := B)) ^ (N - j) =
        pairCoordinate ^ (N - j - 1) * pairCoordinate := by
      calc
        pairCoordinate ^ (N - j) =
            pairCoordinate ^ ((N - j - 1) + 1) := by congr 1; omega
        _ = pairCoordinate ^ (N - j - 1) * pairCoordinate := by
          rw [pow_add, pow_one]
    change
      (pairCoefficient b * pairCoordinate ^ a * pairMomentum ^ j) *
          pairCoordinate ^ N =
        (pairCoefficient b * pairCoordinate ^ a *
            eulerPolynomialEval pairCoordinate pairMomentum f *
              pairCoordinate ^ (N - j - 1)) * pairCoordinate
    calc
      (pairCoefficient b * pairCoordinate ^ a * pairMomentum ^ j) *
          pairCoordinate ^ N =
        pairCoefficient b * pairCoordinate ^ a *
          (pairMomentum ^ j * pairCoordinate ^ j) *
            pairCoordinate ^ (N - j) := by
              rw [hpowN]
              simp only [mul_assoc]
      _ = pairCoefficient b * pairCoordinate ^ a *
          eulerPolynomialEval pairCoordinate pairMomentum f *
            pairCoordinate ^ (N - j) := by
              rw [hf]
      _ = (pairCoefficient b * pairCoordinate ^ a *
            eulerPolynomialEval pairCoordinate pairMomentum f *
              pairCoordinate ^ (N - j - 1)) * pairCoordinate := by
              rw [hpowDiff]
              simp only [mul_assoc]
  · calc
      pairCoordinate ^ N *
          (pairCoefficient b * pairCoordinate ^ a * pairMomentum ^ j) =
        pairCoefficient b * pairCoordinate ^ (N + a) * pairMomentum ^ j := by
          calc
            pairCoordinate ^ N *
                (pairCoefficient b * pairCoordinate ^ a * pairMomentum ^ j) =
              (pairCoordinate ^ N * pairCoefficient b) *
                pairCoordinate ^ a * pairMomentum ^ j := by
                  simp only [mul_assoc]
            _ = (pairCoefficient b * pairCoordinate ^ N) *
                pairCoordinate ^ a * pairMomentum ^ j := by
                  rw [pairCoordinate_pow_mul_coefficient B b N]
            _ = pairCoefficient b * pairCoordinate ^ (N + a) *
                pairMomentum ^ j := by
                  rw [pow_add]
                  simp only [mul_assoc]
      _ = (V : PairStage (B := B)) * pairCoordinate := hV

private lemma coordinateCoefficientTerm_hasPositive
    (c : CoordinateStage (B := B)) (j N : ℕ) (hjN : j < N) :
    HasPositiveCoordinateFactor B N
      (normalCoefficient coordinateDerivation c * pairMomentum ^ j) := by
  let q := (normalFormAddEquiv (zeroDerivation (B := B))).symm c
  have hc : c = normalForm (zeroDerivation (B := B)) q := by
    exact (normalFormAddEquiv (zeroDerivation (B := B))).apply_symm_apply c |>.symm
  rw [hc]
  induction q using Polynomial.induction_on' with
  | add q r hq hr =>
      rw [normalForm_add,
        (normalCoefficient (coordinateDerivation (B := B))).map_add, add_mul]
      exact hasPositiveCoordinateFactor_add (B := B) hq hr
  | monomial a b =>
      rw [normalForm_monomial,
        (normalCoefficient (coordinateDerivation (B := B))).map_mul,
        (normalCoefficient (coordinateDerivation (B := B))).map_pow]
      exact pairOrderedMonomial_hasPositiveCoordinateFactor B b a j N hjN

/-- Every element whose outer momentum support lies below `N` has both
positive right-coordinate factorizations. -/
theorem hasPositiveCoordinateFactor_of_outer_support
    (z : PairStage (B := B)) (N : ℕ)
    (hsupport : ∀ j ∈
      ((normalFormAddEquiv coordinateDerivation).symm z).support, j < N) :
    HasPositiveCoordinateFactor B N z := by
  let q := (normalFormAddEquiv coordinateDerivation).symm z
  have hz : z = normalForm coordinateDerivation q := by
    exact (normalFormAddEquiv coordinateDerivation).apply_symm_apply z |>.symm
  rw [hz, ← Polynomial.sum_monomial_eq q]
  change HasPositiveCoordinateFactor B N
    (normalFormAddHom (coordinateDerivation (B := B))
      (∑ j ∈ q.support, Polynomial.monomial j (q.coeff j)))
  rw [map_sum]
  refine Finset.sum_induction (M := PairStage (B := B))
    (fun j => normalFormAddHom (coordinateDerivation (B := B))
      (Polynomial.monomial j (q.coeff j)))
    (HasPositiveCoordinateFactor B N) ?_ ?_ ?_
  · intro a b ha hb
    exact hasPositiveCoordinateFactor_add (B := B) ha hb
  · exact hasPositiveCoordinateFactor_zero B N
  · intro j hj
    change HasPositiveCoordinateFactor B N
      (normalForm (coordinateDerivation (B := B))
        (Polynomial.monomial j (q.coeff j)))
    rw [normalForm_monomial]
    exact coordinateCoefficientTerm_hasPositive B (q.coeff j) j N
      (hsupport j hj)

omit [Algebra ℚ B] in
lemma support_sub_X_pow_lt
    (H : Polynomial (CoordinateStage (B := B))) (N : ℕ)
    (hN : H.coeff N = 1)
    (hgt : ∀ j, N < j → H.coeff j = 0) :
    ∀ j ∈ (H - Polynomial.X ^ N).support, j < N := by
  intro j hj
  by_contra hnot
  have hle : N ≤ j := Nat.le_of_not_gt hnot
  have hcoeff : (H - Polynomial.X ^ N).coeff j = 0 := by
    rcases hle.eq_or_lt with rfl | hlt
    · simp [hN]
    · rw [Polynomial.coeff_sub, hgt j hlt]
      simp [Polynomial.coeff_X_pow, hlt.ne']
  exact (Polynomial.mem_support_iff.mp hj) hcoeff

/-- Subtracting the monic outer power leaves an element to which the positive
factor theorem applies. -/
theorem normalForm_sub_X_pow_hasPositiveCoordinateFactor
    (H : Polynomial (CoordinateStage (B := B))) (N : ℕ)
    (hN : H.coeff N = 1)
    (hgt : ∀ j, N < j → H.coeff j = 0) :
    HasPositiveCoordinateFactor B N
      (normalForm (coordinateDerivation (B := B))
        (H - Polynomial.X ^ N)) := by
  apply hasPositiveCoordinateFactor_of_outer_support B
  intro j hj
  change j ∈ ((normalFormAddEquiv (coordinateDerivation (B := B))).symm
    ((normalFormAddEquiv (coordinateDerivation (B := B)))
      (H - Polynomial.X ^ N))).support at hj
  rw [(normalFormAddEquiv (coordinateDerivation (B := B))).symm_apply_apply] at hj
  exact support_sub_X_pow_lt B H N hN hgt j hj

/-- The positive-factor interface turns the explicit Euler residue into the
exact shaped residue consumed by quotient surjectivity. -/
theorem positiveEulerResidue_eq_eulerSubring_mul_coordinate
    (d sigma : PairStage (B := B)) (N : ℕ)
    (hd : d = pairMomentum ^ N + sigma)
    (hpositive : HasPositiveCoordinateFactor B N sigma) :
    ∃ U : pairEulerSubring B,
      1 + (U : PairStage (B := B)) * pairCoordinate ∈
        canonicalRightIdeal pairCoordinate d N := by
  obtain ⟨u, v, hmem⟩ := positiveEulerResidue_polynomial_mem
    pairCoordinate pairMomentum d sigma N pairMomentum_mul_coordinate hd
  obtain ⟨U, V, hright, hleft⟩ := hpositive
  obtain ⟨su, hsu⟩ := coordinate_mul_eulerPolynomial
    (pairOldSubring B) pairCoordinate pairMomentum
    pairMomentum_mul_coordinate (pairOldSubring_commutes_coordinate B)
    (rational_mem_pairOldSubring B) u
  obtain ⟨sv, hsv⟩ := coordinate_mul_eulerPolynomial
    (pairOldSubring B) pairCoordinate pairMomentum
    pairMomentum_mul_coordinate (pairOldSubring_commutes_coordinate B)
    (rational_mem_pairOldSubring B) v
  refine ⟨U * su + V * sv, ?_⟩
  convert hmem using 1
  simp only [Subring.coe_add, Subring.coe_mul, add_mul]
  rw [hright, hleft]
  simp only [mul_assoc]
  rw [hsu, hsv]

omit [Algebra ℚ B] in
private lemma coordinateCoefficient_mem_pairGeneratorSubring
    (c : CoordinateStage (B := B)) :
    normalCoefficient coordinateDerivation c ∈
      Subring.closure (((pairOldSubring B : Subring (PairStage (B := B))) :
        Set (PairStage (B := B))) ∪ {pairCoordinate, pairMomentum}) := by
  let q := (normalFormAddEquiv (zeroDerivation (B := B))).symm c
  have hc : c = normalForm (zeroDerivation (B := B)) q := by
    exact (normalFormAddEquiv (zeroDerivation (B := B))).apply_symm_apply c |>.symm
  rw [hc]
  induction q using Polynomial.induction_on' with
  | add q r hq hr =>
      rw [normalForm_add,
        (normalCoefficient (coordinateDerivation (B := B))).map_add]
      exact Subring.add_mem _ hq hr
  | monomial a b =>
      rw [normalForm_monomial,
        (normalCoefficient (coordinateDerivation (B := B))).map_mul,
        (normalCoefficient (coordinateDerivation (B := B))).map_pow]
      apply Subring.mul_mem
      · apply Subring.subset_closure
        exact Or.inl ⟨b, rfl⟩
      · apply Subring.pow_mem
        apply Subring.subset_closure
        exact Or.inr (Or.inl rfl)

/-- The old coefficient ring together with the new coordinate and momentum
generates the complete pair stage. -/
theorem closure_pairOldSubring_union_coordinate_momentum_eq_top :
    Subring.closure (((pairOldSubring B : Subring (PairStage (B := B))) :
      Set (PairStage (B := B))) ∪ {pairCoordinate, pairMomentum}) = ⊤ := by
  apply top_unique
  intro z hz
  let q := (normalFormAddEquiv (coordinateDerivation (B := B))).symm z
  have hzq : z = normalForm coordinateDerivation q := by
    exact (normalFormAddEquiv coordinateDerivation).apply_symm_apply z |>.symm
  rw [hzq]
  induction q using Polynomial.induction_on' with
  | add q r hq hr =>
      rw [normalForm_add]
      exact Subring.add_mem _ hq hr
  | monomial j c =>
      rw [normalForm_monomial]
      apply Subring.mul_mem
      · exact coordinateCoefficient_mem_pairGeneratorSubring B c
      · apply Subring.pow_mem
        apply Subring.subset_closure
        exact Or.inr (Or.inr rfl)


section Presented

open Stafford38.OreIteratedPairStage
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylOuterOreMonic
open Stafford38.WeylPBWMonicBridge

universe u

variable (k : Type u) [Field k] [Algebra ℚ k]

local instance iteratedRatAlgebra :
    (n : ℕ) → Algebra ℚ (IteratedPairStage k n)
  | 0 => by
      change Algebra ℚ k
      infer_instance
  | n + 1 => by
      letI : Algebra ℚ (IteratedPairStage k n) := iteratedRatAlgebra n
      change Algebra ℚ (PairStage (B := IteratedPairStage k n))
      exact pairStageAlgebra

local instance (n : ℕ) : Algebra k (IteratedPairStage k n) :=
  iteratedPairStageAlgebra k n

local instance (n : ℕ) :
    Algebra ℚ (CoordinateStage (B := IteratedPairStage k n)) :=
  coordinateStageAlgebra

local instance (n : ℕ) :
    Algebra ℚ (PairStage (B := IteratedPairStage k n)) :=
  pairStageAlgebra

/-- The concrete remainder of a normalized presented Weyl operator satisfies
both positive-coordinate factorizations. -/
theorem presentedRemainder_hasPositiveCoordinateFactor
    (n N : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    HasPositiveCoordinateFactor (IteratedPairStage k n) N
      (presentedToIterated k (n + 1) d - stageMomentum k n ^ N) := by
  let H := presentedOuterPolynomial k n d
  have hpositive := normalForm_sub_X_pow_hasPositiveCoordinateFactor
    (IteratedPairStage k n) H N
    (outer_coeff_eq_one_at_bound k n N hd)
    (fun j hj => outer_coeff_eq_zero_of_exponent_gt k n N hd hj)
  have hnormal :
      normalForm (coordinateDerivation (B := IteratedPairStage k n))
          (H - Polynomial.X ^ N) =
        presentedToIterated k (n + 1) d - stageMomentum k n ^ N := by
    change normalFormAddHom coordinateDerivation (H - Polynomial.X ^ N) = _
    have hH : normalForm (coordinateDerivation (B := IteratedPairStage k n)) H =
        presentedToIterated k (n + 1) d := by
      exact (normalFormAddEquiv coordinateDerivation).apply_symm_apply _
    have hH' : normalFormAddHom coordinateDerivation H =
        presentedToIterated k (n + 1) d := hH
    rw [map_sub, hH']
    congr 1
    rw [Polynomial.X_pow_eq_monomial]
    change normalForm coordinateDerivation (Polynomial.monomial N 1) = _
    rw [normalForm_monomial]
    rw [map_one, one_mul]
    change pairMomentum (B := IteratedPairStage k n) ^ N =
      stageMomentum k n ^ N
    rfl
  rw [hnormal] at hpositive
  exact hpositive

/-- The normalized presented operator has the exact positive Euler residue in
its literal canonical right ideal. -/
theorem presentedPositiveEulerResidue
    (n N : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    ∃ U : pairEulerSubring (IteratedPairStage k n),
      1 + (U : PairStage (B := IteratedPairStage k n)) * pairCoordinate ∈
        canonicalRightIdeal (pairCoordinate (B := IteratedPairStage k n))
          (presentedToIterated k (n + 1) d) N := by
  let sigma := presentedToIterated k (n + 1) d - stageMomentum k n ^ N
  have hdecomp : presentedToIterated k (n + 1) d =
      stageMomentum k n ^ N + sigma := by
    simp [sigma]
  have hpositive : HasPositiveCoordinateFactor (IteratedPairStage k n) N sigma :=
    presentedRemainder_hasPositiveCoordinateFactor k n N hd
  exact positiveEulerResidue_eq_eulerSubring_mul_coordinate
    (IteratedPairStage k n) (presentedToIterated k (n + 1) d) sigma N
      hdecomp hpositive

/-- Right multiplication by the selected coordinate is onto the concrete
canonical quotient. -/
theorem presentedCanonicalQuotient_rightMul_coordinate_surjective
    (n N : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    Function.Surjective
      (rightMul
        (canonicalRightIdeal (pairCoordinate (B := IteratedPairStage k n))
          (presentedToIterated k (n + 1) d) N)
        (pairCoordinate (B := IteratedPairStage k n))) := by
  apply rightMul_surjective_of_euler_normal
    (R := pairEulerSubring (IteratedPairStage k n))
    (p := pairMomentum (B := IteratedPairStage k n))
  · exact coordinate_normal_eulerSubring
      (pairOldSubring (IteratedPairStage k n))
      pairCoordinate pairMomentum
      (stageMomentum_mul_coordinate k n)
      (pairOldSubring_commutes_coordinate (IteratedPairStage k n))
  · exact euler_mem_eulerSubring
      (pairOldSubring (IteratedPairStage k n))
      pairCoordinate pairMomentum
  · exact presentedPositiveEulerResidue k n N hd
  · apply closure_eulerSubring_union_momentum_eq_top
    exact closure_pairOldSubring_union_coordinate_momentum_eq_top
      (IteratedPairStage k n)


end Presented

end
end Stafford38.WeylEulerRemainder
