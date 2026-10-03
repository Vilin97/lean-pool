/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.Homogeneous
public import LeanPool.BooleanMultiplication.N4.BooleanIdentities

/-!
# ANF low-product bridge

This module turns the exterior prefix-rigidity lemma into a statement about
actual Boolean ANFs.  All coordinate certificates below range only over an
input coordinate and one of the three rational places; no circuit states are
enumerated.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

@[simp] theorem linearANF_zero : linearANF (0 : LinearForm) = 0 := by
  simp [linearANF]

theorem linearANF_add (ell m : LinearForm) :
    linearANF (ell + m) = linearANF ell + linearANF m := by
  simp only [linearANF, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem linearANF_smul (a : F₂) (ell : LinearForm) :
    linearANF (a • ell) = a • linearANF ell := by
  simp only [linearANF, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]

theorem linearANF_coordinate (i : Fin 8) :
    linearANF (coordinateLinear i) = X i := by
  fin_cases i <;> simp [linearANF, coordinateLinear]

theorem affineANF_add (a b : F₂) (ell m : LinearForm) :
    affineANF (a + b) (ell + m) =
      affineANF a ell + affineANF b m := by
  rw [affineANF, affineANF, affineANF, linearANF_add]
  module

theorem affineANF_smul (a b : F₂) (ell : LinearForm) :
    affineANF (a * b) (a • ell) = a • affineANF b ell := by
  rw [affineANF, affineANF, linearANF_smul]
  simp only [smul_add, smul_smul]

theorem affineANF_mem (a : F₂) (ell : LinearForm) :
    affineANF a ell ∈ affine 8 := by
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ _ (one_mem_affine 8)
  · rw [linearANF]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (X_mem_affine i)

theorem exists_affineANF_of_mem {p : ANF 8} (hp : p ∈ affine 8) :
    ∃ (a : F₂) (ell : LinearForm), p = affineANF a ell := by
  refine Submodule.span_induction
    (p := fun p _ => ∃ (a : F₂) (ell : LinearForm),
      p = affineANF a ell) ?_ ?_ ?_ ?_ hp
  · intro q hq
    rcases hq with hq | hq
    · have : q = 1 := by simpa only [Set.mem_singleton_iff] using hq
      subst q
      exact ⟨1, 0, by simp [affineANF]⟩
    · rcases hq with ⟨i, rfl⟩
      exact ⟨0, coordinateLinear i, by
        simp [affineANF, linearANF_coordinate]⟩
  · exact ⟨0, 0, by simp [affineANF]⟩
  · rintro p q _ _ ⟨a, ell, rfl⟩ ⟨b, m, rfl⟩
    exact ⟨a + b, ell + m, (affineANF_add a b ell m).symm⟩
  · rintro a p _ ⟨b, ell, rfl⟩
    exact ⟨a * b, a • ell, (affineANF_smul a b ell).symm⟩

@[simp] theorem rationalANF_zero :
    rationalANF (0 : Fin 3 → F₂) = 0 := by
  change targetANFLinear (rationalCoeffRep 0) = 0
  have hrep : rationalCoeffRep (0 : Fin 3 → F₂) = 0 := by
    funext i
    fin_cases i <;> simp [rationalCoeffRep]
  rw [hrep, map_zero]

private theorem anfThreeProjection_one :
    anfThreeProjection (1 : ANF 8) = 0 := by
  funext i j k
  change (if ({i, j, k} : Finset (Fin 8)).card = 3 then
    (1 : ANF 8).coeff ⟨{i, j, k}⟩ else 0) = 0
  split
  · rename_i hcard
    rw [MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply]
    split
    · rename_i heq
      have hc := congrArg (fun s : Monomial 8 => s.vars.card) heq
      simp [hcard] at hc
    · rfl
  · rfl

private theorem anfThreeProjection_X_mul_X (i j : Fin 8) :
    anfThreeProjection (X i * X j) = 0 := by
  rw [show X i * X j = monomial {i, j} by simp [X]]
  rw [anfThreeProjection_monomial]
  funext r s t
  by_cases hcard : ({r, s, t} : Finset (Fin 8)).card = 3
  · simp only [monomialThree, hcard, ite_eq_left, Pi.zero_apply]
    split
    · rename_i heq
      have hc := congrArg Finset.card heq
      have hp : ({i, j} : Finset (Fin 8)).card ≤ 2 :=
        Finset.card_le_two
      omega
    · rfl
  · simp [monomialThree, hcard]

private theorem anfThreeProjection_X (i : Fin 8) :
    anfThreeProjection (X i) = 0 := by
  rw [X, anfThreeProjection_monomial]
  funext r s t
  by_cases hcard : ({r, s, t} : Finset (Fin 8)).card = 3
  · simp only [monomialThree, hcard, ite_eq_left, Pi.zero_apply]
    split
    · rename_i heq
      have hc := congrArg Finset.card heq
      simp [hcard] at hc
    · rfl
  · simp [monomialThree, hcard]

private theorem anfThreeProjection_linearANF (ell : LinearForm) :
    anfThreeProjection (linearANF ell) = 0 := by
  rw [linearANF]
  simp only [map_sum, map_smul, anfThreeProjection_X, smul_zero, Finset.sum_const_zero]

theorem anfThreeProjection_linear_mul_linear
    (ell m : LinearForm) :
    anfThreeProjection (linearANF ell * linearANF m) = 0 := by
  rw [linearANF, linearANF]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, map_sum, map_smul,
    anfThreeProjection_X_mul_X, smul_zero, Finset.sum_const_zero]

theorem anfThreeProjection_affine_mul_affine
    (a b : F₂) (ell m : LinearForm) :
    anfThreeProjection (affineANF a ell * affineANF b m) = 0 := by
  rw [affineANF, affineANF]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, map_add,
    map_smul, anfThreeProjection_one, anfThreeProjection_linearANF,
    anfThreeProjection_linear_mul_linear, smul_zero, add_zero]

private theorem quarticProbeANF_one :
    quarticProbeANF (1 : ANF 8) = 0 := by
  funext t
  change (1 : ANF 8).coeff ⟨quarticProbeSet t⟩ = 0
  rw [MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  split
  · rename_i heq
    have hc := congrArg (fun s : Monomial 8 => s.vars.card) heq
    have hp : (quarticProbeSet t).card = 4 := by fin_cases t <;> decide
    simp [hp] at hc
  · rfl

private theorem quarticProbeANF_X_mul_X (i j : Fin 8) :
    quarticProbeANF (X i * X j) = 0 := by
  rw [show X i * X j = monomial {i, j} by simp [X]]
  funext t
  rw [quarticProbeANF_monomial]
  split
  · rename_i heq
    have hc := congrArg Finset.card heq
    have hp : ({i, j} : Finset (Fin 8)).card ≤ 2 := Finset.card_le_two
    have hprobe : (quarticProbeSet t).card = 4 := by
      fin_cases t <;> decide
    omega
  · rfl

private theorem quarticProbeANF_X (i : Fin 8) :
    quarticProbeANF (X i) = 0 := by
  funext t
  change (monomial {i} : ANF 8).coeff ⟨quarticProbeSet t⟩ = 0
  rw [coeff_monomial]
  split
  · rename_i heq
    have hc := congrArg Finset.card heq
    have hp : (quarticProbeSet t).card = 4 := by
      fin_cases t <;> decide
    simp [hp] at hc
  · rfl

private theorem quarticProbeANF_linearANF (ell : LinearForm) :
    quarticProbeANF (linearANF ell) = 0 := by
  rw [linearANF]
  simp only [map_sum, map_smul, quarticProbeANF_X, smul_zero, Finset.sum_const_zero]

theorem quarticProbeANF_affine_mul_affine
    (a b : F₂) (ell m : LinearForm) :
    quarticProbeANF (affineANF a ell * affineANF b m) = 0 := by
  rw [affineANF, affineANF, linearANF, linearANF]
  simp only [add_mul, mul_add, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, map_add, map_sum, map_smul, quarticProbeANF_one, quarticProbeANF_X,
    quarticProbeANF_X_mul_X, smul_zero, add_zero, Finset.sum_const_zero]

private theorem quarticProbeANF_X_mul_targetPair
    (r : Fin 8) (i j : Fin 4) :
    quarticProbeANF (X r * monomial (targetPair i j)) = 0 := by
  rw [X, monomial_mul]
  funext t
  rw [quarticProbeANF_monomial]
  split
  · rename_i heq
    have hc := congrArg Finset.card heq
    have hpair : (targetPair i j).card = 2 := by
      fin_cases i <;> fin_cases j <;> decide
    have hle : ({r} ∪ targetPair i j).card ≤ 3 := by
      calc
        ({r} ∪ targetPair i j).card ≤
            ({r} : Finset (Fin 8)).card + (targetPair i j).card :=
          Finset.card_union_le ({r} : Finset (Fin 8)) (targetPair i j)
        _ = 3 := by simp [hpair]
    have hprobe : (quarticProbeSet t).card = 4 := by
      fin_cases t <;> decide
    omega
  · rfl

private theorem quarticProbeANF_linear_mul_targetANF
    (ell : LinearForm) (c : TargetCoeff) :
    quarticProbeANF (linearANF ell * targetANF c) = 0 := by
  rw [linearANF, targetANF_eq_double_sum]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, map_sum, map_smul,
    quarticProbeANF_X_mul_targetPair, smul_zero, Finset.sum_const_zero]

private theorem quarticProbeANF_rationalANF (α : Fin 3 → F₂) :
    quarticProbeANF (rationalANF α) = 0 := by
  apply quarticProbeANF_eq_zero_of_mem_targetAmbient
  exact Submodule.mem_sup_right (targetANF_mem_mulTarget _)

theorem quarticProbeANF_affine_mul_rational
    (a : F₂) (ell : LinearForm) (β : Fin 3 → F₂) :
    quarticProbeANF (affineANF a ell * rationalANF β) = 0 := by
  have hlinear : quarticProbeANF
      (linearANF ell * rationalANF β) = 0 := by
    exact quarticProbeANF_linear_mul_targetANF ell (rationalCoeffRep β)
  rw [affineANF, add_mul]
  simp only [smul_mul_assoc, one_mul, map_add, map_smul, quarticProbeANF_rationalANF, hlinear,
    smul_zero, add_zero]

theorem quarticProbeANF_rational_mul_affine
    (α : Fin 3 → F₂) (b : F₂) (m : LinearForm) :
    quarticProbeANF (rationalANF α * affineANF b m) = 0 := by
  rw [mul_comm]
  exact quarticProbeANF_affine_mul_rational b m α

private theorem anfThreeProjection_rationalANF (α : Fin 3 → F₂) :
    anfThreeProjection (rationalANF α) = 0 := by
  apply anfThreeProjection_eq_zero_of_mem_targetAmbient
  exact Submodule.mem_sup_right (targetANF_mem_mulTarget _)

theorem anfThreeProjection_affine_mul_rational
    (a : F₂) (ell : LinearForm) (β : Fin 3 → F₂) :
    anfThreeProjection (affineANF a ell * rationalANF β) =
      vectorWedgeTwo ell (rationalTwo β) := by
  rw [affineANF, add_mul]
  simp only [smul_mul_assoc, one_mul, map_add, map_smul, anfThreeProjection_rationalANF,
    anfThreeProjection_linear_mul_rational, smul_zero, zero_add]

theorem anfThreeProjection_rational_mul_affine
    (α : Fin 3 → F₂) (b : F₂) (m : LinearForm) :
    anfThreeProjection (rationalANF α * affineANF b m) =
      vectorWedgeTwo m (rationalTwo α) := by
  rw [mul_comm]
  exact anfThreeProjection_affine_mul_rational b m α

private theorem anfThreeProjection_rational_mul_rational_of_probe_zero
    (α β : Fin 3 → F₂)
    (hprobe : quarticWedgeProbe (rationalTwo α) (rationalTwo β) = 0) :
    anfThreeProjection (rationalANF α * rationalANF β) = 0 := by
  rcases rational_probe_zero_dependent α β hprobe with hα | hβ | hαβ
  · subst α
    simp
  · subst β
    simp
  · subst β
    rw [anf_mul_self]
    exact anfThreeProjection_rationalANF α

theorem lowProduct_quarticProjection
    (a b : F₂) (ell m : LinearForm) (α β : Fin 3 → F₂) :
    quarticProbeANF
        ((affineANF a ell + rationalANF α) *
          (affineANF b m + rationalANF β)) =
      quarticWedgeProbe (rationalTwo α) (rationalTwo β) := by
  simp only [add_mul, mul_add, map_add, quarticProbeANF_affine_mul_affine,
    quarticProbeANF_affine_mul_rational, quarticProbeANF_rational_mul_affine,
    quarticProbe_rational_mul_rational, zero_add]

theorem lowProduct_cubicProjection_of_quartic_zero
    (a b : F₂) (ell m : LinearForm) (α β : Fin 3 → F₂)
    (hprobe : quarticWedgeProbe (rationalTwo α) (rationalTwo β) = 0) :
    anfThreeProjection
        ((affineANF a ell + rationalANF α) *
          (affineANF b m + rationalANF β)) =
      rationalProductCubic ell m α β := by
  simp only [add_mul, mul_add, map_add, anfThreeProjection_affine_mul_affine,
    anfThreeProjection_affine_mul_rational, anfThreeProjection_rational_mul_affine,
    anfThreeProjection_rational_mul_rational_of_probe_zero α β hprobe, zero_add, add_zero,
    rationalProductCubic]
  rw [add_comm]

/-- The exterior product of two linear forms as a bilinear map. -/
@[expose]
def vectorWedgeBilinear :
    LinearForm →ₗ[F₂] LinearForm →ₗ[F₂] TwoForm where
  toFun ell :=
    { toFun := fun m => vectorWedge ell m
      map_add' := vectorWedge_add_right ell
      map_smul' := fun a m => vectorWedge_smul_right_qp a ell m }
  map_add' ell m := by
    apply LinearMap.ext
    intro n
    exact vectorWedge_add_left_qp ell m n
  map_smul' a ell := by
    apply LinearMap.ext
    intro m
    exact vectorWedge_smul_left_qp a ell m

private theorem anfLinearProjection_X_eq_coordinate (i : Fin 8) :
    anfLinearProjection (X i) = coordinateLinear i := by
  funext j
  simp [coordinateLinear, eq_comm]

private theorem anfTwoProjection_linear_mul_X
    (ell : LinearForm) (j : Fin 8) :
    anfTwoProjection (linearANF ell * X j) =
      vectorWedge ell (coordinateLinear j) := by
  rw [linearANF]
  simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, anfTwoProjection_X_mul_X]
  simp_rw [anfLinearProjection_X_eq_coordinate]
  change (∑ i : Fin 8, ell i •
      vectorWedge (coordinateLinear i) (coordinateLinear j)) = _
  change _ = vectorWedgeBilinear ell (coordinateLinear j)
  conv_rhs => rw [linear_eq_sum_coordinate ell]
  simp only [map_sum, map_smul]
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rfl

theorem anfTwoProjection_linear_mul_linear
    (ell m : LinearForm) :
    anfTwoProjection (linearANF ell * linearANF m) =
      vectorWedge ell m := by
  change anfTwoProjection
      (linearANF ell * ∑ j : Fin 8, m j • X j) = _
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, anfTwoProjection_linear_mul_X]
  change (∑ j : Fin 8, m j •
      vectorWedge ell (coordinateLinear j)) = _
  change _ = vectorWedgeBilinear ell m
  conv_rhs => rw [linear_eq_sum_coordinate m]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro j _
  rfl

private theorem anfTwoProjection_linearANF (ell : LinearForm) :
    anfTwoProjection (linearANF ell) = 0 := by
  apply anfTwoProjection_kills_affine
  rw [linearANF]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (X_mem_affine i)

theorem anfTwoProjection_affine_mul_affine
    (a b : F₂) (ell m : LinearForm) :
    anfTwoProjection (affineANF a ell * affineANF b m) =
      vectorWedge ell m := by
  rw [affineANF, affineANF]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, map_add,
    map_smul, anfTwoProjection_one, anfTwoProjection_linearANF,
    anfTwoProjection_linear_mul_linear, smul_zero, zero_add, add_zero]

/-- The quadratic coordinate array of a squarefree monomial. -/
@[expose] def monomialTwo (s : Finset (Fin 8)) : TwoForm := fun i j =>
  if i = j then 0 else if s = {i, j} then 1 else 0

theorem anfTwoProjection_monomial (s : Finset (Fin 8)) :
    anfTwoProjection (monomial s) = monomialTwo s := by
  funext i j
  by_cases hij : i = j <;>
    simp [anfTwoProjection, monomialTwo, hij, coeff_monomial]

theorem booleanContraction_add_left_h (ell m : LinearForm) (q : TwoForm) :
    booleanContraction (ell + m) q =
      booleanContraction ell q + booleanContraction m q := by
  funext i j
  simp only [booleanContraction, Pi.add_apply]
  ring

theorem booleanContraction_smul_left_h
    (a : F₂) (ell : LinearForm) (q : TwoForm) :
    booleanContraction (a • ell) q =
      a • booleanContraction ell q := by
  funext i j
  simp only [booleanContraction, Pi.smul_apply, smul_eq_mul]
  ring

theorem booleanContraction_add_right_h (ell : LinearForm) (q r : TwoForm) :
    booleanContraction ell (q + r) =
      booleanContraction ell q + booleanContraction ell r := by
  funext i j
  simp only [booleanContraction, Pi.add_apply]
  ring

theorem booleanContraction_smul_right_h
    (a : F₂) (ell : LinearForm) (q : TwoForm) :
    booleanContraction ell (a • q) =
      a • booleanContraction ell q := by
  funext i j
  simp only [booleanContraction, Pi.smul_apply, smul_eq_mul]
  ring

/-- Boolean contraction of a linear form with a two-form, as a bilinear map. -/
def booleanContractionBilinear :
    LinearForm →ₗ[F₂] TwoForm →ₗ[F₂] TwoForm where
  toFun ell :=
    { toFun := fun q => booleanContraction ell q
      map_add' := booleanContraction_add_right_h ell
      map_smul' := fun a q => booleanContraction_smul_right_h a ell q }
  map_add' ell m := by
    apply LinearMap.ext
    intro q
    exact booleanContraction_add_left_h ell m q
  map_smul' a ell := by
    apply LinearMap.ext
    intro q
    exact booleanContraction_smul_left_h a ell q

private theorem anfTwoProjection_three_X_contraction
    (r a b : Fin 8) (hab : a ≠ b) :
    anfTwoProjection (X r * (X a * X b)) =
      booleanContraction (coordinateLinear r)
        (vectorWedge (coordinateLinear a) (coordinateLinear b)) := by
  by_cases hra : r = a
  · subst r
    rw [show X a * (X a * X b) = X a * X b by
      rw [← mul_assoc, X_mul_self]]
    rw [anfTwoProjection_X_mul_X]
    have hlinA : anfLinearProjection (X a) = coordinateLinear a := by
      funext i
      simp [coordinateLinear, eq_comm]
    have hlinB : anfLinearProjection (X b) = coordinateLinear b := by
      funext i
      simp [coordinateLinear, eq_comm]
    rw [hlinA, hlinB]
    funext i j
    simp only [booleanContraction, vectorWedge, coordinateLinear]
    by_cases hia : i = a <;> by_cases hja : j = a <;>
      by_cases hib : i = b <;> by_cases hjb : j = b <;>
        simp_all []
  · by_cases hrb : r = b
    · subst r
      rw [show X b * (X a * X b) = X a * X b by
        calc
          X b * (X a * X b) = X a * (X b * X b) := by ac_rfl
          _ = X a * X b := by rw [X_mul_self]]
      rw [anfTwoProjection_X_mul_X]
      have hlinA : anfLinearProjection (X a) = coordinateLinear a := by
        funext i
        simp [coordinateLinear, eq_comm]
      have hlinB : anfLinearProjection (X b) = coordinateLinear b := by
        funext i
        simp [coordinateLinear, eq_comm]
      rw [hlinA, hlinB]
      funext i j
      simp only [booleanContraction, vectorWedge, coordinateLinear]
      by_cases hia : i = a <;> by_cases hja : j = a <;>
        by_cases hib : i = b <;> by_cases hjb : j = b <;>
          simp_all []
    · rw [show X r * (X a * X b) = monomial {r, a, b} by
        rw [X, X, X, monomial_mul, monomial_mul]
        congr 1]
      funext i j
      by_cases hij : i = j
      · subst j
        change (if i = i then 0 else
          (monomial {r, a, b}).coeff ⟨{i, i}⟩) = _
        rw [ite_eq_left rfl]
        change 0 = (coordinateLinear r i + coordinateLinear r i) *
          vectorWedge (coordinateLinear a) (coordinateLinear b) i i
        rw [@CharTwo.add_self_eq_zero F₂, zero_mul]
      · have hcard : ({r, a, b} : Finset (Fin 8)).card = 3 := by
          simp [hab, hra, hrb, ]
        have hne : ({r, a, b} : Finset (Fin 8)) ≠ {i, j} := by
          intro h
          have hc := congrArg Finset.card h
          have hle := Finset.card_le_two (a := i) (b := j)
          rw [hcard] at hc
          omega
        change (if i = j then 0 else
          (monomial {r, a, b}).coeff ⟨{i, j}⟩) = _
        rw [ite_eq_right hij, coeff_monomial, ite_eq_right hne]
        by_cases hir : i = r
        · subst i
          simp [booleanContraction, coordinateLinear, vectorWedge, hra, hrb,]
        · by_cases hjr : j = r
          · subst j
            simp [booleanContraction, coordinateLinear, vectorWedge, hra, hrb,]
          · simp [booleanContraction, coordinateLinear, hir, hjr]

private theorem monomialTwo_union_targetPair (r : Fin 8) (i j : Fin 4) :
    monomialTwo ({r} ∪ targetPair i j) =
      booleanContraction (coordinateLinear r)
        (vectorWedge (coordinateLinear (aCoord i))
          (coordinateLinear (bCoord j))) := by
  rw [← anfTwoProjection_monomial]
  rw [show monomial ({r} ∪ targetPair i j) =
      X r * (X (aCoord i) * X (bCoord j)) by
    simp [targetPair, X, monomial_mul]]
  apply anfTwoProjection_three_X_contraction
  exact aVar_ne_bVar_index i j

/-- Quadratic part of an input variable times a rational-place product. -/
def quadraticPlaceModel (r : Fin 8) (θ : Fin 3) : TwoForm :=
  ∑ i : Fin 4, ∑ j : Fin 4,
    rationalPlaceCoeff θ (hankelIndex i j) •
      monomialTwo ({r} ∪ targetPair i j)

private theorem quadraticPlaceModel_eq :
    ∀ (r : Fin 8) (θ : Fin 3),
      quadraticPlaceModel r θ =
        booleanContraction (coordinateLinear r) (rationalPlaceTwo θ) := by
  intro r θ
  rw [← targetTwo_rationalPlaceCoeff, targetTwo_eq_double_wedge]
  change quadraticPlaceModel r θ =
    booleanContractionBilinear (coordinateLinear r)
      (∑ i : Fin 4, ∑ j : Fin 4,
        rationalPlaceCoeff θ (hankelIndex i j) •
          vectorWedge (coordinateLinear (aCoord i))
            (coordinateLinear (bCoord j)))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, monomialTwo_union_targetPair]
  rfl

private theorem anfTwoProjection_X_mul_rationalPlace
    (r : Fin 8) (θ : Fin 3) :
    anfTwoProjection (X r * targetANF (rationalPlaceCoeff θ)) =
      booleanContraction (coordinateLinear r) (rationalPlaceTwo θ) := by
  rw [targetANF_eq_double_sum]
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, X, monomial_mul,
    anfTwoProjection_monomial]
  exact quadraticPlaceModel_eq r θ

private theorem anfTwoProjection_linear_mul_rationalPlace
    (ell : LinearForm) (θ : Fin 3) :
    anfTwoProjection
        (linearANF ell * targetANF (rationalPlaceCoeff θ)) =
      booleanContraction ell (rationalPlaceTwo θ) := by
  rw [linearANF]
  simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul,
    anfTwoProjection_X_mul_rationalPlace]
  change (∑ i : Fin 8, ell i •
      booleanContraction (coordinateLinear i) (rationalPlaceTwo θ)) = _
  change _ = booleanContractionBilinear ell (rationalPlaceTwo θ)
  conv_rhs => rw [linear_eq_sum_coordinate ell]
  simp only [map_sum, map_smul]
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rfl

theorem anfTwoProjection_linear_mul_rational
    (ell : LinearForm) (β : Fin 3 → F₂) :
    anfTwoProjection (linearANF ell * rationalANF β) =
      booleanContraction ell (rationalTwo β) := by
  rw [rationalANF_eq_sum]
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul,
    anfTwoProjection_linear_mul_rationalPlace]
  change (∑ θ : Fin 3, β θ •
      booleanContraction ell (rationalPlaceTwo θ)) = _
  change _ = booleanContractionBilinear ell (rationalTwo β)
  conv_rhs => rw [rationalTwo]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro θ _
  rfl

theorem anfTwoProjection_rationalANF (α : Fin 3 → F₂) :
    anfTwoProjection (rationalANF α) = rationalTwo α := by
  exact anfTwoProjection_targetANF (rationalCoeffRep α) |>.trans
    (targetTwo_rationalCoeffRep α)

theorem anfTwoProjection_affine_mul_rational
    (a : F₂) (ell : LinearForm) (β : Fin 3 → F₂) :
    anfTwoProjection (affineANF a ell * rationalANF β) =
      a • rationalTwo β + booleanContraction ell (rationalTwo β) := by
  rw [affineANF, add_mul]
  simp only [smul_mul_assoc, one_mul, map_add, map_smul, anfTwoProjection_rationalANF,
    anfTwoProjection_linear_mul_rational]

theorem anfTwoProjection_rational_mul_affine
    (α : Fin 3 → F₂) (b : F₂) (m : LinearForm) :
    anfTwoProjection (rationalANF α * affineANF b m) =
      b • rationalTwo α + booleanContraction m (rationalTwo α) := by
  rw [mul_comm]
  exact anfTwoProjection_affine_mul_rational b m α

private theorem twoHadamard_self (q : TwoForm) :
    twoHadamard q q = q := by
  funext i j
  simp only [twoHadamard]
  exact N3Certificate.mul_self_f2 (q i j)

private theorem twoHadamard_zero_left (q : TwoForm) :
    twoHadamard 0 q = 0 := by funext i j; simp [twoHadamard]

private theorem twoHadamard_zero_right (q : TwoForm) :
    twoHadamard q 0 = 0 := by funext i j; simp [twoHadamard]

private theorem anfTwoProjection_rational_mul_rational_of_probe_zero
    (α β : Fin 3 → F₂)
    (hprobe : quarticWedgeProbe (rationalTwo α) (rationalTwo β) = 0) :
    anfTwoProjection (rationalANF α * rationalANF β) =
      twoHadamard (rationalTwo α) (rationalTwo β) := by
  rcases rational_probe_zero_dependent α β hprobe with hα | hβ | hαβ
  · subst α
    rw [rationalANF_zero, zero_mul, map_zero, rationalTwo_zero,
      twoHadamard_zero_left]
  · subst β
    rw [rationalANF_zero, mul_zero, map_zero, rationalTwo_zero,
      twoHadamard_zero_right]
  · subst β
    rw [anf_mul_self, anfTwoProjection_rationalANF, twoHadamard_self]

theorem lowProduct_quadraticProjection_of_quartic_zero
    (a b : F₂) (ell m : LinearForm) (α β : Fin 3 → F₂)
    (hprobe : quarticWedgeProbe (rationalTwo α) (rationalTwo β) = 0) :
    anfTwoProjection
        ((affineANF a ell + rationalANF α) *
          (affineANF b m + rationalANF β)) =
      rationalProductQuadratic a b ell m α β := by
  simp only [add_mul, mul_add, map_add, anfTwoProjection_affine_mul_affine,
    anfTwoProjection_affine_mul_rational, anfTwoProjection_rational_mul_affine,
    anfTwoProjection_rational_mul_rational_of_probe_zero α β hprobe, rationalProductQuadratic]
  funext i j
  simp only [Pi.add_apply]
  ring

theorem exists_lowProduct_rep_of_mem_rationalLow {p : ANF 8}
    (hp : p ∈ rationalLowSpace) :
    ∃ (a : F₂) (ell : LinearForm) (α : Fin 3 → F₂),
      p = affineANF a ell + rationalANF α := by
  rcases Submodule.mem_sup.mp hp with ⟨u, hu, q, hq, hpq⟩
  rcases exists_affineANF_of_mem hu with ⟨a, ell, huRep⟩
  rcases (mem_rationalTargetSpace_iff q).mp hq with ⟨α, hqRep⟩
  refine ⟨a, ell, α, ?_⟩
  rw [← hpq, huRep, hqRep]
  rfl

theorem exists_targetAmbient_rep {p : ANF 8}
    (hp : p ∈ targetAmbient 8 (mulTarget 4)) :
    ∃ (u : ANF 8) (c : TargetCoeff),
      u ∈ affine 8 ∧ p = u + targetANF c := by
  rcases Submodule.mem_sup.mp hp with ⟨u, hu, q, hq, hpq⟩
  rcases (Submodule.mem_span_range_iff_exists_fun
      (R := F₂) (v := Mul 4) (x := q)).mp hq with ⟨c, hc⟩
  refine ⟨u, c, hu, ?_⟩
  rw [← hpq, ← hc]
  rfl

theorem targetCoeff_eq_rationalCoeffRep_of_mem
    {c : TargetCoeff} (hc : c ∈ rationalCoeffSpace) :
    ∃ α : Fin 3 → F₂, c = rationalCoeffRep α := by
  rw [rationalCoeffSpace_eq] at hc
  rcases (Submodule.mem_span_range_iff_exists_fun
      (R := F₂)
      (v := ![rZeroCoeff, rOneCoeff, rInfinityCoeff])
      (x := c)).mp hc with ⟨α, hα⟩
  refine ⟨α, ?_⟩
  rw [← hα]
  funext i
  fin_cases i <;>
    simp [rationalCoeffRep, Fin.sum_univ_succ, rZeroCoeff, rOneCoeff, rInfinityCoeff]

/-- Actual ANF prefix closure: a product of two affine-plus-rational wires
that lands back in `Aff + T` has no new target direction. -/
theorem rationalLow_mul_mem_of_mem_targetAmbient
    {p q : ANF 8}
    (hp : p ∈ rationalLowSpace) (hq : q ∈ rationalLowSpace)
    (hpq : p * q ∈ targetAmbient 8 (mulTarget 4)) :
    p * q ∈ rationalLowSpace := by
  rcases exists_lowProduct_rep_of_mem_rationalLow hp with
    ⟨a, ell, α, hpRep⟩
  rcases exists_lowProduct_rep_of_mem_rationalLow hq with
    ⟨b, m, β, hqRep⟩
  rcases exists_targetAmbient_rep hpq with ⟨u, c, hu, hprodRep⟩
  have hprobe :
      quarticWedgeProbe (rationalTwo α) (rationalTwo β) = 0 := by
    have hz := quarticProbeANF_eq_zero_of_mem_targetAmbient hpq
    rw [hpRep, hqRep, lowProduct_quarticProjection] at hz
    exact hz
  have hcubic : rationalProductCubic ell m α β = 0 := by
    have hz := anfThreeProjection_eq_zero_of_mem_targetAmbient hpq
    rw [hpRep, hqRep,
      lowProduct_cubicProjection_of_quartic_zero a b ell m α β hprobe] at hz
    exact hz
  have htwo : anfTwoProjection (p * q) = targetTwo c := by
    rw [hprodRep, map_add, anfTwoProjection_kills_affine hu,
      anfTwoProjection_targetANF, zero_add]
  have hquadratic :
      targetTwo c = rationalProductQuadratic a b ell m α β := by
    rw [← htwo, hpRep, hqRep]
    exact lowProduct_quadraticProjection_of_quartic_zero
      a b ell m α β hprobe
  have hwedge := rational_wedge_zero_of_probe_zero α β hprobe
  have hcRat := exterior_prefix_rigidity a b ell m α β c
    hwedge hcubic hquadratic
  rcases targetCoeff_eq_rationalCoeffRep_of_mem hcRat with ⟨γ, hcγ⟩
  apply Submodule.mem_sup.mpr
  refine ⟨u, hu, targetANF c, ?_, ?_⟩
  · apply (mem_rationalTargetSpace_iff (targetANF c)).mpr
    exact ⟨γ, by rw [hcγ]⟩
  · exact hprodRep.symm

end

end N4
end UnrestrictedBooleanMul
