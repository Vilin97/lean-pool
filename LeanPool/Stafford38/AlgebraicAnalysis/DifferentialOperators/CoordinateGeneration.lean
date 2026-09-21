/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.DifferentialOperators.Basic
import LeanPool.Stafford38.AlgebraicAnalysis.LinearAlgebra.FiniteTaylorReconstruction
import Mathlib.RingTheory.Derivation.Basic

/-!
# Generation from coordinates and coordinate derivations

This is the presentation-free coordinate-elimination argument.  A finite
family of elements and dual derivations generates every intrinsic finite-order
differential operator, provided that commuting with all the coordinates
already characterizes multiplication operators.
-/

namespace AlgebraicAnalysis.DifferentialOperators.CoordinateGeneration


open AlgebraicAnalysis.DifferentialOperators
open AlgebraicAnalysis.FiniteTaylorReconstruction

noncomputable section

variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [Algebra k R]

private def delta (x : R) : Module.End k R →ₗ[k] Module.End k R :=
  { toFun := fun P => commutator P x
    map_add' := by
      intro P Q
      ext y
      simp [commutator_apply, mul_add]
      abel
    map_smul' := by
      intro c P
      ext y
      simp [commutator_apply, smul_sub] }

private def rightComposition (D : Module.End k R) :
    Module.End k R →ₗ[k] Module.End k R := LinearMap.mulRight k D

omit [CharZero k] in
private lemma rightComposition_pow_apply (D : Module.End k R)
    (a : ℕ) (P : Module.End k R) :
    (rightComposition D ^ a) P = P * D ^ a := by
  induction a with
  | zero => simp [rightComposition]
  | succ a ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      simp [rightComposition, pow_succ, mul_assoc]

omit [CharZero k] in
private lemma delta_mul (x : R) (P Q : Module.End k R) :
    delta x (P * Q) = delta x P * Q + P * delta x Q := by
  simpa [delta, add_comm] using commutator_mul P Q x

omit [CharZero k] in
private lemma delta_right_derivation (x : R) (D : Derivation k R R) :
    delta x D.toLinearMap = multiplication (D x) := by
  ext y
  simp [delta, commutator_apply, multiplication_apply, mul_comm]

omit [CharZero k] in
private lemma deltas_commute (x y : R) (P : Module.End k R) :
    delta x (delta y P) = delta y (delta x P) := by
  ext z
  simp [delta, commutator_apply]
  ring_nf

omit [CharZero k] in
private lemma delta_iterate_preserves_kernel (x y : R) (a : ℕ)
    (P : Module.End k R) (hP : delta y P = 0) :
    delta y ((delta x ^ a) P) = 0 := by
  induction a with
  | zero => simpa using hP
  | succ a ih =>
      rw [pow_succ', Module.End.mul_apply]
      rw [deltas_commute, ih]
      exact (delta x).map_zero

omit [CharZero k] in
private lemma right_derivation_preserves_kernel (y : R) (D : Derivation k R R)
    (hxy : D y = 0) (a : ℕ) (P : Module.End k R)
    (hP : delta y P = 0) :
    delta y ((rightComposition D.toLinearMap ^ a) P) = 0 := by
  induction a with
  | zero => simpa using hP
  | succ a ih =>
      rw [pow_succ', Module.End.mul_apply]
      change delta y (rightComposition D.toLinearMap
        ((rightComposition D.toLinearMap ^ a) P)) = 0
      rw [show rightComposition D.toLinearMap
          ((rightComposition D.toLinearMap ^ a) P) =
          (rightComposition D.toLinearMap ^ a) P * D.toLinearMap by rfl,
        delta_mul, delta_right_derivation, hxy]
      rw [ih, zero_mul, zero_add]
      ext z
      simp [multiplication_apply]

omit [CharZero k] in
private lemma delta_mem_order {m : ℕ} (x : R) (P : Module.End k R)
    (hP : P ∈ order (k := k) (R := R) (m + 1)) :
    delta x P ∈ order (k := k) (R := R) m := hP x

omit [CharZero k] in
private lemma delta_pow_order_zero (m : ℕ) (x : R)
    (P : Module.End k R) (hP : P ∈ order (k := k) (R := R) m) :
    (delta x ^ (m + 1)) P = 0 := by
  induction m generalizing P with
  | zero =>
      rw [pow_one]
      exact hP x
  | succ m ih =>
      rw [pow_succ, Module.End.mul_apply]
      exact ih (delta x P) (delta_mem_order x P hP)

omit [CharZero k] in
private lemma delta_pow_after_zero (x : R) (m a : ℕ) (P : Module.End k R)
    (h : (delta x ^ m) P = 0) :
    (delta x ^ m) ((delta x ^ a) P) = 0 := by
  rw [← Module.End.mul_apply, ← pow_add]
  rw [Nat.add_comm]
  rw [pow_add, Module.End.mul_apply, h, map_zero]

omit [CharZero k] in
private lemma delta_mem_algebra (x : R) (P : Module.End k R)
    (hP : P ∈ algebra (k := k) (R := R)) :
    delta x P ∈ algebra (k := k) (R := R) := by
  rcases hP with ⟨m, hm⟩
  cases m with
  | zero =>
      refine ⟨0, ?_⟩
      change commutator P x ∈ order 0
      rw [hm x]
      exact (order 0).zero_mem
  | succ m => exact ⟨m, delta_mem_order x P hm⟩

omit [CharZero k] in
private lemma delta_pow_mem_algebra (x : R) (a : ℕ)
    (P : Module.End k R)
    (hP : P ∈ algebra (k := k) (R := R)) :
    (delta x ^ a) P ∈ algebra (k := k) (R := R) := by
  induction a with
  | zero => simpa using hP
  | succ a ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact delta_mem_algebra x _ ih

private def projection (x : R) (D : Derivation k R R) (m : ℕ)
    (P : Module.End k R) : Module.End k R :=
  ∑ a ∈ Finset.range (m + 1),
    ((-1 : k) ^ a / (a.factorial : k)) • ((delta x ^ a) P * D.toLinearMap ^ a)

omit [CharZero k] in
private lemma projectorMapG_apply (x : R) (D : Derivation k R R) (m : ℕ)
    (P : Module.End k R) :
    projectorMapG m (rightComposition D.toLinearMap) (delta x) P =
      projection x D m P := by
  unfold projectorMapG projection
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [LinearMap.smul_apply, Module.End.mul_apply]
  rw [rightComposition_pow_apply]

private lemma delta_derivation_pow (x : R) (D : Derivation k R R)
    (hDx : D x = 1) : ∀ a : ℕ,
    delta x (D.toLinearMap ^ a) = (a : k) • D.toLinearMap ^ (a - 1)
  | 0 => by
      ext y
      simp [delta, commutator_apply]
  | a + 1 => by
      rw [pow_succ, delta_mul, delta_right_derivation, hDx,
        delta_derivation_pow x D hDx a]
      cases a with
      | zero =>
          ext y
          simp [multiplication_apply]
      | succ a =>
          ext y
          simp [pow_succ, add_mul, add_smul, multiplication_apply]

private lemma projection_kernel (x : R) (D : Derivation k R R) (hDx : D x = 1)
    (m : ℕ) (P : Module.End k R)
    (hnil : (delta x ^ (m + 1)) P = 0) :
    delta x (projection x D m P) = 0 := by
  simp only [projection, map_sum]
  have hterm (a : ℕ) :
      delta x (((-1 : k) ^ a / (a.factorial : k)) •
        ((delta x ^ a) P * D.toLinearMap ^ a)) =
      ((-1 : k) ^ a / (a.factorial : k)) •
        (((delta x ^ (a + 1)) P * D.toLinearMap ^ a) +
          ((a : k) • ((delta x ^ a) P * D.toLinearMap ^ (a - 1)))) := by
    rw [map_smul, delta_mul, delta_derivation_pow x D hDx]
    rw [show delta x ((delta x ^ a) P) = (delta x ^ (a + 1)) P by
      rw [pow_succ', Module.End.mul_apply]]
    simp only [smul_add]
    rw [mul_smul_comm, smul_smul]
  simp_rw [hterm]
  simp only [smul_add, Finset.sum_add_distrib]
  rw [Finset.sum_range_succ, hnil]
  simp only [zero_mul, smul_zero, add_zero]
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_smul]
  have hcancel (a : ℕ) :
      ((-1 : k) ^ a / (a.factorial : k)) •
          ((delta x ^ (a + 1)) P * D.toLinearMap ^ a) +
        ((-1 : k) ^ (a + 1) / ((a + 1).factorial : k)) •
          ((a + 1 : k) •
            ((delta x ^ (a + 1)) P * D.toLinearMap ^ a)) = 0 := by
    have ha : ((a + 1 : ℕ) : k) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero a
    have hfac : ((a.factorial : ℕ) : k) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero a
    have hc : ((-1 : k) ^ a / (a.factorial : k)) +
        ((-1 : k) ^ (a + 1) / ((a + 1).factorial : k)) * (a + 1 : k) = 0 := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
      field_simp [hfac, ha]
      ring
    rw [smul_smul, ← add_smul, hc, zero_smul]
  simp only [smul_zero, add_zero]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro a ha
  simpa [Nat.succ_sub_one] using hcancel a

omit [CharZero k] in
private lemma projection_preserves_kernel (x y : R) (D : Derivation k R R)
    (hDy : D y = 0) (m : ℕ) (P : Module.End k R)
    (hP : delta y P = 0) : delta y (projection x D m P) = 0 := by
  simp only [projection, map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro a ha
  rw [delta_mul]
  have hpow : delta y (D.toLinearMap ^ a) = 0 := by
    have h := right_derivation_preserves_kernel y D hDy a (1 : Module.End k R)
      (by ext z; simp [delta, commutator_apply])
    simpa [rightComposition_pow_apply] using h
  rw [delta_iterate_preserves_kernel x y a P hP, hpow]
  simp

/-! A derivation is a finite-order operator.  This is exported separately from
the coordinate-generation theorem so concrete carriers can expose their
derivation generators without importing an application-specific predicate. -/
omit [CharZero k] in
theorem derivation_mem_algebra (D : Derivation k R R) :
    D.toLinearMap ∈ algebra (k := k) (R := R) := by
  refine ⟨1, ?_⟩
  rw [mem_order_succ_iff]
  intro r
  change delta r D.toLinearMap ∈ order 0
  rw [delta_right_derivation]
  apply (mem_order_zero_iff_eq_multiplication _).2
  ext z
  simp [multiplication_apply]

omit [CharZero k] in
private lemma projection_mem_algebra (x : R) (D : Derivation k R R) (m : ℕ)
    (P : Module.End k R)
    (hP : P ∈ algebra (k := k) (R := R)) : projection x D m P ∈ algebra := by
  unfold projection
  apply (algebra (k := k) (R := R)).sum_mem
  intro a ha
  apply (algebra (k := k) (R := R)).smul_mem
  exact (algebra (k := k) (R := R)).mul_mem
    (delta_pow_mem_algebra x a P hP)
    ((algebra (k := k) (R := R)).pow_mem (derivation_mem_algebra D) a)

/-- Finite-order variant: the coordinate-rigidity hypothesis is required only
for operators in `algebra`.  Every intrinsic finite-order differential
operator belongs to any linear subspace containing all multiplications and
stable under right composition by a finite dual coordinate frame.  No
multiplicative closure of the subspace, or commutation hypothesis among the
derivations, is required. -/
theorem mem_submodule_of_coordinates'
    {n : ℕ} (x : Fin n → R) (D : Fin n → Derivation k R R)
    (hdual : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hcoordinate : ∀ P : Module.End k R, P ∈ algebra (k := k) (R := R) →
      (∀ i, commutator P (x i) = 0) →
        P = multiplication (P 1))
    (H : Submodule k (Module.End k R))
    (hmul : ∀ r : R, multiplication r ∈ H)
    (hright : ∀ i Q, Q ∈ H → Q * (D i).toLinearMap ∈ H)
    (P : Module.End k R)
    (hP : P ∈ algebra (k := k) (R := R)) : P ∈ H := by
  have hright_pow : ∀ i a (Q : Module.End k R), Q ∈ H →
      Q * (D i).toLinearMap ^ a ∈ H := by
    intro i a
    induction a with
    | zero =>
        intro Q hQ
        simpa using hQ
    | succ a ih =>
        intro Q hQ
        rw [pow_succ, ← mul_assoc]
        exact hright i _ (ih Q hQ)
  have heliminate : ∀ l : List (Fin n), l.Nodup →
      (∀ Q : Module.End k R,
        Q ∈ algebra (k := k) (R := R) →
        (∀ i ∈ l, delta (x i) Q = 0) → Q ∈ H) →
      ∀ Q : Module.End k R,
        Q ∈ algebra (k := k) (R := R) → Q ∈ H := by
    intro l hnod
    induction l with
    | nil =>
        intro hend Q hQ
        exact hend Q hQ (by simp)
    | cons i l ih =>
        have hinot : i ∉ l := (List.nodup_cons.mp hnod).1
        have hlnod : l.Nodup := (List.nodup_cons.mp hnod).2
        intro hend
        apply ih hlnod
        intro Q hQ hkern
        rcases hQ with ⟨m, hm⟩
        have hnil : (delta (x i) ^ (m + 1)) Q = 0 :=
          delta_pow_order_zero m (x i) Q hm
        rw [reconstruction_all m (rightComposition (D i).toLinearMap)
          (delta (x i)) Q hnil]
        apply Submodule.sum_mem
        intro a ha
        apply Submodule.smul_mem
        rw [Module.End.mul_apply, Module.End.mul_apply,
          projectorMapG_apply, rightComposition_pow_apply]
        apply hright_pow
        apply hend _ (projection_mem_algebra (x i) (D i) m _
              (delta_pow_mem_algebra (x i) a Q ⟨m, hm⟩))
        intro j hj
        simp only [List.mem_cons] at hj
        rcases hj with hji | hj
        · subst j
          exact projection_kernel (x i) (D i) (by simpa using hdual i i)
            m _ (delta_pow_after_zero (x i) (m + 1) a Q hnil)
        · have hij : i ≠ j := fun e => hinot (e ▸ hj)
          apply projection_preserves_kernel (x i) (x j) (D i)
              (by rw [hdual, ite_eq_right hij])
          exact delta_iterate_preserves_kernel (x i) (x j) a Q (hkern j hj)
  apply heliminate (List.ofFn fun i : Fin n => i)
    (List.nodup_ofFn.mpr fun _ _ h => h) ?_ P hP
  intro Q hQ hkern
  rw [hcoordinate Q hQ (fun i => by
    simpa [delta] using hkern i (List.mem_ofFn.mpr ⟨i, rfl⟩))]
  exact hmul (Q 1)

/-- Every intrinsic finite-order differential operator belongs to any linear
subspace containing all multiplications and stable under right composition by
a finite dual coordinate frame.  No multiplicative closure of the subspace,
or commutation hypothesis among the derivations, is required. -/
theorem mem_submodule_of_coordinates
    {n : ℕ} (x : Fin n → R) (D : Fin n → Derivation k R R)
    (hdual : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hcoordinate : ∀ P : Module.End k R,
      (∀ i, commutator P (x i) = 0) →
        P = multiplication (P 1))
    (H : Submodule k (Module.End k R))
    (hmul : ∀ r : R, multiplication r ∈ H)
    (hright : ∀ i Q, Q ∈ H → Q * (D i).toLinearMap ∈ H)
    (P : Module.End k R)
    (hP : P ∈ algebra (k := k) (R := R)) : P ∈ H :=
  mem_submodule_of_coordinates' x D hdual (fun P _ h => hcoordinate P h) H
    hmul hright P hP

/-- Finite-order variant: the coordinate-rigidity hypothesis is required only
for operators in `algebra`.  Subalgebras containing the coordinate
derivations satisfy the weaker right-stability hypothesis automatically. -/
theorem mem_subalgebra_of_coordinates'
    {n : ℕ} (x : Fin n → R) (D : Fin n → Derivation k R R)
    (hdual : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hcoordinate : ∀ P : Module.End k R, P ∈ algebra (k := k) (R := R) →
      (∀ i, commutator P (x i) = 0) →
        P = multiplication (P 1))
    (H : Subalgebra k (Module.End k R))
    (hmul : ∀ r : R, multiplication r ∈ H)
    (hder : ∀ i, (D i).toLinearMap ∈ H)
    (P : Module.End k R)
    (hP : P ∈ algebra (k := k) (R := R)) : P ∈ H := by
  apply mem_submodule_of_coordinates' x D hdual hcoordinate H.toSubmodule
    hmul (fun i Q hQ => H.mul_mem hQ (hder i)) P hP

/-- Subalgebras containing the coordinate derivations satisfy the weaker
right-stability hypothesis automatically. -/
theorem mem_subalgebra_of_coordinates
    {n : ℕ} (x : Fin n → R) (D : Fin n → Derivation k R R)
    (hdual : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hcoordinate : ∀ P : Module.End k R,
      (∀ i, commutator P (x i) = 0) →
        P = multiplication (P 1))
    (H : Subalgebra k (Module.End k R))
    (hmul : ∀ r : R, multiplication r ∈ H)
    (hder : ∀ i, (D i).toLinearMap ∈ H)
    (P : Module.End k R)
    (hP : P ∈ algebra (k := k) (R := R)) : P ∈ H :=
  mem_subalgebra_of_coordinates' x D hdual (fun P _ h => hcoordinate P h) H
    hmul hder P hP

end
end AlgebraicAnalysis.DifferentialOperators.CoordinateGeneration
