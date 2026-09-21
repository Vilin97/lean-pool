/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Weyl.Symplectic
import LeanPool.Stafford38.Stafford38.Characteristic.HomogeneousChart

/-!
# Symplectic completion of a phase vector

An explicit symplectic transvection preserves the standard phase pairing.
One transvection sends a nonzero vector to another when they pair nontrivially;
an elementary bridge vector reduces the remaining case to two transvections.
Consequently any nonzero phase vector can occupy a prescribed matrix column.
Combined with homogeneous nonvanishing, this makes the transformed pure-power
coefficient nonzero over the original characteristic-zero field.
-/

namespace Stafford38.CharacteristicSymplecticCompletion

open Stafford38.Characteristic
open Stafford38.CharacteristicHomogeneousChart
open Stafford38.WeylSymplectic

noncomputable section
universe u
variable (k : Type u) [Field k]

/-- The standard alternating pairing on coordinate and momentum vectors. -/
def phasePairing {n : ℕ} (u v : PhaseVar n → k) : k :=
  ∑ i, (u (.inr i) * v (.inl i) - u (.inl i) * v (.inr i))

/-- The standard basis vector of phase space at a chosen phase index. -/
def phaseBasis {n : ℕ} (j : PhaseVar n) : PhaseVar n → k :=
  fun i => if i = j then 1 else 0

/-- The symplectic transvection adding a multiple of `u` determined by its alternating pairing. -/
def symplecticTransvection {n : ℕ} (a : k) (u : PhaseVar n → k) :
    Matrix (PhaseVar n) (PhaseVar n) k :=
  fun i j => (if i = j then 1 else 0) +
    a * phasePairing k (phaseBasis k j) u * u i

theorem phasePairing_basis_left {n : ℕ} (j : PhaseVar n)
    (u : PhaseVar n → k) :
    phasePairing k (phaseBasis k j) u =
      match j with
      | .inl i => -u (.inr i)
      | .inr i => u (.inl i) := by
  cases j with
  | inl j =>
      simp [phasePairing, phaseBasis]
  | inr j =>
      simp [phasePairing, phaseBasis]

theorem transvection_mulVec {n : ℕ} (a : k) (u z : PhaseVar n → k)
    (i : PhaseVar n) :
    Matrix.mulVec (symplecticTransvection k a u) z i =
      z i + a * phasePairing k z u * u i := by
  simp only [Matrix.mulVec, dotProduct, symplecticTransvection]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  rw [show (∑ x, (if i = x then 1 else 0) * z x) = z i by simp]
  congr 1
  rw [phasePairing]
  rw [Fintype.sum_sum_type]
  simp only [phasePairing_basis_left]
  simp only [Finset.sum_sub_distrib]
  rw [mul_sub, sub_mul]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem phasePairing_add_left {n : ℕ} (u v w : PhaseVar n → k) :
    phasePairing k (u + v) w = phasePairing k u w + phasePairing k v w := by
  simp? [phasePairing]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

theorem phasePairing_add_right {n : ℕ} (u v w : PhaseVar n → k) :
    phasePairing k u (v + w) = phasePairing k u v + phasePairing k u w := by
  simp? [phasePairing]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

theorem phasePairing_smul_left {n : ℕ} (c : k) (u v : PhaseVar n → k) :
    phasePairing k (c • u) v = c * phasePairing k u v := by
  simp? [phasePairing]
  rw [mul_sub]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro x hx <;> ring

theorem phasePairing_smul_right {n : ℕ} (c : k) (u v : PhaseVar n → k) :
    phasePairing k u (c • v) = c * phasePairing k u v := by
  simp? [phasePairing]
  rw [mul_sub]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro x hx <;> ring

theorem phasePairing_skew {n : ℕ} (u v : PhaseVar n → k) :
    phasePairing k u v = -phasePairing k v u := by
  simp? [phasePairing]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro x hx <;> ring

theorem phasePairing_self {n : ℕ} (u : PhaseVar n → k) :
    phasePairing k u u = 0 := by
  simp? [phasePairing]
  have hsum : (∑ x, u (.inl x) * u (.inr x)) =
      ∑ x, u (.inr x) * u (.inl x) := by
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hsum, sub_self]

theorem transvection_preserves_pairing {n : ℕ} (a : k)
    (u x y : PhaseVar n → k) :
    phasePairing k (Matrix.mulVec (symplecticTransvection k a u) x)
        (Matrix.mulVec (symplecticTransvection k a u) y) =
      phasePairing k x y := by
  have hx : Matrix.mulVec (symplecticTransvection k a u) x =
      x + (a * phasePairing k x u) • u := by
    funext i
    rw [transvection_mulVec]
    rfl
  have hy : Matrix.mulVec (symplecticTransvection k a u) y =
      y + (a * phasePairing k y u) • u := by
    funext i
    rw [transvection_mulVec]
    rfl
  rw [hx, hy, phasePairing_add_left]
  simp_rw [phasePairing_add_right, phasePairing_smul_left,
    phasePairing_smul_right, phasePairing_self]
  rw [phasePairing_skew k u y]
  ring

theorem transpose_standardForm_mul_apply {n : ℕ}
    (A : Matrix (PhaseVar n) (PhaseVar n) k) (i j : PhaseVar n) :
    (Matrix.transpose A * standardForm k n * A) i j =
      phasePairing k (fun l => A l i) (fun l => A l j) := by
  simp [Matrix.mul_apply, standardForm, Matrix.J, phasePairing,
    Matrix.one_apply]
  ring

theorem phasePairing_basis {n : ℕ} (i j : PhaseVar n) :
    phasePairing k (phaseBasis k i) (phaseBasis k j) =
      standardForm k n i j := by
  cases i <;> cases j <;>
    simp [phasePairing, phaseBasis, standardForm, Matrix.J, Matrix.one_apply,
      eq_comm]

theorem mulVec_phaseBasis {n : ℕ}
    (A : Matrix (PhaseVar n) (PhaseVar n) k) (j : PhaseVar n) :
    Matrix.mulVec A (phaseBasis k j) = fun i => A i j := by
  funext i
  simp [Matrix.mulVec, dotProduct, phaseBasis]

theorem symplecticTransvection_mem {n : ℕ} (a : k)
    (u : PhaseVar n → k) :
    symplecticTransvection k a u ∈ Matrix.symplecticGroup (Fin n) k := by
  rw [SymplecticGroup.mem_iff']
  ext i j
  rw [transpose_standardForm_mul_apply]
  change phasePairing k (fun l => symplecticTransvection k a u l i)
      (fun l => symplecticTransvection k a u l j) = standardForm k n i j
  rw [← phasePairing_basis k i j]
  rw [← mulVec_phaseBasis k (symplecticTransvection k a u) i,
    ← mulVec_phaseBasis k (symplecticTransvection k a u) j]
  exact transvection_preserves_pairing k a u (phaseBasis k i) (phaseBasis k j)

theorem phasePairing_sub_right {n : ℕ} (u v w : PhaseVar n → k) :
    phasePairing k u (v - w) = phasePairing k u v - phasePairing k u w := by
  simp? [phasePairing, Finset.sum_sub_distrib]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  ring

theorem exists_phasePairing_right_ne_zero {n : ℕ}
    {u : PhaseVar n → k} (hu : u ≠ 0) :
    ∃ z : PhaseVar n → k, phasePairing k u z ≠ 0 := by
  have hex : ∃ i, u i ≠ 0 := by
    by_contra h
    push Not at h
    apply hu
    funext i
    exact h i
  rcases hex with ⟨i, hi⟩
  cases i with
  | inl i =>
      refine ⟨phaseBasis k (.inr i), ?_⟩
      simpa [phasePairing, phaseBasis] using neg_ne_zero.mpr hi
  | inr i =>
      refine ⟨phaseBasis k (.inl i), ?_⟩
      simpa [phasePairing, phaseBasis] using hi

theorem exists_phasePairing_left_ne_zero {n : ℕ}
    {u : PhaseVar n → k} (hu : u ≠ 0) :
    ∃ z : PhaseVar n → k, phasePairing k z u ≠ 0 := by
  rcases exists_phasePairing_right_ne_zero k hu with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  rw [phasePairing_skew k z u]
  exact neg_ne_zero.mpr hz

theorem exists_phasePairing_bridge {n : ℕ}
    {e v : PhaseVar n → k} (he : e ≠ 0) (hv : v ≠ 0) :
    ∃ w : PhaseVar n → k,
      phasePairing k e w ≠ 0 ∧ phasePairing k w v ≠ 0 := by
  rcases exists_phasePairing_right_ne_zero k he with ⟨r, her⟩
  rcases exists_phasePairing_left_ne_zero k hv with ⟨s, hsv⟩
  by_cases hrv : phasePairing k r v ≠ 0
  · exact ⟨r, her, hrv⟩
  by_cases hes : phasePairing k e s ≠ 0
  · exact ⟨s, hes, hsv⟩
  refine ⟨r + s, ?_, ?_⟩
  · rw [phasePairing_add_right]
    simpa [not_not.mp hes] using her
  · rw [phasePairing_add_left]
    simpa [not_not.mp hrv] using hsv

/-- The transvection sending `x` to `y` when their alternating pairing is nonzero. -/
def transvectionSending {n : ℕ} (x y : PhaseVar n → k) :
    Matrix (PhaseVar n) (PhaseVar n) k :=
  symplecticTransvection k (phasePairing k x y)⁻¹ (y - x)

theorem transvectionSending_mem {n : ℕ} (x y : PhaseVar n → k) :
    transvectionSending k x y ∈ Matrix.symplecticGroup (Fin n) k :=
  symplecticTransvection_mem k _ _

theorem transvectionSending_mulVec {n : ℕ} (x y : PhaseVar n → k)
    (hxy : phasePairing k x y ≠ 0) :
    Matrix.mulVec (transvectionSending k x y) x = y := by
  funext i
  rw [transvectionSending, transvection_mulVec]
  rw [phasePairing_sub_right, phasePairing_self, sub_zero]
  rw [inv_mul_cancel₀ hxy]
  simp

theorem exists_symplectic_mulVec_eq {n : ℕ}
    {e v : PhaseVar n → k} (he : e ≠ 0) (hv : v ≠ 0) :
    ∃ M : Matrix (PhaseVar n) (PhaseVar n) k,
      M ∈ Matrix.symplecticGroup (Fin n) k ∧ Matrix.mulVec M e = v := by
  by_cases hev : phasePairing k e v ≠ 0
  · exact ⟨transvectionSending k e v, transvectionSending_mem k e v,
      transvectionSending_mulVec k e v hev⟩
  rcases exists_phasePairing_bridge k he hv with ⟨w, hew, hwv⟩
  refine ⟨transvectionSending k w v * transvectionSending k e w, ?_, ?_⟩
  · exact (Matrix.symplecticGroup (Fin n) k).mul_mem
      (transvectionSending_mem k w v) (transvectionSending_mem k e w)
  · rw [← Matrix.mulVec_mulVec]
    rw [transvectionSending_mulVec k e w hew]
    exact transvectionSending_mulVec k w v hwv

theorem exists_symplectic_column_eq {n : ℕ} (t : PhaseVar n)
    {v : PhaseVar n → k} (hv : v ≠ 0) :
    ∃ M : Matrix (PhaseVar n) (PhaseVar n) k,
      M ∈ Matrix.symplecticGroup (Fin n) k ∧ (fun i => M i t) = v := by
  have hb : phaseBasis k t ≠ 0 := by
    intro h
    have := congrFun h t
    simp [phaseBasis] at this
  rcases exists_symplectic_mulVec_eq k hb hv with ⟨M, hM, hMv⟩
  refine ⟨M, hM, ?_⟩
  rw [← mulVec_phaseBasis]
  exact hMv

theorem exists_symplectic_pureCoefficient_ne_zero [CharZero k]
    {n N : ℕ} (t : PhaseVar n) {P : SymbolRing k n}
    (hP : P.IsHomogeneous N) (hne : P ≠ 0) (hN : 0 < N) :
    ∃ M : Matrix (PhaseVar n) (PhaseVar n) k,
      M ∈ Matrix.symplecticGroup (Fin n) k ∧
      (axisPolynomial k t
            (CharacteristicLinearAction.symbolLinearAlgHom k M P)).coeff (Finsupp.single () N) ≠
              0 := by
  rcases exists_eval_ne_zero_of_homogeneous k hP hne with ⟨v, hv⟩
  have hvne : v ≠ 0 := by
    intro hvzero
    subst v
    apply hv
    have hc : P.coeff 0 = 0 :=
      hP.coeff_eq_zero (by simpa using Nat.ne_of_lt hN)
    simpa [hc]
  rcases exists_symplectic_column_eq k t hvne with ⟨M, hM, hcol⟩
  refine ⟨M, hM, ?_⟩
  rw [pureCoefficient_symbolLinearAlgHom k M t hP]
  rw [hcol]
  exact hv

theorem exists_symplectic_chart_matrices [CharZero k]
    {n N : ℕ} (t : PhaseVar n) {P : SymbolRing k n}
    (hP : P.IsHomogeneous N) (hne : P ≠ 0) (hN : 0 < N) :
    ∃ M Ninv : Matrix (PhaseVar n) (PhaseVar n) k,
      M * standardForm k n * Matrix.transpose M = standardForm k n ∧
      Ninv * standardForm k n * Matrix.transpose Ninv = standardForm k n ∧
      M * Ninv = 1 ∧ Ninv * M = 1 ∧
      (axisPolynomial k t
            (CharacteristicLinearAction.symbolLinearAlgHom k M P)).coeff (Finsupp.single () N) ≠
              0 := by
  rcases exists_symplectic_pureCoefficient_ne_zero k t hP hne hN with
    ⟨M, hM, hcoeff⟩
  let A : Matrix.symplecticGroup (Fin n) k := ⟨M, hM⟩
  let Ninv : Matrix (PhaseVar n) (PhaseVar n) k := ↑(A⁻¹)
  refine ⟨M, Ninv, SymplecticGroup.mem_iff.mp hM,
    SymplecticGroup.mem_iff.mp (A⁻¹).property, ?_, ?_, hcoeff⟩
  · dsimp only [Ninv]
    calc
      M * (↑(A⁻¹) : Matrix (PhaseVar n) (PhaseVar n) k) = ↑(A * A⁻¹) := rfl
      _ = ↑(1 : Matrix.symplecticGroup (Fin n) k) := by simp
      _ = 1 := rfl
  · dsimp only [Ninv]
    calc
      (↑(A⁻¹) : Matrix (PhaseVar n) (PhaseVar n) k) * M = ↑(A⁻¹ * A) := rfl
      _ = ↑(1 : Matrix.symplecticGroup (Fin n) k) := by simp
      _ = 1 := rfl

/- Exact statement pins for symplectic column completion and the monic-symbol
precursor. -/
theorem symplectic_column_statement {n : ℕ} (t : PhaseVar n)
    {v : PhaseVar n → k} (hv : v ≠ 0) :
    ∃ M : Matrix (PhaseVar n) (PhaseVar n) k,
      M ∈ Matrix.symplecticGroup (Fin n) k ∧ (fun i => M i t) = v :=
  exists_symplectic_column_eq k t hv

theorem symplectic_pureCoefficient_statement [CharZero k]
    {n N : ℕ} (t : PhaseVar n) {P : SymbolRing k n}
    (hP : P.IsHomogeneous N) (hne : P ≠ 0) (hN : 0 < N) :
    ∃ M : Matrix (PhaseVar n) (PhaseVar n) k,
      M ∈ Matrix.symplecticGroup (Fin n) k ∧
      (axisPolynomial k t
            (CharacteristicLinearAction.symbolLinearAlgHom k M P)).coeff (Finsupp.single () N) ≠
              0 :=
  exists_symplectic_pureCoefficient_ne_zero k t hP hne hN

theorem symplectic_chart_matrices_statement [CharZero k]
    {n N : ℕ} (t : PhaseVar n) {P : SymbolRing k n}
    (hP : P.IsHomogeneous N) (hne : P ≠ 0) (hN : 0 < N) :
    ∃ M Ninv : Matrix (PhaseVar n) (PhaseVar n) k,
      M * standardForm k n * Matrix.transpose M = standardForm k n ∧
      Ninv * standardForm k n * Matrix.transpose Ninv = standardForm k n ∧
      M * Ninv = 1 ∧ Ninv * M = 1 ∧
      (axisPolynomial k t
            (CharacteristicLinearAction.symbolLinearAlgHom k M P)).coeff (Finsupp.single () N) ≠
              0 :=
  exists_symplectic_chart_matrices k t hP hne hN


end
end Stafford38.CharacteristicSymplecticCompletion
