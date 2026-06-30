/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import LeanPool.LeanQuantumAlg.Core.State
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Hilbert operators and unitary gates

`HilbertOperator n` is the raw `2^n × 2^n` complex matrix type. It is used for
observables, projectors, matrix sums, and block-encoding operators that are not
necessarily unitary.

`Gate n` is a unitary Hilbert operator. Gate application maps pure states to
pure states; arbitrary linear combinations stay at the raw `StateVector` layer
until separately normalized.

Pinned Mathlib API: `Matrix.mulVec` (and `mulVec_add/smul/single_one`,
`one_mulVec`, `mulVec_mulVec`), `Matrix.mem_unitaryGroup_iff`,
`Equiv.Perm.permMatrix` (and `Matrix.permMatrix_mulVec`,
`Matrix.conjTranspose_permMatrix`, `Matrix.permMatrix_mul`,
`Matrix.permMatrix_one`), `Finset.sum_ite_eq'`.
-/

@[expose] public section

namespace QuantumAlg

/-- Raw linear operator on an `n`-qubit Hilbert space. -/
abbrev HilbertOperator (n : ℕ) : Type := Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ

namespace HilbertOperator

section

variable {n : ℕ}

/-- A Hilbert operator acts on a raw state vector by matrix-vector multiplication. -/
noncomputable def applyVec (A : HilbertOperator n) (ψ : StateVector n) : StateVector n :=
  WithLp.toLp 2 (A.mulVec ψ.ofLp)

@[simp]
theorem applyVec_apply (A : HilbertOperator n) (ψ : StateVector n) (i : Fin (2 ^ n)) :
    applyVec A ψ i = ∑ j, A i j * ψ j :=
  rfl

@[simp]
theorem applyVec_add (A : HilbertOperator n) (ψ φ : StateVector n) :
    applyVec A (ψ + φ) = applyVec A ψ + applyVec A φ := by
  unfold applyVec
  rw [show (ψ + φ).ofLp = ψ.ofLp + φ.ofLp from rfl, Matrix.mulVec_add]
  rfl

@[simp]
theorem applyVec_sub (A : HilbertOperator n) (ψ φ : StateVector n) :
    applyVec A (ψ - φ) = applyVec A ψ - applyVec A φ := by
  unfold applyVec
  rw [show (ψ - φ).ofLp = ψ.ofLp - φ.ofLp from rfl, Matrix.mulVec_sub]
  rfl

@[simp]
theorem applyVec_smul (A : HilbertOperator n) (c : ℂ) (ψ : StateVector n) :
    applyVec A (c • ψ) = c • applyVec A ψ := by
  unfold applyVec
  rw [show (c • ψ).ofLp = c • ψ.ofLp from rfl, Matrix.mulVec_smul]
  rfl

@[simp]
theorem applyVec_neg (A : HilbertOperator n) (ψ : StateVector n) :
    applyVec A (-ψ) = -applyVec A ψ := by
  unfold applyVec
  rw [show (-ψ).ofLp = -ψ.ofLp from rfl, Matrix.mulVec_neg]
  rfl

@[simp]
theorem add_applyVec (A B : HilbertOperator n) (ψ : StateVector n) :
    applyVec (A + B) ψ = applyVec A ψ + applyVec B ψ := by
  unfold applyVec
  rw [Matrix.add_mulVec]
  rfl

@[simp]
theorem smul_applyVec (c : ℂ) (A : HilbertOperator n) (ψ : StateVector n) :
    applyVec (c • A) ψ = c • applyVec A ψ := by
  unfold applyVec
  rw [Matrix.smul_mulVec]
  rfl

@[simp]
theorem one_applyVec (ψ : StateVector n) : applyVec (1 : HilbertOperator n) ψ = ψ := by
  unfold applyVec
  rw [Matrix.one_mulVec]

theorem mul_applyVec (A B : HilbertOperator n) (ψ : StateVector n) :
    applyVec (A * B) ψ = applyVec A (applyVec B ψ) := by
  unfold applyVec
  rw [show (WithLp.toLp 2 (B.mulVec ψ.ofLp)).ofLp = B.mulVec ψ.ofLp from rfl,
    Matrix.mulVec_mulVec]

/-- A Hilbert operator sends a basis ket to its corresponding column. -/
theorem applyVec_ket (A : HilbertOperator n) (x : Fin (2 ^ n)) (i : Fin (2 ^ n)) :
    applyVec A (PureState.ket x : StateVector n) i = A i x := by
  rw [applyVec_apply]
  simp only [PureState.ket_apply, mul_ite, mul_one, mul_zero]
  exact Fintype.sum_ite_eq' x (fun j => A i j)

/-- A unitary Hilbert operator preserves inner products on raw state vectors. -/
theorem inner_applyVec_applyVec_of_mem_unitaryGroup {U : HilbertOperator n}
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) (ψ φ : StateVector n) :
    inner ℂ (applyVec U ψ) (applyVec U φ) = inner ℂ ψ φ := by
  have hUU : U.conjTranspose * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hU
  simp only [PiLp.inner_apply, RCLike.inner_apply, applyVec_apply]
  calc ∑ i, (∑ k, U i k * φ k) * starRingEnd ℂ (∑ j, U i j * ψ j)
      = ∑ i, ∑ k, ∑ j, (U i k * starRingEnd ℂ (U i j))
          * (φ k * starRingEnd ℂ (ψ j)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul]
        ring
    _ = ∑ k, ∑ j, (∑ i, U i k * starRingEnd ℂ (U i j))
          * (φ k * starRingEnd ℂ (ψ j)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ k, ∑ j, (1 : HilbertOperator n) j k * (φ k * starRingEnd ℂ (ψ j)) := by
        refine Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun j _ => ?_
        congr 1
        rw [← hUU, Matrix.mul_apply]
        exact Finset.sum_congr rfl fun i _ => by
          rw [Matrix.conjTranspose_apply,
            show star (U i j) = starRingEnd ℂ (U i j) from rfl, mul_comm]
    _ = ∑ k, φ k * starRingEnd ℂ (ψ k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul]
        exact Fintype.sum_ite_eq' k fun j => φ k * starRingEnd ℂ (ψ j)

/-- A unitary Hilbert operator preserves raw vector norms. -/
theorem norm_applyVec_of_mem_unitaryGroup {U : HilbertOperator n}
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) (ψ : StateVector n) :
    ‖applyVec U ψ‖ = ‖ψ‖ := by
  have h := inner_applyVec_applyVec_of_mem_unitaryGroup hU ψ ψ
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖applyVec U ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by exact_mod_cast h
  calc ‖applyVec U ψ‖ = √(‖applyVec U ψ‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = √(‖ψ‖ ^ 2) := by rw [h2]
    _ = ‖ψ‖ := Real.sqrt_sq (norm_nonneg _)

end

end HilbertOperator

/-- A unitary gate on an `n`-qubit Hilbert space. -/
structure Gate (n : ℕ) where
  /-- Underlying Hilbert-space operator. -/
  op : HilbertOperator n
  /-- Gates are unitary by definition. -/
  unitary : op ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ

namespace Gate

noncomputable section

variable {n : ℕ}

instance : Coe (Gate n) (HilbertOperator n) := ⟨Gate.op⟩

instance : CoeFun (Gate n) (fun _ => Fin (2 ^ n) → Fin (2 ^ n) → ℂ) :=
  ⟨fun G => G.op⟩

instance : HMul (Gate n) (HilbertOperator n) (HilbertOperator n) where
  hMul G A := (G : HilbertOperator n) * A

instance : HMul (HilbertOperator n) (Gate n) (HilbertOperator n) where
  hMul A G := A * (G : HilbertOperator n)

@[ext]
theorem ext {G K : Gate n} (h : ∀ i j, G i j = K i j) : G = K := by
  cases G with
  | mk G hG =>
    cases K with
    | mk K hK =>
      have hGK : G = K := by
        ext i j
        exact h i j
      subst hGK
      rfl

/-- Build a gate from a unitary Hilbert operator. -/
def ofUnitary (U : HilbertOperator n)
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) : Gate n := ⟨U, hU⟩

@[simp]
theorem coe_ofUnitary (U : HilbertOperator n)
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :
    ((ofUnitary U hU : Gate n) : HilbertOperator n) = U := rfl

instance : Monoid (Gate n) where
  one := ofUnitary 1 (one_mem _)
  mul G K := ofUnitary ((G : HilbertOperator n) * (K : HilbertOperator n))
    (mul_mem G.unitary K.unitary)
  one_mul G := by
    ext i j
    change ((1 : HilbertOperator n) * (G : HilbertOperator n)) i j = G i j
    simp
  mul_one G := by
    ext i j
    change ((G : HilbertOperator n) * (1 : HilbertOperator n)) i j = G i j
    simp
  mul_assoc G K L := by
    ext i j
    change (((G : HilbertOperator n) * (K : HilbertOperator n)) * (L : HilbertOperator n)) i j
      = ((G : HilbertOperator n) * ((K : HilbertOperator n) * (L : HilbertOperator n))) i j
    rw [Matrix.mul_assoc]

@[simp]
theorem coe_one : (((1 : Gate n) : HilbertOperator n)) = 1 := rfl

@[simp]
theorem coe_mul (G K : Gate n) :
    (((G * K : Gate n) : HilbertOperator n))
      = (G : HilbertOperator n) * (K : HilbertOperator n) := rfl

/-- Conjugate transpose of a unitary gate, again as a gate. -/
def conjTranspose (G : Gate n) : Gate n :=
  ofUnitary ((G : HilbertOperator n).conjTranspose) (by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp G.unitary)

instance : Inv (Gate n) := ⟨conjTranspose⟩

@[simp]
theorem coe_conjTranspose (G : Gate n) :
    ((G.conjTranspose : Gate n) : HilbertOperator n)
      = (G : HilbertOperator n).conjTranspose := rfl

/-- A gate acts on a raw vector by its underlying Hilbert operator. -/
def applyVec (G : Gate n) (ψ : StateVector n) : StateVector n :=
  HilbertOperator.applyVec (G : HilbertOperator n) ψ

/-- A gate evolves a pure state to a pure state. -/
def apply (G : Gate n) (ψ : PureState n) : PureState n :=
  PureState.ofVec (G.applyVec (ψ : StateVector n)) (by
    change ‖HilbertOperator.applyVec (G : HilbertOperator n) (ψ : StateVector n)‖ = 1
    rw [HilbertOperator.norm_applyVec_of_mem_unitaryGroup G.unitary, ψ.norm_eq_one])

/-- Alias for `apply`, emphasizing unitary time evolution. -/
def evolve (G : Gate n) (ψ : PureState n) : PureState n := G.apply ψ

@[simp]
theorem applyVec_apply (G : Gate n) (ψ : StateVector n) (i : Fin (2 ^ n)) :
    G.applyVec ψ i = ∑ j, G i j * ψ j := rfl

@[simp]
theorem apply_apply (G : Gate n) (ψ : PureState n) (i : Fin (2 ^ n)) :
    G.apply ψ i = ∑ j, G i j * ψ j := by
  change G.applyVec (ψ : StateVector n) i = ∑ j, G i j * ψ j
  rfl

@[simp]
theorem applyVec_add (G : Gate n) (ψ φ : StateVector n) :
    G.applyVec (ψ + φ) = G.applyVec ψ + G.applyVec φ :=
  HilbertOperator.applyVec_add (G : HilbertOperator n) ψ φ

@[simp]
theorem applyVec_sub (G : Gate n) (ψ φ : StateVector n) :
    G.applyVec (ψ - φ) = G.applyVec ψ - G.applyVec φ :=
  HilbertOperator.applyVec_sub (G : HilbertOperator n) ψ φ

@[simp]
theorem applyVec_smul (G : Gate n) (c : ℂ) (ψ : StateVector n) :
    G.applyVec (c • ψ) = c • G.applyVec ψ :=
  HilbertOperator.applyVec_smul (G : HilbertOperator n) c ψ

@[simp]
theorem applyVec_neg (G : Gate n) (ψ : StateVector n) :
    G.applyVec (-ψ) = -G.applyVec ψ :=
  HilbertOperator.applyVec_neg (G : HilbertOperator n) ψ

-- Compatibility names for linear proofs at the raw vector layer.
theorem apply_add (G : Gate n) (ψ φ : StateVector n) :
    G.applyVec (ψ + φ) = G.applyVec ψ + G.applyVec φ :=
  applyVec_add G ψ φ

theorem apply_sub (G : Gate n) (ψ φ : StateVector n) :
    G.applyVec (ψ - φ) = G.applyVec ψ - G.applyVec φ :=
  applyVec_sub G ψ φ

theorem apply_smul (G : Gate n) (c : ℂ) (ψ : StateVector n) :
    G.applyVec (c • ψ) = c • G.applyVec ψ :=
  applyVec_smul G c ψ

theorem apply_neg (G : Gate n) (ψ : StateVector n) :
    G.applyVec (-ψ) = -G.applyVec ψ :=
  applyVec_neg G ψ

@[simp]
theorem one_apply (ψ : PureState n) : (1 : Gate n).apply ψ = ψ := by
  ext i
  change HilbertOperator.applyVec (1 : HilbertOperator n) (ψ : StateVector n) i = ψ i
  rw [HilbertOperator.one_applyVec]

@[simp]
theorem one_applyVec (ψ : StateVector n) : (1 : Gate n).applyVec ψ = ψ :=
  HilbertOperator.one_applyVec ψ

theorem mul_applyVec (G K : Gate n) (ψ : StateVector n) :
    (G * K).applyVec ψ = G.applyVec (K.applyVec ψ) :=
  HilbertOperator.mul_applyVec (G : HilbertOperator n) (K : HilbertOperator n) ψ

theorem mul_apply (G K : Gate n) (ψ : PureState n) :
    (G * K).apply ψ = G.apply (K.apply ψ) := by
  ext i
  change (G * K).applyVec (ψ : StateVector n) i
      = G.applyVec (K.applyVec (ψ : StateVector n)) i
  rw [mul_applyVec]

/-- A gate sends the basis ket `|x⟩` to its `x`-th column. -/
theorem apply_ket (G : Gate n) (x : Fin (2 ^ n)) (i : Fin (2 ^ n)) :
    G.apply (PureState.ket x) i = G i x := by
  rw [apply_apply]
  simp only [PureState.ket_apply, mul_ite, mul_one, mul_zero]
  exact Fintype.sum_ite_eq' x (fun j => G i j)

/-! ## Permutation gates -/

/-- The gate permuting the computational basis by `σ`:
`(ofPerm σ).apply (ket x) = ket (σ⁻¹ x)`. Unitary by construction. -/
def ofPerm (σ : Equiv.Perm (Fin (2 ^ n))) : Gate n :=
  ofUnitary (σ.permMatrix ℂ) (by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul,
      inv_mul_cancel, Matrix.permMatrix_one])

theorem ofPerm_apply (σ : Equiv.Perm (Fin (2 ^ n))) (ψ : PureState n)
    (i : Fin (2 ^ n)) : (ofPerm σ).apply ψ i = ψ (σ i) := by
  change HilbertOperator.applyVec (σ.permMatrix ℂ) (ψ : StateVector n) i = ψ (σ i)
  unfold HilbertOperator.applyVec
  rw [Matrix.permMatrix_mulVec]
  rfl

theorem ofPerm_apply_ket (σ : Equiv.Perm (Fin (2 ^ n))) (x : Fin (2 ^ n)) :
    (ofPerm σ).apply (PureState.ket x) = PureState.ket (σ⁻¹ x) := by
  ext i
  rw [ofPerm_apply, PureState.ket_apply, PureState.ket_apply]
  by_cases h : σ i = x
  · rw [if_pos h, if_pos (by rw [← h]; exact (Equiv.symm_apply_apply σ i).symm)]
  · rw [if_neg h,
      if_neg (fun hi => h (by rw [hi]; exact Equiv.apply_symm_apply σ x))]

theorem ofPerm_mem_unitaryGroup (σ : Equiv.Perm (Fin (2 ^ n))) :
    (ofPerm σ : HilbertOperator n) ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  (ofPerm σ).unitary

/-! ## Unitary gates preserve inner products and norms -/

/-- Unitary gates preserve the inner product. -/
theorem inner_apply_apply_of_mem_unitaryGroup {U : Gate n}
    (_hU : (U : HilbertOperator n) ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    (ψ φ : PureState n) :
    inner ℂ (U.apply ψ : StateVector n) (U.apply φ : StateVector n)
      = inner ℂ (ψ : StateVector n) (φ : StateVector n) :=
  HilbertOperator.inner_applyVec_applyVec_of_mem_unitaryGroup U.unitary
    (ψ : StateVector n) (φ : StateVector n)

/-- Unitary gates preserve the norm. -/
theorem norm_apply_of_mem_unitaryGroup {U : Gate n}
    (_hU : (U : HilbertOperator n) ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    (ψ : PureState n) :
    ‖(U.apply ψ : StateVector n)‖ = ‖(ψ : StateVector n)‖ :=
  HilbertOperator.norm_applyVec_of_mem_unitaryGroup U.unitary (ψ : StateVector n)

theorem norm_apply (U : Gate n) (ψ : PureState n) :
    ‖(U.apply ψ : StateVector n)‖ = 1 :=
  (U.apply ψ).norm_eq_one

end

end Gate

end QuantumAlg
