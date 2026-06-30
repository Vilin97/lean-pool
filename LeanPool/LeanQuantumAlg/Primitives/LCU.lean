/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import LeanPool.LeanQuantumAlg.Init
public import LeanPool.LeanQuantumAlg.Core.Tensor
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Linear combination of unitaries (LCU)

The LCU primitive block-encodes a linear combination of unitaries into a larger
operator acting on an ancilla control register tensored with the system
[Lin22, hermfunc.tex:531].

The SELECT sum and the walk operator are `HilbertOperator`s: they are linear
operators used inside a block encoding, not themselves declared as unitary
`Gate`s in this file.
-/

@[expose] public section

namespace QuantumAlg

noncomputable section

variable {a n : ℕ}

/-- The control-basis projector `|i><i|` on the `a`-qubit control register. -/
def lcuProj (i : Fin (2 ^ a)) : HilbertOperator a :=
  Matrix.of fun r c => (if r = i then (1 : ℂ) else 0) * (if c = i then (1 : ℂ) else 0)

/-- The select operator `SELECT = sum_i |i><i| ⊗ U_i` [Lin22, hermfunc.tex:492]. -/
def lcuSelect (U : Fin (2 ^ a) → Gate n) : HilbertOperator (a + n) :=
  ∑ i, HilbertOperator.tensor (lcuProj i) (U i : HilbertOperator n)

/-- The coefficient 1-norm `lambda = sum_i alpha_i` for nonnegative coefficients. -/
def lcuNorm (alpha : Fin (2 ^ a) → ℝ) : ℝ := ∑ i, alpha i

/-- The LCU walk operator `W = (V† ⊗ I) · SELECT · (V ⊗ I)`. -/
def lcuWalk (V : Gate a) (U : Fin (2 ^ a) → Gate n) : HilbertOperator (a + n) :=
  HilbertOperator.tensor (V.conjTranspose : HilbertOperator a) (1 : HilbertOperator n)
    * lcuSelect U
    * HilbertOperator.tensor (V : HilbertOperator a) (1 : HilbertOperator n)

/-- Sandwiching a control projector between `V†` and `V` and reading the
`(0, 0)` entry leaves the squared first-column amplitude. -/
private theorem lcuProj_sandwich (V : Gate a) (i : Fin (2 ^ a)) :
    ((V.conjTranspose : HilbertOperator a) * lcuProj i * (V : HilbertOperator a)) 0 0
      = star (V i 0) * V i 0 := by
  change (((V : HilbertOperator a).conjTranspose * lcuProj i * (V : HilbertOperator a)) 0 0)
      = star (V i 0) * V i 0
  have hsum : (∑ k, star (V k 0) * (if k = i then (1 : ℂ) else 0)) = star (V i 0) := by
    simp only [mul_ite, mul_one, mul_zero]
    exact Fintype.sum_ite_eq' i (fun k => star (V k 0))
  have hsum2 : (∑ c, (if c = i then (1 : ℂ) else 0) * V c 0) = V i 0 := by
    simp only [ite_mul, one_mul, zero_mul]
    exact Fintype.sum_ite_eq' i (fun c => V c 0)
  have key : ∀ c, ((V : HilbertOperator a).conjTranspose * lcuProj i) 0 c
      = star (V i 0) * (if c = i then (1 : ℂ) else 0) := by
    intro c
    rw [Matrix.mul_apply]
    simp only [lcuProj, Matrix.of_apply, Matrix.conjTranspose_apply, ← mul_assoc]
    rw [← Finset.sum_mul, hsum]
  rw [Matrix.mul_apply]
  calc
    ∑ c, (((V : HilbertOperator a).conjTranspose * lcuProj i) 0 c) * V c 0
        = ∑ c, (star (V i 0) * (if c = i then (1 : ℂ) else 0)) * V c 0 := by
          refine Finset.sum_congr rfl fun c _ => by rw [key c]
    _ = ∑ c, star (V i 0) * ((if c = i then (1 : ℂ) else 0) * V c 0) := by
          refine Finset.sum_congr rfl fun c _ => by ring
    _ = star (V i 0) * (∑ c, (if c = i then (1 : ℂ) else 0) * V c 0) := by
          rw [Finset.mul_sum]
    _ = star (V i 0) * V i 0 := by rw [hsum2]

/-- The LCU walk operator expands into a control-block sum. -/
theorem lcuWalk_eq_sum (V : Gate a) (U : Fin (2 ^ a) → Gate n) :
    lcuWalk V U
      = ∑ i, HilbertOperator.tensor
          ((V.conjTranspose : HilbertOperator a) * lcuProj i * (V : HilbertOperator a))
          (U i : HilbertOperator n) := by
  unfold lcuWalk lcuSelect
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [HilbertOperator.tensor_mul_tensor, HilbertOperator.tensor_mul_tensor]
  simp

/-- **LCU block encoding** [Lin22, hermfunc.tex:531]. -/
theorem LinearCombinationOfUnitaries.main (V : Gate a) (U : Fin (2 ^ a) → Gate n)
    (alpha : Fin (2 ^ a) → ℝ) (halpha : ∀ i, 0 ≤ alpha i) (hlam : 0 < lcuNorm alpha)
    (hV : ∀ i, V i 0 = ((Real.sqrt (alpha i / lcuNorm alpha) : ℝ) : ℂ))
    (s t : Fin (2 ^ n)) :
    lcuWalk V U (prodEquiv (0, s)) (prodEquiv (0, t))
      = ((lcuNorm alpha : ℂ))⁻¹ * ∑ i, ((alpha i : ℝ) : ℂ) * U i s t := by
  have tprod : ∀ (G : HilbertOperator a) (K : HilbertOperator n) (x x' : Fin (2 ^ a))
      (y y' : Fin (2 ^ n)),
      (HilbertOperator.tensor G K) (prodEquiv (x, y)) (prodEquiv (x', y'))
        = G x x' * K y y' := by
    intro G K x x' y y'
    rw [HilbertOperator.tensor_apply]
    simp only [Equiv.symm_apply_apply]
  rw [lcuWalk_eq_sum, Matrix.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tprod, lcuProj_sandwich]
  have hnn : (0 : ℝ) ≤ alpha i / lcuNorm alpha := div_nonneg (halpha i) hlam.le
  rw [hV i, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt hnn, Complex.ofReal_div]
  ring

end

end QuantumAlg
