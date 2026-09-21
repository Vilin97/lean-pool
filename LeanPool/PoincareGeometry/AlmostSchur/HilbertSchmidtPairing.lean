/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.HilbertSchmidt
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Hilbert--Schmidt pairing

The final almost-Schur estimate pairs the trace-free Ricci endomorphism with
the trace-free Hessian.  This file supplies the intrinsic pairing, its full
orthonormal-basis contraction, and the finite-dimensional Cauchy--Schwarz
estimate.  It contains no geometric or analytic assumptions.
-/

@[expose] public noncomputable section
open scoped BigOperators

namespace AlmostSchur

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The intrinsic Hilbert--Schmidt pairing of two endomorphisms. -/
def hilbertSchmidtInner (A B : V →L[ℝ] V) : ℝ :=
  LinearMap.trace ℝ V (A.adjoint.comp B).toLinearMap

/-- The Hilbert--Schmidt pairing is the sum of the pointwise inner products
in every orthonormal basis. -/
theorem hilbertSchmidtInner_eq_sum_inner (A B : V →L[ℝ] V)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V) :
    hilbertSchmidtInner A B = ∑ i, inner ℝ (A (b i)) (B (b i)) := by
  rw [hilbertSchmidtInner, LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro i _
  exact ContinuousLinearMap.adjoint_inner_right A (b i) (B (b i))

/-- Full double-contraction formula for the Hilbert--Schmidt pairing. -/
theorem hilbertSchmidtInner_eq_sum_mul (A B : V →L[ℝ] V)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V) :
    hilbertSchmidtInner A B =
      ∑ i, ∑ j, inner ℝ (A (b i)) (b j) * inner ℝ (B (b i)) (b j) := by
  rw [hilbertSchmidtInner_eq_sum_inner A B b]
  apply Finset.sum_congr rfl
  intro i _
  rw [← b.sum_inner_mul_inner (A (b i)) (B (b i))]
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_comm (b j) (B (b i))]

/-- Squared Cauchy--Schwarz for the intrinsic Hilbert--Schmidt pairing. -/
theorem hilbertSchmidtInner_sq_le (A B : V →L[ℝ] V) :
    hilbertSchmidtInner A B ^ 2 ≤ hilbertSchmidtSq A * hilbertSchmidtSq B := by
  let b := stdOrthonormalBasis ℝ V
  rw [hilbertSchmidtInner_eq_sum_mul A B b,
    hilbertSchmidtSq_eq_sum_sq A b, hilbertSchmidtSq_eq_sum_sq B b]
  let a := fun ij : Fin (Module.finrank ℝ V) × Fin (Module.finrank ℝ V) =>
    inner ℝ (A (b ij.1)) (b ij.2)
  let c := fun ij : Fin (Module.finrank ℝ V) × Fin (Module.finrank ℝ V) =>
    inner ℝ (B (b ij.1)) (b ij.2)
  have h := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset
      (Fin (Module.finrank ℝ V) × Fin (Module.finrank ℝ V))) a c
  change (∑ i, ∑ j, a (i, j) * c (i, j)) ^ 2 ≤
    (∑ i, ∑ j, a (i, j) ^ 2) * ∑ i, ∑ j, c (i, j) ^ 2
  simpa only [Fintype.sum_prod_type] using h

/-- The Hilbert--Schmidt pairing of an endomorphism with itself is its squared
Hilbert--Schmidt norm. -/
theorem hilbertSchmidtInner_self (A : V →L[ℝ] V) :
    hilbertSchmidtInner A A = hilbertSchmidtSq A := by
  rw [hilbertSchmidtInner_eq_sum_inner A A (stdOrthonormalBasis ℝ V),
    hilbertSchmidtSq_eq_sum_norm_sq A (stdOrthonormalBasis ℝ V)]
  apply Finset.sum_congr rfl
  intro i _
  exact real_inner_self_eq_norm_sq _

/-- Pairing with the identity recovers the trace. -/
theorem hilbertSchmidtInner_id_right (A : V →L[ℝ] V) :
    hilbertSchmidtInner A (ContinuousLinearMap.id ℝ V) =
      LinearMap.trace ℝ V A.toLinearMap := by
  rw [hilbertSchmidtInner_eq_sum_inner A (ContinuousLinearMap.id ℝ V)
      (stdOrthonormalBasis ℝ V),
    LinearMap.trace_eq_sum_inner A.toLinearMap (stdOrthonormalBasis ℝ V)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ContinuousLinearMap.id_apply]
  exact real_inner_comm _ _

/-- Removing the scalar trace from the second factor does not change its
pairing with a trace-free first factor. -/
theorem hilbertSchmidtInner_traceFree_right (A B : V →L[ℝ] V)
    (hA : LinearMap.trace ℝ V A.toLinearMap = 0) :
    hilbertSchmidtInner A (traceFree B) = hilbertSchmidtInner A B := by
  have hsum :
      (∑ i, inner ℝ (A ((stdOrthonormalBasis ℝ V) i))
        ((stdOrthonormalBasis ℝ V) i)) = LinearMap.trace ℝ V A.toLinearMap := by
    rw [LinearMap.trace_eq_sum_inner A.toLinearMap (stdOrthonormalBasis ℝ V)]
    apply Finset.sum_congr rfl
    intro i _
    exact real_inner_comm _ _
  rw [hilbertSchmidtInner_eq_sum_inner A (traceFree B) (stdOrthonormalBasis ℝ V),
    hilbertSchmidtInner_eq_sum_inner A B (stdOrthonormalBasis ℝ V)]
  simp_rw [traceFree, sub_apply, smul_apply, ContinuousLinearMap.id_apply,
    inner_sub_right, real_inner_smul_right]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, hA, mul_zero, sub_zero]

/-- Consequently, the trace-free parts pair exactly as the first trace-free
part pairs with the original second factor. -/
theorem hilbertSchmidtInner_traceFree_traceFree (A B : V →L[ℝ] V)
    (hdim : Module.finrank ℝ V ≠ 0) :
    hilbertSchmidtInner (traceFree A) (traceFree B) =
      hilbertSchmidtInner (traceFree A) B :=
  hilbertSchmidtInner_traceFree_right _ _ (trace_traceFree A hdim)

end AlmostSchur
