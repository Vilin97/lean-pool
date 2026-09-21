/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5A2Envelope.Closure
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Basis.Basic

/-!
Norm- and pairing-preserving transformations are linear, using the dual image basis.
-/

namespace V7.Stage5AboveTwoLowerS5A2Envelope

open scoped BigOperators
open Stage5AboveTwoLower.S5ARepair

/-- The vector equal to one at coordinate `i` and zero elsewhere. -/
def coordinateUnit (i : Fin d) : Point d := fun j ↦ if j = i then 1 else 0

lemma pairing_coordinateUnit (x : Point d) (i : Fin d) :
    O3.pairing (coordinateUnit i) x = x i := by
  simp [O3.pairing, coordinateUnit]

/-- The dual images of the coordinate vectors are a basis.  This is the
separation wheel that turns the frozen pairing identity into linearity. -/
lemma signedLpSymmetry_dual_linearIndependent {p : ℝ}
    {Q Qdual : Point d → Point d} (hsym : SignedLpSymmetry p Q Qdual) :
    LinearIndependent ℝ (fun i : Fin d ↦ Qdual (coordinateUnit i)) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  have hpair : O3.pairing (Q (coordinateUnit i))
      (∑ j, a j • Qdual (coordinateUnit j)) = 0 := by
    rw [ha]
    simp [O3.pairing]
  have hpairing := hsym.2.2
  have hcoord : ∀ j : Fin d,
      O3.pairing (Qdual (coordinateUnit j)) (Q (coordinateUnit i)) =
        if j = i then 1 else 0 := by
    intro j
    calc
      O3.pairing (Qdual (coordinateUnit j)) (Q (coordinateUnit i)) =
          pairing (coordinateUnit j) (coordinateUnit i) :=
        hpairing (coordinateUnit j) (coordinateUnit i)
      _ = _ := by
        change O3.pairing (coordinateUnit j) (coordinateUnit i) = _
        rw [pairing_coordinateUnit]
        simp [coordinateUnit]
  rw [← pairingCLM_apply (Q (coordinateUnit i))
    (∑ j, a j • Qdual (coordinateUnit j))] at hpair
  rw [map_sum] at hpair
  simp only [map_smul] at hpair
  simp only [pairingCLM_apply] at hpair
  have hcoord' : ∀ j : Fin d,
      O3.pairing (Q (coordinateUnit i)) (Qdual (coordinateUnit j)) =
        if j = i then 1 else 0 := by
    intro j
    rw [O3.pairing_comm]
    exact hcoord j
  simp_rw [hcoord'] at hpair
  simpa using hpair

/-- The basis formed by the dual symmetry images of coordinate unit vectors. -/
noncomputable def signedLpDualBasis {p : ℝ}
    (Q Qdual : Point d → Point d) (hsym : SignedLpSymmetry p Q Qdual) :
    Module.Basis (Fin d) ℝ (Point d) :=
  by
    classical
    exact basisOfPiSpaceOfLinearIndependent
      (signedLpSymmetry_dual_linearIndependent hsym)

lemma eq_zero_of_pairing_dual_images_zero {p : ℝ}
    {Q Qdual : Point d → Point d} (hsym : SignedLpSymmetry p Q Qdual)
    {z : Point d} (hz : ∀ i : Fin d,
      O3.pairing (Qdual (coordinateUnit i)) z = 0) : z = 0 := by
  let b := signedLpDualBasis Q Qdual hsym
  have hall : ∀ v : Point d, O3.pairing v z = 0 := by
    intro v
    rw [← b.sum_repr v]
    rw [O3.pairing_comm]
    rw [← pairingCLM_apply z]
    rw [map_sum]
    simp only [map_smul, pairingCLM_apply]
    simp_rw [show ∀ i, b i = Qdual (coordinateUnit i) by
      intro i
      simp [b, signedLpDualBasis]]
    have hz' : ∀ i, O3.pairing z (Qdual (coordinateUnit i)) = 0 := by
      intro i
      rw [O3.pairing_comm]
      exact hz i
    simp_rw [hz']
    simp
  have hself := hall z
  have hsquares : ∑ i, z i ^ (2 : ℕ) = 0 := by
    simpa [O3.pairing, pow_two] using hself
  funext i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ Finset.univ) ↦ sq_nonneg (z j))).mp hsquares i
      (Finset.mem_univ i)
  exact sq_eq_zero_iff.mp hi

/-- The frozen pairing identity forces the primal map to be additive. -/
lemma signedLpSymmetry_Q_add {p : ℝ}
    {Q Qdual : Point d → Point d} (hsym : SignedLpSymmetry p Q Qdual)
    (x y : Point d) : Q (x + y) = Q x + Q y := by
  apply sub_eq_zero.mp
  apply eq_zero_of_pairing_dual_images_zero hsym
  intro i
  have hp := hsym.2.2
  have hxy := hp (coordinateUnit i) (x + y)
  have hx := hp (coordinateUnit i) x
  have hy := hp (coordinateUnit i) y
  change O3.pairing (Qdual (coordinateUnit i))
    (Q (x + y) - (Q x + Q y)) = 0
  have hlin : O3.pairing (Qdual (coordinateUnit i))
      (Q (x + y) - (Q x + Q y)) =
      O3.pairing (Qdual (coordinateUnit i)) (Q (x + y)) -
        (O3.pairing (Qdual (coordinateUnit i)) (Q x) +
          O3.pairing (Qdual (coordinateUnit i)) (Q y)) := by
    simp [O3.pairing, Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_sub, mul_add]
  rw [hlin]
  change pairing (Qdual (coordinateUnit i)) (Q (x + y)) -
    (pairing (Qdual (coordinateUnit i)) (Q x) +
      pairing (Qdual (coordinateUnit i)) (Q y)) = 0
  rw [hxy, hx, hy]
  simp [pairing_coordinateUnit]

/-- The frozen pairing identity forces the primal map to be homogeneous. -/
lemma signedLpSymmetry_Q_smul {p : ℝ}
    {Q Qdual : Point d → Point d} (hsym : SignedLpSymmetry p Q Qdual)
    (a : ℝ) (x : Point d) : Q (a • x) = a • Q x := by
  apply sub_eq_zero.mp
  apply eq_zero_of_pairing_dual_images_zero hsym
  intro i
  have hp := hsym.2.2
  have hax := hp (coordinateUnit i) (a • x)
  have hx := hp (coordinateUnit i) x
  change O3.pairing (Qdual (coordinateUnit i)) (Q (a • x) - a • Q x) = 0
  have hlin : O3.pairing (Qdual (coordinateUnit i)) (Q (a • x) - a • Q x) =
      O3.pairing (Qdual (coordinateUnit i)) (Q (a • x)) -
        a * O3.pairing (Qdual (coordinateUnit i)) (Q x) := by
    simp [O3.pairing, Finset.sum_sub_distrib, Finset.mul_sum, mul_sub,
      mul_left_comm]
  rw [hlin]
  change pairing (Qdual (coordinateUnit i)) (Q (a • x)) -
    a * pairing (Qdual (coordinateUnit i)) (Q x) = 0
  rw [hax, hx]
  simp [pairing_coordinateUnit]

end V7.Stage5AboveTwoLowerS5A2Envelope
