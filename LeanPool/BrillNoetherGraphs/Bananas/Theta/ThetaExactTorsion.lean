/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaPrincipal
import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaResidue
import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaArithmetic
import LeanPool.BrillNoetherGraphs.Bananas.Transmission.TransmissionAPI
import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaTorsionAPI

/-! Exact torsion order for normalized evenly marked theta marks. -/

namespace Bananas

open Utilities
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

theorem interiorMoment_zsmul
    (B : Banana 2) (alpha : Fin 3) (n : ℤ) (D : CFDiv B.graph) :
    interiorMoment B alpha (n • D) = n * interiorMoment B alpha D := by
  classical
  unfold interiorMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases h : r + 1 < B.length alpha
  · simp [h, Pi.smul_apply]
    ring
  · simp [h]

theorem thetaJacobianMoment_zsmul
    (B : Banana 2) (n : ℤ) (D : CFDiv B.graph) :
    thetaJacobianMoment B (n • D) = n • thetaJacobianMoment B D := by
  unfold thetaJacobianMoment
  rw [interiorMoment_zsmul B 0 n D, interiorMoment_zsmul B 1 n D,
    interiorMoment_zsmul B 2 n D]
  change
    (n * interiorMoment B 0 D + (B.length 0 : ℤ) * (n * D (rightEndpoint B)) -
        n * interiorMoment B 2 D,
      n * interiorMoment B 1 D - n * interiorMoment B 2 D) =
    (n * (interiorMoment B 0 D + (B.length 0 : ℤ) * D (rightEndpoint B) -
        interiorMoment B 2 D),
      n * (interiorMoment B 1 D - interiorMoment B 2 D))
  ext <;> ring

theorem torsionWitness_coordinate_mem_thetaLattice_01
    (B : Banana 2) (i : B.PathPosition 0) (j : B.PathPosition 1)
    (hi : B.IsInteriorPosition 0 i) (hj : B.IsInteriorPosition 1 j)
    (m : ℕ)
    (hm : TorsionWitness
      (mark B.graph (strandVertex B 0 i) (strandVertex B 1 j)) m) :
    (((m * i.val : ℕ) : ℤ), -((m * j.val : ℕ) : ℤ)) ∈
      thetaLattice (B.length 0) (B.length 1) (B.length 2) := by
  let diff : CFDiv B.graph :=
    oneChip (strandVertex B 0 i) - oneChip (strandVertex B 1 j)
  have hequiv : linearEquiv B.graph 0 ((m : ℤ) • diff) := hm.2.symm
  unfold linearEquiv at hequiv
  obtain ⟨script, hscript⟩ :=
    (principal_iff_eq_prin B.graph (((m : ℤ) • diff) - 0)).mp hequiv
  have hmem := thetaJacobianMoment_prin_mem B script
  have hmomentDiff : thetaJacobianMoment B diff =
      ((i.val : ℤ), -(j.val : ℤ)) := by
    exact thetaJacobianMoment_marked_difference_01 B i j hi hj
  have hmoment : thetaJacobianMoment B ((m : ℤ) • diff) =
      (((m * i.val : ℕ) : ℤ), -((m * j.val : ℕ) : ℤ)) := by
    rw [thetaJacobianMoment_zsmul, hmomentDiff]
    ext <;> simp
  rw [← hscript, sub_zero, hmoment] at hmem
  exact hmem

theorem evenlyMarkedTheta_isTorsionOrder_01
    (B : Banana 2) (i : B.PathPosition 0) (j : B.PathPosition 1)
    (hEven : EvenlyMarkedTheta B 0 1 i j) :
    IsTorsionOrder
      (mark B.graph (strandVertex B 0 i) (strandVertex B 1 j))
      (B.length 0 / Nat.gcd (B.length 0) i.val) := by
  let k := B.length 0 / Nat.gcd (B.length 0) i.val
  have hk : 0 < k := evenlyMarkedTheta_k_pos B 0 1 i j hEven
  have hWitness : TorsionWitness
      (mark B.graph (strandVertex B 0 i) (strandVertex B 1 j)) k := by
    have hContract : EvenlyMarkedThetaMultiplePrincipalContract := by
      intro B' alpha beta i' j' hEven'
      exact evenlyMarkedTheta_multiple_principal B' alpha beta i' j' hEven'
    exact torsionWitness_of_evenlyMarkedTheta_contract
      hContract B 0 1 i j hEven
  refine ⟨hWitness, ?_⟩
  intro m hm
  have hmem := torsionWitness_coordinate_mem_thetaLattice_01 B i j
    ⟨hEven.2.1, hEven.2.2.1⟩
    ⟨hEven.2.2.2.1, hEven.2.2.2.2.1⟩ m hm
  have hMin := thetaLattice_evenlyMarked_multiple_mem_iff
    (B.length 0) (B.length 1) (B.length 2) i.val j.val m
    (B.length_pos 0) (B.length_pos 1) (B.length_pos 2)
    hEven.2.1 hEven.2.2.1 hEven.2.2.2.1 hEven.2.2.2.2.1
    (by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using hEven.2.2.2.2.2.symm)
  have hdiv : k ∣ m := by simpa [k] using hMin.mp hmem
  exact Nat.le_of_dvd hm.1 hdiv

end Bananas
