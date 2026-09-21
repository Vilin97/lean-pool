/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Foundations.Parameters

/-!
# Kernel-checked rank-one certificates

This module is the small handwritten soundness layer for externally generated
rank-one witnesses on a fixed finite graph.  A certificate contains only
passive data:

* a divisor `D`; and
* for every vertex `q`, an integer firing script which makes `D - q`
  effective.

The Boolean checker evaluates degrees, Laplacians, and pointwise inequalities
inside Lean.  The soundness theorem then turns a successful check into
`BNExists G 1 d`.  Consequently a C (or other) program may search for and emit
the data, but it is not part of the trusted proof.

Our script convention agrees with `ChipFiringWithLean.prin`: the checked
residual is `D - q + prin G sigma`, equivalently `D - q - L sigma`.
-/

namespace Utilities.Certificate

open Finset

/-- An effective degree-one divisor consists of a single chip at one vertex. -/
theorem effective_degree_one_eq_one_chip
    {G : CFGraph} {E : CFDiv G}
    (hEffective : effective E) (hDegree : deg E = 1) :
    ∃ q : G.V, E = one_chip q := by
  have hSum : ∑ q : G.V, E q = 1 := by
    simpa [deg] using hDegree
  have hSumNe : ∑ q : G.V, E q ≠ 0 := by
    rw [hSum]
    norm_num
  obtain ⟨q, _hqMem, hqNe⟩ := Finset.exists_ne_zero_of_sum_ne_zero hSumNe
  have hqPos : 0 < E q :=
    lt_of_le_of_ne (hEffective q) hqNe.symm
  have hqLe : E q ≤ ∑ v : G.V, E v :=
    Finset.single_le_sum (fun v _ => hEffective v) (Finset.mem_univ q)
  have hq : E q = 1 := by
    rw [hSum] at hqLe
    omega
  have hSubEffective : effective (E - one_chip q) := by
    intro v
    by_cases hv : v = q
    · subst v
      simp [one_chip, hq]
    · simp [one_chip, hv, hEffective v]
  have hSubDegree : deg (E - one_chip q) = 0 := by
    rw [deg.map_sub, deg_one_chip, hDegree]
    norm_num
  have hSubZero : E - one_chip q = 0 :=
    eff_degree_zero (E - one_chip q) hSubEffective hSubDegree
  exact ⟨q, sub_eq_zero.mp hSubZero⟩

/-- Passive certificate data for a rank-one divisor on a fixed graph. -/
structure RankOne (G : CFGraph) where
  divisor : CFDiv G
  scripts : G.V → firing_script G

namespace RankOne

variable {G : CFGraph}

/-- The result of removing the chip at `q` and applying its certificate script. -/
def residual (certificate : RankOne G) (q : G.V) : CFDiv G :=
  certificate.divisor - one_chip q + prin G (certificate.scripts q)

/-- Propositional validity at one vertex. -/
def ValidAt (certificate : RankOne G) (q : G.V) : Prop :=
  effective (certificate.residual q)

/-- A rank-one certificate with the requested divisor degree. -/
def Valid (certificate : RankOne G) (d : ℤ) : Prop :=
  deg certificate.divisor = d ∧ ∀ q : G.V, certificate.ValidAt q

/-- Executable pointwise effectivity test. -/
def checkEffective (D : CFDiv G) : Bool :=
  @decide (∀ v : G.V, 0 ≤ D v) Fintype.decidableForallFintype

/-- Executable check of the script associated to one removed chip. -/
def checkAt (certificate : RankOne G) (q : G.V) : Bool :=
  checkEffective (certificate.residual q)

/-- Executable check of the degree and every vertex script. -/
def check (certificate : RankOne G) (d : ℤ) : Bool :=
  decide (deg certificate.divisor = d) &&
    @decide (∀ q : G.V, certificate.checkAt q = true)
      Fintype.decidableForallFintype

@[simp] theorem checkEffective_eq_true_iff (D : CFDiv G) :
    checkEffective D = true ↔ effective D := by
  simp [checkEffective, effective]

@[simp] theorem checkAt_eq_true_iff
    (certificate : RankOne G) (q : G.V) :
    certificate.checkAt q = true ↔ certificate.ValidAt q := by
  simp [checkAt, ValidAt]

@[simp] theorem check_eq_true_iff
    (certificate : RankOne G) (d : ℤ) :
    certificate.check d = true ↔ certificate.Valid d := by
  simp [check, Valid]

/-- A certificate script supplies an explicit linear equivalence from
`D - q` to its residual. -/
theorem sub_one_chip_linear_equiv_residual
    (certificate : RankOne G) (q : G.V) :
    linear_equiv G (certificate.divisor - one_chip q)
      (certificate.residual q) := by
  unfold linear_equiv residual
  rw [principal_iff_eq_prin]
  refine ⟨certificate.scripts q, ?_⟩
  abel

/-- Soundness at one vertex: a checked effective residual makes `D - q`
winnable. -/
theorem winnable_sub_one_chip_of_validAt
    (certificate : RankOne G) (q : G.V)
    (hValid : certificate.ValidAt q) :
    winnable G (certificate.divisor - one_chip q) := by
  exact ⟨certificate.residual q, hValid,
    certificate.sub_one_chip_linear_equiv_residual q⟩

/-- The mathematical soundness theorem for the passive certificate object. -/
theorem rank_ge_one_of_valid
    (certificate : RankOne G) {d : ℤ}
    (hValid : certificate.Valid d) :
    rank G certificate.divisor ≥ 1 := by
  apply (rank_geq_iff G certificate.divisor 1).mp
  intro E hE
  obtain ⟨q, rfl⟩ :=
    effective_degree_one_eq_one_chip hE.1 hE.2
  exact certificate.winnable_sub_one_chip_of_validAt q (hValid.2 q)

/-- A propositionally valid certificate is already a rank-one
Brill--Noether witness. -/
theorem bnExists_of_valid
    (certificate : RankOne G) (d : ℤ)
    (hValid : certificate.Valid d) :
    BNExists G 1 d :=
  ⟨certificate.divisor, hValid.1,
    certificate.rank_ge_one_of_valid hValid⟩

/-- A successful Boolean check yields a kernel-checked Brill--Noether
rank-one existence theorem. -/
theorem bnExists_of_check_eq_true
    (certificate : RankOne G) (d : ℤ)
    (hCheck : certificate.check d = true) :
    BNExists G 1 d := by
  have hValid : certificate.Valid d :=
    (certificate.check_eq_true_iff d).mp hCheck
  exact certificate.bnExists_of_valid d hValid

end RankOne

end Utilities.Certificate
