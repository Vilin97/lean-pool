/-
Copyright (c) 2026 jayyswan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: jayyswan
-/
module

public import LeanPool.HasseMinkowski.RankCriteria
public import LeanPool.HasseMinkowski.RankTwo
public import LeanPool.HasseMinkowski.HilbertSymbol.Reciprocity

/-!
# Rank-three Hasse–Minkowski over `ℚ` (Legendre descent)

This file reduces the rank-three Hasse–Minkowski principle over `ℚ` to a single, clearly
isolated local–global statement about the Hilbert symbol, the Hasse norm theorem for
quadratic extensions.  Writing `σ = -wq 2 * wq 0` and `τ = -wq 2 * wq 1` for the two
Hilbert-symbol arguments that the ternary criterion produces, the argument is:

1. diagonalize a nondegenerate rank-three form as `⟨w₀, w₁, w₂⟩` with `wᵢ : ℚˣ`
   (`equivalent_weightedSumSquares_units_of_nondegenerate'`);
2. the rank-three isotropy criterion `weightedSumSquares_isotropic_iff_hilbertSym_eq_one`
   identifies isotropy of `⟨w₀, w₁, w₂⟩` with `(σ, τ)_ℚ = 1`;
3. base-changing the local isotropy data produces `(σ, τ)_v = 1` at every place `v`
   (the finite places `ℚ_[p]` and the archimedean place `ℝ`);
4. the local–global statement `HilbertSymLocalGlobal` then yields `(σ, τ)_ℚ = 1`.

Step 4, `HilbertSymLocalGlobal`, is the Hasse norm theorem for quadratic extensions of `ℚ`
(equivalently, Hasse–Minkowski for the conic `z² = σ x² + τ y²`); it is the rank-three
local–global principle and is **proved** by elementary Legendre descent in
`HasseMinkowski/Legendre.lean` (`hilbertSymLocalGlobal`), which also derives the
unconditional `isotropic_of_rank_three'`.  It is kept here as an explicit hypothesis so the
reduction below is independent of the descent proof.  Every declaration below is sorry-free.

## Main results

* `HilbertSymLocalGlobal`: the missing local–global input.
* `isotropic_of_rank_three`: the rank-three case, conditional on `HilbertSymLocalGlobal`.
-/

public section

open Module QuadraticMap TensorProduct

namespace HasseMinkowski

/-! ### The isolated local–global input for the Hilbert symbol -/

/-- **Legendre's theorem.**  A global Hilbert symbol `(A, B)_ℚ` is trivial as soon as its
base changes `(A, B)_v` are trivial at every place `v` of `ℚ` (every prime `p` and the
archimedean place `ℝ`).

This is the Hasse norm theorem for the quadratic extension `ℚ(√B)` (or `√A`) and the
rank-three local–global principle; it is proved by elementary descent (CRT plus the norm
criterion) in `HasseMinkowski/Legendre.lean` (`hilbertSymLocalGlobal`).  It is kept as a
`def`/`Prop` here so that the rank-three reduction does not depend on that proof. -/
def HilbertSymLocalGlobal : Prop :=
  ∀ A B : ℚ, A ≠ 0 → B ≠ 0 →
    (∀ (p : ℕ) [Fact (Nat.Prime p)], hilbertSym (A : ℚ_[p]) (B : ℚ_[p]) = 1) →
    hilbertSym (A : ℝ) (B : ℝ) = 1 → hilbertSym A B = 1

/-! ### Reindexing `Fin 3` weights -/

-- Theorem: the diagonal form with weights written `![w 0, w 1, w 2]` is the same diagonal
-- form as the one with weights `w`.
private theorem weightedSumSquares_fin3_eq {k : Type*} [Field k] (w : Fin 3 → k) :
    weightedSumSquares k ![w 0, w 1, w 2] = weightedSumSquares k w := by
  rw [show (![w 0, w 1, w 2] : Fin 3 → k) = w from by
    funext i
    fin_cases i <;> rfl]

-- Theorem: if a rank-three diagonal form `⟨w 0, w 1, w 2⟩` with nonzero weights is
-- isotropic, the criterion reads off `(−w₂w₀, −w₂w₁) = 1` for its Hilbert symbol.
private theorem hilbertSym_neg_mul_of_isotropic {k : Type*} [Field k] (w : Fin 3 → k)
    (h0 : w 0 ≠ 0) (h1 : w 1 ≠ 0) (h2 : w 2 ≠ 0)
    (h : (weightedSumSquares k w).Isotropic) :
    hilbertSym (-w 2 * w 0) (-w 2 * w 1) = 1 := by
  have h' : (weightedSumSquares k ![w 0, w 1, w 2]).Isotropic := by
    rwa [weightedSumSquares_fin3_eq w]
  exact (weightedSumSquares_isotropic_iff_hilbertSym_eq_one (w 0) (w 1) (w 2)
    h0 h1 h2).mp h'

/-! ### The rank-three theorem -/

section RankThree

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]

-- Theorem: a nondegenerate rank-three form over `ℚ` that is isotropic over every
-- completion is isotropic over `ℚ`, conditional on the local–global principle for the
-- Hilbert symbol (`HilbertSymLocalGlobal`).
theorem isotropic_of_rank_three (hloc : HilbertSymLocalGlobal) (Q : QuadraticForm ℚ V)
    (hr : finrank ℚ V = 3) (hQ : Q.Nondegenerate) (hQ' : EverywhereLocallyIsotropic Q) :
    Isotropic Q := by
  obtain ⟨hQ'f, hQ'R⟩ := hQ'
  have hsep : (QuadraticMap.associated (R := ℚ) Q).SeparatingLeft :=
    (QuadraticMap.nondegenerate_associated_iff.mpr hQ).1
  obtain ⟨w₀, hw₀⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hsep
  have hw3 : ∃ w : Fin 3 → ℚˣ,
      Q.Equivalent (weightedSumSquares ℚ (fun i => (w i : ℚ))) := by
    revert w₀ hw₀
    rw [hr]
    exact fun w hw => ⟨w, hw⟩
  obtain ⟨w, hw⟩ := hw3
  let wq : Fin 3 → ℚ := fun i => (w i : ℚ)
  have hwq0 : wq 0 ≠ 0 := by simp [wq]
  have hwq1 : wq 1 ≠ 0 := by simp [wq]
  have hwq2 : wq 2 ≠ 0 := by simp [wq]
  have hw' : Q.Equivalent (weightedSumSquares ℚ wq) := by
    simpa only [wq] using hw
  set A : ℚ := -wq 2 * wq 0 with hA_def
  set B : ℚ := -wq 2 * wq 1 with hB_def
  have hA : A ≠ 0 := by
    rw [hA_def]
    exact mul_ne_zero (neg_ne_zero.mpr hwq2) hwq0
  have hB : B ≠ 0 := by
    rw [hB_def]
    exact mul_ne_zero (neg_ne_zero.mpr hwq2) hwq1
  have hlocp : ∀ (p : ℕ) [Fact (Nat.Prime p)],
      hilbertSym (A : ℚ_[p]) (B : ℚ_[p]) = 1 := by
    intro p _
    have heq : (Q.baseChange ℚ_[p]).Equivalent
        (weightedSumSquares ℚ_[p] (fun i => algebraMap ℚ ℚ_[p] (wq i))) :=
      (hw'.baseChange (A := ℚ_[p])).trans
        (baseChange_weightedSumSquares (R := ℚ) (A := ℚ_[p]) (w := wq))
    have hiso : (weightedSumSquares ℚ_[p]
        (fun i => algebraMap ℚ ℚ_[p] (wq i))).Isotropic :=
      (heq.isotropic_iff).mp (hQ'f p)
    have h0 : algebraMap ℚ ℚ_[p] (wq 0) ≠ 0 := Rat.cast_ne_zero.mpr hwq0
    have h1 : algebraMap ℚ ℚ_[p] (wq 1) ≠ 0 := Rat.cast_ne_zero.mpr hwq1
    have h2 : algebraMap ℚ ℚ_[p] (wq 2) ≠ 0 := Rat.cast_ne_zero.mpr hwq2
    have hraw := hilbertSym_neg_mul_of_isotropic
      (fun i => algebraMap ℚ ℚ_[p] (wq i)) h0 h1 h2 hiso
    rw [hA_def, hB_def]
    push_cast
    exact hraw
  have hlocR : hilbertSym (A : ℝ) (B : ℝ) = 1 := by
    have heq : (Q.baseChange ℝ).Equivalent
        (weightedSumSquares ℝ (fun i => algebraMap ℚ ℝ (wq i))) :=
      (hw'.baseChange (A := ℝ)).trans
        (baseChange_weightedSumSquares (R := ℚ) (A := ℝ) (w := wq))
    have hiso : (weightedSumSquares ℝ
        (fun i => algebraMap ℚ ℝ (wq i))).Isotropic :=
      (heq.isotropic_iff).mp hQ'R
    have h0 : algebraMap ℚ ℝ (wq 0) ≠ 0 := Rat.cast_ne_zero.mpr hwq0
    have h1 : algebraMap ℚ ℝ (wq 1) ≠ 0 := Rat.cast_ne_zero.mpr hwq1
    have h2 : algebraMap ℚ ℝ (wq 2) ≠ 0 := Rat.cast_ne_zero.mpr hwq2
    have hraw := hilbertSym_neg_mul_of_isotropic
      (fun i => algebraMap ℚ ℝ (wq i)) h0 h1 h2 hiso
    rw [hA_def, hB_def]
    push_cast
    exact hraw
  have hsym : hilbertSym A B = 1 := hloc A B hA hB hlocp hlocR
  have hglob : (weightedSumSquares ℚ wq).Isotropic := by
    have h! : (weightedSumSquares ℚ ![wq 0, wq 1, wq 2]).Isotropic :=
      (weightedSumSquares_isotropic_iff_hilbertSym_eq_one (wq 0) (wq 1) (wq 2)
        hwq0 hwq1 hwq2).mpr (by rw [← hA_def, ← hB_def]; exact hsym)
    rw [show (![wq 0, wq 1, wq 2] : Fin 3 → ℚ) = wq from by
      funext i
      fin_cases i <;> rfl] at h!
    exact h!
  exact (hw'.isotropic_iff).mpr hglob

end RankThree

end HasseMinkowski

namespace HasseMinkowski

/-! ### C.0 assessment: why the product-formula route is circular

Under the hypotheses of `HilbertSymLocalGlobal` every local factor `(A,B)_v` is already `1`,
so the product formula `hilbertReciprocity` reduces to the tautology `1 * 1 = 1` and carries
no information about the *global* symbol `(A,B)_ℚ` (see
`hilbertProd_eq_one_of_local_eq_one`).  The target is instead exactly the rank-three
local–global principle for the diagonal ternary form `⟨-A,-B,1⟩`, i.e. Legendre's theorem /
the Hasse norm theorem for quadratic extensions of `ℚ`; the equivalence
`hilbertSymLocalGlobal_iff_rankThreeDiagonal` below pins this down precisely.  That principle
is now proved by Legendre descent in `HasseMinkowski/Legendre.lean`; it is recorded here
as a hypothesis so that this file does not depend on that proof. -/

/-- The rank-three local–global principle for diagonal ternary forms of the shape
`⟨-A,-B,1⟩` over `ℚ` (equivalently, solvability of the conic `z² = A x² + B y²`): local
isotropy over every completion implies global isotropy.  This is Legendre's theorem. -/
def RankThreeDiagonalLocalGlobal : Prop :=
  ∀ A B : ℚ, A ≠ 0 → B ≠ 0 →
    (∀ (p : ℕ) [Fact (Nat.Prime p)],
        (weightedSumSquares ℚ_[p]
          ![(-(A : ℚ_[p])), (-(B : ℚ_[p])), (1 : ℚ_[p])]).Isotropic) →
    (weightedSumSquares ℝ ![(-(A : ℝ)), (-(B : ℝ)), (1 : ℝ)]).Isotropic →
    (weightedSumSquares ℚ ![(-A), (-B), (1 : ℚ)]).Isotropic

-- Theorem: under the hypotheses of `HilbertSymLocalGlobal` the conclusion of Hilbert
-- reciprocity holds automatically, so reciprocity cannot constrain the global symbol.
theorem hilbertProd_eq_one_of_local_eq_one {A B : ℚ}
    (hloc : ∀ (p : ℕ) [Fact (Nat.Prime p)], hilbertSym (A : ℚ_[p]) (B : ℚ_[p]) = 1)
    (hR : hilbertSym (A : ℝ) (B : ℝ) = 1) : hilbertProd A B = 1 := by
  unfold hilbertProd
  rw [finprod_eq_one_of_forall_eq_one (fun p : Nat.Primes => hloc (p : ℕ)), hR, one_mul]

-- Theorem: `HilbertSymLocalGlobal` is precisely the rank-three local–global principle for
-- the diagonal forms `⟨-A,-B,1⟩` (Legendre's theorem); the product formula is not involved.
theorem hilbertSymLocalGlobal_iff_rankThreeDiagonal :
    HilbertSymLocalGlobal ↔ RankThreeDiagonalLocalGlobal := by
  constructor
  · intro hloc A B hA hB hisop hisoR
    have hp : ∀ (p : ℕ) [Fact (Nat.Prime p)],
        hilbertSym (A : ℚ_[p]) (B : ℚ_[p]) = 1 := by
      intro p _
      have h := (weightedSumSquares_isotropic_iff_hilbertSym_eq_one
        (-(A : ℚ_[p])) (-(B : ℚ_[p])) (1 : ℚ_[p])
        (neg_ne_zero.mpr (Rat.cast_ne_zero.mpr hA))
        (neg_ne_zero.mpr (Rat.cast_ne_zero.mpr hB)) one_ne_zero).mp (hisop p)
      simpa using h
    have hR : hilbertSym (A : ℝ) (B : ℝ) = 1 := by
      have h := (weightedSumSquares_isotropic_iff_hilbertSym_eq_one
        (-(A : ℝ)) (-(B : ℝ)) (1 : ℝ)
        (neg_ne_zero.mpr (Rat.cast_ne_zero.mpr hA))
        (neg_ne_zero.mpr (Rat.cast_ne_zero.mpr hB)) one_ne_zero).mp hisoR
      simpa using h
    exact (weightedSumSquares_isotropic_iff_hilbertSym_eq_one (-A) (-B) (1 : ℚ)
      (neg_ne_zero.mpr hA) (neg_ne_zero.mpr hB) one_ne_zero).mpr
      (by simpa using hloc A B hA hB hp hR)
  · intro hdiag A B hA hB hlocp hlocR
    have hisop : ∀ (p : ℕ) [Fact (Nat.Prime p)],
        (weightedSumSquares ℚ_[p]
          ![(-(A : ℚ_[p])), (-(B : ℚ_[p])), (1 : ℚ_[p])]).Isotropic := by
      intro p _
      exact (weightedSumSquares_isotropic_iff_hilbertSym_eq_one
        (-(A : ℚ_[p])) (-(B : ℚ_[p])) (1 : ℚ_[p])
        (neg_ne_zero.mpr (Rat.cast_ne_zero.mpr hA))
        (neg_ne_zero.mpr (Rat.cast_ne_zero.mpr hB)) one_ne_zero).mpr
        (by simpa using hlocp p)
    have hisoR : (weightedSumSquares ℝ ![(-(A : ℝ)), (-(B : ℝ)), (1 : ℝ)]).Isotropic :=
      (weightedSumSquares_isotropic_iff_hilbertSym_eq_one
        (-(A : ℝ)) (-(B : ℝ)) (1 : ℝ)
        (neg_ne_zero.mpr (Rat.cast_ne_zero.mpr hA))
        (neg_ne_zero.mpr (Rat.cast_ne_zero.mpr hB)) one_ne_zero).mpr
        (by simpa using hlocR)
    have hglob := hdiag A B hA hB hisop hisoR
    have h := (weightedSumSquares_isotropic_iff_hilbertSym_eq_one (-A) (-B) (1 : ℚ)
      (neg_ne_zero.mpr hA) (neg_ne_zero.mpr hB) one_ne_zero).mp hglob
    simpa using h

end HasseMinkowski
