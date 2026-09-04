/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.ProductSplit

/-!
# Constructing a dominating chain for ordered two-point systems

This is the finite induction used to prove the two-point case of Theorem 2.1.
Its sole input is the local insertion theorem.  The product law is split at
the last coordinate, the induction hypothesis constructs a chain on the old
coordinates, and one insertion of the new coordinate completes the step.
-/

open scoped BigOperators

namespace Feige

/-- The uniform local conclusion needed at every induction stage, restricted
to the strict ordered systems to which the analytic insertion proof applies. -/
def StrictOrderedLocalInsertion : Prop :=
  ∀ {n : ℕ}
    (γ β : Fin (n + 1) → ℝ)
    (hγpos : ∀ i, 0 < γ i) (_hγle : ∀ i, γ i ≤ 1)
    (hβpos : ∀ i, 0 < β i) (_hγord : Antitone γ)
    (σ : Equiv.Perm (Fin n))
    (g : Finset (Fin (n + 1)) → ℝ),
    Monotone g →
      ∃ J : Fin (n + 1),
        booleanChainExpectation
            (fun i ↦ γ i.castSucc) (fun i ↦ β i.castSucc) σ
            (fun i ↦ (hγpos i.castSucc).le)
            (fun i ↦ (hβpos i.castSucc).le)
            (revealedLastPayoff
              (twoPointHighProbability γ β (Fin.last n)) g) ≤
          booleanChainExpectation γ β (insertChainPerm σ J)
            (fun i ↦ (hγpos i).le) (fun i ↦ (hβpos i).le) g

/-- Revealing one independent Bernoulli coordinate preserves monotonicity
of a payoff on the Boolean lattice. -/
theorem monotone_revealedLastPayoff {n : ℕ}
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {g : Finset (Fin (n + 1)) → ℝ} (hg : Monotone g) :
    Monotone (revealedLastPayoff p g) := by
  intro S T hST
  unfold revealedLastPayoff
  have hlift :
      liftChainState S ⊆ liftChainState T := by
    exact Finset.map_subset_map.mpr hST
  have hlower :
      g (liftChainState S) ≤ g (liftChainState T) :=
    hg hlift
  have hupper :
      g (insert (Fin.last n) (liftChainState S)) ≤
        g (insert (Fin.last n) (liftChainState T)) := by
    exact hg (Finset.insert_subset_insert (Fin.last n) hlift)
  exact add_le_add
    (mul_le_mul_of_nonneg_left hlower (sub_nonneg.mpr hp1))
    (mul_le_mul_of_nonneg_left hupper hp0)

/-- The unique zero-dimensional Boolean chain has the same expectation as
the zero-dimensional product law. -/
theorem productHighSetExpectation_zero_eq_chain
    (γ β : Fin 0 → ℝ) (g : Finset (Fin 0) → ℝ) :
    productHighSetExpectation
        (twoPointHighProbability γ β) g =
      booleanChainExpectation γ β (Equiv.refl (Fin 0))
        (fun i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i) g := by
  classical
  have hK : twoPointKFinset γ β ∅ = 1 := by
    simpa [twoPointKFinset] using
      twoPointK_empty γ β (fun i ↦ Fin.elim0 i)
  unfold productHighSetExpectation booleanChainExpectation
    CalibratedChain.expectation
  simp [highSetMass, booleanCalibratedChain, chainMass,
    booleanChainK, hK]

/-- The finite chain construction for strictly positive parameters already
arranged in nonincreasing `γ` order. -/
theorem exists_chain_dominating_product_of_localInsertion
    (hlocal : StrictOrderedLocalInsertion)
    {m : ℕ} (γ β : Fin m → ℝ)
    (hγpos : ∀ i, 0 < γ i) (hγle : ∀ i, γ i ≤ 1)
    (hβpos : ∀ i, 0 < β i) (hγord : Antitone γ)
    (g : Finset (Fin m) → ℝ) (hg : Monotone g) :
    ∃ σ : Equiv.Perm (Fin m),
      productHighSetExpectation (twoPointHighProbability γ β) g ≤
        booleanChainExpectation γ β σ
          (fun i ↦ (hγpos i).le) (fun i ↦ (hβpos i).le) g := by
  induction m with
  | zero =>
      refine ⟨Equiv.refl (Fin 0), ?_⟩
      exact (productHighSetExpectation_zero_eq_chain γ β g).le
  | succ n ih =>
      let γold : Fin n → ℝ := fun i ↦ γ i.castSucc
      let βold : Fin n → ℝ := fun i ↦ β i.castSucc
      let p : ℝ := twoPointHighProbability γ β (Fin.last n)
      let gold : Finset (Fin n) → ℝ := revealedLastPayoff p g
      have hp0 : 0 ≤ p :=
        twoPointHighProbability_nonneg
          (fun i ↦ (hγpos i).le) hβpos (Fin.last n)
      have hp1 : p ≤ 1 :=
        twoPointHighProbability_le_one
          (fun i ↦ (hγpos i).le) hβpos (Fin.last n)
      have hgold : Monotone gold :=
        monotone_revealedLastPayoff hp0 hp1 hg
      have hγoldpos : ∀ i, 0 < γold i :=
        fun i ↦ hγpos i.castSucc
      have hγoldle : ∀ i, γold i ≤ 1 :=
        fun i ↦ hγle i.castSucc
      have hβoldpos : ∀ i, 0 < βold i :=
        fun i ↦ hβpos i.castSucc
      have hγoldord : Antitone γold := by
        intro i j hij
        exact hγord (Fin.castSucc_le_castSucc_iff.mpr hij)
      obtain ⟨σ, hσ⟩ :=
        ih γold βold hγoldpos hγoldle hβoldpos hγoldord
          gold hgold
      obtain ⟨J, hJ⟩ :=
        hlocal γ β hγpos hγle hβpos hγord σ g hg
      refine ⟨insertChainPerm σ J, ?_⟩
      rw [productHighSetExpectation_succ]
      exact hσ.trans hJ

/-- Ordered strict two-point calibration follows immediately once the local
insertion theorem has been discharged. -/
theorem orderedStrictTwoPoint_rejection_le_of_localInsertion
    (hlocal : StrictOrderedLocalInsertion)
    {m : ℕ} (γ β : Fin m → ℝ)
    (hγpos : ∀ i, 0 < γ i) (hγle : ∀ i, γ i ≤ 1)
    (hβpos : ∀ i, 0 < β i) (hγord : Antitone γ)
    {α : ℝ} (hα : 0 ≤ α) :
    twoPointRejectionMass γ β α ≤ α := by
  rw [← productExpectation_rejection_eq]
  obtain ⟨σ, hσ⟩ :=
    exists_chain_dominating_product_of_localInsertion hlocal
      γ β hγpos hγle hβpos hγord
      (booleanRejectionPayoff γ β α)
      (monotone_booleanRejectionPayoff γ β
        (fun i ↦ (hγpos i).le) (fun i ↦ (hβpos i).le) α)
  exact hσ.trans
    (booleanChain_rejection_le γ β σ
      (fun i ↦ (hγpos i).le) (fun i ↦ (hβpos i).le) hα)

end Feige
