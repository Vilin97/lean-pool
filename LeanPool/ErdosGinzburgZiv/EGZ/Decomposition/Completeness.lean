/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Cleanup

/-!
# Stability of decomposition completeness

These monotonicity and mass identities are used when normalizing epsilon,
choosing the final uniform delta, and transferring thickness through cleanup.
-/

@[expose] public section

open scoped BigOperators

namespace EGZ

theorem IsThickAlong.mono_delta {p d : ℕ} [NeZero p]
    {w : FpCoord p d → ℕ} {ξ : FpCoord p d →ᵃ[ZMod p] ZMod p}
    {K : ℕ} {δ δ' : ℝ} (h : IsThickAlong w ξ K δ) (hδ : δ' ≤ δ) :
    IsThickAlong w ξ K δ' := by
  rw [isThickAlong_iff_compl] at h ⊢
  exact (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg _)).trans_lt h

namespace FlagDecomposition

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}

/-- Total lifted mass at a node is its cumulative finite-field mass. -/
theorem liftedMassOn_polytope (hp : Odd p) (Φ : FlagDecomposition p d f)
    (x : Φ.flag.Node) :
    Φ.liftedMassOn x (Φ.flag.polytope x).carrier = natMass (Φ.cumulativeWeight x) := by
  classical
  rw [← Φ.sum_liftedSupport hp x]
  apply Finset.sum_congr rfl
  intro q hq
  apply ite_eq_left
  rw [Φ.polytope_eq_liftedSupport]
  exact _root_.subset_convexHull ℝ _ ⟨q, hq, rfl⟩

theorem isLargeElement_iff_natMass (hp : Odd p) (Φ : FlagDecomposition p d f)
    (ε : ℝ) (x : Φ.flag.Node) :
    Φ.IsLargeElement ε x ↔ ε * (Φ.retainedMass : ℝ) ≤ natMass (Φ.cumulativeWeight x) := by
  rw [IsLargeElement, Φ.liftedMassOn_polytope hp]

theorem IsLargeElement.mono_epsilon {Φ : FlagDecomposition p d f}
    {ε ε' : ℝ} {x : Φ.flag.Node} (h : Φ.IsLargeElement ε x) (hε : ε' ≤ ε) :
    Φ.IsLargeElement ε' x :=
  (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _)).trans h

theorem IsLargeFace.mono_epsilon {Φ : FlagDecomposition p d f}
    {ε ε' : ℝ} {x : Φ.flag.Node} {Γ : (Φ.flag.polytope x).Face}
    (h : Φ.IsLargeFace ε x Γ) (hε : ε' ≤ ε) : Φ.IsLargeFace ε' x Γ := by
  refine ⟨(mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _)).trans h.1, ?_⟩
  intro Γ' hΓ'
  exact (h.2 Γ' hΓ').trans
    (mul_le_mul_of_nonneg_right (sub_le_sub_left hε 1) (Nat.cast_nonneg _))

theorem IsCompleteElement.mono_delta {Φ : FlagDecomposition p d f}
    {x : Φ.flag.Node} {t : ℕ} {δ δ' : ℝ}
    (h : Φ.IsCompleteElement x t δ) (hδ : δ' ≤ δ) :
    Φ.IsCompleteElement x t δ' := fun ξ hξ ↦ (h ξ hξ).mono_delta hδ

/-- Increasing epsilon asks for completeness and realization at fewer nodes
and faces. -/
theorem IsComplete.mono_epsilon {Φ : FlagDecomposition p d f}
    {T : Φ.flag.Node → ℕ} {ε ε' δ : ℝ}
    (h : Φ.IsComplete T ε δ) (hε : ε ≤ ε') : Φ.IsComplete T ε' δ :=
  ⟨h.1, h.2.1, fun x hx ↦ h.2.2.1 x (hx.mono_epsilon hε),
    fun x Γ hΓ ↦ h.2.2.2 x Γ (hΓ.mono_epsilon hε)⟩

theorem IsComplete.mono_delta {Φ : FlagDecomposition p d f}
    {T : Φ.flag.Node → ℕ} {ε δ δ' : ℝ}
    (h : Φ.IsComplete T ε δ) (hδ : δ' ≤ δ) : Φ.IsComplete T ε δ' :=
  ⟨h.1, h.2.1, fun x hx ↦ (h.2.2.1 x hx).mono_delta hδ, h.2.2.2⟩

end FlagDecomposition

end EGZ
