/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.Basic

/-!
# Statement of relative expansion

`RelativeExpansionStatement` is the proposition corresponding to the
paper's Theorem `thexp`. Its proof is `relative_expansion_theorem` in
`EGZ.Expansion.RelativeProof`. This separate statement module also lets
the main assembly expose its analytic dependencies explicitly.

The multisets `X_q` are encoded by one multiplicity function on the product
coordinates.  The first-coordinate support condition records their labels.
The harmless condition `2 * K < p` makes those integer labels distinct
modulo `p`; it can always be absorbed into the prime threshold.

The paper's "linear functions" are affine functionals, consistently with
its slab definition and with the functional constructed in its proof.
-/

@[expose] public section

open scoped BigOperators

namespace EGZ
namespace Expansion

/-- A single instance of the relative expansion conclusion, at the stated
dimension, box, thickness, width, and prime. -/
def RelativeExpansionAt (r t K : ℕ) (δ : ℝ) (T p : ℕ) [NeZero p] : Prop :=
  ∀ (S : Finset (IntCoord r)) (w : FpCoord p (r + t) → ℕ) (α : S → ℤ),
    (∀ q ∈ S, latticeSupNorm q ≤ K) →
    (∀ v, w v ≠ 0 → ∃ q ∈ S, Coord.first r t v = q.mod p) →
    (∑ q : S, α q • (q : IntCoord r)) = 0 →
    (∑ q : S, α q) = (p : ℤ) →
    (∀ q : S, δ * p ≤ (α q : ℝ) ∧
      (α q : ℝ) ≤ (pushWeight (Coord.first r t) w ((q : IntCoord r).mod p) : ℝ) -
        δ * p) →
    IsThickRelative w (Coord.first r t) T δ →
    HasZeroSumMultiplicity w

/-- The relative expansion theorem, with its uniform quantifier order.
Neither threshold depends on `T`, `p`, the support, the multiplicities,
or the selected coefficients. -/
def RelativeExpansionStatement : Prop :=
  ∀ r t K : ℕ, 1 ≤ K → ∀ δ : ℝ, 0 < δ →
    ∃ T₀ p₀ : ℕ, ∀ T : ℕ, T₀ ≤ T →
      ∀ p : ℕ, ∀ (_ : Fact p.Prime) (_ : NeZero p), p₀ ≤ p → 2 * K < p →
        RelativeExpansionAt r t K δ T p

/-- A usable threshold can include injectivity of reduction on the box. -/
theorem RelativeExpansionStatement.thresholds (h : RelativeExpansionStatement)
    (r t K : ℕ) (hK : 1 ≤ K) (δ : ℝ) (hδ : 0 < δ) :
    ∃ T₀ p₀ : ℕ, 2 * K < p₀ ∧
      ∀ T : ℕ, T₀ ≤ T → ∀ p : ℕ,
        ∀ (_ : Fact p.Prime) (_ : NeZero p), p₀ ≤ p →
          RelativeExpansionAt r t K δ T p := by
  obtain ⟨T₀, p₀, hp⟩ := h r t K hK δ hδ
  refine ⟨T₀, max p₀ (2 * K + 1), by omega, ?_⟩
  intro T hT p hpprime hpzero hpp
  exact hp T hT p hpprime hpzero (by omega) (by omega)

/-- A theorem at a smaller slab width applies at every larger width. -/
theorem RelativeExpansionAt.mono_width {r t K T T' p : ℕ} [NeZero p] {δ : ℝ}
    (h : RelativeExpansionAt r t K δ T p) (hT : T ≤ T') :
    RelativeExpansionAt r t K δ T' p := by
  intro S w α hbox hs hz hm ha hthick
  exact h S w α hbox hs hz hm ha (hthick.mono hT le_rfl)

/-- Natural coefficients, as produced by balanced convex combinations,
are a special case of the integer coefficients in the paper. -/
theorem RelativeExpansionAt.of_nat_coefficients {r t K T p : ℕ} [NeZero p] {δ : ℝ}
    (h : RelativeExpansionAt r t K δ T p)
    (S : Finset (IntCoord r)) (w : FpCoord p (r + t) → ℕ) (α : S → ℕ)
    (hbox : ∀ q ∈ S, latticeSupNorm q ≤ K)
    (hs : ∀ v, w v ≠ 0 → ∃ q ∈ S, Coord.first r t v = q.mod p)
    (hz : (∑ q : S, α q • (q : IntCoord r)) = 0)
    (hm : (∑ q : S, α q) = p)
    (ha : ∀ q : S, δ * p ≤ (α q : ℝ) ∧
      (α q : ℝ) ≤ (pushWeight (Coord.first r t) w ((q : IntCoord r).mod p) : ℝ) - δ * p)
    (hthick : IsThickRelative w (Coord.first r t) T δ) :
    HasZeroSumMultiplicity w := by
  apply h S w (fun q ↦ (α q : ℤ)) hbox hs
  · simpa only [natCast_zsmul] using hz
  · exact_mod_cast hm
  · simpa only [Int.cast_natCast] using ha
  · exact hthick

end Expansion
end EGZ
