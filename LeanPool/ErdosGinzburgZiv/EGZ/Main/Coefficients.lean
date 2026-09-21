/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.BalancedRounding
import LeanPool.ErdosGinzburgZiv.EGZ.Main.Input
import LeanPool.ErdosGinzburgZiv.EGZ.Main.Selection
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Cleanup

/-!
# Uniform balanced coefficients at the selected flag node

The fraction and length threshold are functions of the coordinate radius
chosen before the driving function, decomposition, prime, or selected node.
The normalized input and gap estimates place the selected cumulative weight
within their scope. The centrality identity then gives the reserve required
by relative expansion.
-/

open scoped BigOperators

namespace EGZ.MainProof

/-- The bounded-rounding conclusion for one prescribed coordinate radius. -/
def RoundingBound (d K : ℕ) (C γ η μ : ℝ) (N : ℕ) : Prop :=
  ∀ (r : ℕ), r ≤ d →
    ∀ (S : Finset (IntCoord r)), S ⊆ latticeBox r K → S.Nonempty →
      ∀ (c : IntCoord r), c ∈ latticeBox r K →
        c ∈ affineSpan ℤ (↑S : Set (IntCoord r)) →
        c.real ∈ intrinsicInterior ℝ
          (convexHull ℝ (IntCoord.real '' (↑S : Set (IntCoord r)))) →
        ∀ (m : S → ℕ) (p : ℕ), N < p →
          (∀ q, γ * p ≤ (m q : ℝ)) → (∑ q, (m q : ℝ)) ≤ C * p →
          ∀ (θ : ℝ), 0 < θ →
            BalancedCombination.IsCentral S (fun q ↦ (m q : ℝ)) θ c.real →
            ∃ a : S → ℕ,
              (∑ q, a q) = p ∧ (∑ q, a q • q.val) = p • c ∧
              (∀ q, μ * p ≤ (a q : ℝ)) ∧
              (∀ q, (a q : ℝ) ≤ (1 + η) / (1 - η) ^ 2 *
                p * (m q : ℝ) / (θ * ∑ s, (m s : ℝ)))

/-- The radius-dependent parameters used before choosing the flag lemma's
driving function. Radius zero receives harmless positive default data. -/
structure CoefficientParameters (d : ℕ) (δ ζ : ℝ) where
  /-- The positive retained fraction used in the rounding bound at each radius. -/
  fraction : ℕ → ℝ
  /-- The size threshold required for the rounding bound at each radius. -/
  threshold : ℕ → ℕ
  fraction_pos : ∀ K, 0 < fraction K
  bound : ∀ K, 1 ≤ K → RoundingBound d K ((hollowBound d : ℝ) + 2)
    (gapScale d δ K) (errorScale (hollowBound d) ζ) (fraction K) (threshold K)

theorem exists_coefficientParameters (hBalanced : BalancedCombinationLemma)
    (d : ℕ) {δ ζ : ℝ} (hδ : 0 < δ) (hζ : 0 < ζ) (hζone : ζ ≤ 1) :
    Nonempty (CoefficientParameters d δ ζ) := by
  classical
  have he : 0 < errorScale (hollowBound d) ζ := errorScale_pos (Nat.cast_nonneg _) hζ
  have heone : errorScale (hollowBound d) ζ < 1 :=
    (errorScale_le (Nat.cast_nonneg _) hζone).trans_lt (by norm_num)
  have hall (K : ℕ) : ∃ (μ : ℝ) (N : ℕ), 0 < μ ∧
      (1 ≤ K → RoundingBound d K ((hollowBound d : ℝ) + 2)
        (gapScale d δ K) (errorScale (hollowBound d) ζ) μ N) := by
    by_cases hK : 1 ≤ K
    · obtain ⟨μ, N, hμ, hbound⟩ := BalancedCombination.uniform_rounded_coefficients
        hBalanced d K ((hollowBound d : ℝ) + 2) (gapScale d δ K)
        (errorScale (hollowBound d) ζ) (gapScale_pos hδ hK) he heone
      exact ⟨μ, N, hμ, fun _ ↦ hbound⟩
    · exact ⟨1, 0, by norm_num, fun h ↦ (hK h).elim⟩
  choose μ N hμ hbound using hall
  exact ⟨⟨μ, N, hμ, hbound⟩⟩

/-- Choose radius-dependent rounding parameters from the balanced combination lemma. -/
noncomputable def coefficientParameters (hBalanced : BalancedCombinationLemma)
    (d : ℕ) {δ ζ : ℝ} (hδ : 0 < δ) (hζ : 0 < ζ) (hζone : ζ ≤ 1) :
    CoefficientParameters d δ ζ :=
  Classical.choice (exists_coefficientParameters hBalanced d hδ hζ hζone)

namespace CoefficientParameters

variable {d : ℕ} {δ ζ : ℝ} (P : CoefficientParameters d δ ζ)

/-- A common scale for thickness and the reserve on both sides of each
coefficient. It is fixed as a function of the old radius before the flag
decomposition's driving function is chosen. -/
noncomputable def expansionScale (K : ℕ) : ℝ :=
  min (P.fraction K) (min δ (errorScale (hollowBound d) ζ * gapScale d δ K))

theorem expansionScale_pos {K : ℕ} (hδ : 0 < δ) (hζ : 0 < ζ) (hK : 1 ≤ K) :
    0 < P.expansionScale K := by
  exact lt_min (P.fraction_pos K) (lt_min hδ
    (mul_pos (errorScale_pos (Nat.cast_nonneg _) hζ) (gapScale_pos hδ hK)))

theorem expansionScale_le_delta (K : ℕ) : P.expansionScale K ≤ δ :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem expansionScale_le_fraction (K : ℕ) : P.expansionScale K ≤ P.fraction K :=
  min_le_left _ _

/-- The proportional reserve gives the two additive margins in the relative
expansion theorem. -/
theorem expansion_slack {I : Type*} (K p : ℕ) (m a : I → ℕ) (hζ : 0 < ζ)
    (hmlower : ∀ q, gapScale d δ K * p ≤ (m q : ℝ))
    (hlower : ∀ q, P.fraction K * p ≤ (a q : ℝ))
    (hupper : ∀ q, (a q : ℝ) ≤ (1 - errorScale (hollowBound d) ζ) * m q) :
    ∀ q, P.expansionScale K * p ≤ (a q : ℝ) ∧
      (a q : ℝ) ≤ (m q : ℝ) - P.expansionScale K * p := by
  intro q
  refine ⟨(mul_le_mul_of_nonneg_right (P.expansionScale_le_fraction K)
    (Nat.cast_nonneg p)).trans (hlower q), ?_⟩
  have hsmall : P.expansionScale K ≤ errorScale (hollowBound d) ζ * gapScale d δ K :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hscale := mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg p)
  have hweight := mul_le_mul_of_nonneg_left (hmlower q)
    (errorScale_pos (Nat.cast_nonneg (hollowBound d)) hζ).le
  nlinarith [hupper q]

/-- Apply the parameters to any selected cumulative node. The selection
already records that this node is complete at `T(node), δ`. -/
theorem coefficients_of_selection {p : ℕ} [NeZero p] [Fact p.Prime]
    {f : FpCoord p d → ℕ} (Φ : FlagDecomposition p d f)
    {T K : Φ.flag.Node → ℕ} (D : Φ.CumulativeSelection T K δ)
    (hodd : Odd p) (hδ : 0 < δ) (hζ : 0 < ζ) (hζone : ζ ≤ 1)
    (hW : (hollowConstant p d : ℝ) ≤ hollowBound d)
    (hK : 1 ≤ K D.node) (hp : P.threshold (K D.node) < p)
    (hinput_lower : p ≤ natMass f)
    (hinput_upper : (natMass f : ℝ) ≤ ((hollowBound d : ℝ) + 2) * p)
    (hretained : (1 - errorScale (hollowBound d) ζ) *
      ((hollowConstant p d : ℝ) + ζ) * p ≤ (Φ.retainedMass : ℝ))
    (hgap : ∀ x, gapScale d δ (K x) * (natMass f : ℝ) ≤ (Φ.gap x : ℝ)) :
    ∃ a : Φ.liftedSupport D.node → ℕ,
      (∑ q, a q) = p ∧ (∑ q, a q • q.val) = p • D.center ∧
      (∀ q, P.fraction (K D.node) * p ≤ (a q : ℝ)) ∧
      (∀ q, (a q : ℝ) ≤
        (1 - errorScale (hollowBound d) ζ) * Φ.hat D.node q) := by
  classical
  have hγ : 0 < gapScale d δ (K D.node) := gapScale_pos hδ hK
  have hmlower (q : Φ.liftedSupport D.node) :
      gapScale d δ (K D.node) * p ≤ (Φ.hat D.node q : ℝ) := by
    apply (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hinput_lower) hγ.le).trans
    exact (hgap D.node).trans (Nat.cast_le.mpr
      (Φ.gap_le_hat D.node q ((Φ.liftedSupport_spec D.node q).mp q.property)))
  have hmass : (∑ q : Φ.liftedSupport D.node, (Φ.hat D.node q : ℝ)) ≤
      ((hollowBound d : ℝ) + 2) * p := by
    apply (D.mass_le_retained hodd).trans
    exact (Nat.cast_le.mpr (natMass_mono Φ.retained_le)).trans hinput_upper
  obtain ⟨a, hsum, hweighted, hlower, hupper⟩ :=
    P.bound (K D.node) hK (Φ.flag.rank D.node) (Φ.representation.rank_le D.node)
      (Φ.liftedSupport D.node) D.support_subset_box (Φ.liftedSupport_nonempty D.node)
      D.center D.center_mem_box D.center_mem_span D.center_mem_interior
      (fun q ↦ Φ.hat D.node q) p hp hmlower hmass
      (Φ.cumulativeCentrality D.node) D.centrality_pos D.central
  refine ⟨a, hsum, hweighted, hlower, ?_⟩
  intro q
  apply coefficient_le_reserve (Nat.cast_nonneg (hollowBound d)) hζ hζone
    (Nat.cast_nonneg (hollowConstant p d)) hW (Nat.cast_nonneg p)
    (Nat.cast_nonneg (Φ.hat D.node q)) (by exact_mod_cast Φ.retainedMass_pos hodd) hretained
  have hq := hupper q
  rw [D.centrality_mul_mass hodd] at hq
  apply hq.trans_eq
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- A threshold imposed on every allowed node radius permits selecting the
node only after the flag decomposition has been constructed. -/
theorem exists_selected_coefficients {p : ℕ} [NeZero p] [Fact p.Prime]
    {f : FpCoord p d → ℕ} (Φ : FlagDecomposition p d f)
    {T K : Φ.flag.Node → ℕ} (hodd : Odd p)
    (hδ : 0 < δ) (hζ : 0 < ζ) (hζone : ζ ≤ 1)
    (hW : (hollowConstant p d : ℝ) ≤ hollowBound d)
    (hK : ∀ x, 1 ≤ K x) (hp : ∀ x, P.threshold (K x) < p)
    (hcomplete : Φ.IsComplete T (errorScale (hollowBound d) ζ) δ)
    (hbounded : Φ.IsKBounded K)
    (hinput_lower : p ≤ natMass f)
    (hinput_upper : (natMass f : ℝ) ≤ ((hollowBound d : ℝ) + 2) * p)
    (hretained : (1 - errorScale (hollowBound d) ζ) *
      ((hollowConstant p d : ℝ) + ζ) * p ≤ (Φ.retainedMass : ℝ))
    (hgap : ∀ x, gapScale d δ (K x) * (natMass f : ℝ) ≤ (Φ.gap x : ℝ)) :
    ∃ D : Φ.CumulativeSelection T K δ,
      ∃ a : Φ.liftedSupport D.node → ℕ,
        (∑ q, a q) = p ∧ (∑ q, a q • q.val) = p • D.center ∧
        (∀ q, P.fraction (K D.node) * p ≤ (a q : ℝ)) ∧
        (∀ q, (a q : ℝ) ≤
          (1 - errorScale (hollowBound d) ζ) * Φ.hat D.node q) := by
  have hprime : p.Prime := Fact.out
  have hWpos : (0 : ℝ) < hollowConstant p d := by
    exact_mod_cast (Nat.zero_lt_one.trans_le (one_le_hollowConstant hprime))
  have he := errorScale_pos (Nat.cast_nonneg (hollowBound d)) hζ
  have heW := errorScale_le_inv (Nat.cast_nonneg (hollowBound d)) hζ hζone hWpos hW
  obtain ⟨D⟩ := Φ.select_cumulative_node hprime hodd he.le heW hcomplete hbounded
  exact ⟨D, P.coefficients_of_selection Φ D hodd hδ hζ hζone hW (hK D.node)
    (hp D.node) hinput_lower hinput_upper hretained hgap⟩

end CoefficientParameters
end EGZ.MainProof
