/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Convex.AffineLattice
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.CenteredLift

/-!
# Balanced integer convex combinations

This file states the balanced-combination lemma (`lm2`) as an explicit
proposition. Its proof is `balanced_combination_lemma` in
`EGZ.Balanced.Existence`. The support is
written in integer affine-lattice coordinates, so the generated affine
lattice and the rationality used in the paper have an unambiguous meaning.
Relative interior includes lower-dimensional supports and the singleton
case. The constants are chosen before the centrality parameter, as required
by the paper's uniformity in the main proof.
-/

open scoped BigOperators

namespace EGZ

namespace BalancedCombination

/-- Centrality for a finite weight on integer coordinate points. Testing
closed halfspaces through the center suffices for all containing halfspaces. -/
def IsCentral {d : ℕ} (S : Finset (IntCoord d)) (w : S → ℝ)
    (θ : ℝ) (c : RealCoord d) : Prop := by
  classical
  exact ∀ ξ : RealCoord d →ᵃ[ℝ] ℝ,
    θ * (∑ q : S, w q) ≤ ∑ q : S, if ξ c ≤ ξ q.val.real then w q else 0

/-- A finite positive weight and an interior point of its generated affine
integer lattice. All coordinates are taken in a chosen ambient lattice. -/
structure Data (d : ℕ) where
  /-- Finite set of lattice points to be combined. -/
  support : Finset (IntCoord d)
  support_nonempty : support.Nonempty
  /-- Positive real weight assigned to each support point. -/
  weight : support → ℝ
  weight_pos : ∀ q, 0 < weight q
  /-- Integral center of the balanced combination. -/
  center : IntCoord d
  center_mem_span : center ∈ affineSpan ℤ (↑support : Set (IntCoord d))
  center_mem_interior : center.real ∈ intrinsicInterior ℝ
    (convexHull ℝ (IntCoord.real '' (↑support : Set (IntCoord d))))

/-- The integer coefficients and all bounds supplied by the lemma. -/
structure Coefficients {d : ℕ} (D : Data d) (ε θ μ : ℝ) (n : ℕ) where
  /-- Multiplicity of each support point in the integer combination. -/
  coeff : D.support → ℕ
  sum_eq : ∑ q, coeff q = n
  weighted_sum_eq : ∑ q, coeff q • q.val = n • D.center
  lower : ∀ q, μ * n ≤ (coeff q : ℝ)
  upper : ∀ q, (coeff q : ℝ) ≤
    (1 + ε) * n * D.weight q / (θ * ∑ r, D.weight r)

namespace Data

theorem totalWeight_pos {d : ℕ} (D : Data d) : 0 < ∑ q, D.weight q := by
  classical
  obtain ⟨q, hq⟩ := D.support_nonempty
  exact Finset.sum_pos' (fun q _ ↦ (D.weight_pos q).le)
    ⟨⟨q, hq⟩, Finset.mem_univ _, D.weight_pos _⟩

theorem centrality_le_one {d : ℕ} (D : Data d) {θ : ℝ}
    (h : IsCentral D.support D.weight θ D.center.real) : θ ≤ 1 := by
  have hzero := h (AffineMap.const ℝ (RealCoord d) (0 : ℝ))
  simp only [AffineMap.const_apply, le_refl, ite_true] at hzero
  nlinarith [D.totalWeight_pos]

end Data

namespace Coefficients

/-- The lower fraction can be decreased without changing any coefficient. -/
def monoLower {d : ℕ} {D : Data d} {ε θ μ μ' : ℝ} {n : ℕ}
    (A : Coefficients D ε θ μ n) (hμ : μ' ≤ μ) : Coefficients D ε θ μ' n where
  coeff := A.coeff
  sum_eq := A.sum_eq
  weighted_sum_eq := A.weighted_sum_eq
  lower q := (mul_le_mul_of_nonneg_right hμ (Nat.cast_nonneg n)).trans (A.lower q)
  upper := A.upper

/-- Balance at length `p` becomes zero sum after reducing lattice coordinates
modulo `p`. The center need not be zero. -/
theorem mod_sum_eq_zero {d p : ℕ} {D : Data d} {ε θ μ : ℝ}
    (A : Coefficients D ε θ μ p) :
    ∑ q, (A.coeff q : ZMod p) • q.val.mod p = 0 := by
  classical
  ext i
  have h := congrArg (fun z : IntCoord d ↦ (z i : ZMod p)) A.weighted_sum_eq
  simpa [Finset.sum_apply, Pi.smul_apply, IntCoord.mod, nsmul_eq_mul,
    Nat.cast_smul_eq_nsmul] using h

/-- The slack used by relative expansion follows from a positive lower
fraction, a proportional upper bound, and a positive lower bound on each
available fibre size. -/
theorem expansion_slack {d n : ℕ} {D : Data d} {ε θ μ : ℝ}
    (A : Coefficients D ε θ μ n) (size : D.support → ℕ)
    {η γ δ : ℝ} (hη : 0 ≤ η) (hδμ : δ ≤ μ) (hδηγ : δ ≤ η * γ)
    (hsize : ∀ q, γ * n ≤ (size q : ℝ))
    (hupper : ∀ q, (A.coeff q : ℝ) ≤ (1 - η) * size q) :
    ∀ q, δ * n ≤ (A.coeff q : ℝ) ∧
      (A.coeff q : ℝ) ≤ (size q : ℝ) - δ * n := by
  intro q
  refine ⟨(mul_le_mul_of_nonneg_right hδμ (Nat.cast_nonneg n)).trans (A.lower q), ?_⟩
  have hsmall := (mul_le_mul_of_nonneg_right hδηγ (Nat.cast_nonneg n)).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hsize q) hη)
  nlinarith [hupper q]

end Coefficients

/-- A finite encoding of all integer-weighted configurations in a fixed
box: a support, weights at most `W`, and a center in the same box. -/
abbrev BoundedConfiguration (d K W : ℕ) :=
  Σ S : {s : Finset (IntCoord d) // s ∈ (latticeBox d K).powerset},
    (S.val → Fin (W + 1)) × {c : IntCoord d // c ∈ latticeBox d K}

namespace BoundedConfiguration

variable {d K W : ℕ}

/-- Underlying finite lattice support of the bounded configuration. -/
def support (Q : BoundedConfiguration d K W) : Finset (IntCoord d) := Q.1.val

/-- Real weights obtained from the bounded integer weights. -/
def weight (Q : BoundedConfiguration d K W) : Q.support → ℝ :=
  fun q ↦ (Q.2.1 q).val

/-- Integral center encoded by the bounded configuration. -/
def center (Q : BoundedConfiguration d K W) : IntCoord d := Q.2.2.val

/-- Geometric validity and positivity are checked before applying the
balanced-combination statement. Centrality is deliberately absent. -/
def Valid (Q : BoundedConfiguration d K W) : Prop :=
  Q.support.Nonempty ∧ (∀ q, 0 < Q.weight q) ∧
    Q.center ∈ affineSpan ℤ (↑Q.support : Set (IntCoord d)) ∧
      Q.center.real ∈ intrinsicInterior ℝ
        (convexHull ℝ (IntCoord.real '' (↑Q.support : Set (IntCoord d))))

/-- Construct balanced-combination data from a valid bounded configuration. -/
def data (Q : BoundedConfiguration d K W) (h : Q.Valid) : Data d where
  support := Q.support
  support_nonempty := h.1
  weight := Q.weight
  weight_pos := h.2.1
  center := Q.center
  center_mem_span := h.2.2.1
  center_mem_interior := h.2.2.2

/-- Encode any support and positive bounded integer weights. -/
def ofWeights (S : Finset (IntCoord d)) (hS : S ⊆ latticeBox d K)
    (w : S → ℕ) (hw : ∀ q, w q ≤ W)
    (c : IntCoord d) (hc : c ∈ latticeBox d K) : BoundedConfiguration d K W :=
  ⟨⟨S, Finset.mem_powerset.mpr hS⟩, (fun q ↦ ⟨w q, Nat.lt_succ_of_le (hw q)⟩), ⟨c, hc⟩⟩

end BoundedConfiguration

end BalancedCombination

/-- The finite balanced convex-combination lemma in integer lattice
coordinates. This is a proposition interface, not an axiom or a proved
theorem. In particular, both `μ` and `N` are independent of `θ` and `n`. -/
def BalancedCombinationLemma : Prop :=
  ∀ (d : ℕ) (D : BalancedCombination.Data d) (ε : ℝ), 0 < ε →
    ∃ (μ : ℝ) (N : ℕ), 0 < μ ∧
      ∀ (θ : ℝ), 0 < θ →
        BalancedCombination.IsCentral D.support D.weight θ D.center.real →
          ∀ n : ℕ, N < n → Nonempty (BalancedCombination.Coefficients D ε θ μ n)

namespace BalancedCombinationLemma

/-- A finite family admits common constants. Their dependence on centrality
and on the eventual integer length remains absent. -/
theorem uniform_finite_family (h : BalancedCombinationLemma)
    {I : Type*} [Finite I] (d : I → ℕ) (D : ∀ i, BalancedCombination.Data (d i))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (μ : ℝ) (N : ℕ), 0 < μ ∧
      ∀ i (θ : ℝ), 0 < θ →
        BalancedCombination.IsCentral (D i).support (D i).weight θ (D i).center.real →
          ∀ n : ℕ, N < n → Nonempty (BalancedCombination.Coefficients (D i) ε θ μ n) := by
  let := Fintype.ofFinite I
  classical
  cases isEmpty_or_nonempty I with
  | inl hI =>
    let := hI
    exact ⟨1, 0, by norm_num, fun i ↦ isEmptyElim i⟩
  | inr hI =>
    let := hI
    choose μ N hμ hcoeff using fun i ↦ h (d i) (D i) ε hε
    let μ₀ := Finset.univ.inf' Finset.univ_nonempty μ
    let N₀ := Finset.univ.sup N
    refine ⟨μ₀, N₀, ?_, ?_⟩
    · exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun i _ ↦ hμ i)
    · intro i θ hθ hc n hn
      have hNi : N i ≤ N₀ := Finset.le_sup (Finset.mem_univ i)
      obtain ⟨A⟩ := hcoeff i θ hθ hc n (hNi.trans_lt hn)
      exact ⟨A.monoLower (Finset.inf'_le _ (Finset.mem_univ i))⟩

/-- Bounded supports, bounded positive integer weights, and bounded lattice
centers have common constants. No centrality parameter or length enters the
choice of those constants. -/
theorem uniform_bounded_configurations (h : BalancedCombinationLemma)
    (d K W : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (μ : ℝ) (N : ℕ), 0 < μ ∧
      ∀ (Q : BalancedCombination.BoundedConfiguration d K W) (hQ : Q.Valid)
        (θ : ℝ), 0 < θ →
          BalancedCombination.IsCentral Q.support Q.weight θ Q.center.real →
            ∀ n : ℕ, N < n →
              Nonempty (BalancedCombination.Coefficients (Q.data hQ) ε θ μ n) := by
  classical
  let I := {Q : BalancedCombination.BoundedConfiguration d K W // Q.Valid}
  let : Fintype I := Fintype.ofFinite I
  obtain ⟨μ, N, hμ, hcoeff⟩ := h.uniform_finite_family (I := I)
    (fun _ ↦ d) (fun Q ↦ Q.val.data Q.property) ε hε
  exact ⟨μ, N, hμ, fun Q hQ ↦ hcoeff ⟨Q, hQ⟩⟩

/-- The same constants can be chosen for every coordinate rank at most
the fixed ambient dimension. -/
theorem uniform_bounded_dimensions (h : BalancedCombinationLemma)
    (d K W : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (μ : ℝ) (N : ℕ), 0 < μ ∧
      ∀ (r : ℕ), r ≤ d →
        ∀ (Q : BalancedCombination.BoundedConfiguration r K W) (hQ : Q.Valid)
          (θ : ℝ), 0 < θ →
            BalancedCombination.IsCentral Q.support Q.weight θ Q.center.real →
              ∀ n : ℕ, N < n →
                Nonempty (BalancedCombination.Coefficients (Q.data hQ) ε θ μ n) := by
  classical
  let I := Σ r : Fin (d + 1),
    {Q : BalancedCombination.BoundedConfiguration r.val K W // Q.Valid}
  let : Fintype I := Fintype.ofFinite I
  obtain ⟨μ, N, hμ, hcoeff⟩ := h.uniform_finite_family (I := I)
    (fun Q ↦ Q.1.val) (fun Q ↦ Q.2.val.data Q.2.property) ε hε
  exact ⟨μ, N, hμ, fun r hr Q hQ ↦ hcoeff ⟨⟨r, Nat.lt_succ_of_le hr⟩, ⟨Q, hQ⟩⟩⟩

end BalancedCombinationLemma
end EGZ
