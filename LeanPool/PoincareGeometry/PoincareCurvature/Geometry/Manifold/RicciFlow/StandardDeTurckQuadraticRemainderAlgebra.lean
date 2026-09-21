/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Algebra of the quadratic Ricci--DeTurck remainder

This file isolates the pointwise finite-dimensional contraction calculation
that remains after the second-derivative terms in the Ricci--DeTurck
comparison have cancelled.  It uses only a real inner-product space, a finite
orthonormal frame, and a symmetric bilinear correction.
-/

@[expose] public noncomputable section
namespace RicciFlow

variable {ι V : Type*} [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- The raw lower-order contraction in the Ricci--DeTurck comparison reduces
to the displayed quadratic expression.  The left hand side deliberately
retains every term produced by the Ricci connection-change and differentiated
DeTurck-trace expansions. -/
theorem standardDeTurck_quadraticRemainder_raw_eq
    (b : OrthonormalBasis ι ℝ V)
    (A : V →L[ℝ] V →L[ℝ] V)
    (D : V → V → V → ℝ)
    (hA : ∀ a b : V, A a b = A b a)
    (hD : ∀ p q r : V, D p q r = ⟪A p r, q⟫ + ⟪p, A q r⟫)
    (u v : V) :
    (∑ i : ι,
        (2 * D (A v u) (b i) (b i) - 2 * D (A v (b i)) (b i) u -
          2 * (⟪A (A v u) (b i), b i⟫ - ⟪A (A v (b i)) u, b i⟫) -
          D (A (b i) (b i)) v u - D (A (b i) (b i)) u v +
          ⟪A (A (b i) (b i)) u, v⟫ + ⟪u, A (A (b i) (b i)) v⟫)) -
      ∑ i : ι, ∑ r : ι,
        D (b i) (b r) u * ⟪A (b r) (b i), v⟫ -
      ∑ i : ι, ∑ r : ι,
        D (b i) (b r) v * ⟪A (b r) (b i), u⟫ =
      -2 * ∑ i : ι, ⟪A v (b i), A (b i) u⟫ -
        2 * ∑ i : ι, ∑ r : ι,
          ⟪A (b i) u, b r⟫ * ⟪A (b r) (b i), v⟫ -
        2 * ∑ i : ι, ∑ r : ι,
          ⟪A (b i) v, b r⟫ * ⟪A (b r) (b i), u⟫ := by
  have hsingle : ∀ i : ι,
      2 * D (A v u) (b i) (b i) - 2 * D (A v (b i)) (b i) u -
          2 * (⟪A (A v u) (b i), b i⟫ - ⟪A (A v (b i)) u, b i⟫) -
          D (A (b i) (b i)) v u - D (A (b i) (b i)) u v +
          ⟪A (A (b i) (b i)) u, v⟫ + ⟪u, A (A (b i) (b i)) v⟫ =
        -2 * ⟪A v (b i), A (b i) u⟫ := by
    intro i
    rw [hD, hD, hD, hD]
    rw [hA u v]
    rw [real_inner_comm (A v u) (A (b i) (b i))]
    rw [real_inner_comm u (A (A (b i) (b i)) v)]
    ring
  have hsingle_sum :
      ∑ i : ι,
        (2 * D (A v u) (b i) (b i) - 2 * D (A v (b i)) (b i) u -
          2 * (⟪A (A v u) (b i), b i⟫ - ⟪A (A v (b i)) u, b i⟫) -
          D (A (b i) (b i)) v u - D (A (b i) (b i)) u v +
          ⟪A (A (b i) (b i)) u, v⟫ + ⟪u, A (A (b i) (b i)) v⟫) =
        -2 * ∑ i : ι, ⟪A v (b i), A (b i) u⟫ := by
    calc
      ∑ i : ι,
          (2 * D (A v u) (b i) (b i) - 2 * D (A v (b i)) (b i) u -
            2 * (⟪A (A v u) (b i), b i⟫ - ⟪A (A v (b i)) u, b i⟫) -
            D (A (b i) (b i)) v u - D (A (b i) (b i)) u v +
            ⟪A (A (b i) (b i)) u, v⟫ + ⟪u, A (A (b i) (b i)) v⟫) =
          ∑ i : ι, -2 * ⟪A v (b i), A (b i) u⟫ := by
            apply Finset.sum_congr rfl
            intro i _
            exact hsingle i
      _ = -2 * ∑ i : ι, ⟪A v (b i), A (b i) u⟫ := by
            rw [Finset.mul_sum]
  have hswap (w z : V) :
      (∑ i : ι, ∑ r : ι,
        ⟪b i, A (b r) w⟫ * ⟪A (b r) (b i), z⟫) =
        ∑ i : ι, ∑ r : ι,
          ⟪A (b i) w, b r⟫ * ⟪A (b r) (b i), z⟫ := by
    calc
      (∑ i : ι, ∑ r : ι,
          ⟪b i, A (b r) w⟫ * ⟪A (b r) (b i), z⟫) =
        ∑ r : ι, ∑ i : ι,
          ⟪b i, A (b r) w⟫ * ⟪A (b r) (b i), z⟫ := by
            rw [Finset.sum_comm]
      _ = ∑ r : ι, ∑ i : ι,
          ⟪A (b r) w, b i⟫ * ⟪A (b i) (b r), z⟫ := by
            apply Finset.sum_congr rfl
            intro r _
            apply Finset.sum_congr rfl
            intro i _
            rw [real_inner_comm (b i) (A (b r) w), hA (b r) (b i)]
      _ = ∑ i : ι, ∑ r : ι,
          ⟪A (b i) w, b r⟫ * ⟪A (b r) (b i), z⟫ := by rfl
  have hdouble (w z : V) :
      ∑ i : ι, ∑ r : ι,
        D (b i) (b r) w * ⟪A (b r) (b i), z⟫ =
        2 * ∑ i : ι, ∑ r : ι,
          ⟪A (b i) w, b r⟫ * ⟪A (b r) (b i), z⟫ := by
    calc
      ∑ i : ι, ∑ r : ι,
          D (b i) (b r) w * ⟪A (b r) (b i), z⟫ =
        ∑ i : ι, ∑ r : ι,
          (⟪A (b i) w, b r⟫ * ⟪A (b r) (b i), z⟫ +
            ⟪b i, A (b r) w⟫ * ⟪A (b r) (b i), z⟫) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro r _
            rw [hD]
            ring
      _ = (∑ i : ι, ∑ r : ι,
            ⟪A (b i) w, b r⟫ * ⟪A (b r) (b i), z⟫) +
          ∑ i : ι, ∑ r : ι,
            ⟪b i, A (b r) w⟫ * ⟪A (b r) (b i), z⟫ := by
            simp only [Finset.sum_add_distrib]
      _ = 2 * ∑ i : ι, ∑ r : ι,
          ⟪A (b i) w, b r⟫ * ⟪A (b r) (b i), z⟫ := by
            rw [hswap w z]
            ring
  rw [hsingle_sum, hdouble u v, hdouble v u]

end RicciFlow
