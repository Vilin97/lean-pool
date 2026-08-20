/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132ConvexK3.Lens
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Forced penultimate coordinates

Algebraic kernel for draft Section 5 and Lean-plan step 9.  The two circle
systems force the penultimate points to be mirror images; no symmetry is
assumed.  The previously implicit P5-4 height constraint is named and used
explicitly in every distance-subtraction identity.
-/

namespace LeanPool.Erdos132ConvexK3

/-- The two penultimate circle systems force `W+R=2c`, equal positive
ordinates, and the horizontal class difference. -/
theorem forced_penultimate_mirror
    {c A B W R K_w K_r : ℝ} (hc : 0 < c)
    (hwA : W ^ 2 + K_w ^ 2 = A)
    (hwB : (W - 2 * c) ^ 2 + K_w ^ 2 = B)
    (hrB : R ^ 2 + K_r ^ 2 = B)
    (hrA : (R - 2 * c) ^ 2 + K_r ^ 2 = A)
    (hKw : 0 < K_w) (hKr : 0 < K_r) :
    W + R = 2 * c ∧ K_w = K_r ∧ A - B = 4 * c * (W - c) := by
  have hW : A - B = 4 * c * (W - c) := by
    nlinarith
  have hR : A - B = 4 * c * (c - R) := by
    nlinarith
  have hmul : 4 * c * (W + R - 2 * c) = 0 := by
    nlinarith
  have hc4 : 4 * c ≠ 0 := by positivity
  have hsum : W + R = 2 * c := by
    have hz : W + R - 2 * c = 0 := (mul_eq_zero.mp hmul).resolve_left hc4
    linarith
  have hsq : K_w ^ 2 = K_r ^ 2 := by
    nlinarith
  have hK : K_w = K_r := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with heq | heq
    · exact heq
    · nlinarith
  exact ⟨hsum, hK, hW⟩

/-- Canonical mirror-coordinate form with `d>0` when `A>B`. -/
theorem forced_penultimate_coordinates
    {c A B W R K_w K_r : ℝ} (hc : 0 < c) (hBA : B < A)
    (hwA : W ^ 2 + K_w ^ 2 = A)
    (hwB : (W - 2 * c) ^ 2 + K_w ^ 2 = B)
    (hrB : R ^ 2 + K_r ^ 2 = B)
    (hrA : (R - 2 * c) ^ 2 + K_r ^ 2 = A)
    (hKw : 0 < K_w) (hKr : 0 < K_r) :
    ∃ d K : ℝ, 0 < d ∧ W = c + d ∧ R = c - d ∧
      K_w = K ∧ K_r = K ∧ A - B = 4 * c * d := by
  obtain ⟨hsum, hK, hclass⟩ :=
    forced_penultimate_mirror hc hwA hwB hrB hrA hKw hKr
  let d := W - c
  have hd : 0 < d := by
    by_contra hnot
    have hdle : d ≤ 0 := le_of_not_gt hnot
    have hprod : 4 * c * d ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hdle
    dsimp [d] at hprod
    linarith
  refine ⟨d, K_w, hd, ?_, ?_, rfl, hK.symm, ?_⟩
  · simp [d]
  · dsimp [d]
    linarith
  · simpa [d] using hclass

/-- **P5-4, displayed.** Equality of the two diameter radii forces
`2cd+d² = Δ(H+K)` when `Δ=H-K`. -/
theorem forced_penultimate_height_constraint
    {c d H K Δ : ℝ}
    (hradius : (c + d) ^ 2 + K ^ 2 = c ^ 2 + H ^ 2)
    (hΔ : Δ = H - K) :
    2 * c * d + d ^ 2 = Δ * (H + K) := by
  rw [hΔ]
  nlinarith

/-- The exact P5-4 constraint in the draft parameterization `K=H-Δ`. -/
theorem forced_penultimate_height_constraint_reparam
    {c d H Δ : ℝ}
    (hradius : (c + d) ^ 2 + (H - Δ) ^ 2 = c ^ 2 + H ^ 2) :
    2 * c * d + d ^ 2 = Δ * (H + (H - Δ)) := by
  nlinarith

/-- Left penultimate subtraction identity, with P5-4 explicit. -/
theorem left_penultimate_distance_difference
    {c d H Δ X Y : ℝ}
    (hconstraint : 2 * c * d + d ^ 2 = Δ * (H + (H - Δ))) :
    sqDist (X, Y) (c + d, H - Δ) - sqDist (X, Y) (c, H) =
      -2 * d * X + 2 * Δ * Y := by
  simp only [sqDist]
  nlinarith

/-- Right penultimate subtraction identity, with P5-4 explicit. -/
theorem right_penultimate_distance_difference
    {c d H Δ X Y : ℝ}
    (hconstraint : 2 * c * d + d ^ 2 = Δ * (H + (H - Δ))) :
    sqDist (X, Y) (c - d, H - Δ) - sqDist (X, Y) (c, H) =
      -2 * d * (2 * c - X) + 2 * Δ * Y := by
  simp only [sqDist]
  nlinarith

/-- Ordinate of the nontrivial reflection of `(2c,0)` across the line
through `(c,H)` and `(c+d,H-Δ)`. -/
noncomputable def penultimateReflectionOrdinate (c d H Δ : ℝ) : ℝ :=
  2 * d * (H * d - c * Δ) / (d ^ 2 + Δ ^ 2)

/-- The convexity sign `Hd>cΔ` puts the reflected intersection strictly
above the lower chord. -/
theorem penultimate_reflection_ordinate_pos
    {c d H Δ : ℝ} (hd : 0 < d) (hconvex : c * Δ < H * d) :
    0 < penultimateReflectionOrdinate c d H Δ := by
  have hden : 0 < d ^ 2 + Δ ^ 2 := by
    nlinarith [sq_pos_of_pos hd, sq_nonneg Δ]
  exact div_pos (mul_pos (mul_pos (by norm_num) hd) (sub_pos.mpr hconvex)) hden

/-- The two circle equations have the known intersection `(2c,0)`; every
other intersection has exactly the reflected ordinate from attempt 9. -/
theorem penultimate_nontrivial_intersection_ordinate
    {c d H Δ X Y : ℝ} (hd : 0 < d)
    (hcircleS :
      sqDist (X, Y) (c, H) = sqDist (2 * c, 0) (c, H))
    (hcircleW :
      sqDist (X, Y) (c + d, H - Δ) =
        sqDist (2 * c, 0) (c + d, H - Δ))
    (hneq : (X, Y) ≠ (2 * c, 0)) :
    Y = penultimateReflectionOrdinate c d H Δ := by
  have hS : X ^ 2 + Y ^ 2 - 2 * c * X - 2 * H * Y = 0 := by
    simp only [sqDist] at hcircleS
    nlinarith
  have hline : d * (X - 2 * c) = Δ * Y := by
    simp only [sqDist] at hcircleW
    nlinarith [hcircleS]
  have hY : Y ≠ 0 := by
    intro hYzero
    have hX : X = 2 * c := by
      rw [hYzero] at hline
      have hd0 : d ≠ 0 := ne_of_gt hd
      exact sub_eq_zero.mp ((mul_eq_zero.mp (by simpa using hline)).resolve_left hd0)
    apply hneq
    simp [hX, hYzero]
  have hlineSq := congrArg (fun z : ℝ => z ^ 2) hline
  have hfactor :
      Y * ((d ^ 2 + Δ ^ 2) * Y - 2 * d * (H * d - c * Δ)) = 0 := by
    linear_combination d ^ 2 * hS - hlineSq - 2 * c * d * hline
  have hlinear :
      (d ^ 2 + Δ ^ 2) * Y = 2 * d * (H * d - c * Δ) := by
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left hY)
  have hden : d ^ 2 + Δ ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_pos hd, sq_nonneg Δ]
  rw [penultimateReflectionOrdinate]
  exact (eq_div_iff hden).2 (by nlinarith)

/-- With the polygon-order sign `Hd>cΔ`, the nontrivial circle intersection
is above the lower chord; the known intersection is `(2c,0)`. -/
theorem penultimate_nontrivial_intersection_above
    {c d H Δ X Y : ℝ} (hd : 0 < d) (hconvex : c * Δ < H * d)
    (hcircleS :
      sqDist (X, Y) (c, H) = sqDist (2 * c, 0) (c, H))
    (hcircleW :
      sqDist (X, Y) (c + d, H - Δ) =
        sqDist (2 * c, 0) (c + d, H - Δ))
    (hneq : (X, Y) ≠ (2 * c, 0)) :
    0 < Y := by
  rw [penultimate_nontrivial_intersection_ordinate hd hcircleS hcircleW hneq]
  exact penultimate_reflection_ordinate_pos hd hconvex

/-- A local top-three bound has exactly the shared-tip split used in the
proof: top class `A`, second class `B`, or at most `C`. -/
theorem top_three_value_split
    {F A B C : ℝ}
    (hbound : F ≤ A ∧ (F < A → F ≤ B) ∧ (F < B → F ≤ C)) :
    F = A ∨ F = B ∨ F ≤ C := by
  rcases lt_or_eq_of_le hbound.1 with hFA | hFA
  · have hFB := hbound.2.1 hFA
    rcases lt_or_eq_of_le hFB with hFB | hFB
    · exact Or.inr (Or.inr (hbound.2.2 hFB))
    · exact Or.inr (Or.inl hFB)
  · exact Or.inl hFA

/-- **P5-2, existential form.** The left-adjacent lower vertex uses the
partition `arc(P,s) + arc(s,x) + {s,x}`; its mirror uses
`arc(Q,s) + arc(s,Q) + {s}`.  The hypotheses expose those two different
partitions instead of quantifying one universal partition over both points. -/
theorem case_three_existential_partition_bound
    {degreeP degreeQ pToS sToX qToS sToQ : ℕ}
    (hPpartition : degreeP ≤ pToS + sToX + 2)
    (hpToS : pToS ≤ 2) (hsToX : sToX ≤ 2)
    (hQpartition : degreeQ ≤ qToS + sToQ + 1)
    (hqToS : qToS ≤ 2) (hsToQ : sToQ ≤ 2) :
    degreeP ≤ 6 ∧ degreeQ ≤ 5 ∧
      ∃ degree, (degree = degreeP ∨ degree = degreeQ) ∧ degree ≤ 6 := by
  refine ⟨by omega, by omega, degreeP, Or.inl rfl, by omega⟩

end LeanPool.Erdos132ConvexK3
