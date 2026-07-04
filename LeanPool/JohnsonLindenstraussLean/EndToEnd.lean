import JL.Rotation
import JL.Lemma

/-!
# The end-to-end Gaussian Johnson–Lindenstrauss theorem

This file assembles the complete Johnson–Lindenstrauss statement for an *arbitrary finite
point set* in a Euclidean space, with the target dimension `k` **explicitly bounded** (not
merely assumed via an abstract counting hypothesis):

> For any `m` points `p : Fin m → EuclideanSpace ℝ (Fin d)` and any
> `0 < ε < 1`, if the projection dimension satisfies
> `4 · log (2 m²) < (ε² − ε³) · k`, then there EXISTS a Gaussian random projection matrix
> `A : Fin k → Fin d → ℝ` such that *every* pairwise squared distance is preserved within a
> relative factor `1 ± ε`.

The proof combines:

* `jlMap_concentration` (`JL.Rotation`): the per-vector concentration bound for the *real*
  Gaussian projection, obtained through Gaussian rotation invariance;
* `card_condition`: the elementary derivation that the dimension bound on `k` discharges the
  union-bound counting condition `m² · C < 1` with `C = 2·exp(-(ε²−ε³)k/4)`;
* `johnson_lindenstrauss` (`JL.Lemma`): the abstract probabilistic-method union bound, which
  is kept as a standalone lemma.
-/

open MeasureTheory ProbabilityTheory Real

namespace JL

/-- **Dimension bound discharges the counting condition.** If
`4·log(2 m²) < (ε²−ε³)·k`, then the union-bound condition `m²·C < 1` holds for the JL
failure probability `C = 2·exp(-(ε²−ε³)k/4)`. -/
theorem card_condition {m k : ℕ} {ε : ℝ}
    (hdim : 4 * Real.log (2 * (m : ℝ) ^ 2) < (ε ^ 2 - ε ^ 3) * (k : ℝ)) :
    (m : ℝ) ^ 2 * (2 * rexp (-(ε ^ 2 - ε ^ 3) * (k : ℝ) / 4)) < 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
    have h2m : 0 < 2 * (m : ℝ) ^ 2 := by positivity
    have hlog : Real.log (2 * (m : ℝ) ^ 2) < (ε ^ 2 - ε ^ 3) * (k : ℝ) / 4 := by linarith
    have hrw : (m : ℝ) ^ 2 * (2 * rexp (-(ε ^ 2 - ε ^ 3) * (k : ℝ) / 4))
        = rexp (Real.log (2 * (m : ℝ) ^ 2) + -(ε ^ 2 - ε ^ 3) * (k : ℝ) / 4) := by
      rw [Real.exp_add, Real.exp_log h2m]; ring
    rw [hrw, ← Real.exp_zero]
    apply Real.exp_lt_exp.mpr
    linarith

/-- **Johnson–Lindenstrauss (end-to-end Gaussian form).** For an arbitrary set of `m`
distinct points in `EuclideanSpace ℝ (Fin d)`, any `0 < ε < 1`, and any target dimension
`k` with `4·log(2 m²) < (ε²−ε³)·k`, there exists a Gaussian projection matrix
`A : Fin k → Fin d → ℝ` whose induced map `jlMap k d A` preserves all pairwise squared
distances to within a factor `1 ± ε`. -/
theorem johnson_lindenstrauss_pointset {m d k : ℕ} (hk : 0 < k)
    (p : Fin m → EuclideanSpace ℝ (Fin d)) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1)
    (hp : ∀ a b, a ≠ b → p a ≠ p b)
    (hdim : 4 * Real.log (2 * (m : ℝ) ^ 2) < (ε ^ 2 - ε ^ 3) * (k : ℝ)) :
    ∃ A : Fin k → Fin d → ℝ, ∀ a b, a ≠ b →
      |(∑ i, (jlMap k d A (fun j => (p a - p b) j) i) ^ 2) - ‖p a - p b‖ ^ 2|
        < ε * ‖p a - p b‖ ^ 2 := by
  apply johnson_lindenstrauss (μ := gaussianMatrix k d)
    (C := 2 * rexp (-(ε ^ 2 - ε ^ 3) * (k : ℝ) / 4))
    (r := fun a b A => ∑ i, (jlMap k d A (fun j => (p a - p b) j) i) ^ 2)
    (D := fun a b => ‖p a - p b‖ ^ 2)
  · intro a b hab
    have hne : p a - p b ≠ 0 := sub_ne_zero.mpr (hp a b hab)
    have hwne : ∑ j, ((p a - p b) j) ^ 2 ≠ 0 := by
      rw [← EuclideanSpace.real_norm_sq_eq]
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)
    have hnorm : ∑ j, ((p a - p b) j) ^ 2 = ‖p a - p b‖ ^ 2 :=
      (EuclideanSpace.real_norm_sq_eq _).symm
    have hconc := jlMap_concentration hk (fun j => (p a - p b) j) hwne h0 h1
    rw [hnorm] at hconc
    exact hconc
  · positivity
  · exact card_condition hdim

end JL
