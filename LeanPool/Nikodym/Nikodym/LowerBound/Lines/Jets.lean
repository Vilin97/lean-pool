/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.Nikodym.Nikodym.LowerBound.Lines.Basic

/-!
# Jet vanishing restricts to divisibility on a line

This file implements blueprint node **L01** of the lower-bound side of the sharp finite-field
Nikodym exponent.

If a line `T ↦ b + T v` lies on an ideal `I` (that is, `I ≤ λ_{b,v}`) and a polynomial
`g` lies in the jet ideal `I ⊔ 𝔪_{b+av} ^ r`, then `(T - a)^r` divides the univariate
restriction `res_{b,v} g`. The finite-field form substitutes the coordinate lift `liftPt`.
-/

namespace Nikodym.LowerBound

open MvPolynomial

variable {K : Type*} [Field K] {d : ℕ}

/-- Blueprint L01: the generator `X i - (b i + a v i)` restricts to `v i · (T - a)` on the line
`T ↦ b + T v`. -/
theorem lineRes_X_sub_C (b v : Fin d → K) (a : K) (i : Fin d) :
    lineRes b v (X i - C (b i + a * v i)) =
      Polynomial.C (v i) * (Polynomial.X - Polynomial.C a) := by
  simp only [map_sub, lineRes_X, lineRes_C, map_add, map_mul]
  ring

/-- Blueprint L01: the image of `𝔪_{b+av}` under `res_{b,v}` is contained in the principal ideal
`(T - a)`. -/
theorem map_pointIdeal_le (b v : Fin d → K) (a : K) :
    (pointIdeal (b + a • v)).map (lineRes b v : MvPolynomial (Fin d) K →+* Polynomial K) ≤
      Ideal.span {Polynomial.X - Polynomial.C a} := by
  rw [pointIdeal_eq_span, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  change lineRes b v (X i - C ((b + a • v) i)) ∈ _
  have hi : (b + a • v) i = b i + a * v i := by
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hi, lineRes_X_sub_C]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

/-- Blueprint L01: the image of `𝔪_{b+av} ^ r` under `res_{b,v}` is contained in `(T - a)^r`. -/
theorem map_pointIdeal_pow_le (b v : Fin d → K) (a : K) (r : ℕ) :
    (pointIdeal (b + a • v) ^ r).map (lineRes b v : MvPolynomial (Fin d) K →+* Polynomial K) ≤
      Ideal.span {Polynomial.X - Polynomial.C a} ^ r := by
  rw [Ideal.map_pow]
  exact Ideal.pow_right_mono (map_pointIdeal_le b v a) r

/-- Blueprint L01: if `I ≤ λ_{b,v}` and `g ∈ I ⊔ 𝔪_{b+av} ^ r`, then `(T - a)^r` divides
`res_{b,v} g`. -/
theorem dvd_lineRes_of_mem_jetIdeal (b v : Fin d → K) (a : K)
    {I : Ideal (MvPolynomial (Fin d) K)} (hI : I ≤ lineIdeal b v)
    {g : MvPolynomial (Fin d) K} (r : ℕ) (hg : g ∈ jetIdeal I (b + a • v) r) :
    (Polynomial.X - Polynomial.C a) ^ r ∣ lineRes b v g := by
  have hmap :
      (jetIdeal I (b + a • v) r).map
          (lineRes b v : MvPolynomial (Fin d) K →+* Polynomial K) ≤
        Ideal.span {Polynomial.X - Polynomial.C a} ^ r := by
    rw [jetIdeal, Ideal.map_sup]
    have hbot :
        I.map (lineRes b v : MvPolynomial (Fin d) K →+* Polynomial K) = ⊥ := by
      rw [eq_bot_iff, Ideal.map_le_iff_le_comap, ← RingHom.ker_eq_comap_bot]
      exact hI
    rw [hbot, bot_sup_eq]
    exact map_pointIdeal_pow_le b v a r
  have hmem :
      lineRes b v g ∈ Ideal.span {Polynomial.X - Polynomial.C a} ^ r :=
    hmap (Ideal.mem_map_of_mem _ hg)
  rw [Ideal.span_singleton_pow] at hmem
  exact Ideal.mem_span_singleton.mp hmem

variable {F : Type*} [Field F] [Algebra F K]

/-- Blueprint L01: the finite-field form of jet-to-divisibility, with points and directions
lifted along `algebraMap F K`. -/
theorem dvd_lineRes_of_mem_jetIdeal_liftPt (b v : Fin d → F) (a : F)
    {I : Ideal (MvPolynomial (Fin d) K)}
    (hI : I ≤ lineIdeal (liftPt b) (liftPt v)) {g : MvPolynomial (Fin d) K} (r : ℕ)
    (hg : g ∈ jetIdeal I (liftPt (b + a • v)) r) :
    (Polynomial.X - Polynomial.C (algebraMap F K a)) ^ r ∣
      lineRes (liftPt b) (liftPt v) g := by
  have hg' : g ∈ jetIdeal I (liftPt b + algebraMap F K a • liftPt v) r := by
    rwa [← liftPt_smul K, ← liftPt_add K]
  exact dvd_lineRes_of_mem_jetIdeal (liftPt b) (liftPt v) (algebraMap F K a) hI r hg'

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
