/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import LeanPool.ZetaZeros.Hilbert.Defs

/-!
# Inner products of symmetric functions are real

The reason the source may apply real inequalities such as `a² + 1 ≥ 2a` to the Bessel coefficients:
every inner product formed from symmetric functions is real, because conjugating it is the same as
reflecting the interval, and the interval `(-lam, lam)` is reflection-invariant.
-/

@[expose] public section

namespace ZetaZeros

/-- **Inner products of symmetric functions are self-conjugate.** -/
theorem conj_inner_symmetric {Φ₁ Φ₂ : ℝ → ℂ} (h1 : IsSymmetric Φ₁) (h2 : IsSymmetric Φ₂)
    (lam : ℝ) :
    (starRingEnd ℂ) (∫ u in (-lam)..lam, Φ₁ u * (starRingEnd ℂ) (Φ₂ u))
      = ∫ u in (-lam)..lam, Φ₁ u * (starRingEnd ℂ) (Φ₂ u) := by
  rw [← intervalIntegral.intervalIntegral_conj]
  have hpt : ∀ u : ℝ, (starRingEnd ℂ) (Φ₁ u * (starRingEnd ℂ) (Φ₂ u))
      = Φ₁ (-u) * (starRingEnd ℂ) (Φ₂ (-u)) := by
    intro u
    rw [map_mul, Complex.conj_conj, h1 u]
    congr 1
    rw [h2 (-u), neg_neg]
  calc ∫ u in (-lam)..lam, (starRingEnd ℂ) (Φ₁ u * (starRingEnd ℂ) (Φ₂ u))
      = ∫ u in (-lam)..lam, Φ₁ (-u) * (starRingEnd ℂ) (Φ₂ (-u)) := by
        exact intervalIntegral.integral_congr fun u _ => hpt u
    _ = ∫ u in (-lam)..lam, Φ₁ u * (starRingEnd ℂ) (Φ₂ u) := by
        rw [intervalIntegral.integral_comp_neg fun v => Φ₁ v * (starRingEnd ℂ) (Φ₂ v)]
        norm_num

/-- **Inner products of symmetric functions are real.** -/
@[zz_tag "lem_symmetric_inner_real"]
theorem inner_symmetric_im_eq_zero {Φ₁ Φ₂ : ℝ → ℂ} (h1 : IsSymmetric Φ₁) (h2 : IsSymmetric Φ₂)
    (lam : ℝ) :
    (∫ u in (-lam)..lam, Φ₁ u * (starRingEnd ℂ) (Φ₂ u)).im = 0 := by
  have h := conj_inner_symmetric h1 h2 lam
  have := Complex.conj_eq_iff_im.mp h
  exact this

end ZetaZeros
