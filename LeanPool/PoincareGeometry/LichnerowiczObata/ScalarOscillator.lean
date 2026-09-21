/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Tactic

/-! # The cosine solution of the scalar oscillator, including zero frequency -/

@[expose] public noncomputable section
open Set
open scoped Topology

namespace LichnerowiczObata

/-- A scalar oscillator with zero initial velocity is the cosine solution.
The energy argument also covers zero frequency without division. -/
theorem scalar_oscillator_eq_cos {F V : ℝ → ℝ} {ω a : ℝ} {T : Set ℝ}
    (hT : IsOpen T) (hconn : IsPreconnected T) (hzero : (0 : ℝ) ∈ T)
    (hF : ∀ t ∈ T, HasDerivAt F (V t) t)
    (hV : ∀ t ∈ T, HasDerivAt V (-(ω ^ 2) * F t) t)
    (hFzero : F 0 = a) (hVzero : V 0 = 0) {t : ℝ} (ht : t ∈ T) :
    F t = a * Real.cos (ω * t) := by
  let G : ℝ → ℝ := fun s => F s - a * Real.cos (ω * s)
  let W : ℝ → ℝ := fun s => V s + a * ω * Real.sin (ω * s)
  have hG : ∀ s ∈ T, HasDerivAt G (W s) s := by
    intro s hs
    convert (hF s hs).sub
      ((((hasDerivAt_id s).const_mul ω).cos).const_mul a) using 1 <;>
      first | rfl | dsimp [W]; ring
  have hW : ∀ s ∈ T, HasDerivAt W (-(ω ^ 2) * G s) s := by
    intro s hs
    convert (hV s hs).add
      ((((hasDerivAt_id s).const_mul ω).sin).const_mul (a * ω)) using 1 <;>
      first | rfl | dsimp [G]; ring
  have henergy : ∀ s ∈ T,
      HasDerivAt (fun x => W x ^ 2 + ω ^ 2 * G x ^ 2) 0 s := by
    intro s hs
    convert ((hW s hs).pow 2).add (((hG s hs).pow 2).const_mul (ω ^ 2)) using 1 <;>
      first | rfl | ring
  have hWzero : ∀ s ∈ T, W s = 0 := by
    intro s hs
    have he := hT.is_const_of_deriv_eq_zero hconn
      (fun x hx => (henergy x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (henergy x hx).deriv) hs hzero
    have he0 : W s ^ 2 + ω ^ 2 * G s ^ 2 = 0 := by
      simpa [W, G, hFzero, hVzero] using he
    nlinarith [sq_nonneg (W s), mul_nonneg (sq_nonneg ω) (sq_nonneg (G s))]
  have hGzero : G t = G 0 := hT.is_const_of_deriv_eq_zero hconn
    (fun x hx => (hG x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hG x hx).deriv.trans (hWzero x hx)) ht hzero
  have he : F t - a * Real.cos (ω * t) = 0 := by
    simpa [G, hFzero] using hGzero
  exact sub_eq_zero.mp he

end LichnerowiczObata
