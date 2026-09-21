/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.RoundAmbientDirections

/-! # Nondegeneracy of the regular polar derivative -/

@[expose] public noncomputable section
namespace LichnerowiczObata
variable {P V : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A positive angular coefficient and a unit radial coefficient rule out
every nonzero tangent vector in the kernel of a polar derivative. -/
theorem polar_derivative_eq_zero_iff (D : P × ℝ →L[ℝ] V) {u w : P} {s B : ℝ}
    (hB : 0 < B) (hw : inner ℝ u w = 0)
    (hmetric : ∀ v : P, inner ℝ u v = 0 → ∀ t : ℝ,
      inner ℝ (D (v, t)) (D (v, t)) = B * inner ℝ v v + t * t) :
    D (w, s) = 0 ↔ w = 0 ∧ s = 0 := by
  constructor
  · intro hz
    have hh := hmetric w hw s
    rw [hz, inner_zero_left, real_inner_self_eq_norm_sq] at hh
    have hw0 : ‖w‖ ^ 2 = 0 := by nlinarith [sq_nonneg s, sq_nonneg ‖w‖]
    have hs0 : s = 0 := by nlinarith [sq_nonneg s]
    exact ⟨norm_eq_zero.mp (by nlinarith [norm_nonneg w]), hs0⟩
  · rintro ⟨rfl, rfl⟩
    exact map_zero D

theorem polar_derivative_injOn (D : P × ℝ →L[ℝ] V) {u : P} {B : ℝ}
    (hB : 0 < B)
    (hmetric : ∀ v : P, inner ℝ u v = 0 → ∀ t : ℝ,
      inner ℝ (D (v, t)) (D (v, t)) = B * inner ℝ v v + t * t) :
    Set.InjOn D {q : P × ℝ | inner ℝ u q.1 = 0} := by
  intro x hx y hy he
  have ht : inner ℝ u (x - y).1 = 0 := by
    change inner ℝ u (x.1 - y.1) = 0
    rw [inner_sub_right, hx, hy, sub_self]
  have hz : D (x - y) = 0 := by rw [map_sub, he, sub_self]
  have hh := (polar_derivative_eq_zero_iff D hB ht hmetric).mp hz
  apply sub_eq_zero.mp
  exact Prod.ext hh.1 hh.2

theorem obata_polar_coefficient_pos {K r : ℝ} (hK : 0 < K)
    (hr : r ∈ Set.Ioo 0 (Real.pi / Real.sqrt K)) :
    0 < Real.sin (Real.sqrt K * r) ^ 2 / K := by
  have hs : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hp : Real.sqrt K * r < Real.pi := by
    have hh := (lt_div_iff₀ hs).mp hr.2
    simpa only [mul_comm] using hh
  exact div_pos (sq_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi (mul_pos hs hr.1) hp)) hK

/-- The actual intrinsic round polar derivative is injective on the angular
tangent and radial directions at every regular parameter. -/
theorem intrinsicRoundPolar_derivative_injOn {K : ℝ} (hK : 0 < K)
    (u : P) (hu : ‖u‖ = 1) {r : ℝ}
    (hr : r ∈ Set.Ioo 0 (Real.pi / Real.sqrt K)) :
    let Ψ := fun q : P × ℝ => roundPolarCurve (1 / Real.sqrt K)
      roundNorth (roundAngularInclusion q.1) q.2
    Set.InjOn (fderiv ℝ Ψ (u, r)) {q : P × ℝ | inner ℝ u q.1 = 0} := by
  apply polar_derivative_injOn _ (obata_polar_coefficient_pos hK hr)
  intro v hv t
  exact intrinsicRoundPolar_metric hK u v v hu hv hv r t t

end LichnerowiczObata
