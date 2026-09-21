/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.RadialProduct

/-! # Matching opposite polar coordinates on their equator -/

@[expose] public noncomputable section
open Set
namespace LichnerowiczObata

/-- Restrict a product homeomorphism to a fiber that it and its inverse preserve. -/
def productFiberHomeomorph {X Y T : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace T] (e : X × T ≃ₜ Y × T) (t : T)
    (hf : ∀ x, (e (x, t)).2 = t) (hb : ∀ y, (e.symm (y, t)).2 = t) : X ≃ₜ Y where
  toFun x := (e (x, t)).1
  invFun y := (e.symm (y, t)).1
  left_inv x := by
    have he : e (x, t) = ((e (x, t)).1, t) := Prod.ext rfl (hf x)
    have hh := e.symm_apply_apply (x, t)
    rw [he] at hh
    exact congrArg Prod.fst hh
  right_inv y := by
    have he : e.symm (y, t) = ((e.symm (y, t)).1, t) := Prod.ext rfl (hb y)
    have hh := e.apply_symm_apply (y, t)
    rw [he] at hh
    exact congrArg Prod.fst hh
  continuous_toFun := continuous_fst.comp (e.continuous.comp (continuous_id.prodMk continuous_const))
  continuous_invFun := continuous_fst.comp (e.symm.continuous.comp (continuous_id.prodMk continuous_const))

/-- Complementary radial coordinates identify the same equatorial level
and construct its angular homeomorphism without an assumed matching map. -/
theorem exists_polar_equator_matching {X Y U : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace U]
    {L : ℝ} (hL : 0 < L) (N : X × Ioo 0 L ≃ₜ U) (S : Y × Ioo 0 L ≃ₜ U)
    (ρ : U → ℝ) (hN : ∀ q, ρ (N q) = (q.2 : ℝ))
    (hS : ∀ q, ρ (S q) = L - (q.2 : ℝ)) :
    ∃ A : X ≃ₜ Y, ∀ x,
      N (x, ⟨L / 2, by constructor <;> linarith⟩) =
        S (A x, ⟨L / 2, by constructor <;> linarith⟩) := by
  let t : Ioo 0 L := ⟨L / 2, by constructor <;> linarith⟩
  let e := N.trans S.symm
  have hf : ∀ x, (e (x, t)).2 = t := by
    intro x
    have hh := hS (e (x, t))
    change ρ (S (S.symm (N (x, t)))) = L - ((e (x, t)).2 : ℝ) at hh
    rw [S.apply_symm_apply, hN] at hh
    apply Subtype.ext
    change ((e (x, t)).2 : ℝ) = L / 2
    change L / 2 = L - ((e (x, t)).2 : ℝ) at hh
    linarith
  have hb : ∀ y, (e.symm (y, t)).2 = t := by
    intro y
    have hh := hN (e.symm (y, t))
    change ρ (N (N.symm (S (y, t)))) = ((e.symm (y, t)).2 : ℝ) at hh
    rw [N.apply_symm_apply, hS] at hh
    apply Subtype.ext
    change ((e.symm (y, t)).2 : ℝ) = L / 2
    change L - L / 2 = ((e.symm (y, t)).2 : ℝ) at hh
    linarith
  let A := productFiberHomeomorph e t hf hb
  refine ⟨A, ?_⟩
  intro x
  have he : e (x, t) = (A x, t) := Prod.ext rfl (hf x)
  have hh := congrArg S he
  change S (S.symm (N (x, t))) = S (A x, t) at hh
  simpa only [S.apply_symm_apply] using hh

end LichnerowiczObata
