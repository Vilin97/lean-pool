/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.SphereImmersionCalculus
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Tangent and radial decomposition for a spherical immersion -/

@[expose] public noncomputable section
namespace LichnerowiczObata
variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [FiniteDimensional ℝ A]

/-- An injective codimension-one tangent map and a nonzero orthogonal
radius span the entire ambient space. -/
theorem exists_tangent_radial_decomposition
    (L : E →L[ℝ] A) (hL : Function.Injective L)
    (hdim : Module.finrank ℝ A = Module.finrank ℝ E + 1)
    {q : A} (hq : q ≠ 0) (ho : ∀ v, inner ℝ q (L v) = 0) (a : A) :
    ∃ v : E, ∃ t : ℝ, a = L v + t • q := by
  let J : E × ℝ →ₗ[ℝ] A :=
    { toFun := fun z => L z.1 + z.2 • q
      map_add' := by intro z w; simp [add_smul]; abel
      map_smul' := by intro t z; simp [smul_add, smul_smul] }
  have hJ : Function.Injective J := by
    apply (injective_iff_map_eq_zero J).mpr
    intro z hz
    have hh := congrArg (fun b => inner ℝ q b) hz
    change inner ℝ q (L z.1 + z.2 • q) = inner ℝ q 0 at hh
    rw [inner_add_right, ho, inner_smul_right, inner_zero_right, zero_add] at hh
    have ht : z.2 = 0 := (mul_eq_zero.mp hh).resolve_right (inner_self_ne_zero.mpr hq)
    have hv : z.1 = 0 := by
      apply hL
      simpa [J, ht] using hz
    exact Prod.ext hv ht
  have hdim' : Module.finrank ℝ (E × ℝ) = Module.finrank ℝ A := by
    simpa only [Module.finrank_prod, Module.finrank_self] using hdim.symm
  obtain ⟨z, hz⟩ := (J.linearEquivOfInjective hJ hdim').surjective a
  exact ⟨z.1, z.2, hz.symm⟩

/-- A normal vector is determined by its radial pairing. -/
theorem eq_smul_of_orthogonal_tangent
    (L : E →L[ℝ] A) (hL : Function.Injective L)
    (hdim : Module.finrank ℝ A = Module.finrank ℝ E + 1)
    {q : A} (hq : q ≠ 0) (ho : ∀ v, inner ℝ q (L v) = 0)
    {a : A} (ha : ∀ v, inner ℝ a (L v) = 0) :
    a = (inner ℝ a q / ‖q‖ ^ 2) • q := by
  obtain ⟨v, t, hv⟩ := exists_tangent_radial_decomposition L hL hdim hq ho a
  have htangent := ha v
  rw [hv, inner_add_left, inner_smul_left, ho, mul_zero, add_zero] at htangent
  have hvzero : L v = 0 := inner_self_eq_zero.mp htangent
  rw [hvzero, zero_add] at hv
  have hnorm : ‖q‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hq)
  rw [hv, real_inner_smul_left, real_inner_self_eq_norm_sq]
  congr 1
  field_simp

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ A] in
/-- The algebraic Koszul cancellation: symmetry and metric compatibility
force the tangential part of a second derivative to be the connection term. -/
theorem second_form_orthogonal_of_metric_compatibility
    (L : E →L[ℝ] A) (B : E →L[ℝ] E →L[ℝ] A) (Γ : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ v w, B v w = B w v) (hΓ : ∀ v w, Γ v w = Γ w v)
    (hm : ∀ d u w, inner ℝ (B d u) (L w) + inner ℝ (L u) (B d w) =
      inner ℝ (L (Γ d u)) (L w) + inner ℝ (L u) (L (Γ d w)))
    (v w z : E) : inner ℝ (B v w - L (Γ v w)) (L z) = 0 := by
  have h1 := hm v w z
  have h2 := hm w z v
  have h3 := hm z v w
  simp only [hB w v, hB z v, hB z w, hΓ w v, hΓ z v, hΓ z w] at h2 h3
  simp only [inner_sub_left]
  simp only [real_inner_comm] at h1 h2 h3 ⊢
  linarith

end LichnerowiczObata
