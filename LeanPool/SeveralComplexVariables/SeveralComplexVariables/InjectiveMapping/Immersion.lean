/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.InjectiveMapping.OneVariable

/-!
# Immersion points of injective holomorphic maps

Scalar projections with nonzero differential admit local coordinates. Restricting to a level
hyperplane lowers the source dimension and preserves injectivity. This gives immersion points
without assuming that source and target dimensions agree.

## Main results

`exists_fderiv_ne_zero_of_injOn` finds a point of nonzero derivative on a nonempty open set in
positive dimension. `exists_scalar_projection_fderiv_ne_zero` produces a scalar coordinate with
nonzero derivative. `exists_injective_fderiv_of_injOn` is the immersion-point theorem after
restricting to a level hyperplane.
-/

public noncomputable section

open Set Filter Metric Function
open scoped Topology

namespace SeveralComplexVariables

universe u

variable {E : Type u} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
/-- An injective holomorphic map on a nonempty open set in positive dimension has nonzero
differential somewhere. -/
theorem exists_fderiv_ne_zero_of_injOn [Nontrivial E]
    {U : Set E} (hU : IsOpen U) (hne : U.Nonempty) {f : E → F}
    (hf : DifferentiableOn ℂ f U) (hi : InjOn f U) :
    ∃ a ∈ U, fderiv ℂ f a ≠ 0 := by
  by_contra! hz
  obtain ⟨a, ha⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  have hs : ({a} : Set E) ∈ 𝓝 a := by
    filter_upwards [ball_mem_nhds a hr] with z hzball
    apply hi (hball hzball) ha
    exact isOpen_ball.is_const_of_fderiv_eq_zero isPreconnected_ball
      (hf.mono hball) (fun w hw => hz w (hball hw)) hzball (mem_ball_self hr)
  have := mem_interior_iff_mem_nhds.mpr hs
  simp at this

omit [FiniteDimensional ℂ E] in
/-- Some scalar projection of an injective holomorphic map has nonzero differential at a point of
any nonempty open domain of positive dimension. -/
theorem exists_scalar_projection_fderiv_ne_zero [Nontrivial E]
    {U : Set E} (hU : IsOpen U) (hne : U.Nonempty) {f : E → F}
    (hf : DifferentiableOn ℂ f U) (hi : InjOn f U) :
    ∃ a ∈ U, ∃ ℓ : F →L[ℂ] ℂ, fderiv ℂ (ℓ ∘ f) a ≠ 0 := by
  obtain ⟨a, ha, hdfa⟩ := exists_fderiv_ne_zero_of_injOn hU hne hf hi
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hdfa
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_ne_zero ℂ hv
  let ℓ : F →L[ℂ] ℂ := l.toContinuousLinearMap
  refine ⟨a, ha, ℓ, ?_⟩
  have hd : fderiv ℂ (ℓ ∘ f) a = ℓ.comp (fderiv ℂ f a) :=
    (ℓ.hasFDerivAt.comp a ((hf a ha).differentiableAt (hU.mem_nhds ha)).hasFDerivAt).fderiv
  intro hz
  apply hl
  change ℓ (fderiv ℂ f a v) = 0
  rw [← ContinuousLinearMap.comp_apply, ← hd, hz, zero_apply]

/-- A scalar holomorphic submersion becomes its own differential in suitable local coordinates. -/
theorem exists_biholomorphic_scalar_normalization {U : Set E} (hU : IsOpen U)
    {f : E → ℂ} (hf : DifferentiableOn ℂ f U) {a : E} (ha : a ∈ U)
    (hn : fderiv ℂ f a ≠ 0) :
    ∃ e : OpenPartialHomeomorph E E, IsBiholomorphic e ∧ a ∈ e.source ∧ e.source ⊆ U ∧
      ∀ z ∈ e.source, (fderiv ℂ f a) (e z) = f z := by
  let L := fderiv ℂ f a
  have hL : L.toLinearMap ≠ 0 := fun h => hn (by ext z; exact DFunLike.congr_fun h z)
  obtain ⟨R, hR⟩ := L.toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (LinearMap.surjective hL))
  let B : ℂ →L[ℂ] E := R.toContinuousLinearMap
  have hLB (w : ℂ) : L (B w) = w := DFunLike.congr_fun hR w
  let g : E → E := fun z => z + B (f z - L z)
  have hg : DifferentiableOn ℂ g U :=
    differentiableOn_id.add (B.differentiable.comp_differentiableOn
      (hf.sub L.differentiable.differentiableOn))
  have hd : HasFDerivAt g (ContinuousLinearMap.id ℂ E) a := by
    simpa only [g, L, Pi.add_def, Pi.sub_def, Function.comp_def, id_eq,
      sub_self, ContinuousLinearMap.comp_zero, add_zero] using
      (hasFDerivAt_id a).add (B.hasFDerivAt.comp a
        (((hf a ha).differentiableAt (hU.mem_nhds ha)).hasFDerivAt.sub L.hasFDerivAt))
  obtain ⟨e, he, hae, heU, heq⟩ := exists_biholomorphic_of_isInvertible_fderiv hU hg ha
    (by rw [hd.fderiv]; exact ⟨ContinuousLinearEquiv.refl ℂ E, rfl⟩)
  refine ⟨e, he, hae, heU, fun z _ => ?_⟩
  rw [heq]
  change L (z + B (f z - L z)) = f z
  rw [map_add, hLB]
  abel

omit [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] in
/-- Dimension induction for the existence of immersion points. -/
private theorem exists_injective_fderiv_aux (n : ℕ) :
    ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E],
      Module.finrank ℂ E = n → ∀ {U : Set E}, IsOpen U → U.Nonempty →
      ∀ {f : E → F}, DifferentiableOn ℂ f U → InjOn f U →
        ∃ a ∈ U, Injective (fderiv ℂ f a) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E _ _ _ hn U hU hne f hf hi
    by_cases hzero : Module.finrank ℂ E = 0
    · have : Subsingleton E := Module.finrank_zero_iff.mp hzero
      obtain ⟨a, ha⟩ := hne
      exact ⟨a, ha, fun _ _ _ => Subsingleton.elim _ _⟩
    have : Nontrivial E := not_subsingleton_iff_nontrivial.mp
      (fun hs => hzero (@Module.finrank_zero_of_subsingleton ℂ E _ _ _ _ hs))
    obtain ⟨a, ha, ℓ, hL⟩ := exists_scalar_projection_fderiv_ne_zero hU hne hf hi
    let φ := ℓ ∘ f
    have hφ : DifferentiableOn ℂ φ U := ℓ.differentiable.comp_differentiableOn hf
    let L := fderiv ℂ φ a
    obtain ⟨e, he, hae, heU, heφ⟩ := exists_biholomorphic_scalar_normalization hU hφ ha hL
    let G := f ∘ e.symm
    have hG : DifferentiableOn ℂ G e.target :=
      hf.comp he.2 (fun y hy => heU (e.map_target hy))
    have hGL : EqOn (ℓ ∘ G) L e.target := by
      intro y hy
      exact (heφ (e.symm y) (e.map_target hy)).symm.trans (by rw [e.right_inv hy])
    let K := L.ker
    let κ : K → E := fun z => e a + z
    have hκ : ∀ z, HasFDerivAt κ K.subtypeL z := by
      intro z
      simpa only [zero_add, κ, Pi.add_def, Submodule.subtypeL_apply] using
        (hasFDerivAt_const (e a) z).add K.subtypeL.hasFDerivAt
    let V := κ ⁻¹' e.target
    have hV : IsOpen V := e.open_target.preimage
      (continuous_const.add continuous_subtype_val)
    have hVne : V.Nonempty := ⟨0, by simpa [V, κ] using e.map_source hae⟩
    have hGK : DifferentiableOn ℂ (G ∘ κ) V :=
      hG.comp (fun z _ => (hκ z).differentiableAt.differentiableWithinAt) (fun _ hz => hz)
    have hGKi : InjOn (G ∘ κ) V := by
      intro z hz w hw hzw
      apply Subtype.val_injective
      apply add_left_cancel (a := e a)
      apply e.symm.injOn hz hw
      exact hi (heU (e.map_target hz)) (heU (e.map_target hw)) hzw
    have hL' : L.toLinearMap ≠ 0 := fun h => hL (by ext z; exact DFunLike.congr_fun h z)
    have hdim : Module.finrank ℂ K < n := by
      have hh := Module.Dual.finrank_ker_add_one_of_ne_zero hL'
      change Module.finrank ℂ K + 1 = Module.finrank ℂ E at hh
      omega
    obtain ⟨z, hz, hzi⟩ := ih (Module.finrank ℂ K) hdim rfl hV hVne hGK hGKi
    have hGd := (hG (κ z) hz).differentiableAt (e.open_target.mem_nhds hz)
    have hLG : ℓ.comp (fderiv ℂ G (κ z)) = L := by
      rw [← (ℓ.hasFDerivAt.comp (κ z) hGd.hasFDerivAt).fderiv]
      have hh : (ℓ ∘ G) =ᶠ[𝓝 (κ z)] L :=
        Filter.mem_of_superset (e.open_target.mem_nhds hz) hGL
      exact hh.fderiv_eq.trans L.fderiv
    have hKG : fderiv ℂ (G ∘ κ) z = (fderiv ℂ G (κ z)).comp K.subtypeL :=
      (hGd.hasFDerivAt.comp z (hκ z)).fderiv
    have hinjG : Injective (fderiv ℂ G (κ z)) := by
      apply (injective_iff_map_eq_zero _).mpr
      intro v hv
      have hvK : v ∈ K := by
        change L v = 0
        rw [← hLG, ContinuousLinearMap.comp_apply, hv, map_zero]
      have hvz : (⟨v, hvK⟩ : K) = 0 := hzi (by simp [hKG, hv])
      exact congrArg Subtype.val hvz
    refine ⟨e.symm (κ z), heU (e.map_target hz), ?_⟩
    have hd : fderiv ℂ G (κ z) =
        (fderiv ℂ f (e.symm (κ z))).comp (fderiv ℂ e.symm (κ z)) :=
      fderiv_comp _ ((hf _ (heU (e.map_target hz))).differentiableAt
        (hU.mem_nhds (heU (e.map_target hz)))) (he.symm.differentiableAt hz)
    have hsurj := (he.symm.isInvertible_fderiv hz).bijective.surjective
    intro v w hvw
    obtain ⟨v', rfl⟩ := hsurj v
    obtain ⟨w', rfl⟩ := hsurj w
    exact congrArg (fderiv ℂ e.symm (κ z)) (hinjG (by simpa only [hd,
      ContinuousLinearMap.comp_apply] using hvw))

/-- Every nonempty open restriction of an injective holomorphic map has an immersion point. The
source and target dimensions need not agree. -/
theorem exists_injective_fderiv_of_injOn {U : Set E} (hU : IsOpen U) (hne : U.Nonempty)
    {f : E → F} (hf : DifferentiableOn ℂ f U) (hi : InjOn f U) :
    ∃ a ∈ U, Injective (fderiv ℂ f a) :=
  exists_injective_fderiv_aux (Module.finrank ℂ E) rfl hU hne hf hi

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
