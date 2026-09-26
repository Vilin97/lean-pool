/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.ImplicitMapping
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.InjectiveMapping.OneVariable

/-!
# Nonsingularity in the presence of an invertible transverse minor

The implicit function theorem reduces an injective map to an injective scalar function on a
one-dimensional level set. Its nonzero derivative completes an invertible minor to the full
derivative. These results are independent of the general injective-mapping theorem.

## Main results

`isInvertible_fderiv_of_injOn_of_invertible_partial` completes an invertible transverse minor.
`isInvertible_fderiv_of_injOn_of_hyperplane` is the corresponding statement after restricting to
a level hyperplane. `injective_of_injective_vertical_of_transverse_vector` is the
one-dimensional reduction.
-/

public noncomputable section

open Set Filter Function
open scoped Topology

namespace SeveralComplexVariables

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]

/-- An injective vertical block and a nonzero transverse image imply injectivity. -/
theorem injective_of_injective_vertical_of_transverse_vector
    (L : (ℂ × P) →L[ℂ] (ℂ × P))
    (hi : Injective (fun p : P => (L (0, p)).2)) {b : P}
    (hs : (L (1, b)).2 = 0) (ht : (L (1, b)).1 ≠ 0) : Injective L := by
  apply (injective_iff_map_eq_zero L).mpr
  intro v hv
  have he : (0, v.2 - v.1 • b) = v - v.1 • (1, b) := by
    ext <;> simp
  have hz : (L (0, v.2 - v.1 • b)).2 = 0 := by
    rw [he, map_sub, map_smul, hv]
    simp [hs]
  have hb : v.2 - v.1 • b = 0 :=
    hi (by simpa only [Prod.mk_zero_zero, map_zero, Prod.snd_zero] using hz)
  have hv' : v = v.1 • (1, b) := by
    ext
    · simp
    · exact sub_eq_zero.mp hb
  have him : L v = v.1 • L (1, b) := by
    conv_lhs => rw [hv']
    rw [map_smul]
  have hc : v.1 * (L (1, b)).1 = 0 := by
    simpa only [Prod.smul_fst, smul_eq_mul, Prod.fst_zero] using
      congrArg Prod.fst (him.symm.trans hv)
  have h0 : v.1 = 0 := (mul_eq_zero.mp hc).resolve_right ht
  rw [hv', h0, zero_smul]

variable [FiniteDimensional ℂ P]

/-- An injective holomorphic map with an invertible codimension-one minor is nonsingular. -/
theorem isInvertible_fderiv_of_injOn_of_invertible_partial
    {D : Set (ℂ × P)} (hD : IsOpen D) {f : (ℂ × P) → (ℂ × P)}
    (hf : DifferentiableOn ℂ f D) (hi : InjOn f D) {a : ℂ} {b : P}
    (hab : (a, b) ∈ D)
    (hpart : ((fderiv ℂ (fun z => (f z).2) (a, b)).comp
      (ContinuousLinearMap.inr ℂ ℂ P)).IsInvertible) :
    (fderiv ℂ f (a, b)).IsInvertible := by
  let := FiniteDimensional.complete ℂ P
  have hfs : DifferentiableOn ℂ (fun z => (f z).2) D := hf.snd
  obtain ⟨U, V, g, hU, ha, hV, hb, hUV, hg, hm, hga, _, heq⟩ :=
    exists_holomorphic_implicit_mapping hD hfs hab hpart
  let γ : ℂ → ℂ × P := fun w => (w, g w)
  have hγ : DifferentiableOn ℂ γ U := differentiableOn_id.prodMk hg
  have hγD : MapsTo γ U D := fun w hw => hUV ⟨hw, hm hw⟩
  have hfg : DifferentiableOn ℂ (f ∘ γ) U := hf.comp hγ hγD
  have hscalar : InjOn (fun w => (f (γ w)).1) U := by
    intro w hw z hz he
    have hs : (f (γ w)).2 = (f (γ z)).2 :=
      ((heq w hw (g w) (hm hw)).mpr rfl).trans
        ((heq z hz (g z) (hm hz)).mpr rfl).symm
    exact congrArg Prod.fst (hi (hγD hw) (hγD hz) (Prod.ext he hs))
  have hne := deriv_ne_zero_of_injOn hU hfg.fst hscalar ha
  have hγa : HasDerivAt γ (1, deriv g a) a :=
    (hasDerivAt_id a).prodMk ((hg a ha).differentiableAt (hU.mem_nhds ha)).hasDerivAt
  have hfa := ((hf (a, b) hab).differentiableAt (hD.mem_nhds hab)).hasFDerivAt
  have hc := hfa.comp_hasDerivAt_of_eq a hγa (by simp [γ, hga])
  have hcf := (ContinuousLinearMap.fst ℂ ℂ P).hasFDerivAt.comp_hasDerivAt a hc
  have hcs := (ContinuousLinearMap.snd ℂ ℂ P).hasFDerivAt.comp_hasDerivAt a hc
  change HasDerivAt (fun w => (f (γ w)).1)
    (fderiv ℂ f (a, b) (1, deriv g a)).1 a at hcf
  change HasDerivAt (fun w => (f (γ w)).2)
    (fderiv ℂ f (a, b) (1, deriv g a)).2 a at hcs
  have hs : (fderiv ℂ f (a, b) (1, deriv g a)).2 = 0 := by
    rw [← hcs.deriv]
    apply (Filter.EventuallyEq.deriv_eq ?_).trans (deriv_const a (f (a, b)).2)
    filter_upwards [hU.mem_nhds ha] with w hw
    exact (heq w hw (g w) (hm hw)).mpr rfl
  have ht : (fderiv ℂ f (a, b) (1, deriv g a)).1 ≠ 0 := by
    rwa [← hcf.deriv]
  have hA : Injective (fun p : P => (fderiv ℂ f (a, b) (0, p)).2) := by
    obtain ⟨A, hA⟩ := hpart
    have he : (fun p : P => (fderiv ℂ f (a, b) (0, p)).2) = A := by
      funext p
      change _ = (A : P →L[ℂ] P) p
      rw [hA]
      rw [hfa.snd.fderiv]
      rfl
    rw [he]
    exact A.injective
  have hinj := injective_of_injective_vertical_of_transverse_vector
    (fderiv ℂ f (a, b)) hA hs ht
  exact ⟨(LinearEquiv.ofBijective (fderiv ℂ f (a, b)).toLinearMap
    ⟨hinj, (LinearMap.injective_iff_surjective).mp hinj⟩).toContinuousLinearEquiv, rfl⟩

/-- An embedding of a hyperplane extends to linear coordinates with one extra scalar variable. -/
theorem exists_linearEquiv_prod_extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (i : P →L[ℂ] E) (hi : Injective i)
    (hdim : Module.finrank ℂ P + 1 = Module.finrank ℂ E) :
    ∃ A : (ℂ × P) ≃L[ℂ] E, ∀ p, A (0, p) = i p := by
  let R := LinearMap.range i.toLinearMap
  let e : P ≃ₗ[ℂ] R := LinearEquiv.ofInjective i.toLinearMap hi
  obtain ⟨Q, hQ⟩ := R.exists_isCompl
  have hdimQ : Module.finrank ℂ Q = 1 := by
    have hh := Submodule.finrank_add_eq_of_isCompl hQ
    have he := e.finrank_eq
    omega
  let c : ℂ ≃ₗ[ℂ] Q := LinearEquiv.ofFinrankEq ℂ Q (by simpa using hdimQ.symm)
  let A := ((c.prodCongr e).trans (Q.prodEquivOfIsCompl R hQ.symm)).toContinuousLinearEquiv
  refine ⟨A, fun p => ?_⟩
  change (c 0 : E) + (e p : E) = i p
  simp only [map_zero, Submodule.coe_zero, zero_add]
  rfl

/-- If the derivative of an injective holomorphic map is injective on a hyperplane, then its full
derivative is invertible. -/
theorem isInvertible_fderiv_of_injOn_of_hyperplane
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    (hdim : Module.finrank ℂ E = Module.finrank ℂ F)
    {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U)
    (hi : InjOn f U) {a : E} (ha : a ∈ U) (S : P →L[ℂ] E)
    (hS : Injective S) (hP : Module.finrank ℂ P + 1 = Module.finrank ℂ E)
    (hdfS : Injective ((fderiv ℂ f a).comp S)) : (fderiv ℂ f a).IsInvertible := by
  obtain ⟨A, hA⟩ := exists_linearEquiv_prod_extension S hS hP
  obtain ⟨B, hB⟩ := exists_linearEquiv_prod_extension ((fderiv ℂ f a).comp S) hdfS
    (hP.trans hdim)
  let g := B.symm ∘ f ∘ A
  let D := A ⁻¹' U
  have hD : IsOpen D := hU.preimage A.continuous
  have hg : DifferentiableOn ℂ g D :=
    B.symm.differentiable.comp_differentiableOn
      (hf.comp A.differentiable.differentiableOn (fun _ hz => hz))
  have hgi : InjOn g D := by
    intro z hz w hw he
    apply A.injective
    apply hi hz hw
    exact B.symm.injective he
  have haD : A.symm a ∈ D := by simpa [D]
  have hda : fderiv ℂ g (A.symm a) =
      B.symm.toContinuousLinearMap.comp ((fderiv ℂ f a).comp A.toContinuousLinearMap) := by
    have hfa : HasFDerivAt f (fderiv ℂ f a) (A (A.symm a)) := by
      simpa only [A.apply_symm_apply] using
        ((hf a ha).differentiableAt (hU.mem_nhds ha)).hasFDerivAt
    exact (B.symm.hasFDerivAt.comp (A.symm a) (hfa.comp (A.symm a) A.hasFDerivAt)).fderiv
  have hpartial : (fderiv ℂ (fun z => (g z).2) (A.symm a)).comp
      (ContinuousLinearMap.inr ℂ ℂ P) = ContinuousLinearMap.id ℂ P := by
    rw [((hg _ haD).differentiableAt (hD.mem_nhds haD)).hasFDerivAt.snd.fderiv, hda]
    ext p
    change (B.symm ((fderiv ℂ f a) (A (0, p)))).2 = p
    rw [hA, ← ContinuousLinearMap.comp_apply, ← hB, B.symm_apply_apply]
  have hinv : (fderiv ℂ g (A.symm a)).IsInvertible :=
    isInvertible_fderiv_of_injOn_of_invertible_partial hD hg hgi haD
      (by
        change ((fderiv ℂ (fun z => (g z).2) (A.symm a)).comp
          (ContinuousLinearMap.inr ℂ ℂ P)).IsInvertible
        rw [hpartial]
        exact ⟨ContinuousLinearEquiv.refl ℂ P, rfl⟩)
  obtain ⟨T, hT⟩ := hinv
  refine ⟨A.symm.trans (T.trans B), ?_⟩
  ext v
  change B (T (A.symm v)) = (fderiv ℂ f a) v
  apply B.symm.injective
  have he := DFunLike.congr_fun hT (A.symm v)
  simpa only [hda, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    A.apply_symm_apply, B.symm_apply_apply] using he

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
