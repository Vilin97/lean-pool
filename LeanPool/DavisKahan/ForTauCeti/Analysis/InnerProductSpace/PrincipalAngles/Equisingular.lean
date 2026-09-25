/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Polar.PartialIsometry
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.SameSequence

/-!
# Composition with an isometry on the range preserves the Gram operator

Let `J` be a bounded operator that is *isometric on the range of `T`*, in the
sharp form `J⋆J T = T`.  Then

`(J T)⋆ (J T) = T⋆ T`,

so `J T` and `T` have the *same* modulus — not merely the same singular-value
list.  The identity is purely algebraic and therefore survives noncompactness,
infinite multiplicity, and empty point spectrum.

## Why this matters for principal angles

Davis and Kahan represent the block operator `f(Θ)` of a pair of subspaces by
an off-diagonal operator `J f(Θ)`, where `J` is the polar partial isometry of
the direct rotation.  `J⋆J` is the orthogonal projection onto the support of
`Θ`, so `J⋆J f(Θ) = f(Θ)` exactly when `f(Θ)` annihilates `ker Θ`.  That holds
for every `f` vanishing at `0`; here the hypothesis is packaged through a
continuous factorisation `f t = t * g t`, which covers the two functions the
paper actually applies — `f t = tan t` and `f t = sin 2t` — and keeps the proof
free of any approximation argument.  The consequence is that the off-diagonal
representative and the diagonal functional calculus have literally the same
modulus, hence the same value under every unitarily invariant norm.

## Main results

* `TauCeti.gram_comp_left_of_adjoint_comp_self_comp`: `(J T)⋆(J T) = T⋆T`.
* `TauCeti.norm_comp_left_apply_of_adjoint_comp_self_comp`: `‖J (T x)‖ = ‖T x‖`.
* `TauCeti.modulus_comp_left_of_adjoint_comp_self_comp`: `|J T| = |T|`.
* `TauCeti.adjoint_comp_self_comp_of_starProjection`: the hypothesis holds when
  `J⋆J` is the projection onto a subspace containing the range of `T`.
* `TauCeti.cfc_eq_mul_cfc_of_eq_id_mul`: `f(a) = a * g(a)` when `f t = t * g t`.
* `TauCeti.modulus_comp_left_cfc`: the two combined — for `f t = t * g t`, if
  `J` is isometric on the range of a self-adjoint `a`, then `|J f(a)| = |f(a)|`.
* `TauCeti.modulus_polarPartial_comp_cfc_modulus`: the instance the principal
  angles use, with `a = |M|` and `J` the polar factor of `M`.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46, Sections 2 and 7: the off-diagonal
  representatives `[[0, -J₀⋆ f(Θ₁)], [J₀ f(Θ₀), 0]]` of the block-diagonal
  operator `f(Θ) = f(Θ₀) ⊕ f(Θ₁)`.
-/

@[expose] public section

namespace TauCeti

open scoped InnerProductSpace

section Gram

universe u v w

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} {F : Type v} {G : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- **Composition with an operator isometric on the range preserves the Gram
operator.**  The hypothesis `J⋆J T = T` says that `J` restricts to an isometry
on the closure of the range of `T`; the conclusion is an operator identity, not
a statement about singular-value lists, so it needs neither compactness nor a
discrete spectrum. -/
theorem gram_comp_left_of_adjoint_comp_self_comp
    {J : F →L[𝕜] G} {T : E →L[𝕜] F}
    (h : J.adjoint ∘L J ∘L T = T) :
    (J ∘L T).adjoint ∘L (J ∘L T) = T.adjoint ∘L T := by
  calc (J ∘L T).adjoint ∘L (J ∘L T)
      = T.adjoint ∘L (J.adjoint ∘L (J ∘L T)) := by
        rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]
    _ = T.adjoint ∘L T := by rw [h]

omit [CompleteSpace E] in
/-- The pointwise form: `J` does not change the length of any value of `T`. -/
theorem norm_comp_left_apply_of_adjoint_comp_self_comp
    {J : F →L[𝕜] G} {T : E →L[𝕜] F}
    (h : J.adjoint ∘L J ∘L T = T) (x : E) :
    ‖J (T x)‖ = ‖T x‖ := by
  have hx : J.adjoint (J (T x)) = T x :=
    congrArg (fun S : E →L[𝕜] F => S x) h
  have hinner : (⟪J (T x), J (T x)⟫_𝕜 : 𝕜) = ⟪T x, T x⟫_𝕜 := by
    rw [← ContinuousLinearMap.adjoint_inner_left J (T x) (J (T x)), hx]
  have hre := congrArg RCLike.re hinner
  rw [inner_self_eq_norm_mul_norm, inner_self_eq_norm_mul_norm] at hre
  nlinarith [norm_nonneg (J (T x)), norm_nonneg (T x), hre]

omit [CompleteSpace G] in
/-- The hypothesis of `TauCeti.gram_comp_left_of_adjoint_comp_self_comp` holds
whenever `J⋆J` is the orthogonal projection onto a subspace containing the range
of `T`.  For a partial isometry `J` that subspace is its initial space. -/
theorem adjoint_comp_self_comp_of_starProjection
    {J : E →L[𝕜] F} {T : G →L[𝕜] E} {W : Submodule 𝕜 E} [W.HasOrthogonalProjection]
    (hJ : J.adjoint ∘L J = W.starProjection)
    (hrange : ∀ x, T x ∈ W) :
    J.adjoint ∘L J ∘L T = T := by
  rw [← ContinuousLinearMap.comp_assoc, hJ]
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [ContinuousLinearMap.comp_apply]
  exact Submodule.starProjection_eq_self_iff.mpr (hrange x)

end Gram

section Approximation

universe u v w

variable {E : Type u} {F : Type v} {G : Type w}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- An operator isometric on the range of `T` leaves the whole approximation-number
sequence of `T` unchanged, hence the value of every unitarily invariant norm. -/
theorem hasSameApproximationNumbers_comp_left_of_adjoint_comp_self_comp
    {J : F →L[ℂ] G} {T : E →L[ℂ] F}
    (h : J.adjoint ∘L J ∘L T = T) :
    (J ∘L T).HasSameApproximationNumbers T :=
  ContinuousLinearMap.hasSameApproximationNumbers_of_norm_apply_eq _ _
    (norm_comp_left_apply_of_adjoint_comp_self_comp h)

end Approximation

section Modulus

universe u v w

variable {E : Type u} {F : Type v} {G : Type w}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- **The equisingularity identity.**  If `J` is isometric on the range of `T`
then `J T` and `T` have the *same* modulus.  Since a unitarily invariant norm is
a function of the modulus, the two operators are interchangeable inside any such
norm. -/
theorem modulus_comp_left_of_adjoint_comp_self_comp
    {J : F →L[ℂ] G} {T : E →L[ℂ] F}
    (h : J.adjoint ∘L J ∘L T = T) :
    (J ∘L T).modulus = T.modulus := by
  refine (ContinuousLinearMap.eq_modulus_of_nonneg_of_mul_self_eq
    T.modulus_nonneg ?_).symm
  rw [ContinuousLinearMap.modulus_mul_self,
    gram_comp_left_of_adjoint_comp_self_comp h]

end Modulus

section FunctionalCalculus

universe u w

variable {E : Type u} {G : Type w}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- A continuous function vanishing at `0` through the explicit factorisation
`f t = t * g t` gives `f(a) = a * g(a)`.  In particular the range of `f(a)` sits
inside the range of `a`, which is the geometric content: `f(a)` annihilates the
kernel of `a`. -/
theorem cfc_eq_mul_cfc_of_eq_id_mul
    (a : E →L[ℂ] E) (f g : ℝ → ℝ) (ha : IsSelfAdjoint a)
    (hfg : ∀ t ∈ spectrum ℝ a, f t = t * g t)
    (hg : ContinuousOn g (spectrum ℝ a)) :
    cfc f a = a * cfc g a := by
  rw [cfc_congr hfg, cfc_mul (fun t : ℝ => t) g a continuousOn_id hg,
    cfc_id' ℝ a]

/-- If `J` is isometric on the range of the self-adjoint operator `a`, it is
isometric on the range of `f(a)` for every `f` vanishing at the origin through a
continuous factorisation `f t = t * g t`.  This is the operator-theoretic form of
"`f(Θ)` annihilates `ker Θ`, and `J⋆J` is the identity on the support of `Θ`". -/
theorem adjoint_comp_self_comp_cfc
    {J : E →L[ℂ] G} {a : E →L[ℂ] E} (ha : IsSelfAdjoint a)
    (hJ : J.adjoint ∘L J ∘L a = a)
    (f g : ℝ → ℝ)
    (hfg : ∀ t ∈ spectrum ℝ a, f t = t * g t)
    (hg : ContinuousOn g (spectrum ℝ a)) :
    J.adjoint ∘L J ∘L cfc f a = cfc f a := by
  have hfa : cfc f a = a ∘L cfc g a := cfc_eq_mul_cfc_of_eq_id_mul a f g ha hfg hg
  calc J.adjoint ∘L J ∘L cfc f a
      = J.adjoint ∘L J ∘L (a ∘L cfc g a) := by rw [hfa]
    _ = (J.adjoint ∘L J ∘L a) ∘L cfc g a := by
        rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc]
    _ = a ∘L cfc g a := by rw [hJ]
    _ = cfc f a := hfa.symm

/-- **The equisingularity identity for a functional calculus vanishing at the
origin.**  If `J` is isometric on the range of the self-adjoint operator `a` and
`f t = t * g t` with `g` continuous on the spectrum, then `|J f(a)| = |f(a)|`.

This is the form used for principal angles: `a = Θ`, `J` the polar partial
isometry of the direct rotation, and `f` either `tan` or `t ↦ sin 2t`. -/
theorem modulus_comp_left_cfc
    {J : E →L[ℂ] G} {a : E →L[ℂ] E} (ha : IsSelfAdjoint a)
    (hJ : J.adjoint ∘L J ∘L a = a)
    (f g : ℝ → ℝ)
    (hfg : ∀ t ∈ spectrum ℝ a, f t = t * g t)
    (hg : ContinuousOn g (spectrum ℝ a)) :
    (J ∘L cfc f a).modulus = (cfc f a).modulus :=
  modulus_comp_left_of_adjoint_comp_self_comp
    (adjoint_comp_self_comp_cfc ha hJ f g hfg hg)

/-- The Gram form of `TauCeti.modulus_comp_left_cfc`. -/
theorem gram_comp_left_cfc
    {J : E →L[ℂ] G} {a : E →L[ℂ] E} (ha : IsSelfAdjoint a)
    (hJ : J.adjoint ∘L J ∘L a = a)
    (f g : ℝ → ℝ)
    (hfg : ∀ t ∈ spectrum ℝ a, f t = t * g t)
    (hg : ContinuousOn g (spectrum ℝ a)) :
    (J ∘L cfc f a).adjoint ∘L (J ∘L cfc f a) =
      (cfc f a).adjoint ∘L cfc f a :=
  gram_comp_left_of_adjoint_comp_self_comp
    (adjoint_comp_self_comp_cfc ha hJ f g hfg hg)

/-- The approximation-number form: the off-diagonal representative `J f(a)` and
the diagonal `f(a)` have the same singular-value sequence, hence the same value
under every unitarily invariant norm. -/
theorem hasSameApproximationNumbers_comp_left_cfc
    {J : E →L[ℂ] G} {a : E →L[ℂ] E} (ha : IsSelfAdjoint a)
    (hJ : J.adjoint ∘L J ∘L a = a)
    (f g : ℝ → ℝ)
    (hfg : ∀ t ∈ spectrum ℝ a, f t = t * g t)
    (hg : ContinuousOn g (spectrum ℝ a)) :
    (J ∘L cfc f a).HasSameApproximationNumbers (cfc f a) :=
  hasSameApproximationNumbers_comp_left_of_adjoint_comp_self_comp
    (adjoint_comp_self_comp_cfc ha hJ f g hfg hg)

end FunctionalCalculus

section Polar

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The polar partial isometry of `M` is isometric on the range of `|M|`.  This
is the hypothesis of the equisingularity identity in the case the principal-angle
application needs: `|M|` plays the role of `Θ` and `M.polarPartial` the role of
the direct rotation's polar factor `J`. -/
theorem adjoint_comp_self_comp_modulus (M : E →L[ℂ] F) :
    M.polarPartial.adjoint ∘L M.polarPartial ∘L M.modulus = M.modulus :=
  adjoint_comp_self_comp_of_starProjection (W := M.polarInitial)
    (M.adjoint_comp_polarPartial) M.modulus_apply_mem_polarInitial

/-- **The equisingularity identity for the polar factor.**  For `f` vanishing at
the origin through a continuous factorisation, the off-diagonal representative
`J f(|M|)` and the diagonal `f(|M|)` have the same modulus, hence the same value
under every unitarily invariant norm.

With `|M| = Θ` the principal-angle operator this is exactly the Davis--Kahan
step: the off-diagonal block `J f(Θ)` may be substituted for `f(Θ)` inside any
source norm, for `f = tan` and for `f = (sin 2 ·)`. -/
theorem modulus_polarPartial_comp_cfc_modulus (M : E →L[ℂ] F) (f g : ℝ → ℝ)
    (hfg : ∀ t ∈ spectrum ℝ M.modulus, f t = t * g t)
    (hg : ContinuousOn g (spectrum ℝ M.modulus)) :
    (M.polarPartial ∘L cfc f M.modulus).modulus = (cfc f M.modulus).modulus :=
  modulus_comp_left_cfc M.modulus_isSelfAdjoint
    (adjoint_comp_self_comp_modulus M) f g hfg hg

end Polar

end TauCeti
