/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.GradedLemmas

/-!
# Hypersurface section of a homogeneous prime

This file implements blueprint node **B01** of the algebra backend: for a homogeneous prime `Q`
of `P = MvPolynomial σ K` and a form `G ∉ Q` of degree `e`,

  `homHilbert (Q ⊔ (G)) t + homHilbert Q (t - e) = homHilbert Q t`   for `e ≤ t`.

Multiplication by the class `ḡ` of `G` is an injective `K`-linear map of the domain `P ⧸ Q`
(`Q` is prime and `G ∉ Q`) sending the image `V_{t-e}` of `P_{t-e}` into the image `V_t` of `P_t`;
its image is exactly the kernel of the factor map `V_t → P ⧸ (Q ⊔ (G))`
(`ker_factor_inf_map_eq_map_mulLeft`): a form `F` of degree `t` in `Q ⊔ (G)` is `q + u * G`, and
taking degree-`t` homogeneous components gives `F = q_t + u_{t-e} * G` with `q_t ∈ Q`. Rank–nullity
for the factor map restricted to `V_t` then gives the identity.

## Main declarations

* `Nikodym.LowerBound.ker_factor_inf_map_eq_map_mulLeft`: the kernel computation.
* `Nikodym.LowerBound.homHilbert_sup_span_singleton_add`: the identity above (blueprint B01).
-/

namespace Nikodym.LowerBound

open MvPolynomial Module

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K] {σ : Type*}

/-- Blueprint B01, kernel computation: for a homogeneous ideal `Q`, a form `G` of degree `e ≤ t`,
the part of the image `V_t` of `P_t` in `P ⧸ Q` killed by the factor map `P ⧸ Q → P ⧸ (Q ⊔ (G))`
is `ḡ • V_{t-e}`, the image of `V_{t-e}` under multiplication by the class of `G`. -/
theorem ker_factor_inf_map_eq_map_mulLeft {Q : Ideal (MvPolynomial σ K)}
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) {G : MvPolynomial σ K} {e : ℕ}
    (hG : G.IsHomogeneous e) {t : ℕ} (ht : e ≤ t) :
    LinearMap.ker (Ideal.Quotient.factorₐ K (le_sup_left : Q ≤ Q ⊔ Ideal.span {G})).toLinearMap ⊓
        (homogeneousSubmodule σ K t).map (Ideal.Quotient.mkₐ K Q).toLinearMap =
      ((homogeneousSubmodule σ K (t - e)).map (Ideal.Quotient.mkₐ K Q).toLinearMap).map
        (LinearMap.mulLeft K (Ideal.Quotient.mk Q G)) := by
  have hf : ∀ F : MvPolynomial σ K,
      Ideal.Quotient.factorₐ K (le_sup_left : Q ≤ Q ⊔ Ideal.span {G}) (Ideal.Quotient.mk Q F) =
        Ideal.Quotient.mk (Q ⊔ Ideal.span {G}) F := fun F ↦ by
    rw [Ideal.Quotient.factorₐ_apply, Ideal.Quotient.factor_mk]
  ext x
  simp only [Submodule.mem_inf, LinearMap.mem_ker, Submodule.mem_map, AlgHom.toLinearMap_apply,
    Ideal.Quotient.mkₐ_eq_mk, LinearMap.mulLeft_apply, mem_homogeneousSubmodule]
  constructor
  · rintro ⟨hx, F, hF, rfl⟩
    rw [hf, Ideal.Quotient.eq_zero_iff_mem] at hx
    obtain ⟨q, hq, z, hz, hFqz⟩ := Submodule.mem_sup.mp hx
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    have hcomp : homogeneousComponent t (u * G) = homogeneousComponent (t - e) u * G := by
      have h := homogeneousComponent_mul_of_isHomogeneous' hG (t - e) u
      rwa [Nat.sub_add_cancel ht] at h
    have hFeq : F = homogeneousComponent t q + homogeneousComponent (t - e) u * G := by
      rw [← hcomp, ← map_add, hFqz, homogeneousComponent_eq_self hF]
    refine ⟨Ideal.Quotient.mk Q (homogeneousComponent (t - e) u),
      ⟨homogeneousComponent (t - e) u, homogeneousComponent_isHomogeneous _ _, rfl⟩, ?_⟩
    rw [hFeq, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr (homogeneousComponent_mem_of_mem hQ hq t),
      zero_add, map_mul, mul_comm]
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨?_, G * u, ?_, map_mul _ _ _⟩
    · rw [← map_mul, hf, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_sup_right (Ideal.mul_mem_right u _ (Ideal.mem_span_singleton_self G))
    · have h := hG.mul hu
      rwa [Nat.add_sub_cancel' ht] at h

variable [Finite σ]

/-- Blueprint B01: **hypersurface section.** For a homogeneous prime `Q` of `MvPolynomial σ K` and
a form `G ∉ Q` of degree `e ≤ t`,
`homHilbert (Q ⊔ (G)) t + homHilbert Q (t - e) = homHilbert Q t`. Multiplication by the class of
`G` embeds `P_{t-e} ⧸ Q_{t-e}` into `P_t ⧸ Q_t` with image the kernel of the surjection onto
`P_t ⧸ (Q ⊔ (G))_t`. -/
theorem homHilbert_sup_span_singleton_add {Q : Ideal (MvPolynomial σ K)} [Q.IsPrime]
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ K)) {G : MvPolynomial σ K} {e : ℕ}
    (hG : G.IsHomogeneous e) (hGQ : G ∉ Q) {t : ℕ} (ht : e ≤ t) :
    homHilbert (Q ⊔ Ideal.span {G}) t + homHilbert Q (t - e) = homHilbert Q t := by
  set f := (Ideal.Quotient.factorₐ K (le_sup_left : Q ≤ Q ⊔ Ideal.span {G})).toLinearMap with hf
  set V : ℕ → Submodule K (MvPolynomial σ K ⧸ Q) := fun u ↦
    (homogeneousSubmodule σ K u).map (Ideal.Quotient.mkₐ K Q).toLinearMap with hV
  have hg0 : Ideal.Quotient.mk Q G ≠ 0 := fun h ↦ hGQ (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hμ : Function.Injective (LinearMap.mulLeft K (Ideal.Quotient.mk Q G)) :=
    mul_right_injective₀ hg0
  have h1 : homHilbert (Q ⊔ Ideal.span {G}) t = finrank K ((V t).map f) := by
    rw [homHilbert, map_mkₐ_eq_map_factor (le_sup_left : Q ≤ Q ⊔ Ideal.span {G})]
  haveI : Module.Finite K (V t) := Module.Finite.map _ _
  have h2 := LinearMap.finrank_range_add_finrank_ker (f ∘ₗ (V t).subtype)
  rw [LinearMap.range_comp, Submodule.range_subtype, LinearMap.ker_comp] at h2
  have h3 : finrank K ((LinearMap.ker f).comap (V t).subtype) =
      finrank K ↥(LinearMap.ker f ⊓ V t) := by
    rw [← (Submodule.comapSubtypeEquivOfLe (inf_le_right : LinearMap.ker f ⊓ V t ≤ V t)).finrank_eq,
      Submodule.comap_inf, Submodule.comap_subtype_self, inf_top_eq]
  have h4 : finrank K ↥((V (t - e)).map (LinearMap.mulLeft K (Ideal.Quotient.mk Q G))) =
      finrank K (V (t - e)) :=
    ((Submodule.equivMapOfInjective _ hμ _).finrank_eq).symm
  have h5 : LinearMap.ker f ⊓ V t =
      (V (t - e)).map (LinearMap.mulLeft K (Ideal.Quotient.mk Q G)) :=
    ker_factor_inf_map_eq_map_mulLeft hQ hG ht
  have h6 : homHilbert Q (t - e) = finrank K (V (t - e)) := rfl
  have h7 : homHilbert Q t = finrank K (V t) := rfl
  rw [h1, h6, h7, ← h2, h3, h5, h4]

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
