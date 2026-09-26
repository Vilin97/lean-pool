/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Theorem61Universal

/-! # Common Domain -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# The common-domain formulation used in the unbounded appendix

The appendix to Davis--Kahan 1970 states the unbounded residual hypothesis by
requiring `(A + H) E₀` and `E₀ A₀` to have a common dense domain, with the
residual bounded there and extended continuously.  Because `E₀` is bounded,
the domain of `E₀ A₀` is exactly `dom A₀`; hence the literal source condition is
that the pullback of `dom A` through `E₀` equals `dom A₀`.

The previously accepted theorem needs only the forward inclusion.  This module
records the exact equality, proves the two formulations agree on the paper
inputs, and delegates to the stronger accepted theorem.  No arbitrary smaller
core is introduced: equality only on an unspecified dense core would not in
general determine the closed-operator product used by the theorem.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- Domain of the composition of a closed operator with a bounded map on the
right. -/
def boundedPullbackDomain
    (A : E →ₗ.[𝕜] E)
    (X : F →L[𝕜] E) : Set F :=
  {x | X x ∈ A.domain}

omit [CompleteSpace E] [CompleteSpace F] in
/-- Membership in the bounded pullback domain, in terms of the underlying vector. -/
@[simp]
theorem mem_boundedPullbackDomain
    (A : E →ₗ.[𝕜] E)
    (X : F →L[𝕜] E) (x : F) :
    x ∈ boundedPullbackDomain A X ↔ X x ∈ A.domain :=
  Iff.rfl

/-- Exact source-paper domain condition for the trial map. -/
def HasCommonDomain
    (A : E →ₗ.[𝕜] E)
    (A₀ : F →ₗ.[𝕜] F)
    (X : F →L[𝕜] E) : Prop :=
  boundedPullbackDomain A X = A₀.domain

namespace HasCommonDomain

omit [CompleteSpace E] [CompleteSpace F] in
/-- Pointwise form of the common-domain equality. -/
theorem mem_iff
    {A : E →ₗ.[𝕜] E}
    {A₀ : F →ₗ.[𝕜] F}
    {X : F →L[𝕜] E} (h : HasCommonDomain A A₀ X) (x : F) :
    X x ∈ A.domain ↔ x ∈ A₀.domain := by
  change x ∈ boundedPullbackDomain A X ↔ x ∈ A₀.domain
  rw [h]
  exact SetLike.mem_coe

omit [CompleteSpace E] [CompleteSpace F] in
/-- The exact source condition implies the forward domain compatibility used
by the accepted theorem. -/
theorem maps_domain
    {A : E →ₗ.[𝕜] E}
    {A₀ : F →ₗ.[𝕜] F}
    {X : F →L[𝕜] E} (h : HasCommonDomain A A₀ X) :
    ∀ x : A₀.domain, X (x : F) ∈ A.domain := by
  intro x
  exact (h.mem_iff (x : F)).2 x.property

omit [CompleteSpace E] [CompleteSpace F] in
/-- The common domain is dense because it is the domain of the densely defined
trial operator. -/
theorem dense
    {A : E →ₗ.[𝕜] E}
    {A₀ : F →ₗ.[𝕜] F}
    {X : F →L[𝕜] E} (h : HasCommonDomain A A₀ X)
    (hA₀ : Dense ((A₀.domain : Submodule 𝕜 F) : Set F)) :
    Dense (boundedPullbackDomain A X) := by
  rw [h]
  exact hA₀

end HasCommonDomain

/-- Construct the accepted bookkeeping package from the exact appendix
hypotheses.  The residual identity is stated on the common domain, identified
with `dom A₀` by `hcommon`. -/
noncomputable def unboundedSinThetaDataOfCommonDomain
    (A : E →ₗ.[𝕜] E)
    (A₀ : F →ₗ.[𝕜] F)
    (Λ₁ : G →ₗ.[𝕜] G)
    (X : F →L[𝕜] E) (F₁ : G →L[𝕜] E) (R : F →L[𝕜] E)
    (hcommon : HasCommonDomain A A₀ X)
    (hF₁ : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain)
    (hR : ∀ x : F, (hx : X x ∈ A.domain) → (hx₀ : x ∈ A₀.domain) →
      A ⟨X x, hx⟩ - X (A₀ ⟨x, hx₀⟩) = R x)
    (hintertwines : ∀ y : Λ₁.domain,
      A ⟨F₁ (y : G), hF₁ y⟩ = F₁ (Λ₁ y)) :
    UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G) where
  A := A
  A₀ := A₀
  Λ₁ := Λ₁
  X := X
  F₁ := F₁
  residual := R
  X_maps_domain := hcommon.maps_domain
  F₁_maps_domain := hF₁
  residual_eq := by
    intro x
    exact hR (x : F) (hcommon.maps_domain x) x.property
  intertwines := hintertwines

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace G] in
/-- The constructed data carries the supplied residual unchanged.

Downstream statements quote the source residual `R`, while the accepted engine
returns the residual field of the constructed package; without this projection
the two do not match syntactically. -/
@[simp]
theorem unboundedSinThetaDataOfCommonDomain_residual
    (A : E →ₗ.[𝕜] E)
    (A₀ : F →ₗ.[𝕜] F)
    (Λ₁ : G →ₗ.[𝕜] G)
    (X : F →L[𝕜] E) (F₁ : G →L[𝕜] E) (R : F →L[𝕜] E)
    (hcommon : HasCommonDomain A A₀ X)
    (hF₁ : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain)
    (hR : ∀ x : F, (hx : X x ∈ A.domain) → (hx₀ : x ∈ A₀.domain) →
      A ⟨X x, hx⟩ - X (A₀ ⟨x, hx₀⟩) = R x)
    (hintertwines : ∀ y : Λ₁.domain,
      A ⟨F₁ (y : G), hF₁ y⟩ = F₁ (Λ₁ y)) :
    (unboundedSinThetaDataOfCommonDomain A A₀ Λ₁ X F₁ R
      hcommon hF₁ hR hintertwines).residual = R := rfl

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace G] in
/-- The constructed data remembers the exact paper common-domain equality. -/
theorem unboundedSinThetaDataOfCommonDomain_hasCommonDomain
    (A : E →ₗ.[𝕜] E)
    (A₀ : F →ₗ.[𝕜] F)
    (Λ₁ : G →ₗ.[𝕜] G)
    (X : F →L[𝕜] E) (F₁ : G →L[𝕜] E) (R : F →L[𝕜] E)
    (hcommon : HasCommonDomain A A₀ X)
    (hF₁ : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain)
    (hR : ∀ x : F, (hx : X x ∈ A.domain) → (hx₀ : x ∈ A₀.domain) →
      A ⟨X x, hx⟩ - X (A₀ ⟨x, hx₀⟩) = R x)
    (hintertwines : ∀ y : Λ₁.domain,
      A ⟨F₁ (y : G), hF₁ y⟩ = F₁ (Λ₁ y)) :
    HasCommonDomain
      (unboundedSinThetaDataOfCommonDomain A A₀ Λ₁ X F₁ R
        hcommon hF₁ hR hintertwines).A
      (unboundedSinThetaDataOfCommonDomain A A₀ Λ₁ X F₁ R
        hcommon hF₁ hR hintertwines).A₀
      (unboundedSinThetaDataOfCommonDomain A A₀ Λ₁ X F₁ R
        hcommon hF₁ hR hintertwines).X :=
  hcommon

end ExactSinTheta
end DavisKahan
end TauCeti
