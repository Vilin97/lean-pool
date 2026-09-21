/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.CommonDomain

/-!
# Graph-core form of the unbounded residual hypothesis

The unbounded appendix may be read as specifying the residual identity on a
common dense operator core rather than requiring equality of the two full
composition domains.  The mathematically sufficient condition is graph-density
for the trial operator: every vector in `dom A₀` is approximated both in the
ambient norm and after applying `A₀`.

This module proves the closed-graph extension step explicitly.  If the bounded
residual identity holds on such a graph core, then the trial map sends all of
`dom A₀` into `dom A` and the same identity holds on the full trial domain.
Thus the accepted unbounded sine-theta theorem applies without strengthening a
source statement that was intended only on a core.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace
open Filter Topology

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

open TauCeti.DavisKahan

namespace PartialMap

/-- A linear subspace of the operator domain that is sequentially dense in the
graph norm.  The sequence formulation avoids installing a second topology on
the domain subtype while recording exactly the two convergences needed by the
closed-graph argument. -/
def IsGraphCore
    (A : E →ₗ.[𝕜] E)
    (D : Submodule 𝕜 A.domain) : Prop :=
  ∀ x : A.domain, ∃ u : ℕ → D,
    Tendsto (fun n => ((((u n : D) : A.domain) : E))) atTop (𝓝 (x : E)) ∧
    Tendsto (fun n => A ((u n : D) : A.domain))
      atTop (𝓝 (A x))

namespace IsGraphCore

omit [CompleteSpace E] in
/-- The full operator domain is a graph core. -/
theorem top (A : E →ₗ.[𝕜] E) :
    PartialMap.IsGraphCore A ⊤ := by
  intro x
  refine ⟨fun _ => ⟨x, Submodule.mem_top⟩, ?_, ?_⟩
  · simp
  · simp

omit [CompleteSpace E] in
/-- A graph core is ambiently dense in the operator domain: every domain vector
is an ambient-norm limit of vectors from the core. -/
theorem ambient_approximation
    {A : E →ₗ.[𝕜] E}
    {D : Submodule 𝕜 A.domain} (hD : PartialMap.IsGraphCore A D)
    (x : A.domain) :
    ∃ u : ℕ → D,
      Tendsto (fun n => ((((u n : D) : A.domain) : E))) atTop (𝓝 (x : E)) := by
  obtain ⟨u, hu, _⟩ := hD x
  exact ⟨u, hu⟩

end IsGraphCore
end PartialMap

/-- Residual data on a graph core of the trial operator. -/
structure CommonCoreResidualData
    (A : E →ₗ.[𝕜] E)
    (A₀ : F →ₗ.[𝕜] F)
    (X : F →L[𝕜] E) (R : F →L[𝕜] E) where
  core : Submodule 𝕜 A₀.domain
  graph_core : PartialMap.IsGraphCore A₀ core
  maps_core : ∀ x : core, X (((x : core) : A₀.domain) : F) ∈ A.domain
  residual_on_core : ∀ x : core,
    A
        ⟨X (((x : core) : A₀.domain) : F), maps_core x⟩ -
      X (A₀ ((x : core) : A₀.domain)) =
        R (((x : core) : A₀.domain) : F)

namespace CommonCoreResidualData

omit [CompleteSpace E] [CompleteSpace F] in
/-- The core residual identity extends to every vector in the trial domain.
This is the load-bearing closed-graph argument behind the literal appendix
formulation. -/
theorem extends_to_domain
    {A : E →ₗ.[𝕜] E}
    {A₀ : F →ₗ.[𝕜] F}
    {X : F →L[𝕜] E} {R : F →L[𝕜] E}
    (C : CommonCoreResidualData A A₀ X R)
    (hAclosed : A.IsClosed)
    (x : A₀.domain) :
    ∃ hx : X (x : F) ∈ A.domain,
      A ⟨X (x : F), hx⟩ - X (A₀ x) = R (x : F) := by
  obtain ⟨u, hu, hAu⟩ := C.graph_core x
  let xu : ℕ → A.domain := fun n =>
    ⟨X ((((u n : C.core) : A₀.domain) : F)), C.maps_core (u n)⟩
  have hX : Tendsto (fun n => ((xu n : A.domain) : E))
      atTop (𝓝 (X (x : F))) := by
    change Tendsto
      (fun n => X ((((u n : C.core) : A₀.domain) : F)))
      atTop (𝓝 (X (x : F)))
    exact (X.continuous.tendsto (x : F)).comp hu
  have hR : Tendsto
      (fun n => R ((((u n : C.core) : A₀.domain) : F)))
      atTop (𝓝 (R (x : F))) :=
    (R.continuous.tendsto (x : F)).comp hu
  have hXA₀ : Tendsto
      (fun n => X (A₀ ((u n : C.core) : A₀.domain)))
      atTop (𝓝 (X (A₀ x))) :=
    (X.continuous.tendsto (A₀ x)).comp hAu
  have hAseq : Tendsto (fun n => A (xu n))
      atTop (𝓝 (R (x : F) + X (A₀ x))) := by
    have hsum := hR.add hXA₀
    convert hsum using 1
    funext n
    change A
        ⟨X ((((u n : C.core) : A₀.domain) : F)), C.maps_core (u n)⟩ =
      R ((((u n : C.core) : A₀.domain) : F)) +
        X (A₀ ((u n : C.core) : A₀.domain))
    exact sub_eq_iff_eq_add.mp (C.residual_on_core (u n))
  have hgraph :
      (X (x : F), R (x : F) + X (A₀ x)) ∈
        Set.range (fun z : A.domain => ((z : E), A z)) :=
    ((TauCeti.LinearPMap.isClosed_iff_range_isClosed A).mp hAclosed).mem_of_tendsto
      (hX.prodMk_nhds hAseq)
      (Eventually.of_forall fun n => ⟨xu n, rfl⟩)
  rcases hgraph with ⟨z, hz⟩
  have hzX : (z : E) = X (x : F) := congrArg Prod.fst hz
  have hzA : A z = R (x : F) + X (A₀ x) :=
    congrArg Prod.snd hz
  have hx : X (x : F) ∈ A.domain := by
    rw [← hzX]
    exact z.property
  refine ⟨hx, ?_⟩
  have hsubtype : z = (⟨X (x : F), hx⟩ : A.domain) := Subtype.ext hzX
  have haction : A ⟨X (x : F), hx⟩ =
      R (x : F) + X (A₀ x) := by
    rw [← hsubtype]
    exact hzA
  rw [haction]
  abel

omit [CompleteSpace E] [CompleteSpace F] in
/-- Full-domain compatibility obtained from the graph-core hypothesis. -/
theorem maps_domain
    {A : E →ₗ.[𝕜] E}
    {A₀ : F →ₗ.[𝕜] F}
    {X : F →L[𝕜] E} {R : F →L[𝕜] E}
    (C : CommonCoreResidualData A A₀ X R) (hAclosed : A.IsClosed) :
    ∀ x : A₀.domain, X (x : F) ∈ A.domain := by
  intro x
  exact (C.extends_to_domain hAclosed x).choose

omit [CompleteSpace E] [CompleteSpace F] in
/-- Full-domain residual identity obtained from the graph-core hypothesis. -/
theorem residual_eq
    {A : E →ₗ.[𝕜] E}
    {A₀ : F →ₗ.[𝕜] F}
    {X : F →L[𝕜] E} {R : F →L[𝕜] E}
    (C : CommonCoreResidualData A A₀ X R) (hAclosed : A.IsClosed)
    (x : A₀.domain) :
    A ⟨X (x : F), C.maps_domain hAclosed x⟩ -
      X (A₀ x) = R (x : F) := by
  obtain ⟨hx, hEq⟩ := C.extends_to_domain hAclosed x
  have hsub :
      (⟨X (x : F), hx⟩ : A.domain) =
        ⟨X (x : F), C.maps_domain hAclosed x⟩ := Subtype.ext rfl
  simpa [hsub] using hEq

end CommonCoreResidualData

/-- Construct the accepted sine-theta bookkeeping package from a residual
identity available only on a graph core. -/
noncomputable def unboundedSinThetaDataOfCommonCore
    (A : E →ₗ.[𝕜] E)
    (A₀ : F →ₗ.[𝕜] F)
    (Λ₁ : G →ₗ.[𝕜] G)
    (X : F →L[𝕜] E) (F₁ : G →L[𝕜] E) (R : F →L[𝕜] E)
    (C : CommonCoreResidualData A A₀ X R) (hAclosed : A.IsClosed)
    (hF₁ : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain)
    (hintertwines : ∀ y : Λ₁.domain,
      A ⟨F₁ (y : G), hF₁ y⟩ = F₁ (Λ₁ y)) :
    UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G) where
  A := A
  A₀ := A₀
  Λ₁ := Λ₁
  X := X
  F₁ := F₁
  residual := R
  X_maps_domain := C.maps_domain hAclosed
  F₁_maps_domain := hF₁
  residual_eq := C.residual_eq hAclosed
  intertwines := hintertwines

omit [CompleteSpace G] [CompleteSpace E] [CompleteSpace F] in
/-- The constructed data carries the supplied residual unchanged.

Downstream statements quote the source residual `R`, while the accepted engine
returns the residual field of the constructed package; without this projection
the two do not match syntactically. -/
@[simp]
theorem unboundedSinThetaDataOfCommonCore_residual
    (A : E →ₗ.[𝕜] E)
    (A₀ : F →ₗ.[𝕜] F)
    (Λ₁ : G →ₗ.[𝕜] G)
    (X : F →L[𝕜] E) (F₁ : G →L[𝕜] E) (R : F →L[𝕜] E)
    (C : CommonCoreResidualData A A₀ X R) (hAclosed : A.IsClosed)
    (hF₁ : ∀ y : Λ₁.domain, F₁ (y : G) ∈ A.domain)
    (hintertwines : ∀ y : Λ₁.domain,
      A ⟨F₁ (y : G), hF₁ y⟩ = F₁ (Λ₁ y)) :
    (unboundedSinThetaDataOfCommonCore A A₀ Λ₁ X F₁ R C hAclosed hF₁
      hintertwines).residual = R := rfl

end ExactSinTheta
end DavisKahan
end TauCeti
