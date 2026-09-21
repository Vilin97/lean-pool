/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Domain-aware infrastructure for partial linear maps

Reusable algebra for unbounded operators represented canonically by Mathlib's
`LinearPMap`: domain transport, extension, symmetry, graph norms, relative
bounds, and elementary real resolvent predicates.

The declarations deliberately take raw partial maps.  Closedness, dense domain,
and self-adjointness are separate hypotheses supplied by the theorem that needs
them; they are not bundled into a parallel operator structure.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `DavisKahan/SpectralTheory/ClosedOperator/Basic.lean`.
* Extraction class: **representation migration**.  The original declarations
  were methods of a bundled `ClosedOperator` record -- a `LinearPMap` with
  dense domain and closed graph as fields, since deleted downstream; this
  module restates their reusable content directly over Mathlib `LinearPMap`.
* Spectra influence: none.  This module imports only Mathlib.
-/

public section

namespace TauCeti
namespace LinearPMap

open scoped InnerProductSpace
open Filter Topology

universe u v w

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- `LinearPMap.IsClosed` is stated on the graph, while the canonical
reducing-restriction API states closedness as a range.  The two are the same set,
so this is a reindexing lemma used in both directions. -/
theorem isClosed_iff_range_isClosed
    (f : E →ₗ.[𝕜] F) :
    f.IsClosed ↔ IsClosed (Set.range fun x : f.domain => ((x : E), f x)) := by
  have hgraph : (f.graph : Set (E × F)) =
      Set.range (fun x : f.domain => ((x : E), f x)) := by
    ext q
    simp only [SetLike.mem_coe, LinearPMap.mem_graph_iff, Set.mem_range]
    constructor
    · rintro ⟨y, hy1, hy2⟩
      exact ⟨y, Prod.ext hy1 hy2⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, congrArg Prod.fst hy, congrArg Prod.snd hy⟩
  change IsClosed (f.graph : Set (E × F)) ↔ _
  rw [hgraph]

/-- Two partial linear maps have the same operator domain. -/
def SameDomain (A B : E →ₗ.[𝕜] E) : Prop :=
  A.domain = B.domain

/-- Equality of partial-map domains is reflexive. -/
@[refl] theorem SameDomain.refl (A : E →ₗ.[𝕜] E) : SameDomain A A := (rfl)
/-- Equality of partial-map domains is symmetric. -/
@[symm] theorem SameDomain.symm {A B : E →ₗ.[𝕜] E}
    (h : SameDomain A B) : SameDomain B A :=
  Eq.symm h

/-- Equality of partial-map domains is transitive. -/
@[trans] theorem SameDomain.trans {A B C : E →ₗ.[𝕜] E}
    (hAB : SameDomain A B) (hBC : SameDomain B C) : SameDomain A C :=
  Eq.trans hAB hBC

-- `@[expose]` is deliberate: this is a `Prop`-valued abbreviation for a ∀-statement and
-- consumers *apply* it (`h x : X x ∈ A.domain`), which is unfolding by definition. The
-- `api-design` carve-out for a consumer that must unfold, not blanket exposure.
/-- A bounded map sends the domain of `B` into the domain of `A`. -/
@[expose]
def MapsDomainTo (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F)
    (X : F →L[𝕜] E) : Prop :=
  ∀ x : B.domain, X (x : F) ∈ A.domain

/-- The identity bounded map preserves every partial-map domain. -/
theorem MapsDomainTo.id (A : E →ₗ.[𝕜] E) :
    MapsDomainTo A A (ContinuousLinearMap.id 𝕜 E) := by
  intro x
  -- states the goal with the local definition unfolded, in the shape the next step
  -- needs.
  change (x : E) ∈ A.domain
  exact x.property

/-- Domain transport composes with bounded maps. -/
theorem MapsDomainTo.comp
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F} {C : G →ₗ.[𝕜] G}
    {X : F →L[𝕜] E} {Y : G →L[𝕜] F}
    (hX : MapsDomainTo A B X) (hY : MapsDomainTo B C Y) :
    MapsDomainTo A C (X ∘L Y) := by
  intro z
  exact hX ⟨Y (z : G), hY z⟩

-- `@[expose]` for the same reason as `MapsDomainTo` above: consumers *apply* the
-- statement (`h x hx : A x ∈ U`), which is unfolding by definition.
/-- A subspace is invariant under a partial linear map on its domain. -/
@[expose]
def InvariantSubspace
    (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E) : Prop :=
  ∀ x : A.domain, (x : E) ∈ U → A x ∈ U

/-- A subspace reduces a partial linear map when both orthogonal projections
preserve its domain and both summands are invariant. -/
def ReducesSubspace
    (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] : Prop :=
  (∀ x : A.domain, U.starProjection (x : E) ∈ A.domain) ∧
  (∀ x : A.domain, Uᗮ.starProjection (x : E) ∈ A.domain) ∧
  InvariantSubspace A U ∧ InvariantSubspace A Uᗮ

/-- Build a `ReducesSubspace` from its four components.  The definition is a
conjunction whose body is not exposed across module boundaries, so this is the
supported way for a consumer to construct one. -/
theorem ReducesSubspace.of_components
    {A : E →ₗ.[𝕜] E} {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (h₁ : ∀ x : A.domain, U.starProjection (x : E) ∈ A.domain)
    (h₂ : ∀ x : A.domain, Uᗮ.starProjection (x : E) ∈ A.domain)
    (h₃ : InvariantSubspace A U) (h₄ : InvariantSubspace A Uᗮ) :
    ReducesSubspace A U := ⟨h₁, h₂, h₃, h₄⟩

namespace ReducesSubspace

/-- The projection onto a reducing subspace preserves the partial-map domain. -/
theorem projection_mem_domain
    {A : E →ₗ.[𝕜] E} {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (h : ReducesSubspace A U) (x : A.domain) :
    U.starProjection (x : E) ∈ A.domain :=
  h.1 x

/-- The complementary projection of a reducing subspace preserves the domain. -/
theorem orthogonalProjection_mem_domain
    {A : E →ₗ.[𝕜] E} {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (h : ReducesSubspace A U) (x : A.domain) :
    Uᗮ.starProjection (x : E) ∈ A.domain :=
  h.2.1 x

/-- The selected summand of a reducing subspace is invariant. -/
theorem invariant
    {A : E →ₗ.[𝕜] E} {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (h : ReducesSubspace A U) : InvariantSubspace A U :=
  h.2.2.1

/-- The complementary summand of a reducing subspace is invariant. -/
theorem orthogonal_invariant
    {A : E →ₗ.[𝕜] E} {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (h : ReducesSubspace A U) : InvariantSubspace A Uᗮ :=
  h.2.2.2

/-- Orthogonal complementation preserves the reducing-subspace property. -/
theorem orthogonal
    {A : E →ₗ.[𝕜] E} {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (h : ReducesSubspace A U) : ReducesSubspace A Uᗮ := by
  refine ⟨h.orthogonalProjection_mem_domain, ?_,
    h.orthogonal_invariant, ?_⟩
  · intro x
    simpa only [Submodule.orthogonal_orthogonal] using
      h.projection_mem_domain x
  · intro x hx
    rw [Submodule.orthogonal_orthogonal] at hx ⊢
    exact h.invariant x hx

end ReducesSubspace

/-- The operator domain inside a reducing subspace. -/
def reducingRestrictionDomain
    (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E) : Submodule 𝕜 U where
  carrier := {x | (x : E) ∈ A.domain}
  zero_mem' := A.domain.zero_mem
  add_mem' hx hy := A.domain.add_mem hx hy
  smul_mem' c _ hx := A.domain.smul_mem c hx

/-- Membership in the restricted domain is membership of the ambient vector in
`A.domain`: restricting the domain to `U` adds no condition beyond lying in `U`,
which the subtype already carries. -/
@[simp] theorem mem_reducingRestrictionDomain_iff
    (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E) (x : U) :
    x ∈ reducingRestrictionDomain A U ↔ (x : E) ∈ A.domain :=
  Iff.rfl

/-- A restricted-domain vector viewed in the ambient partial-map domain. -/
def reducingRestrictionDomainToAmbient
    (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E)
    (x : reducingRestrictionDomain A U) : A.domain :=
  ⟨((x : reducingRestrictionDomain A U) : U), x.property⟩

/-- Viewing a restricted-domain vector in the ambient domain does not move it.
The two subtypes differ only in which membership proof they carry. -/
@[simp] theorem reducingRestrictionDomainToAmbient_coe
    (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E)
    (x : reducingRestrictionDomain A U) :
    ((reducingRestrictionDomainToAmbient A U x : A.domain) : E) =
      ((x : reducingRestrictionDomain A U) : U) := (rfl)
/-- Action of a partial map restricted to a reducing subspace. -/
def reducingRestrictionLinearMap
    (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : ReducesSubspace A U) :
    reducingRestrictionDomain A U →ₗ[𝕜] U where
  toFun x :=
    ⟨A (reducingRestrictionDomainToAmbient A U x),
      hred.invariant (reducingRestrictionDomainToAmbient A U x)
        (((x : reducingRestrictionDomain A U) : U).property)⟩
  map_add' x y := by
    apply Subtype.ext
    simp only [Submodule.coe_add]
    rw [show reducingRestrictionDomainToAmbient A U (x + y) =
      reducingRestrictionDomainToAmbient A U x +
        reducingRestrictionDomainToAmbient A U y from rfl]
    exact A.toFun.map_add _ _
  map_smul' c x := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, RingHom.id_apply]
    rw [show reducingRestrictionDomainToAmbient A U (c • x) =
      c • reducingRestrictionDomainToAmbient A U x from rfl]
    exact A.toFun.map_smul c _

/-- The restricted map acts by the ambient one: `A|_U x = A x`, read through the
two coercions.  This is where `ReducesSubspace` earns its keep — it is what
makes `A x` land back in `U` so the corestriction typechecks. -/
@[simp] theorem coe_reducingRestrictionLinearMap
    (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : ReducesSubspace A U) (x : reducingRestrictionDomain A U) :
    ((reducingRestrictionLinearMap A U hred x : U) : E) =
      A (reducingRestrictionDomainToAmbient A U x) := (rfl)
/-- Projection of an ambient domain vector into the restricted domain. -/
noncomputable def projectDomainToReducingRestriction
    (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : ReducesSubspace A U) (x : A.domain) :
    reducingRestrictionDomain A U :=
  ⟨⟨U.starProjection (x : E), U.starProjection_apply_mem (x : E)⟩,
    hred.projection_mem_domain x⟩

/-- Projecting an ambient domain vector into the restricted domain is the
orthogonal projection onto `U`.  It stays in the domain because `A` reduces
`U`. -/
@[simp] theorem coe_projectDomainToReducingRestriction
    (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : ReducesSubspace A U) (x : A.domain) :
    (((projectDomainToReducingRestriction A U hred x :
        reducingRestrictionDomain A U) : U) : E) =
      U.starProjection (x : E) := (rfl)
/-- The partial map induced on a reducing subspace.  Density and closedness
are properties supplied separately by the theorem using this construction. -/
noncomputable def reducingRestriction
    (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : ReducesSubspace A U) : U →ₗ.[𝕜] U where
  domain := reducingRestrictionDomain A U
  toFun := reducingRestrictionLinearMap A U hred

/-- The restricted partial map has the restricted domain, definitionally. -/
@[simp] theorem reducingRestriction_domain
    (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : ReducesSubspace A U) :
    (reducingRestriction A U hred).domain = reducingRestrictionDomain A U := (rfl)
/-- Membership in the restricted domain, stated without naming the intermediate
domain submodule.  This is the form a consumer outside this module can use: the
restricted operator's domain is `U`-vectors that already lay in `A.domain`. -/
theorem mem_reducingRestriction_domain_iff
    (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : ReducesSubspace A U) (x : U) :
    x ∈ (reducingRestriction A U hred).domain ↔ (x : E) ∈ A.domain := Iff.rfl

/-- **The reducing restriction acts by the ambient partial map**, read through
the two coercions and indexed by an ambient-domain proof rather than by the
restricted domain's subtype.  `coe_reducingRestrictionLinearMap` says the same
about the underlying linear map; this is the partial-map form, and it is what a
consumer needs to compute with a restriction it did not build. -/
theorem coe_reducingRestriction_apply
    (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : ReducesSubspace A U) (x : U) (hx : (x : E) ∈ A.domain) :
    ((reducingRestriction A U hred
        ⟨x, (mem_reducingRestriction_domain_iff A U hred x).mpr hx⟩ : U) : E) =
      A ⟨(x : E), hx⟩ := (rfl)
/-- A dense partial-map domain remains dense after restriction to a reducing
subspace. -/
theorem reducingRestriction_dense
    (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : ReducesSubspace A U) (hA : Dense (A.domain : Set E)) :
    Dense ((reducingRestriction A U hred).domain : Set U) := by
  rw [reducingRestriction_domain, dense_iff_closure_eq]
  ext u
  simp only [Set.mem_univ, iff_true]
  have hu : (u : E) ∈ closure (A.domain : Set E) := by
    rw [hA.closure_eq]
    trivial
  obtain ⟨s, hs, hs_lim⟩ := mem_closure_iff_seq_limit.mp hu
  let t : ℕ → U := fun n =>
    ⟨U.starProjection (s n), U.starProjection_apply_mem (s n)⟩
  refine mem_closure_iff_seq_limit.mpr ⟨t, ?_, ?_⟩
  · intro n
    exact hred.projection_mem_domain ⟨s n, hs n⟩
  · have hlim := (U.starProjection.continuous.tendsto (u : E)).comp hs_lim
    have hfix : U.starProjection (u : E) = (u : E) :=
      Submodule.starProjection_eq_self_iff.mpr u.property
    -- names the sequence explicitly so the limit lemma matches its shape.
    change Tendsto (fun n => t n) atTop (𝓝 u)
    apply tendsto_subtype_rng.mpr
    simpa [t, hfix, Function.comp_def] using hlim

/-- Closedness of the graph is preserved by restriction to a reducing
subspace.  The hypothesis is stated as a graph range to make it directly
applicable to compatibility records as well as raw partial maps. -/
theorem reducingRestriction_closedGraph
    (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : ReducesSubspace A U)
    (hA : IsClosed (Set.range fun x : A.domain => ((x : E), A x))) :
    IsClosed (Set.range fun x : (reducingRestriction A U hred).domain =>
      (((x : (reducingRestriction A U hred).domain) : U),
        reducingRestriction A U hred x)) := by
  let coords : U × U → E × E := fun p => ((p.1 : E), (p.2 : E))
  have hcoords : Continuous coords :=
    (U.subtypeL.continuous.comp continuous_fst).prodMk
      (U.subtypeL.continuous.comp continuous_snd)
  rw [show Set.range (fun x : (reducingRestriction A U hred).domain =>
      (((x : (reducingRestriction A U hred).domain) : U),
        reducingRestriction A U hred x)) =
      coords ⁻¹' (Set.range fun x : A.domain => ((x : E), A x)) by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨reducingRestrictionDomainToAmbient A U x, rfl⟩
    · rintro ⟨x, hx⟩
      have hx0 : (x : E) = (p.1 : E) := congrArg Prod.fst hx
      have hx1 : A x = (p.2 : E) := congrArg Prod.snd hx
      have hpdom : (p.1 : E) ∈ A.domain := hx0 ▸ x.property
      let u : (reducingRestriction A U hred).domain := ⟨p.1, hpdom⟩
      refine ⟨u, Prod.ext rfl ?_⟩
      apply Subtype.ext
      -- states the goal with the local definition unfolded, in the shape the next step
      -- needs.
      change A (reducingRestrictionDomainToAmbient A U u) = (p.2 : E)
      have hxu : reducingRestrictionDomainToAmbient A U u = x := by
        apply Subtype.ext
        exact hx0.symm
      simpa [hxu] using hx1]
  exact hA.preimage hcoords

/-- Adjoint-domain membership of a reducing restriction is exactly ambient
adjoint-domain membership for the included vector. -/
theorem mem_reducingRestriction_adjoint_domain_iff
    (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [CompleteSpace E] [CompleteSpace U]
    (hred : ReducesSubspace A U) (y : U) :
    y ∈ (reducingRestriction A U hred).adjoint.domain ↔
      (y : E) ∈ A.adjoint.domain := by
  rw [LinearPMap.mem_adjoint_domain_iff,
    LinearPMap.mem_adjoint_domain_iff]
  constructor
  · intro hy
    have hproject : Continuous (projectDomainToReducingRestriction A U hred) := by
      have hproj : Continuous fun x : A.domain =>
          U.starProjection (x : E) :=
        U.starProjection.continuous.comp A.domain.subtypeL.continuous
      have hprojU : Continuous fun x : A.domain =>
          (⟨U.starProjection (x : E),
            U.starProjection_apply_mem (x : E)⟩ : U) :=
        hproj.subtype_mk _
      exact hprojU.subtype_mk fun x => hred.projection_mem_domain x
    have hcomp : Continuous fun x : A.domain =>
        ⟪y, (reducingRestriction A U hred)
          (projectDomainToReducingRestriction A U hred x)⟫_𝕜 :=
      hy.comp hproject
    have hfun : (fun x : A.domain =>
        ⟪y, (reducingRestriction A U hred)
          (projectDomainToReducingRestriction A U hred x)⟫_𝕜) =
        fun x : A.domain => ⟪(y : E), A x⟫_𝕜 := by
      funext x
      let xu : A.domain :=
        ⟨U.starProjection (x : E), hred.projection_mem_domain x⟩
      let xo : A.domain :=
        ⟨Uᗮ.starProjection (x : E), hred.orthogonalProjection_mem_domain x⟩
      have hxsplit : x = xu + xo := by
        apply Subtype.ext
        exact (U.starProjection_add_starProjection_orthogonal (x : E)).symm
      have horth : ⟪(y : E), A xo⟫_𝕜 = 0 := by
        exact Submodule.inner_right_of_mem_orthogonal y.property
          (hred.orthogonal_invariant xo
            (Uᗮ.starProjection_apply_mem (x : E)))
      calc
        ⟪y, (reducingRestriction A U hred)
            (projectDomainToReducingRestriction A U hred x)⟫_𝕜 =
            ⟪(y : E), A xu⟫_𝕜 := (rfl)
        _ = ⟪(y : E), A xu + A xo⟫_𝕜 := by
              rw [inner_add_right, horth, add_zero]
        _ = ⟪(y : E), A (xu + xo)⟫_𝕜 := by
              congr 1
              exact (A.toFun.map_add xu xo).symm
        _ = ⟪(y : E), A x⟫_𝕜 := by rw [← hxsplit]
    rw [hfun] at hcomp
    exact hcomp
  · intro hy
    have hincl : Continuous fun x : (reducingRestriction A U hred).domain =>
        reducingRestrictionDomainToAmbient A U x := by
      have hcoe : Continuous fun x : (reducingRestriction A U hred).domain =>
          (((x : (reducingRestriction A U hred).domain) : U) : E) :=
        U.subtypeL.continuous.comp
          (reducingRestriction A U hred).domain.subtypeL.continuous
      exact hcoe.subtype_mk fun x => x.property
    have hcomp := hy.comp hincl
    have hcomp' : Continuous fun x : (reducingRestriction A U hred).domain =>
        ⟪(y : E), A (reducingRestrictionDomainToAmbient A U x)⟫_𝕜 := hcomp
    exact hcomp'

/-- Symmetry passes to a reducing restriction of a partial map. -/
theorem reducingRestriction_isSymmetric
    (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : ReducesSubspace A U)
    (hA : ∀ x y : A.domain,
      ⟪A x, (y : E)⟫_𝕜 = ⟪(x : E), A y⟫_𝕜) :
    ∀ x y : (reducingRestriction A U hred).domain,
      ⟪reducingRestriction A U hred x, (y : U)⟫_𝕜 =
        ⟪(x : U), reducingRestriction A U hred y⟫_𝕜 := by
  intro x y
  exact hA (reducingRestrictionDomainToAmbient A U x)
    (reducingRestrictionDomainToAmbient A U y)

/-- A linear map on a submodule has a bounded extension to the ambient space. -/
structure BoundedExtension (D : Submodule 𝕜 F) (T : D →ₗ[𝕜] E) where
  operator : F →L[𝕜] E
  agrees : ∀ x : D, operator (x : F) = T x

/-- Extension relation for partial linear maps. -/
def Extends (A B : E →ₗ.[𝕜] E) : Prop :=
  ∃ hdom : A.domain ≤ B.domain,
    ∀ x : A.domain, B ⟨(x : E), hdom x.property⟩ = A x

/-- Every partial linear map extends itself. -/
@[refl] theorem Extends.refl (A : E →ₗ.[𝕜] E) : Extends A A := by
  refine ⟨le_rfl, ?_⟩
  intro x
  rfl

/-- Extension of partial linear maps is transitive. -/
@[trans] theorem Extends.trans {A B C : E →ₗ.[𝕜] E}
    (hAB : Extends A B) (hBC : Extends B C) : Extends A C := by
  rcases hAB with ⟨hdomAB, hactAB⟩
  rcases hBC with ⟨hdomBC, hactBC⟩
  refine ⟨hdomAB.trans hdomBC, ?_⟩
  intro x
  calc
    C ⟨(x : E), hdomBC (hdomAB x.property)⟩ =
        B ⟨(x : E), hdomAB x.property⟩ :=
      hactBC ⟨(x : E), hdomAB x.property⟩
    _ = A x := hactAB x

/-- Domain obtained by pulling a partial-map domain back through a continuous
linear equivalence. -/
def pullbackDomain (A : E →ₗ.[𝕜] E) (e : E ≃L[𝕜] E) : Submodule 𝕜 E :=
  A.domain.comap e.toLinearMap

/-- `x` lies in the pulled-back domain exactly when `e x` lies in the original
one — the pullback domain is the preimage, so the condition is on the image. -/
@[simp] theorem mem_pullbackDomain_iff
    (A : E →ₗ.[𝕜] E) (e : E ≃L[𝕜] E) (x : E) :
    x ∈ pullbackDomain A e ↔ e x ∈ A.domain :=
  Iff.rfl

/-- A vector in a pulled-back domain, transported to the original domain. -/
def pullbackDomainToOriginal
    (A : E →ₗ.[𝕜] E) (e : E ≃L[𝕜] E) :
    pullbackDomain A e →ₗ[𝕜] A.domain where
  toFun x := ⟨e (x : E), x.property⟩
  map_add' x y := by
    apply Subtype.ext
    exact e.map_add (x : E) (y : E)
  map_smul' c x := by
    apply Subtype.ext
    exact e.map_smul c (x : E)

/-- Transporting a pulled-back domain vector applies `e`.  Unlike the reducing
restriction, this map genuinely moves the vector. -/
@[simp] theorem pullbackDomainToOriginal_coe
    (A : E →ₗ.[𝕜] E) (e : E ≃L[𝕜] E)
    (x : pullbackDomain A e) :
    ((pullbackDomainToOriginal A e x : A.domain) : E) = e (x : E) := (rfl)
/-- Action of the partial map pulled back through a continuous linear
equivalence. -/
def pullbackLinearMap (A : E →ₗ.[𝕜] E) (e : E ≃L[𝕜] E) :
    pullbackDomain A e →ₗ[𝕜] E :=
  e.symm.toLinearMap.comp (A.toFun.comp (pullbackDomainToOriginal A e))

/-- The pulled-back action is `e⁻¹ ∘ A ∘ e`: push forward by `e`, apply `A`,
pull back by `e⁻¹`.  Conjugation, written on the domain subtypes. -/
@[simp] theorem pullbackLinearMap_apply
    (A : E →ₗ.[𝕜] E) (e : E ≃L[𝕜] E)
    (x : pullbackDomain A e) :
    pullbackLinearMap A e x =
      e.symm (A (pullbackDomainToOriginal A e x)) := (rfl)
/-- Pull a partial map back through a continuous linear equivalence.  Density
and graph closedness are separate properties of the resulting partial map. -/
noncomputable def pullback (A : E →ₗ.[𝕜] E) (e : E ≃L[𝕜] E) : E →ₗ.[𝕜] E where
  domain := pullbackDomain A e
  toFun := pullbackLinearMap A e

/-- The pulled-back partial map has the pulled-back domain, definitionally. -/
@[simp] theorem pullback_domain
    (A : E →ₗ.[𝕜] E) (e : E ≃L[𝕜] E) :
    (pullback A e).domain = pullbackDomain A e := (rfl)
/-- Pullback through a continuous linear equivalence preserves a dense domain. -/
theorem pullback_dense
    (A : E →ₗ.[𝕜] E) (e : E ≃L[𝕜] E)
    (hA : Dense (A.domain : Set E)) :
    Dense ((pullback A e).domain : Set E) := by
  rw [pullback_domain]
  have himage : Dense (e.symm '' (A.domain : Set E)) :=
    (e.symm.toHomeomorph.isDenseEmbedding.dense_image).2 hA
  rw [show ((pullbackDomain A e : Submodule 𝕜 E) : Set E) =
      e.symm '' (A.domain : Set E) by
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy]
  exact himage

/-- Pullback through a continuous linear equivalence preserves graph
closedness. -/
theorem pullback_closedGraph
    (A : E →ₗ.[𝕜] E) (e : E ≃L[𝕜] E)
    (hA : IsClosed (Set.range fun x : A.domain => ((x : E), A x))) :
    IsClosed (Set.range fun x : (pullback A e).domain =>
      ((x : E), pullback A e x)) := by
  let coords : E × E → E × E := fun p => (e p.1, e p.2)
  have hcoords : Continuous coords := by fun_prop
  rw [show Set.range (fun x : (pullback A e).domain =>
      ((x : E), pullback A e x)) =
      coords ⁻¹' (Set.range fun x : A.domain => ((x : E), A x)) by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨pullbackDomainToOriginal A e x, ?_⟩
      apply Prod.ext
      · rfl
      · change A (pullbackDomainToOriginal A e x) =
          e (pullbackLinearMap A e x)
        -- `rw [pullbackLinearMap_apply]` cannot fire: `x : (pullback A e).domain` is only
        -- definitionally `pullbackDomain A e`, and `rw`'s pattern match is syntactic.
        -- `exact` checks up to defeq, so it goes through where the rewrite does not.
        exact (e.apply_symm_apply _).symm
    · rintro ⟨x, hx⟩
      have hfst : (x : E) = e p.1 := congrArg Prod.fst hx
      have hsnd : A x = e p.2 := congrArg Prod.snd hx
      have hp1 : p.1 ∈ pullbackDomain A e := by
        -- states the goal with the local definition unfolded, in the shape the next step
        -- needs.
        change e p.1 ∈ A.domain
        rw [← hfst]
        exact x.property
      let z : (pullback A e).domain := ⟨p.1, hp1⟩
      have hz : pullbackDomainToOriginal A e z = x := by
        apply Subtype.ext
        exact hfst.symm
      refine ⟨z, Prod.ext rfl ?_⟩
      apply e.injective
      -- `pullback` has a `_domain` lemma but no `_apply` one, and an `_apply` cannot be
      -- stated without a cast: `x : (pullback A e).domain` does not reduce to
      -- `pullbackDomain A e` unless the body is exposed. Tried; it fails to elaborate.
      -- `change` names the unfolded form instead.
      change e (pullbackLinearMap A e z) = e p.2
      -- See the `exact` above: `z : (pullback A e).domain` blocks the syntactic rewrite.
      refine (e.apply_symm_apply _).trans ?_
      exact (congrArg (fun y : A.domain => A y) hz).trans hsnd]
  exact hA.preimage hcoords

/-- A bounded operator is unitary when it is norm preserving and surjective. -/
def IsUnitaryOperator (W : E →L[𝕜] E) : Prop :=
  (∀ x, ‖W x‖ = ‖x‖) ∧ Function.Surjective W

/-- Two partial maps are unitarily equivalent when mutually inverse unitary
maps transport both domains and both actions. -/
def UnitaryEquivalent (A B : E →ₗ.[𝕜] E)
    (W Winv : E →L[𝕜] E) : Prop :=
  IsUnitaryOperator W ∧ IsUnitaryOperator Winv ∧
  Winv ∘L W = ContinuousLinearMap.id 𝕜 E ∧
  W ∘L Winv = ContinuousLinearMap.id 𝕜 E ∧
  ∃ hWdom : ∀ x : A.domain, W (x : E) ∈ B.domain,
  ∃ hWinvdom : ∀ y : B.domain, Winv (y : E) ∈ A.domain,
    (∀ x : A.domain,
      B ⟨W (x : E), hWdom x⟩ = W (A x)) ∧
    (∀ y : B.domain,
      A ⟨Winv (y : E), hWinvdom y⟩ = Winv (B y))

/-- Pullback through a unitary equivalence is unitarily equivalent to the
original partial map. -/
theorem pullback_unitaryEquivalent
    (A : E →ₗ.[𝕜] E) (e : E ≃L[𝕜] E)
    (he : IsUnitaryOperator e.toContinuousLinearMap) :
    UnitaryEquivalent (pullback A e) A e.toContinuousLinearMap
      e.symm.toContinuousLinearMap := by
  have hesymm : IsUnitaryOperator e.symm.toContinuousLinearMap := by
    constructor
    · intro y
      have h := he.1 (e.symm y)
      simpa using h.symm
    · exact e.symm.surjective
  have hleft : e.symm.toContinuousLinearMap ∘L e.toContinuousLinearMap =
      ContinuousLinearMap.id 𝕜 E := by
    apply ContinuousLinearMap.ext
    intro x
    simp
  have hright : e.toContinuousLinearMap ∘L e.symm.toContinuousLinearMap =
      ContinuousLinearMap.id 𝕜 E := by
    apply ContinuousLinearMap.ext
    intro x
    simp
  refine ⟨he, hesymm, hleft, hright, ?_⟩
  let hWdom : ∀ x : (pullback A e).domain,
      e (x : E) ∈ A.domain := fun x => x.property
  refine ⟨hWdom, ?_⟩
  let hWinvdom : ∀ y : A.domain,
      e.symm (y : E) ∈ (pullback A e).domain := fun y => by
        -- states the goal with the local definition unfolded, in the shape the next step
        -- needs.
        change e (e.symm (y : E)) ∈ A.domain
        simpa only [e.apply_symm_apply] using y.property
  refine ⟨hWinvdom, ?_, ?_⟩
  · intro x
    -- `pullback` has a `_domain` lemma but no `_apply` one, and an `_apply` cannot be
    -- stated without a cast: `x : (pullback A e).domain` does not reduce to
    -- `pullbackDomain A e` unless the body is exposed. Tried; it fails to elaborate.
    -- `change` names the unfolded form instead.
    change A ⟨e (x : E), hWdom x⟩ = e ((pullback A e) x)
    -- `pullback` has a `_domain` lemma but no `_apply` one, and an `_apply` cannot be
    -- stated without a cast: `x : (pullback A e).domain` does not reduce to
    -- `pullbackDomain A e` unless the body is exposed. Tried; it fails to elaborate.
    -- `change` names the unfolded form instead.
    change A ⟨e (x : E), hWdom x⟩ = e (pullbackLinearMap A e x)
    -- See the `exact` in `isClosed_pullback`: `x : (pullback A e).domain` blocks the
    -- syntactic rewrite, but the two sides are still definitionally equal.
    exact (e.apply_symm_apply _).symm
  · intro y
    -- `pullback` has a `_domain` lemma but no `_apply` one, and an `_apply` cannot be
    -- stated without a cast: `x : (pullback A e).domain` does not reduce to
    -- `pullbackDomain A e` unless the body is exposed. Tried; it fails to elaborate.
    -- `change` names the unfolded form instead.
    change (pullback A e) ⟨e.symm (y : E), hWinvdom y⟩ = e.symm (A y)
    -- `pullback` has a `_domain` lemma but no `_apply` one, and an `_apply` cannot be
    -- stated without a cast: `x : (pullback A e).domain` does not reduce to
    -- `pullbackDomain A e` unless the body is exposed. Tried; it fails to elaborate.
    -- `change` names the unfolded form instead.
    change pullbackLinearMap A e ⟨e.symm (y : E), hWinvdom y⟩ = e.symm (A y)
    rw [pullbackLinearMap_apply]
    congr 2
    apply Subtype.ext
    simp

/-- The explicit product domain of two partial maps, transported to the
`L²` Hilbert direct sum. -/
noncomputable def directSumDomain
    (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) :
    Submodule 𝕜 (WithLp 2 (E × F)) :=
  (A.domain.prod B.domain).comap
    (WithLp.linearEquiv 2 𝕜 (E × F)).toLinearMap

/-- A vector lies in the direct-sum domain exactly when each coordinate lies in
the corresponding domain.  The `WithLp 2` wrapper carries the Hilbert norm and
changes nothing about membership. -/
@[simp] theorem mem_directSumDomain_iff
    (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (z : WithLp 2 (E × F)) :
    z ∈ directSumDomain A B ↔
      WithLp.fst z ∈ A.domain ∧ WithLp.snd z ∈ B.domain :=
  Iff.rfl

/-- First coordinate of a direct-sum domain vector. -/
def directSumDomainFst (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F)
    (z : directSumDomain A B) : A.domain :=
  ⟨WithLp.fst (z : WithLp 2 (E × F)),
    (mem_directSumDomain_iff A B z).mp z.property |>.1⟩

/-- Second coordinate of a direct-sum domain vector. -/
def directSumDomainSnd (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F)
    (z : directSumDomain A B) : B.domain :=
  ⟨WithLp.snd (z : WithLp 2 (E × F)),
    (mem_directSumDomain_iff A B z).mp z.property |>.2⟩

/-- First-coordinate extraction as a linear map on a direct-sum domain. -/
def directSumDomainFstLinearMap (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) :
    directSumDomain A B →ₗ[𝕜] A.domain where
  toFun := directSumDomainFst A B
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- Second-coordinate extraction as a linear map on a direct-sum domain. -/
def directSumDomainSndLinearMap (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) :
    directSumDomain A B →ₗ[𝕜] B.domain where
  toFun := directSumDomainSnd A B
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- Componentwise partial-map action on a direct-sum domain. -/
noncomputable def directSumLinearMap
    (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) :
    directSumDomain A B →ₗ[𝕜] WithLp 2 (E × F) :=
  (WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap.comp
    ((A.toFun.comp
      (directSumDomainFstLinearMap A B)).prod
     (B.toFun.comp
      (directSumDomainSndLinearMap A B)))

/-- The direct sum of two partial maps.  Density and closedness remain
separate properties. -/
noncomputable def directSum
    (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) :
    WithLp 2 (E × F) →ₗ.[𝕜] WithLp 2 (E × F) where
  domain := directSumDomain A B
  toFun := directSumLinearMap A B

/-- The direct-sum partial map has the direct-sum domain, definitionally. -/
@[simp] theorem directSum_domain
    (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) :
    (directSum A B).domain = directSumDomain A B := (rfl)
/-- The direct sum of dense partial-map domains is dense. -/
theorem directSum_dense
    (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F)
    (hA : Dense (A.domain : Set E)) (hB : Dense (B.domain : Set F)) :
    Dense ((directSum A B).domain : Set (WithLp 2 (E × F))) := by
  rw [directSum_domain]
  have hprod : Dense ((A.domain : Set E) ×ˢ (B.domain : Set F)) := hA.prod hB
  have himage : Dense
      ((WithLp.homeomorphProd 2 E F).symm ''
        ((A.domain : Set E) ×ˢ (B.domain : Set F))) :=
    ((WithLp.homeomorphProd 2 E F).symm.isDenseEmbedding.dense_image).2 hprod
  rw [show ((directSumDomain A B : Submodule 𝕜 (WithLp 2 (E × F))) :
      Set (WithLp 2 (E × F))) =
      (WithLp.homeomorphProd 2 E F).symm ''
        ((A.domain : Set E) ×ˢ (B.domain : Set F)) by
    ext z
    constructor
    · intro hz
      exact ⟨WithLp.ofLp z, hz, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact hp]
  exact himage

/-- The direct sum of closed partial-map graphs is closed. -/
theorem directSum_closedGraph
    (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F)
    (hA : IsClosed (Set.range fun x : A.domain => ((x : E), A x)))
    (hB : IsClosed (Set.range fun y : B.domain => ((y : F), B y))) :
    IsClosed (Set.range fun z : (directSum A B).domain =>
      ((z : WithLp 2 (E × F)), directSum A B z)) := by
  let coords : (WithLp 2 (E × F) × WithLp 2 (E × F)) →
      ((E × E) × (F × F)) := fun p =>
    ((WithLp.fst p.1, WithLp.fst p.2),
      (WithLp.snd p.1, WithLp.snd p.2))
  have hcoords : Continuous coords := by fun_prop
  have hclosed : IsClosed
      ((Set.range fun x : A.domain => ((x : E), A x)) ×ˢ
       (Set.range fun y : B.domain => ((y : F), B y))) := hA.prod hB
  rw [show Set.range (fun z : (directSum A B).domain =>
      ((z : WithLp 2 (E × F)), directSum A B z)) =
      coords ⁻¹' ((Set.range fun x : A.domain => ((x : E), A x)) ×ˢ
        (Set.range fun y : B.domain => ((y : F), B y))) by
    ext p
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨⟨directSumDomainFst A B z, by ext <;> rfl⟩,
        ⟨directSumDomainSnd A B z, by ext <;> rfl⟩⟩
    · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      have hxf : (x : E) = WithLp.fst p.1 := congrArg Prod.fst hx
      have hxa : A x = WithLp.fst p.2 := congrArg Prod.snd hx
      have hyf : (y : F) = WithLp.snd p.1 := congrArg Prod.fst hy
      have hyb : B y = WithLp.snd p.2 := congrArg Prod.snd hy
      let z : (directSum A B).domain := ⟨p.1,
        (mem_directSumDomain_iff A B p.1).2
          ⟨hxf ▸ x.property, hyf ▸ y.property⟩⟩
      have hzx : directSumDomainFst A B z = x := Subtype.ext hxf.symm
      have hzy : directSumDomainSnd A B z = y := Subtype.ext hyf.symm
      refine ⟨z, Prod.ext rfl ?_⟩
      apply (WithLp.linearEquiv 2 𝕜 (E × F)).injective
      apply Prod.ext
      · change A (directSumDomainFst A B z) = WithLp.fst p.2
        simpa [hzx] using hxa
      · change B (directSumDomainSnd A B z) = WithLp.snd p.2
        simpa [hzy] using hyb]
  exact hclosed.preimage hcoords

/-- A partial linear map is symmetric on its operator domain. -/
def IsSymmetric (A : E →ₗ.[𝕜] E) : Prop :=
  ∀ x y : A.domain, ⟪A x, (y : E)⟫_𝕜 = ⟪(x : E), A y⟫_𝕜

/-- Characteristic form of symmetry for a partial linear map.

This theorem is the public unfolding interface for `IsSymmetric`.  Keep downstream
modules on this theorem rather than depending on definitional transparency across
module boundaries. -/
theorem isSymmetric_iff (A : E →ₗ.[𝕜] E) :
    IsSymmetric A ↔
      ∀ x y : A.domain, ⟪A x, (y : E)⟫_𝕜 = ⟪(x : E), A y⟫_𝕜 := by
  rfl

/-- A self-adjoint partial map is symmetric on its operator domain.

The converse fails: symmetry compares `A` with `A†` only on `dom A`, while
self-adjointness also asserts that the two domains agree. -/
theorem isSymmetric_of_isSelfAdjoint [CompleteSpace E] {A : E →ₗ.[𝕜] E}
    (hA : _root_.IsSelfAdjoint A) : IsSymmetric A := by
  have hformal := LinearPMap.adjoint_isFormalAdjoint hA.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp hA] at hformal
  intro x y
  exact hformal x y

/-- A self-adjoint partial map restricts to a self-adjoint partial map on every
reducing subspace. -/
theorem reducingRestriction_isSelfAdjoint
    (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [CompleteSpace E] [CompleteSpace U]
    (hred : ReducesSubspace A U) (hDense : Dense (A.domain : Set E))
    (hA : _root_.IsSelfAdjoint A) :
    _root_.IsSelfAdjoint (reducingRestriction A U hred) := by
  let R := reducingRestriction A U hred
  -- states the goal against the bundled predicate so the structure lemma applies.
  change _root_.IsSelfAdjoint R
  rw [LinearPMap.isSelfAdjoint_def] at hA ⊢
  refine LinearPMap.ext_iff.mpr ⟨?_, ?_⟩
  · ext y
    -- states the goal against the bundled predicate so the structure lemma applies.
    change y ∈ R.adjoint.domain ↔ y ∈ R.domain
    rw [show R = reducingRestriction A U hred by rfl,
      mem_reducingRestriction_adjoint_domain_iff A U hred]
    rw [hA]
    rfl
  · intro y hyAdj hyR
    let yAdj : U := R.adjoint ⟨y, hyAdj⟩
    let yAct : U := R ⟨y, hyR⟩
    have hformal := LinearPMap.adjoint_isFormalAdjoint
      (reducingRestriction_dense A U hred hDense) ⟨y, hyAdj⟩
    have hAformal := LinearPMap.adjoint_isFormalAdjoint hDense
    rw [hA] at hAformal
    have hAsymm : IsSymmetric A := by
      intro x z
      exact hAformal x z
    have hsymm := reducingRestriction_isSymmetric A U hred hAsymm
    have hinner : (fun x : U => ⟪yAdj, x⟫_𝕜) =
        fun x : U => ⟪yAct, x⟫_𝕜 := by
      apply Continuous.ext_on (reducingRestriction_dense A U hred hDense)
      · exact continuous_const.inner continuous_id
      · exact continuous_const.inner continuous_id
      · intro x hx
        let xDom : R.domain := ⟨x, hx⟩
        calc
          ⟪yAdj, x⟫_𝕜 = ⟪y, R xDom⟫_𝕜 := by
            simpa [yAdj, xDom] using hformal xDom
          _ = ⟪yAct, x⟫_𝕜 := by
            simpa [yAct, xDom, R] using (hsymm ⟨y, hyR⟩ xDom).symm
    have hzero : ⟪yAdj - yAct, yAdj - yAct⟫_𝕜 = 0 := by
      rw [inner_sub_left, congrFun hinner (yAdj - yAct), sub_self]
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)

/-- Graph norm associated with a partial linear map. -/
noncomputable def graphNorm (A : E →ₗ.[𝕜] E) (x : A.domain) : ℝ :=
  Real.sqrt (‖(x : E)‖ ^ 2 + ‖A x‖ ^ 2)

/-- The graph norm is nonnegative. -/
theorem graphNorm_nonneg (A : E →ₗ.[𝕜] E) (x : A.domain) :
    0 ≤ graphNorm A x :=
  Real.sqrt_nonneg _

/-- Squaring the graph norm recovers its defining sum of squares. -/
theorem graphNorm_sq (A : E →ₗ.[𝕜] E) (x : A.domain) :
    graphNorm A x ^ 2 = ‖(x : E)‖ ^ 2 + ‖A x‖ ^ 2 := by
  unfold graphNorm
  exact Real.sq_sqrt (by positivity)

/-- The ambient norm is controlled by the graph norm. -/
theorem norm_coe_le_graphNorm (A : E →ₗ.[𝕜] E) (x : A.domain) :
    ‖(x : E)‖ ≤ graphNorm A x := by
  rw [graphNorm]
  exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖A x‖])

/-- The operator-value norm is controlled by the graph norm. -/
theorem norm_apply_le_graphNorm (A : E →ₗ.[𝕜] E) (x : A.domain) :
    ‖A x‖ ≤ graphNorm A x := by
  rw [graphNorm]
  exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖(x : E)‖])

/-- Add a bounded ambient perturbation to a partial map on its original
domain.  Closedness remains a separate property of the resulting map. -/
-- `@[expose]` here is deliberate and minimal: the `_apply` lemma below cannot be
-- *stated* without `.domain` reducing, since it indexes its argument by this map's
-- domain and applies the underlying map to it. That is the `api-design` rubric's own
-- carve-out — a consumer that must unfold — not the blanket exposure it rejects.
@[expose]
noncomputable def addBounded (A : E →ₗ.[𝕜] E) (V : E →L[𝕜] E) :
    E →ₗ.[𝕜] E where
  domain := A.domain
  toFun := A.toFun + V.toLinearMap.domRestrict A.domain

/-- A bounded perturbation leaves the domain unchanged — `V` is everywhere
defined, so `A + V` is defined exactly where `A` is.  This is what makes
perturbation arguments comparable on the nose rather than up to a domain
inclusion. -/
@[simp] theorem addBounded_domain (A : E →ₗ.[𝕜] E) (V : E →L[𝕜] E) :
    (TauCeti.LinearPMap.addBounded A V).domain = A.domain := (rfl)
/-- The perturbed map acts by `A x + V x`. -/
@[simp] theorem addBounded_apply (A : E →ₗ.[𝕜] E) (V : E →L[𝕜] E)
    (x : (TauCeti.LinearPMap.addBounded A V).domain) :
    TauCeti.LinearPMap.addBounded A V x = A x + V (x : E) := (rfl)
/-- **A bounded perturbation is undone by its negation, on the nose.**

`addBounded` leaves the domain alone, so `(A + V) + (-V)` is `A` as a partial map
rather than merely an extension of it.  This is what lets a theorem stated with
the roles of the unperturbed and perturbed operators exchanged be applied without
any domain bookkeeping. -/
@[simp] theorem addBounded_neg_cancel (A : E →ₗ.[𝕜] E) (V : E →L[𝕜] E) :
    TauCeti.LinearPMap.addBounded (TauCeti.LinearPMap.addBounded A V) (-V) = A := by
  refine LinearPMap.ext rfl fun x hf hg => ?_
  change A ⟨x, hf⟩ + V x + (-V) x = A ⟨x, hg⟩
  simp

/-- A bounded left inverse for the real shift of a partial map. -/
def LeftShiftedInverseBound (A : E →ₗ.[𝕜] E) (c s : ℝ) : Prop :=
  ∃ J : E →L[𝕜] E,
    (∀ x : A.domain,
      J (A x - ((c : ℝ) : 𝕜) • (x : E)) = (x : E)) ∧
    ‖J‖ ≤ s⁻¹

/-- A bounded two-sided inverse for the real shift of a partial map, with the
domain transport required by the right-inverse leg. -/
def TwoSidedShiftedInverseBound (A : E →ₗ.[𝕜] E) (c s : ℝ) : Prop :=
  ∃ J : E →L[𝕜] E, ∃ hdom : ∀ z : E, J z ∈ A.domain,
    (∀ x : A.domain,
      J (A x - ((c : ℝ) : 𝕜) • (x : E)) = (x : E)) ∧
    (∀ z : E, A ⟨J z, hdom z⟩ - ((c : ℝ) : 𝕜) • J z = z) ∧
    ‖J‖ ≤ s⁻¹

/-- A two-sided shifted inverse supplies its left-inverse component. -/
theorem TwoSidedShiftedInverseBound.leftShiftedInverseBound
    {A : E →ₗ.[𝕜] E} {c s : ℝ}
    (h : TwoSidedShiftedInverseBound A c s) :
    LeftShiftedInverseBound A c s := by
  obtain ⟨J, _hdom, hleft, _hright, hnorm⟩ := h
  exact ⟨J, hleft, hnorm⟩

/-- Relative boundedness of a domain-defined perturbation with respect to a
partial linear map. -/
def RelativelyBounded (A : E →ₗ.[𝕜] E)
    (V : A.domain →ₗ[𝕜] E) (a b : ℝ) : Prop :=
  ∀ x, ‖V x‖ ≤ a * ‖(x : E)‖ + b * ‖A x‖

namespace RelativelyBounded

/-- The zero perturbation has zero relative bound. -/
theorem zero (A : E →ₗ.[𝕜] E) :
    RelativelyBounded A (0 : A.domain →ₗ[𝕜] E) 0 0 := by
  intro x
  simp

/-- Relative bounds may be weakened by increasing either coefficient. -/
theorem mono {A : E →ₗ.[𝕜] E}
    {V : A.domain →ₗ[𝕜] E} {a b a' b' : ℝ}
    (hV : RelativelyBounded A V a b)
    (haa' : a ≤ a') (hbb' : b ≤ b') :
    RelativelyBounded A V a' b' := by
  intro x
  exact (hV x).trans <| add_le_add
    (mul_le_mul_of_nonneg_right haa' (norm_nonneg (x : E)))
    (mul_le_mul_of_nonneg_right hbb' (norm_nonneg (A x)))

/-- Relative bounds add under addition of perturbations. -/
theorem add {A : E →ₗ.[𝕜] E}
    {V W : A.domain →ₗ[𝕜] E} {a b c d : ℝ}
    (hV : RelativelyBounded A V a b)
    (hW : RelativelyBounded A W c d) :
    RelativelyBounded A (V + W) (a + c) (b + d) := by
  intro x
  calc
    ‖(V + W) x‖ ≤ ‖V x‖ + ‖W x‖ := norm_add_le _ _
    _ ≤ (a * ‖(x : E)‖ + b * ‖A x‖) +
        (c * ‖(x : E)‖ + d * ‖A x‖) :=
      add_le_add (hV x) (hW x)
    _ = (a + c) * ‖(x : E)‖ + (b + d) * ‖A x‖ := by ring

/-- Relative bounds scale by the norm of the scalar. -/
theorem smul {A : E →ₗ.[𝕜] E}
    {V : A.domain →ₗ[𝕜] E} {a b : ℝ}
    (hV : RelativelyBounded A V a b) (c : 𝕜) :
    RelativelyBounded A (c • V) (‖c‖ * a) (‖c‖ * b) := by
  intro x
  rw [LinearMap.smul_apply, norm_smul]
  calc
    ‖c‖ * ‖V x‖ ≤ ‖c‖ * (a * ‖(x : E)‖ + b * ‖A x‖) :=
      mul_le_mul_of_nonneg_left (hV x) (norm_nonneg c)
    _ = (‖c‖ * a) * ‖(x : E)‖ + (‖c‖ * b) * ‖A x‖ := by ring

/-- Relative bounds are preserved by negation. -/
theorem neg {A : E →ₗ.[𝕜] E}
    {V : A.domain →ₗ[𝕜] E} {a b : ℝ}
    (hV : RelativelyBounded A V a b) :
    RelativelyBounded A (-V) a b := by
  simpa using hV.smul (-1 : 𝕜)

/-- Relative bounds add under subtraction of perturbations. -/
theorem sub {A : E →ₗ.[𝕜] E}
    {V W : A.domain →ₗ[𝕜] E} {a b c d : ℝ}
    (hV : RelativelyBounded A V a b)
    (hW : RelativelyBounded A W c d) :
    RelativelyBounded A (V - W) (a + c) (b + d) := by
  simpa [sub_eq_add_neg] using hV.add hW.neg

/-- Restricting a bounded ambient operator to the domain gives relative bound
`(‖V‖, 0)`. -/
theorem domRestrict (A : E →ₗ.[𝕜] E) (V : E →L[𝕜] E) :
    RelativelyBounded A (V.toLinearMap.domRestrict A.domain) ‖V‖ 0 := by
  intro x
  simpa using V.le_opNorm (x : E)

end RelativelyBounded

/-- Real resolvent set of a partial linear map.  A parameter belongs to the set
when the shifted map has a bounded two-sided inverse with explicit domain
transport for the right-inverse leg. -/
def realResolventSet (A : E →ₗ.[𝕜] E) : Set ℝ :=
  {lam : ℝ | ∃ R : E →L[𝕜] E,
      (∀ x : A.domain, R (A x - (lam : 𝕜) • (x : E)) = (x : E)) ∧
      (∀ y : E, ∃ h : R y ∈ A.domain,
        A ⟨R y, h⟩ - (lam : 𝕜) • R y = y)}

/-- Unfolds real resolvent membership through a stable public API.

`realResolventSet` is intentionally kept abstract across module boundaries; downstream
proofs should use this theorem instead of depending on definitional transparency. -/
theorem mem_realResolventSet_iff {A : E →ₗ.[𝕜] E} {lam : ℝ} :
    lam ∈ realResolventSet A ↔
      ∃ R : E →L[𝕜] E,
        (∀ x : A.domain, R (A x - (lam : 𝕜) • (x : E)) = (x : E)) ∧
        (∀ y : E, ∃ h : R y ∈ A.domain,
          A ⟨R y, h⟩ - (lam : 𝕜) • R y = y) :=
  Iff.rfl

/-- Real spectrum defined as the complement of `realResolventSet`. -/
def realSpectrum (A : E →ₗ.[𝕜] E) : Set ℝ :=
  (realResolventSet A)ᶜ

/-- A real scalar is spectral exactly when it is not a real resolvent point. -/
@[simp] theorem mem_realSpectrum_iff {A : E →ₗ.[𝕜] E} {lam : ℝ} :
    lam ∈ realSpectrum A ↔ lam ∉ realResolventSet A :=
  Iff.rfl

/-- **A real eigenvalue is a real spectral point.**  A left inverse of the shifted map
would have to send `0` back to the eigenvector, so no such bounded inverse exists.

This is the introduction rule for `realSpectrum`: every other lemma about it either
consumes membership or proves a containment, and a containment is vacuously true of an
operator with no spectrum at all.  Only the surjectivity half of `realResolventSet` is
unused here, so the hypotheses are the weakest possible — no closedness, no dense domain,
and no symmetry. -/
theorem mem_realSpectrum_of_eigenvector {A : E →ₗ.[𝕜] E} {lam : ℝ} {x : A.domain}
    (hx : (x : E) ≠ 0) (heig : A x = (lam : 𝕜) • (x : E)) :
    lam ∈ realSpectrum A := by
  intro hres
  obtain ⟨R, hleft, -⟩ := hres
  have hzero : R (A x - (lam : 𝕜) • (x : E)) = (x : E) := hleft x
  rw [heig, sub_self, map_zero] at hzero
  exact hx hzero.symm

/-- Spectral-set separation for two partial maps, possibly on different Hilbert
spaces. -/
def SpectralSetsSeparated (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F)
    (s t : Set ℝ) (d : ℝ) : Prop :=
  ∀ a ∈ realSpectrum A, a ∈ s →
    ∀ b ∈ realSpectrum B, b ∈ t → d ≤ |a - b|

/-- Spectral-set separation is symmetric in the two maps. -/
theorem SpectralSetsSeparated.symm
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {s t : Set ℝ} {d : ℝ}
    (h : SpectralSetsSeparated A B s t d) :
    SpectralSetsSeparated B A t s d := by
  intro b hb ht a ha hs
  simpa [abs_sub_comm] using h a ha hs b hb ht

/-- Weakening the required gap preserves spectral-set separation. -/
theorem SpectralSetsSeparated.mono_gap
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {s t : Set ℝ} {d e : ℝ}
    (h : SpectralSetsSeparated A B s t d) (hed : e ≤ d) :
    SpectralSetsSeparated A B s t e := by
  intro a ha hs b hb ht
  exact hed.trans (h a ha hs b hb ht)

/-- Restricting either selected spectral set preserves separation. -/
theorem SpectralSetsSeparated.mono_sets
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {s s' t t' : Set ℝ} {d : ℝ}
    (h : SpectralSetsSeparated A B s t d)
    (hs : s' ⊆ s) (ht : t' ⊆ t) :
    SpectralSetsSeparated A B s' t' d := by
  intro a ha has' b hb hbt'
  exact h a ha (hs has') b hb (ht hbt')

end LinearPMap
end TauCeti

end
