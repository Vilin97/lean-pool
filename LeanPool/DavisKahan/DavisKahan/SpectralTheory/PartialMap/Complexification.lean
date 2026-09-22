/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.PartialMap.RealSpectrum
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Complexification.Subspace
import LeanPool.DavisKahan.DavisKahan.Sylvester.Gap
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent

/-! # Complexification -/

open TauCeti.DavisKahan.Sylvester

/-!
# Complexification of real closed operators

This file transports the domain, action, graph, adjoint relation, form bounds,
resolvent, and domain-aware Sylvester equation of a real closed operator to the
concrete complexification of its Hilbert space.

The construction is coordinatewise.  The complexified domain consists of
vectors whose real and imaginary coordinates both lie in the original domain,
and the operator applies the original map to those two coordinates.  The graph
proof is the product closed-graph proof transported through the L2 coordinate
homeomorphism.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace
open Filter Topology

noncomputable section

universe v

namespace PartialMapComplexification

open TauCeti.RealComplexification
-- `Basic` moved to `ForTauCeti`; `Subspace` (and `complexifySubmodule`) is still here, so the
-- namespace is split across the two libraries and both halves have to be opened.
open TauCeti.DavisKahan.Foundation.RealComplexification

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Local shorthand for the complexified ambient space.  This is notation
rather than an abbreviation so that the underlying real space is resolved from
the ambient section variable at each use site instead of becoming an
uninferable implicit argument. -/
local notation "Eℂ" => RealComplexification E
local notation "Fℂ" => RealComplexification F

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- The real coordinate is continuous: it is the first projection composed
with the L2 coordinate homeomorphism. -/
theorem continuous_re : Continuous (re : Eℂ → E) :=
  continuous_fst.comp (WithLp.homeomorphProd 2 E E).continuous

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- The imaginary coordinate is continuous. -/
theorem continuous_im : Continuous (im : Eℂ → E) :=
  continuous_snd.comp (WithLp.homeomorphProd 2 E E).continuous

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Each coordinate norm is bounded by the L2 norm. -/
theorem norm_im_le (z : Eℂ) : ‖im z‖ ≤ ‖z‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), RealComplexification.norm_sq]
  nlinarith [sq_nonneg ‖re z‖]

/-- Coordinatewise complexification of a real closed-operator domain. -/
def domain (A : E →ₗ.[ℝ] E) :
    Submodule ℂ Eℂ :=
  complexifySubmodule A.domain

omit [CompleteSpace E] in
/-- Membership in the complexified domain, in terms of the two coordinates. -/
@[simp] theorem mem_domain_iff
    (A : E →ₗ.[ℝ] E)
    (z : Eℂ) :
    z ∈ domain A ↔ re z ∈ A.domain ∧ im z ∈ A.domain := by
  rfl

/-- Real coordinate of a vector in the complexified operator domain. -/
def domainRe
    (A : E →ₗ.[ℝ] E)
    (z : domain A) : A.domain :=
  ⟨re (z : Eℂ), (mem_domain_iff A z).mp z.property |>.1⟩

/-- Imaginary coordinate of a vector in the complexified operator domain. -/
def domainIm
    (A : E →ₗ.[ℝ] E)
    (z : domain A) : A.domain :=
  ⟨im (z : Eℂ), (mem_domain_iff A z).mp z.property |>.2⟩

/-- Coordinatewise action on the complexified domain. -/
def linearMap
    (A : E →ₗ.[ℝ] E) :
    domain A →ₗ[ℂ] Eℂ where
  toFun z := mk (A (domainRe A z))
    (A (domainIm A z))
  map_add' z w := by
    refine RealComplexification.ext ?_ ?_
    · change A (domainRe A z + domainRe A w) =
        A (domainRe A z) + A (domainRe A w)
      exact LinearPMap.map_add _ _ _
    · change A (domainIm A z + domainIm A w) =
        A (domainIm A z) + A (domainIm A w)
      exact LinearPMap.map_add _ _ _
  map_smul' c z := by
    refine RealComplexification.ext ?_ ?_
    · change A (c.re • domainRe A z - c.im • domainIm A z) =
        c.re • A (domainRe A z) -
          c.im • A (domainIm A z)
      rw [LinearPMap.map_sub, LinearPMap.map_smul, LinearPMap.map_smul]
    · change A (c.im • domainRe A z + c.re • domainIm A z) =
        c.im • A (domainRe A z) +
          c.re • A (domainIm A z)
      rw [LinearPMap.map_add, LinearPMap.map_smul, LinearPMap.map_smul]

omit [CompleteSpace E] in
/-- The real-part map, as a linear map. -/
@[simp] theorem re_linearMap
    (A : E →ₗ.[ℝ] E)
    (z : domain A) :
    re (linearMap A z) = A (domainRe A z) := rfl

omit [CompleteSpace E] in
/-- The imaginary-part map, as a linear map. -/
@[simp] theorem im_linearMap
    (A : E →ₗ.[ℝ] E)
    (z : domain A) :
    im (linearMap A z) = A (domainIm A z) := rfl

omit [CompleteSpace E] in
/-- The complexified domain is dense when the real one is. -/
theorem domain_dense
    (A : E →ₗ.[ℝ] E) (hdense : Dense ((A.domain : Submodule ℝ E) : Set E)) :
    Dense ((domain A : Submodule ℂ Eℂ) : Set Eℂ) := by
  have hprod : Dense
      ((A.domain : Set E) ×ˢ (A.domain : Set E)) :=
    hdense.prod hdense
  have himage : Dense
      ((WithLp.homeomorphProd 2 E E).symm ''
        ((A.domain : Set E) ×ˢ (A.domain : Set E))) :=
    (((WithLp.homeomorphProd 2 E E).symm.isDenseEmbedding.dense_image).2 hprod)
  rw [show ((domain A : Submodule ℂ Eℂ) : Set Eℂ) =
      (WithLp.homeomorphProd 2 E E).symm ''
        ((A.domain : Set E) ×ˢ (A.domain : Set E)) by
    ext z
    constructor
    · intro hz
      exact ⟨WithLp.ofLp z, (mem_domain_iff A z).mp hz, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact (mem_domain_iff A _).2 hp]
  exact himage

omit [CompleteSpace E] in
/-- The complexified graph is closed when the real one is. -/
theorem linearMap_closedGraph
    (A : E →ₗ.[ℝ] E)
    (hgraph : IsClosed (Set.range fun x : A.domain => ((x : E), A x))) :
    IsClosed (Set.range fun z : domain A =>
      ((z : Eℂ), linearMap A z)) := by
  let coords : (Eℂ × Eℂ) → ((E × E) × (E × E)) :=
    fun p => ((re p.1, re p.2), (im p.1, im p.2))
  have hcoords : Continuous coords :=
    ((continuous_re.comp continuous_fst).prodMk
        (continuous_re.comp continuous_snd)).prodMk
      ((continuous_im.comp continuous_fst).prodMk
        (continuous_im.comp continuous_snd))
  have hclosed : IsClosed
      ((Set.range fun x : A.domain => ((x : E), A x)) ×ˢ
       (Set.range fun y : A.domain => ((y : E), A y))) :=
    hgraph.prod hgraph
  rw [show Set.range (fun z : domain A => ((z : Eℂ), linearMap A z)) =
      coords ⁻¹'
        ((Set.range fun x : A.domain => ((x : E), A x)) ×ˢ
         (Set.range fun y : A.domain => ((y : E), A y))) by
    ext p
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨
        ⟨domainRe A z, by ext <;> rfl⟩,
        ⟨domainIm A z, by ext <;> rfl⟩⟩
    · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      have hx0 : (x : E) = re p.1 := congrArg Prod.fst hx
      have hx1 : A x = re p.2 := congrArg Prod.snd hx
      have hy0 : (y : E) = im p.1 := congrArg Prod.fst hy
      have hy1 : A y = im p.2 := congrArg Prod.snd hy
      let z : domain A :=
        ⟨p.1, (mem_domain_iff A p.1).2
          ⟨hx0 ▸ x.property, hy0 ▸ y.property⟩⟩
      have hzr : domainRe A z = x := Subtype.ext hx0.symm
      have hzi : domainIm A z = y := Subtype.ext hy0.symm
      refine ⟨z, Prod.ext rfl ?_⟩
      apply RealComplexification.ext
      · simpa [hzr] using hx1
      · simpa [hzi] using hy1]
  exact hclosed.preimage hcoords

/-- Coordinatewise complexification of a real partial map. -/
def complexify (A : E →ₗ.[ℝ] E) : Eℂ →ₗ.[ℂ] Eℂ where
  domain := domain A
  toFun := linearMap A

omit [CompleteSpace E] in
/-- The complexified domain, unfolded. -/
@[simp] theorem complexify_domain
    (A : E →ₗ.[ℝ] E) :
    (complexify A).domain = domain A := rfl

omit [CompleteSpace E] in
/-- Membership criterion for the complexified domain. -/
theorem mem_complexify_domain_iff
    (A : E →ₗ.[ℝ] E)
    (z : Eℂ) :
    z ∈ (complexify A).domain ↔ re z ∈ A.domain ∧ im z ∈ A.domain := by
  rfl

omit [CompleteSpace E] in
/-- The complexified operator acts on the real coordinate by the original operator. -/
@[simp] theorem complexify_apply_re
    (A : E →ₗ.[ℝ] E)
    (z : (complexify A).domain) :
    re ((complexify A) z) =
      A ⟨re (z : Eℂ), (mem_complexify_domain_iff A z).mp z.property |>.1⟩ :=
  rfl

omit [CompleteSpace E] in
/-- The complexified operator acts on the imaginary coordinate by the original operator. -/
@[simp] theorem complexify_apply_im
    (A : E →ₗ.[ℝ] E)
    (z : (complexify A).domain) :
    im ((complexify A) z) =
      A ⟨im (z : Eℂ), (mem_complexify_domain_iff A z).mp z.property |>.2⟩ :=
  rfl

omit [CompleteSpace E] in
/-- Membership in the canonical partial-map domain of a complexified closed
operator separates coordinatewise.  This is the `LinearPMap`-native form of
`mem_complexify_domain_iff`, used while the historical bundle remains as a
compatibility adapter. -/
theorem mem_complexify_toLinearPMap_domain_iff
    (A : E →ₗ.[ℝ] E)
    (z : Eℂ) :
    z ∈ (complexify A).domain ↔
      re z ∈ A.domain ∧ im z ∈ A.domain := by
  rfl

/-- Real coordinate of a canonical partial-map domain vector. -/
def domainRePMap
    (A : E →ₗ.[ℝ] E)
    (z : (complexify A).domain) : A.domain :=
  ⟨re (z : Eℂ),
    (mem_complexify_toLinearPMap_domain_iff A z).mp z.property |>.1⟩

/-- Imaginary coordinate of a canonical partial-map domain vector. -/
def domainImPMap
    (A : E →ₗ.[ℝ] E)
    (z : (complexify A).domain) : A.domain :=
  ⟨im (z : Eℂ),
    (mem_complexify_toLinearPMap_domain_iff A z).mp z.property |>.2⟩

omit [CompleteSpace E] in
/-- The same, through the underlying partial map. -/
theorem complexify_toLinearPMap_apply_re
    (A : E →ₗ.[ℝ] E)
    (z : (complexify A).domain) :
    re ((complexify A) z) =
      A (domainRePMap A z) :=
  rfl

omit [CompleteSpace E] in
/-- The same on the imaginary coordinate, through the underlying partial map. -/
theorem complexify_toLinearPMap_apply_im
    (A : E →ₗ.[ℝ] E)
    (z : (complexify A).domain) :
    im ((complexify A) z) =
      A (domainImPMap A z) :=
  rfl

omit [CompleteSpace E] in
/-- Applying a closed operator depends only on the underlying vector, not on
the domain-membership witness. -/
theorem toLinearMap_congr
    {A : E →ₗ.[ℝ] E}
    {u v : A.domain} (h : (u : E) = (v : E)) :
    A u = A v :=
  congrArg A (Subtype.ext h)

/-- The real copy of a domain vector lies in the complexified domain. -/
def ofRealDomain
    (A : E →ₗ.[ℝ] E)
    (x : A.domain) : (complexify A).domain :=
  ⟨ofReal (x : E), by simp⟩

omit [CompleteSpace E] in
/-- Complexification agrees with the original operator on real vectors, so the real operator embeds
in its complexification rather than merely mapping to it. -/
@[simp] theorem complexify_apply_ofReal
    (A : E →ₗ.[ℝ] E)
    (x : A.domain) :
    (complexify A) (ofRealDomain A x) =
      ofReal (A x) := by
  refine RealComplexification.ext ?_ ?_
  · have hR : re (ofReal (A x)) = A x := re_ofReal _
    rw [complexify_apply_re, hR]
    exact toLinearMap_congr (by simp [ofRealDomain])
  · have hR : im (ofReal (A x)) = 0 := im_ofReal _
    rw [complexify_apply_im, hR]
    exact (toLinearMap_congr (v := (0 : A.domain))
      (by simp [ofRealDomain])).trans (map_zero _)

/-- The real copy of a canonical partial-map domain vector. -/
def ofRealDomainPMap
    (A : E →ₗ.[ℝ] E)
    (x : A.domain) : (complexify A).domain :=
  -- `x.2` lands in `A.domain`, which is only definitionally `A.domain`.
  ⟨ofReal (x : E), by simp⟩

omit [CompleteSpace E] in
/-- The real-vector agreement, through the underlying partial map. -/
@[simp] theorem complexify_toLinearPMap_apply_ofReal
    (A : E →ₗ.[ℝ] E)
    (x : A.domain) :
    (complexify A) (ofRealDomainPMap A x) =
      ofReal (A x) := by
  refine RealComplexification.ext ?_ ?_
  · rw [complexify_toLinearPMap_apply_re]
    change A (domainRePMap A (ofRealDomainPMap A x)) =
      A x
    congr 1
  · rw [complexify_toLinearPMap_apply_im]
    change A (domainImPMap A (ofRealDomainPMap A x)) = 0
    rw [show domainImPMap A (ofRealDomainPMap A x) = 0 by
      apply Subtype.ext
      simp [domainImPMap, ofRealDomainPMap]]
    exact LinearPMap.map_zero A

/-- The imaginary copy of a domain vector lies in the complexified domain. -/
def ofImaginaryDomain
    (A : E →ₗ.[ℝ] E)
    (x : A.domain) : (complexify A).domain :=
  ⟨Complex.I • ofReal (x : E), by
    rw [mem_complexify_domain_iff]
    simp only [I_smul_ofReal, re_mk, im_mk]
    exact ⟨A.domain.zero_mem, x.property⟩⟩

omit [CompleteSpace E] in
/-- Action on a purely imaginary vector: the operator commutes with multiplication by `i`. -/
@[simp] theorem complexify_apply_ofImaginary
    (A : E →ₗ.[ℝ] E)
    (x : A.domain) :
    (complexify A) (ofImaginaryDomain A x) =
      Complex.I • ofReal (A x) := by
  refine RealComplexification.ext ?_ ?_
  · have hR : re (Complex.I • ofReal (A x)) = 0 := by
      rw [I_smul_ofReal, re_mk]
    rw [complexify_apply_re, hR]
    exact (toLinearMap_congr (v := (0 : A.domain))
      (by simp [ofImaginaryDomain])).trans (map_zero _)
  · have hR : im (Complex.I • ofReal (A x)) = A x := by
      rw [I_smul_ofReal, im_mk]
    rw [complexify_apply_im, hR]
    exact toLinearMap_congr (by simp [ofImaginaryDomain])

/-- Two partial maps coincide when their domains coincide and their actions
agree on corresponding domain vectors. -/
theorem partialMap_ext
    {𝕜 : Type*} [RCLike 𝕜] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    {A B : H →ₗ.[𝕜] H}
    (hdom : A.domain = B.domain)
    (haction : ∀ (x : A.domain) (y : B.domain),
      (x : H) = (y : H) → A x = B y) :
    A = B := by
  cases A with
  | mk dA fA =>
    cases B with
    | mk dB fB =>
      cases hdom
      have hf : fA = fB := by
        ext x
        exact haction x x rfl
      cases hf
      rfl

omit [CompleteSpace E] in
/-- Complexification commutes with embedding a bounded operator as a closed
operator. -/
theorem complexify_ofBounded
    (T : E →L[ℝ] E) :
    complexify ((T.toLinearMap.toPMap ⊤)) =
      ((RealComplexification.complexify T).toLinearMap.toPMap ⊤) := by
  refine partialMap_ext ?_ ?_
  · ext z
    simp [complexify, domain, complexifySubmodule]
  · intro x y hxy
    refine RealComplexification.ext ?_ ?_
    · rw [complexify_apply_re]
      change T (re (x : Eℂ)) =
        re (RealComplexification.complexify T (y : Eℂ))
      rw [re_complexify, hxy]
    · rw [complexify_apply_im]
      change T (im (x : Eℂ)) =
        im (RealComplexification.complexify T (y : Eℂ))
      rw [im_complexify, hxy]

omit [CompleteSpace E] [CompleteSpace F] in
/-- A real domain map complexifies to a complex domain map. -/
theorem mapsDomainTo_complexify
    {A : E →ₗ.[ℝ] E}
    {B : F →ₗ.[ℝ] F}
    {X : F →L[ℝ] E}
    (hX : TauCeti.LinearPMap.MapsDomainTo A B X) :
    TauCeti.LinearPMap.MapsDomainTo (complexify A) (complexify B)
      (RealComplexification.complexify X) := by
  intro z
  rw [mem_complexify_toLinearPMap_domain_iff]
  constructor
  · rw [re_complexify]
    exact hX (domainRePMap B z)
  · rw [im_complexify]
    exact hX (domainImPMap B z)

omit [CompleteSpace E] [CompleteSpace F] in
/-- The domain-aware Sylvester equation complexifies coordinatewise. -/
theorem closedSylvesterEquation_complexify
    {A : E →ₗ.[ℝ] E}
    {B : F →ₗ.[ℝ] F}
    {X C : F →L[ℝ] E}
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X C) :
    TauCeti.LinearPMap.SylvesterEquation (complexify A) (complexify B)
      (RealComplexification.complexify X)
      (RealComplexification.complexify C) := by
  refine {
    mapsTo_domain := mapsDomainTo_complexify hEq.mapsTo_domain
    equation := ?_
  }
  intro z
  apply RealComplexification.ext
  · have h := hEq.equation
        ⟨re (z : Fℂ), (mem_complexify_domain_iff B z).mp z.property |>.1⟩
    exact h
  · have h := hEq.equation
        ⟨im (z : Fℂ), (mem_complexify_domain_iff B z).mp z.property |>.2⟩
    exact h

omit [CompleteSpace E] in
/-- A lower quadratic-form bound is preserved exactly by complexification. -/
theorem semiboundedBelow_complexify
    {A : E →ₗ.[ℝ] E}
    {c : ℝ} (hA : TauCeti.LinearPMap.SemiboundedBelow A c) :
    TauCeti.LinearPMap.SemiboundedBelow (complexify A) c := by
  intro z
  have hr : c * ‖re (z : Eℂ)‖ ^ 2 ≤
      ⟪A (domainRe A z), re (z : Eℂ)⟫_ℝ := hA (domainRe A z)
  have hi : c * ‖im (z : Eℂ)‖ ^ 2 ≤
      ⟪A (domainIm A z), im (z : Eℂ)⟫_ℝ := hA (domainIm A z)
  rw [RealComplexification.norm_sq]
  change c * (‖re (z : Eℂ)‖ ^ 2 + ‖im (z : Eℂ)‖ ^ 2) ≤
    ⟪A (domainRe A z), re (z : Eℂ)⟫_ℝ +
      ⟪A (domainIm A z), im (z : Eℂ)⟫_ℝ
  nlinarith [hr, hi]

omit [CompleteSpace E] in
/-- An upper quadratic-form bound is preserved exactly by complexification. -/
theorem semiboundedAbove_complexify
    {A : E →ₗ.[ℝ] E}
    {c : ℝ} (hA : TauCeti.LinearPMap.SemiboundedAbove A c) :
    TauCeti.LinearPMap.SemiboundedAbove (complexify A) c := by
  intro z
  have hr : ⟪A (domainRe A z), re (z : Eℂ)⟫_ℝ ≤
      c * ‖re (z : Eℂ)‖ ^ 2 := hA (domainRe A z)
  have hi : ⟪A (domainIm A z), im (z : Eℂ)⟫_ℝ ≤
      c * ‖im (z : Eℂ)‖ ^ 2 := hA (domainIm A z)
  rw [RealComplexification.norm_sq]
  change
    ⟪A (domainRe A z), re (z : Eℂ)⟫_ℝ +
      ⟪A (domainIm A z), im (z : Eℂ)⟫_ℝ ≤
      c * (‖re (z : Eℂ)‖ ^ 2 + ‖im (z : Eℂ)‖ ^ 2)
  nlinarith [hr, hi]

omit [CompleteSpace E] in
/-- Symmetry is preserved by coordinatewise complexification. -/
theorem isSymmetric_complexify
    {A : E →ₗ.[ℝ] E}
    (hA : TauCeti.LinearPMap.IsSymmetric A) :
    TauCeti.LinearPMap.IsSymmetric (complexify A) := by
  intro z w
  apply Complex.ext
  · change
      ⟪A (domainRePMap A z), domainRePMap A w⟫_ℝ +
        ⟪A (domainImPMap A z), domainImPMap A w⟫_ℝ =
      ⟪(domainRePMap A z : E), A (domainRePMap A w)⟫_ℝ +
        ⟪(domainImPMap A z : E), A (domainImPMap A w)⟫_ℝ
    rw [hA (domainRePMap A z) (domainRePMap A w),
      hA (domainImPMap A z) (domainImPMap A w)]
  · change
      ⟪A (domainRePMap A z), domainImPMap A w⟫_ℝ -
        ⟪A (domainImPMap A z), domainRePMap A w⟫_ℝ =
      ⟪(domainRePMap A z : E), A (domainImPMap A w)⟫_ℝ -
        ⟪(domainImPMap A z : E), A (domainRePMap A w)⟫_ℝ
    rw [hA (domainRePMap A z) (domainImPMap A w),
      hA (domainImPMap A z) (domainRePMap A w)]

omit [CompleteSpace E] in
/-- The real embedding of the domain is continuous.  `fun_prop` cannot see
through the `WithLp` wrapper or the subtype, so this is proved by hand. -/
private theorem continuous_ofRealDomain
    (A : E →ₗ.[ℝ] E) :
    Continuous (ofRealDomain A) :=
  ((ofReal (E := E)).continuous.comp continuous_subtype_val).subtype_mk _

omit [CompleteSpace E] in
/-- The imaginary embedding of the domain is continuous. -/
private theorem continuous_ofImaginaryDomain
    (A : E →ₗ.[ℝ] E) :
    Continuous (ofImaginaryDomain A) := by
  have h : Continuous fun x : A.domain => Complex.I • (ofReal (x : E) : Eℂ) :=
    (continuous_const_smul (Complex.I : ℂ)).comp
      ((ofReal (E := E)).continuous.comp continuous_subtype_val)
  exact h.subtype_mk _

omit [CompleteSpace E] in
/-- The real coordinate of the complexified domain is continuous. -/
private theorem continuous_domainRe
    (A : E →ₗ.[ℝ] E) :
    Continuous (domainRe A) :=
  (continuous_re.comp continuous_subtype_val).subtype_mk _

omit [CompleteSpace E] in
/-- The imaginary coordinate of the complexified domain is continuous. -/
private theorem continuous_domainIm
    (A : E →ₗ.[ℝ] E) :
    Continuous (domainIm A) :=
  (continuous_im.comp continuous_subtype_val).subtype_mk _

omit [CompleteSpace E] in
/-- Real part of a complex inner product against a real-copy vector. -/
private theorem inner_ofReal_right_re (z : Eℂ) (v : E) :
    (⟪z, ofReal v⟫_ℂ).re = ⟪re z, v⟫_ℝ := by
  simp [inner_apply]

omit [CompleteSpace E] in
/-- Real part of a complex inner product against an imaginary-copy vector. -/
private theorem inner_I_ofReal_right_re (z : Eℂ) (v : E) :
    (⟪z, Complex.I • ofReal v⟫_ℂ).re = ⟪im z, v⟫_ℝ := by
  simp [inner_apply]

/-- Membership in the adjoint domain separates into the two real adjoint-domain
conditions.  This is the maximality step in the real-to-complex self-adjoint
transport. -/
theorem mem_complexify_adjoint_domain_iff
    (A : E →ₗ.[ℝ] E)
    (z : Eℂ) :
    z ∈ (complexify A).adjoint.domain ↔
      re z ∈ A.adjoint.domain ∧
      im z ∈ A.adjoint.domain := by
  rw [LinearPMap.mem_adjoint_domain_iff]
  constructor
  · intro hz
    have hofReal : Continuous (ofRealDomain A) := continuous_ofRealDomain A
    have hofImaginary : Continuous (ofImaginaryDomain A) :=
      continuous_ofImaginaryDomain A
    constructor
    · rw [LinearPMap.mem_adjoint_domain_iff]
      change Continuous fun x : A.domain => ⟪re z, A x⟫_ℝ
      have hrestrict : Continuous fun x : A.domain =>
          ⟪z, (complexify A) (ofRealDomain A x)⟫_ℂ :=
        hz.comp hofReal
      have hre := Complex.continuous_re.comp hrestrict
      simp only [Function.comp_def,
        complexify_apply_ofReal, inner_ofReal_right_re] at hre
      exact hre
    · rw [LinearPMap.mem_adjoint_domain_iff]
      change Continuous fun x : A.domain => ⟪im z, A x⟫_ℝ
      have hrestrict : Continuous fun x : A.domain =>
          ⟪z, (complexify A) (ofImaginaryDomain A x)⟫_ℂ :=
        hz.comp hofImaginary
      have hre := Complex.continuous_re.comp hrestrict
      simp only [Function.comp_def,
        complexify_apply_ofImaginary, inner_I_ofReal_right_re] at hre
      exact hre
  · rintro ⟨hr, hi⟩
    rw [LinearPMap.mem_adjoint_domain_iff] at hr hi
    replace hr : Continuous fun x : A.domain => ⟪re z, A x⟫_ℝ := hr
    replace hi : Continuous fun x : A.domain => ⟪im z, A x⟫_ℝ := hi
    have hdomainRe : Continuous (domainRe A) := continuous_domainRe A
    have hdomainIm : Continuous (domainIm A) := continuous_domainIm A
    change Continuous fun w : domain A => ⟪z, linearMap A w⟫_ℂ
    have hre : Continuous fun w : domain A => (⟪z, linearMap A w⟫_ℂ).re :=
      (hr.comp hdomainRe).add (hi.comp hdomainIm)
    have him : Continuous fun w : domain A => (⟪z, linearMap A w⟫_ℂ).im :=
      (hr.comp hdomainIm).sub (hi.comp hdomainRe)
    have hsplit : (fun w : domain A => ⟪z, linearMap A w⟫_ℂ) =
        fun w : domain A => (((⟪z, linearMap A w⟫_ℂ).re : ℂ) +
          ((⟪z, linearMap A w⟫_ℂ).im : ℂ) * Complex.I) := by
      funext w
      exact (Complex.re_add_im _).symm
    rw [hsplit]
    exact (Complex.continuous_ofReal.comp hre).add
      ((Complex.continuous_ofReal.comp him).mul continuous_const)

/-- Self-adjointness of a real closed operator is preserved by
complexification. -/
theorem isSelfAdjoint_complexify
    {A : E →ₗ.[ℝ] E}
    (hA : IsSelfAdjoint A) :
    _root_.IsSelfAdjoint (complexify A) := by
  rw [LinearPMap.isSelfAdjoint_def]
  refine LinearPMap.ext_iff.mpr ⟨?_, ?_⟩
  · ext z
    rw [mem_complexify_adjoint_domain_iff]
    rw [LinearPMap.isSelfAdjoint_def.mp hA]
    exact mem_complexify_domain_iff A z
  · intro z hzAdj hzA
    let zAdj : Eℂ := (complexify A).adjoint ⟨z, hzAdj⟩
    let zAct : Eℂ := (complexify A) ⟨z, hzA⟩
    have hformal := LinearPMap.adjoint_isFormalAdjoint
      (domain_dense A hA.dense_domain) ⟨z, hzAdj⟩
    have hsymm := isSymmetric_complexify (TauCeti.LinearPMap.isSymmetric_of_isSelfAdjoint hA)
    have hinner :
        (fun x : Eℂ => ⟪zAdj, x⟫_ℂ) = fun x : Eℂ => ⟪zAct, x⟫_ℂ := by
      apply Continuous.ext_on (domain_dense A hA.dense_domain)
      · exact continuous_const.inner continuous_id
      · exact continuous_const.inner continuous_id
      · intro x hx
        let xDom : (complexify A).domain := ⟨x, hx⟩
        calc
          ⟪zAdj, x⟫_ℂ = ⟪z, (complexify A) xDom⟫_ℂ := by
            simpa [zAdj, xDom] using hformal xDom
          _ = ⟪zAct, x⟫_ℂ := by
            simpa [zAct, xDom] using (hsymm ⟨z, hzA⟩ xDom).symm
    have hzero : ⟪zAdj - zAct, zAdj - zAct⟫_ℂ = 0 := by
      rw [inner_sub_left, congrFun hinner (zAdj - zAct), sub_self]
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)

omit [CompleteSpace E] in
/-- A real bounded inverse complexifies to a complex bounded inverse of every
real shift. -/
theorem realResolvent_mem_complexify
    (A : E →ₗ.[ℝ] E)
    {lam : ℝ} (hlam : lam ∈ TauCeti.LinearPMap.realResolventSet A) :
    lam ∈ TauCeti.LinearPMap.realResolventSet (complexify A) := by
  rcases hlam with ⟨R, hleft, hright⟩
  refine ⟨RealComplexification.complexify R, ?_, ?_⟩
  · intro z
    apply RealComplexification.ext
    · rw [re_complexify, re_sub, complexify_toLinearPMap_apply_re,
        re_complex_smul]
      simpa [domainRePMap] using hleft (domainRePMap A z)
    · rw [im_complexify, im_sub, complexify_toLinearPMap_apply_im,
        im_complex_smul]
      simpa [domainImPMap] using hleft (domainImPMap A z)
  · intro w
    obtain ⟨hrdom, hr⟩ := hright (re w)
    obtain ⟨hidom, hi⟩ := hright (im w)
    refine ⟨(mem_complexify_toLinearPMap_domain_iff A _).2
      ⟨hrdom, hidom⟩, ?_⟩
    apply RealComplexification.ext
    · rw [re_sub, complexify_toLinearPMap_apply_re, re_complex_smul]
      simpa [domainRePMap] using hr
    · rw [im_sub, complexify_toLinearPMap_apply_im, im_complex_smul]
      simpa [domainImPMap] using hi

omit [CompleteSpace E] in
/-- A complex resolvent of the coordinatewise complexification descends to a
real resolvent by restricting to the real copy and taking real coordinates. -/
theorem complexify_realResolvent_mem
    (A : E →ₗ.[ℝ] E)
    {lam : ℝ} (hlam : lam ∈ TauCeti.LinearPMap.realResolventSet (complexify A)) :
    lam ∈ TauCeti.LinearPMap.realResolventSet A := by
  rcases hlam with ⟨R, hleft, hright⟩
  let RrLinear : E →ₗ[ℝ] E :=
    { toFun := fun y => re (R (ofReal y))
      map_add' := fun y z => by simp
      map_smul' := fun r y => by simp }
  let Rr : E →L[ℝ] E :=
    RrLinear.mkContinuous ‖R‖ (fun y => by
      calc
        ‖RrLinear y‖ ≤ ‖R (ofReal y)‖ := norm_re_le _
        _ ≤ ‖R‖ * ‖ofReal y‖ := R.le_opNorm _
        _ = ‖R‖ * ‖y‖ := by rw [ofReal.norm_map])
  refine ⟨Rr, ?_, ?_⟩
  · intro x
    have hx := hleft (ofRealDomainPMap A x)
    rw [complexify_toLinearPMap_apply_ofReal] at hx
    simpa [Rr, RrLinear, ofRealDomainPMap] using congrArg re hx
  · intro y
    obtain ⟨hdom, hy⟩ := hright (ofReal y)
    refine ⟨(mem_complexify_toLinearPMap_domain_iff A
      (R (ofReal y))).mp hdom |>.1, ?_⟩
    have hre := congrArg re hy
    rw [re_sub, complexify_toLinearPMap_apply_re, re_complex_smul] at hre
    simpa [Rr, RrLinear, domainRePMap] using hre

omit [CompleteSpace E] in
/-- Real resolvent membership is exactly preserved by closed-operator
complexification. -/
theorem mem_realResolventSet_complexify_iff
    (A : E →ₗ.[ℝ] E)
    (lam : ℝ) :
    lam ∈ TauCeti.LinearPMap.realResolventSet (complexify A) ↔ lam ∈ TauCeti.LinearPMap.realResolventSet A := by
  exact ⟨complexify_realResolvent_mem A, realResolvent_mem_complexify A⟩

omit [CompleteSpace E] in
/-- Closed-operator real spectrum is exactly preserved by
coordinatewise complexification. -/
theorem closed_realSpectrum_complexify
    (A : E →ₗ.[ℝ] E) :
    TauCeti.LinearPMap.realSpectrum (complexify A) = TauCeti.LinearPMap.realSpectrum A := by
  ext lam
  change lam ∉ TauCeti.LinearPMap.realResolventSet (complexify A) ↔
    lam ∉ TauCeti.LinearPMap.realResolventSet A
  rw [mem_realResolventSet_complexify_iff A lam]

omit [CompleteSpace E] in
/-- The real spectrum of a real closed operator is the genuine real spectrum
of its complexification. -/
theorem realSpectrum_complexify
    (A : E →ₗ.[ℝ] E) :
    TauCeti.LinearPMap.realSpectrum A
      = Complex.ofReal ⁻¹'
          TauCeti.LinearPMap.spectrum (complexify A) := by
  -- `realSpectrum` inverts `A - lam` while `spectrum` inverts `lam • I - A`, so this is no
  -- longer a definitional identity; `realSpectrum_eq_spectraSpectrum` is the bridge.
  rw [← closed_realSpectrum_complexify A]
  exact realSpectrum_eq_spectraSpectrum (complexify A)

omit [CompleteSpace E] [CompleteSpace F] in
/-- Complexification preserves every constructor of the manuscript gap
predicate. -/
theorem unboundedSylvesterGap_complexify
    {A : E →ₗ.[ℝ] E}
    {B : F →ₗ.[ℝ] F}
    {δ : ℝ}
    (hgap : FormBoundedSylvesterGap A B δ) :
    FormBoundedSylvesterGap (complexify A)
      (complexify B) δ := by
  cases hgap with
  | intervalExterior hβα hgap =>
      apply FormBoundedSylvesterGap.intervalExterior hβα
      rcases hgap with hgap | hgap
      · left
        constructor
        · intro lam hlam
          have hlamA : lam ∈ TauCeti.LinearPMap.realSpectrum (complexify A) := hlam
          have hlam' : lam ∈ TauCeti.LinearPMap.realSpectrum A := by
            rwa [closed_realSpectrum_complexify A] at hlamA
          exact hgap.1 hlam'
        · intro lam hlam
          have hlamB : lam ∈ TauCeti.LinearPMap.realSpectrum (complexify B) := hlam
          have hlam' : lam ∈ TauCeti.LinearPMap.realSpectrum B := by
            rwa [closed_realSpectrum_complexify B] at hlamB
          exact hgap.2 hlam'
      · right
        constructor
        · intro lam hlam
          have hlamB : lam ∈ TauCeti.LinearPMap.realSpectrum (complexify B) := hlam
          have hlam' : lam ∈ TauCeti.LinearPMap.realSpectrum B := by
            rwa [closed_realSpectrum_complexify B] at hlamB
          exact hgap.1 hlam'
        · intro lam hlam
          have hlamA : lam ∈ TauCeti.LinearPMap.realSpectrum (complexify A) := hlam
          have hlam' : lam ∈ TauCeti.LinearPMap.realSpectrum A := by
            rwa [closed_realSpectrum_complexify A] at hlamA
          exact hgap.2 hlam'
  | leftAboveRightBelow c hA hB =>
      exact FormBoundedSylvesterGap.leftAboveRightBelow c
        (semiboundedBelow_complexify hA) (semiboundedAbove_complexify hB)
  | leftBelowRightAbove c hA hB =>
      exact FormBoundedSylvesterGap.leftBelowRightAbove c
        (semiboundedAbove_complexify hA) (semiboundedBelow_complexify hB)

end PartialMapComplexification

end

end ExactSinTheta
end DavisKahan
end TauCeti
