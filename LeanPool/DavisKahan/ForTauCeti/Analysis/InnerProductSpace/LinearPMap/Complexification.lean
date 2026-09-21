/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/

/-
## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Generalized from:
  `DavisKahan/SpectralTheory/PartialMap/Complexification.lean`.
* Extraction class: **representation migration and generalization**.  The original
  construction was tied to the historical bundled `PartialMap` and to square
  operators.  This module defines the coordinatewise complexification directly on
  Mathlib `LinearPMap`, with independent source and target spaces.
* The construction and structural transport use no Davis--Kahan theorem and import
  only `ForTauCeti` / Mathlib foundations.
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Complexification.Basic
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed

/-!
# Complexification of real partial linear maps

The canonical carrier for an unbounded operator in Tau Ceti is Mathlib's
`LinearPMap`.  Complexification should therefore be defined on that carrier,
not on a parallel bundled closed-operator type.

For a real partial map `A : E →ₗ.[ℝ] F`, `complexifyReal A` has domain

`{z : E_ℂ | re z ∈ dom A ∧ im z ∈ dom A}`

and acts coordinatewise:

`A_ℂ (x + i y) = A x + i A y`.

This first layer deliberately contains no spectral theorem.  It establishes the
base object and the structural facts that later adjoint, self-adjoint, resolvent,
and spectral-measure transport can target directly:

* exact domain membership;
* exact real/imaginary action formulas;
* agreement on the embedded real and imaginary copies;
* dense-domain transport;
* closed-graph transport;
* symmetry transport in the square case.

The construction is rectangular (`E → F`) even though the first spectral consumers
are square.  That avoids repeating the same migration later for Sylvester-type maps.
-/

public section

namespace TauCeti
namespace LinearPMap

open scoped InnerProductSpace
open Filter Topology
open TauCeti.RealComplexification

noncomputable section

universe v w

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

local notation "Eℂ" => RealComplexification E
local notation "Fℂ" => RealComplexification F

omit [InnerProductSpace ℝ E] in
private theorem continuous_re_source : Continuous (re : Eℂ → E) :=
  continuous_fst.comp (WithLp.homeomorphProd 2 E E).continuous

omit [InnerProductSpace ℝ E] in
private theorem continuous_im_source : Continuous (im : Eℂ → E) :=
  continuous_snd.comp (WithLp.homeomorphProd 2 E E).continuous

omit [InnerProductSpace ℝ F] in
private theorem continuous_re_target : Continuous (re : Fℂ → F) :=
  continuous_fst.comp (WithLp.homeomorphProd 2 F F).continuous

omit [InnerProductSpace ℝ F] in
private theorem continuous_im_target : Continuous (im : Fℂ → F) :=
  continuous_snd.comp (WithLp.homeomorphProd 2 F F).continuous

/-- The complexified domain of a real partial map: both coordinates belong to
its original real domain. -/
@[expose]
def complexificationDomain (A : E →ₗ.[ℝ] F) : Submodule ℂ Eℂ where
  carrier := {z | re z ∈ A.domain ∧ im z ∈ A.domain}
  zero_mem' := by simp
  add_mem' := by
    intro z w hz hw
    exact ⟨A.domain.add_mem hz.1 hw.1, A.domain.add_mem hz.2 hw.2⟩
  smul_mem' := by
    intro c z hz
    exact
      ⟨A.domain.sub_mem (A.domain.smul_mem c.re hz.1)
          (A.domain.smul_mem c.im hz.2),
        A.domain.add_mem (A.domain.smul_mem c.im hz.1)
          (A.domain.smul_mem c.re hz.2)⟩

/-- Membership in a complexified partial-map domain is exactly coordinatewise
membership in the real domain. -/
@[simp] theorem mem_complexificationDomain_iff
    (A : E →ₗ.[ℝ] F) (z : Eℂ) :
    z ∈ complexificationDomain A ↔ re z ∈ A.domain ∧ im z ∈ A.domain := by
  rfl

/-- The real coordinate of a vector in the complexified domain. -/
def complexificationDomainRe
    (A : E →ₗ.[ℝ] F) (z : complexificationDomain A) : A.domain :=
  ⟨re (z : Eℂ), (mem_complexificationDomain_iff A z).mp z.property |>.1⟩

/-- The imaginary coordinate of a vector in the complexified domain. -/
def complexificationDomainIm
    (A : E →ₗ.[ℝ] F) (z : complexificationDomain A) : A.domain :=
  ⟨im (z : Eℂ), (mem_complexificationDomain_iff A z).mp z.property |>.2⟩

/-- Coordinatewise complex-linear action of a real partial map on its
complexified domain. -/
@[expose]
def complexificationLinearMap
    (A : E →ₗ.[ℝ] F) : complexificationDomain A →ₗ[ℂ] Fℂ where
  toFun z := mk (A (complexificationDomainRe A z))
    (A (complexificationDomainIm A z))
  map_add' z w := by
    refine RealComplexification.ext ?_ ?_
    · change A (complexificationDomainRe A z + complexificationDomainRe A w) =
        A (complexificationDomainRe A z) + A (complexificationDomainRe A w)
      exact _root_.LinearPMap.map_add A _ _
    · change A (complexificationDomainIm A z + complexificationDomainIm A w) =
        A (complexificationDomainIm A z) + A (complexificationDomainIm A w)
      exact _root_.LinearPMap.map_add A _ _
  map_smul' c z := by
    refine RealComplexification.ext ?_ ?_
    · change A (c.re • complexificationDomainRe A z -
          c.im • complexificationDomainIm A z) =
        c.re • A (complexificationDomainRe A z) -
          c.im • A (complexificationDomainIm A z)
      rw [_root_.LinearPMap.map_sub A,
        _root_.LinearPMap.map_smul A, _root_.LinearPMap.map_smul A]
    · change A (c.im • complexificationDomainRe A z +
          c.re • complexificationDomainIm A z) =
        c.im • A (complexificationDomainRe A z) +
          c.re • A (complexificationDomainIm A z)
      rw [_root_.LinearPMap.map_add A,
        _root_.LinearPMap.map_smul A, _root_.LinearPMap.map_smul A]

/-- **Complexification of a raw real `LinearPMap`.**

This is the canonical generalized replacement for the historical
closed-operator-specific complexification.  Closedness and density are not
stored; they are transported by separate theorems below. -/
@[expose]
def complexifyReal (A : E →ₗ.[ℝ] F) : Eℂ →ₗ.[ℂ] Fℂ where
  domain := complexificationDomain A
  toFun := complexificationLinearMap A

/-- Complexification has the coordinatewise complexified domain definitionally. -/
@[simp] theorem complexifyReal_domain (A : E →ₗ.[ℝ] F) :
    (complexifyReal A).domain = complexificationDomain A := rfl

/-- Domain membership for the raw partial-map complexification. -/
 theorem mem_complexifyReal_domain_iff
    (A : E →ₗ.[ℝ] F) (z : Eℂ) :
    z ∈ (complexifyReal A).domain ↔ re z ∈ A.domain ∧ im z ∈ A.domain := by
  rfl

/-- Real-coordinate formula for the complexified partial map. -/
@[simp] theorem complexifyReal_apply_re
    (A : E →ₗ.[ℝ] F) (z : (complexifyReal A).domain) :
    re (complexifyReal A z) = A (complexificationDomainRe A z) := rfl

/-- Imaginary-coordinate formula for the complexified partial map. -/
@[simp] theorem complexifyReal_apply_im
    (A : E →ₗ.[ℝ] F) (z : (complexifyReal A).domain) :
    im (complexifyReal A z) = A (complexificationDomainIm A z) := rfl

/-- The embedded real copy of a domain vector belongs to the complexified domain. -/
@[expose]
def complexifyRealOfRealDomain
    (A : E →ₗ.[ℝ] F) (x : A.domain) : (complexifyReal A).domain :=
  ⟨ofReal (x : E), by
    rw [mem_complexifyReal_domain_iff]
    simp only [re_ofReal, im_ofReal]
    exact ⟨x.property, A.domain.zero_mem⟩⟩

/-- Coercing the embedded real domain vector back to the ambient complexification
is exactly the canonical real embedding. -/
@[simp] theorem complexifyRealOfRealDomain_coe
    (A : E →ₗ.[ℝ] F) (x : A.domain) :
    ((complexifyRealOfRealDomain A x : (complexifyReal A).domain) : Eℂ) =
      ofReal (x : E) := rfl

/-- Complexification agrees exactly with the original partial map on the real copy. -/
@[simp] theorem complexifyReal_apply_ofReal
    (A : E →ₗ.[ℝ] F) (x : A.domain) :
    complexifyReal A (complexifyRealOfRealDomain A x) = ofReal (A x) := by
  refine RealComplexification.ext ?_ ?_
  · rw [complexifyReal_apply_re, re_ofReal]
    apply congrArg A
    apply Subtype.ext
    simp [complexificationDomainRe, complexifyRealOfRealDomain]
  · rw [complexifyReal_apply_im, im_ofReal]
    rw [show complexificationDomainIm A (complexifyRealOfRealDomain A x) = 0 by
      apply Subtype.ext
      simp [complexificationDomainIm, complexifyRealOfRealDomain]]
    exact _root_.LinearPMap.map_zero A

/-- The embedded imaginary copy of a domain vector belongs to the complexified domain. -/
def complexifyRealOfImaginaryDomain
    (A : E →ₗ.[ℝ] F) (x : A.domain) : (complexifyReal A).domain :=
  ⟨Complex.I • ofReal (x : E), by
    rw [mem_complexifyReal_domain_iff]
    simp only [I_smul_ofReal, re_mk, im_mk]
    exact ⟨A.domain.zero_mem, x.property⟩⟩

/-- Complexification commutes with multiplication by `i` on the embedded
imaginary copy. -/
@[simp] theorem complexifyReal_apply_ofImaginary
    (A : E →ₗ.[ℝ] F) (x : A.domain) :
    complexifyReal A (complexifyRealOfImaginaryDomain A x) =
      Complex.I • ofReal (A x) := by
  refine RealComplexification.ext ?_ ?_
  · rw [complexifyReal_apply_re]
    simp only [I_smul_ofReal, re_mk]
    rw [show complexificationDomainRe A (complexifyRealOfImaginaryDomain A x) = 0 by
      apply Subtype.ext
      simp [complexificationDomainRe, complexifyRealOfImaginaryDomain]]
    exact _root_.LinearPMap.map_zero A
  · rw [complexifyReal_apply_im]
    simp only [I_smul_ofReal, im_mk]
    apply congrArg A
    apply Subtype.ext
    simp [complexificationDomainIm, complexifyRealOfImaginaryDomain]

/-- Dense real domain implies dense complexified domain. -/
theorem dense_domain_complexifyReal
    (A : E →ₗ.[ℝ] F) (hA : Dense (A.domain : Set E)) :
    Dense (((complexifyReal A).domain : Submodule ℂ Eℂ) : Set Eℂ) := by
  have hprod : Dense ((A.domain : Set E) ×ˢ (A.domain : Set E)) := hA.prod hA
  have himage : Dense
      ((WithLp.homeomorphProd 2 E E).symm ''
        ((A.domain : Set E) ×ˢ (A.domain : Set E))) :=
    (((WithLp.homeomorphProd 2 E E).symm.isDenseEmbedding.dense_image).2 hprod)
  rw [show (((complexifyReal A).domain : Submodule ℂ Eℂ) : Set Eℂ) =
      (WithLp.homeomorphProd 2 E E).symm ''
        ((A.domain : Set E) ×ˢ (A.domain : Set E)) by
    ext z
    constructor
    · intro hz
      exact ⟨WithLp.ofLp z, (mem_complexifyReal_domain_iff A z).mp hz, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact (mem_complexifyReal_domain_iff A _).2 hp]
  exact himage

/-- Closed graph is preserved by raw `LinearPMap` complexification. -/
theorem closedGraph_complexifyReal
    (A : E →ₗ.[ℝ] F)
    (hA : IsClosed (Set.range fun x : A.domain => ((x : E), A x))) :
    IsClosed (Set.range fun z : (complexifyReal A).domain =>
      ((z : Eℂ), complexifyReal A z)) := by
  let coords : (Eℂ × Fℂ) → ((E × F) × (E × F)) :=
    fun p => ((re p.1, re p.2), (im p.1, im p.2))
  have hcoords : Continuous coords :=
    ((continuous_re_source.comp continuous_fst).prodMk
        (continuous_re_target.comp continuous_snd)).prodMk
      ((continuous_im_source.comp continuous_fst).prodMk
        (continuous_im_target.comp continuous_snd))
  have hclosed : IsClosed
      ((Set.range fun x : A.domain => ((x : E), A x)) ×ˢ
       (Set.range fun y : A.domain => ((y : E), A y))) :=
    hA.prod hA
  rw [show Set.range (fun z : (complexifyReal A).domain =>
      ((z : Eℂ), complexifyReal A z)) =
      coords ⁻¹'
        ((Set.range fun x : A.domain => ((x : E), A x)) ×ˢ
         (Set.range fun y : A.domain => ((y : E), A y))) by
    ext p
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨
        ⟨complexificationDomainRe A z, by ext <;> rfl⟩,
        ⟨complexificationDomainIm A z, by ext <;> rfl⟩⟩
    · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      have hx0 : (x : E) = re p.1 := congrArg Prod.fst hx
      have hx1 : A x = re p.2 := congrArg Prod.snd hx
      have hy0 : (y : E) = im p.1 := congrArg Prod.fst hy
      have hy1 : A y = im p.2 := congrArg Prod.snd hy
      let z : (complexifyReal A).domain :=
        ⟨p.1, (mem_complexifyReal_domain_iff A p.1).2
          ⟨hx0 ▸ x.property, hy0 ▸ y.property⟩⟩
      have hzr : complexificationDomainRe A z = x := Subtype.ext hx0.symm
      have hzi : complexificationDomainIm A z = y := Subtype.ext hy0.symm
      refine ⟨z, Prod.ext rfl ?_⟩
      apply RealComplexification.ext
      · simpa [hzr] using hx1
      · simpa [hzi] using hy1]
  exact hclosed.preimage hcoords

section Square

variable {A : E →ₗ.[ℝ] E}

/-! ## Real resolvent and spectrum transport -/

/-- A bounded inverse of a real shift complexifies coordinatewise to a bounded inverse
of the same real shift of the raw complexified partial map. -/
theorem realResolvent_mem_complexifyReal
    (A : E →ₗ.[ℝ] E) {lam : ℝ}
    (hlam : lam ∈ realResolventSet A) :
    lam ∈ realResolventSet (complexifyReal A) := by
  rw [mem_realResolventSet_iff] at hlam ⊢
  rcases hlam with ⟨R, hleft, hright⟩
  refine ⟨RealComplexification.complexify R, ?_, ?_⟩
  · intro z
    apply RealComplexification.ext
    · rw [RealComplexification.re_complexify, re_sub, complexifyReal_apply_re,
        RealComplexification.re_complex_smul]
      simpa [complexificationDomainRe] using hleft (complexificationDomainRe A z)
    · rw [RealComplexification.im_complexify, im_sub, complexifyReal_apply_im,
        RealComplexification.im_complex_smul]
      simpa [complexificationDomainIm] using hleft (complexificationDomainIm A z)
  · intro w
    obtain ⟨hrdom, hr⟩ := hright (re w)
    obtain ⟨hidom, hi⟩ := hright (im w)
    have hdom : RealComplexification.complexify R w ∈ (complexifyReal A).domain := by
      rw [mem_complexifyReal_domain_iff, RealComplexification.re_complexify,
        RealComplexification.im_complexify]
      exact ⟨hrdom, hidom⟩
    refine ⟨hdom, ?_⟩
    apply RealComplexification.ext
    · rw [re_sub, complexifyReal_apply_re, RealComplexification.re_complex_smul]
      simpa [complexificationDomainRe] using hr
    · rw [im_sub, complexifyReal_apply_im, RealComplexification.im_complex_smul]
      simpa [complexificationDomainIm] using hi

/-- A bounded inverse of a real shift of the complexification descends by restricting
the inverse to the real copy and taking its real coordinate. -/
theorem complexifyReal_realResolvent_mem
    (A : E →ₗ.[ℝ] E) {lam : ℝ}
    (hlam : lam ∈ realResolventSet (complexifyReal A)) :
    lam ∈ realResolventSet A := by
  rw [mem_realResolventSet_iff] at hlam ⊢
  rcases hlam with ⟨R, hleft, hright⟩
  let Rr : E →L[ℝ] E := RealComplexification.realPartOperator R
  refine ⟨Rr, ?_, ?_⟩
  · intro x
    have hx := hleft (complexifyRealOfRealDomain A x)
    rw [complexifyReal_apply_ofReal] at hx
    have hre := congrArg re hx
    simpa [Rr, RealComplexification.realPartOperator_apply] using hre
  · intro y
    obtain ⟨hdom, hy⟩ := hright (ofReal y)
    have hcoords := (mem_complexifyReal_domain_iff A (R (ofReal y))).mp hdom
    have hRrdom : Rr y ∈ A.domain := by
      simpa [Rr, RealComplexification.realPartOperator_apply] using hcoords.1
    refine ⟨hRrdom, ?_⟩
    have hre := congrArg re hy
    rw [re_sub, complexifyReal_apply_re, RealComplexification.re_complex_smul] at hre
    simpa [Rr, RealComplexification.realPartOperator_apply, complexificationDomainRe] using hre

/-- Real resolvent membership is exactly preserved by raw `LinearPMap`
complexification. -/
theorem mem_realResolventSet_complexifyReal_iff
    (A : E →ₗ.[ℝ] E) (lam : ℝ) :
    lam ∈ realResolventSet (complexifyReal A) ↔
      lam ∈ realResolventSet A :=
  ⟨complexifyReal_realResolvent_mem A, realResolvent_mem_complexifyReal A⟩

/-- The real spectrum is exactly preserved by raw `LinearPMap` complexification. -/
theorem realSpectrum_complexifyReal (A : E →ₗ.[ℝ] E) :
    realSpectrum (complexifyReal A) = realSpectrum A := by
  ext lam
  simp only [mem_realSpectrum_iff]
  rw [mem_realResolventSet_complexifyReal_iff A lam]

/-- The embedded real-domain map is continuous. -/
private theorem continuous_complexifyRealOfRealDomain
    (A : E →ₗ.[ℝ] E) :
    Continuous (complexifyRealOfRealDomain A) :=
  ((ofReal (E := E)).continuous.comp continuous_subtype_val).subtype_mk _

/-- The embedded imaginary-domain map is continuous. -/
private theorem continuous_complexifyRealOfImaginaryDomain
    (A : E →ₗ.[ℝ] E) :
    Continuous (complexifyRealOfImaginaryDomain A) := by
  have h : Continuous fun x : A.domain => Complex.I • (ofReal (x : E) : Eℂ) :=
    (continuous_const_smul (Complex.I : ℂ)).comp
      ((ofReal (E := E)).continuous.comp continuous_subtype_val)
  exact h.subtype_mk _

/-- The real coordinate of the complexified domain is continuous. -/
private theorem continuous_complexificationDomainRe
    (A : E →ₗ.[ℝ] E) :
    Continuous (complexificationDomainRe A) :=
  (continuous_re_source.comp continuous_subtype_val).subtype_mk _

/-- The imaginary coordinate of the complexified domain is continuous. -/
private theorem continuous_complexificationDomainIm
    (A : E →ₗ.[ℝ] E) :
    Continuous (complexificationDomainIm A) :=
  (continuous_im_source.comp continuous_subtype_val).subtype_mk _

/-- Real part of a complex inner product against a real-copy vector. -/
private theorem inner_ofReal_right_re (z : Eℂ) (v : E) :
    (⟪z, ofReal v⟫_ℂ).re = ⟪re z, v⟫_ℝ := by
  simp [inner_apply]

/-- Real part of a complex inner product against an imaginary-copy vector. -/
private theorem inner_I_ofReal_right_re (z : Eℂ) (v : E) :
    (⟪z, Complex.I • ofReal v⟫_ℂ).re = ⟪im z, v⟫_ℝ := by
  simp [inner_apply]

/-- Symmetry is preserved by raw partial-map complexification. -/
theorem IsSymmetric.complexifyReal (hA : IsSymmetric A) :
    IsSymmetric (TauCeti.LinearPMap.complexifyReal A) := by
  rw [isSymmetric_iff] at hA ⊢
  intro z w
  apply Complex.ext
  · change
      ⟪A (complexificationDomainRe A z), complexificationDomainRe A w⟫_ℝ +
        ⟪A (complexificationDomainIm A z), complexificationDomainIm A w⟫_ℝ =
      ⟪(complexificationDomainRe A z : E), A (complexificationDomainRe A w)⟫_ℝ +
        ⟪(complexificationDomainIm A z : E), A (complexificationDomainIm A w)⟫_ℝ
    rw [hA (complexificationDomainRe A z) (complexificationDomainRe A w),
      hA (complexificationDomainIm A z) (complexificationDomainIm A w)]
  · change
      ⟪A (complexificationDomainRe A z), complexificationDomainIm A w⟫_ℝ -
        ⟪A (complexificationDomainIm A z), complexificationDomainRe A w⟫_ℝ =
      ⟪(complexificationDomainRe A z : E), A (complexificationDomainIm A w)⟫_ℝ -
        ⟪(complexificationDomainIm A z : E), A (complexificationDomainRe A w)⟫_ℝ
    rw [hA (complexificationDomainRe A z) (complexificationDomainIm A w),
      hA (complexificationDomainIm A z) (complexificationDomainRe A w)]

variable [CompleteSpace E]

/-- Membership in the adjoint domain of a raw complexified real partial map is exactly
coordinatewise membership in the real adjoint domain.

This is the maximality theorem needed to transport real self-adjointness to the canonical
complexification without introducing a bundled closed-operator bridge. -/
theorem mem_complexifyReal_adjoint_domain_iff
    (A : E →ₗ.[ℝ] E) (z : Eℂ) :
    z ∈ (complexifyReal A).adjoint.domain ↔
      re z ∈ A.adjoint.domain ∧ im z ∈ A.adjoint.domain := by
  rw [_root_.LinearPMap.mem_adjoint_domain_iff]
  constructor
  · intro hz
    have hofReal : Continuous (complexifyRealOfRealDomain A) :=
      continuous_complexifyRealOfRealDomain A
    have hofImaginary : Continuous (complexifyRealOfImaginaryDomain A) :=
      continuous_complexifyRealOfImaginaryDomain A
    constructor
    · rw [_root_.LinearPMap.mem_adjoint_domain_iff]
      change Continuous fun x : A.domain => ⟪re z, A x⟫_ℝ
      have hrestrict : Continuous fun x : A.domain =>
          ⟪z, complexifyReal A (complexifyRealOfRealDomain A x)⟫_ℂ :=
        hz.comp hofReal
      have hre := Complex.continuous_re.comp hrestrict
      simp only [Function.comp_def, complexifyReal_apply_ofReal,
        inner_ofReal_right_re] at hre
      exact hre
    · rw [_root_.LinearPMap.mem_adjoint_domain_iff]
      change Continuous fun x : A.domain => ⟪im z, A x⟫_ℝ
      have hrestrict : Continuous fun x : A.domain =>
          ⟪z, complexifyReal A (complexifyRealOfImaginaryDomain A x)⟫_ℂ :=
        hz.comp hofImaginary
      have hre := Complex.continuous_re.comp hrestrict
      simp only [Function.comp_def, complexifyReal_apply_ofImaginary,
        inner_I_ofReal_right_re] at hre
      exact hre
  · rintro ⟨hr, hi⟩
    rw [_root_.LinearPMap.mem_adjoint_domain_iff] at hr hi
    replace hr : Continuous fun x : A.domain => ⟪re z, A x⟫_ℝ := hr
    replace hi : Continuous fun x : A.domain => ⟪im z, A x⟫_ℝ := hi
    have hdomainRe : Continuous (complexificationDomainRe A) :=
      continuous_complexificationDomainRe A
    have hdomainIm : Continuous (complexificationDomainIm A) :=
      continuous_complexificationDomainIm A
    change Continuous fun w : (complexifyReal A).domain =>
      ⟪z, complexifyReal A w⟫_ℂ
    have hre : Continuous fun w : (complexifyReal A).domain =>
        (⟪z, complexifyReal A w⟫_ℂ).re :=
      (hr.comp hdomainRe).add (hi.comp hdomainIm)
    have him : Continuous fun w : (complexifyReal A).domain =>
        (⟪z, complexifyReal A w⟫_ℂ).im :=
      (hr.comp hdomainIm).sub (hi.comp hdomainRe)
    have hsplit : (fun w : (complexifyReal A).domain =>
        ⟪z, complexifyReal A w⟫_ℂ) =
        fun w : (complexifyReal A).domain =>
          (((⟪z, complexifyReal A w⟫_ℂ).re : ℂ) +
            ((⟪z, complexifyReal A w⟫_ℂ).im : ℂ) * Complex.I) := by
      funext w
      exact (Complex.re_add_im _).symm
    rw [hsplit]
    exact (Complex.continuous_ofReal.comp hre).add
      ((Complex.continuous_ofReal.comp him).mul continuous_const)

/-- Self-adjointness of a real raw `LinearPMap` is preserved by canonical
complexification.

The proof uses the adjoint-domain characterization above and symmetry.  In particular,
it does not reconstruct adjoint values through the historical bundled closed-operator
representation. -/
theorem isSelfAdjoint_complexifyReal
    {A : E →ₗ.[ℝ] E} (hA : _root_.IsSelfAdjoint A) :
    _root_.IsSelfAdjoint (complexifyReal A) := by
  have hAeq : A.adjoint = A := _root_.LinearPMap.isSelfAdjoint_def.mp hA
  have hdense : Dense (((complexifyReal A).domain : Submodule ℂ Eℂ) : Set Eℂ) :=
    dense_domain_complexifyReal A hA.dense_domain
  have hAformal := _root_.LinearPMap.adjoint_isFormalAdjoint (T := A) hA.dense_domain
  rw [hAeq] at hAformal
  have hAsymm : IsSymmetric A := by
    rw [isSymmetric_iff]
    exact hAformal
  have hsymm := hAsymm.complexifyReal
  rw [isSymmetric_iff] at hsymm
  have hformal : (complexifyReal A).IsFormalAdjoint (complexifyReal A) := by
    exact hsymm
  have hle : complexifyReal A ≤ (complexifyReal A).adjoint :=
    _root_.LinearPMap.IsFormalAdjoint.le_adjoint
      (T := complexifyReal A) (S := complexifyReal A) hdense hformal
  have hdomeq : (complexifyReal A).domain = (complexifyReal A).adjoint.domain := by
    ext z
    rw [mem_complexifyReal_domain_iff, mem_complexifyReal_adjoint_domain_iff, hAeq]
  rw [_root_.LinearPMap.isSelfAdjoint_def]
  exact (_root_.LinearPMap.eq_of_le_of_domain_eq hle hdomeq).symm

end Square

end
end LinearPMap
end TauCeti
