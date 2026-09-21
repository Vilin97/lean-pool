/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.CyclicDecomposition
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.ProjValMeasure.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# The Borel calculus of a restricted operator

Layer 4 of the Hahn--Hellinger stack, and the step with no partial credit: the multiplicity
decomposition recurses into a reducing subspace, and to do that it must know that the Borel
calculus of the *restricted* operator is the restriction of the ambient Borel calculus.

Let `a : H →L[ℂ] H` be normal and let `K` be a **calculus-invariant** subspace
(`IsCalculusInvariant`, from
`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/CyclicDecomposition.lean`), which is the
reducing hypothesis: `Kᗮ` is then invariant too, by `IsCalculusInvariant.orthogonal`.  This
file builds

1. the restriction `compress K a : K →L[ℂ] K` and its normality
   (`isStarNormal_compress`);
2. the spectral inclusion `spectrum ℂ (compress K a) ⊆ spectrum ℂ a`
   (`spectrum_compress_subset`), packaged as a continuous, measurable map `specIncl`;
3. **the compatibility law** `borelCalculus_compress`: restricting a bounded measurable symbol
   along `specIncl` and applying the restricted calculus is the ambient calculus, compressed;
4. the transport of scalar spectral measures, `map_specIncl_diagMeasure` -- which is what the
   uniform-multiplicity decomposition actually consumes.

## The route

Everything hangs on (4), and (4) hangs on the *continuous* case.

The compression `T ↦ P_K T|_K` is a star-algebra homomorphism on any set of operators leaving
`K` invariant, and it is continuous on the whole algebra; so `g ↦ compress K (cfcHom a g)` and
`g ↦ cfcHom (a|_K) (g ∘ specIncl)` are two continuous star-algebra homomorphisms
`C(spectrum ℂ a, ℂ) →⋆ₐ[ℂ] (K →L[ℂ] K)`.  They agree at the coordinate function -- both give
`compress K a` -- so Stone--Weierstrass (`ContinuousMap.starAlgHom_ext_map_X`) makes them
equal.  That is `cfcHom_comp_specIncl`.

Feeding continuous symbols into `integral_diagMeasure_ofReal` on both sides then says that
`Measure.map specIncl (diagMeasure (a|_K) x)` and `diagMeasure a x` integrate every bounded
continuous function alike, and a finite Borel measure on a metrisable space is determined by
those integrals (`MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure`).  That is (4),
and (3) follows because the Borel calculus is determined by its diagonal matrix elements
(`TauCeti.op_ext_of_inner_self`), which are exactly integrals against the diagonal measures
(`inner_borelCalculus_self`).

## No separability hypothesis

**Nothing here is countable or separable.**  The Stone--Weierstrass step needs only
compactness of `spectrum ℂ a`, and the measure-uniqueness step needs only that the spectrum is
a Borel subspace of `ℂ` (so pseudo-metrisable).  This matches layers 1--3 and the scope of the
repository's Davis--Kahan Theorem 3.1, which carries no separability hypothesis either; see
the uniform-multiplicity normal form.

## Main results

* `TauCeti.BorelCalculus.compress`: the compression of an operator to a submodule.
* `TauCeti.BorelCalculus.isStarNormal_compress`: the restriction of a normal operator to a
  calculus-invariant subspace is normal.
* `TauCeti.BorelCalculus.spectrum_compress_subset`: **spectral inclusion.**
* `TauCeti.BorelCalculus.cfcHom_comp_specIncl`: the compatibility law for the *continuous*
  functional calculus.
* `TauCeti.BorelCalculus.map_specIncl_diagMeasure`: the scalar spectral measure of a vector of
  `K` for the restriction pushes forward to its scalar spectral measure for `a`.
* `TauCeti.BorelCalculus.borelCalculus_compress` and
  `TauCeti.BorelCalculus.coe_borelCalculus_compress`: **the compatibility law.**

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib and `ForTauCeti`.
-/

public section

open scoped InnerProductSpace
open MeasureTheory

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace TauCeti
namespace BorelCalculus

-- The continuous functional calculus of an operator on `↥K` is reached only after synthesising
-- `CStarAlgebra (↥K →L[ℂ] ↥K)`, which itself needs `CompleteSpace ↥K`; that is one nesting level
-- more than the default budget allows, and without this the instance is not found at all.  The
-- same search succeeds unaided for `H →L[ℂ] H`, where no subtype intervenes.
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {a : H →L[ℂ] H}

section Ext

variable {K : Submodule ℂ H}

omit [CompleteSpace H] in
/-- Two operators on a submodule are equal when their values agree after inclusion. -/
theorem clm_ext_coe {S T : K →L[ℂ] K} (h : ∀ x : K, (S x : H) = (T x : H)) : S = T :=
  ContinuousLinearMap.ext fun x => Subtype.ext (h x)

end Ext

section Compress

variable (K : Submodule ℂ H) [K.HasOrthogonalProjection]

/-- **The compression of a bounded operator to a submodule**: restrict the domain to `K`, then
project the result back onto `K`.

For a subspace invariant under `T` this is the honest restriction of `T`, which is the only way
it is used below (`coe_compress_apply`).  It is defined for *every* `T` on purpose: the
compatibility proof needs the compression to be a continuous function of `T` on the whole
operator algebra (`continuous_compress`), and a definition carrying an invariance proof could
not be composed with `cfcHom` that way. -/
noncomputable def compress (T : H →L[ℂ] H) : K →L[ℂ] K :=
  K.orthogonalProjectionOnto ∘L (T ∘L K.subtypeL)

variable {K}

omit [CompleteSpace H] in
/-- Rewrite form of `compress`, so a call site need not unfold the definition. -/
theorem compress_apply (T : H →L[ℂ] H) (x : K) :
    compress K T x = K.orthogonalProjectionOnto (T (x : H)) := (rfl)

omit [CompleteSpace H] in
/-- **The compression of an invariant operator is its restriction.** -/
theorem coe_compress_apply {T : H →L[ℂ] H} (hT : ∀ x ∈ K, T x ∈ K) (x : K) :
    (compress K T x : H) = T (x : H) := by
  have hmem : T (x : H) ∈ K := hT _ x.2
  rw [compress_apply]
  exact congrArg Subtype.val
    (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨T (x : H), hmem⟩ : K))

omit [CompleteSpace H] in
/-- Compression is additive. -/
theorem compress_add (S T : H →L[ℂ] H) : compress K (S + T) = compress K S + compress K T := by
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [compress_apply, _root_.add_apply, map_add]

omit [CompleteSpace H] in
/-- Compression kills the zero operator. -/
theorem compress_zero : compress K (0 : H →L[ℂ] H) = 0 := by
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [compress_apply, _root_.zero_apply, map_zero]

omit [CompleteSpace H] in
/-- Compression is subtractive. -/
theorem compress_sub (S T : H →L[ℂ] H) : compress K (S - T) = compress K S - compress K T := by
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [compress_apply, _root_.sub_apply, map_sub]

omit [CompleteSpace H] in
/-- Compression is homogeneous. -/
theorem compress_smul (c : ℂ) (T : H →L[ℂ] H) : compress K (c • T) = c • compress K T := by
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [compress_apply, _root_.smul_apply, map_smul]

omit [CompleteSpace H] in
/-- The compression of the identity is the identity. -/
theorem compress_one : compress K (1 : H →L[ℂ] H) = 1 := by
  refine clm_ext_coe fun x => ?_
  rw [coe_compress_apply (fun y hy => by rwa [one_apply_eq_self]), one_apply_eq_self,
    one_apply_eq_self]

omit [CompleteSpace H] in
/-- Compression preserves the scalars. -/
theorem compress_algebraMap (z : ℂ) :
    compress K (algebraMap ℂ (H →L[ℂ] H) z) = algebraMap ℂ (K →L[ℂ] K) z := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, compress_smul,
    compress_one]

omit [CompleteSpace H] in
/-- **Compression is multiplicative on invariant operators.** -/
theorem compress_mul {S T : H →L[ℂ] H} (hS : ∀ x ∈ K, S x ∈ K) (hT : ∀ x ∈ K, T x ∈ K) :
    compress K (S * T) = compress K S * compress K T := by
  refine clm_ext_coe fun x => ?_
  have hST : ∀ y ∈ K, (S * T) y ∈ K := fun y hy => hS _ (hT _ hy)
  rw [coe_compress_apply hST, _root_.mul_apply_eq_comp, _root_.mul_apply_eq_comp,
    coe_compress_apply hS, coe_compress_apply hT]

/-- **The adjoint of a compression is the compression of the adjoint**, for an operator whose
adjoint also leaves the subspace invariant. -/
theorem adjoint_compress [CompleteSpace K] {T : H →L[ℂ] H} (hT : ∀ x ∈ K, T x ∈ K)
    (hT' : ∀ x ∈ K, ContinuousLinearMap.adjoint T x ∈ K) :
    ContinuousLinearMap.adjoint (compress K T) = compress K (ContinuousLinearMap.adjoint T) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [Submodule.coe_inner, Submodule.coe_inner, coe_compress_apply hT', coe_compress_apply hT,
    ContinuousLinearMap.adjoint_inner_left]

omit [CompleteSpace H] in
/-- **Compression is continuous in the operator.**  This is the reason `compress` is total: the
Stone--Weierstrass step compares two continuous star-algebra homomorphisms, and one of them is
the compression of the continuous functional calculus. -/
theorem continuous_compress (K : Submodule ℂ H) [K.HasOrthogonalProjection] :
    Continuous (compress K) := by
  change Continuous fun T : H →L[ℂ] H =>
    K.orthogonalProjectionOnto.comp (T.comp K.subtypeL)
  exact continuous_const.clm_comp (continuous_id.clm_comp continuous_const)

end Compress

section Invariance

variable {K : Submodule ℂ H}

/-- A calculus-invariant subspace is invariant under the operator itself: `a` is the value of
the calculus at the coordinate symbol. -/
theorem IsCalculusInvariant.apply_mem {ha : IsStarNormal a} (hK : IsCalculusInvariant ha K)
    {x : H} (hx : x ∈ K) : a x ∈ K := by
  have h := hK.borelCalculus_mem (isBddMeasurable_coord (a := a)) hx
  rwa [borelCalculus_coord ha] at h

/-- A calculus-invariant subspace is invariant under `a⋆`: that is the value of the calculus at
the conjugate of the coordinate symbol. -/
theorem IsCalculusInvariant.star_apply_mem {ha : IsStarNormal a} (hK : IsCalculusInvariant ha K)
    {x : H} (hx : x ∈ K) : star a x ∈ K := by
  have h := hK.borelCalculus_mem (isBddMeasurable_coord (a := a)).conj hx
  rwa [borelCalculus_conj ha (isBddMeasurable_coord (a := a)), borelCalculus_coord ha,
    ← ContinuousLinearMap.star_eq_adjoint] at h

/-- A calculus-invariant subspace is invariant under every value of the *continuous* functional
calculus, since those are values of the Borel calculus. -/
theorem IsCalculusInvariant.cfcHom_apply_mem {ha : IsStarNormal a}
    (hK : IsCalculusInvariant ha K) (g : C(spectrum ℂ a, ℂ)) {x : H} (hx : x ∈ K) :
    cfcHom ha g x ∈ K := by
  have h := hK.borelCalculus_mem (IsBddMeasurable.of_continuous g) hx
  rwa [borelCalculus_of_continuous ha g (IsBddMeasurable.of_continuous g)] at h

end Invariance

section Normal

variable {K : Submodule ℂ H} [CompleteSpace K]

/-- **The restriction of a normal operator to a calculus-invariant subspace is normal.**

`a` and `a⋆` both leave `K` invariant, so compression is multiplicative on both and carries
adjoints to adjoints; the commutation `a⋆ a = a a⋆` therefore descends. -/
theorem isStarNormal_compress (ha : IsStarNormal a) (hK : IsCalculusInvariant ha K) :
    IsStarNormal (compress K a) := by
  have hinv : ∀ x ∈ K, a x ∈ K := fun _ hx => hK.apply_mem hx
  have hinv' : ∀ x ∈ K, star a x ∈ K := fun _ hx => hK.star_apply_mem hx
  have hadj : ∀ x ∈ K, ContinuousLinearMap.adjoint a x ∈ K := by
    intro x hx
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact hinv' x hx
  have hstar : star (compress K a) = compress K (star a) := by
    rw [ContinuousLinearMap.star_eq_adjoint, adjoint_compress hinv hadj,
      ← ContinuousLinearMap.star_eq_adjoint]
  refine ⟨?_⟩
  rw [Commute, SemiconjBy, hstar, ← compress_mul hinv' hinv, ← compress_mul hinv hinv']
  exact congrArg _ ha.star_comm_self

end Normal

section Spectrum

variable {K : Submodule ℂ H} [CompleteSpace K]

/-- **Spectral inclusion.**  The spectrum of the restriction of `a` to a calculus-invariant
subspace is contained in the spectrum of `a`.

If `a - z` is invertible then its inverse `v` also leaves `K` invariant: splitting `v y` into
its `K`- and `Kᗮ`-components and applying `a - z`, which is block diagonal because `K` reduces
`a`, forces the `Kᗮ`-component into `K ⊓ Kᗮ = ⊥`.  Compressing `v` therefore inverts the
compression of `a - z`, which is `compress K a - z`. -/
theorem spectrum_compress_subset (ha : IsStarNormal a) (hK : IsCalculusInvariant ha K) :
    spectrum ℂ (compress K a) ⊆ spectrum ℂ a := by
  intro z hz
  by_contra hznot
  rw [spectrum.notMem_iff] at hznot
  obtain ⟨u, hu⟩ := hznot
  set w : H →L[ℂ] H := algebraMap ℂ (H →L[ℂ] H) z - a with hw
  set v : H →L[ℂ] H := (↑u⁻¹ : H →L[ℂ] H) with hv
  have hwv : w * v = 1 := by rw [hv, ← hu]; exact u.mul_inv
  have hvw : v * w = 1 := by rw [hv, ← hu]; exact u.inv_mul
  -- `w` is block diagonal: it preserves `K` and `Kᗮ`
  have hwapply : ∀ y : H, w y = z • y - a y := by
    intro y
    rw [hw, _root_.sub_apply, Algebra.algebraMap_eq_smul_one,
      _root_.smul_apply, one_apply_eq_self]
  have hwK : ∀ y ∈ K, w y ∈ K := by
    intro y hy
    rw [hwapply]
    exact K.sub_mem (K.smul_mem z hy) (hK.apply_mem hy)
  have hwKperp : ∀ y ∈ Kᗮ, w y ∈ Kᗮ := by
    intro y hy
    rw [hwapply]
    exact Kᗮ.sub_mem (Kᗮ.smul_mem z hy) (hK.orthogonal.apply_mem hy)
  -- a vector lying in both `K` and `Kᗮ` is zero
  have hbot : ∀ t : H, t ∈ K → t ∈ Kᗮ → t = 0 := fun t h1 h2 =>
    inner_self_eq_zero.mp ((Submodule.mem_orthogonal K t).mp h2 t h1)
  -- hence `v` preserves `K`
  have hvK : ∀ y ∈ K, v y ∈ K := by
    intro y hy
    have hp : K.starProjection (v y) ∈ K := K.starProjection_apply_mem _
    have hq : v y - K.starProjection (v y) ∈ Kᗮ := K.sub_starProjection_mem_orthogonal _
    have hsum : w (K.starProjection (v y)) + w (v y - K.starProjection (v y)) = y := by
      rw [← map_add, add_sub_cancel, ← _root_.mul_apply_eq_comp, hwv, one_apply_eq_self]
    have hmemK : w (v y - K.starProjection (v y)) ∈ K := by
      rw [eq_sub_of_add_eq' hsum]
      exact K.sub_mem hy (hwK _ hp)
    have hzero : w (v y - K.starProjection (v y)) = 0 :=
      hbot _ hmemK (hwKperp _ hq)
    have hq0 : v y - K.starProjection (v y) = 0 := by
      have h := congrArg v hzero
      rwa [map_zero, ← _root_.mul_apply_eq_comp, hvw, one_apply_eq_self] at h
    have : v y = K.starProjection (v y) := by
      rw [← sub_eq_zero]; exact hq0
    rw [this]; exact hp
  -- the compressions invert one another
  have h1 : compress K w * compress K v = 1 := by
    rw [← compress_mul hwK hvK, hwv, compress_one]
  have h2 : compress K v * compress K w = 1 := by
    rw [← compress_mul hvK hwK, hvw, compress_one]
  have hunit : IsUnit (algebraMap ℂ (K →L[ℂ] K) z - compress K a) := by
    have hcw : compress K w = algebraMap ℂ (K →L[ℂ] K) z - compress K a := by
      rw [hw, compress_sub, compress_algebraMap]
    exact ⟨⟨compress K w, compress K v, h1, h2⟩, hcw⟩
  exact (spectrum.mem_iff.mp hz) hunit

/-- **The spectral inclusion, as a map.**  The inclusion of the spectrum of the restriction into
the spectrum of `a`, which is what a symbol is restricted along. -/
def specIncl (ha : IsStarNormal a) (hK : IsCalculusInvariant ha K) :
    spectrum ℂ (compress K a) → spectrum ℂ a :=
  fun w => ⟨(w : ℂ), spectrum_compress_subset ha hK w.2⟩

/-- The spectral inclusion is the identity on the underlying complex numbers. -/
@[simp] theorem coe_specIncl (ha : IsStarNormal a) (hK : IsCalculusInvariant ha K)
    (w : spectrum ℂ (compress K a)) : (specIncl ha hK w : ℂ) = (w : ℂ) := (rfl)

/-- The spectral inclusion is continuous. -/
theorem continuous_specIncl (ha : IsStarNormal a) (hK : IsCalculusInvariant ha K) :
    Continuous (specIncl ha hK) :=
  Continuous.subtype_mk continuous_subtype_val _

/-- The spectral inclusion is measurable, which is what lets a symbol be pulled back. -/
theorem measurable_specIncl (ha : IsStarNormal a) (hK : IsCalculusInvariant ha K) :
    Measurable (specIncl ha hK) :=
  (continuous_specIncl ha hK).measurable

/-- The spectral inclusion, bundled as a continuous map. -/
def specInclCM (ha : IsStarNormal a) (hK : IsCalculusInvariant ha K) :
    C(spectrum ℂ (compress K a), spectrum ℂ a) :=
  ⟨specIncl ha hK, continuous_specIncl ha hK⟩

/-- The bundled spectral inclusion, unfolded. -/
@[simp] theorem specInclCM_apply (ha : IsStarNormal a) (hK : IsCalculusInvariant ha K)
    (w : spectrum ℂ (compress K a)) : specInclCM ha hK w = specIncl ha hK w := (rfl)

end Spectrum

section ContinuousCalculus

variable {K : Submodule ℂ H} [CompleteSpace K]

/-- **The compressed continuous functional calculus**, as a star-algebra homomorphism.

Every value of the continuous functional calculus of `a` leaves `K` invariant, and so does its
adjoint; compression is therefore multiplicative and `⋆`-preserving on the whole range of
`cfcHom ha`, which is what makes this a homomorphism rather than merely a linear map. -/
noncomputable def compressCfc (ha : IsStarNormal a) (hK : IsCalculusInvariant ha K) :
    C(spectrum ℂ a, ℂ) →⋆ₐ[ℂ] (K →L[ℂ] K) where
  toFun g := compress K (cfcHom ha g)
  map_one' := by rw [map_one]; exact compress_one
  map_mul' g₁ g₂ := by
    rw [map_mul]
    exact compress_mul (fun _ hx => hK.cfcHom_apply_mem g₁ hx)
      (fun _ hx => hK.cfcHom_apply_mem g₂ hx)
  map_zero' := by rw [map_zero]; exact compress_zero
  map_add' g₁ g₂ := by rw [map_add]; exact compress_add _ _
  commutes' r := by rw [AlgHomClass.commutes]; exact compress_algebraMap r
  map_star' g := by
    have hT : ∀ x ∈ K, cfcHom ha g x ∈ K := fun _ hx => hK.cfcHom_apply_mem g hx
    have hadj : ContinuousLinearMap.adjoint (cfcHom ha g) = cfcHom ha (star g) := by
      rw [map_star, ContinuousLinearMap.star_eq_adjoint]
    have hT' : ∀ x ∈ K, ContinuousLinearMap.adjoint (cfcHom ha g) x ∈ K := by
      intro x hx
      rw [hadj]
      exact hK.cfcHom_apply_mem (star g) hx
    rw [ContinuousLinearMap.star_eq_adjoint, adjoint_compress hT hT', hadj]

/-- The compressed continuous calculus, unfolded. -/
@[simp] theorem compressCfc_apply (ha : IsStarNormal a) (hK : IsCalculusInvariant ha K)
    (g : C(spectrum ℂ a, ℂ)) : compressCfc ha hK g = compress K (cfcHom ha g) := (rfl)

/-- The compressed continuous calculus is continuous, because compression is. -/
theorem continuous_compressCfc (ha : IsStarNormal a) (hK : IsCalculusInvariant ha K) :
    Continuous (compressCfc ha hK) := by
  change Continuous fun g : C(spectrum ℂ a, ℂ) => compress K (cfcHom ha g)
  exact (continuous_compress K).comp (cfcHom_continuous ha)

/-- **Pulling a symbol back along the spectral inclusion and applying the restricted calculus**,
as a star-algebra homomorphism.  This is the other half of the Stone--Weierstrass comparison. -/
noncomputable def restrictCfc (ha : IsStarNormal a) (hK : IsCalculusInvariant ha K) :
    C(spectrum ℂ a, ℂ) →⋆ₐ[ℂ] (K →L[ℂ] K) :=
  (cfcHom (isStarNormal_compress ha hK)).comp
    (ContinuousMap.compStarAlgHom' ℂ ℂ (specInclCM ha hK))

/-- The restricted calculus of a pulled-back symbol, unfolded. -/
@[simp] theorem restrictCfc_apply (ha : IsStarNormal a) (hK : IsCalculusInvariant ha K)
    (g : C(spectrum ℂ a, ℂ)) :
    restrictCfc ha hK g
      = cfcHom (isStarNormal_compress ha hK) (g.comp (specInclCM ha hK)) := (rfl)

/-- The restricted calculus of a pulled-back symbol is continuous in the symbol. -/
theorem continuous_restrictCfc (ha : IsStarNormal a) (hK : IsCalculusInvariant ha K) :
    Continuous (restrictCfc ha hK) := by
  change Continuous fun g : C(spectrum ℂ a, ℂ) =>
    cfcHom (isStarNormal_compress ha hK) (g.comp (specInclCM ha hK))
  exact (cfcHom_continuous (isStarNormal_compress ha hK)).comp
    (specInclCM ha hK).continuous_precomp

/-- Pulling the coordinate symbol back along the spectral inclusion gives the coordinate symbol
of the restriction -- both are `w ↦ (w : ℂ)`. -/
theorem restrict_id_comp_specInclCM (ha : IsStarNormal a) (hK : IsCalculusInvariant ha K) :
    (ContinuousMap.restrict (spectrum ℂ a) (ContinuousMap.id ℂ)).comp (specInclCM ha hK)
      = ContinuousMap.restrict (spectrum ℂ (compress K a)) (ContinuousMap.id ℂ) := by
  ext w
  rfl

/-- **The two homomorphisms agree.**  They are continuous and take the same value at the
coordinate symbol -- namely `compress K a` -- so Stone--Weierstrass, in the form of the
uniqueness of the continuous functional calculus, identifies them. -/
theorem compressCfc_eq_restrictCfc (ha : IsStarNormal a) (hK : IsCalculusInvariant ha K) :
    compressCfc ha hK = restrictCfc ha hK := by
  refine ContinuousMap.UniqueHom.eq_of_continuous_of_map_id (spectrum ℂ a)
    (compressCfc ha hK) (restrictCfc ha hK)
    (continuous_compressCfc ha hK) (continuous_restrictCfc ha hK) ?_
  rw [compressCfc_apply, restrictCfc_apply, cfcHom_id ha, restrict_id_comp_specInclCM ha hK,
    cfcHom_id (isStarNormal_compress ha hK)]

/-- **The compatibility law for the continuous functional calculus.**

For a continuous symbol, restricting it along the spectral inclusion and applying the calculus
of the restricted operator is the compression of the ambient calculus. -/
theorem cfcHom_comp_specIncl (ha : IsStarNormal a) (hK : IsCalculusInvariant ha K)
    (g : C(spectrum ℂ a, ℂ)) :
    cfcHom (isStarNormal_compress ha hK) (g.comp (specInclCM ha hK))
      = compress K (cfcHom ha g) :=
  (DFunLike.congr_fun (compressCfc_eq_restrictCfc ha hK) g).symm

end ContinuousCalculus

section DiagonalMeasure

variable {K : Submodule ℂ H} [CompleteSpace K]

omit [CompleteSpace H] in
/-- The diagonal matrix elements of a compression are those of the operator, at vectors of the
subspace. -/
theorem inner_compress_self {T : H →L[ℂ] H} (hT : ∀ x ∈ K, T x ∈ K) (x : K) :
    ⟪x, compress K T x⟫_ℂ = ⟪(x : H), T (x : H)⟫_ℂ := by
  rw [Submodule.coe_inner, coe_compress_apply hT]

/-- Complexifying a pulled-back real symbol is pulling back its complexification. -/
theorem ofRealLM_comp_specInclCM (ha : IsStarNormal a) (hK : IsCalculusInvariant ha K)
    (g : C(spectrum ℂ a, ℝ)) :
    ofRealLM (g.comp (specInclCM ha hK)) = (ofRealLM g).comp (specInclCM ha hK) := by
  ext w
  simp only [ofRealLM_apply, ContinuousMap.comp_apply]

/-- **The scalar spectral measures transport along the spectral inclusion.**

`diagMeasure` of the restriction at a vector of `K` pushes forward, along the inclusion of
spectra, to `diagMeasure` of `a` at the same vector.  This is what the uniform-multiplicity
decomposition consumes.

Both measures are finite Borel measures on a metrisable space, so it is enough to compare their
integrals of bounded continuous functions; there the statement is the compatibility law for the
continuous calculus, read through `integral_diagMeasure_ofReal`. -/
theorem map_specIncl_diagMeasure (ha : IsStarNormal a) (hK : IsCalculusInvariant ha K) (x : K) :
    Measure.map (specIncl ha hK) (diagMeasure (isStarNormal_compress ha hK) x)
      = diagMeasure ha (x : H) := by
  have : IsFiniteMeasure
      (Measure.map (specIncl ha hK) (diagMeasure (isStarNormal_compress ha hK) x)) :=
    (diagMeasure (isStarNormal_compress ha hK) x).isFiniteMeasure_map _
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun g => ?_
  set G : C(spectrum ℂ a, ℝ) := ⟨⇑g, g.continuous⟩
  have hmap : ∫ w, g w ∂(Measure.map (specIncl ha hK)
        (diagMeasure (isStarNormal_compress ha hK) x))
      = ∫ w, (G.comp (specInclCM ha hK)) w ∂(diagMeasure (isStarNormal_compress ha hK) x) :=
    integral_map (measurable_specIncl ha hK).aemeasurable g.continuous.aestronglyMeasurable
  have hT : ∀ y ∈ K, cfcHom ha (ofRealLM G) y ∈ K := fun _ hy =>
    hK.cfcHom_apply_mem (ofRealLM G) hy
  rw [hmap, integral_diagMeasure_ofReal, ofRealLM_comp_specInclCM ha hK G,
    cfcHom_comp_specIncl ha hK (ofRealLM G), inner_compress_self hT,
    ← integral_diagMeasure_ofReal ha (x : H) G]
  rfl

end DiagonalMeasure

section BorelCompatibility

variable {K : Submodule ℂ H} [CompleteSpace K]

/-- Pulling a bounded measurable symbol back along the spectral inclusion keeps it admissible:
measurability composes and the bound is unchanged. -/
theorem IsBddMeasurable.comp_specIncl (ha : IsStarNormal a) (hK : IsCalculusInvariant ha K)
    {f : spectrum ℂ a → ℂ} (hf : IsBddMeasurable f) :
    IsBddMeasurable (fun w : spectrum ℂ (compress K a) => f (specIncl ha hK w)) :=
  ⟨hf.measurable.comp (measurable_specIncl ha hK), hf.chooseBound, hf.chooseBound_nonneg,
    fun _ => hf.norm_le_chooseBound _⟩

/-- **The compatibility law.**  For a bounded measurable symbol `f` on the spectrum of `a`, the
Borel calculus of the restriction at the restricted symbol is the compression of the ambient
Borel calculus at `f`.

Both sides are bounded operators on `K`, and a bounded operator on a complex Hilbert space is
determined by its diagonal matrix elements; those are integrals against the diagonal measures,
which correspond under `map_specIncl_diagMeasure`. -/
theorem borelCalculus_compress (ha : IsStarNormal a) (hK : IsCalculusInvariant ha K)
    {f : spectrum ℂ a → ℂ} (hf : IsBddMeasurable f) :
    borelCalculus (isStarNormal_compress ha hK) (hf.comp_specIncl ha hK)
      = compress K (borelCalculus ha hf) := by
  refine op_ext_of_inner_self fun x => ?_
  rw [inner_borelCalculus_self, inner_compress_self (fun _ hy => hK.borelCalculus_mem hf hy),
    inner_borelCalculus_self, ← map_specIncl_diagMeasure ha hK x]
  exact (integral_map (measurable_specIncl ha hK).aemeasurable
    hf.measurable.aestronglyMeasurable).symm

/-- **The compatibility law, at a vector.**  This is the form layer 4 uses: applying the
restricted calculus to a vector of `K` and forgetting the subspace is applying the ambient
calculus. -/
theorem coe_borelCalculus_compress (ha : IsStarNormal a) (hK : IsCalculusInvariant ha K)
    {f : spectrum ℂ a → ℂ} (hf : IsBddMeasurable f) (x : K) :
    (borelCalculus (isStarNormal_compress ha hK) (hf.comp_specIncl ha hK) x : H)
      = borelCalculus ha hf (x : H) := by
  rw [borelCalculus_compress ha hK hf,
    coe_compress_apply (fun _ hy => hK.borelCalculus_mem hf hy)]

/-- **The compatibility law, as an identity of operators `K →L[ℂ] H`.** -/
theorem subtypeL_comp_borelCalculus_compress (ha : IsStarNormal a)
    (hK : IsCalculusInvariant ha K) {f : spectrum ℂ a → ℂ} (hf : IsBddMeasurable f) :
    K.subtypeL ∘L borelCalculus (isStarNormal_compress ha hK) (hf.comp_specIncl ha hK)
      = borelCalculus ha hf ∘L K.subtypeL := by
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  exact coe_borelCalculus_compress ha hK hf x

end BorelCompatibility

section CyclicSubspace

/-- **A cyclic subspace is complete**, being closed.

This is the instance layer 4 supplies when it recurses: a cyclic subspace is calculus-invariant
(`isCalculusInvariant_cyclicSubspace`) and complete, which is everything the restriction API of
this file asks for.  It is a `theorem` rather than an `instance` because `cyclicSubspace`
carries the normality proof as an explicit argument, so there is nothing for instance
resolution to key on; a consumer writes `haveI := completeSpace_cyclicSubspace ha ξ`. -/
theorem completeSpace_cyclicSubspace (ha : IsStarNormal a) (ξ : H) :
    CompleteSpace (cyclicSubspace ha ξ) :=
  (isClosed_cyclicSubspace ha ξ).completeSpace_coe

end CyclicSubspace

end BorelCalculus
end TauCeti
