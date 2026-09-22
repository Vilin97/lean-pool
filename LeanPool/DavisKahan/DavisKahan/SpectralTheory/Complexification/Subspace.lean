/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Complexification.Basic
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.Projector
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks
import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem

/-!
# Complexification of real closed subspaces

This file transports the orthogonal-projection geometry of a real Hilbert
space into the concrete complexification from `Core/Complexification.lean`.
It is the missing foundation required to reuse the completed complex
operator-angle calculus for real subspaces without duplicating the Halmos
projection analysis.

For a real subspace `U`, `complexifySubmodule U` consists of all pairs whose
real and imaginary coordinates both lie in `U`.  The main results prove that:

* an orthogonally complemented real subspace remains orthogonally complemented;
* its complex orthogonal projection is exactly the complexification of the
  real orthogonal projection;
* complexification commutes with orthogonal complement;
* symmetric and directed projection gaps are preserved exactly;
* acuteness and quarter-acuteness are preserved;
* reducing-subspace data transports through operator complexification.
-/

namespace TauCeti
namespace DavisKahan
namespace Foundation
namespace RealComplexification

open scoped InnerProductSpace
open TauCeti.RealComplexification
-- the namespace is split across the two libraries: `Basic` is in `ForTauCeti`, `Subspace` here
open TauCeti.DavisKahan.Foundation.RealComplexification

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Complexification of a real subspace: both coordinates belong to the real
subspace. -/
def complexifySubmodule (U : Submodule ℝ E) :
    Submodule ℂ (RealComplexification E) where
  carrier := {z | re z ∈ U ∧ im z ∈ U}
  zero_mem' := by
    change re (0 : RealComplexification E) ∈ U ∧
      im (0 : RealComplexification E) ∈ U
    simp
  add_mem' := by
    intro z w hz hw
    change re z ∈ U ∧ im z ∈ U at hz
    change re w ∈ U ∧ im w ∈ U at hw
    change re (z + w) ∈ U ∧ im (z + w) ∈ U
    exact ⟨U.add_mem hz.1 hw.1, U.add_mem hz.2 hw.2⟩
  smul_mem' := by
    intro c z hz
    change re z ∈ U ∧ im z ∈ U at hz
    change re (c • z) ∈ U ∧ im (c • z) ∈ U
    exact
      ⟨U.sub_mem (U.smul_mem c.re hz.1) (U.smul_mem c.im hz.2),
        U.add_mem (U.smul_mem c.im hz.1) (U.smul_mem c.re hz.2)⟩

omit [CompleteSpace E] in
/-- Membership in a complexified submodule, in terms of the real and imaginary coordinates. -/
@[simp]
theorem mem_complexifySubmodule {U : Submodule ℝ E}
    {z : RealComplexification E} :
    z ∈ complexifySubmodule U ↔ re z ∈ U ∧ im z ∈ U := by
  change (re z ∈ U ∧ im z ∈ U) ↔ re z ∈ U ∧ im z ∈ U
  rfl

omit [CompleteSpace E] in
/-- The range of a complexified real operator is exactly the complexification
of its real range.  This belongs with subspace complexification rather than in
an operator-ideal consumer: it is pure linear geometry and is useful whenever
a real projection or partial isometry is descended from the complex side. -/
theorem range_complexify
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : E →L[ℝ] F) :
    LinearMap.range (complexify T).toLinearMap =
      complexifySubmodule (LinearMap.range T.toLinearMap) := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    rw [mem_complexifySubmodule]
    exact ⟨⟨re w, rfl⟩, ⟨im w, rfl⟩⟩
  · intro hz
    rw [mem_complexifySubmodule] at hz
    rcases hz with ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    refine ⟨mk x y, ?_⟩
    apply RealComplexification.ext
    · simpa using hx
    · simpa using hy

omit [CompleteSpace E] in
/-- Membership criterion for a vector given by its coordinates. -/

theorem mk_mem_complexifySubmodule_iff (U : Submodule ℝ E) (x y : E) :
    mk x y ∈ complexifySubmodule U ↔ x ∈ U ∧ y ∈ U := by
  rw [mem_complexifySubmodule]
  simp

omit [CompleteSpace E] in
/-- A real vector lies in the complexification exactly when it lies in the original submodule. -/

theorem ofReal_mem_complexifySubmodule_iff (U : Submodule ℝ E) (x : E) :
    ofReal x ∈ complexifySubmodule U ↔ x ∈ U := by
  rw [mem_complexifySubmodule]
  simp

omit [CompleteSpace E] in
/-- Complexification reflects equality of real subspaces. -/
theorem complexifySubmodule_injective :
    Function.Injective (complexifySubmodule :
      Submodule ℝ E → Submodule ℂ (RealComplexification E)) := by
  intro U V hUV
  ext x
  rw [← ofReal_mem_complexifySubmodule_iff U x, hUV,
    ofReal_mem_complexifySubmodule_iff V x]

omit [CompleteSpace E] in
/-- Complexified subspaces are invariant under the canonical conjugation. -/
theorem conjugation_mem_complexifySubmodule_iff (U : Submodule ℝ E)
    (z : RealComplexification E) :
    conjugation z ∈ complexifySubmodule U ↔ z ∈ complexifySubmodule U := by
  rw [mem_complexifySubmodule, mem_complexifySubmodule]
  simp

variable (U : Submodule ℝ E) [U.HasOrthogonalProjection]

omit [CompleteSpace E] in
/-- The coordinatewise real projection lands in the complexified subspace. -/
theorem complexify_starProjection_mem (z : RealComplexification E) :
    complexify U.starProjection z ∈ complexifySubmodule U := by
  rw [mem_complexifySubmodule]
  exact
    ⟨U.starProjection_apply_mem (re z),
      U.starProjection_apply_mem (im z)⟩

omit [CompleteSpace E] in
/-- The residual from the coordinatewise projection is orthogonal to the
complexified subspace. -/
theorem sub_complexify_starProjection_mem_orthogonal
    (z : RealComplexification E) :
    z - complexify U.starProjection z ∈ (complexifySubmodule U)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro w hw
  have hw' : re w ∈ U ∧ im w ∈ U :=
    mem_complexifySubmodule.mp hw
  have hre : re z - U.starProjection (re z) ∈ Uᗮ :=
    U.sub_starProjection_mem_orthogonal (re z)
  have him : im z - U.starProjection (im z) ∈ Uᗮ :=
    U.sub_starProjection_mem_orthogonal (im z)
  apply Complex.ext
  · change
      ⟪re w, re z - U.starProjection (re z)⟫_ℝ +
        ⟪im w, im z - U.starProjection (im z)⟫_ℝ = 0
    rw [Submodule.inner_right_of_mem_orthogonal hw'.1 hre,
      Submodule.inner_right_of_mem_orthogonal hw'.2 him]
    simp
  · change
      ⟪re w, im z - U.starProjection (im z)⟫_ℝ -
        ⟪im w, re z - U.starProjection (re z)⟫_ℝ = 0
    rw [Submodule.inner_right_of_mem_orthogonal hw'.1 him,
      Submodule.inner_right_of_mem_orthogonal hw'.2 hre]
    simp

/-- Orthogonal complementation of a real subspace supplies an orthogonal
projection after complexification. -/
instance instHasOrthogonalProjectionComplexifySubmodule :
    (complexifySubmodule U).HasOrthogonalProjection where
  exists_orthogonal z :=
    ⟨complexify U.starProjection z, complexify_starProjection_mem U z,
      sub_complexify_starProjection_mem_orthogonal U z⟩

omit [CompleteSpace E] in
/-- The orthogonal projection onto a complexified real subspace is exactly the
coordinatewise complexification of the real orthogonal projection. -/

theorem starProjection_complexifySubmodule :
    (complexifySubmodule U).starProjection = complexify U.starProjection := by
  apply ContinuousLinearMap.ext
  intro z
  exact (complexifySubmodule U).eq_starProjection_of_mem_orthogonal
    (complexify_starProjection_mem U z)
    (sub_complexify_starProjection_mem_orthogonal U z)

omit [U.HasOrthogonalProjection] [CompleteSpace E] in
/-- Complexification commutes with orthogonal complement. -/
theorem complexifySubmodule_orthogonal :
    complexifySubmodule Uᗮ = (complexifySubmodule U)ᗮ := by
  ext z
  constructor
  · intro hz
    have hz' : re z ∈ Uᗮ ∧ im z ∈ Uᗮ :=
      mem_complexifySubmodule.mp hz
    rw [Submodule.mem_orthogonal]
    intro w hw
    have hw' : re w ∈ U ∧ im w ∈ U :=
      mem_complexifySubmodule.mp hw
    apply Complex.ext
    · change ⟪re w, re z⟫_ℝ + ⟪im w, im z⟫_ℝ = 0
      rw [Submodule.inner_right_of_mem_orthogonal hw'.1 hz'.1,
        Submodule.inner_right_of_mem_orthogonal hw'.2 hz'.2]
      simp
    · change ⟪re w, im z⟫_ℝ - ⟪im w, re z⟫_ℝ = 0
      rw [Submodule.inner_right_of_mem_orthogonal hw'.1 hz'.2,
        Submodule.inner_right_of_mem_orthogonal hw'.2 hz'.1]
      simp
  · intro hz
    rw [mem_complexifySubmodule]
    constructor
    · rw [Submodule.mem_orthogonal]
      intro u hu
      have h := hz (ofReal u)
        ((ofReal_mem_complexifySubmodule_iff U u).2 hu)
      simpa [inner_apply] using congrArg Complex.re h
    · rw [Submodule.mem_orthogonal]
      intro u hu
      have h := hz (ofReal u)
        ((ofReal_mem_complexifySubmodule_iff U u).2 hu)
      simpa [inner_apply] using congrArg Complex.im h

omit [CompleteSpace E] in
/-- Orthogonal-complement projection transport, in projection form. -/

theorem starProjection_complexifySubmodule_orthogonal :
    (complexifySubmodule U)ᗮ.starProjection = complexify Uᗮ.starProjection := by
  calc
    (complexifySubmodule U)ᗮ.starProjection =
        ContinuousLinearMap.id ℂ (RealComplexification E) -
          (complexifySubmodule U).starProjection :=
      Submodule.starProjection_orthogonal (complexifySubmodule U)
    _ = ContinuousLinearMap.id ℂ (RealComplexification E) -
          complexify U.starProjection := by
      rw [starProjection_complexifySubmodule]
    _ = complexify (ContinuousLinearMap.id ℝ E - U.starProjection) := by
      rw [complexify_sub, complexify_id]
    _ = complexify Uᗮ.starProjection := by
      rw [Submodule.starProjection_orthogonal]

variable {U}

omit [CompleteSpace E] in
/-- Exact preservation of the symmetric projection gap. -/
theorem projectionGap_complexifySubmodule
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    (complexifySubmodule U).projectionGap (complexifySubmodule V) =
      U.projectionGap V := by
  unfold Submodule.projectionGap
  rw [starProjection_complexifySubmodule,
    starProjection_complexifySubmodule, ← complexify_sub, norm_complexify]

omit [CompleteSpace E] in
/-- Exact preservation of the directed projection gap. -/
theorem directedProjectionGap_complexifySubmodule
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    (complexifySubmodule U).directedProjectionGap (complexifySubmodule V) =
      U.directedProjectionGap V := by
  unfold Submodule.directedProjectionGap
  rw [starProjection_complexifySubmodule_orthogonal,
    starProjection_complexifySubmodule, ← complexify_comp, norm_complexify]

omit [CompleteSpace E] in
/-- Davis--Kahan symmetric gap is unchanged by complexification. -/
theorem subspaceGap_complexifySubmodule
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    Submodule.projectionGap (complexifySubmodule U)
        (complexifySubmodule V) =
      U.projectionGap V :=
  projectionGap_complexifySubmodule U V

omit [CompleteSpace E] in
/-- Davis--Kahan directed gap is unchanged by complexification. -/
theorem directedGap_complexifySubmodule
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    Submodule.directedProjectionGap (complexifySubmodule U)
        (complexifySubmodule V) =
      U.directedProjectionGap V :=
  directedProjectionGap_complexifySubmodule U V

omit [CompleteSpace E] in
/-- Acuteness is preserved and reflected by complexification. -/
theorem isUniformlyAcute_complexifySubmodule_iff
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    TauCeti.DavisKahan.IsUniformlyAcute (complexifySubmodule U)
        (complexifySubmodule V) ↔
      TauCeti.DavisKahan.IsUniformlyAcute U V := by
  simp only [TauCeti.DavisKahan.IsUniformlyAcute,
    subspaceGap_complexifySubmodule]

omit [CompleteSpace E] in
/-- Quarter-acuteness is preserved and reflected by complexification. -/
theorem isQuarterAcute_complexifySubmodule_iff
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    TauCeti.DavisKahan.IsQuarterAcute (complexifySubmodule U)
        (complexifySubmodule V) ↔
      TauCeti.DavisKahan.IsQuarterAcute U V := by
  simp only [TauCeti.DavisKahan.IsQuarterAcute,
    subspaceGap_complexifySubmodule]

omit [CompleteSpace E] in
/-- Reduction by a real operator is preserved and reflected by operator and
subspace complexification. -/
theorem complexify_reduces_iff (T : E →L[ℝ] E) (U : Submodule ℝ E)
     :
    (complexify T).Reduces (complexifySubmodule U) ↔ T.Reduces U := by
  constructor
  · rintro ⟨hU, hUperp⟩
    constructor
    · intro x hx
      have hcx := hU (ofReal x)
        ((ofReal_mem_complexifySubmodule_iff U x).2 hx)
      have hcx' : re (complexify T (ofReal x)) ∈ U :=
        (mem_complexifySubmodule.mp hcx).1
      simpa using hcx'
    · intro x hx
      have hxC : ofReal x ∈ (complexifySubmodule U)ᗮ := by
        rw [← complexifySubmodule_orthogonal U]
        exact (ofReal_mem_complexifySubmodule_iff Uᗮ x).2 hx
      have hcx := hUperp (ofReal x) hxC
      have hcx' : complexify T (ofReal x) ∈ complexifySubmodule Uᗮ := by
        simpa only [complexifySubmodule_orthogonal U] using hcx
      have hre : re (complexify T (ofReal x)) ∈ Uᗮ :=
        (mem_complexifySubmodule.mp hcx').1
      simpa using hre
  · rintro ⟨hU, hUperp⟩
    constructor
    · intro z hz
      have hz' : re z ∈ U ∧ im z ∈ U :=
        mem_complexifySubmodule.mp hz
      rw [mem_complexifySubmodule]
      exact ⟨hU (re z) hz'.1, hU (im z) hz'.2⟩
    · intro z hz
      have hzC : z ∈ complexifySubmodule Uᗮ := by
        simpa only [complexifySubmodule_orthogonal U] using hz
      have hz' : re z ∈ Uᗮ ∧ im z ∈ Uᗮ :=
        mem_complexifySubmodule.mp hzC
      have hresult : complexify T z ∈ complexifySubmodule Uᗮ := by
        rw [mem_complexifySubmodule]
        exact ⟨hUperp (re z) hz'.1, hUperp (im z) hz'.2⟩
      simpa only [complexifySubmodule_orthogonal U] using hresult

end

end RealComplexification
end Foundation
end DavisKahan
end TauCeti
