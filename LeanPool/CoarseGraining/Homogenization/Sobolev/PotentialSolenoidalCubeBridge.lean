/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicCubeTranslation
import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicPartition
import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalOriginCubeBridge
import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalTranslation
import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalL2Recovery

/-! # Potential Solenoidal Cube Bridge -/

namespace Homogenization

/-!
# Potential and solenoidal transport across triadic cube realizations

The deterministic multiscale layer mostly uses the half-open `cubeSet Q`, while
the Sobolev layer often proves things first on the open cube `openCubeSet Q`.
This file promotes the existing centered-cube bridge to arbitrary triadic cubes
by translating to the centered cube, using the origin-cube bridge, and
translating back.
-/

noncomputable section

namespace H1Function

@[simp] theorem toCubeSetOriginCube_grad {d : ℕ} [NeZero d] {n : ℤ}
    (u : H1Function (openCubeSet (originCube d n))) :
    u.toCubeSetOriginCube.grad = u.grad :=
  rfl

@[simp] theorem toCubeSetOriginCube_toFun {d : ℕ} [NeZero d] {n : ℤ}
    (u : H1Function (openCubeSet (originCube d n))) :
    u.toCubeSetOriginCube.toFun = u.toFun :=
  rfl

private noncomputable def castDomain {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H1Function U) : H1Function V :=
  hUV ▸ u

@[simp] theorem grad_castDomain {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H1Function U) :
    (castDomain hUV u).grad = u.grad := by
  subst V
  rfl

@[simp] theorem toFun_castDomain {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H1Function U) :
    (castDomain hUV u).toFun = u.toFun := by
  subst V
  rfl

/-- Promote an `H¹` witness on an open triadic cube to the corresponding
half-open triadic cube. -/
noncomputable def toCubeSet {d : ℕ} [NeZero d] {Q : TriadicCube d}
    (u : H1Function (openCubeSet Q)) : H1Function (cubeSet Q) := by
  let z : Vec d := triadicCubeShift Q
  let Uo : Set (Vec d) := openCubeSet (originCube d Q.scale)
  let Uc : Set (Vec d) := cubeSet (originCube d Q.scale)
  have hopen : openCubeSet Q = translateSet z Uo := by
    simpa [z, Uo] using openCubeSet_eq_translateSet_originCube_of_triadicCube Q
  let uTranslated : H1Function (translateSet z Uo) := castDomain hopen u
  let uOriginTranslated : H1Function (translateSet (-z) (translateSet z Uo)) :=
    uTranslated.translate (-z)
  have hdomain : translateSet (-z) (translateSet z Uo) = Uo := by
    simpa [sub_eq_add_neg] using (translateSet_translateSet (d := d) z (-z) Uo)
  let uOriginOpen : H1Function Uo := castDomain hdomain uOriginTranslated
  let uOriginCube : H1Function Uc := uOriginOpen.toCubeSetOriginCube
  have hcube : cubeSet Q = translateSet z Uc := by
    simpa [z, Uc] using cubeSet_eq_translateSet_originCube_of_triadicCube Q
  let uCubeTranslated : H1Function (translateSet z Uc) := uOriginCube.translate z
  exact castDomain hcube.symm uCubeTranslated

@[simp] theorem grad_toCubeSet {d : ℕ} [NeZero d] {Q : TriadicCube d}
    (u : H1Function (openCubeSet Q)) :
    u.toCubeSet.grad = u.grad := by
  funext x
  simp [toCubeSet]

@[simp] theorem toFun_toCubeSet {d : ℕ} [NeZero d] {Q : TriadicCube d}
    (u : H1Function (openCubeSet Q)) :
    u.toCubeSet.toFun = u.toFun := by
  funext x
  simp [toCubeSet]

/-- Restrict an `H¹` witness on a half-open triadic cube to its open
realization. -/
noncomputable def toOpenCubeSet {d : ℕ} {Q : TriadicCube d}
    (u : H1Function (cubeSet Q)) : H1Function (openCubeSet Q) :=
  u.restrict (isOpen_openCubeSet Q) (openCubeSet_subset_cubeSet Q)

@[simp] theorem grad_toOpenCubeSet {d : ℕ} {Q : TriadicCube d}
    (u : H1Function (cubeSet Q)) :
    u.toOpenCubeSet.grad = u.grad :=
  rfl

@[simp] theorem toFun_toOpenCubeSet {d : ℕ} {Q : TriadicCube d}
    (u : H1Function (cubeSet Q)) :
    u.toOpenCubeSet.toFun = u.toFun :=
  rfl

end H1Function

namespace H10Function

private noncomputable def castDomain {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H10Function U) : H10Function V :=
  hUV ▸ u

@[simp] theorem castDomain_toH1Function_grad {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H10Function U) :
    (castDomain hUV u).toH1Function.grad = u.toH1Function.grad := by
  subst V
  rfl

@[simp] theorem castDomain_toH1Function_toFun {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (u : H10Function U) :
    (castDomain hUV u).toH1Function.toFun = u.toH1Function.toFun := by
  subst V
  rfl

/-- Promote an `H¹₀` witness on an open triadic cube to the corresponding
half-open triadic cube. -/
noncomputable def toCubeSet {d : ℕ} [NeZero d] {Q : TriadicCube d}
    (u : H10Function (openCubeSet Q)) : H10Function (cubeSet Q) := by
  let z : Vec d := triadicCubeShift Q
  let Uo : Set (Vec d) := openCubeSet (originCube d Q.scale)
  let Uc : Set (Vec d) := cubeSet (originCube d Q.scale)
  have hopen : openCubeSet Q = translateSet z Uo := by
    simpa [z, Uo] using openCubeSet_eq_translateSet_originCube_of_triadicCube Q
  let uTranslated : H10Function (translateSet z Uo) := castDomain hopen u
  let uOriginTranslated : H10Function (translateSet (-z) (translateSet z Uo)) :=
    uTranslated.translate (-z)
  have hdomain : translateSet (-z) (translateSet z Uo) = Uo := by
    simpa [sub_eq_add_neg] using (translateSet_translateSet (d := d) z (-z) Uo)
  let uOriginOpen : H10Function Uo := castDomain hdomain uOriginTranslated
  let uOriginCube : H10Function Uc := uOriginOpen.toCubeSetOriginCube
  have hcube : cubeSet Q = translateSet z Uc := by
    simpa [z, Uc] using cubeSet_eq_translateSet_originCube_of_triadicCube Q
  let uCubeTranslated : H10Function (translateSet z Uc) := uOriginCube.translate z
  exact castDomain hcube.symm uCubeTranslated

@[simp] theorem toCubeSet_toH1Function_grad {d : ℕ} [NeZero d] {Q : TriadicCube d}
    (u : H10Function (openCubeSet Q)) :
    u.toCubeSet.toH1Function.grad = u.toH1Function.grad := by
  funext x
  simp [toCubeSet]

@[simp] theorem toCubeSet_toH1Function_toFun {d : ℕ} [NeZero d] {Q : TriadicCube d}
    (u : H10Function (openCubeSet Q)) :
    u.toCubeSet.toH1Function.toFun = u.toH1Function.toFun := by
  funext x
  simp [toCubeSet]

/-- Restrict an `H¹₀` witness on a half-open triadic cube to the corresponding
open triadic cube. -/
noncomputable def toOpenCubeSet {d : ℕ} [NeZero d] {Q : TriadicCube d}
    (u : H10Function (cubeSet Q)) : H10Function (openCubeSet Q) := by
  let z : Vec d := triadicCubeShift Q
  let Uc : Set (Vec d) := cubeSet (originCube d Q.scale)
  let Uo : Set (Vec d) := openCubeSet (originCube d Q.scale)
  have hcube : cubeSet Q = translateSet z Uc := by
    simpa [z, Uc] using cubeSet_eq_translateSet_originCube_of_triadicCube Q
  let uTranslated : H10Function (translateSet z Uc) := castDomain hcube u
  let uOriginTranslated : H10Function (translateSet (-z) (translateSet z Uc)) :=
    uTranslated.translate (-z)
  have hdomain : translateSet (-z) (translateSet z Uc) = Uc := by
    simpa [sub_eq_add_neg] using (translateSet_translateSet (d := d) z (-z) Uc)
  let uOriginCube : H10Function Uc := castDomain hdomain uOriginTranslated
  let uOriginOpen : H10Function Uo := uOriginCube.toOpenCubeSetOriginCube
  have hopen : openCubeSet Q = translateSet z Uo := by
    simpa [z, Uo] using openCubeSet_eq_translateSet_originCube_of_triadicCube Q
  let uOpenTranslated : H10Function (translateSet z Uo) := uOriginOpen.translate z
  exact castDomain hopen.symm uOpenTranslated

@[simp] theorem toOpenCubeSet_toH1Function_grad {d : ℕ} [NeZero d] {Q : TriadicCube d}
    (u : H10Function (cubeSet Q)) :
    u.toOpenCubeSet.toH1Function.grad = u.toH1Function.grad := by
  funext x
  simp [toOpenCubeSet]

@[simp] theorem toOpenCubeSet_toH1Function_toFun {d : ℕ} [NeZero d] {Q : TriadicCube d}
    (u : H10Function (cubeSet Q)) :
    u.toOpenCubeSet.toH1Function.toFun = u.toH1Function.toFun := by
  funext x
  simp [toOpenCubeSet]

end H10Function

theorem isPotentialOn_openCubeSet_triadicCube_of_cubeSet
    {d : ℕ} {Q : TriadicCube d} {f : Vec d → Vec d}
    (hf : IsPotentialOn (cubeSet Q) f) :
    IsPotentialOn (openCubeSet Q) f := by
  rcases hf with ⟨u, rfl⟩
  exact ⟨u.toOpenCubeSet, rfl⟩

theorem isPotentialOn_cubeSet_triadicCube_of_openCubeSet
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {f : Vec d → Vec d}
    (hf : IsPotentialOn (openCubeSet Q) f) :
    IsPotentialOn (cubeSet Q) f := by
  rcases hf with ⟨u, rfl⟩
  exact ⟨u.toCubeSet, by simp⟩

theorem isPotentialOn_cubeSet_triadicCube_iff_openCubeSet
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {f : Vec d → Vec d} :
    IsPotentialOn (cubeSet Q) f ↔ IsPotentialOn (openCubeSet Q) f := by
  constructor
  · exact isPotentialOn_openCubeSet_triadicCube_of_cubeSet
  · exact isPotentialOn_cubeSet_triadicCube_of_openCubeSet

theorem isPotentialZeroTraceOn_openCubeSet_triadicCube_of_cubeSet
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {f : Vec d → Vec d}
    (hf : IsPotentialZeroTraceOn (cubeSet Q) f) :
    IsPotentialZeroTraceOn (openCubeSet Q) f := by
  rcases hf with ⟨u, rfl⟩
  exact ⟨u.toOpenCubeSet, by simp⟩

theorem isPotentialZeroTraceOn_cubeSet_triadicCube_of_openCubeSet
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {f : Vec d → Vec d}
    (hf : IsPotentialZeroTraceOn (openCubeSet Q) f) :
    IsPotentialZeroTraceOn (cubeSet Q) f := by
  rcases hf with ⟨u, rfl⟩
  exact ⟨u.toCubeSet, by simp⟩

theorem isPotentialZeroTraceOn_cubeSet_triadicCube_iff_openCubeSet
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {f : Vec d → Vec d} :
    IsPotentialZeroTraceOn (cubeSet Q) f ↔ IsPotentialZeroTraceOn (openCubeSet Q) f := by
  constructor
  · exact isPotentialZeroTraceOn_openCubeSet_triadicCube_of_cubeSet
  · exact isPotentialZeroTraceOn_cubeSet_triadicCube_of_openCubeSet

theorem isSolenoidalOn_cubeSet_triadicCube_of_openCubeSet
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {g : Vec d → Vec d}
    (hg : IsSolenoidalOn (openCubeSet Q) g) :
    IsSolenoidalOn (cubeSet Q) g := by
  intro φ
  have hopen := hg φ.toOpenCubeSet
  have hset :
      ∫ x in cubeSet Q, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q,
          vecDot (g x) (φ.toOpenCubeSet.toH1Function.grad x) ∂MeasureTheory.volume := by
    simpa using
      (setIntegral_cubeSet_eq_setIntegral_openCubeSet
        (Q := Q) (f := fun x => vecDot (g x) (φ.toH1Function.grad x)))
  rw [hset]
  simpa using hopen

theorem isSolenoidalOn_openCubeSet_triadicCube_of_cubeSet
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {g : Vec d → Vec d}
    (hg : IsSolenoidalOn (cubeSet Q) g) :
    IsSolenoidalOn (openCubeSet Q) g := by
  intro φ
  have hcube := hg φ.toCubeSet
  have hset :
      ∫ x in cubeSet Q,
          vecDot (g x) (φ.toCubeSet.toH1Function.grad x) ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume := by
    simpa using
      (setIntegral_cubeSet_eq_setIntegral_openCubeSet
        (Q := Q) (f := fun x => vecDot (g x) (φ.toCubeSet.toH1Function.grad x)))
  rw [hset] at hcube
  simpa using hcube

theorem isSolenoidalOn_cubeSet_triadicCube_iff_openCubeSet
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {g : Vec d → Vec d} :
    IsSolenoidalOn (cubeSet Q) g ↔ IsSolenoidalOn (openCubeSet Q) g := by
  constructor
  · exact isSolenoidalOn_openCubeSet_triadicCube_of_cubeSet
  · exact isSolenoidalOn_cubeSet_triadicCube_of_openCubeSet

theorem isSolenoidalZeroNormalTraceOn_cubeSet_triadicCube_of_openCubeSet
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {g : Vec d → Vec d}
    (hg : IsSolenoidalZeroNormalTraceOn (openCubeSet Q) g) :
    IsSolenoidalZeroNormalTraceOn (cubeSet Q) g := by
  intro φ
  have hopen := hg φ.toOpenCubeSet
  have hset :
      ∫ x in cubeSet Q, vecDot (g x) (φ.grad x) ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q,
          vecDot (g x) (φ.toOpenCubeSet.grad x) ∂MeasureTheory.volume := by
    simpa using
      (setIntegral_cubeSet_eq_setIntegral_openCubeSet
        (Q := Q) (f := fun x => vecDot (g x) (φ.grad x)))
  rw [hset]
  simpa using hopen

theorem isSolenoidalZeroNormalTraceOn_openCubeSet_triadicCube_of_cubeSet
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {g : Vec d → Vec d}
    (hg : IsSolenoidalZeroNormalTraceOn (cubeSet Q) g) :
    IsSolenoidalZeroNormalTraceOn (openCubeSet Q) g := by
  intro φ
  have hcube := hg φ.toCubeSet
  have hset :
      ∫ x in cubeSet Q,
          vecDot (g x) (φ.toCubeSet.grad x) ∂MeasureTheory.volume =
        ∫ x in openCubeSet Q, vecDot (g x) (φ.grad x) ∂MeasureTheory.volume := by
    simpa using
      (setIntegral_cubeSet_eq_setIntegral_openCubeSet
        (Q := Q) (f := fun x => vecDot (g x) (φ.toCubeSet.grad x)))
  rw [hset] at hcube
  simpa using hcube

theorem isSolenoidalZeroNormalTraceOn_cubeSet_triadicCube_iff_openCubeSet
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {g : Vec d → Vec d} :
    IsSolenoidalZeroNormalTraceOn (cubeSet Q) g ↔
      IsSolenoidalZeroNormalTraceOn (openCubeSet Q) g := by
  constructor
  · exact isSolenoidalZeroNormalTraceOn_openCubeSet_triadicCube_of_cubeSet
  · exact isSolenoidalZeroNormalTraceOn_cubeSet_triadicCube_of_openCubeSet

namespace IsPotentialOn

/-- Restrict a potential field on a half-open triadic cube to a descendant
half-open triadic cube. -/
theorem restrict_cubeSet_of_mem_descendantsAtDepth
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {n : ℕ}
    {u : Vec d → Vec d}
    (hu : IsPotentialOn (cubeSet Q) u)
    (hR : R ∈ descendantsAtDepth Q n) :
    IsPotentialOn (cubeSet R) u := by
  have huOpenQ : IsPotentialOn (openCubeSet Q) u :=
    isPotentialOn_openCubeSet_triadicCube_of_cubeSet hu
  rcases huOpenQ with ⟨v, hv⟩
  have huOpenR : IsPotentialOn (openCubeSet R) u := by
    refine ⟨v.restrict (isOpen_openCubeSet R)
      (openCubeSet_subset_of_mem_descendantsAtDepth hR), ?_⟩
    simpa [H1Function.restrict] using hv
  exact isPotentialOn_cubeSet_triadicCube_of_openCubeSet huOpenR

end IsPotentialOn

namespace IsSolenoidalOn

/-- Restrict a solenoidal field on a half-open triadic cube to a descendant
half-open triadic cube. -/
theorem restrict_cubeSet_of_mem_descendantsAtDepth
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {n : ℕ}
    {F : Vec d → Vec d}
    (hF : IsSolenoidalOn (cubeSet Q) F)
    (hR : R ∈ descendantsAtDepth Q n)
    (hmemR : MemVectorL2 (cubeSet R) F) :
    IsSolenoidalOn (cubeSet R) F := by
  have : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet R).isFiniteMeasure_restrict_volume
  have hOpenQ : IsSolenoidalOn (openCubeSet Q) F :=
    isSolenoidalOn_openCubeSet_triadicCube_of_cubeSet hF
  have hmemOpenR : MemVectorL2 (openCubeSet R) F := by
    simpa [MemVectorL2, volumeMeasureOn, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
      using hmemR
  have hOpenR : IsSolenoidalOn (openCubeSet R) F :=
    hOpenQ.restrict_of_isOpen_of_memVectorL2
      (isOpen_openCubeSet Q) (isOpen_openCubeSet R)
      (openCubeSet_subset_of_mem_descendantsAtDepth hR) hmemOpenR
  exact isSolenoidalOn_cubeSet_triadicCube_of_openCubeSet hOpenR

end IsSolenoidalOn

end

end Homogenization
