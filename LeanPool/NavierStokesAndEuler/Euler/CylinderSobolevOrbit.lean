/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderOrbitSobolev
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevOperators
import LeanPool.NavierStokesAndEuler.Euler.CylinderPathWords
import LeanPool.NavierStokesAndEuler.Euler.ParameterWordHigher
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Smoothness of the actual translated continuous Sobolev path

The finite Sobolev array consists of genuine derivative words of the given
L² orbit. A bounded retraction of the closed compatible-array space proves
its smoothness in the complete Hq path norm. It is used qualitatively only.
-/

section

/-!
Every closed subspace of a finite product of Hilbert spaces has a bounded
retraction. We use the equivalent Hilbert product norm only to construct the
retraction; all stated spaces retain their original sup norms.
-/

@[expose] public section

noncomputable section

namespace EulerHilbertProductSubspace

open ContinuousLinearMap

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Hilbert equiv, given by `(PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => E)).symm`. -/
def hilbertEquiv : (ι → E) ≃L[ℝ] PiLp 2 (fun _ : ι => E) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => E)).symm

/-- Hilbert subspace, given by `S.mapEquiv hilbertEquiv`. -/
def hilbertSubspace (S : ClosedSubmodule ℝ (ι → E)) :
    ClosedSubmodule ℝ (PiLp 2 (fun _ : ι => E)) := S.mapEquiv hilbertEquiv

/-- Restriction as an element of `hilbertSubspace S →L[ℝ] S`. -/
def restriction (S : ClosedSubmodule ℝ (ι → E)) : hilbertSubspace S →L[ℝ] S :=
  (hilbertEquiv.symm.toContinuousLinearMap.comp (hilbertSubspace
      S).toSubmodule.subtypeL).codRestrict
    S.toSubmodule (fun u => (ClosedSubmodule.mem_mapEquiv_iff hilbertEquiv S u).mp u.property)

/-- A genuine bounded retraction, obtained from orthogonal projection in the equivalent Hilbert
norm. -/
def retraction (S : ClosedSubmodule ℝ (ι → E)) : (ι → E) →L[ℝ] S :=
  (restriction S).comp ((hilbertSubspace S).toSubmodule.orthogonalProjectionOnto.comp
    hilbertEquiv.toContinuousLinearMap)

@[simp] theorem retraction_subtype (S : ClosedSubmodule ℝ (ι → E)) (u : S) :
    retraction S (u : ι → E) = u := by
  have hu : hilbertEquiv (u : ι → E) ∈ hilbertSubspace S :=
    (ClosedSubmodule.mem_mapEquiv_iff' hilbertEquiv S (u : ι → E)).mpr u.property
  have hp := (hilbertSubspace S).toSubmodule.orthogonalProjectionOnto_mem_subspace_eq_self
    (⟨hilbertEquiv (u : ι → E),hu⟩ : hilbertSubspace S)
  apply Subtype.ext
  change hilbertEquiv.symm
    (((hilbertSubspace S).toSubmodule.orthogonalProjectionOnto (hilbertEquiv (u : ι → E))) :
      PiLp 2 (fun _ : ι => E)) = (u : ι → E)
  rw [hp]
  exact hilbertEquiv.symm_apply_apply (u : ι → E)

section Paths

variable {K V : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Interchange a finite tuple and a continuous path by a bounded linear map. -/
def packPaths : (ι → C(K,V)) →L[ℝ] C(K,ι → V) := by
  classical
  exact ∑ i : ι, ((ContinuousLinearMap.single ℝ (fun _ : ι => V) i).compLeftContinuous ℝ K).comp
    (ContinuousLinearMap.proj i)

omit [CompactSpace K] in
@[simp] theorem packPaths_apply (p : ι → C(K, V)) (t : K) (i : ι) :
    packPaths (ι := ι) (K := K) (V := V) p t i = p i t := by
  classical
  simp only [packPaths, sum_apply, comp_apply, proj_apply, compLeftContinuous_apply,
      ZeroHom.toFun_eq_coe,
    AddMonoidHom.toZeroHom_coe, ContinuousMap.coe_sum, Finset.sum_apply]
  change (∑ j : ι, Pi.single j (p j t) i) = p i t
  simp [Pi.single_apply]

end Paths
end EulerHilbertProductSubspace

end
end

end

@[expose] public section

noncomputable section

namespace EulerCylinderSmoothOrbit

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSobolevSpace EulerLpCylinderTranslation EulerParameterWordGevrey
  EulerHilbertProductSubspace EulerCylinderSobolev
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Sobolev path translate, given by `(sobolevTranslation P q (coveringMap P
a)).compLeftContinuous ℝ K`. -/
def sobolevPathTranslate (q : ℕ) (a : LiftTangent) :
    C(K,SobolevSpace P q) →L[ℝ] C(K,SobolevSpace P q) :=
  (sobolevTranslation P q (coveringMap P a)).compLeftContinuous ℝ K

/-- Sobolev orbit, given by `sobolevPathTranslate P q a (sobolevPath P q p hp)`. -/
def sobolevOrbit (q : ℕ) (p : C(K, LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p)) (a : LiftTangent) :
    C(K,SobolevSpace P q) := sobolevPathTranslate P q a (sobolevPath P q p hp)

@[simp] theorem sobolevOrbit_value (q : ℕ) (p : C(K, LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
    (a : LiftTangent) (t : K) : value P (sobolevOrbit P q p hp a t) = pathTranslate P a p t := by
  change translation P (coveringMap P a) (value P (sobolevPath P q p hp t)) = _
  rw [sobolevPath_value]
  rfl

theorem sobolevOrbit_coordinate (q : ℕ) (p : C(K, LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
    (a : LiftTangent) (t : K) (w : SobolevWord q) :
    (sobolevOrbit P q p hp a t).val w =
      wordDerivative standardDirection (fun b : LiftTangent => pathTranslate P b p) w.2 a t := by
  have hc : (sobolevPath P q p hp t).val w = wordPath P p w.2 t := by
    exact (sobolev_coordinate P q (p t) (path_evaluation_smooth P p hp t) w).trans
      (path_word_evaluation P p hp w.2 t)
  change translate P a ((sobolevPath P q p hp t).val w) = _
  rw [hc]
  exact congrArg (fun z : C(K,LiftL2 P) => z t) (wordPath_translation P p hp w.2 a)

/-- Assemble sobolev path, given by `((retraction (sobolevSubspace P q)).compLeftContinuous ℝ
K).comp packPaths`. -/
def assembleSobolevPath (q : ℕ) :
    (SobolevWord q → C(K,LiftL2 P)) →L[ℝ] C(K,SobolevSpace P q) :=
  ((retraction (sobolevSubspace P q)).compLeftContinuous ℝ K).comp packPaths

theorem sobolevOrbit_eq_assemble (q : ℕ) (p : C(K, LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p)) (a : LiftTangent) :
    sobolevOrbit P q p hp a = assembleSobolevPath P q
      (fun w => wordDerivative standardDirection (fun b : LiftTangent => pathTranslate P b p) w.2
          a) := by
  apply ContinuousMap.ext
  intro t
  have he : packPaths (fun w : SobolevWord q =>
        wordDerivative standardDirection (fun b : LiftTangent => pathTranslate P b p) w.2 a) t =
      (sobolevOrbit P q p hp a t).val := by
    funext w
    rw [packPaths_apply]
    exact (sobolevOrbit_coordinate P q p hp a t w).symm
  change sobolevOrbit P q p hp a t = retraction (sobolevSubspace P q) _
  exact ((congrArg (retraction (sobolevSubspace P q)) he).trans
    (retraction_subtype (sobolevSubspace P q) (sobolevOrbit P q p hp a t))).symm

/-- Actual L² orbit smoothness promotes to every fixed complete Sobolev path space. -/
theorem sobolevOrbit_contDiff (q : ℕ) (p : C(K, LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p)) :
    ContDiff ℝ ∞ (sobolevOrbit P q p hp) := by
  have he : sobolevOrbit P q p hp = fun a => assembleSobolevPath P q
      (fun w => wordDerivative standardDirection (fun b : LiftTangent => pathTranslate P b p) w.2
          a) :=
    funext (sobolevOrbit_eq_assemble P q p hp)
  rw [he]
  apply (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := SobolevWord q → C(K,LiftL2 P)) (F := C(K,SobolevSpace P q)) (assembleSobolevPath P
        q)).comp
  apply contDiff_pi.mpr
  intro w
  exact wordDerivative_contDiff standardDirection (fun b : LiftTangent => pathTranslate P b p) hp
      w.2

end EulerCylinderSmoothOrbit
