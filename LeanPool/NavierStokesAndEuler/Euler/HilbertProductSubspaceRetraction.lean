/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.ContinuousMap.Algebra

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
