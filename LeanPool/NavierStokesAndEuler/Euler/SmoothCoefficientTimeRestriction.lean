/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientPathJets
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevLinear

@[expose] public section

/-!
# Restricting the time parameter of genuine smooth coefficient fields

Continuous precomposition keeps the actual spatial jets and has norm at
most one. In particular it does not enlarge the spatial factorial radius
when a source field is restricted to a history interval or shifted to a
forward interval.
-/

noncomputable section

namespace EulerMeanCoefficients

open EulerSmoothLimit
open scoped ContDiff BoundedContinuousFunction

variable {K L V : Type*} [TopologicalSpace K] [CompactSpace K]
  [TopologicalSpace L] [CompactSpace L]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

private local instance : NormedAddCommGroup (Space →ᵇ V) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ V) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (Space →ᵇ (Space [×n]→L[ℝ] V)) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (Space →ᵇ (Space [×n]→L[ℝ] V)) := inferInstance

namespace SmoothCoefficientPath

/-- Actual time precomposition, including every spatial jet. -/
def comp (A : SmoothCoefficientPath K V) (φ : C(L,K)) : SmoothCoefficientPath L V where
  field := A.field.comp φ
  smooth t := A.smooth (φ t)
  jet n := (A.jet n).comp φ
  jet_eq n t x := A.jet_eq n (φ t) x

@[simp] theorem comp_apply (A : SmoothCoefficientPath K V) (φ : C(L,K)) (t : L) (x : Space) :
    (A.comp φ).field t x = A.field (φ t) x := rfl

theorem comp_norm_le (A : SmoothCoefficientPath K V) (φ : C(L,K)) :
    ‖(A.comp φ).field‖ ≤ ‖A.field‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro t
  exact A.field.norm_coe_le_norm (φ t)

theorem comp_jet_norm_le (A : SmoothCoefficientPath K V) (φ : C(L,K)) (n : ℕ) :
    ‖(A.comp φ).jet n‖ ≤ ‖A.jet n‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro t
  exact (A.jet n).norm_coe_le_norm (φ t)

theorem comp_translation (A : SmoothCoefficientPath K V) (φ : C(L,K)) (a : Space) :
    translateCoefficientPath (A.comp φ).field a =
      (translateCoefficientPath A.field a).comp φ := rfl

/-- A continuous change of time parameter preserves each literal spatial
derivative bound with exactly the same constant. -/
theorem comp_derivative_bound (A : SmoothCoefficientPath K V) (φ : C(L,K))
    (n : ℕ) (C : ℝ)
    (hb : ∀ t x, ‖iteratedFDeriv ℝ n (A.field t : Space → V) x‖ ≤ C)
    (t : L) (x : Space) :
    ‖iteratedFDeriv ℝ n ((A.comp φ).field t : Space → V) x‖ ≤ C :=
  hb (φ t) x

theorem comp_translation_bound (A : SmoothCoefficientPath K V) (φ : C(L,K))
    (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ t x, ‖iteratedFDeriv ℝ n (A.field t : Space → V) x‖ ≤ C)
    (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath (A.comp φ).field) a‖ ≤ C :=
  (A.comp φ).norm_iteratedFDeriv_translation_le n C hC
    (A.comp_derivative_bound φ n C hb) a

end SmoothCoefficientPath

end EulerMeanCoefficients

namespace EulerTimeIntervalRestriction

open Set EulerVolterraConvolution

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def initialInclusion (S τ : ℝ) (hτS : τ ≤ S) : C(Icc (0 : ℝ) τ,Icc (0 : ℝ) S) :=
  ⟨fun t => ⟨t,t.property.1,t.property.2.trans hτS⟩,
    continuous_subtype_val.subtype_mk _⟩

def tailInclusion (S τ : ℝ) (hτ : 0 ≤ τ) : C(Icc (0 : ℝ) (S-τ),Icc (0 : ℝ) S) :=
  ⟨fun t => ⟨τ+t,add_nonneg hτ t.property.1,by linarith [t.property.2]⟩,
    (continuous_const.add continuous_subtype_val).subtype_mk _⟩

def initialPath (S τ : ℝ) (hτS : τ ≤ S) : C(Icc (0 : ℝ) S,V) →L[ℝ] C(Icc (0 : ℝ) τ,V) :=
  ContinuousMap.compCLM ℝ V (initialInclusion S τ hτS)

def tailPath (S τ : ℝ) (hτ : 0 ≤ τ) : C(Icc (0 : ℝ) S,V) →L[ℝ] C(Icc (0 : ℝ) (S-τ),V) :=
  ContinuousMap.compCLM ℝ V (tailInclusion S τ hτ)

theorem initialPath_norm (S τ : ℝ) (hτS : τ ≤ S) : ‖initialPath (V := V) S τ hτS‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg A)).2
  intro t
  exact A.norm_coe_le_norm _

theorem tailPath_norm (S τ : ℝ) (hτ : 0 ≤ τ) : ‖tailPath (V := V) S τ hτ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg A)).2
  intro t
  exact A.norm_coe_le_norm _

theorem initial_extend (S τ : ℝ) (hS : 0 ≤ S) (hτ : 0 ≤ τ) (hτS : τ ≤ S)
    (A : C(Icc (0 : ℝ) S,V)) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) τ) :
    extendPath τ hτ (initialPath S τ hτS A) t = extendPath S hS A t := by
  simp only [extendPath, projIcc_of_mem hτ ht, initialPath, ContinuousMap.compCLM_apply,
    ContinuousMap.comp_apply, initialInclusion]
  rw [projIcc_of_mem hS ⟨ht.1,ht.2.trans hτS⟩]
  rfl

theorem tail_extend (S τ : ℝ) (hS : 0 ≤ S) (hτ : 0 ≤ τ) (hτS : τ ≤ S)
    (A : C(Icc (0 : ℝ) S,V)) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (S-τ)) :
    extendPath (S-τ) (sub_nonneg.mpr hτS) (tailPath S τ hτ A) t = extendPath S hS A (τ+t) := by
  have hs : τ+t ∈ Icc (0 : ℝ) S := ⟨add_nonneg hτ ht.1,by linarith [ht.2]⟩
  simp only [extendPath, projIcc_of_mem (sub_nonneg.mpr hτS) ht, tailPath,
    ContinuousMap.compCLM_apply,
    ContinuousMap.comp_apply, tailInclusion, projIcc_of_mem hS hs]
  rfl

/-- A true within-time derivative restricts to the closed history interval. -/
theorem initialPath_hasDerivWithinAt (S τ : ℝ) (hS : 0 ≤ S) (hτ : 0 ≤ τ) (hτS : τ ≤ S)
    (A A₁ : C(Icc (0 : ℝ) S,V))
    (hd : ∀ t ∈ Icc (0 : ℝ) S, HasDerivWithinAt (extendPath S hS A)
      (extendPath S hS A₁ t) (Icc (0 : ℝ) S) t)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) τ) :
    HasDerivWithinAt (extendPath τ hτ (initialPath S τ hτS A))
      (extendPath τ hτ (initialPath S τ hτS A₁) t) (Icc (0 : ℝ) τ) t := by
  rw [initial_extend S τ hS hτ hτS A₁ t ht]
  exact ((hd t ⟨ht.1,ht.2.trans hτS⟩).mono (Icc_subset_Icc le_rfl hτS)).congr_of_mem
    (fun s hs => initial_extend S τ hS hτ hτS A s hs) ht

/-- Translation of the time variable has derivative one, including the
within-derivatives at both ends of the forward interval. -/
theorem tailPath_hasDerivWithinAt (S τ : ℝ) (hS : 0 ≤ S) (hτ : 0 ≤ τ) (hτS : τ ≤ S)
    (A A₁ : C(Icc (0 : ℝ) S,V))
    (hd : ∀ t ∈ Icc (0 : ℝ) S, HasDerivWithinAt (extendPath S hS A)
      (extendPath S hS A₁ t) (Icc (0 : ℝ) S) t)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (S-τ)) :
    HasDerivWithinAt (extendPath (S-τ) (sub_nonneg.mpr hτS) (tailPath S τ hτ A))
      (extendPath (S-τ) (sub_nonneg.mpr hτS) (tailPath S τ hτ A₁) t) (Icc (0 : ℝ) (S-τ)) t := by
  have hm : MapsTo (fun s : ℝ => τ+s) (Icc (0 : ℝ) (S-τ)) (Icc (0 : ℝ) S) := by
    intro s hs
    exact ⟨add_nonneg hτ hs.1,by linarith [hs.2]⟩
  have hc := (hd (τ+t) (hm ht)).scomp t ((hasDerivAt_id t).const_add τ).hasDerivWithinAt hm
  rw [tail_extend S τ hS hτ hτS A₁ t ht]
  simpa only [one_smul] using hc.congr_of_mem
    (fun s hs => tail_extend S τ hS hτ hτS A s hs) ht

end EulerTimeIntervalRestriction
