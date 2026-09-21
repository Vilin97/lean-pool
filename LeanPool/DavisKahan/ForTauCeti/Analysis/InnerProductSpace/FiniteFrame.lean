/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 High, Claude Fable 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.RectangularSingularValues


/-!
# Finite families: analysis, synthesis, frame and Gram operators

For a finite family `v : ι → E` in an inner-product space we define the analysis map
`x ↦ (⟪v i, x⟫)ᵢ` into `EuclideanSpace 𝕜 ι`, the synthesis map `c ↦ ∑ i, c i • v i`, and the
two adjoint products: the frame operator `synthesis ∘ analysis` on `E` and the Gram operator
`analysis ∘ synthesis` on coefficient space.

Together with the rectangular spectral bridge of
`TauCeti.Analysis.InnerProductSpace.RectangularSingularValues`, this yields the two-way
correspondence between lower frame bounds and spectral floors of the Gram operator:

* `TauCeti.le_eigenvalues_finiteGramOperator_of_forall_le_sum_sq`: a lower frame bound
  forces the first `finrank 𝕜 E` sorted Gram eigenvalues to be at least the bound;
* `TauCeti.sum_sq_floor_of_le_eigenvalues_finiteGramOperator`: conversely, a spectral
  floor on those Gram eigenvalues recovers the lower frame bound.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.InnerProductSpace.FiniteFrame`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `82d20de`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, GPT-5.6 High, Claude Fable 5; Copyright (c) 2026
  Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

public section

namespace TauCeti

open Module LinearMap
open scoped InnerProductSpace

variable (𝕜 : Type*) {E ι : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [Fintype ι]

/-- Analysis map of a finite family, with coordinate `i` equal to `⟪v i, x⟫`.  The
inner-product argument order makes this map `𝕜`-linear. -/
noncomputable def finiteAnalysis (v : ι → E) : E →ₗ[𝕜] EuclideanSpace 𝕜 ι :=
  (WithLp.linearEquiv 2 𝕜 (ι → 𝕜)).symm.toLinearMap ∘ₗ
    LinearMap.pi fun i => (innerSL 𝕜 (v i)).toLinearMap

omit [FiniteDimensional 𝕜 E] [Fintype ι] in
/-- Analysis reads off the frame coefficients `⟪vᵢ, x⟫`. -/
@[simp] theorem finiteAnalysis_apply (v : ι → E) (x : E) (i : ι) :
    finiteAnalysis 𝕜 v x i = inner 𝕜 (v i) x :=
  (rfl)

/-- Synthesis map `c ↦ ∑ i, c i • v i` of a finite family. -/
noncomputable def finiteSynthesis (v : ι → E) : EuclideanSpace 𝕜 ι →ₗ[𝕜] E where
  toFun c := ∑ i, c i • v i
  map_add' a b := by
    simp only [PiLp.add_apply, add_smul]
    exact Finset.sum_add_distrib
  map_smul' r a := by
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]

omit [FiniteDimensional 𝕜 E] in
/-- Synthesis reassembles a coefficient vector as `∑ᵢ cᵢ • vᵢ`. -/
@[simp] theorem finiteSynthesis_apply (v : ι → E) (c : EuclideanSpace 𝕜 ι) :
    finiteSynthesis 𝕜 v c = ∑ i, c i • v i :=
  (rfl)

/-- Analysis and synthesis are adjoint to each other. -/
theorem adjoint_finiteAnalysis (v : ι → E) :
    (finiteAnalysis 𝕜 v).adjoint = finiteSynthesis 𝕜 v := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro c x
  rw [finiteSynthesis_apply, sum_inner, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, finiteAnalysis_apply, RCLike.inner_apply]
  ring

/-- Synthesis and analysis are adjoint to each other. -/
theorem adjoint_finiteSynthesis (v : ι → E) :
    (finiteSynthesis 𝕜 v).adjoint = finiteAnalysis 𝕜 v := by
  rw [← adjoint_finiteAnalysis, adjoint_adjoint]

/-- Frame operator `synthesis ∘ analysis` on the ambient space. -/
noncomputable def finiteFrameOperator (v : ι → E) : E →ₗ[𝕜] E :=
  (finiteSynthesis 𝕜 v).comp (finiteAnalysis 𝕜 v)

/-- Gram operator `analysis ∘ synthesis` on coefficient space. -/
noncomputable def finiteGramOperator (v : ι → E) :
    EuclideanSpace 𝕜 ι →ₗ[𝕜] EuclideanSpace 𝕜 ι :=
  (finiteAnalysis 𝕜 v).comp (finiteSynthesis 𝕜 v)

/-- The frame operator is the domain Gram product `A†A` of analysis. -/
theorem finiteFrameOperator_eq_adjointCompSelf (v : ι → E) :
    finiteFrameOperator 𝕜 v = (finiteAnalysis 𝕜 v).adjoint.comp (finiteAnalysis 𝕜 v) := by
  rw [finiteFrameOperator, adjoint_finiteAnalysis]

/-- The Gram operator is the codomain Gram product `AA†` of analysis. -/
theorem finiteGramOperator_eq_selfCompAdjoint (v : ι → E) :
    finiteGramOperator 𝕜 v = (finiteAnalysis 𝕜 v).comp (finiteAnalysis 𝕜 v).adjoint := by
  rw [finiteGramOperator, adjoint_finiteAnalysis]

omit [FiniteDimensional 𝕜 E] in
/-- Entrywise formula for the Gram operator: it acts by the Gram matrix `(⟪v i, v j⟫)ᵢⱼ`. -/
@[simp]
theorem finiteGramOperator_apply (v : ι → E) (c : EuclideanSpace 𝕜 ι) (i : ι) :
    finiteGramOperator 𝕜 v c i = ∑ j, inner 𝕜 (v i) (v j) * c j := by
  rw [finiteGramOperator, LinearMap.comp_apply, finiteAnalysis_apply, finiteSynthesis_apply,
    inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_right]
  ring

/-- The frame operator is positive. -/
theorem finiteFrameOperator_isPositive (v : ι → E) :
    (finiteFrameOperator 𝕜 v).IsPositive := by
  rw [finiteFrameOperator_eq_adjointCompSelf]
  exact (finiteAnalysis 𝕜 v).isPositive_adjoint_comp_self

/-- The Gram operator is positive. -/
theorem finiteGramOperator_isPositive (v : ι → E) :
    (finiteGramOperator 𝕜 v).IsPositive := by
  rw [finiteGramOperator_eq_selfCompAdjoint]
  exact (finiteAnalysis 𝕜 v).isPositive_self_comp_adjoint

/-- The Gram operator is symmetric. -/
theorem isSymmetric_finiteGramOperator (v : ι → E) :
    (finiteGramOperator 𝕜 v).IsSymmetric :=
  (finiteGramOperator_isPositive 𝕜 v).isSymmetric

omit [FiniteDimensional 𝕜 E] in
/-- The squared analysis norm is the sum of squared coefficients. -/
theorem norm_sq_finiteAnalysis (v : ι → E) (x : E) :
    ‖finiteAnalysis 𝕜 v x‖ ^ 2 = ∑ i, ‖inner 𝕜 (v i) x‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [finiteAnalysis_apply]

/-- The frame quadratic form is the sum of squared analysis coefficients. -/
theorem re_inner_finiteFrameOperator_eq_sum_sq (v : ι → E) (x : E) :
    RCLike.re (inner 𝕜 (finiteFrameOperator 𝕜 v x) x) =
      ∑ i, ‖inner 𝕜 (v i) x‖ ^ 2 := by
  rw [finiteFrameOperator_eq_adjointCompSelf,
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    show (finiteAnalysis 𝕜 v).adjoint.comp (finiteAnalysis 𝕜 v) =
      (finiteAnalysis 𝕜 v).adjoint ∘ₗ finiteAnalysis 𝕜 v from rfl,
    re_inner_adjointCompSelf_self, norm_sq_finiteAnalysis]

/-- A lower frame bound forces the first `finrank 𝕜 E` sorted eigenvalues of the Gram
operator to be at least the bound.  No relation between `finrank 𝕜 E` and the family size is
assumed. -/
theorem le_eigenvalues_finiteGramOperator_of_forall_le_sum_sq
    {v : ι → E} {a : ℝ} (h : ∀ x : E, a * ‖x‖ ^ 2 ≤ ∑ i, ‖inner 𝕜 (v i) x‖ ^ 2)
    {n : ℕ} (hn : finrank 𝕜 (EuclideanSpace 𝕜 ι) = n) (k : Fin n)
    (hk : (k : ℕ) < finrank 𝕜 E) :
    a ≤ (isSymmetric_finiteGramOperator 𝕜 v).eigenvalues hn k := by
  have hfloor : ∀ x : E, a * ‖x‖ ^ 2 ≤ ‖finiteAnalysis 𝕜 v x‖ ^ 2 := fun x => by
    rw [norm_sq_finiteAnalysis]
    exact h x
  have hcongr := eigenvalues_congr' (finiteGramOperator_eq_selfCompAdjoint 𝕜 v)
    (isSymmetric_finiteGramOperator 𝕜 v)
    (isSymmetric_self_comp_adjoint (finiteAnalysis 𝕜 v)) hn
  rw [congrFun hcongr k]
  exact le_eigenvalues_selfCompAdjoint_of_norm_sq_floor (finiteAnalysis 𝕜 v) hfloor hn k hk

/-- Converse to `le_eigenvalues_finiteGramOperator_of_forall_le_sum_sq`: when the family has
at least `finrank 𝕜 E` members, a spectral floor on the first `finrank 𝕜 E` sorted Gram
eigenvalues recovers the lower frame bound. -/
theorem sum_sq_floor_of_le_eigenvalues_finiteGramOperator
    {v : ι → E} {a : ℝ} {n : ℕ} (hn : finrank 𝕜 (EuclideanSpace 𝕜 ι) = n)
    (hdn : finrank 𝕜 E ≤ n)
    (h : ∀ k : Fin n, (k : ℕ) < finrank 𝕜 E →
      a ≤ (isSymmetric_finiteGramOperator 𝕜 v).eigenvalues hn k)
    (x : E) :
    a * ‖x‖ ^ 2 ≤ ∑ i, ‖inner 𝕜 (v i) x‖ ^ 2 := by
  have hcongr := eigenvalues_congr' (finiteGramOperator_eq_selfCompAdjoint 𝕜 v)
    (isSymmetric_finiteGramOperator 𝕜 v)
    (isSymmetric_self_comp_adjoint (finiteAnalysis 𝕜 v)) hn
  have hlowE : ∀ i : Fin (finrank 𝕜 E),
      a ≤ (finiteAnalysis 𝕜 v).isSymmetric_adjoint_comp_self.eigenvalues rfl i := by
    intro i
    have hin : (i : ℕ) < n := lt_of_lt_of_le i.2 hdn
    rw [eigenvalues_adjointCompSelf_eq_selfCompAdjoint (finiteAnalysis 𝕜 v) rfl hn i.2 hin]
    have hk := h ⟨i, hin⟩ i.2
    rw [congrFun hcongr ⟨i, hin⟩] at hk
    exact hk
  have hfloor := norm_sq_floor_of_le_eigenvalues_adjointCompSelf
    (finiteAnalysis 𝕜 v) rfl hlowE x
  rwa [norm_sq_finiteAnalysis] at hfloor

end TauCeti
