/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Analyticity

/-!
# Holomorphic hulls relative to an ambient set

The hull is tested by scalar analytic functions on the ambient set. On open sets these are
precisely holomorphic functions. The formulation uses all real upper bounds rather than a real
supremum, so empty sets and unbounded functions have the intended behavior. In particular the
empty hull is empty. Relative closedness is expressed on the ambient subtype; no ambient
closedness or compactness of the hull is assumed.

References: [Range][Range1986] II §3.2; [Scheidemann][Scheidemann2005] §6.2;
[Jakóbczak–Jarnicki][JakobczakJarnicki2021] §2.7.

## Main results

`holomorphicHull` is the scalar hull relative to an ambient set, tested by all real modulus
bounds. `IsHolomorphicallyConvex` is the property that compact subsets of an open set have
compact hulls in that set. `exists_separator_of_notMem_holomorphicHull` separates a point
outside the hull. `holomorphicHull_idem` is idempotence.

## References

* [P. Jakóbczak and M. Jarnicki, *Lectures on Holomorphic Functions of Several Complex
  Variables*][JakobczakJarnicki2021]
* [R. M. Range, *Holomorphic Functions and Integral Representations in Several Complex
  Variables*][Range1986]
* [V. Scheidemann, *Introduction to Complex Analysis in Several Variables*][Scheidemann2005]
-/

public noncomputable section

open Set

namespace SeveralComplexVariables

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The scalar holomorphic hull of `K` relative to `U`, using all real modulus bounds. -/
@[expose] def holomorphicHull (U K : Set E) : Set E :=
  {z | z ∈ U ∧ ∀ f : E → ℂ, AnalyticOnNhd ℂ f U →
    ∀ M : ℝ, (∀ w ∈ K, ‖f w‖ ≤ M) → ‖f z‖ ≤ M}

/-- On an open finite-dimensional domain, the hull may equivalently be tested by complex
Fréchet-differentiable scalar functions. -/
theorem mem_holomorphicHull_iff_differentiableOn [FiniteDimensional ℂ E]
    {U K : Set E} (ho : IsOpen U) {z : E} :
    z ∈ holomorphicHull U K ↔ z ∈ U ∧
      ∀ f : E → ℂ, DifferentiableOn ℂ f U →
        ∀ M : ℝ, (∀ w ∈ K, ‖f w‖ ≤ M) → ‖f z‖ ≤ M := by
  constructor
  · intro hz
    exact ⟨hz.1, fun f hf => hz.2 f (hf.analyticOnNhd_of_finiteDimensional ho)⟩
  · intro hz
    exact ⟨hz.1, fun f hf => hz.2 f hf.differentiableOn⟩

/-- A holomorphic hull is contained in its ambient set. -/
theorem holomorphicHull_subset (U K : Set E) : holomorphicHull U K ⊆ U :=
  fun _ hz => hz.1

/-- A set contained in the ambient set is contained in its holomorphic hull. -/
theorem subset_holomorphicHull {U K : Set E} (hKU : K ⊆ U) : K ⊆ holomorphicHull U K :=
  fun z hz => ⟨hKU hz, fun _ _ _ h => h z hz⟩

/-- Modulus bounds transfer from a set to its holomorphic hull. -/
theorem norm_le_on_holomorphicHull {U K : Set E} {f : E → ℂ}
    (hf : AnalyticOnNhd ℂ f U) {M : ℝ} (hM : ∀ w ∈ K, ‖f w‖ ≤ M) :
    ∀ z ∈ holomorphicHull U K, ‖f z‖ ≤ M :=
  fun _ hz => hz.2 f hf M hM

/-- Norm bounds transfer from a set to its scalar holomorphic hull for Banach-valued holomorphic
maps, by norming functionals. -/
theorem norm_le_on_holomorphicHull_vector {U K : Set E} {G : E → F}
    (hG : AnalyticOnNhd ℂ G U) {M : ℝ} (hM : ∀ w ∈ K, ‖G w‖ ≤ M) :
    ∀ z ∈ holomorphicHull U K, ‖G z‖ ≤ M := by
  intro z hz
  obtain ⟨ℓ, hℓ, hℓz⟩ := exists_dual_vector'' ℂ (G z)
  have hcomp : AnalyticOnNhd ℂ (fun w => ℓ (G w)) U :=
    (ℓ.analyticOnNhd univ).comp hG (mapsTo_univ _ _)
  have := hz.2 _ hcomp M fun w hw =>
    calc ‖ℓ (G w)‖ ≤ ‖ℓ‖ * ‖G w‖ := ℓ.le_opNorm _
      _ ≤ 1 * M := by
          gcongr
          exact hM w hw
      _ = M := one_mul M
  rwa [hℓz, RCLike.norm_ofReal, abs_norm] at this

/-- Holomorphic hulls are monotone in the set being tested. -/
theorem holomorphicHull_mono {U K L : Set E} (hKL : K ⊆ L) :
    holomorphicHull U K ⊆ holomorphicHull U L :=
  fun _ hz => ⟨hz.1, fun f hf M h => hz.2 f hf M (fun w hw => h w (hKL hw))⟩

/-- Enlarging the ambient set enlarges its relative holomorphic hull. -/
theorem holomorphicHull_mono_ambient {U V K : Set E} (hUV : U ⊆ V) :
    holomorphicHull U K ⊆ holomorphicHull V K :=
  fun _ hz => ⟨hUV hz.1, fun f hf M h => hz.2 f (hf.mono hUV) M h⟩

/-- Taking a holomorphic hull twice has no further effect. -/
@[simp] theorem holomorphicHull_idem (U K : Set E) :
    holomorphicHull U (holomorphicHull U K) = holomorphicHull U K := by
  apply Subset.antisymm
  · intro z hz
    exact ⟨hz.1, fun f hf M h => hz.2 f hf M (norm_le_on_holomorphicHull hf h)⟩
  · exact subset_holomorphicHull (holomorphicHull_subset U K)

/-- The empty set has empty holomorphic hull, in every ambient set. -/
@[simp] theorem holomorphicHull_empty (U : Set E) : holomorphicHull U ∅ = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  have h := hz.2 (fun _ => 0) analyticOnNhd_const (-1) (by simp)
  norm_num at h

/-- The ambient set is fixed by its holomorphic hull. -/
@[simp] theorem holomorphicHull_self (U : Set E) : holomorphicHull U U = U :=
  Subset.antisymm (holomorphicHull_subset _ _) (subset_holomorphicHull Subset.rfl)

/-- The holomorphic hull is closed relative to its ambient set. -/
theorem isClosed_holomorphicHull_preimage (U K : Set E) :
    IsClosed ((Subtype.val : U → E) ⁻¹' holomorphicHull U K) := by
  have he : (Subtype.val : U → E) ⁻¹' holomorphicHull U K =
      ⋂ (f : E → ℂ) (hf : AnalyticOnNhd ℂ f U) (M : ℝ)
        (_ : ∀ w ∈ K, ‖f w‖ ≤ M), {z : U | ‖f z‖ ≤ M} := by
    ext z
    simp [holomorphicHull]
  rw [he]
  exact isClosed_iInter fun f => isClosed_iInter fun hf =>
    isClosed_iInter fun M => isClosed_iInter fun _ =>
      isClosed_le (continuousOn_iff_continuous_domRestrict.mp hf.continuousOn).norm continuous_const

/-- A point of the ambient set outside the hull is separated by a scalar holomorphic function and a
strict modulus bound. -/
theorem exists_separator_of_notMem_holomorphicHull {U K : Set E} {z : E}
    (hz : z ∈ U) (hn : z ∉ holomorphicHull U K) :
    ∃ f : E → ℂ, AnalyticOnNhd ℂ f U ∧ ∃ M : ℝ,
      (∀ w ∈ K, ‖f w‖ ≤ M) ∧ M < ‖f z‖ := by
  simpa only [holomorphicHull, mem_ofPred_eq, hz, true_and, not_forall, not_le,
    exists_prop] using hn

/-- Holomorphic maps carry relative hulls into relative hulls. -/
theorem mapsTo_holomorphicHull {U K : Set E} {V : Set F} {g : E → F}
    (hg : AnalyticOnNhd ℂ g U) (hgV : MapsTo g U V) :
    MapsTo g (holomorphicHull U K) (holomorphicHull V (g '' K)) := by
  intro z hz
  refine ⟨hgV hz.1, fun f hf M hM => ?_⟩
  exact hz.2 (f ∘ g) (hf.comp hg hgV) M (fun w hw => hM (g w) ⟨w, hw, rfl⟩)

/-- A set is holomorphically convex relative to `U` when its hull equals itself. -/
@[expose] def IsHolomorphicallyConvexIn (U K : Set E) : Prop := holomorphicHull U K = K

/-- Every holomorphic hull is holomorphically convex relative to its ambient set. -/
theorem isHolomorphicallyConvexIn_holomorphicHull (U K : Set E) :
    IsHolomorphicallyConvexIn U (holomorphicHull U K) := holomorphicHull_idem U K

/-- Holomorphic convexity of an ambient set means compactness of the hull of each compact subset.
Openness and connectedness are separate hypotheses. -/
@[expose] def IsHolomorphicallyConvex (U : Set E) : Prop :=
  ∀ K : Set E, IsCompact K → K ⊆ U → IsCompact (holomorphicHull U K)

/-- The empty ambient set is holomorphically convex. -/
theorem isHolomorphicallyConvex_empty : IsHolomorphicallyConvex (∅ : Set E) := by
  intro K _ _
  have : holomorphicHull (∅ : Set E) K = ∅ :=
    subset_empty_iff.mp (holomorphicHull_subset _ _)
  rw [this]
  exact isCompact_empty

/-- A relative holomorphic hull contained in a compact subset of its ambient set is compact. -/
theorem isCompact_holomorphicHull_of_subset_compact {U K C : Set E}
    (hC : IsCompact C) (hCU : C ⊆ U) (hHC : holomorphicHull U K ⊆ C) :
    IsCompact (holomorphicHull U K) := by
  obtain ⟨S, hS, he⟩ := isClosed_induced_iff.mp (isClosed_holomorphicHull_preimage U K)
  have heq : holomorphicHull U K = C ∩ S := by
    ext z
    constructor
    · intro hz
      refine ⟨hHC hz, ?_⟩
      have h := Set.ext_iff.mp he ⟨z, (holomorphicHull_subset U K) hz⟩
      exact h.mpr hz
    · rintro ⟨hzC, hzS⟩
      have h := Set.ext_iff.mp he ⟨z, hCU hzC⟩
      exact h.mp hzS
  rw [heq]
  exact hC.inter_right hS

/-- Finite intersections preserve holomorphic convexity of ambient sets. -/
theorem IsHolomorphicallyConvex.inter {U V : Set E}
    (hU : IsHolomorphicallyConvex U) (hV : IsHolomorphicallyConvex V) :
    IsHolomorphicallyConvex (U ∩ V) := by
  intro K hK hKU
  apply isCompact_holomorphicHull_of_subset_compact
    ((hU K hK (hKU.trans inter_subset_left)).inter
      (hV K hK (hKU.trans inter_subset_right)))
  · rintro z ⟨hzU, hzV⟩
    exact ⟨hzU.1, hzV.1⟩
  · intro z hz
    exact ⟨holomorphicHull_mono_ambient inter_subset_left hz,
      holomorphicHull_mono_ambient inter_subset_right hz⟩

/-- In finite coordinate spaces, the hull of a bounded set is bounded. -/
theorem isBounded_holomorphicHull {ι : Type*} [Fintype ι]
    (U : Set (ι → ℂ)) {K : Set (ι → ℂ)} (hK : Bornology.IsBounded K) :
    Bornology.IsBounded (holomorphicHull U K) := by
  obtain ⟨M, hM⟩ := hK.exists_norm_le
  apply (isBounded_iff_forall_norm_le).mpr
  refine ⟨max M 0, fun z hz => (pi_norm_le_iff_of_nonneg (le_max_right _ _)).mpr fun i => ?_⟩
  exact (hz.2 (fun w => w i) ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticOnNhd U) M
    (fun w hw => (norm_le_pi_norm w i).trans (hM w hw))).trans (le_max_left _ _)

/-- A singleton has no additional hull points; if it lies outside the ambient set, its relative hull
is empty. Empty coordinate types are included. -/
@[simp] theorem holomorphicHull_singleton {ι : Type*} [Fintype ι]
    (U : Set (ι → ℂ)) (a : ι → ℂ) : holomorphicHull U {a} = U ∩ {a} := by
  ext z
  constructor
  · intro hz
    refine ⟨hz.1, ?_⟩
    have he : z = a := by
      ext i
      have hf : AnalyticOnNhd ℂ (fun w : ι → ℂ => w i - a i) U :=
        ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticOnNhd U).sub analyticOnNhd_const
      have h := hz.2 _ hf 0 (by simp)
      exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
    exact mem_singleton_iff.mpr he
  · rintro ⟨hz, rfl⟩
    exact ⟨hz, fun f hf M hM => hM z (mem_singleton z)⟩

/-- The full finite-dimensional coordinate space is holomorphically convex. -/
theorem isHolomorphicallyConvex_univ {ι : Type*} [Fintype ι] :
    IsHolomorphicallyConvex (univ : Set (ι → ℂ)) := by
  intro K hK _
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ι → ℂ)).mp
    (isBounded_holomorphicHull univ hK.isBounded)
  exact isCompact_holomorphicHull_of_subset_compact (isCompact_closedBall 0 r)
    (subset_univ _) hr

/-- Continuous complex-linear equivalences preserve holomorphic convexity. -/
theorem IsHolomorphicallyConvex.image_equiv {U : Set E}
    (hU : IsHolomorphicallyConvex U) (L : E ≃L[ℂ] F) :
    IsHolomorphicallyConvex (L '' U) := by
  intro K hK hKU
  have hmap : MapsTo L.symm (L '' U) U := by
    rintro _ ⟨z, hz, rfl⟩
    simpa using hz
  have hc := hU (L.symm '' K) (hK.image L.symm.continuous)
    (by rintro _ ⟨z, hz, rfl⟩; exact hmap (hKU hz))
  apply isCompact_holomorphicHull_of_subset_compact (hc.image L.continuous)
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, hz.1, rfl⟩
  · intro z hz
    exact ⟨L.symm z,
      mapsTo_holomorphicHull (L.symm.toContinuousLinearMap.analyticOnNhd _) hmap hz,
      L.apply_symm_apply z⟩

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
