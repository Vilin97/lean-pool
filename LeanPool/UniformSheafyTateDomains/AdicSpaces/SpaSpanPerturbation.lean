/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.SpaParameterPerturbation
import LeanPool.UniformSheafyTateDomains.AdicSpaces.GeometricSeries
import LeanPool.UniformSheafyTateDomains.AdicSpaces.HuberRings

/-!
# Span preservation under parameter perturbation (Kedlaya Exercise 1.2.2, second half)

The `SpaParameterPerturbation.lean` file proves that perturbing the parameters of a
rational-subset presentation does not change the subset (subset-equality half of
Kedlaya Exercise 1.2.2). This file supplies the **other half**: if the original
finite family generates the unit ideal, then a sufficiently small perturbation of
its members still generates the unit ideal.

* `exists_parameterPerturbation_span_top` — a zero-neighborhood `O` such that
  perturbing every member of a spanning family `T` by an element of `O` preserves
  `span = ⊤`.

## Proof (source-faithful, Kedlaya Ex. 1.2.2)

Write `1 = ∑_{t ∈ T} cₜ · t`. Multiplication by each `cₜ` is continuous and fixes
`0`, and the topologically nilpotent elements `A°°` are open
(`IsTateRing.isOpen_topologicallyNilpotentElements`); so `O := ⋂_{t ∈ T} (cₜ · —)⁻¹(A°°)`
is a zero-neighborhood. For `δₜ ∈ O`, `∑ cₜ·δₜ ∈ A°°` (a finite sum of topologically
nilpotent elements, nonarchimedean), hence `∑ cₜ·(t + δₜ) = 1 + ∑ cₜ·δₜ` is a **unit**
(`IsTopologicallyNilpotent.isUnit_one_add`). That unit lies in the span of the
perturbed family, so the perturbed family generates `⊤`.
-/

noncomputable section

open Filter Topology TopologicalRing

namespace ValuationSpectrum

universe u

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsHuberRing A] [IsTateRing A] [T2Space A] [NonarchimedeanRing A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]

/-- **Span preservation under perturbation** (Kedlaya Exercise 1.2.2, second half):
for a finite family `T` spanning the unit ideal there is a zero-neighborhood `O`
such that perturbing each `t ∈ T` by any `δ t ∈ O` keeps the family spanning the
unit ideal. -/
theorem exists_parameterPerturbation_span_top [DecidableEq A] {T : Finset A}
    (hspan : Ideal.span (T : Set A) = ⊤) :
    ∃ O ∈ 𝓝 (0 : A), ∀ δ : A → A, (∀ t ∈ T, δ t ∈ O) →
      Ideal.span ((T.image (fun t => t + δ t) : Finset A) : Set A) = ⊤ := by
  classical
  -- a unit combination `1 = ∑ cₜ · t`
  have h1 : (1 : A) ∈ Ideal.span (T : Set A) := hspan ▸ Submodule.mem_top
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp h1
  simp only [smul_eq_mul] at hc
  -- `A°°` is open and contains `0`
  have hAoo_open : IsOpen (topologicallyNilpotentElements A) :=
    IsTateRing.isOpen_topologicallyNilpotentElements_nonarch
  have hAoo_zero : (0 : A) ∈ topologicallyNilpotentElements A :=
    IsTopologicallyNilpotent.zero
  -- the box neighborhood
  set O : Set A := ⋂ t ∈ T, (fun x => c t * x) ⁻¹' topologicallyNilpotentElements A with hO
  have hO_mem : O ∈ 𝓝 (0 : A) := by
    rw [hO]
    refine (Filter.biInter_finset_mem T).mpr fun t _ => ?_
    refine (hAoo_open.preimage (continuous_const.mul continuous_id)).mem_nhds ?_
    show c t * 0 ∈ topologicallyNilpotentElements A
    rw [mul_zero]; exact hAoo_zero
  refine ⟨O, hO_mem, fun δ hδ => ?_⟩
  -- each `cₜ · δₜ` is topologically nilpotent
  have hcδ : ∀ t ∈ T, IsTopologicallyNilpotent (c t * δ t) := by
    intro t ht
    have := hδ t ht
    rw [hO, Set.mem_iInter₂] at this
    exact this t ht
  -- their finite sum is topologically nilpotent (nonarchimedean)
  have hsum_tn : IsTopologicallyNilpotent (∑ t ∈ T, c t * δ t) := by
    refine Finset.sum_induction _ IsTopologicallyNilpotent
      (fun _ _ => IsTopologicallyNilpotent.add_of_nonarch) IsTopologicallyNilpotent.zero ?_
    exact fun t ht => hcδ t ht
  -- `∑ cₜ (t + δₜ) = 1 + ∑ cₜ δₜ`, a unit
  have hcombo : ∑ t ∈ T, c t * (t + δ t) = 1 + ∑ t ∈ T, c t * δ t := by
    rw [← hc, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  have hunit : IsUnit (∑ t ∈ T, c t * (t + δ t)) := by
    letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
    haveI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
    rw [hcombo]; exact hsum_tn.isUnit_one_add
  -- that unit lies in the span of the perturbed family
  refine Ideal.eq_top_of_isUnit_mem _ ?_ hunit
  refine Submodule.sum_mem _ fun t ht => Ideal.mul_mem_left _ _ ?_
  exact Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ ht))

end ValuationSpectrum
