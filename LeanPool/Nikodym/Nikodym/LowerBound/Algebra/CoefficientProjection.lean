/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import LeanPool.Nikodym.Nikodym.LowerBound.Algebra.Interface

/-! # Coefficientwise linear projection under a field extension

The common coefficient API used by both the Hilbert and Krull-dimension base-change proofs.
-/

@[expose] public section

namespace Nikodym.LowerBound

open MvPolynomial

variable {K K' σ : Type*} [Field K] [Field K'] [Algebra K K']

local notation "ι" => (MvPolynomial.map (algebraMap K K') :
  MvPolynomial σ K →+* MvPolynomial σ K')

section CoeffProj

/-- Blueprint TR0 (auxiliary): the coefficients of `∑ α ∈ g'.support, monomial α (π (g'.coeff α))`
are `π (g'.coeff α)`. -/
private theorem coeff_sum_monomial_proj (π : K' →ₗ[K] K) (g' : MvPolynomial σ K')
    (β : σ →₀ ℕ) :
    (∑ α ∈ g'.support, monomial α (π (g'.coeff α))).coeff β = π (g'.coeff β) := by
  classical
  rw [coeff_sum]
  simp only [coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, map_zero]

/-- Blueprint TR0: coefficientwise application of a `K`-linear functional `π : K' →ₗ[K] K`,
as a `K`-linear map `P' →ₗ[K] P`. -/
noncomputable def coeffProj (π : K' →ₗ[K] K) :
    MvPolynomial σ K' →ₗ[K] MvPolynomial σ K where
  toFun g' := ∑ α ∈ g'.support, monomial α (π (g'.coeff α))
  map_add' g h := by
    ext β
    rw [coeff_sum_monomial_proj]
    change π (g.coeff β + h.coeff β) =
      (∑ α ∈ g.support, monomial α (π (g.coeff α))).coeff β +
        (∑ α ∈ h.support, monomial α (π (h.coeff α))).coeff β
    rw [coeff_sum_monomial_proj, coeff_sum_monomial_proj, map_add]
  map_smul' c g := by
    ext β
    rw [RingHom.id_apply, coeff_smul, coeff_sum_monomial_proj, coeff_sum_monomial_proj,
      coeff_smul, map_smul]

/-- Blueprint TR0: `(coeffProj π g').coeff α = π (g'.coeff α)`. -/
@[simp]
theorem coeff_coeffProj (π : K' →ₗ[K] K) (g' : MvPolynomial σ K') (α : σ →₀ ℕ) :
    (coeffProj π g').coeff α = π (g'.coeff α) :=
  coeff_sum_monomial_proj π g' α

/-- Blueprint TR0: `coeffProj π` sends constants to constants. -/
theorem coeffProj_C (π : K' →ₗ[K] K) (c : K') :
    coeffProj π (C c : MvPolynomial σ K') = C (π c) := by
  classical
  ext α
  rw [coeff_coeffProj, coeff_C, coeff_C, apply_ite π, map_zero]

/-- Blueprint TR0: if `π 1 = 1`, then `coeffProj π` is a left inverse of `ι`. -/
theorem coeffProj_map {π : K' →ₗ[K] K} (hπ : π 1 = 1) (f : MvPolynomial σ K) :
    coeffProj π (ι f) = f := by
  ext α
  rw [coeff_coeffProj, coeff_map, Algebra.algebraMap_eq_smul_one, map_smul, hπ, smul_eq_mul,
    mul_one]

/-- Blueprint TR0: `coeffProj π` is `P`-linear: `coeffProj π (ι f * g') = f * coeffProj π g'`. -/
theorem coeffProj_map_mul (π : K' →ₗ[K] K) (f : MvPolynomial σ K)
    (g' : MvPolynomial σ K') :
    coeffProj π (ι f * g') = f * coeffProj π g' := by
  classical
  ext α
  rw [coeff_coeffProj, coeff_mul, coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [coeff_map, coeff_coeffProj, ← Algebra.smul_def, map_smul, smul_eq_mul]

/-- Blueprint TR0: `coeffProj π (g' * ι f) = coeffProj π g' * f`. -/
theorem coeffProj_mul_map (π : K' →ₗ[K] K) (g' : MvPolynomial σ K')
    (f : MvPolynomial σ K) :
    coeffProj π (g' * ι f) = coeffProj π g' * f := by
  rw [mul_comm, coeffProj_map_mul, mul_comm]

/-- Blueprint TR0: `coeffProj π` maps the extended ideal `I.map ι` back into `I`. -/
theorem coeffProj_mem_of_mem_map (π : K' →ₗ[K] K) (I : Ideal (MvPolynomial σ K))
    {g' : MvPolynomial σ K'} (hg' : g' ∈ I.map ι) : coeffProj π g' ∈ I := by
  have hspan : g' ∈ Submodule.span (MvPolynomial σ K')
      ((ι : MvPolynomial σ K → MvPolynomial σ K') '' (I : Set _)) := hg'
  have key : ∀ c : MvPolynomial σ K', coeffProj π (c * g') ∈ I := by
    refine Submodule.span_induction (p := fun y _ ↦ ∀ c : MvPolynomial σ K',
      coeffProj π (c * y) ∈ I) ?_ ?_ ?_ ?_ hspan
    · rintro y ⟨f, hf, rfl⟩ c
      rw [coeffProj_mul_map]
      exact I.mul_mem_left _ hf
    · intro c
      rw [mul_zero, map_zero]
      exact I.zero_mem
    · intro y z _ _ hy hz c
      rw [mul_add, map_add]
      exact I.add_mem (hy c) (hz c)
    · intro a y _ hy c
      rw [smul_eq_mul, ← mul_assoc]
      exact hy (c * a)
  have h1 := key 1
  rwa [one_mul] at h1

/-- Blueprint TR0: `coeffProj π` does not increase the total degree. -/
theorem totalDegree_coeffProj_le (π : K' →ₗ[K] K) (g' : MvPolynomial σ K') :
    (coeffProj π g').totalDegree ≤ g'.totalDegree := by
  have hsub : (coeffProj π g').support ⊆ g'.support := by
    intro α hα
    rw [mem_support_iff] at hα ⊢
    intro h
    exact hα (by rw [coeff_coeffProj, h, map_zero])
  exact Finset.sup_mono hsub

/-- Blueprint TR0: decomposition of `g' : P'` along a `K`-basis `b` of `K'`: for any finset `s`
containing the `b`-supports of all coefficients of `g'`,
`g' = ∑ j ∈ s, b j • ι (coeffProj (b.coord j) g')`. -/
theorem sum_smul_map_coeffProj {β : Type*} (b : Module.Basis β K K')
    (g' : MvPolynomial σ K') {s : Finset β}
    (hs : ∀ α ∈ g'.support, (b.repr (g'.coeff α)).support ⊆ s) :
    ∑ j ∈ s, b j • ι (coeffProj (b.coord j) g') = g' := by
  ext α
  rw [coeff_sum]
  simp only [coeff_smul, coeff_map, coeff_coeffProj, Module.Basis.coord_apply]
  have hsub : (b.repr (g'.coeff α)).support ⊆ s := by
    by_cases hα : α ∈ g'.support
    · exact hs α hα
    · rw [notMem_support_iff.mp hα, map_zero, Finsupp.support_zero]
      exact Finset.empty_subset _
  conv_rhs => rw [← b.linearCombination_repr (g'.coeff α), Finsupp.linearCombination_apply,
    Finsupp.sum_of_support_subset _ hsub _ (fun j _ ↦ zero_smul K (b j))]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [smul_eq_mul, Algebra.smul_def, mul_comm]

/-- Blueprint TR0: every `g' : P'` is a finite `K'`-combination
`∑ j ∈ s, b j • ι (coeffProj (b.coord j) g')` of base-changed polynomials, for any `K`-basis
`b` of `K'`. -/
theorem exists_sum_smul_map_coeffProj {β : Type*} (b : Module.Basis β K K')
    (g' : MvPolynomial σ K') :
    ∃ s : Finset β, g' = ∑ j ∈ s, b j • ι (coeffProj (b.coord j) g') := by
  classical
  exact ⟨g'.support.biUnion fun α ↦ (b.repr (g'.coeff α)).support,
    (sum_smul_map_coeffProj b g' fun α hα ↦
      Finset.subset_biUnion_of_mem (fun α ↦ (b.repr (g'.coeff α)).support) hα).symm⟩

end CoeffProj

end Nikodym.LowerBound
