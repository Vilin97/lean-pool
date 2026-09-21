/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.SourceStableEncoding
import Mathlib.Tactic

/-! # Source Stable Reindex -/

open scoped BigOperators

namespace BeyondBethe

/-!
# Transporting the stable-coefficient theorem across finite coordinate types

The coefficient-table induction is most naturally indexed by `Fin n`.  This
file proves that all quantities in the theorem are invariant under a bijective
renaming of variables, and hence transports the result to an arbitrary finite
type.  No mathematical theorem is hidden in this bookkeeping layer.
-/

open MvPolynomial

theorem renameEquiv_nonnegativeCoefficients
    {σ τ : Type*} (e : σ ≃ τ) {p : MvPolynomial σ ℝ}
    (hp : HasNonnegativeCoefficients p) :
    HasNonnegativeCoefficients (MvPolynomial.rename e p) := by
  intro d
  have hcoeff :
      (MvPolynomial.rename e p).coeff d =
        p.coeff (d.mapDomain e.symm) := by
    have h := MvPolynomial.coeff_rename_mapDomain
      e.symm e.symm.injective (MvPolynomial.rename e p) d
    have hrename :
        MvPolynomial.rename e.symm (MvPolynomial.rename e p) = p :=
      MvPolynomial.rename_leftInverse e.left_inv p
    rw [hrename] at h
    exact h.symm
  rw [hcoeff]
  exact hp _

theorem renameEquiv_multiaffine
    {σ τ : Type*} (e : σ ≃ τ) {p : MvPolynomial σ ℝ}
    (hp : IsMultiaffine p) :
    IsMultiaffine (MvPolynomial.rename e p) := by
  intro j
  have hdegree :=
    MvPolynomial.degreeOf_rename_of_injective (R := ℝ) (p := p)
      e.injective (e.symm j)
  rw [e.apply_symm_apply] at hdegree
  rw [hdegree]
  exact hp (e.symm j)

theorem stableBoundaryFactor_equiv
    {σ τ : Type*} [Fintype σ] [Fintype τ]
    (e : σ ≃ τ) (α : σ → ℝ) :
    stableBoundaryFactor (fun j ↦ α (e.symm j)) =
      stableBoundaryFactor α := by
  unfold stableBoundaryFactor
  exact e.symm.prod_comp
    (fun i ↦ α i ^ α i * (1 - α i) ^ (1 - α i))

theorem realMonomial_equiv
    {σ τ : Type*} [Fintype σ] [Fintype τ]
    (e : σ ≃ τ) (z α : σ → ℝ) :
    realMonomial (fun j ↦ z (e.symm j)) (fun j ↦ α (e.symm j)) =
      realMonomial z α := by
  unfold realMonomial
  exact e.symm.prod_comp (fun i ↦ z i ^ α i)

theorem renameEquiv_eval
    {σ τ : Type*} (e : σ ≃ τ) (p : MvPolynomial σ ℝ)
    (z : σ → ℝ) :
    (MvPolynomial.rename e p).eval (fun j ↦ z (e.symm j)) = p.eval z := by
  rw [MvPolynomial.eval_rename]
  apply congrArg (fun w : σ → ℝ ↦ p.eval w)
  funext i
  simpa only [Function.comp_apply] using congrArg z (e.symm_apply_apply i)

theorem polynomialCapacity_renameEquiv
    {σ τ : Type*} [Fintype σ] [Fintype τ]
    (e : σ ≃ τ) {p : MvPolynomial σ ℝ}
    (hp : HasNonnegativeCoefficients p) (α : σ → ℝ) :
    polynomialCapacity (fun j ↦ α (e.symm j))
        (MvPolynomial.rename e p) =
      polynomialCapacity α p := by
  let p' := MvPolynomial.rename e p
  let α' : τ → ℝ := fun j ↦ α (e.symm j)
  have hp' : HasNonnegativeCoefficients p' :=
    renameEquiv_nonnegativeCoefficients e hp
  apply le_antisymm
  · apply le_polynomialCapacity_of_le_ratio
    intro z hz
    let z' : τ → ℝ := fun j ↦ z (e.symm j)
    have hz' : ∀ j, 0 < z' j := fun j ↦ hz (e.symm j)
    have h := polynomialCapacity_le_ratio hp' α' z' hz'
    simpa only [p', α', z', renameEquiv_eval,
      realMonomial_equiv] using h
  · apply le_polynomialCapacity_of_le_ratio
    intro z hz
    let z' : σ → ℝ := fun i ↦ z (e i)
    have hz' : ∀ i, 0 < z' i := fun i ↦ hz (e i)
    have h := polynomialCapacity_le_ratio hp α z' hz'
    have heval : p.eval z' = p'.eval z := by
      dsimp only [p', z']
      rw [MvPolynomial.eval_rename]
      rfl
    have hmonomial : realMonomial z' α = realMonomial z α' := by
      rw [show z' = fun i ↦ z (e i) by rfl]
      rw [show α = fun i ↦ α' (e i) by
        funext i
        simp [α']]
      unfold realMonomial
      exact e.prod_comp (fun j ↦ z j ^ α' j)
    simpa only [heval, hmonomial] using h

theorem coefficientInnerProduct_renameEquiv
    {σ τ : Type*} (e : σ ≃ τ) (p q : MvPolynomial σ ℝ) :
    coefficientInnerProduct (MvPolynomial.rename e p)
        (MvPolynomial.rename e q) =
      coefficientInnerProduct p q := by
  classical
  let E : (σ →₀ ℕ) ≃ (τ →₀ ℕ) := (Finsupp.domCongr e).toEquiv
  have hE (d : σ →₀ ℕ) : E d = d.mapDomain e := by
    change Finsupp.equivMapDomain e d = d.mapDomain e
    exact Finsupp.equivMapDomain_eq_mapDomain e d
  have hmem (d : σ →₀ ℕ) :
      d ∈ p.support.filter (· ∈ q.support) ↔
        E d ∈ (MvPolynomial.rename e p).support.filter
          (· ∈ (MvPolynomial.rename e q).support) := by
    simp only [Finset.mem_filter]
    have hpSupport := MvPolynomial.support_rename_of_injective
      (p := p) e.injective
    have hqSupport := MvPolynomial.support_rename_of_injective
      (p := q) e.injective
    rw [hpSupport, hqSupport, hE]
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨hdp, hdq⟩
      exact ⟨⟨d, hdp, rfl⟩, d, hdq, rfl⟩
    · rintro ⟨⟨a, hap, ha⟩, b, hbq, hb⟩
      have had : a = d := Finsupp.mapDomain_injective e.injective ha
      have hbd : b = d := Finsupp.mapDomain_injective e.injective hb
      simpa only [had, hbd] using And.intro hap hbq
  have hsum :
      (∑ d ∈ p.support.filter (· ∈ q.support),
          p.coeff d * q.coeff d) =
        ∑ d ∈ (MvPolynomial.rename e p).support.filter
            (· ∈ (MvPolynomial.rename e q).support),
          (MvPolynomial.rename e p).coeff d *
            (MvPolynomial.rename e q).coeff d := by
    apply Finset.sum_equiv E hmem
    intro d hd
    rw [hE]
    simp only [MvPolynomial.coeff_rename_mapDomain e e.injective]
  unfold coefficientInnerProduct
  symm
  convert hsum using 1

/-- The Anari--Oveis Gharan stable-coefficient inequality, reconstructed from
its bivariate analytic lemma and multilinear induction and transported from
`Fin n` to every finite coordinate type. -/
theorem anariOveisGharanStableCoefficient :
    AnariOveisGharanStableCoefficient := by
  intro σ inst p q d α hpNonneg hqNonneg hpMulti hqMulti
    hpStable hqStable hpHomogeneous hqHomogeneous hα hαsum
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let p' := MvPolynomial.rename e p
  let q' := MvPolynomial.rename e q
  let α' : Fin (Fintype.card σ) → ℝ := fun j ↦ α (e.symm j)
  have hfin := stableCoefficient_fin p' q' α'
    (renameEquiv_nonnegativeCoefficients e hpNonneg)
    (renameEquiv_nonnegativeCoefficients e hqNonneg)
    (renameEquiv_multiaffine e hpMulti)
    (renameEquiv_multiaffine e hqMulti)
    (hpStable.rename e) (hqStable.rename e)
    (fun j ↦ hα (e.symm j))
  have hboundary : stableBoundaryFactor α' = stableBoundaryFactor α :=
    stableBoundaryFactor_equiv e α
  have hcapP : polynomialCapacity α' p' = polynomialCapacity α p :=
    polynomialCapacity_renameEquiv e hpNonneg α
  have hcapQ : polynomialCapacity α' q' = polynomialCapacity α q :=
    polynomialCapacity_renameEquiv e hqNonneg α
  have hinner : coefficientInnerProduct p' q' = coefficientInnerProduct p q :=
    coefficientInnerProduct_renameEquiv e p q
  rw [hboundary, hcapP, hcapQ, hinner] at hfin
  exact hfin

end BeyondBethe
