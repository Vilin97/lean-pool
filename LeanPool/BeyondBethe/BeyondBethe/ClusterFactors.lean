/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.ClusterProduct
public import LeanPool.BeyondBethe.BeyondBethe.PairStability
public import Mathlib.Data.Fin.Tuple.Embedding

/-! # Cluster Factors -/

@[expose] public section

open scoped BigOperators

namespace BeyondBethe

open MvPolynomial

theorem injectionPolynomial_reindex_rows
    {m m' n : ℕ} (B : Fin m → Fin n → ℝ) (e : Fin m ≃ Fin m') :
    injectionPolynomial B =
      injectionPolynomial (fun k j ↦ B (e.symm k) j) := by
  rw [injectionPolynomial, injectionPolynomial]
  let E := Equiv.embeddingCongr e (Equiv.refl (Fin n))
  calc
    (∑ f : Fin m ↪ Fin n,
        monomial (∑ k, Finsupp.single (f k) 1)
          (∏ k, B k (f k))) =
        ∑ f : Fin m ↪ Fin n,
          monomial (∑ k, Finsupp.single (E f k) 1)
            (∏ k, B (e.symm k) (E f k)) := by
              apply Finset.sum_congr rfl
              intro f _
              have hexp : (∑ k, Finsupp.single (E f k) 1) =
                  ∑ k, Finsupp.single (f k) 1 := by
                simpa [E] using Equiv.sum_comp e.symm
                  (fun k ↦ Finsupp.single (f k) 1)
              have hweight : (∏ k, B (e.symm k) (E f k)) =
                  ∏ k, B k (f k) := by
                simpa [E] using Equiv.prod_comp e.symm
                  (fun k ↦ B k (f k))
              rw [hexp, hweight]
    _ = ∑ f : Fin m' ↪ Fin n,
          monomial (∑ k, Finsupp.single (f k) 1)
            (∏ k, B (e.symm k) (f k)) :=
      Equiv.sum_comp E (fun f ↦
        monomial (∑ k, Finsupp.single (f k) 1)
          (∏ k, B (e.symm k) (f k)))

theorem injectionPolynomial_fin_one
    {n : ℕ} (B : Fin 1 → Fin n → ℝ) :
    injectionPolynomial B = positiveLinearPolynomial (B 0) := by
  rw [injectionPolynomial, positiveLinearPolynomial]
  let e := Function.Embedding.oneEmbeddingEquiv (one := Fin 1) (α := Fin n)
  calc
    (∑ f : Fin 1 ↪ Fin n,
        monomial (∑ k, Finsupp.single (f k) 1)
          (∏ k, B k (f k))) =
        ∑ f : Fin 1 ↪ Fin n,
          monomial (Finsupp.single (e f) 1) (B 0 (e f)) := by
            apply Finset.sum_congr rfl
            intro f _
            simp [e, Function.Embedding.oneEmbeddingEquiv]
    _ = ∑ j : Fin n, monomial (Finsupp.single j 1) (B 0 j) :=
      Equiv.sum_comp e
        (fun j ↦ monomial (Finsupp.single j 1) (B 0 j))

theorem injectionPolynomial_fin_two
    {n : ℕ} (B : Fin 2 → Fin n → ℝ) :
    injectionPolynomial B = pairPolynomial (B 0) (B 1) := by
  rw [injectionPolynomial, pairPolynomial]
  let e := Function.Embedding.twoEmbeddingEquiv (α := Fin n)
  calc
    (∑ f : Fin 2 ↪ Fin n,
        monomial (∑ k, Finsupp.single (f k) 1)
          (∏ k, B k (f k))) =
        ∑ f : Fin 2 ↪ Fin n,
          monomial
            (Finsupp.single (f 0) 1 + Finsupp.single (f 1) 1)
            (B 0 (f 0) * B 1 (f 1)) := by
              apply Finset.sum_congr rfl
              intro f _
              simp [Fin.sum_univ_two, Fin.prod_univ_two]
    _ = ∑ p : {(a, b) : Fin n × Fin n | a ≠ b},
          monomial
            (Finsupp.single p.1.1 1 + Finsupp.single p.1.2 1)
            (B 0 p.1.1 * B 1 p.1.2) :=
      by
        simpa [e, Function.Embedding.twoEmbeddingEquiv] using
          Equiv.sum_comp e (fun p ↦
            monomial
              (Finsupp.single p.1.1 1 + Finsupp.single p.1.2 1)
              (B 0 p.1.1 * B 1 p.1.2))
    _ = ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag,
          monomial
            (Finsupp.single p.1 1 + Finsupp.single p.2 1)
            (B 0 p.1 * B 1 p.2) := by
              symm
              apply Finset.sum_subtype
              intro p
              simp

theorem injectionPolynomial_fin_one_isRealStable
    {n : ℕ} [Nonempty (Fin n)] {B : Fin 1 → Fin n → ℝ}
    (hB : ∀ k j, 0 < B k j) :
    IsRealStable (injectionPolynomial B) := by
  rw [injectionPolynomial_fin_one]
  exact positiveLinearPolynomial_isRealStable (fun j ↦ hB 0 j)

theorem injectionPolynomial_fin_two_isRealStable
    {n : ℕ} {B : Fin 2 → Fin n → ℝ}
    (hcard : 2 ≤ n) (hB : ∀ k j, 0 < B k j) :
    IsRealStable (injectionPolynomial B) := by
  rw [injectionPolynomial_fin_two]
  exact pairPolynomial_isRealStable_of_pos (by simpa using hcard)
    (fun j ↦ hB 0 j) (fun j ↦ hB 1 j)

theorem rowClusterPolynomial_isRealStable_of_size_one
    {n : ℕ} [Nonempty (Fin n)]
    {A : Matrix (Fin n) (Fin n) ℝ} (C : RowClustering n)
    (hA : ∀ i j, 0 < A i j) (c : C.Cluster)
    (hc : C.size c = 1) :
    IsRealStable (rowClusterPolynomial A C c) := by
  rw [rowClusterPolynomial_eq_rename_injectionPolynomial]
  apply IsRealStable.rename
  let e : Fin (C.size c) ≃ Fin 1 := (Fin.castOrderIso hc).toEquiv
  rw [injectionPolynomial_reindex_rows _ e]
  exact injectionPolynomial_fin_one_isRealStable
    (fun k j ↦ hA (C.rows ⟨c, e.symm k⟩) j)

theorem rowClusterPolynomial_isRealStable_of_size_two
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (C : RowClustering n)
    (hcard : 2 ≤ n) (hA : ∀ i j, 0 < A i j) (c : C.Cluster)
    (hc : C.size c = 2) :
    IsRealStable (rowClusterPolynomial A C c) := by
  rw [rowClusterPolynomial_eq_rename_injectionPolynomial]
  apply IsRealStable.rename
  let e : Fin (C.size c) ≃ Fin 2 := (Fin.castOrderIso hc).toEquiv
  rw [injectionPolynomial_reindex_rows _ e]
  exact injectionPolynomial_fin_two_isRealStable hcard
    (fun k j ↦ hA (C.rows ⟨c, e.symm k⟩) j)

/-- Every cluster contains either one row or two rows. -/
def IsSingletonPairClustering
    {n : ℕ} (C : RowClustering n) : Prop :=
  ∀ c, C.size c = 1 ∨ C.size c = 2

theorem rowClusterProduct_isRealStable_of_singletonPairs
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (C : RowClustering n)
    (hcard : 2 ≤ n) (hA : ∀ i j, 0 < A i j)
    (hclusters : IsSingletonPairClustering C) :
    IsRealStable (rowClusterProduct A C) := by
  letI : Nonempty (Fin n) := Fintype.card_pos_iff.mp (by
    simpa using (lt_of_lt_of_le (by norm_num : 0 < 2) hcard))
  apply rowClusterProduct_isRealStable_of_factors
  intro c
  rcases hclusters c with hc | hc
  · exact rowClusterPolynomial_isRealStable_of_size_one C hA c hc
  · exact rowClusterPolynomial_isRealStable_of_size_two C hcard hA c hc

theorem singletonPairCluster_stableCoefficient_lower
    {n : ℕ}
    (stableCoefficient : AnariOveisGharanStableCoefficient.{0})
    {A : Matrix (Fin n) (Fin n) ℝ} (C : RowClustering n)
    (hcard : 2 ≤ n) (hA : ∀ i j, 0 < A i j)
    (hclusters : IsSingletonPairClustering C)
    (α : C.Cluster × Fin n → ℝ)
    (hα : ∀ v, 0 ≤ α v ∧ α v ≤ 1)
    (hαsum : (∑ v, α v) = n) :
    stableBoundaryFactor α *
        polynomialCapacity α (rowClusterProduct A C) *
        polynomialCapacity α (columnSelector C.Cluster (Fin n)) ≤
      Matrix.permanent A := by
  letI : Nonempty (Fin n) := Fintype.card_pos_iff.mp (by
    simpa using (lt_of_lt_of_le (by norm_num : 0 < 2) hcard))
  letI : Nonempty C.Cluster :=
    ⟨(C.rows.symm (Classical.choice inferInstance)).1⟩
  apply rowClusterProduct_stableCoefficient_lower stableCoefficient C
  · intro i j
    exact le_of_lt (hA i j)
  · exact fun c ↦ by
      rcases hclusters c with hc | hc
      · exact rowClusterPolynomial_isRealStable_of_size_one C hA c hc
      · exact rowClusterPolynomial_isRealStable_of_size_two C hcard hA c hc
  · exact hα
  · exact hαsum

end BeyondBethe
