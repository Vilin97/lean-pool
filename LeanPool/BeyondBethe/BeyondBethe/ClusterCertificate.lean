/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.CertificateCapacity
import LeanPool.BeyondBethe.BeyondBethe.ClusterAlpha
import LeanPool.BeyondBethe.BeyondBethe.Bethe
import Mathlib.Tactic

/-! # Cluster Certificate -/

open scoped BigOperators

namespace BeyondBethe

/-- The part of the stable boundary factor which remains after the powers of
`alpha` cancel against the column-selector capacity. -/
noncomputable def clusterComplementFactor
    {σ : Type*} [Fintype σ] (α : σ → ℝ) : ℝ :=
  ∏ v, (1 - α v) ^ (1 - α v)

theorem stableBoundaryFactor_nonnegative
    {σ : Type*} [Fintype σ] {α : σ → ℝ}
    (hα : ∀ v, 0 ≤ α v ∧ α v ≤ 1) :
    0 ≤ stableBoundaryFactor α := by
  rw [stableBoundaryFactor]
  exact Finset.prod_nonneg fun v _ ↦ mul_nonneg
    (Real.rpow_nonneg (hα v).1 _) (Real.rpow_nonneg (sub_nonneg.mpr (hα v).2) _)

theorem selectorCapacityValue_pos
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    {α : κ × ι → ℝ} (hα : ∀ v, 0 < α v) :
    0 < selectorCapacityValue α := by
  rw [selectorCapacityValue]
  apply Finset.prod_pos
  intro j _
  rw [linearCapacityValue]
  exact Finset.prod_pos fun c _ ↦
    Real.rpow_pos_of_pos (div_pos (by norm_num) (hα (c, j))) _

theorem boundaryTerm_mul_selectorTerm
    {a : ℝ} (ha : 0 < a) :
    (a ^ a * (1 - a) ^ (1 - a)) * (1 / a) ^ a =
      (1 - a) ^ (1 - a) := by
  rw [one_div, Real.inv_rpow (le_of_lt ha)]
  have hp : 0 < a ^ a := Real.rpow_pos_of_pos ha _
  calc
    (a ^ a * (1 - a) ^ (1 - a)) * (a ^ a)⁻¹ =
        (a ^ a * (a ^ a)⁻¹) * (1 - a) ^ (1 - a) := by ring
    _ = (1 - a) ^ (1 - a) := by rw [mul_inv_cancel₀ hp.ne', one_mul]

theorem stableBoundaryFactor_mul_selectorCapacityValue
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    {α : κ × ι → ℝ} (hα : ∀ v, 0 < α v) :
    stableBoundaryFactor α * selectorCapacityValue α =
      clusterComplementFactor α := by
  rw [stableBoundaryFactor, selectorCapacityValue, clusterComplementFactor]
  simp only [linearCapacityValue, Fintype.prod_prod_type]
  have hcomm :
      (∏ j, ∏ c, (1 / α (c, j)) ^ α (c, j)) =
        ∏ c, ∏ j, (1 / α (c, j)) ^ α (c, j) :=
    Finset.prod_comm
  rw [hcomm]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro c _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  exact boundaryTerm_mul_selectorTerm (hα (c, j))

/-- The cluster form of the paired certificate: singleton and pair factors
are recovered below by specializing each local injection polynomial. -/
noncomputable def clusterCertificateValue
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (C : RowClustering n)
    (α : C.Cluster × Fin n → ℝ) : ℝ :=
  clusterComplementFactor α * clusterProductCapacityValue A C α

/-- The factor contributed by one cluster before distinguishing singleton and
pair clusters. -/
noncomputable def localClusterCertificate
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (C : RowClustering n)
    (α : C.Cluster × Fin n → ℝ) (c : C.Cluster) : ℝ :=
  (∏ j, (1 - α (c, j)) ^ (1 - α (c, j))) *
    polynomialCapacity (fun j ↦ α (c, j))
      (injectionPolynomial (fun k j ↦ A (C.rows ⟨c, k⟩) j))

theorem clusterCertificateValue_eq_prod_local
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (C : RowClustering n)
    (α : C.Cluster × Fin n → ℝ) :
    clusterCertificateValue A C α =
      ∏ c, localClusterCertificate A C α c := by
  rw [clusterCertificateValue, clusterComplementFactor,
    clusterProductCapacityValue]
  simp only [Fintype.prod_prod_type, localClusterCertificate,
    ← Finset.prod_mul_distrib]

/-- The unique row in a cluster whose size has been identified as one. -/
noncomputable def singletonClusterRow
    {n : ℕ} (C : RowClustering n) (c : C.Cluster) (hc : C.size c = 1) :
    Fin n :=
  C.rows ⟨c, (Fin.castOrderIso hc).symm 0⟩

/-- The two ordered rows in a cluster whose size has been identified as two.
The order is immaterial to the symmetric pair certificate. -/
noncomputable def pairClusterRow
    {n : ℕ} (C : RowClustering n) (c : C.Cluster) (hc : C.size c = 2) :
    Fin 2 → Fin n :=
  fun k ↦ C.rows ⟨c, (Fin.castOrderIso hc).symm k⟩

theorem pairClusterRow_ne
    {n : ℕ} (C : RowClustering n) (c : C.Cluster) (hc : C.size c = 2) :
    pairClusterRow C c hc 0 ≠ pairClusterRow C c hc 1 := by
  intro h
  have hs := C.rows.injective h
  have hk : (0 : Fin 2) = 1 := by
    apply (Fin.castOrderIso hc).symm.injective
    exact eq_of_heq (Sigma.mk.inj_iff.mp hs).2
  norm_num at hk

theorem clusterAlpha_eq_singleton
    {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (C : RowClustering n)
    (c : C.Cluster) (hc : C.size c = 1) (j : Fin n) :
    clusterAlpha X C (c, j) = X (singletonClusterRow C c hc) j := by
  let e : Fin (C.size c) ≃ Fin 1 := (Fin.castOrderIso hc).toEquiv
  change (∑ k : Fin (C.size c), X (C.rows ⟨c, k⟩) j) = _
  calc
    (∑ k : Fin (C.size c), X (C.rows ⟨c, k⟩) j) =
        ∑ k : Fin 1, X (C.rows ⟨c, e.symm k⟩) j :=
      (Equiv.sum_comp e.symm
        (fun k : Fin (C.size c) ↦ X (C.rows ⟨c, k⟩) j)).symm
    _ = X (singletonClusterRow C c hc) j := by
      simp [singletonClusterRow, e]

theorem clusterAlpha_eq_pair
    {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (C : RowClustering n)
    (c : C.Cluster) (hc : C.size c = 2) (j : Fin n) :
    clusterAlpha X C (c, j) =
      pairAlpha X (pairClusterRow C c hc 0) (pairClusterRow C c hc 1) j := by
  let e : Fin (C.size c) ≃ Fin 2 := (Fin.castOrderIso hc).toEquiv
  change (∑ k : Fin (C.size c), X (C.rows ⟨c, k⟩) j) = _
  calc
    (∑ k : Fin (C.size c), X (C.rows ⟨c, k⟩) j) =
        ∑ k : Fin 2, X (C.rows ⟨c, e.symm k⟩) j :=
      (Equiv.sum_comp e.symm
        (fun k : Fin (C.size c) ↦ X (C.rows ⟨c, k⟩) j)).symm
    _ = pairAlpha X (pairClusterRow C c hc 0)
          (pairClusterRow C c hc 1) j := by
      simp [Fin.sum_univ_two, pairAlpha, pairClusterRow, e]

theorem clusterInjectionPolynomial_eq_singleton
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (C : RowClustering n)
    (c : C.Cluster) (hc : C.size c = 1) :
    injectionPolynomial (fun k j ↦ A (C.rows ⟨c, k⟩) j) =
      positiveLinearPolynomial (fun j ↦ A (singletonClusterRow C c hc) j) := by
  let e : Fin (C.size c) ≃ Fin 1 := (Fin.castOrderIso hc).toEquiv
  calc
    injectionPolynomial (fun k j ↦ A (C.rows ⟨c, k⟩) j) =
        injectionPolynomial (fun k : Fin 1 ↦ fun j ↦
          A (C.rows ⟨c, e.symm k⟩) j) :=
      injectionPolynomial_reindex_rows _ e
    _ = positiveLinearPolynomial (fun j ↦
          A (singletonClusterRow C c hc) j) := by
      rw [injectionPolynomial_fin_one]
      rfl

theorem clusterInjectionPolynomial_eq_pair
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (C : RowClustering n)
    (c : C.Cluster) (hc : C.size c = 2) :
    injectionPolynomial (fun k j ↦ A (C.rows ⟨c, k⟩) j) =
      pairPolynomial (fun j ↦ A (pairClusterRow C c hc 0) j)
        (fun j ↦ A (pairClusterRow C c hc 1) j) := by
  let e : Fin (C.size c) ≃ Fin 2 := (Fin.castOrderIso hc).toEquiv
  calc
    injectionPolynomial (fun k j ↦ A (C.rows ⟨c, k⟩) j) =
        injectionPolynomial (fun k : Fin 2 ↦ fun j ↦
          A (C.rows ⟨c, e.symm k⟩) j) :=
      injectionPolynomial_reindex_rows _ e
    _ = pairPolynomial (fun j ↦ A (pairClusterRow C c hc 0) j)
          (fun j ↦ A (pairClusterRow C c hc 1) j) := by
      rw [injectionPolynomial_fin_two]
      rfl

noncomputable def singletonProductValue
    {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ :=
  ∏ j, (A i j / X i j) ^ (X i j) *
    (1 - X i j) ^ (1 - X i j)

noncomputable def pairCertificateValue
    {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℝ) (r s : Fin n) : ℝ :=
  (∏ j, (1 - pairAlpha X r s j) ^ (1 - pairAlpha X r s j)) *
    polynomialCapacity (pairAlpha X r s)
      (pairPolynomial (fun j ↦ A r j) (fun j ↦ A s j))

theorem localClusterCertificate_eq_singletonProduct
    {n : ℕ} {A X : Matrix (Fin n) (Fin n) ℝ} (C : RowClustering n)
    (hA : ∀ i j, 0 < A i j) (hX : IsDoublyStochastic X)
    (hXpos : ∀ i j, 0 < X i j)
    (c : C.Cluster) (hc : C.size c = 1) :
    localClusterCertificate A C (clusterAlpha X C) c =
      singletonProductValue A X (singletonClusterRow C c hc) := by
  rw [localClusterCertificate]
  simp_rw [clusterAlpha_eq_singleton X C c hc]
  rw [clusterInjectionPolynomial_eq_singleton A C c hc,
    ← linearCapacityValue_eq_capacity
      (fun j ↦ hA (singletonClusterRow C c hc) j)
      (fun j ↦ hXpos (singletonClusterRow C c hc) j)
      (hX.row_sum (singletonClusterRow C c hc))]
  rw [singletonProductValue, linearCapacityValue,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  ring

theorem localClusterCertificate_eq_pairCertificate
    {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℝ) (C : RowClustering n)
    (c : C.Cluster) (hc : C.size c = 2) :
    localClusterCertificate A C (clusterAlpha X C) c =
      pairCertificateValue A X (pairClusterRow C c hc 0)
        (pairClusterRow C c hc 1) := by
  rw [localClusterCertificate, pairCertificateValue]
  simp_rw [clusterAlpha_eq_pair X C c hc]
  rw [clusterInjectionPolynomial_eq_pair A C c hc]

theorem singletonProductValue_eq_singletonFactor
    {n : ℕ} {A X : Matrix (Fin n) (Fin n) ℝ}
    (hcard : 2 ≤ n) (hA : ∀ i j, 0 < A i j)
    (hX : IsDoublyStochastic X) (hXpos : ∀ i j, 0 < X i j)
    (i : Fin n) :
    singletonProductValue A X i = singletonFactor A X i := by
  have hXlt : ∀ j, X i j < 1 := fun j ↦
    hX.entry_lt_one_of_positive hXpos (by
      simpa only [Fintype.card_fin] using
        (lt_of_lt_of_le (by norm_num : 1 < 2) hcard)) i j
  rw [singletonProductValue, singletonFactor, betheRowObjective,
    Real.exp_sum]
  apply Finset.prod_congr rfl
  intro j _
  rw [Real.rpow_def_of_pos (div_pos (hA i j) (hXpos i j)),
    Real.rpow_def_of_pos (sub_pos.mpr (hXlt j)), ← Real.exp_add]
  congr 1
  rw [Real.negMulLog, Real.log_div (hA i j).ne' (hXpos i j).ne']
  ring

/-- The paper's factor attached to a singleton-or-pair cluster.  A clustering
of this kind is equivalent to a matching together with harmless names and an
ordering of the two rows in each matched pair. -/
noncomputable def paperClusterFactor
    {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℝ) (C : RowClustering n)
    (hclusters : IsSingletonPairClustering C) (c : C.Cluster) : ℝ :=
  if hc : C.size c = 1 then
    singletonFactor A X (singletonClusterRow C c hc)
  else
    let hc2 : C.size c = 2 := (hclusters c).resolve_left hc
    pairCertificateValue A X (pairClusterRow C c hc2 0)
      (pairClusterRow C c hc2 1)

theorem localClusterCertificate_eq_paperClusterFactor
    {n : ℕ} {A X : Matrix (Fin n) (Fin n) ℝ} (C : RowClustering n)
    (hcard : 2 ≤ n) (hA : ∀ i j, 0 < A i j)
    (hX : IsDoublyStochastic X) (hXpos : ∀ i j, 0 < X i j)
    (hclusters : IsSingletonPairClustering C) (c : C.Cluster) :
    localClusterCertificate A C (clusterAlpha X C) c =
      paperClusterFactor A X C hclusters c := by
  rw [paperClusterFactor]
  split
  next hc =>
    exact (localClusterCertificate_eq_singletonProduct C hA hX hXpos c hc).trans
      (singletonProductValue_eq_singletonFactor hcard hA hX hXpos _)
  next hc =>
    let hc2 : C.size c = 2 := (hclusters c).resolve_left hc
    exact localClusterCertificate_eq_pairCertificate A X C c hc2

/-- The polynomial heart of the paired lower certificate.  All clustering,
stability, coefficient-pairing, capacity monotonicity, and cancellation steps
are internal.  The theorem keeps the stable-coefficient statement as an
explicit argument for modularity; `SourceStableReindex` discharges it from
Mathlib in the final theorem. -/
theorem clusterCertificateValue_le_permanent
    {n : ℕ}
    (stableCoefficient : AnariOveisGharanStableCoefficient.{0})
    {A X : Matrix (Fin n) (Fin n) ℝ} (C : RowClustering n)
    (hcard : 2 ≤ n) (hA : ∀ i j, 0 < A i j)
    (hX : IsDoublyStochastic X) (hXpos : ∀ i j, 0 < X i j)
    (hclusters : IsSingletonPairClustering C) :
    clusterCertificateValue A C (clusterAlpha X C) ≤ Matrix.permanent A := by
  let α := clusterAlpha X C
  have hαpos : ∀ v, 0 < α v :=
    clusterAlpha_pos_of_singletonPairs C hXpos hclusters
  have hαunit : ∀ v, 0 ≤ α v ∧ α v ≤ 1 :=
    clusterAlpha_in_unit_interval C hX
  have hαsum : ∑ v, α v = n := clusterAlpha_total_sum C hX
  have hA0 : Matrix.Nonnegative A := fun i j ↦ le_of_lt (hA i j)
  have hstable := singletonPairCluster_stableCoefficient_lower
    stableCoefficient C hcard hA hclusters α hαunit hαsum
  have hcluster := clusterProductCapacityValue_le_capacity C hA0 α
  have hselector := selectorCapacityValue_le_capacity hαpos
    (clusterAlpha_col_sum C hX)
  have hboundary0 : 0 ≤ stableBoundaryFactor α :=
    stableBoundaryFactor_nonnegative hαunit
  have hcluster0 : 0 ≤ clusterProductCapacityValue A C α :=
    clusterProductCapacityValue_nonneg C hA0 α
  have hselector0 : 0 ≤ selectorCapacityValue α :=
    le_of_lt (selectorCapacityValue_pos hαpos)
  have hcapCluster0 :
      0 ≤ polynomialCapacity α (rowClusterProduct A C) :=
    polynomialCapacity_nonneg (rowClusterProduct_nonnegativeCoefficients C hA0) α
  have hreplaceCluster :
      stableBoundaryFactor α * clusterProductCapacityValue A C α ≤
        stableBoundaryFactor α * polynomialCapacity α (rowClusterProduct A C) :=
    mul_le_mul_of_nonneg_left hcluster hboundary0
  have hreplaceCluster' :
      stableBoundaryFactor α * clusterProductCapacityValue A C α *
          selectorCapacityValue α ≤
        stableBoundaryFactor α * polynomialCapacity α (rowClusterProduct A C) *
          selectorCapacityValue α :=
    mul_le_mul_of_nonneg_right hreplaceCluster hselector0
  have hreplaceSelector :
      stableBoundaryFactor α * polynomialCapacity α (rowClusterProduct A C) *
          selectorCapacityValue α ≤
        stableBoundaryFactor α * polynomialCapacity α (rowClusterProduct A C) *
          polynomialCapacity α (columnSelector C.Cluster (Fin n)) := by
    apply mul_le_mul_of_nonneg_left hselector
    exact mul_nonneg hboundary0 hcapCluster0
  have hraw :
      stableBoundaryFactor α * clusterProductCapacityValue A C α *
          selectorCapacityValue α ≤ Matrix.permanent A :=
    hreplaceCluster'.trans (hreplaceSelector.trans hstable)
  rw [clusterCertificateValue]
  calc
    clusterComplementFactor α * clusterProductCapacityValue A C α =
        stableBoundaryFactor α * clusterProductCapacityValue A C α *
          selectorCapacityValue α := by
      rw [← stableBoundaryFactor_mul_selectorCapacityValue hαpos]
      ring
    _ ≤ Matrix.permanent A := hraw

/-- Paper Theorem 5 in an equivalent cluster presentation of a row matching.
The product contains one Bethe singleton factor for every unmatched row and
one pair-capacity factor for every matched pair. -/
theorem pairedLowerCertificate_for_clustering
    {n : ℕ}
    (stableCoefficient : AnariOveisGharanStableCoefficient.{0})
    {A X : Matrix (Fin n) (Fin n) ℝ} (C : RowClustering n)
    (hcard : 2 ≤ n) (hA : ∀ i j, 0 < A i j)
    (hX : IsDoublyStochastic X) (hXpos : ∀ i j, 0 < X i j)
    (hclusters : IsSingletonPairClustering C) :
    (∏ c, paperClusterFactor A X C hclusters c) ≤ Matrix.permanent A := by
  calc
    (∏ c, paperClusterFactor A X C hclusters c) =
        ∏ c, localClusterCertificate A C (clusterAlpha X C) c := by
      apply Finset.prod_congr rfl
      intro c _
      exact (localClusterCertificate_eq_paperClusterFactor C hcard hA hX
        hXpos hclusters c).symm
    _ = clusterCertificateValue A C (clusterAlpha X C) :=
      (clusterCertificateValue_eq_prod_local A C (clusterAlpha X C)).symm
    _ ≤ Matrix.permanent A :=
      clusterCertificateValue_le_permanent stableCoefficient C hcard hA
        hX hXpos hclusters

end BeyondBethe
