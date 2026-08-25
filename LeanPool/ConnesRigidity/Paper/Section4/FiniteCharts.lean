/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
/-

Finite polynomial charts for Zhou's property-(T) detector. Paper: §4.
-/
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Polynomial.OfFn
import LeanPool.ConnesRigidity.Construction

/-!
The finite charts component of the Connes rigidity formalization.
-/

namespace Connes
namespace PaperFiniteCharts

open Construction
open Construction.PaperKernel

noncomputable section

/--
The `F` construction used in the Connes rigidity formalization.
-/
abbrev F := Construction.k
/--
The `R` construction used in the Connes rigidity formalization.
-/
abbrev R := Construction.R
/--
The `A` construction used in the Connes rigidity formalization.
-/
abbrev A := Construction.A
/--
The `C` construction used in the Connes rigidity formalization.
-/
abbrev C := PaperKernel.C

noncomputable instance paperFintype : Fintype F := by
  let _ : NeZero (2 : ℕ) := ⟨by decide⟩
  infer_instance

/- The finite polynomial model for ℘_N. Paper: Lemma 4.2.
-/
/--
The `polynomialChart` construction used in the Connes rigidity formalization.
-/
def polynomialChart (N : ℕ) : Finset R :=
  (Finset.univ : Finset (Fin N → F)).image (Polynomial.ofFn N)

theorem mem_polynomialChart_iff (N : ℕ) (p : R) :
    p ∈ polynomialChart N ↔
      ∃ v : Fin N → F, Polynomial.ofFn N v = p := by
  simp [polynomialChart]

theorem polynomialChart_card (N : ℕ) :
    (polynomialChart N).card = Fintype.card (Fin N → F) := by
  classical
  rw [polynomialChart, Finset.card_image_of_injective _
    (Polynomial.injective_ofFn N)]
  simp

/-- Coefficient extension preserves the represented polynomial. Paper: Lemma 4.2.
-/
def extendCoefficients {N M : ℕ} (_hNM : N ≤ M) (v : Fin N → F) : Fin M → F :=
  fun i => if hi : i.val < N then v ⟨i.val, hi⟩ else 0

theorem ofFn_extendCoefficients {N M : ℕ} (hNM : N ≤ M)
    (v : Fin N → F) :
    Polynomial.ofFn M (extendCoefficients hNM v) =
      Polynomial.ofFn N v := by
  ext i
  by_cases hi : i < N
  · simp only [Polynomial.ofFn_coeff_eq_val_of_lt _ hi]
    simp [extendCoefficients, hi,
      Polynomial.ofFn_coeff_eq_val_of_lt _ (lt_of_lt_of_le hi hNM)]
  · have hiN : N ≤ i := Nat.le_of_not_gt hi
    rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ hiN]
    by_cases hiM : M ≤ i
    · exact Polynomial.ofFn_coeff_eq_zero_of_ge _ hiM
    · have hiM' : i < M := Nat.lt_of_not_ge hiM
      rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hiM']
      simp [extendCoefficients, hi]

theorem polynomialChart_mono {N M : ℕ} (hNM : N ≤ M) :
    polynomialChart N ⊆ polynomialChart M := by
  intro p hp
  obtain ⟨v, rfl⟩ := (mem_polynomialChart_iff N _).mp hp
  exact (mem_polynomialChart_iff M _).mpr ⟨extendCoefficients hNM v,
    ofFn_extendCoefficients hNM v⟩

/-- The cyclic coordinate order used for the three paper charts. Paper: Lemma 4.2.
-/
def next (s : Fin 3) : Fin 3 :=
  ⟨(s.val + 1) % 3, Nat.mod_lt _ (by decide)⟩

/--
The `nextNext` construction used in the Connes rigidity formalization.
-/
def nextNext (s : Fin 3) : Fin 3 := next (next s)

theorem next_ne (s : Fin 3) : next s ≠ s := by
  fin_cases s <;> decide

theorem nextNext_ne (s : Fin 3) : nextNext s ≠ s := by
  fin_cases s <;> decide

theorem next_nextNext_ne (s : Fin 3) : next s ≠ nextNext s := by
  fin_cases s <;> decide

/-- The standard basis vector in A. Paper: Lemma 4.2.
-/
def basisVector (s : Fin 3) : A := Pi.single s 1

/-- A point in one of the three finite charts. Paper: Lemma 4.2.
-/
def chartVector (s : Fin 3) (f h : R) : A :=
  basisVector s + f • basisVector (next s) + h • basisVector (nextNext s)

/--
The `ChartIndex` construction used in the Connes rigidity formalization.
-/
abbrev ChartIndex (N : ℕ) := Fin 3 × (Fin N → F) × (Fin N → F)

/--
The `chartPoint` construction used in the Connes rigidity formalization.
-/
def chartPoint (N : ℕ) (i : ChartIndex N) : A :=
  chartVector i.1 (Polynomial.ofFn N i.2.1) (Polynomial.ofFn N i.2.2)

/--
The `chartSquare` construction used in the Connes rigidity formalization.
-/
def chartSquare (N : ℕ) (i : ChartIndex N) : C :=
  PaperKernel.diagonal (chartPoint N i)

/-- The chart span C_N. Paper: Lemma 4.2.
-/
def chartSubmodule (N : ℕ) : Submodule k C :=
  Submodule.span k (Set.range (chartSquare N))

/-- Coordinate basis for the two polynomial parameters. Paper: Lemma 4.2.
-/
def polynomialBasis (N : ℕ) (i : Fin N) : R :=
  Polynomial.ofFn N (Pi.single i 1)

theorem ofFn_eq_sum_polynomialBasis (N : ℕ) (v : Fin N → F) :
    Polynomial.ofFn N v = ∑ i, v i • polynomialBasis N i := by
  have hv : v = ∑ i, v i • (Pi.single i 1) := by
    funext j
    simp [Pi.single_apply]
  rw [hv]
  simp only [map_sum, map_smul]
  simp [polynomialBasis, Pi.single_apply]

/--
The `CoeffIndex` construction used in the Connes rigidity formalization.
-/
abbrev CoeffIndex (N : ℕ) := Fin N ⊕ Fin N

/--
The `coefficientVector` construction used in the Connes rigidity formalization.
-/
def coefficientVector (N : ℕ) (s : Fin 3) : CoeffIndex N → A
  | Sum.inl i => polynomialBasis N i • basisVector (next s)
  | Sum.inr i => polynomialBasis N i • basisVector (nextNext s)

theorem chartPoint_eq_affine_sum (N : ℕ) (s : Fin 3)
    (f h : Fin N → F) :
    chartPoint N (s, f, h) =
      basisVector s +
        ∑ i, f i • coefficientVector N s (Sum.inl i) +
        ∑ i, h i • coefficientVector N s (Sum.inr i) := by
  simp only [chartPoint, chartVector, coefficientVector]
  rw [ofFn_eq_sum_polynomialBasis N f,
    ofFn_eq_sum_polynomialBasis N h]
  simp only [Finset.sum_smul, smul_assoc]

theorem chartPoint_apply_self (N : ℕ) (s : Fin 3)
    (f h : Fin N → F) : chartPoint N (s, f, h) s = 1 := by
  fin_cases s <;>
    simp [chartPoint, chartVector, basisVector, next, nextNext]

theorem chartPoint_mem_span (N : ℕ) (i : ChartIndex N) :
    chartSquare N i ∈ chartSubmodule N := by
  exact Submodule.subset_span ⟨i, rfl⟩

theorem chartSubmodule_mono {N M : ℕ} (hNM : N ≤ M) :
    chartSubmodule N ≤ chartSubmodule M := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  let j : ChartIndex M :=
    (i.1, extendCoefficients hNM i.2.1,
      extendCoefficients hNM i.2.2)
  have hpoint : chartPoint M j = chartPoint N i := by
    simp [j, chartPoint, chartVector,
      ofFn_extendCoefficients hNM i.2.1,
      ofFn_extendCoefficients hNM i.2.2]
  change PaperKernel.diagonal (chartPoint N i) ∈ chartSubmodule M
  rw [← hpoint]
  exact Submodule.subset_span ⟨j, rfl⟩

/- Every polynomial occurs in a finite chart. Paper: Lemma 4.2. -/
theorem polynomial_mem_some_chart (p : R) :
    ∃ N, p ∈ polynomialChart N := by
  refine ⟨p.natDegree + 1, ?_⟩
  apply (mem_polynomialChart_iff _ _).mpr
  refine ⟨Polynomial.toFn (p.natDegree + 1) p, ?_⟩
  exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt
    (Nat.lt_succ_self p.natDegree)

end
end PaperFiniteCharts
end Connes
