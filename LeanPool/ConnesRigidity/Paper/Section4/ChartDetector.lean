/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
import Mathlib.LinearAlgebra.CrossProduct
import LeanPool.ConnesRigidity.Foundation.LinearAlgebra.BooleanPolynomial
import LeanPool.ConnesRigidity.Paper.Section4.FiniteCharts

/-!
Algebraic finite-chart detector spine for Zhou's §4. Paper: §4.
-/

namespace Connes
namespace PaperChartDetector

open Construction
open Construction.PaperKernel
open PaperFiniteCharts

noncomputable section

/--
The `F` construction used in the Connes rigidity formalization.
-/
abbrev F := Construction.k
/--
The `A` construction used in the Connes rigidity formalization.
-/
abbrev A := Construction.A
/--
The `C` construction used in the Connes rigidity formalization.
-/
abbrev C := PaperKernel.C
/--
The `TensorAA` construction used in the Connes rigidity formalization.
-/
abbrev TensorAA := PaperKernel.TensorAA

noncomputable instance coeffIndexLinearOrder (N : ℕ) :
    LinearOrder (PaperFiniteCharts.CoeffIndex N) :=
  LinearOrder.lift' (finSumFinEquiv :
    PaperFiniteCharts.CoeffIndex N ≃ Fin (N + N))
    (finSumFinEquiv : PaperFiniteCharts.CoeffIndex N ≃ Fin (N + N)).injective

/-- The symmetric cross term of two vectors. Paper: §4. -/
def cross (a b : A) : C :=
  ⟨a ⊗ₜ[k] b + b ⊗ₜ[k] a, by
    change TensorProduct.comm k A A
        (a ⊗ₜ[k] b + b ⊗ₜ[k] a) = a ⊗ₜ[k] b + b ⊗ₜ[k] a
    simp [TensorProduct.comm]
    abel
  ⟩

@[simp] theorem cross_apply (a b : A) :
    (cross a b : TensorAA) = a ⊗ₜ[k] b + b ⊗ₜ[k] a := rfl

/-- The square of a sum splits into squares and the symmetric cross term.
Paper: §4. -/
theorem diagonal_add (a b : A) :
    PaperKernel.diagonal (a + b) =
      PaperKernel.diagonal a + PaperKernel.diagonal b + cross a b := by
  apply Subtype.ext
  change (a + b) ⊗ₜ[k] (a + b) =
    a ⊗ₜ[k] a + b ⊗ₜ[k] b +
      (a ⊗ₜ[k] b + b ⊗ₜ[k] a)
  simp only [TensorProduct.add_tmul, TensorProduct.tmul_add]
  abel

/-- Expansion of a square over a finite affine coordinate family. Paper: §4. -/
def upper {ι : Type*} [Fintype ι] [LinearOrder ι] (i : ι) : Finset ι :=
  Finset.univ.filter (i < ·)

theorem sum_pair_upper {ι : Type*} [Fintype ι] [LinearOrder ι]
    (T : ι → ι → TensorAA) :
    ∑ i, ∑ j, T i j =
      ∑ i, T i i + ∑ i, ∑ j ∈ upper i, (T i j + T j i) := by
  classical
  have hsplit (i : ι) :
      ∑ j, T i j =
        T i i +
          (∑ j, if i < j then T i j else 0) +
            (∑ j, if j < i then T i j else 0) := by
    calc
      ∑ j, T i j =
          ∑ j, ((if j = i then T i j else 0) +
            (if i < j then T i j else 0) +
              (if j < i then T i j else 0)) := by
                apply Fintype.sum_congr
                intro j
                by_cases hji : j = i
                · simp [hji]
                · rcases lt_or_gt_of_ne hji with hlt | hgt
                  · simp [hji, hlt, not_lt_of_ge (le_of_lt hlt)]
                  · simp [hji, hgt, not_lt_of_ge (le_of_lt hgt)]
      _ = (∑ j, if j = i then T i j else 0) +
          (∑ j, if i < j then T i j else 0) +
            (∑ j, if j < i then T i j else 0) := by
              simp only [Finset.sum_add_distrib]
      _ = _ := by
        simp only [Fintype.sum_ite_eq', add_assoc]
  have hswap :
      (∑ i, ∑ j, if j < i then T i j else 0) =
        ∑ i, ∑ j, if i < j then T j i else 0 := by
    rw [Finset.sum_comm]
  calc
    ∑ i, ∑ j, T i j =
        ∑ i, (T i i +
          (∑ j, if i < j then T i j else 0) +
            (∑ j, if j < i then T i j else 0)) :=
      Fintype.sum_congr _ _ hsplit
    _ = (∑ i, T i i) +
        (∑ i, ∑ j, if i < j then T i j else 0) +
          (∑ i, ∑ j, if j < i then T i j else 0) := by
      simp only [Finset.sum_add_distrib]
    _ = (∑ i, T i i) +
        (∑ i, ∑ j, if i < j then T i j + T j i else 0) := by
      rw [hswap]
      simp only [add_assoc]
      apply congrArg (fun z : TensorAA => (∑ i, T i i) + z)
      rw [← Finset.sum_add_distrib]
      apply Fintype.sum_congr
      intro i
      rw [← Finset.sum_add_distrib]
      apply Fintype.sum_congr
      intro j
      by_cases h : i < j <;> simp [h]
    _ = ∑ i, T i i + ∑ i, ∑ j ∈ upper i, (T i j + T j i) := by
      simp only [upper, Finset.sum_filter]

theorem diagonal_sum_expansion {ι : Type*} [Fintype ι] [LinearOrder ι]
    (b : A) (u : ι → A) :
    PaperKernel.diagonal (b + ∑ i, u i) =
      PaperKernel.diagonal b +
        ∑ i, cross b (u i) +
          ∑ i, PaperKernel.diagonal (u i) +
            ∑ i, ∑ j ∈ upper i, cross (u i) (u j) := by
  classical
  apply Subtype.ext
  simp only [PaperKernel.diagonal, cross, upper, Submodule.coe_add,
    Submodule.coe_sum]
  change (b + ∑ i, u i) ⊗ₜ[k] (b + ∑ i, u i) =
    b ⊗ₜ[k] b +
      ∑ i, (b ⊗ₜ[k] u i + u i ⊗ₜ[k] b) +
        ∑ i, (u i ⊗ₜ[k] u i) +
          ∑ i, ∑ j ∈ upper i,
            (u i ⊗ₜ[k] u j + u j ⊗ₜ[k] u i)
  simp only [TensorProduct.add_tmul, TensorProduct.tmul_add,
    TensorProduct.sum_tmul, TensorProduct.tmul_sum]
  simp only [Finset.sum_add_distrib]
  have hdouble :
      (∑ x, ∑ y, u y ⊗ₜ[k] u x) =
        ∑ i, u i ⊗ₜ[k] u i +
          ∑ i, ∑ j ∈ upper i,
            (u i ⊗ₜ[k] u j + u j ⊗ₜ[k] u i) := by
    rw [Finset.sum_comm]
    exact sum_pair_upper (fun i j => u i ⊗ₜ[k] u j)
  rw [hdouble]
  simp only [Finset.sum_add_distrib]
  abel

/--
The `chartIndexOfCoefficients` construction used in the Connes rigidity formalization.
-/
def chartIndexOfCoefficients (N : ℕ) (s : Fin 3)
    (x : PaperFiniteCharts.CoeffIndex N → F) :
    PaperFiniteCharts.ChartIndex N :=
  (s, (fun i => x (Sum.inl i)), (fun i => x (Sum.inr i)))

theorem chartPoint_ofCoefficients_eq_sum (N : ℕ) (s : Fin 3)
    (x : PaperFiniteCharts.CoeffIndex N → F) :
    PaperFiniteCharts.chartPoint N (chartIndexOfCoefficients N s x) =
      PaperFiniteCharts.basisVector s +
        ∑ i, x i • PaperFiniteCharts.coefficientVector N s i := by
  rw [PaperFiniteCharts.chartPoint_eq_affine_sum]
  simp only [chartIndexOfCoefficients, Fintype.sum_sum_type,
    PaperFiniteCharts.coefficientVector]
  simp only [add_assoc]

@[simp] theorem cross_smul_left (r : F) (a b : A) :
    cross (r • a) b = r • cross a b := by
  apply Subtype.ext
  change (r • a) ⊗ₜ[k] b + b ⊗ₜ[k] (r • a) =
    r • (a ⊗ₜ[k] b + b ⊗ₜ[k] a)
  calc
    (r • a) ⊗ₜ[k] b + b ⊗ₜ[k] (r • a) =
        r • (a ⊗ₜ[k] b) + r • (b ⊗ₜ[k] a) := by
          rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
    _ = r • (a ⊗ₜ[k] b + b ⊗ₜ[k] a) := by rw [smul_add]

@[simp] theorem cross_smul_right (r : F) (a b : A) :
    cross a (r • b) = r • cross a b := by
  apply Subtype.ext
  change a ⊗ₜ[k] (r • b) + (r • b) ⊗ₜ[k] a =
    r • (a ⊗ₜ[k] b + b ⊗ₜ[k] a)
  calc
    a ⊗ₜ[k] (r • b) + (r • b) ⊗ₜ[k] a =
        r • (a ⊗ₜ[k] b) + r • (b ⊗ₜ[k] a) := by
          rw [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul']
    _ = r • (a ⊗ₜ[k] b + b ⊗ₜ[k] a) := by rw [smul_add]

@[simp] theorem diagonal_smul (r : F) (a : A) :
    PaperKernel.diagonal (r • a) = r • PaperKernel.diagonal a := by
  apply Subtype.ext
  change (r • a) ⊗ₜ[k] (r • a) = r • (a ⊗ₜ[k] a)
  calc
    (r • a) ⊗ₜ[k] (r • a) = r • (a ⊗ₜ[k] (r • a)) := by
      rw [← TensorProduct.smul_tmul']
    _ = r • (r • (a ⊗ₜ[k] a)) := by rw [TensorProduct.tmul_smul]
    _ = r • (a ⊗ₜ[k] a) := by
      rw [smul_smul]
      have hrr : r * r = r := by
        simpa only [pow_two] using ZMod.pow_card r
      rw [hrr]

/--
The `chartEvaluation` construction used in the Connes rigidity formalization.
-/
def chartEvaluation (χ : C →ₗ[k] k) (N : ℕ) (s : Fin 3)
    (x : PaperFiniteCharts.CoeffIndex N → F) : F :=
  χ (PaperKernel.diagonal
    (PaperFiniteCharts.chartPoint N (chartIndexOfCoefficients N s x)))

/--
The `chartQuadraticData` construction used in the Connes rigidity formalization.
-/
def chartQuadraticData (χ : C →ₗ[k] k) (N : ℕ) (s : Fin 3) :
    BooleanPolynomial.QuadraticData (PaperFiniteCharts.CoeffIndex N) := by
  classical
  let _ : LT (PaperFiniteCharts.CoeffIndex N) :=
    (coeffIndexLinearOrder N).toLT
  let _ : DecidableEq (PaperFiniteCharts.CoeffIndex N) :=
    (coeffIndexLinearOrder N).toDecidableEq
  exact {
    constantTerm := χ (PaperKernel.diagonal (PaperFiniteCharts.basisVector s))
    linear := fun i =>
      χ (cross (PaperFiniteCharts.basisVector s)
        (PaperFiniteCharts.coefficientVector N s i))
    quadratic := fun i j =>
      if i = j then
        χ (PaperKernel.diagonal
          (PaperFiniteCharts.coefficientVector N s i))
      else if i < j then
        χ (cross (PaperFiniteCharts.coefficientVector N s i)
          (PaperFiniteCharts.coefficientVector N s j))
      else 0 }

theorem upper_quadratic_sum {ι : Type*} [Fintype ι] [LinearOrder ι]
    (d : ι → F) (c : ι → ι → F) (x : ι → F) :
    (∑ i, ∑ j,
      (if i = j then d i else if i < j then c i j else 0) * x i * x j) =
      ∑ i, d i * x i +
        ∑ i, ∑ j ∈ upper i, c i j * x i * x j := by
  classical
  have hbool (a : F) : a * a = a := by
    fin_cases a <;> rfl
  calc
    (∑ i, ∑ j,
      (if i = j then d i else if i < j then c i j else 0) * x i * x j) =
        ∑ i, ∑ j,
          ((if j = i then d i * x i else 0) +
            (if i < j then c i j * x i * x j else 0)) := by
      apply Fintype.sum_congr
      intro i
      apply Fintype.sum_congr
      intro j
      by_cases hji : j = i
      · subst j
        simp only [lt_self_iff_false, ↓reduceIte, add_zero]
        simp [mul_assoc, hbool]
      · rcases lt_or_gt_of_ne hji with hlt | hgt
        · have hne : ¬ i = j := ne_of_gt hlt
          have hnlt : ¬ i < j := not_lt_of_ge (le_of_lt hlt)
          simp [hji, hne, hnlt]
        · have hne : ¬ i = j := ne_of_lt hgt
          have hnlt : ¬ j < i := not_lt_of_ge (le_of_lt hgt)
          simp [hji, hne, hgt]
    _ = (∑ i, ∑ j, if j = i then d i * x i else 0) +
        ∑ i, ∑ j, if i < j then c i j * x i * x j else 0 := by
      simp only [Finset.sum_add_distrib]
    _ = ∑ i, d i * x i +
        ∑ i, ∑ j, if i < j then c i j * x i * x j else 0 := by
      simp only [Fintype.sum_ite_eq']
    _ = ∑ i, d i * x i +
        ∑ i, ∑ j ∈ upper i, c i j * x i * x j := by
      simp only [upper, Finset.sum_filter]

theorem chartEvaluation_eq_quadraticData_eval (χ : C →ₗ[k] k)
    (N : ℕ) (s : Fin 3) (x : PaperFiniteCharts.CoeffIndex N → F) :
    (chartQuadraticData χ N s).eval x = chartEvaluation χ N s x := by
  classical
  let _ : LT (PaperFiniteCharts.CoeffIndex N) :=
    (coeffIndexLinearOrder N).toLT
  let _ : DecidableEq (PaperFiniteCharts.CoeffIndex N) :=
    (coeffIndexLinearOrder N).toDecidableEq
  dsimp [chartEvaluation, chartQuadraticData,
    BooleanPolynomial.QuadraticData.eval]
  rw [chartPoint_ofCoefficients_eq_sum,
    diagonal_sum_expansion]
  simp only [map_add, map_sum, map_smul, cross_smul_left,
    cross_smul_right, diagonal_smul, smul_smul, smul_eq_mul]
  have hquad := upper_quadratic_sum
    (fun i => χ (PaperKernel.diagonal
      (PaperFiniteCharts.coefficientVector N s i)))
    (fun i j => χ (cross
      (PaperFiniteCharts.coefficientVector N s i)
      (PaperFiniteCharts.coefficientVector N s j))) x
  calc
    _ = χ (PaperKernel.diagonal (PaperFiniteCharts.basisVector s)) +
        (∑ i, χ (cross (PaperFiniteCharts.basisVector s)
          (PaperFiniteCharts.coefficientVector N s i)) * x i) +
          (∑ i, ∑ j,
            (if i = j then χ (PaperKernel.diagonal
                (PaperFiniteCharts.coefficientVector N s i))
              else if i < j then χ (cross
                (PaperFiniteCharts.coefficientVector N s i)
                (PaperFiniteCharts.coefficientVector N s j)) else 0) *
              x i * x j) := by rfl
    _ = χ (PaperKernel.diagonal (PaperFiniteCharts.basisVector s)) +
        (∑ i, χ (cross (PaperFiniteCharts.basisVector s)
          (PaperFiniteCharts.coefficientVector N s i)) * x i) +
          ((∑ i, χ (PaperKernel.diagonal
            (PaperFiniteCharts.coefficientVector N s i)) * x i) +
            ∑ i, ∑ j ∈ upper i, χ (cross
              (PaperFiniteCharts.coefficientVector N s i)
              (PaperFiniteCharts.coefficientVector N s j)) * x i * x j) := by
      exact congrArg (fun z : F =>
        χ (PaperKernel.diagonal (PaperFiniteCharts.basisVector s)) +
          (∑ i, χ (cross (PaperFiniteCharts.basisVector s)
            (PaperFiniteCharts.coefficientVector N s i)) * x i) + z) hquad
    _ = _ := by
      simp only [mul_comm, mul_left_comm, mul_assoc]
      abel

theorem chartEvaluation_isQuadratic (χ : C →ₗ[k] k) (N : ℕ) (s : Fin 3) :
    BooleanPolynomial.IsQuadratic (chartEvaluation χ N s) := by
  exact ⟨chartQuadraticData χ N s,
    chartEvaluation_eq_quadraticData_eval χ N s⟩

theorem quadratic_support_card_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι] (P : (ι → F) → F)
    (hdeg : BooleanPolynomial.IsQuadratic P) (hP : P ≠ 0) :
    Fintype.card (ι → F) ≤ 4 * BooleanPolynomial.weightOn P := by
  have hweight := BooleanPolynomial.quadratic_weight_lower_bound P hdeg hP
  by_cases hn : 2 ≤ Fintype.card ι
  · have hexp : (Fintype.card ι - 2) + 2 = Fintype.card ι := by omega
    have hpow : 2 ^ Fintype.card ι =
        4 * 2 ^ (Fintype.card ι - 2) := by
      rw [← hexp, pow_add]
      norm_num [Nat.mul_comm]
    rw [Fintype.card_fun, ZMod.card, hpow]
    exact Nat.mul_le_mul_left 4 hweight
  · have hn' : Fintype.card ι = 0 ∨ Fintype.card ι = 1 := by omega
    rw [Fintype.card_fun, ZMod.card]
    rcases hn' with hzero | hone
    · simp [hzero] at hweight ⊢
      omega
    · simp [hone] at hweight ⊢
      omega

/--
The `ChartEvalIndex` construction used in the Connes rigidity formalization.
-/
abbrev ChartEvalIndex (N : ℕ) :=
  Fin 3 × (PaperFiniteCharts.CoeffIndex N → F)

/--
The `chartEvalValue` construction used in the Connes rigidity formalization.
-/
def chartEvalValue (χ : C →ₗ[k] k) (N : ℕ) (i : ChartEvalIndex N) : F :=
  chartEvaluation χ N i.1 i.2

/--
The `chartEvalSupport` construction used in the Connes rigidity formalization.
-/
def chartEvalSupport (χ : C →ₗ[k] k) (N : ℕ) :
    Finset (ChartEvalIndex N) := by
  classical
  exact Finset.univ.filter (fun i => chartEvalValue χ N i ≠ 0)

theorem chart_support_card_bound (χ : C →ₗ[k] k) (N : ℕ)
    (hactive : (chartEvalSupport χ N).Nonempty) :
    Fintype.card (ChartEvalIndex N) ≤
      12 * (chartEvalSupport χ N).card := by
  classical
  obtain ⟨⟨s, x⟩, hx⟩ := hactive
  have hPx : chartEvaluation χ N s ≠ 0 := by
    have hx' : chartEvaluation χ N s x ≠ 0 := by
      simpa [chartEvalSupport, chartEvalValue] using
        (Finset.mem_filter.mp hx).2
    intro hzero
    exact hx' (congrFun hzero x)
  have hquartic := quadratic_support_card_bound
    (chartEvaluation χ N s)
    (chartEvaluation_isQuadratic χ N s) hPx
  let S := BooleanPolynomial.supportOn (chartEvaluation χ N s)
  have hsubset :
      (S.image (fun y => (s, y))) ⊆ chartEvalSupport χ N := by
    intro i hi
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hi
    have hy' : chartEvaluation χ N s y ≠ 0 := by
      exact (Finset.mem_filter.mp hy).2
    change (s, y) ∈ Finset.univ.filter
      (fun i => chartEvalValue χ N i ≠ 0)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy'⟩
  have hinj : Function.Injective
      (fun y : PaperFiniteCharts.CoeffIndex N → F => (s, y)) := by
    intro y z h
    exact congrArg Prod.snd h
  have hScard : S.card ≤ (chartEvalSupport χ N).card := by
    rw [← Finset.card_image_of_injective _ hinj]
    exact Finset.card_le_card hsubset
  have hcardIndex : Fintype.card (ChartEvalIndex N) =
      3 * Fintype.card (PaperFiniteCharts.CoeffIndex N → F) := by
    simp [ChartEvalIndex]
  rw [hcardIndex]
  calc
    3 * Fintype.card (PaperFiniteCharts.CoeffIndex N → F) ≤
        3 * (4 * S.card) := Nat.mul_le_mul_left 3 hquartic
    _ = 12 * S.card := by omega
    _ ≤ 12 * (chartEvalSupport χ N).card :=
      Nat.mul_le_mul_left 12 hScard

end
end PaperChartDetector
end Connes
