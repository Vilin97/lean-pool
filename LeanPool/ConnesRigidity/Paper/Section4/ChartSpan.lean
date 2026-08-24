/-
Copyright (c) 2026 Utensil Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song
-/
import LeanPool.ConnesRigidity.Paper.Section4.ChartOrbits
import LeanPool.ConnesRigidity.Paper.Section4.ChartDetector
import LeanPool.ConnesRigidity.Construction.SquareSpan

/-!
Finite chart span and exhaustion for Zhou's §4 detector. Paper: §4.
-/

namespace Connes
namespace PaperChartSpan

open Construction
open Construction.PaperKernel
open PaperFiniteCharts
open PaperChartDetector

noncomputable section

/--
The `k` construction used in the Connes rigidity formalization.
-/
abbrev k := Construction.k
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

/- A chart square with bounded polynomial coordinates belongs to the finite
chart span. Paper: §4. -/
lemma diagonal_chartVector_mem_of_mem (N : ℕ) (s : Fin 3) (f h : R)
    (hf : f ∈ polynomialChart N) (hh : h ∈ polynomialChart N) :
    PaperKernel.diagonal (chartVector s f h) ∈ chartSubmodule N := by
  obtain ⟨vf, hvf⟩ := (mem_polynomialChart_iff N f).mp hf
  obtain ⟨vh, hvh⟩ := (mem_polynomialChart_iff N h).mp hh
  apply Submodule.subset_span
  refine ⟨(s, vf, vh), ?_⟩
  simp only [chartSquare, chartPoint, chartVector]
  rw [hvf, hvh]

/-- The zero polynomial occurs at every finite chart level. Paper: §4. -/
lemma zero_mem_polynomialChart (N : ℕ) :
    (0 : R) ∈ polynomialChart N := by
  rw [mem_polynomialChart_iff]
  refine ⟨0, ?_⟩
  simp

/-- The constant polynomial is represented at the first positive chart level. Paper: §4. -/
lemma one_mem_polynomialChart_one :
    (1 : R) ∈ polynomialChart 1 := by
  rw [mem_polynomialChart_iff]
  refine ⟨fun _ => 1, ?_⟩
  apply Polynomial.ext
  intro n
  by_cases hn : n = 0
  · subst n
    rw [Polynomial.ofFn_coeff_eq_val_of_lt _ (by decide)]
    simp
  · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.one_le_iff_ne_zero.mpr hn)]
    simp [Polynomial.coeff_one, hn]

/-- The constant polynomial persists under chart enlargement. Paper: §4. -/
lemma one_mem_polynomialChart {N : ℕ} (hN : 0 < N) :
    (1 : R) ∈ polynomialChart N := by
  exact polynomialChart_mono (by omega) one_mem_polynomialChart_one

/-- The cyclic coordinate successor closes after two steps. Paper: §4. -/
lemma next_cycle (s : Fin 3) : next (nextNext s) = s := by
  fin_cases s <;> rfl

/-- The second cyclic successor reduces to the remaining coordinate. Paper: §4. -/
lemma nextNext_cycle (s : Fin 3) : nextNext (nextNext s) = next s := by
  fin_cases s <;> rfl

/-- A characteristic-two six-square identity isolates one diagonal coordinate. Paper: §4. -/
lemma diagonal_single_next_identity (s : Fin 3) (w : A) :
    PaperKernel.diagonal w =
      PaperKernel.diagonal (basisVector s + w) +
        PaperKernel.diagonal (basisVector s) +
        PaperKernel.diagonal (basisVector (nextNext s) + w) +
        PaperKernel.diagonal (basisVector (nextNext s)) +
        PaperKernel.diagonal
          (basisVector s + basisVector (nextNext s) + w) +
        PaperKernel.diagonal
          (basisVector s + basisVector (nextNext s)) := by
  apply Subtype.ext
  simp only [PaperKernel.diagonal, Submodule.coe_add,
    TensorProduct.add_tmul, TensorProduct.tmul_add]
  have h2K (x : A) : (2 : k) • x = 0 := by
    rw [show (2 : k) = 0 by decide, zero_smul]
  have h3K (x : A) : (3 : k) • x = x := by
    rw [show (3 : k) = 1 by decide, one_smul]
  have h4K (x : A) : (4 : k) • x = 0 := by
    rw [show (4 : k) = 0 by decide, zero_smul]
  have h2A (x : A) : 2 • x = 0 :=
    ZModModule.char_nsmul_eq_zero 2 x
  have h3A (x : A) : 3 • x = x := by
    change (Nat.succ 2) • x = x
    rw [succ_nsmul, h2A, zero_add]
  have h4A (x : A) : 4 • x = 0 := by
    change (Nat.succ 3) • x = 0
    rw [succ_nsmul, h3A]
    exact ZModModule.add_self x
  have h2 (x : PaperKernel.TensorAA) : 2 • x = 0 :=
    ZModModule.char_nsmul_eq_zero 2 x
  have h3 (x : PaperKernel.TensorAA) : 3 • x = x := by
    change (Nat.succ 2) • x = x
    rw [succ_nsmul, h2, zero_add]
  have h4 (x : PaperKernel.TensorAA) : 4 • x = 0 := by
    change (Nat.succ 3) • x = 0
    rw [succ_nsmul, h3]
    exact ZModModule.add_self x
  have h2Z (x : PaperKernel.TensorAA) : (2 : ℤ) • x = 0 := by
    rw [two_zsmul]
    exact ZModModule.add_self x
  have h3Z (x : PaperKernel.TensorAA) : (3 : ℤ) • x = x := by
    rw [show (3 : ℤ) = 2 + 1 by norm_num, add_zsmul, h2Z, zero_add,
      one_zsmul]
  have h4Z (x : PaperKernel.TensorAA) : (4 : ℤ) • x = 0 := by
    rw [show (4 : ℤ) = 3 + 1 by norm_num, add_zsmul, h3Z]
    rw [one_zsmul]
    exact ZModModule.add_self x
  abel_nf
  simp only [h2Z, h3Z, h4Z]
  simp only [zero_add, add_zero]

/-- A bounded scalar multiple of a coordinate diagonal lies in a finite chart span. Paper: §4. -/
lemma diagonal_smul_basis_mem (N : ℕ) (hN : 0 < N) (s : Fin 3) (f : R)
    (hf : f ∈ polynomialChart N) :
    PaperKernel.diagonal (f • basisVector (next s)) ∈ chartSubmodule N := by
  have hzero := zero_mem_polynomialChart N
  have hone := one_mem_polynomialChart hN
  have h₁ : PaperKernel.diagonal
      (basisVector s + f • basisVector (next s)) ∈ chartSubmodule N := by
    simpa [chartVector] using
      diagonal_chartVector_mem_of_mem N s f 0 hf hzero
  have h₂ : PaperKernel.diagonal (basisVector s) ∈ chartSubmodule N := by
    simpa [chartVector] using
      diagonal_chartVector_mem_of_mem N s 0 0 hzero hzero
  have h₃ : PaperKernel.diagonal
      (basisVector (nextNext s) + f • basisVector (next s)) ∈
        chartSubmodule N := by
    simpa [chartVector, next_cycle, nextNext_cycle, add_assoc,
      add_comm, add_left_comm] using
      diagonal_chartVector_mem_of_mem N (nextNext s) 0 f hzero hf
  have h₄ : PaperKernel.diagonal (basisVector (nextNext s)) ∈
      chartSubmodule N := by
    simpa [chartVector] using
      diagonal_chartVector_mem_of_mem N (nextNext s) 0 0 hzero hzero
  have h₅ : PaperKernel.diagonal
      (basisVector s + basisVector (nextNext s) +
        f • basisVector (next s)) ∈ chartSubmodule N := by
    simpa [chartVector, add_assoc, add_comm, add_left_comm] using
      diagonal_chartVector_mem_of_mem N s f 1 hf hone
  have h₆ : PaperKernel.diagonal
      (basisVector s + basisVector (nextNext s)) ∈ chartSubmodule N := by
    simpa [chartVector] using
      diagonal_chartVector_mem_of_mem N s 0 1 hzero hone
  rw [diagonal_single_next_identity s (f • basisVector (next s))]
  have h₁₂ := (chartSubmodule N).add_mem h₁ h₂
  have h₁₂₃ := (chartSubmodule N).add_mem h₁₂ h₃
  have h₁₂₃₄ := (chartSubmodule N).add_mem h₁₂₃ h₄
  have h₁₂₃₄₅ := (chartSubmodule N).add_mem h₁₂₃₄ h₅
  exact (chartSubmodule N).add_mem h₁₂₃₄₅ h₆

/-- Every coordinate diagonal has the same finite-chart membership property. Paper: §4. -/
lemma diagonal_smul_basis_any_mem (N : ℕ) (hN : 0 < N)
    (i : Fin 3) (f : R) (hf : f ∈ polynomialChart N) :
    PaperKernel.diagonal (f • basisVector i) ∈ chartSubmodule N := by
  simpa [next_cycle] using
    diagonal_smul_basis_mem N hN (nextNext i) f hf

/-- A cross term on two distinct coordinates expands into four chart squares. Paper: §4. -/
lemma cross_distinct_identity (s : Fin 3) (f h : R) :
    cross (f • basisVector (next s)) (h • basisVector (nextNext s)) =
      PaperKernel.diagonal
          (basisVector s + f • basisVector (next s) +
            h • basisVector (nextNext s)) +
        PaperKernel.diagonal (basisVector s + f • basisVector (next s)) +
        PaperKernel.diagonal (basisVector s + h • basisVector (nextNext s)) +
        PaperKernel.diagonal (basisVector s) := by
  apply Subtype.ext
  simp only [cross, PaperKernel.diagonal, Submodule.coe_add,
    TensorProduct.add_tmul, TensorProduct.tmul_add]
  have h2AZ (x : A) : (2 : ℤ) • x = 0 := by
    rw [two_zsmul]
    exact ZModModule.add_self x
  have h4AZ (x : A) : (4 : ℤ) • x = 0 := by
    rw [show (4 : ℤ) = 2 + 2 by norm_num, add_zsmul]
    simp [h2AZ]
  have h2CZ (x : PaperKernel.TensorAA) : (2 : ℤ) • x = 0 := by
    rw [two_zsmul]
    exact ZModModule.add_self x
  have h4CZ (x : PaperKernel.TensorAA) : (4 : ℤ) • x = 0 := by
    rw [show (4 : ℤ) = 2 + 2 by norm_num, add_zsmul]
    simp [h2CZ]
  abel_nf
  simp only [h2CZ, h4CZ]
  simp only [add_zero]

/- Distinct-coordinate cross terms with bounded coefficients lie in a finite
chart span. Paper: §4. -/
lemma cross_distinct_mem (N : ℕ) (_hN : 0 < N) (s : Fin 3)
    (f h : R) (hf : f ∈ polynomialChart N) (hh : h ∈ polynomialChart N) :
    cross (f • basisVector (next s)) (h • basisVector (nextNext s)) ∈
      chartSubmodule N := by
  have hzero := zero_mem_polynomialChart N
  have h₁ : PaperKernel.diagonal
      (basisVector s + f • basisVector (next s) +
        h • basisVector (nextNext s)) ∈ chartSubmodule N := by
    simpa [chartVector] using
      diagonal_chartVector_mem_of_mem N s f h hf hh
  have h₂ : PaperKernel.diagonal
      (basisVector s + f • basisVector (next s)) ∈ chartSubmodule N := by
    simpa [chartVector] using
      diagonal_chartVector_mem_of_mem N s f 0 hf hzero
  have h₃ : PaperKernel.diagonal
      (basisVector s + h • basisVector (nextNext s)) ∈ chartSubmodule N := by
    simpa [chartVector, add_assoc, add_comm, add_left_comm] using
      diagonal_chartVector_mem_of_mem N s 0 h hzero hh
  have h₄ : PaperKernel.diagonal (basisVector s) ∈ chartSubmodule N := by
    simpa [chartVector] using
      diagonal_chartVector_mem_of_mem N s 0 0 hzero hzero
  rw [cross_distinct_identity]
  have h₁₂ := (chartSubmodule N).add_mem h₁ h₂
  have h₁₂₃ := (chartSubmodule N).add_mem h₁₂ h₃
  exact (chartSubmodule N).add_mem h₁₂₃ h₄

/-- A same-coordinate cross term reduces to three diagonal squares. Paper: §4. -/
lemma cross_same_identity (i : Fin 3) (f h : R) :
    cross (f • basisVector i) (h • basisVector i) =
      PaperKernel.diagonal ((f + h) • basisVector i) +
        PaperKernel.diagonal (f • basisVector i) +
        PaperKernel.diagonal (h • basisVector i) := by
  apply Subtype.ext
  simp only [cross, PaperKernel.diagonal, Submodule.coe_add,
    add_smul, TensorProduct.add_tmul, TensorProduct.tmul_add]
  have h2AZ (x : A) : (2 : ℤ) • x = 0 := by
    rw [two_zsmul]
    exact ZModModule.add_self x
  have h4AZ (x : A) : (4 : ℤ) • x = 0 := by
    rw [show (4 : ℤ) = 2 + 2 by norm_num, add_zsmul]
    simp [h2AZ]
  have h2CZ (x : PaperKernel.TensorAA) : (2 : ℤ) • x = 0 := by
    rw [two_zsmul]
    exact ZModModule.add_self x
  have h4CZ (x : PaperKernel.TensorAA) : (4 : ℤ) • x = 0 := by
    rw [show (4 : ℤ) = 2 + 2 by norm_num, add_zsmul]
    simp [h2CZ]
  abel_nf
  simp only [h2CZ]
  simp only [add_zero]

/-- Same-coordinate cross terms with bounded coefficients lie in a finite chart span. Paper: §4. -/
lemma cross_same_mem (N : ℕ) (hN : 0 < N) (i : Fin 3)
    (f h : R) (hf : f ∈ polynomialChart N) (hh : h ∈ polynomialChart N)
    (hfh : f + h ∈ polynomialChart N) :
    cross (f • basisVector i) (h • basisVector i) ∈ chartSubmodule N := by
  have h₁ := diagonal_smul_basis_any_mem N hN i (f + h) hfh
  have h₂ := diagonal_smul_basis_any_mem N hN i f hf
  have h₃ := diagonal_smul_basis_any_mem N hN i h hh
  rw [cross_same_identity]
  exact (chartSubmodule N).add_mem ((chartSubmodule N).add_mem h₁ h₂) h₃

/-- The symmetric cross term is additive in its left input. Paper: §4. -/
lemma cross_add_left (a b c : A) :
    cross (a + b) c = cross a c + cross b c := by
  apply Subtype.ext
  simp only [cross, Submodule.coe_add, TensorProduct.add_tmul,
    TensorProduct.tmul_add]
  abel

/-- The symmetric cross term is additive in its right input. Paper: §4. -/
lemma cross_add_right (a b c : A) :
    cross a (b + c) = cross a b + cross a c := by
  apply Subtype.ext
  simp only [cross, Submodule.coe_add, TensorProduct.add_tmul,
    TensorProduct.tmul_add]
  abel

/-- A diagonal tensor decomposes into coordinate diagonals and pairwise cross terms. Paper: §4. -/
lemma diagonal_three_decompose (a : A) :
    PaperKernel.diagonal a =
      PaperKernel.diagonal (a 0 • basisVector 0) +
        PaperKernel.diagonal (a 1 • basisVector 1) +
        PaperKernel.diagonal (a 2 • basisVector 2) +
        cross (a 0 • basisVector 0) (a 1 • basisVector 1) +
        cross (a 0 • basisVector 0) (a 2 • basisVector 2) +
        cross (a 1 • basisVector 1) (a 2 • basisVector 2) := by
  have ha : a = a 0 • basisVector 0 + a 1 • basisVector 1 +
      a 2 • basisVector 2 := by
    funext i
    fin_cases i <;> simp [basisVector]
  calc
    PaperKernel.diagonal a = PaperKernel.diagonal
        (a 0 • basisVector 0 + a 1 • basisVector 1 +
          a 2 • basisVector 2) := congrArg PaperKernel.diagonal ha
    _ = _ := by
      rw [diagonal_add, diagonal_add, cross_add_left]
      abel

/-- The symmetric cross term is invariant under exchanging its inputs. Paper: §4. -/
lemma cross_comm (a b : A) : cross a b = cross b a := by
  apply Subtype.ext
  simp only [cross]
  abel

/-- Every bounded cross term on distinct standard coordinates is chart-generated. Paper: §4. -/
lemma cross_scalar_basis_ne_mem (N : ℕ) (hN : 0 < N)
    (i j : Fin 3) (hij : i ≠ j) (f h : R)
    (hf : f ∈ polynomialChart N) (hh : h ∈ polynomialChart N) :
    cross (f • basisVector i) (h • basisVector j) ∈ chartSubmodule N := by
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · simpa [next, nextNext] using cross_distinct_mem N hN 2 f h hf hh
  · rw [cross_comm]
    simpa [next, nextNext] using cross_distinct_mem N hN 1 h f hh hf
  · rw [cross_comm]
    simpa [next, nextNext] using cross_distinct_mem N hN 2 h f hh hf
  · exact False.elim (hij rfl)
  · simpa [next, nextNext] using cross_distinct_mem N hN 0 f h hf hh
  · simpa [next, nextNext] using cross_distinct_mem N hN 1 f h hf hh
  · rw [cross_comm]
    simpa [next, nextNext] using cross_distinct_mem N hN 0 h f hh hf
  · exact False.elim (hij rfl)

/-- A vector with bounded coordinates has its diagonal in one finite chart span. Paper: §4. -/
lemma diagonal_mem_chart_of_coeff (N : ℕ) (hN : 0 < N) (a : A)
    (h0 : a 0 ∈ polynomialChart N)
    (h1 : a 1 ∈ polynomialChart N)
    (h2 : a 2 ∈ polynomialChart N) :
    PaperKernel.diagonal a ∈ chartSubmodule N := by
  rw [diagonal_three_decompose]
  have hdiag0 := diagonal_smul_basis_any_mem N hN 0 (a 0) h0
  have hdiag1 := diagonal_smul_basis_any_mem N hN 1 (a 1) h1
  have hdiag2 := diagonal_smul_basis_any_mem N hN 2 (a 2) h2
  have hcross01 := cross_scalar_basis_ne_mem N hN 0 1 (by decide)
    (a 0) (a 1) h0 h1
  have hcross02 := cross_scalar_basis_ne_mem N hN 0 2 (by decide)
    (a 0) (a 2) h0 h2
  have hcross12 := cross_scalar_basis_ne_mem N hN 1 2 (by decide)
    (a 1) (a 2) h1 h2
  exact (chartSubmodule N).add_mem
    ((chartSubmodule N).add_mem
      ((chartSubmodule N).add_mem
        ((chartSubmodule N).add_mem
          ((chartSubmodule N).add_mem hdiag0 hdiag1) hdiag2) hcross01)
      hcross02) hcross12

/-- A polynomial is represented by a finite coefficient chart. Paper: §4. -/
lemma polynomial_mem_chart_succ (p : R) :
    p ∈ polynomialChart (p.natDegree + 1) := by
  apply (mem_polynomialChart_iff _ _).mpr
  refine ⟨Polynomial.toFn (p.natDegree + 1) p, ?_⟩
  exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt
    (Nat.lt_succ_self p.natDegree)

/-- Every vector diagonal is captured by a finite chart span. Paper: §4. -/
lemma diagonal_mem_some_chart (a : A) :
    ∃ N, PaperKernel.diagonal a ∈ chartSubmodule N := by
  let N0 : ℕ := (a 0).natDegree + 1
  let N1 : ℕ := (a 1).natDegree + 1
  let N2 : ℕ := (a 2).natDegree + 1
  let N : ℕ := max (max N0 N1) N2
  have h0 : a 0 ∈ polynomialChart N0 := by
    exact polynomial_mem_chart_succ (a 0)
  have h1 : a 1 ∈ polynomialChart N1 := by
    exact polynomial_mem_chart_succ (a 1)
  have h2 : a 2 ∈ polynomialChart N2 := by
    exact polynomial_mem_chart_succ (a 2)
  have hN0 : 0 < N0 := by
    dsimp [N0]
    omega
  have hN1 : 0 < N1 := by
    dsimp [N1]
    omega
  have hN2 : 0 < N2 := by
    dsimp [N2]
    omega
  have hN0N : N0 ≤ N := by
    dsimp [N]
    exact le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hN1N : N1 ≤ N := by
    dsimp [N]
    exact le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hN2N : N2 ≤ N := by
    dsimp [N]
    exact Nat.le_max_right _ _
  have hN : 0 < N := lt_of_lt_of_le hN0 hN0N
  refine ⟨N, diagonal_mem_chart_of_coeff N hN a ?_ ?_ ?_⟩
  · exact polynomialChart_mono hN0N h0
  · exact polynomialChart_mono hN1N h1
  · exact polynomialChart_mono hN2N h2

/-- The square span has symmetry and finite-chart witnesses. Paper: §2 and §4. -/
lemma span_has_chart (x : PaperKernel.TensorAA) (hx : x ∈ squareSpan) :
    TensorProduct.comm k A A x = x ∧
      ∃ N, ∃ c : C, (c : PaperKernel.TensorAA) = x ∧
        c ∈ chartSubmodule N := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      refine ⟨?_, ?_⟩
      · simp [TensorProduct.comm]
      · obtain ⟨N, hN⟩ := diagonal_mem_some_chart a
        exact ⟨N, PaperKernel.diagonal a, rfl, hN⟩
  | zero =>
      refine ⟨by simp, 0, 0, by simp, ?_⟩
      exact (chartSubmodule 0).zero_mem
  | add x y hx hy ihx ihy =>
      rcases ihx with ⟨hxs, Nx, cx, hcx, hxm⟩
      rcases ihy with ⟨hys, Ny, cy, hcy, hym⟩
      let M : ℕ := max Nx Ny
      have hxM : cx ∈ chartSubmodule M := by
        apply chartSubmodule_mono (Nat.le_max_left _ _)
        exact hxm
      have hyM : cy ∈ chartSubmodule M := by
        apply chartSubmodule_mono (Nat.le_max_right _ _)
        exact hym
      refine ⟨?_, M, cx + cy, ?_, (chartSubmodule M).add_mem hxM hyM⟩
      · simp only [map_add, hxs, hys]
      · simp [hcx, hcy]
  | smul r x hx ih =>
      rcases ih with ⟨hxs, N, cx, hcx, hxm⟩
      refine ⟨?_, N, r • cx, ?_, (chartSubmodule N).smul_mem r hxm⟩
      · simp only [map_smul, hxs]
      · simp [hcx]

/-- Every fixed tensor-module element is captured by a finite chart span. Paper: §2 and §4. -/
lemma diagonal_mem_chart_some_level (c : C) :
    ∃ N, c ∈ chartSubmodule N := by
  rcases (span_has_chart (c : PaperKernel.TensorAA)
    (concreteSquareSpanData.squares_span c)).2 with ⟨N, c', hcc', hmem⟩
  have hcc : c' = c := Subtype.ext hcc'
  exact ⟨N, hcc ▸ hmem⟩

end
end PaperChartSpan
end Connes
