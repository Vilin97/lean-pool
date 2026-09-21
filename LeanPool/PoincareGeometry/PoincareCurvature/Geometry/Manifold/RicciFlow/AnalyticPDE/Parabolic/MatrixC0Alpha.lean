/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FunctionSpace
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Trace
/-!
# Matrix-valued parabolic `C^{0,α}` closure

This module contains finite-dimensional algebraic closure facts for the
parabolic `C^{0,α}` predicates.  It is kept separate from `ParabolicHolder`
so determinant imports do not enlarge the base parabolic Holder module.
-/

@[expose] public noncomputable section

open Set
open scoped Topology NNReal BigOperators Matrix.Norms.Elementwise

namespace RicciFlow
namespace AnalyticPDE

namespace ParabolicC0AlphaNormLe

variable {X : Type*} [PseudoMetricSpace X]
variable {α : ℝ} {s : Set (ℝ × X)}

/-- Entrywise single-radius parabolic `C^{0,α}` control packages as matrix-valued control, with
the matrix radius the sum of the entry radii. -/
theorem matrix_of_entries {m n A : Type*} [Fintype m] [Fintype n]
    [NormedAddCommGroup A] {N : m → n → ℝ} {M : ℝ × X → Matrix m n A}
    (h : ∀ i j, ParabolicC0AlphaNormLe (N i j) α (fun z => M z i j) s) :
    ParabolicC0AlphaNormLe (∑ i, ∑ j, N i j) α M s := by
  change ParabolicC0AlphaNormLe (∑ i, ∑ j, N i j) α (fun z i j => M z i j) s
  exact
    ParabolicC0AlphaNormLe.pi (X := X) (F := n → A) (α := α) (s := s)
      (N := fun i => ∑ j, N i j) (u := fun z i j => M z i j) fun i =>
        ParabolicC0AlphaNormLe.pi (X := X) (F := A) (α := α) (s := s)
          (N := N i) (u := fun z j => M z i j) (h i)

/-- A matrix-valued single-radius parabolic `C^{0,α}` control projects to each entry with the
same radius. -/
theorem matrix_apply {m n A : Type*} [Fintype m] [Fintype n] [NormedAddCommGroup A]
    {N : ℝ} {M : ℝ × X → Matrix m n A}
    (h : ParabolicC0AlphaNormLe N α M s) (i : m) (j : n) :
    ParabolicC0AlphaNormLe N α (fun z => M z i j) s := by
  rcases h with ⟨B, hB, H, hH, hsum, hctrl⟩
  exact ⟨B, hB, H, hH, hsum,
    ParabolicC0AlphaWith.eval (ParabolicC0AlphaWith.eval hctrl i) j⟩

end ParabolicC0AlphaNormLe

namespace ParabolicC0AlphaOn

variable {X : Type*} [PseudoMetricSpace X]
variable {α : ℝ} {s : Set (ℝ × X)}

/-- A continuous nonvanishing function on a compact time-space set has norm uniformly bounded away
from zero. -/
theorem exists_pos_norm_lower_bound_of_isCompact_of_continuousOn_ne_zero {E : Type*}
    [NormedAddCommGroup E] {K : Set (ℝ × X)} {f : ℝ × X → E}
    (hK : IsCompact K) (hf : ContinuousOn f K)
    (hne : ∀ ⦃z : ℝ × X⦄, z ∈ K → f z ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖f z‖ := by
  by_cases hKnonempty : K.Nonempty
  · have hnorm : ContinuousOn (fun z => ‖f z‖) K := hf.norm
    rcases hK.exists_isMinOn hKnonempty hnorm with ⟨z₀, hz₀, hmin⟩
    refine ⟨‖f z₀‖, norm_pos_iff.mpr (hne hz₀), ?_⟩
    intro z hz
    exact (isMinOn_iff.mp hmin) z hz
  · refine ⟨1, by norm_num, ?_⟩
    intro z hz
    exact False.elim (hKnonempty ⟨z, hz⟩)

/-- A finite family of continuous nonvanishing functions on a compact time-space set has one
positive lower bound for all norms in the family. -/
theorem exists_pos_norm_lower_bound_finset_of_isCompact_of_continuousOn_ne_zero {ι E : Type*}
    [DecidableEq ι] [NormedAddCommGroup E] {K : Set (ℝ × X)}
    {f : ι → ℝ × X → E} (S : Finset ι) (hK : IsCompact K)
    (hf : ∀ a, ContinuousOn (f a) K)
    (hne : ∀ a ⦃z : ℝ × X⦄, z ∈ K → f a z ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ⦃a : ι⦄, a ∈ S → ∀ ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖f a z‖ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨1, by norm_num, ?_⟩
      intro a ha
      exact False.elim (by
        simp at ha)
  | insert a S ha ih =>
      rcases ih with ⟨δS, hδS, hS⟩
      rcases exists_pos_norm_lower_bound_of_isCompact_of_continuousOn_ne_zero
          (K := K) (f := f a) hK (hf a) (hne a) with
        ⟨δa, hδa, ha_bound⟩
      refine ⟨min δa δS, lt_min hδa hδS, ?_⟩
      intro b hb z hz
      rw [Finset.mem_insert] at hb
      rcases hb with rfl | hb
      · exact (min_le_left δa δS).trans (ha_bound hz)
      · exact (min_le_right δa δS).trans (hS hb hz)

/-- A finite-index family of continuous nonvanishing functions on a compact time-space set has
one positive lower bound for all norms in the family. -/
theorem exists_pos_norm_lower_bound_fintype_of_isCompact_of_continuousOn_ne_zero {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] {K : Set (ℝ × X)}
    {f : ι → ℝ × X → E} (hK : IsCompact K)
    (hf : ∀ a, ContinuousOn (f a) K)
    (hne : ∀ a ⦃z : ℝ × X⦄, z ∈ K → f a z ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ a ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖f a z‖ := by
  classical
  rcases exists_pos_norm_lower_bound_finset_of_isCompact_of_continuousOn_ne_zero
      (K := K) (f := f) (S := Finset.univ) hK hf hne with
    ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro a z hz
  exact hδ (a := a) (Finset.mem_univ a) (z := z) hz

/-- The sup constant for a single Leibniz-term in the determinant estimate. -/
def matrixDetTermBoundConst {n A : Type*} [Fintype n] [NormedRing A]
    (B : n → n → ℝ) (σ : Equiv.Perm n) : ℝ :=
  max ‖(1 : A)‖ 1 * ∏ i : n, max (B (σ i) i) 1

/-- The Holder constant for a single Leibniz-term in the determinant estimate. -/
def matrixDetTermHolderConst {n A : Type*} [Fintype n] [NormedRing A]
    (B H : n → n → ℝ) (σ : Equiv.Perm n) : ℝ :=
  (∑ i : n, H (σ i) i) * matrixDetTermBoundConst (A := A) B σ

/-- The sup constant used by the quantitative finite determinant estimate. -/
def matrixDetBoundConst {n A : Type*} [Fintype n] [DecidableEq n] [NormedRing A]
    (B : n → n → ℝ) : ℝ :=
  ∑ σ : Equiv.Perm n, ‖(Equiv.Perm.sign σ : ℤ)‖ *
    matrixDetTermBoundConst (A := A) B σ

/-- The Holder constant used by the quantitative finite determinant estimate. -/
def matrixDetHolderConst {n A : Type*} [Fintype n] [DecidableEq n] [NormedRing A]
    (B H : n → n → ℝ) : ℝ :=
  ∑ σ : Equiv.Perm n, ‖(Equiv.Perm.sign σ : ℤ)‖ *
    matrixDetTermHolderConst (A := A) B H σ

/-- The sup constant for a determinant Leibniz-term difference. -/
def matrixDetTermSubBoundConst {n A : Type*} [Fintype n] [NormedRing A]
    (B Bd : n → n → ℝ) (σ : Equiv.Perm n) : ℝ :=
  (∑ i : n, Bd (σ i) i) * matrixDetTermBoundConst (A := A) B σ

/-- The Holder constant for a determinant Leibniz-term difference. -/
def matrixDetTermSubHolderConst {n A : Type*} [Fintype n] [NormedRing A]
    (B H Bd Hd : n → n → ℝ) (σ : Equiv.Perm n) : ℝ :=
  ((∑ i : n, Hd (σ i) i) +
      (∑ i : n, H (σ i) i) * (∑ i : n, Bd (σ i) i)) *
    matrixDetTermBoundConst (A := A) B σ

/-- The sup constant for determinant differences. -/
def matrixDetSubBoundConst {n A : Type*} [Fintype n] [DecidableEq n] [NormedRing A]
    (B Bd : n → n → ℝ) : ℝ :=
  ∑ σ : Equiv.Perm n, ‖(Equiv.Perm.sign σ : ℤ)‖ *
    matrixDetTermSubBoundConst (A := A) B Bd σ

/-- The Holder constant for determinant differences. -/
def matrixDetSubHolderConst {n A : Type*} [Fintype n] [DecidableEq n] [NormedRing A]
    (B H Bd Hd : n → n → ℝ) : ℝ :=
  ∑ σ : Equiv.Perm n, ‖(Equiv.Perm.sign σ : ℤ)‖ *
    matrixDetTermSubHolderConst (A := A) B H Bd Hd σ

/-- The sup constant for reciprocal determinant differences. -/
def matrixDetInvSubBoundConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (B Bd : n → n → ℝ) : ℝ :=
  ParabolicC0AlphaWith.invSubBoundConst δ (matrixDetSubBoundConst (A := 𝕜) B Bd)

/-- The Holder constant for reciprocal determinant differences. -/
def matrixDetInvSubHolderConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (B H Bd Hd : n → n → ℝ) : ℝ :=
  ParabolicC0AlphaWith.invSubHolderConst δ
    (matrixDetHolderConst (A := 𝕜) B H)
    (matrixDetHolderConst (A := 𝕜) B H)
    (matrixDetSubBoundConst (A := 𝕜) B Bd)
    (matrixDetSubHolderConst (A := 𝕜) B H Bd Hd)

theorem matrixDetTermBoundConst_nonneg {n A : Type*} [Fintype n] [NormedRing A]
    (B : n → n → ℝ) (σ : Equiv.Perm n) :
    0 ≤ matrixDetTermBoundConst (A := A) B σ := by
  exact mul_nonneg (zero_le_one.trans (le_max_right _ _))
    (Finset.prod_nonneg fun i _hi => zero_le_one.trans (le_max_right (B (σ i) i) 1))

theorem matrixDetTermHolderConst_nonneg {n A : Type*} [Fintype n] [NormedRing A]
    {B H : n → n → ℝ} (hH : ∀ i j, 0 ≤ H i j) (σ : Equiv.Perm n) :
    0 ≤ matrixDetTermHolderConst (A := A) B H σ := by
  exact mul_nonneg
    (Finset.sum_nonneg fun i _hi => hH (σ i) i)
    (matrixDetTermBoundConst_nonneg (A := A) B σ)

theorem matrixDetBoundConst_nonneg {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedRing A] (B : n → n → ℝ) :
    0 ≤ matrixDetBoundConst (A := A) B := by
  exact Finset.sum_nonneg fun σ _hσ =>
    mul_nonneg (norm_nonneg _) (matrixDetTermBoundConst_nonneg (A := A) B σ)

theorem matrixDetHolderConst_nonneg {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedRing A] {B H : n → n → ℝ} (hH : ∀ i j, 0 ≤ H i j) :
    0 ≤ matrixDetHolderConst (A := A) B H := by
  exact Finset.sum_nonneg fun σ _hσ =>
    mul_nonneg (norm_nonneg _) (matrixDetTermHolderConst_nonneg (A := A) hH σ)

theorem matrixDetTermSubBoundConst_nonneg {n A : Type*} [Fintype n] [NormedRing A]
    {B Bd : n → n → ℝ} (hBd : ∀ i j, 0 ≤ Bd i j) (σ : Equiv.Perm n) :
    0 ≤ matrixDetTermSubBoundConst (A := A) B Bd σ := by
  exact mul_nonneg
    (Finset.sum_nonneg fun i _hi => hBd (σ i) i)
    (matrixDetTermBoundConst_nonneg (A := A) B σ)

theorem matrixDetTermSubHolderConst_nonneg {n A : Type*} [Fintype n] [NormedRing A]
    {B H Bd Hd : n → n → ℝ} (hH : ∀ i j, 0 ≤ H i j)
    (hBd : ∀ i j, 0 ≤ Bd i j) (hHd : ∀ i j, 0 ≤ Hd i j)
    (σ : Equiv.Perm n) :
    0 ≤ matrixDetTermSubHolderConst (A := A) B H Bd Hd σ := by
  exact mul_nonneg
    (add_nonneg
      (Finset.sum_nonneg fun i _hi => hHd (σ i) i)
      (mul_nonneg
        (Finset.sum_nonneg fun i _hi => hH (σ i) i)
        (Finset.sum_nonneg fun i _hi => hBd (σ i) i)))
    (matrixDetTermBoundConst_nonneg (A := A) B σ)

theorem matrixDetSubBoundConst_nonneg {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedRing A] {B Bd : n → n → ℝ} (hBd : ∀ i j, 0 ≤ Bd i j) :
    0 ≤ matrixDetSubBoundConst (A := A) B Bd := by
  exact Finset.sum_nonneg fun σ _hσ =>
    mul_nonneg (norm_nonneg _) (matrixDetTermSubBoundConst_nonneg (A := A) hBd σ)

theorem matrixDetSubHolderConst_nonneg {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedRing A] {B H Bd Hd : n → n → ℝ} (hH : ∀ i j, 0 ≤ H i j)
    (hBd : ∀ i j, 0 ≤ Bd i j) (hHd : ∀ i j, 0 ≤ Hd i j) :
    0 ≤ matrixDetSubHolderConst (A := A) B H Bd Hd := by
  exact Finset.sum_nonneg fun σ _hσ =>
    mul_nonneg (norm_nonneg _)
      (matrixDetTermSubHolderConst_nonneg (A := A) hH hBd hHd σ)

theorem matrixDetInvSubBoundConst_nonneg {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {B Bd : n → n → ℝ}
    (hδpos : 0 < δ) (hBd : ∀ i j, 0 ≤ Bd i j) :
    0 ≤ matrixDetInvSubBoundConst (𝕜 := 𝕜) δ B Bd :=
  ParabolicC0AlphaWith.invSubBoundConst_nonneg hδpos
    (matrixDetSubBoundConst_nonneg (A := 𝕜) hBd)

theorem matrixDetInvSubHolderConst_nonneg {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {B H Bd Hd : n → n → ℝ}
    (hδpos : 0 < δ) (hH : ∀ i j, 0 ≤ H i j)
    (hBd : ∀ i j, 0 ≤ Bd i j) (hHd : ∀ i j, 0 ≤ Hd i j) :
    0 ≤ matrixDetInvSubHolderConst (𝕜 := 𝕜) δ B H Bd Hd :=
  ParabolicC0AlphaWith.invSubHolderConst_nonneg hδpos
    (matrixDetHolderConst_nonneg (A := 𝕜) hH)
    (matrixDetHolderConst_nonneg (A := 𝕜) hH)
    (matrixDetSubBoundConst_nonneg (A := 𝕜) hBd)
    (matrixDetSubHolderConst_nonneg (A := 𝕜) hH hBd hHd)

/-- The determinant of a finite matrix whose entries have explicit parabolic `C^{0,α}` bounds
has an explicit bounded parabolic `C^{0,α}` estimate.  This is the quantitative version used
before passing to the existential `ParabolicC0AlphaOn` closure theorem. -/
theorem matrix_det_with {n A : Type*} [Fintype n] [DecidableEq n] [NormedCommRing A]
    {B H : n → n → ℝ} {M : ℝ × X → Matrix n n A}
    (hH : ∀ i j, 0 ≤ H i j)
    (hM : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => M z i j) s) :
    ParabolicC0AlphaWith
      (matrixDetBoundConst (A := A) B) (matrixDetHolderConst (A := A) B H)
      α (fun z => (M z).det) s := by
  classical
  let term : Equiv.Perm n → ℝ × X → A :=
    fun σ z => ((Equiv.Perm.sign σ : ℤ) : A) * ∏ i : n, M z (σ i) i
  have hterm : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm n)),
      ParabolicC0AlphaWith
        (‖(Equiv.Perm.sign σ : ℤ)‖ * matrixDetTermBoundConst (A := A) B σ)
        (‖(Equiv.Perm.sign σ : ℤ)‖ * matrixDetTermHolderConst (A := A) B H σ)
        α (term σ) s := by
    intro σ _hσ
    have hprod :
        ParabolicC0AlphaWith
          (matrixDetTermBoundConst (A := A) B σ)
          (matrixDetTermHolderConst (A := A) B H σ)
          α (fun z => ∏ i : n, M z (σ i) i) s := by
      simpa [matrixDetTermBoundConst, matrixDetTermHolderConst] using
        (ParabolicC0AlphaWith.finset_prod (X := X) (α := α) (s := s)
          (S := (Finset.univ : Finset n))
          (B := fun i => B (σ i) i)
          (H := fun i => H (σ i) i)
          (u := fun i z => M z (σ i) i)
          (fun i _hi => hH (σ i) i)
          (fun i _hi => hM (σ i) i))
    dsimp [term]
    simpa [zsmul_eq_mul] using hprod.zsmul (Equiv.Perm.sign σ)
  have hsum :
      ParabolicC0AlphaWith
        (matrixDetBoundConst (A := A) B) (matrixDetHolderConst (A := A) B H)
        α (fun z => ∑ σ : Equiv.Perm n, term σ z) s := by
    simpa [matrixDetBoundConst, matrixDetHolderConst] using
      (ParabolicC0AlphaWith.sum (X := X) (α := α) (s := s)
        (S := (Finset.univ : Finset (Equiv.Perm n)))
        (B := fun σ => ‖(Equiv.Perm.sign σ : ℤ)‖ *
          matrixDetTermBoundConst (A := A) B σ)
        (H := fun σ => ‖(Equiv.Perm.sign σ : ℤ)‖ *
          matrixDetTermHolderConst (A := A) B H σ)
        (u := term) hterm)
  convert hsum using 1
  funext z
  dsimp [term]
  rw [Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _hσ
  rw [← zsmul_eq_mul]
  rfl

/-- Determinant differences inherit parabolic `C^{0,α}` control from entrywise difference
controls.  The Holder constant depends on the entrywise Holder constants of `M - N`, not merely
on subtracting two standalone determinant estimates. -/
theorem matrix_det_sub_with {n A : Type*} [Fintype n] [DecidableEq n] [NormedCommRing A]
    {B H Bd Hd : n → n → ℝ} {M N : ℝ × X → Matrix n n A}
    (hH : ∀ i j, 0 ≤ H i j)
    (hBd : ∀ i j, 0 ≤ Bd i j)
    (hHd : ∀ i j, 0 ≤ Hd i j)
    (hM : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => M z i j) s)
    (hN : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => N z i j) s)
    (hdiff : ∀ i j,
      ParabolicC0AlphaWith (Bd i j) (Hd i j) α (fun z => M z i j - N z i j) s) :
    ParabolicC0AlphaWith
      (matrixDetSubBoundConst (A := A) B Bd)
      (matrixDetSubHolderConst (A := A) B H Bd Hd)
      α (fun z => (M z).det - (N z).det) s := by
  classical
  let termM : Equiv.Perm n → ℝ × X → A :=
    fun σ z => ((Equiv.Perm.sign σ : ℤ) : A) * ∏ i : n, M z (σ i) i
  let termN : Equiv.Perm n → ℝ × X → A :=
    fun σ z => ((Equiv.Perm.sign σ : ℤ) : A) * ∏ i : n, N z (σ i) i
  have hterm : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm n)),
      ParabolicC0AlphaWith
        (‖(Equiv.Perm.sign σ : ℤ)‖ *
          matrixDetTermSubBoundConst (A := A) B Bd σ)
        (‖(Equiv.Perm.sign σ : ℤ)‖ *
          matrixDetTermSubHolderConst (A := A) B H Bd Hd σ)
        α (fun z => termM σ z - termN σ z) s := by
    intro σ _hσ
    have hprod :
        ParabolicC0AlphaWith
          (matrixDetTermSubBoundConst (A := A) B Bd σ)
          (matrixDetTermSubHolderConst (A := A) B H Bd Hd σ)
          α
          (fun z => (∏ i : n, M z (σ i) i) -
            ∏ i : n, N z (σ i) i) s := by
      simpa [matrixDetTermSubBoundConst, matrixDetTermSubHolderConst,
        matrixDetTermBoundConst] using
        (ParabolicC0AlphaWith.finset_prod_sub_prod (X := X) (α := α) (s := s)
          (S := (Finset.univ : Finset n))
          (B := fun i => B (σ i) i)
          (H := fun i => H (σ i) i)
          (Bd := fun i => Bd (σ i) i)
          (Hd := fun i => Hd (σ i) i)
          (u := fun i z => M z (σ i) i)
          (v := fun i z => N z (σ i) i)
          (fun i _hi => hH (σ i) i)
          (fun i _hi => hBd (σ i) i)
          (fun i _hi => hHd (σ i) i)
          (fun i _hi => hM (σ i) i)
          (fun i _hi => hN (σ i) i)
          (fun i _hi => hdiff (σ i) i))
    dsimp [termM, termN]
    simpa [zsmul_eq_mul, mul_sub] using hprod.zsmul (Equiv.Perm.sign σ)
  have hsum :
      ParabolicC0AlphaWith
        (matrixDetSubBoundConst (A := A) B Bd)
        (matrixDetSubHolderConst (A := A) B H Bd Hd)
        α (fun z => ∑ σ : Equiv.Perm n, (termM σ z - termN σ z)) s := by
    simpa [matrixDetSubBoundConst, matrixDetSubHolderConst] using
      (ParabolicC0AlphaWith.sum (X := X) (α := α) (s := s)
        (S := (Finset.univ : Finset (Equiv.Perm n)))
        (B := fun σ => ‖(Equiv.Perm.sign σ : ℤ)‖ *
          matrixDetTermSubBoundConst (A := A) B Bd σ)
        (H := fun σ => ‖(Equiv.Perm.sign σ : ℤ)‖ *
          matrixDetTermSubHolderConst (A := A) B H Bd Hd σ)
        (u := fun σ z => termM σ z - termN σ z) hterm)
  convert hsum using 1
  funext z
  dsimp [termM, termN]
  rw [Matrix.det_apply, Matrix.det_apply]
  rw [Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro σ _hσ
    rw [← zsmul_eq_mul]
    rfl
  · apply Finset.sum_congr rfl
    intro σ _hσ
    rw [← zsmul_eq_mul]
    rfl

end ParabolicC0AlphaOn

namespace ParabolicC0AlphaNormLe

variable {X : Type*} [PseudoMetricSpace X]
variable {α : ℝ} {s : Set (ℝ × X)}

/-- Entrywise single-radius control packages the determinant with the corresponding quantitative
determinant radius. -/
theorem matrix_det_of_entries {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedCommRing A] {N : n → n → ℝ} {M : ℝ × X → Matrix n n A}
    (h : ∀ i j, ParabolicC0AlphaNormLe (N i j) α (fun z => M z i j) s) :
    ParabolicC0AlphaNormLe
      (ParabolicC0AlphaOn.matrixDetBoundConst (A := A) N +
        ParabolicC0AlphaOn.matrixDetHolderConst (A := A) N N)
      α (fun z => (M z).det) s := by
  have hN : ∀ i j, 0 ≤ N i j := fun i j => (h i j).nonneg
  exact ParabolicC0AlphaNormLe.of_c0AlphaWith
    (ParabolicC0AlphaOn.matrixDetBoundConst_nonneg (A := A) N)
    (ParabolicC0AlphaOn.matrixDetHolderConst_nonneg (A := A) hN)
    (ParabolicC0AlphaOn.matrix_det_with (M := M) (B := N) (H := N) hN fun i j =>
      ParabolicC0AlphaNormLe.c0AlphaWith_self (h i j))

/-- Entrywise single-radius control of two matrices and their difference packages determinant
differences with the corresponding quantitative determinant-difference radius. -/
theorem matrix_det_sub_of_entries {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedCommRing A] {R Rd : n → n → ℝ} {M N : ℝ × X → Matrix n n A}
    (hM : ∀ i j, ParabolicC0AlphaNormLe (R i j) α (fun z => M z i j) s)
    (hN : ∀ i j, ParabolicC0AlphaNormLe (R i j) α (fun z => N z i j) s)
    (hdiff : ∀ i j, ParabolicC0AlphaNormLe (Rd i j) α
      (fun z => M z i j - N z i j) s) :
    ParabolicC0AlphaNormLe
      (ParabolicC0AlphaOn.matrixDetSubBoundConst (A := A) R Rd +
        ParabolicC0AlphaOn.matrixDetSubHolderConst (A := A) R R Rd Rd)
      α (fun z => (M z).det - (N z).det) s := by
  have hR : ∀ i j, 0 ≤ R i j := fun i j => (hM i j).nonneg
  have hRd : ∀ i j, 0 ≤ Rd i j := fun i j => (hdiff i j).nonneg
  exact ParabolicC0AlphaNormLe.of_c0AlphaWith
    (ParabolicC0AlphaOn.matrixDetSubBoundConst_nonneg (A := A) hRd)
    (ParabolicC0AlphaOn.matrixDetSubHolderConst_nonneg (A := A) hR hRd hRd)
    (ParabolicC0AlphaOn.matrix_det_sub_with (M := M) (N := N)
      (B := R) (H := R) (Bd := Rd) (Hd := Rd)
      hR hRd hRd
      (fun i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hM i j))
      (fun i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hN i j))
      (fun i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hdiff i j)))

end ParabolicC0AlphaNormLe

namespace ParabolicC0AlphaOn

variable {X : Type*} [PseudoMetricSpace X]
variable {α : ℝ} {s : Set (ℝ × X)}

/-- Reciprocal determinant differences inherit parabolic `C^{0,α}` control from entrywise matrix
difference controls under a common determinant lower bound. -/
theorem matrix_det_inv_sub_with {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {B H Bd Hd : n → n → ℝ} {δ : ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    (hH : ∀ i j, 0 ≤ H i j)
    (hBd : ∀ i j, 0 ≤ Bd i j)
    (hHd : ∀ i j, 0 ≤ Hd i j)
    (hM : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => M z i j) s)
    (hN : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => N z i j) s)
    (hdiff : ∀ i j,
      ParabolicC0AlphaWith (Bd i j) (Hd i j) α (fun z => M z i j - N z i j) s)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicC0AlphaWith
      (matrixDetInvSubBoundConst (𝕜 := 𝕜) δ B Bd)
      (matrixDetInvSubHolderConst (𝕜 := 𝕜) δ B H Bd Hd)
      α (fun z => ((M z).det)⁻¹ - ((N z).det)⁻¹) s := by
  have hdetM_with :
      ParabolicC0AlphaWith
        (matrixDetBoundConst (A := 𝕜) B)
        (matrixDetHolderConst (A := 𝕜) B H)
        α (fun z => (M z).det) s :=
    matrix_det_with (M := M) hH hM
  have hdetN_with :
      ParabolicC0AlphaWith
        (matrixDetBoundConst (A := 𝕜) B)
        (matrixDetHolderConst (A := 𝕜) B H)
        α (fun z => (N z).det) s :=
    matrix_det_with (M := N) hH hN
  have hdetdiff :
      ParabolicC0AlphaWith
        (matrixDetSubBoundConst (A := 𝕜) B Bd)
        (matrixDetSubHolderConst (A := 𝕜) B H Bd Hd)
        α (fun z => (M z).det - (N z).det) s :=
    matrix_det_sub_with (M := M) (N := N) hH hBd hHd hM hN hdiff
  simpa [matrixDetInvSubBoundConst, matrixDetInvSubHolderConst] using
    hdetM_with.inv_sub_inv hdetN_with hdetdiff hδpos hdetM hdetN
      (matrixDetSubBoundConst_nonneg (A := 𝕜) hBd)

/-- Determinants are pointwise Lipschitz on entrywise bounded finite matrices.  This is the
finite-dimensional algebra estimate behind local Lipschitz control of determinant terms in chart
coordinates. -/
theorem matrix_det_norm_sub_le {n A : Type*} [Fintype n] [DecidableEq n] [NormedCommRing A]
    {C : n → n → ℝ} (M N : Matrix n n A)
    (hM : ∀ i j, ‖M i j‖ ≤ C i j) (hN : ∀ i j, ‖N i j‖ ≤ C i j) :
    ‖M.det - N.det‖ ≤
      ∑ σ : Equiv.Perm n,
        ‖(Equiv.Perm.sign σ : ℤ)‖ *
          ((∑ i : n, ‖M (σ i) i - N (σ i) i‖) *
            (max ‖(1 : A)‖ 1 * ∏ i : n, max (C (σ i) i) 1)) := by
  classical
  let termM : Equiv.Perm n → A :=
    fun σ => ((Equiv.Perm.sign σ : ℤ) : A) * ∏ i : n, M (σ i) i
  let termN : Equiv.Perm n → A :=
    fun σ => ((Equiv.Perm.sign σ : ℤ) : A) * ∏ i : n, N (σ i) i
  have hdetM : M.det = ∑ σ : Equiv.Perm n, termM σ := by
    dsimp [termM]
    rw [Matrix.det_apply]
    apply Finset.sum_congr rfl
    intro σ _hσ
    rw [← zsmul_eq_mul]
    rfl
  have hdetN : N.det = ∑ σ : Equiv.Perm n, termN σ := by
    dsimp [termN]
    rw [Matrix.det_apply]
    apply Finset.sum_congr rfl
    intro σ _hσ
    rw [← zsmul_eq_mul]
    rfl
  have hterm : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm n)),
      ‖termM σ - termN σ‖ ≤
        ‖(Equiv.Perm.sign σ : ℤ)‖ *
          ((∑ i : n, ‖M (σ i) i - N (σ i) i‖) *
            (max ‖(1 : A)‖ 1 * ∏ i : n, max (C (σ i) i) 1)) := by
    intro σ _hσ
    have hprod :
        ‖(∏ i : n, M (σ i) i) - ∏ i : n, N (σ i) i‖ ≤
          (∑ i : n, ‖M (σ i) i - N (σ i) i‖) *
            (max ‖(1 : A)‖ 1 * ∏ i : n, max (C (σ i) i) 1) := by
      simpa using
        (norm_finset_prod_sub_prod_le_sum_norm_sub_mul_unit_prod_max
          (A := A) (S := (Finset.univ : Finset n))
          (C := fun i => C (σ i) i)
          (a := fun i => M (σ i) i)
          (b := fun i => N (σ i) i)
          (fun i _hi => hM (σ i) i)
          (fun i _hi => hN (σ i) i))
    have hsub :
        termM σ - termN σ =
          (Equiv.Perm.sign σ : ℤ) • ((∏ i : n, M (σ i) i) - ∏ i : n, N (σ i) i) := by
      dsimp [termM, termN]
      rw [← zsmul_eq_mul, ← zsmul_eq_mul, zsmul_sub]
    calc
      ‖termM σ - termN σ‖ =
          ‖(Equiv.Perm.sign σ : ℤ) • ((∏ i : n, M (σ i) i) - ∏ i : n, N (σ i) i)‖ := by
        rw [hsub]
      _ ≤ ‖(Equiv.Perm.sign σ : ℤ)‖ *
            ‖(∏ i : n, M (σ i) i) - ∏ i : n, N (σ i) i‖ :=
        norm_zsmul_le _ _
      _ ≤ ‖(Equiv.Perm.sign σ : ℤ)‖ *
          ((∑ i : n, ‖M (σ i) i - N (σ i) i‖) *
            (max ‖(1 : A)‖ 1 * ∏ i : n, max (C (σ i) i) 1)) :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
  calc
    ‖M.det - N.det‖ =
        ‖(∑ σ : Equiv.Perm n, termM σ) - ∑ σ : Equiv.Perm n, termN σ‖ := by
      rw [hdetM, hdetN]
    _ = ‖∑ σ : Equiv.Perm n, (termM σ - termN σ)‖ := by
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ σ : Equiv.Perm n, ‖termM σ - termN σ‖ :=
      norm_sum_le _ _
    _ ≤ ∑ σ : Equiv.Perm n,
        ‖(Equiv.Perm.sign σ : ℤ)‖ *
          ((∑ i : n, ‖M (σ i) i - N (σ i) i‖) *
            (max ‖(1 : A)‖ 1 * ∏ i : n, max (C (σ i) i) 1)) :=
      Finset.sum_le_sum hterm

/-- Elementwise matrix-norm Lipschitz constant for the determinant on an entrywise bounded set. -/
def matrixDetLipschitzConst {n A : Type*} [Fintype n] [DecidableEq n] [NormedCommRing A]
    (C : n → n → ℝ) : ℝ :=
  ∑ σ : Equiv.Perm n,
    ‖(Equiv.Perm.sign σ : ℤ)‖ *
      ((Fintype.card n : ℝ) *
        (max ‖(1 : A)‖ 1 * ∏ i : n, max (C (σ i) i) 1))

theorem matrixDetLipschitzConst_nonneg {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedCommRing A] (C : n → n → ℝ) :
    0 ≤ matrixDetLipschitzConst (A := A) C := by
  exact Finset.sum_nonneg fun σ _hσ =>
    mul_nonneg (norm_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (zero_le_one.trans (le_max_right _ _))
          (Finset.prod_nonneg fun i _hi =>
            zero_le_one.trans (le_max_right (C (σ i) i) 1))))

/-- Determinants are Lipschitz in the elementwise matrix norm on entrywise bounded finite
matrices. -/
theorem matrix_det_norm_sub_le_const_mul {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedCommRing A] {C : n → n → ℝ} (M N : Matrix n n A)
    (hM : ∀ i j, ‖M i j‖ ≤ C i j) (hN : ∀ i j, ‖N i j‖ ≤ C i j) :
    ‖M.det - N.det‖ ≤ matrixDetLipschitzConst (A := A) C * ‖M - N‖ := by
  classical
  have hbase := matrix_det_norm_sub_le (C := C) M N hM hN
  have hsum : ∀ σ : Equiv.Perm n,
      (∑ i : n, ‖M (σ i) i - N (σ i) i‖) ≤
        (Fintype.card n : ℝ) * ‖M - N‖ := by
    intro σ
    calc
      (∑ i : n, ‖M (σ i) i - N (σ i) i‖) ≤ ∑ _i : n, ‖M - N‖ := by
        exact Finset.sum_le_sum fun i _hi => by
          simpa using Matrix.norm_entry_le_entrywise_sup_norm (M - N) (i := σ i) (j := i)
      _ = (Fintype.card n : ℝ) * ‖M - N‖ := by
        simp
  refine hbase.trans ?_
  calc
    (∑ σ : Equiv.Perm n,
        ‖(Equiv.Perm.sign σ : ℤ)‖ *
          ((∑ i : n, ‖M (σ i) i - N (σ i) i‖) *
            (max ‖(1 : A)‖ 1 * ∏ i : n, max (C (σ i) i) 1)))
        ≤
      ∑ σ : Equiv.Perm n,
        (‖(Equiv.Perm.sign σ : ℤ)‖ *
          ((Fintype.card n : ℝ) *
            (max ‖(1 : A)‖ 1 * ∏ i : n, max (C (σ i) i) 1))) * ‖M - N‖ := by
      refine Finset.sum_le_sum fun σ _hσ => ?_
      let Lσ : ℝ := max ‖(1 : A)‖ 1 * ∏ i : n, max (C (σ i) i) 1
      have hLσ_nonneg : 0 ≤ Lσ := by
        exact mul_nonneg (zero_le_one.trans (le_max_right _ _))
          (Finset.prod_nonneg fun i _hi => zero_le_one.trans (le_max_right (C (σ i) i) 1))
      calc
        ‖(Equiv.Perm.sign σ : ℤ)‖ *
            ((∑ i : n, ‖M (σ i) i - N (σ i) i‖) * Lσ) ≤
          ‖(Equiv.Perm.sign σ : ℤ)‖ *
            (((Fintype.card n : ℝ) * ‖M - N‖) * Lσ) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hsum σ) hLσ_nonneg) (norm_nonneg _)
        _ =
          (‖(Equiv.Perm.sign σ : ℤ)‖ *
            ((Fintype.card n : ℝ) * Lσ)) * ‖M - N‖ := by
          ring
    _ = matrixDetLipschitzConst (A := A) C * ‖M - N‖ := by
      simp [matrixDetLipschitzConst, Finset.sum_mul, mul_assoc]

/-- Determinants are bounded-difference controlled on a time-space set by a uniform matrix
difference bound. -/
theorem matrix_det_bounded_sub_le_const_mul {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedCommRing A] {C : n → n → ℝ} {η : ℝ}
    {M N : ℝ × X → Matrix n n A}
    (hM : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ i j, ‖M z i j‖ ≤ C i j)
    (hN : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ i j, ‖N z i j‖ ≤ C i j)
    (hdiff : ∀ ⦃z : ℝ × X⦄, z ∈ s → ‖M z - N z‖ ≤ η) :
    ParabolicBoundedWith (matrixDetLipschitzConst (A := A) C * η)
      (fun z : ℝ × X => (M z).det - (N z).det) s := by
  intro z hz
  exact (matrix_det_norm_sub_le_const_mul (C := C) (M z) (N z) (hM hz) (hN hz)).trans
    (mul_le_mul_of_nonneg_left (hdiff hz) (matrixDetLipschitzConst_nonneg (A := A) C))

/-- Determinants are pointwise bounded by the quantitative finite product constant. -/
theorem matrix_det_norm_le {n A : Type*} [Fintype n] [DecidableEq n] [NormedCommRing A]
    {C : n → n → ℝ} (M : Matrix n n A)
    (hM : ∀ i j, ‖M i j‖ ≤ C i j) :
    ‖M.det‖ ≤ matrixDetBoundConst (A := A) C := by
  classical
  let term : Equiv.Perm n → A :=
    fun σ => ((Equiv.Perm.sign σ : ℤ) : A) * ∏ i : n, M (σ i) i
  have hdet : M.det = ∑ σ : Equiv.Perm n, term σ := by
    dsimp [term]
    rw [Matrix.det_apply]
    apply Finset.sum_congr rfl
    intro σ _hσ
    rw [← zsmul_eq_mul]
    rfl
  have hterm : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm n)),
      ‖term σ‖ ≤
        ‖(Equiv.Perm.sign σ : ℤ)‖ * matrixDetTermBoundConst (A := A) C σ := by
    intro σ _hσ
    have hprod :
        ‖∏ i : n, M (σ i) i‖ ≤ matrixDetTermBoundConst (A := A) C σ := by
      simpa [matrixDetTermBoundConst] using
        (norm_finset_prod_le_unit_mul_prod_max
          (A := A) (S := (Finset.univ : Finset n))
          (C := fun i => C (σ i) i)
          (a := fun i => M (σ i) i)
          (fun i _hi => hM (σ i) i))
    have hterm_zsmul :
        term σ = (Equiv.Perm.sign σ : ℤ) • (∏ i : n, M (σ i) i) := by
      dsimp [term]
      rw [← zsmul_eq_mul]
    calc
      ‖term σ‖ = ‖(Equiv.Perm.sign σ : ℤ) • (∏ i : n, M (σ i) i)‖ := by
        rw [hterm_zsmul]
      _ ≤ ‖(Equiv.Perm.sign σ : ℤ)‖ * ‖∏ i : n, M (σ i) i‖ :=
        norm_zsmul_le _ _
      _ ≤ ‖(Equiv.Perm.sign σ : ℤ)‖ * matrixDetTermBoundConst (A := A) C σ :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
  calc
    ‖M.det‖ = ‖∑ σ : Equiv.Perm n, term σ‖ := by rw [hdet]
    _ ≤ ∑ σ : Equiv.Perm n, ‖term σ‖ := norm_sum_le _ _
    _ ≤ ∑ σ : Equiv.Perm n,
        ‖(Equiv.Perm.sign σ : ℤ)‖ * matrixDetTermBoundConst (A := A) C σ :=
      Finset.sum_le_sum hterm
    _ = matrixDetBoundConst (A := A) C := by
      rfl

/-- The determinant of a finite matrix whose entries are parabolic `C^{0,α}` functions is
again parabolic `C^{0,α}`. -/
theorem matrix_det {n A : Type*} [Fintype n] [DecidableEq n] [NormedCommRing A]
    {M : ℝ × X → Matrix n n A}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s) :
    ParabolicC0AlphaOn α (fun z => (M z).det) s := by
  classical
  let term : Equiv.Perm n → ℝ × X → A :=
    fun σ z => ((Equiv.Perm.sign σ : ℤ) : A) * ∏ i : n, M z (σ i) i
  have hterm : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm n)),
      ParabolicC0AlphaOn α (term σ) s := by
    intro σ _hσ
    have hprod : ParabolicC0AlphaOn α (fun z => ∏ i : n, M z (σ i) i) s := by
      simpa using
        (ParabolicC0AlphaOn.finset_prod (X := X) (α := α) (s := s)
          (S := (Finset.univ : Finset n))
          (u := fun i z => M z (σ i) i)
          (fun i _hi => hM (σ i) i))
    dsimp [term]
    simpa [zsmul_eq_mul] using hprod.zsmul (Equiv.Perm.sign σ : ℤ)
  have hsum :
      ParabolicC0AlphaOn α
        (fun z => ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm n)), term σ z) s :=
    ParabolicC0AlphaOn.sum (X := X) (α := α) (s := s)
      (S := (Finset.univ : Finset (Equiv.Perm n))) hterm
  convert hsum using 1
  funext z
  dsimp [term]
  rw [Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _hσ
  rw [← zsmul_eq_mul]
  rfl

/-- Determinant differences inherit existential parabolic `C^{0,α}` control from entrywise
controls and entrywise difference controls. -/
theorem matrix_det_sub {n A : Type*} [Fintype n] [DecidableEq n] [NormedCommRing A]
    {M N : ℝ × X → Matrix n n A}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s)
    (hN : ∀ i j, ParabolicC0AlphaOn α (fun z => N z i j) s)
    (hdiff : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j - N z i j) s) :
    ParabolicC0AlphaOn α (fun z => (M z).det - (N z).det) s := by
  classical
  let termM : Equiv.Perm n → ℝ × X → A :=
    fun σ z => ((Equiv.Perm.sign σ : ℤ) : A) * ∏ i : n, M z (σ i) i
  let termN : Equiv.Perm n → ℝ × X → A :=
    fun σ z => ((Equiv.Perm.sign σ : ℤ) : A) * ∏ i : n, N z (σ i) i
  have hterm : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm n)),
      ParabolicC0AlphaOn α (fun z => termM σ z - termN σ z) s := by
    intro σ _hσ
    have hprod :
        ParabolicC0AlphaOn α
          (fun z => (∏ i : n, M z (σ i) i) - ∏ i : n, N z (σ i) i) s := by
      simpa using
        (ParabolicC0AlphaOn.finset_prod_sub_prod (X := X) (α := α) (s := s)
          (S := (Finset.univ : Finset n))
          (u := fun i z => M z (σ i) i)
          (v := fun i z => N z (σ i) i)
          (fun i _hi => hM (σ i) i)
          (fun i _hi => hN (σ i) i)
          (fun i _hi => hdiff (σ i) i))
    dsimp [termM, termN]
    simpa [zsmul_eq_mul, mul_sub] using hprod.zsmul (Equiv.Perm.sign σ)
  have hsum :
      ParabolicC0AlphaOn α
        (fun z => ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm n)),
          (termM σ z - termN σ z)) s :=
    ParabolicC0AlphaOn.sum (X := X) (α := α) (s := s)
      (S := (Finset.univ : Finset (Equiv.Perm n))) hterm
  convert hsum using 1
  funext z
  dsimp [termM, termN]
  rw [Matrix.det_apply, Matrix.det_apply]
  rw [Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro σ _hσ
    rw [← zsmul_eq_mul]
    rfl
  · apply Finset.sum_congr rfl
    intro σ _hσ
    rw [← zsmul_eq_mul]
    rfl

/-- Reciprocal determinant differences inherit existential parabolic `C^{0,α}` control from
entrywise matrix controls and a common determinant lower bound. -/
theorem matrix_det_inv_sub {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {M N : ℝ × X → Matrix n n 𝕜} {δ : ℝ}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s)
    (hN : ∀ i j, ParabolicC0AlphaOn α (fun z => N z i j) s)
    (hdiff : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j - N z i j) s)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicC0AlphaOn α (fun z => ((M z).det)⁻¹ - ((N z).det)⁻¹) s :=
  (matrix_det (M := M) hM).inv_sub_inv (matrix_det (M := N) hN)
    (matrix_det_sub (M := M) (N := N) hM hN hdiff) hδpos hdetM hdetN

/-- On a compact time-space set, a finite matrix with parabolic `C^{0,α}` entries and nonvanishing
determinant has determinant norm uniformly bounded away from zero. -/
theorem matrix_det_exists_pos_norm_lower_bound_of_isCompact {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)} {M : ℝ × X → Matrix n n 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) K)
    (hdet_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M z).det‖ :=
  exists_pos_norm_lower_bound_of_isCompact_of_continuousOn_ne_zero hK
    ((matrix_det (M := M) hM).continuousOn hα) hdet_ne

/-- On a compact time-space set, two finite matrices with parabolic `C^{0,α}` entries and
nonvanishing determinants have a common positive determinant-norm lower bound. -/
theorem matrix_det_pair_exists_pos_norm_lower_bound_of_isCompact {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)}
    {M N : ℝ × X → Matrix n n 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) K)
    (hN : ∀ i j, ParabolicC0AlphaOn α (fun z => N z i j) K)
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (N z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M z).det‖) ∧
      (∀ ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(N z).det‖) := by
  rcases matrix_det_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hM hdetM_ne with
    ⟨δM, hδM, hdetM⟩
  rcases matrix_det_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := N) hK hα hN hdetN_ne with
    ⟨δN, hδN, hdetN⟩
  refine ⟨min δM δN, lt_min hδM hδN, ?_, ?_⟩
  · intro z hz
    exact (min_le_left δM δN).trans (hdetM hz)
  · intro z hz
    exact (min_le_right δM δN).trans (hdetN hz)

/-- Compact-domain reciprocal determinant difference control: pointwise
nonvanishing of both determinants supplies the common determinant lower bound. -/
theorem matrix_det_inv_sub_of_isCompact_det_ne_zero {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)}
    {M N : ℝ × X → Matrix n n 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) K)
    (hN : ∀ i j, ParabolicC0AlphaOn α (fun z => N z i j) K)
    (hdiff : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j - N z i j) K)
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (N z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ParabolicC0AlphaOn α (fun z => ((M z).det)⁻¹ - ((N z).det)⁻¹) K := by
  rcases matrix_det_pair_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) (N := N) hK hα hM hN hdetM_ne hdetN_ne with
    ⟨δ, hδpos, hdetM, hdetN⟩
  exact ⟨δ, hδpos, matrix_det_inv_sub (M := M) (N := N)
    hM hN hdiff hδpos hdetM hdetN⟩

/-- On a compact time-space set, a finite family of finite matrices with parabolic `C^{0,α}`
entries and nonvanishing determinants has a common positive determinant-norm lower bound. -/
theorem matrix_det_family_exists_pos_norm_lower_bound_of_isCompact {ι n 𝕜 : Type*}
    [Fintype ι] [Fintype n] [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)}
    {M : ι → ℝ × X → Matrix n n 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hM : ∀ a i j, ParabolicC0AlphaOn α (fun z => M a z i j) K)
    (hdet_ne : ∀ a ⦃z : ℝ × X⦄, z ∈ K → (M a z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ a ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M a z).det‖ :=
  exists_pos_norm_lower_bound_fintype_of_isCompact_of_continuousOn_ne_zero
    (K := K) (f := fun a z => (M a z).det) hK
    (fun a => ((matrix_det (M := M a) (hM a)).continuousOn hα))
    (fun a z hz => hdet_ne a (z := z) hz)

/-- On a compact time-space set, two finite families of finite matrices with parabolic
`C^{0,α}` entries and nonvanishing determinants have one common positive determinant-norm
lower bound. -/
theorem matrix_det_pair_family_exists_pos_norm_lower_bound_of_isCompact {ι n 𝕜 : Type*}
    [Fintype ι] [Fintype n] [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)}
    {M N : ι → ℝ × X → Matrix n n 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hM : ∀ r i j, ParabolicC0AlphaOn α (fun z => M r z i j) K)
    (hN : ∀ r i j, ParabolicC0AlphaOn α (fun z => N r z i j) K)
    (hdetM_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (M r z).det ≠ 0)
    (hdetN_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (N r z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M r z).det‖) ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(N r z).det‖) := by
  rcases matrix_det_family_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hM hdetM_ne with
    ⟨δM, hδM, hdetM⟩
  rcases matrix_det_family_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := N) hK hα hN hdetN_ne with
    ⟨δN, hδN, hdetN⟩
  refine ⟨min δM δN, lt_min hδM hδN, ?_, ?_⟩
  · intro r z hz
    exact (min_le_left δM δN).trans (hdetM r hz)
  · intro r z hz
    exact (min_le_right δM δN).trans (hdetN r hz)

/-- Quantitative entrywise parabolic `C^{0,α}` control packages a finite vector-valued
coefficient family, summing the component constants. -/
theorem vector_of_entries_with {n A : Type*} [Fintype n] [NormedAddCommGroup A]
    {B H : n → ℝ} {v : ℝ × X → n → A}
    (hB : ∀ i, 0 ≤ B i) (hH : ∀ i, 0 ≤ H i)
    (hv : ∀ i, ParabolicC0AlphaWith (B i) (H i) α (fun z => v z i) s) :
    ParabolicC0AlphaWith (∑ i, B i) (∑ i, H i) α v s :=
  ParabolicC0AlphaWith.pi hB hH hv

/-- Quantitative entrywise parabolic `C^{0,α}` control packages a finite matrix-valued
coefficient family, summing the component constants. -/
theorem matrix_of_entries_with {m n A : Type*} [Fintype m] [Fintype n]
    [NormedAddCommGroup A] {B H : m → n → ℝ} {M : ℝ × X → Matrix m n A}
    (hB : ∀ i j, 0 ≤ B i j) (hH : ∀ i j, 0 ≤ H i j)
    (hM : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => M z i j) s) :
    ParabolicC0AlphaWith (∑ i, ∑ j, B i j) (∑ i, ∑ j, H i j) α M s := by
  refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
  · intro i
    exact Finset.sum_nonneg fun j _hj => hB i j
  · intro i
    exact Finset.sum_nonneg fun j _hj => hH i j
  · intro i
    refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
    · intro j
      exact hB i j
    · intro j
      exact hH i j
    · intro j
      exact hM i j

/-- Entrywise spatial boundedness and Holder control package as a vector-valued parabolic
`C^{0,α}` estimate for the time-independent lift. -/
theorem vector_of_snd_holder_with {n A : Type*} [Fintype n] [NormedAddCommGroup A]
    {B H : n → ℝ} {v : X → n → A}
    (hB_nonneg : ∀ i, 0 ≤ B i) (hH_nonneg : ∀ i, 0 ≤ H i) (hα : 0 ≤ α)
    (hB : ∀ i ⦃x : X⦄, x ∈ Prod.snd '' s → ‖v x i‖ ≤ B i)
    (hholder : ∀ i ⦃x : X⦄, x ∈ Prod.snd '' s → ∀ ⦃y : X⦄,
      y ∈ Prod.snd '' s → ‖v x i - v y i‖ ≤ H i * dist x y ^ α) :
    ParabolicC0AlphaWith (∑ i, B i) (∑ i, H i) α
      (fun z : ℝ × X => v z.2) s := by
  refine vector_of_entries_with hB_nonneg hH_nonneg ?_
  intro i
  exact ParabolicC0AlphaWith.of_snd_holder (s := s) (B := B i) (H := H i)
    (α := α) (f := fun x => v x i) (hB i) (hH_nonneg i) hα (hholder i)

/-- Entrywise spatial boundedness and Lipschitz control package as a vector-valued
parabolic `C^{0,1}` estimate for the time-independent lift. -/
theorem vector_of_snd_lipschitzOnWith_with {n A : Type*} [Fintype n]
    [NormedAddCommGroup A] {B : n → ℝ} {K : n → ℝ≥0} {v : X → n → A}
    (hB_nonneg : ∀ i, 0 ≤ B i)
    (hB : ∀ i ⦃x : X⦄, x ∈ Prod.snd '' s → ‖v x i‖ ≤ B i)
    (hL : ∀ i, LipschitzOnWith (K i) (fun x => v x i) (Prod.snd '' s)) :
    ParabolicC0AlphaWith (∑ i, B i) (∑ i, (K i : ℝ)) 1
      (fun z : ℝ × X => v z.2) s := by
  refine vector_of_entries_with hB_nonneg (fun i => NNReal.coe_nonneg (K i)) ?_
  intro i
  exact ParabolicC0AlphaWith.of_snd_lipschitzOnWith (s := s) (B := B i) (K := K i)
    (f := fun x => v x i) (hB i) (hL i)

/-- On a unit parabolic-diameter domain, entrywise spatial Lipschitz control packages a
finite vector-valued coefficient family as an explicit parabolic `C^{0,α}` estimate for
every `0 ≤ α ≤ 1`. -/
theorem vector_of_snd_lipschitzOnWith_with_of_parabolicDistance_le_one {n A : Type*}
    [Fintype n] [NormedAddCommGroup A] {B : n → ℝ} {K : n → ℝ≥0}
    {v : X → n → A}
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hB_nonneg : ∀ i, 0 ≤ B i)
    (hB : ∀ i ⦃x : X⦄, x ∈ Prod.snd '' s → ‖v x i‖ ≤ B i)
    (hL : ∀ i, LipschitzOnWith (K i) (fun x => v x i) (Prod.snd '' s))
    (hdiam : ∀ ⦃p : ℝ × X⦄, p ∈ s → ∀ ⦃q : ℝ × X⦄, q ∈ s →
      parabolicDistance p q ≤ 1) :
    ParabolicC0AlphaWith (∑ i, B i) (∑ i, (K i : ℝ)) α
      (fun z : ℝ × X => v z.2) s :=
  (vector_of_snd_lipschitzOnWith_with hB_nonneg hB hL).mono_exponent_of_parabolicDistance_le_one
    (Finset.sum_nonneg fun i _hi => NNReal.coe_nonneg (K i))
    hα_nonneg hα_le_one hdiam

/-- On a subset of a closed parabolic ball of diameter at most one, entrywise spatial Lipschitz
control packages a finite vector-valued coefficient family as an explicit parabolic `C^{0,α}`
estimate for every `0 ≤ α ≤ 1`. -/
theorem vector_of_snd_lipschitzOnWith_with_of_subset_closedBall {n A : Type*}
    [Fintype n] [NormedAddCommGroup A] {B : n → ℝ} {K : n → ℝ≥0}
    {v : X → n → A} {R : ℝ} {c : ℝ × X}
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hB_nonneg : ∀ i, 0 ≤ B i)
    (hB : ∀ i ⦃x : X⦄, x ∈ Prod.snd '' s → ‖v x i‖ ≤ B i)
    (hL : ∀ i, LipschitzOnWith (K i) (fun x => v x i) (Prod.snd '' s))
    (hs : s ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1) :
    ParabolicC0AlphaWith (∑ i, B i) (∑ i, (K i : ℝ)) α
      (fun z : ℝ × X => v z.2) s := by
  have hbase := vector_of_snd_lipschitzOnWith_with hB_nonneg hB hL
  exact hbase.mono_exponent_of_subset_closedBall
    (Finset.sum_nonneg fun i _hi => NNReal.coe_nonneg (K i))
    hα_nonneg hα_le_one hs hR

/-- On a subset of a closed parabolic cylinder of diameter at most one, entrywise spatial
Lipschitz control packages a finite vector-valued coefficient family as an explicit parabolic
`C^{0,α}` estimate for every `0 ≤ α ≤ 1`. -/
theorem vector_of_snd_lipschitzOnWith_with_of_subset_closedCylinder {n A : Type*}
    [Fintype n] [NormedAddCommGroup A] {B : n → ℝ} {K : n → ℝ≥0}
    {v : X → n → A} {timeRadius spaceRadius : ℝ} {c : ℝ × X}
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hB_nonneg : ∀ i, 0 ≤ B i)
    (hB : ∀ i ⦃x : X⦄, x ∈ Prod.snd '' s → ‖v x i‖ ≤ B i)
    (hL : ∀ i, LipschitzOnWith (K i) (fun x => v x i) (Prod.snd '' s))
    (hs : s ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1) :
    ParabolicC0AlphaWith (∑ i, B i) (∑ i, (K i : ℝ)) α
      (fun z : ℝ × X => v z.2) s := by
  have hbase := vector_of_snd_lipschitzOnWith_with hB_nonneg hB hL
  exact hbase.mono_exponent_of_subset_closedCylinder
    (Finset.sum_nonneg fun i _hi => NNReal.coe_nonneg (K i))
    hα_nonneg hα_le_one hs hdiam

/-- Entrywise spatial boundedness and Holder control package as a matrix-valued parabolic
`C^{0,α}` estimate for the time-independent lift. -/
theorem matrix_of_snd_holder_with {m n A : Type*} [Fintype m] [Fintype n]
    [NormedAddCommGroup A] {B H : m → n → ℝ} {M : X → Matrix m n A}
    (hB_nonneg : ∀ i j, 0 ≤ B i j) (hH_nonneg : ∀ i j, 0 ≤ H i j)
    (hα : 0 ≤ α)
    (hB : ∀ i j ⦃x : X⦄, x ∈ Prod.snd '' s → ‖M x i j‖ ≤ B i j)
    (hholder : ∀ i j ⦃x : X⦄, x ∈ Prod.snd '' s → ∀ ⦃y : X⦄,
      y ∈ Prod.snd '' s → ‖M x i j - M y i j‖ ≤ H i j * dist x y ^ α) :
    ParabolicC0AlphaWith (∑ i, ∑ j, B i j) (∑ i, ∑ j, H i j) α
      (fun z : ℝ × X => M z.2) s := by
  refine matrix_of_entries_with hB_nonneg hH_nonneg ?_
  intro i j
  exact ParabolicC0AlphaWith.of_snd_holder (s := s) (B := B i j) (H := H i j)
    (α := α) (f := fun x => M x i j) (hB i j) (hH_nonneg i j) hα
    (hholder i j)

/-- Entrywise spatial boundedness and Lipschitz control package as a matrix-valued
parabolic `C^{0,1}` estimate for the time-independent lift. -/
theorem matrix_of_snd_lipschitzOnWith_with {m n A : Type*} [Fintype m] [Fintype n]
    [NormedAddCommGroup A] {B : m → n → ℝ} {K : m → n → ℝ≥0}
    {M : X → Matrix m n A}
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hB : ∀ i j ⦃x : X⦄, x ∈ Prod.snd '' s → ‖M x i j‖ ≤ B i j)
    (hL : ∀ i j, LipschitzOnWith (K i j) (fun x => M x i j) (Prod.snd '' s)) :
    ParabolicC0AlphaWith (∑ i, ∑ j, B i j) (∑ i, ∑ j, (K i j : ℝ)) 1
      (fun z : ℝ × X => M z.2) s := by
  refine matrix_of_entries_with hB_nonneg (fun i j => NNReal.coe_nonneg (K i j)) ?_
  intro i j
  exact ParabolicC0AlphaWith.of_snd_lipschitzOnWith (s := s) (B := B i j) (K := K i j)
    (f := fun x => M x i j) (hB i j) (hL i j)

/-- On a unit parabolic-diameter domain, entrywise spatial Lipschitz control packages a
finite matrix-valued coefficient family as an explicit parabolic `C^{0,α}` estimate for
every `0 ≤ α ≤ 1`. -/
theorem matrix_of_snd_lipschitzOnWith_with_of_parabolicDistance_le_one {m n A : Type*}
    [Fintype m] [Fintype n] [NormedAddCommGroup A]
    {B : m → n → ℝ} {K : m → n → ℝ≥0}
    {M : X → Matrix m n A}
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hB : ∀ i j ⦃x : X⦄, x ∈ Prod.snd '' s → ‖M x i j‖ ≤ B i j)
    (hL : ∀ i j, LipschitzOnWith (K i j) (fun x => M x i j) (Prod.snd '' s))
    (hdiam : ∀ ⦃p : ℝ × X⦄, p ∈ s → ∀ ⦃q : ℝ × X⦄, q ∈ s →
      parabolicDistance p q ≤ 1) :
    ParabolicC0AlphaWith (∑ i, ∑ j, B i j) (∑ i, ∑ j, (K i j : ℝ)) α
      (fun z : ℝ × X => M z.2) s :=
  (matrix_of_snd_lipschitzOnWith_with hB_nonneg hB hL).mono_exponent_of_parabolicDistance_le_one
    (Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj => NNReal.coe_nonneg (K i j))
    hα_nonneg hα_le_one hdiam

/-- On a subset of a closed parabolic ball of diameter at most one, entrywise spatial Lipschitz
control packages a finite matrix-valued coefficient family as an explicit parabolic `C^{0,α}`
estimate for every `0 ≤ α ≤ 1`. -/
theorem matrix_of_snd_lipschitzOnWith_with_of_subset_closedBall {m n A : Type*}
    [Fintype m] [Fintype n] [NormedAddCommGroup A]
    {B : m → n → ℝ} {K : m → n → ℝ≥0}
    {M : X → Matrix m n A} {R : ℝ} {c : ℝ × X}
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hB : ∀ i j ⦃x : X⦄, x ∈ Prod.snd '' s → ‖M x i j‖ ≤ B i j)
    (hL : ∀ i j, LipschitzOnWith (K i j) (fun x => M x i j) (Prod.snd '' s))
    (hs : s ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1) :
    ParabolicC0AlphaWith (∑ i, ∑ j, B i j) (∑ i, ∑ j, (K i j : ℝ)) α
      (fun z : ℝ × X => M z.2) s := by
  have hbase := matrix_of_snd_lipschitzOnWith_with hB_nonneg hB hL
  exact hbase.mono_exponent_of_subset_closedBall
    (Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj => NNReal.coe_nonneg (K i j))
    hα_nonneg hα_le_one hs hR

/-- On a subset of a closed parabolic cylinder of diameter at most one, entrywise spatial
Lipschitz control packages a finite matrix-valued coefficient family as an explicit parabolic
`C^{0,α}` estimate for every `0 ≤ α ≤ 1`. -/
theorem matrix_of_snd_lipschitzOnWith_with_of_subset_closedCylinder {m n A : Type*}
    [Fintype m] [Fintype n] [NormedAddCommGroup A]
    {B : m → n → ℝ} {K : m → n → ℝ≥0}
    {M : X → Matrix m n A} {timeRadius spaceRadius : ℝ} {c : ℝ × X}
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hB : ∀ i j ⦃x : X⦄, x ∈ Prod.snd '' s → ‖M x i j‖ ≤ B i j)
    (hL : ∀ i j, LipschitzOnWith (K i j) (fun x => M x i j) (Prod.snd '' s))
    (hs : s ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1) :
    ParabolicC0AlphaWith (∑ i, ∑ j, B i j) (∑ i, ∑ j, (K i j : ℝ)) α
      (fun z : ℝ × X => M z.2) s := by
  have hbase := matrix_of_snd_lipschitzOnWith_with hB_nonneg hB hL
  exact hbase.mono_exponent_of_subset_closedCylinder
    (Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj => NNReal.coe_nonneg (K i j))
    hα_nonneg hα_le_one hs hdiam

/-- Entrywise spatial boundedness and Holder control package as existential vector-valued
parabolic `C^{0,α}` control for the time-independent lift. -/
theorem vector_of_snd_holder {n A : Type*} [Fintype n] [NormedAddCommGroup A]
    {B H : n → ℝ} {v : X → n → A}
    (hB_nonneg : ∀ i, 0 ≤ B i) (hH_nonneg : ∀ i, 0 ≤ H i) (hα : 0 ≤ α)
    (hB : ∀ i ⦃x : X⦄, x ∈ Prod.snd '' s → ‖v x i‖ ≤ B i)
    (hholder : ∀ i ⦃x : X⦄, x ∈ Prod.snd '' s → ∀ ⦃y : X⦄,
      y ∈ Prod.snd '' s → ‖v x i - v y i‖ ≤ H i * dist x y ^ α) :
    ParabolicC0AlphaOn α (fun z : ℝ × X => v z.2) s :=
  ⟨∑ i, B i, Finset.sum_nonneg fun i _hi => hB_nonneg i,
    ∑ i, H i, Finset.sum_nonneg fun i _hi => hH_nonneg i,
    vector_of_snd_holder_with hB_nonneg hH_nonneg hα hB hholder⟩

/-- Entrywise spatial boundedness and Lipschitz control package as existential vector-valued
parabolic `C^{0,1}` control for the time-independent lift. -/
theorem vector_of_snd_lipschitzOnWith {n A : Type*} [Fintype n]
    [NormedAddCommGroup A] {B : n → ℝ} {K : n → ℝ≥0} {v : X → n → A}
    (hB_nonneg : ∀ i, 0 ≤ B i)
    (hB : ∀ i ⦃x : X⦄, x ∈ Prod.snd '' s → ‖v x i‖ ≤ B i)
    (hL : ∀ i, LipschitzOnWith (K i) (fun x => v x i) (Prod.snd '' s)) :
    ParabolicC0AlphaOn 1 (fun z : ℝ × X => v z.2) s :=
  ⟨∑ i, B i, Finset.sum_nonneg fun i _hi => hB_nonneg i,
    ∑ i, (K i : ℝ), Finset.sum_nonneg fun i _hi => NNReal.coe_nonneg (K i),
    vector_of_snd_lipschitzOnWith_with hB_nonneg hB hL⟩

/-- On a unit parabolic-diameter domain, entrywise spatial Lipschitz control packages a
finite vector-valued coefficient family as parabolic `C^{0,α}` for every `0 ≤ α ≤ 1`. -/
theorem vector_of_snd_lipschitzOnWith_of_parabolicDistance_le_one {n A : Type*}
    [Fintype n] [NormedAddCommGroup A] {B : n → ℝ} {K : n → ℝ≥0}
    {v : X → n → A}
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hB_nonneg : ∀ i, 0 ≤ B i)
    (hB : ∀ i ⦃x : X⦄, x ∈ Prod.snd '' s → ‖v x i‖ ≤ B i)
    (hL : ∀ i, LipschitzOnWith (K i) (fun x => v x i) (Prod.snd '' s))
    (hdiam : ∀ ⦃p : ℝ × X⦄, p ∈ s → ∀ ⦃q : ℝ × X⦄, q ∈ s →
      parabolicDistance p q ≤ 1) :
    ParabolicC0AlphaOn α (fun z : ℝ × X => v z.2) s :=
  ⟨∑ i, B i, Finset.sum_nonneg fun i _hi => hB_nonneg i,
    ∑ i, (K i : ℝ), Finset.sum_nonneg fun i _hi => NNReal.coe_nonneg (K i),
    vector_of_snd_lipschitzOnWith_with_of_parabolicDistance_le_one
      hα_nonneg hα_le_one hB_nonneg hB hL hdiam⟩

/-- On a subset of a closed parabolic ball of diameter at most one, entrywise spatial Lipschitz
control packages a finite vector-valued coefficient family as parabolic `C^{0,α}` for every
`0 ≤ α ≤ 1`. -/
theorem vector_of_snd_lipschitzOnWith_of_subset_closedBall {n A : Type*}
    [Fintype n] [NormedAddCommGroup A] {B : n → ℝ} {K : n → ℝ≥0}
    {v : X → n → A} {R : ℝ} {c : ℝ × X}
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hB_nonneg : ∀ i, 0 ≤ B i)
    (hB : ∀ i ⦃x : X⦄, x ∈ Prod.snd '' s → ‖v x i‖ ≤ B i)
    (hL : ∀ i, LipschitzOnWith (K i) (fun x => v x i) (Prod.snd '' s))
    (hs : s ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1) :
    ParabolicC0AlphaOn α (fun z : ℝ × X => v z.2) s :=
  ⟨∑ i, B i, Finset.sum_nonneg fun i _hi => hB_nonneg i,
    ∑ i, (K i : ℝ), Finset.sum_nonneg fun i _hi => NNReal.coe_nonneg (K i),
    vector_of_snd_lipschitzOnWith_with_of_subset_closedBall
      hα_nonneg hα_le_one hB_nonneg hB hL hs hR⟩

/-- On a subset of a closed parabolic cylinder of diameter at most one, entrywise spatial
Lipschitz control packages a finite vector-valued coefficient family as parabolic `C^{0,α}` for
every `0 ≤ α ≤ 1`. -/
theorem vector_of_snd_lipschitzOnWith_of_subset_closedCylinder {n A : Type*}
    [Fintype n] [NormedAddCommGroup A] {B : n → ℝ} {K : n → ℝ≥0}
    {v : X → n → A} {timeRadius spaceRadius : ℝ} {c : ℝ × X}
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hB_nonneg : ∀ i, 0 ≤ B i)
    (hB : ∀ i ⦃x : X⦄, x ∈ Prod.snd '' s → ‖v x i‖ ≤ B i)
    (hL : ∀ i, LipschitzOnWith (K i) (fun x => v x i) (Prod.snd '' s))
    (hs : s ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1) :
    ParabolicC0AlphaOn α (fun z : ℝ × X => v z.2) s :=
  ⟨∑ i, B i, Finset.sum_nonneg fun i _hi => hB_nonneg i,
    ∑ i, (K i : ℝ), Finset.sum_nonneg fun i _hi => NNReal.coe_nonneg (K i),
    vector_of_snd_lipschitzOnWith_with_of_subset_closedCylinder
      hα_nonneg hα_le_one hB_nonneg hB hL hs hdiam⟩

/-- Entrywise spatial boundedness and Holder control package as existential matrix-valued
parabolic `C^{0,α}` control for the time-independent lift. -/
theorem matrix_of_snd_holder {m n A : Type*} [Fintype m] [Fintype n]
    [NormedAddCommGroup A] {B H : m → n → ℝ} {M : X → Matrix m n A}
    (hB_nonneg : ∀ i j, 0 ≤ B i j) (hH_nonneg : ∀ i j, 0 ≤ H i j)
    (hα : 0 ≤ α)
    (hB : ∀ i j ⦃x : X⦄, x ∈ Prod.snd '' s → ‖M x i j‖ ≤ B i j)
    (hholder : ∀ i j ⦃x : X⦄, x ∈ Prod.snd '' s → ∀ ⦃y : X⦄,
      y ∈ Prod.snd '' s → ‖M x i j - M y i j‖ ≤ H i j * dist x y ^ α) :
    ParabolicC0AlphaOn α (fun z : ℝ × X => M z.2) s :=
  ⟨∑ i, ∑ j, B i j, Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj => hB_nonneg i j,
    ∑ i, ∑ j, H i j, Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj => hH_nonneg i j,
    matrix_of_snd_holder_with hB_nonneg hH_nonneg hα hB hholder⟩

/-- Entrywise spatial boundedness and Lipschitz control package as existential matrix-valued
parabolic `C^{0,1}` control for the time-independent lift. -/
theorem matrix_of_snd_lipschitzOnWith {m n A : Type*} [Fintype m] [Fintype n]
    [NormedAddCommGroup A] {B : m → n → ℝ} {K : m → n → ℝ≥0}
    {M : X → Matrix m n A}
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hB : ∀ i j ⦃x : X⦄, x ∈ Prod.snd '' s → ‖M x i j‖ ≤ B i j)
    (hL : ∀ i j, LipschitzOnWith (K i j) (fun x => M x i j) (Prod.snd '' s)) :
    ParabolicC0AlphaOn 1 (fun z : ℝ × X => M z.2) s :=
  ⟨∑ i, ∑ j, B i j, Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj => hB_nonneg i j,
    ∑ i, ∑ j, (K i j : ℝ), Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj => NNReal.coe_nonneg (K i j),
    matrix_of_snd_lipschitzOnWith_with hB_nonneg hB hL⟩

/-- On a unit parabolic-diameter domain, entrywise spatial Lipschitz control packages a
finite matrix-valued coefficient family as parabolic `C^{0,α}` for every `0 ≤ α ≤ 1`. -/
theorem matrix_of_snd_lipschitzOnWith_of_parabolicDistance_le_one {m n A : Type*}
    [Fintype m] [Fintype n] [NormedAddCommGroup A]
    {B : m → n → ℝ} {K : m → n → ℝ≥0}
    {M : X → Matrix m n A}
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hB : ∀ i j ⦃x : X⦄, x ∈ Prod.snd '' s → ‖M x i j‖ ≤ B i j)
    (hL : ∀ i j, LipschitzOnWith (K i j) (fun x => M x i j) (Prod.snd '' s))
    (hdiam : ∀ ⦃p : ℝ × X⦄, p ∈ s → ∀ ⦃q : ℝ × X⦄, q ∈ s →
      parabolicDistance p q ≤ 1) :
    ParabolicC0AlphaOn α (fun z : ℝ × X => M z.2) s :=
  ⟨∑ i, ∑ j, B i j, Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj => hB_nonneg i j,
    ∑ i, ∑ j, (K i j : ℝ), Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj => NNReal.coe_nonneg (K i j),
    matrix_of_snd_lipschitzOnWith_with_of_parabolicDistance_le_one
      hα_nonneg hα_le_one hB_nonneg hB hL hdiam⟩

/-- On a subset of a closed parabolic ball of diameter at most one, entrywise spatial Lipschitz
control packages a finite matrix-valued coefficient family as parabolic `C^{0,α}` for every
`0 ≤ α ≤ 1`. -/
theorem matrix_of_snd_lipschitzOnWith_of_subset_closedBall {m n A : Type*}
    [Fintype m] [Fintype n] [NormedAddCommGroup A]
    {B : m → n → ℝ} {K : m → n → ℝ≥0}
    {M : X → Matrix m n A} {R : ℝ} {c : ℝ × X}
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hB : ∀ i j ⦃x : X⦄, x ∈ Prod.snd '' s → ‖M x i j‖ ≤ B i j)
    (hL : ∀ i j, LipschitzOnWith (K i j) (fun x => M x i j) (Prod.snd '' s))
    (hs : s ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1) :
    ParabolicC0AlphaOn α (fun z : ℝ × X => M z.2) s :=
  ⟨∑ i, ∑ j, B i j, Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj => hB_nonneg i j,
    ∑ i, ∑ j, (K i j : ℝ), Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj => NNReal.coe_nonneg (K i j),
    matrix_of_snd_lipschitzOnWith_with_of_subset_closedBall
      hα_nonneg hα_le_one hB_nonneg hB hL hs hR⟩

/-- On a subset of a closed parabolic cylinder of diameter at most one, entrywise spatial
Lipschitz control packages a finite matrix-valued coefficient family as parabolic `C^{0,α}` for
every `0 ≤ α ≤ 1`. -/
theorem matrix_of_snd_lipschitzOnWith_of_subset_closedCylinder {m n A : Type*}
    [Fintype m] [Fintype n] [NormedAddCommGroup A]
    {B : m → n → ℝ} {K : m → n → ℝ≥0}
    {M : X → Matrix m n A} {timeRadius spaceRadius : ℝ} {c : ℝ × X}
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hB : ∀ i j ⦃x : X⦄, x ∈ Prod.snd '' s → ‖M x i j‖ ≤ B i j)
    (hL : ∀ i j, LipschitzOnWith (K i j) (fun x => M x i j) (Prod.snd '' s))
    (hs : s ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1) :
    ParabolicC0AlphaOn α (fun z : ℝ × X => M z.2) s :=
  ⟨∑ i, ∑ j, B i j, Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj => hB_nonneg i j,
    ∑ i, ∑ j, (K i j : ℝ), Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj => NNReal.coe_nonneg (K i j),
    matrix_of_snd_lipschitzOnWith_with_of_subset_closedCylinder
      hα_nonneg hα_le_one hB_nonneg hB hL hs hdiam⟩

/-- Entrywise time-only boundedness and Holder control package as a vector-valued parabolic
`C^{0,α}` estimate.  The time Holder exponent is `α / 2`, matching parabolic scaling. -/
theorem vector_of_fst_holder_with {n A : Type*} [Fintype n] [NormedAddCommGroup A]
    {B H : n → ℝ} {v : ℝ → n → A}
    (hB_nonneg : ∀ i, 0 ≤ B i) (hH_nonneg : ∀ i, 0 ≤ H i) (hα : 0 ≤ α)
    (hB : ∀ i ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ‖v t i‖ ≤ B i)
    (hholder : ∀ i ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ∀ ⦃τ : ℝ⦄,
      τ ∈ Prod.fst '' s → ‖v t i - v τ i‖ ≤ H i * |t - τ| ^ (α / 2)) :
    ParabolicC0AlphaWith (∑ i, B i) (∑ i, H i) α
      (fun z : ℝ × X => v z.1) s := by
  refine vector_of_entries_with hB_nonneg hH_nonneg ?_
  intro i
  exact ParabolicC0AlphaWith.of_fst_holder (s := s) (B := B i) (H := H i)
    (α := α) (f := fun t => v t i) (hB i) (hH_nonneg i) hα (hholder i)

/-- Entrywise time-only boundedness and Lipschitz control package as a vector-valued parabolic
`C^{0,2}` estimate. -/
theorem vector_of_fst_lipschitzOnWith_with {n A : Type*} [Fintype n] [NormedAddCommGroup A]
    {B : n → ℝ} {K : n → ℝ≥0} {v : ℝ → n → A}
    (hB_nonneg : ∀ i, 0 ≤ B i)
    (hB : ∀ i ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ‖v t i‖ ≤ B i)
    (hL : ∀ i, LipschitzOnWith (K i) (fun t => v t i) (Prod.fst '' s)) :
    ParabolicC0AlphaWith (∑ i, B i) (∑ i, (K i : ℝ)) 2
      (fun z : ℝ × X => v z.1) s := by
  refine vector_of_entries_with hB_nonneg (fun i => NNReal.coe_nonneg (K i)) ?_
  intro i
  exact ParabolicC0AlphaWith.of_fst_lipschitzOnWith (s := s) (B := B i) (K := K i)
    (f := fun t => v t i) (hB i) (hL i)

/-- Entrywise time-only boundedness and Holder control package as a matrix-valued parabolic
`C^{0,α}` estimate.  The time Holder exponent is `α / 2`, matching parabolic scaling. -/
theorem matrix_of_fst_holder_with {m n A : Type*} [Fintype m] [Fintype n]
    [NormedAddCommGroup A] {B H : m → n → ℝ} {M : ℝ → Matrix m n A}
    (hB_nonneg : ∀ i j, 0 ≤ B i j) (hH_nonneg : ∀ i j, 0 ≤ H i j)
    (hα : 0 ≤ α)
    (hB : ∀ i j ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ‖M t i j‖ ≤ B i j)
    (hholder : ∀ i j ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ∀ ⦃τ : ℝ⦄,
      τ ∈ Prod.fst '' s → ‖M t i j - M τ i j‖ ≤ H i j * |t - τ| ^ (α / 2)) :
    ParabolicC0AlphaWith (∑ i, ∑ j, B i j) (∑ i, ∑ j, H i j) α
      (fun z : ℝ × X => M z.1) s := by
  refine matrix_of_entries_with hB_nonneg hH_nonneg ?_
  intro i j
  exact ParabolicC0AlphaWith.of_fst_holder (s := s) (B := B i j) (H := H i j)
    (α := α) (f := fun t => M t i j) (hB i j) (hH_nonneg i j) hα (hholder i j)

/-- Entrywise time-only boundedness and Lipschitz control package as a matrix-valued parabolic
`C^{0,2}` estimate. -/
theorem matrix_of_fst_lipschitzOnWith_with {m n A : Type*} [Fintype m] [Fintype n]
    [NormedAddCommGroup A] {B : m → n → ℝ} {K : m → n → ℝ≥0}
    {M : ℝ → Matrix m n A}
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hB : ∀ i j ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ‖M t i j‖ ≤ B i j)
    (hL : ∀ i j, LipschitzOnWith (K i j) (fun t => M t i j) (Prod.fst '' s)) :
    ParabolicC0AlphaWith (∑ i, ∑ j, B i j) (∑ i, ∑ j, (K i j : ℝ)) 2
      (fun z : ℝ × X => M z.1) s := by
  refine matrix_of_entries_with hB_nonneg (fun i j => NNReal.coe_nonneg (K i j)) ?_
  intro i j
  exact ParabolicC0AlphaWith.of_fst_lipschitzOnWith (s := s) (B := B i j) (K := K i j)
    (f := fun t => M t i j) (hB i j) (hL i j)

/-- On a unit parabolic-diameter domain, entrywise time-only Lipschitz control packages a
finite vector-valued coefficient family as an explicit parabolic `C^{0,α}` estimate for
every `0 ≤ α ≤ 2`. -/
theorem vector_of_fst_lipschitzOnWith_with_of_parabolicDistance_le_one {n A : Type*}
    [Fintype n] [NormedAddCommGroup A] {B : n → ℝ} {K : n → ℝ≥0}
    {v : ℝ → n → A}
    (hα_nonneg : 0 ≤ α) (hα_le_two : α ≤ 2)
    (hB_nonneg : ∀ i, 0 ≤ B i)
    (hB : ∀ i ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ‖v t i‖ ≤ B i)
    (hL : ∀ i, LipschitzOnWith (K i) (fun t => v t i) (Prod.fst '' s))
    (hdiam : ∀ ⦃p : ℝ × X⦄, p ∈ s → ∀ ⦃q : ℝ × X⦄, q ∈ s →
      parabolicDistance p q ≤ 1) :
    ParabolicC0AlphaWith (∑ i, B i) (∑ i, (K i : ℝ)) α
      (fun z : ℝ × X => v z.1) s :=
  (vector_of_fst_lipschitzOnWith_with hB_nonneg hB hL).mono_exponent_of_parabolicDistance_le_one
    (Finset.sum_nonneg fun i _hi => NNReal.coe_nonneg (K i))
    hα_nonneg hα_le_two hdiam

/-- On a unit parabolic-diameter domain, entrywise time-only Lipschitz control packages a
finite matrix-valued coefficient family as an explicit parabolic `C^{0,α}` estimate for
every `0 ≤ α ≤ 2`. -/
theorem matrix_of_fst_lipschitzOnWith_with_of_parabolicDistance_le_one {m n A : Type*}
    [Fintype m] [Fintype n] [NormedAddCommGroup A]
    {B : m → n → ℝ} {K : m → n → ℝ≥0}
    {M : ℝ → Matrix m n A}
    (hα_nonneg : 0 ≤ α) (hα_le_two : α ≤ 2)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hB : ∀ i j ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ‖M t i j‖ ≤ B i j)
    (hL : ∀ i j, LipschitzOnWith (K i j) (fun t => M t i j) (Prod.fst '' s))
    (hdiam : ∀ ⦃p : ℝ × X⦄, p ∈ s → ∀ ⦃q : ℝ × X⦄, q ∈ s →
      parabolicDistance p q ≤ 1) :
    ParabolicC0AlphaWith (∑ i, ∑ j, B i j) (∑ i, ∑ j, (K i j : ℝ)) α
      (fun z : ℝ × X => M z.1) s :=
  (matrix_of_fst_lipschitzOnWith_with hB_nonneg hB hL).mono_exponent_of_parabolicDistance_le_one
    (Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj => NNReal.coe_nonneg (K i j))
    hα_nonneg hα_le_two hdiam

/-- On a subset of a closed parabolic ball of diameter at most one, entrywise time-only Lipschitz
control packages a finite vector-valued coefficient family as an explicit parabolic `C^{0,α}`
estimate for every `0 ≤ α ≤ 2`. -/
theorem vector_of_fst_lipschitzOnWith_with_of_subset_closedBall {n A : Type*}
    [Fintype n] [NormedAddCommGroup A] {B : n → ℝ} {K : n → ℝ≥0}
    {v : ℝ → n → A} {R : ℝ} {c : ℝ × X}
    (hα_nonneg : 0 ≤ α) (hα_le_two : α ≤ 2)
    (hB_nonneg : ∀ i, 0 ≤ B i)
    (hB : ∀ i ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ‖v t i‖ ≤ B i)
    (hL : ∀ i, LipschitzOnWith (K i) (fun t => v t i) (Prod.fst '' s))
    (hs : s ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1) :
    ParabolicC0AlphaWith (∑ i, B i) (∑ i, (K i : ℝ)) α
      (fun z : ℝ × X => v z.1) s := by
  have hbase := vector_of_fst_lipschitzOnWith_with hB_nonneg hB hL
  exact hbase.mono_exponent_of_subset_closedBall
    (Finset.sum_nonneg fun i _hi => NNReal.coe_nonneg (K i))
    hα_nonneg hα_le_two hs hR

/-- On a subset of a closed parabolic cylinder of diameter at most one, entrywise time-only
Lipschitz control packages a finite vector-valued coefficient family as an explicit parabolic
`C^{0,α}` estimate for every `0 ≤ α ≤ 2`. -/
theorem vector_of_fst_lipschitzOnWith_with_of_subset_closedCylinder {n A : Type*}
    [Fintype n] [NormedAddCommGroup A] {B : n → ℝ} {K : n → ℝ≥0}
    {v : ℝ → n → A} {timeRadius spaceRadius : ℝ} {c : ℝ × X}
    (hα_nonneg : 0 ≤ α) (hα_le_two : α ≤ 2)
    (hB_nonneg : ∀ i, 0 ≤ B i)
    (hB : ∀ i ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ‖v t i‖ ≤ B i)
    (hL : ∀ i, LipschitzOnWith (K i) (fun t => v t i) (Prod.fst '' s))
    (hs : s ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1) :
    ParabolicC0AlphaWith (∑ i, B i) (∑ i, (K i : ℝ)) α
      (fun z : ℝ × X => v z.1) s := by
  have hbase := vector_of_fst_lipschitzOnWith_with hB_nonneg hB hL
  exact hbase.mono_exponent_of_subset_closedCylinder
    (Finset.sum_nonneg fun i _hi => NNReal.coe_nonneg (K i))
    hα_nonneg hα_le_two hs hdiam

/-- On a subset of a closed parabolic ball of diameter at most one, entrywise time-only Lipschitz
control packages a finite matrix-valued coefficient family as an explicit parabolic `C^{0,α}`
estimate for every `0 ≤ α ≤ 2`. -/
theorem matrix_of_fst_lipschitzOnWith_with_of_subset_closedBall {m n A : Type*}
    [Fintype m] [Fintype n] [NormedAddCommGroup A]
    {B : m → n → ℝ} {K : m → n → ℝ≥0}
    {M : ℝ → Matrix m n A} {R : ℝ} {c : ℝ × X}
    (hα_nonneg : 0 ≤ α) (hα_le_two : α ≤ 2)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hB : ∀ i j ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ‖M t i j‖ ≤ B i j)
    (hL : ∀ i j, LipschitzOnWith (K i j) (fun t => M t i j) (Prod.fst '' s))
    (hs : s ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1) :
    ParabolicC0AlphaWith (∑ i, ∑ j, B i j) (∑ i, ∑ j, (K i j : ℝ)) α
      (fun z : ℝ × X => M z.1) s := by
  have hbase := matrix_of_fst_lipschitzOnWith_with hB_nonneg hB hL
  exact hbase.mono_exponent_of_subset_closedBall
    (Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj => NNReal.coe_nonneg (K i j))
    hα_nonneg hα_le_two hs hR

/-- On a subset of a closed parabolic cylinder of diameter at most one, entrywise time-only
Lipschitz control packages a finite matrix-valued coefficient family as an explicit parabolic
`C^{0,α}` estimate for every `0 ≤ α ≤ 2`. -/
theorem matrix_of_fst_lipschitzOnWith_with_of_subset_closedCylinder {m n A : Type*}
    [Fintype m] [Fintype n] [NormedAddCommGroup A]
    {B : m → n → ℝ} {K : m → n → ℝ≥0}
    {M : ℝ → Matrix m n A} {timeRadius spaceRadius : ℝ} {c : ℝ × X}
    (hα_nonneg : 0 ≤ α) (hα_le_two : α ≤ 2)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hB : ∀ i j ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ‖M t i j‖ ≤ B i j)
    (hL : ∀ i j, LipschitzOnWith (K i j) (fun t => M t i j) (Prod.fst '' s))
    (hs : s ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1) :
    ParabolicC0AlphaWith (∑ i, ∑ j, B i j) (∑ i, ∑ j, (K i j : ℝ)) α
      (fun z : ℝ × X => M z.1) s := by
  have hbase := matrix_of_fst_lipschitzOnWith_with hB_nonneg hB hL
  exact hbase.mono_exponent_of_subset_closedCylinder
    (Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj => NNReal.coe_nonneg (K i j))
    hα_nonneg hα_le_two hs hdiam

/-- Entrywise time-only boundedness and Holder control package as existential vector-valued
parabolic `C^{0,α}` control. -/
theorem vector_of_fst_holder {n A : Type*} [Fintype n] [NormedAddCommGroup A]
    {B H : n → ℝ} {v : ℝ → n → A}
    (hB_nonneg : ∀ i, 0 ≤ B i) (hH_nonneg : ∀ i, 0 ≤ H i) (hα : 0 ≤ α)
    (hB : ∀ i ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ‖v t i‖ ≤ B i)
    (hholder : ∀ i ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ∀ ⦃τ : ℝ⦄,
      τ ∈ Prod.fst '' s → ‖v t i - v τ i‖ ≤ H i * |t - τ| ^ (α / 2)) :
    ParabolicC0AlphaOn α (fun z : ℝ × X => v z.1) s :=
  ⟨∑ i, B i, Finset.sum_nonneg fun i _hi => hB_nonneg i,
    ∑ i, H i, Finset.sum_nonneg fun i _hi => hH_nonneg i,
    vector_of_fst_holder_with hB_nonneg hH_nonneg hα hB hholder⟩

/-- Entrywise time-only boundedness and Lipschitz control package as existential vector-valued
parabolic `C^{0,2}` control. -/
theorem vector_of_fst_lipschitzOnWith {n A : Type*} [Fintype n] [NormedAddCommGroup A]
    {B : n → ℝ} {K : n → ℝ≥0} {v : ℝ → n → A}
    (hB_nonneg : ∀ i, 0 ≤ B i)
    (hB : ∀ i ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ‖v t i‖ ≤ B i)
    (hL : ∀ i, LipschitzOnWith (K i) (fun t => v t i) (Prod.fst '' s)) :
    ParabolicC0AlphaOn 2 (fun z : ℝ × X => v z.1) s :=
  ⟨∑ i, B i, Finset.sum_nonneg fun i _hi => hB_nonneg i,
    ∑ i, (K i : ℝ), Finset.sum_nonneg fun i _hi => NNReal.coe_nonneg (K i),
    vector_of_fst_lipschitzOnWith_with hB_nonneg hB hL⟩

/-- Entrywise time-only boundedness and Holder control package as existential matrix-valued
parabolic `C^{0,α}` control. -/
theorem matrix_of_fst_holder {m n A : Type*} [Fintype m] [Fintype n]
    [NormedAddCommGroup A] {B H : m → n → ℝ} {M : ℝ → Matrix m n A}
    (hB_nonneg : ∀ i j, 0 ≤ B i j) (hH_nonneg : ∀ i j, 0 ≤ H i j)
    (hα : 0 ≤ α)
    (hB : ∀ i j ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ‖M t i j‖ ≤ B i j)
    (hholder : ∀ i j ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ∀ ⦃τ : ℝ⦄,
      τ ∈ Prod.fst '' s → ‖M t i j - M τ i j‖ ≤ H i j * |t - τ| ^ (α / 2)) :
    ParabolicC0AlphaOn α (fun z : ℝ × X => M z.1) s :=
  ⟨∑ i, ∑ j, B i j, Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj => hB_nonneg i j,
    ∑ i, ∑ j, H i j, Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj => hH_nonneg i j,
    matrix_of_fst_holder_with hB_nonneg hH_nonneg hα hB hholder⟩

/-- Entrywise time-only boundedness and Lipschitz control package as existential matrix-valued
parabolic `C^{0,2}` control. -/
theorem matrix_of_fst_lipschitzOnWith {m n A : Type*} [Fintype m] [Fintype n]
    [NormedAddCommGroup A] {B : m → n → ℝ} {K : m → n → ℝ≥0}
    {M : ℝ → Matrix m n A}
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hB : ∀ i j ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ‖M t i j‖ ≤ B i j)
    (hL : ∀ i j, LipschitzOnWith (K i j) (fun t => M t i j) (Prod.fst '' s)) :
    ParabolicC0AlphaOn 2 (fun z : ℝ × X => M z.1) s :=
  ⟨∑ i, ∑ j, B i j, Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj => hB_nonneg i j,
    ∑ i, ∑ j, (K i j : ℝ), Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj => NNReal.coe_nonneg (K i j),
    matrix_of_fst_lipschitzOnWith_with hB_nonneg hB hL⟩

/-- On a unit parabolic-diameter domain, entrywise time-only Lipschitz control packages a
finite vector-valued coefficient family as parabolic `C^{0,α}` for every `0 ≤ α ≤ 2`. -/
theorem vector_of_fst_lipschitzOnWith_of_parabolicDistance_le_one {n A : Type*}
    [Fintype n] [NormedAddCommGroup A] {B : n → ℝ} {K : n → ℝ≥0}
    {v : ℝ → n → A}
    (hα_nonneg : 0 ≤ α) (hα_le_two : α ≤ 2)
    (hB_nonneg : ∀ i, 0 ≤ B i)
    (hB : ∀ i ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ‖v t i‖ ≤ B i)
    (hL : ∀ i, LipschitzOnWith (K i) (fun t => v t i) (Prod.fst '' s))
    (hdiam : ∀ ⦃p : ℝ × X⦄, p ∈ s → ∀ ⦃q : ℝ × X⦄, q ∈ s →
      parabolicDistance p q ≤ 1) :
    ParabolicC0AlphaOn α (fun z : ℝ × X => v z.1) s :=
  ⟨∑ i, B i, Finset.sum_nonneg fun i _hi => hB_nonneg i,
    ∑ i, (K i : ℝ), Finset.sum_nonneg fun i _hi => NNReal.coe_nonneg (K i),
    vector_of_fst_lipschitzOnWith_with_of_parabolicDistance_le_one
      hα_nonneg hα_le_two hB_nonneg hB hL hdiam⟩

/-- On a subset of a closed parabolic ball of diameter at most one, entrywise time-only Lipschitz
control packages a finite vector-valued coefficient family as parabolic `C^{0,α}` for every
`0 ≤ α ≤ 2`. -/
theorem vector_of_fst_lipschitzOnWith_of_subset_closedBall {n A : Type*}
    [Fintype n] [NormedAddCommGroup A] {B : n → ℝ} {K : n → ℝ≥0}
    {v : ℝ → n → A} {R : ℝ} {c : ℝ × X}
    (hα_nonneg : 0 ≤ α) (hα_le_two : α ≤ 2)
    (hB_nonneg : ∀ i, 0 ≤ B i)
    (hB : ∀ i ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ‖v t i‖ ≤ B i)
    (hL : ∀ i, LipschitzOnWith (K i) (fun t => v t i) (Prod.fst '' s))
    (hs : s ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1) :
    ParabolicC0AlphaOn α (fun z : ℝ × X => v z.1) s :=
  ⟨∑ i, B i, Finset.sum_nonneg fun i _hi => hB_nonneg i,
    ∑ i, (K i : ℝ), Finset.sum_nonneg fun i _hi => NNReal.coe_nonneg (K i),
    vector_of_fst_lipschitzOnWith_with_of_subset_closedBall
      hα_nonneg hα_le_two hB_nonneg hB hL hs hR⟩

/-- On a subset of a closed parabolic cylinder of diameter at most one, entrywise time-only
Lipschitz control packages a finite vector-valued coefficient family as parabolic `C^{0,α}` for
every `0 ≤ α ≤ 2`. -/
theorem vector_of_fst_lipschitzOnWith_of_subset_closedCylinder {n A : Type*}
    [Fintype n] [NormedAddCommGroup A] {B : n → ℝ} {K : n → ℝ≥0}
    {v : ℝ → n → A} {timeRadius spaceRadius : ℝ} {c : ℝ × X}
    (hα_nonneg : 0 ≤ α) (hα_le_two : α ≤ 2)
    (hB_nonneg : ∀ i, 0 ≤ B i)
    (hB : ∀ i ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ‖v t i‖ ≤ B i)
    (hL : ∀ i, LipschitzOnWith (K i) (fun t => v t i) (Prod.fst '' s))
    (hs : s ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1) :
    ParabolicC0AlphaOn α (fun z : ℝ × X => v z.1) s :=
  ⟨∑ i, B i, Finset.sum_nonneg fun i _hi => hB_nonneg i,
    ∑ i, (K i : ℝ), Finset.sum_nonneg fun i _hi => NNReal.coe_nonneg (K i),
    vector_of_fst_lipschitzOnWith_with_of_subset_closedCylinder
      hα_nonneg hα_le_two hB_nonneg hB hL hs hdiam⟩

/-- On a unit parabolic-diameter domain, entrywise time-only Lipschitz control packages a
finite matrix-valued coefficient family as parabolic `C^{0,α}` for every `0 ≤ α ≤ 2`. -/
theorem matrix_of_fst_lipschitzOnWith_of_parabolicDistance_le_one {m n A : Type*}
    [Fintype m] [Fintype n] [NormedAddCommGroup A]
    {B : m → n → ℝ} {K : m → n → ℝ≥0}
    {M : ℝ → Matrix m n A}
    (hα_nonneg : 0 ≤ α) (hα_le_two : α ≤ 2)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hB : ∀ i j ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ‖M t i j‖ ≤ B i j)
    (hL : ∀ i j, LipschitzOnWith (K i j) (fun t => M t i j) (Prod.fst '' s))
    (hdiam : ∀ ⦃p : ℝ × X⦄, p ∈ s → ∀ ⦃q : ℝ × X⦄, q ∈ s →
      parabolicDistance p q ≤ 1) :
    ParabolicC0AlphaOn α (fun z : ℝ × X => M z.1) s :=
  ⟨∑ i, ∑ j, B i j, Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj => hB_nonneg i j,
    ∑ i, ∑ j, (K i j : ℝ), Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj => NNReal.coe_nonneg (K i j),
    matrix_of_fst_lipschitzOnWith_with_of_parabolicDistance_le_one
      hα_nonneg hα_le_two hB_nonneg hB hL hdiam⟩

/-- On a subset of a closed parabolic ball of diameter at most one, entrywise time-only Lipschitz
control packages a finite matrix-valued coefficient family as parabolic `C^{0,α}` for every
`0 ≤ α ≤ 2`. -/
theorem matrix_of_fst_lipschitzOnWith_of_subset_closedBall {m n A : Type*}
    [Fintype m] [Fintype n] [NormedAddCommGroup A]
    {B : m → n → ℝ} {K : m → n → ℝ≥0}
    {M : ℝ → Matrix m n A} {R : ℝ} {c : ℝ × X}
    (hα_nonneg : 0 ≤ α) (hα_le_two : α ≤ 2)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hB : ∀ i j ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ‖M t i j‖ ≤ B i j)
    (hL : ∀ i j, LipschitzOnWith (K i j) (fun t => M t i j) (Prod.fst '' s))
    (hs : s ⊆ parabolicClosedBall c R) (hR : 2 * R ≤ 1) :
    ParabolicC0AlphaOn α (fun z : ℝ × X => M z.1) s :=
  ⟨∑ i, ∑ j, B i j, Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj => hB_nonneg i j,
    ∑ i, ∑ j, (K i j : ℝ), Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj => NNReal.coe_nonneg (K i j),
    matrix_of_fst_lipschitzOnWith_with_of_subset_closedBall
      hα_nonneg hα_le_two hB_nonneg hB hL hs hR⟩

/-- On a subset of a closed parabolic cylinder of diameter at most one, entrywise time-only
Lipschitz control packages a finite matrix-valued coefficient family as parabolic `C^{0,α}` for
every `0 ≤ α ≤ 2`. -/
theorem matrix_of_fst_lipschitzOnWith_of_subset_closedCylinder {m n A : Type*}
    [Fintype m] [Fintype n] [NormedAddCommGroup A]
    {B : m → n → ℝ} {K : m → n → ℝ≥0}
    {M : ℝ → Matrix m n A} {timeRadius spaceRadius : ℝ} {c : ℝ × X}
    (hα_nonneg : 0 ≤ α) (hα_le_two : α ≤ 2)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hB : ∀ i j ⦃t : ℝ⦄, t ∈ Prod.fst '' s → ‖M t i j‖ ≤ B i j)
    (hL : ∀ i j, LipschitzOnWith (K i j) (fun t => M t i j) (Prod.fst '' s))
    (hs : s ⊆ parabolicClosedCylinder c timeRadius spaceRadius)
    (hdiam : max (Real.sqrt (2 * timeRadius)) (2 * spaceRadius) ≤ 1) :
    ParabolicC0AlphaOn α (fun z : ℝ × X => M z.1) s :=
  ⟨∑ i, ∑ j, B i j, Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj => hB_nonneg i j,
    ∑ i, ∑ j, (K i j : ℝ), Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj => NNReal.coe_nonneg (K i j),
    matrix_of_fst_lipschitzOnWith_with_of_subset_closedCylinder
      hα_nonneg hα_le_two hB_nonneg hB hL hs hdiam⟩

/-- Entrywise parabolic `C^{0,α}` control packages a finite vector-valued coefficient family. -/
theorem vector_of_entries {n A : Type*} [Fintype n] [NormedAddCommGroup A]
    {v : ℝ × X → n → A}
    (hv : ∀ i, ParabolicC0AlphaOn α (fun z => v z i) s) :
    ParabolicC0AlphaOn α v s :=
  ParabolicC0AlphaOn.pi hv

/-- Entrywise difference control packages a finite vector-valued difference. -/
theorem vector_of_entries_sub {n A : Type*} [Fintype n] [NormedAddCommGroup A]
    {v w : ℝ × X → n → A}
    (hdiff : ∀ i, ParabolicC0AlphaOn α (fun z => v z i - w z i) s) :
    ParabolicC0AlphaOn α (fun z => v z - w z) s :=
  vector_of_entries hdiff

/-- Entrywise parabolic `C^{0,α}` control packages a finite matrix-valued coefficient family. -/
theorem matrix_of_entries {m n A : Type*} [Fintype m] [Fintype n] [NormedAddCommGroup A]
    {M : ℝ × X → Matrix m n A}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s) :
    ParabolicC0AlphaOn α M s :=
  ParabolicC0AlphaOn.pi fun i => ParabolicC0AlphaOn.pi fun j => hM i j

/-- Entrywise difference control packages a finite matrix-valued difference. -/
theorem matrix_of_entries_sub {m n A : Type*} [Fintype m] [Fintype n]
    [NormedAddCommGroup A] {M N : ℝ × X → Matrix m n A}
    (hdiff : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j - N z i j) s) :
    ParabolicC0AlphaOn α (fun z => M z - N z) s :=
  matrix_of_entries hdiff

/-- Transposes of finite matrix-valued parabolic `C^{0,α}` functions are parabolic `C^{0,α}`
from entrywise control. -/
theorem matrix_transpose {m n A : Type*} [Fintype m] [Fintype n] [NormedAddCommGroup A]
    {M : ℝ × X → Matrix m n A}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s) :
    ParabolicC0AlphaOn α (fun z => (M z).transpose) s :=
  matrix_of_entries fun i j => hM j i

/-- Transpose differences preserve existential parabolic `C^{0,α}` control from entrywise
difference control. -/
theorem matrix_transpose_sub {m n A : Type*} [Fintype m] [Fintype n]
    [NormedAddCommGroup A] {M N : ℝ × X → Matrix m n A}
    (hdiff : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j - N z i j) s) :
    ParabolicC0AlphaOn α (fun z => (M z).transpose - (N z).transpose) s :=
  matrix_of_entries fun i j => by
    simpa using hdiff j i

/-- Quantitative sup constant for one entry of a finite matrix transpose. -/
def matrixTransposeEntryBoundConst {m n : Type*} (B : m → n → ℝ) (i : n) (j : m) :
    ℝ :=
  B j i

/-- Quantitative Holder constant for one entry of a finite matrix transpose. -/
def matrixTransposeEntryHolderConst {m n : Type*} (H : m → n → ℝ) (i : n) (j : m) :
    ℝ :=
  H j i

theorem matrixTransposeEntryBoundConst_nonneg {m n : Type*} {B : m → n → ℝ}
    (hB : ∀ i j, 0 ≤ B i j) (i : n) (j : m) :
    0 ≤ matrixTransposeEntryBoundConst B i j :=
  hB j i

theorem matrixTransposeEntryHolderConst_nonneg {m n : Type*} {H : m → n → ℝ}
    (hH : ∀ i j, 0 ≤ H i j) (i : n) (j : m) :
    0 ≤ matrixTransposeEntryHolderConst H i j :=
  hH j i

/-- One entry of a finite matrix transpose has an explicit bounded parabolic `C^{0,α}`
estimate. -/
theorem matrix_transpose_entry_with {m n A : Type*} [NormedAddCommGroup A]
    {B H : m → n → ℝ} {M : ℝ × X → Matrix m n A}
    (hM : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => M z i j) s)
    (i : n) (j : m) :
    ParabolicC0AlphaWith
      (matrixTransposeEntryBoundConst B i j)
      (matrixTransposeEntryHolderConst H i j)
      α (fun z => (M z).transpose i j) s := by
  simpa [matrixTransposeEntryBoundConst, matrixTransposeEntryHolderConst] using hM j i

/-- Quantitative sup constant for a finite matrix transpose. -/
def matrixTransposeBoundConst {m n : Type*} [Fintype m] [Fintype n] (B : m → n → ℝ) :
    ℝ :=
  ∑ i : n, ∑ j : m, matrixTransposeEntryBoundConst B i j

/-- Quantitative Holder constant for a finite matrix transpose. -/
def matrixTransposeHolderConst {m n : Type*} [Fintype m] [Fintype n] (H : m → n → ℝ) :
    ℝ :=
  ∑ i : n, ∑ j : m, matrixTransposeEntryHolderConst H i j

theorem matrixTransposeBoundConst_nonneg {m n : Type*} [Fintype m] [Fintype n]
    {B : m → n → ℝ} (hB : ∀ i j, 0 ≤ B i j) :
    0 ≤ matrixTransposeBoundConst B := by
  simpa [matrixTransposeBoundConst] using
    (Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj => matrixTransposeEntryBoundConst_nonneg hB i j)

theorem matrixTransposeHolderConst_nonneg {m n : Type*} [Fintype m] [Fintype n]
    {H : m → n → ℝ} (hH : ∀ i j, 0 ≤ H i j) :
    0 ≤ matrixTransposeHolderConst H := by
  simpa [matrixTransposeHolderConst] using
    (Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj => matrixTransposeEntryHolderConst_nonneg hH i j)

/-- Finite matrix transposes have an explicit matrix-valued bounded parabolic `C^{0,α}`
estimate. -/
theorem matrix_transpose_with {m n A : Type*} [Fintype m] [Fintype n]
    [NormedAddCommGroup A] {B H : m → n → ℝ} {M : ℝ × X → Matrix m n A}
    (hB : ∀ i j, 0 ≤ B i j) (hH : ∀ i j, 0 ≤ H i j)
    (hM : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => M z i j) s) :
    ParabolicC0AlphaWith
      (matrixTransposeBoundConst B) (matrixTransposeHolderConst H)
      α (fun z => (M z).transpose) s := by
  simp only [matrixTransposeBoundConst, matrixTransposeHolderConst]
  refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
  · intro i
    exact Finset.sum_nonneg fun j _hj => matrixTransposeEntryBoundConst_nonneg hB i j
  · intro i
    exact Finset.sum_nonneg fun j _hj => matrixTransposeEntryHolderConst_nonneg hH i j
  · intro i
    refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
    · intro j
      exact matrixTransposeEntryBoundConst_nonneg hB i j
    · intro j
      exact matrixTransposeEntryHolderConst_nonneg hH i j
    · intro j
      exact matrix_transpose_entry_with hM i j

/-- Quantitative sup constant for one entry of a finite matrix transpose difference. -/
def matrixTransposeEntrySubBoundConst {m n : Type*} (B : m → n → ℝ) (i : n) (j : m) :
    ℝ :=
  matrixTransposeEntryBoundConst B i j

/-- Quantitative Holder constant for one entry of a finite matrix transpose difference. -/
def matrixTransposeEntrySubHolderConst {m n : Type*} (H : m → n → ℝ) (i : n) (j : m) :
    ℝ :=
  matrixTransposeEntryHolderConst H i j

theorem matrixTransposeEntrySubBoundConst_nonneg {m n : Type*} {B : m → n → ℝ}
    (hB : ∀ i j, 0 ≤ B i j) (i : n) (j : m) :
    0 ≤ matrixTransposeEntrySubBoundConst B i j :=
  matrixTransposeEntryBoundConst_nonneg hB i j

theorem matrixTransposeEntrySubHolderConst_nonneg {m n : Type*} {H : m → n → ℝ}
    (hH : ∀ i j, 0 ≤ H i j) (i : n) (j : m) :
    0 ≤ matrixTransposeEntrySubHolderConst H i j :=
  matrixTransposeEntryHolderConst_nonneg hH i j

/-- One entry of a finite matrix transpose difference has an explicit bounded parabolic
`C^{0,α}` estimate. -/
theorem matrix_transpose_entry_sub_with {m n A : Type*} [NormedAddCommGroup A]
    {B H : m → n → ℝ} {M M' : ℝ × X → Matrix m n A}
    (hMd : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α
      (fun z => M z i j - M' z i j) s)
    (i : n) (j : m) :
    ParabolicC0AlphaWith
      (matrixTransposeEntrySubBoundConst B i j)
      (matrixTransposeEntrySubHolderConst H i j)
      α (fun z => (M z).transpose i j - (M' z).transpose i j) s := by
  simpa [matrixTransposeEntrySubBoundConst, matrixTransposeEntrySubHolderConst,
    matrixTransposeEntryBoundConst, matrixTransposeEntryHolderConst] using hMd j i

/-- Quantitative sup constant for a finite matrix transpose difference. -/
def matrixTransposeSubBoundConst {m n : Type*} [Fintype m] [Fintype n]
    (B : m → n → ℝ) : ℝ :=
  ∑ i : n, ∑ j : m, matrixTransposeEntrySubBoundConst B i j

/-- Quantitative Holder constant for a finite matrix transpose difference. -/
def matrixTransposeSubHolderConst {m n : Type*} [Fintype m] [Fintype n]
    (H : m → n → ℝ) : ℝ :=
  ∑ i : n, ∑ j : m, matrixTransposeEntrySubHolderConst H i j

theorem matrixTransposeSubBoundConst_nonneg {m n : Type*} [Fintype m] [Fintype n]
    {B : m → n → ℝ} (hB : ∀ i j, 0 ≤ B i j) :
    0 ≤ matrixTransposeSubBoundConst B := by
  simpa [matrixTransposeSubBoundConst] using
    (Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj => matrixTransposeEntrySubBoundConst_nonneg hB i j)

theorem matrixTransposeSubHolderConst_nonneg {m n : Type*} [Fintype m] [Fintype n]
    {H : m → n → ℝ} (hH : ∀ i j, 0 ≤ H i j) :
    0 ≤ matrixTransposeSubHolderConst H := by
  simpa [matrixTransposeSubHolderConst] using
    (Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj => matrixTransposeEntrySubHolderConst_nonneg hH i j)

/-- Finite matrix transpose differences have an explicit matrix-valued bounded parabolic
`C^{0,α}` estimate. -/
theorem matrix_transpose_sub_with {m n A : Type*} [Fintype m] [Fintype n]
    [NormedAddCommGroup A] {B H : m → n → ℝ} {M M' : ℝ × X → Matrix m n A}
    (hB : ∀ i j, 0 ≤ B i j) (hH : ∀ i j, 0 ≤ H i j)
    (hMd : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α
      (fun z => M z i j - M' z i j) s) :
    ParabolicC0AlphaWith
      (matrixTransposeSubBoundConst B) (matrixTransposeSubHolderConst H)
      α (fun z => (M z).transpose - (M' z).transpose) s := by
  simp only [matrixTransposeSubBoundConst, matrixTransposeSubHolderConst]
  refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
  · intro i
    exact Finset.sum_nonneg fun j _hj => matrixTransposeEntrySubBoundConst_nonneg hB i j
  · intro i
    exact Finset.sum_nonneg fun j _hj => matrixTransposeEntrySubHolderConst_nonneg hH i j
  · intro i
    refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
    · intro j
      exact matrixTransposeEntrySubBoundConst_nonneg hB i j
    · intro j
      exact matrixTransposeEntrySubHolderConst_nonneg hH i j
    · intro j
      simpa using matrix_transpose_entry_sub_with (M := M) (M' := M') hMd i j

/-- Finite matrix symmetrization preserves parabolic `C^{0,α}` control from entrywise control. -/
theorem matrix_symmetrize {n 𝕜 : Type*} [Fintype n] [NormedField 𝕜]
    {M : ℝ × X → Matrix n n 𝕜}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s) :
    ParabolicC0AlphaOn α (fun z => (2 : 𝕜)⁻¹ • (M z + (M z).transpose)) s :=
  ((matrix_of_entries hM).add (matrix_transpose hM)).smul ((2 : 𝕜)⁻¹)

/-- Finite matrix symmetrization differences preserve existential parabolic `C^{0,α}` control
from entrywise difference control. -/
theorem matrix_symmetrize_sub {n 𝕜 : Type*} [Fintype n] [NormedField 𝕜]
    {M N : ℝ × X → Matrix n n 𝕜}
    (hdiff : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j - N z i j) s) :
    ParabolicC0AlphaOn α
      (fun z => (2 : 𝕜)⁻¹ • (M z + (M z).transpose) -
        (2 : 𝕜)⁻¹ • (N z + (N z).transpose)) s := by
  convert ((matrix_of_entries_sub hdiff).add (matrix_transpose_sub hdiff)).smul ((2 : 𝕜)⁻¹)
      using 1
  ext z i j
  change (2 : 𝕜)⁻¹ * (M z i j + M z j i) -
      (2 : 𝕜)⁻¹ * (N z i j + N z j i) =
    (2 : 𝕜)⁻¹ * ((M z i j - N z i j) + (M z j i - N z j i))
  ring

/-- Quantitative sup constant for one entry of finite matrix symmetrization. -/
def matrixSymmetrizeEntryBoundConst {n 𝕜 : Type*} [NormedField 𝕜]
    (B : n → n → ℝ) (i j : n) : ℝ :=
  ‖(2 : 𝕜)⁻¹‖ * (B i j + B j i)

/-- Quantitative Holder constant for one entry of finite matrix symmetrization. -/
def matrixSymmetrizeEntryHolderConst {n 𝕜 : Type*} [NormedField 𝕜]
    (H : n → n → ℝ) (i j : n) : ℝ :=
  ‖(2 : 𝕜)⁻¹‖ * (H i j + H j i)

theorem matrixSymmetrizeEntryBoundConst_nonneg {n 𝕜 : Type*} [NormedField 𝕜]
    {B : n → n → ℝ} (hB : ∀ i j, 0 ≤ B i j) (i j : n) :
    0 ≤ matrixSymmetrizeEntryBoundConst (𝕜 := 𝕜) B i j :=
  mul_nonneg (norm_nonneg _) (add_nonneg (hB i j) (hB j i))

theorem matrixSymmetrizeEntryHolderConst_nonneg {n 𝕜 : Type*} [NormedField 𝕜]
    {H : n → n → ℝ} (hH : ∀ i j, 0 ≤ H i j) (i j : n) :
    0 ≤ matrixSymmetrizeEntryHolderConst (𝕜 := 𝕜) H i j :=
  mul_nonneg (norm_nonneg _) (add_nonneg (hH i j) (hH j i))

/-- One entry of finite matrix symmetrization has an explicit bounded parabolic `C^{0,α}`
estimate. -/
theorem matrix_symmetrize_entry_with {n 𝕜 : Type*} [NormedField 𝕜]
    {B H : n → n → ℝ} {M : ℝ × X → Matrix n n 𝕜}
    (hM : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => M z i j) s)
    (i j : n) :
    ParabolicC0AlphaWith
      (matrixSymmetrizeEntryBoundConst (𝕜 := 𝕜) B i j)
      (matrixSymmetrizeEntryHolderConst (𝕜 := 𝕜) H i j)
      α (fun z => ((2 : 𝕜)⁻¹ • (M z + (M z).transpose)) i j) s := by
  simpa [matrixSymmetrizeEntryBoundConst, matrixSymmetrizeEntryHolderConst] using
    (((hM i j).add (hM j i)).smul ((2 : 𝕜)⁻¹))

/-- Quantitative sup constant for finite matrix symmetrization. -/
def matrixSymmetrizeBoundConst {n 𝕜 : Type*} [Fintype n] [NormedField 𝕜]
    (B : n → n → ℝ) : ℝ :=
  ∑ i : n, ∑ j : n, matrixSymmetrizeEntryBoundConst (𝕜 := 𝕜) B i j

/-- Quantitative Holder constant for finite matrix symmetrization. -/
def matrixSymmetrizeHolderConst {n 𝕜 : Type*} [Fintype n] [NormedField 𝕜]
    (H : n → n → ℝ) : ℝ :=
  ∑ i : n, ∑ j : n, matrixSymmetrizeEntryHolderConst (𝕜 := 𝕜) H i j

theorem matrixSymmetrizeBoundConst_nonneg {n 𝕜 : Type*} [Fintype n] [NormedField 𝕜]
    {B : n → n → ℝ} (hB : ∀ i j, 0 ≤ B i j) :
    0 ≤ matrixSymmetrizeBoundConst (𝕜 := 𝕜) B := by
  simpa [matrixSymmetrizeBoundConst] using
    (Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj =>
        matrixSymmetrizeEntryBoundConst_nonneg (𝕜 := 𝕜) hB i j)

theorem matrixSymmetrizeHolderConst_nonneg {n 𝕜 : Type*} [Fintype n] [NormedField 𝕜]
    {H : n → n → ℝ} (hH : ∀ i j, 0 ≤ H i j) :
    0 ≤ matrixSymmetrizeHolderConst (𝕜 := 𝕜) H := by
  simpa [matrixSymmetrizeHolderConst] using
    (Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj =>
        matrixSymmetrizeEntryHolderConst_nonneg (𝕜 := 𝕜) hH i j)

/-- Finite matrix symmetrization has an explicit matrix-valued bounded parabolic `C^{0,α}`
estimate. -/
theorem matrix_symmetrize_with {n 𝕜 : Type*} [Fintype n] [NormedField 𝕜]
    {B H : n → n → ℝ} {M : ℝ × X → Matrix n n 𝕜}
    (hB : ∀ i j, 0 ≤ B i j) (hH : ∀ i j, 0 ≤ H i j)
    (hM : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => M z i j) s) :
    ParabolicC0AlphaWith
      (matrixSymmetrizeBoundConst (𝕜 := 𝕜) B)
      (matrixSymmetrizeHolderConst (𝕜 := 𝕜) H)
      α (fun z => (2 : 𝕜)⁻¹ • (M z + (M z).transpose)) s := by
  simp only [matrixSymmetrizeBoundConst, matrixSymmetrizeHolderConst]
  refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
  · intro i
    exact Finset.sum_nonneg fun j _hj =>
      matrixSymmetrizeEntryBoundConst_nonneg (𝕜 := 𝕜) hB i j
  · intro i
    exact Finset.sum_nonneg fun j _hj =>
      matrixSymmetrizeEntryHolderConst_nonneg (𝕜 := 𝕜) hH i j
  · intro i
    refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
    · intro j
      exact matrixSymmetrizeEntryBoundConst_nonneg (𝕜 := 𝕜) hB i j
    · intro j
      exact matrixSymmetrizeEntryHolderConst_nonneg (𝕜 := 𝕜) hH i j
    · intro j
      exact matrix_symmetrize_entry_with hM i j

/-- Quantitative sup constant for one entry of finite matrix symmetrization difference. -/
def matrixSymmetrizeEntrySubBoundConst {n 𝕜 : Type*} [NormedField 𝕜]
    (B : n → n → ℝ) (i j : n) : ℝ :=
  matrixSymmetrizeEntryBoundConst (𝕜 := 𝕜) B i j

/-- Quantitative Holder constant for one entry of finite matrix symmetrization difference. -/
def matrixSymmetrizeEntrySubHolderConst {n 𝕜 : Type*} [NormedField 𝕜]
    (H : n → n → ℝ) (i j : n) : ℝ :=
  matrixSymmetrizeEntryHolderConst (𝕜 := 𝕜) H i j

theorem matrixSymmetrizeEntrySubBoundConst_nonneg {n 𝕜 : Type*} [NormedField 𝕜]
    {B : n → n → ℝ} (hB : ∀ i j, 0 ≤ B i j) (i j : n) :
    0 ≤ matrixSymmetrizeEntrySubBoundConst (𝕜 := 𝕜) B i j :=
  matrixSymmetrizeEntryBoundConst_nonneg (𝕜 := 𝕜) hB i j

theorem matrixSymmetrizeEntrySubHolderConst_nonneg {n 𝕜 : Type*} [NormedField 𝕜]
    {H : n → n → ℝ} (hH : ∀ i j, 0 ≤ H i j) (i j : n) :
    0 ≤ matrixSymmetrizeEntrySubHolderConst (𝕜 := 𝕜) H i j :=
  matrixSymmetrizeEntryHolderConst_nonneg (𝕜 := 𝕜) hH i j

/-- One entry of finite matrix symmetrization difference has an explicit bounded parabolic
`C^{0,α}` estimate. -/
theorem matrix_symmetrize_entry_sub_with {n 𝕜 : Type*} [NormedField 𝕜]
    {B H : n → n → ℝ} {M M' : ℝ × X → Matrix n n 𝕜}
    (hMd : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α
      (fun z => M z i j - M' z i j) s)
    (i j : n) :
    ParabolicC0AlphaWith
      (matrixSymmetrizeEntrySubBoundConst (𝕜 := 𝕜) B i j)
      (matrixSymmetrizeEntrySubHolderConst (𝕜 := 𝕜) H i j)
      α (fun z =>
        ((2 : 𝕜)⁻¹ • (M z + (M z).transpose) -
          (2 : 𝕜)⁻¹ • (M' z + (M' z).transpose)) i j) s := by
  convert (((hMd i j).add (hMd j i)).smul ((2 : 𝕜)⁻¹)) using 1 <;>
    first
    | rfl
    | (funext z
       change (2 : 𝕜)⁻¹ * (M z i j + M z j i) -
           (2 : 𝕜)⁻¹ * (M' z i j + M' z j i) =
         (2 : 𝕜)⁻¹ * ((M z i j - M' z i j) + (M z j i - M' z j i))
       ring)

/-- Quantitative sup constant for finite matrix symmetrization difference. -/
def matrixSymmetrizeSubBoundConst {n 𝕜 : Type*} [Fintype n] [NormedField 𝕜]
    (B : n → n → ℝ) : ℝ :=
  ∑ i : n, ∑ j : n, matrixSymmetrizeEntrySubBoundConst (𝕜 := 𝕜) B i j

/-- Quantitative Holder constant for finite matrix symmetrization difference. -/
def matrixSymmetrizeSubHolderConst {n 𝕜 : Type*} [Fintype n] [NormedField 𝕜]
    (H : n → n → ℝ) : ℝ :=
  ∑ i : n, ∑ j : n, matrixSymmetrizeEntrySubHolderConst (𝕜 := 𝕜) H i j

theorem matrixSymmetrizeSubBoundConst_nonneg {n 𝕜 : Type*} [Fintype n] [NormedField 𝕜]
    {B : n → n → ℝ} (hB : ∀ i j, 0 ≤ B i j) :
    0 ≤ matrixSymmetrizeSubBoundConst (𝕜 := 𝕜) B := by
  simpa [matrixSymmetrizeSubBoundConst] using
    (Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj =>
        matrixSymmetrizeEntrySubBoundConst_nonneg (𝕜 := 𝕜) hB i j)

theorem matrixSymmetrizeSubHolderConst_nonneg {n 𝕜 : Type*} [Fintype n] [NormedField 𝕜]
    {H : n → n → ℝ} (hH : ∀ i j, 0 ≤ H i j) :
    0 ≤ matrixSymmetrizeSubHolderConst (𝕜 := 𝕜) H := by
  simpa [matrixSymmetrizeSubHolderConst] using
    (Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj =>
        matrixSymmetrizeEntrySubHolderConst_nonneg (𝕜 := 𝕜) hH i j)

/-- Finite matrix symmetrization differences have an explicit matrix-valued bounded parabolic
`C^{0,α}` estimate. -/
theorem matrix_symmetrize_sub_with {n 𝕜 : Type*} [Fintype n] [NormedField 𝕜]
    {B H : n → n → ℝ} {M M' : ℝ × X → Matrix n n 𝕜}
    (hB : ∀ i j, 0 ≤ B i j) (hH : ∀ i j, 0 ≤ H i j)
    (hMd : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α
      (fun z => M z i j - M' z i j) s) :
    ParabolicC0AlphaWith
      (matrixSymmetrizeSubBoundConst (𝕜 := 𝕜) B)
      (matrixSymmetrizeSubHolderConst (𝕜 := 𝕜) H)
      α (fun z =>
        (2 : 𝕜)⁻¹ • (M z + (M z).transpose) -
          (2 : 𝕜)⁻¹ • (M' z + (M' z).transpose)) s := by
  simp only [matrixSymmetrizeSubBoundConst, matrixSymmetrizeSubHolderConst]
  refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
  · intro i
    exact Finset.sum_nonneg fun j _hj =>
      matrixSymmetrizeEntrySubBoundConst_nonneg (𝕜 := 𝕜) hB i j
  · intro i
    exact Finset.sum_nonneg fun j _hj =>
      matrixSymmetrizeEntrySubHolderConst_nonneg (𝕜 := 𝕜) hH i j
  · intro i
    refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
    · intro j
      exact matrixSymmetrizeEntrySubBoundConst_nonneg (𝕜 := 𝕜) hB i j
    · intro j
      exact matrixSymmetrizeEntrySubHolderConst_nonneg (𝕜 := 𝕜) hH i j
    · intro j
      simpa using matrix_symmetrize_entry_sub_with (M := M) (M' := M') hMd i j

/-- The finite matrix symmetrization is pointwise symmetric. -/
theorem matrix_symmetrize_isSymm {n 𝕜 : Type*} [NormedField 𝕜] (M : Matrix n n 𝕜) :
    ((2 : 𝕜)⁻¹ • (M + M.transpose)).IsSymm :=
  (Matrix.isSymm_add_transpose_self M).smul ((2 : 𝕜)⁻¹)

/-- Finite matrix traces preserve parabolic `C^{0,α}` control from entrywise control. -/
theorem matrix_trace {n A : Type*} [Fintype n] [NormedAddCommGroup A]
    {M : ℝ × X → Matrix n n A}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s) :
    ParabolicC0AlphaOn α (fun z => Matrix.trace (M z)) s := by
  simpa [Matrix.trace] using
    (ParabolicC0AlphaOn.sum (X := X) (α := α) (s := s)
      (S := (Finset.univ : Finset n)) (u := fun i z => M z i i)
      (fun i _hi => hM i i))

/-- Finite matrix trace differences preserve existential parabolic `C^{0,α}` control from
entrywise difference control. -/
theorem matrix_trace_sub {n A : Type*} [Fintype n] [NormedAddCommGroup A]
    {M N : ℝ × X → Matrix n n A}
    (hdiff : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j - N z i j) s) :
    ParabolicC0AlphaOn α (fun z => Matrix.trace (M z) - Matrix.trace (N z)) s := by
  have hsum :
      ParabolicC0AlphaOn α (fun z => (∑ i : n, M z i i) - ∑ i : n, N z i i) s :=
    ParabolicC0AlphaOn.sum_sub_sum (X := X) (α := α) (s := s)
      (S := (Finset.univ : Finset n)) (u := fun i z => M z i i)
      (v := fun i z => N z i i) (fun i _hi => hdiff i i)
  simpa [Matrix.trace] using hsum

/-- Quantitative sup constant for a finite matrix trace. -/
def matrixTraceBoundConst {n : Type*} [Fintype n] (B : n → n → ℝ) : ℝ :=
  ∑ i : n, B i i

/-- Quantitative Holder constant for a finite matrix trace. -/
def matrixTraceHolderConst {n : Type*} [Fintype n] (H : n → n → ℝ) : ℝ :=
  ∑ i : n, H i i

theorem matrixTraceBoundConst_nonneg {n : Type*} [Fintype n] {B : n → n → ℝ}
    (hB : ∀ i j, 0 ≤ B i j) :
    0 ≤ matrixTraceBoundConst B := by
  simpa [matrixTraceBoundConst] using Finset.sum_nonneg fun i _hi => hB i i

theorem matrixTraceHolderConst_nonneg {n : Type*} [Fintype n] {H : n → n → ℝ}
    (hH : ∀ i j, 0 ≤ H i j) :
    0 ≤ matrixTraceHolderConst H := by
  simpa [matrixTraceHolderConst] using Finset.sum_nonneg fun i _hi => hH i i

/-- Finite matrix traces have an explicit bounded parabolic `C^{0,α}` estimate. -/
theorem matrix_trace_with {n A : Type*} [Fintype n] [NormedAddCommGroup A]
    {B H : n → n → ℝ} {M : ℝ × X → Matrix n n A}
    (hM : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => M z i j) s) :
    ParabolicC0AlphaWith
      (matrixTraceBoundConst B) (matrixTraceHolderConst H)
      α (fun z => Matrix.trace (M z)) s := by
  simpa [Matrix.trace, matrixTraceBoundConst, matrixTraceHolderConst] using
    (ParabolicC0AlphaWith.sum (X := X) (α := α) (s := s)
      (S := (Finset.univ : Finset n)) (B := fun i => B i i) (H := fun i => H i i)
      (u := fun i z => M z i i) (fun i _hi => hM i i))

/-- Quantitative sup constant for a finite matrix trace difference. -/
def matrixTraceSubBoundConst {n : Type*} [Fintype n] (B : n → n → ℝ) : ℝ :=
  ∑ i : n, B i i

/-- Quantitative Holder constant for a finite matrix trace difference. -/
def matrixTraceSubHolderConst {n : Type*} [Fintype n] (H : n → n → ℝ) : ℝ :=
  ∑ i : n, H i i

theorem matrixTraceSubBoundConst_nonneg {n : Type*} [Fintype n] {B : n → n → ℝ}
    (hB : ∀ i j, 0 ≤ B i j) :
    0 ≤ matrixTraceSubBoundConst B := by
  simpa [matrixTraceSubBoundConst] using Finset.sum_nonneg fun i _hi => hB i i

theorem matrixTraceSubHolderConst_nonneg {n : Type*} [Fintype n] {H : n → n → ℝ}
    (hH : ∀ i j, 0 ≤ H i j) :
    0 ≤ matrixTraceSubHolderConst H := by
  simpa [matrixTraceSubHolderConst] using Finset.sum_nonneg fun i _hi => hH i i

/-- Finite matrix trace differences have an explicit bounded parabolic `C^{0,α}` estimate. -/
theorem matrix_trace_sub_with {n A : Type*} [Fintype n] [NormedAddCommGroup A]
    {B H : n → n → ℝ} {M M' : ℝ × X → Matrix n n A}
    (hMd : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α
      (fun z => M z i j - M' z i j) s) :
    ParabolicC0AlphaWith
      (matrixTraceSubBoundConst B) (matrixTraceSubHolderConst H)
      α (fun z => Matrix.trace (M z) - Matrix.trace (M' z)) s := by
  have hsum :
      ParabolicC0AlphaWith
        (∑ i : n, B i i) (∑ i : n, H i i)
        α (fun z => (∑ i : n, M z i i) - ∑ i : n, M' z i i) s :=
    ParabolicC0AlphaWith.sum_sub_sum (X := X) (α := α) (s := s)
      (S := (Finset.univ : Finset n)) (B := fun i => B i i) (H := fun i => H i i)
      (u := fun i z => M z i i) (v := fun i z => M' z i i) (fun i _hi => hMd i i)
  simpa [Matrix.trace, matrixTraceSubBoundConst, matrixTraceSubHolderConst] using hsum

/-- Entrywise sup constants for replacing row `j` by the `i`th coordinate vector. -/
def matrixUpdateRowBoundConst {n A : Type*} [DecidableEq n] [NormedRing A]
    (B : n → n → ℝ) (i j : n) : n → n → ℝ :=
  fun r c => if r = j then ‖((Pi.single i (1 : A)) : n → A) c‖ else B r c

/-- Entrywise Holder constants for replacing row `j` by the constant `i`th coordinate vector. -/
def matrixUpdateRowHolderConst {n : Type*} [DecidableEq n]
    (H : n → n → ℝ) (j : n) : n → n → ℝ :=
  fun r c => if r = j then 0 else H r c

theorem matrixUpdateRowHolderConst_nonneg {n : Type*} [DecidableEq n]
    {H : n → n → ℝ} (hH : ∀ i j, 0 ≤ H i j) (j : n) :
    ∀ r c, 0 ≤ matrixUpdateRowHolderConst H j r c := by
  intro r c
  by_cases hr : r = j
  · simp [matrixUpdateRowHolderConst, hr]
  · simpa [matrixUpdateRowHolderConst, hr] using hH r c

/-- The quantitative sup constant used for an adjugate entry. -/
def matrixAdjugateEntryBoundConst {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedRing A] (B : n → n → ℝ) (i j : n) : ℝ :=
  matrixDetBoundConst (A := A) (matrixUpdateRowBoundConst (A := A) B i j)

/-- The quantitative Holder constant used for an adjugate entry. -/
def matrixAdjugateEntryHolderConst {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedRing A] (B H : n → n → ℝ) (i j : n) : ℝ :=
  matrixDetHolderConst (A := A) (matrixUpdateRowBoundConst (A := A) B i j)
    (matrixUpdateRowHolderConst H j)

/-- The quantitative sup constant used for an adjugate-entry difference. -/
def matrixAdjugateEntrySubBoundConst {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedRing A] (B Bd : n → n → ℝ) (i j : n) : ℝ :=
  matrixDetSubBoundConst (A := A) (matrixUpdateRowBoundConst (A := A) B i j)
    (matrixUpdateRowHolderConst Bd j)

/-- The quantitative Holder constant used for an adjugate-entry difference. -/
def matrixAdjugateEntrySubHolderConst {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedRing A] (B H Bd Hd : n → n → ℝ) (i j : n) : ℝ :=
  matrixDetSubHolderConst (A := A) (matrixUpdateRowBoundConst (A := A) B i j)
    (matrixUpdateRowHolderConst H j) (matrixUpdateRowHolderConst Bd j)
    (matrixUpdateRowHolderConst Hd j)

theorem matrixAdjugateEntryBoundConst_nonneg {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedRing A] (B : n → n → ℝ) (i j : n) :
    0 ≤ matrixAdjugateEntryBoundConst (A := A) B i j :=
  matrixDetBoundConst_nonneg (A := A) (matrixUpdateRowBoundConst (A := A) B i j)

theorem matrixAdjugateEntryHolderConst_nonneg {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedRing A] {B H : n → n → ℝ} (hH : ∀ i j, 0 ≤ H i j) (i j : n) :
    0 ≤ matrixAdjugateEntryHolderConst (A := A) B H i j :=
  matrixDetHolderConst_nonneg (A := A)
    (matrixUpdateRowHolderConst_nonneg hH j)

theorem matrixAdjugateEntrySubBoundConst_nonneg {n A : Type*} [Fintype n]
    [DecidableEq n] [NormedRing A] {B Bd : n → n → ℝ}
    (hBd : ∀ i j, 0 ≤ Bd i j) (i j : n) :
    0 ≤ matrixAdjugateEntrySubBoundConst (A := A) B Bd i j :=
  matrixDetSubBoundConst_nonneg (A := A)
    (matrixUpdateRowHolderConst_nonneg hBd j)

theorem matrixAdjugateEntrySubHolderConst_nonneg {n A : Type*} [Fintype n]
    [DecidableEq n] [NormedRing A] {B H Bd Hd : n → n → ℝ}
    (hH : ∀ i j, 0 ≤ H i j) (hBd : ∀ i j, 0 ≤ Bd i j)
    (hHd : ∀ i j, 0 ≤ Hd i j) (i j : n) :
    0 ≤ matrixAdjugateEntrySubHolderConst (A := A) B H Bd Hd i j :=
  matrixDetSubHolderConst_nonneg (A := A)
    (matrixUpdateRowHolderConst_nonneg hH j)
    (matrixUpdateRowHolderConst_nonneg hBd j)
    (matrixUpdateRowHolderConst_nonneg hHd j)


/-- Each adjugate entry has an explicit bounded parabolic `C^{0,α}` estimate when the matrix
entries do. -/
theorem matrix_adjugate_entry_with {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedCommRing A] {B H : n → n → ℝ} {M : ℝ × X → Matrix n n A}
    (hH : ∀ i j, 0 ≤ H i j)
    (hM : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => M z i j) s)
    (i j : n) :
    ParabolicC0AlphaWith
      (matrixAdjugateEntryBoundConst (A := A) B i j)
      (matrixAdjugateEntryHolderConst (A := A) B H i j)
      α (fun z => (M z).adjugate i j) s := by
  have hHupd : ∀ r c, 0 ≤ matrixUpdateRowHolderConst H j r c := by
    intro r c
    by_cases hr : r = j
    · simp [matrixUpdateRowHolderConst, hr]
    · simpa [matrixUpdateRowHolderConst, hr] using hH r c
  have hMupd : ∀ r c,
      ParabolicC0AlphaWith
        (matrixUpdateRowBoundConst (A := A) B i j r c)
        (matrixUpdateRowHolderConst H j r c)
        α
        (fun z => ((M z).updateRow j ((Pi.single i (1 : A)) : n → A)) r c) s := by
    intro r c
    by_cases hr : r = j
    · subst r
      simpa [matrixUpdateRowBoundConst, matrixUpdateRowHolderConst, Matrix.updateRow_apply] using
        (ParabolicC0AlphaWith.const (s := s) (α := α)
          (((Pi.single i (1 : A)) : n → A) c) le_rfl le_rfl)
    · simpa [matrixUpdateRowBoundConst, matrixUpdateRowHolderConst, Matrix.updateRow_apply,
        Function.update_of_ne hr, hr] using hM r c
  have hdet :
      ParabolicC0AlphaWith
        (matrixAdjugateEntryBoundConst (A := A) B i j)
        (matrixAdjugateEntryHolderConst (A := A) B H i j)
        α
        (fun z => ((M z).updateRow j ((Pi.single i (1 : A)) : n → A)).det) s := by
    simpa [matrixAdjugateEntryBoundConst, matrixAdjugateEntryHolderConst] using
      (matrix_det_with
        (M := fun z => (M z).updateRow j ((Pi.single i (1 : A)) : n → A))
        (B := matrixUpdateRowBoundConst (A := A) B i j)
        (H := matrixUpdateRowHolderConst H j)
        hHupd hMupd)
  convert hdet using 1
  funext z
  rw [Matrix.adjugate_apply]

/-- Adjugate-entry differences inherit parabolic `C^{0,α}` control from entrywise matrix
difference controls. -/
theorem matrix_adjugate_entry_sub_with {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedCommRing A] {B H Bd Hd : n → n → ℝ} {M N : ℝ × X → Matrix n n A}
    (hH : ∀ i j, 0 ≤ H i j)
    (hBd : ∀ i j, 0 ≤ Bd i j)
    (hHd : ∀ i j, 0 ≤ Hd i j)
    (hM : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => M z i j) s)
    (hN : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => N z i j) s)
    (hdiff : ∀ i j,
      ParabolicC0AlphaWith (Bd i j) (Hd i j) α (fun z => M z i j - N z i j) s)
    (i j : n) :
    ParabolicC0AlphaWith
      (matrixAdjugateEntrySubBoundConst (A := A) B Bd i j)
      (matrixAdjugateEntrySubHolderConst (A := A) B H Bd Hd i j)
      α (fun z => (M z).adjugate i j - (N z).adjugate i j) s := by
  let e : n → A := (Pi.single i (1 : A))
  have hHupd : ∀ r c, 0 ≤ matrixUpdateRowHolderConst H j r c :=
    matrixUpdateRowHolderConst_nonneg hH j
  have hBdupd : ∀ r c, 0 ≤ matrixUpdateRowHolderConst Bd j r c :=
    matrixUpdateRowHolderConst_nonneg hBd j
  have hHdupd : ∀ r c, 0 ≤ matrixUpdateRowHolderConst Hd j r c :=
    matrixUpdateRowHolderConst_nonneg hHd j
  have hMupd : ∀ r c,
      ParabolicC0AlphaWith
        (matrixUpdateRowBoundConst (A := A) B i j r c)
        (matrixUpdateRowHolderConst H j r c)
        α (fun z => ((M z).updateRow j e) r c) s := by
    intro r c
    by_cases hr : r = j
    · subst r
      simpa [e, matrixUpdateRowBoundConst, matrixUpdateRowHolderConst, Matrix.updateRow_apply] using
        (ParabolicC0AlphaWith.const (s := s) (α := α)
          (((Pi.single i (1 : A)) : n → A) c) le_rfl le_rfl)
    · simpa [e, matrixUpdateRowBoundConst, matrixUpdateRowHolderConst, Matrix.updateRow_apply,
        Function.update_of_ne hr, hr] using hM r c
  have hNupd : ∀ r c,
      ParabolicC0AlphaWith
        (matrixUpdateRowBoundConst (A := A) B i j r c)
        (matrixUpdateRowHolderConst H j r c)
        α (fun z => ((N z).updateRow j e) r c) s := by
    intro r c
    by_cases hr : r = j
    · subst r
      simpa [e, matrixUpdateRowBoundConst, matrixUpdateRowHolderConst, Matrix.updateRow_apply] using
        (ParabolicC0AlphaWith.const (s := s) (α := α)
          (((Pi.single i (1 : A)) : n → A) c) le_rfl le_rfl)
    · simpa [e, matrixUpdateRowBoundConst, matrixUpdateRowHolderConst, Matrix.updateRow_apply,
        Function.update_of_ne hr, hr] using hN r c
  have hdiffupd : ∀ r c,
      ParabolicC0AlphaWith
        (matrixUpdateRowHolderConst Bd j r c)
        (matrixUpdateRowHolderConst Hd j r c)
        α (fun z => ((M z).updateRow j e) r c - ((N z).updateRow j e) r c) s := by
    intro r c
    by_cases hr : r = j
    · subst r
      simpa [e, matrixUpdateRowHolderConst, Matrix.updateRow_apply] using
        (ParabolicC0AlphaWith.const (s := s) (α := α) (B := 0) (H := 0)
          (0 : A) (by simp) le_rfl)
    · simpa [e, matrixUpdateRowHolderConst, Matrix.updateRow_apply, Function.update_of_ne hr, hr]
        using hdiff r c
  have hdet :
      ParabolicC0AlphaWith
        (matrixAdjugateEntrySubBoundConst (A := A) B Bd i j)
        (matrixAdjugateEntrySubHolderConst (A := A) B H Bd Hd i j)
        α
        (fun z => ((M z).updateRow j e).det - ((N z).updateRow j e).det) s := by
    simpa [e, matrixAdjugateEntrySubBoundConst, matrixAdjugateEntrySubHolderConst] using
      (matrix_det_sub_with
        (M := fun z => (M z).updateRow j e)
        (N := fun z => (N z).updateRow j e)
        (B := matrixUpdateRowBoundConst (A := A) B i j)
        (H := matrixUpdateRowHolderConst H j)
        (Bd := matrixUpdateRowHolderConst Bd j)
        (Hd := matrixUpdateRowHolderConst Hd j)
        hHupd hBdupd hHdupd hMupd hNupd hdiffupd)
  simpa [e, Matrix.adjugate_apply] using hdet

/-- Adjugate entries are pointwise Lipschitz on entrywise bounded finite matrices.  The estimate
is obtained by applying the determinant Lipschitz bound to the row-replacement matrices defining
the adjugate entry. -/
theorem matrix_adjugate_entry_norm_sub_le {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedCommRing A] {C : n → n → ℝ} (M N : Matrix n n A)
    (hM : ∀ r c, ‖M r c‖ ≤ C r c) (hN : ∀ r c, ‖N r c‖ ≤ C r c)
    (i j : n) :
    ‖M.adjugate i j - N.adjugate i j‖ ≤
      ∑ σ : Equiv.Perm n,
        ‖(Equiv.Perm.sign σ : ℤ)‖ *
          ((∑ r : n,
              ‖(M.updateRow j ((Pi.single i (1 : A)) : n → A)) (σ r) r -
                (N.updateRow j ((Pi.single i (1 : A)) : n → A)) (σ r) r‖) *
            (max ‖(1 : A)‖ 1 *
              ∏ r : n, max (matrixUpdateRowBoundConst (A := A) C i j (σ r) r) 1)) := by
  let e : n → A := (Pi.single i (1 : A))
  have hMupd : ∀ r c, ‖(M.updateRow j e) r c‖ ≤
      matrixUpdateRowBoundConst (A := A) C i j r c := by
    intro r c
    by_cases hr : r = j
    · subst r
      simp [e, matrixUpdateRowBoundConst, Matrix.updateRow_apply]
    · simpa [e, matrixUpdateRowBoundConst, Matrix.updateRow_apply, Function.update_of_ne hr, hr]
        using hM r c
  have hNupd : ∀ r c, ‖(N.updateRow j e) r c‖ ≤
      matrixUpdateRowBoundConst (A := A) C i j r c := by
    intro r c
    by_cases hr : r = j
    · subst r
      simp [e, matrixUpdateRowBoundConst, Matrix.updateRow_apply]
    · simpa [e, matrixUpdateRowBoundConst, Matrix.updateRow_apply, Function.update_of_ne hr, hr]
        using hN r c
  simpa [e, Matrix.adjugate_apply] using
    (matrix_det_norm_sub_le
      (C := matrixUpdateRowBoundConst (A := A) C i j)
      (M.updateRow j e) (N.updateRow j e) hMupd hNupd)

/-- Elementwise matrix-norm Lipschitz constant for one adjugate entry on an entrywise bounded
set. -/
def matrixAdjugateEntryLipschitzConst {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedCommRing A] (C : n → n → ℝ) (i j : n) : ℝ :=
  matrixDetLipschitzConst (A := A) (matrixUpdateRowBoundConst (A := A) C i j)

theorem matrixAdjugateEntryLipschitzConst_nonneg {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedCommRing A] (C : n → n → ℝ) (i j : n) :
    0 ≤ matrixAdjugateEntryLipschitzConst (A := A) C i j :=
  matrixDetLipschitzConst_nonneg (A := A) (matrixUpdateRowBoundConst (A := A) C i j)

/-- Adjugate entries are Lipschitz in the elementwise matrix norm on entrywise bounded finite
matrices. -/
theorem matrix_adjugate_entry_norm_sub_le_const_mul {n A : Type*} [Fintype n]
    [DecidableEq n] [NormedCommRing A] {C : n → n → ℝ} (M N : Matrix n n A)
    (hM : ∀ r c, ‖M r c‖ ≤ C r c) (hN : ∀ r c, ‖N r c‖ ≤ C r c)
    (i j : n) :
    ‖M.adjugate i j - N.adjugate i j‖ ≤
      matrixAdjugateEntryLipschitzConst (A := A) C i j * ‖M - N‖ := by
  let e : n → A := (Pi.single i (1 : A))
  have hMupd : ∀ r c, ‖(M.updateRow j e) r c‖ ≤
      matrixUpdateRowBoundConst (A := A) C i j r c := by
    intro r c
    by_cases hr : r = j
    · subst r
      simp [e, matrixUpdateRowBoundConst, Matrix.updateRow_apply]
    · simpa [e, matrixUpdateRowBoundConst, Matrix.updateRow_apply, Function.update_of_ne hr, hr]
        using hM r c
  have hNupd : ∀ r c, ‖(N.updateRow j e) r c‖ ≤
      matrixUpdateRowBoundConst (A := A) C i j r c := by
    intro r c
    by_cases hr : r = j
    · subst r
      simp [e, matrixUpdateRowBoundConst, Matrix.updateRow_apply]
    · simpa [e, matrixUpdateRowBoundConst, Matrix.updateRow_apply, Function.update_of_ne hr, hr]
        using hN r c
  have hupd_norm :
      ‖M.updateRow j e - N.updateRow j e‖ ≤ ‖M - N‖ := by
    refine (Matrix.norm_le_iff (norm_nonneg _)).2 ?_
    intro r c
    by_cases hr : r = j
    · subst r
      simp [Matrix.updateRow_apply]
    · simpa [Matrix.updateRow_ne hr] using
        Matrix.norm_entry_le_entrywise_sup_norm (M - N) (i := r) (j := c)
  have hdet :
      ‖(M.updateRow j e).det - (N.updateRow j e).det‖ ≤
        matrixAdjugateEntryLipschitzConst (A := A) C i j * ‖M.updateRow j e - N.updateRow j e‖ := by
    simpa [matrixAdjugateEntryLipschitzConst] using
      matrix_det_norm_sub_le_const_mul
        (C := matrixUpdateRowBoundConst (A := A) C i j)
        (M.updateRow j e) (N.updateRow j e) hMupd hNupd
  calc
    ‖M.adjugate i j - N.adjugate i j‖ =
        ‖(M.updateRow j e).det - (N.updateRow j e).det‖ := by
      simp [e, Matrix.adjugate_apply]
    _ ≤ matrixAdjugateEntryLipschitzConst (A := A) C i j *
        ‖M.updateRow j e - N.updateRow j e‖ := hdet
    _ ≤ matrixAdjugateEntryLipschitzConst (A := A) C i j * ‖M - N‖ :=
      mul_le_mul_of_nonneg_left hupd_norm
        (matrixAdjugateEntryLipschitzConst_nonneg (A := A) C i j)

/-- Adjugate entries are pointwise bounded by the quantitative adjugate-entry constant. -/
theorem matrix_adjugate_entry_norm_le {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedCommRing A] {C : n → n → ℝ} (M : Matrix n n A)
    (hM : ∀ r c, ‖M r c‖ ≤ C r c) (i j : n) :
    ‖M.adjugate i j‖ ≤ matrixAdjugateEntryBoundConst (A := A) C i j := by
  let e : n → A := (Pi.single i (1 : A))
  have hMupd : ∀ r c, ‖(M.updateRow j e) r c‖ ≤
      matrixUpdateRowBoundConst (A := A) C i j r c := by
    intro r c
    by_cases hr : r = j
    · subst r
      simp [e, matrixUpdateRowBoundConst, Matrix.updateRow_apply]
    · simpa [e, matrixUpdateRowBoundConst, Matrix.updateRow_apply, Function.update_of_ne hr, hr]
        using hM r c
  simpa [e, Matrix.adjugate_apply, matrixAdjugateEntryBoundConst] using
    (matrix_det_norm_le
      (C := matrixUpdateRowBoundConst (A := A) C i j)
      (M.updateRow j e) hMupd)

/-- Each adjugate entry of a finite matrix is parabolic `C^{0,α}` when the matrix entries are. -/
theorem matrix_adjugate_entry {n A : Type*} [Fintype n] [DecidableEq n] [NormedCommRing A]
    {M : ℝ × X → Matrix n n A}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s) (i j : n) :
    ParabolicC0AlphaOn α (fun z => (M z).adjugate i j) s := by
  have hdet :
      ParabolicC0AlphaOn α
        (fun z => ((M z).updateRow j ((Pi.single i (1 : A)) : n → A)).det) s := by
    exact matrix_det (M := fun z => (M z).updateRow j ((Pi.single i (1 : A)) : n → A))
      (fun r c => by
        by_cases hr : r = j
        · subst r
          simpa [Matrix.updateRow_apply] using
            (ParabolicC0AlphaOn.const (α := α) (s := s)
              (((Pi.single i (1 : A)) : n → A) c))
        · simpa [Matrix.updateRow_ne hr] using hM r c)
  convert hdet using 1
  funext z
  rw [Matrix.adjugate_apply]

/-- Adjugate-entry differences inherit existential parabolic `C^{0,α}` control from entrywise
matrix controls and entrywise difference controls. -/
theorem matrix_adjugate_entry_sub {n A : Type*} [Fintype n] [DecidableEq n]
    [NormedCommRing A] {M N : ℝ × X → Matrix n n A}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s)
    (hN : ∀ i j, ParabolicC0AlphaOn α (fun z => N z i j) s)
    (hdiff : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j - N z i j) s)
    (i j : n) :
    ParabolicC0AlphaOn α (fun z => (M z).adjugate i j - (N z).adjugate i j) s := by
  let e : n → A := (Pi.single i (1 : A))
  have hMupd : ∀ r c,
      ParabolicC0AlphaOn α (fun z => ((M z).updateRow j e) r c) s := by
    intro r c
    by_cases hr : r = j
    · subst r
      simpa [e, Matrix.updateRow_apply] using
        (ParabolicC0AlphaOn.const (α := α) (s := s)
          (((Pi.single i (1 : A)) : n → A) c))
    · simpa [e, Matrix.updateRow_ne hr] using hM r c
  have hNupd : ∀ r c,
      ParabolicC0AlphaOn α (fun z => ((N z).updateRow j e) r c) s := by
    intro r c
    by_cases hr : r = j
    · subst r
      simpa [e, Matrix.updateRow_apply] using
        (ParabolicC0AlphaOn.const (α := α) (s := s)
          (((Pi.single i (1 : A)) : n → A) c))
    · simpa [e, Matrix.updateRow_ne hr] using hN r c
  have hdiffupd : ∀ r c,
      ParabolicC0AlphaOn α
        (fun z => ((M z).updateRow j e) r c - ((N z).updateRow j e) r c) s := by
    intro r c
    by_cases hr : r = j
    · subst r
      simpa [e, Matrix.updateRow_apply] using
        (ParabolicC0AlphaOn.const (α := α) (s := s) (0 : A))
    · simpa [e, Matrix.updateRow_ne hr] using hdiff r c
  have hdet :
      ParabolicC0AlphaOn α
        (fun z => ((M z).updateRow j e).det - ((N z).updateRow j e).det) s :=
    matrix_det_sub (M := fun z => (M z).updateRow j e)
      (N := fun z => (N z).updateRow j e) hMupd hNupd hdiffupd
  simpa [e, Matrix.adjugate_apply] using hdet

/-- Each inverse-matrix entry is parabolic `C^{0,α}` when the matrix entries are and the
determinant is uniformly bounded away from zero on the domain. -/
theorem matrix_inv_entry {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {δ : ℝ} {M : ℝ × X → Matrix n n 𝕜}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (i j : n) :
    ParabolicC0AlphaOn α (fun z => (M z)⁻¹ i j) s := by
  have hdet_inv : ParabolicC0AlphaOn α (fun z => ((M z).det)⁻¹) s :=
    (matrix_det (M := M) hM).inv hδpos hdet
  have hadj : ParabolicC0AlphaOn α (fun z => (M z).adjugate i j) s :=
    matrix_adjugate_entry (M := M) hM i j
  have hprod := hdet_inv.mul hadj
  convert hprod using 1
  funext z
  rw [Matrix.inv_def, Ring.inverse_eq_inv]
  rfl

/-- The quantitative sup constant used for an inverse-matrix entry. -/
def matrixInvEntryBoundConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    (δ : ℝ) (B : n → n → ℝ) (i j : n) : ℝ :=
  δ⁻¹ * matrixAdjugateEntryBoundConst (A := 𝕜) B i j

/-- The quantitative Holder constant used for an inverse-matrix entry. -/
def matrixInvEntryHolderConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    (δ : ℝ) (B H : n → n → ℝ) (i j : n) : ℝ :=
  δ⁻¹ * matrixAdjugateEntryHolderConst (A := 𝕜) B H i j +
    matrixAdjugateEntryBoundConst (A := 𝕜) B i j *
      (δ⁻¹ * matrixDetHolderConst (A := 𝕜) B H * δ⁻¹)

/-- Sup constant for one inverse-matrix entry difference from entrywise matrix-difference
controls. -/
def matrixInvEntrySubBoundConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (B Bd : n → n → ℝ) (i j : n) : ℝ :=
  δ⁻¹ * matrixAdjugateEntrySubBoundConst (A := 𝕜) B Bd i j +
    matrixDetInvSubBoundConst (𝕜 := 𝕜) δ B Bd *
      matrixAdjugateEntryBoundConst (A := 𝕜) B i j

/-- Holder constant for one inverse-matrix entry difference from entrywise matrix-difference
controls. -/
def matrixInvEntrySubHolderConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (B H Bd Hd : n → n → ℝ) (i j : n) : ℝ :=
  (δ⁻¹ * matrixAdjugateEntrySubHolderConst (A := 𝕜) B H Bd Hd i j +
    matrixAdjugateEntrySubBoundConst (A := 𝕜) B Bd i j *
      (δ⁻¹ * matrixDetHolderConst (A := 𝕜) B H * δ⁻¹)) +
    (matrixDetInvSubBoundConst (𝕜 := 𝕜) δ B Bd *
      matrixAdjugateEntryHolderConst (A := 𝕜) B H i j +
    matrixAdjugateEntryBoundConst (A := 𝕜) B i j *
      matrixDetInvSubHolderConst (𝕜 := 𝕜) δ B H Bd Hd)

/-- Sup constant for finite inverse-matrix differences from entrywise matrix-difference
controls. -/
def matrixInvEntrywiseSubBoundConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (B Bd : n → n → ℝ) : ℝ :=
  ∑ i : n, ∑ j : n, matrixInvEntrySubBoundConst (𝕜 := 𝕜) δ B Bd i j

/-- Holder constant for finite inverse-matrix differences from entrywise matrix-difference
controls. -/
def matrixInvEntrywiseSubHolderConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (B H Bd Hd : n → n → ℝ) : ℝ :=
  ∑ i : n, ∑ j : n, matrixInvEntrySubHolderConst (𝕜 := 𝕜) δ B H Bd Hd i j

theorem matrixInvEntryBoundConst_nonneg {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} (hδpos : 0 < δ) (B : n → n → ℝ) (i j : n) :
    0 ≤ matrixInvEntryBoundConst (𝕜 := 𝕜) δ B i j := by
  exact mul_nonneg (inv_nonneg.mpr hδpos.le)
    (matrixAdjugateEntryBoundConst_nonneg (A := 𝕜) B i j)

theorem matrixInvEntryHolderConst_nonneg {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {B H : n → n → ℝ}
    (hH : ∀ i j, 0 ≤ H i j) (hδpos : 0 < δ) (i j : n) :
    0 ≤ matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H i j := by
  exact add_nonneg
    (mul_nonneg (inv_nonneg.mpr hδpos.le)
      (matrixAdjugateEntryHolderConst_nonneg (A := 𝕜) hH i j))
    (mul_nonneg (matrixAdjugateEntryBoundConst_nonneg (A := 𝕜) B i j)
      (mul_nonneg
        (mul_nonneg (inv_nonneg.mpr hδpos.le) (matrixDetHolderConst_nonneg (A := 𝕜) hH))
        (inv_nonneg.mpr hδpos.le)))

theorem matrixInvEntrySubBoundConst_nonneg {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {B Bd : n → n → ℝ}
    (hδpos : 0 < δ) (hBd : ∀ i j, 0 ≤ Bd i j) (i j : n) :
    0 ≤ matrixInvEntrySubBoundConst (𝕜 := 𝕜) δ B Bd i j := by
  exact add_nonneg
    (mul_nonneg (inv_nonneg.mpr hδpos.le)
      (matrixAdjugateEntrySubBoundConst_nonneg (A := 𝕜) hBd i j))
    (mul_nonneg (matrixDetInvSubBoundConst_nonneg (𝕜 := 𝕜) hδpos hBd)
      (matrixAdjugateEntryBoundConst_nonneg (A := 𝕜) B i j))

theorem matrixInvEntrySubHolderConst_nonneg {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {B H Bd Hd : n → n → ℝ}
    (hδpos : 0 < δ) (hH : ∀ i j, 0 ≤ H i j)
    (hBd : ∀ i j, 0 ≤ Bd i j) (hHd : ∀ i j, 0 ≤ Hd i j) (i j : n) :
    0 ≤ matrixInvEntrySubHolderConst (𝕜 := 𝕜) δ B H Bd Hd i j := by
  have hδnn : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδpos.le
  exact add_nonneg
    (add_nonneg
      (mul_nonneg hδnn
        (matrixAdjugateEntrySubHolderConst_nonneg (A := 𝕜) hH hBd hHd i j))
      (mul_nonneg
        (matrixAdjugateEntrySubBoundConst_nonneg (A := 𝕜) hBd i j)
        (mul_nonneg (mul_nonneg hδnn (matrixDetHolderConst_nonneg (A := 𝕜) hH))
          hδnn)))
    (add_nonneg
      (mul_nonneg (matrixDetInvSubBoundConst_nonneg (𝕜 := 𝕜) hδpos hBd)
        (matrixAdjugateEntryHolderConst_nonneg (A := 𝕜) hH i j))
      (mul_nonneg (matrixAdjugateEntryBoundConst_nonneg (A := 𝕜) B i j)
        (matrixDetInvSubHolderConst_nonneg (𝕜 := 𝕜) hδpos hH hBd hHd)))

theorem matrixInvEntrywiseSubBoundConst_nonneg {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {B Bd : n → n → ℝ}
    (hδpos : 0 < δ) (hBd : ∀ i j, 0 ≤ Bd i j) :
    0 ≤ matrixInvEntrywiseSubBoundConst (𝕜 := 𝕜) δ B Bd := by
  exact Finset.sum_nonneg fun i _hi =>
    Finset.sum_nonneg fun j _hj =>
      matrixInvEntrySubBoundConst_nonneg (𝕜 := 𝕜) hδpos hBd i j

theorem matrixInvEntrywiseSubHolderConst_nonneg {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {B H Bd Hd : n → n → ℝ}
    (hδpos : 0 < δ) (hH : ∀ i j, 0 ≤ H i j)
    (hBd : ∀ i j, 0 ≤ Bd i j) (hHd : ∀ i j, 0 ≤ Hd i j) :
    0 ≤ matrixInvEntrywiseSubHolderConst (𝕜 := 𝕜) δ B H Bd Hd := by
  exact Finset.sum_nonneg fun i _hi =>
    Finset.sum_nonneg fun j _hj =>
      matrixInvEntrySubHolderConst_nonneg (𝕜 := 𝕜) hδpos hH hBd hHd i j

/-- Pointwise finite-dimensional Lipschitz bound for one inverse-matrix entry.  It depends on
the two matrices through the determinant and row-replacement adjugate differences. -/
def matrixInvEntryLipschitzBound {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (C : n → n → ℝ) (M N : Matrix n n 𝕜)
    (i j : n) : ℝ :=
  δ⁻¹ *
    (∑ σ : Equiv.Perm n,
      ‖(Equiv.Perm.sign σ : ℤ)‖ *
        ((∑ r : n,
            ‖(M.updateRow j ((Pi.single i (1 : 𝕜)) : n → 𝕜)) (σ r) r -
              (N.updateRow j ((Pi.single i (1 : 𝕜)) : n → 𝕜)) (σ r) r‖) *
          (max ‖(1 : 𝕜)‖ 1 *
            ∏ r : n, max (matrixUpdateRowBoundConst (A := 𝕜) C i j (σ r) r) 1))) +
    ((δ⁻¹ * δ⁻¹) *
      (∑ σ : Equiv.Perm n,
        ‖(Equiv.Perm.sign σ : ℤ)‖ *
          ((∑ r : n, ‖M (σ r) r - N (σ r) r‖) *
            (max ‖(1 : 𝕜)‖ 1 * ∏ r : n, max (C (σ r) r) 1)))) *
      matrixAdjugateEntryBoundConst (A := 𝕜) C i j

/-- Inverse-matrix entries are pointwise Lipschitz on entrywise bounded matrices whose
determinants have a common positive lower bound.  The estimate separates the adjugate variation
from the reciprocal determinant variation. -/
theorem matrix_inv_entry_norm_sub_le {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ} (M N : Matrix n n 𝕜)
    (hM : ∀ r c, ‖M r c‖ ≤ C r c) (hN : ∀ r c, ‖N r c‖ ≤ C r c)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖)
    (i j : n) :
    ‖M⁻¹ i j - N⁻¹ i j‖ ≤
      matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N i j := by
  classical
  let adjRhs : ℝ :=
    ∑ σ : Equiv.Perm n,
      ‖(Equiv.Perm.sign σ : ℤ)‖ *
        ((∑ r : n,
            ‖(M.updateRow j ((Pi.single i (1 : 𝕜)) : n → 𝕜)) (σ r) r -
              (N.updateRow j ((Pi.single i (1 : 𝕜)) : n → 𝕜)) (σ r) r‖) *
          (max ‖(1 : 𝕜)‖ 1 *
            ∏ r : n, max (matrixUpdateRowBoundConst (A := 𝕜) C i j (σ r) r) 1))
  let detRhs : ℝ :=
    ∑ σ : Equiv.Perm n,
      ‖(Equiv.Perm.sign σ : ℤ)‖ *
        ((∑ r : n, ‖M (σ r) r - N (σ r) r‖) *
          (max ‖(1 : 𝕜)‖ 1 * ∏ r : n, max (C (σ r) r) 1))
  have hinvδ_nonneg : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδpos.le
  have hdet_lip : ‖M.det - N.det‖ ≤ detRhs := by
    simpa [detRhs] using matrix_det_norm_sub_le (C := C) M N hM hN
  have hadj_lip : ‖M.adjugate i j - N.adjugate i j‖ ≤ adjRhs := by
    simpa [adjRhs] using matrix_adjugate_entry_norm_sub_le (C := C) M N hM hN i j
  have hdetRhs_nonneg : 0 ≤ detRhs := (norm_nonneg _).trans hdet_lip
  have hadjRhs_nonneg : 0 ≤ adjRhs := (norm_nonneg _).trans hadj_lip
  have hadj_boundN :
      ‖N.adjugate i j‖ ≤ matrixAdjugateEntryBoundConst (A := 𝕜) C i j :=
    matrix_adjugate_entry_norm_le (C := C) N hN i j
  have hinv_detM : ‖(M.det)⁻¹‖ ≤ δ⁻¹ := by
    have hnorm_pos : 0 < ‖M.det‖ := lt_of_lt_of_le hδpos hdetM
    rw [norm_inv]
    exact (inv_le_inv₀ hnorm_pos hδpos).2 hdetM
  have hdet_inv_lip :
      ‖(M.det)⁻¹ - (N.det)⁻¹‖ ≤ (δ⁻¹ * δ⁻¹) * ‖M.det - N.det‖ := by
    have hdist := (lipschitzOnWith_inv_of_norm_ge (𝕜 := 𝕜) hδpos).dist_le_mul
      M.det (show M.det ∈ {a : 𝕜 | δ ≤ ‖a‖} from hdetM)
      N.det (show N.det ∈ {a : 𝕜 | δ ≤ ‖a‖} from hdetN)
    change dist ((M.det)⁻¹) ((N.det)⁻¹) ≤
      (δ⁻¹ * δ⁻¹ : ℝ) * dist M.det N.det at hdist
    simpa [dist_eq_norm, mul_assoc] using hdist
  have hdet_inv_Rhs :
      ‖(M.det)⁻¹ - (N.det)⁻¹‖ ≤ (δ⁻¹ * δ⁻¹) * detRhs :=
    hdet_inv_lip.trans
      (mul_le_mul_of_nonneg_left hdet_lip (mul_nonneg hinvδ_nonneg hinvδ_nonneg))
  have hfirst :
      ‖(M.det)⁻¹‖ * ‖M.adjugate i j - N.adjugate i j‖ ≤ δ⁻¹ * adjRhs :=
    mul_le_mul hinv_detM hadj_lip (norm_nonneg _) hinvδ_nonneg
  have hsecond :
      ‖(M.det)⁻¹ - (N.det)⁻¹‖ * ‖N.adjugate i j‖ ≤
        ((δ⁻¹ * δ⁻¹) * detRhs) *
          matrixAdjugateEntryBoundConst (A := 𝕜) C i j := by
    exact mul_le_mul hdet_inv_Rhs hadj_boundN (norm_nonneg _)
      (mul_nonneg (mul_nonneg hinvδ_nonneg hinvδ_nonneg) hdetRhs_nonneg)
  have hentry :
      M⁻¹ i j - N⁻¹ i j =
        (M.det)⁻¹ * M.adjugate i j - (N.det)⁻¹ * N.adjugate i j := by
    rw [Matrix.inv_def, Matrix.inv_def, Ring.inverse_eq_inv, Ring.inverse_eq_inv]
    rfl
  have hsplit :
      (M.det)⁻¹ * M.adjugate i j - (N.det)⁻¹ * N.adjugate i j =
        (M.det)⁻¹ * (M.adjugate i j - N.adjugate i j) +
          ((M.det)⁻¹ - (N.det)⁻¹) * N.adjugate i j := by
    ring
  calc
    ‖M⁻¹ i j - N⁻¹ i j‖ =
        ‖(M.det)⁻¹ * M.adjugate i j - (N.det)⁻¹ * N.adjugate i j‖ := by
      rw [hentry]
    _ =
        ‖(M.det)⁻¹ * (M.adjugate i j - N.adjugate i j) +
          ((M.det)⁻¹ - (N.det)⁻¹) * N.adjugate i j‖ := by
      rw [hsplit]
    _ ≤
        ‖(M.det)⁻¹ * (M.adjugate i j - N.adjugate i j)‖ +
          ‖((M.det)⁻¹ - (N.det)⁻¹) * N.adjugate i j‖ :=
      norm_add_le _ _
    _ ≤
        ‖(M.det)⁻¹‖ * ‖M.adjugate i j - N.adjugate i j‖ +
          (‖(M.det)⁻¹ - (N.det)⁻¹‖ * ‖N.adjugate i j‖) :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤
        δ⁻¹ * adjRhs +
          ((δ⁻¹ * δ⁻¹) * detRhs) *
            matrixAdjugateEntryBoundConst (A := 𝕜) C i j :=
      add_le_add hfirst hsecond
    _ = matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N i j := by
      simp [adjRhs, detRhs, matrixInvEntryLipschitzBound]

theorem matrixInvEntryLipschitzBound_nonneg {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ} (M N : Matrix n n 𝕜)
    (hM : ∀ r c, ‖M r c‖ ≤ C r c) (hN : ∀ r c, ‖N r c‖ ≤ C r c)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖)
    (i j : n) :
    0 ≤ matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N i j :=
  (norm_nonneg _).trans (matrix_inv_entry_norm_sub_le M N hM hN hδpos hdetM hdetN i j)

/-- Elementwise matrix-norm Lipschitz constant for one inverse-matrix entry on an entrywise
bounded set with a determinant lower bound. -/
def matrixInvEntryMatrixNormLipschitzConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (C : n → n → ℝ) (i j : n) : ℝ :=
  δ⁻¹ * matrixAdjugateEntryLipschitzConst (A := 𝕜) C i j +
    ((δ⁻¹ * δ⁻¹) * matrixDetLipschitzConst (A := 𝕜) C) *
      matrixAdjugateEntryBoundConst (A := 𝕜) C i j

theorem matrixInvEntryMatrixNormLipschitzConst_nonneg {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} (hδpos : 0 < δ)
    (C : n → n → ℝ) (i j : n) :
    0 ≤ matrixInvEntryMatrixNormLipschitzConst (𝕜 := 𝕜) δ C i j := by
  exact add_nonneg
    (mul_nonneg (inv_nonneg.mpr hδpos.le)
      (matrixAdjugateEntryLipschitzConst_nonneg (A := 𝕜) C i j))
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (inv_nonneg.mpr hδpos.le) (inv_nonneg.mpr hδpos.le))
        (matrixDetLipschitzConst_nonneg (A := 𝕜) C))
      (matrixAdjugateEntryBoundConst_nonneg (A := 𝕜) C i j))

/-- Inverse-matrix entries are Lipschitz in the elementwise matrix norm on entrywise bounded
matrices whose determinants have a common positive lower bound. -/
theorem matrix_inv_entry_norm_sub_le_const_mul {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ} (M N : Matrix n n 𝕜)
    (hM : ∀ r c, ‖M r c‖ ≤ C r c) (hN : ∀ r c, ‖N r c‖ ≤ C r c)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖)
    (i j : n) :
    ‖M⁻¹ i j - N⁻¹ i j‖ ≤
      matrixInvEntryMatrixNormLipschitzConst (𝕜 := 𝕜) δ C i j * ‖M - N‖ := by
  have hinvδ_nonneg : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδpos.le
  have hadj_lip :
      ‖M.adjugate i j - N.adjugate i j‖ ≤
        matrixAdjugateEntryLipschitzConst (A := 𝕜) C i j * ‖M - N‖ :=
    matrix_adjugate_entry_norm_sub_le_const_mul M N hM hN i j
  have hdet_lip :
      ‖M.det - N.det‖ ≤ matrixDetLipschitzConst (A := 𝕜) C * ‖M - N‖ :=
    matrix_det_norm_sub_le_const_mul M N hM hN
  have hadj_boundN :
      ‖N.adjugate i j‖ ≤ matrixAdjugateEntryBoundConst (A := 𝕜) C i j :=
    matrix_adjugate_entry_norm_le (C := C) N hN i j
  have hinv_detM : ‖(M.det)⁻¹‖ ≤ δ⁻¹ := by
    have hnorm_pos : 0 < ‖M.det‖ := lt_of_lt_of_le hδpos hdetM
    rw [norm_inv]
    exact (inv_le_inv₀ hnorm_pos hδpos).2 hdetM
  have hdet_inv_lip :
      ‖(M.det)⁻¹ - (N.det)⁻¹‖ ≤ (δ⁻¹ * δ⁻¹) * ‖M.det - N.det‖ := by
    have hdist := (lipschitzOnWith_inv_of_norm_ge (𝕜 := 𝕜) hδpos).dist_le_mul
      M.det (show M.det ∈ {a : 𝕜 | δ ≤ ‖a‖} from hdetM)
      N.det (show N.det ∈ {a : 𝕜 | δ ≤ ‖a‖} from hdetN)
    change dist ((M.det)⁻¹) ((N.det)⁻¹) ≤
      (δ⁻¹ * δ⁻¹ : ℝ) * dist M.det N.det at hdist
    simpa [dist_eq_norm, mul_assoc] using hdist
  have hdet_inv_const :
      ‖(M.det)⁻¹ - (N.det)⁻¹‖ ≤
        (δ⁻¹ * δ⁻¹) * (matrixDetLipschitzConst (A := 𝕜) C * ‖M - N‖) :=
    hdet_inv_lip.trans
      (mul_le_mul_of_nonneg_left hdet_lip (mul_nonneg hinvδ_nonneg hinvδ_nonneg))
  have hfirst :
      ‖(M.det)⁻¹‖ * ‖M.adjugate i j - N.adjugate i j‖ ≤
        (δ⁻¹ * matrixAdjugateEntryLipschitzConst (A := 𝕜) C i j) * ‖M - N‖ := by
    calc
      ‖(M.det)⁻¹‖ * ‖M.adjugate i j - N.adjugate i j‖ ≤
          δ⁻¹ * (matrixAdjugateEntryLipschitzConst (A := 𝕜) C i j * ‖M - N‖) :=
        mul_le_mul hinv_detM hadj_lip (norm_nonneg _) hinvδ_nonneg
      _ = (δ⁻¹ * matrixAdjugateEntryLipschitzConst (A := 𝕜) C i j) * ‖M - N‖ := by
        ring
  have hsecond :
      ‖(M.det)⁻¹ - (N.det)⁻¹‖ * ‖N.adjugate i j‖ ≤
        (((δ⁻¹ * δ⁻¹) * matrixDetLipschitzConst (A := 𝕜) C) *
          matrixAdjugateEntryBoundConst (A := 𝕜) C i j) * ‖M - N‖ := by
    have hdet_rhs_nonneg :
        0 ≤ (δ⁻¹ * δ⁻¹) * (matrixDetLipschitzConst (A := 𝕜) C * ‖M - N‖) := by
      exact mul_nonneg (mul_nonneg hinvδ_nonneg hinvδ_nonneg)
        (mul_nonneg (matrixDetLipschitzConst_nonneg (A := 𝕜) C) (norm_nonneg _))
    calc
      ‖(M.det)⁻¹ - (N.det)⁻¹‖ * ‖N.adjugate i j‖ ≤
          ((δ⁻¹ * δ⁻¹) * (matrixDetLipschitzConst (A := 𝕜) C * ‖M - N‖)) *
            matrixAdjugateEntryBoundConst (A := 𝕜) C i j :=
        mul_le_mul hdet_inv_const hadj_boundN (norm_nonneg _) hdet_rhs_nonneg
      _ =
          (((δ⁻¹ * δ⁻¹) * matrixDetLipschitzConst (A := 𝕜) C) *
            matrixAdjugateEntryBoundConst (A := 𝕜) C i j) * ‖M - N‖ := by
        ring
  have hentry :
      M⁻¹ i j - N⁻¹ i j =
        (M.det)⁻¹ * M.adjugate i j - (N.det)⁻¹ * N.adjugate i j := by
    rw [Matrix.inv_def, Matrix.inv_def, Ring.inverse_eq_inv, Ring.inverse_eq_inv]
    rfl
  have hsplit :
      (M.det)⁻¹ * M.adjugate i j - (N.det)⁻¹ * N.adjugate i j =
        (M.det)⁻¹ * (M.adjugate i j - N.adjugate i j) +
          ((M.det)⁻¹ - (N.det)⁻¹) * N.adjugate i j := by
    ring
  calc
    ‖M⁻¹ i j - N⁻¹ i j‖ =
        ‖(M.det)⁻¹ * M.adjugate i j - (N.det)⁻¹ * N.adjugate i j‖ := by
      rw [hentry]
    _ =
        ‖(M.det)⁻¹ * (M.adjugate i j - N.adjugate i j) +
          ((M.det)⁻¹ - (N.det)⁻¹) * N.adjugate i j‖ := by
      rw [hsplit]
    _ ≤
        ‖(M.det)⁻¹ * (M.adjugate i j - N.adjugate i j)‖ +
          ‖((M.det)⁻¹ - (N.det)⁻¹) * N.adjugate i j‖ :=
      norm_add_le _ _
    _ ≤
        ‖(M.det)⁻¹‖ * ‖M.adjugate i j - N.adjugate i j‖ +
          (‖(M.det)⁻¹ - (N.det)⁻¹‖ * ‖N.adjugate i j‖) :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤
        (δ⁻¹ * matrixAdjugateEntryLipschitzConst (A := 𝕜) C i j) * ‖M - N‖ +
          (((δ⁻¹ * δ⁻¹) * matrixDetLipschitzConst (A := 𝕜) C) *
            matrixAdjugateEntryBoundConst (A := 𝕜) C i j) * ‖M - N‖ :=
      add_le_add hfirst hsecond
    _ =
        matrixInvEntryMatrixNormLipschitzConst (𝕜 := 𝕜) δ C i j * ‖M - N‖ := by
      simp [matrixInvEntryMatrixNormLipschitzConst]
      ring

/-- Elementwise matrix-norm Lipschitz constant for finite matrix inversion on an entrywise bounded
set with a determinant lower bound. -/
def matrixInvMatrixNormLipschitzConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (C : n → n → ℝ) : ℝ :=
  ∑ i : n, ∑ j : n, matrixInvEntryMatrixNormLipschitzConst (𝕜 := 𝕜) δ C i j

theorem matrixInvMatrixNormLipschitzConst_nonneg {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} (hδpos : 0 < δ) (C : n → n → ℝ) :
    0 ≤ matrixInvMatrixNormLipschitzConst (𝕜 := 𝕜) δ C := by
  exact Finset.sum_nonneg fun i _hi =>
    Finset.sum_nonneg fun j _hj =>
      matrixInvEntryMatrixNormLipschitzConst_nonneg (𝕜 := 𝕜) hδpos C i j

/-- Finite matrix inversion is Lipschitz in the elementwise matrix norm on entrywise bounded
matrices whose determinants have a common positive lower bound. -/
theorem matrix_inv_norm_sub_le_const_mul {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ} (M N : Matrix n n 𝕜)
    (hM : ∀ r c, ‖M r c‖ ≤ C r c) (hN : ∀ r c, ‖N r c‖ ≤ C r c)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖) :
    ‖M⁻¹ - N⁻¹‖ ≤ matrixInvMatrixNormLipschitzConst (𝕜 := 𝕜) δ C * ‖M - N‖ := by
  classical
  let entryConst : n → n → ℝ :=
    fun i j => matrixInvEntryMatrixNormLipschitzConst (𝕜 := 𝕜) δ C i j
  let entryBound : n → n → ℝ := fun i j => entryConst i j * ‖M - N‖
  have hentry : ∀ i j, ‖M⁻¹ i j - N⁻¹ i j‖ ≤ entryBound i j := by
    intro i j
    simpa [entryBound, entryConst] using
      matrix_inv_entry_norm_sub_le_const_mul M N hM hN hδpos hdetM hdetN i j
  have hentry_nonneg : ∀ i j, 0 ≤ entryBound i j := by
    intro i j
    exact mul_nonneg
      (matrixInvEntryMatrixNormLipschitzConst_nonneg (𝕜 := 𝕜) hδpos C i j)
      (norm_nonneg _)
  have hrow_nonneg : ∀ i, 0 ≤ ∑ j : n, entryBound i j := by
    intro i
    exact Finset.sum_nonneg fun j _hj => hentry_nonneg i j
  have htotal_nonneg : 0 ≤ ∑ i : n, ∑ j : n, entryBound i j :=
    Finset.sum_nonneg fun i _hi => hrow_nonneg i
  have hnorm : ‖M⁻¹ - N⁻¹‖ ≤ ∑ i : n, ∑ j : n, entryBound i j := by
    refine (Matrix.norm_le_iff htotal_nonneg).2 ?_
    intro i j
    calc
      ‖(M⁻¹ - N⁻¹) i j‖ = ‖M⁻¹ i j - N⁻¹ i j‖ := rfl
      _ ≤ entryBound i j := hentry i j
      _ ≤ ∑ j : n, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hentry_nonneg i k) (Finset.mem_univ j)
      _ ≤ ∑ i : n, ∑ j : n, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hrow_nonneg k) (Finset.mem_univ i)
  calc
    ‖M⁻¹ - N⁻¹‖ ≤ ∑ i : n, ∑ j : n, entryBound i j := hnorm
    _ = matrixInvMatrixNormLipschitzConst (𝕜 := 𝕜) δ C * ‖M - N‖ := by
      simp [entryBound, entryConst, matrixInvMatrixNormLipschitzConst, Finset.sum_mul]

/-- Matrix inversion is bounded-difference controlled on a time-space set by a uniform matrix
difference bound and a common determinant lower bound. -/
theorem matrix_inv_bounded_sub_le_const_mul {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ} {η : ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    (hM : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ i j, ‖M z i j‖ ≤ C i j)
    (hN : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ i j, ‖N z i j‖ ≤ C i j)
    (hdiff : ∀ ⦃z : ℝ × X⦄, z ∈ s → ‖M z - N z‖ ≤ η)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicBoundedWith (matrixInvMatrixNormLipschitzConst (𝕜 := 𝕜) δ C * η)
      (fun z : ℝ × X => (M z)⁻¹ - (N z)⁻¹) s := by
  intro z hz
  exact (matrix_inv_norm_sub_le_const_mul (δ := δ) (C := C)
      (M z) (N z) (hM hz) (hN hz) hδpos (hdetM hz) (hdetN hz)).trans
    (mul_le_mul_of_nonneg_left (hdiff hz)
      (matrixInvMatrixNormLipschitzConst_nonneg (𝕜 := 𝕜) hδpos C))

/-- Compact-domain version of `matrix_inv_bounded_sub_le_const_mul`: pointwise nonvanishing of
both determinants supplies a common lower bound. -/
theorem matrix_inv_bounded_sub_le_const_mul_of_isCompact_det_ne_zero {n 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)}
    {C : n → n → ℝ} {η : ℝ} {M N : ℝ × X → Matrix n n 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hMctrl : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) K)
    (hNctrl : ∀ i j, ParabolicC0AlphaOn α (fun z => N z i j) K)
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (N z).det ≠ 0)
    (hM : ∀ ⦃z : ℝ × X⦄, z ∈ K → ∀ i j, ‖M z i j‖ ≤ C i j)
    (hN : ∀ ⦃z : ℝ × X⦄, z ∈ K → ∀ i j, ‖N z i j‖ ≤ C i j)
    (hdiff : ∀ ⦃z : ℝ × X⦄, z ∈ K → ‖M z - N z‖ ≤ η) :
    ∃ δ > 0,
      ParabolicBoundedWith (matrixInvMatrixNormLipschitzConst (𝕜 := 𝕜) δ C * η)
        (fun z : ℝ × X => (M z)⁻¹ - (N z)⁻¹) K := by
  rcases matrix_det_pair_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) (N := N) hK hα hMctrl hNctrl hdetM_ne hdetN_ne with
    ⟨δ, hδpos, hdetM, hdetN⟩
  refine ⟨δ, hδpos, ?_⟩
  exact matrix_inv_bounded_sub_le_const_mul
    (s := K) (δ := δ) (C := C) (η := η) hM hN hdiff hδpos hdetM hdetN

/-- Finite matrix inversion is pointwise Lipschitz in the elementwise matrix norm on entrywise
bounded matrices whose determinants have a common positive lower bound. -/
theorem matrix_inv_norm_sub_le {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ} (M N : Matrix n n 𝕜)
    (hM : ∀ r c, ‖M r c‖ ≤ C r c) (hN : ∀ r c, ‖N r c‖ ≤ C r c)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖) :
    ‖M⁻¹ - N⁻¹‖ ≤
      ∑ i : n, ∑ j : n, matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N i j := by
  classical
  let entryBound : n → n → ℝ :=
    fun i j => matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N i j
  have hentry : ∀ i j, ‖M⁻¹ i j - N⁻¹ i j‖ ≤ entryBound i j := by
    intro i j
    simpa [entryBound] using matrix_inv_entry_norm_sub_le M N hM hN hδpos hdetM hdetN i j
  have hentry_nonneg : ∀ i j, 0 ≤ entryBound i j := by
    intro i j
    exact (norm_nonneg _).trans (hentry i j)
  have hrow_nonneg : ∀ i, 0 ≤ ∑ j : n, entryBound i j := by
    intro i
    exact Finset.sum_nonneg fun j _hj => hentry_nonneg i j
  have htotal_nonneg : 0 ≤ ∑ i : n, ∑ j : n, entryBound i j :=
    Finset.sum_nonneg fun i _hi => hrow_nonneg i
  have hnorm :
      ‖M⁻¹ - N⁻¹‖ ≤ ∑ i : n, ∑ j : n, entryBound i j := by
    refine (Matrix.norm_le_iff htotal_nonneg).2 ?_
    intro i j
    calc
      ‖(M⁻¹ - N⁻¹) i j‖ = ‖M⁻¹ i j - N⁻¹ i j‖ := rfl
      _ ≤ entryBound i j := hentry i j
      _ ≤ ∑ j : n, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hentry_nonneg i k) (Finset.mem_univ j)
      _ ≤ ∑ i : n, ∑ j : n, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hrow_nonneg k) (Finset.mem_univ i)
  simpa [entryBound] using hnorm

/-- Inverse-matrix entries are pointwise bounded by the quantitative inverse-entry constant. -/
theorem matrix_inv_entry_norm_le {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ} (M : Matrix n n 𝕜)
    (hM : ∀ r c, ‖M r c‖ ≤ C r c)
    (hδpos : 0 < δ) (hdet : δ ≤ ‖M.det‖) (i j : n) :
    ‖M⁻¹ i j‖ ≤ matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i j := by
  have hinvδ_nonneg : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδpos.le
  have hadj_bound :
      ‖M.adjugate i j‖ ≤ matrixAdjugateEntryBoundConst (A := 𝕜) C i j :=
    matrix_adjugate_entry_norm_le (C := C) M hM i j
  have hinv_det : ‖(M.det)⁻¹‖ ≤ δ⁻¹ := by
    have hnorm_pos : 0 < ‖M.det‖ := lt_of_lt_of_le hδpos hdet
    rw [norm_inv]
    exact (inv_le_inv₀ hnorm_pos hδpos).2 hdet
  have hentry :
      M⁻¹ i j = (M.det)⁻¹ * M.adjugate i j := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv]
    rfl
  calc
    ‖M⁻¹ i j‖ = ‖(M.det)⁻¹ * M.adjugate i j‖ := by rw [hentry]
    _ ≤ ‖(M.det)⁻¹‖ * ‖M.adjugate i j‖ := norm_mul_le _ _
    _ ≤ δ⁻¹ * matrixAdjugateEntryBoundConst (A := 𝕜) C i j :=
      mul_le_mul hinv_det hadj_bound (norm_nonneg _) hinvδ_nonneg
    _ = matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i j := by
      rfl

/-- Each inverse-matrix entry has an explicit bounded parabolic `C^{0,α}` estimate when the matrix
entries do and the determinant is uniformly bounded away from zero on the domain. -/
theorem matrix_inv_entry_with {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {B H : n → n → ℝ} {δ : ℝ} {M : ℝ × X → Matrix n n 𝕜}
    (hH : ∀ i j, 0 ≤ H i j)
    (hM : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => M z i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (i j : n) :
    ParabolicC0AlphaWith
      (matrixInvEntryBoundConst (𝕜 := 𝕜) δ B i j)
      (matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H i j)
      α (fun z => (M z)⁻¹ i j) s := by
  have hdet_with :
      ParabolicC0AlphaWith
        (matrixDetBoundConst (A := 𝕜) B) (matrixDetHolderConst (A := 𝕜) B H)
        α (fun z => (M z).det) s :=
    matrix_det_with (M := M) hH hM
  have hdet_inv :
      ParabolicC0AlphaWith δ⁻¹
        (δ⁻¹ * matrixDetHolderConst (A := 𝕜) B H * δ⁻¹)
        α (fun z => ((M z).det)⁻¹) s :=
    hdet_with.inv hδpos hdet
  have hadj :
    ParabolicC0AlphaWith
      (matrixAdjugateEntryBoundConst (A := 𝕜) B i j)
      (matrixAdjugateEntryHolderConst (A := 𝕜) B H i j)
      α (fun z => (M z).adjugate i j) s :=
    matrix_adjugate_entry_with (M := M) hH hM i j
  have hprod := hdet_inv.mul hadj (inv_nonneg.mpr hδpos.le)
  convert hprod using 1 <;>
    first
    | rfl
    | (funext z
       rw [Matrix.inv_def, Ring.inverse_eq_inv]
       rfl)

/-- One inverse-matrix entry has existential difference-based parabolic `C^{0,α}` control when
the two matrices have entrywise controls and a common determinant lower bound. -/
theorem matrix_inv_entry_sub {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {δ : ℝ} {M N : ℝ × X → Matrix n n 𝕜}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s)
    (hN : ∀ i j, ParabolicC0AlphaOn α (fun z => N z i j) s)
    (hdiff : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j - N z i j) s)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖)
    (i j : n) :
    ParabolicC0AlphaOn α (fun z => (M z)⁻¹ i j - (N z)⁻¹ i j) s := by
  have hdetM_inv :
      ParabolicC0AlphaOn α (fun z => ((M z).det)⁻¹) s :=
    (matrix_det (M := M) hM).inv hδpos hdetM
  have hdet_inv_diff :
      ParabolicC0AlphaOn α (fun z => ((M z).det)⁻¹ - ((N z).det)⁻¹) s :=
    matrix_det_inv_sub (M := M) (N := N) hM hN hdiff hδpos hdetM hdetN
  have hNadj :
      ParabolicC0AlphaOn α (fun z => (N z).adjugate i j) s :=
    matrix_adjugate_entry (M := N) hN i j
  have hadjdiff :
      ParabolicC0AlphaOn α (fun z => (M z).adjugate i j - (N z).adjugate i j) s :=
    matrix_adjugate_entry_sub (M := M) (N := N) hM hN hdiff i j
  have hprod :
      ParabolicC0AlphaOn α
        (fun z =>
          ((M z).det)⁻¹ * (M z).adjugate i j -
            ((N z).det)⁻¹ * (N z).adjugate i j) s :=
    hdetM_inv.mul_sub_mul hNadj hdet_inv_diff hadjdiff
  convert hprod using 1
  ext z
  rw [Matrix.inv_def, Matrix.inv_def, Ring.inverse_eq_inv, Ring.inverse_eq_inv]
  rfl

/-- One inverse-matrix entry has difference-based parabolic `C^{0,α}` control when the two
matrices have entrywise controls and a common determinant lower bound. -/
theorem matrix_inv_entry_sub_with {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {B H Bd Hd : n → n → ℝ} {δ : ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    (hH : ∀ i j, 0 ≤ H i j)
    (hBd : ∀ i j, 0 ≤ Bd i j)
    (hHd : ∀ i j, 0 ≤ Hd i j)
    (hM : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => M z i j) s)
    (hN : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => N z i j) s)
    (hdiff : ∀ i j,
      ParabolicC0AlphaWith (Bd i j) (Hd i j) α (fun z => M z i j - N z i j) s)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖)
    (i j : n) :
    ParabolicC0AlphaWith
      (matrixInvEntrySubBoundConst (𝕜 := 𝕜) δ B Bd i j)
      (matrixInvEntrySubHolderConst (𝕜 := 𝕜) δ B H Bd Hd i j)
      α (fun z => (M z)⁻¹ i j - (N z)⁻¹ i j) s := by
  have hdetM_with :
      ParabolicC0AlphaWith
        (matrixDetBoundConst (A := 𝕜) B)
        (matrixDetHolderConst (A := 𝕜) B H)
        α (fun z => (M z).det) s :=
    matrix_det_with (M := M) hH hM
  have hdetM_inv :
      ParabolicC0AlphaWith δ⁻¹
        (δ⁻¹ * matrixDetHolderConst (A := 𝕜) B H * δ⁻¹)
        α (fun z => ((M z).det)⁻¹) s :=
    hdetM_with.inv hδpos hdetM
  have hdet_inv_diff :
      ParabolicC0AlphaWith
        (matrixDetInvSubBoundConst (𝕜 := 𝕜) δ B Bd)
        (matrixDetInvSubHolderConst (𝕜 := 𝕜) δ B H Bd Hd)
        α (fun z => ((M z).det)⁻¹ - ((N z).det)⁻¹) s :=
    matrix_det_inv_sub_with (M := M) (N := N)
      hH hBd hHd hM hN hdiff hδpos hdetM hdetN
  have hNadj :
      ParabolicC0AlphaWith
        (matrixAdjugateEntryBoundConst (A := 𝕜) B i j)
        (matrixAdjugateEntryHolderConst (A := 𝕜) B H i j)
        α (fun z => (N z).adjugate i j) s :=
    matrix_adjugate_entry_with (M := N) hH hN i j
  have hadjdiff :
      ParabolicC0AlphaWith
        (matrixAdjugateEntrySubBoundConst (A := 𝕜) B Bd i j)
        (matrixAdjugateEntrySubHolderConst (A := 𝕜) B H Bd Hd i j)
        α (fun z => (M z).adjugate i j - (N z).adjugate i j) s :=
    matrix_adjugate_entry_sub_with (M := M) (N := N) hH hBd hHd hM hN hdiff i j
  have hprod :
      ParabolicC0AlphaWith
        (matrixInvEntrySubBoundConst (𝕜 := 𝕜) δ B Bd i j)
        (matrixInvEntrySubHolderConst (𝕜 := 𝕜) δ B H Bd Hd i j)
        α
        (fun z =>
          ((M z).det)⁻¹ * (M z).adjugate i j -
            ((N z).det)⁻¹ * (N z).adjugate i j) s := by
    simpa [matrixInvEntrySubBoundConst, matrixInvEntrySubHolderConst] using
      hdetM_inv.mul_sub_mul hNadj hdet_inv_diff hadjdiff
        (inv_nonneg.mpr hδpos.le)
        (matrixDetInvSubBoundConst_nonneg (𝕜 := 𝕜) hδpos hBd)
  convert hprod using 1
  ext z
  rw [Matrix.inv_def, Matrix.inv_def, Ring.inverse_eq_inv, Ring.inverse_eq_inv]
  rfl

/-- Finite inverse-matrix differences have entrywise-difference-based parabolic `C^{0,α}`
control under a common determinant lower bound. -/
theorem matrix_inv_sub_with_entrywise {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {B H Bd Hd : n → n → ℝ} {δ : ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    (hH : ∀ i j, 0 ≤ H i j)
    (hBd : ∀ i j, 0 ≤ Bd i j)
    (hHd : ∀ i j, 0 ≤ Hd i j)
    (hM : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => M z i j) s)
    (hN : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => N z i j) s)
    (hdiff : ∀ i j,
      ParabolicC0AlphaWith (Bd i j) (Hd i j) α (fun z => M z i j - N z i j) s)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicC0AlphaWith
      (matrixInvEntrywiseSubBoundConst (𝕜 := 𝕜) δ B Bd)
      (matrixInvEntrywiseSubHolderConst (𝕜 := 𝕜) δ B H Bd Hd)
      α (fun z => (M z)⁻¹ - (N z)⁻¹) s := by
  refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
  · intro i
    exact Finset.sum_nonneg fun j _hj =>
      matrixInvEntrySubBoundConst_nonneg (𝕜 := 𝕜) hδpos hBd i j
  · intro i
    exact Finset.sum_nonneg fun j _hj =>
      matrixInvEntrySubHolderConst_nonneg (𝕜 := 𝕜) hδpos hH hBd hHd i j
  · intro i
    refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
    · intro j
      exact matrixInvEntrySubBoundConst_nonneg (𝕜 := 𝕜) hδpos hBd i j
    · intro j
      exact matrixInvEntrySubHolderConst_nonneg (𝕜 := 𝕜) hδpos hH hBd hHd i j
    · intro j
      exact matrix_inv_entry_sub_with (M := M) (N := N)
        hH hBd hHd hM hN hdiff hδpos hdetM hdetN i j

/-- A finite inverse-matrix-valued function has an explicit bounded parabolic `C^{0,α}` estimate
when the matrix entries do and the determinant is uniformly bounded away from zero. -/
theorem matrix_inv_with {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {B H : n → n → ℝ} {δ : ℝ} {M : ℝ × X → Matrix n n 𝕜}
    (hH : ∀ i j, 0 ≤ H i j)
    (hM : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => M z i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaWith
      (∑ i : n, ∑ j : n, matrixInvEntryBoundConst (𝕜 := 𝕜) δ B i j)
      (∑ i : n, ∑ j : n, matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H i j)
      α (fun z => (M z)⁻¹) s := by
  refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
  · intro i
    exact Finset.sum_nonneg fun j _hj => matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos B i j
  · intro i
    exact Finset.sum_nonneg fun j _hj => matrixInvEntryHolderConst_nonneg (𝕜 := 𝕜) hH hδpos i j
  · intro i
    refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
    · intro j
      exact matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos B i j
    · intro j
      exact matrixInvEntryHolderConst_nonneg (𝕜 := 𝕜) hH hδpos i j
    · intro j
      exact matrix_inv_entry_with (M := M) hH hM hδpos hdet i j

end ParabolicC0AlphaOn

namespace ParabolicC0AlphaNormLe

variable {X : Type*} [PseudoMetricSpace X]
variable {α : ℝ} {s : Set (ℝ × X)}

/-- Entrywise single-radius control and a determinant lower bound package inverse matrices with
the corresponding quantitative inverse-matrix radius. -/
theorem matrix_inv_of_entries {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {R : n → n → ℝ} {δ : ℝ} {M : ℝ × X → Matrix n n 𝕜}
    (hM : ∀ i j, ParabolicC0AlphaNormLe (R i j) α (fun z => M z i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaNormLe
      ((∑ i : n, ∑ j : n, ParabolicC0AlphaOn.matrixInvEntryBoundConst
          (𝕜 := 𝕜) δ R i j) +
        (∑ i : n, ∑ j : n, ParabolicC0AlphaOn.matrixInvEntryHolderConst
          (𝕜 := 𝕜) δ R R i j))
      α (fun z => (M z)⁻¹) s := by
  have hR : ∀ i j, 0 ≤ R i j := fun i j => (hM i j).nonneg
  exact ParabolicC0AlphaNormLe.of_c0AlphaWith
    (Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj =>
        ParabolicC0AlphaOn.matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos R i j)
    (Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj =>
        ParabolicC0AlphaOn.matrixInvEntryHolderConst_nonneg (𝕜 := 𝕜) hR hδpos i j)
    (ParabolicC0AlphaOn.matrix_inv_with (M := M) (B := R) (H := R) (δ := δ)
      hR (fun i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hM i j))
      hδpos hdet)

/-- Entrywise single-radius control of two matrices and their difference, plus a common
determinant lower bound, packages inverse-matrix differences with the corresponding quantitative
inverse-difference radius. -/
theorem matrix_inv_sub_of_entries {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {R Rd : n → n → ℝ} {δ : ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    (hM : ∀ i j, ParabolicC0AlphaNormLe (R i j) α (fun z => M z i j) s)
    (hN : ∀ i j, ParabolicC0AlphaNormLe (R i j) α (fun z => N z i j) s)
    (hdiff : ∀ i j, ParabolicC0AlphaNormLe (Rd i j) α
      (fun z => M z i j - N z i j) s)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicC0AlphaNormLe
      (ParabolicC0AlphaOn.matrixInvEntrywiseSubBoundConst (𝕜 := 𝕜) δ R Rd +
        ParabolicC0AlphaOn.matrixInvEntrywiseSubHolderConst (𝕜 := 𝕜) δ R R Rd Rd)
      α (fun z => (M z)⁻¹ - (N z)⁻¹) s := by
  have hR : ∀ i j, 0 ≤ R i j := fun i j => (hM i j).nonneg
  have hRd : ∀ i j, 0 ≤ Rd i j := fun i j => (hdiff i j).nonneg
  exact ParabolicC0AlphaNormLe.of_c0AlphaWith
    (ParabolicC0AlphaOn.matrixInvEntrywiseSubBoundConst_nonneg (𝕜 := 𝕜) hδpos hRd)
    (ParabolicC0AlphaOn.matrixInvEntrywiseSubHolderConst_nonneg
      (𝕜 := 𝕜) hδpos hR hRd hRd)
    (ParabolicC0AlphaOn.matrix_inv_sub_with_entrywise
      (M := M) (N := N) (B := R) (H := R) (Bd := Rd) (Hd := Rd)
      hR hRd hRd
      (fun i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hM i j))
      (fun i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hN i j))
      (fun i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hdiff i j))
      hδpos hdetM hdetN)

end ParabolicC0AlphaNormLe

namespace ParabolicC0AlphaOn

variable {X : Type*} [PseudoMetricSpace X]
variable {α : ℝ} {s : Set (ℝ × X)}

/-- A finite family of inverse-matrix-valued functions has explicit bounded parabolic
`C^{0,α}` estimates with one compact determinant lower bound shared by the whole family. -/
theorem matrix_inv_family_with_of_isCompact_det_ne_zero {ι n 𝕜 : Type*} [Fintype ι]
    [Fintype n] [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)}
    {B H : ι → n → n → ℝ} {M : ι → ℝ × X → Matrix n n 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hB : ∀ a i j, 0 ≤ B a i j) (hH : ∀ a i j, 0 ≤ H a i j)
    (hM : ∀ a i j,
      ParabolicC0AlphaWith (B a i j) (H a i j) α (fun z => M a z i j) K)
    (hdet_ne : ∀ a ⦃z : ℝ × X⦄, z ∈ K → (M a z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ a ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M a z).det‖) ∧
      ∀ a,
        ParabolicC0AlphaWith
          (∑ i : n, ∑ j : n, matrixInvEntryBoundConst (𝕜 := 𝕜) δ (B a) i j)
          (∑ i : n, ∑ j : n, matrixInvEntryHolderConst (𝕜 := 𝕜) δ (B a) (H a) i j)
          α (fun z => (M a z)⁻¹) K := by
  have hMctrl : ∀ a i j, ParabolicC0AlphaOn α (fun z => M a z i j) K := by
    intro a i j
    exact ⟨B a i j, hB a i j, H a i j, hH a i j, hM a i j⟩
  rcases matrix_det_family_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hMctrl hdet_ne with
    ⟨δ, hδpos, hdet⟩
  refine ⟨δ, hδpos, hdet, ?_⟩
  intro a
  exact matrix_inv_with (M := M a) (B := B a) (H := H a) (δ := δ)
    (hH a) (hM a) hδpos (hdet a)

/-- Sup constant for the difference of two inverse finite-matrix fields, using a uniform
matrix-difference bound. -/
def matrixInvSubBoundConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    (δ : ℝ) (B : n → n → ℝ) (η : ℝ) : ℝ :=
  matrixInvMatrixNormLipschitzConst (𝕜 := 𝕜) δ B * η

/-- Holder constant for the difference of two inverse finite-matrix fields, using the sum of the
two inverse Holder constants. -/
def matrixInvSubHolderConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    (δ : ℝ) (B H : n → n → ℝ) : ℝ :=
  (∑ i : n, ∑ j : n, matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H i j) +
    (∑ i : n, ∑ j : n, matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H i j)

theorem matrixInvSubBoundConst_nonneg {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ η : ℝ} {B : n → n → ℝ}
    (hδpos : 0 < δ) (hη : 0 ≤ η) :
    0 ≤ matrixInvSubBoundConst (𝕜 := 𝕜) δ B η := by
  exact mul_nonneg (matrixInvMatrixNormLipschitzConst_nonneg (𝕜 := 𝕜) hδpos B) hη

theorem matrixInvSubHolderConst_nonneg {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {B H : n → n → ℝ}
    (hH : ∀ i j, 0 ≤ H i j) (hδpos : 0 < δ) :
    0 ≤ matrixInvSubHolderConst (𝕜 := 𝕜) δ B H := by
  exact add_nonneg
    (Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj =>
        matrixInvEntryHolderConst_nonneg (𝕜 := 𝕜) hH hδpos i j)
    (Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj =>
        matrixInvEntryHolderConst_nonneg (𝕜 := 𝕜) hH hδpos i j)

/-- The difference of two inverse finite-matrix fields has parabolic `C^{0,α}` control: the sup
constant uses the inverse Lipschitz bound, while the Holder constant is the sum of the two inverse
Holder constants. -/
theorem matrix_inv_sub_with {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {B H : n → n → ℝ} {δ η : ℝ} {M N : ℝ × X → Matrix n n 𝕜}
    (hH : ∀ i j, 0 ≤ H i j)
    (hM : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => M z i j) s)
    (hN : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => N z i j) s)
    (hdiff : ∀ ⦃z : ℝ × X⦄, z ∈ s → ‖M z - N z‖ ≤ η)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicC0AlphaWith
      (matrixInvSubBoundConst (𝕜 := 𝕜) δ B η)
      (matrixInvSubHolderConst (𝕜 := 𝕜) δ B H)
      α (fun z => (M z)⁻¹ - (N z)⁻¹) s := by
  have hbounded :
      ParabolicBoundedWith (matrixInvSubBoundConst (𝕜 := 𝕜) δ B η)
        (fun z : ℝ × X => (M z)⁻¹ - (N z)⁻¹) s := by
    simpa [matrixInvSubBoundConst] using
      (matrix_inv_bounded_sub_le_const_mul
        (s := s) (δ := δ) (C := B) (η := η)
        (M := M) (N := N)
        (by
          intro z hz i j
          exact (hM i j).bounded hz)
        (by
          intro z hz i j
          exact (hN i j).bounded hz)
        hdiff hδpos hdetM hdetN)
  have hMinv := matrix_inv_with (M := M) hH hM hδpos hdetM
  have hNinv := matrix_inv_with (M := N) hH hN hδpos hdetN
  exact ⟨hbounded, by
    simpa [matrixInvSubHolderConst] using hMinv.holder.sub hNinv.holder⟩

/-- Compact-domain version of `matrix_inv_sub_with`: pointwise nonvanishing of both determinants
supplies one common determinant lower bound. -/
theorem matrix_inv_sub_with_of_isCompact_det_ne_zero {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)}
    {B H : n → n → ℝ} {η : ℝ} {M N : ℝ × X → Matrix n n 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hB : ∀ i j, 0 ≤ B i j) (hH : ∀ i j, 0 ≤ H i j)
    (hM : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => M z i j) K)
    (hN : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => N z i j) K)
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (N z).det ≠ 0)
    (hdiff : ∀ ⦃z : ℝ × X⦄, z ∈ K → ‖M z - N z‖ ≤ η) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvSubBoundConst (𝕜 := 𝕜) δ B η)
        (matrixInvSubHolderConst (𝕜 := 𝕜) δ B H)
        α (fun z : ℝ × X => (M z)⁻¹ - (N z)⁻¹) K := by
  have hMctrl : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) K := by
    intro i j
    exact ⟨B i j, hB i j, H i j, hH i j, hM i j⟩
  have hNctrl : ∀ i j, ParabolicC0AlphaOn α (fun z => N z i j) K := by
    intro i j
    exact ⟨B i j, hB i j, H i j, hH i j, hN i j⟩
  rcases matrix_det_pair_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) (N := N) hK hα hMctrl hNctrl hdetM_ne hdetN_ne with
    ⟨δ, hδpos, hdetM, hdetN⟩
  exact ⟨δ, hδpos, matrix_inv_sub_with (M := M) (N := N)
    hH hM hN hdiff hδpos hdetM hdetN⟩

/-- Compact-domain version of `matrix_inv_sub_with_entrywise`: pointwise nonvanishing of both
determinants supplies one common determinant lower bound. -/
theorem matrix_inv_sub_with_entrywise_of_isCompact_det_ne_zero {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)}
    {B H Bd Hd : n → n → ℝ} {M N : ℝ × X → Matrix n n 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hB : ∀ i j, 0 ≤ B i j) (hH : ∀ i j, 0 ≤ H i j)
    (hBd : ∀ i j, 0 ≤ Bd i j) (hHd : ∀ i j, 0 ≤ Hd i j)
    (hM : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => M z i j) K)
    (hN : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => N z i j) K)
    (hdiff : ∀ i j,
      ParabolicC0AlphaWith (Bd i j) (Hd i j) α (fun z => M z i j - N z i j) K)
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (N z).det ≠ 0) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvEntrywiseSubBoundConst (𝕜 := 𝕜) δ B Bd)
        (matrixInvEntrywiseSubHolderConst (𝕜 := 𝕜) δ B H Bd Hd)
        α (fun z : ℝ × X => (M z)⁻¹ - (N z)⁻¹) K := by
  have hMctrl : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) K := by
    intro i j
    exact ⟨B i j, hB i j, H i j, hH i j, hM i j⟩
  have hNctrl : ∀ i j, ParabolicC0AlphaOn α (fun z => N z i j) K := by
    intro i j
    exact ⟨B i j, hB i j, H i j, hH i j, hN i j⟩
  rcases matrix_det_pair_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) (N := N) hK hα hMctrl hNctrl hdetM_ne hdetN_ne with
    ⟨δ, hδpos, hdetM, hdetN⟩
  exact ⟨δ, hδpos, matrix_inv_sub_with_entrywise (M := M) (N := N)
    hH hBd hHd hM hN hdiff hδpos hdetM hdetN⟩

/-- Compact-domain finite-family version of `matrix_inv_sub_with`: pointwise nonvanishing of
all determinants supplies one determinant lower bound shared by both matrix families. -/
theorem matrix_inv_sub_with_family_of_isCompact_det_ne_zero {ι n 𝕜 : Type*} [Fintype ι]
    [Fintype n] [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)}
    {B H : ι → n → n → ℝ} {η : ι → ℝ}
    {M N : ι → ℝ × X → Matrix n n 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hB : ∀ r i j, 0 ≤ B r i j) (hH : ∀ r i j, 0 ≤ H r i j)
    (hM : ∀ r i j,
      ParabolicC0AlphaWith (B r i j) (H r i j) α (fun z => M r z i j) K)
    (hN : ∀ r i j,
      ParabolicC0AlphaWith (B r i j) (H r i j) α (fun z => N r z i j) K)
    (hdetM_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (M r z).det ≠ 0)
    (hdetN_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (N r z).det ≠ 0)
    (hdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ K → ‖M r z - N r z‖ ≤ η r) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M r z).det‖) ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(N r z).det‖) ∧
      ∀ r,
        ParabolicC0AlphaWith
          (matrixInvSubBoundConst (𝕜 := 𝕜) δ (B r) (η r))
          (matrixInvSubHolderConst (𝕜 := 𝕜) δ (B r) (H r))
          α (fun z : ℝ × X => (M r z)⁻¹ - (N r z)⁻¹) K := by
  have hMctrl : ∀ r i j, ParabolicC0AlphaOn α (fun z => M r z i j) K := by
    intro r i j
    exact ⟨B r i j, hB r i j, H r i j, hH r i j, hM r i j⟩
  have hNctrl : ∀ r i j, ParabolicC0AlphaOn α (fun z => N r z i j) K := by
    intro r i j
    exact ⟨B r i j, hB r i j, H r i j, hH r i j, hN r i j⟩
  rcases matrix_det_pair_family_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) (N := N) hK hα hMctrl hNctrl hdetM_ne hdetN_ne with
    ⟨δ, hδpos, hdetM, hdetN⟩
  refine ⟨δ, hδpos, hdetM, hdetN, ?_⟩
  intro r
  exact matrix_inv_sub_with (M := M r) (N := N r)
    (hH r) (hM r) (hN r) (hdiff r) hδpos (hdetM r) (hdetN r)

/-- Compact-domain finite-family version of `matrix_inv_sub_with_entrywise`: pointwise
nonvanishing of all determinants supplies one determinant lower bound shared by both matrix
families. -/
theorem matrix_inv_sub_with_entrywise_family_of_isCompact_det_ne_zero {ι n 𝕜 : Type*}
    [Fintype ι] [Fintype n] [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)}
    {B H Bd Hd : ι → n → n → ℝ} {M N : ι → ℝ × X → Matrix n n 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hB : ∀ r i j, 0 ≤ B r i j) (hH : ∀ r i j, 0 ≤ H r i j)
    (hBd : ∀ r i j, 0 ≤ Bd r i j) (hHd : ∀ r i j, 0 ≤ Hd r i j)
    (hM : ∀ r i j,
      ParabolicC0AlphaWith (B r i j) (H r i j) α (fun z => M r z i j) K)
    (hN : ∀ r i j,
      ParabolicC0AlphaWith (B r i j) (H r i j) α (fun z => N r z i j) K)
    (hdiff : ∀ r i j,
      ParabolicC0AlphaWith (Bd r i j) (Hd r i j) α
        (fun z => M r z i j - N r z i j) K)
    (hdetM_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (M r z).det ≠ 0)
    (hdetN_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (N r z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M r z).det‖) ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(N r z).det‖) ∧
      ∀ r,
        ParabolicC0AlphaWith
          (matrixInvEntrywiseSubBoundConst (𝕜 := 𝕜) δ (B r) (Bd r))
          (matrixInvEntrywiseSubHolderConst (𝕜 := 𝕜) δ (B r) (H r) (Bd r) (Hd r))
          α (fun z : ℝ × X => (M r z)⁻¹ - (N r z)⁻¹) K := by
  have hMctrl : ∀ r i j, ParabolicC0AlphaOn α (fun z => M r z i j) K := by
    intro r i j
    exact ⟨B r i j, hB r i j, H r i j, hH r i j, hM r i j⟩
  have hNctrl : ∀ r i j, ParabolicC0AlphaOn α (fun z => N r z i j) K := by
    intro r i j
    exact ⟨B r i j, hB r i j, H r i j, hH r i j, hN r i j⟩
  rcases matrix_det_pair_family_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) (N := N) hK hα hMctrl hNctrl hdetM_ne hdetN_ne with
    ⟨δ, hδpos, hdetM, hdetN⟩
  refine ⟨δ, hδpos, hdetM, hdetN, ?_⟩
  intro r
  exact matrix_inv_sub_with_entrywise (M := M r) (N := N r)
    (hH r) (hBd r) (hHd r) (hM r) (hN r) (hdiff r)
    hδpos (hdetM r) (hdetN r)

/-- On a compact time-space set, inverse-matrix entries preserve parabolic `C^{0,α}` control from
entrywise control and pointwise nonvanishing determinant. -/
theorem matrix_inv_entry_of_isCompact_det_ne_zero {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {K : Set (ℝ × X)} {M : ℝ × X → Matrix n n 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) K)
    (hdet_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0) (i j : n) :
    ParabolicC0AlphaOn α (fun z => (M z)⁻¹ i j) K := by
  rcases matrix_det_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hM hdet_ne with
    ⟨δ, hδpos, hdet⟩
  exact matrix_inv_entry (M := M) hM hδpos hdet i j

/-- A finite inverse-matrix-valued function is parabolic `C^{0,α}` when the matrix entries are and
the determinant is uniformly bounded away from zero. -/
theorem matrix_inv {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {δ : ℝ} {M : ℝ × X → Matrix n n 𝕜}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaOn α (fun z => (M z)⁻¹) s :=
  matrix_of_entries fun i j => matrix_inv_entry (M := M) hM hδpos hdet i j

/-- Finite inverse-matrix differences have existential entrywise-difference-based parabolic
`C^{0,α}` control under a common determinant lower bound. -/
theorem matrix_inv_sub_entrywise {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {δ : ℝ} {M N : ℝ × X → Matrix n n 𝕜}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s)
    (hN : ∀ i j, ParabolicC0AlphaOn α (fun z => N z i j) s)
    (hdiff : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j - N z i j) s)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicC0AlphaOn α (fun z => (M z)⁻¹ - (N z)⁻¹) s :=
  matrix_of_entries fun i j => by
    simpa using matrix_inv_entry_sub (M := M) (N := N)
      hM hN hdiff hδpos hdetM hdetN i j

/-- Compact-domain inverse-matrix-valued closure from entrywise control and pointwise
nonvanishing determinant. -/
theorem matrix_inv_of_isCompact_det_ne_zero {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {K : Set (ℝ × X)} {M : ℝ × X → Matrix n n 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) K)
    (hdet_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0) :
    ParabolicC0AlphaOn α (fun z => (M z)⁻¹) K :=
  matrix_of_entries fun i j =>
    matrix_inv_entry_of_isCompact_det_ne_zero hK hα hM hdet_ne i j

/-- Compact-domain finite-family inverse-matrix closure from entrywise control and pointwise
nonvanishing determinants, with one determinant lower bound shared by the family. -/
theorem matrix_inv_family_of_isCompact_det_ne_zero {ι n 𝕜 : Type*} [Fintype ι]
    [Fintype n] [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)}
    {M : ι → ℝ × X → Matrix n n 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hM : ∀ a i j, ParabolicC0AlphaOn α (fun z => M a z i j) K)
    (hdet_ne : ∀ a ⦃z : ℝ × X⦄, z ∈ K → (M a z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ a ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M a z).det‖) ∧
      ∀ a, ParabolicC0AlphaOn α (fun z : ℝ × X => (M a z)⁻¹) K := by
  rcases matrix_det_family_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hM hdet_ne with
    ⟨δ, hδpos, hdet⟩
  refine ⟨δ, hδpos, hdet, ?_⟩
  intro a
  exact matrix_inv (M := M a) (hM a) hδpos (hdet a)

/-- Compact-domain inverse-matrix difference control from entrywise controls and pointwise
nonvanishing determinants. -/
theorem matrix_inv_sub_entrywise_of_isCompact_det_ne_zero {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)}
    {M N : ℝ × X → Matrix n n 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) K)
    (hN : ∀ i j, ParabolicC0AlphaOn α (fun z => N z i j) K)
    (hdiff : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j - N z i j) K)
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (N z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ParabolicC0AlphaOn α (fun z => (M z)⁻¹ - (N z)⁻¹) K := by
  rcases matrix_det_pair_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) (N := N) hK hα hM hN hdetM_ne hdetN_ne with
    ⟨δ, hδpos, hdetM, hdetN⟩
  exact ⟨δ, hδpos, matrix_inv_sub_entrywise (M := M) (N := N)
    hM hN hdiff hδpos hdetM hdetN⟩

/-- Compact-domain finite-family inverse-matrix difference control from entrywise existential
controls and pointwise nonvanishing determinants, with one determinant lower bound shared by both
matrix families. -/
theorem matrix_inv_sub_entrywise_family_of_isCompact_det_ne_zero {ι n 𝕜 : Type*}
    [Fintype ι] [Fintype n] [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)}
    {M N : ι → ℝ × X → Matrix n n 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hM : ∀ r i j, ParabolicC0AlphaOn α (fun z => M r z i j) K)
    (hN : ∀ r i j, ParabolicC0AlphaOn α (fun z => N r z i j) K)
    (hdiff : ∀ r i j, ParabolicC0AlphaOn α (fun z => M r z i j - N r z i j) K)
    (hdetM_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (M r z).det ≠ 0)
    (hdetN_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (N r z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M r z).det‖) ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(N r z).det‖) ∧
      ∀ r,
        ParabolicC0AlphaOn α (fun z : ℝ × X => (M r z)⁻¹ - (N r z)⁻¹) K := by
  rcases matrix_det_pair_family_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) (N := N) hK hα hM hN hdetM_ne hdetN_ne with
    ⟨δ, hδpos, hdetM, hdetN⟩
  refine ⟨δ, hδpos, hdetM, hdetN, ?_⟩
  intro r
  exact matrix_inv_sub_entrywise (M := M r) (N := N r)
    (hM r) (hN r) (hdiff r) hδpos (hdetM r) (hdetN r)

/-- Entries of a product of two matrix-valued parabolic `C^{0,α}` functions are
parabolic `C^{0,α}` when all input entries are. -/
theorem matrix_mul_entry {l m n A : Type*} [Fintype m] [NormedRing A]
    {M : ℝ × X → Matrix l m A} {N : ℝ × X → Matrix m n A}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s)
    (hN : ∀ i j, ParabolicC0AlphaOn α (fun z => N z i j) s) (i : l) (j : n) :
    ParabolicC0AlphaOn α (fun z => (M z * N z) i j) s := by
  have hsum : ParabolicC0AlphaOn α (fun z => ∑ k : m, M z i k * N z k j) s :=
    ParabolicC0AlphaOn.finset_sum_mul (X := X) (α := α) (s := s)
      (S := (Finset.univ : Finset m))
      (u := fun k z => M z i k) (v := fun k z => N z k j)
      (fun k _hk => hM i k) (fun k _hk => hN k j)
  simpa [Matrix.mul_apply] using hsum

/-- Products of finite matrix-valued parabolic `C^{0,α}` functions are parabolic `C^{0,α}` from
entrywise control. -/
theorem matrix_mul {l m n A : Type*} [Fintype l] [Fintype m] [Fintype n] [NormedRing A]
    {M : ℝ × X → Matrix l m A} {N : ℝ × X → Matrix m n A}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s)
    (hN : ∀ i j, ParabolicC0AlphaOn α (fun z => N z i j) s) :
    ParabolicC0AlphaOn α (fun z => M z * N z) s :=
  matrix_of_entries fun i j => matrix_mul_entry hM hN i j

/-- Quantitative sup constant for one entry of a finite matrix product. -/
def matrixMulEntryBoundConst {l m n : Type*} [Fintype m]
    (BM : l → m → ℝ) (BN : m → n → ℝ) (i : l) (j : n) : ℝ :=
  Finset.univ.sum fun k : m => BM i k * BN k j

/-- Quantitative Holder constant for one entry of a finite matrix product. -/
def matrixMulEntryHolderConst {l m n : Type*} [Fintype m]
    (BM HM : l → m → ℝ) (BN HN : m → n → ℝ) (i : l) (j : n) : ℝ :=
  Finset.univ.sum fun k : m => BM i k * HN k j + BN k j * HM i k

theorem matrixMulEntryBoundConst_nonneg {l m n : Type*} [Fintype m]
    {BM : l → m → ℝ} {BN : m → n → ℝ} (hBM : ∀ i k, 0 ≤ BM i k)
    (hBN : ∀ k j, 0 ≤ BN k j) (i : l) (j : n) :
    0 ≤ matrixMulEntryBoundConst BM BN i j := by
  simpa [matrixMulEntryBoundConst] using
    (Finset.sum_nonneg fun k _hk => mul_nonneg (hBM i k) (hBN k j))

theorem matrixMulEntryHolderConst_nonneg {l m n : Type*} [Fintype m]
    {BM HM : l → m → ℝ} {BN HN : m → n → ℝ} (hBM : ∀ i k, 0 ≤ BM i k)
    (hHM : ∀ i k, 0 ≤ HM i k) (hBN : ∀ k j, 0 ≤ BN k j)
    (hHN : ∀ k j, 0 ≤ HN k j) (i : l) (j : n) :
    0 ≤ matrixMulEntryHolderConst BM HM BN HN i j := by
  simpa [matrixMulEntryHolderConst] using
    (Finset.sum_nonneg fun k _hk =>
      add_nonneg (mul_nonneg (hBM i k) (hHN k j)) (mul_nonneg (hBN k j) (hHM i k)))

/-- One entry of a finite matrix product has an explicit bounded parabolic `C^{0,α}` estimate. -/
theorem matrix_mul_entry_with {l m n A : Type*} [Fintype m] [NormedRing A]
    {BM HM : l → m → ℝ} {BN HN : m → n → ℝ}
    {M : ℝ × X → Matrix l m A} {N : ℝ × X → Matrix m n A}
    (hBM : ∀ i k, 0 ≤ BM i k)
    (hM : ∀ i k, ParabolicC0AlphaWith (BM i k) (HM i k) α
      (fun z => M z i k) s)
    (hN : ∀ k j, ParabolicC0AlphaWith (BN k j) (HN k j) α
      (fun z => N z k j) s)
    (i : l) (j : n) :
    ParabolicC0AlphaWith
      (matrixMulEntryBoundConst BM BN i j)
      (matrixMulEntryHolderConst BM HM BN HN i j)
      α (fun z => (M z * N z) i j) s := by
  classical
  simpa [Matrix.mul_apply, matrixMulEntryBoundConst, matrixMulEntryHolderConst] using
    (ParabolicC0AlphaWith.finset_sum_mul (X := X) (α := α) (s := s)
      (S := (Finset.univ : Finset m))
      (Bu := fun k => BM i k) (Hu := fun k => HM i k)
      (Bv := fun k => BN k j) (Hv := fun k => HN k j)
      (u := fun k z => M z i k) (v := fun k z => N z k j)
      (fun k _hk => hM i k) (fun k _hk => hN k j) (fun k _hk => hBM i k))

/-- Finite matrix products have an explicit matrix-valued bounded parabolic `C^{0,α}` estimate. -/
theorem matrix_mul_with {l m n A : Type*} [Fintype l] [Fintype m] [Fintype n]
    [NormedRing A] {BM HM : l → m → ℝ} {BN HN : m → n → ℝ}
    {M : ℝ × X → Matrix l m A} {N : ℝ × X → Matrix m n A}
    (hBM : ∀ i k, 0 ≤ BM i k) (hHM : ∀ i k, 0 ≤ HM i k)
    (hBN : ∀ k j, 0 ≤ BN k j) (hHN : ∀ k j, 0 ≤ HN k j)
    (hM : ∀ i k, ParabolicC0AlphaWith (BM i k) (HM i k) α
      (fun z => M z i k) s)
    (hN : ∀ k j, ParabolicC0AlphaWith (BN k j) (HN k j) α
      (fun z => N z k j) s) :
    ParabolicC0AlphaWith
      (∑ i : l, ∑ j : n, matrixMulEntryBoundConst BM BN i j)
      (∑ i : l, ∑ j : n, matrixMulEntryHolderConst BM HM BN HN i j)
      α (fun z => M z * N z) s := by
  refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
  · intro i
    exact Finset.sum_nonneg fun j _hj => matrixMulEntryBoundConst_nonneg hBM hBN i j
  · intro i
    exact Finset.sum_nonneg fun j _hj =>
      matrixMulEntryHolderConst_nonneg hBM hHM hBN hHN i j
  · intro i
    refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
    · intro j
      exact matrixMulEntryBoundConst_nonneg hBM hBN i j
    · intro j
      exact matrixMulEntryHolderConst_nonneg hBM hHM hBN hHN i j
    · intro j
      exact matrix_mul_entry_with hBM hM hN i j

/-- Quantitative sup constant for one entry of the difference of two finite matrix products. -/
def matrixMulEntrySubBoundConst {l m n : Type*} [Fintype m]
    (BM : l → m → ℝ) (BN' : m → n → ℝ) (BMd : l → m → ℝ)
    (BNd : m → n → ℝ) (i : l) (j : n) : ℝ :=
  Finset.univ.sum fun k : m => BM i k * BNd k j + BMd i k * BN' k j

/-- Quantitative Holder constant for one entry of the difference of two finite matrix products. -/
def matrixMulEntrySubHolderConst {l m n : Type*} [Fintype m]
    (BM HM : l → m → ℝ) (BN' HN' : m → n → ℝ) (BMd HMd : l → m → ℝ)
    (BNd HNd : m → n → ℝ) (i : l) (j : n) : ℝ :=
  Finset.univ.sum fun k : m =>
    (BM i k * HNd k j + BNd k j * HM i k) +
      (BMd i k * HN' k j + BN' k j * HMd i k)

theorem matrixMulEntrySubBoundConst_nonneg {l m n : Type*} [Fintype m]
    {BM : l → m → ℝ} {BN' : m → n → ℝ} {BMd : l → m → ℝ}
    {BNd : m → n → ℝ} (hBM : ∀ i k, 0 ≤ BM i k)
    (hBN' : ∀ k j, 0 ≤ BN' k j) (hBMd : ∀ i k, 0 ≤ BMd i k)
    (hBNd : ∀ k j, 0 ≤ BNd k j) (i : l) (j : n) :
    0 ≤ matrixMulEntrySubBoundConst BM BN' BMd BNd i j := by
  simpa [matrixMulEntrySubBoundConst] using
    (Finset.sum_nonneg fun k _hk =>
      add_nonneg (mul_nonneg (hBM i k) (hBNd k j)) (mul_nonneg (hBMd i k) (hBN' k j)))

theorem matrixMulEntrySubHolderConst_nonneg {l m n : Type*} [Fintype m]
    {BM HM : l → m → ℝ} {BN' HN' : m → n → ℝ} {BMd HMd : l → m → ℝ}
    {BNd HNd : m → n → ℝ} (hBM : ∀ i k, 0 ≤ BM i k)
    (hHM : ∀ i k, 0 ≤ HM i k) (hBN' : ∀ k j, 0 ≤ BN' k j)
    (hHN' : ∀ k j, 0 ≤ HN' k j) (hBMd : ∀ i k, 0 ≤ BMd i k)
    (hHMd : ∀ i k, 0 ≤ HMd i k) (hBNd : ∀ k j, 0 ≤ BNd k j)
    (hHNd : ∀ k j, 0 ≤ HNd k j) (i : l) (j : n) :
    0 ≤ matrixMulEntrySubHolderConst BM HM BN' HN' BMd HMd BNd HNd i j := by
  simpa [matrixMulEntrySubHolderConst] using
    (Finset.sum_nonneg fun k _hk =>
      add_nonneg
        (add_nonneg (mul_nonneg (hBM i k) (hHNd k j))
          (mul_nonneg (hBNd k j) (hHM i k)))
        (add_nonneg (mul_nonneg (hBMd i k) (hHN' k j))
          (mul_nonneg (hBN' k j) (hHMd i k))))

/-- One entry of the difference of two finite matrix products has an explicit bounded parabolic
`C^{0,α}` estimate from one left factor, one right factor, and factor-difference estimates. -/
theorem matrix_mul_entry_sub_with {l m n A : Type*} [Fintype m] [NormedRing A]
    {BM HM : l → m → ℝ} {BN' HN' : m → n → ℝ} {BMd HMd : l → m → ℝ}
    {BNd HNd : m → n → ℝ}
    {M M' : ℝ × X → Matrix l m A} {N N' : ℝ × X → Matrix m n A}
    (hM : ∀ i k, ParabolicC0AlphaWith (BM i k) (HM i k) α
      (fun z => M z i k) s)
    (hN' : ∀ k j, ParabolicC0AlphaWith (BN' k j) (HN' k j) α
      (fun z => N' z k j) s)
    (hMdiff : ∀ i k, ParabolicC0AlphaWith (BMd i k) (HMd i k) α
      (fun z => M z i k - M' z i k) s)
    (hNdiff : ∀ k j, ParabolicC0AlphaWith (BNd k j) (HNd k j) α
      (fun z => N z k j - N' z k j) s)
    (hBM : ∀ i k, 0 ≤ BM i k) (hBMd : ∀ i k, 0 ≤ BMd i k) (i : l) (j : n) :
    ParabolicC0AlphaWith
      (matrixMulEntrySubBoundConst BM BN' BMd BNd i j)
      (matrixMulEntrySubHolderConst BM HM BN' HN' BMd HMd BNd HNd i j)
      α (fun z => (M z * N z - M' z * N' z) i j) s := by
  classical
  simpa [Matrix.mul_apply, matrixMulEntrySubBoundConst, matrixMulEntrySubHolderConst] using
    (ParabolicC0AlphaWith.finset_sum_mul_sub_sum_mul (X := X) (α := α) (s := s)
      (S := (Finset.univ : Finset m))
      (Bu := fun k => BM i k) (Hu := fun k => HM i k)
      (Bv := fun k => BN' k j) (Hv := fun k => HN' k j)
      (Bdu := fun k => BMd i k) (Hdu := fun k => HMd i k)
      (Bdv := fun k => BNd k j) (Hdv := fun k => HNd k j)
      (u := fun k z => M z i k) (u' := fun k z => M' z i k)
      (v := fun k z => N z k j) (v' := fun k z => N' z k j)
      (fun k _hk => hM i k) (fun k _hk => hN' k j)
      (fun k _hk => hMdiff i k) (fun k _hk => hNdiff k j)
      (fun k _hk => hBM i k) (fun k _hk => hBMd i k))

/-- Differences of finite matrix products have an explicit matrix-valued bounded parabolic
`C^{0,α}` estimate from entrywise factor and factor-difference estimates. -/
theorem matrix_mul_sub_with {l m n A : Type*} [Fintype l] [Fintype m] [Fintype n]
    [NormedRing A] {BM HM : l → m → ℝ} {BN' HN' : m → n → ℝ}
    {BMd HMd : l → m → ℝ} {BNd HNd : m → n → ℝ}
    {M M' : ℝ × X → Matrix l m A} {N N' : ℝ × X → Matrix m n A}
    (hBM : ∀ i k, 0 ≤ BM i k) (hHM : ∀ i k, 0 ≤ HM i k)
    (hBN' : ∀ k j, 0 ≤ BN' k j) (hHN' : ∀ k j, 0 ≤ HN' k j)
    (hBMd : ∀ i k, 0 ≤ BMd i k) (hHMd : ∀ i k, 0 ≤ HMd i k)
    (hBNd : ∀ k j, 0 ≤ BNd k j) (hHNd : ∀ k j, 0 ≤ HNd k j)
    (hM : ∀ i k, ParabolicC0AlphaWith (BM i k) (HM i k) α
      (fun z => M z i k) s)
    (hN' : ∀ k j, ParabolicC0AlphaWith (BN' k j) (HN' k j) α
      (fun z => N' z k j) s)
    (hMdiff : ∀ i k, ParabolicC0AlphaWith (BMd i k) (HMd i k) α
      (fun z => M z i k - M' z i k) s)
    (hNdiff : ∀ k j, ParabolicC0AlphaWith (BNd k j) (HNd k j) α
      (fun z => N z k j - N' z k j) s) :
    ParabolicC0AlphaWith
      (∑ i : l, ∑ j : n, matrixMulEntrySubBoundConst BM BN' BMd BNd i j)
      (∑ i : l, ∑ j : n,
        matrixMulEntrySubHolderConst BM HM BN' HN' BMd HMd BNd HNd i j)
      α (fun z => M z * N z - M' z * N' z) s := by
  refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
  · intro i
    exact Finset.sum_nonneg fun j _hj =>
      matrixMulEntrySubBoundConst_nonneg hBM hBN' hBMd hBNd i j
  · intro i
    exact Finset.sum_nonneg fun j _hj =>
      matrixMulEntrySubHolderConst_nonneg hBM hHM hBN' hHN' hBMd hHMd hBNd hHNd i j
  · intro i
    refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
    · intro j
      exact matrixMulEntrySubBoundConst_nonneg hBM hBN' hBMd hBNd i j
    · intro j
      exact matrixMulEntrySubHolderConst_nonneg hBM hHM hBN' hHN' hBMd hHMd hBNd hHNd i j
    · intro j
      exact matrix_mul_entry_sub_with (M := M) (M' := M') (N := N) (N' := N')
        hM hN' hMdiff hNdiff hBM hBMd i j

end ParabolicC0AlphaOn

namespace ParabolicC0AlphaNormLe

variable {X : Type*} [PseudoMetricSpace X]
variable {α : ℝ} {s : Set (ℝ × X)}

/-- Entrywise single-radius control of two finite matrices packages matrix multiplication with the
corresponding quantitative product radius. -/
theorem matrix_mul_of_entries {l m n A : Type*} [Fintype l] [Fintype m] [Fintype n]
    [NormedRing A] {RM : l → m → ℝ} {RN : m → n → ℝ}
    {M : ℝ × X → Matrix l m A} {N : ℝ × X → Matrix m n A}
    (hM : ∀ i k, ParabolicC0AlphaNormLe (RM i k) α (fun z => M z i k) s)
    (hN : ∀ k j, ParabolicC0AlphaNormLe (RN k j) α (fun z => N z k j) s) :
    ParabolicC0AlphaNormLe
      ((∑ i : l, ∑ j : n,
          ParabolicC0AlphaOn.matrixMulEntryBoundConst RM RN i j) +
        (∑ i : l, ∑ j : n,
          ParabolicC0AlphaOn.matrixMulEntryHolderConst RM RM RN RN i j))
      α (fun z => M z * N z) s := by
  have hRM : ∀ i k, 0 ≤ RM i k := fun i k => (hM i k).nonneg
  have hRN : ∀ k j, 0 ≤ RN k j := fun k j => (hN k j).nonneg
  exact ParabolicC0AlphaNormLe.of_c0AlphaWith
    (Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj =>
        ParabolicC0AlphaOn.matrixMulEntryBoundConst_nonneg hRM hRN i j)
    (Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj =>
        ParabolicC0AlphaOn.matrixMulEntryHolderConst_nonneg hRM hRM hRN hRN i j)
    (ParabolicC0AlphaOn.matrix_mul_with
      (M := M) (N := N) (BM := RM) (HM := RM) (BN := RN) (HN := RN)
      hRM hRM hRN hRN
      (fun i k => ParabolicC0AlphaNormLe.c0AlphaWith_self (hM i k))
      (fun k j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hN k j)))

/-- Entrywise single-radius control of product factors and their differences packages matrix
product differences with the corresponding quantitative product-difference radius. -/
theorem matrix_mul_sub_of_entries {l m n A : Type*} [Fintype l] [Fintype m] [Fintype n]
    [NormedRing A] {RM : l → m → ℝ} {RN' : m → n → ℝ}
    {RMd : l → m → ℝ} {RNd : m → n → ℝ}
    {M M' : ℝ × X → Matrix l m A} {N N' : ℝ × X → Matrix m n A}
    (hM : ∀ i k, ParabolicC0AlphaNormLe (RM i k) α (fun z => M z i k) s)
    (hN' : ∀ k j, ParabolicC0AlphaNormLe (RN' k j) α (fun z => N' z k j) s)
    (hMdiff : ∀ i k, ParabolicC0AlphaNormLe (RMd i k) α
      (fun z => M z i k - M' z i k) s)
    (hNdiff : ∀ k j, ParabolicC0AlphaNormLe (RNd k j) α
      (fun z => N z k j - N' z k j) s) :
    ParabolicC0AlphaNormLe
      ((∑ i : l, ∑ j : n,
          ParabolicC0AlphaOn.matrixMulEntrySubBoundConst RM RN' RMd RNd i j) +
        (∑ i : l, ∑ j : n,
          ParabolicC0AlphaOn.matrixMulEntrySubHolderConst
            RM RM RN' RN' RMd RMd RNd RNd i j))
      α (fun z => M z * N z - M' z * N' z) s := by
  have hRM : ∀ i k, 0 ≤ RM i k := fun i k => (hM i k).nonneg
  have hRN' : ∀ k j, 0 ≤ RN' k j := fun k j => (hN' k j).nonneg
  have hRMd : ∀ i k, 0 ≤ RMd i k := fun i k => (hMdiff i k).nonneg
  have hRNd : ∀ k j, 0 ≤ RNd k j := fun k j => (hNdiff k j).nonneg
  exact ParabolicC0AlphaNormLe.of_c0AlphaWith
    (Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj =>
        ParabolicC0AlphaOn.matrixMulEntrySubBoundConst_nonneg hRM hRN' hRMd hRNd i j)
    (Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj =>
        ParabolicC0AlphaOn.matrixMulEntrySubHolderConst_nonneg
          hRM hRM hRN' hRN' hRMd hRMd hRNd hRNd i j)
    (ParabolicC0AlphaOn.matrix_mul_sub_with
      (M := M) (M' := M') (N := N) (N' := N')
      (BM := RM) (HM := RM) (BN' := RN') (HN' := RN')
      (BMd := RMd) (HMd := RMd) (BNd := RNd) (HNd := RNd)
      hRM hRM hRN' hRN' hRMd hRMd hRNd hRNd
      (fun i k => ParabolicC0AlphaNormLe.c0AlphaWith_self (hM i k))
      (fun k j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hN' k j))
      (fun i k => ParabolicC0AlphaNormLe.c0AlphaWith_self (hMdiff i k))
      (fun k j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hNdiff k j)))

end ParabolicC0AlphaNormLe

namespace ParabolicC0AlphaOn

variable {X : Type*} [PseudoMetricSpace X]
variable {α : ℝ} {s : Set (ℝ × X)}

/-- Entries of finite matrix products are pointwise Lipschitz on bounded left/right factors. -/
theorem matrix_mul_entry_norm_sub_le {l m n A : Type*} [Fintype m] [NormedRing A]
    {BM : l → m → ℝ} {BN : m → n → ℝ}
    (M M' : Matrix l m A) (N N' : Matrix m n A)
    (hM : ∀ i k, ‖M i k‖ ≤ BM i k) (hN' : ∀ k j, ‖N' k j‖ ≤ BN k j)
    (i : l) (j : n) :
    ‖(M * N) i j - (M' * N') i j‖ ≤
      ∑ k : m, (BM i k * ‖N k j - N' k j‖ + BN k j * ‖M i k - M' i k‖) := by
  simpa [Matrix.mul_apply] using
    (norm_finset_sum_mul_sub_sum_mul_le
      (S := (Finset.univ : Finset m))
      (B := fun k => BM i k)
      (D := fun k => BN k j)
      (a := fun k => M i k)
      (b := fun k => N k j)
      (c := fun k => M' i k)
      (d := fun k => N' k j)
      (fun k _hk => hM i k)
      (fun k _hk => hN' k j))

/-- Finite matrix multiplication is pointwise Lipschitz in the elementwise matrix norm on bounded
left/right factors. -/
theorem matrix_mul_norm_sub_le {l m n A : Type*} [Fintype l] [Fintype m] [Fintype n]
    [NormedRing A] {BM : l → m → ℝ} {BN : m → n → ℝ}
    (M M' : Matrix l m A) (N N' : Matrix m n A)
    (hM : ∀ i k, ‖M i k‖ ≤ BM i k) (hN' : ∀ k j, ‖N' k j‖ ≤ BN k j) :
    ‖M * N - M' * N'‖ ≤
      ∑ i : l, ∑ j : n, ∑ k : m,
        (BM i k * ‖N k j - N' k j‖ + BN k j * ‖M i k - M' i k‖) := by
  classical
  let entryBound : l → n → ℝ :=
    fun i j => ∑ k : m,
      (BM i k * ‖N k j - N' k j‖ + BN k j * ‖M i k - M' i k‖)
  have hentry : ∀ i j, ‖(M * N) i j - (M' * N') i j‖ ≤ entryBound i j := by
    intro i j
    simpa [entryBound] using matrix_mul_entry_norm_sub_le M M' N N' hM hN' i j
  have hentry_nonneg : ∀ i j, 0 ≤ entryBound i j := by
    intro i j
    exact (norm_nonneg _).trans (hentry i j)
  have hrow_nonneg : ∀ i, 0 ≤ ∑ j : n, entryBound i j := by
    intro i
    exact Finset.sum_nonneg fun j _hj => hentry_nonneg i j
  have htotal_nonneg : 0 ≤ ∑ i : l, ∑ j : n, entryBound i j :=
    Finset.sum_nonneg fun i _hi => hrow_nonneg i
  have hnorm : ‖M * N - M' * N'‖ ≤ ∑ i : l, ∑ j : n, entryBound i j := by
    refine (Matrix.norm_le_iff htotal_nonneg).2 ?_
    intro i j
    calc
      ‖(M * N - M' * N') i j‖ = ‖(M * N) i j - (M' * N') i j‖ := rfl
      _ ≤ entryBound i j := hentry i j
      _ ≤ ∑ j : n, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hentry_nonneg i k) (Finset.mem_univ j)
      _ ≤ ∑ i : l, ∑ j : n, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hrow_nonneg k) (Finset.mem_univ i)
  simpa [entryBound] using hnorm

/-- Matrix-norm Lipschitz constant for varying the right factor of a matrix product, with the
left factor bounded entrywise by `BM`. -/
def matrixMulRightFactorLipschitzConst {l m n : Type*} [Fintype l] [Fintype m]
    [Fintype n] (BM : l → m → ℝ) : ℝ :=
  ∑ i : l, ∑ _j : n, ∑ k : m, BM i k

/-- Matrix-norm Lipschitz constant for varying the left factor of a matrix product, with the
right factor bounded entrywise by `BN`. -/
def matrixMulLeftFactorLipschitzConst {l m n : Type*} [Fintype l] [Fintype m]
    [Fintype n] (BN : m → n → ℝ) : ℝ :=
  ∑ _i : l, ∑ j : n, ∑ k : m, BN k j

theorem matrixMulRightFactorLipschitzConst_nonneg {l m n : Type*} [Fintype l]
    [Fintype m] [Fintype n] {BM : l → m → ℝ} (hBM : ∀ i k, 0 ≤ BM i k) :
    0 ≤ matrixMulRightFactorLipschitzConst (n := n) BM := by
  exact Finset.sum_nonneg fun i _hi =>
    Finset.sum_nonneg fun _j _hj =>
      Finset.sum_nonneg fun k _hk => hBM i k

theorem matrixMulLeftFactorLipschitzConst_nonneg {l m n : Type*} [Fintype l]
    [Fintype m] [Fintype n] {BN : m → n → ℝ} (hBN : ∀ k j, 0 ≤ BN k j) :
    0 ≤ matrixMulLeftFactorLipschitzConst (l := l) BN := by
  exact Finset.sum_nonneg fun _i _hi =>
    Finset.sum_nonneg fun j _hj =>
      Finset.sum_nonneg fun k _hk => hBN k j

/-- Finite matrix multiplication is Lipschitz in the elementwise matrix norm on bounded
left/right factors, with separate constants for the two factor differences. -/
theorem matrix_mul_norm_sub_le_const {l m n A : Type*} [Fintype l] [Fintype m]
    [Fintype n] [NormedRing A] {BM : l → m → ℝ} {BN : m → n → ℝ}
    (M M' : Matrix l m A) (N N' : Matrix m n A)
    (hM : ∀ i k, ‖M i k‖ ≤ BM i k) (hN' : ∀ k j, ‖N' k j‖ ≤ BN k j) :
    ‖M * N - M' * N'‖ ≤
      matrixMulRightFactorLipschitzConst (n := n) BM * ‖N - N'‖ +
        matrixMulLeftFactorLipschitzConst (l := l) BN * ‖M - M'‖ := by
  have hBM_nonneg : ∀ i k, 0 ≤ BM i k := by
    intro i k
    exact (norm_nonneg _).trans (hM i k)
  have hBN_nonneg : ∀ k j, 0 ≤ BN k j := by
    intro k j
    exact (norm_nonneg _).trans (hN' k j)
  have hbase := matrix_mul_norm_sub_le M M' N N' hM hN'
  refine hbase.trans ?_
  calc
    (∑ i : l, ∑ j : n, ∑ k : m,
        (BM i k * ‖N k j - N' k j‖ + BN k j * ‖M i k - M' i k‖))
        ≤
      ∑ i : l, ∑ j : n, ∑ k : m,
        (BM i k * ‖N - N'‖ + BN k j * ‖M - M'‖) := by
      refine Finset.sum_le_sum fun i _hi =>
        Finset.sum_le_sum fun j _hj =>
          Finset.sum_le_sum fun k _hk => ?_
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (by simpa using Matrix.norm_entry_le_entrywise_sup_norm (N - N') (i := k) (j := j))
          (hBM_nonneg i k))
        (mul_le_mul_of_nonneg_left
          (by simpa using Matrix.norm_entry_le_entrywise_sup_norm (M - M') (i := i) (j := k))
          (hBN_nonneg k j))
    _ =
      (∑ i : l, ∑ j : n, ∑ k : m, BM i k * ‖N - N'‖) +
        (∑ i : l, ∑ j : n, ∑ k : m, BN k j * ‖M - M'‖) := by
      simp [Finset.sum_add_distrib]
    _ =
      matrixMulRightFactorLipschitzConst (n := n) BM * ‖N - N'‖ +
        matrixMulLeftFactorLipschitzConst (l := l) BN * ‖M - M'‖ := by
      have hright :
          (∑ i : l, ∑ j : n, ∑ k : m, BM i k * ‖N - N'‖) =
            matrixMulRightFactorLipschitzConst (n := n) BM * ‖N - N'‖ := by
        simp_rw [matrixMulRightFactorLipschitzConst, Finset.sum_mul]
      have hleft :
          (∑ i : l, ∑ j : n, ∑ k : m, BN k j * ‖M - M'‖) =
            matrixMulLeftFactorLipschitzConst (l := l) BN * ‖M - M'‖ := by
        simp_rw [matrixMulLeftFactorLipschitzConst, Finset.sum_mul]
      rw [hright, hleft]

/-- Finite matrix multiplication is bounded-difference controlled on a time-space set by
separate uniform bounds for the two factor differences. -/
theorem matrix_mul_bounded_sub_le_const {l m n A : Type*} [Fintype l] [Fintype m]
    [Fintype n] [NormedRing A] {BM : l → m → ℝ} {BN : m → n → ℝ}
    {ηM ηN : ℝ} {M M' : ℝ × X → Matrix l m A} {N N' : ℝ × X → Matrix m n A}
    (hBM : ∀ i k, 0 ≤ BM i k) (hBN : ∀ k j, 0 ≤ BN k j)
    (hM : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ i k, ‖M z i k‖ ≤ BM i k)
    (hN' : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ k j, ‖N' z k j‖ ≤ BN k j)
    (hMdiff : ∀ ⦃z : ℝ × X⦄, z ∈ s → ‖M z - M' z‖ ≤ ηM)
    (hNdiff : ∀ ⦃z : ℝ × X⦄, z ∈ s → ‖N z - N' z‖ ≤ ηN) :
    ParabolicBoundedWith
      (matrixMulRightFactorLipschitzConst (n := n) BM * ηN +
        matrixMulLeftFactorLipschitzConst (l := l) BN * ηM)
      (fun z : ℝ × X => M z * N z - M' z * N' z) s := by
  intro z hz
  exact (matrix_mul_norm_sub_le_const (BM := BM) (BN := BN)
      (M z) (M' z) (N z) (N' z) (hM hz) (hN' hz)).trans
    (add_le_add
      (mul_le_mul_of_nonneg_left (hNdiff hz)
        (matrixMulRightFactorLipschitzConst_nonneg (n := n) hBM))
      (mul_le_mul_of_nonneg_left (hMdiff hz)
        (matrixMulLeftFactorLipschitzConst_nonneg (l := l) hBN)))

/-- Entries of a matrix-vector product are parabolic `C^{0,α}` when the matrix entries and
vector components are. -/
theorem matrix_mulVec_entry {m n A : Type*} [Fintype n] [NormedRing A]
    {M : ℝ × X → Matrix m n A} {v : ℝ × X → n → A}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s)
    (hv : ∀ j, ParabolicC0AlphaOn α (fun z => v z j) s) (i : m) :
    ParabolicC0AlphaOn α (fun z => (M z).mulVec (v z) i) s := by
  have hsum : ParabolicC0AlphaOn α (fun z => ∑ j : n, M z i j * v z j) s :=
    ParabolicC0AlphaOn.finset_sum_mul (X := X) (α := α) (s := s)
      (S := (Finset.univ : Finset n))
      (u := fun j z => M z i j) (v := fun j z => v z j)
      (fun j _hj => hM i j) (fun j _hj => hv j)
  simpa only [Matrix.mulVec_apply_eq_sum] using hsum

/-- Matrix-vector products preserve parabolic `C^{0,α}` control from entrywise matrix control and
componentwise vector control. -/
theorem matrix_mulVec {m n A : Type*} [Fintype m] [Fintype n] [NormedRing A]
    {M : ℝ × X → Matrix m n A} {v : ℝ × X → n → A}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s)
    (hv : ∀ j, ParabolicC0AlphaOn α (fun z => v z j) s) :
    ParabolicC0AlphaOn α (fun z => (M z).mulVec (v z)) s :=
  vector_of_entries fun i => matrix_mulVec_entry hM hv i

/-- Quantitative sup constant for one component of a finite matrix-vector product. -/
def matrixMulVecEntryBoundConst {m n : Type*} [Fintype n]
    (BM : m → n → ℝ) (Bv : n → ℝ) (i : m) : ℝ :=
  Finset.univ.sum fun j : n => BM i j * Bv j

/-- Quantitative Holder constant for one component of a finite matrix-vector product. -/
def matrixMulVecEntryHolderConst {m n : Type*} [Fintype n]
    (BM HM : m → n → ℝ) (Bv Hv : n → ℝ) (i : m) : ℝ :=
  Finset.univ.sum fun j : n => BM i j * Hv j + Bv j * HM i j

theorem matrixMulVecEntryBoundConst_nonneg {m n : Type*} [Fintype n]
    {BM : m → n → ℝ} {Bv : n → ℝ} (hBM : ∀ i j, 0 ≤ BM i j)
    (hBv : ∀ j, 0 ≤ Bv j) (i : m) :
    0 ≤ matrixMulVecEntryBoundConst BM Bv i := by
  simpa [matrixMulVecEntryBoundConst] using
    (Finset.sum_nonneg fun j _hj => mul_nonneg (hBM i j) (hBv j))

theorem matrixMulVecEntryHolderConst_nonneg {m n : Type*} [Fintype n]
    {BM HM : m → n → ℝ} {Bv Hv : n → ℝ} (hBM : ∀ i j, 0 ≤ BM i j)
    (hHM : ∀ i j, 0 ≤ HM i j) (hBv : ∀ j, 0 ≤ Bv j) (hHv : ∀ j, 0 ≤ Hv j)
    (i : m) :
    0 ≤ matrixMulVecEntryHolderConst BM HM Bv Hv i := by
  simpa [matrixMulVecEntryHolderConst] using
    (Finset.sum_nonneg fun j _hj =>
      add_nonneg (mul_nonneg (hBM i j) (hHv j)) (mul_nonneg (hBv j) (hHM i j)))

/-- One component of a finite matrix-vector product has an explicit bounded parabolic
`C^{0,α}` estimate. -/
theorem matrix_mulVec_entry_with {m n A : Type*} [Fintype n] [NormedRing A]
    {BM HM : m → n → ℝ} {Bv Hv : n → ℝ}
    {M : ℝ × X → Matrix m n A} {v : ℝ × X → n → A}
    (hBM : ∀ i j, 0 ≤ BM i j)
    (hM : ∀ i j, ParabolicC0AlphaWith (BM i j) (HM i j) α
      (fun z => M z i j) s)
    (hv : ∀ j, ParabolicC0AlphaWith (Bv j) (Hv j) α (fun z => v z j) s)
    (i : m) :
    ParabolicC0AlphaWith
      (matrixMulVecEntryBoundConst BM Bv i)
      (matrixMulVecEntryHolderConst BM HM Bv Hv i)
      α (fun z => (M z).mulVec (v z) i) s := by
  classical
  simpa [Matrix.mulVec_apply_eq_sum, matrixMulVecEntryBoundConst,
    matrixMulVecEntryHolderConst] using
    (ParabolicC0AlphaWith.finset_sum_mul (X := X) (α := α) (s := s)
      (S := (Finset.univ : Finset n))
      (Bu := fun j => BM i j) (Hu := fun j => HM i j)
      (Bv := fun j => Bv j) (Hv := fun j => Hv j)
      (u := fun j z => M z i j) (v := fun j z => v z j)
      (fun j _hj => hM i j) (fun j _hj => hv j) (fun j _hj => hBM i j))

/-- Finite matrix-vector products have an explicit vector-valued bounded parabolic `C^{0,α}`
estimate. -/
theorem matrix_mulVec_with {m n A : Type*} [Fintype m] [Fintype n] [NormedRing A]
    {BM HM : m → n → ℝ} {Bv Hv : n → ℝ}
    {M : ℝ × X → Matrix m n A} {v : ℝ × X → n → A}
    (hBM : ∀ i j, 0 ≤ BM i j) (hHM : ∀ i j, 0 ≤ HM i j)
    (hBv : ∀ j, 0 ≤ Bv j) (hHv : ∀ j, 0 ≤ Hv j)
    (hM : ∀ i j, ParabolicC0AlphaWith (BM i j) (HM i j) α
      (fun z => M z i j) s)
    (hv : ∀ j, ParabolicC0AlphaWith (Bv j) (Hv j) α (fun z => v z j) s) :
    ParabolicC0AlphaWith
      (∑ i : m, matrixMulVecEntryBoundConst BM Bv i)
      (∑ i : m, matrixMulVecEntryHolderConst BM HM Bv Hv i)
      α (fun z => (M z).mulVec (v z)) s := by
  refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
  · intro i
    exact matrixMulVecEntryBoundConst_nonneg hBM hBv i
  · intro i
    exact matrixMulVecEntryHolderConst_nonneg hBM hHM hBv hHv i
  · intro i
    exact matrix_mulVec_entry_with hBM hM hv i

/-- Quantitative sup constant for one component of the difference of two finite
matrix-vector products. -/
def matrixMulVecEntrySubBoundConst {m n : Type*} [Fintype n]
    (BM : m → n → ℝ) (Bv' : n → ℝ) (BMd : m → n → ℝ) (Bvd : n → ℝ)
    (i : m) : ℝ :=
  Finset.univ.sum fun j : n => BM i j * Bvd j + BMd i j * Bv' j

/-- Quantitative Holder constant for one component of the difference of two finite
matrix-vector products. -/
def matrixMulVecEntrySubHolderConst {m n : Type*} [Fintype n]
    (BM HM : m → n → ℝ) (Bv' Hv' : n → ℝ) (BMd HMd : m → n → ℝ)
    (Bvd Hvd : n → ℝ) (i : m) : ℝ :=
  Finset.univ.sum fun j : n =>
    (BM i j * Hvd j + Bvd j * HM i j) +
      (BMd i j * Hv' j + Bv' j * HMd i j)

theorem matrixMulVecEntrySubBoundConst_nonneg {m n : Type*} [Fintype n]
    {BM : m → n → ℝ} {Bv' : n → ℝ} {BMd : m → n → ℝ} {Bvd : n → ℝ}
    (hBM : ∀ i j, 0 ≤ BM i j) (hBv' : ∀ j, 0 ≤ Bv' j)
    (hBMd : ∀ i j, 0 ≤ BMd i j) (hBvd : ∀ j, 0 ≤ Bvd j) (i : m) :
    0 ≤ matrixMulVecEntrySubBoundConst BM Bv' BMd Bvd i := by
  simpa [matrixMulVecEntrySubBoundConst] using
    (Finset.sum_nonneg fun j _hj =>
      add_nonneg (mul_nonneg (hBM i j) (hBvd j)) (mul_nonneg (hBMd i j) (hBv' j)))

theorem matrixMulVecEntrySubHolderConst_nonneg {m n : Type*} [Fintype n]
    {BM HM : m → n → ℝ} {Bv' Hv' : n → ℝ} {BMd HMd : m → n → ℝ}
    {Bvd Hvd : n → ℝ} (hBM : ∀ i j, 0 ≤ BM i j) (hHM : ∀ i j, 0 ≤ HM i j)
    (hBv' : ∀ j, 0 ≤ Bv' j) (hHv' : ∀ j, 0 ≤ Hv' j)
    (hBMd : ∀ i j, 0 ≤ BMd i j) (hHMd : ∀ i j, 0 ≤ HMd i j)
    (hBvd : ∀ j, 0 ≤ Bvd j) (hHvd : ∀ j, 0 ≤ Hvd j) (i : m) :
    0 ≤ matrixMulVecEntrySubHolderConst BM HM Bv' Hv' BMd HMd Bvd Hvd i := by
  simpa [matrixMulVecEntrySubHolderConst] using
    (Finset.sum_nonneg fun j _hj =>
      add_nonneg
        (add_nonneg (mul_nonneg (hBM i j) (hHvd j))
          (mul_nonneg (hBvd j) (hHM i j)))
        (add_nonneg (mul_nonneg (hBMd i j) (hHv' j))
          (mul_nonneg (hBv' j) (hHMd i j))))

/-- One component of the difference of two finite matrix-vector products has an explicit
bounded parabolic `C^{0,α}` estimate from matrix, vector, and difference estimates. -/
theorem matrix_mulVec_entry_sub_with {m n A : Type*} [Fintype n] [NormedRing A]
    {BM HM : m → n → ℝ} {Bv' Hv' : n → ℝ} {BMd HMd : m → n → ℝ}
    {Bvd Hvd : n → ℝ}
    {M M' : ℝ × X → Matrix m n A} {v v' : ℝ × X → n → A}
    (hM : ∀ i j, ParabolicC0AlphaWith (BM i j) (HM i j) α
      (fun z => M z i j) s)
    (hv' : ∀ j, ParabolicC0AlphaWith (Bv' j) (Hv' j) α (fun z => v' z j) s)
    (hMdiff : ∀ i j, ParabolicC0AlphaWith (BMd i j) (HMd i j) α
      (fun z => M z i j - M' z i j) s)
    (hvdiff : ∀ j, ParabolicC0AlphaWith (Bvd j) (Hvd j) α
      (fun z => v z j - v' z j) s)
    (hBM : ∀ i j, 0 ≤ BM i j) (hBMd : ∀ i j, 0 ≤ BMd i j) (i : m) :
    ParabolicC0AlphaWith
      (matrixMulVecEntrySubBoundConst BM Bv' BMd Bvd i)
      (matrixMulVecEntrySubHolderConst BM HM Bv' Hv' BMd HMd Bvd Hvd i)
      α (fun z => (M z).mulVec (v z) i - (M' z).mulVec (v' z) i) s := by
  classical
  simpa [Matrix.mulVec_apply_eq_sum, matrixMulVecEntrySubBoundConst,
    matrixMulVecEntrySubHolderConst] using
    (ParabolicC0AlphaWith.finset_sum_mul_sub_sum_mul (X := X) (α := α) (s := s)
      (S := (Finset.univ : Finset n))
      (Bu := fun j => BM i j) (Hu := fun j => HM i j)
      (Bv := fun j => Bv' j) (Hv := fun j => Hv' j)
      (Bdu := fun j => BMd i j) (Hdu := fun j => HMd i j)
      (Bdv := fun j => Bvd j) (Hdv := fun j => Hvd j)
      (u := fun j z => M z i j) (u' := fun j z => M' z i j)
      (v := fun j z => v z j) (v' := fun j z => v' z j)
      (fun j _hj => hM i j) (fun j _hj => hv' j)
      (fun j _hj => hMdiff i j) (fun j _hj => hvdiff j)
      (fun j _hj => hBM i j) (fun j _hj => hBMd i j))

/-- Differences of finite matrix-vector products have an explicit vector-valued bounded
parabolic `C^{0,α}` estimate. -/
theorem matrix_mulVec_sub_with {m n A : Type*} [Fintype m] [Fintype n] [NormedRing A]
    {BM HM : m → n → ℝ} {Bv' Hv' : n → ℝ} {BMd HMd : m → n → ℝ}
    {Bvd Hvd : n → ℝ}
    {M M' : ℝ × X → Matrix m n A} {v v' : ℝ × X → n → A}
    (hBM : ∀ i j, 0 ≤ BM i j) (hHM : ∀ i j, 0 ≤ HM i j)
    (hBv' : ∀ j, 0 ≤ Bv' j) (hHv' : ∀ j, 0 ≤ Hv' j)
    (hBMd : ∀ i j, 0 ≤ BMd i j) (hHMd : ∀ i j, 0 ≤ HMd i j)
    (hBvd : ∀ j, 0 ≤ Bvd j) (hHvd : ∀ j, 0 ≤ Hvd j)
    (hM : ∀ i j, ParabolicC0AlphaWith (BM i j) (HM i j) α
      (fun z => M z i j) s)
    (hv' : ∀ j, ParabolicC0AlphaWith (Bv' j) (Hv' j) α (fun z => v' z j) s)
    (hMdiff : ∀ i j, ParabolicC0AlphaWith (BMd i j) (HMd i j) α
      (fun z => M z i j - M' z i j) s)
    (hvdiff : ∀ j, ParabolicC0AlphaWith (Bvd j) (Hvd j) α
      (fun z => v z j - v' z j) s) :
    ParabolicC0AlphaWith
      (∑ i : m, matrixMulVecEntrySubBoundConst BM Bv' BMd Bvd i)
      (∑ i : m, matrixMulVecEntrySubHolderConst BM HM Bv' Hv' BMd HMd Bvd Hvd i)
      α (fun z => (M z).mulVec (v z) - (M' z).mulVec (v' z)) s := by
  refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
  · intro i
    exact matrixMulVecEntrySubBoundConst_nonneg hBM hBv' hBMd hBvd i
  · intro i
    exact matrixMulVecEntrySubHolderConst_nonneg hBM hHM hBv' hHv' hBMd hHMd hBvd hHvd i
  · intro i
    exact matrix_mulVec_entry_sub_with (M := M) (M' := M') (v := v) (v' := v')
      hM hv' hMdiff hvdiff hBM hBMd i

/-- Entries of a vector-matrix product are parabolic `C^{0,α}` when the vector components and
matrix entries are. -/
theorem matrix_vecMul_entry {m n A : Type*} [Fintype m] [NormedRing A]
    {v : ℝ × X → m → A} {M : ℝ × X → Matrix m n A}
    (hv : ∀ i, ParabolicC0AlphaOn α (fun z => v z i) s)
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s) (j : n) :
    ParabolicC0AlphaOn α (fun z => Matrix.vecMul (v z) (M z) j) s := by
  have hsum : ParabolicC0AlphaOn α (fun z => ∑ i : m, v z i * M z i j) s :=
    ParabolicC0AlphaOn.finset_sum_mul (X := X) (α := α) (s := s)
      (S := (Finset.univ : Finset m))
      (u := fun i z => v z i) (v := fun i z => M z i j)
      (fun i _hi => hv i) (fun i _hi => hM i j)
  simpa only [Matrix.vecMul_apply_eq_sum] using hsum

/-- Vector-matrix products preserve parabolic `C^{0,α}` control from componentwise vector control
and entrywise matrix control. -/
theorem matrix_vecMul {m n A : Type*} [Fintype m] [Fintype n] [NormedRing A]
    {v : ℝ × X → m → A} {M : ℝ × X → Matrix m n A}
    (hv : ∀ i, ParabolicC0AlphaOn α (fun z => v z i) s)
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s) :
    ParabolicC0AlphaOn α (fun z => Matrix.vecMul (v z) (M z)) s :=
  vector_of_entries fun j => matrix_vecMul_entry hv hM j

/-- Quantitative sup constant for one component of a finite vector-matrix product. -/
def matrixVecMulEntryBoundConst {m n : Type*} [Fintype m]
    (Bv : m → ℝ) (BM : m → n → ℝ) (j : n) : ℝ :=
  Finset.univ.sum fun i : m => Bv i * BM i j

/-- Quantitative Holder constant for one component of a finite vector-matrix product. -/
def matrixVecMulEntryHolderConst {m n : Type*} [Fintype m]
    (Bv Hv : m → ℝ) (BM HM : m → n → ℝ) (j : n) : ℝ :=
  Finset.univ.sum fun i : m => Bv i * HM i j + BM i j * Hv i

theorem matrixVecMulEntryBoundConst_nonneg {m n : Type*} [Fintype m]
    {Bv : m → ℝ} {BM : m → n → ℝ} (hBv : ∀ i, 0 ≤ Bv i)
    (hBM : ∀ i j, 0 ≤ BM i j) (j : n) :
    0 ≤ matrixVecMulEntryBoundConst Bv BM j := by
  simpa [matrixVecMulEntryBoundConst] using
    (Finset.sum_nonneg fun i _hi => mul_nonneg (hBv i) (hBM i j))

theorem matrixVecMulEntryHolderConst_nonneg {m n : Type*} [Fintype m]
    {Bv Hv : m → ℝ} {BM HM : m → n → ℝ} (hBv : ∀ i, 0 ≤ Bv i)
    (hHv : ∀ i, 0 ≤ Hv i) (hBM : ∀ i j, 0 ≤ BM i j)
    (hHM : ∀ i j, 0 ≤ HM i j) (j : n) :
    0 ≤ matrixVecMulEntryHolderConst Bv Hv BM HM j := by
  simpa [matrixVecMulEntryHolderConst] using
    (Finset.sum_nonneg fun i _hi =>
      add_nonneg (mul_nonneg (hBv i) (hHM i j)) (mul_nonneg (hBM i j) (hHv i)))

/-- One component of a finite vector-matrix product has an explicit bounded parabolic
`C^{0,α}` estimate. -/
theorem matrix_vecMul_entry_with {m n A : Type*} [Fintype m] [NormedRing A]
    {Bv Hv : m → ℝ} {BM HM : m → n → ℝ}
    {v : ℝ × X → m → A} {M : ℝ × X → Matrix m n A}
    (hBv : ∀ i, 0 ≤ Bv i)
    (hv : ∀ i, ParabolicC0AlphaWith (Bv i) (Hv i) α (fun z => v z i) s)
    (hM : ∀ i j, ParabolicC0AlphaWith (BM i j) (HM i j) α
      (fun z => M z i j) s)
    (j : n) :
    ParabolicC0AlphaWith
      (matrixVecMulEntryBoundConst Bv BM j)
      (matrixVecMulEntryHolderConst Bv Hv BM HM j)
      α (fun z => Matrix.vecMul (v z) (M z) j) s := by
  classical
  simpa [Matrix.vecMul_apply_eq_sum, matrixVecMulEntryBoundConst,
    matrixVecMulEntryHolderConst] using
    (ParabolicC0AlphaWith.finset_sum_mul (X := X) (α := α) (s := s)
      (S := (Finset.univ : Finset m))
      (Bu := fun i => Bv i) (Hu := fun i => Hv i)
      (Bv := fun i => BM i j) (Hv := fun i => HM i j)
      (u := fun i z => v z i) (v := fun i z => M z i j)
      (fun i _hi => hv i) (fun i _hi => hM i j) (fun i _hi => hBv i))

/-- Finite vector-matrix products have an explicit vector-valued bounded parabolic `C^{0,α}`
estimate. -/
theorem matrix_vecMul_with {m n A : Type*} [Fintype m] [Fintype n] [NormedRing A]
    {Bv Hv : m → ℝ} {BM HM : m → n → ℝ}
    {v : ℝ × X → m → A} {M : ℝ × X → Matrix m n A}
    (hBv : ∀ i, 0 ≤ Bv i) (hHv : ∀ i, 0 ≤ Hv i)
    (hBM : ∀ i j, 0 ≤ BM i j) (hHM : ∀ i j, 0 ≤ HM i j)
    (hv : ∀ i, ParabolicC0AlphaWith (Bv i) (Hv i) α (fun z => v z i) s)
    (hM : ∀ i j, ParabolicC0AlphaWith (BM i j) (HM i j) α
      (fun z => M z i j) s) :
    ParabolicC0AlphaWith
      (∑ j : n, matrixVecMulEntryBoundConst Bv BM j)
      (∑ j : n, matrixVecMulEntryHolderConst Bv Hv BM HM j)
      α (fun z => Matrix.vecMul (v z) (M z)) s := by
  refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
  · intro j
    exact matrixVecMulEntryBoundConst_nonneg hBv hBM j
  · intro j
    exact matrixVecMulEntryHolderConst_nonneg hBv hHv hBM hHM j
  · intro j
    exact matrix_vecMul_entry_with hBv hv hM j

/-- Quantitative sup constant for one component of the difference of two finite
vector-matrix products. -/
def matrixVecMulEntrySubBoundConst {m n : Type*} [Fintype m]
    (Bv : m → ℝ) (BM' : m → n → ℝ) (Bvd : m → ℝ) (BMd : m → n → ℝ)
    (j : n) : ℝ :=
  Finset.univ.sum fun i : m => Bv i * BMd i j + Bvd i * BM' i j

/-- Quantitative Holder constant for one component of the difference of two finite
vector-matrix products. -/
def matrixVecMulEntrySubHolderConst {m n : Type*} [Fintype m]
    (Bv Hv : m → ℝ) (BM' HM' : m → n → ℝ) (Bvd Hvd : m → ℝ)
    (BMd HMd : m → n → ℝ) (j : n) : ℝ :=
  Finset.univ.sum fun i : m =>
    (Bv i * HMd i j + BMd i j * Hv i) +
      (Bvd i * HM' i j + BM' i j * Hvd i)

theorem matrixVecMulEntrySubBoundConst_nonneg {m n : Type*} [Fintype m]
    {Bv : m → ℝ} {BM' : m → n → ℝ} {Bvd : m → ℝ} {BMd : m → n → ℝ}
    (hBv : ∀ i, 0 ≤ Bv i) (hBM' : ∀ i j, 0 ≤ BM' i j)
    (hBvd : ∀ i, 0 ≤ Bvd i) (hBMd : ∀ i j, 0 ≤ BMd i j) (j : n) :
    0 ≤ matrixVecMulEntrySubBoundConst Bv BM' Bvd BMd j := by
  simpa [matrixVecMulEntrySubBoundConst] using
    (Finset.sum_nonneg fun i _hi =>
      add_nonneg (mul_nonneg (hBv i) (hBMd i j)) (mul_nonneg (hBvd i) (hBM' i j)))

theorem matrixVecMulEntrySubHolderConst_nonneg {m n : Type*} [Fintype m]
    {Bv Hv : m → ℝ} {BM' HM' : m → n → ℝ} {Bvd Hvd : m → ℝ}
    {BMd HMd : m → n → ℝ} (hBv : ∀ i, 0 ≤ Bv i) (hHv : ∀ i, 0 ≤ Hv i)
    (hBM' : ∀ i j, 0 ≤ BM' i j) (hHM' : ∀ i j, 0 ≤ HM' i j)
    (hBvd : ∀ i, 0 ≤ Bvd i) (hHvd : ∀ i, 0 ≤ Hvd i)
    (hBMd : ∀ i j, 0 ≤ BMd i j) (hHMd : ∀ i j, 0 ≤ HMd i j) (j : n) :
    0 ≤ matrixVecMulEntrySubHolderConst Bv Hv BM' HM' Bvd Hvd BMd HMd j := by
  simpa [matrixVecMulEntrySubHolderConst] using
    (Finset.sum_nonneg fun i _hi =>
      add_nonneg
        (add_nonneg (mul_nonneg (hBv i) (hHMd i j))
          (mul_nonneg (hBMd i j) (hHv i)))
        (add_nonneg (mul_nonneg (hBvd i) (hHM' i j))
          (mul_nonneg (hBM' i j) (hHvd i))))

/-- One component of the difference of two finite vector-matrix products has an explicit
bounded parabolic `C^{0,α}` estimate from vector, matrix, and difference estimates. -/
theorem matrix_vecMul_entry_sub_with {m n A : Type*} [Fintype m] [NormedRing A]
    {Bv Hv : m → ℝ} {BM' HM' : m → n → ℝ} {Bvd Hvd : m → ℝ}
    {BMd HMd : m → n → ℝ}
    {v v' : ℝ × X → m → A} {M M' : ℝ × X → Matrix m n A}
    (hv : ∀ i, ParabolicC0AlphaWith (Bv i) (Hv i) α (fun z => v z i) s)
    (hM' : ∀ i j, ParabolicC0AlphaWith (BM' i j) (HM' i j) α
      (fun z => M' z i j) s)
    (hvdiff : ∀ i, ParabolicC0AlphaWith (Bvd i) (Hvd i) α
      (fun z => v z i - v' z i) s)
    (hMdiff : ∀ i j, ParabolicC0AlphaWith (BMd i j) (HMd i j) α
      (fun z => M z i j - M' z i j) s)
    (hBv : ∀ i, 0 ≤ Bv i) (hBvd : ∀ i, 0 ≤ Bvd i) (j : n) :
    ParabolicC0AlphaWith
      (matrixVecMulEntrySubBoundConst Bv BM' Bvd BMd j)
      (matrixVecMulEntrySubHolderConst Bv Hv BM' HM' Bvd Hvd BMd HMd j)
      α (fun z => Matrix.vecMul (v z) (M z) j - Matrix.vecMul (v' z) (M' z) j) s := by
  classical
  simpa [Matrix.vecMul_apply_eq_sum, matrixVecMulEntrySubBoundConst,
    matrixVecMulEntrySubHolderConst] using
    (ParabolicC0AlphaWith.finset_sum_mul_sub_sum_mul (X := X) (α := α) (s := s)
      (S := (Finset.univ : Finset m))
      (Bu := fun i => Bv i) (Hu := fun i => Hv i)
      (Bv := fun i => BM' i j) (Hv := fun i => HM' i j)
      (Bdu := fun i => Bvd i) (Hdu := fun i => Hvd i)
      (Bdv := fun i => BMd i j) (Hdv := fun i => HMd i j)
      (u := fun i z => v z i) (u' := fun i z => v' z i)
      (v := fun i z => M z i j) (v' := fun i z => M' z i j)
      (fun i _hi => hv i) (fun i _hi => hM' i j)
      (fun i _hi => hvdiff i) (fun i _hi => hMdiff i j)
      (fun i _hi => hBv i) (fun i _hi => hBvd i))

/-- Differences of finite vector-matrix products have an explicit vector-valued bounded
parabolic `C^{0,α}` estimate. -/
theorem matrix_vecMul_sub_with {m n A : Type*} [Fintype m] [Fintype n] [NormedRing A]
    {Bv Hv : m → ℝ} {BM' HM' : m → n → ℝ} {Bvd Hvd : m → ℝ}
    {BMd HMd : m → n → ℝ}
    {v v' : ℝ × X → m → A} {M M' : ℝ × X → Matrix m n A}
    (hBv : ∀ i, 0 ≤ Bv i) (hHv : ∀ i, 0 ≤ Hv i)
    (hBM' : ∀ i j, 0 ≤ BM' i j) (hHM' : ∀ i j, 0 ≤ HM' i j)
    (hBvd : ∀ i, 0 ≤ Bvd i) (hHvd : ∀ i, 0 ≤ Hvd i)
    (hBMd : ∀ i j, 0 ≤ BMd i j) (hHMd : ∀ i j, 0 ≤ HMd i j)
    (hv : ∀ i, ParabolicC0AlphaWith (Bv i) (Hv i) α (fun z => v z i) s)
    (hM' : ∀ i j, ParabolicC0AlphaWith (BM' i j) (HM' i j) α
      (fun z => M' z i j) s)
    (hvdiff : ∀ i, ParabolicC0AlphaWith (Bvd i) (Hvd i) α
      (fun z => v z i - v' z i) s)
    (hMdiff : ∀ i j, ParabolicC0AlphaWith (BMd i j) (HMd i j) α
      (fun z => M z i j - M' z i j) s) :
    ParabolicC0AlphaWith
      (∑ j : n, matrixVecMulEntrySubBoundConst Bv BM' Bvd BMd j)
      (∑ j : n, matrixVecMulEntrySubHolderConst Bv Hv BM' HM' Bvd Hvd BMd HMd j)
      α (fun z => Matrix.vecMul (v z) (M z) - Matrix.vecMul (v' z) (M' z)) s := by
  refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
  · intro j
    exact matrixVecMulEntrySubBoundConst_nonneg hBv hBM' hBvd hBMd j
  · intro j
    exact matrixVecMulEntrySubHolderConst_nonneg hBv hHv hBM' hHM' hBvd hHvd hBMd hHMd j
  · intro j
    exact matrix_vecMul_entry_sub_with (v := v) (v' := v') (M := M) (M' := M')
      hv hM' hvdiff hMdiff hBv hBvd j

end ParabolicC0AlphaOn

namespace ParabolicC0AlphaNormLe

variable {X : Type*} [PseudoMetricSpace X]
variable {α : ℝ} {s : Set (ℝ × X)}

/-- Entrywise single-radius control of a finite matrix and componentwise single-radius control of
a finite vector package matrix-vector multiplication with the corresponding quantitative product
radius. -/
theorem matrix_mulVec_of_entries {m n A : Type*} [Fintype m] [Fintype n] [NormedRing A]
    {RM : m → n → ℝ} {Rv : n → ℝ}
    {M : ℝ × X → Matrix m n A} {v : ℝ × X → n → A}
    (hM : ∀ i j, ParabolicC0AlphaNormLe (RM i j) α (fun z => M z i j) s)
    (hv : ∀ j, ParabolicC0AlphaNormLe (Rv j) α (fun z => v z j) s) :
    ParabolicC0AlphaNormLe
      ((∑ i : m, ParabolicC0AlphaOn.matrixMulVecEntryBoundConst RM Rv i) +
        (∑ i : m, ParabolicC0AlphaOn.matrixMulVecEntryHolderConst RM RM Rv Rv i))
      α (fun z => (M z).mulVec (v z)) s := by
  have hRM : ∀ i j, 0 ≤ RM i j := fun i j => (hM i j).nonneg
  have hRv : ∀ j, 0 ≤ Rv j := fun j => (hv j).nonneg
  exact ParabolicC0AlphaNormLe.of_c0AlphaWith
    (Finset.sum_nonneg fun i _hi =>
      ParabolicC0AlphaOn.matrixMulVecEntryBoundConst_nonneg hRM hRv i)
    (Finset.sum_nonneg fun i _hi =>
      ParabolicC0AlphaOn.matrixMulVecEntryHolderConst_nonneg hRM hRM hRv hRv i)
    (ParabolicC0AlphaOn.matrix_mulVec_with
      (M := M) (v := v) (BM := RM) (HM := RM) (Bv := Rv) (Hv := Rv)
      hRM hRM hRv hRv
      (fun i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hM i j))
      (fun j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hv j)))

/-- Entrywise single-radius control of matrix-vector factors and their differences packages
matrix-vector product differences with the corresponding quantitative product-difference
radius. -/
theorem matrix_mulVec_sub_of_entries {m n A : Type*} [Fintype m] [Fintype n]
    [NormedRing A] {RM : m → n → ℝ} {Rv' : n → ℝ}
    {RMd : m → n → ℝ} {Rvd : n → ℝ}
    {M M' : ℝ × X → Matrix m n A} {v v' : ℝ × X → n → A}
    (hM : ∀ i j, ParabolicC0AlphaNormLe (RM i j) α (fun z => M z i j) s)
    (hv' : ∀ j, ParabolicC0AlphaNormLe (Rv' j) α (fun z => v' z j) s)
    (hMdiff : ∀ i j, ParabolicC0AlphaNormLe (RMd i j) α
      (fun z => M z i j - M' z i j) s)
    (hvdiff : ∀ j, ParabolicC0AlphaNormLe (Rvd j) α
      (fun z => v z j - v' z j) s) :
    ParabolicC0AlphaNormLe
      ((∑ i : m, ParabolicC0AlphaOn.matrixMulVecEntrySubBoundConst RM Rv' RMd Rvd i) +
        (∑ i : m, ParabolicC0AlphaOn.matrixMulVecEntrySubHolderConst
          RM RM Rv' Rv' RMd RMd Rvd Rvd i))
      α (fun z => (M z).mulVec (v z) - (M' z).mulVec (v' z)) s := by
  have hRM : ∀ i j, 0 ≤ RM i j := fun i j => (hM i j).nonneg
  have hRv' : ∀ j, 0 ≤ Rv' j := fun j => (hv' j).nonneg
  have hRMd : ∀ i j, 0 ≤ RMd i j := fun i j => (hMdiff i j).nonneg
  have hRvd : ∀ j, 0 ≤ Rvd j := fun j => (hvdiff j).nonneg
  exact ParabolicC0AlphaNormLe.of_c0AlphaWith
    (Finset.sum_nonneg fun i _hi =>
      ParabolicC0AlphaOn.matrixMulVecEntrySubBoundConst_nonneg hRM hRv' hRMd hRvd i)
    (Finset.sum_nonneg fun i _hi =>
      ParabolicC0AlphaOn.matrixMulVecEntrySubHolderConst_nonneg
        hRM hRM hRv' hRv' hRMd hRMd hRvd hRvd i)
    (ParabolicC0AlphaOn.matrix_mulVec_sub_with
      (M := M) (M' := M') (v := v) (v' := v')
      (BM := RM) (HM := RM) (Bv' := Rv') (Hv' := Rv')
      (BMd := RMd) (HMd := RMd) (Bvd := Rvd) (Hvd := Rvd)
      hRM hRM hRv' hRv' hRMd hRMd hRvd hRvd
      (fun i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hM i j))
      (fun j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hv' j))
      (fun i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hMdiff i j))
      (fun j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hvdiff j)))

/-- Componentwise single-radius control of a finite vector and entrywise single-radius control of
a finite matrix package vector-matrix multiplication with the corresponding quantitative product
radius. -/
theorem matrix_vecMul_of_entries {m n A : Type*} [Fintype m] [Fintype n] [NormedRing A]
    {Rv : m → ℝ} {RM : m → n → ℝ}
    {v : ℝ × X → m → A} {M : ℝ × X → Matrix m n A}
    (hv : ∀ i, ParabolicC0AlphaNormLe (Rv i) α (fun z => v z i) s)
    (hM : ∀ i j, ParabolicC0AlphaNormLe (RM i j) α (fun z => M z i j) s) :
    ParabolicC0AlphaNormLe
      ((∑ j : n, ParabolicC0AlphaOn.matrixVecMulEntryBoundConst Rv RM j) +
        (∑ j : n, ParabolicC0AlphaOn.matrixVecMulEntryHolderConst Rv Rv RM RM j))
      α (fun z => Matrix.vecMul (v z) (M z)) s := by
  have hRv : ∀ i, 0 ≤ Rv i := fun i => (hv i).nonneg
  have hRM : ∀ i j, 0 ≤ RM i j := fun i j => (hM i j).nonneg
  exact ParabolicC0AlphaNormLe.of_c0AlphaWith
    (Finset.sum_nonneg fun j _hj =>
      ParabolicC0AlphaOn.matrixVecMulEntryBoundConst_nonneg hRv hRM j)
    (Finset.sum_nonneg fun j _hj =>
      ParabolicC0AlphaOn.matrixVecMulEntryHolderConst_nonneg hRv hRv hRM hRM j)
    (ParabolicC0AlphaOn.matrix_vecMul_with
      (v := v) (M := M) (Bv := Rv) (Hv := Rv) (BM := RM) (HM := RM)
      hRv hRv hRM hRM
      (fun i => ParabolicC0AlphaNormLe.c0AlphaWith_self (hv i))
      (fun i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hM i j)))

/-- Componentwise and entrywise single-radius control of vector-matrix factors and their
differences packages vector-matrix product differences with the corresponding quantitative
product-difference radius. -/
theorem matrix_vecMul_sub_of_entries {m n A : Type*} [Fintype m] [Fintype n]
    [NormedRing A] {Rv : m → ℝ} {RM' : m → n → ℝ}
    {Rvd : m → ℝ} {RMd : m → n → ℝ}
    {v v' : ℝ × X → m → A} {M M' : ℝ × X → Matrix m n A}
    (hv : ∀ i, ParabolicC0AlphaNormLe (Rv i) α (fun z => v z i) s)
    (hM' : ∀ i j, ParabolicC0AlphaNormLe (RM' i j) α (fun z => M' z i j) s)
    (hvdiff : ∀ i, ParabolicC0AlphaNormLe (Rvd i) α
      (fun z => v z i - v' z i) s)
    (hMdiff : ∀ i j, ParabolicC0AlphaNormLe (RMd i j) α
      (fun z => M z i j - M' z i j) s) :
    ParabolicC0AlphaNormLe
      ((∑ j : n, ParabolicC0AlphaOn.matrixVecMulEntrySubBoundConst Rv RM' Rvd RMd j) +
        (∑ j : n, ParabolicC0AlphaOn.matrixVecMulEntrySubHolderConst
          Rv Rv RM' RM' Rvd Rvd RMd RMd j))
      α (fun z => Matrix.vecMul (v z) (M z) - Matrix.vecMul (v' z) (M' z)) s := by
  have hRv : ∀ i, 0 ≤ Rv i := fun i => (hv i).nonneg
  have hRM' : ∀ i j, 0 ≤ RM' i j := fun i j => (hM' i j).nonneg
  have hRvd : ∀ i, 0 ≤ Rvd i := fun i => (hvdiff i).nonneg
  have hRMd : ∀ i j, 0 ≤ RMd i j := fun i j => (hMdiff i j).nonneg
  exact ParabolicC0AlphaNormLe.of_c0AlphaWith
    (Finset.sum_nonneg fun j _hj =>
      ParabolicC0AlphaOn.matrixVecMulEntrySubBoundConst_nonneg hRv hRM' hRvd hRMd j)
    (Finset.sum_nonneg fun j _hj =>
      ParabolicC0AlphaOn.matrixVecMulEntrySubHolderConst_nonneg
        hRv hRv hRM' hRM' hRvd hRvd hRMd hRMd j)
    (ParabolicC0AlphaOn.matrix_vecMul_sub_with
      (v := v) (v' := v') (M := M) (M' := M')
      (Bv := Rv) (Hv := Rv) (BM' := RM') (HM' := RM')
      (Bvd := Rvd) (Hvd := Rvd) (BMd := RMd) (HMd := RMd)
      hRv hRv hRM' hRM' hRvd hRvd hRMd hRMd
      (fun i => ParabolicC0AlphaNormLe.c0AlphaWith_self (hv i))
      (fun i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hM' i j))
      (fun i => ParabolicC0AlphaNormLe.c0AlphaWith_self (hvdiff i))
      (fun i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hMdiff i j)))

end ParabolicC0AlphaNormLe

namespace ParabolicC0AlphaOn

variable {X : Type*} [PseudoMetricSpace X]
variable {α : ℝ} {s : Set (ℝ × X)}

/-- Entries of an inverse-matrix-vector product are parabolic `C^{0,α}` when the matrix entries
and vector components are, and the determinant is uniformly bounded away from zero. -/
theorem matrix_inv_mulVec_entry {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {δ : ℝ} {M : ℝ × X → Matrix n n 𝕜} {v : ℝ × X → n → 𝕜}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s)
    (hv : ∀ j, ParabolicC0AlphaOn α (fun z => v z j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (i : n) :
    ParabolicC0AlphaOn α (fun z => ((M z)⁻¹).mulVec (v z) i) s :=
  matrix_mulVec_entry
    (M := fun z => (M z)⁻¹) (v := v)
    (fun r c => matrix_inv_entry (M := M) hM hδpos hdet r c) hv i

/-- Inverse-matrix-vector products preserve parabolic `C^{0,α}` control when the determinant is
uniformly bounded away from zero. -/
theorem matrix_inv_mulVec {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {δ : ℝ} {M : ℝ × X → Matrix n n 𝕜} {v : ℝ × X → n → 𝕜}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s)
    (hv : ∀ j, ParabolicC0AlphaOn α (fun z => v z j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaOn α (fun z => ((M z)⁻¹).mulVec (v z)) s :=
  vector_of_entries fun i => matrix_inv_mulVec_entry hM hv hδpos hdet i

/-- Quantitative sup constant for one component of an inverse-matrix-vector product. -/
def matrixInvMulVecEntryBoundConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (B : n → n → ℝ) (Bv : n → ℝ) (i : n) : ℝ :=
  matrixMulVecEntryBoundConst (fun r c => matrixInvEntryBoundConst (𝕜 := 𝕜) δ B r c) Bv i

/-- Quantitative Holder constant for one component of an inverse-matrix-vector product. -/
def matrixInvMulVecEntryHolderConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (B H : n → n → ℝ) (Bv Hv : n → ℝ) (i : n) :
    ℝ :=
  matrixMulVecEntryHolderConst
    (fun r c => matrixInvEntryBoundConst (𝕜 := 𝕜) δ B r c)
    (fun r c => matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H r c) Bv Hv i

theorem matrixInvMulVecEntryBoundConst_nonneg {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {B : n → n → ℝ} {Bv : n → ℝ}
    (hδpos : 0 < δ) (hBv : ∀ j, 0 ≤ Bv j) (i : n) :
    0 ≤ matrixInvMulVecEntryBoundConst (𝕜 := 𝕜) δ B Bv i := by
  simpa [matrixInvMulVecEntryBoundConst] using
    (matrixMulVecEntryBoundConst_nonneg
      (fun r c => matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos B r c) hBv i)

theorem matrixInvMulVecEntryHolderConst_nonneg {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {B H : n → n → ℝ} {Bv Hv : n → ℝ}
    (hH : ∀ i j, 0 ≤ H i j) (hδpos : 0 < δ)
    (hBv : ∀ j, 0 ≤ Bv j) (hHv : ∀ j, 0 ≤ Hv j) (i : n) :
    0 ≤ matrixInvMulVecEntryHolderConst (𝕜 := 𝕜) δ B H Bv Hv i := by
  simpa [matrixInvMulVecEntryHolderConst] using
    (matrixMulVecEntryHolderConst_nonneg
      (fun r c => matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos B r c)
      (fun r c => matrixInvEntryHolderConst_nonneg (𝕜 := 𝕜) hH hδpos r c)
      hBv hHv i)

/-- One component of an inverse-matrix-vector product has an explicit bounded parabolic
`C^{0,α}` estimate. -/
theorem matrix_inv_mulVec_entry_with {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {B H : n → n → ℝ} {Bv Hv : n → ℝ} {δ : ℝ}
    {M : ℝ × X → Matrix n n 𝕜} {v : ℝ × X → n → 𝕜}
    (hH : ∀ i j, 0 ≤ H i j)
    (hM : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => M z i j) s)
    (hv : ∀ j, ParabolicC0AlphaWith (Bv j) (Hv j) α (fun z => v z j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (i : n) :
    ParabolicC0AlphaWith
      (matrixInvMulVecEntryBoundConst (𝕜 := 𝕜) δ B Bv i)
      (matrixInvMulVecEntryHolderConst (𝕜 := 𝕜) δ B H Bv Hv i)
      α (fun z => ((M z)⁻¹).mulVec (v z) i) s := by
  simpa [matrixInvMulVecEntryBoundConst, matrixInvMulVecEntryHolderConst] using
    (matrix_mulVec_entry_with
      (M := fun z => (M z)⁻¹) (v := v)
      (BM := fun r c => matrixInvEntryBoundConst (𝕜 := 𝕜) δ B r c)
      (HM := fun r c => matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H r c)
      (Bv := Bv) (Hv := Hv)
      (fun r c => matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos B r c)
      (fun r c => matrix_inv_entry_with (M := M) hH hM hδpos hdet r c)
      hv i)

/-- Inverse-matrix-vector products have an explicit vector-valued bounded parabolic `C^{0,α}`
estimate. -/
theorem matrix_inv_mulVec_with {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {B H : n → n → ℝ} {Bv Hv : n → ℝ} {δ : ℝ}
    {M : ℝ × X → Matrix n n 𝕜} {v : ℝ × X → n → 𝕜}
    (hH : ∀ i j, 0 ≤ H i j) (hBv : ∀ j, 0 ≤ Bv j) (hHv : ∀ j, 0 ≤ Hv j)
    (hM : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => M z i j) s)
    (hv : ∀ j, ParabolicC0AlphaWith (Bv j) (Hv j) α (fun z => v z j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaWith
      (∑ i : n, matrixInvMulVecEntryBoundConst (𝕜 := 𝕜) δ B Bv i)
      (∑ i : n, matrixInvMulVecEntryHolderConst (𝕜 := 𝕜) δ B H Bv Hv i)
      α (fun z => ((M z)⁻¹).mulVec (v z)) s := by
  refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
  · intro i
    exact matrixInvMulVecEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos hBv i
  · intro i
    exact matrixInvMulVecEntryHolderConst_nonneg (𝕜 := 𝕜) hH hδpos hBv hHv i
  · intro i
    exact matrix_inv_mulVec_entry_with (M := M) hH hM hv hδpos hdet i

/-- Compact-domain inverse-matrix-vector entry closure from entrywise control and pointwise
nonvanishing determinant. -/
theorem matrix_inv_mulVec_entry_of_isCompact_det_ne_zero {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)}
    {M : ℝ × X → Matrix n n 𝕜} {v : ℝ × X → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) K)
    (hv : ∀ j, ParabolicC0AlphaOn α (fun z => v z j) K)
    (hdet_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0) (i : n) :
    ParabolicC0AlphaOn α (fun z => ((M z)⁻¹).mulVec (v z) i) K := by
  rcases matrix_det_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hM hdet_ne with
    ⟨δ, hδpos, hdet⟩
  exact matrix_inv_mulVec_entry hM hv hδpos hdet i

/-- Compact-domain inverse-matrix-vector closure from entrywise control and pointwise
nonvanishing determinant. -/
theorem matrix_inv_mulVec_of_isCompact_det_ne_zero {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)}
    {M : ℝ × X → Matrix n n 𝕜} {v : ℝ × X → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) K)
    (hv : ∀ j, ParabolicC0AlphaOn α (fun z => v z j) K)
    (hdet_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0) :
    ParabolicC0AlphaOn α (fun z => ((M z)⁻¹).mulVec (v z)) K := by
  rcases matrix_det_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hM hdet_ne with
    ⟨δ, hδpos, hdet⟩
  exact matrix_inv_mulVec hM hv hδpos hdet

/-- Compact-domain finite-family inverse-matrix/vector closure from entrywise matrix and vector
control, with one determinant lower bound shared by the family. -/
theorem matrix_inv_mulVec_family_of_isCompact_det_ne_zero {ι n 𝕜 : Type*}
    [Fintype ι] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {K : Set (ℝ × X)}
    {M : ι → ℝ × X → Matrix n n 𝕜} {v : ι → ℝ × X → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hM : ∀ a i j, ParabolicC0AlphaOn α (fun z => M a z i j) K)
    (hv : ∀ a j, ParabolicC0AlphaOn α (fun z => v a z j) K)
    (hdet_ne : ∀ a ⦃z : ℝ × X⦄, z ∈ K → (M a z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ a ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M a z).det‖) ∧
      ∀ a, ParabolicC0AlphaOn α (fun z : ℝ × X => ((M a z)⁻¹).mulVec (v a z)) K := by
  rcases matrix_det_family_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hM hdet_ne with
    ⟨δ, hδpos, hdet⟩
  refine ⟨δ, hδpos, hdet, ?_⟩
  intro a
  exact matrix_inv_mulVec (M := M a) (v := v a) (hM a) (hv a) hδpos (hdet a)

/-- A finite family of inverse-matrix/vector products has explicit vector-valued bounded
parabolic `C^{0,α}` estimates with one compact determinant lower bound shared by the family. -/
theorem matrix_inv_mulVec_family_with_of_isCompact_det_ne_zero {ι n 𝕜 : Type*}
    [Fintype ι] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {K : Set (ℝ × X)}
    {B H : ι → n → n → ℝ} {Bv Hv : ι → n → ℝ}
    {M : ι → ℝ × X → Matrix n n 𝕜} {v : ι → ℝ × X → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hB : ∀ a i j, 0 ≤ B a i j) (hH : ∀ a i j, 0 ≤ H a i j)
    (hBv : ∀ a j, 0 ≤ Bv a j) (hHv : ∀ a j, 0 ≤ Hv a j)
    (hM : ∀ a i j,
      ParabolicC0AlphaWith (B a i j) (H a i j) α (fun z => M a z i j) K)
    (hv : ∀ a j, ParabolicC0AlphaWith (Bv a j) (Hv a j) α
      (fun z => v a z j) K)
    (hdet_ne : ∀ a ⦃z : ℝ × X⦄, z ∈ K → (M a z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ a ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M a z).det‖) ∧
      ∀ a,
        ParabolicC0AlphaWith
          (∑ i : n, matrixInvMulVecEntryBoundConst (𝕜 := 𝕜) δ (B a) (Bv a) i)
          (∑ i : n,
            matrixInvMulVecEntryHolderConst (𝕜 := 𝕜) δ (B a) (H a) (Bv a) (Hv a) i)
          α (fun z : ℝ × X => ((M a z)⁻¹).mulVec (v a z)) K := by
  have hMctrl : ∀ a i j, ParabolicC0AlphaOn α (fun z => M a z i j) K := by
    intro a i j
    exact ⟨B a i j, hB a i j, H a i j, hH a i j, hM a i j⟩
  rcases matrix_det_family_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hMctrl hdet_ne with
    ⟨δ, hδpos, hdet⟩
  refine ⟨δ, hδpos, hdet, ?_⟩
  intro a
  exact matrix_inv_mulVec_with (M := M a) (v := v a)
    (hH a) (hBv a) (hHv a) (hM a) (hv a) hδpos (hdet a)

/-- Compact-domain quantitative inverse-matrix-vector closure from entrywise control and
pointwise nonvanishing determinant. -/
theorem matrix_inv_mulVec_with_of_isCompact_det_ne_zero {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)}
    {B H : n → n → ℝ} {Bv Hv : n → ℝ}
    {M : ℝ × X → Matrix n n 𝕜} {v : ℝ × X → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hB : ∀ i j, 0 ≤ B i j) (hH : ∀ i j, 0 ≤ H i j)
    (hBv : ∀ j, 0 ≤ Bv j) (hHv : ∀ j, 0 ≤ Hv j)
    (hM : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => M z i j) K)
    (hv : ∀ j, ParabolicC0AlphaWith (Bv j) (Hv j) α (fun z => v z j) K)
    (hdet_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (∑ i : n, matrixInvMulVecEntryBoundConst (𝕜 := 𝕜) δ B Bv i)
        (∑ i : n, matrixInvMulVecEntryHolderConst (𝕜 := 𝕜) δ B H Bv Hv i)
        α (fun z : ℝ × X => ((M z)⁻¹).mulVec (v z)) K := by
  have hMctrl : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) K := by
    intro i j
    exact ⟨B i j, hB i j, H i j, hH i j, hM i j⟩
  rcases matrix_det_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hMctrl hdet_ne with
    ⟨δ, hδpos, hdet⟩
  exact ⟨δ, hδpos, matrix_inv_mulVec_with (M := M) (v := v)
    hH hBv hHv hM hv hδpos hdet⟩

/-- Entries of a vector-inverse-matrix product are parabolic `C^{0,α}` when the matrix entries
and vector components are, and the determinant is uniformly bounded away from zero. -/
theorem matrix_vecMul_inv_entry {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {δ : ℝ} {v : ℝ × X → n → 𝕜} {M : ℝ × X → Matrix n n 𝕜}
    (hv : ∀ i, ParabolicC0AlphaOn α (fun z => v z i) s)
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (j : n) :
    ParabolicC0AlphaOn α (fun z => Matrix.vecMul (v z) (M z)⁻¹ j) s :=
  matrix_vecMul_entry
    (v := v) (M := fun z => (M z)⁻¹)
    hv (fun r c => matrix_inv_entry (M := M) hM hδpos hdet r c) j

/-- Vector-inverse-matrix products preserve parabolic `C^{0,α}` control when the determinant is
uniformly bounded away from zero. -/
theorem matrix_vecMul_inv {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {δ : ℝ} {v : ℝ × X → n → 𝕜} {M : ℝ × X → Matrix n n 𝕜}
    (hv : ∀ i, ParabolicC0AlphaOn α (fun z => v z i) s)
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaOn α (fun z => Matrix.vecMul (v z) (M z)⁻¹) s :=
  vector_of_entries fun j => matrix_vecMul_inv_entry hv hM hδpos hdet j

/-- Quantitative sup constant for one component of a vector-inverse-matrix product. -/
def matrixVecMulInvEntryBoundConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (Bv : n → ℝ) (B : n → n → ℝ) (j : n) : ℝ :=
  matrixVecMulEntryBoundConst Bv (fun r c => matrixInvEntryBoundConst (𝕜 := 𝕜) δ B r c) j

/-- Quantitative Holder constant for one component of a vector-inverse-matrix product. -/
def matrixVecMulInvEntryHolderConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (Bv Hv : n → ℝ) (B H : n → n → ℝ) (j : n) :
    ℝ :=
  matrixVecMulEntryHolderConst Bv Hv
    (fun r c => matrixInvEntryBoundConst (𝕜 := 𝕜) δ B r c)
    (fun r c => matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H r c) j

theorem matrixVecMulInvEntryBoundConst_nonneg {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {Bv : n → ℝ} {B : n → n → ℝ}
    (hδpos : 0 < δ) (hBv : ∀ i, 0 ≤ Bv i) (j : n) :
    0 ≤ matrixVecMulInvEntryBoundConst (𝕜 := 𝕜) δ Bv B j := by
  simpa [matrixVecMulInvEntryBoundConst] using
    (matrixVecMulEntryBoundConst_nonneg hBv
      (fun r c => matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos B r c) j)

theorem matrixVecMulInvEntryHolderConst_nonneg {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {Bv Hv : n → ℝ} {B H : n → n → ℝ}
    (hH : ∀ i j, 0 ≤ H i j) (hδpos : 0 < δ)
    (hBv : ∀ i, 0 ≤ Bv i) (hHv : ∀ i, 0 ≤ Hv i) (j : n) :
    0 ≤ matrixVecMulInvEntryHolderConst (𝕜 := 𝕜) δ Bv Hv B H j := by
  simpa [matrixVecMulInvEntryHolderConst] using
    (matrixVecMulEntryHolderConst_nonneg hBv hHv
      (fun r c => matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos B r c)
      (fun r c => matrixInvEntryHolderConst_nonneg (𝕜 := 𝕜) hH hδpos r c) j)

/-- One component of a vector-inverse-matrix product has an explicit bounded parabolic
`C^{0,α}` estimate. -/
theorem matrix_vecMul_inv_entry_with {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {Bv Hv : n → ℝ} {B H : n → n → ℝ} {δ : ℝ}
    {v : ℝ × X → n → 𝕜} {M : ℝ × X → Matrix n n 𝕜}
    (hBv : ∀ i, 0 ≤ Bv i) (hH : ∀ i j, 0 ≤ H i j)
    (hv : ∀ i, ParabolicC0AlphaWith (Bv i) (Hv i) α (fun z => v z i) s)
    (hM : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => M z i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (j : n) :
    ParabolicC0AlphaWith
      (matrixVecMulInvEntryBoundConst (𝕜 := 𝕜) δ Bv B j)
      (matrixVecMulInvEntryHolderConst (𝕜 := 𝕜) δ Bv Hv B H j)
      α (fun z => Matrix.vecMul (v z) (M z)⁻¹ j) s := by
  simpa [matrixVecMulInvEntryBoundConst, matrixVecMulInvEntryHolderConst] using
    (matrix_vecMul_entry_with
      (v := v) (M := fun z => (M z)⁻¹)
      (Bv := Bv) (Hv := Hv)
      (BM := fun r c => matrixInvEntryBoundConst (𝕜 := 𝕜) δ B r c)
      (HM := fun r c => matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H r c)
      hBv hv
      (fun r c => matrix_inv_entry_with (M := M) hH hM hδpos hdet r c)
      j)

/-- Vector-inverse-matrix products have an explicit vector-valued bounded parabolic `C^{0,α}`
estimate. -/
theorem matrix_vecMul_inv_with {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {Bv Hv : n → ℝ} {B H : n → n → ℝ} {δ : ℝ}
    {v : ℝ × X → n → 𝕜} {M : ℝ × X → Matrix n n 𝕜}
    (hBv : ∀ i, 0 ≤ Bv i) (hHv : ∀ i, 0 ≤ Hv i) (hH : ∀ i j, 0 ≤ H i j)
    (hv : ∀ i, ParabolicC0AlphaWith (Bv i) (Hv i) α (fun z => v z i) s)
    (hM : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => M z i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaWith
      (∑ j : n, matrixVecMulInvEntryBoundConst (𝕜 := 𝕜) δ Bv B j)
      (∑ j : n, matrixVecMulInvEntryHolderConst (𝕜 := 𝕜) δ Bv Hv B H j)
      α (fun z => Matrix.vecMul (v z) (M z)⁻¹) s := by
  refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
  · intro j
    exact matrixVecMulInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos hBv j
  · intro j
    exact matrixVecMulInvEntryHolderConst_nonneg (𝕜 := 𝕜) hH hδpos hBv hHv j
  · intro j
    exact matrix_vecMul_inv_entry_with (v := v) (M := M) hBv hH hv hM hδpos hdet j

end ParabolicC0AlphaOn

namespace ParabolicC0AlphaNormLe

variable {X : Type*} [PseudoMetricSpace X]
variable {α : ℝ} {s : Set (ℝ × X)}

/-- Entrywise single-radius control and a determinant lower bound package inverse-matrix-vector
products with the corresponding quantitative radius. -/
theorem matrix_inv_mulVec_of_entries {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {R : n → n → ℝ} {Rv : n → ℝ} {δ : ℝ}
    {M : ℝ × X → Matrix n n 𝕜} {v : ℝ × X → n → 𝕜}
    (hM : ∀ i j, ParabolicC0AlphaNormLe (R i j) α (fun z => M z i j) s)
    (hv : ∀ j, ParabolicC0AlphaNormLe (Rv j) α (fun z => v z j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaNormLe
      ((∑ i : n, ParabolicC0AlphaOn.matrixInvMulVecEntryBoundConst
          (𝕜 := 𝕜) δ R Rv i) +
        (∑ i : n, ParabolicC0AlphaOn.matrixInvMulVecEntryHolderConst
          (𝕜 := 𝕜) δ R R Rv Rv i))
      α (fun z => ((M z)⁻¹).mulVec (v z)) s := by
  have hR : ∀ i j, 0 ≤ R i j := fun i j => (hM i j).nonneg
  have hRv : ∀ j, 0 ≤ Rv j := fun j => (hv j).nonneg
  exact ParabolicC0AlphaNormLe.of_c0AlphaWith
    (Finset.sum_nonneg fun i _hi =>
      ParabolicC0AlphaOn.matrixInvMulVecEntryBoundConst_nonneg
        (𝕜 := 𝕜) hδpos hRv i)
    (Finset.sum_nonneg fun i _hi =>
      ParabolicC0AlphaOn.matrixInvMulVecEntryHolderConst_nonneg
        (𝕜 := 𝕜) hR hδpos hRv hRv i)
    (ParabolicC0AlphaOn.matrix_inv_mulVec_with
      (M := M) (v := v) (B := R) (H := R) (Bv := Rv) (Hv := Rv)
      hR hRv hRv
      (fun i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hM i j))
      (fun j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hv j))
      hδpos hdet)

/-- Entrywise single-radius controls, vector controls, and a common determinant lower bound
package inverse-matrix-vector product differences with the corresponding quantitative radius. -/
theorem matrix_inv_mulVec_sub_of_entries {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {R Rd : n → n → ℝ} {Rv' Rvd : n → ℝ} {δ : ℝ}
    {M N : ℝ × X → Matrix n n 𝕜} {v v' : ℝ × X → n → 𝕜}
    (hM : ∀ i j, ParabolicC0AlphaNormLe (R i j) α (fun z => M z i j) s)
    (hN : ∀ i j, ParabolicC0AlphaNormLe (R i j) α (fun z => N z i j) s)
    (hv' : ∀ j, ParabolicC0AlphaNormLe (Rv' j) α (fun z => v' z j) s)
    (hMdiff : ∀ i j, ParabolicC0AlphaNormLe (Rd i j) α
      (fun z => M z i j - N z i j) s)
    (hvdiff : ∀ j, ParabolicC0AlphaNormLe (Rvd j) α
      (fun z => v z j - v' z j) s)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicC0AlphaNormLe
      ((∑ i : n,
          ParabolicC0AlphaOn.matrixMulVecEntrySubBoundConst
            (fun r c => ParabolicC0AlphaOn.matrixInvEntryBoundConst (𝕜 := 𝕜) δ R r c)
            Rv'
            (fun r c =>
              ParabolicC0AlphaOn.matrixInvEntrySubBoundConst (𝕜 := 𝕜) δ R Rd r c)
            Rvd i) +
        (∑ i : n,
          ParabolicC0AlphaOn.matrixMulVecEntrySubHolderConst
            (fun r c => ParabolicC0AlphaOn.matrixInvEntryBoundConst (𝕜 := 𝕜) δ R r c)
            (fun r c => ParabolicC0AlphaOn.matrixInvEntryHolderConst (𝕜 := 𝕜) δ R R r c)
            Rv' Rv'
            (fun r c =>
              ParabolicC0AlphaOn.matrixInvEntrySubBoundConst (𝕜 := 𝕜) δ R Rd r c)
            (fun r c =>
              ParabolicC0AlphaOn.matrixInvEntrySubHolderConst
                (𝕜 := 𝕜) δ R R Rd Rd r c)
            Rvd Rvd i))
      α (fun z => ((M z)⁻¹).mulVec (v z) - ((N z)⁻¹).mulVec (v' z)) s := by
  have hR : ∀ i j, 0 ≤ R i j := fun i j => (hM i j).nonneg
  have hRd : ∀ i j, 0 ≤ Rd i j := fun i j => (hMdiff i j).nonneg
  have hRv' : ∀ j, 0 ≤ Rv' j := fun j => (hv' j).nonneg
  have hRvd : ∀ j, 0 ≤ Rvd j := fun j => (hvdiff j).nonneg
  exact ParabolicC0AlphaNormLe.of_c0AlphaWith
    (Finset.sum_nonneg fun i _hi =>
      ParabolicC0AlphaOn.matrixMulVecEntrySubBoundConst_nonneg
        (fun r c =>
          ParabolicC0AlphaOn.matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos R r c)
        hRv'
        (fun r c =>
          ParabolicC0AlphaOn.matrixInvEntrySubBoundConst_nonneg
            (𝕜 := 𝕜) hδpos hRd r c)
        hRvd i)
    (Finset.sum_nonneg fun i _hi =>
      ParabolicC0AlphaOn.matrixMulVecEntrySubHolderConst_nonneg
        (fun r c =>
          ParabolicC0AlphaOn.matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos R r c)
        (fun r c =>
          ParabolicC0AlphaOn.matrixInvEntryHolderConst_nonneg (𝕜 := 𝕜) hR hδpos r c)
        hRv' hRv'
        (fun r c =>
          ParabolicC0AlphaOn.matrixInvEntrySubBoundConst_nonneg
            (𝕜 := 𝕜) hδpos hRd r c)
        (fun r c =>
          ParabolicC0AlphaOn.matrixInvEntrySubHolderConst_nonneg
            (𝕜 := 𝕜) hδpos hR hRd hRd r c)
        hRvd hRvd i)
    (ParabolicC0AlphaOn.matrix_mulVec_sub_with
      (M := fun z => (M z)⁻¹) (M' := fun z => (N z)⁻¹) (v := v) (v' := v')
      (BM := fun r c => ParabolicC0AlphaOn.matrixInvEntryBoundConst (𝕜 := 𝕜) δ R r c)
      (HM := fun r c => ParabolicC0AlphaOn.matrixInvEntryHolderConst (𝕜 := 𝕜) δ R R r c)
      (Bv' := Rv') (Hv' := Rv')
      (BMd := fun r c =>
        ParabolicC0AlphaOn.matrixInvEntrySubBoundConst (𝕜 := 𝕜) δ R Rd r c)
      (HMd := fun r c =>
        ParabolicC0AlphaOn.matrixInvEntrySubHolderConst (𝕜 := 𝕜) δ R R Rd Rd r c)
      (Bvd := Rvd) (Hvd := Rvd)
      (fun r c =>
        ParabolicC0AlphaOn.matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos R r c)
      (fun r c =>
        ParabolicC0AlphaOn.matrixInvEntryHolderConst_nonneg (𝕜 := 𝕜) hR hδpos r c)
      hRv' hRv'
      (fun r c =>
        ParabolicC0AlphaOn.matrixInvEntrySubBoundConst_nonneg (𝕜 := 𝕜) hδpos hRd r c)
      (fun r c =>
        ParabolicC0AlphaOn.matrixInvEntrySubHolderConst_nonneg
          (𝕜 := 𝕜) hδpos hR hRd hRd r c)
      hRvd hRvd
      (fun r c =>
        ParabolicC0AlphaOn.matrix_inv_entry_with
          (M := M) hR
          (fun i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hM i j))
          hδpos hdetM r c)
      (fun j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hv' j))
      (fun r c =>
        ParabolicC0AlphaOn.matrix_inv_entry_sub_with
          (M := M) (N := N) hR hRd hRd
          (fun i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hM i j))
          (fun i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hN i j))
          (fun i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hMdiff i j))
          hδpos hdetM hdetN r c)
      (fun j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hvdiff j)))

/-- Componentwise single-radius control, entrywise single-radius control, and a determinant lower
bound package vector-inverse-matrix products with the corresponding quantitative radius. -/
theorem matrix_vecMul_inv_of_entries {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {Rv : n → ℝ} {R : n → n → ℝ} {δ : ℝ}
    {v : ℝ × X → n → 𝕜} {M : ℝ × X → Matrix n n 𝕜}
    (hv : ∀ i, ParabolicC0AlphaNormLe (Rv i) α (fun z => v z i) s)
    (hM : ∀ i j, ParabolicC0AlphaNormLe (R i j) α (fun z => M z i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaNormLe
      ((∑ j : n, ParabolicC0AlphaOn.matrixVecMulInvEntryBoundConst
          (𝕜 := 𝕜) δ Rv R j) +
        (∑ j : n, ParabolicC0AlphaOn.matrixVecMulInvEntryHolderConst
          (𝕜 := 𝕜) δ Rv Rv R R j))
      α (fun z => Matrix.vecMul (v z) (M z)⁻¹) s := by
  have hRv : ∀ i, 0 ≤ Rv i := fun i => (hv i).nonneg
  have hR : ∀ i j, 0 ≤ R i j := fun i j => (hM i j).nonneg
  exact ParabolicC0AlphaNormLe.of_c0AlphaWith
    (Finset.sum_nonneg fun j _hj =>
      ParabolicC0AlphaOn.matrixVecMulInvEntryBoundConst_nonneg
        (𝕜 := 𝕜) hδpos hRv j)
    (Finset.sum_nonneg fun j _hj =>
      ParabolicC0AlphaOn.matrixVecMulInvEntryHolderConst_nonneg
        (𝕜 := 𝕜) hR hδpos hRv hRv j)
    (ParabolicC0AlphaOn.matrix_vecMul_inv_with
      (v := v) (M := M) (Bv := Rv) (Hv := Rv) (B := R) (H := R)
      hRv hRv hR
      (fun i => ParabolicC0AlphaNormLe.c0AlphaWith_self (hv i))
      (fun i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hM i j))
      hδpos hdet)

/-- Componentwise and entrywise single-radius controls, plus a common determinant lower bound,
package vector-inverse-matrix product differences with the corresponding quantitative radius. -/
theorem matrix_vecMul_inv_sub_of_entries {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {Rv Rvd : n → ℝ} {R Rd : n → n → ℝ} {δ : ℝ}
    {v v' : ℝ × X → n → 𝕜} {M N : ℝ × X → Matrix n n 𝕜}
    (hv : ∀ i, ParabolicC0AlphaNormLe (Rv i) α (fun z => v z i) s)
    (hM : ∀ i j, ParabolicC0AlphaNormLe (R i j) α (fun z => M z i j) s)
    (hN : ∀ i j, ParabolicC0AlphaNormLe (R i j) α (fun z => N z i j) s)
    (hvdiff : ∀ i, ParabolicC0AlphaNormLe (Rvd i) α
      (fun z => v z i - v' z i) s)
    (hMdiff : ∀ i j, ParabolicC0AlphaNormLe (Rd i j) α
      (fun z => M z i j - N z i j) s)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicC0AlphaNormLe
      ((∑ j : n,
          ParabolicC0AlphaOn.matrixVecMulEntrySubBoundConst
            Rv
            (fun r c => ParabolicC0AlphaOn.matrixInvEntryBoundConst (𝕜 := 𝕜) δ R r c)
            Rvd
            (fun r c =>
              ParabolicC0AlphaOn.matrixInvEntrySubBoundConst (𝕜 := 𝕜) δ R Rd r c)
            j) +
        (∑ j : n,
          ParabolicC0AlphaOn.matrixVecMulEntrySubHolderConst
            Rv Rv
            (fun r c => ParabolicC0AlphaOn.matrixInvEntryBoundConst (𝕜 := 𝕜) δ R r c)
            (fun r c => ParabolicC0AlphaOn.matrixInvEntryHolderConst (𝕜 := 𝕜) δ R R r c)
            Rvd Rvd
            (fun r c =>
              ParabolicC0AlphaOn.matrixInvEntrySubBoundConst (𝕜 := 𝕜) δ R Rd r c)
            (fun r c =>
              ParabolicC0AlphaOn.matrixInvEntrySubHolderConst
                (𝕜 := 𝕜) δ R R Rd Rd r c)
            j))
      α (fun z => Matrix.vecMul (v z) (M z)⁻¹ - Matrix.vecMul (v' z) (N z)⁻¹) s := by
  have hRv : ∀ i, 0 ≤ Rv i := fun i => (hv i).nonneg
  have hRvd : ∀ i, 0 ≤ Rvd i := fun i => (hvdiff i).nonneg
  have hR : ∀ i j, 0 ≤ R i j := fun i j => (hM i j).nonneg
  have hRd : ∀ i j, 0 ≤ Rd i j := fun i j => (hMdiff i j).nonneg
  exact ParabolicC0AlphaNormLe.of_c0AlphaWith
    (Finset.sum_nonneg fun j _hj =>
      ParabolicC0AlphaOn.matrixVecMulEntrySubBoundConst_nonneg hRv
        (fun r c =>
          ParabolicC0AlphaOn.matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos R r c)
        hRvd
        (fun r c =>
          ParabolicC0AlphaOn.matrixInvEntrySubBoundConst_nonneg
            (𝕜 := 𝕜) hδpos hRd r c)
        j)
    (Finset.sum_nonneg fun j _hj =>
      ParabolicC0AlphaOn.matrixVecMulEntrySubHolderConst_nonneg hRv hRv
        (fun r c =>
          ParabolicC0AlphaOn.matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos R r c)
        (fun r c =>
          ParabolicC0AlphaOn.matrixInvEntryHolderConst_nonneg (𝕜 := 𝕜) hR hδpos r c)
        hRvd hRvd
        (fun r c =>
          ParabolicC0AlphaOn.matrixInvEntrySubBoundConst_nonneg
            (𝕜 := 𝕜) hδpos hRd r c)
        (fun r c =>
          ParabolicC0AlphaOn.matrixInvEntrySubHolderConst_nonneg
            (𝕜 := 𝕜) hδpos hR hRd hRd r c)
        j)
    (ParabolicC0AlphaOn.matrix_vecMul_sub_with
      (v := v) (v' := v') (M := fun z => (M z)⁻¹) (M' := fun z => (N z)⁻¹)
      (Bv := Rv) (Hv := Rv)
      (BM' := fun r c => ParabolicC0AlphaOn.matrixInvEntryBoundConst (𝕜 := 𝕜) δ R r c)
      (HM' := fun r c => ParabolicC0AlphaOn.matrixInvEntryHolderConst (𝕜 := 𝕜) δ R R r c)
      (Bvd := Rvd) (Hvd := Rvd)
      (BMd := fun r c =>
        ParabolicC0AlphaOn.matrixInvEntrySubBoundConst (𝕜 := 𝕜) δ R Rd r c)
      (HMd := fun r c =>
        ParabolicC0AlphaOn.matrixInvEntrySubHolderConst (𝕜 := 𝕜) δ R R Rd Rd r c)
      hRv hRv
      (fun r c =>
        ParabolicC0AlphaOn.matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos R r c)
      (fun r c =>
        ParabolicC0AlphaOn.matrixInvEntryHolderConst_nonneg (𝕜 := 𝕜) hR hδpos r c)
      hRvd hRvd
      (fun r c =>
        ParabolicC0AlphaOn.matrixInvEntrySubBoundConst_nonneg (𝕜 := 𝕜) hδpos hRd r c)
      (fun r c =>
        ParabolicC0AlphaOn.matrixInvEntrySubHolderConst_nonneg
          (𝕜 := 𝕜) hδpos hR hRd hRd r c)
      (fun i => ParabolicC0AlphaNormLe.c0AlphaWith_self (hv i))
      (fun r c =>
        ParabolicC0AlphaOn.matrix_inv_entry_with
          (M := N) hR
          (fun i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hN i j))
          hδpos hdetN r c)
      (fun i => ParabolicC0AlphaNormLe.c0AlphaWith_self (hvdiff i))
      (fun r c =>
        ParabolicC0AlphaOn.matrix_inv_entry_sub_with
          (M := M) (N := N) hR hRd hRd
          (fun i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hM i j))
          (fun i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hN i j))
          (fun i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hMdiff i j))
          hδpos hdetM hdetN r c))

end ParabolicC0AlphaNormLe

namespace ParabolicC0AlphaOn

variable {X : Type*} [PseudoMetricSpace X]
variable {α : ℝ} {s : Set (ℝ × X)}

/-- Compact-domain vector-inverse-matrix entry closure from entrywise control and pointwise
nonvanishing determinant. -/
theorem matrix_vecMul_inv_entry_of_isCompact_det_ne_zero {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)}
    {v : ℝ × X → n → 𝕜} {M : ℝ × X → Matrix n n 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hv : ∀ i, ParabolicC0AlphaOn α (fun z => v z i) K)
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) K)
    (hdet_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0) (j : n) :
    ParabolicC0AlphaOn α (fun z => Matrix.vecMul (v z) (M z)⁻¹ j) K := by
  rcases matrix_det_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hM hdet_ne with
    ⟨δ, hδpos, hdet⟩
  exact matrix_vecMul_inv_entry hv hM hδpos hdet j

/-- Compact-domain vector-inverse-matrix closure from entrywise control and pointwise
nonvanishing determinant. -/
theorem matrix_vecMul_inv_of_isCompact_det_ne_zero {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)}
    {v : ℝ × X → n → 𝕜} {M : ℝ × X → Matrix n n 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hv : ∀ i, ParabolicC0AlphaOn α (fun z => v z i) K)
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) K)
    (hdet_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0) :
    ParabolicC0AlphaOn α (fun z => Matrix.vecMul (v z) (M z)⁻¹) K := by
  rcases matrix_det_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hM hdet_ne with
    ⟨δ, hδpos, hdet⟩
  exact matrix_vecMul_inv hv hM hδpos hdet

/-- Compact-domain finite-family vector/inverse-matrix closure from entrywise vector and matrix
control, with one determinant lower bound shared by the family. -/
theorem matrix_vecMul_inv_family_of_isCompact_det_ne_zero {ι n 𝕜 : Type*}
    [Fintype ι] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {K : Set (ℝ × X)}
    {v : ι → ℝ × X → n → 𝕜} {M : ι → ℝ × X → Matrix n n 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hv : ∀ a i, ParabolicC0AlphaOn α (fun z => v a z i) K)
    (hM : ∀ a i j, ParabolicC0AlphaOn α (fun z => M a z i j) K)
    (hdet_ne : ∀ a ⦃z : ℝ × X⦄, z ∈ K → (M a z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ a ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M a z).det‖) ∧
      ∀ a, ParabolicC0AlphaOn α (fun z : ℝ × X => Matrix.vecMul (v a z) (M a z)⁻¹) K := by
  rcases matrix_det_family_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hM hdet_ne with
    ⟨δ, hδpos, hdet⟩
  refine ⟨δ, hδpos, hdet, ?_⟩
  intro a
  exact matrix_vecMul_inv (M := M a) (v := v a) (hv a) (hM a) hδpos (hdet a)

/-- A finite family of vector/inverse-matrix products has explicit vector-valued bounded
parabolic `C^{0,α}` estimates with one compact determinant lower bound shared by the family. -/
theorem matrix_vecMul_inv_family_with_of_isCompact_det_ne_zero {ι n 𝕜 : Type*}
    [Fintype ι] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {K : Set (ℝ × X)}
    {Bv Hv : ι → n → ℝ} {B H : ι → n → n → ℝ}
    {v : ι → ℝ × X → n → 𝕜} {M : ι → ℝ × X → Matrix n n 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hBv : ∀ a i, 0 ≤ Bv a i) (hHv : ∀ a i, 0 ≤ Hv a i)
    (hB : ∀ a i j, 0 ≤ B a i j) (hH : ∀ a i j, 0 ≤ H a i j)
    (hv : ∀ a i, ParabolicC0AlphaWith (Bv a i) (Hv a i) α
      (fun z => v a z i) K)
    (hM : ∀ a i j,
      ParabolicC0AlphaWith (B a i j) (H a i j) α (fun z => M a z i j) K)
    (hdet_ne : ∀ a ⦃z : ℝ × X⦄, z ∈ K → (M a z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ a ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M a z).det‖) ∧
      ∀ a,
        ParabolicC0AlphaWith
          (∑ j : n, matrixVecMulInvEntryBoundConst (𝕜 := 𝕜) δ (Bv a) (B a) j)
          (∑ j : n,
            matrixVecMulInvEntryHolderConst (𝕜 := 𝕜) δ (Bv a) (Hv a) (B a) (H a) j)
          α (fun z : ℝ × X => Matrix.vecMul (v a z) (M a z)⁻¹) K := by
  have hMctrl : ∀ a i j, ParabolicC0AlphaOn α (fun z => M a z i j) K := by
    intro a i j
    exact ⟨B a i j, hB a i j, H a i j, hH a i j, hM a i j⟩
  rcases matrix_det_family_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hMctrl hdet_ne with
    ⟨δ, hδpos, hdet⟩
  refine ⟨δ, hδpos, hdet, ?_⟩
  intro a
  exact matrix_vecMul_inv_with (v := v a) (M := M a)
    (hBv a) (hHv a) (hH a) (hv a) (hM a) hδpos (hdet a)

/-- Compact-domain quantitative vector-inverse-matrix closure from entrywise control and
pointwise nonvanishing determinant. -/
theorem matrix_vecMul_inv_with_of_isCompact_det_ne_zero {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)}
    {Bv Hv : n → ℝ} {B H : n → n → ℝ}
    {v : ℝ × X → n → 𝕜} {M : ℝ × X → Matrix n n 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hBv : ∀ i, 0 ≤ Bv i) (hHv : ∀ i, 0 ≤ Hv i)
    (hB : ∀ i j, 0 ≤ B i j) (hH : ∀ i j, 0 ≤ H i j)
    (hv : ∀ i, ParabolicC0AlphaWith (Bv i) (Hv i) α (fun z => v z i) K)
    (hM : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => M z i j) K)
    (hdet_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (∑ j : n, matrixVecMulInvEntryBoundConst (𝕜 := 𝕜) δ Bv B j)
        (∑ j : n, matrixVecMulInvEntryHolderConst (𝕜 := 𝕜) δ Bv Hv B H j)
        α (fun z : ℝ × X => Matrix.vecMul (v z) (M z)⁻¹) K := by
  have hMctrl : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) K := by
    intro i j
    exact ⟨B i j, hB i j, H i j, hH i j, hM i j⟩
  rcases matrix_det_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hMctrl hdet_ne with
    ⟨δ, hδpos, hdet⟩
  exact ⟨δ, hδpos, matrix_vecMul_inv_with (v := v) (M := M)
    hBv hHv hH hv hM hδpos hdet⟩

/-- Finite dot products of vector-valued parabolic `C^{0,α}` functions are parabolic
`C^{0,α}`. -/
theorem vector_dot_entry {n A : Type*} [Fintype n] [NormedRing A]
    {v w : ℝ × X → n → A}
    (hv : ∀ i, ParabolicC0AlphaOn α (fun z => v z i) s)
    (hw : ∀ i, ParabolicC0AlphaOn α (fun z => w z i) s) :
    ParabolicC0AlphaOn α (fun z => ∑ i : n, v z i * w z i) s := by
  simpa using
    (ParabolicC0AlphaOn.finset_sum_mul (X := X) (α := α) (s := s)
      (S := (Finset.univ : Finset n))
      (u := fun i z => v z i) (v := fun i z => w z i)
      (fun i _hi => hv i) (fun i _hi => hw i))

/-- Quantitative sup constant for a finite dot product. -/
def vectorDotBoundConst {n : Type*} [Fintype n] (Bv Bw : n → ℝ) : ℝ :=
  Finset.univ.sum fun i : n => Bv i * Bw i

/-- Quantitative Holder constant for a finite dot product. -/
def vectorDotHolderConst {n : Type*} [Fintype n] (Bv Hv Bw Hw : n → ℝ) : ℝ :=
  Finset.univ.sum fun i : n => Bv i * Hw i + Bw i * Hv i

theorem vectorDotBoundConst_nonneg {n : Type*} [Fintype n] {Bv Bw : n → ℝ}
    (hBv : ∀ i, 0 ≤ Bv i) (hBw : ∀ i, 0 ≤ Bw i) :
    0 ≤ vectorDotBoundConst Bv Bw := by
  simpa [vectorDotBoundConst] using
    (Finset.sum_nonneg fun i _hi => mul_nonneg (hBv i) (hBw i))

theorem vectorDotHolderConst_nonneg {n : Type*} [Fintype n] {Bv Hv Bw Hw : n → ℝ}
    (hBv : ∀ i, 0 ≤ Bv i) (hHv : ∀ i, 0 ≤ Hv i)
    (hBw : ∀ i, 0 ≤ Bw i) (hHw : ∀ i, 0 ≤ Hw i) :
    0 ≤ vectorDotHolderConst Bv Hv Bw Hw := by
  simpa [vectorDotHolderConst] using
    (Finset.sum_nonneg fun i _hi =>
      add_nonneg (mul_nonneg (hBv i) (hHw i)) (mul_nonneg (hBw i) (hHv i)))

/-- Finite dot products have an explicit bounded parabolic `C^{0,α}` estimate. -/
theorem vector_dot_with {n A : Type*} [Fintype n] [NormedRing A]
    {Bv Hv Bw Hw : n → ℝ} {v w : ℝ × X → n → A}
    (hBv : ∀ i, 0 ≤ Bv i)
    (hv : ∀ i, ParabolicC0AlphaWith (Bv i) (Hv i) α (fun z => v z i) s)
    (hw : ∀ i, ParabolicC0AlphaWith (Bw i) (Hw i) α (fun z => w z i) s) :
    ParabolicC0AlphaWith (vectorDotBoundConst Bv Bw) (vectorDotHolderConst Bv Hv Bw Hw)
      α (fun z => ∑ i : n, v z i * w z i) s := by
  classical
  simpa [vectorDotBoundConst, vectorDotHolderConst] using
    (ParabolicC0AlphaWith.finset_sum_mul (X := X) (α := α) (s := s)
      (S := (Finset.univ : Finset n))
      (Bu := fun i => Bv i) (Hu := fun i => Hv i)
      (Bv := fun i => Bw i) (Hv := fun i => Hw i)
      (u := fun i z => v z i) (v := fun i z => w z i)
      (fun i _hi => hv i) (fun i _hi => hw i) (fun i _hi => hBv i))

/-- Quantitative sup constant for the difference of two finite dot products. -/
def vectorDotSubBoundConst {n : Type*} [Fintype n]
    (Bv Bw' Bvd Bwd : n → ℝ) : ℝ :=
  Finset.univ.sum fun i : n => Bv i * Bwd i + Bvd i * Bw' i

/-- Quantitative Holder constant for the difference of two finite dot products. -/
def vectorDotSubHolderConst {n : Type*} [Fintype n]
    (Bv Hv Bw' Hw' Bvd Hvd Bwd Hwd : n → ℝ) : ℝ :=
  Finset.univ.sum fun i : n =>
    (Bv i * Hwd i + Bwd i * Hv i) + (Bvd i * Hw' i + Bw' i * Hvd i)

theorem vectorDotSubBoundConst_nonneg {n : Type*} [Fintype n]
    {Bv Bw' Bvd Bwd : n → ℝ} (hBv : ∀ i, 0 ≤ Bv i)
    (hBw' : ∀ i, 0 ≤ Bw' i) (hBvd : ∀ i, 0 ≤ Bvd i)
    (hBwd : ∀ i, 0 ≤ Bwd i) :
    0 ≤ vectorDotSubBoundConst Bv Bw' Bvd Bwd := by
  simpa [vectorDotSubBoundConst] using
    (Finset.sum_nonneg fun i _hi =>
      add_nonneg (mul_nonneg (hBv i) (hBwd i)) (mul_nonneg (hBvd i) (hBw' i)))

theorem vectorDotSubHolderConst_nonneg {n : Type*} [Fintype n]
    {Bv Hv Bw' Hw' Bvd Hvd Bwd Hwd : n → ℝ} (hBv : ∀ i, 0 ≤ Bv i)
    (hHv : ∀ i, 0 ≤ Hv i) (hBw' : ∀ i, 0 ≤ Bw' i)
    (hHw' : ∀ i, 0 ≤ Hw' i) (hBvd : ∀ i, 0 ≤ Bvd i)
    (hHvd : ∀ i, 0 ≤ Hvd i) (hBwd : ∀ i, 0 ≤ Bwd i)
    (hHwd : ∀ i, 0 ≤ Hwd i) :
    0 ≤ vectorDotSubHolderConst Bv Hv Bw' Hw' Bvd Hvd Bwd Hwd := by
  simpa [vectorDotSubHolderConst] using
    (Finset.sum_nonneg fun i _hi =>
      add_nonneg
        (add_nonneg (mul_nonneg (hBv i) (hHwd i)) (mul_nonneg (hBwd i) (hHv i)))
        (add_nonneg (mul_nonneg (hBvd i) (hHw' i)) (mul_nonneg (hBw' i) (hHvd i))))

/-- Differences of finite dot products have an explicit bounded parabolic `C^{0,α}` estimate. -/
theorem vector_dot_sub_with {n A : Type*} [Fintype n] [NormedRing A]
    {Bv Hv Bw' Hw' Bvd Hvd Bwd Hwd : n → ℝ}
    {v v' w w' : ℝ × X → n → A}
    (hv : ∀ i, ParabolicC0AlphaWith (Bv i) (Hv i) α (fun z => v z i) s)
    (hw' : ∀ i, ParabolicC0AlphaWith (Bw' i) (Hw' i) α (fun z => w' z i) s)
    (hvdiff : ∀ i, ParabolicC0AlphaWith (Bvd i) (Hvd i) α
      (fun z => v z i - v' z i) s)
    (hwdiff : ∀ i, ParabolicC0AlphaWith (Bwd i) (Hwd i) α
      (fun z => w z i - w' z i) s)
    (hBv : ∀ i, 0 ≤ Bv i) (hBvd : ∀ i, 0 ≤ Bvd i) :
    ParabolicC0AlphaWith
      (vectorDotSubBoundConst Bv Bw' Bvd Bwd)
      (vectorDotSubHolderConst Bv Hv Bw' Hw' Bvd Hvd Bwd Hwd)
      α (fun z => (∑ i : n, v z i * w z i) - ∑ i : n, v' z i * w' z i) s := by
  classical
  simpa [vectorDotSubBoundConst, vectorDotSubHolderConst] using
    (ParabolicC0AlphaWith.finset_sum_mul_sub_sum_mul (X := X) (α := α) (s := s)
      (S := (Finset.univ : Finset n))
      (Bu := Bv) (Hu := Hv) (Bv := Bw') (Hv := Hw')
      (Bdu := Bvd) (Hdu := Hvd) (Bdv := Bwd) (Hdv := Hwd)
      (u := fun i z => v z i) (u' := fun i z => v' z i)
      (v := fun i z => w z i) (v' := fun i z => w' z i)
      (fun i _hi => hv i) (fun i _hi => hw' i)
      (fun i _hi => hvdiff i) (fun i _hi => hwdiff i)
      (fun i _hi => hBv i) (fun i _hi => hBvd i))

/-- Quantitative sup constant for the difference of two finite bilinear matrix contractions
`v · (M w)`. -/
def matrixBilinearEntrySubBoundConst {m n : Type*} [Fintype m] [Fintype n]
    (Bv : m → ℝ) (BM' : m → n → ℝ) (Bw' : n → ℝ) (Bvd : m → ℝ)
    (BM BMd : m → n → ℝ) (Bwd : n → ℝ) : ℝ :=
  vectorDotSubBoundConst Bv (fun i => matrixMulVecEntryBoundConst BM' Bw' i) Bvd
    (fun i => matrixMulVecEntrySubBoundConst BM Bw' BMd Bwd i)

/-- Quantitative Holder constant for the difference of two finite bilinear matrix contractions
`v · (M w)`. -/
def matrixBilinearEntrySubHolderConst {m n : Type*} [Fintype m] [Fintype n]
    (Bv Hv : m → ℝ) (BM' HM' : m → n → ℝ) (Bw' Hw' : n → ℝ)
    (Bvd Hvd : m → ℝ) (BM HM BMd HMd : m → n → ℝ) (Bwd Hwd : n → ℝ) :
    ℝ :=
  vectorDotSubHolderConst Bv Hv
    (fun i => matrixMulVecEntryBoundConst BM' Bw' i)
    (fun i => matrixMulVecEntryHolderConst BM' HM' Bw' Hw' i)
    Bvd Hvd
    (fun i => matrixMulVecEntrySubBoundConst BM Bw' BMd Bwd i)
    (fun i => matrixMulVecEntrySubHolderConst BM HM Bw' Hw' BMd HMd Bwd Hwd i)

theorem matrixBilinearEntrySubBoundConst_nonneg {m n : Type*} [Fintype m] [Fintype n]
    {Bv : m → ℝ} {BM' : m → n → ℝ} {Bw' : n → ℝ} {Bvd : m → ℝ}
    {BM BMd : m → n → ℝ} {Bwd : n → ℝ}
    (hBv : ∀ i, 0 ≤ Bv i) (hBM' : ∀ i j, 0 ≤ BM' i j)
    (hBw' : ∀ j, 0 ≤ Bw' j) (hBvd : ∀ i, 0 ≤ Bvd i)
    (hBM : ∀ i j, 0 ≤ BM i j) (hBMd : ∀ i j, 0 ≤ BMd i j)
    (hBwd : ∀ j, 0 ≤ Bwd j) :
    0 ≤ matrixBilinearEntrySubBoundConst Bv BM' Bw' Bvd BM BMd Bwd := by
  simpa [matrixBilinearEntrySubBoundConst] using
    (vectorDotSubBoundConst_nonneg hBv
      (fun i => matrixMulVecEntryBoundConst_nonneg hBM' hBw' i) hBvd
      (fun i => matrixMulVecEntrySubBoundConst_nonneg hBM hBw' hBMd hBwd i))

theorem matrixBilinearEntrySubHolderConst_nonneg {m n : Type*} [Fintype m] [Fintype n]
    {Bv Hv : m → ℝ} {BM' HM' : m → n → ℝ} {Bw' Hw' : n → ℝ}
    {Bvd Hvd : m → ℝ} {BM HM BMd HMd : m → n → ℝ} {Bwd Hwd : n → ℝ}
    (hBv : ∀ i, 0 ≤ Bv i) (hHv : ∀ i, 0 ≤ Hv i)
    (hBM' : ∀ i j, 0 ≤ BM' i j) (hHM' : ∀ i j, 0 ≤ HM' i j)
    (hBw' : ∀ j, 0 ≤ Bw' j) (hHw' : ∀ j, 0 ≤ Hw' j)
    (hBvd : ∀ i, 0 ≤ Bvd i) (hHvd : ∀ i, 0 ≤ Hvd i)
    (hBM : ∀ i j, 0 ≤ BM i j) (hHM : ∀ i j, 0 ≤ HM i j)
    (hBMd : ∀ i j, 0 ≤ BMd i j) (hHMd : ∀ i j, 0 ≤ HMd i j)
    (hBwd : ∀ j, 0 ≤ Bwd j) (hHwd : ∀ j, 0 ≤ Hwd j) :
    0 ≤ matrixBilinearEntrySubHolderConst Bv Hv BM' HM' Bw' Hw' Bvd Hvd
      BM HM BMd HMd Bwd Hwd := by
  simpa [matrixBilinearEntrySubHolderConst] using
    (vectorDotSubHolderConst_nonneg hBv hHv
      (fun i => matrixMulVecEntryBoundConst_nonneg hBM' hBw' i)
      (fun i => matrixMulVecEntryHolderConst_nonneg hBM' hHM' hBw' hHw' i)
      hBvd hHvd
      (fun i => matrixMulVecEntrySubBoundConst_nonneg hBM hBw' hBMd hBwd i)
      (fun i =>
        matrixMulVecEntrySubHolderConst_nonneg hBM hHM hBw' hHw' hBMd hHMd hBwd hHwd i))

/-- Differences of finite bilinear matrix contractions have an explicit bounded parabolic
`C^{0,α}` estimate. -/
theorem matrix_bilinear_entry_sub_with {m n A : Type*} [Fintype m] [Fintype n]
    [NormedRing A]
    {Bv Hv Bvd Hvd : m → ℝ} {BM HM BM' HM' BMd HMd : m → n → ℝ}
    {Bw' Hw' Bwd Hwd : n → ℝ}
    {v v' : ℝ × X → m → A} {M M' : ℝ × X → Matrix m n A}
    {w w' : ℝ × X → n → A}
    (hv : ∀ i, ParabolicC0AlphaWith (Bv i) (Hv i) α (fun z => v z i) s)
    (hM : ∀ i j, ParabolicC0AlphaWith (BM i j) (HM i j) α
      (fun z => M z i j) s)
    (hM' : ∀ i j, ParabolicC0AlphaWith (BM' i j) (HM' i j) α
      (fun z => M' z i j) s)
    (hw' : ∀ j, ParabolicC0AlphaWith (Bw' j) (Hw' j) α (fun z => w' z j) s)
    (hvdiff : ∀ i, ParabolicC0AlphaWith (Bvd i) (Hvd i) α
      (fun z => v z i - v' z i) s)
    (hMdiff : ∀ i j, ParabolicC0AlphaWith (BMd i j) (HMd i j) α
      (fun z => M z i j - M' z i j) s)
    (hwdiff : ∀ j, ParabolicC0AlphaWith (Bwd j) (Hwd j) α
      (fun z => w z j - w' z j) s)
    (hBv : ∀ i, 0 ≤ Bv i) (hBM : ∀ i j, 0 ≤ BM i j)
    (hBM' : ∀ i j, 0 ≤ BM' i j) (hBMd : ∀ i j, 0 ≤ BMd i j)
    (hBvd : ∀ i, 0 ≤ Bvd i) :
    ParabolicC0AlphaWith
      (matrixBilinearEntrySubBoundConst Bv BM' Bw' Bvd BM BMd Bwd)
      (matrixBilinearEntrySubHolderConst Bv Hv BM' HM' Bw' Hw' Bvd Hvd
        BM HM BMd HMd Bwd Hwd)
      α (fun z =>
        (∑ i : m, v z i * (M z).mulVec (w z) i) -
          ∑ i : m, v' z i * (M' z).mulVec (w' z) i) s := by
  classical
  simpa [matrixBilinearEntrySubBoundConst, matrixBilinearEntrySubHolderConst] using
    (vector_dot_sub_with (X := X) (α := α) (s := s)
      (Bv := Bv) (Hv := Hv)
      (Bw' := fun i => matrixMulVecEntryBoundConst BM' Bw' i)
      (Hw' := fun i => matrixMulVecEntryHolderConst BM' HM' Bw' Hw' i)
      (Bvd := Bvd) (Hvd := Hvd)
      (Bwd := fun i => matrixMulVecEntrySubBoundConst BM Bw' BMd Bwd i)
      (Hwd := fun i => matrixMulVecEntrySubHolderConst BM HM Bw' Hw' BMd HMd Bwd Hwd i)
      (v := v) (v' := v')
      (w := fun z i => (M z).mulVec (w z) i)
      (w' := fun z i => (M' z).mulVec (w' z) i)
      hv
      (fun i => matrix_mulVec_entry_with (M := M') (v := w') hBM' hM' hw' i)
      hvdiff
      (fun i => matrix_mulVec_entry_sub_with (M := M) (M' := M') (v := w) (v' := w')
        hM hw' hMdiff hwdiff hBM hBMd i)
      hBv hBvd)

/-- Finite bilinear matrix contractions `v · (M w)` preserve parabolic `C^{0,α}` control from
entrywise control. -/
theorem matrix_bilinear_entry {m n A : Type*} [Fintype m] [Fintype n] [NormedRing A]
    {v : ℝ × X → m → A} {M : ℝ × X → Matrix m n A} {w : ℝ × X → n → A}
    (hv : ∀ i, ParabolicC0AlphaOn α (fun z => v z i) s)
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s)
    (hw : ∀ j, ParabolicC0AlphaOn α (fun z => w z j) s) :
    ParabolicC0AlphaOn α (fun z => ∑ i : m, v z i * (M z).mulVec (w z) i) s :=
  vector_dot_entry hv (fun i => matrix_mulVec_entry hM hw i)

/-- Quantitative sup constant for a finite bilinear matrix contraction `v · (M w)`. -/
def matrixBilinearEntryBoundConst {m n : Type*} [Fintype m] [Fintype n]
    (Bv : m → ℝ) (BM : m → n → ℝ) (Bw : n → ℝ) : ℝ :=
  vectorDotBoundConst Bv (fun i => matrixMulVecEntryBoundConst BM Bw i)

/-- Quantitative Holder constant for a finite bilinear matrix contraction `v · (M w)`. -/
def matrixBilinearEntryHolderConst {m n : Type*} [Fintype m] [Fintype n]
    (Bv Hv : m → ℝ) (BM HM : m → n → ℝ) (Bw Hw : n → ℝ) : ℝ :=
  vectorDotHolderConst Bv Hv (fun i => matrixMulVecEntryBoundConst BM Bw i)
    (fun i => matrixMulVecEntryHolderConst BM HM Bw Hw i)

theorem matrixBilinearEntryBoundConst_nonneg {m n : Type*} [Fintype m] [Fintype n]
    {Bv : m → ℝ} {BM : m → n → ℝ} {Bw : n → ℝ}
    (hBv : ∀ i, 0 ≤ Bv i) (hBM : ∀ i j, 0 ≤ BM i j) (hBw : ∀ j, 0 ≤ Bw j) :
    0 ≤ matrixBilinearEntryBoundConst Bv BM Bw := by
  simpa [matrixBilinearEntryBoundConst] using
    (vectorDotBoundConst_nonneg hBv
      (fun i => matrixMulVecEntryBoundConst_nonneg hBM hBw i))

theorem matrixBilinearEntryHolderConst_nonneg {m n : Type*} [Fintype m] [Fintype n]
    {Bv Hv : m → ℝ} {BM HM : m → n → ℝ} {Bw Hw : n → ℝ}
    (hBv : ∀ i, 0 ≤ Bv i) (hHv : ∀ i, 0 ≤ Hv i)
    (hBM : ∀ i j, 0 ≤ BM i j) (hHM : ∀ i j, 0 ≤ HM i j)
    (hBw : ∀ j, 0 ≤ Bw j) (hHw : ∀ j, 0 ≤ Hw j) :
    0 ≤ matrixBilinearEntryHolderConst Bv Hv BM HM Bw Hw := by
  simpa [matrixBilinearEntryHolderConst] using
    (vectorDotHolderConst_nonneg hBv hHv
      (fun i => matrixMulVecEntryBoundConst_nonneg hBM hBw i)
      (fun i => matrixMulVecEntryHolderConst_nonneg hBM hHM hBw hHw i))

/-- Finite bilinear matrix contractions `v · (M w)` have an explicit bounded parabolic
`C^{0,α}` estimate. -/
theorem matrix_bilinear_entry_with {m n A : Type*} [Fintype m] [Fintype n]
    [NormedRing A]
    {Bv Hv : m → ℝ} {BM HM : m → n → ℝ} {Bw Hw : n → ℝ}
    {v : ℝ × X → m → A} {M : ℝ × X → Matrix m n A} {w : ℝ × X → n → A}
    (hBv : ∀ i, 0 ≤ Bv i) (hBM : ∀ i j, 0 ≤ BM i j)
    (hv : ∀ i, ParabolicC0AlphaWith (Bv i) (Hv i) α (fun z => v z i) s)
    (hM : ∀ i j, ParabolicC0AlphaWith (BM i j) (HM i j) α
      (fun z => M z i j) s)
    (hw : ∀ j, ParabolicC0AlphaWith (Bw j) (Hw j) α (fun z => w z j) s) :
    ParabolicC0AlphaWith (matrixBilinearEntryBoundConst Bv BM Bw)
      (matrixBilinearEntryHolderConst Bv Hv BM HM Bw Hw) α
      (fun z => ∑ i : m, v z i * (M z).mulVec (w z) i) s := by
  classical
  simpa [matrixBilinearEntryBoundConst, matrixBilinearEntryHolderConst] using
    (vector_dot_with (X := X) (α := α) (s := s)
      (Bv := Bv) (Hv := Hv)
      (Bw := fun i => matrixMulVecEntryBoundConst BM Bw i)
      (Hw := fun i => matrixMulVecEntryHolderConst BM HM Bw Hw i)
      (v := v) (w := fun z i => (M z).mulVec (w z) i)
      hBv hv
      (fun i => matrix_mulVec_entry_with (M := M) (v := w) hBM hM hw i))

/-- Finite bilinear contractions through an inverse matrix `v · (M⁻¹ w)` preserve parabolic
`C^{0,α}` control when the matrix determinant is uniformly bounded away from zero. -/
theorem matrix_inv_bilinear_entry {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {δ : ℝ} {v : ℝ × X → n → 𝕜} {M : ℝ × X → Matrix n n 𝕜}
    {w : ℝ × X → n → 𝕜}
    (hv : ∀ i, ParabolicC0AlphaOn α (fun z => v z i) s)
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s)
    (hw : ∀ j, ParabolicC0AlphaOn α (fun z => w z j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaOn α (fun z => ∑ i : n, v z i * ((M z)⁻¹).mulVec (w z) i) s :=
  vector_dot_entry hv (fun i => matrix_inv_mulVec_entry hM hw hδpos hdet i)

/-- Quantitative sup constant for a finite inverse-bilinear matrix contraction
`v · (M⁻¹ w)`. -/
def matrixInvBilinearEntryBoundConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (Bv : n → ℝ) (B : n → n → ℝ) (Bw : n → ℝ) :
    ℝ :=
  vectorDotBoundConst Bv (fun i => matrixInvMulVecEntryBoundConst (𝕜 := 𝕜) δ B Bw i)

/-- Quantitative Holder constant for a finite inverse-bilinear matrix contraction
`v · (M⁻¹ w)`. -/
def matrixInvBilinearEntryHolderConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (Bv Hv : n → ℝ) (B H : n → n → ℝ) (Bw Hw : n → ℝ) :
    ℝ :=
  vectorDotHolderConst Bv Hv
    (fun i => matrixInvMulVecEntryBoundConst (𝕜 := 𝕜) δ B Bw i)
    (fun i => matrixInvMulVecEntryHolderConst (𝕜 := 𝕜) δ B H Bw Hw i)

theorem matrixInvBilinearEntryBoundConst_nonneg {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {Bv : n → ℝ} {B : n → n → ℝ}
    {Bw : n → ℝ} (hδpos : 0 < δ)
    (hBv : ∀ i, 0 ≤ Bv i) (hBw : ∀ i, 0 ≤ Bw i) :
    0 ≤ matrixInvBilinearEntryBoundConst (𝕜 := 𝕜) δ Bv B Bw := by
  simpa [matrixInvBilinearEntryBoundConst] using
    (vectorDotBoundConst_nonneg hBv
      (fun i => matrixInvMulVecEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos hBw i))

theorem matrixInvBilinearEntryHolderConst_nonneg {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {Bv Hv : n → ℝ} {B H : n → n → ℝ}
    {Bw Hw : n → ℝ} (hH : ∀ i j, 0 ≤ H i j) (hδpos : 0 < δ)
    (hBv : ∀ i, 0 ≤ Bv i) (hHv : ∀ i, 0 ≤ Hv i)
    (hBw : ∀ i, 0 ≤ Bw i) (hHw : ∀ i, 0 ≤ Hw i) :
    0 ≤ matrixInvBilinearEntryHolderConst (𝕜 := 𝕜) δ Bv Hv B H Bw Hw := by
  simpa [matrixInvBilinearEntryHolderConst] using
    (vectorDotHolderConst_nonneg hBv hHv
      (fun i => matrixInvMulVecEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos hBw i)
      (fun i => matrixInvMulVecEntryHolderConst_nonneg (𝕜 := 𝕜) hH hδpos hBw hHw i))

/-- Finite inverse-bilinear matrix contractions `v · (M⁻¹ w)` have an explicit bounded
parabolic `C^{0,α}` estimate under a determinant lower bound. -/
theorem matrix_inv_bilinear_entry_with {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {Bv Hv : n → ℝ} {B H : n → n → ℝ} {Bw Hw : n → ℝ} {δ : ℝ}
    {v : ℝ × X → n → 𝕜} {M : ℝ × X → Matrix n n 𝕜}
    {w : ℝ × X → n → 𝕜}
    (hBv : ∀ i, 0 ≤ Bv i) (hH : ∀ i j, 0 ≤ H i j)
    (hv : ∀ i, ParabolicC0AlphaWith (Bv i) (Hv i) α (fun z => v z i) s)
    (hM : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => M z i j) s)
    (hw : ∀ i, ParabolicC0AlphaWith (Bw i) (Hw i) α (fun z => w z i) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaWith
      (matrixInvBilinearEntryBoundConst (𝕜 := 𝕜) δ Bv B Bw)
      (matrixInvBilinearEntryHolderConst (𝕜 := 𝕜) δ Bv Hv B H Bw Hw)
      α (fun z => ∑ i : n, v z i * ((M z)⁻¹).mulVec (w z) i) s := by
  simpa [matrixInvBilinearEntryBoundConst, matrixInvBilinearEntryHolderConst] using
    (vector_dot_with (X := X) (α := α) (s := s)
      (Bv := Bv) (Hv := Hv)
      (Bw := fun i => matrixInvMulVecEntryBoundConst (𝕜 := 𝕜) δ B Bw i)
      (Hw := fun i => matrixInvMulVecEntryHolderConst (𝕜 := 𝕜) δ B H Bw Hw i)
      (v := v) (w := fun z i => ((M z)⁻¹).mulVec (w z) i)
      hBv hv
      (fun i => matrix_inv_mulVec_entry_with (M := M) (v := w) hH hM hw hδpos hdet i))

/-- Quantitative sup constant for the difference of two finite inverse-bilinear contractions
`v · (M⁻¹ w)`. -/
def matrixInvBilinearEntrySubBoundConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (Bv : n → ℝ) (B : n → n → ℝ) (Bw' : n → ℝ)
    (Bvd : n → ℝ) (Bd : n → n → ℝ) (Bwd : n → ℝ) : ℝ :=
  vectorDotSubBoundConst Bv
    (fun i => matrixInvMulVecEntryBoundConst (𝕜 := 𝕜) δ B Bw' i) Bvd
    (fun i =>
      matrixMulVecEntrySubBoundConst
        (fun r c => matrixInvEntryBoundConst (𝕜 := 𝕜) δ B r c) Bw'
        (fun r c => matrixInvEntrySubBoundConst (𝕜 := 𝕜) δ B Bd r c) Bwd i)

/-- Quantitative Holder constant for the difference of two finite inverse-bilinear contractions
`v · (M⁻¹ w)`. -/
def matrixInvBilinearEntrySubHolderConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (Bv Hv : n → ℝ) (B H : n → n → ℝ)
    (Bw' Hw' : n → ℝ) (Bvd Hvd : n → ℝ) (Bd Hd : n → n → ℝ)
    (Bwd Hwd : n → ℝ) : ℝ :=
  vectorDotSubHolderConst Bv Hv
    (fun i => matrixInvMulVecEntryBoundConst (𝕜 := 𝕜) δ B Bw' i)
    (fun i => matrixInvMulVecEntryHolderConst (𝕜 := 𝕜) δ B H Bw' Hw' i)
    Bvd Hvd
    (fun i =>
      matrixMulVecEntrySubBoundConst
        (fun r c => matrixInvEntryBoundConst (𝕜 := 𝕜) δ B r c) Bw'
        (fun r c => matrixInvEntrySubBoundConst (𝕜 := 𝕜) δ B Bd r c) Bwd i)
    (fun i =>
      matrixMulVecEntrySubHolderConst
        (fun r c => matrixInvEntryBoundConst (𝕜 := 𝕜) δ B r c)
        (fun r c => matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H r c) Bw' Hw'
        (fun r c => matrixInvEntrySubBoundConst (𝕜 := 𝕜) δ B Bd r c)
        (fun r c => matrixInvEntrySubHolderConst (𝕜 := 𝕜) δ B H Bd Hd r c)
        Bwd Hwd i)

theorem matrixInvBilinearEntrySubBoundConst_nonneg {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {Bv : n → ℝ} {B : n → n → ℝ}
    {Bw' : n → ℝ} {Bvd : n → ℝ} {Bd : n → n → ℝ} {Bwd : n → ℝ}
    (hδpos : 0 < δ) (hBv : ∀ i, 0 ≤ Bv i) (hBw' : ∀ i, 0 ≤ Bw' i)
    (hBvd : ∀ i, 0 ≤ Bvd i) (hBd : ∀ i j, 0 ≤ Bd i j)
    (hBwd : ∀ i, 0 ≤ Bwd i) :
    0 ≤ matrixInvBilinearEntrySubBoundConst (𝕜 := 𝕜) δ Bv B Bw' Bvd Bd Bwd := by
  simpa [matrixInvBilinearEntrySubBoundConst] using
    (vectorDotSubBoundConst_nonneg hBv
      (fun i => matrixInvMulVecEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos hBw' i)
      hBvd
      (fun i =>
        matrixMulVecEntrySubBoundConst_nonneg
          (fun r c => matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos B r c)
          hBw'
          (fun r c => matrixInvEntrySubBoundConst_nonneg (𝕜 := 𝕜) hδpos hBd r c)
          hBwd i))

theorem matrixInvBilinearEntrySubHolderConst_nonneg {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {Bv Hv : n → ℝ} {B H : n → n → ℝ}
    {Bw' Hw' : n → ℝ} {Bvd Hvd : n → ℝ} {Bd Hd : n → n → ℝ}
    {Bwd Hwd : n → ℝ} (hδpos : 0 < δ) (hBv : ∀ i, 0 ≤ Bv i)
    (hHv : ∀ i, 0 ≤ Hv i) (hH : ∀ i j, 0 ≤ H i j)
    (hBw' : ∀ i, 0 ≤ Bw' i) (hHw' : ∀ i, 0 ≤ Hw' i)
    (hBvd : ∀ i, 0 ≤ Bvd i) (hHvd : ∀ i, 0 ≤ Hvd i)
    (hBd : ∀ i j, 0 ≤ Bd i j) (hHd : ∀ i j, 0 ≤ Hd i j)
    (hBwd : ∀ i, 0 ≤ Bwd i) (hHwd : ∀ i, 0 ≤ Hwd i) :
    0 ≤ matrixInvBilinearEntrySubHolderConst
      (𝕜 := 𝕜) δ Bv Hv B H Bw' Hw' Bvd Hvd Bd Hd Bwd Hwd := by
  simpa [matrixInvBilinearEntrySubHolderConst] using
    (vectorDotSubHolderConst_nonneg hBv hHv
      (fun i => matrixInvMulVecEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos hBw' i)
      (fun i => matrixInvMulVecEntryHolderConst_nonneg (𝕜 := 𝕜)
        hH hδpos hBw' hHw' i)
      hBvd hHvd
      (fun i =>
        matrixMulVecEntrySubBoundConst_nonneg
          (fun r c => matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos B r c)
          hBw'
          (fun r c => matrixInvEntrySubBoundConst_nonneg (𝕜 := 𝕜) hδpos hBd r c)
          hBwd i)
      (fun i =>
        matrixMulVecEntrySubHolderConst_nonneg
          (fun r c => matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos B r c)
          (fun r c => matrixInvEntryHolderConst_nonneg (𝕜 := 𝕜) hH hδpos r c)
          hBw' hHw'
          (fun r c => matrixInvEntrySubBoundConst_nonneg (𝕜 := 𝕜) hδpos hBd r c)
          (fun r c =>
            matrixInvEntrySubHolderConst_nonneg (𝕜 := 𝕜) hδpos hH hBd hHd r c)
          hBwd hHwd i))

/-- Differences of finite inverse-bilinear contractions `v · (M⁻¹ w)` have an explicit bounded
parabolic `C^{0,α}` estimate under a common determinant lower bound. -/
theorem matrix_inv_bilinear_entry_sub_with {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {Bv Hv Bvd Hvd : n → ℝ} {B H Bd Hd : n → n → ℝ}
    {Bw' Hw' Bwd Hwd : n → ℝ} {δ : ℝ}
    {v v' : ℝ × X → n → 𝕜} {M N : ℝ × X → Matrix n n 𝕜}
    {w w' : ℝ × X → n → 𝕜}
    (hv : ∀ i, ParabolicC0AlphaWith (Bv i) (Hv i) α (fun z => v z i) s)
    (hM : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => M z i j) s)
    (hN : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => N z i j) s)
    (hw' : ∀ i, ParabolicC0AlphaWith (Bw' i) (Hw' i) α (fun z => w' z i) s)
    (hvdiff : ∀ i, ParabolicC0AlphaWith (Bvd i) (Hvd i) α
      (fun z => v z i - v' z i) s)
    (hMdiff : ∀ i j, ParabolicC0AlphaWith (Bd i j) (Hd i j) α
      (fun z => M z i j - N z i j) s)
    (hwdiff : ∀ i, ParabolicC0AlphaWith (Bwd i) (Hwd i) α
      (fun z => w z i - w' z i) s)
    (hBv : ∀ i, 0 ≤ Bv i) (hH : ∀ i j, 0 ≤ H i j)
    (hBd : ∀ i j, 0 ≤ Bd i j) (hHd : ∀ i j, 0 ≤ Hd i j)
    (hBvd : ∀ i, 0 ≤ Bvd i) (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicC0AlphaWith
      (matrixInvBilinearEntrySubBoundConst (𝕜 := 𝕜) δ Bv B Bw' Bvd Bd Bwd)
      (matrixInvBilinearEntrySubHolderConst
        (𝕜 := 𝕜) δ Bv Hv B H Bw' Hw' Bvd Hvd Bd Hd Bwd Hwd)
      α (fun z =>
        (∑ i : n, v z i * ((M z)⁻¹).mulVec (w z) i) -
          ∑ i : n, v' z i * ((N z)⁻¹).mulVec (w' z) i) s := by
  classical
  simpa [matrixInvBilinearEntrySubBoundConst, matrixInvBilinearEntrySubHolderConst] using
    (vector_dot_sub_with (X := X) (α := α) (s := s)
      (Bv := Bv) (Hv := Hv)
      (Bw' := fun i => matrixInvMulVecEntryBoundConst (𝕜 := 𝕜) δ B Bw' i)
      (Hw' := fun i => matrixInvMulVecEntryHolderConst (𝕜 := 𝕜) δ B H Bw' Hw' i)
      (Bvd := Bvd) (Hvd := Hvd)
      (Bwd := fun i =>
        matrixMulVecEntrySubBoundConst
          (fun r c => matrixInvEntryBoundConst (𝕜 := 𝕜) δ B r c) Bw'
          (fun r c => matrixInvEntrySubBoundConst (𝕜 := 𝕜) δ B Bd r c) Bwd i)
      (Hwd := fun i =>
        matrixMulVecEntrySubHolderConst
          (fun r c => matrixInvEntryBoundConst (𝕜 := 𝕜) δ B r c)
          (fun r c => matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H r c) Bw' Hw'
          (fun r c => matrixInvEntrySubBoundConst (𝕜 := 𝕜) δ B Bd r c)
          (fun r c => matrixInvEntrySubHolderConst (𝕜 := 𝕜) δ B H Bd Hd r c)
          Bwd Hwd i)
      (v := v) (v' := v')
      (w := fun z i => ((M z)⁻¹).mulVec (w z) i)
      (w' := fun z i => ((N z)⁻¹).mulVec (w' z) i)
      hv
      (fun i => matrix_inv_mulVec_entry_with (M := N) (v := w') hH hN hw' hδpos hdetN i)
      hvdiff
      (fun i =>
        matrix_mulVec_entry_sub_with
          (M := fun z => (M z)⁻¹) (M' := fun z => (N z)⁻¹) (v := w) (v' := w')
          (BM := fun r c => matrixInvEntryBoundConst (𝕜 := 𝕜) δ B r c)
          (HM := fun r c => matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H r c)
          (Bv' := Bw') (Hv' := Hw')
          (BMd := fun r c => matrixInvEntrySubBoundConst (𝕜 := 𝕜) δ B Bd r c)
          (HMd := fun r c => matrixInvEntrySubHolderConst (𝕜 := 𝕜) δ B H Bd Hd r c)
          (Bvd := Bwd) (Hvd := Hwd)
          (fun r c => matrix_inv_entry_with (M := M) hH hM hδpos hdetM r c)
          hw'
          (fun r c =>
            matrix_inv_entry_sub_with
              (M := M) (N := N) hH hBd hHd hM hN hMdiff hδpos hdetM hdetN r c)
          hwdiff
          (fun r c => matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos B r c)
          (fun r c => matrixInvEntrySubBoundConst_nonneg (𝕜 := 𝕜) hδpos hBd r c)
          i)
      hBv hBvd)

end ParabolicC0AlphaOn

namespace ParabolicC0AlphaNormLe

variable {X : Type*} [PseudoMetricSpace X]
variable {α : ℝ} {s : Set (ℝ × X)}

/-- Componentwise single-radius control packages finite dot products with the corresponding
quantitative product radius. -/
theorem vector_dot_of_entries {n A : Type*} [Fintype n] [NormedRing A]
    {Rv Rw : n → ℝ} {v w : ℝ × X → n → A}
    (hv : ∀ i, ParabolicC0AlphaNormLe (Rv i) α (fun z => v z i) s)
    (hw : ∀ i, ParabolicC0AlphaNormLe (Rw i) α (fun z => w z i) s) :
    ParabolicC0AlphaNormLe
      (ParabolicC0AlphaOn.vectorDotBoundConst Rv Rw +
        ParabolicC0AlphaOn.vectorDotHolderConst Rv Rv Rw Rw)
      α (fun z => ∑ i : n, v z i * w z i) s := by
  have hRv : ∀ i, 0 ≤ Rv i := fun i => (hv i).nonneg
  have hRw : ∀ i, 0 ≤ Rw i := fun i => (hw i).nonneg
  exact ParabolicC0AlphaNormLe.of_c0AlphaWith
    (ParabolicC0AlphaOn.vectorDotBoundConst_nonneg hRv hRw)
    (ParabolicC0AlphaOn.vectorDotHolderConst_nonneg hRv hRv hRw hRw)
    (ParabolicC0AlphaOn.vector_dot_with
      (v := v) (w := w) (Bv := Rv) (Hv := Rv) (Bw := Rw) (Hw := Rw)
      hRv
      (fun i => ParabolicC0AlphaNormLe.c0AlphaWith_self (hv i))
      (fun i => ParabolicC0AlphaNormLe.c0AlphaWith_self (hw i)))

/-- Componentwise single-radius controls of two vector pairs and their differences package finite
dot-product differences with the corresponding quantitative product-difference radius. -/
theorem vector_dot_sub_of_entries {n A : Type*} [Fintype n] [NormedRing A]
    {Rv Rw' Rvd Rwd : n → ℝ} {v v' w w' : ℝ × X → n → A}
    (hv : ∀ i, ParabolicC0AlphaNormLe (Rv i) α (fun z => v z i) s)
    (hw' : ∀ i, ParabolicC0AlphaNormLe (Rw' i) α (fun z => w' z i) s)
    (hvdiff : ∀ i, ParabolicC0AlphaNormLe (Rvd i) α
      (fun z => v z i - v' z i) s)
    (hwdiff : ∀ i, ParabolicC0AlphaNormLe (Rwd i) α
      (fun z => w z i - w' z i) s) :
    ParabolicC0AlphaNormLe
      (ParabolicC0AlphaOn.vectorDotSubBoundConst Rv Rw' Rvd Rwd +
        ParabolicC0AlphaOn.vectorDotSubHolderConst Rv Rv Rw' Rw' Rvd Rvd Rwd Rwd)
      α (fun z => (∑ i : n, v z i * w z i) - ∑ i : n, v' z i * w' z i) s := by
  have hRv : ∀ i, 0 ≤ Rv i := fun i => (hv i).nonneg
  have hRw' : ∀ i, 0 ≤ Rw' i := fun i => (hw' i).nonneg
  have hRvd : ∀ i, 0 ≤ Rvd i := fun i => (hvdiff i).nonneg
  have hRwd : ∀ i, 0 ≤ Rwd i := fun i => (hwdiff i).nonneg
  exact ParabolicC0AlphaNormLe.of_c0AlphaWith
    (ParabolicC0AlphaOn.vectorDotSubBoundConst_nonneg hRv hRw' hRvd hRwd)
    (ParabolicC0AlphaOn.vectorDotSubHolderConst_nonneg
      hRv hRv hRw' hRw' hRvd hRvd hRwd hRwd)
    (ParabolicC0AlphaOn.vector_dot_sub_with
      (v := v) (v' := v') (w := w) (w' := w')
      (Bv := Rv) (Hv := Rv) (Bw' := Rw') (Hw' := Rw')
      (Bvd := Rvd) (Hvd := Rvd) (Bwd := Rwd) (Hwd := Rwd)
      (fun i => ParabolicC0AlphaNormLe.c0AlphaWith_self (hv i))
      (fun i => ParabolicC0AlphaNormLe.c0AlphaWith_self (hw' i))
      (fun i => ParabolicC0AlphaNormLe.c0AlphaWith_self (hvdiff i))
      (fun i => ParabolicC0AlphaNormLe.c0AlphaWith_self (hwdiff i))
      hRv hRvd)

/-- Componentwise vector control and entrywise matrix control package finite bilinear matrix
contractions with the corresponding quantitative product radius. -/
theorem matrix_bilinear_entry_of_entries {m n A : Type*} [Fintype m] [Fintype n]
    [NormedRing A] {Rv : m → ℝ} {RM : m → n → ℝ} {Rw : n → ℝ}
    {v : ℝ × X → m → A} {M : ℝ × X → Matrix m n A} {w : ℝ × X → n → A}
    (hv : ∀ i, ParabolicC0AlphaNormLe (Rv i) α (fun z => v z i) s)
    (hM : ∀ i j, ParabolicC0AlphaNormLe (RM i j) α (fun z => M z i j) s)
    (hw : ∀ j, ParabolicC0AlphaNormLe (Rw j) α (fun z => w z j) s) :
    ParabolicC0AlphaNormLe
      (ParabolicC0AlphaOn.matrixBilinearEntryBoundConst Rv RM Rw +
        ParabolicC0AlphaOn.matrixBilinearEntryHolderConst Rv Rv RM RM Rw Rw)
      α (fun z => ∑ i : m, v z i * (M z).mulVec (w z) i) s := by
  have hRv : ∀ i, 0 ≤ Rv i := fun i => (hv i).nonneg
  have hRM : ∀ i j, 0 ≤ RM i j := fun i j => (hM i j).nonneg
  have hRw : ∀ j, 0 ≤ Rw j := fun j => (hw j).nonneg
  exact ParabolicC0AlphaNormLe.of_c0AlphaWith
    (ParabolicC0AlphaOn.matrixBilinearEntryBoundConst_nonneg hRv hRM hRw)
    (ParabolicC0AlphaOn.matrixBilinearEntryHolderConst_nonneg
      hRv hRv hRM hRM hRw hRw)
    (ParabolicC0AlphaOn.matrix_bilinear_entry_with
      (v := v) (M := M) (w := w) (Bv := Rv) (Hv := Rv)
      (BM := RM) (HM := RM) (Bw := Rw) (Hw := Rw)
      hRv hRM
      (fun i => ParabolicC0AlphaNormLe.c0AlphaWith_self (hv i))
      (fun i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hM i j))
      (fun j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hw j)))

/-- Componentwise and entrywise single-radius controls of two bilinear matrix-contraction inputs
and their differences package the bilinear-contraction difference radius. -/
theorem matrix_bilinear_entry_sub_of_entries {m n A : Type*} [Fintype m] [Fintype n]
    [NormedRing A] {Rv Rvd : m → ℝ} {RM RM' RMd : m → n → ℝ}
    {Rw' Rwd : n → ℝ}
    {v v' : ℝ × X → m → A} {M M' : ℝ × X → Matrix m n A}
    {w w' : ℝ × X → n → A}
    (hv : ∀ i, ParabolicC0AlphaNormLe (Rv i) α (fun z => v z i) s)
    (hM : ∀ i j, ParabolicC0AlphaNormLe (RM i j) α (fun z => M z i j) s)
    (hM' : ∀ i j, ParabolicC0AlphaNormLe (RM' i j) α (fun z => M' z i j) s)
    (hw' : ∀ j, ParabolicC0AlphaNormLe (Rw' j) α (fun z => w' z j) s)
    (hvdiff : ∀ i, ParabolicC0AlphaNormLe (Rvd i) α
      (fun z => v z i - v' z i) s)
    (hMdiff : ∀ i j, ParabolicC0AlphaNormLe (RMd i j) α
      (fun z => M z i j - M' z i j) s)
    (hwdiff : ∀ j, ParabolicC0AlphaNormLe (Rwd j) α
      (fun z => w z j - w' z j) s) :
    ParabolicC0AlphaNormLe
      (ParabolicC0AlphaOn.matrixBilinearEntrySubBoundConst
          Rv RM' Rw' Rvd RM RMd Rwd +
        ParabolicC0AlphaOn.matrixBilinearEntrySubHolderConst
          Rv Rv RM' RM' Rw' Rw' Rvd Rvd RM RM RMd RMd Rwd Rwd)
      α (fun z =>
        (∑ i : m, v z i * (M z).mulVec (w z) i) -
          ∑ i : m, v' z i * (M' z).mulVec (w' z) i) s := by
  have hRv : ∀ i, 0 ≤ Rv i := fun i => (hv i).nonneg
  have hRM : ∀ i j, 0 ≤ RM i j := fun i j => (hM i j).nonneg
  have hRM' : ∀ i j, 0 ≤ RM' i j := fun i j => (hM' i j).nonneg
  have hRw' : ∀ j, 0 ≤ Rw' j := fun j => (hw' j).nonneg
  have hRvd : ∀ i, 0 ≤ Rvd i := fun i => (hvdiff i).nonneg
  have hRMd : ∀ i j, 0 ≤ RMd i j := fun i j => (hMdiff i j).nonneg
  have hRwd : ∀ j, 0 ≤ Rwd j := fun j => (hwdiff j).nonneg
  exact ParabolicC0AlphaNormLe.of_c0AlphaWith
    (ParabolicC0AlphaOn.matrixBilinearEntrySubBoundConst_nonneg
      hRv hRM' hRw' hRvd hRM hRMd hRwd)
    (ParabolicC0AlphaOn.matrixBilinearEntrySubHolderConst_nonneg
      hRv hRv hRM' hRM' hRw' hRw' hRvd hRvd hRM hRM hRMd hRMd hRwd hRwd)
    (ParabolicC0AlphaOn.matrix_bilinear_entry_sub_with
      (v := v) (v' := v') (M := M) (M' := M') (w := w) (w' := w')
      (Bv := Rv) (Hv := Rv) (BM := RM) (HM := RM) (BM' := RM') (HM' := RM')
      (Bw' := Rw') (Hw' := Rw') (Bvd := Rvd) (Hvd := Rvd)
      (BMd := RMd) (HMd := RMd) (Bwd := Rwd) (Hwd := Rwd)
      (fun i => ParabolicC0AlphaNormLe.c0AlphaWith_self (hv i))
      (fun i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hM i j))
      (fun i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hM' i j))
      (fun j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hw' j))
      (fun i => ParabolicC0AlphaNormLe.c0AlphaWith_self (hvdiff i))
      (fun i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hMdiff i j))
      (fun j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hwdiff j))
      hRv hRM hRM' hRMd hRvd)

/-- Componentwise vector control, entrywise matrix control, and a determinant lower bound package
finite inverse-bilinear contractions with the corresponding quantitative radius. -/
theorem matrix_inv_bilinear_entry_of_entries {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {Rv : n → ℝ} {R : n → n → ℝ} {Rw : n → ℝ} {δ : ℝ}
    {v : ℝ × X → n → 𝕜} {M : ℝ × X → Matrix n n 𝕜}
    {w : ℝ × X → n → 𝕜}
    (hv : ∀ i, ParabolicC0AlphaNormLe (Rv i) α (fun z => v z i) s)
    (hM : ∀ i j, ParabolicC0AlphaNormLe (R i j) α (fun z => M z i j) s)
    (hw : ∀ j, ParabolicC0AlphaNormLe (Rw j) α (fun z => w z j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaNormLe
      (ParabolicC0AlphaOn.matrixInvBilinearEntryBoundConst (𝕜 := 𝕜) δ Rv R Rw +
        ParabolicC0AlphaOn.matrixInvBilinearEntryHolderConst
          (𝕜 := 𝕜) δ Rv Rv R R Rw Rw)
      α (fun z => ∑ i : n, v z i * ((M z)⁻¹).mulVec (w z) i) s := by
  have hRv : ∀ i, 0 ≤ Rv i := fun i => (hv i).nonneg
  have hR : ∀ i j, 0 ≤ R i j := fun i j => (hM i j).nonneg
  have hRw : ∀ j, 0 ≤ Rw j := fun j => (hw j).nonneg
  exact ParabolicC0AlphaNormLe.of_c0AlphaWith
    (ParabolicC0AlphaOn.matrixInvBilinearEntryBoundConst_nonneg
      (𝕜 := 𝕜) hδpos hRv hRw)
    (ParabolicC0AlphaOn.matrixInvBilinearEntryHolderConst_nonneg
      (𝕜 := 𝕜) hR hδpos hRv hRv hRw hRw)
    (ParabolicC0AlphaOn.matrix_inv_bilinear_entry_with
      (v := v) (M := M) (w := w) (Bv := Rv) (Hv := Rv) (B := R) (H := R)
      (Bw := Rw) (Hw := Rw)
      hRv hR
      (fun i => ParabolicC0AlphaNormLe.c0AlphaWith_self (hv i))
      (fun i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hM i j))
      (fun j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hw j))
      hδpos hdet)

/-- Componentwise and entrywise single-radius controls of two inverse-bilinear inputs, plus a
common determinant lower bound, package the inverse-bilinear contraction difference radius. -/
theorem matrix_inv_bilinear_entry_sub_of_entries {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {Rv Rvd : n → ℝ} {R Rd : n → n → ℝ} {Rw' Rwd : n → ℝ}
    {δ : ℝ} {v v' : ℝ × X → n → 𝕜} {M N : ℝ × X → Matrix n n 𝕜}
    {w w' : ℝ × X → n → 𝕜}
    (hv : ∀ i, ParabolicC0AlphaNormLe (Rv i) α (fun z => v z i) s)
    (hM : ∀ i j, ParabolicC0AlphaNormLe (R i j) α (fun z => M z i j) s)
    (hN : ∀ i j, ParabolicC0AlphaNormLe (R i j) α (fun z => N z i j) s)
    (hw' : ∀ i, ParabolicC0AlphaNormLe (Rw' i) α (fun z => w' z i) s)
    (hvdiff : ∀ i, ParabolicC0AlphaNormLe (Rvd i) α
      (fun z => v z i - v' z i) s)
    (hMdiff : ∀ i j, ParabolicC0AlphaNormLe (Rd i j) α
      (fun z => M z i j - N z i j) s)
    (hwdiff : ∀ i, ParabolicC0AlphaNormLe (Rwd i) α
      (fun z => w z i - w' z i) s)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicC0AlphaNormLe
      (ParabolicC0AlphaOn.matrixInvBilinearEntrySubBoundConst
          (𝕜 := 𝕜) δ Rv R Rw' Rvd Rd Rwd +
        ParabolicC0AlphaOn.matrixInvBilinearEntrySubHolderConst
          (𝕜 := 𝕜) δ Rv Rv R R Rw' Rw' Rvd Rvd Rd Rd Rwd Rwd)
      α (fun z =>
        (∑ i : n, v z i * ((M z)⁻¹).mulVec (w z) i) -
          ∑ i : n, v' z i * ((N z)⁻¹).mulVec (w' z) i) s := by
  have hRv : ∀ i, 0 ≤ Rv i := fun i => (hv i).nonneg
  have hR : ∀ i j, 0 ≤ R i j := fun i j => (hM i j).nonneg
  have hRw' : ∀ i, 0 ≤ Rw' i := fun i => (hw' i).nonneg
  have hRvd : ∀ i, 0 ≤ Rvd i := fun i => (hvdiff i).nonneg
  have hRd : ∀ i j, 0 ≤ Rd i j := fun i j => (hMdiff i j).nonneg
  have hRwd : ∀ i, 0 ≤ Rwd i := fun i => (hwdiff i).nonneg
  exact ParabolicC0AlphaNormLe.of_c0AlphaWith
    (ParabolicC0AlphaOn.matrixInvBilinearEntrySubBoundConst_nonneg
      (𝕜 := 𝕜) hδpos hRv hRw' hRvd hRd hRwd)
    (ParabolicC0AlphaOn.matrixInvBilinearEntrySubHolderConst_nonneg
      (𝕜 := 𝕜) hδpos hRv hRv hR hRw' hRw' hRvd hRvd hRd hRd hRwd hRwd)
    (ParabolicC0AlphaOn.matrix_inv_bilinear_entry_sub_with
      (v := v) (v' := v') (M := M) (N := N) (w := w) (w' := w')
      (Bv := Rv) (Hv := Rv) (Bvd := Rvd) (Hvd := Rvd)
      (B := R) (H := R) (Bd := Rd) (Hd := Rd)
      (Bw' := Rw') (Hw' := Rw') (Bwd := Rwd) (Hwd := Rwd)
      (fun i => ParabolicC0AlphaNormLe.c0AlphaWith_self (hv i))
      (fun i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hM i j))
      (fun i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hN i j))
      (fun i => ParabolicC0AlphaNormLe.c0AlphaWith_self (hw' i))
      (fun i => ParabolicC0AlphaNormLe.c0AlphaWith_self (hvdiff i))
      (fun i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hMdiff i j))
      (fun i => ParabolicC0AlphaNormLe.c0AlphaWith_self (hwdiff i))
      hRv hR hRd hRd hRvd hδpos hdetM hdetN)

end ParabolicC0AlphaNormLe

namespace ParabolicC0AlphaOn

variable {X : Type*} [PseudoMetricSpace X]
variable {α : ℝ} {s : Set (ℝ × X)}

/-- Compact-domain bilinear contraction through an inverse matrix, from entrywise control and
pointwise nonvanishing determinant. -/
theorem matrix_inv_bilinear_entry_of_isCompact_det_ne_zero {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)}
    {v : ℝ × X → n → 𝕜} {M : ℝ × X → Matrix n n 𝕜}
    {w : ℝ × X → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hv : ∀ i, ParabolicC0AlphaOn α (fun z => v z i) K)
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) K)
    (hw : ∀ j, ParabolicC0AlphaOn α (fun z => w z j) K)
    (hdet_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0) :
    ParabolicC0AlphaOn α (fun z => ∑ i : n, v z i * ((M z)⁻¹).mulVec (w z) i) K := by
  rcases matrix_det_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hM hdet_ne with
    ⟨δ, hδpos, hdet⟩
  exact matrix_inv_bilinear_entry hv hM hw hδpos hdet

/-- Compact-domain finite-family inverse-bilinear contraction closure from entrywise vector and
matrix controls, with one determinant lower bound shared by the family. -/
theorem matrix_inv_bilinear_entry_family_of_isCompact_det_ne_zero {ι n 𝕜 : Type*}
    [Fintype ι] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {K : Set (ℝ × X)}
    {v : ι → ℝ × X → n → 𝕜} {M : ι → ℝ × X → Matrix n n 𝕜}
    {w : ι → ℝ × X → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hv : ∀ a i, ParabolicC0AlphaOn α (fun z => v a z i) K)
    (hM : ∀ a i j, ParabolicC0AlphaOn α (fun z => M a z i j) K)
    (hw : ∀ a j, ParabolicC0AlphaOn α (fun z => w a z j) K)
    (hdet_ne : ∀ a ⦃z : ℝ × X⦄, z ∈ K → (M a z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ a ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M a z).det‖) ∧
      ∀ a,
        ParabolicC0AlphaOn α
          (fun z : ℝ × X => ∑ i : n, v a z i * ((M a z)⁻¹).mulVec (w a z) i) K := by
  rcases matrix_det_family_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hM hdet_ne with
    ⟨δ, hδpos, hdet⟩
  refine ⟨δ, hδpos, hdet, ?_⟩
  intro a
  exact matrix_inv_bilinear_entry
    (M := M a) (v := v a) (w := w a) (hv a) (hM a) (hw a) hδpos (hdet a)

/-- A finite family of inverse-bilinear contractions `v · (M⁻¹ w)` has explicit bounded
parabolic `C^{0,α}` estimates with one compact determinant lower bound shared by the family. -/
theorem matrix_inv_bilinear_entry_family_with_of_isCompact_det_ne_zero {ι n 𝕜 : Type*}
    [Fintype ι] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {K : Set (ℝ × X)}
    {Bv Hv : ι → n → ℝ} {B H : ι → n → n → ℝ} {Bw Hw : ι → n → ℝ}
    {v : ι → ℝ × X → n → 𝕜} {M : ι → ℝ × X → Matrix n n 𝕜}
    {w : ι → ℝ × X → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hBv : ∀ a i, 0 ≤ Bv a i) (hB : ∀ a i j, 0 ≤ B a i j)
    (hH : ∀ a i j, 0 ≤ H a i j)
    (hv : ∀ a i,
      ParabolicC0AlphaWith (Bv a i) (Hv a i) α (fun z => v a z i) K)
    (hM : ∀ a i j,
      ParabolicC0AlphaWith (B a i j) (H a i j) α (fun z => M a z i j) K)
    (hw : ∀ a j,
      ParabolicC0AlphaWith (Bw a j) (Hw a j) α (fun z => w a z j) K)
    (hdet_ne : ∀ a ⦃z : ℝ × X⦄, z ∈ K → (M a z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ a ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M a z).det‖) ∧
      ∀ a,
        ParabolicC0AlphaWith
          (matrixInvBilinearEntryBoundConst (𝕜 := 𝕜) δ (Bv a) (B a) (Bw a))
          (matrixInvBilinearEntryHolderConst (𝕜 := 𝕜) δ (Bv a) (Hv a)
            (B a) (H a) (Bw a) (Hw a))
          α
          (fun z : ℝ × X => ∑ i : n, v a z i * ((M a z)⁻¹).mulVec (w a z) i) K := by
  have hMctrl : ∀ a i j, ParabolicC0AlphaOn α (fun z => M a z i j) K := by
    intro a i j
    exact ⟨B a i j, hB a i j, H a i j, hH a i j, hM a i j⟩
  rcases matrix_det_family_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hMctrl hdet_ne with
    ⟨δ, hδpos, hdet⟩
  refine ⟨δ, hδpos, hdet, ?_⟩
  intro a
  exact matrix_inv_bilinear_entry_with
    (M := M a) (v := v a) (w := w a)
    (hBv a) (hH a) (hv a) (hM a) (hw a) hδpos (hdet a)

/-- Compact-domain quantitative bilinear contraction through an inverse matrix, from entrywise
control and pointwise nonvanishing determinant. -/
theorem matrix_inv_bilinear_entry_with_of_isCompact_det_ne_zero {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)}
    {Bv Hv : n → ℝ} {B H : n → n → ℝ} {Bw Hw : n → ℝ}
    {v : ℝ × X → n → 𝕜} {M : ℝ × X → Matrix n n 𝕜}
    {w : ℝ × X → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hBv : ∀ i, 0 ≤ Bv i) (hB : ∀ i j, 0 ≤ B i j)
    (hH : ∀ i j, 0 ≤ H i j)
    (hv : ∀ i, ParabolicC0AlphaWith (Bv i) (Hv i) α (fun z => v z i) K)
    (hM : ∀ i j, ParabolicC0AlphaWith (B i j) (H i j) α (fun z => M z i j) K)
    (hw : ∀ j, ParabolicC0AlphaWith (Bw j) (Hw j) α (fun z => w z j) K)
    (hdet_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvBilinearEntryBoundConst (𝕜 := 𝕜) δ Bv B Bw)
        (matrixInvBilinearEntryHolderConst (𝕜 := 𝕜) δ Bv Hv B H Bw Hw)
        α (fun z : ℝ × X => ∑ i : n, v z i * ((M z)⁻¹).mulVec (w z) i) K := by
  have hMctrl : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) K := by
    intro i j
    exact ⟨B i j, hB i j, H i j, hH i j, hM i j⟩
  rcases matrix_det_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hMctrl hdet_ne with
    ⟨δ, hδpos, hdet⟩
  exact ⟨δ, hδpos, matrix_inv_bilinear_entry_with (M := M) (v := v) (w := w)
    hBv hH hv hM hw hδpos hdet⟩

/-- Christoffel-symbol type inverse-metric contractions preserve parabolic `C^{0,α}` control:
if `M` and the three-index derivative array `D` are controlled entrywise and `det M` is bounded
away from zero, then each finite contraction
`(1 / 2) * M⁻¹ᵢˡ (Dⱼₖₗ + Dₖⱼₗ - Dₗⱼₖ)` is controlled. -/
theorem matrix_inv_christoffel_entry {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {M : ℝ × X → Matrix n n 𝕜}
    {D : ℝ × X → n → n → n → 𝕜}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s)
    (hD : ∀ i j k, ParabolicC0AlphaOn α (fun z => D z i j k) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (i j k : n) :
    ParabolicC0AlphaOn α
      (fun z =>
        (2 : 𝕜)⁻¹ *
          ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) i l *
            (D z j k l + D z k j l - D z l j k)) s := by
  have hvec : ∀ l : n,
      ParabolicC0AlphaOn α (fun z => D z j k l + D z k j l - D z l j k) s := by
    intro l
    exact ((hD j k l).add (hD k j l)).sub (hD l j k)
  have hcontraction :
      ParabolicC0AlphaOn α
        (fun z =>
          ((M z)⁻¹).mulVec (fun l : n => D z j k l + D z k j l - D z l j k) i) s :=
    matrix_inv_mulVec_entry hM hvec hδpos hdet i
  have hhalf :
      ParabolicC0AlphaOn α
        (fun z =>
          (2 : 𝕜)⁻¹ *
            ((M z)⁻¹).mulVec (fun l : n => D z j k l + D z k j l - D z l j k) i) s :=
    (ParabolicC0AlphaOn.const (α := α) (s := s) ((2 : 𝕜)⁻¹)).mul hcontraction
  simpa only [Matrix.mulVec_apply_eq_sum] using hhalf

/-- The full finite Christoffel-symbol type array preserves parabolic `C^{0,α}` control from
entrywise metric and derivative control, under a determinant lower bound. -/
theorem matrix_inv_christoffel {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {M : ℝ × X → Matrix n n 𝕜}
    {D : ℝ × X → n → n → n → 𝕜}
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) s)
    (hD : ∀ i j k, ParabolicC0AlphaOn α (fun z => D z i j k) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaOn α
      (fun z i j k =>
        (2 : 𝕜)⁻¹ *
          ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) i l *
            (D z j k l + D z k j l - D z l j k)) s := by
  refine ParabolicC0AlphaOn.pi ?_
  intro i
  refine ParabolicC0AlphaOn.pi ?_
  intro j
  refine ParabolicC0AlphaOn.pi ?_
  intro k
  exact matrix_inv_christoffel_entry (M := M) (D := D) hM hD hδpos hdet i j k

/-- The Christoffel derivative combination is Lipschitz in its three displayed derivative
entries. -/
theorem christoffelDerivativeCombo_norm_sub_le {n A : Type*} [NormedAddCommGroup A]
    (D E : n → n → n → A) (j k l : n) :
    ‖(D j k l + D k j l - D l j k) - (E j k l + E k j l - E l j k)‖ ≤
      ‖D j k l - E j k l‖ + ‖D k j l - E k j l‖ + ‖D l j k - E l j k‖ := by
  have hsplit :
      (D j k l + D k j l - D l j k) - (E j k l + E k j l - E l j k) =
        (D j k l - E j k l) + (D k j l - E k j l) - (D l j k - E l j k) := by
    abel
  calc
    ‖(D j k l + D k j l - D l j k) - (E j k l + E k j l - E l j k)‖ =
        ‖(D j k l - E j k l) + (D k j l - E k j l) -
          (D l j k - E l j k)‖ := by
      rw [hsplit]
    _ ≤ ‖(D j k l - E j k l) + (D k j l - E k j l)‖ +
        ‖D l j k - E l j k‖ :=
      norm_sub_le _ _
    _ ≤ (‖D j k l - E j k l‖ + ‖D k j l - E k j l‖) +
        ‖D l j k - E l j k‖ :=
      add_le_add_left (norm_add_le _ _) _
    _ = ‖D j k l - E j k l‖ + ‖D k j l - E k j l‖ +
        ‖D l j k - E l j k‖ := by
      ring

/-- A bounded derivative array bounds the Christoffel derivative combination. -/
theorem christoffelDerivativeCombo_norm_le {n A : Type*} [NormedAddCommGroup A]
    {B : n → n → n → ℝ} (D : n → n → n → A)
    (hD : ∀ a b c, ‖D a b c‖ ≤ B a b c) (j k l : n) :
    ‖D j k l + D k j l - D l j k‖ ≤ B j k l + B k j l + B l j k := by
  calc
    ‖D j k l + D k j l - D l j k‖ ≤ ‖D j k l + D k j l‖ + ‖D l j k‖ :=
      norm_sub_le _ _
    _ ≤ (‖D j k l‖ + ‖D k j l‖) + ‖D l j k‖ :=
      add_le_add_left (norm_add_le _ _) _
    _ ≤ (B j k l + B k j l) + B l j k :=
      add_le_add (add_le_add (hD j k l) (hD k j l)) (hD l j k)
    _ = B j k l + B k j l + B l j k := by
      ring

/-- Christoffel-symbol type inverse-metric contractions are pointwise Lipschitz on bounded
derivative arrays and entrywise bounded matrices with a common determinant lower bound. -/
theorem matrix_inv_christoffel_entry_norm_sub_le {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} (M N : Matrix n n 𝕜)
    (D E : n → n → n → 𝕜)
    (hM : ∀ a b, ‖M a b‖ ≤ C a b) (hN : ∀ a b, ‖N a b‖ ≤ C a b)
    (hE : ∀ a b c, ‖E a b c‖ ≤ DB a b c)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖)
    (i j k : n) :
    ‖((2 : 𝕜)⁻¹ *
        ∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l *
          (D j k l + D k j l - D l j k)) -
      ((2 : 𝕜)⁻¹ *
        ∑ l : n, (N⁻¹ : Matrix n n 𝕜) i l *
          (E j k l + E k j l - E l j k))‖ ≤
      ‖(2 : 𝕜)⁻¹‖ *
        ∑ l : n,
          (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l *
              (‖D j k l - E j k l‖ + ‖D k j l - E k j l‖ +
                ‖D l j k - E l j k‖) +
            (DB j k l + DB k j l + DB l j k) *
              matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N i l) := by
  classical
  let comboD : n → 𝕜 := fun l => D j k l + D k j l - D l j k
  let comboE : n → 𝕜 := fun l => E j k l + E k j l - E l j k
  let comboDiffBound : n → ℝ := fun l =>
    ‖D j k l - E j k l‖ + ‖D k j l - E k j l‖ + ‖D l j k - E l j k‖
  let comboBound : n → ℝ := fun l => DB j k l + DB k j l + DB l j k
  let innerBound : ℝ :=
    ∑ l : n,
      (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l * comboDiffBound l +
        comboBound l * matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N i l)
  have hinner :
      ‖(∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l * comboD l) -
          ∑ l : n, (N⁻¹ : Matrix n n 𝕜) i l * comboE l‖ ≤ innerBound := by
    have hsum :
        ‖(∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l * comboD l) -
            ∑ l : n, (N⁻¹ : Matrix n n 𝕜) i l * comboE l‖ ≤
          ∑ l : n,
            (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l *
                ‖comboD l - comboE l‖ +
              comboBound l * ‖(M⁻¹ : Matrix n n 𝕜) i l -
                (N⁻¹ : Matrix n n 𝕜) i l‖) := by
      simpa using
        (norm_finset_sum_mul_sub_sum_mul_le
          (S := (Finset.univ : Finset n))
          (B := fun l => matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l)
          (D := comboBound)
          (a := fun l => (M⁻¹ : Matrix n n 𝕜) i l)
          (b := comboD)
          (c := fun l => (N⁻¹ : Matrix n n 𝕜) i l)
          (d := comboE)
          (fun l _hl => matrix_inv_entry_norm_le M hM hδpos hdetM i l)
          (fun l _hl => by
            simpa [comboE, comboBound] using christoffelDerivativeCombo_norm_le E hE j k l))
    refine hsum.trans ?_
    exact Finset.sum_le_sum fun l _hl => by
      have hcombo_bound :
          ‖comboE l‖ ≤ comboBound l := by
        simpa [comboE, comboBound] using christoffelDerivativeCombo_norm_le E hE j k l
      have hcombo_bound_nonneg : 0 ≤ comboBound l :=
        (norm_nonneg _).trans hcombo_bound
      have hcombo_diff :
          ‖comboD l - comboE l‖ ≤ comboDiffBound l := by
        simpa [comboD, comboE, comboDiffBound] using
          christoffelDerivativeCombo_norm_sub_le D E j k l
      have hlip :
          ‖(M⁻¹ : Matrix n n 𝕜) i l - (N⁻¹ : Matrix n n 𝕜) i l‖ ≤
            matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N i l :=
        matrix_inv_entry_norm_sub_le M N hM hN hδpos hdetM hdetN i l
      exact add_le_add
        (mul_le_mul_of_nonneg_left hcombo_diff
          (matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos C i l))
        (mul_le_mul_of_nonneg_left hlip hcombo_bound_nonneg)
  have hsplit :
      ((2 : 𝕜)⁻¹ * (∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l * comboD l)) -
        ((2 : 𝕜)⁻¹ * (∑ l : n, (N⁻¹ : Matrix n n 𝕜) i l * comboE l)) =
          (2 : 𝕜)⁻¹ *
            ((∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l * comboD l) -
              ∑ l : n, (N⁻¹ : Matrix n n 𝕜) i l * comboE l) := by
    ring
  calc
    ‖((2 : 𝕜)⁻¹ *
        ∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l *
          (D j k l + D k j l - D l j k)) -
      ((2 : 𝕜)⁻¹ *
        ∑ l : n, (N⁻¹ : Matrix n n 𝕜) i l *
          (E j k l + E k j l - E l j k))‖ =
        ‖((2 : 𝕜)⁻¹ * (∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l * comboD l)) -
          ((2 : 𝕜)⁻¹ * (∑ l : n, (N⁻¹ : Matrix n n 𝕜) i l * comboE l))‖ := by
      simp [comboD, comboE]
    _ = ‖(2 : 𝕜)⁻¹ *
          ((∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l * comboD l) -
            ∑ l : n, (N⁻¹ : Matrix n n 𝕜) i l * comboE l)‖ := by
      rw [hsplit]
    _ ≤ ‖(2 : 𝕜)⁻¹‖ *
        ‖(∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l * comboD l) -
          ∑ l : n, (N⁻¹ : Matrix n n 𝕜) i l * comboE l‖ :=
      norm_mul_le _ _
    _ ≤ ‖(2 : 𝕜)⁻¹‖ * innerBound :=
      mul_le_mul_of_nonneg_left hinner (norm_nonneg _)
    _ = ‖(2 : 𝕜)⁻¹‖ *
        ∑ l : n,
          (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l *
              (‖D j k l - E j k l‖ + ‖D k j l - E k j l‖ +
                ‖D l j k - E l j k‖) +
            (DB j k l + DB k j l + DB l j k) *
              matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N i l) := by
      simp [innerBound, comboDiffBound, comboBound]

/-- Christoffel-symbol type inverse-metric contractions are pointwise bounded by the quantitative
inverse-entry constants and derivative-array bounds. -/
theorem matrix_inv_christoffel_entry_norm_le {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ} {DB : n → n → n → ℝ}
    (M : Matrix n n 𝕜) (D : n → n → n → 𝕜)
    (hM : ∀ a b, ‖M a b‖ ≤ C a b)
    (hD : ∀ a b c, ‖D a b c‖ ≤ DB a b c)
    (hδpos : 0 < δ) (hdet : δ ≤ ‖M.det‖) (i j k : n) :
    ‖(2 : 𝕜)⁻¹ *
        ∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l *
          (D j k l + D k j l - D l j k)‖ ≤
      ‖(2 : 𝕜)⁻¹‖ *
        ∑ l : n,
          matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l *
            (DB j k l + DB k j l + DB l j k) := by
  classical
  let comboD : n → 𝕜 := fun l => D j k l + D k j l - D l j k
  let comboBound : n → ℝ := fun l => DB j k l + DB k j l + DB l j k
  let innerBound : ℝ := ∑ l : n,
    matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l * comboBound l
  have hterm : ∀ l ∈ (Finset.univ : Finset n),
      ‖(M⁻¹ : Matrix n n 𝕜) i l * comboD l‖ ≤
        matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l * comboBound l := by
    intro l _hl
    have hinv :
        ‖(M⁻¹ : Matrix n n 𝕜) i l‖ ≤ matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l :=
      matrix_inv_entry_norm_le M hM hδpos hdet i l
    have hcombo : ‖comboD l‖ ≤ comboBound l := by
      simpa [comboD, comboBound] using christoffelDerivativeCombo_norm_le D hD j k l
    calc
      ‖(M⁻¹ : Matrix n n 𝕜) i l * comboD l‖ ≤
          ‖(M⁻¹ : Matrix n n 𝕜) i l‖ * ‖comboD l‖ :=
        norm_mul_le _ _
      _ ≤ matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l * comboBound l :=
        mul_le_mul hinv hcombo (norm_nonneg _)
          (matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos C i l)
  have hinner :
      ‖∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l * comboD l‖ ≤ innerBound := by
    calc
      ‖∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l * comboD l‖ ≤
          ∑ l : n, ‖(M⁻¹ : Matrix n n 𝕜) i l * comboD l‖ :=
        norm_sum_le _ _
      _ ≤ ∑ l : n, matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l * comboBound l :=
        Finset.sum_le_sum hterm
      _ = innerBound := by
        rfl
  calc
    ‖(2 : 𝕜)⁻¹ *
        ∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l *
          (D j k l + D k j l - D l j k)‖ =
        ‖(2 : 𝕜)⁻¹ * ∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l * comboD l‖ := by
      simp [comboD]
    _ ≤ ‖(2 : 𝕜)⁻¹‖ * ‖∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l * comboD l‖ :=
      norm_mul_le _ _
    _ ≤ ‖(2 : 𝕜)⁻¹‖ * innerBound :=
      mul_le_mul_of_nonneg_left hinner (norm_nonneg _)
    _ = ‖(2 : 𝕜)⁻¹‖ *
        ∑ l : n,
          matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l *
            (DB j k l + DB k j l + DB l j k) := by
      simp [innerBound, comboBound]

/-- Quantitative pointwise bound for one inverse-Christoffel contraction entry. -/
def matrixInvChristoffelEntryBoundConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (C : n → n → ℝ) (DB : n → n → n → ℝ)
    (i j k : n) : ℝ :=
  ‖(2 : 𝕜)⁻¹‖ *
    ∑ l : n,
      matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l *
        (DB j k l + DB k j l + DB l j k)

/-- Quantitative Holder constant for one inverse-Christoffel contraction entry. -/
def matrixInvChristoffelEntryHolderConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (B H : n → n → ℝ) (DB DH : n → n → n → ℝ)
    (i j k : n) : ℝ :=
  ‖(2 : 𝕜)⁻¹‖ *
    ∑ l : n,
      (matrixInvEntryBoundConst (𝕜 := 𝕜) δ B i l *
          (DH j k l + DH k j l + DH l j k) +
        (DB j k l + DB k j l + DB l j k) *
          matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H i l)

/-- Difference-based sup constant for one inverse-Christoffel contraction entry. -/
def matrixInvChristoffelEntrySubBoundConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (B Bd : n → n → ℝ)
    (DB DDB : n → n → n → ℝ) (i j k : n) : ℝ :=
  ‖(2 : 𝕜)⁻¹‖ *
    ∑ l : n,
      (matrixInvEntryBoundConst (𝕜 := 𝕜) δ B i l *
          (DDB j k l + DDB k j l + DDB l j k) +
        matrixInvEntrySubBoundConst (𝕜 := 𝕜) δ B Bd i l *
          (DB j k l + DB k j l + DB l j k))

/-- Difference-based Holder constant for one inverse-Christoffel contraction entry. -/
def matrixInvChristoffelEntrySubHolderConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (B H Bd Hd : n → n → ℝ)
    (DB DH DDB DDH : n → n → n → ℝ) (i j k : n) : ℝ :=
  ‖(2 : 𝕜)⁻¹‖ *
    ∑ l : n,
      ((matrixInvEntryBoundConst (𝕜 := 𝕜) δ B i l *
            (DDH j k l + DDH k j l + DDH l j k) +
          (DDB j k l + DDB k j l + DDB l j k) *
            matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H i l) +
        (matrixInvEntrySubBoundConst (𝕜 := 𝕜) δ B Bd i l *
            (DH j k l + DH k j l + DH l j k) +
          (DB j k l + DB k j l + DB l j k) *
            matrixInvEntrySubHolderConst (𝕜 := 𝕜) δ B H Bd Hd i l))

/-- Difference-based sup constant for finite inverse-Christoffel arrays. -/
def matrixInvChristoffelEntrywiseSubBoundConst {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] (δ : ℝ) (B Bd : n → n → ℝ)
    (DB DDB : n → n → n → ℝ) : ℝ :=
  ∑ i : n, ∑ j : n, ∑ k : n,
    matrixInvChristoffelEntrySubBoundConst (𝕜 := 𝕜) δ B Bd DB DDB i j k

/-- Difference-based Holder constant for finite inverse-Christoffel arrays. -/
def matrixInvChristoffelEntrywiseSubHolderConst {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] (δ : ℝ) (B H Bd Hd : n → n → ℝ)
    (DB DH DDB DDH : n → n → n → ℝ) : ℝ :=
  ∑ i : n, ∑ j : n, ∑ k : n,
    matrixInvChristoffelEntrySubHolderConst (𝕜 := 𝕜) δ B H Bd Hd DB DH DDB DDH i j k

/-- Quantitative pointwise Lipschitz bound for one inverse-Christoffel contraction entry. -/
def matrixInvChristoffelEntryLipschitzBound {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (C : n → n → ℝ) (DB : n → n → n → ℝ)
    (M N : Matrix n n 𝕜) (D E : n → n → n → 𝕜) (i j k : n) : ℝ :=
  ‖(2 : 𝕜)⁻¹‖ *
    ∑ l : n,
      (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l *
          (‖D j k l - E j k l‖ + ‖D k j l - E k j l‖ +
            ‖D l j k - E l j k‖) +
        (DB j k l + DB k j l + DB l j k) *
          matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N i l)

/-- Matrix-norm Lipschitz constant for varying the metric in one inverse-Christoffel contraction
entry, with the derivative array bounded by `DB`. -/
def matrixInvChristoffelEntryMetricDiffConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (C : n → n → ℝ) (DB : n → n → n → ℝ)
    (i j k : n) : ℝ :=
  ‖(2 : 𝕜)⁻¹‖ *
    ∑ l : n,
      (DB j k l + DB k j l + DB l j k) *
        matrixInvEntryMatrixNormLipschitzConst (𝕜 := 𝕜) δ C i l

/-- Matrix-norm Lipschitz constant for varying the derivative array in one inverse-Christoffel
contraction entry, with a uniform entrywise derivative-array difference bound. -/
def matrixInvChristoffelEntryDerivDiffConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (C : n → n → ℝ) (i _j _k : n) : ℝ :=
  ‖(2 : 𝕜)⁻¹‖ *
    ∑ l : n, matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l * (3 : ℝ)

theorem matrixInvChristoffelEntryMetricDiffConst_nonneg {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} (hδpos : 0 < δ)
    {C : n → n → ℝ} {DB : n → n → n → ℝ} (hDB : ∀ a b c, 0 ≤ DB a b c)
    (i j k : n) :
    0 ≤ matrixInvChristoffelEntryMetricDiffConst (𝕜 := 𝕜) δ C DB i j k := by
  exact mul_nonneg (norm_nonneg _)
    (Finset.sum_nonneg fun l _hl =>
      mul_nonneg
        (add_nonneg (add_nonneg (hDB j k l) (hDB k j l)) (hDB l j k))
        (matrixInvEntryMatrixNormLipschitzConst_nonneg (𝕜 := 𝕜) hδpos C i l))

theorem matrixInvChristoffelEntryDerivDiffConst_nonneg {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} (hδpos : 0 < δ)
    (C : n → n → ℝ) (i j k : n) :
    0 ≤ matrixInvChristoffelEntryDerivDiffConst (𝕜 := 𝕜) δ C i j k := by
  exact mul_nonneg (norm_nonneg _)
    (Finset.sum_nonneg fun l _hl =>
      mul_nonneg (matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos C i l)
        (by norm_num))

theorem matrixInvChristoffelEntryBoundConst_nonneg {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} (hδpos : 0 < δ) (C : n → n → ℝ)
    {DB : n → n → n → ℝ} (hDB : ∀ a b c, 0 ≤ DB a b c) (i j k : n) :
    0 ≤ matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB i j k := by
  exact mul_nonneg (norm_nonneg _)
    (Finset.sum_nonneg fun l _hl =>
      mul_nonneg (matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos C i l)
        (add_nonneg (add_nonneg (hDB j k l) (hDB k j l)) (hDB l j k)))

theorem matrixInvChristoffelEntryHolderConst_nonneg {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {B H : n → n → ℝ}
    (hH : ∀ a b, 0 ≤ H a b) (hδpos : 0 < δ)
    {DB DH : n → n → n → ℝ} (hDB : ∀ a b c, 0 ≤ DB a b c)
    (hDH : ∀ a b c, 0 ≤ DH a b c) (i j k : n) :
    0 ≤ matrixInvChristoffelEntryHolderConst (𝕜 := 𝕜) δ B H DB DH i j k := by
  exact mul_nonneg (norm_nonneg _)
    (Finset.sum_nonneg fun l _hl =>
      add_nonneg
        (mul_nonneg (matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos B i l)
          (add_nonneg (add_nonneg (hDH j k l) (hDH k j l)) (hDH l j k)))
        (mul_nonneg
          (add_nonneg (add_nonneg (hDB j k l) (hDB k j l)) (hDB l j k))
          (matrixInvEntryHolderConst_nonneg (𝕜 := 𝕜) hH hδpos i l)))

theorem matrixInvChristoffelEntrySubBoundConst_nonneg {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {B Bd : n → n → ℝ}
    (hδpos : 0 < δ) (hBd : ∀ a b, 0 ≤ Bd a b)
    {DB DDB : n → n → n → ℝ} (hDB : ∀ a b c, 0 ≤ DB a b c)
    (hDDB : ∀ a b c, 0 ≤ DDB a b c) (i j k : n) :
    0 ≤ matrixInvChristoffelEntrySubBoundConst (𝕜 := 𝕜) δ B Bd DB DDB i j k := by
  exact mul_nonneg (norm_nonneg _)
    (Finset.sum_nonneg fun l _hl =>
      add_nonneg
        (mul_nonneg (matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos B i l)
          (add_nonneg (add_nonneg (hDDB j k l) (hDDB k j l)) (hDDB l j k)))
        (mul_nonneg (matrixInvEntrySubBoundConst_nonneg (𝕜 := 𝕜) hδpos hBd i l)
          (add_nonneg (add_nonneg (hDB j k l) (hDB k j l)) (hDB l j k))))

theorem matrixInvChristoffelEntrySubHolderConst_nonneg {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {B H Bd Hd : n → n → ℝ}
    (hδpos : 0 < δ) (hH : ∀ a b, 0 ≤ H a b) (hBd : ∀ a b, 0 ≤ Bd a b)
    (hHd : ∀ a b, 0 ≤ Hd a b)
    {DB DH DDB DDH : n → n → n → ℝ}
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hDH : ∀ a b c, 0 ≤ DH a b c)
    (hDDB : ∀ a b c, 0 ≤ DDB a b c) (hDDH : ∀ a b c, 0 ≤ DDH a b c)
    (i j k : n) :
    0 ≤ matrixInvChristoffelEntrySubHolderConst
      (𝕜 := 𝕜) δ B H Bd Hd DB DH DDB DDH i j k := by
  exact mul_nonneg (norm_nonneg _)
    (Finset.sum_nonneg fun l _hl =>
      add_nonneg
        (add_nonneg
          (mul_nonneg (matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos B i l)
            (add_nonneg (add_nonneg (hDDH j k l) (hDDH k j l)) (hDDH l j k)))
          (mul_nonneg
            (add_nonneg (add_nonneg (hDDB j k l) (hDDB k j l)) (hDDB l j k))
            (matrixInvEntryHolderConst_nonneg (𝕜 := 𝕜) hH hδpos i l)))
        (add_nonneg
          (mul_nonneg (matrixInvEntrySubBoundConst_nonneg (𝕜 := 𝕜) hδpos hBd i l)
            (add_nonneg (add_nonneg (hDH j k l) (hDH k j l)) (hDH l j k)))
          (mul_nonneg
            (add_nonneg (add_nonneg (hDB j k l) (hDB k j l)) (hDB l j k))
            (matrixInvEntrySubHolderConst_nonneg
              (𝕜 := 𝕜) hδpos hH hBd hHd i l))))

theorem matrixInvChristoffelEntrywiseSubBoundConst_nonneg {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {B Bd : n → n → ℝ}
    (hδpos : 0 < δ) (hBd : ∀ a b, 0 ≤ Bd a b)
    {DB DDB : n → n → n → ℝ} (hDB : ∀ a b c, 0 ≤ DB a b c)
    (hDDB : ∀ a b c, 0 ≤ DDB a b c) :
    0 ≤ matrixInvChristoffelEntrywiseSubBoundConst (𝕜 := 𝕜) δ B Bd DB DDB := by
  exact Finset.sum_nonneg fun i _hi =>
    Finset.sum_nonneg fun j _hj =>
      Finset.sum_nonneg fun k _hk =>
        matrixInvChristoffelEntrySubBoundConst_nonneg
          (𝕜 := 𝕜) hδpos hBd hDB hDDB i j k

theorem matrixInvChristoffelEntrywiseSubHolderConst_nonneg {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {B H Bd Hd : n → n → ℝ}
    (hδpos : 0 < δ) (hH : ∀ a b, 0 ≤ H a b) (hBd : ∀ a b, 0 ≤ Bd a b)
    (hHd : ∀ a b, 0 ≤ Hd a b)
    {DB DH DDB DDH : n → n → n → ℝ}
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hDH : ∀ a b c, 0 ≤ DH a b c)
    (hDDB : ∀ a b c, 0 ≤ DDB a b c) (hDDH : ∀ a b c, 0 ≤ DDH a b c) :
    0 ≤ matrixInvChristoffelEntrywiseSubHolderConst
      (𝕜 := 𝕜) δ B H Bd Hd DB DH DDB DDH := by
  exact Finset.sum_nonneg fun i _hi =>
    Finset.sum_nonneg fun j _hj =>
      Finset.sum_nonneg fun k _hk =>
        matrixInvChristoffelEntrySubHolderConst_nonneg
          (𝕜 := 𝕜) hδpos hH hBd hHd hDB hDH hDDB hDDH i j k

/-- One inverse-Christoffel entry is Lipschitz in the metric matrix norm, while retaining the
explicit derivative-array entry differences. -/
theorem matrix_inv_christoffel_entry_norm_sub_le_metric_const {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} (M N : Matrix n n 𝕜) (D E : n → n → n → 𝕜)
    (hM : ∀ a b, ‖M a b‖ ≤ C a b) (hN : ∀ a b, ‖N a b‖ ≤ C a b)
    (hE : ∀ a b c, ‖E a b c‖ ≤ DB a b c)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖)
    (i j k : n) :
    ‖((2 : 𝕜)⁻¹ *
        ∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l *
          (D j k l + D k j l - D l j k)) -
      ((2 : 𝕜)⁻¹ *
        ∑ l : n, (N⁻¹ : Matrix n n 𝕜) i l *
          (E j k l + E k j l - E l j k))‖ ≤
      ‖(2 : 𝕜)⁻¹‖ *
        ∑ l : n,
          matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l *
            (‖D j k l - E j k l‖ + ‖D k j l - E k j l‖ +
              ‖D l j k - E l j k‖) +
        matrixInvChristoffelEntryMetricDiffConst (𝕜 := 𝕜) δ C DB i j k * ‖M - N‖ := by
  classical
  let comboD : n → 𝕜 := fun l => D j k l + D k j l - D l j k
  let comboE : n → 𝕜 := fun l => E j k l + E k j l - E l j k
  let comboDiffBound : n → ℝ := fun l =>
    ‖D j k l - E j k l‖ + ‖D k j l - E k j l‖ + ‖D l j k - E l j k‖
  let comboBound : n → ℝ := fun l => DB j k l + DB k j l + DB l j k
  let derivPart : ℝ :=
    ∑ l : n, matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l * comboDiffBound l
  let metricPart : ℝ :=
    ∑ l : n,
      comboBound l * matrixInvEntryMatrixNormLipschitzConst (𝕜 := 𝕜) δ C i l
  let innerBound : ℝ :=
    derivPart + metricPart * ‖M - N‖
  have hinner :
      ‖(∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l * comboD l) -
          ∑ l : n, (N⁻¹ : Matrix n n 𝕜) i l * comboE l‖ ≤ innerBound := by
    have hsum :
        ‖(∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l * comboD l) -
            ∑ l : n, (N⁻¹ : Matrix n n 𝕜) i l * comboE l‖ ≤
          ∑ l : n,
            (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l *
                ‖comboD l - comboE l‖ +
              comboBound l * ‖(M⁻¹ : Matrix n n 𝕜) i l -
                (N⁻¹ : Matrix n n 𝕜) i l‖) := by
      simpa using
        (norm_finset_sum_mul_sub_sum_mul_le
          (S := (Finset.univ : Finset n))
          (B := fun l => matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l)
          (D := comboBound)
          (a := fun l => (M⁻¹ : Matrix n n 𝕜) i l)
          (b := comboD)
          (c := fun l => (N⁻¹ : Matrix n n 𝕜) i l)
          (d := comboE)
          (fun l _hl => matrix_inv_entry_norm_le M hM hδpos hdetM i l)
          (fun l _hl => by
            simpa [comboE, comboBound] using christoffelDerivativeCombo_norm_le E hE j k l))
    refine hsum.trans ?_
    calc
      (∑ l : n,
        (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l *
            ‖comboD l - comboE l‖ +
          comboBound l * ‖(M⁻¹ : Matrix n n 𝕜) i l -
            (N⁻¹ : Matrix n n 𝕜) i l‖)) ≤
          ∑ l : n,
            (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l * comboDiffBound l +
              comboBound l *
                (matrixInvEntryMatrixNormLipschitzConst (𝕜 := 𝕜) δ C i l * ‖M - N‖)) := by
        refine Finset.sum_le_sum fun l _hl => ?_
        have hcombo_bound :
            ‖comboE l‖ ≤ comboBound l := by
          simpa [comboE, comboBound] using christoffelDerivativeCombo_norm_le E hE j k l
        have hcombo_bound_nonneg : 0 ≤ comboBound l :=
          (norm_nonneg _).trans hcombo_bound
        have hcombo_diff :
            ‖comboD l - comboE l‖ ≤ comboDiffBound l := by
          simpa [comboD, comboE, comboDiffBound] using
            christoffelDerivativeCombo_norm_sub_le D E j k l
        have hinv_diff :
            ‖(M⁻¹ : Matrix n n 𝕜) i l - (N⁻¹ : Matrix n n 𝕜) i l‖ ≤
              matrixInvEntryMatrixNormLipschitzConst (𝕜 := 𝕜) δ C i l * ‖M - N‖ :=
          matrix_inv_entry_norm_sub_le_const_mul M N hM hN hδpos hdetM hdetN i l
        exact add_le_add
          (mul_le_mul_of_nonneg_left hcombo_diff
            (matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos C i l))
          (mul_le_mul_of_nonneg_left hinv_diff hcombo_bound_nonneg)
      _ = innerBound := by
        have hmetric :
            (∑ l : n,
              comboBound l *
                (matrixInvEntryMatrixNormLipschitzConst (𝕜 := 𝕜) δ C i l * ‖M - N‖)) =
              metricPart * ‖M - N‖ := by
          calc
            (∑ l : n,
              comboBound l *
                (matrixInvEntryMatrixNormLipschitzConst (𝕜 := 𝕜) δ C i l * ‖M - N‖)) =
                ∑ l : n,
                  (comboBound l *
                    matrixInvEntryMatrixNormLipschitzConst (𝕜 := 𝕜) δ C i l) * ‖M - N‖ := by
              refine Finset.sum_congr rfl fun l _hl => ?_
              ring
            _ = metricPart * ‖M - N‖ := by
              simp_rw [metricPart, Finset.sum_mul]
        rw [Finset.sum_add_distrib, hmetric]
  have hsplit :
      ((2 : 𝕜)⁻¹ * (∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l * comboD l)) -
        ((2 : 𝕜)⁻¹ * (∑ l : n, (N⁻¹ : Matrix n n 𝕜) i l * comboE l)) =
          (2 : 𝕜)⁻¹ *
            ((∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l * comboD l) -
              ∑ l : n, (N⁻¹ : Matrix n n 𝕜) i l * comboE l) := by
    ring
  have hmetric_const :
      matrixInvChristoffelEntryMetricDiffConst (𝕜 := 𝕜) δ C DB i j k =
        ‖(2 : 𝕜)⁻¹‖ * metricPart := by
    simp [matrixInvChristoffelEntryMetricDiffConst, metricPart, comboBound]
  calc
    ‖((2 : 𝕜)⁻¹ *
        ∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l *
          (D j k l + D k j l - D l j k)) -
      ((2 : 𝕜)⁻¹ *
        ∑ l : n, (N⁻¹ : Matrix n n 𝕜) i l *
          (E j k l + E k j l - E l j k))‖ =
        ‖((2 : 𝕜)⁻¹ * (∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l * comboD l)) -
          ((2 : 𝕜)⁻¹ * (∑ l : n, (N⁻¹ : Matrix n n 𝕜) i l * comboE l))‖ := by
      simp [comboD, comboE]
    _ = ‖(2 : 𝕜)⁻¹ *
          ((∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l * comboD l) -
            ∑ l : n, (N⁻¹ : Matrix n n 𝕜) i l * comboE l)‖ := by
      rw [hsplit]
    _ ≤ ‖(2 : 𝕜)⁻¹‖ *
        ‖(∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l * comboD l) -
          ∑ l : n, (N⁻¹ : Matrix n n 𝕜) i l * comboE l‖ :=
      norm_mul_le _ _
    _ ≤ ‖(2 : 𝕜)⁻¹‖ * innerBound :=
      mul_le_mul_of_nonneg_left hinner (norm_nonneg _)
    _ = ‖(2 : 𝕜)⁻¹‖ * derivPart +
        matrixInvChristoffelEntryMetricDiffConst (𝕜 := 𝕜) δ C DB i j k * ‖M - N‖ := by
      rw [hmetric_const]
      simp [innerBound]
      ring
    _ = ‖(2 : 𝕜)⁻¹‖ *
        ∑ l : n,
          matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l *
            (‖D j k l - E j k l‖ + ‖D k j l - E k j l‖ +
              ‖D l j k - E l j k‖) +
        matrixInvChristoffelEntryMetricDiffConst (𝕜 := 𝕜) δ C DB i j k * ‖M - N‖ := by
      simp [derivPart, comboDiffBound]

/-- One inverse-Christoffel entry is Lipschitz in the metric matrix norm and a uniform entrywise
derivative-array difference bound. -/
theorem matrix_inv_christoffel_entry_norm_sub_le_const {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} {ηD : ℝ} (M N : Matrix n n 𝕜) (D E : n → n → n → 𝕜)
    (hM : ∀ a b, ‖M a b‖ ≤ C a b) (hN : ∀ a b, ‖N a b‖ ≤ C a b)
    (hE : ∀ a b c, ‖E a b c‖ ≤ DB a b c)
    (hDdiff : ∀ a b c, ‖D a b c - E a b c‖ ≤ ηD)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖)
    (i j k : n) :
    ‖((2 : 𝕜)⁻¹ *
        ∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l *
          (D j k l + D k j l - D l j k)) -
      ((2 : 𝕜)⁻¹ *
        ∑ l : n, (N⁻¹ : Matrix n n 𝕜) i l *
          (E j k l + E k j l - E l j k))‖ ≤
      matrixInvChristoffelEntryDerivDiffConst (𝕜 := 𝕜) δ C i j k * ηD +
        matrixInvChristoffelEntryMetricDiffConst (𝕜 := 𝕜) δ C DB i j k * ‖M - N‖ := by
  classical
  have hbase :=
    matrix_inv_christoffel_entry_norm_sub_le_metric_const
      M N D E hM hN hE hδpos hdetM hdetN i j k
  refine hbase.trans ?_
  have hcombo : ∀ l : n,
      ‖D j k l - E j k l‖ + ‖D k j l - E k j l‖ + ‖D l j k - E l j k‖ ≤
        (3 : ℝ) * ηD := by
    intro l
    calc
      ‖D j k l - E j k l‖ + ‖D k j l - E k j l‖ + ‖D l j k - E l j k‖ ≤
          ηD + ηD + ηD :=
        add_le_add (add_le_add (hDdiff j k l) (hDdiff k j l)) (hDdiff l j k)
      _ = (3 : ℝ) * ηD := by ring
  have hderiv :
      ‖(2 : 𝕜)⁻¹‖ *
        ∑ l : n,
          matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l *
            (‖D j k l - E j k l‖ + ‖D k j l - E k j l‖ +
              ‖D l j k - E l j k‖) ≤
        matrixInvChristoffelEntryDerivDiffConst (𝕜 := 𝕜) δ C i j k * ηD := by
    calc
      ‖(2 : 𝕜)⁻¹‖ *
        ∑ l : n,
          matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l *
            (‖D j k l - E j k l‖ + ‖D k j l - E k j l‖ +
              ‖D l j k - E l j k‖) ≤
          ‖(2 : 𝕜)⁻¹‖ *
            ∑ l : n, matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l * ((3 : ℝ) * ηD) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact Finset.sum_le_sum fun l _hl =>
          mul_le_mul_of_nonneg_left (hcombo l)
            (matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos C i l)
      _ = matrixInvChristoffelEntryDerivDiffConst (𝕜 := 𝕜) δ C i j k * ηD := by
        calc
          ‖(2 : 𝕜)⁻¹‖ *
              ∑ l : n, matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l * ((3 : ℝ) * ηD) =
              ‖(2 : 𝕜)⁻¹‖ *
                ∑ l : n, (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l * (3 : ℝ)) * ηD := by
            congr 1
            refine Finset.sum_congr rfl fun l _hl => ?_
            ring
          _ = ‖(2 : 𝕜)⁻¹‖ *
              ((∑ l : n, matrixInvEntryBoundConst (𝕜 := 𝕜) δ C i l * (3 : ℝ)) * ηD) := by
            rw [Finset.sum_mul]
          _ = matrixInvChristoffelEntryDerivDiffConst (𝕜 := 𝕜) δ C i j k * ηD := by
            simp [matrixInvChristoffelEntryDerivDiffConst]
            ring
  exact add_le_add hderiv (le_refl _)

/-- Uniform scalar bound for all entries of the inverse-Christoffel array, in terms of a uniform
derivative-array difference bound and a metric matrix-norm difference bound. -/
def matrixInvChristoffelArrayDiffBoundConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (C : n → n → ℝ) (DB : n → n → n → ℝ)
    (ηD ρ : ℝ) : ℝ :=
  ∑ a : n, ∑ b : n, ∑ c : n,
    (matrixInvChristoffelEntryDerivDiffConst (𝕜 := 𝕜) δ C a b c * ηD +
      matrixInvChristoffelEntryMetricDiffConst (𝕜 := 𝕜) δ C DB a b c * ρ)

theorem matrixInvChristoffelArrayDiffBoundConst_nonneg {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} (hδpos : 0 < δ) {C : n → n → ℝ}
    {DB : n → n → n → ℝ} (hDB : ∀ a b c, 0 ≤ DB a b c)
    {ηD ρ : ℝ} (hηD : 0 ≤ ηD) (hρ : 0 ≤ ρ) :
    0 ≤ matrixInvChristoffelArrayDiffBoundConst (𝕜 := 𝕜) δ C DB ηD ρ := by
  exact Finset.sum_nonneg fun a _ha =>
    Finset.sum_nonneg fun b _hb =>
      Finset.sum_nonneg fun c _hc =>
        add_nonneg
          (mul_nonneg
            (matrixInvChristoffelEntryDerivDiffConst_nonneg (𝕜 := 𝕜) hδpos C a b c)
            hηD)
          (mul_nonneg
            (matrixInvChristoffelEntryMetricDiffConst_nonneg (𝕜 := 𝕜) hδpos hDB a b c)
            hρ)

/-- The uniform inverse-Christoffel array-difference constant is linear in a shared comparison
radius when both primitive difference radii are multiples of that radius. -/
theorem matrixInvChristoffelArrayDiffBoundConst_mul_radius {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] (δ : ℝ) (C : n → n → ℝ)
    (DB : n → n → n → ℝ) (KD KM R : ℝ) :
    matrixInvChristoffelArrayDiffBoundConst (𝕜 := 𝕜) δ C DB (KD * R) (KM * R) =
      matrixInvChristoffelArrayDiffBoundConst (𝕜 := 𝕜) δ C DB KD KM * R := by
  classical
  simp_rw [matrixInvChristoffelArrayDiffBoundConst, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ha => ?_
  refine Finset.sum_congr rfl fun b _hb => ?_
  refine Finset.sum_congr rfl fun c _hc => ?_
  ring

/-- The uniform inverse-Christoffel array-difference bound is monotone in the metric
matrix-difference radius. -/
theorem matrixInvChristoffelArrayDiffBoundConst_mono_right {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} (hδpos : 0 < δ) {C : n → n → ℝ}
    {DB : n → n → n → ℝ} (hDB : ∀ a b c, 0 ≤ DB a b c)
    {ηD ρ ρ' : ℝ} (hρ : ρ ≤ ρ') :
    matrixInvChristoffelArrayDiffBoundConst (𝕜 := 𝕜) δ C DB ηD ρ ≤
      matrixInvChristoffelArrayDiffBoundConst (𝕜 := 𝕜) δ C DB ηD ρ' := by
  classical
  refine Finset.sum_le_sum fun a _ha => ?_
  refine Finset.sum_le_sum fun b _hb => ?_
  refine Finset.sum_le_sum fun c _hc => ?_
  exact add_le_add_right
    (mul_le_mul_of_nonneg_left hρ
      (matrixInvChristoffelEntryMetricDiffConst_nonneg (𝕜 := 𝕜) hδpos hDB a b c))
    _

/-- The uniform inverse-Christoffel array-difference bound is monotone in both primitive
difference radii. -/
theorem matrixInvChristoffelArrayDiffBoundConst_mono {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} (hδpos : 0 < δ) {C : n → n → ℝ}
    {DB : n → n → n → ℝ} (hDB : ∀ a b c, 0 ≤ DB a b c)
    {ηD ηD' ρ ρ' : ℝ} (hηD : ηD ≤ ηD') (hρ : ρ ≤ ρ') :
    matrixInvChristoffelArrayDiffBoundConst (𝕜 := 𝕜) δ C DB ηD ρ ≤
      matrixInvChristoffelArrayDiffBoundConst (𝕜 := 𝕜) δ C DB ηD' ρ' := by
  classical
  refine Finset.sum_le_sum fun a _ha => ?_
  refine Finset.sum_le_sum fun b _hb => ?_
  refine Finset.sum_le_sum fun c _hc => ?_
  exact add_le_add
    (mul_le_mul_of_nonneg_left hηD
      (matrixInvChristoffelEntryDerivDiffConst_nonneg (𝕜 := 𝕜) hδpos C a b c))
    (mul_le_mul_of_nonneg_left hρ
      (matrixInvChristoffelEntryMetricDiffConst_nonneg (𝕜 := 𝕜) hδpos hDB a b c))

/-- Every inverse-Christoffel entry is controlled by the summed uniform array-difference bound. -/
theorem matrix_inv_christoffel_entry_norm_sub_le_array_const {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} {ηD : ℝ} (M N : Matrix n n 𝕜) (D E : n → n → n → 𝕜)
    (hM : ∀ a b, ‖M a b‖ ≤ C a b) (hN : ∀ a b, ‖N a b‖ ≤ C a b)
    (hE : ∀ a b c, ‖E a b c‖ ≤ DB a b c)
    (hηD : 0 ≤ ηD) (hDdiff : ∀ a b c, ‖D a b c - E a b c‖ ≤ ηD)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖)
    (i j k : n) :
    ‖((2 : 𝕜)⁻¹ *
        ∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l *
          (D j k l + D k j l - D l j k)) -
      ((2 : 𝕜)⁻¹ *
        ∑ l : n, (N⁻¹ : Matrix n n 𝕜) i l *
          (E j k l + E k j l - E l j k))‖ ≤
      matrixInvChristoffelArrayDiffBoundConst (𝕜 := 𝕜) δ C DB ηD ‖M - N‖ := by
  classical
  let entryBound : n → n → n → ℝ := fun a b c =>
    matrixInvChristoffelEntryDerivDiffConst (𝕜 := 𝕜) δ C a b c * ηD +
      matrixInvChristoffelEntryMetricDiffConst (𝕜 := 𝕜) δ C DB a b c * ‖M - N‖
  have hDB_nonneg : ∀ a b c, 0 ≤ DB a b c := by
    intro a b c
    exact (norm_nonneg _).trans (hE a b c)
  have hentry :
      ‖((2 : 𝕜)⁻¹ *
          ∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l *
            (D j k l + D k j l - D l j k)) -
        ((2 : 𝕜)⁻¹ *
          ∑ l : n, (N⁻¹ : Matrix n n 𝕜) i l *
            (E j k l + E k j l - E l j k))‖ ≤ entryBound i j k := by
    simpa [entryBound] using
      matrix_inv_christoffel_entry_norm_sub_le_const
        M N D E hM hN hE hDdiff hδpos hdetM hdetN i j k
  have hentry_nonneg : ∀ a b c, 0 ≤ entryBound a b c := by
    intro a b c
    exact add_nonneg
      (mul_nonneg
        (matrixInvChristoffelEntryDerivDiffConst_nonneg (𝕜 := 𝕜) hδpos C a b c)
        hηD)
      (mul_nonneg
        (matrixInvChristoffelEntryMetricDiffConst_nonneg (𝕜 := 𝕜) hδpos hDB_nonneg a b c)
        (norm_nonneg _))
  have hle_sum :
      entryBound i j k ≤ ∑ a : n, ∑ b : n, ∑ c : n, entryBound a b c := by
    calc
      entryBound i j k ≤ ∑ c : n, entryBound i j c :=
        Finset.single_le_sum (fun c _hc => hentry_nonneg i j c) (Finset.mem_univ k)
      _ ≤ ∑ b : n, ∑ c : n, entryBound i b c :=
        Finset.single_le_sum
          (fun b _hb => Finset.sum_nonneg fun c _hc => hentry_nonneg i b c)
          (Finset.mem_univ j)
      _ ≤ ∑ a : n, ∑ b : n, ∑ c : n, entryBound a b c :=
        Finset.single_le_sum
          (fun a _ha => Finset.sum_nonneg fun b _hb =>
            Finset.sum_nonneg fun c _hc => hentry_nonneg a b c)
          (Finset.mem_univ i)
  exact hentry.trans (hle_sum.trans (by rfl))

/-- Function-level bounded-difference estimate for the finite inverse-Christoffel array. -/
theorem matrix_inv_christoffel_bounded_sub_le_const {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} {ηM ηD : ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    (hM : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b, ‖M z a b‖ ≤ C a b)
    (hN : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b, ‖N z a b‖ ≤ C a b)
    (hE : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c, ‖E z a b c‖ ≤ DB a b c)
    (hηD : 0 ≤ ηD)
    (hMdiff : ∀ ⦃z : ℝ × X⦄, z ∈ s → ‖M z - N z‖ ≤ ηM)
    (hDdiff : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c,
      ‖D z a b c - E z a b c‖ ≤ ηD)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicBoundedWith
      (matrixInvChristoffelArrayDiffBoundConst (𝕜 := 𝕜) δ C DB ηD ηM)
      (fun z : ℝ × X =>
        (fun i j k =>
          (2 : 𝕜)⁻¹ *
            ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) i l *
              (D z j k l + D z k j l - D z l j k)) -
        (fun i j k =>
          (2 : 𝕜)⁻¹ *
            ∑ l : n, ((N z)⁻¹ : Matrix n n 𝕜) i l *
              (E z j k l + E z k j l - E z l j k))) s := by
  classical
  intro z hz
  let Γ : n → n → n → 𝕜 := fun i j k =>
    (2 : 𝕜)⁻¹ *
      ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) i l *
        (D z j k l + D z k j l - D z l j k)
  let Λ : n → n → n → 𝕜 := fun i j k =>
    (2 : 𝕜)⁻¹ *
      ∑ l : n, ((N z)⁻¹ : Matrix n n 𝕜) i l *
        (E z j k l + E z k j l - E z l j k)
  have hDB_nonneg : ∀ a b c, 0 ≤ DB a b c := by
    intro a b c
    exact (norm_nonneg _).trans (hE hz a b c)
  have hηM : 0 ≤ ηM := (norm_nonneg _).trans (hMdiff hz)
  have htarget_nonneg :
      0 ≤ matrixInvChristoffelArrayDiffBoundConst (𝕜 := 𝕜) δ C DB ηD ηM :=
    matrixInvChristoffelArrayDiffBoundConst_nonneg
      (𝕜 := 𝕜) hδpos hDB_nonneg hηD hηM
  have hentry : ∀ i j k,
      ‖Γ i j k - Λ i j k‖ ≤
        matrixInvChristoffelArrayDiffBoundConst (𝕜 := 𝕜) δ C DB ηD ηM := by
    intro i j k
    have hbase :=
      matrix_inv_christoffel_entry_norm_sub_le_array_const
        (δ := δ) (C := C) (DB := DB) (ηD := ηD)
        (M z) (N z) (D z) (E z) (hM hz) (hN hz) (hE hz)
        hηD (hDdiff hz) hδpos (hdetM hz) (hdetN hz) i j k
    exact hbase.trans
      (matrixInvChristoffelArrayDiffBoundConst_mono_right
        (𝕜 := 𝕜) hδpos hDB_nonneg (hMdiff hz))
  change ‖Γ - Λ‖ ≤ matrixInvChristoffelArrayDiffBoundConst (𝕜 := 𝕜) δ C DB ηD ηM
  exact (pi_norm_le_iff_of_nonneg htarget_nonneg).2 fun i =>
    (pi_norm_le_iff_of_nonneg htarget_nonneg).2 fun j =>
      (pi_norm_le_iff_of_nonneg htarget_nonneg).2 fun k => hentry i j k

/-- Compact-domain version of `matrix_inv_christoffel_bounded_sub_le_const`: pointwise
nonvanishing of both metric determinants supplies one common determinant lower bound. -/
theorem matrix_inv_christoffel_bounded_sub_le_const_of_isCompact_det_ne_zero {n 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)}
    {C : n → n → ℝ} {DB : n → n → n → ℝ} {ηM ηD : ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hMctrl : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) K)
    (hNctrl : ∀ i j, ParabolicC0AlphaOn α (fun z => N z i j) K)
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (N z).det ≠ 0)
    (hM : ∀ ⦃z : ℝ × X⦄, z ∈ K → ∀ a b, ‖M z a b‖ ≤ C a b)
    (hN : ∀ ⦃z : ℝ × X⦄, z ∈ K → ∀ a b, ‖N z a b‖ ≤ C a b)
    (hE : ∀ ⦃z : ℝ × X⦄, z ∈ K → ∀ a b c, ‖E z a b c‖ ≤ DB a b c)
    (hηD : 0 ≤ ηD)
    (hMdiff : ∀ ⦃z : ℝ × X⦄, z ∈ K → ‖M z - N z‖ ≤ ηM)
    (hDdiff : ∀ ⦃z : ℝ × X⦄, z ∈ K → ∀ a b c,
      ‖D z a b c - E z a b c‖ ≤ ηD) :
    ∃ δ > 0,
      ParabolicBoundedWith
        (matrixInvChristoffelArrayDiffBoundConst (𝕜 := 𝕜) δ C DB ηD ηM)
        (fun z : ℝ × X =>
          (fun i j k =>
            (2 : 𝕜)⁻¹ *
              ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) i l *
                (D z j k l + D z k j l - D z l j k)) -
          (fun i j k =>
            (2 : 𝕜)⁻¹ *
              ∑ l : n, ((N z)⁻¹ : Matrix n n 𝕜) i l *
                (E z j k l + E z k j l - E z l j k))) K := by
  rcases matrix_det_pair_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) (N := N) hK hα hMctrl hNctrl hdetM_ne hdetN_ne with
    ⟨δ, hδpos, hdetM, hdetN⟩
  refine ⟨δ, hδpos, ?_⟩
  exact matrix_inv_christoffel_bounded_sub_le_const
    (s := K) (δ := δ) (C := C) (DB := DB) (ηM := ηM) (ηD := ηD)
    hM hN hE hηD hMdiff hDdiff hδpos hdetM hdetN

theorem matrix_inv_christoffel_entry_norm_le_bound {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} (M : Matrix n n 𝕜) (D : n → n → n → 𝕜)
    (hM : ∀ a b, ‖M a b‖ ≤ C a b)
    (hD : ∀ a b c, ‖D a b c‖ ≤ DB a b c)
    (hδpos : 0 < δ) (hdet : δ ≤ ‖M.det‖) (i j k : n) :
    ‖(2 : 𝕜)⁻¹ *
        ∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l *
          (D j k l + D k j l - D l j k)‖ ≤
      matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB i j k := by
  simpa [matrixInvChristoffelEntryBoundConst] using
    matrix_inv_christoffel_entry_norm_le M D hM hD hδpos hdet i j k

theorem matrix_inv_christoffel_entry_norm_sub_le_bound {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} (M N : Matrix n n 𝕜) (D E : n → n → n → 𝕜)
    (hM : ∀ a b, ‖M a b‖ ≤ C a b) (hN : ∀ a b, ‖N a b‖ ≤ C a b)
    (hE : ∀ a b c, ‖E a b c‖ ≤ DB a b c)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖)
    (i j k : n) :
    ‖((2 : 𝕜)⁻¹ *
        ∑ l : n, (M⁻¹ : Matrix n n 𝕜) i l *
          (D j k l + D k j l - D l j k)) -
      ((2 : 𝕜)⁻¹ *
        ∑ l : n, (N⁻¹ : Matrix n n 𝕜) i l *
          (E j k l + E k j l - E l j k))‖ ≤
      matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E i j k := by
  simpa [matrixInvChristoffelEntryLipschitzBound] using
    matrix_inv_christoffel_entry_norm_sub_le M N D E hM hN hE hδpos hdetM hdetN i j k

/-- One inverse-Christoffel entry has an explicit bounded parabolic `C^{0,α}` estimate from
explicit metric-entry and derivative-array estimates. -/
theorem matrix_inv_christoffel_entry_with {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {B H : n → n → ℝ} {DB DH : n → n → n → ℝ} {δ : ℝ}
    {M : ℝ × X → Matrix n n 𝕜} {D : ℝ × X → n → n → n → 𝕜}
    (hH : ∀ a b, 0 ≤ H a b)
    (hM : ∀ a b, ParabolicC0AlphaWith (B a b) (H a b) α (fun z => M z a b) s)
    (hD : ∀ a b c, ParabolicC0AlphaWith (DB a b c) (DH a b c) α
      (fun z => D z a b c) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (i j k : n) :
    ParabolicC0AlphaWith
      (matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ B DB i j k)
      (matrixInvChristoffelEntryHolderConst (𝕜 := 𝕜) δ B H DB DH i j k)
      α
      (fun z =>
        (2 : 𝕜)⁻¹ *
          ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) i l *
            (D z j k l + D z k j l - D z l j k)) s := by
  classical
  let term : n → ℝ × X → 𝕜 := fun l z =>
    ((M z)⁻¹ : Matrix n n 𝕜) i l *
      (D z j k l + D z k j l - D z l j k)
  have hterm : ∀ l ∈ (Finset.univ : Finset n),
      ParabolicC0AlphaWith
        (matrixInvEntryBoundConst (𝕜 := 𝕜) δ B i l *
          (DB j k l + DB k j l + DB l j k))
        (matrixInvEntryBoundConst (𝕜 := 𝕜) δ B i l *
            (DH j k l + DH k j l + DH l j k) +
          (DB j k l + DB k j l + DB l j k) *
            matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H i l)
        α (term l) s := by
    intro l _hl
    have hinv :
        ParabolicC0AlphaWith
          (matrixInvEntryBoundConst (𝕜 := 𝕜) δ B i l)
          (matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H i l)
          α (fun z => ((M z)⁻¹ : Matrix n n 𝕜) i l) s :=
      matrix_inv_entry_with (M := M) hH hM hδpos hdet i l
    have hcombo :
        ParabolicC0AlphaWith
          (DB j k l + DB k j l + DB l j k)
          (DH j k l + DH k j l + DH l j k)
          α (fun z => D z j k l + D z k j l - D z l j k) s := by
      have hsum := (hD j k l).add (hD k j l)
      simpa [add_assoc] using hsum.sub (hD l j k)
    simpa [term] using
      hinv.mul hcombo (matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos B i l)
  have hsum :
      ParabolicC0AlphaWith
        (∑ l : n,
          matrixInvEntryBoundConst (𝕜 := 𝕜) δ B i l *
            (DB j k l + DB k j l + DB l j k))
        (∑ l : n,
          (matrixInvEntryBoundConst (𝕜 := 𝕜) δ B i l *
              (DH j k l + DH k j l + DH l j k) +
            (DB j k l + DB k j l + DB l j k) *
              matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H i l))
        α (fun z => ∑ l : n, term l z) s := by
    simpa using
      (ParabolicC0AlphaWith.sum (X := X) (α := α) (s := s)
        (S := (Finset.univ : Finset n))
        (B := fun l => matrixInvEntryBoundConst (𝕜 := 𝕜) δ B i l *
          (DB j k l + DB k j l + DB l j k))
        (H := fun l =>
          matrixInvEntryBoundConst (𝕜 := 𝕜) δ B i l *
              (DH j k l + DH k j l + DH l j k) +
            (DB j k l + DB k j l + DB l j k) *
              matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H i l)
        (u := term) hterm)
  have hhalf :
      ParabolicC0AlphaWith ‖(2 : 𝕜)⁻¹‖ 0 α (fun _ : ℝ × X => (2 : 𝕜)⁻¹) s :=
    ParabolicC0AlphaWith.const (s := s) (α := α) (B := ‖(2 : 𝕜)⁻¹‖) (H := 0)
      ((2 : 𝕜)⁻¹) le_rfl le_rfl
  simpa [term, matrixInvChristoffelEntryBoundConst, matrixInvChristoffelEntryHolderConst] using
    hhalf.mul hsum (norm_nonneg _)

/-- One inverse-Christoffel entry has difference-based parabolic `C^{0,α}` control from
entrywise metric and derivative-array difference controls. -/
theorem matrix_inv_christoffel_entry_sub_with_entrywise {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {B H Bd Hd : n → n → ℝ}
    {DB DH DDB DDH : n → n → n → ℝ} {δ : ℝ}
    {M N : ℝ × X → Matrix n n 𝕜} {D E : ℝ × X → n → n → n → 𝕜}
    (hH : ∀ a b, 0 ≤ H a b)
    (hBd : ∀ a b, 0 ≤ Bd a b) (hHd : ∀ a b, 0 ≤ Hd a b)
    (hM : ∀ a b, ParabolicC0AlphaWith (B a b) (H a b) α (fun z => M z a b) s)
    (hN : ∀ a b, ParabolicC0AlphaWith (B a b) (H a b) α (fun z => N z a b) s)
    (hMdiff : ∀ a b,
      ParabolicC0AlphaWith (Bd a b) (Hd a b) α (fun z => M z a b - N z a b) s)
    (hE : ∀ a b c, ParabolicC0AlphaWith (DB a b c) (DH a b c) α
      (fun z => E z a b c) s)
    (hDdiff : ∀ a b c,
      ParabolicC0AlphaWith (DDB a b c) (DDH a b c) α
        (fun z => D z a b c - E z a b c) s)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖)
    (i j k : n) :
    ParabolicC0AlphaWith
      (matrixInvChristoffelEntrySubBoundConst (𝕜 := 𝕜) δ B Bd DB DDB i j k)
      (matrixInvChristoffelEntrySubHolderConst
        (𝕜 := 𝕜) δ B H Bd Hd DB DH DDB DDH i j k)
      α
      (fun z =>
        ((2 : 𝕜)⁻¹ *
          ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) i l *
            (D z j k l + D z k j l - D z l j k)) -
        ((2 : 𝕜)⁻¹ *
          ∑ l : n, ((N z)⁻¹ : Matrix n n 𝕜) i l *
            (E z j k l + E z k j l - E z l j k))) s := by
  classical
  let invM : n → ℝ × X → 𝕜 := fun l z => ((M z)⁻¹ : Matrix n n 𝕜) i l
  let invN : n → ℝ × X → 𝕜 := fun l z => ((N z)⁻¹ : Matrix n n 𝕜) i l
  let comboD : n → ℝ × X → 𝕜 :=
    fun l z => D z j k l + D z k j l - D z l j k
  let comboE : n → ℝ × X → 𝕜 :=
    fun l z => E z j k l + E z k j l - E z l j k
  have hcomboE : ∀ l ∈ (Finset.univ : Finset n),
      ParabolicC0AlphaWith
        (DB j k l + DB k j l + DB l j k)
        (DH j k l + DH k j l + DH l j k)
        α (comboE l) s := by
    intro l _hl
    have hsum := (hE j k l).add (hE k j l)
    simpa [comboE, add_assoc] using hsum.sub (hE l j k)
  have hcomboDiff : ∀ l ∈ (Finset.univ : Finset n),
      ParabolicC0AlphaWith
        (DDB j k l + DDB k j l + DDB l j k)
        (DDH j k l + DDH k j l + DDH l j k)
        α (fun z => comboD l z - comboE l z) s := by
    intro l _hl
    have hraw := ((hDdiff j k l).add (hDdiff k j l)).sub (hDdiff l j k)
    convert hraw using 1
    ext z
    simp [comboD, comboE]
    abel
  have hinvM : ∀ l ∈ (Finset.univ : Finset n),
      ParabolicC0AlphaWith
        (matrixInvEntryBoundConst (𝕜 := 𝕜) δ B i l)
        (matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H i l)
        α (invM l) s := by
    intro l _hl
    simpa [invM] using matrix_inv_entry_with (M := M) hH hM hδpos hdetM i l
  have hinvDiff : ∀ l ∈ (Finset.univ : Finset n),
      ParabolicC0AlphaWith
        (matrixInvEntrySubBoundConst (𝕜 := 𝕜) δ B Bd i l)
        (matrixInvEntrySubHolderConst (𝕜 := 𝕜) δ B H Bd Hd i l)
        α (fun z => invM l z - invN l z) s := by
    intro l _hl
    simpa [invM, invN] using
      matrix_inv_entry_sub_with (M := M) (N := N)
        hH hBd hHd hM hN hMdiff hδpos hdetM hdetN i l
  have hsum :
      ParabolicC0AlphaWith
        (∑ l : n,
          (matrixInvEntryBoundConst (𝕜 := 𝕜) δ B i l *
              (DDB j k l + DDB k j l + DDB l j k) +
            matrixInvEntrySubBoundConst (𝕜 := 𝕜) δ B Bd i l *
              (DB j k l + DB k j l + DB l j k)))
        (∑ l : n,
          ((matrixInvEntryBoundConst (𝕜 := 𝕜) δ B i l *
                (DDH j k l + DDH k j l + DDH l j k) +
              (DDB j k l + DDB k j l + DDB l j k) *
                matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H i l) +
            (matrixInvEntrySubBoundConst (𝕜 := 𝕜) δ B Bd i l *
                (DH j k l + DH k j l + DH l j k) +
              (DB j k l + DB k j l + DB l j k) *
                matrixInvEntrySubHolderConst (𝕜 := 𝕜) δ B H Bd Hd i l)))
        α
        (fun z =>
          (∑ l : n, invM l z * comboD l z) -
            ∑ l : n, invN l z * comboE l z) s := by
    simpa [invM, invN, comboD, comboE] using
      (ParabolicC0AlphaWith.finset_sum_mul_sub_sum_mul (X := X) (α := α) (s := s)
        (S := (Finset.univ : Finset n))
        (Bu := fun l => matrixInvEntryBoundConst (𝕜 := 𝕜) δ B i l)
        (Hu := fun l => matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H i l)
        (Bv := fun l => DB j k l + DB k j l + DB l j k)
        (Hv := fun l => DH j k l + DH k j l + DH l j k)
        (Bdu := fun l => matrixInvEntrySubBoundConst (𝕜 := 𝕜) δ B Bd i l)
        (Hdu := fun l => matrixInvEntrySubHolderConst (𝕜 := 𝕜) δ B H Bd Hd i l)
        (Bdv := fun l => DDB j k l + DDB k j l + DDB l j k)
        (Hdv := fun l => DDH j k l + DDH k j l + DDH l j k)
        (u := invM) (u' := invN) (v := comboD) (v' := comboE)
        hinvM hcomboE hinvDiff hcomboDiff
        (fun l _hl => matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos B i l)
        (fun l _hl => matrixInvEntrySubBoundConst_nonneg (𝕜 := 𝕜) hδpos hBd i l))
  have hhalf := hsum.smul ((2 : 𝕜)⁻¹)
  convert hhalf using 1 <;>
    first
    | rfl
    | (funext z
       simp [invM, invN, comboD, comboE, smul_eq_mul]
       ring)

/-- Finite inverse-Christoffel arrays have difference-based parabolic `C^{0,α}` control from
entrywise metric and derivative-array difference controls. -/
theorem matrix_inv_christoffel_sub_with_entrywise {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {B H Bd Hd : n → n → ℝ}
    {DB DH DDB DDH : n → n → n → ℝ} {δ : ℝ}
    {M N : ℝ × X → Matrix n n 𝕜} {D E : ℝ × X → n → n → n → 𝕜}
    (hH : ∀ a b, 0 ≤ H a b)
    (hBd : ∀ a b, 0 ≤ Bd a b) (hHd : ∀ a b, 0 ≤ Hd a b)
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hDH : ∀ a b c, 0 ≤ DH a b c)
    (hDDB : ∀ a b c, 0 ≤ DDB a b c) (hDDH : ∀ a b c, 0 ≤ DDH a b c)
    (hM : ∀ a b, ParabolicC0AlphaWith (B a b) (H a b) α (fun z => M z a b) s)
    (hN : ∀ a b, ParabolicC0AlphaWith (B a b) (H a b) α (fun z => N z a b) s)
    (hMdiff : ∀ a b,
      ParabolicC0AlphaWith (Bd a b) (Hd a b) α (fun z => M z a b - N z a b) s)
    (hE : ∀ a b c, ParabolicC0AlphaWith (DB a b c) (DH a b c) α
      (fun z => E z a b c) s)
    (hDdiff : ∀ a b c,
      ParabolicC0AlphaWith (DDB a b c) (DDH a b c) α
        (fun z => D z a b c - E z a b c) s)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicC0AlphaWith
      (matrixInvChristoffelEntrywiseSubBoundConst (𝕜 := 𝕜) δ B Bd DB DDB)
      (matrixInvChristoffelEntrywiseSubHolderConst
        (𝕜 := 𝕜) δ B H Bd Hd DB DH DDB DDH)
      α
      (fun z : ℝ × X =>
        (fun i j k =>
          (2 : 𝕜)⁻¹ *
            ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) i l *
              (D z j k l + D z k j l - D z l j k)) -
        (fun i j k =>
          (2 : 𝕜)⁻¹ *
            ∑ l : n, ((N z)⁻¹ : Matrix n n 𝕜) i l *
              (E z j k l + E z k j l - E z l j k))) s := by
  refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
  · intro i
    exact Finset.sum_nonneg fun j _hj =>
      Finset.sum_nonneg fun k _hk =>
        matrixInvChristoffelEntrySubBoundConst_nonneg
          (𝕜 := 𝕜) hδpos hBd hDB hDDB i j k
  · intro i
    exact Finset.sum_nonneg fun j _hj =>
      Finset.sum_nonneg fun k _hk =>
        matrixInvChristoffelEntrySubHolderConst_nonneg
          (𝕜 := 𝕜) hδpos hH hBd hHd hDB hDH hDDB hDDH i j k
  · intro i
    refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
    · intro j
      exact Finset.sum_nonneg fun k _hk =>
        matrixInvChristoffelEntrySubBoundConst_nonneg
          (𝕜 := 𝕜) hδpos hBd hDB hDDB i j k
    · intro j
      exact Finset.sum_nonneg fun k _hk =>
        matrixInvChristoffelEntrySubHolderConst_nonneg
          (𝕜 := 𝕜) hδpos hH hBd hHd hDB hDH hDDB hDDH i j k
    · intro j
      refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
      · intro k
        exact matrixInvChristoffelEntrySubBoundConst_nonneg
          (𝕜 := 𝕜) hδpos hBd hDB hDDB i j k
      · intro k
        exact matrixInvChristoffelEntrySubHolderConst_nonneg
          (𝕜 := 𝕜) hδpos hH hBd hHd hDB hDH hDDB hDDH i j k
      · intro k
        exact matrix_inv_christoffel_entry_sub_with_entrywise
          (M := M) (N := N) (D := D) (E := E)
          hH hBd hHd hM hN hMdiff hE hDdiff hδpos hdetM hdetN i j k

/-- The inverse-Christoffel array has an explicit bounded parabolic `C^{0,α}` estimate from
explicit metric-entry and derivative-array estimates. -/
theorem matrix_inv_christoffel_with {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {B H : n → n → ℝ} {DB DH : n → n → n → ℝ} {δ : ℝ}
    {M : ℝ × X → Matrix n n 𝕜} {D : ℝ × X → n → n → n → 𝕜}
    (hH : ∀ a b, 0 ≤ H a b)
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hDH : ∀ a b c, 0 ≤ DH a b c)
    (hM : ∀ a b, ParabolicC0AlphaWith (B a b) (H a b) α (fun z => M z a b) s)
    (hD : ∀ a b c, ParabolicC0AlphaWith (DB a b c) (DH a b c) α
      (fun z => D z a b c) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaWith
      (∑ i : n, ∑ j : n, ∑ k : n,
        matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ B DB i j k)
      (∑ i : n, ∑ j : n, ∑ k : n,
        matrixInvChristoffelEntryHolderConst (𝕜 := 𝕜) δ B H DB DH i j k)
      α
      (fun z i j k =>
        (2 : 𝕜)⁻¹ *
          ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) i l *
            (D z j k l + D z k j l - D z l j k)) s := by
  refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
  · intro i
    exact Finset.sum_nonneg fun j _hj =>
      Finset.sum_nonneg fun k _hk =>
        matrixInvChristoffelEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos B hDB i j k
  · intro i
    exact Finset.sum_nonneg fun j _hj =>
      Finset.sum_nonneg fun k _hk =>
        matrixInvChristoffelEntryHolderConst_nonneg (𝕜 := 𝕜) hH hδpos hDB hDH i j k
  · intro i
    refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
    · intro j
      exact Finset.sum_nonneg fun k _hk =>
        matrixInvChristoffelEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos B hDB i j k
    · intro j
      exact Finset.sum_nonneg fun k _hk =>
        matrixInvChristoffelEntryHolderConst_nonneg (𝕜 := 𝕜) hH hδpos hDB hDH i j k
    · intro j
      refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
      · intro k
        exact matrixInvChristoffelEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos B hDB i j k
      · intro k
        exact matrixInvChristoffelEntryHolderConst_nonneg (𝕜 := 𝕜) hH hδpos hDB hDH i j k
      · intro k
        exact matrix_inv_christoffel_entry_with (M := M) (D := D)
          hH hM hD hδpos hdet i j k

/-- Holder constant for the difference of two inverse-Christoffel arrays, using the sum of the
two individual inverse-Christoffel Holder constants. -/
def matrixInvChristoffelDiffHolderConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (B H : n → n → ℝ) (DB DH : n → n → n → ℝ) : ℝ :=
  (∑ i : n, ∑ j : n, ∑ k : n,
    matrixInvChristoffelEntryHolderConst (𝕜 := 𝕜) δ B H DB DH i j k) +
  (∑ i : n, ∑ j : n, ∑ k : n,
    matrixInvChristoffelEntryHolderConst (𝕜 := 𝕜) δ B H DB DH i j k)

theorem matrixInvChristoffelDiffHolderConst_nonneg {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {B H : n → n → ℝ}
    {DB DH : n → n → n → ℝ} (hH : ∀ a b, 0 ≤ H a b) (hδpos : 0 < δ)
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hDH : ∀ a b c, 0 ≤ DH a b c) :
    0 ≤ matrixInvChristoffelDiffHolderConst (𝕜 := 𝕜) δ B H DB DH := by
  exact add_nonneg
    (Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj =>
        Finset.sum_nonneg fun k _hk =>
          matrixInvChristoffelEntryHolderConst_nonneg
            (𝕜 := 𝕜) hH hδpos hDB hDH i j k)
    (Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj =>
        Finset.sum_nonneg fun k _hk =>
          matrixInvChristoffelEntryHolderConst_nonneg
            (𝕜 := 𝕜) hH hδpos hDB hDH i j k)

/-- The difference of two inverse-Christoffel arrays has parabolic `C^{0,α}` control: the sup
constant is the primitive-input bounded-difference constant and the Holder constant is the sum of
the two standalone inverse-Christoffel Holder constants. -/
theorem matrix_inv_christoffel_sub_with {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {B H : n → n → ℝ} {DB DH : n → n → n → ℝ}
    {ηM ηD : ℝ} {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    (hH : ∀ a b, 0 ≤ H a b)
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hDH : ∀ a b c, 0 ≤ DH a b c)
    (hM : ∀ a b, ParabolicC0AlphaWith (B a b) (H a b) α (fun z => M z a b) s)
    (hN : ∀ a b, ParabolicC0AlphaWith (B a b) (H a b) α (fun z => N z a b) s)
    (hD : ∀ a b c, ParabolicC0AlphaWith (DB a b c) (DH a b c) α
      (fun z => D z a b c) s)
    (hE : ∀ a b c, ParabolicC0AlphaWith (DB a b c) (DH a b c) α
      (fun z => E z a b c) s)
    (hηD : 0 ≤ ηD)
    (hMdiff : ∀ ⦃z : ℝ × X⦄, z ∈ s → ‖M z - N z‖ ≤ ηM)
    (hDdiff : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c,
      ‖D z a b c - E z a b c‖ ≤ ηD)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicC0AlphaWith
      (matrixInvChristoffelArrayDiffBoundConst (𝕜 := 𝕜) δ B DB ηD ηM)
      (matrixInvChristoffelDiffHolderConst (𝕜 := 𝕜) δ B H DB DH)
      α
      (fun z : ℝ × X =>
        (fun i j k =>
          (2 : 𝕜)⁻¹ *
            ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) i l *
              (D z j k l + D z k j l - D z l j k)) -
        (fun i j k =>
          (2 : 𝕜)⁻¹ *
            ∑ l : n, ((N z)⁻¹ : Matrix n n 𝕜) i l *
              (E z j k l + E z k j l - E z l j k))) s := by
  have hbounded :
      ParabolicBoundedWith
        (matrixInvChristoffelArrayDiffBoundConst (𝕜 := 𝕜) δ B DB ηD ηM)
        (fun z : ℝ × X =>
          (fun i j k =>
            (2 : 𝕜)⁻¹ *
              ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) i l *
                (D z j k l + D z k j l - D z l j k)) -
          (fun i j k =>
            (2 : 𝕜)⁻¹ *
              ∑ l : n, ((N z)⁻¹ : Matrix n n 𝕜) i l *
                (E z j k l + E z k j l - E z l j k))) s := by
    exact matrix_inv_christoffel_bounded_sub_le_const
      (s := s) (δ := δ) (C := B) (DB := DB) (ηM := ηM) (ηD := ηD)
      (fun z hz a b => (hM a b).bounded hz)
      (fun z hz a b => (hN a b).bounded hz)
      (fun z hz a b c => (hE a b c).bounded hz)
      hηD hMdiff hDdiff hδpos hdetM hdetN
  have hMD := matrix_inv_christoffel_with
    (M := M) (D := D) hH hDB hDH hM hD hδpos hdetM
  have hNE := matrix_inv_christoffel_with
    (M := N) (D := E) hH hDB hDH hN hE hδpos hdetN
  exact ⟨hbounded, by
    simpa [matrixInvChristoffelDiffHolderConst] using hMD.holder.sub hNE.holder⟩

end ParabolicC0AlphaOn

namespace ParabolicC0AlphaNormLe

variable {X : Type*} [PseudoMetricSpace X]
variable {α : ℝ} {s : Set (ℝ × X)}

/-- Entrywise metric control, derivative-array control, and a determinant lower bound package the
inverse-Christoffel array with the corresponding single-radius `C^{0,α}` bound. -/
theorem matrix_inv_christoffel_of_entries {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {R : n → n → ℝ} {RD : n → n → n → ℝ} {δ : ℝ}
    {M : ℝ × X → Matrix n n 𝕜} {D : ℝ × X → n → n → n → 𝕜}
    (hM : ∀ a b, ParabolicC0AlphaNormLe (R a b) α (fun z => M z a b) s)
    (hD : ∀ a b c, ParabolicC0AlphaNormLe (RD a b c) α (fun z => D z a b c) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaNormLe
      ((∑ i : n, ∑ j : n, ∑ k : n,
          ParabolicC0AlphaOn.matrixInvChristoffelEntryBoundConst
            (𝕜 := 𝕜) δ R RD i j k) +
        (∑ i : n, ∑ j : n, ∑ k : n,
          ParabolicC0AlphaOn.matrixInvChristoffelEntryHolderConst
            (𝕜 := 𝕜) δ R R RD RD i j k))
      α
      (fun z i j k =>
        (2 : 𝕜)⁻¹ *
          ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) i l *
            (D z j k l + D z k j l - D z l j k)) s := by
  have hR : ∀ a b, 0 ≤ R a b := fun a b => (hM a b).nonneg
  have hRD : ∀ a b c, 0 ≤ RD a b c := fun a b c => (hD a b c).nonneg
  exact ParabolicC0AlphaNormLe.of_c0AlphaWith
    (Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj =>
        Finset.sum_nonneg fun k _hk =>
          ParabolicC0AlphaOn.matrixInvChristoffelEntryBoundConst_nonneg
            (𝕜 := 𝕜) hδpos R hRD i j k)
    (Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj =>
        Finset.sum_nonneg fun k _hk =>
          ParabolicC0AlphaOn.matrixInvChristoffelEntryHolderConst_nonneg
            (𝕜 := 𝕜) hR hδpos hRD hRD i j k)
    (ParabolicC0AlphaOn.matrix_inv_christoffel_with
      (M := M) (D := D) (B := R) (H := R) (DB := RD) (DH := RD)
      hR hRD hRD
      (fun a b => ParabolicC0AlphaNormLe.c0AlphaWith_self (hM a b))
      (fun a b c => ParabolicC0AlphaNormLe.c0AlphaWith_self (hD a b c))
      hδpos hdet)

/-- Entrywise metric controls, derivative-array controls, their differences, and a common
determinant lower bound package inverse-Christoffel array differences with the corresponding
single-radius `C^{0,α}` bound. -/
theorem matrix_inv_christoffel_sub_entrywise_of_entries {n 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {R Rd : n → n → ℝ} {RD RDd : n → n → n → ℝ} {δ : ℝ}
    {M N : ℝ × X → Matrix n n 𝕜} {D E : ℝ × X → n → n → n → 𝕜}
    (hM : ∀ a b, ParabolicC0AlphaNormLe (R a b) α (fun z => M z a b) s)
    (hN : ∀ a b, ParabolicC0AlphaNormLe (R a b) α (fun z => N z a b) s)
    (hMdiff : ∀ a b, ParabolicC0AlphaNormLe (Rd a b) α
      (fun z => M z a b - N z a b) s)
    (hE : ∀ a b c, ParabolicC0AlphaNormLe (RD a b c) α (fun z => E z a b c) s)
    (hDdiff : ∀ a b c, ParabolicC0AlphaNormLe (RDd a b c) α
      (fun z => D z a b c - E z a b c) s)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicC0AlphaNormLe
      (ParabolicC0AlphaOn.matrixInvChristoffelEntrywiseSubBoundConst
          (𝕜 := 𝕜) δ R Rd RD RDd +
        ParabolicC0AlphaOn.matrixInvChristoffelEntrywiseSubHolderConst
          (𝕜 := 𝕜) δ R R Rd Rd RD RD RDd RDd)
      α
      (fun z : ℝ × X =>
        (fun i j k =>
          (2 : 𝕜)⁻¹ *
            ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) i l *
              (D z j k l + D z k j l - D z l j k)) -
        (fun i j k =>
          (2 : 𝕜)⁻¹ *
            ∑ l : n, ((N z)⁻¹ : Matrix n n 𝕜) i l *
              (E z j k l + E z k j l - E z l j k))) s := by
  have hR : ∀ a b, 0 ≤ R a b := fun a b => (hM a b).nonneg
  have hRd : ∀ a b, 0 ≤ Rd a b := fun a b => (hMdiff a b).nonneg
  have hRD : ∀ a b c, 0 ≤ RD a b c := fun a b c => (hE a b c).nonneg
  have hRDd : ∀ a b c, 0 ≤ RDd a b c := fun a b c => (hDdiff a b c).nonneg
  exact ParabolicC0AlphaNormLe.of_c0AlphaWith
    (ParabolicC0AlphaOn.matrixInvChristoffelEntrywiseSubBoundConst_nonneg
      (𝕜 := 𝕜) hδpos hRd hRD hRDd)
    (ParabolicC0AlphaOn.matrixInvChristoffelEntrywiseSubHolderConst_nonneg
      (𝕜 := 𝕜) hδpos hR hRd hRd hRD hRD hRDd hRDd)
    (ParabolicC0AlphaOn.matrix_inv_christoffel_sub_with_entrywise
      (M := M) (N := N) (D := D) (E := E)
      (B := R) (H := R) (Bd := Rd) (Hd := Rd)
      (DB := RD) (DH := RD) (DDB := RDd) (DDH := RDd)
      hR hRd hRd hRD hRD hRDd hRDd
      (fun a b => ParabolicC0AlphaNormLe.c0AlphaWith_self (hM a b))
      (fun a b => ParabolicC0AlphaNormLe.c0AlphaWith_self (hN a b))
      (fun a b => ParabolicC0AlphaNormLe.c0AlphaWith_self (hMdiff a b))
      (fun a b c => ParabolicC0AlphaNormLe.c0AlphaWith_self (hE a b c))
      (fun a b c => ParabolicC0AlphaNormLe.c0AlphaWith_self (hDdiff a b c))
      hδpos hdetM hdetN)

end ParabolicC0AlphaNormLe

namespace ParabolicC0AlphaOn

variable {X : Type*} [PseudoMetricSpace X]
variable {α : ℝ} {s : Set (ℝ × X)}

/-- Compact-domain version of `matrix_inv_christoffel_sub_with`: pointwise nonvanishing of both
metric determinants supplies one common determinant lower bound. -/
theorem matrix_inv_christoffel_sub_with_of_isCompact_det_ne_zero {n 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)}
    {B H : n → n → ℝ} {DB DH : n → n → n → ℝ} {ηM ηD : ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hB : ∀ a b, 0 ≤ B a b) (hH : ∀ a b, 0 ≤ H a b)
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hDH : ∀ a b c, 0 ≤ DH a b c)
    (hM : ∀ a b, ParabolicC0AlphaWith (B a b) (H a b) α (fun z => M z a b) K)
    (hN : ∀ a b, ParabolicC0AlphaWith (B a b) (H a b) α (fun z => N z a b) K)
    (hD : ∀ a b c, ParabolicC0AlphaWith (DB a b c) (DH a b c) α
      (fun z => D z a b c) K)
    (hE : ∀ a b c, ParabolicC0AlphaWith (DB a b c) (DH a b c) α
      (fun z => E z a b c) K)
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (N z).det ≠ 0)
    (hηD : 0 ≤ ηD)
    (hMdiff : ∀ ⦃z : ℝ × X⦄, z ∈ K → ‖M z - N z‖ ≤ ηM)
    (hDdiff : ∀ ⦃z : ℝ × X⦄, z ∈ K → ∀ a b c,
      ‖D z a b c - E z a b c‖ ≤ ηD) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvChristoffelArrayDiffBoundConst (𝕜 := 𝕜) δ B DB ηD ηM)
        (matrixInvChristoffelDiffHolderConst (𝕜 := 𝕜) δ B H DB DH)
        α
        (fun z : ℝ × X =>
          (fun i j k =>
            (2 : 𝕜)⁻¹ *
              ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) i l *
                (D z j k l + D z k j l - D z l j k)) -
          (fun i j k =>
            (2 : 𝕜)⁻¹ *
              ∑ l : n, ((N z)⁻¹ : Matrix n n 𝕜) i l *
                (E z j k l + E z k j l - E z l j k))) K := by
  have hMctrl : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) K := by
    intro a b
    exact ⟨B a b, hB a b, H a b, hH a b, hM a b⟩
  have hNctrl : ∀ a b, ParabolicC0AlphaOn α (fun z => N z a b) K := by
    intro a b
    exact ⟨B a b, hB a b, H a b, hH a b, hN a b⟩
  rcases matrix_det_pair_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) (N := N) hK hα hMctrl hNctrl hdetM_ne hdetN_ne with
    ⟨δ, hδpos, hdetM, hdetN⟩
  exact ⟨δ, hδpos, matrix_inv_christoffel_sub_with
    (M := M) (N := N) (D := D) (E := E)
    hH hDB hDH hM hN hD hE hηD hMdiff hDdiff hδpos hdetM hdetN⟩

/-- Compact-domain version of `matrix_inv_christoffel_sub_with_entrywise`: pointwise
nonvanishing of both metric determinants supplies one common determinant lower bound. -/
theorem matrix_inv_christoffel_sub_with_entrywise_of_isCompact_det_ne_zero {n 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)}
    {B H Bd Hd : n → n → ℝ} {DB DH DDB DDH : n → n → n → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hB : ∀ a b, 0 ≤ B a b) (hH : ∀ a b, 0 ≤ H a b)
    (hBd : ∀ a b, 0 ≤ Bd a b) (hHd : ∀ a b, 0 ≤ Hd a b)
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hDH : ∀ a b c, 0 ≤ DH a b c)
    (hDDB : ∀ a b c, 0 ≤ DDB a b c) (hDDH : ∀ a b c, 0 ≤ DDH a b c)
    (hM : ∀ a b, ParabolicC0AlphaWith (B a b) (H a b) α (fun z => M z a b) K)
    (hN : ∀ a b, ParabolicC0AlphaWith (B a b) (H a b) α (fun z => N z a b) K)
    (hMdiff : ∀ a b,
      ParabolicC0AlphaWith (Bd a b) (Hd a b) α (fun z => M z a b - N z a b) K)
    (hE : ∀ a b c, ParabolicC0AlphaWith (DB a b c) (DH a b c) α
      (fun z => E z a b c) K)
    (hDdiff : ∀ a b c,
      ParabolicC0AlphaWith (DDB a b c) (DDH a b c) α
        (fun z => D z a b c - E z a b c) K)
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (N z).det ≠ 0) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvChristoffelEntrywiseSubBoundConst (𝕜 := 𝕜) δ B Bd DB DDB)
        (matrixInvChristoffelEntrywiseSubHolderConst
          (𝕜 := 𝕜) δ B H Bd Hd DB DH DDB DDH)
        α
        (fun z : ℝ × X =>
          (fun i j k =>
            (2 : 𝕜)⁻¹ *
              ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) i l *
                (D z j k l + D z k j l - D z l j k)) -
          (fun i j k =>
            (2 : 𝕜)⁻¹ *
              ∑ l : n, ((N z)⁻¹ : Matrix n n 𝕜) i l *
                (E z j k l + E z k j l - E z l j k))) K := by
  have hMctrl : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) K := by
    intro a b
    exact ⟨B a b, hB a b, H a b, hH a b, hM a b⟩
  have hNctrl : ∀ a b, ParabolicC0AlphaOn α (fun z => N z a b) K := by
    intro a b
    exact ⟨B a b, hB a b, H a b, hH a b, hN a b⟩
  rcases matrix_det_pair_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) (N := N) hK hα hMctrl hNctrl hdetM_ne hdetN_ne with
    ⟨δ, hδpos, hdetM, hdetN⟩
  exact ⟨δ, hδpos, matrix_inv_christoffel_sub_with_entrywise
    (M := M) (N := N) (D := D) (E := E)
    hH hBd hHd hDB hDH hDDB hDDH hM hN hMdiff hE hDdiff
    hδpos hdetM hdetN⟩

/-- One inverse-Christoffel entry has existential parabolic `C^{0,α}` difference control from
entrywise metric and derivative-array difference controls. -/
theorem matrix_inv_christoffel_entry_sub_entrywise {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ}
    {M N : ℝ × X → Matrix n n 𝕜} {D E : ℝ × X → n → n → n → 𝕜}
    (hM : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) s)
    (hN : ∀ a b, ParabolicC0AlphaOn α (fun z => N z a b) s)
    (hMdiff : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b - N z a b) s)
    (hE : ∀ a b c, ParabolicC0AlphaOn α (fun z => E z a b c) s)
    (hDdiff : ∀ a b c,
      ParabolicC0AlphaOn α (fun z => D z a b c - E z a b c) s)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖)
    (i j k : n) :
    ParabolicC0AlphaOn α
      (fun z =>
        ((2 : 𝕜)⁻¹ *
          ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) i l *
            (D z j k l + D z k j l - D z l j k)) -
        ((2 : 𝕜)⁻¹ *
          ∑ l : n, ((N z)⁻¹ : Matrix n n 𝕜) i l *
            (E z j k l + E z k j l - E z l j k))) s := by
  classical
  let invM : n → ℝ × X → 𝕜 := fun l z => ((M z)⁻¹ : Matrix n n 𝕜) i l
  let invN : n → ℝ × X → 𝕜 := fun l z => ((N z)⁻¹ : Matrix n n 𝕜) i l
  let comboD : n → ℝ × X → 𝕜 :=
    fun l z => D z j k l + D z k j l - D z l j k
  let comboE : n → ℝ × X → 𝕜 :=
    fun l z => E z j k l + E z k j l - E z l j k
  have hcomboE : ∀ l ∈ (Finset.univ : Finset n),
      ParabolicC0AlphaOn α (comboE l) s := by
    intro l _hl
    have hsum := (hE j k l).add (hE k j l)
    simpa [comboE, add_assoc] using hsum.sub (hE l j k)
  have hcomboDiff : ∀ l ∈ (Finset.univ : Finset n),
      ParabolicC0AlphaOn α (fun z => comboD l z - comboE l z) s := by
    intro l _hl
    have hraw := ((hDdiff j k l).add (hDdiff k j l)).sub (hDdiff l j k)
    convert hraw using 1
    ext z
    simp [comboD, comboE]
    abel
  have hsum : ParabolicC0AlphaOn α
      (fun z =>
        (∑ l : n, invM l z * comboD l z) - ∑ l : n, invN l z * comboE l z) s := by
    simpa using
      (ParabolicC0AlphaOn.finset_sum_mul_sub_sum_mul (X := X) (α := α) (s := s)
        (S := (Finset.univ : Finset n))
        (u := fun l z => invM l z) (u' := fun l z => invN l z)
        (v := fun l z => comboD l z) (v' := fun l z => comboE l z)
        (fun l _hl => by
          simpa [invM] using matrix_inv_entry (M := M) hM hδpos hdetM i l)
        hcomboE
        (fun l _hl => by
          simpa [invM, invN] using
            matrix_inv_entry_sub (M := M) (N := N)
              hM hN hMdiff hδpos hdetM hdetN i l)
        hcomboDiff)
  have hhalf := hsum.smul ((2 : 𝕜)⁻¹)
  convert hhalf using 1
  · ext z
    simp [invM, invN, comboD, comboE, smul_eq_mul]
    ring

/-- Inverse-Christoffel arrays have existential parabolic `C^{0,α}` difference control from
entrywise metric and derivative-array difference controls. -/
theorem matrix_inv_christoffel_sub_entrywise {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ}
    {M N : ℝ × X → Matrix n n 𝕜} {D E : ℝ × X → n → n → n → 𝕜}
    (hM : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) s)
    (hN : ∀ a b, ParabolicC0AlphaOn α (fun z => N z a b) s)
    (hMdiff : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b - N z a b) s)
    (hE : ∀ a b c, ParabolicC0AlphaOn α (fun z => E z a b c) s)
    (hDdiff : ∀ a b c,
      ParabolicC0AlphaOn α (fun z => D z a b c - E z a b c) s)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × X =>
        (fun i j k =>
          (2 : 𝕜)⁻¹ *
            ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) i l *
              (D z j k l + D z k j l - D z l j k)) -
        (fun i j k =>
          (2 : 𝕜)⁻¹ *
            ∑ l : n, ((N z)⁻¹ : Matrix n n 𝕜) i l *
              (E z j k l + E z k j l - E z l j k))) s := by
  refine ParabolicC0AlphaOn.pi ?_
  intro i
  refine ParabolicC0AlphaOn.pi ?_
  intro j
  refine ParabolicC0AlphaOn.pi ?_
  intro k
  exact matrix_inv_christoffel_entry_sub_entrywise (M := M) (N := N) (D := D) (E := E)
    hM hN hMdiff hE hDdiff hδpos hdetM hdetN i j k

/-- Compact-domain inverse-Christoffel arrays have existential parabolic `C^{0,α}` difference
control from entrywise controls and pointwise nonvanishing determinants. -/
theorem matrix_inv_christoffel_sub_entrywise_of_isCompact_det_ne_zero {n 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)}
    {M N : ℝ × X → Matrix n n 𝕜} {D E : ℝ × X → n → n → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hM : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) K)
    (hN : ∀ a b, ParabolicC0AlphaOn α (fun z => N z a b) K)
    (hMdiff : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b - N z a b) K)
    (hE : ∀ a b c, ParabolicC0AlphaOn α (fun z => E z a b c) K)
    (hDdiff : ∀ a b c,
      ParabolicC0AlphaOn α (fun z => D z a b c - E z a b c) K)
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (N z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ParabolicC0AlphaOn α
        (fun z : ℝ × X =>
          (fun i j k =>
            (2 : 𝕜)⁻¹ *
              ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) i l *
                (D z j k l + D z k j l - D z l j k)) -
          (fun i j k =>
            (2 : 𝕜)⁻¹ *
              ∑ l : n, ((N z)⁻¹ : Matrix n n 𝕜) i l *
                (E z j k l + E z k j l - E z l j k))) K := by
  rcases matrix_det_pair_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) (N := N) hK hα hM hN hdetM_ne hdetN_ne with
    ⟨δ, hδpos, hdetM, hdetN⟩
  exact ⟨δ, hδpos, matrix_inv_christoffel_sub_entrywise
    (M := M) (N := N) (D := D) (E := E)
    hM hN hMdiff hE hDdiff hδpos hdetM hdetN⟩

/-- Compact-domain Christoffel-symbol type array closure from entrywise control and pointwise
nonvanishing determinant. -/
theorem matrix_inv_christoffel_of_isCompact_det_ne_zero {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)}
    {M : ℝ × X → Matrix n n 𝕜} {D : ℝ × X → n → n → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hM : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) K)
    (hD : ∀ i j k, ParabolicC0AlphaOn α (fun z => D z i j k) K)
    (hdet_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0) :
    ParabolicC0AlphaOn α
      (fun z i j k =>
        (2 : 𝕜)⁻¹ *
          ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) i l *
            (D z j k l + D z k j l - D z l j k)) K := by
  rcases matrix_det_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hM hdet_ne with
    ⟨δ, hδpos, hdet⟩
  exact matrix_inv_christoffel (M := M) (D := D) hM hD hδpos hdet

/-- Compact-domain finite-family Christoffel-symbol type array closure from entrywise controls
and pointwise nonvanishing determinants, with one determinant lower bound shared by the family. -/
theorem matrix_inv_christoffel_family_of_isCompact_det_ne_zero {ι n 𝕜 : Type*}
    [Fintype ι] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {K : Set (ℝ × X)}
    {M : ι → ℝ × X → Matrix n n 𝕜}
    {D : ι → ℝ × X → n → n → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hM : ∀ r i j, ParabolicC0AlphaOn α (fun z => M r z i j) K)
    (hD : ∀ r i j k, ParabolicC0AlphaOn α (fun z => D r z i j k) K)
    (hdet_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (M r z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M r z).det‖) ∧
      ∀ r,
        ParabolicC0AlphaOn α
          (fun z i j k =>
            (2 : 𝕜)⁻¹ *
              ∑ l : n, ((M r z)⁻¹ : Matrix n n 𝕜) i l *
                (D r z j k l + D r z k j l - D r z l j k)) K := by
  rcases matrix_det_family_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hM hdet_ne with
    ⟨δ, hδpos, hdet⟩
  refine ⟨δ, hδpos, hdet, ?_⟩
  intro r
  exact matrix_inv_christoffel
    (M := M r) (D := D r) (hM r) (hD r) hδpos (hdet r)

/-- A finite family of inverse-Christoffel arrays has explicit bounded parabolic `C^{0,α}`
estimates with one compact determinant lower bound shared by the family. -/
theorem matrix_inv_christoffel_family_with_of_isCompact_det_ne_zero {ι n 𝕜 : Type*}
    [Fintype ι] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {K : Set (ℝ × X)}
    {B H : ι → n → n → ℝ} {DB DH : ι → n → n → n → ℝ}
    {M : ι → ℝ × X → Matrix n n 𝕜}
    {D : ι → ℝ × X → n → n → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hB : ∀ r a b, 0 ≤ B r a b) (hH : ∀ r a b, 0 ≤ H r a b)
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hDH : ∀ r a b c, 0 ≤ DH r a b c)
    (hM : ∀ r a b,
      ParabolicC0AlphaWith (B r a b) (H r a b) α (fun z => M r z a b) K)
    (hD : ∀ r a b c,
      ParabolicC0AlphaWith (DB r a b c) (DH r a b c) α
        (fun z => D r z a b c) K)
    (hdet_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (M r z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M r z).det‖) ∧
      ∀ r,
        ParabolicC0AlphaWith
          (∑ i : n, ∑ j : n, ∑ k : n,
            matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ (B r) (DB r) i j k)
          (∑ i : n, ∑ j : n, ∑ k : n,
            matrixInvChristoffelEntryHolderConst (𝕜 := 𝕜) δ (B r) (H r) (DB r) (DH r) i j k)
          α
          (fun z i j k =>
            (2 : 𝕜)⁻¹ *
              ∑ l : n, ((M r z)⁻¹ : Matrix n n 𝕜) i l *
                (D r z j k l + D r z k j l - D r z l j k)) K := by
  have hMctrl : ∀ r a b, ParabolicC0AlphaOn α (fun z => M r z a b) K := by
    intro r a b
    exact ⟨B r a b, hB r a b, H r a b, hH r a b, hM r a b⟩
  rcases matrix_det_family_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hMctrl hdet_ne with
    ⟨δ, hδpos, hdet⟩
  refine ⟨δ, hδpos, hdet, ?_⟩
  intro r
  exact matrix_inv_christoffel_with
    (M := M r) (D := D r)
    (hH r) (hDB r) (hDH r) (hM r) (hD r) hδpos (hdet r)

/-- Quantitative sup constant for one entry of the finite inverse-principal contraction
`M⁻¹ᵃᵇ T_abij`. -/
def matrixInvTwoIndexContractEntryBoundConst {n p q 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] (δ : ℝ) (B : n → n → ℝ)
    (TB : n → n → p → q → ℝ) (i : p) (j : q) : ℝ :=
  ∑ a : n, ∑ b : n,
    matrixInvEntryBoundConst (𝕜 := 𝕜) δ B a b * TB a b i j

/-- Quantitative Holder constant for one entry of the finite inverse-principal contraction
`M⁻¹ᵃᵇ T_abij`. -/
def matrixInvTwoIndexContractEntryHolderConst {n p q 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] (δ : ℝ) (B H : n → n → ℝ)
    (TB TH : n → n → p → q → ℝ) (i : p) (j : q) : ℝ :=
  ∑ a : n, ∑ b : n,
    (matrixInvEntryBoundConst (𝕜 := 𝕜) δ B a b * TH a b i j +
      TB a b i j * matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H a b)

/-- Difference-based sup constant for one entry of a finite inverse-principal contraction. -/
def matrixInvTwoIndexContractEntrySubBoundConst {n p q 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] (δ : ℝ) (B Bd : n → n → ℝ)
    (TB TDB : n → n → p → q → ℝ) (i : p) (j : q) : ℝ :=
  ∑ a : n, ∑ b : n,
    (matrixInvEntryBoundConst (𝕜 := 𝕜) δ B a b * TDB a b i j +
      matrixInvEntrySubBoundConst (𝕜 := 𝕜) δ B Bd a b * TB a b i j)

/-- Difference-based Holder constant for one entry of a finite inverse-principal contraction. -/
def matrixInvTwoIndexContractEntrySubHolderConst {n p q 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] (δ : ℝ) (B H Bd Hd : n → n → ℝ)
    (TB TH TDB TDH : n → n → p → q → ℝ) (i : p) (j : q) : ℝ :=
  ∑ a : n, ∑ b : n,
    ((matrixInvEntryBoundConst (𝕜 := 𝕜) δ B a b * TDH a b i j +
        TDB a b i j * matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H a b) +
      (matrixInvEntrySubBoundConst (𝕜 := 𝕜) δ B Bd a b * TH a b i j +
        TB a b i j * matrixInvEntrySubHolderConst (𝕜 := 𝕜) δ B H Bd Hd a b))

/-- Difference-based sup constant for a finite inverse-principal contraction matrix. -/
def matrixInvTwoIndexContractEntrywiseSubBoundConst {n p q 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [Fintype p] [Fintype q] [NormedField 𝕜]
    (δ : ℝ) (B Bd : n → n → ℝ) (TB TDB : n → n → p → q → ℝ) : ℝ :=
  ∑ i : p, ∑ j : q,
    matrixInvTwoIndexContractEntrySubBoundConst (𝕜 := 𝕜) δ B Bd TB TDB i j

/-- Difference-based Holder constant for a finite inverse-principal contraction matrix. -/
def matrixInvTwoIndexContractEntrywiseSubHolderConst {n p q 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [Fintype p] [Fintype q] [NormedField 𝕜]
    (δ : ℝ) (B H Bd Hd : n → n → ℝ) (TB TH TDB TDH : n → n → p → q → ℝ) :
    ℝ :=
  ∑ i : p, ∑ j : q,
    matrixInvTwoIndexContractEntrySubHolderConst (𝕜 := 𝕜) δ B H Bd Hd TB TH TDB TDH i j

theorem matrixInvTwoIndexContractEntryBoundConst_nonneg {n p q 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] {δ : ℝ} (hδpos : 0 < δ)
    (B : n → n → ℝ) {TB : n → n → p → q → ℝ}
    (hTB : ∀ a b i j, 0 ≤ TB a b i j) (i : p) (j : q) :
    0 ≤ matrixInvTwoIndexContractEntryBoundConst (𝕜 := 𝕜) δ B TB i j := by
  exact Finset.sum_nonneg fun a _ha =>
    Finset.sum_nonneg fun b _hb =>
      mul_nonneg (matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos B a b)
        (hTB a b i j)

theorem matrixInvTwoIndexContractEntryHolderConst_nonneg {n p q 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {B H : n → n → ℝ}
    (hH : ∀ a b, 0 ≤ H a b) (hδpos : 0 < δ) {TB TH : n → n → p → q → ℝ}
    (hTB : ∀ a b i j, 0 ≤ TB a b i j) (hTH : ∀ a b i j, 0 ≤ TH a b i j)
    (i : p) (j : q) :
    0 ≤ matrixInvTwoIndexContractEntryHolderConst (𝕜 := 𝕜) δ B H TB TH i j := by
  exact Finset.sum_nonneg fun a _ha =>
    Finset.sum_nonneg fun b _hb =>
      add_nonneg
        (mul_nonneg (matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos B a b)
          (hTH a b i j))
        (mul_nonneg (hTB a b i j)
          (matrixInvEntryHolderConst_nonneg (𝕜 := 𝕜) hH hδpos a b))

theorem matrixInvTwoIndexContractEntrySubBoundConst_nonneg {n p q 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {B Bd : n → n → ℝ}
    (hδpos : 0 < δ) (hBd : ∀ a b, 0 ≤ Bd a b)
    {TB TDB : n → n → p → q → ℝ}
    (hTB : ∀ a b i j, 0 ≤ TB a b i j) (hTDB : ∀ a b i j, 0 ≤ TDB a b i j)
    (i : p) (j : q) :
    0 ≤ matrixInvTwoIndexContractEntrySubBoundConst (𝕜 := 𝕜) δ B Bd TB TDB i j := by
  exact Finset.sum_nonneg fun a _ha =>
    Finset.sum_nonneg fun b _hb =>
      add_nonneg
        (mul_nonneg (matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos B a b)
          (hTDB a b i j))
        (mul_nonneg (matrixInvEntrySubBoundConst_nonneg (𝕜 := 𝕜) hδpos hBd a b)
          (hTB a b i j))

theorem matrixInvTwoIndexContractEntrySubHolderConst_nonneg {n p q 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] {δ : ℝ}
    {B H Bd Hd : n → n → ℝ} (hδpos : 0 < δ) (hH : ∀ a b, 0 ≤ H a b)
    (hBd : ∀ a b, 0 ≤ Bd a b) (hHd : ∀ a b, 0 ≤ Hd a b)
    {TB TH TDB TDH : n → n → p → q → ℝ}
    (hTB : ∀ a b i j, 0 ≤ TB a b i j) (hTH : ∀ a b i j, 0 ≤ TH a b i j)
    (hTDB : ∀ a b i j, 0 ≤ TDB a b i j)
    (hTDH : ∀ a b i j, 0 ≤ TDH a b i j) (i : p) (j : q) :
    0 ≤ matrixInvTwoIndexContractEntrySubHolderConst
      (𝕜 := 𝕜) δ B H Bd Hd TB TH TDB TDH i j := by
  exact Finset.sum_nonneg fun a _ha =>
    Finset.sum_nonneg fun b _hb =>
      add_nonneg
        (add_nonneg
          (mul_nonneg (matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos B a b)
            (hTDH a b i j))
          (mul_nonneg (hTDB a b i j)
            (matrixInvEntryHolderConst_nonneg (𝕜 := 𝕜) hH hδpos a b)))
        (add_nonneg
          (mul_nonneg (matrixInvEntrySubBoundConst_nonneg (𝕜 := 𝕜) hδpos hBd a b)
            (hTH a b i j))
          (mul_nonneg (hTB a b i j)
            (matrixInvEntrySubHolderConst_nonneg (𝕜 := 𝕜) hδpos hH hBd hHd a b)))

theorem matrixInvTwoIndexContractEntrywiseSubBoundConst_nonneg {n p q 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [Fintype p] [Fintype q] [NormedField 𝕜]
    {δ : ℝ} {B Bd : n → n → ℝ} (hδpos : 0 < δ) (hBd : ∀ a b, 0 ≤ Bd a b)
    {TB TDB : n → n → p → q → ℝ}
    (hTB : ∀ a b i j, 0 ≤ TB a b i j) (hTDB : ∀ a b i j, 0 ≤ TDB a b i j) :
    0 ≤ matrixInvTwoIndexContractEntrywiseSubBoundConst (𝕜 := 𝕜) δ B Bd TB TDB := by
  exact Finset.sum_nonneg fun i _hi =>
    Finset.sum_nonneg fun j _hj =>
      matrixInvTwoIndexContractEntrySubBoundConst_nonneg
        (𝕜 := 𝕜) hδpos hBd hTB hTDB i j

theorem matrixInvTwoIndexContractEntrywiseSubHolderConst_nonneg {n p q 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [Fintype p] [Fintype q] [NormedField 𝕜]
    {δ : ℝ} {B H Bd Hd : n → n → ℝ}
    (hδpos : 0 < δ) (hH : ∀ a b, 0 ≤ H a b)
    (hBd : ∀ a b, 0 ≤ Bd a b) (hHd : ∀ a b, 0 ≤ Hd a b)
    {TB TH TDB TDH : n → n → p → q → ℝ}
    (hTB : ∀ a b i j, 0 ≤ TB a b i j) (hTH : ∀ a b i j, 0 ≤ TH a b i j)
    (hTDB : ∀ a b i j, 0 ≤ TDB a b i j)
    (hTDH : ∀ a b i j, 0 ≤ TDH a b i j) :
    0 ≤ matrixInvTwoIndexContractEntrywiseSubHolderConst
      (𝕜 := 𝕜) δ B H Bd Hd TB TH TDB TDH := by
  exact Finset.sum_nonneg fun i _hi =>
    Finset.sum_nonneg fun j _hj =>
      matrixInvTwoIndexContractEntrySubHolderConst_nonneg
        (𝕜 := 𝕜) hδpos hH hBd hHd hTB hTH hTDB hTDH i j

/-- Finite inverse-matrix contractions against a four-index coefficient array preserve parabolic
`C^{0,α}` control. This is the coordinate-algebra pattern for terms such as
`g^{ab} H_{abij}` in a local Ricci-DeTurck principal part. -/
theorem matrix_inv_two_index_contract_entry {n p q 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {M : ℝ × X → Matrix n n 𝕜}
    {T : ℝ × X → n → n → p → q → 𝕜}
    (hM : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) s)
    (hT : ∀ a b i j, ParabolicC0AlphaOn α (fun z => T z a b i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (i : p) (j : q) :
    ParabolicC0AlphaOn α
      (fun z => ∑ a : n, ∑ b : n,
        ((M z)⁻¹ : Matrix n n 𝕜) a b * T z a b i j) s := by
  have hinner : ∀ a : n,
      ParabolicC0AlphaOn α
        (fun z => ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * T z a b i j) s := by
    intro a
    simpa using
      (ParabolicC0AlphaOn.sum (X := X) (α := α) (s := s)
        (S := (Finset.univ : Finset n))
        (u := fun b z => ((M z)⁻¹ : Matrix n n 𝕜) a b * T z a b i j)
        (fun b _hb => (matrix_inv_entry (M := M) hM hδpos hdet a b).mul (hT a b i j)))
  simpa using
    (ParabolicC0AlphaOn.sum (X := X) (α := α) (s := s)
      (S := (Finset.univ : Finset n))
      (u := fun a z => ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * T z a b i j)
      (fun a _ha => hinner a))

/-- Finite inverse-matrix contractions against a four-index coefficient array package as a
matrix-valued parabolic `C^{0,α}` function. -/
theorem matrix_inv_two_index_contract {n p q 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [Fintype p] [Fintype q] [NormedField 𝕜] {δ : ℝ}
    {M : ℝ × X → Matrix n n 𝕜} {T : ℝ × X → n → n → p → q → 𝕜}
    (hM : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) s)
    (hT : ∀ a b i j, ParabolicC0AlphaOn α (fun z => T z a b i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × X =>
        (fun i j =>
          ∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * T z a b i j :
            Matrix p q 𝕜)) s :=
  matrix_of_entries fun i j => matrix_inv_two_index_contract_entry hM hT hδpos hdet i j

/-- One entry of a finite inverse-principal contraction has an explicit bounded parabolic
`C^{0,α}` estimate from explicit metric-entry and coefficient-array estimates. -/
theorem matrix_inv_two_index_contract_entry_with {n p q 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {B H : n → n → ℝ}
    {TB TH : n → n → p → q → ℝ}
    {M : ℝ × X → Matrix n n 𝕜} {T : ℝ × X → n → n → p → q → 𝕜}
    (hH : ∀ a b, 0 ≤ H a b)
    (hM : ∀ a b, ParabolicC0AlphaWith (B a b) (H a b) α (fun z => M z a b) s)
    (hT : ∀ a b i j, ParabolicC0AlphaWith (TB a b i j) (TH a b i j) α
      (fun z => T z a b i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (i : p) (j : q) :
    ParabolicC0AlphaWith
      (matrixInvTwoIndexContractEntryBoundConst (𝕜 := 𝕜) δ B TB i j)
      (matrixInvTwoIndexContractEntryHolderConst (𝕜 := 𝕜) δ B H TB TH i j)
      α
      (fun z => ∑ a : n, ∑ b : n,
        ((M z)⁻¹ : Matrix n n 𝕜) a b * T z a b i j) s := by
  classical
  let inner : n → ℝ × X → 𝕜 := fun a z =>
    ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * T z a b i j
  have hinner : ∀ a ∈ (Finset.univ : Finset n),
      ParabolicC0AlphaWith
        (∑ b : n, matrixInvEntryBoundConst (𝕜 := 𝕜) δ B a b * TB a b i j)
        (∑ b : n,
          (matrixInvEntryBoundConst (𝕜 := 𝕜) δ B a b * TH a b i j +
            TB a b i j * matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H a b))
        α (inner a) s := by
    intro a _ha
    let term : n → ℝ × X → 𝕜 := fun b z =>
      ((M z)⁻¹ : Matrix n n 𝕜) a b * T z a b i j
    have hterm : ∀ b ∈ (Finset.univ : Finset n),
        ParabolicC0AlphaWith
          (matrixInvEntryBoundConst (𝕜 := 𝕜) δ B a b * TB a b i j)
          (matrixInvEntryBoundConst (𝕜 := 𝕜) δ B a b * TH a b i j +
            TB a b i j * matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H a b)
          α (term b) s := by
      intro b _hb
      have hinv :
          ParabolicC0AlphaWith
            (matrixInvEntryBoundConst (𝕜 := 𝕜) δ B a b)
            (matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H a b)
            α (fun z => ((M z)⁻¹ : Matrix n n 𝕜) a b) s :=
        matrix_inv_entry_with (M := M) hH hM hδpos hdet a b
      simpa [term] using
        hinv.mul (hT a b i j) (matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos B a b)
    simpa [inner] using
      (ParabolicC0AlphaWith.sum (X := X) (α := α) (s := s)
        (S := (Finset.univ : Finset n))
        (B := fun b => matrixInvEntryBoundConst (𝕜 := 𝕜) δ B a b * TB a b i j)
        (H := fun b =>
          matrixInvEntryBoundConst (𝕜 := 𝕜) δ B a b * TH a b i j +
            TB a b i j * matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H a b)
        (u := term) hterm)
  simpa [inner, matrixInvTwoIndexContractEntryBoundConst,
    matrixInvTwoIndexContractEntryHolderConst] using
    (ParabolicC0AlphaWith.sum (X := X) (α := α) (s := s)
      (S := (Finset.univ : Finset n))
      (B := fun a => ∑ b : n,
        matrixInvEntryBoundConst (𝕜 := 𝕜) δ B a b * TB a b i j)
      (H := fun a => ∑ b : n,
        (matrixInvEntryBoundConst (𝕜 := 𝕜) δ B a b * TH a b i j +
          TB a b i j * matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H a b))
        (u := inner) hinner)

/-- One entry of a finite inverse-principal contraction has difference-based parabolic
`C^{0,α}` control from entrywise metric and coefficient-array difference controls. -/
theorem matrix_inv_two_index_contract_entry_sub_with_entrywise {n p q 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] {δ : ℝ}
    {B H Bd Hd : n → n → ℝ} {TB TH TDB TDH : n → n → p → q → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜} {T U : ℝ × X → n → n → p → q → 𝕜}
    (hH : ∀ a b, 0 ≤ H a b)
    (hBd : ∀ a b, 0 ≤ Bd a b) (hHd : ∀ a b, 0 ≤ Hd a b)
    (hM : ∀ a b, ParabolicC0AlphaWith (B a b) (H a b) α (fun z => M z a b) s)
    (hN : ∀ a b, ParabolicC0AlphaWith (B a b) (H a b) α (fun z => N z a b) s)
    (hMdiff : ∀ a b,
      ParabolicC0AlphaWith (Bd a b) (Hd a b) α (fun z => M z a b - N z a b) s)
    (hU : ∀ a b i j, ParabolicC0AlphaWith (TB a b i j) (TH a b i j) α
      (fun z => U z a b i j) s)
    (hTdiff : ∀ a b i j,
      ParabolicC0AlphaWith (TDB a b i j) (TDH a b i j) α
        (fun z => T z a b i j - U z a b i j) s)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖)
    (i : p) (j : q) :
    ParabolicC0AlphaWith
      (matrixInvTwoIndexContractEntrySubBoundConst (𝕜 := 𝕜) δ B Bd TB TDB i j)
      (matrixInvTwoIndexContractEntrySubHolderConst
        (𝕜 := 𝕜) δ B H Bd Hd TB TH TDB TDH i j)
      α
      (fun z =>
        (∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * T z a b i j) -
          ∑ a : n, ∑ b : n, ((N z)⁻¹ : Matrix n n 𝕜) a b * U z a b i j) s := by
  classical
  let invM : n → n → ℝ × X → 𝕜 :=
    fun a b z => ((M z)⁻¹ : Matrix n n 𝕜) a b
  let invN : n → n → ℝ × X → 𝕜 :=
    fun a b z => ((N z)⁻¹ : Matrix n n 𝕜) a b
  let coeffT : n → n → ℝ × X → 𝕜 := fun a b z => T z a b i j
  let coeffU : n → n → ℝ × X → 𝕜 := fun a b z => U z a b i j
  have hinner : ∀ a ∈ (Finset.univ : Finset n),
      ParabolicC0AlphaWith
        (∑ b : n,
          (matrixInvEntryBoundConst (𝕜 := 𝕜) δ B a b * TDB a b i j +
            matrixInvEntrySubBoundConst (𝕜 := 𝕜) δ B Bd a b * TB a b i j))
        (∑ b : n,
          ((matrixInvEntryBoundConst (𝕜 := 𝕜) δ B a b * TDH a b i j +
              TDB a b i j * matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H a b) +
            (matrixInvEntrySubBoundConst (𝕜 := 𝕜) δ B Bd a b * TH a b i j +
              TB a b i j * matrixInvEntrySubHolderConst (𝕜 := 𝕜) δ B H Bd Hd a b)))
        α
        (fun z =>
          (∑ b : n, invM a b z * coeffT a b z) -
            ∑ b : n, invN a b z * coeffU a b z) s := by
    intro a _ha
    have hinvM : ∀ b ∈ (Finset.univ : Finset n),
        ParabolicC0AlphaWith
          (matrixInvEntryBoundConst (𝕜 := 𝕜) δ B a b)
          (matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H a b)
          α (invM a b) s := by
      intro b _hb
      simpa [invM] using matrix_inv_entry_with (M := M) hH hM hδpos hdetM a b
    have hinvDiff : ∀ b ∈ (Finset.univ : Finset n),
        ParabolicC0AlphaWith
          (matrixInvEntrySubBoundConst (𝕜 := 𝕜) δ B Bd a b)
          (matrixInvEntrySubHolderConst (𝕜 := 𝕜) δ B H Bd Hd a b)
          α (fun z => invM a b z - invN a b z) s := by
      intro b _hb
      simpa [invM, invN] using
        matrix_inv_entry_sub_with (M := M) (N := N)
          hH hBd hHd hM hN hMdiff hδpos hdetM hdetN a b
    have hcoeffU : ∀ b ∈ (Finset.univ : Finset n),
        ParabolicC0AlphaWith (TB a b i j) (TH a b i j) α (coeffU a b) s := by
      intro b _hb
      simpa [coeffU] using hU a b i j
    have hcoeffDiff : ∀ b ∈ (Finset.univ : Finset n),
        ParabolicC0AlphaWith (TDB a b i j) (TDH a b i j) α
          (fun z => coeffT a b z - coeffU a b z) s := by
      intro b _hb
      simpa [coeffT, coeffU] using hTdiff a b i j
    simpa [invM, invN, coeffT, coeffU] using
      (ParabolicC0AlphaWith.finset_sum_mul_sub_sum_mul (X := X) (α := α) (s := s)
        (S := (Finset.univ : Finset n))
        (Bu := fun b => matrixInvEntryBoundConst (𝕜 := 𝕜) δ B a b)
        (Hu := fun b => matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H a b)
        (Bv := fun b => TB a b i j)
        (Hv := fun b => TH a b i j)
        (Bdu := fun b => matrixInvEntrySubBoundConst (𝕜 := 𝕜) δ B Bd a b)
        (Hdu := fun b => matrixInvEntrySubHolderConst (𝕜 := 𝕜) δ B H Bd Hd a b)
        (Bdv := fun b => TDB a b i j)
        (Hdv := fun b => TDH a b i j)
        (u := invM a) (u' := invN a) (v := coeffT a) (v' := coeffU a)
        hinvM hcoeffU hinvDiff hcoeffDiff
        (fun b _hb => matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos B a b)
        (fun b _hb => matrixInvEntrySubBoundConst_nonneg (𝕜 := 𝕜) hδpos hBd a b))
  have hsum :
      ParabolicC0AlphaWith
        (∑ a : n, ∑ b : n,
          (matrixInvEntryBoundConst (𝕜 := 𝕜) δ B a b * TDB a b i j +
            matrixInvEntrySubBoundConst (𝕜 := 𝕜) δ B Bd a b * TB a b i j))
        (∑ a : n, ∑ b : n,
          ((matrixInvEntryBoundConst (𝕜 := 𝕜) δ B a b * TDH a b i j +
              TDB a b i j * matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H a b) +
            (matrixInvEntrySubBoundConst (𝕜 := 𝕜) δ B Bd a b * TH a b i j +
              TB a b i j * matrixInvEntrySubHolderConst (𝕜 := 𝕜) δ B H Bd Hd a b)))
        α
        (fun z =>
          ∑ a : n,
            ((∑ b : n, invM a b z * coeffT a b z) -
              ∑ b : n, invN a b z * coeffU a b z)) s := by
    simpa using
      (ParabolicC0AlphaWith.sum (X := X) (α := α) (s := s)
        (S := (Finset.univ : Finset n))
        (B := fun a => ∑ b : n,
          (matrixInvEntryBoundConst (𝕜 := 𝕜) δ B a b * TDB a b i j +
            matrixInvEntrySubBoundConst (𝕜 := 𝕜) δ B Bd a b * TB a b i j))
        (H := fun a => ∑ b : n,
          ((matrixInvEntryBoundConst (𝕜 := 𝕜) δ B a b * TDH a b i j +
              TDB a b i j * matrixInvEntryHolderConst (𝕜 := 𝕜) δ B H a b) +
            (matrixInvEntrySubBoundConst (𝕜 := 𝕜) δ B Bd a b * TH a b i j +
              TB a b i j * matrixInvEntrySubHolderConst (𝕜 := 𝕜) δ B H Bd Hd a b)))
        (u := fun a z =>
          (∑ b : n, invM a b z * coeffT a b z) -
            ∑ b : n, invN a b z * coeffU a b z)
        hinner)
  convert hsum using 1 <;>
    first
    | rfl
    | (funext z
       simp [invM, invN, coeffT, coeffU, Finset.sum_sub_distrib])

/-- Finite inverse-principal contractions have difference-based parabolic `C^{0,α}` control from
entrywise metric and coefficient-array difference controls. -/
theorem matrix_inv_two_index_contract_sub_with_entrywise {n p q 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [Fintype p] [Fintype q] [NormedField 𝕜]
    {δ : ℝ} {B H Bd Hd : n → n → ℝ} {TB TH TDB TDH : n → n → p → q → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜} {T U : ℝ × X → n → n → p → q → 𝕜}
    (hH : ∀ a b, 0 ≤ H a b)
    (hBd : ∀ a b, 0 ≤ Bd a b) (hHd : ∀ a b, 0 ≤ Hd a b)
    (hTB : ∀ a b i j, 0 ≤ TB a b i j) (hTH : ∀ a b i j, 0 ≤ TH a b i j)
    (hTDB : ∀ a b i j, 0 ≤ TDB a b i j)
    (hTDH : ∀ a b i j, 0 ≤ TDH a b i j)
    (hM : ∀ a b, ParabolicC0AlphaWith (B a b) (H a b) α (fun z => M z a b) s)
    (hN : ∀ a b, ParabolicC0AlphaWith (B a b) (H a b) α (fun z => N z a b) s)
    (hMdiff : ∀ a b,
      ParabolicC0AlphaWith (Bd a b) (Hd a b) α (fun z => M z a b - N z a b) s)
    (hU : ∀ a b i j, ParabolicC0AlphaWith (TB a b i j) (TH a b i j) α
      (fun z => U z a b i j) s)
    (hTdiff : ∀ a b i j,
      ParabolicC0AlphaWith (TDB a b i j) (TDH a b i j) α
        (fun z => T z a b i j - U z a b i j) s)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicC0AlphaWith
      (matrixInvTwoIndexContractEntrywiseSubBoundConst (𝕜 := 𝕜) δ B Bd TB TDB)
      (matrixInvTwoIndexContractEntrywiseSubHolderConst
        (𝕜 := 𝕜) δ B H Bd Hd TB TH TDB TDH)
      α
      (fun z : ℝ × X =>
        ((fun i j => ∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b *
          T z a b i j) : Matrix p q 𝕜) -
        ((fun i j => ∑ a : n, ∑ b : n, ((N z)⁻¹ : Matrix n n 𝕜) a b *
          U z a b i j) : Matrix p q 𝕜)) s := by
  refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
  · intro i
    exact Finset.sum_nonneg fun j _hj =>
      matrixInvTwoIndexContractEntrySubBoundConst_nonneg
        (𝕜 := 𝕜) hδpos hBd hTB hTDB i j
  · intro i
    exact Finset.sum_nonneg fun j _hj =>
      matrixInvTwoIndexContractEntrySubHolderConst_nonneg
        (𝕜 := 𝕜) hδpos hH hBd hHd hTB hTH hTDB hTDH i j
  · intro i
    refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
    · intro j
      exact matrixInvTwoIndexContractEntrySubBoundConst_nonneg
        (𝕜 := 𝕜) hδpos hBd hTB hTDB i j
    · intro j
      exact matrixInvTwoIndexContractEntrySubHolderConst_nonneg
        (𝕜 := 𝕜) hδpos hH hBd hHd hTB hTH hTDB hTDH i j
    · intro j
      exact matrix_inv_two_index_contract_entry_sub_with_entrywise
        (M := M) (N := N) (T := T) (U := U)
        hH hBd hHd hM hN hMdiff hU hTdiff hδpos hdetM hdetN i j

/-- Finite inverse-principal contractions package as a matrix-valued explicit bounded parabolic
`C^{0,α}` estimate. -/
theorem matrix_inv_two_index_contract_with {n p q 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [Fintype p] [Fintype q] [NormedField 𝕜] {δ : ℝ}
    {B H : n → n → ℝ} {TB TH : n → n → p → q → ℝ}
    {M : ℝ × X → Matrix n n 𝕜} {T : ℝ × X → n → n → p → q → 𝕜}
    (hH : ∀ a b, 0 ≤ H a b)
    (hTB : ∀ a b i j, 0 ≤ TB a b i j) (hTH : ∀ a b i j, 0 ≤ TH a b i j)
    (hM : ∀ a b, ParabolicC0AlphaWith (B a b) (H a b) α (fun z => M z a b) s)
    (hT : ∀ a b i j, ParabolicC0AlphaWith (TB a b i j) (TH a b i j) α
      (fun z => T z a b i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaWith
      (∑ i : p, ∑ j : q, matrixInvTwoIndexContractEntryBoundConst (𝕜 := 𝕜) δ B TB i j)
      (∑ i : p, ∑ j : q,
        matrixInvTwoIndexContractEntryHolderConst (𝕜 := 𝕜) δ B H TB TH i j)
      α
      (fun z : ℝ × X =>
        (fun i j =>
          ∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * T z a b i j :
            Matrix p q 𝕜)) s := by
  refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
  · intro i
    exact Finset.sum_nonneg fun j _hj =>
      matrixInvTwoIndexContractEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos B hTB i j
  · intro i
    exact Finset.sum_nonneg fun j _hj =>
      matrixInvTwoIndexContractEntryHolderConst_nonneg (𝕜 := 𝕜) hH hδpos hTB hTH i j
  · intro i
    refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
    · intro j
      exact matrixInvTwoIndexContractEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos B hTB i j
    · intro j
      exact matrixInvTwoIndexContractEntryHolderConst_nonneg (𝕜 := 𝕜) hH hδpos hTB hTH i j
    · intro j
      exact matrix_inv_two_index_contract_entry_with (M := M) (T := T)
        hH hM hT hδpos hdet i j

/-- Finite inverse-matrix contractions against a four-index coefficient array are pointwise
Lipschitz on bounded coefficient arrays and entrywise bounded matrices with a common determinant
lower bound. -/
theorem matrix_inv_two_index_contract_entry_norm_sub_le {n p q 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ}
    {TB : n → n → p → q → ℝ} (M N : Matrix n n 𝕜)
    (T U : n → n → p → q → 𝕜)
    (hM : ∀ a b, ‖M a b‖ ≤ C a b) (hN : ∀ a b, ‖N a b‖ ≤ C a b)
    (hU : ∀ a b i j, ‖U a b i j‖ ≤ TB a b i j)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖)
    (i : p) (j : q) :
    ‖(∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) -
        ∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j‖ ≤
      ∑ a : n, ∑ b : n,
        (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * ‖T a b i j - U a b i j‖ +
          TB a b i j * matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N a b) := by
  classical
  let innerBound : n → ℝ := fun a =>
    ∑ b : n,
      (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * ‖T a b i j - U a b i j‖ +
        TB a b i j * matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N a b)
  have hinner : ∀ a : n,
      ‖(∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) -
          ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j‖ ≤ innerBound a := by
    intro a
    have hsum :
        ‖(∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) -
            ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j‖ ≤
          ∑ b : n,
            (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b *
                ‖T a b i j - U a b i j‖ +
              TB a b i j * ‖(M⁻¹ : Matrix n n 𝕜) a b -
                (N⁻¹ : Matrix n n 𝕜) a b‖) := by
      simpa using
        (norm_finset_sum_mul_sub_sum_mul_le
          (S := (Finset.univ : Finset n))
          (B := fun b => matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b)
          (D := fun b => TB a b i j)
          (a := fun b => (M⁻¹ : Matrix n n 𝕜) a b)
          (b := fun b => T a b i j)
          (c := fun b => (N⁻¹ : Matrix n n 𝕜) a b)
          (d := fun b => U a b i j)
          (fun b _hb => matrix_inv_entry_norm_le M hM hδpos hdetM a b)
          (fun b _hb => hU a b i j))
    refine hsum.trans ?_
    exact Finset.sum_le_sum fun b _hb => by
      have hTB_nonneg : 0 ≤ TB a b i j := (norm_nonneg _).trans (hU a b i j)
      have hlip :
          ‖(M⁻¹ : Matrix n n 𝕜) a b - (N⁻¹ : Matrix n n 𝕜) a b‖ ≤
            matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N a b :=
        matrix_inv_entry_norm_sub_le M N hM hN hδpos hdetM hdetN a b
      exact add_le_add_right (mul_le_mul_of_nonneg_left hlip hTB_nonneg)
        (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * ‖T a b i j - U a b i j‖)
  calc
    ‖(∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) -
        ∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j‖ =
        ‖∑ a : n,
          ((∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) -
            ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j)‖ := by
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ a : n,
        ‖(∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) -
          ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j‖ :=
      norm_sum_le _ _
    _ ≤ ∑ a : n, innerBound a :=
      Finset.sum_le_sum fun a _ha => hinner a
    _ =
      ∑ a : n, ∑ b : n,
        (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * ‖T a b i j - U a b i j‖ +
          TB a b i j * matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N a b) := by
      rfl

/-- Matrix-norm Lipschitz constant for varying the coefficient array in one entry of the
finite contraction `M⁻¹ᵃᵇ T_abij`, with the inverse matrix bounded by the determinant lower
bound and entrywise metric bounds. -/
def matrixInvTwoIndexContractCoeffDiffConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (C : n → n → ℝ) : ℝ :=
  ∑ a : n, ∑ b : n, matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b

/-- Matrix-norm Lipschitz constant for varying the metric in one entry of the finite contraction
`M⁻¹ᵃᵇ T_abij`, with the coefficient array bounded by `TB`. -/
def matrixInvTwoIndexContractMetricDiffConst {n p q 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] (δ : ℝ) (C : n → n → ℝ)
    (TB : n → n → p → q → ℝ) (i : p) (j : q) : ℝ :=
  ∑ a : n, ∑ b : n,
    TB a b i j * matrixInvEntryMatrixNormLipschitzConst (𝕜 := 𝕜) δ C a b

theorem matrixInvTwoIndexContractCoeffDiffConst_nonneg {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} (hδpos : 0 < δ) (C : n → n → ℝ) :
    0 ≤ matrixInvTwoIndexContractCoeffDiffConst (𝕜 := 𝕜) δ C := by
  exact Finset.sum_nonneg fun a _ha =>
    Finset.sum_nonneg fun b _hb =>
      matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos C a b

theorem matrixInvTwoIndexContractMetricDiffConst_nonneg {n p q 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} (hδpos : 0 < δ) {C : n → n → ℝ}
    {TB : n → n → p → q → ℝ} (hTB : ∀ a b i j, 0 ≤ TB a b i j) (i : p) (j : q) :
    0 ≤ matrixInvTwoIndexContractMetricDiffConst (𝕜 := 𝕜) δ C TB i j := by
  exact Finset.sum_nonneg fun a _ha =>
    Finset.sum_nonneg fun b _hb =>
      mul_nonneg (hTB a b i j)
        (matrixInvEntryMatrixNormLipschitzConst_nonneg (𝕜 := 𝕜) hδpos C a b)

/-- One entry of the finite inverse contraction is Lipschitz in the coefficient-array matrix norm
and the metric matrix norm, on bounded coefficient arrays and entrywise bounded matrices with a
common determinant lower bound. -/
theorem matrix_inv_two_index_contract_entry_norm_sub_le_const {n p q 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ}
    {TB : n → n → p → q → ℝ} (M N : Matrix n n 𝕜)
    (T U : n → n → p → q → 𝕜)
    (hM : ∀ a b, ‖M a b‖ ≤ C a b) (hN : ∀ a b, ‖N a b‖ ≤ C a b)
    (hU : ∀ a b i j, ‖U a b i j‖ ≤ TB a b i j)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖)
    (i : p) (j : q) :
    ‖(∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) -
        ∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j‖ ≤
      matrixInvTwoIndexContractCoeffDiffConst (𝕜 := 𝕜) δ C *
          ‖((fun a b => T a b i j) : Matrix n n 𝕜) -
            ((fun a b => U a b i j) : Matrix n n 𝕜)‖ +
        matrixInvTwoIndexContractMetricDiffConst (𝕜 := 𝕜) δ C TB i j * ‖M - N‖ := by
  classical
  let coeffDiffNorm : ℝ :=
    ‖((fun a b => T a b i j) : Matrix n n 𝕜) -
      ((fun a b => U a b i j) : Matrix n n 𝕜)‖
  let innerBound : n → ℝ := fun a =>
    ∑ b : n,
      (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * coeffDiffNorm +
        TB a b i j *
          (matrixInvEntryMatrixNormLipschitzConst (𝕜 := 𝕜) δ C a b * ‖M - N‖))
  have hinner : ∀ a : n,
      ‖(∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) -
          ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j‖ ≤ innerBound a := by
    intro a
    have hsum :
        ‖(∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) -
            ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j‖ ≤
          ∑ b : n,
            (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b *
                ‖T a b i j - U a b i j‖ +
              TB a b i j * ‖(M⁻¹ : Matrix n n 𝕜) a b -
                (N⁻¹ : Matrix n n 𝕜) a b‖) := by
      simpa using
        (norm_finset_sum_mul_sub_sum_mul_le
          (S := (Finset.univ : Finset n))
          (B := fun b => matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b)
          (D := fun b => TB a b i j)
          (a := fun b => (M⁻¹ : Matrix n n 𝕜) a b)
          (b := fun b => T a b i j)
          (c := fun b => (N⁻¹ : Matrix n n 𝕜) a b)
          (d := fun b => U a b i j)
          (fun b _hb => matrix_inv_entry_norm_le M hM hδpos hdetM a b)
          (fun b _hb => hU a b i j))
    refine hsum.trans ?_
    exact Finset.sum_le_sum fun b _hb => by
      have hTB_nonneg : 0 ≤ TB a b i j := (norm_nonneg _).trans (hU a b i j)
      have hcoeff_diff :
          ‖T a b i j - U a b i j‖ ≤ coeffDiffNorm := by
        change ‖T a b i j - U a b i j‖ ≤
          ‖(fun a b => T a b i j) - fun a b => U a b i j‖
        simpa only [Pi.sub_apply] using
          (norm_le_pi_norm
            (((fun a b => T a b i j) - fun a b => U a b i j) a) b).trans
            (norm_le_pi_norm ((fun a b => T a b i j) - fun a b => U a b i j) a)
      have hinv_diff :
          ‖(M⁻¹ : Matrix n n 𝕜) a b - (N⁻¹ : Matrix n n 𝕜) a b‖ ≤
            matrixInvEntryMatrixNormLipschitzConst (𝕜 := 𝕜) δ C a b * ‖M - N‖ :=
        matrix_inv_entry_norm_sub_le_const_mul M N hM hN hδpos hdetM hdetN a b
      exact add_le_add
        (mul_le_mul_of_nonneg_left hcoeff_diff
          (matrixInvEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos C a b))
        (mul_le_mul_of_nonneg_left hinv_diff hTB_nonneg)
  have hnorm :
      ‖(∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) -
          ∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j‖ ≤
        ∑ a : n, innerBound a := by
    calc
      ‖(∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) -
          ∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j‖ =
          ‖∑ a : n,
            ((∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) -
              ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j)‖ := by
        rw [Finset.sum_sub_distrib]
      _ ≤ ∑ a : n,
          ‖(∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) -
            ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j‖ :=
        norm_sum_le _ _
      _ ≤ ∑ a : n, innerBound a :=
        Finset.sum_le_sum fun a _ha => hinner a
  calc
    ‖(∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) -
        ∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j‖ ≤
        ∑ a : n, innerBound a := hnorm
    _ =
        (∑ a : n, ∑ b : n,
            matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * coeffDiffNorm) +
          (∑ a : n, ∑ b : n,
            TB a b i j *
              (matrixInvEntryMatrixNormLipschitzConst (𝕜 := 𝕜) δ C a b * ‖M - N‖)) := by
      simp [innerBound, Finset.sum_add_distrib]
    _ =
      matrixInvTwoIndexContractCoeffDiffConst (𝕜 := 𝕜) δ C * coeffDiffNorm +
        matrixInvTwoIndexContractMetricDiffConst (𝕜 := 𝕜) δ C TB i j * ‖M - N‖ := by
      have hcoeff :
          (∑ a : n, ∑ b : n,
              matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * coeffDiffNorm) =
            matrixInvTwoIndexContractCoeffDiffConst (𝕜 := 𝕜) δ C * coeffDiffNorm := by
        simp_rw [matrixInvTwoIndexContractCoeffDiffConst, Finset.sum_mul]
      have hmetric :
          (∑ a : n, ∑ b : n,
              TB a b i j *
                (matrixInvEntryMatrixNormLipschitzConst (𝕜 := 𝕜) δ C a b * ‖M - N‖)) =
            matrixInvTwoIndexContractMetricDiffConst (𝕜 := 𝕜) δ C TB i j * ‖M - N‖ := by
        calc
          (∑ a : n, ∑ b : n,
              TB a b i j *
                (matrixInvEntryMatrixNormLipschitzConst (𝕜 := 𝕜) δ C a b * ‖M - N‖)) =
              ∑ a : n, ∑ b : n,
                (TB a b i j *
                  matrixInvEntryMatrixNormLipschitzConst (𝕜 := 𝕜) δ C a b) * ‖M - N‖ := by
            refine Finset.sum_congr rfl fun a _ha =>
              Finset.sum_congr rfl fun b _hb => ?_
            ring
          _ =
            matrixInvTwoIndexContractMetricDiffConst (𝕜 := 𝕜) δ C TB i j * ‖M - N‖ := by
            simp_rw [matrixInvTwoIndexContractMetricDiffConst, Finset.sum_mul]
      rw [hcoeff, hmetric]
    _ =
      matrixInvTwoIndexContractCoeffDiffConst (𝕜 := 𝕜) δ C *
          ‖((fun a b => T a b i j) : Matrix n n 𝕜) -
            ((fun a b => U a b i j) : Matrix n n 𝕜)‖ +
        matrixInvTwoIndexContractMetricDiffConst (𝕜 := 𝕜) δ C TB i j * ‖M - N‖ := by
      rfl

/-- Matrix-valued finite inverse contractions against four-index coefficient arrays are
pointwise Lipschitz in the elementwise matrix norm. -/
theorem matrix_inv_two_index_contract_norm_sub_le {n p q 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [Fintype p] [Fintype q] [NormedField 𝕜] {δ : ℝ}
    {C : n → n → ℝ} {TB : n → n → p → q → ℝ} (M N : Matrix n n 𝕜)
    (T U : n → n → p → q → 𝕜)
    (hM : ∀ a b, ‖M a b‖ ≤ C a b) (hN : ∀ a b, ‖N a b‖ ≤ C a b)
    (hU : ∀ a b i j, ‖U a b i j‖ ≤ TB a b i j)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖) :
    ‖((fun i j =>
        ∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) :
        Matrix p q 𝕜) -
      ((fun i j =>
        ∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j) :
        Matrix p q 𝕜)‖ ≤
      ∑ i : p, ∑ j : q, ∑ a : n, ∑ b : n,
        (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * ‖T a b i j - U a b i j‖ +
          TB a b i j * matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N a b) := by
  classical
  let entryBound : p → q → ℝ := fun i j =>
    ∑ a : n, ∑ b : n,
      (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * ‖T a b i j - U a b i j‖ +
        TB a b i j * matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N a b)
  have hentry : ∀ i j,
      ‖(∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) -
          ∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j‖ ≤
        entryBound i j := by
    intro i j
    simpa [entryBound] using
      matrix_inv_two_index_contract_entry_norm_sub_le M N T U hM hN hU hδpos hdetM hdetN i j
  have hentry_nonneg : ∀ i j, 0 ≤ entryBound i j := by
    intro i j
    exact (norm_nonneg _).trans (hentry i j)
  have hrow_nonneg : ∀ i, 0 ≤ ∑ j : q, entryBound i j := by
    intro i
    exact Finset.sum_nonneg fun j _hj => hentry_nonneg i j
  have htotal_nonneg : 0 ≤ ∑ i : p, ∑ j : q, entryBound i j :=
    Finset.sum_nonneg fun i _hi => hrow_nonneg i
  have hnorm :
      ‖((fun i j =>
          ∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) :
          Matrix p q 𝕜) -
        ((fun i j =>
          ∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j) :
          Matrix p q 𝕜)‖ ≤
        ∑ i : p, ∑ j : q, entryBound i j := by
    refine (Matrix.norm_le_iff htotal_nonneg).2 ?_
    intro i j
    calc
      ‖(((fun i j =>
          ∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) :
          Matrix p q 𝕜) -
        ((fun i j =>
          ∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j) :
          Matrix p q 𝕜)) i j‖ =
          ‖(∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * T a b i j) -
            ∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * U a b i j‖ := rfl
      _ ≤ entryBound i j := hentry i j
      _ ≤ ∑ j : q, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hentry_nonneg i k) (Finset.mem_univ j)
      _ ≤ ∑ i : p, ∑ j : q, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hrow_nonneg k) (Finset.mem_univ i)
  simpa [entryBound] using hnorm

/-- Uniform matrix-valued bound for the finite inverse-principal contraction difference. -/
def matrixInvTwoIndexContractDiffBoundConst {n p q 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [Fintype p] [Fintype q] [NormedField 𝕜]
    (δ : ℝ) (C : n → n → ℝ) (TB : n → n → p → q → ℝ)
    (ηM : ℝ) (ηT : p → q → ℝ) : ℝ :=
  ∑ i : p, ∑ j : q,
    (matrixInvTwoIndexContractCoeffDiffConst (𝕜 := 𝕜) δ C * ηT i j +
      matrixInvTwoIndexContractMetricDiffConst (𝕜 := 𝕜) δ C TB i j * ηM)

theorem matrixInvTwoIndexContractDiffBoundConst_nonneg {n p q 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [Fintype p] [Fintype q] [NormedField 𝕜]
    {δ : ℝ} (hδpos : 0 < δ) {C : n → n → ℝ}
    {TB : n → n → p → q → ℝ} (hTB : ∀ a b i j, 0 ≤ TB a b i j)
    {ηM : ℝ} (hηM : 0 ≤ ηM) {ηT : p → q → ℝ}
    (hηT : ∀ i j, 0 ≤ ηT i j) :
    0 ≤ matrixInvTwoIndexContractDiffBoundConst (𝕜 := 𝕜) δ C TB ηM ηT := by
  exact Finset.sum_nonneg fun i _hi =>
    Finset.sum_nonneg fun j _hj =>
      add_nonneg
        (mul_nonneg
          (matrixInvTwoIndexContractCoeffDiffConst_nonneg (𝕜 := 𝕜) hδpos C)
          (hηT i j))
        (mul_nonneg
          (matrixInvTwoIndexContractMetricDiffConst_nonneg (𝕜 := 𝕜) hδpos hTB i j)
          hηM)

/-- Matrix-valued finite inverse-principal contractions are bounded-difference controlled on a
time-space set by uniform metric and coefficient-array difference bounds. -/
theorem matrix_inv_two_index_contract_bounded_sub_le_const {n p q 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [Fintype p] [Fintype q] [NormedField 𝕜]
    {δ : ℝ} {C : n → n → ℝ} {TB : n → n → p → q → ℝ}
    {ηM : ℝ} {ηT : p → q → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {T U : ℝ × X → n → n → p → q → 𝕜}
    (hTB : ∀ a b i j, 0 ≤ TB a b i j)
    (hM : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b, ‖M z a b‖ ≤ C a b)
    (hN : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b, ‖N z a b‖ ≤ C a b)
    (hU : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b i j, ‖U z a b i j‖ ≤ TB a b i j)
    (hMdiff : ∀ ⦃z : ℝ × X⦄, z ∈ s → ‖M z - N z‖ ≤ ηM)
    (hTdiff : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ i j,
      ‖((fun a b => T z a b i j) : Matrix n n 𝕜) -
        ((fun a b => U z a b i j) : Matrix n n 𝕜)‖ ≤ ηT i j)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicBoundedWith
      (matrixInvTwoIndexContractDiffBoundConst (𝕜 := 𝕜) δ C TB ηM ηT)
      (fun z : ℝ × X =>
        ((fun i j => ∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b *
          T z a b i j) : Matrix p q 𝕜) -
        ((fun i j => ∑ a : n, ∑ b : n, ((N z)⁻¹ : Matrix n n 𝕜) a b *
          U z a b i j) : Matrix p q 𝕜)) s := by
  classical
  intro z hz
  let entryBound : p → q → ℝ := fun i j =>
    matrixInvTwoIndexContractCoeffDiffConst (𝕜 := 𝕜) δ C * ηT i j +
      matrixInvTwoIndexContractMetricDiffConst (𝕜 := 𝕜) δ C TB i j * ηM
  have hentry : ∀ i j,
      ‖(∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * T z a b i j) -
        ∑ a : n, ∑ b : n, ((N z)⁻¹ : Matrix n n 𝕜) a b * U z a b i j‖ ≤
        entryBound i j := by
    intro i j
    have hbase :=
      matrix_inv_two_index_contract_entry_norm_sub_le_const
        (δ := δ) (C := C) (TB := TB)
        (M z) (N z) (T z) (U z) (hM hz) (hN hz) (hU hz) hδpos
        (hdetM hz) (hdetN hz) i j
    exact hbase.trans
      (add_le_add
        (mul_le_mul_of_nonneg_left (hTdiff hz i j)
          (matrixInvTwoIndexContractCoeffDiffConst_nonneg (𝕜 := 𝕜) hδpos C))
        (mul_le_mul_of_nonneg_left (hMdiff hz)
          (matrixInvTwoIndexContractMetricDiffConst_nonneg (𝕜 := 𝕜) hδpos hTB i j)))
  have hentry_nonneg : ∀ i j, 0 ≤ entryBound i j := by
    intro i j
    exact (norm_nonneg _).trans (hentry i j)
  have hrow_nonneg : ∀ i, 0 ≤ ∑ j : q, entryBound i j := by
    intro i
    exact Finset.sum_nonneg fun j _hj => hentry_nonneg i j
  have htotal_nonneg : 0 ≤ ∑ i : p, ∑ j : q, entryBound i j :=
    Finset.sum_nonneg fun i _hi => hrow_nonneg i
  have hnorm :
      ‖((fun i j => ∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b *
            T z a b i j) : Matrix p q 𝕜) -
          ((fun i j => ∑ a : n, ∑ b : n, ((N z)⁻¹ : Matrix n n 𝕜) a b *
            U z a b i j) : Matrix p q 𝕜)‖ ≤
        ∑ i : p, ∑ j : q, entryBound i j := by
    refine (Matrix.norm_le_iff htotal_nonneg).2 ?_
    intro i j
    calc
      ‖(((fun i j => ∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b *
            T z a b i j) : Matrix p q 𝕜) -
          ((fun i j => ∑ a : n, ∑ b : n, ((N z)⁻¹ : Matrix n n 𝕜) a b *
            U z a b i j) : Matrix p q 𝕜)) i j‖ =
          ‖(∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * T z a b i j) -
            ∑ a : n, ∑ b : n, ((N z)⁻¹ : Matrix n n 𝕜) a b * U z a b i j‖ := rfl
      _ ≤ entryBound i j := hentry i j
      _ ≤ ∑ j : q, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hentry_nonneg i k) (Finset.mem_univ j)
      _ ≤ ∑ i : p, ∑ j : q, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hrow_nonneg k) (Finset.mem_univ i)
  simpa [entryBound, matrixInvTwoIndexContractDiffBoundConst] using hnorm

/-- Compact-domain version of `matrix_inv_two_index_contract_bounded_sub_le_const`: pointwise
nonvanishing of both metric determinants supplies one common determinant lower bound. -/
theorem matrix_inv_two_index_contract_bounded_sub_le_const_of_isCompact_det_ne_zero
    {n p q 𝕜 : Type*} [Fintype n] [DecidableEq n] [Fintype p] [Fintype q]
    [NormedField 𝕜] {K : Set (ℝ × X)} {C : n → n → ℝ}
    {TB : n → n → p → q → ℝ} {ηM : ℝ} {ηT : p → q → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {T U : ℝ × X → n → n → p → q → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hMctrl : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) K)
    (hNctrl : ∀ i j, ParabolicC0AlphaOn α (fun z => N z i j) K)
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (N z).det ≠ 0)
    (hTB : ∀ a b i j, 0 ≤ TB a b i j)
    (hM : ∀ ⦃z : ℝ × X⦄, z ∈ K → ∀ a b, ‖M z a b‖ ≤ C a b)
    (hN : ∀ ⦃z : ℝ × X⦄, z ∈ K → ∀ a b, ‖N z a b‖ ≤ C a b)
    (hU : ∀ ⦃z : ℝ × X⦄, z ∈ K → ∀ a b i j, ‖U z a b i j‖ ≤ TB a b i j)
    (hMdiff : ∀ ⦃z : ℝ × X⦄, z ∈ K → ‖M z - N z‖ ≤ ηM)
    (hTdiff : ∀ ⦃z : ℝ × X⦄, z ∈ K → ∀ i j,
      ‖((fun a b => T z a b i j) : Matrix n n 𝕜) -
        ((fun a b => U z a b i j) : Matrix n n 𝕜)‖ ≤ ηT i j) :
    ∃ δ > 0,
      ParabolicBoundedWith
        (matrixInvTwoIndexContractDiffBoundConst (𝕜 := 𝕜) δ C TB ηM ηT)
        (fun z : ℝ × X =>
          ((fun i j => ∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b *
            T z a b i j) : Matrix p q 𝕜) -
          ((fun i j => ∑ a : n, ∑ b : n, ((N z)⁻¹ : Matrix n n 𝕜) a b *
            U z a b i j) : Matrix p q 𝕜)) K := by
  rcases matrix_det_pair_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) (N := N) hK hα hMctrl hNctrl hdetM_ne hdetN_ne with
    ⟨δ, hδpos, hdetM, hdetN⟩
  refine ⟨δ, hδpos, ?_⟩
  exact matrix_inv_two_index_contract_bounded_sub_le_const
    (s := K) (δ := δ) (C := C) (TB := TB) (ηM := ηM) (ηT := ηT)
    hTB hM hN hU hMdiff hTdiff hδpos hdetM hdetN

/-- Holder constant for the difference of two finite inverse-principal contractions, using the
sum of the two individual contraction Holder constants. -/
def matrixInvTwoIndexContractDiffHolderConst {n p q 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [Fintype p] [Fintype q] [NormedField 𝕜]
    (δ : ℝ) (B H : n → n → ℝ) (TB TH : n → n → p → q → ℝ) : ℝ :=
  (∑ i : p, ∑ j : q,
    matrixInvTwoIndexContractEntryHolderConst (𝕜 := 𝕜) δ B H TB TH i j) +
  (∑ i : p, ∑ j : q,
    matrixInvTwoIndexContractEntryHolderConst (𝕜 := 𝕜) δ B H TB TH i j)

theorem matrixInvTwoIndexContractDiffHolderConst_nonneg {n p q 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [Fintype p] [Fintype q] [NormedField 𝕜]
    {δ : ℝ} {B H : n → n → ℝ} {TB TH : n → n → p → q → ℝ}
    (hH : ∀ a b, 0 ≤ H a b) (hδpos : 0 < δ)
    (hTB : ∀ a b i j, 0 ≤ TB a b i j) (hTH : ∀ a b i j, 0 ≤ TH a b i j) :
    0 ≤ matrixInvTwoIndexContractDiffHolderConst (𝕜 := 𝕜) δ B H TB TH := by
  exact add_nonneg
    (Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj =>
        matrixInvTwoIndexContractEntryHolderConst_nonneg
          (𝕜 := 𝕜) hH hδpos hTB hTH i j)
    (Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj =>
        matrixInvTwoIndexContractEntryHolderConst_nonneg
          (𝕜 := 𝕜) hH hδpos hTB hTH i j)

/-- The difference of two finite inverse-principal contractions has parabolic `C^{0,α}` control:
the sup constant is the existing primitive-input bounded-difference constant, while the Holder
constant is the sum of the two standalone inverse-principal Holder constants. -/
theorem matrix_inv_two_index_contract_sub_with {n p q 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [Fintype p] [Fintype q] [NormedField 𝕜]
    {δ : ℝ} {B H : n → n → ℝ} {TB TH : n → n → p → q → ℝ}
    {ηM : ℝ} {ηT : p → q → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {T U : ℝ × X → n → n → p → q → 𝕜}
    (hH : ∀ a b, 0 ≤ H a b)
    (hTB : ∀ a b i j, 0 ≤ TB a b i j) (hTH : ∀ a b i j, 0 ≤ TH a b i j)
    (hM : ∀ a b, ParabolicC0AlphaWith (B a b) (H a b) α (fun z => M z a b) s)
    (hN : ∀ a b, ParabolicC0AlphaWith (B a b) (H a b) α (fun z => N z a b) s)
    (hT : ∀ a b i j, ParabolicC0AlphaWith (TB a b i j) (TH a b i j) α
      (fun z => T z a b i j) s)
    (hU : ∀ a b i j, ParabolicC0AlphaWith (TB a b i j) (TH a b i j) α
      (fun z => U z a b i j) s)
    (hMdiff : ∀ ⦃z : ℝ × X⦄, z ∈ s → ‖M z - N z‖ ≤ ηM)
    (hTdiff : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ i j,
      ‖((fun a b => T z a b i j) : Matrix n n 𝕜) -
        ((fun a b => U z a b i j) : Matrix n n 𝕜)‖ ≤ ηT i j)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicC0AlphaWith
      (matrixInvTwoIndexContractDiffBoundConst (𝕜 := 𝕜) δ B TB ηM ηT)
      (matrixInvTwoIndexContractDiffHolderConst (𝕜 := 𝕜) δ B H TB TH)
      α
      (fun z : ℝ × X =>
        ((fun i j => ∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b *
          T z a b i j) : Matrix p q 𝕜) -
        ((fun i j => ∑ a : n, ∑ b : n, ((N z)⁻¹ : Matrix n n 𝕜) a b *
          U z a b i j) : Matrix p q 𝕜)) s := by
  have hbounded :
      ParabolicBoundedWith
        (matrixInvTwoIndexContractDiffBoundConst (𝕜 := 𝕜) δ B TB ηM ηT)
        (fun z : ℝ × X =>
          ((fun i j => ∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b *
            T z a b i j) : Matrix p q 𝕜) -
          ((fun i j => ∑ a : n, ∑ b : n, ((N z)⁻¹ : Matrix n n 𝕜) a b *
            U z a b i j) : Matrix p q 𝕜)) s := by
    exact matrix_inv_two_index_contract_bounded_sub_le_const
      (s := s) (δ := δ) (C := B) (TB := TB) (ηM := ηM) (ηT := ηT)
      hTB
      (fun hz hzs a b => (hM a b).bounded hzs)
      (fun hz hzs a b => (hN a b).bounded hzs)
      (fun hz hzs a b i j => (hU a b i j).bounded hzs)
      hMdiff hTdiff hδpos hdetM hdetN
  have hMT := matrix_inv_two_index_contract_with
    (M := M) (T := T) hH hTB hTH hM hT hδpos hdetM
  have hNU := matrix_inv_two_index_contract_with
    (M := N) (T := U) hH hTB hTH hN hU hδpos hdetN
  exact ⟨hbounded, by
    simpa [matrixInvTwoIndexContractDiffHolderConst] using hMT.holder.sub hNU.holder⟩

end ParabolicC0AlphaOn

namespace ParabolicC0AlphaNormLe

variable {X : Type*} [PseudoMetricSpace X]
variable {α : ℝ} {s : Set (ℝ × X)}

/-- Entrywise metric control, coefficient-array control, and a determinant lower bound package
finite inverse-principal contractions with the corresponding single-radius `C^{0,α}` bound. -/
theorem matrix_inv_two_index_contract_of_entries {n p q 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [Fintype p] [Fintype q] [NormedField 𝕜]
    {R : n → n → ℝ} {RT : n → n → p → q → ℝ} {δ : ℝ}
    {M : ℝ × X → Matrix n n 𝕜} {T : ℝ × X → n → n → p → q → 𝕜}
    (hM : ∀ a b, ParabolicC0AlphaNormLe (R a b) α (fun z => M z a b) s)
    (hT : ∀ a b i j,
      ParabolicC0AlphaNormLe (RT a b i j) α (fun z => T z a b i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaNormLe
      ((∑ i : p, ∑ j : q,
          ParabolicC0AlphaOn.matrixInvTwoIndexContractEntryBoundConst
            (𝕜 := 𝕜) δ R RT i j) +
        (∑ i : p, ∑ j : q,
          ParabolicC0AlphaOn.matrixInvTwoIndexContractEntryHolderConst
            (𝕜 := 𝕜) δ R R RT RT i j))
      α
      (fun z : ℝ × X =>
        (fun i j =>
          ∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * T z a b i j :
            Matrix p q 𝕜)) s := by
  have hR : ∀ a b, 0 ≤ R a b := fun a b => (hM a b).nonneg
  have hRT : ∀ a b i j, 0 ≤ RT a b i j := fun a b i j => (hT a b i j).nonneg
  exact ParabolicC0AlphaNormLe.of_c0AlphaWith
    (Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj =>
        ParabolicC0AlphaOn.matrixInvTwoIndexContractEntryBoundConst_nonneg
          (𝕜 := 𝕜) hδpos R hRT i j)
    (Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj =>
        ParabolicC0AlphaOn.matrixInvTwoIndexContractEntryHolderConst_nonneg
          (𝕜 := 𝕜) hR hδpos hRT hRT i j)
    (ParabolicC0AlphaOn.matrix_inv_two_index_contract_with
      (M := M) (T := T) (B := R) (H := R) (TB := RT) (TH := RT)
      hR hRT hRT
      (fun a b => ParabolicC0AlphaNormLe.c0AlphaWith_self (hM a b))
      (fun a b i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hT a b i j))
      hδpos hdet)

/-- Entrywise metric controls, coefficient-array controls, their differences, and a common
determinant lower bound package finite inverse-principal contraction differences with the
corresponding single-radius `C^{0,α}` bound. -/
theorem matrix_inv_two_index_contract_sub_entrywise_of_entries {n p q 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [Fintype p] [Fintype q] [NormedField 𝕜]
    {R Rd : n → n → ℝ} {RT RTd : n → n → p → q → ℝ} {δ : ℝ}
    {M N : ℝ × X → Matrix n n 𝕜} {T U : ℝ × X → n → n → p → q → 𝕜}
    (hM : ∀ a b, ParabolicC0AlphaNormLe (R a b) α (fun z => M z a b) s)
    (hN : ∀ a b, ParabolicC0AlphaNormLe (R a b) α (fun z => N z a b) s)
    (hMdiff : ∀ a b, ParabolicC0AlphaNormLe (Rd a b) α
      (fun z => M z a b - N z a b) s)
    (hU : ∀ a b i j,
      ParabolicC0AlphaNormLe (RT a b i j) α (fun z => U z a b i j) s)
    (hTdiff : ∀ a b i j, ParabolicC0AlphaNormLe (RTd a b i j) α
      (fun z => T z a b i j - U z a b i j) s)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicC0AlphaNormLe
      (ParabolicC0AlphaOn.matrixInvTwoIndexContractEntrywiseSubBoundConst
          (𝕜 := 𝕜) δ R Rd RT RTd +
        ParabolicC0AlphaOn.matrixInvTwoIndexContractEntrywiseSubHolderConst
          (𝕜 := 𝕜) δ R R Rd Rd RT RT RTd RTd)
      α
      (fun z : ℝ × X =>
        ((fun i j => ∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b *
          T z a b i j) : Matrix p q 𝕜) -
        ((fun i j => ∑ a : n, ∑ b : n, ((N z)⁻¹ : Matrix n n 𝕜) a b *
          U z a b i j) : Matrix p q 𝕜)) s := by
  have hR : ∀ a b, 0 ≤ R a b := fun a b => (hM a b).nonneg
  have hRd : ∀ a b, 0 ≤ Rd a b := fun a b => (hMdiff a b).nonneg
  have hRT : ∀ a b i j, 0 ≤ RT a b i j := fun a b i j => (hU a b i j).nonneg
  have hRTd : ∀ a b i j, 0 ≤ RTd a b i j := fun a b i j => (hTdiff a b i j).nonneg
  exact ParabolicC0AlphaNormLe.of_c0AlphaWith
    (ParabolicC0AlphaOn.matrixInvTwoIndexContractEntrywiseSubBoundConst_nonneg
      (𝕜 := 𝕜) hδpos hRd hRT hRTd)
    (ParabolicC0AlphaOn.matrixInvTwoIndexContractEntrywiseSubHolderConst_nonneg
      (𝕜 := 𝕜) hδpos hR hRd hRd hRT hRT hRTd hRTd)
    (ParabolicC0AlphaOn.matrix_inv_two_index_contract_sub_with_entrywise
      (M := M) (N := N) (T := T) (U := U)
      (B := R) (H := R) (Bd := Rd) (Hd := Rd)
      (TB := RT) (TH := RT) (TDB := RTd) (TDH := RTd)
      hR hRd hRd hRT hRT hRTd hRTd
      (fun a b => ParabolicC0AlphaNormLe.c0AlphaWith_self (hM a b))
      (fun a b => ParabolicC0AlphaNormLe.c0AlphaWith_self (hN a b))
      (fun a b => ParabolicC0AlphaNormLe.c0AlphaWith_self (hMdiff a b))
      (fun a b i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hU a b i j))
      (fun a b i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hTdiff a b i j))
      hδpos hdetM hdetN)

end ParabolicC0AlphaNormLe

namespace ParabolicC0AlphaOn

variable {X : Type*} [PseudoMetricSpace X]
variable {α : ℝ} {s : Set (ℝ × X)}

/-- Compact-domain version of `matrix_inv_two_index_contract_sub_with`: pointwise nonvanishing of
both metric determinants supplies one common determinant lower bound. -/
theorem matrix_inv_two_index_contract_sub_with_of_isCompact_det_ne_zero
    {n p q 𝕜 : Type*} [Fintype n] [DecidableEq n] [Fintype p] [Fintype q]
    [NormedField 𝕜] {K : Set (ℝ × X)}
    {B H : n → n → ℝ} {TB TH : n → n → p → q → ℝ}
    {ηM : ℝ} {ηT : p → q → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {T U : ℝ × X → n → n → p → q → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hB : ∀ a b, 0 ≤ B a b) (hH : ∀ a b, 0 ≤ H a b)
    (hTB : ∀ a b i j, 0 ≤ TB a b i j) (hTH : ∀ a b i j, 0 ≤ TH a b i j)
    (hM : ∀ a b, ParabolicC0AlphaWith (B a b) (H a b) α (fun z => M z a b) K)
    (hN : ∀ a b, ParabolicC0AlphaWith (B a b) (H a b) α (fun z => N z a b) K)
    (hT : ∀ a b i j, ParabolicC0AlphaWith (TB a b i j) (TH a b i j) α
      (fun z => T z a b i j) K)
    (hU : ∀ a b i j, ParabolicC0AlphaWith (TB a b i j) (TH a b i j) α
      (fun z => U z a b i j) K)
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (N z).det ≠ 0)
    (hMdiff : ∀ ⦃z : ℝ × X⦄, z ∈ K → ‖M z - N z‖ ≤ ηM)
    (hTdiff : ∀ ⦃z : ℝ × X⦄, z ∈ K → ∀ i j,
      ‖((fun a b => T z a b i j) : Matrix n n 𝕜) -
        ((fun a b => U z a b i j) : Matrix n n 𝕜)‖ ≤ ηT i j) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvTwoIndexContractDiffBoundConst (𝕜 := 𝕜) δ B TB ηM ηT)
        (matrixInvTwoIndexContractDiffHolderConst (𝕜 := 𝕜) δ B H TB TH)
        α
        (fun z : ℝ × X =>
          ((fun i j => ∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b *
            T z a b i j) : Matrix p q 𝕜) -
          ((fun i j => ∑ a : n, ∑ b : n, ((N z)⁻¹ : Matrix n n 𝕜) a b *
            U z a b i j) : Matrix p q 𝕜)) K := by
  have hMctrl : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) K := by
    intro a b
    exact ⟨B a b, hB a b, H a b, hH a b, hM a b⟩
  have hNctrl : ∀ a b, ParabolicC0AlphaOn α (fun z => N z a b) K := by
    intro a b
    exact ⟨B a b, hB a b, H a b, hH a b, hN a b⟩
  rcases matrix_det_pair_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) (N := N) hK hα hMctrl hNctrl hdetM_ne hdetN_ne with
    ⟨δ, hδpos, hdetM, hdetN⟩
  exact ⟨δ, hδpos, matrix_inv_two_index_contract_sub_with
    (M := M) (N := N) (T := T) (U := U)
    hH hTB hTH hM hN hT hU hMdiff hTdiff hδpos hdetM hdetN⟩

/-- Compact-domain version of `matrix_inv_two_index_contract_sub_with_entrywise`: pointwise
nonvanishing of both metric determinants supplies one common determinant lower bound. -/
theorem matrix_inv_two_index_contract_sub_with_entrywise_of_isCompact_det_ne_zero
    {n p q 𝕜 : Type*} [Fintype n] [DecidableEq n] [Fintype p] [Fintype q]
    [NormedField 𝕜] {K : Set (ℝ × X)}
    {B H Bd Hd : n → n → ℝ} {TB TH TDB TDH : n → n → p → q → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {T U : ℝ × X → n → n → p → q → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hB : ∀ a b, 0 ≤ B a b) (hH : ∀ a b, 0 ≤ H a b)
    (hBd : ∀ a b, 0 ≤ Bd a b) (hHd : ∀ a b, 0 ≤ Hd a b)
    (hTB : ∀ a b i j, 0 ≤ TB a b i j) (hTH : ∀ a b i j, 0 ≤ TH a b i j)
    (hTDB : ∀ a b i j, 0 ≤ TDB a b i j)
    (hTDH : ∀ a b i j, 0 ≤ TDH a b i j)
    (hM : ∀ a b, ParabolicC0AlphaWith (B a b) (H a b) α (fun z => M z a b) K)
    (hN : ∀ a b, ParabolicC0AlphaWith (B a b) (H a b) α (fun z => N z a b) K)
    (hMdiff : ∀ a b,
      ParabolicC0AlphaWith (Bd a b) (Hd a b) α (fun z => M z a b - N z a b) K)
    (hU : ∀ a b i j, ParabolicC0AlphaWith (TB a b i j) (TH a b i j) α
      (fun z => U z a b i j) K)
    (hTdiff : ∀ a b i j,
      ParabolicC0AlphaWith (TDB a b i j) (TDH a b i j) α
        (fun z => T z a b i j - U z a b i j) K)
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (N z).det ≠ 0) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (matrixInvTwoIndexContractEntrywiseSubBoundConst (𝕜 := 𝕜) δ B Bd TB TDB)
        (matrixInvTwoIndexContractEntrywiseSubHolderConst
          (𝕜 := 𝕜) δ B H Bd Hd TB TH TDB TDH)
        α
        (fun z : ℝ × X =>
          ((fun i j => ∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b *
            T z a b i j) : Matrix p q 𝕜) -
          ((fun i j => ∑ a : n, ∑ b : n, ((N z)⁻¹ : Matrix n n 𝕜) a b *
            U z a b i j) : Matrix p q 𝕜)) K := by
  have hMctrl : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) K := by
    intro a b
    exact ⟨B a b, hB a b, H a b, hH a b, hM a b⟩
  have hNctrl : ∀ a b, ParabolicC0AlphaOn α (fun z => N z a b) K := by
    intro a b
    exact ⟨B a b, hB a b, H a b, hH a b, hN a b⟩
  rcases matrix_det_pair_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) (N := N) hK hα hMctrl hNctrl hdetM_ne hdetN_ne with
    ⟨δ, hδpos, hdetM, hdetN⟩
  exact ⟨δ, hδpos, matrix_inv_two_index_contract_sub_with_entrywise
    (M := M) (N := N) (T := T) (U := U)
    hH hBd hHd hTB hTH hTDB hTDH hM hN hMdiff hU hTdiff
    hδpos hdetM hdetN⟩

/-- One entry of a finite inverse-principal contraction difference has existential parabolic
`C^{0,α}` control from entrywise metric and coefficient-array difference controls. -/
theorem matrix_inv_two_index_contract_entry_sub_entrywise {n p q 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] {δ : ℝ}
    {M N : ℝ × X → Matrix n n 𝕜} {T U : ℝ × X → n → n → p → q → 𝕜}
    (hM : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) s)
    (hN : ∀ a b, ParabolicC0AlphaOn α (fun z => N z a b) s)
    (hMdiff : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b - N z a b) s)
    (hU : ∀ a b i j, ParabolicC0AlphaOn α (fun z => U z a b i j) s)
    (hTdiff : ∀ a b i j,
      ParabolicC0AlphaOn α (fun z => T z a b i j - U z a b i j) s)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖)
    (i : p) (j : q) :
    ParabolicC0AlphaOn α
      (fun z =>
        (∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * T z a b i j) -
          ∑ a : n, ∑ b : n, ((N z)⁻¹ : Matrix n n 𝕜) a b * U z a b i j) s := by
  classical
  let invM : n → n → ℝ × X → 𝕜 :=
    fun a b z => ((M z)⁻¹ : Matrix n n 𝕜) a b
  let invN : n → n → ℝ × X → 𝕜 :=
    fun a b z => ((N z)⁻¹ : Matrix n n 𝕜) a b
  let coeffT : n → n → ℝ × X → 𝕜 := fun a b z => T z a b i j
  let coeffU : n → n → ℝ × X → 𝕜 := fun a b z => U z a b i j
  have hinner : ∀ a ∈ (Finset.univ : Finset n),
      ParabolicC0AlphaOn α
        (fun z =>
          (∑ b : n, invM a b z * coeffT a b z) -
            ∑ b : n, invN a b z * coeffU a b z) s := by
    intro a _ha
    simpa using
      (ParabolicC0AlphaOn.finset_sum_mul_sub_sum_mul (X := X) (α := α) (s := s)
        (S := (Finset.univ : Finset n))
        (u := fun b z => invM a b z) (u' := fun b z => invN a b z)
        (v := fun b z => coeffT a b z) (v' := fun b z => coeffU a b z)
        (fun b _hb => by
          simpa [invM] using matrix_inv_entry (M := M) hM hδpos hdetM a b)
        (fun b _hb => by
          simpa [coeffU] using hU a b i j)
        (fun b _hb => by
          simpa [invM, invN] using
            matrix_inv_entry_sub (M := M) (N := N)
              hM hN hMdiff hδpos hdetM hdetN a b)
        (fun b _hb => by
          simpa [coeffT, coeffU] using hTdiff a b i j))
  have hsum := ParabolicC0AlphaOn.sum (X := X) (α := α) (s := s)
    (S := (Finset.univ : Finset n))
    (u := fun a z =>
      (∑ b : n, invM a b z * coeffT a b z) -
        ∑ b : n, invN a b z * coeffU a b z)
    hinner
  convert hsum using 1
  · ext z
    simp [invM, invN, coeffT, coeffU, Finset.sum_sub_distrib]

/-- Finite inverse-principal contraction differences preserve existential parabolic `C^{0,α}`
control from entrywise metric and coefficient-array difference controls. -/
theorem matrix_inv_two_index_contract_sub_entrywise {n p q 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [Fintype p] [Fintype q] [NormedField 𝕜]
    {δ : ℝ} {M N : ℝ × X → Matrix n n 𝕜}
    {T U : ℝ × X → n → n → p → q → 𝕜}
    (hM : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) s)
    (hN : ∀ a b, ParabolicC0AlphaOn α (fun z => N z a b) s)
    (hMdiff : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b - N z a b) s)
    (hU : ∀ a b i j, ParabolicC0AlphaOn α (fun z => U z a b i j) s)
    (hTdiff : ∀ a b i j,
      ParabolicC0AlphaOn α (fun z => T z a b i j - U z a b i j) s)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × X =>
        ((fun i j => ∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b *
          T z a b i j) : Matrix p q 𝕜) -
        ((fun i j => ∑ a : n, ∑ b : n, ((N z)⁻¹ : Matrix n n 𝕜) a b *
          U z a b i j) : Matrix p q 𝕜)) s :=
  matrix_of_entries fun i j =>
    matrix_inv_two_index_contract_entry_sub_entrywise (M := M) (N := N) (T := T) (U := U)
      hM hN hMdiff hU hTdiff hδpos hdetM hdetN i j

/-- Compact-domain finite inverse-principal contraction differences preserve existential
parabolic `C^{0,α}` control from entrywise controls and pointwise nonvanishing determinants. -/
theorem matrix_inv_two_index_contract_sub_entrywise_of_isCompact_det_ne_zero
    {n p q 𝕜 : Type*} [Fintype n] [DecidableEq n] [Fintype p] [Fintype q]
    [NormedField 𝕜] {K : Set (ℝ × X)}
    {M N : ℝ × X → Matrix n n 𝕜}
    {T U : ℝ × X → n → n → p → q → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hM : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) K)
    (hN : ∀ a b, ParabolicC0AlphaOn α (fun z => N z a b) K)
    (hMdiff : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b - N z a b) K)
    (hU : ∀ a b i j, ParabolicC0AlphaOn α (fun z => U z a b i j) K)
    (hTdiff : ∀ a b i j,
      ParabolicC0AlphaOn α (fun z => T z a b i j - U z a b i j) K)
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (N z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ParabolicC0AlphaOn α
        (fun z : ℝ × X =>
          ((fun i j => ∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b *
            T z a b i j) : Matrix p q 𝕜) -
          ((fun i j => ∑ a : n, ∑ b : n, ((N z)⁻¹ : Matrix n n 𝕜) a b *
            U z a b i j) : Matrix p q 𝕜)) K := by
  rcases matrix_det_pair_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) (N := N) hK hα hM hN hdetM_ne hdetN_ne with
    ⟨δ, hδpos, hdetM, hdetN⟩
  exact ⟨δ, hδpos, matrix_inv_two_index_contract_sub_entrywise
    (M := M) (N := N) (T := T) (U := U)
    hM hN hMdiff hU hTdiff hδpos hdetM hdetN⟩

/-- Compact-domain matrix-valued inverse principal-contraction closure from entrywise control and
pointwise nonvanishing determinant. -/
theorem matrix_inv_two_index_contract_of_isCompact_det_ne_zero {n p q 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [Fintype p] [Fintype q] [NormedField 𝕜]
    {K : Set (ℝ × X)} {M : ℝ × X → Matrix n n 𝕜}
    {T : ℝ × X → n → n → p → q → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hM : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) K)
    (hT : ∀ a b i j, ParabolicC0AlphaOn α (fun z => T z a b i j) K)
    (hdet_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × X =>
        (fun i j =>
          ∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * T z a b i j :
            Matrix p q 𝕜)) K := by
  rcases matrix_det_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hM hdet_ne with
    ⟨δ, hδpos, hdet⟩
  exact matrix_inv_two_index_contract (M := M) (T := T) hM hT hδpos hdet

/-- Compact-domain finite-family inverse principal-contraction closure from entrywise controls
and pointwise nonvanishing determinants, with one determinant lower bound shared by the family. -/
theorem matrix_inv_two_index_contract_family_of_isCompact_det_ne_zero
    {ι n p q 𝕜 : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
    [Fintype p] [Fintype q] [NormedField 𝕜]
    {K : Set (ℝ × X)}
    {M : ι → ℝ × X → Matrix n n 𝕜}
    {T : ι → ℝ × X → n → n → p → q → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hM : ∀ r a b, ParabolicC0AlphaOn α (fun z => M r z a b) K)
    (hT : ∀ r a b i j, ParabolicC0AlphaOn α (fun z => T r z a b i j) K)
    (hdet_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (M r z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M r z).det‖) ∧
      ∀ r,
        ParabolicC0AlphaOn α
          (fun z : ℝ × X =>
            (fun i j =>
              ∑ a : n, ∑ b : n, ((M r z)⁻¹ : Matrix n n 𝕜) a b *
                T r z a b i j :
              Matrix p q 𝕜)) K := by
  rcases matrix_det_family_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hM hdet_ne with
    ⟨δ, hδpos, hdet⟩
  refine ⟨δ, hδpos, hdet, ?_⟩
  intro r
  exact matrix_inv_two_index_contract
    (M := M r) (T := T r) (hM r) (hT r) hδpos (hdet r)

/-- A finite family of inverse-principal contractions has explicit matrix-valued bounded
parabolic `C^{0,α}` estimates with one compact determinant lower bound shared by the family. -/
theorem matrix_inv_two_index_contract_family_with_of_isCompact_det_ne_zero
    {ι n p q 𝕜 : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
    [Fintype p] [Fintype q] [NormedField 𝕜]
    {K : Set (ℝ × X)}
    {B H : ι → n → n → ℝ} {TB TH : ι → n → n → p → q → ℝ}
    {M : ι → ℝ × X → Matrix n n 𝕜}
    {T : ι → ℝ × X → n → n → p → q → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hB : ∀ r a b, 0 ≤ B r a b) (hH : ∀ r a b, 0 ≤ H r a b)
    (hTB : ∀ r a b i j, 0 ≤ TB r a b i j)
    (hTH : ∀ r a b i j, 0 ≤ TH r a b i j)
    (hM : ∀ r a b,
      ParabolicC0AlphaWith (B r a b) (H r a b) α (fun z => M r z a b) K)
    (hT : ∀ r a b i j,
      ParabolicC0AlphaWith (TB r a b i j) (TH r a b i j) α
        (fun z => T r z a b i j) K)
    (hdet_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (M r z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M r z).det‖) ∧
      ∀ r,
        ParabolicC0AlphaWith
          (∑ i : p, ∑ j : q,
            matrixInvTwoIndexContractEntryBoundConst (𝕜 := 𝕜) δ (B r) (TB r) i j)
          (∑ i : p, ∑ j : q,
            matrixInvTwoIndexContractEntryHolderConst
              (𝕜 := 𝕜) δ (B r) (H r) (TB r) (TH r) i j)
          α
          (fun z : ℝ × X =>
            (fun i j =>
              ∑ a : n, ∑ b : n, ((M r z)⁻¹ : Matrix n n 𝕜) a b *
                T r z a b i j :
              Matrix p q 𝕜)) K := by
  have hMctrl : ∀ r a b, ParabolicC0AlphaOn α (fun z => M r z a b) K := by
    intro r a b
    exact ⟨B r a b, hB r a b, H r a b, hH r a b, hM r a b⟩
  rcases matrix_det_family_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hMctrl hdet_ne with
    ⟨δ, hδpos, hdet⟩
  refine ⟨δ, hδpos, hdet, ?_⟩
  intro r
  exact matrix_inv_two_index_contract_with
    (M := M r) (T := T r)
    (hH r) (hTB r) (hTH r) (hM r) (hT r) hδpos (hdet r)

/-- Quantitative sup constant for one entry of the finite quadratic Christoffel Ricci
contraction. -/
def christoffelQuadraticRicciEntryBoundConst {n : Type*} [Fintype n]
    (BΓ : n → n → n → ℝ) (i j : n) : ℝ :=
  (∑ a : n, ∑ b : n, BΓ a i j * BΓ b a b) +
    (∑ a : n, ∑ b : n, BΓ a i b * BΓ b a j)

/-- Quantitative Holder constant for one entry of the finite quadratic Christoffel Ricci
contraction. -/
def christoffelQuadraticRicciEntryHolderConst {n : Type*} [Fintype n]
    (BΓ HΓ : n → n → n → ℝ) (i j : n) : ℝ :=
  (∑ a : n, ∑ b : n, (BΓ a i j * HΓ b a b + BΓ b a b * HΓ a i j)) +
    (∑ a : n, ∑ b : n, (BΓ a i b * HΓ b a j + BΓ b a j * HΓ a i b))

theorem christoffelQuadraticRicciEntryBoundConst_nonneg {n : Type*} [Fintype n]
    {BΓ : n → n → n → ℝ} (hBΓ : ∀ a b c, 0 ≤ BΓ a b c) (i j : n) :
    0 ≤ christoffelQuadraticRicciEntryBoundConst BΓ i j := by
  exact add_nonneg
    (Finset.sum_nonneg fun a _ha =>
      Finset.sum_nonneg fun b _hb =>
        mul_nonneg (hBΓ a i j) (hBΓ b a b))
    (Finset.sum_nonneg fun a _ha =>
      Finset.sum_nonneg fun b _hb =>
        mul_nonneg (hBΓ a i b) (hBΓ b a j))

theorem christoffelQuadraticRicciEntryHolderConst_nonneg {n : Type*} [Fintype n]
    {BΓ HΓ : n → n → n → ℝ} (hBΓ : ∀ a b c, 0 ≤ BΓ a b c)
    (hHΓ : ∀ a b c, 0 ≤ HΓ a b c) (i j : n) :
    0 ≤ christoffelQuadraticRicciEntryHolderConst BΓ HΓ i j := by
  exact add_nonneg
    (Finset.sum_nonneg fun a _ha =>
      Finset.sum_nonneg fun b _hb =>
        add_nonneg
          (mul_nonneg (hBΓ a i j) (hHΓ b a b))
          (mul_nonneg (hBΓ b a b) (hHΓ a i j)))
    (Finset.sum_nonneg fun a _ha =>
      Finset.sum_nonneg fun b _hb =>
        add_nonneg
          (mul_nonneg (hBΓ a i b) (hHΓ b a j))
          (mul_nonneg (hBΓ b a j) (hHΓ a i b)))

/-- Ricci-coordinate quadratic Christoffel contractions preserve parabolic `C^{0,α}` control
from entrywise control of the Christoffel array. -/
theorem christoffel_quadratic_ricci_entry {n A : Type*} [Fintype n] [NormedRing A]
    {Γ : ℝ × X → n → n → n → A}
    (hΓ : ∀ a b c, ParabolicC0AlphaOn α (fun z => Γ z a b c) s) (i j : n) :
    ParabolicC0AlphaOn α
      (fun z =>
        (∑ a : n, ∑ b : n, Γ z a i j * Γ z b a b) -
          (∑ a : n, ∑ b : n, Γ z a i b * Γ z b a j)) s := by
  have hleftInner : ∀ a : n,
      ParabolicC0AlphaOn α (fun z => ∑ b : n, Γ z a i j * Γ z b a b) s := by
    intro a
    simpa using
      (ParabolicC0AlphaOn.sum (X := X) (α := α) (s := s)
        (S := (Finset.univ : Finset n))
        (u := fun b z => Γ z a i j * Γ z b a b)
        (fun b _hb => (hΓ a i j).mul (hΓ b a b)))
  have hleft :
      ParabolicC0AlphaOn α (fun z => ∑ a : n, ∑ b : n, Γ z a i j * Γ z b a b) s := by
    simpa using
      (ParabolicC0AlphaOn.sum (X := X) (α := α) (s := s)
        (S := (Finset.univ : Finset n))
        (u := fun a z => ∑ b : n, Γ z a i j * Γ z b a b)
        (fun a _ha => hleftInner a))
  have hrightInner : ∀ a : n,
      ParabolicC0AlphaOn α (fun z => ∑ b : n, Γ z a i b * Γ z b a j) s := by
    intro a
    simpa using
      (ParabolicC0AlphaOn.sum (X := X) (α := α) (s := s)
        (S := (Finset.univ : Finset n))
        (u := fun b z => Γ z a i b * Γ z b a j)
        (fun b _hb => (hΓ a i b).mul (hΓ b a j)))
  have hright :
      ParabolicC0AlphaOn α (fun z => ∑ a : n, ∑ b : n, Γ z a i b * Γ z b a j) s := by
    simpa using
      (ParabolicC0AlphaOn.sum (X := X) (α := α) (s := s)
        (S := (Finset.univ : Finset n))
        (u := fun a z => ∑ b : n, Γ z a i b * Γ z b a j)
        (fun a _ha => hrightInner a))
  exact hleft.sub hright

/-- The full finite Ricci-coordinate quadratic Christoffel contraction packages as a
matrix-valued parabolic `C^{0,α}` function. -/
theorem christoffel_quadratic_ricci {n A : Type*} [Fintype n] [NormedRing A]
    {Γ : ℝ × X → n → n → n → A}
    (hΓ : ∀ a b c, ParabolicC0AlphaOn α (fun z => Γ z a b c) s) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × X =>
        (fun i j =>
          (∑ a : n, ∑ b : n, Γ z a i j * Γ z b a b) -
            (∑ a : n, ∑ b : n, Γ z a i b * Γ z b a j) :
            Matrix n n A)) s :=
  matrix_of_entries fun i j => christoffel_quadratic_ricci_entry hΓ i j

/-- One quadratic Christoffel Ricci contraction entry has an explicit bounded parabolic
`C^{0,α}` estimate from explicit Christoffel-array estimates. -/
theorem christoffel_quadratic_ricci_entry_with {n A : Type*} [Fintype n]
    [NormedRing A] {BΓ HΓ : n → n → n → ℝ} {Γ : ℝ × X → n → n → n → A}
    (hBΓ : ∀ a b c, 0 ≤ BΓ a b c)
    (hΓ : ∀ a b c, ParabolicC0AlphaWith (BΓ a b c) (HΓ a b c) α
      (fun z => Γ z a b c) s)
    (i j : n) :
    ParabolicC0AlphaWith
      (christoffelQuadraticRicciEntryBoundConst BΓ i j)
      (christoffelQuadraticRicciEntryHolderConst BΓ HΓ i j)
      α
      (fun z =>
        (∑ a : n, ∑ b : n, Γ z a i j * Γ z b a b) -
          (∑ a : n, ∑ b : n, Γ z a i b * Γ z b a j)) s := by
  classical
  have hleftInner : ∀ a ∈ (Finset.univ : Finset n),
      ParabolicC0AlphaWith
        (∑ b : n, BΓ a i j * BΓ b a b)
        (∑ b : n, (BΓ a i j * HΓ b a b + BΓ b a b * HΓ a i j))
        α (fun z => ∑ b : n, Γ z a i j * Γ z b a b) s := by
    intro a _ha
    simpa using
      (ParabolicC0AlphaWith.sum (X := X) (α := α) (s := s)
        (S := (Finset.univ : Finset n))
        (B := fun b => BΓ a i j * BΓ b a b)
        (H := fun b => BΓ a i j * HΓ b a b + BΓ b a b * HΓ a i j)
        (u := fun b z => Γ z a i j * Γ z b a b)
        (fun b _hb => (hΓ a i j).mul (hΓ b a b) (hBΓ a i j)))
  have hleft :
      ParabolicC0AlphaWith
        (∑ a : n, ∑ b : n, BΓ a i j * BΓ b a b)
        (∑ a : n, ∑ b : n, (BΓ a i j * HΓ b a b + BΓ b a b * HΓ a i j))
        α (fun z => ∑ a : n, ∑ b : n, Γ z a i j * Γ z b a b) s := by
    simpa using
      (ParabolicC0AlphaWith.sum (X := X) (α := α) (s := s)
        (S := (Finset.univ : Finset n))
        (B := fun a => ∑ b : n, BΓ a i j * BΓ b a b)
        (H := fun a => ∑ b : n, (BΓ a i j * HΓ b a b + BΓ b a b * HΓ a i j))
        (u := fun a z => ∑ b : n, Γ z a i j * Γ z b a b)
        hleftInner)
  have hrightInner : ∀ a ∈ (Finset.univ : Finset n),
      ParabolicC0AlphaWith
        (∑ b : n, BΓ a i b * BΓ b a j)
        (∑ b : n, (BΓ a i b * HΓ b a j + BΓ b a j * HΓ a i b))
        α (fun z => ∑ b : n, Γ z a i b * Γ z b a j) s := by
    intro a _ha
    simpa using
      (ParabolicC0AlphaWith.sum (X := X) (α := α) (s := s)
        (S := (Finset.univ : Finset n))
        (B := fun b => BΓ a i b * BΓ b a j)
        (H := fun b => BΓ a i b * HΓ b a j + BΓ b a j * HΓ a i b)
        (u := fun b z => Γ z a i b * Γ z b a j)
        (fun b _hb => (hΓ a i b).mul (hΓ b a j) (hBΓ a i b)))
  have hright :
      ParabolicC0AlphaWith
        (∑ a : n, ∑ b : n, BΓ a i b * BΓ b a j)
        (∑ a : n, ∑ b : n, (BΓ a i b * HΓ b a j + BΓ b a j * HΓ a i b))
        α (fun z => ∑ a : n, ∑ b : n, Γ z a i b * Γ z b a j) s := by
    simpa using
      (ParabolicC0AlphaWith.sum (X := X) (α := α) (s := s)
        (S := (Finset.univ : Finset n))
        (B := fun a => ∑ b : n, BΓ a i b * BΓ b a j)
        (H := fun a => ∑ b : n, (BΓ a i b * HΓ b a j + BΓ b a j * HΓ a i b))
        (u := fun a z => ∑ b : n, Γ z a i b * Γ z b a j)
        hrightInner)
  simpa [christoffelQuadraticRicciEntryBoundConst, christoffelQuadraticRicciEntryHolderConst]
    using hleft.sub hright

/-- The full finite quadratic Christoffel Ricci contraction has an explicit matrix-valued
bounded parabolic `C^{0,α}` estimate. -/
theorem christoffel_quadratic_ricci_with {n A : Type*} [Fintype n] [NormedRing A]
    {BΓ HΓ : n → n → n → ℝ} {Γ : ℝ × X → n → n → n → A}
    (hBΓ : ∀ a b c, 0 ≤ BΓ a b c) (hHΓ : ∀ a b c, 0 ≤ HΓ a b c)
    (hΓ : ∀ a b c, ParabolicC0AlphaWith (BΓ a b c) (HΓ a b c) α
      (fun z => Γ z a b c) s) :
    ParabolicC0AlphaWith
      (∑ i : n, ∑ j : n, christoffelQuadraticRicciEntryBoundConst BΓ i j)
      (∑ i : n, ∑ j : n, christoffelQuadraticRicciEntryHolderConst BΓ HΓ i j)
      α
      (fun z : ℝ × X =>
        (fun i j =>
          (∑ a : n, ∑ b : n, Γ z a i j * Γ z b a b) -
            (∑ a : n, ∑ b : n, Γ z a i b * Γ z b a j) :
            Matrix n n A)) s := by
  refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
  · intro i
    exact Finset.sum_nonneg fun j _hj =>
      christoffelQuadraticRicciEntryBoundConst_nonneg hBΓ i j
  · intro i
    exact Finset.sum_nonneg fun j _hj =>
      christoffelQuadraticRicciEntryHolderConst_nonneg hBΓ hHΓ i j
  · intro i
    refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
    · intro j
      exact christoffelQuadraticRicciEntryBoundConst_nonneg hBΓ i j
    · intro j
      exact christoffelQuadraticRicciEntryHolderConst_nonneg hBΓ hHΓ i j
    · intro j
      exact christoffel_quadratic_ricci_entry_with hBΓ hΓ i j

/-- Quantitative sup constant for one entry of the difference of two finite quadratic
Christoffel Ricci contractions. -/
def christoffelQuadraticRicciEntrySubBoundConst {n : Type*} [Fintype n]
    (BΓ BΛ Bd : n → n → n → ℝ) (i j : n) : ℝ :=
  (Finset.univ.sum fun a : n =>
    Finset.univ.sum fun b : n => BΓ a i j * Bd b a b + Bd a i j * BΛ b a b) +
    (Finset.univ.sum fun a : n =>
      Finset.univ.sum fun b : n => BΓ a i b * Bd b a j + Bd a i b * BΛ b a j)

/-- Quantitative Holder constant for one entry of the difference of two finite quadratic
Christoffel Ricci contractions. -/
def christoffelQuadraticRicciEntrySubHolderConst {n : Type*} [Fintype n]
    (BΓ HΓ BΛ HΛ Bd Hd : n → n → n → ℝ) (i j : n) : ℝ :=
  (Finset.univ.sum fun a : n =>
    Finset.univ.sum fun b : n =>
      ((BΓ a i j * Hd b a b + Bd b a b * HΓ a i j) +
        (Bd a i j * HΛ b a b + BΛ b a b * Hd a i j))) +
    (Finset.univ.sum fun a : n =>
      Finset.univ.sum fun b : n =>
        ((BΓ a i b * Hd b a j + Bd b a j * HΓ a i b) +
          (Bd a i b * HΛ b a j + BΛ b a j * Hd a i b)))

theorem christoffelQuadraticRicciEntrySubBoundConst_nonneg {n : Type*} [Fintype n]
    {BΓ BΛ Bd : n → n → n → ℝ} (hBΓ : ∀ a b c, 0 ≤ BΓ a b c)
    (hBΛ : ∀ a b c, 0 ≤ BΛ a b c) (hBd : ∀ a b c, 0 ≤ Bd a b c)
    (i j : n) :
    0 ≤ christoffelQuadraticRicciEntrySubBoundConst BΓ BΛ Bd i j := by
  simpa [christoffelQuadraticRicciEntrySubBoundConst] using
    (add_nonneg
      (Finset.sum_nonneg fun a _ha =>
        Finset.sum_nonneg fun b _hb =>
          add_nonneg
            (mul_nonneg (hBΓ a i j) (hBd b a b))
            (mul_nonneg (hBd a i j) (hBΛ b a b)))
      (Finset.sum_nonneg fun a _ha =>
        Finset.sum_nonneg fun b _hb =>
          add_nonneg
            (mul_nonneg (hBΓ a i b) (hBd b a j))
            (mul_nonneg (hBd a i b) (hBΛ b a j))))

theorem christoffelQuadraticRicciEntrySubHolderConst_nonneg {n : Type*} [Fintype n]
    {BΓ HΓ BΛ HΛ Bd Hd : n → n → n → ℝ}
    (hBΓ : ∀ a b c, 0 ≤ BΓ a b c) (hHΓ : ∀ a b c, 0 ≤ HΓ a b c)
    (hBΛ : ∀ a b c, 0 ≤ BΛ a b c) (hHΛ : ∀ a b c, 0 ≤ HΛ a b c)
    (hBd : ∀ a b c, 0 ≤ Bd a b c) (hHd : ∀ a b c, 0 ≤ Hd a b c)
    (i j : n) :
    0 ≤ christoffelQuadraticRicciEntrySubHolderConst BΓ HΓ BΛ HΛ Bd Hd i j := by
  simpa [christoffelQuadraticRicciEntrySubHolderConst] using
    (add_nonneg
      (Finset.sum_nonneg fun a _ha =>
        Finset.sum_nonneg fun b _hb =>
          add_nonneg
            (add_nonneg
              (mul_nonneg (hBΓ a i j) (hHd b a b))
              (mul_nonneg (hBd b a b) (hHΓ a i j)))
            (add_nonneg
              (mul_nonneg (hBd a i j) (hHΛ b a b))
              (mul_nonneg (hBΛ b a b) (hHd a i j))))
      (Finset.sum_nonneg fun a _ha =>
        Finset.sum_nonneg fun b _hb =>
          add_nonneg
            (add_nonneg
              (mul_nonneg (hBΓ a i b) (hHd b a j))
              (mul_nonneg (hBd b a j) (hHΓ a i b)))
            (add_nonneg
              (mul_nonneg (hBd a i b) (hHΛ b a j))
              (mul_nonneg (hBΛ b a j) (hHd a i b)))))

/-- One difference of quadratic Christoffel Ricci contraction entries has an explicit bounded
parabolic `C^{0,α}` estimate from estimates on one Christoffel array, the other array, and their
difference. -/
theorem christoffel_quadratic_ricci_entry_sub_with {n A : Type*} [Fintype n]
    [NormedRing A] {BΓ HΓ BΛ HΛ Bd Hd : n → n → n → ℝ}
    {Γ Λ : ℝ × X → n → n → n → A}
    (hBΓ : ∀ a b c, 0 ≤ BΓ a b c) (hBd : ∀ a b c, 0 ≤ Bd a b c)
    (hΓ : ∀ a b c, ParabolicC0AlphaWith (BΓ a b c) (HΓ a b c) α
      (fun z => Γ z a b c) s)
    (hΛ : ∀ a b c, ParabolicC0AlphaWith (BΛ a b c) (HΛ a b c) α
      (fun z => Λ z a b c) s)
    (hdiff : ∀ a b c, ParabolicC0AlphaWith (Bd a b c) (Hd a b c) α
      (fun z => Γ z a b c - Λ z a b c) s)
    (i j : n) :
    ParabolicC0AlphaWith
      (christoffelQuadraticRicciEntrySubBoundConst BΓ BΛ Bd i j)
      (christoffelQuadraticRicciEntrySubHolderConst BΓ HΓ BΛ HΛ Bd Hd i j)
      α
      (fun z =>
        ((∑ a : n, ∑ b : n, Γ z a i j * Γ z b a b) -
            (∑ a : n, ∑ b : n, Γ z a i b * Γ z b a j)) -
          ((∑ a : n, ∑ b : n, Λ z a i j * Λ z b a b) -
            (∑ a : n, ∑ b : n, Λ z a i b * Λ z b a j))) s := by
  classical
  have hleftInner : ∀ a ∈ (Finset.univ : Finset n),
      ParabolicC0AlphaWith
        (Finset.univ.sum fun b : n => BΓ a i j * Bd b a b + Bd a i j * BΛ b a b)
        (Finset.univ.sum fun b : n =>
          ((BΓ a i j * Hd b a b + Bd b a b * HΓ a i j) +
            (Bd a i j * HΛ b a b + BΛ b a b * Hd a i j)))
        α
        (fun z =>
          (∑ b : n, Γ z a i j * Γ z b a b) -
            ∑ b : n, Λ z a i j * Λ z b a b) s := by
    intro a _ha
    simpa using
      (ParabolicC0AlphaWith.finset_sum_mul_sub_sum_mul (X := X) (α := α) (s := s)
        (S := (Finset.univ : Finset n))
        (Bu := fun _b => BΓ a i j) (Hu := fun _b => HΓ a i j)
        (Bv := fun b => BΛ b a b) (Hv := fun b => HΛ b a b)
        (Bdu := fun _b => Bd a i j) (Hdu := fun _b => Hd a i j)
        (Bdv := fun b => Bd b a b) (Hdv := fun b => Hd b a b)
        (u := fun _b z => Γ z a i j) (u' := fun _b z => Λ z a i j)
        (v := fun b z => Γ z b a b) (v' := fun b z => Λ z b a b)
        (fun _b _hb => hΓ a i j) (fun b _hb => hΛ b a b)
        (fun _b _hb => hdiff a i j) (fun b _hb => hdiff b a b)
        (fun _b _hb => hBΓ a i j) (fun _b _hb => hBd a i j))
  have hleft :
      ParabolicC0AlphaWith
        (Finset.univ.sum fun a : n =>
          Finset.univ.sum fun b : n => BΓ a i j * Bd b a b + Bd a i j * BΛ b a b)
        (Finset.univ.sum fun a : n =>
          Finset.univ.sum fun b : n =>
          ((BΓ a i j * Hd b a b + Bd b a b * HΓ a i j) +
            (Bd a i j * HΛ b a b + BΛ b a b * Hd a i j)))
        α
        (fun z =>
          (∑ a : n, ∑ b : n, Γ z a i j * Γ z b a b) -
            ∑ a : n, ∑ b : n, Λ z a i j * Λ z b a b) s := by
    have hsum := ParabolicC0AlphaWith.sum (X := X) (α := α) (s := s)
      (S := (Finset.univ : Finset n))
      (B := fun a =>
        Finset.univ.sum fun b : n => BΓ a i j * Bd b a b + Bd a i j * BΛ b a b)
      (H := fun a => Finset.univ.sum fun b : n =>
        ((BΓ a i j * Hd b a b + Bd b a b * HΓ a i j) +
          (Bd a i j * HΛ b a b + BΛ b a b * Hd a i j)))
      (u := fun a z =>
        (∑ b : n, Γ z a i j * Γ z b a b) -
          ∑ b : n, Λ z a i j * Λ z b a b)
      hleftInner
    simpa [Finset.sum_sub_distrib] using hsum
  have hrightInner : ∀ a ∈ (Finset.univ : Finset n),
      ParabolicC0AlphaWith
        (Finset.univ.sum fun b : n => BΓ a i b * Bd b a j + Bd a i b * BΛ b a j)
        (Finset.univ.sum fun b : n =>
          ((BΓ a i b * Hd b a j + Bd b a j * HΓ a i b) +
            (Bd a i b * HΛ b a j + BΛ b a j * Hd a i b)))
        α
        (fun z =>
          (∑ b : n, Γ z a i b * Γ z b a j) -
            ∑ b : n, Λ z a i b * Λ z b a j) s := by
    intro a _ha
    simpa using
      (ParabolicC0AlphaWith.finset_sum_mul_sub_sum_mul (X := X) (α := α) (s := s)
        (S := (Finset.univ : Finset n))
        (Bu := fun b => BΓ a i b) (Hu := fun b => HΓ a i b)
        (Bv := fun b => BΛ b a j) (Hv := fun b => HΛ b a j)
        (Bdu := fun b => Bd a i b) (Hdu := fun b => Hd a i b)
        (Bdv := fun b => Bd b a j) (Hdv := fun b => Hd b a j)
        (u := fun b z => Γ z a i b) (u' := fun b z => Λ z a i b)
        (v := fun b z => Γ z b a j) (v' := fun b z => Λ z b a j)
        (fun b _hb => hΓ a i b) (fun b _hb => hΛ b a j)
        (fun b _hb => hdiff a i b) (fun b _hb => hdiff b a j)
        (fun b _hb => hBΓ a i b) (fun b _hb => hBd a i b))
  have hright :
      ParabolicC0AlphaWith
        (Finset.univ.sum fun a : n =>
          Finset.univ.sum fun b : n => BΓ a i b * Bd b a j + Bd a i b * BΛ b a j)
        (Finset.univ.sum fun a : n =>
          Finset.univ.sum fun b : n =>
          ((BΓ a i b * Hd b a j + Bd b a j * HΓ a i b) +
            (Bd a i b * HΛ b a j + BΛ b a j * Hd a i b)))
        α
        (fun z =>
          (∑ a : n, ∑ b : n, Γ z a i b * Γ z b a j) -
            ∑ a : n, ∑ b : n, Λ z a i b * Λ z b a j) s := by
    have hsum := ParabolicC0AlphaWith.sum (X := X) (α := α) (s := s)
      (S := (Finset.univ : Finset n))
      (B := fun a =>
        Finset.univ.sum fun b : n => BΓ a i b * Bd b a j + Bd a i b * BΛ b a j)
      (H := fun a => Finset.univ.sum fun b : n =>
        ((BΓ a i b * Hd b a j + Bd b a j * HΓ a i b) +
          (Bd a i b * HΛ b a j + BΛ b a j * Hd a i b)))
      (u := fun a z =>
        (∑ b : n, Γ z a i b * Γ z b a j) -
          ∑ b : n, Λ z a i b * Λ z b a j)
      hrightInner
    simpa [Finset.sum_sub_distrib] using hsum
  have hsub := hleft.sub hright
  have hsub' :
      ParabolicC0AlphaWith
        (christoffelQuadraticRicciEntrySubBoundConst BΓ BΛ Bd i j)
        (christoffelQuadraticRicciEntrySubHolderConst BΓ HΓ BΛ HΛ Bd Hd i j)
        α
        (fun z =>
          ((∑ a : n, ∑ b : n, Γ z a i j * Γ z b a b) -
              ∑ a : n, ∑ b : n, Λ z a i j * Λ z b a b) -
            ((∑ a : n, ∑ b : n, Γ z a i b * Γ z b a j) -
              ∑ a : n, ∑ b : n, Λ z a i b * Λ z b a j)) s := by
    simpa [christoffelQuadraticRicciEntrySubBoundConst,
      christoffelQuadraticRicciEntrySubHolderConst] using hsub
  convert hsub' using 1
  ext z
  abel

/-- The full difference of finite quadratic Christoffel Ricci contractions has an explicit
matrix-valued bounded parabolic `C^{0,α}` estimate. -/
theorem christoffel_quadratic_ricci_sub_with {n A : Type*} [Fintype n] [NormedRing A]
    {BΓ HΓ BΛ HΛ Bd Hd : n → n → n → ℝ}
    {Γ Λ : ℝ × X → n → n → n → A}
    (hBΓ : ∀ a b c, 0 ≤ BΓ a b c) (hHΓ : ∀ a b c, 0 ≤ HΓ a b c)
    (hBΛ : ∀ a b c, 0 ≤ BΛ a b c) (hHΛ : ∀ a b c, 0 ≤ HΛ a b c)
    (hBd : ∀ a b c, 0 ≤ Bd a b c) (hHd : ∀ a b c, 0 ≤ Hd a b c)
    (hΓ : ∀ a b c, ParabolicC0AlphaWith (BΓ a b c) (HΓ a b c) α
      (fun z => Γ z a b c) s)
    (hΛ : ∀ a b c, ParabolicC0AlphaWith (BΛ a b c) (HΛ a b c) α
      (fun z => Λ z a b c) s)
    (hdiff : ∀ a b c, ParabolicC0AlphaWith (Bd a b c) (Hd a b c) α
      (fun z => Γ z a b c - Λ z a b c) s) :
    ParabolicC0AlphaWith
      (∑ i : n, ∑ j : n, christoffelQuadraticRicciEntrySubBoundConst BΓ BΛ Bd i j)
      (∑ i : n, ∑ j : n,
        christoffelQuadraticRicciEntrySubHolderConst BΓ HΓ BΛ HΛ Bd Hd i j)
      α
      (fun z : ℝ × X =>
        ((fun i j =>
          (∑ a : n, ∑ b : n, Γ z a i j * Γ z b a b) -
            (∑ a : n, ∑ b : n, Γ z a i b * Γ z b a j) :
            Matrix n n A) -
          (fun i j =>
            (∑ a : n, ∑ b : n, Λ z a i j * Λ z b a b) -
              (∑ a : n, ∑ b : n, Λ z a i b * Λ z b a j) :
              Matrix n n A))) s := by
  refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
  · intro i
    exact Finset.sum_nonneg fun j _hj =>
      christoffelQuadraticRicciEntrySubBoundConst_nonneg hBΓ hBΛ hBd i j
  · intro i
    exact Finset.sum_nonneg fun j _hj =>
      christoffelQuadraticRicciEntrySubHolderConst_nonneg hBΓ hHΓ hBΛ hHΛ hBd hHd i j
  · intro i
    refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
    · intro j
      exact christoffelQuadraticRicciEntrySubBoundConst_nonneg hBΓ hBΛ hBd i j
    · intro j
      exact christoffelQuadraticRicciEntrySubHolderConst_nonneg hBΓ hHΓ hBΛ hHΛ hBd hHd i j
    · intro j
      exact christoffel_quadratic_ricci_entry_sub_with hBΓ hBd hΓ hΛ hdiff i j

/-- Differences of quadratic Christoffel Ricci contraction entries preserve existential
parabolic `C^{0,α}` control from entrywise controls and entrywise difference controls. -/
theorem christoffel_quadratic_ricci_entry_sub {n A : Type*} [Fintype n] [NormedRing A]
    {Γ Λ : ℝ × X → n → n → n → A}
    (hΓ : ∀ a b c, ParabolicC0AlphaOn α (fun z => Γ z a b c) s)
    (hΛ : ∀ a b c, ParabolicC0AlphaOn α (fun z => Λ z a b c) s)
    (hdiff : ∀ a b c, ParabolicC0AlphaOn α (fun z => Γ z a b c - Λ z a b c) s)
    (i j : n) :
    ParabolicC0AlphaOn α
      (fun z =>
        ((∑ a : n, ∑ b : n, Γ z a i j * Γ z b a b) -
            (∑ a : n, ∑ b : n, Γ z a i b * Γ z b a j)) -
          ((∑ a : n, ∑ b : n, Λ z a i j * Λ z b a b) -
            (∑ a : n, ∑ b : n, Λ z a i b * Λ z b a j))) s := by
  classical
  have hleftInner : ∀ a ∈ (Finset.univ : Finset n),
      ParabolicC0AlphaOn α
        (fun z =>
          (∑ b : n, Γ z a i j * Γ z b a b) -
            ∑ b : n, Λ z a i j * Λ z b a b) s := by
    intro a _ha
    simpa using
      (ParabolicC0AlphaOn.finset_sum_mul_sub_sum_mul (X := X) (α := α) (s := s)
        (S := (Finset.univ : Finset n))
        (u := fun _b z => Γ z a i j) (u' := fun _b z => Λ z a i j)
        (v := fun b z => Γ z b a b) (v' := fun b z => Λ z b a b)
        (fun _b _hb => hΓ a i j) (fun b _hb => hΛ b a b)
        (fun _b _hb => hdiff a i j) (fun b _hb => hdiff b a b))
  have hleft : ParabolicC0AlphaOn α
      (fun z =>
        (∑ a : n, ∑ b : n, Γ z a i j * Γ z b a b) -
          ∑ a : n, ∑ b : n, Λ z a i j * Λ z b a b) s := by
    have hsum := ParabolicC0AlphaOn.sum (X := X) (α := α) (s := s)
      (S := (Finset.univ : Finset n))
      (u := fun a z =>
        (∑ b : n, Γ z a i j * Γ z b a b) -
          ∑ b : n, Λ z a i j * Λ z b a b)
      hleftInner
    simpa [Finset.sum_sub_distrib] using hsum
  have hrightInner : ∀ a ∈ (Finset.univ : Finset n),
      ParabolicC0AlphaOn α
        (fun z =>
          (∑ b : n, Γ z a i b * Γ z b a j) -
            ∑ b : n, Λ z a i b * Λ z b a j) s := by
    intro a _ha
    simpa using
      (ParabolicC0AlphaOn.finset_sum_mul_sub_sum_mul (X := X) (α := α) (s := s)
        (S := (Finset.univ : Finset n))
        (u := fun b z => Γ z a i b) (u' := fun b z => Λ z a i b)
        (v := fun b z => Γ z b a j) (v' := fun b z => Λ z b a j)
        (fun b _hb => hΓ a i b) (fun b _hb => hΛ b a j)
        (fun b _hb => hdiff a i b) (fun b _hb => hdiff b a j))
  have hright : ParabolicC0AlphaOn α
      (fun z =>
        (∑ a : n, ∑ b : n, Γ z a i b * Γ z b a j) -
          ∑ a : n, ∑ b : n, Λ z a i b * Λ z b a j) s := by
    have hsum := ParabolicC0AlphaOn.sum (X := X) (α := α) (s := s)
      (S := (Finset.univ : Finset n))
      (u := fun a z =>
        (∑ b : n, Γ z a i b * Γ z b a j) -
          ∑ b : n, Λ z a i b * Λ z b a j)
      hrightInner
    simpa [Finset.sum_sub_distrib] using hsum
  have hsub := hleft.sub hright
  convert hsub using 1
  ext z
  abel

/-- Differences of finite quadratic Christoffel Ricci contractions preserve existential
parabolic `C^{0,α}` control from entrywise controls and entrywise difference controls. -/
theorem christoffel_quadratic_ricci_sub {n A : Type*} [Fintype n] [NormedRing A]
    {Γ Λ : ℝ × X → n → n → n → A}
    (hΓ : ∀ a b c, ParabolicC0AlphaOn α (fun z => Γ z a b c) s)
    (hΛ : ∀ a b c, ParabolicC0AlphaOn α (fun z => Λ z a b c) s)
    (hdiff : ∀ a b c, ParabolicC0AlphaOn α (fun z => Γ z a b c - Λ z a b c) s) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × X =>
        ((fun i j =>
          (∑ a : n, ∑ b : n, Γ z a i j * Γ z b a b) -
            (∑ a : n, ∑ b : n, Γ z a i b * Γ z b a j) :
            Matrix n n A) -
          (fun i j =>
            (∑ a : n, ∑ b : n, Λ z a i j * Λ z b a b) -
              (∑ a : n, ∑ b : n, Λ z a i b * Λ z b a j) :
              Matrix n n A))) s :=
  matrix_of_entries fun i j => christoffel_quadratic_ricci_entry_sub hΓ hΛ hdiff i j

/-- Ricci-coordinate quadratic Christoffel contractions are pointwise Lipschitz on bounded
Christoffel arrays. -/
theorem christoffel_quadratic_ricci_entry_norm_sub_le {n A : Type*} [Fintype n]
    [NormedRing A] {BΓ : n → n → n → ℝ} (Γ Λ : n → n → n → A)
    (hΓ : ∀ a b c, ‖Γ a b c‖ ≤ BΓ a b c)
    (hΛ : ∀ a b c, ‖Λ a b c‖ ≤ BΓ a b c) (i j : n) :
    ‖((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
        (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) -
      ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
        (∑ a : n, ∑ b : n, Λ a i b * Λ b a j))‖ ≤
      (∑ a : n, ∑ b : n,
        (BΓ a i j * ‖Γ b a b - Λ b a b‖ +
          BΓ b a b * ‖Γ a i j - Λ a i j‖)) +
      (∑ a : n, ∑ b : n,
        (BΓ a i b * ‖Γ b a j - Λ b a j‖ +
          BΓ b a j * ‖Γ a i b - Λ a i b‖)) := by
  classical
  let leftΓ : A := ∑ a : n, ∑ b : n, Γ a i j * Γ b a b
  let leftΛ : A := ∑ a : n, ∑ b : n, Λ a i j * Λ b a b
  let rightΓ : A := ∑ a : n, ∑ b : n, Γ a i b * Γ b a j
  let rightΛ : A := ∑ a : n, ∑ b : n, Λ a i b * Λ b a j
  let leftBound : ℝ := ∑ a : n, ∑ b : n,
    (BΓ a i j * ‖Γ b a b - Λ b a b‖ + BΓ b a b * ‖Γ a i j - Λ a i j‖)
  let rightBound : ℝ := ∑ a : n, ∑ b : n,
    (BΓ a i b * ‖Γ b a j - Λ b a j‖ + BΓ b a j * ‖Γ a i b - Λ a i b‖)
  have hleftInner : ∀ a : n,
      ‖(∑ b : n, Γ a i j * Γ b a b) - ∑ b : n, Λ a i j * Λ b a b‖ ≤
        ∑ b : n,
          (BΓ a i j * ‖Γ b a b - Λ b a b‖ +
            BΓ b a b * ‖Γ a i j - Λ a i j‖) := by
    intro a
    simpa using
      (norm_finset_sum_mul_sub_sum_mul_le
        (S := (Finset.univ : Finset n))
        (B := fun _b => BΓ a i j)
        (D := fun b => BΓ b a b)
        (a := fun _b => Γ a i j)
        (b := fun b => Γ b a b)
        (c := fun _b => Λ a i j)
        (d := fun b => Λ b a b)
        (fun _b _hb => hΓ a i j)
        (fun b _hb => hΛ b a b))
  have hleft : ‖leftΓ - leftΛ‖ ≤ leftBound := by
    calc
      ‖leftΓ - leftΛ‖ =
          ‖(∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
            ∑ a : n, ∑ b : n, Λ a i j * Λ b a b‖ := by
        rfl
      _ = ‖∑ a : n,
          ((∑ b : n, Γ a i j * Γ b a b) -
            ∑ b : n, Λ a i j * Λ b a b)‖ := by
        rw [Finset.sum_sub_distrib]
      _ ≤ ∑ a : n,
          ‖(∑ b : n, Γ a i j * Γ b a b) -
            ∑ b : n, Λ a i j * Λ b a b‖ :=
        norm_sum_le _ _
      _ ≤ ∑ a : n, ∑ b : n,
          (BΓ a i j * ‖Γ b a b - Λ b a b‖ +
            BΓ b a b * ‖Γ a i j - Λ a i j‖) :=
        Finset.sum_le_sum fun a _ha => hleftInner a
      _ = leftBound := by
        rfl
  have hrightInner : ∀ a : n,
      ‖(∑ b : n, Γ a i b * Γ b a j) - ∑ b : n, Λ a i b * Λ b a j‖ ≤
        ∑ b : n,
          (BΓ a i b * ‖Γ b a j - Λ b a j‖ +
            BΓ b a j * ‖Γ a i b - Λ a i b‖) := by
    intro a
    simpa using
      (norm_finset_sum_mul_sub_sum_mul_le
        (S := (Finset.univ : Finset n))
        (B := fun b => BΓ a i b)
        (D := fun b => BΓ b a j)
        (a := fun b => Γ a i b)
        (b := fun b => Γ b a j)
        (c := fun b => Λ a i b)
        (d := fun b => Λ b a j)
        (fun b _hb => hΓ a i b)
        (fun b _hb => hΛ b a j))
  have hright : ‖rightΓ - rightΛ‖ ≤ rightBound := by
    calc
      ‖rightΓ - rightΛ‖ =
          ‖(∑ a : n, ∑ b : n, Γ a i b * Γ b a j) -
            ∑ a : n, ∑ b : n, Λ a i b * Λ b a j‖ := by
        rfl
      _ = ‖∑ a : n,
          ((∑ b : n, Γ a i b * Γ b a j) -
            ∑ b : n, Λ a i b * Λ b a j)‖ := by
        rw [Finset.sum_sub_distrib]
      _ ≤ ∑ a : n,
          ‖(∑ b : n, Γ a i b * Γ b a j) -
            ∑ b : n, Λ a i b * Λ b a j‖ :=
        norm_sum_le _ _
      _ ≤ ∑ a : n, ∑ b : n,
          (BΓ a i b * ‖Γ b a j - Λ b a j‖ +
            BΓ b a j * ‖Γ a i b - Λ a i b‖) :=
        Finset.sum_le_sum fun a _ha => hrightInner a
      _ = rightBound := by
        rfl
  have hsplit :
      (leftΓ - rightΓ) - (leftΛ - rightΛ) = (leftΓ - leftΛ) - (rightΓ - rightΛ) := by
    abel
  calc
    ‖((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
        (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) -
      ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
        (∑ a : n, ∑ b : n, Λ a i b * Λ b a j))‖ =
        ‖(leftΓ - rightΓ) - (leftΛ - rightΛ)‖ := by
      rfl
    _ = ‖(leftΓ - leftΛ) - (rightΓ - rightΛ)‖ := by
      rw [hsplit]
    _ ≤ ‖leftΓ - leftΛ‖ + ‖rightΓ - rightΛ‖ :=
      norm_sub_le _ _
    _ ≤ leftBound + rightBound :=
      add_le_add hleft hright
    _ =
      (∑ a : n, ∑ b : n,
        (BΓ a i j * ‖Γ b a b - Λ b a b‖ +
          BΓ b a b * ‖Γ a i j - Λ a i j‖)) +
      (∑ a : n, ∑ b : n,
        (BΓ a i b * ‖Γ b a j - Λ b a j‖ +
          BΓ b a j * ‖Γ a i b - Λ a i b‖)) := by
      simp [leftBound, rightBound]

/-- Entrywise Lipschitz constant for the quadratic Christoffel Ricci contraction with respect to
a uniform entrywise Christoffel-array difference bound. -/
def christoffelQuadraticRicciEntryLipschitzConst {n : Type*} [Fintype n]
    (BΓ : n → n → n → ℝ) (i j : n) : ℝ :=
  ((∑ a : n, ∑ _b : n, BΓ a i j) + (∑ a : n, ∑ b : n, BΓ b a b)) +
    ((∑ a : n, ∑ b : n, BΓ a i b) + (∑ a : n, ∑ b : n, BΓ b a j))

theorem christoffelQuadraticRicciEntryLipschitzConst_nonneg {n : Type*} [Fintype n]
    {BΓ : n → n → n → ℝ} (hBΓ : ∀ a b c, 0 ≤ BΓ a b c) (i j : n) :
    0 ≤ christoffelQuadraticRicciEntryLipschitzConst BΓ i j := by
  exact add_nonneg
    (add_nonneg
      (Finset.sum_nonneg fun a _ha => Finset.sum_nonneg fun b _hb => hBΓ a i j)
      (Finset.sum_nonneg fun a _ha => Finset.sum_nonneg fun b _hb => hBΓ b a b))
    (add_nonneg
      (Finset.sum_nonneg fun a _ha => Finset.sum_nonneg fun b _hb => hBΓ a i b)
      (Finset.sum_nonneg fun a _ha => Finset.sum_nonneg fun b _hb => hBΓ b a j))

/-- One quadratic Christoffel Ricci contraction entry is Lipschitz with respect to a uniform
entrywise Christoffel-array difference bound. -/
theorem christoffel_quadratic_ricci_entry_norm_sub_le_const {n A : Type*} [Fintype n]
    [NormedRing A] {BΓ : n → n → n → ℝ} {η : ℝ} (Γ Λ : n → n → n → A)
    (hΓ : ∀ a b c, ‖Γ a b c‖ ≤ BΓ a b c)
    (hΛ : ∀ a b c, ‖Λ a b c‖ ≤ BΓ a b c)
    (hdiff : ∀ a b c, ‖Γ a b c - Λ a b c‖ ≤ η) (i j : n) :
    ‖((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
        (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) -
      ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
        (∑ a : n, ∑ b : n, Λ a i b * Λ b a j))‖ ≤
      christoffelQuadraticRicciEntryLipschitzConst BΓ i j * η := by
  have hBΓ_nonneg : ∀ a b c, 0 ≤ BΓ a b c := by
    intro a b c
    exact (norm_nonneg _).trans (hΓ a b c)
  have hbase := christoffel_quadratic_ricci_entry_norm_sub_le Γ Λ hΓ hΛ i j
  refine hbase.trans ?_
  calc
    (∑ a : n, ∑ b : n,
        (BΓ a i j * ‖Γ b a b - Λ b a b‖ +
          BΓ b a b * ‖Γ a i j - Λ a i j‖)) +
      (∑ a : n, ∑ b : n,
        (BΓ a i b * ‖Γ b a j - Λ b a j‖ +
          BΓ b a j * ‖Γ a i b - Λ a i b‖))
        ≤
      (∑ a : n, ∑ b : n, (BΓ a i j * η + BΓ b a b * η)) +
        (∑ a : n, ∑ b : n, (BΓ a i b * η + BΓ b a j * η)) := by
      exact add_le_add
        (Finset.sum_le_sum fun a _ha =>
          Finset.sum_le_sum fun b _hb =>
            add_le_add
              (mul_le_mul_of_nonneg_left (hdiff b a b) (hBΓ_nonneg a i j))
              (mul_le_mul_of_nonneg_left (hdiff a i j) (hBΓ_nonneg b a b)))
        (Finset.sum_le_sum fun a _ha =>
          Finset.sum_le_sum fun b _hb =>
            add_le_add
              (mul_le_mul_of_nonneg_left (hdiff b a j) (hBΓ_nonneg a i b))
              (mul_le_mul_of_nonneg_left (hdiff a i b) (hBΓ_nonneg b a j)))
    _ =
      christoffelQuadraticRicciEntryLipschitzConst BΓ i j * η := by
      have h1 :
          (∑ a : n, ∑ b : n, BΓ a i j * η) =
            (∑ a : n, ∑ b : n, BΓ a i j) * η := by
        simp_rw [Finset.sum_mul]
      have h2 :
          (∑ a : n, ∑ b : n, BΓ b a b * η) =
            (∑ a : n, ∑ b : n, BΓ b a b) * η := by
        simp_rw [Finset.sum_mul]
      have h3 :
          (∑ a : n, ∑ b : n, BΓ a i b * η) =
            (∑ a : n, ∑ b : n, BΓ a i b) * η := by
        simp_rw [Finset.sum_mul]
      have h4 :
          (∑ a : n, ∑ b : n, BΓ b a j * η) =
            (∑ a : n, ∑ b : n, BΓ b a j) * η := by
        simp_rw [Finset.sum_mul]
      calc
        (∑ a : n, ∑ b : n, (BΓ a i j * η + BΓ b a b * η)) +
          (∑ a : n, ∑ b : n, (BΓ a i b * η + BΓ b a j * η)) =
            ((∑ a : n, ∑ b : n, BΓ a i j * η) +
              (∑ a : n, ∑ b : n, BΓ b a b * η)) +
            ((∑ a : n, ∑ b : n, BΓ a i b * η) +
              (∑ a : n, ∑ b : n, BΓ b a j * η)) := by
          simp [Finset.sum_add_distrib]
        _ =
            ((∑ a : n, ∑ b : n, BΓ a i j) * η +
              (∑ a : n, ∑ b : n, BΓ b a b) * η) +
            ((∑ a : n, ∑ b : n, BΓ a i b) * η +
              (∑ a : n, ∑ b : n, BΓ b a j) * η) := by
          rw [h1, h2, h3, h4]
        _ = christoffelQuadraticRicciEntryLipschitzConst BΓ i j * η := by
          simp [christoffelQuadraticRicciEntryLipschitzConst]
          ring

/-- Matrix-norm Lipschitz constant for the full quadratic Christoffel Ricci contraction with
respect to a uniform entrywise Christoffel-array difference bound. -/
def christoffelQuadraticRicciLipschitzConst {n : Type*} [Fintype n]
    (BΓ : n → n → n → ℝ) : ℝ :=
  ∑ i : n, ∑ j : n, christoffelQuadraticRicciEntryLipschitzConst BΓ i j

theorem christoffelQuadraticRicciLipschitzConst_nonneg {n : Type*} [Fintype n]
    {BΓ : n → n → n → ℝ} (hBΓ : ∀ a b c, 0 ≤ BΓ a b c) :
    0 ≤ christoffelQuadraticRicciLipschitzConst BΓ := by
  exact Finset.sum_nonneg fun i _hi =>
    Finset.sum_nonneg fun j _hj =>
      christoffelQuadraticRicciEntryLipschitzConst_nonneg hBΓ i j

/-- The full finite Ricci-coordinate quadratic Christoffel contraction is pointwise Lipschitz in
the elementwise matrix norm on bounded Christoffel arrays. -/
theorem christoffel_quadratic_ricci_norm_sub_le {n A : Type*} [Fintype n] [NormedRing A]
    {BΓ : n → n → n → ℝ} (Γ Λ : n → n → n → A)
    (hΓ : ∀ a b c, ‖Γ a b c‖ ≤ BΓ a b c)
    (hΛ : ∀ a b c, ‖Λ a b c‖ ≤ BΓ a b c) :
    ‖((fun i j =>
        (∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
          (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) : Matrix n n A) -
      ((fun i j =>
        (∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
          (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)) : Matrix n n A)‖ ≤
      ∑ i : n, ∑ j : n,
        ((∑ a : n, ∑ b : n,
          (BΓ a i j * ‖Γ b a b - Λ b a b‖ +
            BΓ b a b * ‖Γ a i j - Λ a i j‖)) +
        (∑ a : n, ∑ b : n,
          (BΓ a i b * ‖Γ b a j - Λ b a j‖ +
            BΓ b a j * ‖Γ a i b - Λ a i b‖))) := by
  classical
  let entryBound : n → n → ℝ := fun i j =>
    (∑ a : n, ∑ b : n,
      (BΓ a i j * ‖Γ b a b - Λ b a b‖ +
        BΓ b a b * ‖Γ a i j - Λ a i j‖)) +
    (∑ a : n, ∑ b : n,
      (BΓ a i b * ‖Γ b a j - Λ b a j‖ +
        BΓ b a j * ‖Γ a i b - Λ a i b‖))
  have hentry : ∀ i j,
      ‖((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
          (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) -
        ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
          (∑ a : n, ∑ b : n, Λ a i b * Λ b a j))‖ ≤ entryBound i j := by
    intro i j
    simpa [entryBound] using christoffel_quadratic_ricci_entry_norm_sub_le Γ Λ hΓ hΛ i j
  have hentry_nonneg : ∀ i j, 0 ≤ entryBound i j := by
    intro i j
    exact (norm_nonneg _).trans (hentry i j)
  have hrow_nonneg : ∀ i, 0 ≤ ∑ j : n, entryBound i j := by
    intro i
    exact Finset.sum_nonneg fun j _hj => hentry_nonneg i j
  have htotal_nonneg : 0 ≤ ∑ i : n, ∑ j : n, entryBound i j :=
    Finset.sum_nonneg fun i _hi => hrow_nonneg i
  have hnorm :
      ‖((fun i j =>
          (∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
            (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) : Matrix n n A) -
        ((fun i j =>
          (∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
            (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)) : Matrix n n A)‖ ≤
        ∑ i : n, ∑ j : n, entryBound i j := by
    refine (Matrix.norm_le_iff htotal_nonneg).2 ?_
    intro i j
    calc
      ‖(((fun i j =>
          (∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
            (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) : Matrix n n A) -
        ((fun i j =>
          (∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
            (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)) : Matrix n n A)) i j‖ =
          ‖((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
              (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) -
            ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
              (∑ a : n, ∑ b : n, Λ a i b * Λ b a j))‖ := rfl
      _ ≤ entryBound i j := hentry i j
      _ ≤ ∑ j : n, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hentry_nonneg i k) (Finset.mem_univ j)
      _ ≤ ∑ i : n, ∑ j : n, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hrow_nonneg k) (Finset.mem_univ i)
  simpa [entryBound] using hnorm

/-- The full finite Ricci-coordinate quadratic Christoffel contraction is Lipschitz in the
elementwise matrix norm with respect to a uniform entrywise Christoffel-array difference bound. -/
theorem christoffel_quadratic_ricci_norm_sub_le_const {n A : Type*} [Fintype n]
    [NormedRing A] {BΓ : n → n → n → ℝ} {η : ℝ} (Γ Λ : n → n → n → A)
    (hΓ : ∀ a b c, ‖Γ a b c‖ ≤ BΓ a b c)
    (hΛ : ∀ a b c, ‖Λ a b c‖ ≤ BΓ a b c)
    (hη : 0 ≤ η) (hdiff : ∀ a b c, ‖Γ a b c - Λ a b c‖ ≤ η) :
    ‖((fun i j =>
        (∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
          (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) : Matrix n n A) -
      ((fun i j =>
        (∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
          (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)) : Matrix n n A)‖ ≤
      christoffelQuadraticRicciLipschitzConst BΓ * η := by
  classical
  have hBΓ_nonneg : ∀ a b c, 0 ≤ BΓ a b c := by
    intro a b c
    exact (norm_nonneg _).trans (hΓ a b c)
  let entryBound : n → n → ℝ :=
    fun i j => christoffelQuadraticRicciEntryLipschitzConst BΓ i j * η
  have hentry : ∀ i j,
      ‖((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
          (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) -
        ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
          (∑ a : n, ∑ b : n, Λ a i b * Λ b a j))‖ ≤ entryBound i j := by
    intro i j
    simpa [entryBound] using
      christoffel_quadratic_ricci_entry_norm_sub_le_const Γ Λ hΓ hΛ hdiff i j
  have hentry_nonneg : ∀ i j, 0 ≤ entryBound i j := by
    intro i j
    exact mul_nonneg (christoffelQuadraticRicciEntryLipschitzConst_nonneg hBΓ_nonneg i j) hη
  have hrow_nonneg : ∀ i, 0 ≤ ∑ j : n, entryBound i j := by
    intro i
    exact Finset.sum_nonneg fun j _hj => hentry_nonneg i j
  have htotal_nonneg : 0 ≤ ∑ i : n, ∑ j : n, entryBound i j :=
    Finset.sum_nonneg fun i _hi => hrow_nonneg i
  have hnorm :
      ‖((fun i j =>
          (∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
            (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) : Matrix n n A) -
        ((fun i j =>
          (∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
            (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)) : Matrix n n A)‖ ≤
        ∑ i : n, ∑ j : n, entryBound i j := by
    refine (Matrix.norm_le_iff htotal_nonneg).2 ?_
    intro i j
    calc
      ‖(((fun i j =>
          (∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
            (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) : Matrix n n A) -
        ((fun i j =>
          (∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
            (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)) : Matrix n n A)) i j‖ =
          ‖((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
              (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) -
            ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
              (∑ a : n, ∑ b : n, Λ a i b * Λ b a j))‖ := rfl
      _ ≤ entryBound i j := hentry i j
      _ ≤ ∑ j : n, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hentry_nonneg i k) (Finset.mem_univ j)
      _ ≤ ∑ i : n, ∑ j : n, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hrow_nonneg k) (Finset.mem_univ i)
  calc
    ‖((fun i j =>
        (∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
          (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) : Matrix n n A) -
      ((fun i j =>
        (∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
          (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)) : Matrix n n A)‖ ≤
        ∑ i : n, ∑ j : n, entryBound i j := hnorm
    _ = christoffelQuadraticRicciLipschitzConst BΓ * η := by
      simp_rw [entryBound, christoffelQuadraticRicciLipschitzConst, Finset.sum_mul]

/-- The schematic Ricci-DeTurck coordinate entry built from an inverse principal contraction and
a supplied Christoffel array is pointwise Lipschitz on bounded inputs.  This is the algebraic
combination step before substituting the inverse-metric Christoffel formula. -/
theorem ricciDeTurck_schematic_from_christoffel_entry_norm_sub_le {n 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ}
    {HB : n → n → n → n → ℝ} {ΓB : n → n → n → ℝ}
    (M N : Matrix n n 𝕜) (H K : n → n → n → n → 𝕜)
    (Γ Λ : n → n → n → 𝕜)
    (hM : ∀ a b, ‖M a b‖ ≤ C a b) (hN : ∀ a b, ‖N a b‖ ≤ C a b)
    (hK : ∀ a b i j, ‖K a b i j‖ ≤ HB a b i j)
    (hΓ : ∀ a b c, ‖Γ a b c‖ ≤ ΓB a b c)
    (hΛ : ∀ a b c, ‖Λ a b c‖ ≤ ΓB a b c)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖)
    (i j : n) :
    ‖((∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
        ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
          (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) -
      ((∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
        ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
          (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)))‖ ≤
      (∑ a : n, ∑ b : n,
        (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * ‖H a b i j - K a b i j‖ +
          HB a b i j * matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N a b)) +
      ((∑ a : n, ∑ b : n,
        (ΓB a i j * ‖Γ b a b - Λ b a b‖ +
          ΓB b a b * ‖Γ a i j - Λ a i j‖)) +
      (∑ a : n, ∑ b : n,
        (ΓB a i b * ‖Γ b a j - Λ b a j‖ +
          ΓB b a j * ‖Γ a i b - Λ a i b‖))) := by
  classical
  let principalM : 𝕜 := ∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j
  let principalN : 𝕜 := ∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j
  let quadraticΓ : 𝕜 :=
    (∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
      (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)
  let quadraticΛ : 𝕜 :=
    (∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
      (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)
  let principalBound : ℝ := ∑ a : n, ∑ b : n,
    (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * ‖H a b i j - K a b i j‖ +
      HB a b i j * matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N a b)
  let quadraticBound : ℝ :=
    (∑ a : n, ∑ b : n,
      (ΓB a i j * ‖Γ b a b - Λ b a b‖ +
        ΓB b a b * ‖Γ a i j - Λ a i j‖)) +
    (∑ a : n, ∑ b : n,
      (ΓB a i b * ‖Γ b a j - Λ b a j‖ +
        ΓB b a j * ‖Γ a i b - Λ a i b‖))
  have hprincipal : ‖principalM - principalN‖ ≤ principalBound := by
    simpa [principalM, principalN, principalBound] using
      matrix_inv_two_index_contract_entry_norm_sub_le M N H K hM hN hK hδpos hdetM hdetN i j
  have hquadratic : ‖quadraticΓ - quadraticΛ‖ ≤ quadraticBound := by
    simpa [quadraticΓ, quadraticΛ, quadraticBound] using
      christoffel_quadratic_ricci_entry_norm_sub_le Γ Λ hΓ hΛ i j
  have hsplit :
      (principalM + quadraticΓ) - (principalN + quadraticΛ) =
        (principalM - principalN) + (quadraticΓ - quadraticΛ) := by
    abel
  calc
    ‖((∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
        ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
          (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) -
      ((∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
        ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
          (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)))‖ =
        ‖(principalM + quadraticΓ) - (principalN + quadraticΛ)‖ := by
      rfl
    _ = ‖(principalM - principalN) + (quadraticΓ - quadraticΛ)‖ := by
      rw [hsplit]
    _ ≤ ‖principalM - principalN‖ + ‖quadraticΓ - quadraticΛ‖ :=
      norm_add_le _ _
    _ ≤ principalBound + quadraticBound :=
      add_le_add hprincipal hquadratic
    _ =
      (∑ a : n, ∑ b : n,
        (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * ‖H a b i j - K a b i j‖ +
          HB a b i j * matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N a b)) +
      ((∑ a : n, ∑ b : n,
        (ΓB a i j * ‖Γ b a b - Λ b a b‖ +
          ΓB b a b * ‖Γ a i j - Λ a i j‖)) +
      (∑ a : n, ∑ b : n,
        (ΓB a i b * ‖Γ b a j - Λ b a j‖ +
          ΓB b a j * ‖Γ a i b - Λ a i b‖))) := by
      simp [principalBound, quadraticBound]

/-- The schematic Ricci-DeTurck coordinate entry built from an inverse principal contraction and
a supplied Christoffel array is Lipschitz in the metric matrix norm, the principal coefficient
matrix norm, and a uniform Christoffel-array entry difference bound. -/
theorem ricciDeTurck_schematic_from_christoffel_entry_norm_sub_le_const {n 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ}
    {HB : n → n → n → n → ℝ} {ΓB : n → n → n → ℝ} {ηγ : ℝ}
    (M N : Matrix n n 𝕜) (H K : n → n → n → n → 𝕜)
    (Γ Λ : n → n → n → 𝕜)
    (hM : ∀ a b, ‖M a b‖ ≤ C a b) (hN : ∀ a b, ‖N a b‖ ≤ C a b)
    (hK : ∀ a b i j, ‖K a b i j‖ ≤ HB a b i j)
    (hΓ : ∀ a b c, ‖Γ a b c‖ ≤ ΓB a b c)
    (hΛ : ∀ a b c, ‖Λ a b c‖ ≤ ΓB a b c)
    (hΓdiff : ∀ a b c, ‖Γ a b c - Λ a b c‖ ≤ ηγ)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖)
    (i j : n) :
    ‖((∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
        ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
          (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) -
      ((∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
        ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
          (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)))‖ ≤
      (matrixInvTwoIndexContractCoeffDiffConst (𝕜 := 𝕜) δ C *
          ‖((fun a b => H a b i j) : Matrix n n 𝕜) -
            ((fun a b => K a b i j) : Matrix n n 𝕜)‖ +
        matrixInvTwoIndexContractMetricDiffConst (𝕜 := 𝕜) δ C HB i j * ‖M - N‖) +
        christoffelQuadraticRicciEntryLipschitzConst ΓB i j * ηγ := by
  classical
  let principalM : 𝕜 := ∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j
  let principalN : 𝕜 := ∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j
  let quadraticΓ : 𝕜 :=
    (∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
      (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)
  let quadraticΛ : 𝕜 :=
    (∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
      (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)
  let principalBound : ℝ :=
    matrixInvTwoIndexContractCoeffDiffConst (𝕜 := 𝕜) δ C *
        ‖((fun a b => H a b i j) : Matrix n n 𝕜) -
          ((fun a b => K a b i j) : Matrix n n 𝕜)‖ +
      matrixInvTwoIndexContractMetricDiffConst (𝕜 := 𝕜) δ C HB i j * ‖M - N‖
  let quadraticBound : ℝ := christoffelQuadraticRicciEntryLipschitzConst ΓB i j * ηγ
  have hprincipal : ‖principalM - principalN‖ ≤ principalBound := by
    simpa [principalM, principalN, principalBound] using
      matrix_inv_two_index_contract_entry_norm_sub_le_const
        M N H K hM hN hK hδpos hdetM hdetN i j
  have hquadratic : ‖quadraticΓ - quadraticΛ‖ ≤ quadraticBound := by
    simpa [quadraticΓ, quadraticΛ, quadraticBound] using
      christoffel_quadratic_ricci_entry_norm_sub_le_const Γ Λ hΓ hΛ hΓdiff i j
  have hsplit :
      (principalM + quadraticΓ) - (principalN + quadraticΛ) =
        (principalM - principalN) + (quadraticΓ - quadraticΛ) := by
    abel
  calc
    ‖((∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
        ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
          (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) -
      ((∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
        ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
          (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)))‖ =
        ‖(principalM + quadraticΓ) - (principalN + quadraticΛ)‖ := by
      rfl
    _ = ‖(principalM - principalN) + (quadraticΓ - quadraticΛ)‖ := by
      rw [hsplit]
    _ ≤ ‖principalM - principalN‖ + ‖quadraticΓ - quadraticΛ‖ :=
      norm_add_le _ _
    _ ≤ principalBound + quadraticBound :=
      add_le_add hprincipal hquadratic
    _ =
      (matrixInvTwoIndexContractCoeffDiffConst (𝕜 := 𝕜) δ C *
          ‖((fun a b => H a b i j) : Matrix n n 𝕜) -
            ((fun a b => K a b i j) : Matrix n n 𝕜)‖ +
        matrixInvTwoIndexContractMetricDiffConst (𝕜 := 𝕜) δ C HB i j * ‖M - N‖) +
        christoffelQuadraticRicciEntryLipschitzConst ΓB i j * ηγ := by
      simp [principalBound, quadraticBound]

/-- The matrix-valued schematic Ricci-DeTurck expression built from inverse principal contractions
and supplied Christoffel arrays is pointwise Lipschitz in the elementwise matrix norm. -/
theorem ricciDeTurck_schematic_from_christoffel_norm_sub_le {n 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ}
    {HB : n → n → n → n → ℝ} {ΓB : n → n → n → ℝ}
    (M N : Matrix n n 𝕜) (H K : n → n → n → n → 𝕜)
    (Γ Λ : n → n → n → 𝕜)
    (hM : ∀ a b, ‖M a b‖ ≤ C a b) (hN : ∀ a b, ‖N a b‖ ≤ C a b)
    (hK : ∀ a b i j, ‖K a b i j‖ ≤ HB a b i j)
    (hΓ : ∀ a b c, ‖Γ a b c‖ ≤ ΓB a b c)
    (hΛ : ∀ a b c, ‖Λ a b c‖ ≤ ΓB a b c)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖) :
    ‖((fun i j =>
        (∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
          ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
            (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) : Matrix n n 𝕜) -
      ((fun i j =>
        (∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
          ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
            (∑ a : n, ∑ b : n, Λ a i b * Λ b a j))) : Matrix n n 𝕜)‖ ≤
      ∑ i : n, ∑ j : n,
        ((∑ a : n, ∑ b : n,
          (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * ‖H a b i j - K a b i j‖ +
            HB a b i j * matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N a b)) +
        ((∑ a : n, ∑ b : n,
          (ΓB a i j * ‖Γ b a b - Λ b a b‖ +
            ΓB b a b * ‖Γ a i j - Λ a i j‖)) +
        (∑ a : n, ∑ b : n,
          (ΓB a i b * ‖Γ b a j - Λ b a j‖ +
            ΓB b a j * ‖Γ a i b - Λ a i b‖)))) := by
  classical
  let entryBound : n → n → ℝ := fun i j =>
    (∑ a : n, ∑ b : n,
      (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * ‖H a b i j - K a b i j‖ +
        HB a b i j * matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N a b)) +
    ((∑ a : n, ∑ b : n,
      (ΓB a i j * ‖Γ b a b - Λ b a b‖ +
        ΓB b a b * ‖Γ a i j - Λ a i j‖)) +
    (∑ a : n, ∑ b : n,
      (ΓB a i b * ‖Γ b a j - Λ b a j‖ +
        ΓB b a j * ‖Γ a i b - Λ a i b‖)))
  have hentry : ∀ i j,
      ‖((∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
          ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
            (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) -
        ((∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
          ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
            (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)))‖ ≤ entryBound i j := by
    intro i j
    simpa [entryBound] using
      ricciDeTurck_schematic_from_christoffel_entry_norm_sub_le
        M N H K Γ Λ hM hN hK hΓ hΛ hδpos hdetM hdetN i j
  have hentry_nonneg : ∀ i j, 0 ≤ entryBound i j := by
    intro i j
    exact (norm_nonneg _).trans (hentry i j)
  have hrow_nonneg : ∀ i, 0 ≤ ∑ j : n, entryBound i j := by
    intro i
    exact Finset.sum_nonneg fun j _hj => hentry_nonneg i j
  have htotal_nonneg : 0 ≤ ∑ i : n, ∑ j : n, entryBound i j :=
    Finset.sum_nonneg fun i _hi => hrow_nonneg i
  have hnorm :
      ‖((fun i j =>
          (∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
            ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
              (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) : Matrix n n 𝕜) -
        ((fun i j =>
          (∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
            ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
              (∑ a : n, ∑ b : n, Λ a i b * Λ b a j))) : Matrix n n 𝕜)‖ ≤
        ∑ i : n, ∑ j : n, entryBound i j := by
    refine (Matrix.norm_le_iff htotal_nonneg).2 ?_
    intro i j
    calc
      ‖(((fun i j =>
          (∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
            ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
              (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) : Matrix n n 𝕜) -
        ((fun i j =>
          (∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
            ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
              (∑ a : n, ∑ b : n, Λ a i b * Λ b a j))) : Matrix n n 𝕜)) i j‖ =
          ‖((∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
              ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
                (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) -
            ((∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
              ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
                (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)))‖ := rfl
      _ ≤ entryBound i j := hentry i j
      _ ≤ ∑ j : n, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hentry_nonneg i k) (Finset.mem_univ j)
      _ ≤ ∑ i : n, ∑ j : n, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hrow_nonneg k) (Finset.mem_univ i)
  simpa [entryBound] using hnorm

/-- The matrix-valued schematic Ricci-DeTurck expression built from inverse principal contractions
and supplied Christoffel arrays is Lipschitz in the metric matrix norm, the principal coefficient
matrix norms, and a uniform Christoffel-array entry difference bound. -/
theorem ricciDeTurck_schematic_from_christoffel_norm_sub_le_const {n 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ}
    {HB : n → n → n → n → ℝ} {ΓB : n → n → n → ℝ} {ηγ : ℝ}
    (M N : Matrix n n 𝕜) (H K : n → n → n → n → 𝕜)
    (Γ Λ : n → n → n → 𝕜)
    (hM : ∀ a b, ‖M a b‖ ≤ C a b) (hN : ∀ a b, ‖N a b‖ ≤ C a b)
    (hK : ∀ a b i j, ‖K a b i j‖ ≤ HB a b i j)
    (hΓ : ∀ a b c, ‖Γ a b c‖ ≤ ΓB a b c)
    (hΛ : ∀ a b c, ‖Λ a b c‖ ≤ ΓB a b c)
    (hΓdiff : ∀ a b c, ‖Γ a b c - Λ a b c‖ ≤ ηγ)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖) :
    ‖((fun i j =>
        (∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
          ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
            (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) : Matrix n n 𝕜) -
      ((fun i j =>
        (∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
          ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
            (∑ a : n, ∑ b : n, Λ a i b * Λ b a j))) : Matrix n n 𝕜)‖ ≤
      ∑ i : n, ∑ j : n,
        ((matrixInvTwoIndexContractCoeffDiffConst (𝕜 := 𝕜) δ C *
            ‖((fun a b => H a b i j) : Matrix n n 𝕜) -
              ((fun a b => K a b i j) : Matrix n n 𝕜)‖ +
          matrixInvTwoIndexContractMetricDiffConst (𝕜 := 𝕜) δ C HB i j * ‖M - N‖) +
          christoffelQuadraticRicciEntryLipschitzConst ΓB i j * ηγ) := by
  classical
  let entryBound : n → n → ℝ := fun i j =>
    (matrixInvTwoIndexContractCoeffDiffConst (𝕜 := 𝕜) δ C *
        ‖((fun a b => H a b i j) : Matrix n n 𝕜) -
          ((fun a b => K a b i j) : Matrix n n 𝕜)‖ +
      matrixInvTwoIndexContractMetricDiffConst (𝕜 := 𝕜) δ C HB i j * ‖M - N‖) +
      christoffelQuadraticRicciEntryLipschitzConst ΓB i j * ηγ
  have hentry : ∀ i j,
      ‖((∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
          ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
            (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) -
        ((∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
          ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
            (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)))‖ ≤ entryBound i j := by
    intro i j
    simpa [entryBound] using
      ricciDeTurck_schematic_from_christoffel_entry_norm_sub_le_const
        M N H K Γ Λ hM hN hK hΓ hΛ hΓdiff hδpos hdetM hdetN i j
  have hentry_nonneg : ∀ i j, 0 ≤ entryBound i j := by
    intro i j
    exact (norm_nonneg _).trans (hentry i j)
  have hrow_nonneg : ∀ i, 0 ≤ ∑ j : n, entryBound i j := by
    intro i
    exact Finset.sum_nonneg fun j _hj => hentry_nonneg i j
  have htotal_nonneg : 0 ≤ ∑ i : n, ∑ j : n, entryBound i j :=
    Finset.sum_nonneg fun i _hi => hrow_nonneg i
  have hnorm :
      ‖((fun i j =>
          (∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
            ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
              (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) : Matrix n n 𝕜) -
        ((fun i j =>
          (∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
            ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
              (∑ a : n, ∑ b : n, Λ a i b * Λ b a j))) : Matrix n n 𝕜)‖ ≤
        ∑ i : n, ∑ j : n, entryBound i j := by
    refine (Matrix.norm_le_iff htotal_nonneg).2 ?_
    intro i j
    calc
      ‖(((fun i j =>
          (∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
            ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
              (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) : Matrix n n 𝕜) -
        ((fun i j =>
          (∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
            ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
              (∑ a : n, ∑ b : n, Λ a i b * Λ b a j))) : Matrix n n 𝕜)) i j‖ =
          ‖((∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
              ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
                (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) -
            ((∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
              ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
                (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)))‖ := rfl
      _ ≤ entryBound i j := hentry i j
      _ ≤ ∑ j : n, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hentry_nonneg i k) (Finset.mem_univ j)
      _ ≤ ∑ i : n, ∑ j : n, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hrow_nonneg k) (Finset.mem_univ i)
  simpa [entryBound] using hnorm

/-- A supplied-Christoffel schematic Ricci-DeTurck coordinate entry has an explicit bounded
parabolic `C^{0,α}` estimate from explicit metric, principal-coefficient, and Christoffel-array
estimates. -/
theorem ricciDeTurck_schematic_from_christoffel_entry_with {n 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] {δ : ℝ}
    {MB MH : n → n → ℝ} {HB HH : n → n → n → n → ℝ}
    {ΓB ΓH : n → n → n → ℝ}
    {M : ℝ × X → Matrix n n 𝕜} {H : ℝ × X → n → n → n → n → 𝕜}
    {Γ : ℝ × X → n → n → n → 𝕜}
    (hMH : ∀ a b, 0 ≤ MH a b) (hΓB : ∀ a b c, 0 ≤ ΓB a b c)
    (hM : ∀ a b, ParabolicC0AlphaWith (MB a b) (MH a b) α (fun z => M z a b) s)
    (hH : ∀ a b i j, ParabolicC0AlphaWith (HB a b i j) (HH a b i j) α
      (fun z => H z a b i j) s)
    (hΓ : ∀ a b c, ParabolicC0AlphaWith (ΓB a b c) (ΓH a b c) α
      (fun z => Γ z a b c) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (i j : n) :
    ParabolicC0AlphaWith
      (matrixInvTwoIndexContractEntryBoundConst (𝕜 := 𝕜) δ MB HB i j +
        christoffelQuadraticRicciEntryBoundConst ΓB i j)
      (matrixInvTwoIndexContractEntryHolderConst (𝕜 := 𝕜) δ MB MH HB HH i j +
        christoffelQuadraticRicciEntryHolderConst ΓB ΓH i j)
      α
      (fun z =>
        (∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * H z a b i j) +
          ((∑ a : n, ∑ b : n, Γ z a i j * Γ z b a b) -
            (∑ a : n, ∑ b : n, Γ z a i b * Γ z b a j))) s := by
  have hprincipal :
      ParabolicC0AlphaWith
        (matrixInvTwoIndexContractEntryBoundConst (𝕜 := 𝕜) δ MB HB i j)
        (matrixInvTwoIndexContractEntryHolderConst (𝕜 := 𝕜) δ MB MH HB HH i j)
        α
        (fun z => ∑ a : n, ∑ b : n,
          ((M z)⁻¹ : Matrix n n 𝕜) a b * H z a b i j) s :=
    matrix_inv_two_index_contract_entry_with (M := M) (T := H)
      hMH hM hH hδpos hdet i j
  have hquadratic :
      ParabolicC0AlphaWith
        (christoffelQuadraticRicciEntryBoundConst ΓB i j)
        (christoffelQuadraticRicciEntryHolderConst ΓB ΓH i j)
        α
        (fun z =>
          (∑ a : n, ∑ b : n, Γ z a i j * Γ z b a b) -
            (∑ a : n, ∑ b : n, Γ z a i b * Γ z b a j)) s :=
    christoffel_quadratic_ricci_entry_with hΓB hΓ i j
  exact hprincipal.add hquadratic

/-- The supplied-Christoffel schematic Ricci-DeTurck RHS has an explicit matrix-valued bounded
parabolic `C^{0,α}` estimate from explicit metric, principal-coefficient, and Christoffel-array
estimates. -/
theorem ricciDeTurck_schematic_from_christoffel_with {n 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] {δ : ℝ}
    {MB MH : n → n → ℝ} {HB HH : n → n → n → n → ℝ}
    {ΓB ΓH : n → n → n → ℝ}
    {M : ℝ × X → Matrix n n 𝕜} {H : ℝ × X → n → n → n → n → 𝕜}
    {Γ : ℝ × X → n → n → n → 𝕜}
    (hMH : ∀ a b, 0 ≤ MH a b)
    (hHB : ∀ a b i j, 0 ≤ HB a b i j) (hHH : ∀ a b i j, 0 ≤ HH a b i j)
    (hΓB : ∀ a b c, 0 ≤ ΓB a b c) (hΓH : ∀ a b c, 0 ≤ ΓH a b c)
    (hM : ∀ a b, ParabolicC0AlphaWith (MB a b) (MH a b) α (fun z => M z a b) s)
    (hH : ∀ a b i j, ParabolicC0AlphaWith (HB a b i j) (HH a b i j) α
      (fun z => H z a b i j) s)
    (hΓ : ∀ a b c, ParabolicC0AlphaWith (ΓB a b c) (ΓH a b c) α
      (fun z => Γ z a b c) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaWith
      (∑ i : n, ∑ j : n,
        (matrixInvTwoIndexContractEntryBoundConst (𝕜 := 𝕜) δ MB HB i j +
          christoffelQuadraticRicciEntryBoundConst ΓB i j))
      (∑ i : n, ∑ j : n,
        (matrixInvTwoIndexContractEntryHolderConst (𝕜 := 𝕜) δ MB MH HB HH i j +
          christoffelQuadraticRicciEntryHolderConst ΓB ΓH i j))
      α
      (fun z : ℝ × X =>
        (fun i j =>
          (∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * H z a b i j) +
            ((∑ a : n, ∑ b : n, Γ z a i j * Γ z b a b) -
              (∑ a : n, ∑ b : n, Γ z a i b * Γ z b a j)) :
          Matrix n n 𝕜)) s := by
  refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
  · intro i
    exact Finset.sum_nonneg fun j _hj =>
      add_nonneg
        (matrixInvTwoIndexContractEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos MB hHB i j)
        (christoffelQuadraticRicciEntryBoundConst_nonneg hΓB i j)
  · intro i
    exact Finset.sum_nonneg fun j _hj =>
      add_nonneg
        (matrixInvTwoIndexContractEntryHolderConst_nonneg (𝕜 := 𝕜) hMH hδpos hHB hHH i j)
        (christoffelQuadraticRicciEntryHolderConst_nonneg hΓB hΓH i j)
  · intro i
    refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
    · intro j
      exact add_nonneg
        (matrixInvTwoIndexContractEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos MB hHB i j)
        (christoffelQuadraticRicciEntryBoundConst_nonneg hΓB i j)
    · intro j
      exact add_nonneg
        (matrixInvTwoIndexContractEntryHolderConst_nonneg (𝕜 := 𝕜) hMH hδpos hHB hHH i j)
        (christoffelQuadraticRicciEntryHolderConst_nonneg hΓB hΓH i j)
    · intro j
      exact ricciDeTurck_schematic_from_christoffel_entry_with
        hMH hΓB hM hH hΓ hδpos hdet i j

/-- The primitive-input schematic Ricci-DeTurck coordinate entry has an explicit bounded
parabolic `C^{0,α}` estimate from explicit metric, first-derivative, and second-derivative
coefficient estimates. -/
theorem ricciDeTurck_schematic_entry_with {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {MB MH : n → n → ℝ}
    {DB DH : n → n → n → ℝ} {HB HH : n → n → n → n → ℝ}
    {M : ℝ × X → Matrix n n 𝕜} {D : ℝ × X → n → n → n → 𝕜}
    {H : ℝ × X → n → n → n → n → 𝕜}
    (hMH : ∀ a b, 0 ≤ MH a b) (hDB : ∀ a b c, 0 ≤ DB a b c)
    (hM : ∀ a b, ParabolicC0AlphaWith (MB a b) (MH a b) α (fun z => M z a b) s)
    (hD : ∀ a b c, ParabolicC0AlphaWith (DB a b c) (DH a b c) α
      (fun z => D z a b c) s)
    (hH : ∀ a b i j, ParabolicC0AlphaWith (HB a b i j) (HH a b i j) α
      (fun z => H z a b i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (i j : n) :
    ParabolicC0AlphaWith
      (matrixInvTwoIndexContractEntryBoundConst (𝕜 := 𝕜) δ MB HB i j +
        christoffelQuadraticRicciEntryBoundConst
          (fun a b c => matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ MB DB a b c)
          i j)
      (matrixInvTwoIndexContractEntryHolderConst (𝕜 := 𝕜) δ MB MH HB HH i j +
        christoffelQuadraticRicciEntryHolderConst
          (fun a b c => matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ MB DB a b c)
          (fun a b c => matrixInvChristoffelEntryHolderConst (𝕜 := 𝕜) δ MB MH DB DH a b c)
          i j)
      α
      (fun z =>
        let Γ : n → n → n → 𝕜 := fun a b c =>
          (2 : 𝕜)⁻¹ *
            ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) a l *
              (D z b c l + D z c b l - D z l b c)
        (∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * H z a b i j) +
          ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
            (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) s := by
  classical
  let Γ : ℝ × X → n → n → n → 𝕜 := fun z a b c =>
    (2 : 𝕜)⁻¹ *
      ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) a l *
        (D z b c l + D z c b l - D z l b c)
  let ΓB : n → n → n → ℝ := fun a b c =>
    matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ MB DB a b c
  let ΓH : n → n → n → ℝ := fun a b c =>
    matrixInvChristoffelEntryHolderConst (𝕜 := 𝕜) δ MB MH DB DH a b c
  have hΓB_nonneg : ∀ a b c, 0 ≤ ΓB a b c := by
    intro a b c
    exact matrixInvChristoffelEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos MB hDB a b c
  have hΓ : ∀ a b c, ParabolicC0AlphaWith (ΓB a b c) (ΓH a b c) α
      (fun z => Γ z a b c) s := by
    intro a b c
    simpa [Γ, ΓB, ΓH] using
      matrix_inv_christoffel_entry_with (M := M) (D := D)
        hMH hM hD hδpos hdet a b c
  simpa [Γ, ΓB, ΓH] using
    ricciDeTurck_schematic_from_christoffel_entry_with
      hMH hΓB_nonneg hM hH hΓ hδpos hdet i j

/-- The primitive-input schematic Ricci-DeTurck RHS has an explicit matrix-valued bounded
parabolic `C^{0,α}` estimate from explicit metric, first-derivative, and second-derivative
coefficient estimates. -/
theorem ricciDeTurck_schematic_with {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {MB MH : n → n → ℝ}
    {DB DH : n → n → n → ℝ} {HB HH : n → n → n → n → ℝ}
    {M : ℝ × X → Matrix n n 𝕜} {D : ℝ × X → n → n → n → 𝕜}
    {H : ℝ × X → n → n → n → n → 𝕜}
    (hMH : ∀ a b, 0 ≤ MH a b) (hDB : ∀ a b c, 0 ≤ DB a b c)
    (hDH : ∀ a b c, 0 ≤ DH a b c)
    (hHB : ∀ a b i j, 0 ≤ HB a b i j) (hHH : ∀ a b i j, 0 ≤ HH a b i j)
    (hM : ∀ a b, ParabolicC0AlphaWith (MB a b) (MH a b) α (fun z => M z a b) s)
    (hD : ∀ a b c, ParabolicC0AlphaWith (DB a b c) (DH a b c) α
      (fun z => D z a b c) s)
    (hH : ∀ a b i j, ParabolicC0AlphaWith (HB a b i j) (HH a b i j) α
      (fun z => H z a b i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaWith
      (∑ i : n, ∑ j : n,
        (matrixInvTwoIndexContractEntryBoundConst (𝕜 := 𝕜) δ MB HB i j +
          christoffelQuadraticRicciEntryBoundConst
            (fun a b c => matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ MB DB a b c)
            i j))
      (∑ i : n, ∑ j : n,
        (matrixInvTwoIndexContractEntryHolderConst (𝕜 := 𝕜) δ MB MH HB HH i j +
          christoffelQuadraticRicciEntryHolderConst
            (fun a b c => matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ MB DB a b c)
            (fun a b c =>
              matrixInvChristoffelEntryHolderConst (𝕜 := 𝕜) δ MB MH DB DH a b c)
            i j))
      α
      (fun z : ℝ × X =>
        (fun i j =>
          let Γ : n → n → n → 𝕜 := fun a b c =>
            (2 : 𝕜)⁻¹ *
              ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) a l *
                (D z b c l + D z c b l - D z l b c)
          (∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * H z a b i j) +
            ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
              (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) :
          Matrix n n 𝕜)) s := by
  classical
  let Γ : ℝ × X → n → n → n → 𝕜 := fun z a b c =>
    (2 : 𝕜)⁻¹ *
      ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) a l *
        (D z b c l + D z c b l - D z l b c)
  let ΓB : n → n → n → ℝ := fun a b c =>
    matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ MB DB a b c
  let ΓH : n → n → n → ℝ := fun a b c =>
    matrixInvChristoffelEntryHolderConst (𝕜 := 𝕜) δ MB MH DB DH a b c
  have hΓB_nonneg : ∀ a b c, 0 ≤ ΓB a b c := by
    intro a b c
    exact matrixInvChristoffelEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos MB hDB a b c
  have hΓH_nonneg : ∀ a b c, 0 ≤ ΓH a b c := by
    intro a b c
    exact matrixInvChristoffelEntryHolderConst_nonneg (𝕜 := 𝕜)
      hMH hδpos hDB hDH a b c
  have hΓ : ∀ a b c, ParabolicC0AlphaWith (ΓB a b c) (ΓH a b c) α
      (fun z => Γ z a b c) s := by
    intro a b c
    simpa [Γ, ΓB, ΓH] using
      matrix_inv_christoffel_entry_with (M := M) (D := D)
        hMH hM hD hδpos hdet a b c
  simpa [Γ, ΓB, ΓH] using
    ricciDeTurck_schematic_from_christoffel_with
      hMH hHB hHH hΓB_nonneg hΓH_nonneg hM hH hΓ hδpos hdet

/-- A finite family of primitive-input schematic Ricci-DeTurck RHS fields has explicit
matrix-valued bounded parabolic `C^{0,α}` estimates with one compact determinant lower bound
shared by the whole family. -/
theorem ricciDeTurck_schematic_family_with_of_isCompact_det_ne_zero
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {K : Set (ℝ × X)}
    {MB MH : κ → n → n → ℝ}
    {DB DH : κ → n → n → n → ℝ}
    {HB HH : κ → n → n → n → n → ℝ}
    {M : κ → ℝ × X → Matrix n n 𝕜}
    {D : κ → ℝ × X → n → n → n → 𝕜}
    {H : κ → ℝ × X → n → n → n → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hMB : ∀ r a b, 0 ≤ MB r a b) (hMH : ∀ r a b, 0 ≤ MH r a b)
    (hDB : ∀ r a b c, 0 ≤ DB r a b c) (hDH : ∀ r a b c, 0 ≤ DH r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hHH : ∀ r a b i j, 0 ≤ HH r a b i j)
    (hM : ∀ r a b,
      ParabolicC0AlphaWith (MB r a b) (MH r a b) α (fun z => M r z a b) K)
    (hD : ∀ r a b c,
      ParabolicC0AlphaWith (DB r a b c) (DH r a b c) α
        (fun z => D r z a b c) K)
    (hH : ∀ r a b i j,
      ParabolicC0AlphaWith (HB r a b i j) (HH r a b i j) α
        (fun z => H r z a b i j) K)
    (hdet_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (M r z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M r z).det‖) ∧
      ∀ r,
        ParabolicC0AlphaWith
          (∑ i : n, ∑ j : n,
            (matrixInvTwoIndexContractEntryBoundConst (𝕜 := 𝕜) δ (MB r) (HB r) i j +
              christoffelQuadraticRicciEntryBoundConst
                (fun a b c =>
                  matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ (MB r) (DB r) a b c)
                i j))
          (∑ i : n, ∑ j : n,
            (matrixInvTwoIndexContractEntryHolderConst (𝕜 := 𝕜) δ (MB r) (MH r)
                (HB r) (HH r) i j +
              christoffelQuadraticRicciEntryHolderConst
                (fun a b c =>
                  matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ (MB r) (DB r) a b c)
                (fun a b c =>
                  matrixInvChristoffelEntryHolderConst (𝕜 := 𝕜) δ (MB r) (MH r)
                    (DB r) (DH r) a b c)
                i j))
          α
          (fun z : ℝ × X =>
            (fun i j =>
              let Γ : n → n → n → 𝕜 := fun a b c =>
                (2 : 𝕜)⁻¹ *
                  ∑ l : n, ((M r z)⁻¹ : Matrix n n 𝕜) a l *
                    (D r z b c l + D r z c b l - D r z l b c)
              (∑ a : n, ∑ b : n, ((M r z)⁻¹ : Matrix n n 𝕜) a b *
                  H r z a b i j) +
                ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
                  (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) :
              Matrix n n 𝕜)) K := by
  have hMctrl : ∀ r a b, ParabolicC0AlphaOn α (fun z => M r z a b) K := by
    intro r a b
    exact ⟨MB r a b, hMB r a b, MH r a b, hMH r a b, hM r a b⟩
  rcases matrix_det_family_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hMctrl hdet_ne with
    ⟨δ, hδpos, hdet⟩
  refine ⟨δ, hδpos, hdet, ?_⟩
  intro r
  exact ricciDeTurck_schematic_with
    (M := M r) (D := D r) (H := H r)
    (hMH r) (hDB r) (hDH r) (hHB r) (hHH r)
    (hM r) (hD r) (hH r) hδpos (hdet r)

/-- Difference-based sup constant for one supplied-Christoffel schematic Ricci-DeTurck
coordinate entry. -/
def ricciDeTurckSchematicFromChristoffelEntrySubBoundConst {n 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] (δ : ℝ)
    (MB MBd : n → n → ℝ) (HB HBd : n → n → n → n → ℝ)
    (ΓB ΛB ΓdB : n → n → n → ℝ) (i j : n) : ℝ :=
  matrixInvTwoIndexContractEntrySubBoundConst (𝕜 := 𝕜) δ MB MBd HB HBd i j +
    christoffelQuadraticRicciEntrySubBoundConst ΓB ΛB ΓdB i j

/-- Difference-based Holder constant for one supplied-Christoffel schematic Ricci-DeTurck
coordinate entry. -/
def ricciDeTurckSchematicFromChristoffelEntrySubHolderConst {n 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] (δ : ℝ)
    (MB MH MBd MHd : n → n → ℝ) (HB HH HBd HHd : n → n → n → n → ℝ)
    (ΓB ΓH ΛB ΛH ΓdB ΓdH : n → n → n → ℝ) (i j : n) : ℝ :=
  matrixInvTwoIndexContractEntrySubHolderConst
      (𝕜 := 𝕜) δ MB MH MBd MHd HB HH HBd HHd i j +
    christoffelQuadraticRicciEntrySubHolderConst ΓB ΓH ΛB ΛH ΓdB ΓdH i j

/-- Difference-based sup constant for the supplied-Christoffel schematic Ricci-DeTurck matrix. -/
def ricciDeTurckSchematicFromChristoffelSubBoundConst {n 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] (δ : ℝ)
    (MB MBd : n → n → ℝ) (HB HBd : n → n → n → n → ℝ)
    (ΓB ΛB ΓdB : n → n → n → ℝ) : ℝ :=
  ∑ i : n, ∑ j : n,
    ricciDeTurckSchematicFromChristoffelEntrySubBoundConst
      (𝕜 := 𝕜) δ MB MBd HB HBd ΓB ΛB ΓdB i j

/-- Difference-based Holder constant for the supplied-Christoffel schematic Ricci-DeTurck
matrix. -/
def ricciDeTurckSchematicFromChristoffelSubHolderConst {n 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] (δ : ℝ)
    (MB MH MBd MHd : n → n → ℝ) (HB HH HBd HHd : n → n → n → n → ℝ)
    (ΓB ΓH ΛB ΛH ΓdB ΓdH : n → n → n → ℝ) : ℝ :=
  ∑ i : n, ∑ j : n,
    ricciDeTurckSchematicFromChristoffelEntrySubHolderConst
      (𝕜 := 𝕜) δ MB MH MBd MHd HB HH HBd HHd ΓB ΓH ΛB ΛH ΓdB ΓdH i j

theorem ricciDeTurckSchematicFromChristoffelEntrySubBoundConst_nonneg {n 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] {δ : ℝ}
    {MB MBd : n → n → ℝ} {HB HBd : n → n → n → n → ℝ}
    {ΓB ΛB ΓdB : n → n → n → ℝ} (hδpos : 0 < δ)
    (hMBd : ∀ a b, 0 ≤ MBd a b) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hHBd : ∀ a b i j, 0 ≤ HBd a b i j)
    (hΓB : ∀ a b c, 0 ≤ ΓB a b c) (hΛB : ∀ a b c, 0 ≤ ΛB a b c)
    (hΓdB : ∀ a b c, 0 ≤ ΓdB a b c) (i j : n) :
    0 ≤ ricciDeTurckSchematicFromChristoffelEntrySubBoundConst
      (𝕜 := 𝕜) δ MB MBd HB HBd ΓB ΛB ΓdB i j := by
  exact add_nonneg
    (matrixInvTwoIndexContractEntrySubBoundConst_nonneg
      (𝕜 := 𝕜) hδpos hMBd hHB hHBd i j)
    (christoffelQuadraticRicciEntrySubBoundConst_nonneg hΓB hΛB hΓdB i j)

theorem ricciDeTurckSchematicFromChristoffelEntrySubHolderConst_nonneg {n 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] {δ : ℝ}
    {MB MH MBd MHd : n → n → ℝ} {HB HH HBd HHd : n → n → n → n → ℝ}
    {ΓB ΓH ΛB ΛH ΓdB ΓdH : n → n → n → ℝ} (hδpos : 0 < δ)
    (hMH : ∀ a b, 0 ≤ MH a b) (hMBd : ∀ a b, 0 ≤ MBd a b)
    (hMHd : ∀ a b, 0 ≤ MHd a b) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hHH : ∀ a b i j, 0 ≤ HH a b i j)
    (hHBd : ∀ a b i j, 0 ≤ HBd a b i j)
    (hHHd : ∀ a b i j, 0 ≤ HHd a b i j)
    (hΓB : ∀ a b c, 0 ≤ ΓB a b c) (hΓH : ∀ a b c, 0 ≤ ΓH a b c)
    (hΛB : ∀ a b c, 0 ≤ ΛB a b c) (hΛH : ∀ a b c, 0 ≤ ΛH a b c)
    (hΓdB : ∀ a b c, 0 ≤ ΓdB a b c)
    (hΓdH : ∀ a b c, 0 ≤ ΓdH a b c) (i j : n) :
    0 ≤ ricciDeTurckSchematicFromChristoffelEntrySubHolderConst
      (𝕜 := 𝕜) δ MB MH MBd MHd HB HH HBd HHd ΓB ΓH ΛB ΛH ΓdB ΓdH i j := by
  exact add_nonneg
    (matrixInvTwoIndexContractEntrySubHolderConst_nonneg
      (𝕜 := 𝕜) hδpos hMH hMBd hMHd hHB hHH hHBd hHHd i j)
    (christoffelQuadraticRicciEntrySubHolderConst_nonneg
      hΓB hΓH hΛB hΛH hΓdB hΓdH i j)

theorem ricciDeTurckSchematicFromChristoffelSubBoundConst_nonneg {n 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] {δ : ℝ}
    {MB MBd : n → n → ℝ} {HB HBd : n → n → n → n → ℝ}
    {ΓB ΛB ΓdB : n → n → n → ℝ} (hδpos : 0 < δ)
    (hMBd : ∀ a b, 0 ≤ MBd a b) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hHBd : ∀ a b i j, 0 ≤ HBd a b i j)
    (hΓB : ∀ a b c, 0 ≤ ΓB a b c) (hΛB : ∀ a b c, 0 ≤ ΛB a b c)
    (hΓdB : ∀ a b c, 0 ≤ ΓdB a b c) :
    0 ≤ ricciDeTurckSchematicFromChristoffelSubBoundConst
      (𝕜 := 𝕜) δ MB MBd HB HBd ΓB ΛB ΓdB := by
  exact Finset.sum_nonneg fun i _hi =>
    Finset.sum_nonneg fun j _hj =>
      ricciDeTurckSchematicFromChristoffelEntrySubBoundConst_nonneg
        (𝕜 := 𝕜) hδpos hMBd hHB hHBd hΓB hΛB hΓdB i j

theorem ricciDeTurckSchematicFromChristoffelSubHolderConst_nonneg {n 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] {δ : ℝ}
    {MB MH MBd MHd : n → n → ℝ} {HB HH HBd HHd : n → n → n → n → ℝ}
    {ΓB ΓH ΛB ΛH ΓdB ΓdH : n → n → n → ℝ} (hδpos : 0 < δ)
    (hMH : ∀ a b, 0 ≤ MH a b) (hMBd : ∀ a b, 0 ≤ MBd a b)
    (hMHd : ∀ a b, 0 ≤ MHd a b) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hHH : ∀ a b i j, 0 ≤ HH a b i j)
    (hHBd : ∀ a b i j, 0 ≤ HBd a b i j)
    (hHHd : ∀ a b i j, 0 ≤ HHd a b i j)
    (hΓB : ∀ a b c, 0 ≤ ΓB a b c) (hΓH : ∀ a b c, 0 ≤ ΓH a b c)
    (hΛB : ∀ a b c, 0 ≤ ΛB a b c) (hΛH : ∀ a b c, 0 ≤ ΛH a b c)
    (hΓdB : ∀ a b c, 0 ≤ ΓdB a b c)
    (hΓdH : ∀ a b c, 0 ≤ ΓdH a b c) :
    0 ≤ ricciDeTurckSchematicFromChristoffelSubHolderConst
      (𝕜 := 𝕜) δ MB MH MBd MHd HB HH HBd HHd ΓB ΓH ΛB ΛH ΓdB ΓdH := by
  exact Finset.sum_nonneg fun i _hi =>
    Finset.sum_nonneg fun j _hj =>
      ricciDeTurckSchematicFromChristoffelEntrySubHolderConst_nonneg
        (𝕜 := 𝕜) hδpos hMH hMBd hMHd hHB hHH hHBd hHHd
        hΓB hΓH hΛB hΛH hΓdB hΓdH i j

/-- One supplied-Christoffel schematic Ricci-DeTurck coordinate entry has difference-based
parabolic `C^{0,α}` control from entrywise metric, principal-coefficient, and Christoffel-array
difference controls. -/
theorem ricciDeTurck_schematic_from_christoffel_entry_sub_with_entrywise {n 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] {δ : ℝ}
    {MB MH MBd MHd : n → n → ℝ} {HB HH HBd HHd : n → n → n → n → ℝ}
    {ΓB ΓH ΛB ΛH ΓdB ΓdH : n → n → n → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜} {H K : ℝ × X → n → n → n → n → 𝕜}
    {Γ Λ : ℝ × X → n → n → n → 𝕜}
    (hMH : ∀ a b, 0 ≤ MH a b)
    (hMBd : ∀ a b, 0 ≤ MBd a b) (hMHd : ∀ a b, 0 ≤ MHd a b)
    (hΓB : ∀ a b c, 0 ≤ ΓB a b c)
    (hΓdB : ∀ a b c, 0 ≤ ΓdB a b c)
    (hM : ∀ a b, ParabolicC0AlphaWith (MB a b) (MH a b) α (fun z => M z a b) s)
    (hN : ∀ a b, ParabolicC0AlphaWith (MB a b) (MH a b) α (fun z => N z a b) s)
    (hMdiff : ∀ a b,
      ParabolicC0AlphaWith (MBd a b) (MHd a b) α (fun z => M z a b - N z a b) s)
    (hK : ∀ a b i j, ParabolicC0AlphaWith (HB a b i j) (HH a b i j) α
      (fun z => K z a b i j) s)
    (hHdiff : ∀ a b i j,
      ParabolicC0AlphaWith (HBd a b i j) (HHd a b i j) α
        (fun z => H z a b i j - K z a b i j) s)
    (hΓ : ∀ a b c, ParabolicC0AlphaWith (ΓB a b c) (ΓH a b c) α
      (fun z => Γ z a b c) s)
    (hΛ : ∀ a b c, ParabolicC0AlphaWith (ΛB a b c) (ΛH a b c) α
      (fun z => Λ z a b c) s)
    (hΓdiff : ∀ a b c,
      ParabolicC0AlphaWith (ΓdB a b c) (ΓdH a b c) α
        (fun z => Γ z a b c - Λ z a b c) s)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖)
    (i j : n) :
    ParabolicC0AlphaWith
      (ricciDeTurckSchematicFromChristoffelEntrySubBoundConst
        (𝕜 := 𝕜) δ MB MBd HB HBd ΓB ΛB ΓdB i j)
      (ricciDeTurckSchematicFromChristoffelEntrySubHolderConst
        (𝕜 := 𝕜) δ MB MH MBd MHd HB HH HBd HHd ΓB ΓH ΛB ΛH ΓdB ΓdH i j)
      α
      (fun z =>
        ((∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * H z a b i j) +
            ((∑ a : n, ∑ b : n, Γ z a i j * Γ z b a b) -
              (∑ a : n, ∑ b : n, Γ z a i b * Γ z b a j))) -
          ((∑ a : n, ∑ b : n, ((N z)⁻¹ : Matrix n n 𝕜) a b * K z a b i j) +
            ((∑ a : n, ∑ b : n, Λ z a i j * Λ z b a b) -
              (∑ a : n, ∑ b : n, Λ z a i b * Λ z b a j)))) s := by
  have hprincipal :
      ParabolicC0AlphaWith
        (matrixInvTwoIndexContractEntrySubBoundConst (𝕜 := 𝕜) δ MB MBd HB HBd i j)
        (matrixInvTwoIndexContractEntrySubHolderConst
          (𝕜 := 𝕜) δ MB MH MBd MHd HB HH HBd HHd i j)
        α
        (fun z =>
          (∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * H z a b i j) -
            ∑ a : n, ∑ b : n, ((N z)⁻¹ : Matrix n n 𝕜) a b * K z a b i j) s :=
    matrix_inv_two_index_contract_entry_sub_with_entrywise
      (M := M) (N := N) (T := H) (U := K)
      hMH hMBd hMHd hM hN hMdiff hK hHdiff hδpos hdetM hdetN i j
  have hquadratic :
      ParabolicC0AlphaWith
        (christoffelQuadraticRicciEntrySubBoundConst ΓB ΛB ΓdB i j)
        (christoffelQuadraticRicciEntrySubHolderConst ΓB ΓH ΛB ΛH ΓdB ΓdH i j)
        α
        (fun z =>
          ((∑ a : n, ∑ b : n, Γ z a i j * Γ z b a b) -
              (∑ a : n, ∑ b : n, Γ z a i b * Γ z b a j)) -
            ((∑ a : n, ∑ b : n, Λ z a i j * Λ z b a b) -
              (∑ a : n, ∑ b : n, Λ z a i b * Λ z b a j))) s :=
    christoffel_quadratic_ricci_entry_sub_with hΓB hΓdB hΓ hΛ hΓdiff i j
  have hsum := hprincipal.add hquadratic
  convert hsum using 1
  · unfold ricciDeTurckSchematicFromChristoffelEntrySubBoundConst
    abel
  · unfold ricciDeTurckSchematicFromChristoffelEntrySubHolderConst
    abel
  · funext z
    abel

/-- The supplied-Christoffel schematic Ricci-DeTurck RHS has matrix-valued difference-based
parabolic `C^{0,α}` control from entrywise metric, principal-coefficient, and Christoffel-array
difference controls. -/
theorem ricciDeTurck_schematic_from_christoffel_sub_with_entrywise {n 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] {δ : ℝ}
    {MB MH MBd MHd : n → n → ℝ} {HB HH HBd HHd : n → n → n → n → ℝ}
    {ΓB ΓH ΛB ΛH ΓdB ΓdH : n → n → n → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜} {H K : ℝ × X → n → n → n → n → 𝕜}
    {Γ Λ : ℝ × X → n → n → n → 𝕜}
    (hMH : ∀ a b, 0 ≤ MH a b)
    (hMBd : ∀ a b, 0 ≤ MBd a b) (hMHd : ∀ a b, 0 ≤ MHd a b)
    (hHB : ∀ a b i j, 0 ≤ HB a b i j) (hHH : ∀ a b i j, 0 ≤ HH a b i j)
    (hHBd : ∀ a b i j, 0 ≤ HBd a b i j)
    (hHHd : ∀ a b i j, 0 ≤ HHd a b i j)
    (hΓB : ∀ a b c, 0 ≤ ΓB a b c) (hΓH : ∀ a b c, 0 ≤ ΓH a b c)
    (hΛB : ∀ a b c, 0 ≤ ΛB a b c) (hΛH : ∀ a b c, 0 ≤ ΛH a b c)
    (hΓdB : ∀ a b c, 0 ≤ ΓdB a b c)
    (hΓdH : ∀ a b c, 0 ≤ ΓdH a b c)
    (hM : ∀ a b, ParabolicC0AlphaWith (MB a b) (MH a b) α (fun z => M z a b) s)
    (hN : ∀ a b, ParabolicC0AlphaWith (MB a b) (MH a b) α (fun z => N z a b) s)
    (hMdiff : ∀ a b,
      ParabolicC0AlphaWith (MBd a b) (MHd a b) α (fun z => M z a b - N z a b) s)
    (hK : ∀ a b i j, ParabolicC0AlphaWith (HB a b i j) (HH a b i j) α
      (fun z => K z a b i j) s)
    (hHdiff : ∀ a b i j,
      ParabolicC0AlphaWith (HBd a b i j) (HHd a b i j) α
        (fun z => H z a b i j - K z a b i j) s)
    (hΓ : ∀ a b c, ParabolicC0AlphaWith (ΓB a b c) (ΓH a b c) α
      (fun z => Γ z a b c) s)
    (hΛ : ∀ a b c, ParabolicC0AlphaWith (ΛB a b c) (ΛH a b c) α
      (fun z => Λ z a b c) s)
    (hΓdiff : ∀ a b c,
      ParabolicC0AlphaWith (ΓdB a b c) (ΓdH a b c) α
        (fun z => Γ z a b c - Λ z a b c) s)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicC0AlphaWith
      (ricciDeTurckSchematicFromChristoffelSubBoundConst
        (𝕜 := 𝕜) δ MB MBd HB HBd ΓB ΛB ΓdB)
      (ricciDeTurckSchematicFromChristoffelSubHolderConst
        (𝕜 := 𝕜) δ MB MH MBd MHd HB HH HBd HHd ΓB ΓH ΛB ΛH ΓdB ΓdH)
      α
      (fun z : ℝ × X =>
        ((fun i j =>
          (∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * H z a b i j) +
            ((∑ a : n, ∑ b : n, Γ z a i j * Γ z b a b) -
              (∑ a : n, ∑ b : n, Γ z a i b * Γ z b a j)) :
          Matrix n n 𝕜) -
          (fun i j =>
            (∑ a : n, ∑ b : n, ((N z)⁻¹ : Matrix n n 𝕜) a b * K z a b i j) +
              ((∑ a : n, ∑ b : n, Λ z a i j * Λ z b a b) -
                (∑ a : n, ∑ b : n, Λ z a i b * Λ z b a j)) :
            Matrix n n 𝕜))) s := by
  refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
  · intro i
    exact Finset.sum_nonneg fun j _hj =>
      ricciDeTurckSchematicFromChristoffelEntrySubBoundConst_nonneg
        (𝕜 := 𝕜) hδpos hMBd hHB hHBd hΓB hΛB hΓdB i j
  · intro i
    exact Finset.sum_nonneg fun j _hj =>
      ricciDeTurckSchematicFromChristoffelEntrySubHolderConst_nonneg
        (𝕜 := 𝕜) hδpos hMH hMBd hMHd hHB hHH hHBd hHHd
        hΓB hΓH hΛB hΛH hΓdB hΓdH i j
  · intro i
    refine ParabolicC0AlphaWith.pi ?_ ?_ ?_
    · intro j
      exact ricciDeTurckSchematicFromChristoffelEntrySubBoundConst_nonneg
        (𝕜 := 𝕜) hδpos hMBd hHB hHBd hΓB hΛB hΓdB i j
    · intro j
      exact ricciDeTurckSchematicFromChristoffelEntrySubHolderConst_nonneg
        (𝕜 := 𝕜) hδpos hMH hMBd hMHd hHB hHH hHBd hHHd
        hΓB hΓH hΛB hΛH hΓdB hΓdH i j
    · intro j
      exact ricciDeTurck_schematic_from_christoffel_entry_sub_with_entrywise
        (M := M) (N := N) (H := H) (K := K) (Γ := Γ) (Λ := Λ)
        hMH hMBd hMHd hΓB hΓdB hM hN hMdiff hK hHdiff
        hΓ hΛ hΓdiff hδpos hdetM hdetN i j

/-- The schematic Ricci-DeTurck expression built from supplied Christoffel arrays preserves
existential parabolic `C^{0,α}` difference control from entrywise primitive differences. -/
theorem ricciDeTurck_schematic_from_christoffel_sub_entrywise {n 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] {δ : ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {H Kc : ℝ × X → n → n → n → n → 𝕜}
    {Γ Λ : ℝ × X → n → n → n → 𝕜}
    (hM : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) s)
    (hN : ∀ a b, ParabolicC0AlphaOn α (fun z => N z a b) s)
    (hMdiff : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b - N z a b) s)
    (hKc : ∀ a b i j, ParabolicC0AlphaOn α (fun z => Kc z a b i j) s)
    (hHdiff : ∀ a b i j,
      ParabolicC0AlphaOn α (fun z => H z a b i j - Kc z a b i j) s)
    (hΓ : ∀ a b c, ParabolicC0AlphaOn α (fun z => Γ z a b c) s)
    (hΛ : ∀ a b c, ParabolicC0AlphaOn α (fun z => Λ z a b c) s)
    (hΓdiff : ∀ a b c, ParabolicC0AlphaOn α (fun z => Γ z a b c - Λ z a b c) s)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × X =>
        (show Matrix n n 𝕜 from fun i j =>
          (∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * H z a b i j) +
            ((∑ a : n, ∑ b : n, Γ z a i j * Γ z b a b) -
              (∑ a : n, ∑ b : n, Γ z a i b * Γ z b a j))) -
        (show Matrix n n 𝕜 from fun i j =>
          (∑ a : n, ∑ b : n, ((N z)⁻¹ : Matrix n n 𝕜) a b * Kc z a b i j) +
            ((∑ a : n, ∑ b : n, Λ z a i j * Λ z b a b) -
              (∑ a : n, ∑ b : n, Λ z a i b * Λ z b a j)))) s := by
  have hprincipal := matrix_inv_two_index_contract_sub_entrywise
    (M := M) (N := N) (T := H) (U := Kc)
    hM hN hMdiff hKc hHdiff hδpos hdetM hdetN
  have hquad := christoffel_quadratic_ricci_sub (Γ := Γ) (Λ := Λ) hΓ hΛ hΓdiff
  have hsum := hprincipal.add hquad
  change @ParabolicC0AlphaOn X (n → n → 𝕜) _ Pi.normedAddCommGroup α _ s
  rcases hsum with ⟨B, hB, C, hC, hraw⟩
  let P : ℝ × X → n → n → 𝕜 := fun z i j =>
    ∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * H z a b i j
  let Q : ℝ × X → n → n → 𝕜 := fun z i j =>
    (∑ a : n, ∑ b : n, Γ z a i j * Γ z b a b) -
      (∑ a : n, ∑ b : n, Γ z a i b * Γ z b a j)
  let R : ℝ × X → n → n → 𝕜 := fun z i j =>
    ∑ a : n, ∑ b : n, ((N z)⁻¹ : Matrix n n 𝕜) a b * Kc z a b i j
  let S : ℝ × X → n → n → 𝕜 := fun z i j =>
    (∑ a : n, ∑ b : n, Λ z a i j * Λ z b a b) -
      (∑ a : n, ∑ b : n, Λ z a i b * Λ z b a j)
  change @ParabolicC0AlphaWith X (n → n → 𝕜) _ Pi.normedAddCommGroup B C α
    (fun z => (P z - R z) + (Q z - S z)) s at hraw
  refine ⟨B, hB, C, hC, ?_⟩
  change @ParabolicC0AlphaWith X (n → n → 𝕜) _ Pi.normedAddCommGroup B C α
    (fun z => (show Matrix n n 𝕜 from fun i j => P z i j + Q z i j) -
      (show Matrix n n 𝕜 from fun i j => R z i j + S z i j)) s
  have hfun : ∀ z : ℝ × X,
      (show Matrix n n 𝕜 from fun i j => P z i j + Q z i j) -
        (show Matrix n n 𝕜 from fun i j => R z i j + S z i j) =
      (P z - R z) + (Q z - S z) := by
    intro z
    ext i j
    change (P z i j + Q z i j) - (R z i j + S z i j) =
      (P z i j - R z i j) + (Q z i j - S z i j)
    abel
  constructor
  · intro z hz
    change ‖(show Matrix n n 𝕜 from fun i j => P z i j + Q z i j) -
      (show Matrix n n 𝕜 from fun i j => R z i j + S z i j)‖ ≤ B
    rw [hfun z]
    exact hraw.bounded hz
  · intro p hp q hq
    change ‖((show Matrix n n 𝕜 from fun i j => P p i j + Q p i j) -
      (show Matrix n n 𝕜 from fun i j => R p i j + S p i j)) -
      ((show Matrix n n 𝕜 from fun i j => P q i j + Q q i j) -
        (show Matrix n n 𝕜 from fun i j => R q i j + S q i j))‖ ≤
      C * parabolicDistance p q ^ α
    rw [hfun p, hfun q]
    exact hraw.holder hp hq

/-- The finite matrix-valued schematic Ricci-DeTurck coordinate RHS.  This definition names the
algebraic expression used by the pointwise and time-space Lipschitz estimates. -/
def ricciDeTurckSchematicMatrix {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (M : Matrix n n 𝕜) (D : n → n → n → 𝕜)
    (H : n → n → n → n → 𝕜) : Matrix n n 𝕜 :=
  fun i j =>
    let Γ : n → n → n → 𝕜 := fun a b c =>
      (2 : 𝕜)⁻¹ *
        ∑ l : n, (M⁻¹ : Matrix n n 𝕜) a l * (D b c l + D c b l - D l b c)
    (∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
      ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
        (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))

/-- Difference-based sup constant for the primitive-input schematic Ricci-DeTurck matrix, using
entrywise controls on primitive differences. -/
def ricciDeTurckSchematicEntrywiseSubBoundConst {n 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] (δ : ℝ)
    (MB MBd : n → n → ℝ) (DB DDB : n → n → n → ℝ)
    (HB HBd : n → n → n → n → ℝ) : ℝ :=
  ricciDeTurckSchematicFromChristoffelSubBoundConst
    (𝕜 := 𝕜) δ MB MBd HB HBd
    (fun a b c => matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ MB DB a b c)
    (fun a b c => matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ MB DB a b c)
    (fun a b c => matrixInvChristoffelEntrySubBoundConst (𝕜 := 𝕜) δ MB MBd DB DDB a b c)

/-- Difference-based Holder constant for the primitive-input schematic Ricci-DeTurck matrix,
using entrywise controls on primitive differences. -/
def ricciDeTurckSchematicEntrywiseSubHolderConst {n 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] (δ : ℝ)
    (MB MH MBd MHd : n → n → ℝ) (DB DH DDB DDH : n → n → n → ℝ)
    (HB HH HBd HHd : n → n → n → n → ℝ) : ℝ :=
  ricciDeTurckSchematicFromChristoffelSubHolderConst
    (𝕜 := 𝕜) δ MB MH MBd MHd HB HH HBd HHd
    (fun a b c => matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ MB DB a b c)
    (fun a b c =>
      matrixInvChristoffelEntryHolderConst (𝕜 := 𝕜) δ MB MH DB DH a b c)
    (fun a b c => matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ MB DB a b c)
    (fun a b c =>
      matrixInvChristoffelEntryHolderConst (𝕜 := 𝕜) δ MB MH DB DH a b c)
    (fun a b c =>
      matrixInvChristoffelEntrySubBoundConst (𝕜 := 𝕜) δ MB MBd DB DDB a b c)
    (fun a b c =>
      matrixInvChristoffelEntrySubHolderConst
        (𝕜 := 𝕜) δ MB MH MBd MHd DB DH DDB DDH a b c)

/-- The primitive-input schematic Ricci-DeTurck RHS has matrix-valued difference-based
parabolic `C^{0,α}` control from entrywise metric, first-derivative, and second-derivative
difference controls. -/
theorem ricciDeTurckSchematicMatrix_sub_with_entrywise {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ}
    {MB MH MBd MHd : n → n → ℝ} {DB DH DDB DDH : n → n → n → ℝ}
    {HB HH HBd HHd : n → n → n → n → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    {Hc Kc : ℝ × X → n → n → n → n → 𝕜}
    (hMH : ∀ a b, 0 ≤ MH a b)
    (hMBd : ∀ a b, 0 ≤ MBd a b) (hMHd : ∀ a b, 0 ≤ MHd a b)
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hDH : ∀ a b c, 0 ≤ DH a b c)
    (hDDB : ∀ a b c, 0 ≤ DDB a b c) (hDDH : ∀ a b c, 0 ≤ DDH a b c)
    (hHB : ∀ a b i j, 0 ≤ HB a b i j) (hHH : ∀ a b i j, 0 ≤ HH a b i j)
    (hHBd : ∀ a b i j, 0 ≤ HBd a b i j)
    (hHHd : ∀ a b i j, 0 ≤ HHd a b i j)
    (hM : ∀ a b, ParabolicC0AlphaWith (MB a b) (MH a b) α (fun z => M z a b) s)
    (hN : ∀ a b, ParabolicC0AlphaWith (MB a b) (MH a b) α (fun z => N z a b) s)
    (hMdiff : ∀ a b,
      ParabolicC0AlphaWith (MBd a b) (MHd a b) α (fun z => M z a b - N z a b) s)
    (hD : ∀ a b c, ParabolicC0AlphaWith (DB a b c) (DH a b c) α
      (fun z => D z a b c) s)
    (hE : ∀ a b c, ParabolicC0AlphaWith (DB a b c) (DH a b c) α
      (fun z => E z a b c) s)
    (hDdiff : ∀ a b c,
      ParabolicC0AlphaWith (DDB a b c) (DDH a b c) α
        (fun z => D z a b c - E z a b c) s)
    (hKc : ∀ a b i j, ParabolicC0AlphaWith (HB a b i j) (HH a b i j) α
      (fun z => Kc z a b i j) s)
    (hHdiff : ∀ a b i j,
      ParabolicC0AlphaWith (HBd a b i j) (HHd a b i j) α
        (fun z => Hc z a b i j - Kc z a b i j) s)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicC0AlphaWith
      (ricciDeTurckSchematicEntrywiseSubBoundConst
        (𝕜 := 𝕜) δ MB MBd DB DDB HB HBd)
      (ricciDeTurckSchematicEntrywiseSubHolderConst
        (𝕜 := 𝕜) δ MB MH MBd MHd DB DH DDB DDH HB HH HBd HHd)
      α
      (fun z : ℝ × X =>
        ricciDeTurckSchematicMatrix (M z) (D z) (Hc z) -
          ricciDeTurckSchematicMatrix (N z) (E z) (Kc z)) s := by
  classical
  let Γ : ℝ × X → n → n → n → 𝕜 := fun z a b c =>
    (2 : 𝕜)⁻¹ *
      ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) a l *
        (D z b c l + D z c b l - D z l b c)
  let Λ : ℝ × X → n → n → n → 𝕜 := fun z a b c =>
    (2 : 𝕜)⁻¹ *
      ∑ l : n, ((N z)⁻¹ : Matrix n n 𝕜) a l *
        (E z b c l + E z c b l - E z l b c)
  let ΓB : n → n → n → ℝ := fun a b c =>
    matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ MB DB a b c
  let ΓH : n → n → n → ℝ := fun a b c =>
    matrixInvChristoffelEntryHolderConst (𝕜 := 𝕜) δ MB MH DB DH a b c
  let ΓdB : n → n → n → ℝ := fun a b c =>
    matrixInvChristoffelEntrySubBoundConst (𝕜 := 𝕜) δ MB MBd DB DDB a b c
  let ΓdH : n → n → n → ℝ := fun a b c =>
    matrixInvChristoffelEntrySubHolderConst
      (𝕜 := 𝕜) δ MB MH MBd MHd DB DH DDB DDH a b c
  have hΓB_nonneg : ∀ a b c, 0 ≤ ΓB a b c := by
    intro a b c
    exact matrixInvChristoffelEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos MB hDB a b c
  have hΓH_nonneg : ∀ a b c, 0 ≤ ΓH a b c := by
    intro a b c
    exact matrixInvChristoffelEntryHolderConst_nonneg
      (𝕜 := 𝕜) hMH hδpos hDB hDH a b c
  have hΓdB_nonneg : ∀ a b c, 0 ≤ ΓdB a b c := by
    intro a b c
    exact matrixInvChristoffelEntrySubBoundConst_nonneg
      (𝕜 := 𝕜) hδpos hMBd hDB hDDB a b c
  have hΓdH_nonneg : ∀ a b c, 0 ≤ ΓdH a b c := by
    intro a b c
    exact matrixInvChristoffelEntrySubHolderConst_nonneg
      (𝕜 := 𝕜) hδpos hMH hMBd hMHd hDB hDH hDDB hDDH a b c
  have hΓ : ∀ a b c, ParabolicC0AlphaWith (ΓB a b c) (ΓH a b c) α
      (fun z => Γ z a b c) s := by
    intro a b c
    simpa [Γ, ΓB, ΓH] using
      matrix_inv_christoffel_entry_with (M := M) (D := D)
        hMH hM hD hδpos hdetM a b c
  have hΛ : ∀ a b c, ParabolicC0AlphaWith (ΓB a b c) (ΓH a b c) α
      (fun z => Λ z a b c) s := by
    intro a b c
    simpa [Λ, ΓB, ΓH] using
      matrix_inv_christoffel_entry_with (M := N) (D := E)
        hMH hN hE hδpos hdetN a b c
  have hΓdiff : ∀ a b c,
      ParabolicC0AlphaWith (ΓdB a b c) (ΓdH a b c) α
        (fun z => Γ z a b c - Λ z a b c) s := by
    intro a b c
    simpa [Γ, Λ, ΓdB, ΓdH] using
      matrix_inv_christoffel_entry_sub_with_entrywise
        (M := M) (N := N) (D := D) (E := E)
        hMH hMBd hMHd hM hN hMdiff hE hDdiff hδpos hdetM hdetN a b c
  have hraw := ricciDeTurck_schematic_from_christoffel_sub_with_entrywise
      (M := M) (N := N) (H := Hc) (K := Kc) (Γ := Γ) (Λ := Λ)
      hMH hMBd hMHd hHB hHH hHBd hHHd
      hΓB_nonneg hΓH_nonneg hΓB_nonneg hΓH_nonneg hΓdB_nonneg hΓdH_nonneg
      hM hN hMdiff hKc hHdiff hΓ hΛ hΓdiff hδpos hdetM hdetN
  change @ParabolicC0AlphaWith X (n → n → 𝕜) _ Pi.normedAddCommGroup _ _ _ _ _
  constructor
  · intro z hz
    unfold ricciDeTurckSchematicMatrix
    have hbound := hraw.bounded hz
    simp only [Matrix.norm_def, Pi.norm_def, Pi.nnnorm_def, Matrix.sub_apply, Pi.sub_apply,
      Γ, Λ, ricciDeTurckSchematicEntrywiseSubBoundConst,
      ricciDeTurckSchematicEntrywiseSubHolderConst, ΓB, ΓH, ΓdB, ΓdH] at hbound ⊢
    exact hbound
  · intro p hp q hq
    unfold ricciDeTurckSchematicMatrix
    have hholder := hraw.holder hp hq
    simp only [Matrix.norm_def, Pi.norm_def, Pi.nnnorm_def, Matrix.sub_apply, Pi.sub_apply,
      Γ, Λ, ricciDeTurckSchematicEntrywiseSubBoundConst,
      ricciDeTurckSchematicEntrywiseSubHolderConst, ΓB, ΓH, ΓdB, ΓdH] at hholder ⊢
    exact hholder

end ParabolicC0AlphaOn

namespace ParabolicC0AlphaNormLe

variable {X : Type*} [PseudoMetricSpace X]
variable {α : ℝ} {s : Set (ℝ × X)}

/-- Entrywise primitive metric, first-derivative, and second-derivative controls, together with a
determinant lower bound, package the schematic Ricci-DeTurck RHS with the corresponding
single-radius `C^{0,α}` bound. -/
theorem ricciDeTurck_schematic_of_entries {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {R : n → n → ℝ} {RD : n → n → n → ℝ}
    {RH : n → n → n → n → ℝ} {δ : ℝ}
    {M : ℝ × X → Matrix n n 𝕜} {D : ℝ × X → n → n → n → 𝕜}
    {H : ℝ × X → n → n → n → n → 𝕜}
    (hM : ∀ a b, ParabolicC0AlphaNormLe (R a b) α (fun z => M z a b) s)
    (hD : ∀ a b c, ParabolicC0AlphaNormLe (RD a b c) α (fun z => D z a b c) s)
    (hH : ∀ a b i j, ParabolicC0AlphaNormLe (RH a b i j) α
      (fun z => H z a b i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaNormLe
      ((∑ i : n, ∑ j : n,
          (ParabolicC0AlphaOn.matrixInvTwoIndexContractEntryBoundConst
              (𝕜 := 𝕜) δ R RH i j +
            ParabolicC0AlphaOn.christoffelQuadraticRicciEntryBoundConst
              (fun a b c =>
                ParabolicC0AlphaOn.matrixInvChristoffelEntryBoundConst
                  (𝕜 := 𝕜) δ R RD a b c)
              i j)) +
        (∑ i : n, ∑ j : n,
          (ParabolicC0AlphaOn.matrixInvTwoIndexContractEntryHolderConst
              (𝕜 := 𝕜) δ R R RH RH i j +
            ParabolicC0AlphaOn.christoffelQuadraticRicciEntryHolderConst
              (fun a b c =>
                ParabolicC0AlphaOn.matrixInvChristoffelEntryBoundConst
                  (𝕜 := 𝕜) δ R RD a b c)
              (fun a b c =>
                ParabolicC0AlphaOn.matrixInvChristoffelEntryHolderConst
                  (𝕜 := 𝕜) δ R R RD RD a b c)
              i j)))
      α
      (fun z : ℝ × X =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix (M z) (D z) (H z)) s := by
  have hR : ∀ a b, 0 ≤ R a b := fun a b => (hM a b).nonneg
  have hRD : ∀ a b c, 0 ≤ RD a b c := fun a b c => (hD a b c).nonneg
  have hRH : ∀ a b i j, 0 ≤ RH a b i j := fun a b i j => (hH a b i j).nonneg
  have hΓB : ∀ a b c,
      0 ≤ ParabolicC0AlphaOn.matrixInvChristoffelEntryBoundConst
        (𝕜 := 𝕜) δ R RD a b c := by
    intro a b c
    exact ParabolicC0AlphaOn.matrixInvChristoffelEntryBoundConst_nonneg
      (𝕜 := 𝕜) hδpos R hRD a b c
  have hΓH : ∀ a b c,
      0 ≤ ParabolicC0AlphaOn.matrixInvChristoffelEntryHolderConst
        (𝕜 := 𝕜) δ R R RD RD a b c := by
    intro a b c
    exact ParabolicC0AlphaOn.matrixInvChristoffelEntryHolderConst_nonneg
      (𝕜 := 𝕜) hR hδpos hRD hRD a b c
  exact ParabolicC0AlphaNormLe.of_c0AlphaWith
    (Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj =>
        add_nonneg
          (ParabolicC0AlphaOn.matrixInvTwoIndexContractEntryBoundConst_nonneg
            (𝕜 := 𝕜) hδpos R hRH i j)
          (ParabolicC0AlphaOn.christoffelQuadraticRicciEntryBoundConst_nonneg
            hΓB i j))
    (Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj =>
        add_nonneg
          (ParabolicC0AlphaOn.matrixInvTwoIndexContractEntryHolderConst_nonneg
            (𝕜 := 𝕜) hR hδpos hRH hRH i j)
          (ParabolicC0AlphaOn.christoffelQuadraticRicciEntryHolderConst_nonneg
            hΓB hΓH i j))
    (by
      have hraw := ParabolicC0AlphaOn.ricciDeTurck_schematic_with
        (M := M) (D := D) (H := H) (MB := R) (MH := R)
        (DB := RD) (DH := RD) (HB := RH) (HH := RH)
        hR hRD hRD hRH hRH
        (fun a b => ParabolicC0AlphaNormLe.c0AlphaWith_self (hM a b))
        (fun a b c => ParabolicC0AlphaNormLe.c0AlphaWith_self (hD a b c))
        (fun a b i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hH a b i j))
        hδpos hdet
      change @ParabolicC0AlphaWith X (n → n → 𝕜) _ Pi.normedAddCommGroup _ _ _ _ _
      constructor
      · intro z hz
        unfold ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
        simpa only using hraw.1 hz
      · intro p hp q hq
        unfold ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
        simpa only using hraw.2 hp hq)

/-- Entrywise primitive controls, primitive difference controls, and a common determinant lower
bound package schematic Ricci-DeTurck RHS differences with the corresponding single-radius
`C^{0,α}` bound. -/
theorem ricciDeTurckSchematicMatrix_sub_entrywise_of_entries {n 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {R Rd : n → n → ℝ} {RD RDd : n → n → n → ℝ}
    {RH RHd : n → n → n → n → ℝ} {δ : ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    {H K : ℝ × X → n → n → n → n → 𝕜}
    (hM : ∀ a b, ParabolicC0AlphaNormLe (R a b) α (fun z => M z a b) s)
    (hN : ∀ a b, ParabolicC0AlphaNormLe (R a b) α (fun z => N z a b) s)
    (hMdiff : ∀ a b, ParabolicC0AlphaNormLe (Rd a b) α
      (fun z => M z a b - N z a b) s)
    (hD : ∀ a b c, ParabolicC0AlphaNormLe (RD a b c) α (fun z => D z a b c) s)
    (hE : ∀ a b c, ParabolicC0AlphaNormLe (RD a b c) α (fun z => E z a b c) s)
    (hDdiff : ∀ a b c, ParabolicC0AlphaNormLe (RDd a b c) α
      (fun z => D z a b c - E z a b c) s)
    (hK : ∀ a b i j, ParabolicC0AlphaNormLe (RH a b i j) α
      (fun z => K z a b i j) s)
    (hHdiff : ∀ a b i j, ParabolicC0AlphaNormLe (RHd a b i j) α
      (fun z => H z a b i j - K z a b i j) s)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicC0AlphaNormLe
      (ParabolicC0AlphaOn.ricciDeTurckSchematicEntrywiseSubBoundConst
          (𝕜 := 𝕜) δ R Rd RD RDd RH RHd +
        ParabolicC0AlphaOn.ricciDeTurckSchematicEntrywiseSubHolderConst
          (𝕜 := 𝕜) δ R R Rd Rd RD RD RDd RDd RH RH RHd RHd)
      α
      (fun z : ℝ × X =>
        ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix (M z) (D z) (H z) -
          ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix (N z) (E z) (K z)) s := by
  have hR : ∀ a b, 0 ≤ R a b := fun a b => (hM a b).nonneg
  have hRd : ∀ a b, 0 ≤ Rd a b := fun a b => (hMdiff a b).nonneg
  have hRD : ∀ a b c, 0 ≤ RD a b c := fun a b c => (hD a b c).nonneg
  have hRDd : ∀ a b c, 0 ≤ RDd a b c := fun a b c => (hDdiff a b c).nonneg
  have hRH : ∀ a b i j, 0 ≤ RH a b i j := fun a b i j => (hK a b i j).nonneg
  have hRHd : ∀ a b i j, 0 ≤ RHd a b i j := fun a b i j => (hHdiff a b i j).nonneg
  let ΓB : n → n → n → ℝ := fun a b c =>
    ParabolicC0AlphaOn.matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ R RD a b c
  let ΓH : n → n → n → ℝ := fun a b c =>
    ParabolicC0AlphaOn.matrixInvChristoffelEntryHolderConst (𝕜 := 𝕜) δ R R RD RD a b c
  let ΓdB : n → n → n → ℝ := fun a b c =>
    ParabolicC0AlphaOn.matrixInvChristoffelEntrySubBoundConst
      (𝕜 := 𝕜) δ R Rd RD RDd a b c
  let ΓdH : n → n → n → ℝ := fun a b c =>
    ParabolicC0AlphaOn.matrixInvChristoffelEntrySubHolderConst
      (𝕜 := 𝕜) δ R R Rd Rd RD RD RDd RDd a b c
  have hΓB : ∀ a b c, 0 ≤ ΓB a b c := by
    intro a b c
    exact ParabolicC0AlphaOn.matrixInvChristoffelEntryBoundConst_nonneg
      (𝕜 := 𝕜) hδpos R hRD a b c
  have hΓH : ∀ a b c, 0 ≤ ΓH a b c := by
    intro a b c
    exact ParabolicC0AlphaOn.matrixInvChristoffelEntryHolderConst_nonneg
      (𝕜 := 𝕜) hR hδpos hRD hRD a b c
  have hΓdB : ∀ a b c, 0 ≤ ΓdB a b c := by
    intro a b c
    exact ParabolicC0AlphaOn.matrixInvChristoffelEntrySubBoundConst_nonneg
      (𝕜 := 𝕜) hδpos hRd hRD hRDd a b c
  have hΓdH : ∀ a b c, 0 ≤ ΓdH a b c := by
    intro a b c
    exact ParabolicC0AlphaOn.matrixInvChristoffelEntrySubHolderConst_nonneg
      (𝕜 := 𝕜) hδpos hR hRd hRd hRD hRD hRDd hRDd a b c
  have hB_nonneg :
      0 ≤ ParabolicC0AlphaOn.ricciDeTurckSchematicEntrywiseSubBoundConst
        (𝕜 := 𝕜) δ R Rd RD RDd RH RHd := by
    simpa [ParabolicC0AlphaOn.ricciDeTurckSchematicEntrywiseSubBoundConst, ΓB, ΓdB]
      using
        (ParabolicC0AlphaOn.ricciDeTurckSchematicFromChristoffelSubBoundConst_nonneg
          (𝕜 := 𝕜) hδpos hRd hRH hRHd hΓB hΓB hΓdB)
  have hH_nonneg :
      0 ≤ ParabolicC0AlphaOn.ricciDeTurckSchematicEntrywiseSubHolderConst
        (𝕜 := 𝕜) δ R R Rd Rd RD RD RDd RDd RH RH RHd RHd := by
    simpa [ParabolicC0AlphaOn.ricciDeTurckSchematicEntrywiseSubHolderConst,
      ΓB, ΓH, ΓdB, ΓdH] using
        (ParabolicC0AlphaOn.ricciDeTurckSchematicFromChristoffelSubHolderConst_nonneg
          (𝕜 := 𝕜) hδpos hR hRd hRd hRH hRH hRHd hRHd
          hΓB hΓH hΓB hΓH hΓdB hΓdH)
  exact ParabolicC0AlphaNormLe.of_c0AlphaWith hB_nonneg hH_nonneg
    (ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix_sub_with_entrywise
      (M := M) (N := N) (D := D) (E := E) (Hc := H) (Kc := K)
      (MB := R) (MH := R) (MBd := Rd) (MHd := Rd)
      (DB := RD) (DH := RD) (DDB := RDd) (DDH := RDd)
      (HB := RH) (HH := RH) (HBd := RHd) (HHd := RHd)
      hR hRd hRd hRD hRD hRDd hRDd hRH hRH hRHd hRHd
      (fun a b => ParabolicC0AlphaNormLe.c0AlphaWith_self (hM a b))
      (fun a b => ParabolicC0AlphaNormLe.c0AlphaWith_self (hN a b))
      (fun a b => ParabolicC0AlphaNormLe.c0AlphaWith_self (hMdiff a b))
      (fun a b c => ParabolicC0AlphaNormLe.c0AlphaWith_self (hD a b c))
      (fun a b c => ParabolicC0AlphaNormLe.c0AlphaWith_self (hE a b c))
      (fun a b c => ParabolicC0AlphaNormLe.c0AlphaWith_self (hDdiff a b c))
      (fun a b i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hK a b i j))
      (fun a b i j => ParabolicC0AlphaNormLe.c0AlphaWith_self (hHdiff a b i j))
      hδpos hdetM hdetN)

end ParabolicC0AlphaNormLe

namespace ParabolicC0AlphaOn

variable {X : Type*} [PseudoMetricSpace X]
variable {α : ℝ} {s : Set (ℝ × X)}

/-- Compact-domain version of `ricciDeTurckSchematicMatrix_sub_with_entrywise`: pointwise
nonvanishing of both metric determinants supplies one common determinant lower bound. -/
theorem ricciDeTurckSchematicMatrix_sub_with_entrywise_of_isCompact_det_ne_zero
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)}
    {MB MH MBd MHd : n → n → ℝ} {DB DH DDB DDH : n → n → n → ℝ}
    {HB HH HBd HHd : n → n → n → n → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    {Hc Kc : ℝ × X → n → n → n → n → 𝕜}
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (hMB : ∀ a b, 0 ≤ MB a b) (hMH : ∀ a b, 0 ≤ MH a b)
    (hMBd : ∀ a b, 0 ≤ MBd a b) (hMHd : ∀ a b, 0 ≤ MHd a b)
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hDH : ∀ a b c, 0 ≤ DH a b c)
    (hDDB : ∀ a b c, 0 ≤ DDB a b c) (hDDH : ∀ a b c, 0 ≤ DDH a b c)
    (hHB : ∀ a b i j, 0 ≤ HB a b i j) (hHH : ∀ a b i j, 0 ≤ HH a b i j)
    (hHBd : ∀ a b i j, 0 ≤ HBd a b i j)
    (hHHd : ∀ a b i j, 0 ≤ HHd a b i j)
    (hM : ∀ a b, ParabolicC0AlphaWith (MB a b) (MH a b) α (fun z => M z a b) Kdom)
    (hN : ∀ a b, ParabolicC0AlphaWith (MB a b) (MH a b) α (fun z => N z a b) Kdom)
    (hMdiff : ∀ a b,
      ParabolicC0AlphaWith (MBd a b) (MHd a b) α (fun z => M z a b - N z a b)
        Kdom)
    (hD : ∀ a b c, ParabolicC0AlphaWith (DB a b c) (DH a b c) α
      (fun z => D z a b c) Kdom)
    (hE : ∀ a b c, ParabolicC0AlphaWith (DB a b c) (DH a b c) α
      (fun z => E z a b c) Kdom)
    (hDdiff : ∀ a b c,
      ParabolicC0AlphaWith (DDB a b c) (DDH a b c) α
        (fun z => D z a b c - E z a b c) Kdom)
    (hKc : ∀ a b i j, ParabolicC0AlphaWith (HB a b i j) (HH a b i j) α
      (fun z => Kc z a b i j) Kdom)
    (hHdiff : ∀ a b i j,
      ParabolicC0AlphaWith (HBd a b i j) (HHd a b i j) α
        (fun z => Hc z a b i j - Kc z a b i j) Kdom)
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (N z).det ≠ 0) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (ricciDeTurckSchematicEntrywiseSubBoundConst
          (𝕜 := 𝕜) δ MB MBd DB DDB HB HBd)
        (ricciDeTurckSchematicEntrywiseSubHolderConst
          (𝕜 := 𝕜) δ MB MH MBd MHd DB DH DDB DDH HB HH HBd HHd)
        α
        (fun z : ℝ × X =>
          ricciDeTurckSchematicMatrix (M z) (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (E z) (Kc z)) Kdom := by
  have hMctrl : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) Kdom := by
    intro a b
    exact ⟨MB a b, hMB a b, MH a b, hMH a b, hM a b⟩
  have hNctrl : ∀ a b, ParabolicC0AlphaOn α (fun z => N z a b) Kdom := by
    intro a b
    exact ⟨MB a b, hMB a b, MH a b, hMH a b, hN a b⟩
  rcases matrix_det_pair_exists_pos_norm_lower_bound_of_isCompact
      (K := Kdom) (M := M) (N := N) hKdom hα hMctrl hNctrl hdetM_ne hdetN_ne with
    ⟨δ, hδpos, hdetM, hdetN⟩
  exact ⟨δ, hδpos, ricciDeTurckSchematicMatrix_sub_with_entrywise
    (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
    hMH hMBd hMHd hDB hDH hDDB hDDH hHB hHH hHBd hHHd
    hM hN hMdiff hD hE hDdiff hKc hHdiff hδpos hdetM hdetN⟩

/-- The primitive-input schematic Ricci-DeTurck RHS preserves existential parabolic `C^{0,α}`
difference control from entrywise metric, first-derivative, and second-derivative controls. -/
theorem ricciDeTurckSchematicMatrix_sub_entrywise {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    {Hc Kc : ℝ × X → n → n → n → n → 𝕜}
    (hM : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) s)
    (hN : ∀ a b, ParabolicC0AlphaOn α (fun z => N z a b) s)
    (hMdiff : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b - N z a b) s)
    (hD : ∀ a b c, ParabolicC0AlphaOn α (fun z => D z a b c) s)
    (hE : ∀ a b c, ParabolicC0AlphaOn α (fun z => E z a b c) s)
    (hDdiff : ∀ a b c,
      ParabolicC0AlphaOn α (fun z => D z a b c - E z a b c) s)
    (hKc : ∀ a b i j, ParabolicC0AlphaOn α (fun z => Kc z a b i j) s)
    (hHdiff : ∀ a b i j,
      ParabolicC0AlphaOn α (fun z => Hc z a b i j - Kc z a b i j) s)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × X =>
        ricciDeTurckSchematicMatrix (M z) (D z) (Hc z) -
          ricciDeTurckSchematicMatrix (N z) (E z) (Kc z)) s := by
  classical
  let Γ : ℝ × X → n → n → n → 𝕜 := fun z a b c =>
    (2 : 𝕜)⁻¹ *
      ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) a l *
        (D z b c l + D z c b l - D z l b c)
  let Λ : ℝ × X → n → n → n → 𝕜 := fun z a b c =>
    (2 : 𝕜)⁻¹ *
      ∑ l : n, ((N z)⁻¹ : Matrix n n 𝕜) a l *
        (E z b c l + E z c b l - E z l b c)
  have hΓ : ∀ a b c, ParabolicC0AlphaOn α (fun z => Γ z a b c) s := by
    intro a b c
    simpa [Γ] using
      matrix_inv_christoffel_entry (M := M) (D := D) hM hD hδpos hdetM a b c
  have hΛ : ∀ a b c, ParabolicC0AlphaOn α (fun z => Λ z a b c) s := by
    intro a b c
    simpa [Λ] using
      matrix_inv_christoffel_entry (M := N) (D := E) hN hE hδpos hdetN a b c
  have hΓdiff : ∀ a b c,
      ParabolicC0AlphaOn α (fun z => Γ z a b c - Λ z a b c) s := by
    intro a b c
    simpa [Γ, Λ] using
      matrix_inv_christoffel_entry_sub_entrywise (M := M) (N := N) (D := D) (E := E)
        hM hN hMdiff hE hDdiff hδpos hdetM hdetN a b c
  unfold ricciDeTurckSchematicMatrix
  simpa [Matrix.sub_apply, Γ, Λ] using
    ricciDeTurck_schematic_from_christoffel_sub_entrywise
      (M := M) (N := N) (H := Hc) (Kc := Kc) (Γ := Γ) (Λ := Λ)
      hM hN hMdiff hKc hHdiff hΓ hΛ hΓdiff hδpos hdetM hdetN

/-- Compact-domain primitive-input schematic Ricci-DeTurck RHS differences preserve existential
parabolic `C^{0,α}` control from entrywise controls and pointwise nonvanishing determinants. -/
theorem ricciDeTurckSchematicMatrix_sub_entrywise_of_isCompact_det_ne_zero
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    {Hc Kc : ℝ × X → n → n → n → n → 𝕜}
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (hM : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) Kdom)
    (hN : ∀ a b, ParabolicC0AlphaOn α (fun z => N z a b) Kdom)
    (hMdiff : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b - N z a b) Kdom)
    (hD : ∀ a b c, ParabolicC0AlphaOn α (fun z => D z a b c) Kdom)
    (hE : ∀ a b c, ParabolicC0AlphaOn α (fun z => E z a b c) Kdom)
    (hDdiff : ∀ a b c,
      ParabolicC0AlphaOn α (fun z => D z a b c - E z a b c) Kdom)
    (hKc : ∀ a b i j, ParabolicC0AlphaOn α (fun z => Kc z a b i j) Kdom)
    (hHdiff : ∀ a b i j,
      ParabolicC0AlphaOn α (fun z => Hc z a b i j - Kc z a b i j) Kdom)
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (N z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ParabolicC0AlphaOn α
        (fun z : ℝ × X =>
          ricciDeTurckSchematicMatrix (M z) (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (E z) (Kc z)) Kdom := by
  rcases matrix_det_pair_exists_pos_norm_lower_bound_of_isCompact
      (K := Kdom) (M := M) (N := N) hKdom hα hM hN hdetM_ne hdetN_ne with
    ⟨δ, hδpos, hdetM, hdetN⟩
  exact ⟨δ, hδpos, ricciDeTurckSchematicMatrix_sub_entrywise
    (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
    hM hN hMdiff hD hE hDdiff hKc hHdiff hδpos hdetM hdetN⟩

/-- Local finite product-cylinder primitive-difference estimates globalize the compact-domain
schematic Ricci-DeTurck RHS difference closure. -/
theorem ricciDeTurckSchematicMatrix_sub_entrywise_of_finset_parabolicCylinder_cover_closedCylinder_variable
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    {Hc Kc : ℝ × X → n → n → n → n → 𝕜}
    (S : Finset (ℝ × X)) (timeRadius spaceRadius : ℝ × X → ℝ)
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (htime_pos : ∀ y ∈ S, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ S, 0 < spaceRadius y)
    (hcover : Kdom ⊆ ⋃ y ∈ S, parabolicCylinder y (timeRadius y) (spaceRadius y))
    (hMlocal : ∀ y ∈ S, ∀ a b,
      ParabolicC0AlphaOn α (fun z => M z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hNlocal : ∀ y ∈ S, ∀ a b,
      ParabolicC0AlphaOn α (fun z => N z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hMdiffLocal : ∀ y ∈ S, ∀ a b,
      ParabolicC0AlphaOn α (fun z => M z a b - N z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hDlocal : ∀ y ∈ S, ∀ a b c,
      ParabolicC0AlphaOn α (fun z => D z a b c)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hElocal : ∀ y ∈ S, ∀ a b c,
      ParabolicC0AlphaOn α (fun z => E z a b c)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hDdiffLocal : ∀ y ∈ S, ∀ a b c,
      ParabolicC0AlphaOn α (fun z => D z a b c - E z a b c)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hKclocal : ∀ y ∈ S, ∀ a b i j,
      ParabolicC0AlphaOn α (fun z => Kc z a b i j)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hHdiffLocal : ∀ y ∈ S, ∀ a b i j,
      ParabolicC0AlphaOn α (fun z => Hc z a b i j - Kc z a b i j)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (N z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ParabolicC0AlphaOn α
        (fun z : ℝ × X =>
          ricciDeTurckSchematicMatrix (M z) (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (E z) (Kc z)) Kdom := by
  have hM : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) Kdom := by
    intro a b
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hMlocal y hy a b)
  have hN : ∀ a b, ParabolicC0AlphaOn α (fun z => N z a b) Kdom := by
    intro a b
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hNlocal y hy a b)
  have hMdiff : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b - N z a b) Kdom := by
    intro a b
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hMdiffLocal y hy a b)
  have hD : ∀ a b c, ParabolicC0AlphaOn α (fun z => D z a b c) Kdom := by
    intro a b c
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hDlocal y hy a b c)
  have hE : ∀ a b c, ParabolicC0AlphaOn α (fun z => E z a b c) Kdom := by
    intro a b c
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hElocal y hy a b c)
  have hDdiff : ∀ a b c,
      ParabolicC0AlphaOn α (fun z => D z a b c - E z a b c) Kdom := by
    intro a b c
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hDdiffLocal y hy a b c)
  have hKc : ∀ a b i j, ParabolicC0AlphaOn α (fun z => Kc z a b i j) Kdom := by
    intro a b i j
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hKclocal y hy a b i j)
  have hHdiff : ∀ a b i j,
      ParabolicC0AlphaOn α (fun z => Hc z a b i j - Kc z a b i j) Kdom := by
    intro a b i j
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hHdiffLocal y hy a b i j)
  exact ricciDeTurckSchematicMatrix_sub_entrywise_of_isCompact_det_ne_zero
    (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
    hKdom hα hM hN hMdiff hD hE hDdiff hKc hHdiff hdetM_ne hdetN_ne

/-- Point-dependent local product-cylinder primitive-difference estimates globalize the
compact-domain schematic Ricci-DeTurck RHS difference closure.  Compactness chooses the finite
subcover internally before the determinant lower bound is extracted. -/
theorem ricciDeTurckSchematicMatrix_sub_entrywise_of_isCompact_of_local_closedCylinder_variable
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    {Hc Kc : ℝ × X → n → n → n → n → 𝕜}
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (timeRadius spaceRadius : ℝ × X → ℝ)
    (htime_pos : ∀ y ∈ Kdom, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ Kdom, 0 < spaceRadius y)
    (hMlocal : ∀ y ∈ Kdom, ∀ a b,
      ParabolicC0AlphaOn α (fun z => M z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hNlocal : ∀ y ∈ Kdom, ∀ a b,
      ParabolicC0AlphaOn α (fun z => N z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hMdiffLocal : ∀ y ∈ Kdom, ∀ a b,
      ParabolicC0AlphaOn α (fun z => M z a b - N z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hDlocal : ∀ y ∈ Kdom, ∀ a b c,
      ParabolicC0AlphaOn α (fun z => D z a b c)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hElocal : ∀ y ∈ Kdom, ∀ a b c,
      ParabolicC0AlphaOn α (fun z => E z a b c)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hDdiffLocal : ∀ y ∈ Kdom, ∀ a b c,
      ParabolicC0AlphaOn α (fun z => D z a b c - E z a b c)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hKclocal : ∀ y ∈ Kdom, ∀ a b i j,
      ParabolicC0AlphaOn α (fun z => Kc z a b i j)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hHdiffLocal : ∀ y ∈ Kdom, ∀ a b i j,
      ParabolicC0AlphaOn α (fun z => Hc z a b i j - Kc z a b i j)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (N z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ParabolicC0AlphaOn α
        (fun z : ℝ × X =>
          ricciDeTurckSchematicMatrix (M z) (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (E z) (Kc z)) Kdom := by
  have hM : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) Kdom := by
    intro a b
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hKdom hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hMlocal y hy a b)
  have hN : ∀ a b, ParabolicC0AlphaOn α (fun z => N z a b) Kdom := by
    intro a b
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hKdom hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hNlocal y hy a b)
  have hMdiff : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b - N z a b) Kdom := by
    intro a b
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hKdom hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hMdiffLocal y hy a b)
  have hD : ∀ a b c, ParabolicC0AlphaOn α (fun z => D z a b c) Kdom := by
    intro a b c
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hKdom hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hDlocal y hy a b c)
  have hE : ∀ a b c, ParabolicC0AlphaOn α (fun z => E z a b c) Kdom := by
    intro a b c
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hKdom hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hElocal y hy a b c)
  have hDdiff : ∀ a b c,
      ParabolicC0AlphaOn α (fun z => D z a b c - E z a b c) Kdom := by
    intro a b c
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hKdom hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hDdiffLocal y hy a b c)
  have hKc : ∀ a b i j, ParabolicC0AlphaOn α (fun z => Kc z a b i j) Kdom := by
    intro a b i j
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hKdom hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hKclocal y hy a b i j)
  have hHdiff : ∀ a b i j,
      ParabolicC0AlphaOn α (fun z => Hc z a b i j - Kc z a b i j) Kdom := by
    intro a b i j
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hKdom hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hHdiffLocal y hy a b i j)
  exact ricciDeTurckSchematicMatrix_sub_entrywise_of_isCompact_det_ne_zero
    (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
    hKdom hα hM hN hMdiff hD hE hDdiff hKc hHdiff hdetM_ne hdetN_ne

/-- Existential point-local product-cylinder primitive-difference estimates globalize the
compact-domain schematic Ricci-DeTurck RHS difference closure.  This form lets each compact point
provide its own local cylinder radii. -/
theorem ricciDeTurckSchematicMatrix_sub_entrywise_of_isCompact_of_exists_local_closedCylinder
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    {Hc Kc : ℝ × X → n → n → n → n → 𝕜}
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (hlocal : ∀ y ∈ Kdom, ∃ timeRadius > 0, ∃ spaceRadius > 0,
      (∀ a b,
        ParabolicC0AlphaOn α (fun z => M z a b)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ a b,
        ParabolicC0AlphaOn α (fun z => N z a b)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ a b,
        ParabolicC0AlphaOn α (fun z => M z a b - N z a b)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ a b c,
        ParabolicC0AlphaOn α (fun z => D z a b c)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ a b c,
        ParabolicC0AlphaOn α (fun z => E z a b c)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ a b c,
        ParabolicC0AlphaOn α (fun z => D z a b c - E z a b c)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ a b i j,
        ParabolicC0AlphaOn α (fun z => Kc z a b i j)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ a b i j,
        ParabolicC0AlphaOn α (fun z => Hc z a b i j - Kc z a b i j)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))))
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (N z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ParabolicC0AlphaOn α
        (fun z : ℝ × X =>
          ricciDeTurckSchematicMatrix (M z) (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (E z) (Kc z)) Kdom := by
  have hM : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) Kdom := by
    intro a b
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hKdom hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.1 a b⟩)
  have hN : ∀ a b, ParabolicC0AlphaOn α (fun z => N z a b) Kdom := by
    intro a b
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hKdom hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.2.1 a b⟩)
  have hMdiff : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b - N z a b) Kdom := by
    intro a b
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hKdom hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.2.2.1 a b⟩)
  have hD : ∀ a b c, ParabolicC0AlphaOn α (fun z => D z a b c) Kdom := by
    intro a b c
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hKdom hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.2.2.2.1 a b c⟩)
  have hE : ∀ a b c, ParabolicC0AlphaOn α (fun z => E z a b c) Kdom := by
    intro a b c
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hKdom hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.2.2.2.2.1 a b c⟩)
  have hDdiff : ∀ a b c,
      ParabolicC0AlphaOn α (fun z => D z a b c - E z a b c) Kdom := by
    intro a b c
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hKdom hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.2.2.2.2.2.1 a b c⟩)
  have hKc : ∀ a b i j, ParabolicC0AlphaOn α (fun z => Kc z a b i j) Kdom := by
    intro a b i j
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hKdom hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.2.2.2.2.2.2.1 a b i j⟩)
  have hHdiff : ∀ a b i j,
      ParabolicC0AlphaOn α (fun z => Hc z a b i j - Kc z a b i j) Kdom := by
    intro a b i j
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hKdom hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace,
          hdata.2.2.2.2.2.2.2 a b i j⟩)
  exact ricciDeTurckSchematicMatrix_sub_entrywise_of_isCompact_det_ne_zero
    (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
    hKdom hα hM hN hMdiff hD hE hDdiff hKc hHdiff hdetM_ne hdetN_ne

/-- The schematic Ricci-DeTurck coordinate entry is pointwise Lipschitz in the primitive metric,
first-derivative, and second-derivative arrays, on entrywise bounded matrices with a common
determinant lower bound. -/
theorem ricciDeTurck_schematic_entry_norm_sub_le {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} {HB : n → n → n → n → ℝ}
    (M N : Matrix n n 𝕜) (D E : n → n → n → 𝕜)
    (H K : n → n → n → n → 𝕜)
    (hM : ∀ a b, ‖M a b‖ ≤ C a b) (hN : ∀ a b, ‖N a b‖ ≤ C a b)
    (hD : ∀ a b c, ‖D a b c‖ ≤ DB a b c)
    (hE : ∀ a b c, ‖E a b c‖ ≤ DB a b c)
    (hK : ∀ a b i j, ‖K a b i j‖ ≤ HB a b i j)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖)
    (i j : n) :
    ‖(let Γ : n → n → n → 𝕜 := fun a b c =>
          (2 : 𝕜)⁻¹ *
            ∑ l : n, (M⁻¹ : Matrix n n 𝕜) a l *
              (D b c l + D c b l - D l b c);
        (∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
          ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
            (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) -
      (let Λ : n → n → n → 𝕜 := fun a b c =>
          (2 : 𝕜)⁻¹ *
            ∑ l : n, (N⁻¹ : Matrix n n 𝕜) a l *
              (E b c l + E c b l - E l b c);
        (∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
          ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
            (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)))‖ ≤
      (∑ a : n, ∑ b : n,
        (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * ‖H a b i j - K a b i j‖ +
          HB a b i j * matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N a b)) +
      ((∑ a : n, ∑ b : n,
        (matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB a i j *
            matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E b a b +
          matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB b a b *
            matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E a i j)) +
      (∑ a : n, ∑ b : n,
        (matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB a i b *
            matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E b a j +
          matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB b a j *
            matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E a i b))) := by
  classical
  let Γ : n → n → n → 𝕜 := fun a b c =>
    (2 : 𝕜)⁻¹ *
      ∑ l : n, (M⁻¹ : Matrix n n 𝕜) a l * (D b c l + D c b l - D l b c)
  let Λ : n → n → n → 𝕜 := fun a b c =>
    (2 : 𝕜)⁻¹ *
      ∑ l : n, (N⁻¹ : Matrix n n 𝕜) a l * (E b c l + E c b l - E l b c)
  let ΓB : n → n → n → ℝ :=
    fun a b c => matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB a b c
  let ΓL : n → n → n → ℝ :=
    fun a b c => matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E a b c
  let principalBound : ℝ := ∑ a : n, ∑ b : n,
    (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * ‖H a b i j - K a b i j‖ +
      HB a b i j * matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N a b)
  let quadraticActual : ℝ :=
    (∑ a : n, ∑ b : n,
      (ΓB a i j * ‖Γ b a b - Λ b a b‖ +
        ΓB b a b * ‖Γ a i j - Λ a i j‖)) +
    (∑ a : n, ∑ b : n,
      (ΓB a i b * ‖Γ b a j - Λ b a j‖ +
        ΓB b a j * ‖Γ a i b - Λ a i b‖))
  let quadraticBound : ℝ :=
    (∑ a : n, ∑ b : n,
      (ΓB a i j * ΓL b a b + ΓB b a b * ΓL a i j)) +
    (∑ a : n, ∑ b : n,
      (ΓB a i b * ΓL b a j + ΓB b a j * ΓL a i b))
  have hΓbound : ∀ a b c, ‖Γ a b c‖ ≤ ΓB a b c := by
    intro a b c
    simpa [Γ, ΓB] using
      matrix_inv_christoffel_entry_norm_le_bound M D hM hD hδpos hdetM a b c
  have hΛbound : ∀ a b c, ‖Λ a b c‖ ≤ ΓB a b c := by
    intro a b c
    simpa [Λ, ΓB] using
      matrix_inv_christoffel_entry_norm_le_bound N E hN hE hδpos hdetN a b c
  have hΓdiff : ∀ a b c, ‖Γ a b c - Λ a b c‖ ≤ ΓL a b c := by
    intro a b c
    simpa [Γ, Λ, ΓL] using
      matrix_inv_christoffel_entry_norm_sub_le_bound M N D E hM hN hE hδpos hdetM hdetN a b c
  have hbase :
      ‖((∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
          ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
            (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) -
        ((∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
          ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
            (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)))‖ ≤
        principalBound + quadraticActual := by
    simpa [principalBound, quadraticActual, ΓB] using
      ricciDeTurck_schematic_from_christoffel_entry_norm_sub_le
        M N H K Γ Λ hM hN hK hΓbound hΛbound hδpos hdetM hdetN i j
  have hquad : quadraticActual ≤ quadraticBound := by
    have hleft : (∑ a : n, ∑ b : n,
        (ΓB a i j * ‖Γ b a b - Λ b a b‖ +
          ΓB b a b * ‖Γ a i j - Λ a i j‖)) ≤
        ∑ a : n, ∑ b : n,
          (ΓB a i j * ΓL b a b + ΓB b a b * ΓL a i j) := by
      exact Finset.sum_le_sum fun a _ha =>
        Finset.sum_le_sum fun b _hb => by
          have hΓB_aij_nonneg : 0 ≤ ΓB a i j := (norm_nonneg _).trans (hΓbound a i j)
          have hΓB_bab_nonneg : 0 ≤ ΓB b a b := (norm_nonneg _).trans (hΓbound b a b)
          exact add_le_add
            (mul_le_mul_of_nonneg_left (hΓdiff b a b) hΓB_aij_nonneg)
            (mul_le_mul_of_nonneg_left (hΓdiff a i j) hΓB_bab_nonneg)
    have hright : (∑ a : n, ∑ b : n,
        (ΓB a i b * ‖Γ b a j - Λ b a j‖ +
          ΓB b a j * ‖Γ a i b - Λ a i b‖)) ≤
        ∑ a : n, ∑ b : n,
          (ΓB a i b * ΓL b a j + ΓB b a j * ΓL a i b) := by
      exact Finset.sum_le_sum fun a _ha =>
        Finset.sum_le_sum fun b _hb => by
          have hΓB_aib_nonneg : 0 ≤ ΓB a i b := (norm_nonneg _).trans (hΓbound a i b)
          have hΓB_baj_nonneg : 0 ≤ ΓB b a j := (norm_nonneg _).trans (hΓbound b a j)
          exact add_le_add
            (mul_le_mul_of_nonneg_left (hΓdiff b a j) hΓB_aib_nonneg)
            (mul_le_mul_of_nonneg_left (hΓdiff a i b) hΓB_baj_nonneg)
    exact add_le_add hleft hright
  calc
    ‖(let Γ : n → n → n → 𝕜 := fun a b c =>
          (2 : 𝕜)⁻¹ *
            ∑ l : n, (M⁻¹ : Matrix n n 𝕜) a l *
              (D b c l + D c b l - D l b c);
        (∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
          ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
            (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) -
      (let Λ : n → n → n → 𝕜 := fun a b c =>
          (2 : 𝕜)⁻¹ *
            ∑ l : n, (N⁻¹ : Matrix n n 𝕜) a l *
              (E b c l + E c b l - E l b c);
        (∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
          ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
            (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)))‖ =
        ‖((∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
          ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
            (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) -
        ((∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
          ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
            (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)))‖ := by
      simp [Γ, Λ]
    _ ≤ principalBound + quadraticActual := hbase
    _ ≤ principalBound + quadraticBound :=
      add_le_add (le_refl principalBound) hquad
    _ =
      (∑ a : n, ∑ b : n,
        (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * ‖H a b i j - K a b i j‖ +
          HB a b i j * matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N a b)) +
      ((∑ a : n, ∑ b : n,
        (matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB a i j *
            matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E b a b +
          matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB b a b *
            matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E a i j)) +
      (∑ a : n, ∑ b : n,
        (matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB a i b *
            matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E b a j +
          matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB b a j *
            matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E a i b))) := by
      simp [principalBound, quadraticBound, ΓB, ΓL]

/-- The matrix-valued schematic Ricci-DeTurck coordinate RHS is pointwise Lipschitz in the
elementwise matrix norm for the primitive metric, first-derivative, and second-derivative arrays. -/
theorem ricciDeTurck_schematic_norm_sub_le {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} {HB : n → n → n → n → ℝ}
    (M N : Matrix n n 𝕜) (D E : n → n → n → 𝕜)
    (H K : n → n → n → n → 𝕜)
    (hM : ∀ a b, ‖M a b‖ ≤ C a b) (hN : ∀ a b, ‖N a b‖ ≤ C a b)
    (hD : ∀ a b c, ‖D a b c‖ ≤ DB a b c)
    (hE : ∀ a b c, ‖E a b c‖ ≤ DB a b c)
    (hK : ∀ a b i j, ‖K a b i j‖ ≤ HB a b i j)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖) :
    ‖((fun i j =>
        let Γ : n → n → n → 𝕜 := fun a b c =>
          (2 : 𝕜)⁻¹ *
            ∑ l : n, (M⁻¹ : Matrix n n 𝕜) a l *
              (D b c l + D c b l - D l b c);
        (∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
          ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
            (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) : Matrix n n 𝕜) -
      ((fun i j =>
        let Λ : n → n → n → 𝕜 := fun a b c =>
          (2 : 𝕜)⁻¹ *
            ∑ l : n, (N⁻¹ : Matrix n n 𝕜) a l *
              (E b c l + E c b l - E l b c);
        (∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
          ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
            (∑ a : n, ∑ b : n, Λ a i b * Λ b a j))) : Matrix n n 𝕜)‖ ≤
      ∑ i : n, ∑ j : n,
        ((∑ a : n, ∑ b : n,
          (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * ‖H a b i j - K a b i j‖ +
            HB a b i j * matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N a b)) +
        ((∑ a : n, ∑ b : n,
          (matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB a i j *
              matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E b a b +
            matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB b a b *
              matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E a i j)) +
        (∑ a : n, ∑ b : n,
          (matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB a i b *
              matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E b a j +
            matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB b a j *
              matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E a i b)))) := by
  classical
  let entryBound : n → n → ℝ := fun i j =>
    (∑ a : n, ∑ b : n,
      (matrixInvEntryBoundConst (𝕜 := 𝕜) δ C a b * ‖H a b i j - K a b i j‖ +
        HB a b i j * matrixInvEntryLipschitzBound (𝕜 := 𝕜) δ C M N a b)) +
    ((∑ a : n, ∑ b : n,
      (matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB a i j *
          matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E b a b +
        matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB b a b *
          matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E a i j)) +
    (∑ a : n, ∑ b : n,
      (matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB a i b *
          matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E b a j +
        matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB b a j *
          matrixInvChristoffelEntryLipschitzBound (𝕜 := 𝕜) δ C DB M N D E a i b)))
  have hentry : ∀ i j,
      ‖(let Γ : n → n → n → 𝕜 := fun a b c =>
            (2 : 𝕜)⁻¹ *
              ∑ l : n, (M⁻¹ : Matrix n n 𝕜) a l *
                (D b c l + D c b l - D l b c);
          (∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
            ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
              (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) -
        (let Λ : n → n → n → 𝕜 := fun a b c =>
            (2 : 𝕜)⁻¹ *
              ∑ l : n, (N⁻¹ : Matrix n n 𝕜) a l *
                (E b c l + E c b l - E l b c);
          (∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
            ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
              (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)))‖ ≤ entryBound i j := by
    intro i j
    simpa [entryBound] using
      ricciDeTurck_schematic_entry_norm_sub_le M N D E H K
        hM hN hD hE hK hδpos hdetM hdetN i j
  have hentry_nonneg : ∀ i j, 0 ≤ entryBound i j := by
    intro i j
    exact (norm_nonneg _).trans (hentry i j)
  have hrow_nonneg : ∀ i, 0 ≤ ∑ j : n, entryBound i j := by
    intro i
    exact Finset.sum_nonneg fun j _hj => hentry_nonneg i j
  have htotal_nonneg : 0 ≤ ∑ i : n, ∑ j : n, entryBound i j :=
    Finset.sum_nonneg fun i _hi => hrow_nonneg i
  have hnorm :
      ‖((fun i j =>
          let Γ : n → n → n → 𝕜 := fun a b c =>
            (2 : 𝕜)⁻¹ *
              ∑ l : n, (M⁻¹ : Matrix n n 𝕜) a l *
                (D b c l + D c b l - D l b c);
          (∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
            ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
              (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) : Matrix n n 𝕜) -
        ((fun i j =>
          let Λ : n → n → n → 𝕜 := fun a b c =>
            (2 : 𝕜)⁻¹ *
              ∑ l : n, (N⁻¹ : Matrix n n 𝕜) a l *
                (E b c l + E c b l - E l b c);
          (∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
            ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
              (∑ a : n, ∑ b : n, Λ a i b * Λ b a j))) : Matrix n n 𝕜)‖ ≤
        ∑ i : n, ∑ j : n, entryBound i j := by
    refine (Matrix.norm_le_iff htotal_nonneg).2 ?_
    intro i j
    calc
      ‖(((fun i j =>
          let Γ : n → n → n → 𝕜 := fun a b c =>
            (2 : 𝕜)⁻¹ *
              ∑ l : n, (M⁻¹ : Matrix n n 𝕜) a l *
                (D b c l + D c b l - D l b c);
          (∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
            ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
              (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) : Matrix n n 𝕜) -
        ((fun i j =>
          let Λ : n → n → n → 𝕜 := fun a b c =>
            (2 : 𝕜)⁻¹ *
              ∑ l : n, (N⁻¹ : Matrix n n 𝕜) a l *
                (E b c l + E c b l - E l b c);
          (∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
            ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
              (∑ a : n, ∑ b : n, Λ a i b * Λ b a j))) : Matrix n n 𝕜)) i j‖ =
          ‖(let Γ : n → n → n → 𝕜 := fun a b c =>
                (2 : 𝕜)⁻¹ *
                  ∑ l : n, (M⁻¹ : Matrix n n 𝕜) a l *
                    (D b c l + D c b l - D l b c);
              (∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
                ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
                  (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) -
            (let Λ : n → n → n → 𝕜 := fun a b c =>
                (2 : 𝕜)⁻¹ *
                  ∑ l : n, (N⁻¹ : Matrix n n 𝕜) a l *
                    (E b c l + E c b l - E l b c);
              (∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
                ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
                  (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)))‖ := rfl
      _ ≤ entryBound i j := hentry i j
      _ ≤ ∑ j : n, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hentry_nonneg i k) (Finset.mem_univ j)
      _ ≤ ∑ i : n, ∑ j : n, entryBound i j :=
        Finset.single_le_sum (fun k _hk => hrow_nonneg k) (Finset.mem_univ i)
  simpa [entryBound] using hnorm

/-- The schematic Ricci-DeTurck coordinate entry is Lipschitz in primitive inputs with the
Christoffel contribution controlled by a single uniform derivative-array difference bound and
the metric matrix norm. -/
theorem ricciDeTurck_schematic_entry_norm_sub_le_const {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} {HB : n → n → n → n → ℝ} {ηD : ℝ}
    (M N : Matrix n n 𝕜) (D E : n → n → n → 𝕜)
    (H K : n → n → n → n → 𝕜)
    (hM : ∀ a b, ‖M a b‖ ≤ C a b) (hN : ∀ a b, ‖N a b‖ ≤ C a b)
    (hD : ∀ a b c, ‖D a b c‖ ≤ DB a b c)
    (hE : ∀ a b c, ‖E a b c‖ ≤ DB a b c)
    (hK : ∀ a b i j, ‖K a b i j‖ ≤ HB a b i j)
    (hηD : 0 ≤ ηD) (hDdiff : ∀ a b c, ‖D a b c - E a b c‖ ≤ ηD)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖)
    (i j : n) :
    ‖(let Γ : n → n → n → 𝕜 := fun a b c =>
          (2 : 𝕜)⁻¹ *
            ∑ l : n, (M⁻¹ : Matrix n n 𝕜) a l *
              (D b c l + D c b l - D l b c);
        (∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
          ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
            (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) -
      (let Λ : n → n → n → 𝕜 := fun a b c =>
          (2 : 𝕜)⁻¹ *
            ∑ l : n, (N⁻¹ : Matrix n n 𝕜) a l *
              (E b c l + E c b l - E l b c);
        (∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
          ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
            (∑ a : n, ∑ b : n, Λ a i b * Λ b a j)))‖ ≤
      (matrixInvTwoIndexContractCoeffDiffConst (𝕜 := 𝕜) δ C *
          ‖((fun a b => H a b i j) : Matrix n n 𝕜) -
            ((fun a b => K a b i j) : Matrix n n 𝕜)‖ +
        matrixInvTwoIndexContractMetricDiffConst (𝕜 := 𝕜) δ C HB i j * ‖M - N‖) +
        christoffelQuadraticRicciEntryLipschitzConst
          (fun a b c => matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB a b c)
          i j *
          matrixInvChristoffelArrayDiffBoundConst (𝕜 := 𝕜) δ C DB ηD ‖M - N‖ := by
  classical
  let Γ : n → n → n → 𝕜 := fun a b c =>
    (2 : 𝕜)⁻¹ *
      ∑ l : n, (M⁻¹ : Matrix n n 𝕜) a l * (D b c l + D c b l - D l b c)
  let Λ : n → n → n → 𝕜 := fun a b c =>
    (2 : 𝕜)⁻¹ *
      ∑ l : n, (N⁻¹ : Matrix n n 𝕜) a l * (E b c l + E c b l - E l b c)
  let ΓB : n → n → n → ℝ := fun a b c =>
    matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB a b c
  let ηγ : ℝ := matrixInvChristoffelArrayDiffBoundConst (𝕜 := 𝕜) δ C DB ηD ‖M - N‖
  have hΓbound : ∀ a b c, ‖Γ a b c‖ ≤ ΓB a b c := by
    intro a b c
    simpa [Γ, ΓB] using
      matrix_inv_christoffel_entry_norm_le_bound M D hM hD hδpos hdetM a b c
  have hΛbound : ∀ a b c, ‖Λ a b c‖ ≤ ΓB a b c := by
    intro a b c
    simpa [Λ, ΓB] using
      matrix_inv_christoffel_entry_norm_le_bound N E hN hE hδpos hdetN a b c
  have hΓdiff : ∀ a b c, ‖Γ a b c - Λ a b c‖ ≤ ηγ := by
    intro a b c
    simpa [Γ, Λ, ηγ] using
      matrix_inv_christoffel_entry_norm_sub_le_array_const M N D E
        hM hN hE hηD hDdiff hδpos hdetM hdetN a b c
  simpa [Γ, Λ, ΓB, ηγ] using
    ricciDeTurck_schematic_from_christoffel_entry_norm_sub_le_const
      M N H K Γ Λ hM hN hK hΓbound hΛbound hΓdiff hδpos hdetM hdetN i j

/-- The matrix-valued schematic Ricci-DeTurck RHS is Lipschitz in primitive inputs with the
Christoffel contribution controlled by a single uniform derivative-array difference bound and
the metric matrix norm. -/
theorem ricciDeTurck_schematic_norm_sub_le_const {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} {HB : n → n → n → n → ℝ} {ηD : ℝ}
    (M N : Matrix n n 𝕜) (D E : n → n → n → 𝕜)
    (H K : n → n → n → n → 𝕜)
    (hM : ∀ a b, ‖M a b‖ ≤ C a b) (hN : ∀ a b, ‖N a b‖ ≤ C a b)
    (hD : ∀ a b c, ‖D a b c‖ ≤ DB a b c)
    (hE : ∀ a b c, ‖E a b c‖ ≤ DB a b c)
    (hK : ∀ a b i j, ‖K a b i j‖ ≤ HB a b i j)
    (hηD : 0 ≤ ηD) (hDdiff : ∀ a b c, ‖D a b c - E a b c‖ ≤ ηD)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖) :
    ‖((fun i j =>
        let Γ : n → n → n → 𝕜 := fun a b c =>
          (2 : 𝕜)⁻¹ *
            ∑ l : n, (M⁻¹ : Matrix n n 𝕜) a l *
              (D b c l + D c b l - D l b c);
        (∑ a : n, ∑ b : n, (M⁻¹ : Matrix n n 𝕜) a b * H a b i j) +
          ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
            (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) : Matrix n n 𝕜) -
      ((fun i j =>
        let Λ : n → n → n → 𝕜 := fun a b c =>
          (2 : 𝕜)⁻¹ *
            ∑ l : n, (N⁻¹ : Matrix n n 𝕜) a l *
              (E b c l + E c b l - E l b c);
        (∑ a : n, ∑ b : n, (N⁻¹ : Matrix n n 𝕜) a b * K a b i j) +
          ((∑ a : n, ∑ b : n, Λ a i j * Λ b a b) -
            (∑ a : n, ∑ b : n, Λ a i b * Λ b a j))) : Matrix n n 𝕜)‖ ≤
      ∑ i : n, ∑ j : n,
        ((matrixInvTwoIndexContractCoeffDiffConst (𝕜 := 𝕜) δ C *
            ‖((fun a b => H a b i j) : Matrix n n 𝕜) -
              ((fun a b => K a b i j) : Matrix n n 𝕜)‖ +
          matrixInvTwoIndexContractMetricDiffConst (𝕜 := 𝕜) δ C HB i j * ‖M - N‖) +
          christoffelQuadraticRicciEntryLipschitzConst
            (fun a b c => matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB a b c)
            i j *
            matrixInvChristoffelArrayDiffBoundConst (𝕜 := 𝕜) δ C DB ηD ‖M - N‖) := by
  classical
  let Γ : n → n → n → 𝕜 := fun a b c =>
    (2 : 𝕜)⁻¹ *
      ∑ l : n, (M⁻¹ : Matrix n n 𝕜) a l * (D b c l + D c b l - D l b c)
  let Λ : n → n → n → 𝕜 := fun a b c =>
    (2 : 𝕜)⁻¹ *
      ∑ l : n, (N⁻¹ : Matrix n n 𝕜) a l * (E b c l + E c b l - E l b c)
  let ΓB : n → n → n → ℝ := fun a b c =>
    matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB a b c
  let ηγ : ℝ := matrixInvChristoffelArrayDiffBoundConst (𝕜 := 𝕜) δ C DB ηD ‖M - N‖
  have hΓbound : ∀ a b c, ‖Γ a b c‖ ≤ ΓB a b c := by
    intro a b c
    simpa [Γ, ΓB] using
      matrix_inv_christoffel_entry_norm_le_bound M D hM hD hδpos hdetM a b c
  have hΛbound : ∀ a b c, ‖Λ a b c‖ ≤ ΓB a b c := by
    intro a b c
    simpa [Λ, ΓB] using
      matrix_inv_christoffel_entry_norm_le_bound N E hN hE hδpos hdetN a b c
  have hΓdiff : ∀ a b c, ‖Γ a b c - Λ a b c‖ ≤ ηγ := by
    intro a b c
    simpa [Γ, Λ, ηγ] using
      matrix_inv_christoffel_entry_norm_sub_le_array_const M N D E
        hM hN hE hηD hDdiff hδpos hdetM hdetN a b c
  simpa [Γ, Λ, ΓB, ηγ] using
    ricciDeTurck_schematic_from_christoffel_norm_sub_le_const
      M N H K Γ Λ hM hN hK hΓbound hΛbound hΓdiff hδpos hdetM hdetN

/-- Uniform bound used for the function-level schematic Ricci-DeTurck difference estimate. -/
def ricciDeTurckSchematicDiffBoundConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (C : n → n → ℝ) (DB : n → n → n → ℝ)
    (HB : n → n → n → n → ℝ) (ηM ηD : ℝ) (ηH : n → n → ℝ) : ℝ :=
  ∑ i : n, ∑ j : n,
    ((matrixInvTwoIndexContractCoeffDiffConst (𝕜 := 𝕜) δ C * ηH i j +
        matrixInvTwoIndexContractMetricDiffConst (𝕜 := 𝕜) δ C HB i j * ηM) +
      christoffelQuadraticRicciEntryLipschitzConst
        (fun a b c => matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB a b c)
        i j *
        matrixInvChristoffelArrayDiffBoundConst (𝕜 := 𝕜) δ C DB ηD ηM)

theorem ricciDeTurckSchematicDiffBoundConst_nonneg {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} (hδpos : 0 < δ) {C : n → n → ℝ}
    {DB : n → n → n → ℝ} (hDB : ∀ a b c, 0 ≤ DB a b c)
    {HB : n → n → n → n → ℝ} (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    {ηM ηD : ℝ} (hηM : 0 ≤ ηM) (hηD : 0 ≤ ηD)
    {ηH : n → n → ℝ} (hηH : ∀ i j, 0 ≤ ηH i j) :
    0 ≤ ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ C DB HB ηM ηD ηH := by
  classical
  refine Finset.sum_nonneg fun i _hi => ?_
  refine Finset.sum_nonneg fun j _hj => ?_
  have hΓB : ∀ a b c,
      0 ≤ matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB a b c := by
    intro a b c
    exact matrixInvChristoffelEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos C hDB a b c
  exact add_nonneg
    (add_nonneg
      (mul_nonneg (matrixInvTwoIndexContractCoeffDiffConst_nonneg (𝕜 := 𝕜) hδpos C)
        (hηH i j))
      (mul_nonneg
        (matrixInvTwoIndexContractMetricDiffConst_nonneg (𝕜 := 𝕜) hδpos hHB i j)
        hηM))
    (mul_nonneg
      (christoffelQuadraticRicciEntryLipschitzConst_nonneg hΓB i j)
      (matrixInvChristoffelArrayDiffBoundConst_nonneg (𝕜 := 𝕜) hδpos hDB hηD hηM))

/-- The schematic Ricci-DeTurck matrix difference constant is linear in a shared comparison
radius when the metric, first-derivative, and principal-coefficient difference radii are all
multiples of that radius. -/
theorem ricciDeTurckSchematicDiffBoundConst_mul_radius {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] (δ : ℝ) (C : n → n → ℝ)
    (DB : n → n → n → ℝ) (HB : n → n → n → n → ℝ)
    (KM KD : ℝ) (KH : n → n → ℝ) (R : ℝ) :
    ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ C DB HB
        (KM * R) (KD * R) (fun i j => KH i j * R) =
      ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ C DB HB KM KD KH * R := by
  classical
  simp_rw [ricciDeTurckSchematicDiffBoundConst,
    matrixInvChristoffelArrayDiffBoundConst_mul_radius, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _hi => ?_
  refine Finset.sum_congr rfl fun j _hj => ?_
  ring

/-- The schematic Ricci-DeTurck matrix difference constant is monotone in the metric,
first-derivative, and principal-coefficient primitive difference radii. -/
theorem ricciDeTurckSchematicDiffBoundConst_mono {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} (hδpos : 0 < δ) {C : n → n → ℝ}
    {DB : n → n → n → ℝ} (hDB : ∀ a b c, 0 ≤ DB a b c)
    {HB : n → n → n → n → ℝ} (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    {ηM ηM' ηD ηD' : ℝ} {ηH ηH' : n → n → ℝ}
    (hηM : ηM ≤ ηM') (hηD : ηD ≤ ηD')
    (hηH : ∀ i j, ηH i j ≤ ηH' i j) :
    ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ C DB HB ηM ηD ηH ≤
      ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ C DB HB ηM' ηD' ηH' := by
  classical
  refine Finset.sum_le_sum fun i _hi => ?_
  refine Finset.sum_le_sum fun j _hj => ?_
  have hΓB : ∀ a b c,
      0 ≤ matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB a b c := by
    intro a b c
    exact matrixInvChristoffelEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos C hDB a b c
  have harray_mono :
      matrixInvChristoffelArrayDiffBoundConst (𝕜 := 𝕜) δ C DB ηD ηM ≤
        matrixInvChristoffelArrayDiffBoundConst (𝕜 := 𝕜) δ C DB ηD' ηM' :=
    matrixInvChristoffelArrayDiffBoundConst_mono (𝕜 := 𝕜) hδpos hDB hηD hηM
  exact add_le_add
    (add_le_add
      (mul_le_mul_of_nonneg_left (hηH i j)
        (matrixInvTwoIndexContractCoeffDiffConst_nonneg (𝕜 := 𝕜) hδpos C))
      (mul_le_mul_of_nonneg_left hηM
        (matrixInvTwoIndexContractMetricDiffConst_nonneg (𝕜 := 𝕜) hδpos hHB i j)))
    (mul_le_mul_of_nonneg_left harray_mono
      (christoffelQuadraticRicciEntryLipschitzConst_nonneg hΓB i j))

/-- Named version of the primitive schematic Ricci-DeTurck matrix Lipschitz estimate. -/
theorem ricciDeTurckSchematicMatrix_norm_sub_le_const {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} {HB : n → n → n → n → ℝ} {ηD : ℝ}
    (M N : Matrix n n 𝕜) (D E : n → n → n → 𝕜)
    (H K : n → n → n → n → 𝕜)
    (hM : ∀ a b, ‖M a b‖ ≤ C a b) (hN : ∀ a b, ‖N a b‖ ≤ C a b)
    (hD : ∀ a b c, ‖D a b c‖ ≤ DB a b c)
    (hE : ∀ a b c, ‖E a b c‖ ≤ DB a b c)
    (hK : ∀ a b i j, ‖K a b i j‖ ≤ HB a b i j)
    (hηD : 0 ≤ ηD) (hDdiff : ∀ a b c, ‖D a b c - E a b c‖ ≤ ηD)
    (hδpos : 0 < δ) (hdetM : δ ≤ ‖M.det‖) (hdetN : δ ≤ ‖N.det‖) :
    ‖ricciDeTurckSchematicMatrix M D H - ricciDeTurckSchematicMatrix N E K‖ ≤
      ∑ i : n, ∑ j : n,
        ((matrixInvTwoIndexContractCoeffDiffConst (𝕜 := 𝕜) δ C *
            ‖((fun a b => H a b i j) : Matrix n n 𝕜) -
              ((fun a b => K a b i j) : Matrix n n 𝕜)‖ +
          matrixInvTwoIndexContractMetricDiffConst (𝕜 := 𝕜) δ C HB i j * ‖M - N‖) +
          christoffelQuadraticRicciEntryLipschitzConst
            (fun a b c => matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB a b c)
            i j *
            matrixInvChristoffelArrayDiffBoundConst (𝕜 := 𝕜) δ C DB ηD ‖M - N‖) := by
  convert ricciDeTurck_schematic_norm_sub_le_const
    (δ := δ) (C := C) (DB := DB) (HB := HB) (ηD := ηD)
    M N D E H K hM hN hD hE hK hηD hDdiff hδpos hdetM hdetN using 1 <;>
    congr 1

/-- Function-level bounded-difference estimate for the finite schematic Ricci-DeTurck RHS.
It packages the pointwise algebraic Lipschitz estimate into the parabolic sup-norm predicate. -/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} {HB : n → n → n → n → ℝ}
    {ηM ηD : ℝ} {ηH : n → n → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    {H K : ℝ × X → n → n → n → n → 𝕜}
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hM : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b, ‖M z a b‖ ≤ C a b)
    (hN : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b, ‖N z a b‖ ≤ C a b)
    (hD : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c, ‖D z a b c‖ ≤ DB a b c)
    (hE : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c, ‖E z a b c‖ ≤ DB a b c)
    (hK : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b i j, ‖K z a b i j‖ ≤ HB a b i j)
    (hηD : 0 ≤ ηD)
    (hMdiff : ∀ ⦃z : ℝ × X⦄, z ∈ s → ‖M z - N z‖ ≤ ηM)
    (hDdiff : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c, ‖D z a b c - E z a b c‖ ≤ ηD)
    (hHdiff : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ i j,
      ‖((fun a b => H z a b i j) : Matrix n n 𝕜) -
        ((fun a b => K z a b i j) : Matrix n n 𝕜)‖ ≤ ηH i j)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicBoundedWith
      (ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ C DB HB ηM ηD ηH)
      (fun z : ℝ × X =>
        ricciDeTurckSchematicMatrix (M z) (D z) (H z) -
          ricciDeTurckSchematicMatrix (N z) (E z) (K z)) s := by
  classical
  intro z hz
  have hpoint :
      ‖ricciDeTurckSchematicMatrix (M z) (D z) (H z) -
          ricciDeTurckSchematicMatrix (N z) (E z) (K z)‖ ≤
        ∑ i : n, ∑ j : n,
          ((matrixInvTwoIndexContractCoeffDiffConst (𝕜 := 𝕜) δ C *
              ‖((fun a b => H z a b i j) : Matrix n n 𝕜) -
                ((fun a b => K z a b i j) : Matrix n n 𝕜)‖ +
            matrixInvTwoIndexContractMetricDiffConst (𝕜 := 𝕜) δ C HB i j *
              ‖M z - N z‖) +
            christoffelQuadraticRicciEntryLipschitzConst
              (fun a b c => matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB a b c)
              i j *
              matrixInvChristoffelArrayDiffBoundConst (𝕜 := 𝕜) δ C DB ηD ‖M z - N z‖) :=
    ricciDeTurckSchematicMatrix_norm_sub_le_const
      (δ := δ) (C := C) (DB := DB) (HB := HB) (ηD := ηD)
      (M z) (N z) (D z) (E z) (H z) (K z)
      (hM hz) (hN hz) (hD hz) (hE hz) (hK hz)
      hηD (hDdiff hz) hδpos (hdetM hz) (hdetN hz)
  refine hpoint.trans ?_
  refine Finset.sum_le_sum fun i _hi => ?_
  refine Finset.sum_le_sum fun j _hj => ?_
  have hΓB : ∀ a b c,
      0 ≤ matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ C DB a b c := by
    intro a b c
    exact matrixInvChristoffelEntryBoundConst_nonneg (𝕜 := 𝕜) hδpos C hDB a b c
  have harray_mono :
      matrixInvChristoffelArrayDiffBoundConst (𝕜 := 𝕜) δ C DB ηD ‖M z - N z‖ ≤
        matrixInvChristoffelArrayDiffBoundConst (𝕜 := 𝕜) δ C DB ηD ηM :=
    matrixInvChristoffelArrayDiffBoundConst_mono_right
      (𝕜 := 𝕜) hδpos hDB (hMdiff hz)
  exact add_le_add
    (add_le_add
      (mul_le_mul_of_nonneg_left (hHdiff hz i j)
        (matrixInvTwoIndexContractCoeffDiffConst_nonneg (𝕜 := 𝕜) hδpos C))
      (mul_le_mul_of_nonneg_left (hMdiff hz)
        (matrixInvTwoIndexContractMetricDiffConst_nonneg (𝕜 := 𝕜) hδpos hHB i j)))
    (mul_le_mul_of_nonneg_left harray_mono
      (christoffelQuadraticRicciEntryLipschitzConst_nonneg hΓB i j))

/-- Function-level schematic Ricci-DeTurck RHS estimate with coarser primitive
difference constants.  This lets local primitive estimates proved with sharper constants be
consumed by a shared finite-cover constant. -/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_of_primitive_le
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜] {δ : ℝ}
    {C : n → n → ℝ} {DB : n → n → n → ℝ} {HB : n → n → n → n → ℝ}
    {ηM0 ηD0 ηM ηD : ℝ} {ηH0 ηH : n → n → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    {H K : ℝ × X → n → n → n → n → 𝕜}
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hηM : ηM0 ≤ ηM) (hηD : ηD0 ≤ ηD)
    (hηH : ∀ i j, ηH0 i j ≤ ηH i j)
    (hM : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b, ‖M z a b‖ ≤ C a b)
    (hN : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b, ‖N z a b‖ ≤ C a b)
    (hD : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c, ‖D z a b c‖ ≤ DB a b c)
    (hE : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c, ‖E z a b c‖ ≤ DB a b c)
    (hK : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b i j, ‖K z a b i j‖ ≤ HB a b i j)
    (hηD0 : 0 ≤ ηD0)
    (hMdiff : ∀ ⦃z : ℝ × X⦄, z ∈ s → ‖M z - N z‖ ≤ ηM0)
    (hDdiff : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c,
      ‖D z a b c - E z a b c‖ ≤ ηD0)
    (hHdiff : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ i j,
      ‖((fun a b => H z a b i j) : Matrix n n 𝕜) -
        ((fun a b => K z a b i j) : Matrix n n 𝕜)‖ ≤ ηH0 i j)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicBoundedWith
      (ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ C DB HB ηM ηD ηH)
      (fun z : ℝ × X =>
        ricciDeTurckSchematicMatrix (M z) (D z) (H z) -
          ricciDeTurckSchematicMatrix (N z) (E z) (K z)) s := by
  have hbase :
      ParabolicBoundedWith
        (ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ C DB HB ηM0 ηD0 ηH0)
        (fun z : ℝ × X =>
          ricciDeTurckSchematicMatrix (M z) (D z) (H z) -
            ricciDeTurckSchematicMatrix (N z) (E z) (K z)) s :=
    ricciDeTurckSchematicMatrix_bounded_sub_le_const
      (s := s) (δ := δ) (C := C) (DB := DB) (HB := HB)
      (ηM := ηM0) (ηD := ηD0) (ηH := ηH0)
      (M := M) (N := N) (D := D) (E := E) (H := H) (K := K)
      hDB hHB hM hN hD hE hK hηD0 hMdiff hDdiff hHdiff hδpos hdetM hdetN
  exact hbase.mono_const
    (ricciDeTurckSchematicDiffBoundConst_mono
      (𝕜 := 𝕜) hδpos hDB hHB hηM hηD hηH)

/-- Function-level Lipschitz form of the finite schematic Ricci-DeTurck RHS estimate.  If the
primitive metric, first-derivative, and principal-coefficient inputs differ by fixed constants
times one shared radius, then the schematic RHS differs by one named constant times that radius. -/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_mul_radius {n 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [NormedField 𝕜] {δ R KM KD : ℝ}
    {KH : n → n → ℝ} {C : n → n → ℝ} {DB : n → n → n → ℝ}
    {HB : n → n → n → n → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    {H K : ℝ × X → n → n → n → n → 𝕜}
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hM : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b, ‖M z a b‖ ≤ C a b)
    (hN : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b, ‖N z a b‖ ≤ C a b)
    (hD : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c, ‖D z a b c‖ ≤ DB a b c)
    (hE : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c, ‖E z a b c‖ ≤ DB a b c)
    (hK : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b i j, ‖K z a b i j‖ ≤ HB a b i j)
    (hKD : 0 ≤ KD) (hR : 0 ≤ R)
    (hMdiff : ∀ ⦃z : ℝ × X⦄, z ∈ s → ‖M z - N z‖ ≤ KM * R)
    (hDdiff : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c,
      ‖D z a b c - E z a b c‖ ≤ KD * R)
    (hHdiff : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ i j,
      ‖((fun a b => H z a b i j) : Matrix n n 𝕜) -
        ((fun a b => K z a b i j) : Matrix n n 𝕜)‖ ≤ KH i j * R)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicBoundedWith
      (ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ C DB HB KM KD KH * R)
      (fun z : ℝ × X =>
        ricciDeTurckSchematicMatrix (M z) (D z) (H z) -
          ricciDeTurckSchematicMatrix (N z) (E z) (K z)) s := by
  have hbase :
      ParabolicBoundedWith
        (ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ C DB HB
          (KM * R) (KD * R) (fun i j => KH i j * R))
        (fun z : ℝ × X =>
          ricciDeTurckSchematicMatrix (M z) (D z) (H z) -
            ricciDeTurckSchematicMatrix (N z) (E z) (K z)) s :=
    ricciDeTurckSchematicMatrix_bounded_sub_le_const
      (s := s) (δ := δ) (C := C) (DB := DB) (HB := HB)
      (ηM := KM * R) (ηD := KD * R) (ηH := fun i j => KH i j * R)
      (M := M) (N := N) (D := D) (E := E) (H := H) (K := K)
      hDB hHB hM hN hD hE hK (mul_nonneg hKD hR) hMdiff hDdiff hHdiff
      hδpos hdetM hdetN
  simpa [ricciDeTurckSchematicDiffBoundConst_mul_radius] using hbase

/-- Linear-radius schematic Ricci-DeTurck RHS estimate with coarser primitive Lipschitz
constants.  This is the shared-radius form used when finite-cover local constants are replaced by
larger chart constants before entering a common Picard/Lipschitz estimate. -/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_mul_radius_of_primitive_le
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜] {δ R : ℝ}
    {KM0 KD0 KM KD : ℝ} {KH0 KH : n → n → ℝ}
    {C : n → n → ℝ} {DB : n → n → n → ℝ} {HB : n → n → n → n → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    {H K : ℝ × X → n → n → n → n → 𝕜}
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hKM : KM0 ≤ KM) (hKD : KD0 ≤ KD) (hKH : ∀ i j, KH0 i j ≤ KH i j)
    (hM : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b, ‖M z a b‖ ≤ C a b)
    (hN : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b, ‖N z a b‖ ≤ C a b)
    (hD : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c, ‖D z a b c‖ ≤ DB a b c)
    (hE : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c, ‖E z a b c‖ ≤ DB a b c)
    (hK : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b i j, ‖K z a b i j‖ ≤ HB a b i j)
    (hKD0 : 0 ≤ KD0) (hR : 0 ≤ R)
    (hMdiff : ∀ ⦃z : ℝ × X⦄, z ∈ s → ‖M z - N z‖ ≤ KM0 * R)
    (hDdiff : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c,
      ‖D z a b c - E z a b c‖ ≤ KD0 * R)
    (hHdiff : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ i j,
      ‖((fun a b => H z a b i j) : Matrix n n 𝕜) -
        ((fun a b => K z a b i j) : Matrix n n 𝕜)‖ ≤ KH0 i j * R)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicBoundedWith
      (ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ C DB HB KM KD KH * R)
      (fun z : ℝ × X =>
        ricciDeTurckSchematicMatrix (M z) (D z) (H z) -
          ricciDeTurckSchematicMatrix (N z) (E z) (K z)) s := by
  have hbase :
      ParabolicBoundedWith
        (ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ C DB HB KM0 KD0 KH0 * R)
        (fun z : ℝ × X =>
          ricciDeTurckSchematicMatrix (M z) (D z) (H z) -
            ricciDeTurckSchematicMatrix (N z) (E z) (K z)) s :=
    ricciDeTurckSchematicMatrix_bounded_sub_le_const_mul_radius
      (s := s) (δ := δ) (C := C) (DB := DB) (HB := HB)
      (R := R) (KM := KM0) (KD := KD0) (KH := KH0)
      (M := M) (N := N) (D := D) (E := E) (H := H) (K := K)
      hDB hHB hM hN hD hE hK hKD0 hR hMdiff hDdiff hHdiff hδpos hdetM hdetN
  exact hbase.mono_const
    (mul_le_mul_of_nonneg_right
      (ricciDeTurckSchematicDiffBoundConst_mono
        (𝕜 := 𝕜) hδpos hDB hHB hKM hKD hKH)
      hR)

/-- State-space Lipschitz bridge for the finite schematic Ricci-DeTurck RHS.  If the primitive
matrix, first-derivative, and principal-coefficient inputs are Lipschitz on a state set with
constants `KM`, `KD`, and `KH`, and one determinant lower bound works for every state in the set,
then each time-space coordinate of the schematic RHS is Lipschitz on that state set. -/
theorem ricciDeTurckSchematicMatrix_lipschitzOnWith_of_primitive_dist_le
    {Y n 𝕜 : Type*} [PseudoMetricSpace Y] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {δ KM KD : ℝ} {KH : n → n → ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} {HB : n → n → n → n → ℝ}
    {stateSet : Set Y}
    {M : Y → ℝ × X → Matrix n n 𝕜}
    {D : Y → ℝ × X → n → n → n → 𝕜}
    {H : Y → ℝ × X → n → n → n → n → 𝕜}
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hKM : 0 ≤ KM) (hKD : 0 ≤ KD) (hKH : ∀ i j, 0 ≤ KH i j)
    (hM : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b,
      ‖M u z a b‖ ≤ C a b)
    (hD : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c,
      ‖D u z a b c‖ ≤ DB a b c)
    (hH : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b i j,
      ‖H u z a b i j‖ ≤ HB a b i j)
    (hMdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ ⦃z : ℝ × X⦄, z ∈ s → ‖M u z - M v z‖ ≤ KM * dist u v)
    (hDdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c,
        ‖D u z a b c - D v z a b c‖ ≤ KD * dist u v)
    (hHdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ i j,
        ‖((fun a b => H u z a b i j) : Matrix n n 𝕜) -
          ((fun a b => H v z a b i j) : Matrix n n 𝕜)‖ ≤ KH i j * dist u v)
    (hδpos : 0 < δ)
    (hdet : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M u z).det‖) :
    ∀ ⦃z : ℝ × X⦄, z ∈ s →
      LipschitzOnWith
        ⟨ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ C DB HB KM KD KH,
          ricciDeTurckSchematicDiffBoundConst_nonneg
            (𝕜 := 𝕜) hδpos hDB hHB hKM hKD hKH⟩
        (fun u : Y => ricciDeTurckSchematicMatrix (M u z) (D u z) (H u z))
        stateSet := by
  intro z hz
  let L : NNReal :=
    ⟨ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ C DB HB KM KD KH,
      ricciDeTurckSchematicDiffBoundConst_nonneg (𝕜 := 𝕜) hδpos hDB hHB hKM hKD hKH⟩
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hbounded :
      ParabolicBoundedWith
        (ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ C DB HB KM KD KH *
          dist u v)
        (fun z : ℝ × X =>
          ricciDeTurckSchematicMatrix (M u z) (D u z) (H u z) -
            ricciDeTurckSchematicMatrix (M v z) (D v z) (H v z)) s := by
    exact ricciDeTurckSchematicMatrix_bounded_sub_le_const_mul_radius
      (s := s) (δ := δ) (C := C) (DB := DB) (HB := HB)
      (R := dist u v) (KM := KM) (KD := KD) (KH := KH)
      (M := M u) (N := M v) (D := D u) (E := D v) (H := H u) (K := H v)
      hDB hHB (hM hu) (hM hv) (hD hu) (hD hv) (hH hv) hKD dist_nonneg
      (hMdiff hu hv) (hDdiff hu hv) (hHdiff hu hv) hδpos (hdet hu) (hdet hv)
  change dist (ricciDeTurckSchematicMatrix (M u z) (D u z) (H u z))
      (ricciDeTurckSchematicMatrix (M v z) (D v z) (H v z)) ≤
    (↑L : ℝ) * dist u v
  have hL : (↑L : ℝ) =
      ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ C DB HB KM KD KH := rfl
  simpa [hL, dist_eq_norm] using hbounded hz

/-- State-space Lipschitz bridge for the finite schematic Ricci-DeTurck RHS with coarser
primitive Lipschitz constants.  The primitive estimates may be proved with sharper constants
`KM0`, `KD0`, and `KH0`, while the resulting coordinate Lipschitz constant is formed from larger
shared constants `KM`, `KD`, and `KH`. -/
theorem ricciDeTurckSchematicMatrix_lipschitzOnWith_of_primitive_dist_le_of_le
    {Y n 𝕜 : Type*} [PseudoMetricSpace Y] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {δ KM0 KD0 KM KD : ℝ} {KH0 KH : n → n → ℝ} {C : n → n → ℝ}
    {DB : n → n → n → ℝ} {HB : n → n → n → n → ℝ}
    {stateSet : Set Y}
    {M : Y → ℝ × X → Matrix n n 𝕜}
    {D : Y → ℝ × X → n → n → n → 𝕜}
    {H : Y → ℝ × X → n → n → n → n → 𝕜}
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hKM_nonneg : 0 ≤ KM) (hKD_nonneg : 0 ≤ KD) (hKH_nonneg : ∀ i j, 0 ≤ KH i j)
    (hKM : KM0 ≤ KM) (hKD : KD0 ≤ KD) (hKH : ∀ i j, KH0 i j ≤ KH i j)
    (hKD0 : 0 ≤ KD0)
    (hM : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b,
      ‖M u z a b‖ ≤ C a b)
    (hD : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c,
      ‖D u z a b c‖ ≤ DB a b c)
    (hH : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b i j,
      ‖H u z a b i j‖ ≤ HB a b i j)
    (hMdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ ⦃z : ℝ × X⦄, z ∈ s → ‖M u z - M v z‖ ≤ KM0 * dist u v)
    (hDdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c,
        ‖D u z a b c - D v z a b c‖ ≤ KD0 * dist u v)
    (hHdiff : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ i j,
        ‖((fun a b => H u z a b i j) : Matrix n n 𝕜) -
          ((fun a b => H v z a b i j) : Matrix n n 𝕜)‖ ≤ KH0 i j * dist u v)
    (hδpos : 0 < δ)
    (hdet : ∀ ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M u z).det‖) :
    ∀ ⦃z : ℝ × X⦄, z ∈ s →
      LipschitzOnWith
        ⟨ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ C DB HB KM KD KH,
          ricciDeTurckSchematicDiffBoundConst_nonneg
            (𝕜 := 𝕜) hδpos hDB hHB hKM_nonneg hKD_nonneg hKH_nonneg⟩
        (fun u : Y => ricciDeTurckSchematicMatrix (M u z) (D u z) (H u z))
        stateSet := by
  intro z hz
  let L : NNReal :=
    ⟨ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ C DB HB KM KD KH,
      ricciDeTurckSchematicDiffBoundConst_nonneg
        (𝕜 := 𝕜) hδpos hDB hHB hKM_nonneg hKD_nonneg hKH_nonneg⟩
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro u hu v hv
  have hbounded :
      ParabolicBoundedWith
        (ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ C DB HB KM KD KH *
          dist u v)
        (fun z : ℝ × X =>
          ricciDeTurckSchematicMatrix (M u z) (D u z) (H u z) -
            ricciDeTurckSchematicMatrix (M v z) (D v z) (H v z)) s := by
    exact ricciDeTurckSchematicMatrix_bounded_sub_le_const_mul_radius_of_primitive_le
      (s := s) (δ := δ) (C := C) (DB := DB) (HB := HB)
      (R := dist u v) (KM0 := KM0) (KD0 := KD0) (KH0 := KH0)
      (KM := KM) (KD := KD) (KH := KH)
      (M := M u) (N := M v) (D := D u) (E := D v) (H := H u) (K := H v)
      hDB hHB hKM hKD hKH (hM hu) (hM hv) (hD hu) (hD hv) (hH hv)
      hKD0 dist_nonneg (hMdiff hu hv) (hDdiff hu hv) (hHdiff hu hv)
      hδpos (hdet hu) (hdet hv)
  change dist (ricciDeTurckSchematicMatrix (M u z) (D u z) (H u z))
      (ricciDeTurckSchematicMatrix (M v z) (D v z) (H v z)) ≤
    (↑L : ℝ) * dist u v
  have hL : (↑L : ℝ) =
      ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ C DB HB KM KD KH := rfl
  simpa [hL, dist_eq_norm] using hbounded hz

/-- Finite-family version of
`ricciDeTurckSchematicMatrix_lipschitzOnWith_of_primitive_dist_le`: one uniform determinant lower
bound works for every state and every family member, and each family member gets its own primitive
Lipschitz constants. -/
theorem ricciDeTurckSchematicMatrix_lipschitzOnWith_family_of_primitive_dist_le
    {κ Y n 𝕜 : Type*} [Fintype κ] [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ}
    {KM KD : κ → ℝ} {KH : κ → n → n → ℝ}
    {C : κ → n → n → ℝ} {DB : κ → n → n → n → ℝ}
    {HB : κ → n → n → n → n → ℝ}
    {stateSet : Set Y}
    {M : κ → Y → ℝ × X → Matrix n n 𝕜}
    {D : κ → Y → ℝ × X → n → n → n → 𝕜}
    {H : κ → Y → ℝ × X → n → n → n → n → 𝕜}
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hKM : ∀ r, 0 ≤ KM r) (hKD : ∀ r, 0 ≤ KD r)
    (hKH : ∀ r i j, 0 ≤ KH r i j)
    (hM : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b,
      ‖M r u z a b‖ ≤ C r a b)
    (hD : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c,
      ‖D r u z a b c‖ ≤ DB r a b c)
    (hH : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b i j,
      ‖H r u z a b i j‖ ≤ HB r a b i j)
    (hMdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ ⦃z : ℝ × X⦄, z ∈ s → ‖M r u z - M r v z‖ ≤ KM r * dist u v)
    (hDdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c,
        ‖D r u z a b c - D r v z a b c‖ ≤ KD r * dist u v)
    (hHdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ i j,
        ‖((fun a b => H r u z a b i j) : Matrix n n 𝕜) -
          ((fun a b => H r v z a b i j) : Matrix n n 𝕜)‖ ≤
            KH r i j * dist u v)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M r u z).det‖) :
    ∀ r ⦃z : ℝ × X⦄, z ∈ s →
      LipschitzOnWith
        ⟨ricciDeTurckSchematicDiffBoundConst
            (𝕜 := 𝕜) δ (C r) (DB r) (HB r) (KM r) (KD r) (KH r),
          ricciDeTurckSchematicDiffBoundConst_nonneg
            (𝕜 := 𝕜) hδpos (hDB r) (hHB r) (hKM r) (hKD r) (hKH r)⟩
        (fun u : Y => ricciDeTurckSchematicMatrix (M r u z) (D r u z) (H r u z))
        stateSet := by
  intro r z hz
  exact ricciDeTurckSchematicMatrix_lipschitzOnWith_of_primitive_dist_le
    (s := s) (δ := δ) (C := C r) (DB := DB r) (HB := HB r)
    (KM := KM r) (KD := KD r) (KH := KH r)
    (stateSet := stateSet) (M := M r) (D := D r) (H := H r)
    (hDB r) (hHB r) (hKM r) (hKD r) (hKH r)
    (hM r) (hD r) (hH r) (hMdiff r) (hDdiff r) (hHdiff r) hδpos (hdet r)
    hz

/-- Finite-family version of
`ricciDeTurckSchematicMatrix_lipschitzOnWith_of_primitive_dist_le_of_le`: each family member may
prove primitive Lipschitz estimates with sharper local constants, while the exported coordinate
Lipschitz constant uses larger shared constants for that member. -/
theorem ricciDeTurckSchematicMatrix_lipschitzOnWith_family_of_primitive_dist_le_of_le
    {κ Y n 𝕜 : Type*} [Fintype κ] [PseudoMetricSpace Y] [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ}
    {KM0 KD0 KM KD : κ → ℝ} {KH0 KH : κ → n → n → ℝ}
    {C : κ → n → n → ℝ} {DB : κ → n → n → n → ℝ}
    {HB : κ → n → n → n → n → ℝ}
    {stateSet : Set Y}
    {M : κ → Y → ℝ × X → Matrix n n 𝕜}
    {D : κ → Y → ℝ × X → n → n → n → 𝕜}
    {H : κ → Y → ℝ × X → n → n → n → n → 𝕜}
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hKM_nonneg : ∀ r, 0 ≤ KM r) (hKD_nonneg : ∀ r, 0 ≤ KD r)
    (hKH_nonneg : ∀ r i j, 0 ≤ KH r i j)
    (hKM : ∀ r, KM0 r ≤ KM r) (hKD : ∀ r, KD0 r ≤ KD r)
    (hKH : ∀ r i j, KH0 r i j ≤ KH r i j)
    (hKD0 : ∀ r, 0 ≤ KD0 r)
    (hM : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b,
      ‖M r u z a b‖ ≤ C r a b)
    (hD : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c,
      ‖D r u z a b c‖ ≤ DB r a b c)
    (hH : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b i j,
      ‖H r u z a b i j‖ ≤ HB r a b i j)
    (hMdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ ⦃z : ℝ × X⦄, z ∈ s → ‖M r u z - M r v z‖ ≤ KM0 r * dist u v)
    (hDdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c,
        ‖D r u z a b c - D r v z a b c‖ ≤ KD0 r * dist u v)
    (hHdiff : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃v : Y⦄, v ∈ stateSet →
      ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ i j,
        ‖((fun a b => H r u z a b i j) : Matrix n n 𝕜) -
          ((fun a b => H r v z a b i j) : Matrix n n 𝕜)‖ ≤
            KH0 r i j * dist u v)
    (hδpos : 0 < δ)
    (hdet : ∀ r ⦃u : Y⦄, u ∈ stateSet → ∀ ⦃z : ℝ × X⦄, z ∈ s →
      δ ≤ ‖(M r u z).det‖) :
    ∀ r ⦃z : ℝ × X⦄, z ∈ s →
      LipschitzOnWith
        ⟨ricciDeTurckSchematicDiffBoundConst
            (𝕜 := 𝕜) δ (C r) (DB r) (HB r) (KM r) (KD r) (KH r),
          ricciDeTurckSchematicDiffBoundConst_nonneg
            (𝕜 := 𝕜) hδpos (hDB r) (hHB r)
            (hKM_nonneg r) (hKD_nonneg r) (hKH_nonneg r)⟩
        (fun u : Y => ricciDeTurckSchematicMatrix (M r u z) (D r u z) (H r u z))
        stateSet := by
  intro r z hz
  exact ricciDeTurckSchematicMatrix_lipschitzOnWith_of_primitive_dist_le_of_le
    (s := s) (δ := δ) (C := C r) (DB := DB r) (HB := HB r)
    (KM0 := KM0 r) (KD0 := KD0 r) (KH0 := KH0 r)
    (KM := KM r) (KD := KD r) (KH := KH r)
    (stateSet := stateSet) (M := M r) (D := D r) (H := H r)
    (hDB r) (hHB r) (hKM_nonneg r) (hKD_nonneg r) (hKH_nonneg r)
    (hKM r) (hKD r) (hKH r) (hKD0 r)
    (hM r) (hD r) (hH r) (hMdiff r) (hDdiff r) (hHdiff r) hδpos (hdet r)
    hz

/-- Compact-domain version of `ricciDeTurckSchematicMatrix_bounded_sub_le_const`: pointwise
nonvanishing of both metric determinants supplies one common determinant lower bound. -/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_of_isCompact_det_ne_zero
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)} {C : n → n → ℝ} {DB : n → n → n → ℝ}
    {HB : n → n → n → n → ℝ} {ηM ηD : ℝ} {ηH : n → n → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    {Hc Kc : ℝ × X → n → n → n → n → 𝕜}
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (hMctrl : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) Kdom)
    (hNctrl : ∀ i j, ParabolicC0AlphaOn α (fun z => N z i j) Kdom)
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (N z).det ≠ 0)
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hM : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖M z a b‖ ≤ C a b)
    (hN : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖N z a b‖ ≤ C a b)
    (hD : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖D z a b c‖ ≤ DB a b c)
    (hE : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖E z a b c‖ ≤ DB a b c)
    (hKc : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b i j, ‖Kc z a b i j‖ ≤ HB a b i j)
    (hηD : 0 ≤ ηD)
    (hMdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ‖M z - N z‖ ≤ ηM)
    (hDdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c,
      ‖D z a b c - E z a b c‖ ≤ ηD)
    (hHdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ i j,
      ‖((fun a b => Hc z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc z a b i j) : Matrix n n 𝕜)‖ ≤ ηH i j) :
    ∃ δ > 0,
      ParabolicBoundedWith
        (ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ C DB HB ηM ηD ηH)
        (fun z : ℝ × X =>
          ricciDeTurckSchematicMatrix (M z) (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (E z) (Kc z)) Kdom := by
  rcases matrix_det_pair_exists_pos_norm_lower_bound_of_isCompact
      (K := Kdom) (M := M) (N := N) hKdom hα hMctrl hNctrl hdetM_ne hdetN_ne with
    ⟨δ, hδpos, hdetM, hdetN⟩
  refine ⟨δ, hδpos, ?_⟩
  exact ricciDeTurckSchematicMatrix_bounded_sub_le_const
    (s := Kdom) (δ := δ) (C := C) (DB := DB) (HB := HB)
    (ηM := ηM) (ηD := ηD) (ηH := ηH)
    hDB hHB hM hN hD hE hKc hηD hMdiff hDdiff hHdiff hδpos hdetM hdetN

/-- Compact-domain version of
`ricciDeTurckSchematicMatrix_bounded_sub_le_const_of_primitive_le`: determinant nonvanishing
supplies the common determinant lower bound, while primitive differences proved with sharper
constants are consumed by coarser shared constants. -/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_of_isCompact_det_ne_zero_of_primitive_le
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)} {C : n → n → ℝ} {DB : n → n → n → ℝ}
    {HB : n → n → n → n → ℝ} {ηM0 ηD0 ηM ηD : ℝ}
    {ηH0 ηH : n → n → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    {Hc Kc : ℝ × X → n → n → n → n → 𝕜}
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (hMctrl : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) Kdom)
    (hNctrl : ∀ i j, ParabolicC0AlphaOn α (fun z => N z i j) Kdom)
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (N z).det ≠ 0)
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hηM : ηM0 ≤ ηM) (hηD : ηD0 ≤ ηD)
    (hηH : ∀ i j, ηH0 i j ≤ ηH i j)
    (hM : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖M z a b‖ ≤ C a b)
    (hN : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖N z a b‖ ≤ C a b)
    (hD : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖D z a b c‖ ≤ DB a b c)
    (hE : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖E z a b c‖ ≤ DB a b c)
    (hKc : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b i j, ‖Kc z a b i j‖ ≤
      HB a b i j)
    (hηD0 : 0 ≤ ηD0)
    (hMdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ‖M z - N z‖ ≤ ηM0)
    (hDdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c,
      ‖D z a b c - E z a b c‖ ≤ ηD0)
    (hHdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ i j,
      ‖((fun a b => Hc z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc z a b i j) : Matrix n n 𝕜)‖ ≤ ηH0 i j) :
    ∃ δ > 0,
      ParabolicBoundedWith
        (ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ C DB HB ηM ηD ηH)
        (fun z : ℝ × X =>
          ricciDeTurckSchematicMatrix (M z) (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (E z) (Kc z)) Kdom := by
  rcases matrix_det_pair_exists_pos_norm_lower_bound_of_isCompact
      (K := Kdom) (M := M) (N := N) hKdom hα hMctrl hNctrl hdetM_ne hdetN_ne with
    ⟨δ, hδpos, hdetM, hdetN⟩
  refine ⟨δ, hδpos, ?_⟩
  exact ricciDeTurckSchematicMatrix_bounded_sub_le_const_of_primitive_le
    (s := Kdom) (δ := δ) (C := C) (DB := DB) (HB := HB)
    (ηM0 := ηM0) (ηD0 := ηD0) (ηH0 := ηH0)
    (ηM := ηM) (ηD := ηD) (ηH := ηH)
    (M := M) (N := N) (D := D) (E := E) (H := Hc) (K := Kc)
    hDB hHB hηM hηD hηH hM hN hD hE hKc hηD0 hMdiff hDdiff hHdiff
    hδpos hdetM hdetN

/-- Compact-domain Lipschitz form of `ricciDeTurckSchematicMatrix_bounded_sub_le_const`: after
selecting the common determinant lower bound, primitive differences controlled by constants times
one radius give the schematic RHS difference with the same radius factored out. -/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_mul_radius_of_isCompact_det_ne_zero
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)} {C : n → n → ℝ} {DB : n → n → n → ℝ}
    {HB : n → n → n → n → ℝ} {R KM KD : ℝ} {KH : n → n → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    {Hc Kc : ℝ × X → n → n → n → n → 𝕜}
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (hMctrl : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) Kdom)
    (hNctrl : ∀ i j, ParabolicC0AlphaOn α (fun z => N z i j) Kdom)
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (N z).det ≠ 0)
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hM : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖M z a b‖ ≤ C a b)
    (hN : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖N z a b‖ ≤ C a b)
    (hD : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖D z a b c‖ ≤ DB a b c)
    (hE : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖E z a b c‖ ≤ DB a b c)
    (hKc : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b i j, ‖Kc z a b i j‖ ≤
      HB a b i j)
    (hKD : 0 ≤ KD) (hR : 0 ≤ R)
    (hMdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ‖M z - N z‖ ≤ KM * R)
    (hDdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c,
      ‖D z a b c - E z a b c‖ ≤ KD * R)
    (hHdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ i j,
      ‖((fun a b => Hc z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc z a b i j) : Matrix n n 𝕜)‖ ≤ KH i j * R) :
    ∃ δ > 0,
      ParabolicBoundedWith
        (ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ C DB HB KM KD KH * R)
        (fun z : ℝ × X =>
          ricciDeTurckSchematicMatrix (M z) (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (E z) (Kc z)) Kdom := by
  rcases matrix_det_pair_exists_pos_norm_lower_bound_of_isCompact
      (K := Kdom) (M := M) (N := N) hKdom hα hMctrl hNctrl hdetM_ne hdetN_ne with
    ⟨δ, hδpos, hdetM, hdetN⟩
  refine ⟨δ, hδpos, ?_⟩
  exact ricciDeTurckSchematicMatrix_bounded_sub_le_const_mul_radius
    (s := Kdom) (δ := δ) (C := C) (DB := DB) (HB := HB)
    (R := R) (KM := KM) (KD := KD) (KH := KH)
    (M := M) (N := N) (D := D) (E := E) (H := Hc) (K := Kc)
    hDB hHB hM hN hD hE hKc hKD hR hMdiff hDdiff hHdiff hδpos hdetM hdetN

/-- Compact-domain linear-radius schematic RHS estimate with coarser primitive Lipschitz
constants.  The determinant lower bound is extracted from compactness before the coarser shared
constant is applied. -/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_mul_radius_of_isCompact_det_ne_zero_of_primitive_le
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)} {C : n → n → ℝ} {DB : n → n → n → ℝ}
    {HB : n → n → n → n → ℝ} {R KM0 KD0 KM KD : ℝ}
    {KH0 KH : n → n → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    {Hc Kc : ℝ × X → n → n → n → n → 𝕜}
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (hMctrl : ∀ i j, ParabolicC0AlphaOn α (fun z => M z i j) Kdom)
    (hNctrl : ∀ i j, ParabolicC0AlphaOn α (fun z => N z i j) Kdom)
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (N z).det ≠ 0)
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hKM : KM0 ≤ KM) (hKD : KD0 ≤ KD) (hKH : ∀ i j, KH0 i j ≤ KH i j)
    (hM : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖M z a b‖ ≤ C a b)
    (hN : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖N z a b‖ ≤ C a b)
    (hD : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖D z a b c‖ ≤ DB a b c)
    (hE : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖E z a b c‖ ≤ DB a b c)
    (hKc : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b i j, ‖Kc z a b i j‖ ≤
      HB a b i j)
    (hKD0 : 0 ≤ KD0) (hR : 0 ≤ R)
    (hMdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ‖M z - N z‖ ≤ KM0 * R)
    (hDdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c,
      ‖D z a b c - E z a b c‖ ≤ KD0 * R)
    (hHdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ i j,
      ‖((fun a b => Hc z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc z a b i j) : Matrix n n 𝕜)‖ ≤ KH0 i j * R) :
    ∃ δ > 0,
      ParabolicBoundedWith
        (ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ C DB HB KM KD KH * R)
        (fun z : ℝ × X =>
          ricciDeTurckSchematicMatrix (M z) (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (E z) (Kc z)) Kdom := by
  rcases matrix_det_pair_exists_pos_norm_lower_bound_of_isCompact
      (K := Kdom) (M := M) (N := N) hKdom hα hMctrl hNctrl hdetM_ne hdetN_ne with
    ⟨δ, hδpos, hdetM, hdetN⟩
  refine ⟨δ, hδpos, ?_⟩
  exact ricciDeTurckSchematicMatrix_bounded_sub_le_const_mul_radius_of_primitive_le
    (s := Kdom) (δ := δ) (C := C) (DB := DB) (HB := HB)
    (R := R) (KM0 := KM0) (KD0 := KD0) (KH0 := KH0)
    (KM := KM) (KD := KD) (KH := KH)
    (M := M) (N := N) (D := D) (E := E) (H := Hc) (K := Kc)
    hDB hHB hKM hKD hKH hM hN hD hE hKc hKD0 hR hMdiff hDdiff hHdiff
    hδpos hdetM hdetN

/-- Local finite product-cylinder metric controls globalize the compact-domain
function-level bounded-difference estimate for schematic Ricci-DeTurck RHS fields.  The
nonlinear primitive bounds and difference bounds are still checked on the compact target set. -/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_of_finset_parabolicCylinder_cover_closedCylinder_variable
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)} {C : n → n → ℝ} {DB : n → n → n → ℝ}
    {HB : n → n → n → n → ℝ} {ηM ηD : ℝ} {ηH : n → n → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    {Hc Kc : ℝ × X → n → n → n → n → 𝕜}
    (S : Finset (ℝ × X)) (timeRadius spaceRadius : ℝ × X → ℝ)
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (htime_pos : ∀ y ∈ S, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ S, 0 < spaceRadius y)
    (hcover : Kdom ⊆ ⋃ y ∈ S, parabolicCylinder y (timeRadius y) (spaceRadius y))
    (hMlocal : ∀ y ∈ S, ∀ a b,
      ParabolicC0AlphaOn α (fun z => M z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hNlocal : ∀ y ∈ S, ∀ a b,
      ParabolicC0AlphaOn α (fun z => N z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (N z).det ≠ 0)
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hM : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖M z a b‖ ≤ C a b)
    (hN : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖N z a b‖ ≤ C a b)
    (hD : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖D z a b c‖ ≤ DB a b c)
    (hE : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖E z a b c‖ ≤ DB a b c)
    (hKc : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b i j, ‖Kc z a b i j‖ ≤
      HB a b i j)
    (hηD : 0 ≤ ηD)
    (hMdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ‖M z - N z‖ ≤ ηM)
    (hDdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c,
      ‖D z a b c - E z a b c‖ ≤ ηD)
    (hHdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ i j,
      ‖((fun a b => Hc z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc z a b i j) : Matrix n n 𝕜)‖ ≤ ηH i j) :
    ∃ δ > 0,
      ParabolicBoundedWith
        (ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ C DB HB ηM ηD ηH)
        (fun z : ℝ × X =>
          ricciDeTurckSchematicMatrix (M z) (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (E z) (Kc z)) Kdom := by
  have hMctrl : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) Kdom := by
    intro a b
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hMlocal y hy a b)
  have hNctrl : ∀ a b, ParabolicC0AlphaOn α (fun z => N z a b) Kdom := by
    intro a b
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hNlocal y hy a b)
  exact ricciDeTurckSchematicMatrix_bounded_sub_le_const_of_isCompact_det_ne_zero
    (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
    hKdom hα hMctrl hNctrl hdetM_ne hdetN_ne hDB hHB hM hN hD hE hKc
    hηD hMdiff hDdiff hHdiff

/-- Point-dependent local product-cylinder metric controls globalize the compact-domain
function-level bounded-difference estimate for schematic Ricci-DeTurck RHS fields.  Compactness
chooses the finite subcover internally before extracting the common determinant lower bound. -/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_of_isCompact_of_local_closedCylinder_variable
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)} {C : n → n → ℝ} {DB : n → n → n → ℝ}
    {HB : n → n → n → n → ℝ} {ηM ηD : ℝ} {ηH : n → n → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    {Hc Kc : ℝ × X → n → n → n → n → 𝕜}
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (timeRadius spaceRadius : ℝ × X → ℝ)
    (htime_pos : ∀ y ∈ Kdom, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ Kdom, 0 < spaceRadius y)
    (hMlocal : ∀ y ∈ Kdom, ∀ a b,
      ParabolicC0AlphaOn α (fun z => M z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hNlocal : ∀ y ∈ Kdom, ∀ a b,
      ParabolicC0AlphaOn α (fun z => N z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (N z).det ≠ 0)
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hM : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖M z a b‖ ≤ C a b)
    (hN : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖N z a b‖ ≤ C a b)
    (hD : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖D z a b c‖ ≤ DB a b c)
    (hE : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖E z a b c‖ ≤ DB a b c)
    (hKc : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b i j, ‖Kc z a b i j‖ ≤
      HB a b i j)
    (hηD : 0 ≤ ηD)
    (hMdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ‖M z - N z‖ ≤ ηM)
    (hDdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c,
      ‖D z a b c - E z a b c‖ ≤ ηD)
    (hHdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ i j,
      ‖((fun a b => Hc z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc z a b i j) : Matrix n n 𝕜)‖ ≤ ηH i j) :
    ∃ δ > 0,
      ParabolicBoundedWith
        (ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ C DB HB ηM ηD ηH)
        (fun z : ℝ × X =>
          ricciDeTurckSchematicMatrix (M z) (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (E z) (Kc z)) Kdom := by
  have hMctrl : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) Kdom := by
    intro a b
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hKdom hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hMlocal y hy a b)
  have hNctrl : ∀ a b, ParabolicC0AlphaOn α (fun z => N z a b) Kdom := by
    intro a b
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hKdom hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hNlocal y hy a b)
  exact ricciDeTurckSchematicMatrix_bounded_sub_le_const_of_isCompact_det_ne_zero
    (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
    hKdom hα hMctrl hNctrl hdetM_ne hdetN_ne hDB hHB hM hN hD hE hKc
    hηD hMdiff hDdiff hHdiff

/-- Existential point-local product-cylinder metric controls globalize the compact-domain
function-level bounded-difference estimate for schematic Ricci-DeTurck RHS fields.  This form lets
each compact point provide its own local cylinder radii for the two metric matrices. -/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_of_isCompact_of_exists_local_closedCylinder
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)} {C : n → n → ℝ} {DB : n → n → n → ℝ}
    {HB : n → n → n → n → ℝ} {ηM ηD : ℝ} {ηH : n → n → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    {Hc Kc : ℝ × X → n → n → n → n → 𝕜}
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (hlocal : ∀ y ∈ Kdom, ∃ timeRadius > 0, ∃ spaceRadius > 0,
      (∀ a b,
        ParabolicC0AlphaOn α (fun z => M z a b)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ a b,
        ParabolicC0AlphaOn α (fun z => N z a b)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))))
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (N z).det ≠ 0)
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hM : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖M z a b‖ ≤ C a b)
    (hN : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖N z a b‖ ≤ C a b)
    (hD : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖D z a b c‖ ≤ DB a b c)
    (hE : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖E z a b c‖ ≤ DB a b c)
    (hKc : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b i j, ‖Kc z a b i j‖ ≤
      HB a b i j)
    (hηD : 0 ≤ ηD)
    (hMdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ‖M z - N z‖ ≤ ηM)
    (hDdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c,
      ‖D z a b c - E z a b c‖ ≤ ηD)
    (hHdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ i j,
      ‖((fun a b => Hc z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc z a b i j) : Matrix n n 𝕜)‖ ≤ ηH i j) :
    ∃ δ > 0,
      ParabolicBoundedWith
        (ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ C DB HB ηM ηD ηH)
        (fun z : ℝ × X =>
          ricciDeTurckSchematicMatrix (M z) (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (E z) (Kc z)) Kdom := by
  have hMctrl : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) Kdom := by
    intro a b
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hKdom hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.1 a b⟩)
  have hNctrl : ∀ a b, ParabolicC0AlphaOn α (fun z => N z a b) Kdom := by
    intro a b
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hKdom hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.2 a b⟩)
  exact ricciDeTurckSchematicMatrix_bounded_sub_le_const_of_isCompact_det_ne_zero
    (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
    hKdom hα hMctrl hNctrl hdetM_ne hdetN_ne hDB hHB hM hN hD hE hKc
    hηD hMdiff hDdiff hHdiff

/-- Local finite product-cylinder metric controls globalize the compact-domain linear-radius
function-level bounded-difference estimate for schematic Ricci-DeTurck RHS fields. -/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_mul_radius_of_finset_parabolicCylinder_cover_closedCylinder_variable
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)} {C : n → n → ℝ} {DB : n → n → n → ℝ}
    {HB : n → n → n → n → ℝ} {R KM KD : ℝ} {KH : n → n → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    {Hc Kc : ℝ × X → n → n → n → n → 𝕜}
    (S : Finset (ℝ × X)) (timeRadius spaceRadius : ℝ × X → ℝ)
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (htime_pos : ∀ y ∈ S, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ S, 0 < spaceRadius y)
    (hcover : Kdom ⊆ ⋃ y ∈ S, parabolicCylinder y (timeRadius y) (spaceRadius y))
    (hMlocal : ∀ y ∈ S, ∀ a b,
      ParabolicC0AlphaOn α (fun z => M z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hNlocal : ∀ y ∈ S, ∀ a b,
      ParabolicC0AlphaOn α (fun z => N z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (N z).det ≠ 0)
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hM : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖M z a b‖ ≤ C a b)
    (hN : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖N z a b‖ ≤ C a b)
    (hD : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖D z a b c‖ ≤ DB a b c)
    (hE : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖E z a b c‖ ≤ DB a b c)
    (hKc : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b i j, ‖Kc z a b i j‖ ≤
      HB a b i j)
    (hKD : 0 ≤ KD) (hR : 0 ≤ R)
    (hMdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ‖M z - N z‖ ≤ KM * R)
    (hDdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c,
      ‖D z a b c - E z a b c‖ ≤ KD * R)
    (hHdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ i j,
      ‖((fun a b => Hc z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc z a b i j) : Matrix n n 𝕜)‖ ≤ KH i j * R) :
    ∃ δ > 0,
      ParabolicBoundedWith
        (ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ C DB HB KM KD KH * R)
        (fun z : ℝ × X =>
          ricciDeTurckSchematicMatrix (M z) (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (E z) (Kc z)) Kdom := by
  have hMctrl : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) Kdom := by
    intro a b
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hMlocal y hy a b)
  have hNctrl : ∀ a b, ParabolicC0AlphaOn α (fun z => N z a b) Kdom := by
    intro a b
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hNlocal y hy a b)
  exact ricciDeTurckSchematicMatrix_bounded_sub_le_const_mul_radius_of_isCompact_det_ne_zero
    (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
    hKdom hα hMctrl hNctrl hdetM_ne hdetN_ne hDB hHB hM hN hD hE hKc
    hKD hR hMdiff hDdiff hHdiff

/-- Local finite product-cylinder metric controls globalize the compact-domain linear-radius
schematic RHS estimate while allowing sharper primitive Lipschitz constants to be promoted to
coarser shared constants. -/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_mul_radius_of_finset_parabolicCylinder_cover_closedCylinder_variable_of_primitive_le
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)} {C : n → n → ℝ} {DB : n → n → n → ℝ}
    {HB : n → n → n → n → ℝ} {R KM0 KD0 KM KD : ℝ}
    {KH0 KH : n → n → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    {Hc Kc : ℝ × X → n → n → n → n → 𝕜}
    (S : Finset (ℝ × X)) (timeRadius spaceRadius : ℝ × X → ℝ)
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (htime_pos : ∀ y ∈ S, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ S, 0 < spaceRadius y)
    (hcover : Kdom ⊆ ⋃ y ∈ S, parabolicCylinder y (timeRadius y) (spaceRadius y))
    (hMlocal : ∀ y ∈ S, ∀ a b,
      ParabolicC0AlphaOn α (fun z => M z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hNlocal : ∀ y ∈ S, ∀ a b,
      ParabolicC0AlphaOn α (fun z => N z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (N z).det ≠ 0)
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hKM : KM0 ≤ KM) (hKD : KD0 ≤ KD) (hKH : ∀ i j, KH0 i j ≤ KH i j)
    (hM : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖M z a b‖ ≤ C a b)
    (hN : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖N z a b‖ ≤ C a b)
    (hD : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖D z a b c‖ ≤ DB a b c)
    (hE : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖E z a b c‖ ≤ DB a b c)
    (hKc : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b i j, ‖Kc z a b i j‖ ≤
      HB a b i j)
    (hKD0 : 0 ≤ KD0) (hR : 0 ≤ R)
    (hMdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ‖M z - N z‖ ≤ KM0 * R)
    (hDdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c,
      ‖D z a b c - E z a b c‖ ≤ KD0 * R)
    (hHdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ i j,
      ‖((fun a b => Hc z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc z a b i j) : Matrix n n 𝕜)‖ ≤ KH0 i j * R) :
    ∃ δ > 0,
      ParabolicBoundedWith
        (ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ C DB HB KM KD KH * R)
        (fun z : ℝ × X =>
          ricciDeTurckSchematicMatrix (M z) (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (E z) (Kc z)) Kdom := by
  have hMctrl : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) Kdom := by
    intro a b
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hMlocal y hy a b)
  have hNctrl : ∀ a b, ParabolicC0AlphaOn α (fun z => N z a b) Kdom := by
    intro a b
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hNlocal y hy a b)
  exact
    ricciDeTurckSchematicMatrix_bounded_sub_le_const_mul_radius_of_isCompact_det_ne_zero_of_primitive_le
      (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
      hKdom hα hMctrl hNctrl hdetM_ne hdetN_ne hDB hHB hKM hKD hKH
      hM hN hD hE hKc hKD0 hR hMdiff hDdiff hHdiff

/-- Point-dependent local product-cylinder metric controls globalize the compact-domain
linear-radius function-level bounded-difference estimate for schematic Ricci-DeTurck RHS fields.
-/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_mul_radius_of_isCompact_of_local_closedCylinder_variable
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)} {C : n → n → ℝ} {DB : n → n → n → ℝ}
    {HB : n → n → n → n → ℝ} {R KM KD : ℝ} {KH : n → n → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    {Hc Kc : ℝ × X → n → n → n → n → 𝕜}
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (timeRadius spaceRadius : ℝ × X → ℝ)
    (htime_pos : ∀ y ∈ Kdom, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ Kdom, 0 < spaceRadius y)
    (hMlocal : ∀ y ∈ Kdom, ∀ a b,
      ParabolicC0AlphaOn α (fun z => M z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hNlocal : ∀ y ∈ Kdom, ∀ a b,
      ParabolicC0AlphaOn α (fun z => N z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (N z).det ≠ 0)
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hM : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖M z a b‖ ≤ C a b)
    (hN : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖N z a b‖ ≤ C a b)
    (hD : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖D z a b c‖ ≤ DB a b c)
    (hE : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖E z a b c‖ ≤ DB a b c)
    (hKc : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b i j, ‖Kc z a b i j‖ ≤
      HB a b i j)
    (hKD : 0 ≤ KD) (hR : 0 ≤ R)
    (hMdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ‖M z - N z‖ ≤ KM * R)
    (hDdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c,
      ‖D z a b c - E z a b c‖ ≤ KD * R)
    (hHdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ i j,
      ‖((fun a b => Hc z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc z a b i j) : Matrix n n 𝕜)‖ ≤ KH i j * R) :
    ∃ δ > 0,
      ParabolicBoundedWith
        (ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ C DB HB KM KD KH * R)
        (fun z : ℝ × X =>
          ricciDeTurckSchematicMatrix (M z) (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (E z) (Kc z)) Kdom := by
  have hMctrl : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) Kdom := by
    intro a b
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hKdom hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hMlocal y hy a b)
  have hNctrl : ∀ a b, ParabolicC0AlphaOn α (fun z => N z a b) Kdom := by
    intro a b
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hKdom hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hNlocal y hy a b)
  exact ricciDeTurckSchematicMatrix_bounded_sub_le_const_mul_radius_of_isCompact_det_ne_zero
    (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
    hKdom hα hMctrl hNctrl hdetM_ne hdetN_ne hDB hHB hM hN hD hE hKc
    hKD hR hMdiff hDdiff hHdiff

/-- Point-dependent local product-cylinder metric controls globalize the compact-domain
linear-radius schematic RHS estimate while allowing sharper primitive Lipschitz constants to be
promoted to coarser shared constants. -/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_mul_radius_of_isCompact_of_local_closedCylinder_variable_of_primitive_le
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)} {C : n → n → ℝ} {DB : n → n → n → ℝ}
    {HB : n → n → n → n → ℝ} {R KM0 KD0 KM KD : ℝ}
    {KH0 KH : n → n → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    {Hc Kc : ℝ × X → n → n → n → n → 𝕜}
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (timeRadius spaceRadius : ℝ × X → ℝ)
    (htime_pos : ∀ y ∈ Kdom, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ Kdom, 0 < spaceRadius y)
    (hMlocal : ∀ y ∈ Kdom, ∀ a b,
      ParabolicC0AlphaOn α (fun z => M z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hNlocal : ∀ y ∈ Kdom, ∀ a b,
      ParabolicC0AlphaOn α (fun z => N z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (N z).det ≠ 0)
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hKM : KM0 ≤ KM) (hKD : KD0 ≤ KD) (hKH : ∀ i j, KH0 i j ≤ KH i j)
    (hM : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖M z a b‖ ≤ C a b)
    (hN : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖N z a b‖ ≤ C a b)
    (hD : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖D z a b c‖ ≤ DB a b c)
    (hE : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖E z a b c‖ ≤ DB a b c)
    (hKc : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b i j, ‖Kc z a b i j‖ ≤
      HB a b i j)
    (hKD0 : 0 ≤ KD0) (hR : 0 ≤ R)
    (hMdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ‖M z - N z‖ ≤ KM0 * R)
    (hDdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c,
      ‖D z a b c - E z a b c‖ ≤ KD0 * R)
    (hHdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ i j,
      ‖((fun a b => Hc z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc z a b i j) : Matrix n n 𝕜)‖ ≤ KH0 i j * R) :
    ∃ δ > 0,
      ParabolicBoundedWith
        (ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ C DB HB KM KD KH * R)
        (fun z : ℝ × X =>
          ricciDeTurckSchematicMatrix (M z) (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (E z) (Kc z)) Kdom := by
  have hMctrl : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) Kdom := by
    intro a b
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hKdom hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hMlocal y hy a b)
  have hNctrl : ∀ a b, ParabolicC0AlphaOn α (fun z => N z a b) Kdom := by
    intro a b
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hKdom hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hNlocal y hy a b)
  exact
    ricciDeTurckSchematicMatrix_bounded_sub_le_const_mul_radius_of_isCompact_det_ne_zero_of_primitive_le
      (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
      hKdom hα hMctrl hNctrl hdetM_ne hdetN_ne hDB hHB hKM hKD hKH
      hM hN hD hE hKc hKD0 hR hMdiff hDdiff hHdiff

/-- Existential point-local product-cylinder metric controls globalize the compact-domain
linear-radius function-level bounded-difference estimate for schematic Ricci-DeTurck RHS fields.
-/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_mul_radius_of_isCompact_of_exists_local_closedCylinder
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)} {C : n → n → ℝ} {DB : n → n → n → ℝ}
    {HB : n → n → n → n → ℝ} {R KM KD : ℝ} {KH : n → n → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    {Hc Kc : ℝ × X → n → n → n → n → 𝕜}
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (hlocal : ∀ y ∈ Kdom, ∃ timeRadius > 0, ∃ spaceRadius > 0,
      (∀ a b,
        ParabolicC0AlphaOn α (fun z => M z a b)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ a b,
        ParabolicC0AlphaOn α (fun z => N z a b)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))))
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (N z).det ≠ 0)
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hM : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖M z a b‖ ≤ C a b)
    (hN : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖N z a b‖ ≤ C a b)
    (hD : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖D z a b c‖ ≤ DB a b c)
    (hE : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖E z a b c‖ ≤ DB a b c)
    (hKc : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b i j, ‖Kc z a b i j‖ ≤
      HB a b i j)
    (hKD : 0 ≤ KD) (hR : 0 ≤ R)
    (hMdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ‖M z - N z‖ ≤ KM * R)
    (hDdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c,
      ‖D z a b c - E z a b c‖ ≤ KD * R)
    (hHdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ i j,
      ‖((fun a b => Hc z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc z a b i j) : Matrix n n 𝕜)‖ ≤ KH i j * R) :
    ∃ δ > 0,
      ParabolicBoundedWith
        (ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ C DB HB KM KD KH * R)
        (fun z : ℝ × X =>
          ricciDeTurckSchematicMatrix (M z) (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (E z) (Kc z)) Kdom := by
  have hMctrl : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) Kdom := by
    intro a b
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hKdom hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.1 a b⟩)
  have hNctrl : ∀ a b, ParabolicC0AlphaOn α (fun z => N z a b) Kdom := by
    intro a b
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hKdom hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.2 a b⟩)
  exact ricciDeTurckSchematicMatrix_bounded_sub_le_const_mul_radius_of_isCompact_det_ne_zero
    (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
    hKdom hα hMctrl hNctrl hdetM_ne hdetN_ne hDB hHB hM hN hD hE hKc
    hKD hR hMdiff hDdiff hHdiff

/-- Existential point-local product-cylinder metric controls globalize the compact-domain
linear-radius schematic RHS estimate while allowing sharper primitive Lipschitz constants to be
promoted to coarser shared constants. -/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_mul_radius_of_isCompact_of_exists_local_closedCylinder_of_primitive_le
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)} {C : n → n → ℝ} {DB : n → n → n → ℝ}
    {HB : n → n → n → n → ℝ} {R KM0 KD0 KM KD : ℝ}
    {KH0 KH : n → n → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    {Hc Kc : ℝ × X → n → n → n → n → 𝕜}
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (hlocal : ∀ y ∈ Kdom, ∃ timeRadius > 0, ∃ spaceRadius > 0,
      (∀ a b,
        ParabolicC0AlphaOn α (fun z => M z a b)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ a b,
        ParabolicC0AlphaOn α (fun z => N z a b)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))))
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (N z).det ≠ 0)
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hHB : ∀ a b i j, 0 ≤ HB a b i j)
    (hKM : KM0 ≤ KM) (hKD : KD0 ≤ KD) (hKH : ∀ i j, KH0 i j ≤ KH i j)
    (hM : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖M z a b‖ ≤ C a b)
    (hN : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖N z a b‖ ≤ C a b)
    (hD : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖D z a b c‖ ≤ DB a b c)
    (hE : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖E z a b c‖ ≤ DB a b c)
    (hKc : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b i j, ‖Kc z a b i j‖ ≤
      HB a b i j)
    (hKD0 : 0 ≤ KD0) (hR : 0 ≤ R)
    (hMdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ‖M z - N z‖ ≤ KM0 * R)
    (hDdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c,
      ‖D z a b c - E z a b c‖ ≤ KD0 * R)
    (hHdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ i j,
      ‖((fun a b => Hc z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc z a b i j) : Matrix n n 𝕜)‖ ≤ KH0 i j * R) :
    ∃ δ > 0,
      ParabolicBoundedWith
        (ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ C DB HB KM KD KH * R)
        (fun z : ℝ × X =>
          ricciDeTurckSchematicMatrix (M z) (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (E z) (Kc z)) Kdom := by
  have hMctrl : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) Kdom := by
    intro a b
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hKdom hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.1 a b⟩)
  have hNctrl : ∀ a b, ParabolicC0AlphaOn α (fun z => N z a b) Kdom := by
    intro a b
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hKdom hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.2 a b⟩)
  exact
    ricciDeTurckSchematicMatrix_bounded_sub_le_const_mul_radius_of_isCompact_det_ne_zero_of_primitive_le
      (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
      hKdom hα hMctrl hNctrl hdetM_ne hdetN_ne hDB hHB hKM hKD hKH
      hM hN hD hE hKc hKD0 hR hMdiff hDdiff hHdiff

/-- Finite-family function-level bounded-difference estimate for schematic Ricci-DeTurck RHS
fields on a compact time-space set, with one determinant lower bound shared by both metric
families. -/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_family_of_isCompact_det_ne_zero
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)}
    {C : κ → n → n → ℝ} {DB : κ → n → n → n → ℝ}
    {HB : κ → n → n → n → n → ℝ}
    {ηM ηD : κ → ℝ} {ηH : κ → n → n → ℝ}
    {M N : κ → ℝ × X → Matrix n n 𝕜}
    {D E : κ → ℝ × X → n → n → n → 𝕜}
    {Hc Kc : κ → ℝ × X → n → n → n → n → 𝕜}
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (hMctrl : ∀ r i j, ParabolicC0AlphaOn α (fun z => M r z i j) Kdom)
    (hNctrl : ∀ r i j, ParabolicC0AlphaOn α (fun z => N r z i j) Kdom)
    (hdetM_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → (M r z).det ≠ 0)
    (hdetN_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → (N r z).det ≠ 0)
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hM : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖M r z a b‖ ≤ C r a b)
    (hN : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖N r z a b‖ ≤ C r a b)
    (hD : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖D r z a b c‖ ≤ DB r a b c)
    (hE : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖E r z a b c‖ ≤ DB r a b c)
    (hKc : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b i j,
      ‖Kc r z a b i j‖ ≤ HB r a b i j)
    (hηD : ∀ r, 0 ≤ ηD r)
    (hMdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ‖M r z - N r z‖ ≤ ηM r)
    (hDdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c,
      ‖D r z a b c - E r z a b c‖ ≤ ηD r)
    (hHdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ i j,
      ‖((fun a b => Hc r z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc r z a b i j) : Matrix n n 𝕜)‖ ≤ ηH r i j) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → δ ≤ ‖(M r z).det‖) ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → δ ≤ ‖(N r z).det‖) ∧
      ∀ r,
        ParabolicBoundedWith
          (ricciDeTurckSchematicDiffBoundConst
            (𝕜 := 𝕜) δ (C r) (DB r) (HB r) (ηM r) (ηD r) (ηH r))
          (fun z : ℝ × X =>
            ricciDeTurckSchematicMatrix (M r z) (D r z) (Hc r z) -
              ricciDeTurckSchematicMatrix (N r z) (E r z) (Kc r z)) Kdom := by
  rcases matrix_det_pair_family_exists_pos_norm_lower_bound_of_isCompact
      (K := Kdom) (M := M) (N := N) hKdom hα hMctrl hNctrl hdetM_ne hdetN_ne with
    ⟨δ, hδpos, hdetM, hdetN⟩
  refine ⟨δ, hδpos, hdetM, hdetN, ?_⟩
  intro r
  exact ricciDeTurckSchematicMatrix_bounded_sub_le_const
    (s := Kdom) (δ := δ) (C := C r) (DB := DB r) (HB := HB r)
    (ηM := ηM r) (ηD := ηD r) (ηH := ηH r)
    (hDB r) (hHB r) (hM r) (hN r) (hD r) (hE r) (hKc r) (hηD r)
    (hMdiff r) (hDdiff r) (hHdiff r) hδpos (hdetM r) (hdetN r)

/-- Finite-family compact-domain bounded-difference schematic RHS estimate with coarser
primitive constants.  One compact determinant lower bound is shared by all family members, while
primitive differences proved with sharper local constants are consumed by larger chart constants
for each member. -/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_family_of_isCompact_det_ne_zero_of_primitive_le
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)}
    {C : κ → n → n → ℝ} {DB : κ → n → n → n → ℝ}
    {HB : κ → n → n → n → n → ℝ}
    {ηM0 ηD0 ηM ηD : κ → ℝ} {ηH0 ηH : κ → n → n → ℝ}
    {M N : κ → ℝ × X → Matrix n n 𝕜}
    {D E : κ → ℝ × X → n → n → n → 𝕜}
    {Hc Kc : κ → ℝ × X → n → n → n → n → 𝕜}
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (hMctrl : ∀ r i j, ParabolicC0AlphaOn α (fun z => M r z i j) Kdom)
    (hNctrl : ∀ r i j, ParabolicC0AlphaOn α (fun z => N r z i j) Kdom)
    (hdetM_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → (M r z).det ≠ 0)
    (hdetN_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → (N r z).det ≠ 0)
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hηM : ∀ r, ηM0 r ≤ ηM r) (hηD : ∀ r, ηD0 r ≤ ηD r)
    (hηH : ∀ r i j, ηH0 r i j ≤ ηH r i j)
    (hM : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖M r z a b‖ ≤ C r a b)
    (hN : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖N r z a b‖ ≤ C r a b)
    (hD : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖D r z a b c‖ ≤ DB r a b c)
    (hE : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖E r z a b c‖ ≤ DB r a b c)
    (hKc : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b i j,
      ‖Kc r z a b i j‖ ≤ HB r a b i j)
    (hηD0 : ∀ r, 0 ≤ ηD0 r)
    (hMdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ‖M r z - N r z‖ ≤ ηM0 r)
    (hDdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c,
      ‖D r z a b c - E r z a b c‖ ≤ ηD0 r)
    (hHdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ i j,
      ‖((fun a b => Hc r z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc r z a b i j) : Matrix n n 𝕜)‖ ≤ ηH0 r i j) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → δ ≤ ‖(M r z).det‖) ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → δ ≤ ‖(N r z).det‖) ∧
      ∀ r,
        ParabolicBoundedWith
          (ricciDeTurckSchematicDiffBoundConst
            (𝕜 := 𝕜) δ (C r) (DB r) (HB r) (ηM r) (ηD r) (ηH r))
          (fun z : ℝ × X =>
            ricciDeTurckSchematicMatrix (M r z) (D r z) (Hc r z) -
              ricciDeTurckSchematicMatrix (N r z) (E r z) (Kc r z)) Kdom := by
  rcases matrix_det_pair_family_exists_pos_norm_lower_bound_of_isCompact
      (K := Kdom) (M := M) (N := N) hKdom hα hMctrl hNctrl hdetM_ne hdetN_ne with
    ⟨δ, hδpos, hdetM, hdetN⟩
  refine ⟨δ, hδpos, hdetM, hdetN, ?_⟩
  intro r
  exact ricciDeTurckSchematicMatrix_bounded_sub_le_const_of_primitive_le
    (s := Kdom) (δ := δ) (C := C r) (DB := DB r) (HB := HB r)
    (ηM0 := ηM0 r) (ηD0 := ηD0 r) (ηH0 := ηH0 r)
    (ηM := ηM r) (ηD := ηD r) (ηH := ηH r)
    (M := M r) (N := N r) (D := D r) (E := E r) (H := Hc r) (K := Kc r)
    (hDB r) (hHB r) (hηM r) (hηD r) (hηH r)
    (hM r) (hN r) (hD r) (hE r) (hKc r) (hηD0 r)
    (hMdiff r) (hDdiff r) (hHdiff r) hδpos (hdetM r) (hdetN r)

/-- Finite-family linear-radius version of
`ricciDeTurckSchematicMatrix_bounded_sub_le_const_family_of_isCompact_det_ne_zero`.  One compact
determinant lower bound is shared by all family members, and each schematic RHS difference keeps a
single common comparison radius factored out. -/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_family_mul_radius_of_isCompact_det_ne_zero
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)}
    {C : κ → n → n → ℝ} {DB : κ → n → n → n → ℝ}
    {HB : κ → n → n → n → n → ℝ}
    {R : ℝ} {KM KD : κ → ℝ} {KH : κ → n → n → ℝ}
    {M N : κ → ℝ × X → Matrix n n 𝕜}
    {D E : κ → ℝ × X → n → n → n → 𝕜}
    {Hc Kc : κ → ℝ × X → n → n → n → n → 𝕜}
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (hMctrl : ∀ r i j, ParabolicC0AlphaOn α (fun z => M r z i j) Kdom)
    (hNctrl : ∀ r i j, ParabolicC0AlphaOn α (fun z => N r z i j) Kdom)
    (hdetM_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → (M r z).det ≠ 0)
    (hdetN_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → (N r z).det ≠ 0)
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hM : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖M r z a b‖ ≤ C r a b)
    (hN : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖N r z a b‖ ≤ C r a b)
    (hD : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖D r z a b c‖ ≤
      DB r a b c)
    (hE : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖E r z a b c‖ ≤
      DB r a b c)
    (hKc : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b i j,
      ‖Kc r z a b i j‖ ≤ HB r a b i j)
    (hKD : ∀ r, 0 ≤ KD r) (hR : 0 ≤ R)
    (hMdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ‖M r z - N r z‖ ≤ KM r * R)
    (hDdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c,
      ‖D r z a b c - E r z a b c‖ ≤ KD r * R)
    (hHdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ i j,
      ‖((fun a b => Hc r z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc r z a b i j) : Matrix n n 𝕜)‖ ≤ KH r i j * R) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → δ ≤ ‖(M r z).det‖) ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → δ ≤ ‖(N r z).det‖) ∧
      ∀ r,
        ParabolicBoundedWith
          (ricciDeTurckSchematicDiffBoundConst
            (𝕜 := 𝕜) δ (C r) (DB r) (HB r) (KM r) (KD r) (KH r) * R)
          (fun z : ℝ × X =>
            ricciDeTurckSchematicMatrix (M r z) (D r z) (Hc r z) -
              ricciDeTurckSchematicMatrix (N r z) (E r z) (Kc r z)) Kdom := by
  rcases matrix_det_pair_family_exists_pos_norm_lower_bound_of_isCompact
      (K := Kdom) (M := M) (N := N) hKdom hα hMctrl hNctrl hdetM_ne hdetN_ne with
    ⟨δ, hδpos, hdetM, hdetN⟩
  refine ⟨δ, hδpos, hdetM, hdetN, ?_⟩
  intro r
  exact ricciDeTurckSchematicMatrix_bounded_sub_le_const_mul_radius
    (s := Kdom) (δ := δ) (C := C r) (DB := DB r) (HB := HB r)
    (R := R) (KM := KM r) (KD := KD r) (KH := KH r)
    (M := M r) (N := N r) (D := D r) (E := E r) (H := Hc r) (K := Kc r)
    (hDB r) (hHB r) (hM r) (hN r) (hD r) (hE r) (hKc r) (hKD r) hR
    (hMdiff r) (hDdiff r) (hHdiff r) hδpos (hdetM r) (hdetN r)

/-- Finite-family compact-domain linear-radius schematic RHS estimate with coarser primitive
Lipschitz constants.  One compact determinant lower bound is shared by all family members, while
primitive differences proved with sharper local constants are consumed by larger chart constants
for each member. -/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_family_mul_radius_of_isCompact_det_ne_zero_of_primitive_le
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)}
    {C : κ → n → n → ℝ} {DB : κ → n → n → n → ℝ}
    {HB : κ → n → n → n → n → ℝ}
    {R : ℝ} {KM0 KD0 KM KD : κ → ℝ} {KH0 KH : κ → n → n → ℝ}
    {M N : κ → ℝ × X → Matrix n n 𝕜}
    {D E : κ → ℝ × X → n → n → n → 𝕜}
    {Hc Kc : κ → ℝ × X → n → n → n → n → 𝕜}
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (hMctrl : ∀ r i j, ParabolicC0AlphaOn α (fun z => M r z i j) Kdom)
    (hNctrl : ∀ r i j, ParabolicC0AlphaOn α (fun z => N r z i j) Kdom)
    (hdetM_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → (M r z).det ≠ 0)
    (hdetN_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → (N r z).det ≠ 0)
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hKM : ∀ r, KM0 r ≤ KM r) (hKD : ∀ r, KD0 r ≤ KD r)
    (hKH : ∀ r i j, KH0 r i j ≤ KH r i j)
    (hM : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖M r z a b‖ ≤ C r a b)
    (hN : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖N r z a b‖ ≤ C r a b)
    (hD : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖D r z a b c‖ ≤
      DB r a b c)
    (hE : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖E r z a b c‖ ≤
      DB r a b c)
    (hKc : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b i j,
      ‖Kc r z a b i j‖ ≤ HB r a b i j)
    (hKD0 : ∀ r, 0 ≤ KD0 r) (hR : 0 ≤ R)
    (hMdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ‖M r z - N r z‖ ≤ KM0 r * R)
    (hDdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c,
      ‖D r z a b c - E r z a b c‖ ≤ KD0 r * R)
    (hHdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ i j,
      ‖((fun a b => Hc r z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc r z a b i j) : Matrix n n 𝕜)‖ ≤ KH0 r i j * R) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → δ ≤ ‖(M r z).det‖) ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → δ ≤ ‖(N r z).det‖) ∧
      ∀ r,
        ParabolicBoundedWith
          (ricciDeTurckSchematicDiffBoundConst
            (𝕜 := 𝕜) δ (C r) (DB r) (HB r) (KM r) (KD r) (KH r) * R)
          (fun z : ℝ × X =>
            ricciDeTurckSchematicMatrix (M r z) (D r z) (Hc r z) -
              ricciDeTurckSchematicMatrix (N r z) (E r z) (Kc r z)) Kdom := by
  rcases matrix_det_pair_family_exists_pos_norm_lower_bound_of_isCompact
      (K := Kdom) (M := M) (N := N) hKdom hα hMctrl hNctrl hdetM_ne hdetN_ne with
    ⟨δ, hδpos, hdetM, hdetN⟩
  refine ⟨δ, hδpos, hdetM, hdetN, ?_⟩
  intro r
  exact ricciDeTurckSchematicMatrix_bounded_sub_le_const_mul_radius_of_primitive_le
    (s := Kdom) (δ := δ) (C := C r) (DB := DB r) (HB := HB r)
    (R := R) (KM0 := KM0 r) (KD0 := KD0 r) (KH0 := KH0 r)
    (KM := KM r) (KD := KD r) (KH := KH r)
    (M := M r) (N := N r) (D := D r) (E := E r) (H := Hc r) (K := Kc r)
    (hDB r) (hHB r) (hKM r) (hKD r) (hKH r)
    (hM r) (hN r) (hD r) (hE r) (hKc r) (hKD0 r) hR
    (hMdiff r) (hDdiff r) (hHdiff r) hδpos (hdetM r) (hdetN r)

/-- Local finite product-cylinder metric controls globalize the finite-family compact-domain
function-level bounded-difference estimate for schematic Ricci-DeTurck RHS fields, with one
determinant lower bound shared by both metric families. -/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_family_of_finset_parabolicCylinder_cover_closedCylinder_variable
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)}
    {C : κ → n → n → ℝ} {DB : κ → n → n → n → ℝ}
    {HB : κ → n → n → n → n → ℝ}
    {ηM ηD : κ → ℝ} {ηH : κ → n → n → ℝ}
    {M N : κ → ℝ × X → Matrix n n 𝕜}
    {D E : κ → ℝ × X → n → n → n → 𝕜}
    {Hc Kc : κ → ℝ × X → n → n → n → n → 𝕜}
    (S : Finset (ℝ × X)) (timeRadius spaceRadius : ℝ × X → ℝ)
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (htime_pos : ∀ y ∈ S, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ S, 0 < spaceRadius y)
    (hcover : Kdom ⊆ ⋃ y ∈ S, parabolicCylinder y (timeRadius y) (spaceRadius y))
    (hMlocal : ∀ y ∈ S, ∀ r a b,
      ParabolicC0AlphaOn α (fun z => M r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hNlocal : ∀ y ∈ S, ∀ r a b,
      ParabolicC0AlphaOn α (fun z => N r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hdetM_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → (M r z).det ≠ 0)
    (hdetN_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → (N r z).det ≠ 0)
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hM : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖M r z a b‖ ≤ C r a b)
    (hN : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖N r z a b‖ ≤ C r a b)
    (hD : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖D r z a b c‖ ≤
      DB r a b c)
    (hE : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖E r z a b c‖ ≤
      DB r a b c)
    (hKc : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b i j,
      ‖Kc r z a b i j‖ ≤ HB r a b i j)
    (hηD : ∀ r, 0 ≤ ηD r)
    (hMdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ‖M r z - N r z‖ ≤ ηM r)
    (hDdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c,
      ‖D r z a b c - E r z a b c‖ ≤ ηD r)
    (hHdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ i j,
      ‖((fun a b => Hc r z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc r z a b i j) : Matrix n n 𝕜)‖ ≤ ηH r i j) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → δ ≤ ‖(M r z).det‖) ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → δ ≤ ‖(N r z).det‖) ∧
      ∀ r,
        ParabolicBoundedWith
          (ricciDeTurckSchematicDiffBoundConst
            (𝕜 := 𝕜) δ (C r) (DB r) (HB r) (ηM r) (ηD r) (ηH r))
          (fun z : ℝ × X =>
            ricciDeTurckSchematicMatrix (M r z) (D r z) (Hc r z) -
              ricciDeTurckSchematicMatrix (N r z) (E r z) (Kc r z)) Kdom := by
  have hMctrl : ∀ r a b, ParabolicC0AlphaOn α (fun z => M r z a b) Kdom := by
    intro r a b
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hMlocal y hy r a b)
  have hNctrl : ∀ r a b, ParabolicC0AlphaOn α (fun z => N r z a b) Kdom := by
    intro r a b
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hNlocal y hy r a b)
  exact ricciDeTurckSchematicMatrix_bounded_sub_le_const_family_of_isCompact_det_ne_zero
    (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
    hKdom hα hMctrl hNctrl hdetM_ne hdetN_ne hDB hHB hM hN hD hE hKc
    hηD hMdiff hDdiff hHdiff

/-- Point-dependent local product-cylinder metric controls globalize the finite-family
compact-domain function-level bounded-difference estimate for schematic Ricci-DeTurck RHS fields,
with one determinant lower bound shared by both metric families. -/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_family_of_isCompact_of_local_closedCylinder_variable
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)}
    {C : κ → n → n → ℝ} {DB : κ → n → n → n → ℝ}
    {HB : κ → n → n → n → n → ℝ}
    {ηM ηD : κ → ℝ} {ηH : κ → n → n → ℝ}
    {M N : κ → ℝ × X → Matrix n n 𝕜}
    {D E : κ → ℝ × X → n → n → n → 𝕜}
    {Hc Kc : κ → ℝ × X → n → n → n → n → 𝕜}
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (timeRadius spaceRadius : ℝ × X → ℝ)
    (htime_pos : ∀ y ∈ Kdom, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ Kdom, 0 < spaceRadius y)
    (hMlocal : ∀ y ∈ Kdom, ∀ r a b,
      ParabolicC0AlphaOn α (fun z => M r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hNlocal : ∀ y ∈ Kdom, ∀ r a b,
      ParabolicC0AlphaOn α (fun z => N r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hdetM_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → (M r z).det ≠ 0)
    (hdetN_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → (N r z).det ≠ 0)
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hM : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖M r z a b‖ ≤ C r a b)
    (hN : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖N r z a b‖ ≤ C r a b)
    (hD : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖D r z a b c‖ ≤
      DB r a b c)
    (hE : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖E r z a b c‖ ≤
      DB r a b c)
    (hKc : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b i j,
      ‖Kc r z a b i j‖ ≤ HB r a b i j)
    (hηD : ∀ r, 0 ≤ ηD r)
    (hMdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ‖M r z - N r z‖ ≤ ηM r)
    (hDdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c,
      ‖D r z a b c - E r z a b c‖ ≤ ηD r)
    (hHdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ i j,
      ‖((fun a b => Hc r z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc r z a b i j) : Matrix n n 𝕜)‖ ≤ ηH r i j) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → δ ≤ ‖(M r z).det‖) ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → δ ≤ ‖(N r z).det‖) ∧
      ∀ r,
        ParabolicBoundedWith
          (ricciDeTurckSchematicDiffBoundConst
            (𝕜 := 𝕜) δ (C r) (DB r) (HB r) (ηM r) (ηD r) (ηH r))
          (fun z : ℝ × X =>
            ricciDeTurckSchematicMatrix (M r z) (D r z) (Hc r z) -
              ricciDeTurckSchematicMatrix (N r z) (E r z) (Kc r z)) Kdom := by
  have hMctrl : ∀ r a b, ParabolicC0AlphaOn α (fun z => M r z a b) Kdom := by
    intro r a b
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hKdom hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hMlocal y hy r a b)
  have hNctrl : ∀ r a b, ParabolicC0AlphaOn α (fun z => N r z a b) Kdom := by
    intro r a b
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hKdom hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hNlocal y hy r a b)
  exact ricciDeTurckSchematicMatrix_bounded_sub_le_const_family_of_isCompact_det_ne_zero
    (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
    hKdom hα hMctrl hNctrl hdetM_ne hdetN_ne hDB hHB hM hN hD hE hKc
    hηD hMdiff hDdiff hHdiff

/-- Existential point-local product-cylinder metric controls globalize the finite-family
compact-domain function-level bounded-difference estimate for schematic Ricci-DeTurck RHS fields,
with one determinant lower bound shared by both metric families. -/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_family_of_isCompact_of_exists_local_closedCylinder
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)}
    {C : κ → n → n → ℝ} {DB : κ → n → n → n → ℝ}
    {HB : κ → n → n → n → n → ℝ}
    {ηM ηD : κ → ℝ} {ηH : κ → n → n → ℝ}
    {M N : κ → ℝ × X → Matrix n n 𝕜}
    {D E : κ → ℝ × X → n → n → n → 𝕜}
    {Hc Kc : κ → ℝ × X → n → n → n → n → 𝕜}
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (hlocal : ∀ y ∈ Kdom, ∃ timeRadius > 0, ∃ spaceRadius > 0,
      (∀ r a b,
        ParabolicC0AlphaOn α (fun z => M r z a b)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ r a b,
        ParabolicC0AlphaOn α (fun z => N r z a b)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))))
    (hdetM_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → (M r z).det ≠ 0)
    (hdetN_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → (N r z).det ≠ 0)
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hM : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖M r z a b‖ ≤ C r a b)
    (hN : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖N r z a b‖ ≤ C r a b)
    (hD : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖D r z a b c‖ ≤
      DB r a b c)
    (hE : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖E r z a b c‖ ≤
      DB r a b c)
    (hKc : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b i j,
      ‖Kc r z a b i j‖ ≤ HB r a b i j)
    (hηD : ∀ r, 0 ≤ ηD r)
    (hMdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ‖M r z - N r z‖ ≤ ηM r)
    (hDdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c,
      ‖D r z a b c - E r z a b c‖ ≤ ηD r)
    (hHdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ i j,
      ‖((fun a b => Hc r z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc r z a b i j) : Matrix n n 𝕜)‖ ≤ ηH r i j) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → δ ≤ ‖(M r z).det‖) ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → δ ≤ ‖(N r z).det‖) ∧
      ∀ r,
        ParabolicBoundedWith
          (ricciDeTurckSchematicDiffBoundConst
            (𝕜 := 𝕜) δ (C r) (DB r) (HB r) (ηM r) (ηD r) (ηH r))
          (fun z : ℝ × X =>
            ricciDeTurckSchematicMatrix (M r z) (D r z) (Hc r z) -
              ricciDeTurckSchematicMatrix (N r z) (E r z) (Kc r z)) Kdom := by
  have hMctrl : ∀ r a b, ParabolicC0AlphaOn α (fun z => M r z a b) Kdom := by
    intro r a b
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hKdom hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.1 r a b⟩)
  have hNctrl : ∀ r a b, ParabolicC0AlphaOn α (fun z => N r z a b) Kdom := by
    intro r a b
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hKdom hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.2 r a b⟩)
  exact ricciDeTurckSchematicMatrix_bounded_sub_le_const_family_of_isCompact_det_ne_zero
    (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
    hKdom hα hMctrl hNctrl hdetM_ne hdetN_ne hDB hHB hM hN hD hE hKc
    hηD hMdiff hDdiff hHdiff

/-- Local finite product-cylinder metric controls globalize the finite-family compact-domain
bounded-difference schematic RHS estimate while allowing sharper primitive constants to be
promoted to coarser shared constants for each family member. -/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_family_of_finset_parabolicCylinder_cover_closedCylinder_variable_of_primitive_le
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)}
    {C : κ → n → n → ℝ} {DB : κ → n → n → n → ℝ}
    {HB : κ → n → n → n → n → ℝ}
    {ηM0 ηD0 ηM ηD : κ → ℝ} {ηH0 ηH : κ → n → n → ℝ}
    {M N : κ → ℝ × X → Matrix n n 𝕜}
    {D E : κ → ℝ × X → n → n → n → 𝕜}
    {Hc Kc : κ → ℝ × X → n → n → n → n → 𝕜}
    (S : Finset (ℝ × X)) (timeRadius spaceRadius : ℝ × X → ℝ)
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (htime_pos : ∀ y ∈ S, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ S, 0 < spaceRadius y)
    (hcover : Kdom ⊆ ⋃ y ∈ S, parabolicCylinder y (timeRadius y) (spaceRadius y))
    (hMlocal : ∀ y ∈ S, ∀ r a b,
      ParabolicC0AlphaOn α (fun z => M r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hNlocal : ∀ y ∈ S, ∀ r a b,
      ParabolicC0AlphaOn α (fun z => N r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hdetM_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → (M r z).det ≠ 0)
    (hdetN_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → (N r z).det ≠ 0)
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hηM : ∀ r, ηM0 r ≤ ηM r) (hηD : ∀ r, ηD0 r ≤ ηD r)
    (hηH : ∀ r i j, ηH0 r i j ≤ ηH r i j)
    (hM : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖M r z a b‖ ≤ C r a b)
    (hN : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖N r z a b‖ ≤ C r a b)
    (hD : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖D r z a b c‖ ≤
      DB r a b c)
    (hE : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖E r z a b c‖ ≤
      DB r a b c)
    (hKc : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b i j,
      ‖Kc r z a b i j‖ ≤ HB r a b i j)
    (hηD0 : ∀ r, 0 ≤ ηD0 r)
    (hMdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ‖M r z - N r z‖ ≤ ηM0 r)
    (hDdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c,
      ‖D r z a b c - E r z a b c‖ ≤ ηD0 r)
    (hHdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ i j,
      ‖((fun a b => Hc r z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc r z a b i j) : Matrix n n 𝕜)‖ ≤ ηH0 r i j) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → δ ≤ ‖(M r z).det‖) ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → δ ≤ ‖(N r z).det‖) ∧
      ∀ r,
        ParabolicBoundedWith
          (ricciDeTurckSchematicDiffBoundConst
            (𝕜 := 𝕜) δ (C r) (DB r) (HB r) (ηM r) (ηD r) (ηH r))
          (fun z : ℝ × X =>
            ricciDeTurckSchematicMatrix (M r z) (D r z) (Hc r z) -
              ricciDeTurckSchematicMatrix (N r z) (E r z) (Kc r z)) Kdom := by
  have hMctrl : ∀ r a b, ParabolicC0AlphaOn α (fun z => M r z a b) Kdom := by
    intro r a b
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hMlocal y hy r a b)
  have hNctrl : ∀ r a b, ParabolicC0AlphaOn α (fun z => N r z a b) Kdom := by
    intro r a b
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hNlocal y hy r a b)
  exact
    ricciDeTurckSchematicMatrix_bounded_sub_le_const_family_of_isCompact_det_ne_zero_of_primitive_le
      (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
      hKdom hα hMctrl hNctrl hdetM_ne hdetN_ne hDB hHB hηM hηD hηH
      hM hN hD hE hKc hηD0 hMdiff hDdiff hHdiff

/-- Point-dependent local product-cylinder metric controls globalize the finite-family
compact-domain bounded-difference schematic RHS estimate while allowing sharper primitive
constants to be promoted to coarser shared constants for each family member. -/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_family_of_isCompact_of_local_closedCylinder_variable_of_primitive_le
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)}
    {C : κ → n → n → ℝ} {DB : κ → n → n → n → ℝ}
    {HB : κ → n → n → n → n → ℝ}
    {ηM0 ηD0 ηM ηD : κ → ℝ} {ηH0 ηH : κ → n → n → ℝ}
    {M N : κ → ℝ × X → Matrix n n 𝕜}
    {D E : κ → ℝ × X → n → n → n → 𝕜}
    {Hc Kc : κ → ℝ × X → n → n → n → n → 𝕜}
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (timeRadius spaceRadius : ℝ × X → ℝ)
    (htime_pos : ∀ y ∈ Kdom, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ Kdom, 0 < spaceRadius y)
    (hMlocal : ∀ y ∈ Kdom, ∀ r a b,
      ParabolicC0AlphaOn α (fun z => M r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hNlocal : ∀ y ∈ Kdom, ∀ r a b,
      ParabolicC0AlphaOn α (fun z => N r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hdetM_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → (M r z).det ≠ 0)
    (hdetN_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → (N r z).det ≠ 0)
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hηM : ∀ r, ηM0 r ≤ ηM r) (hηD : ∀ r, ηD0 r ≤ ηD r)
    (hηH : ∀ r i j, ηH0 r i j ≤ ηH r i j)
    (hM : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖M r z a b‖ ≤ C r a b)
    (hN : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖N r z a b‖ ≤ C r a b)
    (hD : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖D r z a b c‖ ≤
      DB r a b c)
    (hE : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖E r z a b c‖ ≤
      DB r a b c)
    (hKc : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b i j,
      ‖Kc r z a b i j‖ ≤ HB r a b i j)
    (hηD0 : ∀ r, 0 ≤ ηD0 r)
    (hMdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ‖M r z - N r z‖ ≤ ηM0 r)
    (hDdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c,
      ‖D r z a b c - E r z a b c‖ ≤ ηD0 r)
    (hHdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ i j,
      ‖((fun a b => Hc r z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc r z a b i j) : Matrix n n 𝕜)‖ ≤ ηH0 r i j) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → δ ≤ ‖(M r z).det‖) ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → δ ≤ ‖(N r z).det‖) ∧
      ∀ r,
        ParabolicBoundedWith
          (ricciDeTurckSchematicDiffBoundConst
            (𝕜 := 𝕜) δ (C r) (DB r) (HB r) (ηM r) (ηD r) (ηH r))
          (fun z : ℝ × X =>
            ricciDeTurckSchematicMatrix (M r z) (D r z) (Hc r z) -
              ricciDeTurckSchematicMatrix (N r z) (E r z) (Kc r z)) Kdom := by
  have hMctrl : ∀ r a b, ParabolicC0AlphaOn α (fun z => M r z a b) Kdom := by
    intro r a b
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hKdom hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hMlocal y hy r a b)
  have hNctrl : ∀ r a b, ParabolicC0AlphaOn α (fun z => N r z a b) Kdom := by
    intro r a b
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hKdom hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hNlocal y hy r a b)
  exact
    ricciDeTurckSchematicMatrix_bounded_sub_le_const_family_of_isCompact_det_ne_zero_of_primitive_le
      (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
      hKdom hα hMctrl hNctrl hdetM_ne hdetN_ne hDB hHB hηM hηD hηH
      hM hN hD hE hKc hηD0 hMdiff hDdiff hHdiff

/-- Existential point-local product-cylinder metric controls globalize the finite-family
compact-domain bounded-difference schematic RHS estimate while allowing sharper primitive
constants to be promoted to coarser shared constants for each family member. -/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_family_of_isCompact_of_exists_local_closedCylinder_of_primitive_le
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)}
    {C : κ → n → n → ℝ} {DB : κ → n → n → n → ℝ}
    {HB : κ → n → n → n → n → ℝ}
    {ηM0 ηD0 ηM ηD : κ → ℝ} {ηH0 ηH : κ → n → n → ℝ}
    {M N : κ → ℝ × X → Matrix n n 𝕜}
    {D E : κ → ℝ × X → n → n → n → 𝕜}
    {Hc Kc : κ → ℝ × X → n → n → n → n → 𝕜}
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (hlocal : ∀ y ∈ Kdom, ∃ timeRadius > 0, ∃ spaceRadius > 0,
      (∀ r a b,
        ParabolicC0AlphaOn α (fun z => M r z a b)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ r a b,
        ParabolicC0AlphaOn α (fun z => N r z a b)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))))
    (hdetM_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → (M r z).det ≠ 0)
    (hdetN_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → (N r z).det ≠ 0)
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hηM : ∀ r, ηM0 r ≤ ηM r) (hηD : ∀ r, ηD0 r ≤ ηD r)
    (hηH : ∀ r i j, ηH0 r i j ≤ ηH r i j)
    (hM : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖M r z a b‖ ≤ C r a b)
    (hN : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖N r z a b‖ ≤ C r a b)
    (hD : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖D r z a b c‖ ≤
      DB r a b c)
    (hE : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖E r z a b c‖ ≤
      DB r a b c)
    (hKc : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b i j,
      ‖Kc r z a b i j‖ ≤ HB r a b i j)
    (hηD0 : ∀ r, 0 ≤ ηD0 r)
    (hMdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ‖M r z - N r z‖ ≤ ηM0 r)
    (hDdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c,
      ‖D r z a b c - E r z a b c‖ ≤ ηD0 r)
    (hHdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ i j,
      ‖((fun a b => Hc r z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc r z a b i j) : Matrix n n 𝕜)‖ ≤ ηH0 r i j) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → δ ≤ ‖(M r z).det‖) ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → δ ≤ ‖(N r z).det‖) ∧
      ∀ r,
        ParabolicBoundedWith
          (ricciDeTurckSchematicDiffBoundConst
            (𝕜 := 𝕜) δ (C r) (DB r) (HB r) (ηM r) (ηD r) (ηH r))
          (fun z : ℝ × X =>
            ricciDeTurckSchematicMatrix (M r z) (D r z) (Hc r z) -
              ricciDeTurckSchematicMatrix (N r z) (E r z) (Kc r z)) Kdom := by
  have hMctrl : ∀ r a b, ParabolicC0AlphaOn α (fun z => M r z a b) Kdom := by
    intro r a b
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hKdom hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.1 r a b⟩)
  have hNctrl : ∀ r a b, ParabolicC0AlphaOn α (fun z => N r z a b) Kdom := by
    intro r a b
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hKdom hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.2 r a b⟩)
  exact
    ricciDeTurckSchematicMatrix_bounded_sub_le_const_family_of_isCompact_det_ne_zero_of_primitive_le
      (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
      hKdom hα hMctrl hNctrl hdetM_ne hdetN_ne hDB hHB hηM hηD hηH
      hM hN hD hE hKc hηD0 hMdiff hDdiff hHdiff

/-- Local finite product-cylinder metric controls globalize the finite-family compact-domain
linear-radius bounded-difference estimate for schematic Ricci-DeTurck RHS fields. -/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_family_mul_radius_of_finset_parabolicCylinder_cover_closedCylinder_variable
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)}
    {C : κ → n → n → ℝ} {DB : κ → n → n → n → ℝ}
    {HB : κ → n → n → n → n → ℝ}
    {R : ℝ} {KM KD : κ → ℝ} {KH : κ → n → n → ℝ}
    {M N : κ → ℝ × X → Matrix n n 𝕜}
    {D E : κ → ℝ × X → n → n → n → 𝕜}
    {Hc Kc : κ → ℝ × X → n → n → n → n → 𝕜}
    (S : Finset (ℝ × X)) (timeRadius spaceRadius : ℝ × X → ℝ)
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (htime_pos : ∀ y ∈ S, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ S, 0 < spaceRadius y)
    (hcover : Kdom ⊆ ⋃ y ∈ S, parabolicCylinder y (timeRadius y) (spaceRadius y))
    (hMlocal : ∀ y ∈ S, ∀ r a b,
      ParabolicC0AlphaOn α (fun z => M r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hNlocal : ∀ y ∈ S, ∀ r a b,
      ParabolicC0AlphaOn α (fun z => N r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hdetM_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → (M r z).det ≠ 0)
    (hdetN_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → (N r z).det ≠ 0)
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hM : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖M r z a b‖ ≤ C r a b)
    (hN : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖N r z a b‖ ≤ C r a b)
    (hD : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖D r z a b c‖ ≤
      DB r a b c)
    (hE : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖E r z a b c‖ ≤
      DB r a b c)
    (hKc : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b i j,
      ‖Kc r z a b i j‖ ≤ HB r a b i j)
    (hKD : ∀ r, 0 ≤ KD r) (hR : 0 ≤ R)
    (hMdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ‖M r z - N r z‖ ≤ KM r * R)
    (hDdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c,
      ‖D r z a b c - E r z a b c‖ ≤ KD r * R)
    (hHdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ i j,
      ‖((fun a b => Hc r z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc r z a b i j) : Matrix n n 𝕜)‖ ≤ KH r i j * R) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → δ ≤ ‖(M r z).det‖) ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → δ ≤ ‖(N r z).det‖) ∧
      ∀ r,
        ParabolicBoundedWith
          (ricciDeTurckSchematicDiffBoundConst
            (𝕜 := 𝕜) δ (C r) (DB r) (HB r) (KM r) (KD r) (KH r) * R)
          (fun z : ℝ × X =>
            ricciDeTurckSchematicMatrix (M r z) (D r z) (Hc r z) -
              ricciDeTurckSchematicMatrix (N r z) (E r z) (Kc r z)) Kdom := by
  have hMctrl : ∀ r a b, ParabolicC0AlphaOn α (fun z => M r z a b) Kdom := by
    intro r a b
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hMlocal y hy r a b)
  have hNctrl : ∀ r a b, ParabolicC0AlphaOn α (fun z => N r z a b) Kdom := by
    intro r a b
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hNlocal y hy r a b)
  exact ricciDeTurckSchematicMatrix_bounded_sub_le_const_family_mul_radius_of_isCompact_det_ne_zero
    (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
    hKdom hα hMctrl hNctrl hdetM_ne hdetN_ne hDB hHB hM hN hD hE hKc
    hKD hR hMdiff hDdiff hHdiff

/-- Point-dependent local product-cylinder metric controls globalize the finite-family
compact-domain linear-radius bounded-difference estimate for schematic Ricci-DeTurck RHS fields.
-/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_family_mul_radius_of_isCompact_of_local_closedCylinder_variable
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)}
    {C : κ → n → n → ℝ} {DB : κ → n → n → n → ℝ}
    {HB : κ → n → n → n → n → ℝ}
    {R : ℝ} {KM KD : κ → ℝ} {KH : κ → n → n → ℝ}
    {M N : κ → ℝ × X → Matrix n n 𝕜}
    {D E : κ → ℝ × X → n → n → n → 𝕜}
    {Hc Kc : κ → ℝ × X → n → n → n → n → 𝕜}
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (timeRadius spaceRadius : ℝ × X → ℝ)
    (htime_pos : ∀ y ∈ Kdom, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ Kdom, 0 < spaceRadius y)
    (hMlocal : ∀ y ∈ Kdom, ∀ r a b,
      ParabolicC0AlphaOn α (fun z => M r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hNlocal : ∀ y ∈ Kdom, ∀ r a b,
      ParabolicC0AlphaOn α (fun z => N r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hdetM_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → (M r z).det ≠ 0)
    (hdetN_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → (N r z).det ≠ 0)
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hM : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖M r z a b‖ ≤ C r a b)
    (hN : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖N r z a b‖ ≤ C r a b)
    (hD : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖D r z a b c‖ ≤
      DB r a b c)
    (hE : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖E r z a b c‖ ≤
      DB r a b c)
    (hKc : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b i j,
      ‖Kc r z a b i j‖ ≤ HB r a b i j)
    (hKD : ∀ r, 0 ≤ KD r) (hR : 0 ≤ R)
    (hMdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ‖M r z - N r z‖ ≤ KM r * R)
    (hDdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c,
      ‖D r z a b c - E r z a b c‖ ≤ KD r * R)
    (hHdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ i j,
      ‖((fun a b => Hc r z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc r z a b i j) : Matrix n n 𝕜)‖ ≤ KH r i j * R) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → δ ≤ ‖(M r z).det‖) ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → δ ≤ ‖(N r z).det‖) ∧
      ∀ r,
        ParabolicBoundedWith
          (ricciDeTurckSchematicDiffBoundConst
            (𝕜 := 𝕜) δ (C r) (DB r) (HB r) (KM r) (KD r) (KH r) * R)
          (fun z : ℝ × X =>
            ricciDeTurckSchematicMatrix (M r z) (D r z) (Hc r z) -
              ricciDeTurckSchematicMatrix (N r z) (E r z) (Kc r z)) Kdom := by
  have hMctrl : ∀ r a b, ParabolicC0AlphaOn α (fun z => M r z a b) Kdom := by
    intro r a b
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hKdom hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hMlocal y hy r a b)
  have hNctrl : ∀ r a b, ParabolicC0AlphaOn α (fun z => N r z a b) Kdom := by
    intro r a b
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hKdom hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hNlocal y hy r a b)
  exact ricciDeTurckSchematicMatrix_bounded_sub_le_const_family_mul_radius_of_isCompact_det_ne_zero
    (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
    hKdom hα hMctrl hNctrl hdetM_ne hdetN_ne hDB hHB hM hN hD hE hKc
    hKD hR hMdiff hDdiff hHdiff

/-- Existential point-local product-cylinder metric controls globalize the finite-family
compact-domain linear-radius bounded-difference estimate for schematic Ricci-DeTurck RHS fields.
-/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_family_mul_radius_of_isCompact_of_exists_local_closedCylinder
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)}
    {C : κ → n → n → ℝ} {DB : κ → n → n → n → ℝ}
    {HB : κ → n → n → n → n → ℝ}
    {R : ℝ} {KM KD : κ → ℝ} {KH : κ → n → n → ℝ}
    {M N : κ → ℝ × X → Matrix n n 𝕜}
    {D E : κ → ℝ × X → n → n → n → 𝕜}
    {Hc Kc : κ → ℝ × X → n → n → n → n → 𝕜}
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (hlocal : ∀ y ∈ Kdom, ∃ timeRadius > 0, ∃ spaceRadius > 0,
      (∀ r a b,
        ParabolicC0AlphaOn α (fun z => M r z a b)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ r a b,
        ParabolicC0AlphaOn α (fun z => N r z a b)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))))
    (hdetM_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → (M r z).det ≠ 0)
    (hdetN_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → (N r z).det ≠ 0)
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hM : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖M r z a b‖ ≤ C r a b)
    (hN : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖N r z a b‖ ≤ C r a b)
    (hD : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖D r z a b c‖ ≤
      DB r a b c)
    (hE : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖E r z a b c‖ ≤
      DB r a b c)
    (hKc : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b i j,
      ‖Kc r z a b i j‖ ≤ HB r a b i j)
    (hKD : ∀ r, 0 ≤ KD r) (hR : 0 ≤ R)
    (hMdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ‖M r z - N r z‖ ≤ KM r * R)
    (hDdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c,
      ‖D r z a b c - E r z a b c‖ ≤ KD r * R)
    (hHdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ i j,
      ‖((fun a b => Hc r z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc r z a b i j) : Matrix n n 𝕜)‖ ≤ KH r i j * R) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → δ ≤ ‖(M r z).det‖) ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → δ ≤ ‖(N r z).det‖) ∧
      ∀ r,
        ParabolicBoundedWith
          (ricciDeTurckSchematicDiffBoundConst
            (𝕜 := 𝕜) δ (C r) (DB r) (HB r) (KM r) (KD r) (KH r) * R)
          (fun z : ℝ × X =>
            ricciDeTurckSchematicMatrix (M r z) (D r z) (Hc r z) -
              ricciDeTurckSchematicMatrix (N r z) (E r z) (Kc r z)) Kdom := by
  have hMctrl : ∀ r a b, ParabolicC0AlphaOn α (fun z => M r z a b) Kdom := by
    intro r a b
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hKdom hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.1 r a b⟩)
  have hNctrl : ∀ r a b, ParabolicC0AlphaOn α (fun z => N r z a b) Kdom := by
    intro r a b
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hKdom hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.2 r a b⟩)
  exact ricciDeTurckSchematicMatrix_bounded_sub_le_const_family_mul_radius_of_isCompact_det_ne_zero
    (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
    hKdom hα hMctrl hNctrl hdetM_ne hdetN_ne hDB hHB hM hN hD hE hKc
    hKD hR hMdiff hDdiff hHdiff

/-- Local finite product-cylinder metric controls globalize the finite-family compact-domain
linear-radius schematic RHS estimate while allowing sharper primitive Lipschitz constants to be
promoted to coarser shared constants for each family member. -/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_family_mul_radius_of_finset_parabolicCylinder_cover_closedCylinder_variable_of_primitive_le
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)}
    {C : κ → n → n → ℝ} {DB : κ → n → n → n → ℝ}
    {HB : κ → n → n → n → n → ℝ}
    {R : ℝ} {KM0 KD0 KM KD : κ → ℝ} {KH0 KH : κ → n → n → ℝ}
    {M N : κ → ℝ × X → Matrix n n 𝕜}
    {D E : κ → ℝ × X → n → n → n → 𝕜}
    {Hc Kc : κ → ℝ × X → n → n → n → n → 𝕜}
    (S : Finset (ℝ × X)) (timeRadius spaceRadius : ℝ × X → ℝ)
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (htime_pos : ∀ y ∈ S, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ S, 0 < spaceRadius y)
    (hcover : Kdom ⊆ ⋃ y ∈ S, parabolicCylinder y (timeRadius y) (spaceRadius y))
    (hMlocal : ∀ y ∈ S, ∀ r a b,
      ParabolicC0AlphaOn α (fun z => M r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hNlocal : ∀ y ∈ S, ∀ r a b,
      ParabolicC0AlphaOn α (fun z => N r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hdetM_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → (M r z).det ≠ 0)
    (hdetN_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → (N r z).det ≠ 0)
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hKM : ∀ r, KM0 r ≤ KM r) (hKD : ∀ r, KD0 r ≤ KD r)
    (hKH : ∀ r i j, KH0 r i j ≤ KH r i j)
    (hM : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖M r z a b‖ ≤ C r a b)
    (hN : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖N r z a b‖ ≤ C r a b)
    (hD : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖D r z a b c‖ ≤
      DB r a b c)
    (hE : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖E r z a b c‖ ≤
      DB r a b c)
    (hKc : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b i j,
      ‖Kc r z a b i j‖ ≤ HB r a b i j)
    (hKD0 : ∀ r, 0 ≤ KD0 r) (hR : 0 ≤ R)
    (hMdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ‖M r z - N r z‖ ≤ KM0 r * R)
    (hDdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c,
      ‖D r z a b c - E r z a b c‖ ≤ KD0 r * R)
    (hHdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ i j,
      ‖((fun a b => Hc r z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc r z a b i j) : Matrix n n 𝕜)‖ ≤ KH0 r i j * R) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → δ ≤ ‖(M r z).det‖) ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → δ ≤ ‖(N r z).det‖) ∧
      ∀ r,
        ParabolicBoundedWith
          (ricciDeTurckSchematicDiffBoundConst
            (𝕜 := 𝕜) δ (C r) (DB r) (HB r) (KM r) (KD r) (KH r) * R)
          (fun z : ℝ × X =>
            ricciDeTurckSchematicMatrix (M r z) (D r z) (Hc r z) -
              ricciDeTurckSchematicMatrix (N r z) (E r z) (Kc r z)) Kdom := by
  have hMctrl : ∀ r a b, ParabolicC0AlphaOn α (fun z => M r z a b) Kdom := by
    intro r a b
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hMlocal y hy r a b)
  have hNctrl : ∀ r a b, ParabolicC0AlphaOn α (fun z => N r z a b) Kdom := by
    intro r a b
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hNlocal y hy r a b)
  exact
    ricciDeTurckSchematicMatrix_bounded_sub_le_const_family_mul_radius_of_isCompact_det_ne_zero_of_primitive_le
      (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
      hKdom hα hMctrl hNctrl hdetM_ne hdetN_ne hDB hHB hKM hKD hKH
      hM hN hD hE hKc hKD0 hR hMdiff hDdiff hHdiff

/-- Point-dependent local product-cylinder metric controls globalize the finite-family
compact-domain linear-radius schematic RHS estimate while allowing sharper primitive Lipschitz
constants to be promoted to coarser shared constants for each family member. -/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_family_mul_radius_of_isCompact_of_local_closedCylinder_variable_of_primitive_le
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)}
    {C : κ → n → n → ℝ} {DB : κ → n → n → n → ℝ}
    {HB : κ → n → n → n → n → ℝ}
    {R : ℝ} {KM0 KD0 KM KD : κ → ℝ} {KH0 KH : κ → n → n → ℝ}
    {M N : κ → ℝ × X → Matrix n n 𝕜}
    {D E : κ → ℝ × X → n → n → n → 𝕜}
    {Hc Kc : κ → ℝ × X → n → n → n → n → 𝕜}
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (timeRadius spaceRadius : ℝ × X → ℝ)
    (htime_pos : ∀ y ∈ Kdom, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ Kdom, 0 < spaceRadius y)
    (hMlocal : ∀ y ∈ Kdom, ∀ r a b,
      ParabolicC0AlphaOn α (fun z => M r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hNlocal : ∀ y ∈ Kdom, ∀ r a b,
      ParabolicC0AlphaOn α (fun z => N r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hdetM_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → (M r z).det ≠ 0)
    (hdetN_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → (N r z).det ≠ 0)
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hKM : ∀ r, KM0 r ≤ KM r) (hKD : ∀ r, KD0 r ≤ KD r)
    (hKH : ∀ r i j, KH0 r i j ≤ KH r i j)
    (hM : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖M r z a b‖ ≤ C r a b)
    (hN : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖N r z a b‖ ≤ C r a b)
    (hD : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖D r z a b c‖ ≤
      DB r a b c)
    (hE : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖E r z a b c‖ ≤
      DB r a b c)
    (hKc : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b i j,
      ‖Kc r z a b i j‖ ≤ HB r a b i j)
    (hKD0 : ∀ r, 0 ≤ KD0 r) (hR : 0 ≤ R)
    (hMdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ‖M r z - N r z‖ ≤ KM0 r * R)
    (hDdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c,
      ‖D r z a b c - E r z a b c‖ ≤ KD0 r * R)
    (hHdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ i j,
      ‖((fun a b => Hc r z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc r z a b i j) : Matrix n n 𝕜)‖ ≤ KH0 r i j * R) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → δ ≤ ‖(M r z).det‖) ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → δ ≤ ‖(N r z).det‖) ∧
      ∀ r,
        ParabolicBoundedWith
          (ricciDeTurckSchematicDiffBoundConst
            (𝕜 := 𝕜) δ (C r) (DB r) (HB r) (KM r) (KD r) (KH r) * R)
          (fun z : ℝ × X =>
            ricciDeTurckSchematicMatrix (M r z) (D r z) (Hc r z) -
              ricciDeTurckSchematicMatrix (N r z) (E r z) (Kc r z)) Kdom := by
  have hMctrl : ∀ r a b, ParabolicC0AlphaOn α (fun z => M r z a b) Kdom := by
    intro r a b
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hKdom hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hMlocal y hy r a b)
  have hNctrl : ∀ r a b, ParabolicC0AlphaOn α (fun z => N r z a b) Kdom := by
    intro r a b
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hKdom hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hNlocal y hy r a b)
  exact
    ricciDeTurckSchematicMatrix_bounded_sub_le_const_family_mul_radius_of_isCompact_det_ne_zero_of_primitive_le
      (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
      hKdom hα hMctrl hNctrl hdetM_ne hdetN_ne hDB hHB hKM hKD hKH
      hM hN hD hE hKc hKD0 hR hMdiff hDdiff hHdiff

/-- Existential point-local product-cylinder metric controls globalize the finite-family
compact-domain linear-radius schematic RHS estimate while allowing sharper primitive Lipschitz
constants to be promoted to coarser shared constants for each family member. -/
theorem ricciDeTurckSchematicMatrix_bounded_sub_le_const_family_mul_radius_of_isCompact_of_exists_local_closedCylinder_of_primitive_le
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)}
    {C : κ → n → n → ℝ} {DB : κ → n → n → n → ℝ}
    {HB : κ → n → n → n → n → ℝ}
    {R : ℝ} {KM0 KD0 KM KD : κ → ℝ} {KH0 KH : κ → n → n → ℝ}
    {M N : κ → ℝ × X → Matrix n n 𝕜}
    {D E : κ → ℝ × X → n → n → n → 𝕜}
    {Hc Kc : κ → ℝ × X → n → n → n → n → 𝕜}
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (hlocal : ∀ y ∈ Kdom, ∃ timeRadius > 0, ∃ spaceRadius > 0,
      (∀ r a b,
        ParabolicC0AlphaOn α (fun z => M r z a b)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ r a b,
        ParabolicC0AlphaOn α (fun z => N r z a b)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))))
    (hdetM_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → (M r z).det ≠ 0)
    (hdetN_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → (N r z).det ≠ 0)
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hKM : ∀ r, KM0 r ≤ KM r) (hKD : ∀ r, KD0 r ≤ KD r)
    (hKH : ∀ r i j, KH0 r i j ≤ KH r i j)
    (hM : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖M r z a b‖ ≤ C r a b)
    (hN : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b, ‖N r z a b‖ ≤ C r a b)
    (hD : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖D r z a b c‖ ≤
      DB r a b c)
    (hE : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c, ‖E r z a b c‖ ≤
      DB r a b c)
    (hKc : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b i j,
      ‖Kc r z a b i j‖ ≤ HB r a b i j)
    (hKD0 : ∀ r, 0 ≤ KD0 r) (hR : 0 ≤ R)
    (hMdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ‖M r z - N r z‖ ≤ KM0 r * R)
    (hDdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c,
      ‖D r z a b c - E r z a b c‖ ≤ KD0 r * R)
    (hHdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ i j,
      ‖((fun a b => Hc r z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc r z a b i j) : Matrix n n 𝕜)‖ ≤ KH0 r i j * R) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → δ ≤ ‖(M r z).det‖) ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ Kdom → δ ≤ ‖(N r z).det‖) ∧
      ∀ r,
        ParabolicBoundedWith
          (ricciDeTurckSchematicDiffBoundConst
            (𝕜 := 𝕜) δ (C r) (DB r) (HB r) (KM r) (KD r) (KH r) * R)
          (fun z : ℝ × X =>
            ricciDeTurckSchematicMatrix (M r z) (D r z) (Hc r z) -
              ricciDeTurckSchematicMatrix (N r z) (E r z) (Kc r z)) Kdom := by
  have hMctrl : ∀ r a b, ParabolicC0AlphaOn α (fun z => M r z a b) Kdom := by
    intro r a b
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hKdom hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.1 r a b⟩)
  have hNctrl : ∀ r a b, ParabolicC0AlphaOn α (fun z => N r z a b) Kdom := by
    intro r a b
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hKdom hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.2 r a b⟩)
  exact
    ricciDeTurckSchematicMatrix_bounded_sub_le_const_family_mul_radius_of_isCompact_det_ne_zero_of_primitive_le
      (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
      hKdom hα hMctrl hNctrl hdetM_ne hdetN_ne hDB hHB hKM hKD hKH
      hM hN hD hE hKc hKD0 hR hMdiff hDdiff hHdiff

/-- Holder constant for the difference of two primitive-input schematic Ricci-DeTurck RHS matrix
fields, using the sum of the two individual schematic Holder constants. -/
def ricciDeTurckSchematicDiffHolderConst {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] (δ : ℝ) (MB MH : n → n → ℝ)
    (DB DH : n → n → n → ℝ) (HB HH : n → n → n → n → ℝ) : ℝ :=
  (∑ i : n, ∑ j : n,
    (matrixInvTwoIndexContractEntryHolderConst (𝕜 := 𝕜) δ MB MH HB HH i j +
      christoffelQuadraticRicciEntryHolderConst
        (fun a b c => matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ MB DB a b c)
        (fun a b c => matrixInvChristoffelEntryHolderConst (𝕜 := 𝕜) δ MB MH DB DH a b c)
        i j)) +
  (∑ i : n, ∑ j : n,
    (matrixInvTwoIndexContractEntryHolderConst (𝕜 := 𝕜) δ MB MH HB HH i j +
      christoffelQuadraticRicciEntryHolderConst
        (fun a b c => matrixInvChristoffelEntryBoundConst (𝕜 := 𝕜) δ MB DB a b c)
        (fun a b c => matrixInvChristoffelEntryHolderConst (𝕜 := 𝕜) δ MB MH DB DH a b c)
        i j))

/-- The difference of two primitive-input schematic Ricci-DeTurck RHS matrix fields has parabolic
`C^{0,α}` control: the sup constant is the primitive-input bounded-difference constant and the
Holder constant is the sum of the two standalone schematic Holder constants. -/
theorem ricciDeTurckSchematicMatrix_sub_with {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {δ : ℝ}
    {MB MH : n → n → ℝ} {DB DH : n → n → n → ℝ}
    {HB HH : n → n → n → n → ℝ} {ηM ηD : ℝ} {ηH : n → n → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    {Hc Kc : ℝ × X → n → n → n → n → 𝕜}
    (hMH : ∀ a b, 0 ≤ MH a b)
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hDH : ∀ a b c, 0 ≤ DH a b c)
    (hHB : ∀ a b i j, 0 ≤ HB a b i j) (hHH : ∀ a b i j, 0 ≤ HH a b i j)
    (hM : ∀ a b, ParabolicC0AlphaWith (MB a b) (MH a b) α (fun z => M z a b) s)
    (hN : ∀ a b, ParabolicC0AlphaWith (MB a b) (MH a b) α (fun z => N z a b) s)
    (hD : ∀ a b c, ParabolicC0AlphaWith (DB a b c) (DH a b c) α
      (fun z => D z a b c) s)
    (hE : ∀ a b c, ParabolicC0AlphaWith (DB a b c) (DH a b c) α
      (fun z => E z a b c) s)
    (hHc : ∀ a b i j, ParabolicC0AlphaWith (HB a b i j) (HH a b i j) α
      (fun z => Hc z a b i j) s)
    (hKc : ∀ a b i j, ParabolicC0AlphaWith (HB a b i j) (HH a b i j) α
      (fun z => Kc z a b i j) s)
    (hηD : 0 ≤ ηD)
    (hMdiff : ∀ ⦃z : ℝ × X⦄, z ∈ s → ‖M z - N z‖ ≤ ηM)
    (hDdiff : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ a b c,
      ‖D z a b c - E z a b c‖ ≤ ηD)
    (hHdiff : ∀ ⦃z : ℝ × X⦄, z ∈ s → ∀ i j,
      ‖((fun a b => Hc z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc z a b i j) : Matrix n n 𝕜)‖ ≤ ηH i j)
    (hδpos : 0 < δ)
    (hdetM : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (hdetN : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(N z).det‖) :
    ParabolicC0AlphaWith
      (ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ MB DB HB ηM ηD ηH)
      (ricciDeTurckSchematicDiffHolderConst (𝕜 := 𝕜) δ MB MH DB DH HB HH)
      α
      (fun z : ℝ × X =>
        ricciDeTurckSchematicMatrix (M z) (D z) (Hc z) -
          ricciDeTurckSchematicMatrix (N z) (E z) (Kc z)) s := by
  have hbounded :
      ParabolicBoundedWith
        (ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ MB DB HB ηM ηD ηH)
        (fun z : ℝ × X =>
          ricciDeTurckSchematicMatrix (M z) (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (E z) (Kc z)) s := by
    exact ricciDeTurckSchematicMatrix_bounded_sub_le_const
      (s := s) (δ := δ) (C := MB) (DB := DB) (HB := HB)
      (ηM := ηM) (ηD := ηD) (ηH := ηH)
      hDB hHB
      (fun z hz a b => (hM a b).bounded hz)
      (fun z hz a b => (hN a b).bounded hz)
      (fun z hz a b c => (hD a b c).bounded hz)
      (fun z hz a b c => (hE a b c).bounded hz)
      (fun z hz a b i j => (hKc a b i j).bounded hz)
      hηD hMdiff hDdiff hHdiff hδpos hdetM hdetN
  have hMDH := ricciDeTurck_schematic_with
    (M := M) (D := D) (H := Hc) hMH hDB hDH hHB hHH hM hD hHc hδpos hdetM
  have hNEK := ricciDeTurck_schematic_with
    (M := N) (D := E) (H := Kc) hMH hDB hDH hHB hHH hN hE hKc hδpos hdetN
  exact ⟨hbounded, by
    have hraw := hMDH.holder.sub hNEK.holder
    change @ParabolicHolderWith X (n → n → 𝕜) _ Pi.normedAddCommGroup _ _ _ _
    intro p hp q hq
    unfold ricciDeTurckSchematicMatrix
    have hholder := hraw hp hq
    simp only [Matrix.norm_def, Pi.norm_def, Pi.nnnorm_def, Matrix.sub_apply, Pi.sub_apply,
      ricciDeTurckSchematicDiffHolderConst] at hholder ⊢
    exact hholder⟩

/-- Compact-domain version of `ricciDeTurckSchematicMatrix_sub_with`: pointwise nonvanishing of
both metric determinants supplies one common determinant lower bound. -/
theorem ricciDeTurckSchematicMatrix_sub_with_of_isCompact_det_ne_zero
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)}
    {MB MH : n → n → ℝ} {DB DH : n → n → n → ℝ}
    {HB HH : n → n → n → n → ℝ} {ηM ηD : ℝ} {ηH : n → n → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    {Hc Kc : ℝ × X → n → n → n → n → 𝕜}
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (hMB : ∀ a b, 0 ≤ MB a b) (hMH : ∀ a b, 0 ≤ MH a b)
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hDH : ∀ a b c, 0 ≤ DH a b c)
    (hHB : ∀ a b i j, 0 ≤ HB a b i j) (hHH : ∀ a b i j, 0 ≤ HH a b i j)
    (hM : ∀ a b, ParabolicC0AlphaWith (MB a b) (MH a b) α (fun z => M z a b) Kdom)
    (hN : ∀ a b, ParabolicC0AlphaWith (MB a b) (MH a b) α (fun z => N z a b) Kdom)
    (hD : ∀ a b c, ParabolicC0AlphaWith (DB a b c) (DH a b c) α
      (fun z => D z a b c) Kdom)
    (hE : ∀ a b c, ParabolicC0AlphaWith (DB a b c) (DH a b c) α
      (fun z => E z a b c) Kdom)
    (hHc : ∀ a b i j, ParabolicC0AlphaWith (HB a b i j) (HH a b i j) α
      (fun z => Hc z a b i j) Kdom)
    (hKc : ∀ a b i j, ParabolicC0AlphaWith (HB a b i j) (HH a b i j) α
      (fun z => Kc z a b i j) Kdom)
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (N z).det ≠ 0)
    (hηD : 0 ≤ ηD)
    (hMdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ‖M z - N z‖ ≤ ηM)
    (hDdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c,
      ‖D z a b c - E z a b c‖ ≤ ηD)
    (hHdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ i j,
      ‖((fun a b => Hc z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc z a b i j) : Matrix n n 𝕜)‖ ≤ ηH i j) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ MB DB HB ηM ηD ηH)
        (ricciDeTurckSchematicDiffHolderConst (𝕜 := 𝕜) δ MB MH DB DH HB HH)
        α
        (fun z : ℝ × X =>
          ricciDeTurckSchematicMatrix (M z) (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (E z) (Kc z)) Kdom := by
  have hMctrl : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) Kdom := by
    intro a b
    exact ⟨MB a b, hMB a b, MH a b, hMH a b, hM a b⟩
  have hNctrl : ∀ a b, ParabolicC0AlphaOn α (fun z => N z a b) Kdom := by
    intro a b
    exact ⟨MB a b, hMB a b, MH a b, hMH a b, hN a b⟩
  rcases matrix_det_pair_exists_pos_norm_lower_bound_of_isCompact
      (K := Kdom) (M := M) (N := N) hKdom hα hMctrl hNctrl hdetM_ne hdetN_ne with
    ⟨δ, hδpos, hdetM, hdetN⟩
  exact ⟨δ, hδpos, ricciDeTurckSchematicMatrix_sub_with
    (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
    hMH hDB hDH hHB hHH hM hN hD hE hHc hKc hηD hMdiff hDdiff hHdiff
    hδpos hdetM hdetN⟩

/-- The Holder constant produced by patching fixed local `C^{0,α}` constants over a finite
variable-radius product parabolic-cylinder cover. -/
def parabolicCylinderCoverHolderConst (S : Finset (ℝ × X))
    (timeRadius spaceRadius : ℝ × X → ℝ) (α B H : ℝ) : ℝ :=
  ∑ y ∈ S, max H (2 * B / (min (Real.sqrt (timeRadius y)) (spaceRadius y)) ^ α)

theorem parabolicCylinderCoverHolderConst_nonneg
    (S : Finset (ℝ × X)) (timeRadius spaceRadius : ℝ × X → ℝ)
    {α B H : ℝ} (hH : 0 ≤ H) :
    0 ≤ parabolicCylinderCoverHolderConst S timeRadius spaceRadius α B H := by
  dsimp [parabolicCylinderCoverHolderConst]
  exact Finset.sum_nonneg fun _ _ => hH.trans (le_max_left _ _)

/-- Local finite product-cylinder quantitative primitive estimates globalize the compact-domain
schematic Ricci-DeTurck RHS difference estimate.  The displayed Holder constants are exactly the
finite-cover patching constants coming from `ParabolicC0AlphaWith`. -/
theorem ricciDeTurckSchematicMatrix_sub_with_of_finset_parabolicCylinder_cover_closedCylinder_variable
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)}
    {MB MH : n → n → ℝ} {DB DH : n → n → n → ℝ}
    {HB HH : n → n → n → n → ℝ} {ηM ηD : ℝ} {ηH : n → n → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    {Hc Kc : ℝ × X → n → n → n → n → 𝕜}
    (S : Finset (ℝ × X)) (timeRadius spaceRadius : ℝ × X → ℝ)
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (htime_pos : ∀ y ∈ S, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ S, 0 < spaceRadius y)
    (hcover : Kdom ⊆ ⋃ y ∈ S, parabolicCylinder y (timeRadius y) (spaceRadius y))
    (hMB : ∀ a b, 0 ≤ MB a b) (hMH : ∀ a b, 0 ≤ MH a b)
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hDH : ∀ a b c, 0 ≤ DH a b c)
    (hHB : ∀ a b i j, 0 ≤ HB a b i j) (hHH : ∀ a b i j, 0 ≤ HH a b i j)
    (hMlocal : ∀ y ∈ S, ∀ a b,
      ParabolicC0AlphaWith (MB a b) (MH a b) α (fun z => M z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hNlocal : ∀ y ∈ S, ∀ a b,
      ParabolicC0AlphaWith (MB a b) (MH a b) α (fun z => N z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hDlocal : ∀ y ∈ S, ∀ a b c,
      ParabolicC0AlphaWith (DB a b c) (DH a b c) α (fun z => D z a b c)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hElocal : ∀ y ∈ S, ∀ a b c,
      ParabolicC0AlphaWith (DB a b c) (DH a b c) α (fun z => E z a b c)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hHclocal : ∀ y ∈ S, ∀ a b i j,
      ParabolicC0AlphaWith (HB a b i j) (HH a b i j) α
        (fun z => Hc z a b i j)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hKclocal : ∀ y ∈ S, ∀ a b i j,
      ParabolicC0AlphaWith (HB a b i j) (HH a b i j) α
        (fun z => Kc z a b i j)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (N z).det ≠ 0)
    (hηD : 0 ≤ ηD)
    (hMdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ‖M z - N z‖ ≤ ηM)
    (hDdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c,
      ‖D z a b c - E z a b c‖ ≤ ηD)
    (hHdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ i j,
      ‖((fun a b => Hc z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc z a b i j) : Matrix n n 𝕜)‖ ≤ ηH i j) :
    ∃ δ > 0,
      ParabolicC0AlphaWith
        (ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ MB DB HB ηM ηD ηH)
        (ricciDeTurckSchematicDiffHolderConst (𝕜 := 𝕜) δ MB
          (fun a b => parabolicCylinderCoverHolderConst S timeRadius spaceRadius α
            (MB a b) (MH a b))
          DB
          (fun a b c => parabolicCylinderCoverHolderConst S timeRadius spaceRadius α
            (DB a b c) (DH a b c))
          HB
          (fun a b i j => parabolicCylinderCoverHolderConst S timeRadius spaceRadius α
            (HB a b i j) (HH a b i j)))
        α
        (fun z : ℝ × X =>
          ricciDeTurckSchematicMatrix (M z) (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (E z) (Kc z)) Kdom := by
  let MHg : n → n → ℝ := fun a b =>
    parabolicCylinderCoverHolderConst S timeRadius spaceRadius α (MB a b) (MH a b)
  let DHg : n → n → n → ℝ := fun a b c =>
    parabolicCylinderCoverHolderConst S timeRadius spaceRadius α (DB a b c) (DH a b c)
  let HHg : n → n → n → n → ℝ := fun a b i j =>
    parabolicCylinderCoverHolderConst S timeRadius spaceRadius α (HB a b i j) (HH a b i j)
  have hMHg : ∀ a b, 0 ≤ MHg a b := by
    intro a b
    exact parabolicCylinderCoverHolderConst_nonneg S timeRadius spaceRadius (hMH a b)
  have hDHg : ∀ a b c, 0 ≤ DHg a b c := by
    intro a b c
    exact parabolicCylinderCoverHolderConst_nonneg S timeRadius spaceRadius (hDH a b c)
  have hHHg : ∀ a b i j, 0 ≤ HHg a b i j := by
    intro a b i j
    exact parabolicCylinderCoverHolderConst_nonneg S timeRadius spaceRadius (hHH a b i j)
  have hM : ∀ a b, ParabolicC0AlphaWith (MB a b) (MHg a b) α
      (fun z => M z a b) Kdom := by
    intro a b
    exact ParabolicC0AlphaWith.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hMlocal y hy a b)
  have hN : ∀ a b, ParabolicC0AlphaWith (MB a b) (MHg a b) α
      (fun z => N z a b) Kdom := by
    intro a b
    exact ParabolicC0AlphaWith.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hNlocal y hy a b)
  have hD : ∀ a b c, ParabolicC0AlphaWith (DB a b c) (DHg a b c) α
      (fun z => D z a b c) Kdom := by
    intro a b c
    exact ParabolicC0AlphaWith.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hDlocal y hy a b c)
  have hE : ∀ a b c, ParabolicC0AlphaWith (DB a b c) (DHg a b c) α
      (fun z => E z a b c) Kdom := by
    intro a b c
    exact ParabolicC0AlphaWith.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hElocal y hy a b c)
  have hHc : ∀ a b i j, ParabolicC0AlphaWith (HB a b i j) (HHg a b i j) α
      (fun z => Hc z a b i j) Kdom := by
    intro a b i j
    exact ParabolicC0AlphaWith.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hHclocal y hy a b i j)
  have hKc : ∀ a b i j, ParabolicC0AlphaWith (HB a b i j) (HHg a b i j) α
      (fun z => Kc z a b i j) Kdom := by
    intro a b i j
    exact ParabolicC0AlphaWith.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hKclocal y hy a b i j)
  simpa [MHg, DHg, HHg] using
    ricciDeTurckSchematicMatrix_sub_with_of_isCompact_det_ne_zero
      (Kdom := Kdom) (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
      hKdom hα hMB hMHg hDB hDHg hHB hHHg hM hN hD hE hHc hKc
      hdetM_ne hdetN_ne hηD hMdiff hDdiff hHdiff

/-- Point-dependent local product-cylinder quantitative primitive estimates globalize the
compact-domain schematic Ricci-DeTurck RHS difference estimate.  Compactness chooses the finite
subcover and hence the patched Holder constants. -/
theorem ricciDeTurckSchematicMatrix_sub_with_of_isCompact_of_local_closedCylinder_variable
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)}
    {MB MH : n → n → ℝ} {DB DH : n → n → n → ℝ}
    {HB HH : n → n → n → n → ℝ} {ηM ηD : ℝ} {ηH : n → n → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    {Hc Kc : ℝ × X → n → n → n → n → 𝕜}
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (timeRadius spaceRadius : ℝ × X → ℝ)
    (htime_pos : ∀ y ∈ Kdom, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ Kdom, 0 < spaceRadius y)
    (hMB : ∀ a b, 0 ≤ MB a b) (hMH : ∀ a b, 0 ≤ MH a b)
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hDH : ∀ a b c, 0 ≤ DH a b c)
    (hHB : ∀ a b i j, 0 ≤ HB a b i j) (hHH : ∀ a b i j, 0 ≤ HH a b i j)
    (hMlocal : ∀ y ∈ Kdom, ∀ a b,
      ParabolicC0AlphaWith (MB a b) (MH a b) α (fun z => M z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hNlocal : ∀ y ∈ Kdom, ∀ a b,
      ParabolicC0AlphaWith (MB a b) (MH a b) α (fun z => N z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hDlocal : ∀ y ∈ Kdom, ∀ a b c,
      ParabolicC0AlphaWith (DB a b c) (DH a b c) α (fun z => D z a b c)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hElocal : ∀ y ∈ Kdom, ∀ a b c,
      ParabolicC0AlphaWith (DB a b c) (DH a b c) α (fun z => E z a b c)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hHclocal : ∀ y ∈ Kdom, ∀ a b i j,
      ParabolicC0AlphaWith (HB a b i j) (HH a b i j) α
        (fun z => Hc z a b i j)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hKclocal : ∀ y ∈ Kdom, ∀ a b i j,
      ParabolicC0AlphaWith (HB a b i j) (HH a b i j) α
        (fun z => Kc z a b i j)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (N z).det ≠ 0)
    (hηD : 0 ≤ ηD)
    (hMdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ‖M z - N z‖ ≤ ηM)
    (hDdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c,
      ‖D z a b c - E z a b c‖ ≤ ηD)
    (hHdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ i j,
      ‖((fun a b => Hc z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc z a b i j) : Matrix n n 𝕜)‖ ≤ ηH i j) :
    ∃ δ > 0, ∃ MHg : n → n → ℝ, ∃ DHg : n → n → n → ℝ,
      ∃ HHg : n → n → n → n → ℝ,
      (∀ a b, 0 ≤ MHg a b) ∧
      (∀ a b c, 0 ≤ DHg a b c) ∧
      (∀ a b i j, 0 ≤ HHg a b i j) ∧
      ParabolicC0AlphaWith
        (ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ MB DB HB ηM ηD ηH)
        (ricciDeTurckSchematicDiffHolderConst (𝕜 := 𝕜) δ MB MHg DB DHg HB HHg)
        α
        (fun z : ℝ × X =>
          ricciDeTurckSchematicMatrix (M z) (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (E z) (Kc z)) Kdom := by
  rcases hKdom.elim_nhds_subcover
      (fun y => parabolicCylinder y (timeRadius y) (spaceRadius y))
      (fun y hy => parabolicCylinder.mem_nhds (p := y) (timeRadius := timeRadius y)
        (spaceRadius := spaceRadius y) (htime_pos y hy) (hspace_pos y hy)) with
    ⟨S, hSK, hcover⟩
  let MHg : n → n → ℝ := fun a b =>
    parabolicCylinderCoverHolderConst S timeRadius spaceRadius α (MB a b) (MH a b)
  let DHg : n → n → n → ℝ := fun a b c =>
    parabolicCylinderCoverHolderConst S timeRadius spaceRadius α (DB a b c) (DH a b c)
  let HHg : n → n → n → n → ℝ := fun a b i j =>
    parabolicCylinderCoverHolderConst S timeRadius spaceRadius α (HB a b i j) (HH a b i j)
  have hMHg : ∀ a b, 0 ≤ MHg a b := by
    intro a b
    exact parabolicCylinderCoverHolderConst_nonneg S timeRadius spaceRadius (hMH a b)
  have hDHg : ∀ a b c, 0 ≤ DHg a b c := by
    intro a b c
    exact parabolicCylinderCoverHolderConst_nonneg S timeRadius spaceRadius (hDH a b c)
  have hHHg : ∀ a b i j, 0 ≤ HHg a b i j := by
    intro a b i j
    exact parabolicCylinderCoverHolderConst_nonneg S timeRadius spaceRadius (hHH a b i j)
  rcases
    ricciDeTurckSchematicMatrix_sub_with_of_finset_parabolicCylinder_cover_closedCylinder_variable
      (S := S) (timeRadius := timeRadius) (spaceRadius := spaceRadius)
      (Kdom := Kdom) (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
      hKdom hα
      (fun y hy => htime_pos y (hSK y hy))
      (fun y hy => hspace_pos y (hSK y hy)) hcover
      hMB hMH hDB hDH hHB hHH
      (fun y hy => hMlocal y (hSK y hy))
      (fun y hy => hNlocal y (hSK y hy))
      (fun y hy => hDlocal y (hSK y hy))
      (fun y hy => hElocal y (hSK y hy))
      (fun y hy => hHclocal y (hSK y hy))
      (fun y hy => hKclocal y (hSK y hy))
      hdetM_ne hdetN_ne hηD hMdiff hDdiff hHdiff with
    ⟨δ, hδpos, hwith⟩
  refine ⟨δ, hδpos, MHg, DHg, HHg, hMHg, hDHg, hHHg, ?_⟩
  simpa [MHg, DHg, HHg] using hwith

/-- Existential point-local product-cylinder quantitative primitive estimates globalize the
compact-domain schematic Ricci-DeTurck RHS difference estimate. -/
theorem ricciDeTurckSchematicMatrix_sub_with_of_isCompact_of_exists_local_closedCylinder
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {Kdom : Set (ℝ × X)}
    {MB MH : n → n → ℝ} {DB DH : n → n → n → ℝ}
    {HB HH : n → n → n → n → ℝ} {ηM ηD : ℝ} {ηH : n → n → ℝ}
    {M N : ℝ × X → Matrix n n 𝕜}
    {D E : ℝ × X → n → n → n → 𝕜}
    {Hc Kc : ℝ × X → n → n → n → n → 𝕜}
    (hKdom : IsCompact Kdom) (hα : 0 < α)
    (hMB : ∀ a b, 0 ≤ MB a b) (hMH : ∀ a b, 0 ≤ MH a b)
    (hDB : ∀ a b c, 0 ≤ DB a b c) (hDH : ∀ a b c, 0 ≤ DH a b c)
    (hHB : ∀ a b i j, 0 ≤ HB a b i j) (hHH : ∀ a b i j, 0 ≤ HH a b i j)
    (hlocal : ∀ y ∈ Kdom, ∃ timeRadius > 0, ∃ spaceRadius > 0,
      (∀ a b,
        ParabolicC0AlphaWith (MB a b) (MH a b) α (fun z => M z a b)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ a b,
        ParabolicC0AlphaWith (MB a b) (MH a b) α (fun z => N z a b)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ a b c,
        ParabolicC0AlphaWith (DB a b c) (DH a b c) α (fun z => D z a b c)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ a b c,
        ParabolicC0AlphaWith (DB a b c) (DH a b c) α (fun z => E z a b c)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ a b i j,
        ParabolicC0AlphaWith (HB a b i j) (HH a b i j) α
          (fun z => Hc z a b i j)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ a b i j,
        ParabolicC0AlphaWith (HB a b i j) (HH a b i j) α
          (fun z => Kc z a b i j)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))))
    (hdetM_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (M z).det ≠ 0)
    (hdetN_ne : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → (N z).det ≠ 0)
    (hηD : 0 ≤ ηD)
    (hMdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ‖M z - N z‖ ≤ ηM)
    (hDdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ a b c,
      ‖D z a b c - E z a b c‖ ≤ ηD)
    (hHdiff : ∀ ⦃z : ℝ × X⦄, z ∈ Kdom → ∀ i j,
      ‖((fun a b => Hc z a b i j) : Matrix n n 𝕜) -
        ((fun a b => Kc z a b i j) : Matrix n n 𝕜)‖ ≤ ηH i j) :
    ∃ δ > 0, ∃ MHg : n → n → ℝ, ∃ DHg : n → n → n → ℝ,
      ∃ HHg : n → n → n → n → ℝ,
      (∀ a b, 0 ≤ MHg a b) ∧
      (∀ a b c, 0 ≤ DHg a b c) ∧
      (∀ a b i j, 0 ≤ HHg a b i j) ∧
      ParabolicC0AlphaWith
        (ricciDeTurckSchematicDiffBoundConst (𝕜 := 𝕜) δ MB DB HB ηM ηD ηH)
        (ricciDeTurckSchematicDiffHolderConst (𝕜 := 𝕜) δ MB MHg DB DHg HB HHg)
        α
        (fun z : ℝ × X =>
          ricciDeTurckSchematicMatrix (M z) (D z) (Hc z) -
            ricciDeTurckSchematicMatrix (N z) (E z) (Kc z)) Kdom := by
  classical
  let timeRadius : ℝ × X → ℝ := fun y =>
    if hy : y ∈ Kdom then Classical.choose (hlocal y hy) else 1
  let spaceRadius : ℝ × X → ℝ := fun y =>
    if hy : y ∈ Kdom then Classical.choose (Classical.choose_spec (hlocal y hy)).2 else 1
  have htime_pos : ∀ y ∈ Kdom, 0 < timeRadius y := by
    intro y hy
    dsimp [timeRadius]
    rw [dif_pos hy]
    exact (Classical.choose_spec (hlocal y hy)).1
  have hspace_pos : ∀ y ∈ Kdom, 0 < spaceRadius y := by
    intro y hy
    dsimp [spaceRadius]
    rw [dif_pos hy]
    exact (Classical.choose_spec (Classical.choose_spec (hlocal y hy)).2).1
  have hMlocal : ∀ y ∈ Kdom, ∀ a b,
      ParabolicC0AlphaWith (MB a b) (MH a b) α (fun z => M z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)) := by
    intro y hy a b
    dsimp [timeRadius, spaceRadius]
    rw [dif_pos hy, dif_pos hy]
    exact (Classical.choose_spec (Classical.choose_spec (hlocal y hy)).2).2.1 a b
  have hNlocal : ∀ y ∈ Kdom, ∀ a b,
      ParabolicC0AlphaWith (MB a b) (MH a b) α (fun z => N z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)) := by
    intro y hy a b
    dsimp [timeRadius, spaceRadius]
    rw [dif_pos hy, dif_pos hy]
    exact (Classical.choose_spec (Classical.choose_spec (hlocal y hy)).2).2.2.1 a b
  have hDlocal : ∀ y ∈ Kdom, ∀ a b c,
      ParabolicC0AlphaWith (DB a b c) (DH a b c) α (fun z => D z a b c)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)) := by
    intro y hy a b c
    dsimp [timeRadius, spaceRadius]
    rw [dif_pos hy, dif_pos hy]
    exact (Classical.choose_spec (Classical.choose_spec (hlocal y hy)).2).2.2.2.1 a b c
  have hElocal : ∀ y ∈ Kdom, ∀ a b c,
      ParabolicC0AlphaWith (DB a b c) (DH a b c) α (fun z => E z a b c)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)) := by
    intro y hy a b c
    dsimp [timeRadius, spaceRadius]
    rw [dif_pos hy, dif_pos hy]
    exact (Classical.choose_spec (Classical.choose_spec (hlocal y hy)).2).2.2.2.2.1 a b c
  have hHclocal : ∀ y ∈ Kdom, ∀ a b i j,
      ParabolicC0AlphaWith (HB a b i j) (HH a b i j) α
        (fun z => Hc z a b i j)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)) := by
    intro y hy a b i j
    dsimp [timeRadius, spaceRadius]
    rw [dif_pos hy, dif_pos hy]
    exact (Classical.choose_spec (Classical.choose_spec (hlocal y hy)).2).2.2.2.2.2.1 a b i j
  have hKclocal : ∀ y ∈ Kdom, ∀ a b i j,
      ParabolicC0AlphaWith (HB a b i j) (HH a b i j) α
        (fun z => Kc z a b i j)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)) := by
    intro y hy a b i j
    dsimp [timeRadius, spaceRadius]
    rw [dif_pos hy, dif_pos hy]
    exact (Classical.choose_spec (Classical.choose_spec (hlocal y hy)).2).2.2.2.2.2.2 a b i j
  exact ricciDeTurckSchematicMatrix_sub_with_of_isCompact_of_local_closedCylinder_variable
    (Kdom := Kdom) (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
    hKdom hα timeRadius spaceRadius htime_pos hspace_pos
    hMB hMH hDB hDH hHB hHH
    hMlocal hNlocal hDlocal hElocal hHclocal hKclocal
    hdetM_ne hdetN_ne hηD hMdiff hDdiff hHdiff

/-- Schematic local Ricci-DeTurck coordinate right-hand sides preserve parabolic `C^{0,α}`
control from entrywise control of metric coefficients, first derivative coefficients, and second
derivative coefficients, assuming the metric determinant is bounded away from zero.  The formula
packages the principal contraction `g^{ab} H_{abij}` together with the standard quadratic
Christoffel contraction. -/
theorem ricciDeTurck_schematic_entry {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {M : ℝ × X → Matrix n n 𝕜}
    {D : ℝ × X → n → n → n → 𝕜} {H : ℝ × X → n → n → n → n → 𝕜}
    (hM : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) s)
    (hD : ∀ a b c, ParabolicC0AlphaOn α (fun z => D z a b c) s)
    (hH : ∀ a b i j, ParabolicC0AlphaOn α (fun z => H z a b i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖)
    (i j : n) :
    ParabolicC0AlphaOn α
      (fun z =>
        let Γ : n → n → n → 𝕜 := fun a b c =>
          (2 : 𝕜)⁻¹ *
            ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) a l *
              (D z b c l + D z c b l - D z l b c)
        (∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * H z a b i j) +
          ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
            (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) s := by
  let Γ : ℝ × X → n → n → n → 𝕜 := fun z a b c =>
    (2 : 𝕜)⁻¹ *
      ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) a l *
        (D z b c l + D z c b l - D z l b c)
  have hΓ : ∀ a b c, ParabolicC0AlphaOn α (fun z => Γ z a b c) s := by
    intro a b c
    exact matrix_inv_christoffel_entry (M := M) (D := D) hM hD hδpos hdet a b c
  have hprincipal :
      ParabolicC0AlphaOn α
        (fun z => ∑ a : n, ∑ b : n,
          ((M z)⁻¹ : Matrix n n 𝕜) a b * H z a b i j) s :=
    matrix_inv_two_index_contract_entry hM hH hδpos hdet i j
  have hquadratic :
      ParabolicC0AlphaOn α
        (fun z =>
          (∑ a : n, ∑ b : n, Γ z a i j * Γ z b a b) -
            (∑ a : n, ∑ b : n, Γ z a i b * Γ z b a j)) s :=
    christoffel_quadratic_ricci_entry hΓ i j
  simpa [Γ] using hprincipal.add hquadratic

/-- Schematic local Ricci-DeTurck coordinate right-hand sides package as a matrix-valued
parabolic `C^{0,α}` function from entrywise control, under a determinant lower bound. -/
theorem ricciDeTurck_schematic {n 𝕜 : Type*} [Fintype n] [DecidableEq n]
    [NormedField 𝕜] {δ : ℝ} {M : ℝ × X → Matrix n n 𝕜}
    {D : ℝ × X → n → n → n → 𝕜} {H : ℝ × X → n → n → n → n → 𝕜}
    (hM : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) s)
    (hD : ∀ a b c, ParabolicC0AlphaOn α (fun z => D z a b c) s)
    (hH : ∀ a b i j, ParabolicC0AlphaOn α (fun z => H z a b i j) s)
    (hδpos : 0 < δ) (hdet : ∀ ⦃z : ℝ × X⦄, z ∈ s → δ ≤ ‖(M z).det‖) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × X =>
        (fun i j =>
          let Γ : n → n → n → 𝕜 := fun a b c =>
            (2 : 𝕜)⁻¹ *
              ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) a l *
                (D z b c l + D z c b l - D z l b c)
          (∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * H z a b i j) +
            ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
              (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) :
          Matrix n n 𝕜)) s :=
  matrix_of_entries fun i j =>
    ricciDeTurck_schematic_entry (M := M) (D := D) (H := H)
      hM hD hH hδpos hdet i j

/-- Compact-domain version of `ricciDeTurck_schematic_entry`: pointwise nonvanishing of the
metric determinant supplies the determinant lower bound. -/
theorem ricciDeTurck_schematic_entry_of_isCompact_det_ne_zero {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)} {M : ℝ × X → Matrix n n 𝕜}
    {D : ℝ × X → n → n → n → 𝕜} {H : ℝ × X → n → n → n → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hM : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) K)
    (hD : ∀ a b c, ParabolicC0AlphaOn α (fun z => D z a b c) K)
    (hH : ∀ a b i j, ParabolicC0AlphaOn α (fun z => H z a b i j) K)
    (hdet_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0) (i j : n) :
    ParabolicC0AlphaOn α
      (fun z =>
        let Γ : n → n → n → 𝕜 := fun a b c =>
          (2 : 𝕜)⁻¹ *
            ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) a l *
              (D z b c l + D z c b l - D z l b c)
        (∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * H z a b i j) +
          ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
            (∑ a : n, ∑ b : n, Γ a i b * Γ b a j))) K := by
  rcases matrix_det_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hM hdet_ne with
    ⟨δ, hδpos, hdet⟩
  exact ricciDeTurck_schematic_entry (M := M) (D := D) (H := H)
    hM hD hH hδpos hdet i j

/-- Compact-domain matrix-valued schematic Ricci-DeTurck RHS closure from entrywise control and
pointwise nonvanishing determinant. -/
theorem ricciDeTurck_schematic_of_isCompact_det_ne_zero {n 𝕜 : Type*} [Fintype n]
    [DecidableEq n] [NormedField 𝕜] {K : Set (ℝ × X)} {M : ℝ × X → Matrix n n 𝕜}
    {D : ℝ × X → n → n → n → 𝕜} {H : ℝ × X → n → n → n → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hM : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) K)
    (hD : ∀ a b c, ParabolicC0AlphaOn α (fun z => D z a b c) K)
    (hH : ∀ a b i j, ParabolicC0AlphaOn α (fun z => H z a b i j) K)
    (hdet_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × X =>
        (fun i j =>
          let Γ : n → n → n → 𝕜 := fun a b c =>
            (2 : 𝕜)⁻¹ *
              ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) a l *
                (D z b c l + D z c b l - D z l b c)
          (∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * H z a b i j) +
            ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
              (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) :
          Matrix n n 𝕜)) K := by
  rcases matrix_det_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hM hdet_ne with
    ⟨δ, hδpos, hdet⟩
  exact ricciDeTurck_schematic (M := M) (D := D) (H := H)
    hM hD hH hδpos hdet

/-- Local finite product-cylinder primitive estimates globalize the compact-domain schematic
Ricci-DeTurck RHS closure.  This is the chartwise-local form used before passing to a compact
determinant lower bound. -/
theorem ricciDeTurck_schematic_of_finset_parabolicCylinder_cover_closedCylinder_variable
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {K : Set (ℝ × X)} {M : ℝ × X → Matrix n n 𝕜}
    {D : ℝ × X → n → n → n → 𝕜} {H : ℝ × X → n → n → n → n → 𝕜}
    (N : Finset (ℝ × X)) (timeRadius spaceRadius : ℝ × X → ℝ)
    (hK : IsCompact K) (hα : 0 < α)
    (htime_pos : ∀ y ∈ N, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ N, 0 < spaceRadius y)
    (hcover : K ⊆ ⋃ y ∈ N, parabolicCylinder y (timeRadius y) (spaceRadius y))
    (hMlocal : ∀ y ∈ N, ∀ a b,
      ParabolicC0AlphaOn α (fun z => M z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hDlocal : ∀ y ∈ N, ∀ a b c,
      ParabolicC0AlphaOn α (fun z => D z a b c)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hHlocal : ∀ y ∈ N, ∀ a b i j,
      ParabolicC0AlphaOn α (fun z => H z a b i j)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hdet_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × X =>
        (fun i j =>
          let Γ : n → n → n → 𝕜 := fun a b c =>
            (2 : 𝕜)⁻¹ *
              ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) a l *
                (D z b c l + D z c b l - D z l b c)
          (∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * H z a b i j) +
            ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
              (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) :
          Matrix n n 𝕜)) K := by
  have hM : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) K := by
    intro a b
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      N timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hMlocal y hy a b)
  have hD : ∀ a b c, ParabolicC0AlphaOn α (fun z => D z a b c) K := by
    intro a b c
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      N timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hDlocal y hy a b c)
  have hH : ∀ a b i j, ParabolicC0AlphaOn α (fun z => H z a b i j) K := by
    intro a b i j
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      N timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hHlocal y hy a b i j)
  exact ricciDeTurck_schematic_of_isCompact_det_ne_zero
    (M := M) (D := D) (H := H) hK hα hM hD hH hdet_ne

/-- Point-dependent local product-cylinder primitive estimates globalize the compact-domain
schematic Ricci-DeTurck RHS closure.  Compactness chooses the finite subcover internally. -/
theorem ricciDeTurck_schematic_of_isCompact_of_local_closedCylinder_variable
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {K : Set (ℝ × X)} {M : ℝ × X → Matrix n n 𝕜}
    {D : ℝ × X → n → n → n → 𝕜} {H : ℝ × X → n → n → n → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (timeRadius spaceRadius : ℝ × X → ℝ)
    (htime_pos : ∀ y ∈ K, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ K, 0 < spaceRadius y)
    (hMlocal : ∀ y ∈ K, ∀ a b,
      ParabolicC0AlphaOn α (fun z => M z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hDlocal : ∀ y ∈ K, ∀ a b c,
      ParabolicC0AlphaOn α (fun z => D z a b c)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hHlocal : ∀ y ∈ K, ∀ a b i j,
      ParabolicC0AlphaOn α (fun z => H z a b i j)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hdet_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × X =>
        (fun i j =>
          let Γ : n → n → n → 𝕜 := fun a b c =>
            (2 : 𝕜)⁻¹ *
              ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) a l *
                (D z b c l + D z c b l - D z l b c)
          (∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * H z a b i j) +
            ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
              (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) :
          Matrix n n 𝕜)) K := by
  have hM : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) K := by
    intro a b
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hK hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hMlocal y hy a b)
  have hD : ∀ a b c, ParabolicC0AlphaOn α (fun z => D z a b c) K := by
    intro a b c
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hK hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hDlocal y hy a b c)
  have hH : ∀ a b i j, ParabolicC0AlphaOn α (fun z => H z a b i j) K := by
    intro a b i j
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hK hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hHlocal y hy a b i j)
  exact ricciDeTurck_schematic_of_isCompact_det_ne_zero
    (M := M) (D := D) (H := H) hK hα hM hD hH hdet_ne

/-- Existential point-local product-cylinder primitive estimates globalize the compact-domain
schematic Ricci-DeTurck RHS closure.  This form lets each compact point provide its own local
cylinder radii. -/
theorem ricciDeTurck_schematic_of_isCompact_of_exists_local_closedCylinder
    {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {K : Set (ℝ × X)} {M : ℝ × X → Matrix n n 𝕜}
    {D : ℝ × X → n → n → n → 𝕜} {H : ℝ × X → n → n → n → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hlocal : ∀ y ∈ K, ∃ timeRadius > 0, ∃ spaceRadius > 0,
      (∀ a b,
        ParabolicC0AlphaOn α (fun z => M z a b)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ a b c,
        ParabolicC0AlphaOn α (fun z => D z a b c)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ a b i j,
        ParabolicC0AlphaOn α (fun z => H z a b i j)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))))
    (hdet_ne : ∀ ⦃z : ℝ × X⦄, z ∈ K → (M z).det ≠ 0) :
    ParabolicC0AlphaOn α
      (fun z : ℝ × X =>
        (fun i j =>
          let Γ : n → n → n → 𝕜 := fun a b c =>
            (2 : 𝕜)⁻¹ *
              ∑ l : n, ((M z)⁻¹ : Matrix n n 𝕜) a l *
                (D z b c l + D z c b l - D z l b c)
          (∑ a : n, ∑ b : n, ((M z)⁻¹ : Matrix n n 𝕜) a b * H z a b i j) +
            ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
              (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) :
          Matrix n n 𝕜)) K := by
  have hM : ∀ a b, ParabolicC0AlphaOn α (fun z => M z a b) K := by
    intro a b
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hK hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.1 a b⟩)
  have hD : ∀ a b c, ParabolicC0AlphaOn α (fun z => D z a b c) K := by
    intro a b c
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hK hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.2.1 a b c⟩)
  have hH : ∀ a b i j, ParabolicC0AlphaOn α (fun z => H z a b i j) K := by
    intro a b i j
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hK hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.2.2 a b i j⟩)
  exact ricciDeTurck_schematic_of_isCompact_det_ne_zero
    (M := M) (D := D) (H := H) hK hα hM hD hH hdet_ne

/-- Compact-domain finite-family schematic Ricci-DeTurck RHS closure from entrywise primitive
controls and pointwise nonvanishing metric determinants, with one determinant lower bound shared
by the family. -/
theorem ricciDeTurck_schematic_family_of_isCompact_det_ne_zero
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {K : Set (ℝ × X)}
    {M : κ → ℝ × X → Matrix n n 𝕜}
    {D : κ → ℝ × X → n → n → n → 𝕜}
    {H : κ → ℝ × X → n → n → n → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hM : ∀ r a b, ParabolicC0AlphaOn α (fun z => M r z a b) K)
    (hD : ∀ r a b c, ParabolicC0AlphaOn α (fun z => D r z a b c) K)
    (hH : ∀ r a b i j, ParabolicC0AlphaOn α (fun z => H r z a b i j) K)
    (hdet_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (M r z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M r z).det‖) ∧
      ∀ r,
        ParabolicC0AlphaOn α
          (fun z : ℝ × X =>
            (fun i j =>
              let Γ : n → n → n → 𝕜 := fun a b c =>
                (2 : 𝕜)⁻¹ *
                  ∑ l : n, ((M r z)⁻¹ : Matrix n n 𝕜) a l *
                    (D r z b c l + D r z c b l - D r z l b c)
              (∑ a : n, ∑ b : n, ((M r z)⁻¹ : Matrix n n 𝕜) a b *
                  H r z a b i j) +
                ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
                  (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) :
              Matrix n n 𝕜)) K := by
  rcases matrix_det_family_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) hK hα hM hdet_ne with
    ⟨δ, hδpos, hdet⟩
  refine ⟨δ, hδpos, hdet, ?_⟩
  intro r
  exact ricciDeTurck_schematic (M := M r) (D := D r) (H := H r)
    (hM r) (hD r) (hH r) hδpos (hdet r)

/-- Local finite product-cylinder primitive estimates globalize a finite family of compact-domain
schematic Ricci-DeTurck RHS closures, with one determinant lower bound shared by the family. -/
theorem ricciDeTurck_schematic_family_of_finset_parabolicCylinder_cover_closedCylinder_variable
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {K : Set (ℝ × X)}
    {M : κ → ℝ × X → Matrix n n 𝕜}
    {D : κ → ℝ × X → n → n → n → 𝕜}
    {H : κ → ℝ × X → n → n → n → n → 𝕜}
    (N : Finset (ℝ × X)) (timeRadius spaceRadius : ℝ × X → ℝ)
    (hK : IsCompact K) (hα : 0 < α)
    (htime_pos : ∀ y ∈ N, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ N, 0 < spaceRadius y)
    (hcover : K ⊆ ⋃ y ∈ N, parabolicCylinder y (timeRadius y) (spaceRadius y))
    (hMlocal : ∀ y ∈ N, ∀ r a b,
      ParabolicC0AlphaOn α (fun z => M r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hDlocal : ∀ y ∈ N, ∀ r a b c,
      ParabolicC0AlphaOn α (fun z => D r z a b c)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hHlocal : ∀ y ∈ N, ∀ r a b i j,
      ParabolicC0AlphaOn α (fun z => H r z a b i j)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hdet_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (M r z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M r z).det‖) ∧
      ∀ r,
        ParabolicC0AlphaOn α
          (fun z : ℝ × X =>
            (fun i j =>
              let Γ : n → n → n → 𝕜 := fun a b c =>
                (2 : 𝕜)⁻¹ *
                  ∑ l : n, ((M r z)⁻¹ : Matrix n n 𝕜) a l *
                    (D r z b c l + D r z c b l - D r z l b c)
              (∑ a : n, ∑ b : n, ((M r z)⁻¹ : Matrix n n 𝕜) a b *
                  H r z a b i j) +
                ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
                  (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) :
              Matrix n n 𝕜)) K := by
  have hM : ∀ r a b, ParabolicC0AlphaOn α (fun z => M r z a b) K := by
    intro r a b
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      N timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hMlocal y hy r a b)
  have hD : ∀ r a b c, ParabolicC0AlphaOn α (fun z => D r z a b c) K := by
    intro r a b c
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      N timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hDlocal y hy r a b c)
  have hH : ∀ r a b i j, ParabolicC0AlphaOn α (fun z => H r z a b i j) K := by
    intro r a b i j
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      N timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hHlocal y hy r a b i j)
  exact ricciDeTurck_schematic_family_of_isCompact_det_ne_zero
    (M := M) (D := D) (H := H) hK hα hM hD hH hdet_ne

/-- Point-dependent local product-cylinder primitive estimates globalize a finite family of
compact-domain schematic Ricci-DeTurck RHS closures, with one determinant lower bound shared by the
family. -/
theorem ricciDeTurck_schematic_family_of_isCompact_of_local_closedCylinder_variable
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {K : Set (ℝ × X)}
    {M : κ → ℝ × X → Matrix n n 𝕜}
    {D : κ → ℝ × X → n → n → n → 𝕜}
    {H : κ → ℝ × X → n → n → n → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (timeRadius spaceRadius : ℝ × X → ℝ)
    (htime_pos : ∀ y ∈ K, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ K, 0 < spaceRadius y)
    (hMlocal : ∀ y ∈ K, ∀ r a b,
      ParabolicC0AlphaOn α (fun z => M r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hDlocal : ∀ y ∈ K, ∀ r a b c,
      ParabolicC0AlphaOn α (fun z => D r z a b c)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hHlocal : ∀ y ∈ K, ∀ r a b i j,
      ParabolicC0AlphaOn α (fun z => H r z a b i j)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hdet_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (M r z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M r z).det‖) ∧
      ∀ r,
        ParabolicC0AlphaOn α
          (fun z : ℝ × X =>
            (fun i j =>
              let Γ : n → n → n → 𝕜 := fun a b c =>
                (2 : 𝕜)⁻¹ *
                  ∑ l : n, ((M r z)⁻¹ : Matrix n n 𝕜) a l *
                    (D r z b c l + D r z c b l - D r z l b c)
              (∑ a : n, ∑ b : n, ((M r z)⁻¹ : Matrix n n 𝕜) a b *
                  H r z a b i j) +
                ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
                  (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) :
              Matrix n n 𝕜)) K := by
  have hM : ∀ r a b, ParabolicC0AlphaOn α (fun z => M r z a b) K := by
    intro r a b
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hK hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hMlocal y hy r a b)
  have hD : ∀ r a b c, ParabolicC0AlphaOn α (fun z => D r z a b c) K := by
    intro r a b c
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hK hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hDlocal y hy r a b c)
  have hH : ∀ r a b i j, ParabolicC0AlphaOn α (fun z => H r z a b i j) K := by
    intro r a b i j
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hK hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hHlocal y hy r a b i j)
  exact ricciDeTurck_schematic_family_of_isCompact_det_ne_zero
    (M := M) (D := D) (H := H) hK hα hM hD hH hdet_ne

/-- Existential point-local product-cylinder primitive estimates globalize a finite family of
compact-domain schematic Ricci-DeTurck RHS closures, with one determinant lower bound shared by the
family. -/
theorem ricciDeTurck_schematic_family_of_isCompact_of_exists_local_closedCylinder
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {K : Set (ℝ × X)}
    {M : κ → ℝ × X → Matrix n n 𝕜}
    {D : κ → ℝ × X → n → n → n → 𝕜}
    {H : κ → ℝ × X → n → n → n → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hlocal : ∀ y ∈ K, ∃ timeRadius > 0, ∃ spaceRadius > 0,
      (∀ r a b,
        ParabolicC0AlphaOn α (fun z => M r z a b)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ r a b c,
        ParabolicC0AlphaOn α (fun z => D r z a b c)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ r a b i j,
        ParabolicC0AlphaOn α (fun z => H r z a b i j)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))))
    (hdet_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (M r z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M r z).det‖) ∧
      ∀ r,
        ParabolicC0AlphaOn α
          (fun z : ℝ × X =>
            (fun i j =>
              let Γ : n → n → n → 𝕜 := fun a b c =>
                (2 : 𝕜)⁻¹ *
                  ∑ l : n, ((M r z)⁻¹ : Matrix n n 𝕜) a l *
                    (D r z b c l + D r z c b l - D r z l b c)
              (∑ a : n, ∑ b : n, ((M r z)⁻¹ : Matrix n n 𝕜) a b *
                  H r z a b i j) +
                ((∑ a : n, ∑ b : n, Γ a i j * Γ b a b) -
                  (∑ a : n, ∑ b : n, Γ a i b * Γ b a j)) :
              Matrix n n 𝕜)) K := by
  have hM : ∀ r a b, ParabolicC0AlphaOn α (fun z => M r z a b) K := by
    intro r a b
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hK hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.1 r a b⟩)
  have hD : ∀ r a b c, ParabolicC0AlphaOn α (fun z => D r z a b c) K := by
    intro r a b c
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hK hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.2.1 r a b c⟩)
  have hH : ∀ r a b i j, ParabolicC0AlphaOn α (fun z => H r z a b i j) K := by
    intro r a b i j
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hK hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.2.2 r a b i j⟩)
  exact ricciDeTurck_schematic_family_of_isCompact_det_ne_zero
    (M := M) (D := D) (H := H) hK hα hM hD hH hdet_ne

/-- Compact-domain finite-family quantitative schematic Ricci-DeTurck RHS differences from
bounded primitive-input differences, with one determinant lower bound shared by both metric
families. -/
theorem ricciDeTurckSchematicMatrix_sub_with_family_of_isCompact_det_ne_zero
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {K : Set (ℝ × X)}
    {MB MH : κ → n → n → ℝ}
    {DB DH : κ → n → n → n → ℝ}
    {HB HH : κ → n → n → n → n → ℝ}
    {ηM ηD : κ → ℝ} {ηH : κ → n → n → ℝ}
    {M N : κ → ℝ × X → Matrix n n 𝕜}
    {D E : κ → ℝ × X → n → n → n → 𝕜}
    {Hc Kc : κ → ℝ × X → n → n → n → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hMB : ∀ r a b, 0 ≤ MB r a b) (hMH : ∀ r a b, 0 ≤ MH r a b)
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hDH : ∀ r a b c, 0 ≤ DH r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hHH : ∀ r a b i j, 0 ≤ HH r a b i j)
    (hM : ∀ r a b,
      ParabolicC0AlphaWith (MB r a b) (MH r a b) α (fun z => M r z a b) K)
    (hN : ∀ r a b,
      ParabolicC0AlphaWith (MB r a b) (MH r a b) α (fun z => N r z a b) K)
    (hD : ∀ r a b c,
      ParabolicC0AlphaWith (DB r a b c) (DH r a b c) α
        (fun z => D r z a b c) K)
    (hE : ∀ r a b c,
      ParabolicC0AlphaWith (DB r a b c) (DH r a b c) α
        (fun z => E r z a b c) K)
    (hHc : ∀ r a b i j,
      ParabolicC0AlphaWith (HB r a b i j) (HH r a b i j) α
        (fun z => Hc r z a b i j) K)
    (hKc : ∀ r a b i j,
      ParabolicC0AlphaWith (HB r a b i j) (HH r a b i j) α
        (fun z => Kc r z a b i j) K)
    (hdetM_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (M r z).det ≠ 0)
    (hdetN_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (N r z).det ≠ 0)
    (hηD : ∀ r, 0 ≤ ηD r)
    (hMdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ K → ‖M r z - N r z‖ ≤ ηM r)
    (hDdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ K → ∀ a b c,
      ‖D r z a b c - E r z a b c‖ ≤ ηD r)
    (hHdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ K → ∀ i j,
      ‖((fun a b => Hc r z a b i j) : Matrix n n 𝕜) -
          ((fun a b => Kc r z a b i j) : Matrix n n 𝕜)‖ ≤ ηH r i j) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M r z).det‖) ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(N r z).det‖) ∧
      ∀ r,
        ParabolicC0AlphaWith
          (ricciDeTurckSchematicDiffBoundConst
            (𝕜 := 𝕜) δ (MB r) (DB r) (HB r) (ηM r) (ηD r) (ηH r))
          (ricciDeTurckSchematicDiffHolderConst
            (𝕜 := 𝕜) δ (MB r) (MH r) (DB r) (DH r) (HB r) (HH r))
          α
          (fun z : ℝ × X =>
            ricciDeTurckSchematicMatrix (M r z) (D r z) (Hc r z) -
              ricciDeTurckSchematicMatrix (N r z) (E r z) (Kc r z)) K := by
  have hMctrl : ∀ r a b, ParabolicC0AlphaOn α (fun z => M r z a b) K := by
    intro r a b
    exact ⟨MB r a b, hMB r a b, MH r a b, hMH r a b, hM r a b⟩
  have hNctrl : ∀ r a b, ParabolicC0AlphaOn α (fun z => N r z a b) K := by
    intro r a b
    exact ⟨MB r a b, hMB r a b, MH r a b, hMH r a b, hN r a b⟩
  rcases matrix_det_pair_family_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) (N := N) hK hα hMctrl hNctrl hdetM_ne hdetN_ne with
    ⟨δ, hδpos, hdetM, hdetN⟩
  refine ⟨δ, hδpos, hdetM, hdetN, ?_⟩
  intro r
  exact ricciDeTurckSchematicMatrix_sub_with
    (M := M r) (N := N r) (D := D r) (E := E r) (Hc := Hc r) (Kc := Kc r)
    (hMH r) (hDB r) (hDH r) (hHB r) (hHH r)
    (hM r) (hN r) (hD r) (hE r) (hHc r) (hKc r)
    (hηD r) (hMdiff r) (hDdiff r) (hHdiff r) hδpos (hdetM r) (hdetN r)

/-- Compact-domain finite-family quantitative schematic RHS differences with coarser primitive
difference constants.  The determinant lower bound and Holder constant are unchanged, while the
bounded-difference constant is promoted from sharper memberwise primitive constants to coarser
chart constants. -/
theorem ricciDeTurckSchematicMatrix_sub_with_family_of_isCompact_det_ne_zero_of_primitive_le
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {K : Set (ℝ × X)}
    {MB MH : κ → n → n → ℝ}
    {DB DH : κ → n → n → n → ℝ}
    {HB HH : κ → n → n → n → n → ℝ}
    {ηM0 ηD0 ηM ηD : κ → ℝ} {ηH0 ηH : κ → n → n → ℝ}
    {M N : κ → ℝ × X → Matrix n n 𝕜}
    {D E : κ → ℝ × X → n → n → n → 𝕜}
    {Hc Kc : κ → ℝ × X → n → n → n → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hMB : ∀ r a b, 0 ≤ MB r a b) (hMH : ∀ r a b, 0 ≤ MH r a b)
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hDH : ∀ r a b c, 0 ≤ DH r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hHH : ∀ r a b i j, 0 ≤ HH r a b i j)
    (hM : ∀ r a b,
      ParabolicC0AlphaWith (MB r a b) (MH r a b) α (fun z => M r z a b) K)
    (hN : ∀ r a b,
      ParabolicC0AlphaWith (MB r a b) (MH r a b) α (fun z => N r z a b) K)
    (hD : ∀ r a b c,
      ParabolicC0AlphaWith (DB r a b c) (DH r a b c) α
        (fun z => D r z a b c) K)
    (hE : ∀ r a b c,
      ParabolicC0AlphaWith (DB r a b c) (DH r a b c) α
        (fun z => E r z a b c) K)
    (hHc : ∀ r a b i j,
      ParabolicC0AlphaWith (HB r a b i j) (HH r a b i j) α
        (fun z => Hc r z a b i j) K)
    (hKc : ∀ r a b i j,
      ParabolicC0AlphaWith (HB r a b i j) (HH r a b i j) α
        (fun z => Kc r z a b i j) K)
    (hdetM_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (M r z).det ≠ 0)
    (hdetN_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (N r z).det ≠ 0)
    (hηM : ∀ r, ηM0 r ≤ ηM r) (hηD : ∀ r, ηD0 r ≤ ηD r)
    (hηH : ∀ r i j, ηH0 r i j ≤ ηH r i j)
    (hηD0 : ∀ r, 0 ≤ ηD0 r)
    (hMdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ K → ‖M r z - N r z‖ ≤ ηM0 r)
    (hDdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ K → ∀ a b c,
      ‖D r z a b c - E r z a b c‖ ≤ ηD0 r)
    (hHdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ K → ∀ i j,
      ‖((fun a b => Hc r z a b i j) : Matrix n n 𝕜) -
          ((fun a b => Kc r z a b i j) : Matrix n n 𝕜)‖ ≤ ηH0 r i j) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M r z).det‖) ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(N r z).det‖) ∧
      ∀ r,
        ParabolicC0AlphaWith
          (ricciDeTurckSchematicDiffBoundConst
            (𝕜 := 𝕜) δ (MB r) (DB r) (HB r) (ηM r) (ηD r) (ηH r))
          (ricciDeTurckSchematicDiffHolderConst
            (𝕜 := 𝕜) δ (MB r) (MH r) (DB r) (DH r) (HB r) (HH r))
          α
          (fun z : ℝ × X =>
            ricciDeTurckSchematicMatrix (M r z) (D r z) (Hc r z) -
              ricciDeTurckSchematicMatrix (N r z) (E r z) (Kc r z)) K := by
  rcases ricciDeTurckSchematicMatrix_sub_with_family_of_isCompact_det_ne_zero
      (K := K) (MB := MB) (MH := MH) (DB := DB) (DH := DH)
      (HB := HB) (HH := HH) (ηM := ηM0) (ηD := ηD0) (ηH := ηH0)
      (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
      hK hα hMB hMH hDB hDH hHB hHH hM hN hD hE hHc hKc
      hdetM_ne hdetN_ne hηD0 hMdiff hDdiff hHdiff with
    ⟨δ, hδpos, hdetM, hdetN, hctrl⟩
  refine ⟨δ, hδpos, hdetM, hdetN, ?_⟩
  intro r
  exact (hctrl r).mono_const
    (ricciDeTurckSchematicDiffBoundConst_mono
      (𝕜 := 𝕜) hδpos (hDB r) (hHB r) (hηM r) (hηD r) (hηH r))
    le_rfl

/-- Local finite product-cylinder quantitative primitive estimates globalize finite-family
compact-domain schematic Ricci-DeTurck RHS difference estimates, with one determinant lower bound
shared by both metric families. -/
theorem ricciDeTurckSchematicMatrix_sub_with_family_of_finset_parabolicCylinder_cover_closedCylinder_variable
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {K : Set (ℝ × X)}
    {MB MH : κ → n → n → ℝ}
    {DB DH : κ → n → n → n → ℝ}
    {HB HH : κ → n → n → n → n → ℝ}
    {ηM ηD : κ → ℝ} {ηH : κ → n → n → ℝ}
    {M N : κ → ℝ × X → Matrix n n 𝕜}
    {D E : κ → ℝ × X → n → n → n → 𝕜}
    {Hc Kc : κ → ℝ × X → n → n → n → n → 𝕜}
    (S : Finset (ℝ × X)) (timeRadius spaceRadius : ℝ × X → ℝ)
    (hK : IsCompact K) (hα : 0 < α)
    (htime_pos : ∀ y ∈ S, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ S, 0 < spaceRadius y)
    (hcover : K ⊆ ⋃ y ∈ S, parabolicCylinder y (timeRadius y) (spaceRadius y))
    (hMB : ∀ r a b, 0 ≤ MB r a b) (hMH : ∀ r a b, 0 ≤ MH r a b)
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hDH : ∀ r a b c, 0 ≤ DH r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hHH : ∀ r a b i j, 0 ≤ HH r a b i j)
    (hMlocal : ∀ y ∈ S, ∀ r a b,
      ParabolicC0AlphaWith (MB r a b) (MH r a b) α (fun z => M r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hNlocal : ∀ y ∈ S, ∀ r a b,
      ParabolicC0AlphaWith (MB r a b) (MH r a b) α (fun z => N r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hDlocal : ∀ y ∈ S, ∀ r a b c,
      ParabolicC0AlphaWith (DB r a b c) (DH r a b c) α
        (fun z => D r z a b c)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hElocal : ∀ y ∈ S, ∀ r a b c,
      ParabolicC0AlphaWith (DB r a b c) (DH r a b c) α
        (fun z => E r z a b c)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hHclocal : ∀ y ∈ S, ∀ r a b i j,
      ParabolicC0AlphaWith (HB r a b i j) (HH r a b i j) α
        (fun z => Hc r z a b i j)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hKclocal : ∀ y ∈ S, ∀ r a b i j,
      ParabolicC0AlphaWith (HB r a b i j) (HH r a b i j) α
        (fun z => Kc r z a b i j)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hdetM_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (M r z).det ≠ 0)
    (hdetN_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (N r z).det ≠ 0)
    (hηD : ∀ r, 0 ≤ ηD r)
    (hMdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ K → ‖M r z - N r z‖ ≤ ηM r)
    (hDdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ K → ∀ a b c,
      ‖D r z a b c - E r z a b c‖ ≤ ηD r)
    (hHdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ K → ∀ i j,
      ‖((fun a b => Hc r z a b i j) : Matrix n n 𝕜) -
          ((fun a b => Kc r z a b i j) : Matrix n n 𝕜)‖ ≤ ηH r i j) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M r z).det‖) ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(N r z).det‖) ∧
      ∀ r,
        ParabolicC0AlphaWith
          (ricciDeTurckSchematicDiffBoundConst
            (𝕜 := 𝕜) δ (MB r) (DB r) (HB r) (ηM r) (ηD r) (ηH r))
          (ricciDeTurckSchematicDiffHolderConst
            (𝕜 := 𝕜) δ (MB r)
            (fun a b => parabolicCylinderCoverHolderConst S timeRadius spaceRadius α
              (MB r a b) (MH r a b))
            (DB r)
            (fun a b c => parabolicCylinderCoverHolderConst S timeRadius spaceRadius α
              (DB r a b c) (DH r a b c))
            (HB r)
            (fun a b i j => parabolicCylinderCoverHolderConst S timeRadius spaceRadius α
              (HB r a b i j) (HH r a b i j)))
          α
          (fun z : ℝ × X =>
            ricciDeTurckSchematicMatrix (M r z) (D r z) (Hc r z) -
              ricciDeTurckSchematicMatrix (N r z) (E r z) (Kc r z)) K := by
  let MHg : κ → n → n → ℝ := fun r a b =>
    parabolicCylinderCoverHolderConst S timeRadius spaceRadius α (MB r a b) (MH r a b)
  let DHg : κ → n → n → n → ℝ := fun r a b c =>
    parabolicCylinderCoverHolderConst S timeRadius spaceRadius α (DB r a b c) (DH r a b c)
  let HHg : κ → n → n → n → n → ℝ := fun r a b i j =>
    parabolicCylinderCoverHolderConst S timeRadius spaceRadius α
      (HB r a b i j) (HH r a b i j)
  have hMHg : ∀ r a b, 0 ≤ MHg r a b := by
    intro r a b
    exact parabolicCylinderCoverHolderConst_nonneg S timeRadius spaceRadius (hMH r a b)
  have hDHg : ∀ r a b c, 0 ≤ DHg r a b c := by
    intro r a b c
    exact parabolicCylinderCoverHolderConst_nonneg S timeRadius spaceRadius (hDH r a b c)
  have hHHg : ∀ r a b i j, 0 ≤ HHg r a b i j := by
    intro r a b i j
    exact parabolicCylinderCoverHolderConst_nonneg S timeRadius spaceRadius (hHH r a b i j)
  have hM : ∀ r a b,
      ParabolicC0AlphaWith (MB r a b) (MHg r a b) α (fun z => M r z a b) K := by
    intro r a b
    exact ParabolicC0AlphaWith.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hMlocal y hy r a b)
  have hN : ∀ r a b,
      ParabolicC0AlphaWith (MB r a b) (MHg r a b) α (fun z => N r z a b) K := by
    intro r a b
    exact ParabolicC0AlphaWith.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hNlocal y hy r a b)
  have hD : ∀ r a b c,
      ParabolicC0AlphaWith (DB r a b c) (DHg r a b c) α
        (fun z => D r z a b c) K := by
    intro r a b c
    exact ParabolicC0AlphaWith.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hDlocal y hy r a b c)
  have hE : ∀ r a b c,
      ParabolicC0AlphaWith (DB r a b c) (DHg r a b c) α
        (fun z => E r z a b c) K := by
    intro r a b c
    exact ParabolicC0AlphaWith.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hElocal y hy r a b c)
  have hHc : ∀ r a b i j,
      ParabolicC0AlphaWith (HB r a b i j) (HHg r a b i j) α
        (fun z => Hc r z a b i j) K := by
    intro r a b i j
    exact ParabolicC0AlphaWith.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hHclocal y hy r a b i j)
  have hKc : ∀ r a b i j,
      ParabolicC0AlphaWith (HB r a b i j) (HHg r a b i j) α
        (fun z => Kc r z a b i j) K := by
    intro r a b i j
    exact ParabolicC0AlphaWith.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hKclocal y hy r a b i j)
  simpa [MHg, DHg, HHg] using
    ricciDeTurckSchematicMatrix_sub_with_family_of_isCompact_det_ne_zero
      (K := K) (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
      hK hα hMB hMHg hDB hDHg hHB hHHg hM hN hD hE hHc hKc
      hdetM_ne hdetN_ne hηD hMdiff hDdiff hHdiff

/-- Local finite product-cylinder quantitative primitive estimates globalize finite-family
compact-domain schematic Ricci-DeTurck RHS difference estimates, while promoting the primitive
difference constants to coarser chart constants.  The product-cylinder Holder constants are
unchanged. -/
theorem ricciDeTurckSchematicMatrix_sub_with_family_of_finset_parabolicCylinder_cover_closedCylinder_variable_of_primitive_le
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {K : Set (ℝ × X)}
    {MB MH : κ → n → n → ℝ}
    {DB DH : κ → n → n → n → ℝ}
    {HB HH : κ → n → n → n → n → ℝ}
    {ηM0 ηD0 ηM ηD : κ → ℝ} {ηH0 ηH : κ → n → n → ℝ}
    {M N : κ → ℝ × X → Matrix n n 𝕜}
    {D E : κ → ℝ × X → n → n → n → 𝕜}
    {Hc Kc : κ → ℝ × X → n → n → n → n → 𝕜}
    (S : Finset (ℝ × X)) (timeRadius spaceRadius : ℝ × X → ℝ)
    (hK : IsCompact K) (hα : 0 < α)
    (htime_pos : ∀ y ∈ S, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ S, 0 < spaceRadius y)
    (hcover : K ⊆ ⋃ y ∈ S, parabolicCylinder y (timeRadius y) (spaceRadius y))
    (hMB : ∀ r a b, 0 ≤ MB r a b) (hMH : ∀ r a b, 0 ≤ MH r a b)
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hDH : ∀ r a b c, 0 ≤ DH r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hHH : ∀ r a b i j, 0 ≤ HH r a b i j)
    (hMlocal : ∀ y ∈ S, ∀ r a b,
      ParabolicC0AlphaWith (MB r a b) (MH r a b) α (fun z => M r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hNlocal : ∀ y ∈ S, ∀ r a b,
      ParabolicC0AlphaWith (MB r a b) (MH r a b) α (fun z => N r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hDlocal : ∀ y ∈ S, ∀ r a b c,
      ParabolicC0AlphaWith (DB r a b c) (DH r a b c) α
        (fun z => D r z a b c)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hElocal : ∀ y ∈ S, ∀ r a b c,
      ParabolicC0AlphaWith (DB r a b c) (DH r a b c) α
        (fun z => E r z a b c)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hHclocal : ∀ y ∈ S, ∀ r a b i j,
      ParabolicC0AlphaWith (HB r a b i j) (HH r a b i j) α
        (fun z => Hc r z a b i j)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hKclocal : ∀ y ∈ S, ∀ r a b i j,
      ParabolicC0AlphaWith (HB r a b i j) (HH r a b i j) α
        (fun z => Kc r z a b i j)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hdetM_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (M r z).det ≠ 0)
    (hdetN_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (N r z).det ≠ 0)
    (hηM : ∀ r, ηM0 r ≤ ηM r) (hηD : ∀ r, ηD0 r ≤ ηD r)
    (hηH : ∀ r i j, ηH0 r i j ≤ ηH r i j)
    (hηD0 : ∀ r, 0 ≤ ηD0 r)
    (hMdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ K → ‖M r z - N r z‖ ≤ ηM0 r)
    (hDdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ K → ∀ a b c,
      ‖D r z a b c - E r z a b c‖ ≤ ηD0 r)
    (hHdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ K → ∀ i j,
      ‖((fun a b => Hc r z a b i j) : Matrix n n 𝕜) -
          ((fun a b => Kc r z a b i j) : Matrix n n 𝕜)‖ ≤ ηH0 r i j) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M r z).det‖) ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(N r z).det‖) ∧
      ∀ r,
        ParabolicC0AlphaWith
          (ricciDeTurckSchematicDiffBoundConst
            (𝕜 := 𝕜) δ (MB r) (DB r) (HB r) (ηM r) (ηD r) (ηH r))
          (ricciDeTurckSchematicDiffHolderConst
            (𝕜 := 𝕜) δ (MB r)
            (fun a b => parabolicCylinderCoverHolderConst S timeRadius spaceRadius α
              (MB r a b) (MH r a b))
            (DB r)
            (fun a b c => parabolicCylinderCoverHolderConst S timeRadius spaceRadius α
              (DB r a b c) (DH r a b c))
            (HB r)
            (fun a b i j => parabolicCylinderCoverHolderConst S timeRadius spaceRadius α
              (HB r a b i j) (HH r a b i j)))
          α
          (fun z : ℝ × X =>
            ricciDeTurckSchematicMatrix (M r z) (D r z) (Hc r z) -
              ricciDeTurckSchematicMatrix (N r z) (E r z) (Kc r z)) K := by
  rcases
    ricciDeTurckSchematicMatrix_sub_with_family_of_finset_parabolicCylinder_cover_closedCylinder_variable
      (S := S) (timeRadius := timeRadius) (spaceRadius := spaceRadius)
      (K := K) (ηM := ηM0) (ηD := ηD0) (ηH := ηH0)
      (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
      hK hα htime_pos hspace_pos hcover hMB hMH hDB hDH hHB hHH
      hMlocal hNlocal hDlocal hElocal hHclocal hKclocal
      hdetM_ne hdetN_ne hηD0 hMdiff hDdiff hHdiff with
    ⟨δ, hδpos, hdetM, hdetN, hctrl⟩
  refine ⟨δ, hδpos, hdetM, hdetN, ?_⟩
  intro r
  exact (hctrl r).mono_const
    (ricciDeTurckSchematicDiffBoundConst_mono
      (𝕜 := 𝕜) hδpos (hDB r) (hHB r) (hηM r) (hηD r) (hηH r))
    le_rfl

/-- Point-dependent local product-cylinder quantitative primitive estimates globalize
finite-family compact-domain schematic Ricci-DeTurck RHS difference estimates. -/
theorem ricciDeTurckSchematicMatrix_sub_with_family_of_isCompact_of_local_closedCylinder_variable
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {K : Set (ℝ × X)}
    {MB MH : κ → n → n → ℝ}
    {DB DH : κ → n → n → n → ℝ}
    {HB HH : κ → n → n → n → n → ℝ}
    {ηM ηD : κ → ℝ} {ηH : κ → n → n → ℝ}
    {M N : κ → ℝ × X → Matrix n n 𝕜}
    {D E : κ → ℝ × X → n → n → n → 𝕜}
    {Hc Kc : κ → ℝ × X → n → n → n → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (timeRadius spaceRadius : ℝ × X → ℝ)
    (htime_pos : ∀ y ∈ K, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ K, 0 < spaceRadius y)
    (hMB : ∀ r a b, 0 ≤ MB r a b) (hMH : ∀ r a b, 0 ≤ MH r a b)
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hDH : ∀ r a b c, 0 ≤ DH r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hHH : ∀ r a b i j, 0 ≤ HH r a b i j)
    (hMlocal : ∀ y ∈ K, ∀ r a b,
      ParabolicC0AlphaWith (MB r a b) (MH r a b) α (fun z => M r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hNlocal : ∀ y ∈ K, ∀ r a b,
      ParabolicC0AlphaWith (MB r a b) (MH r a b) α (fun z => N r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hDlocal : ∀ y ∈ K, ∀ r a b c,
      ParabolicC0AlphaWith (DB r a b c) (DH r a b c) α
        (fun z => D r z a b c)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hElocal : ∀ y ∈ K, ∀ r a b c,
      ParabolicC0AlphaWith (DB r a b c) (DH r a b c) α
        (fun z => E r z a b c)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hHclocal : ∀ y ∈ K, ∀ r a b i j,
      ParabolicC0AlphaWith (HB r a b i j) (HH r a b i j) α
        (fun z => Hc r z a b i j)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hKclocal : ∀ y ∈ K, ∀ r a b i j,
      ParabolicC0AlphaWith (HB r a b i j) (HH r a b i j) α
        (fun z => Kc r z a b i j)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hdetM_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (M r z).det ≠ 0)
    (hdetN_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (N r z).det ≠ 0)
    (hηD : ∀ r, 0 ≤ ηD r)
    (hMdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ K → ‖M r z - N r z‖ ≤ ηM r)
    (hDdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ K → ∀ a b c,
      ‖D r z a b c - E r z a b c‖ ≤ ηD r)
    (hHdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ K → ∀ i j,
      ‖((fun a b => Hc r z a b i j) : Matrix n n 𝕜) -
          ((fun a b => Kc r z a b i j) : Matrix n n 𝕜)‖ ≤ ηH r i j) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M r z).det‖) ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(N r z).det‖) ∧
      ∃ MHg : κ → n → n → ℝ, ∃ DHg : κ → n → n → n → ℝ,
        ∃ HHg : κ → n → n → n → n → ℝ,
        (∀ r a b, 0 ≤ MHg r a b) ∧
        (∀ r a b c, 0 ≤ DHg r a b c) ∧
        (∀ r a b i j, 0 ≤ HHg r a b i j) ∧
        ∀ r,
          ParabolicC0AlphaWith
            (ricciDeTurckSchematicDiffBoundConst
              (𝕜 := 𝕜) δ (MB r) (DB r) (HB r) (ηM r) (ηD r) (ηH r))
            (ricciDeTurckSchematicDiffHolderConst
              (𝕜 := 𝕜) δ (MB r) (MHg r) (DB r) (DHg r) (HB r) (HHg r))
            α
            (fun z : ℝ × X =>
              ricciDeTurckSchematicMatrix (M r z) (D r z) (Hc r z) -
                ricciDeTurckSchematicMatrix (N r z) (E r z) (Kc r z)) K := by
  rcases hK.elim_nhds_subcover
      (fun y => parabolicCylinder y (timeRadius y) (spaceRadius y))
      (fun y hy => parabolicCylinder.mem_nhds (p := y) (timeRadius := timeRadius y)
        (spaceRadius := spaceRadius y) (htime_pos y hy) (hspace_pos y hy)) with
    ⟨S, hSK, hcover⟩
  let MHg : κ → n → n → ℝ := fun r a b =>
    parabolicCylinderCoverHolderConst S timeRadius spaceRadius α (MB r a b) (MH r a b)
  let DHg : κ → n → n → n → ℝ := fun r a b c =>
    parabolicCylinderCoverHolderConst S timeRadius spaceRadius α (DB r a b c) (DH r a b c)
  let HHg : κ → n → n → n → n → ℝ := fun r a b i j =>
    parabolicCylinderCoverHolderConst S timeRadius spaceRadius α
      (HB r a b i j) (HH r a b i j)
  have hMHg : ∀ r a b, 0 ≤ MHg r a b := by
    intro r a b
    exact parabolicCylinderCoverHolderConst_nonneg S timeRadius spaceRadius (hMH r a b)
  have hDHg : ∀ r a b c, 0 ≤ DHg r a b c := by
    intro r a b c
    exact parabolicCylinderCoverHolderConst_nonneg S timeRadius spaceRadius (hDH r a b c)
  have hHHg : ∀ r a b i j, 0 ≤ HHg r a b i j := by
    intro r a b i j
    exact parabolicCylinderCoverHolderConst_nonneg S timeRadius spaceRadius (hHH r a b i j)
  rcases
    ricciDeTurckSchematicMatrix_sub_with_family_of_finset_parabolicCylinder_cover_closedCylinder_variable
      (S := S) (timeRadius := timeRadius) (spaceRadius := spaceRadius)
      (K := K) (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
      hK hα
      (fun y hy => htime_pos y (hSK y hy))
      (fun y hy => hspace_pos y (hSK y hy)) hcover
      hMB hMH hDB hDH hHB hHH
      (fun y hy => hMlocal y (hSK y hy))
      (fun y hy => hNlocal y (hSK y hy))
      (fun y hy => hDlocal y (hSK y hy))
      (fun y hy => hElocal y (hSK y hy))
      (fun y hy => hHclocal y (hSK y hy))
      (fun y hy => hKclocal y (hSK y hy))
      hdetM_ne hdetN_ne hηD hMdiff hDdiff hHdiff with
    ⟨δ, hδpos, hdetM, hdetN, hwith⟩
  refine ⟨δ, hδpos, hdetM, hdetN, MHg, DHg, HHg, hMHg, hDHg, hHHg, ?_⟩
  intro r
  simpa [MHg, DHg, HHg] using hwith r

/-- Point-dependent local product-cylinder quantitative primitive estimates globalize
finite-family compact-domain schematic Ricci-DeTurck RHS difference estimates, while promoting the
primitive difference constants to coarser chart constants. -/
theorem ricciDeTurckSchematicMatrix_sub_with_family_of_isCompact_of_local_closedCylinder_variable_of_primitive_le
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {K : Set (ℝ × X)}
    {MB MH : κ → n → n → ℝ}
    {DB DH : κ → n → n → n → ℝ}
    {HB HH : κ → n → n → n → n → ℝ}
    {ηM0 ηD0 ηM ηD : κ → ℝ} {ηH0 ηH : κ → n → n → ℝ}
    {M N : κ → ℝ × X → Matrix n n 𝕜}
    {D E : κ → ℝ × X → n → n → n → 𝕜}
    {Hc Kc : κ → ℝ × X → n → n → n → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (timeRadius spaceRadius : ℝ × X → ℝ)
    (htime_pos : ∀ y ∈ K, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ K, 0 < spaceRadius y)
    (hMB : ∀ r a b, 0 ≤ MB r a b) (hMH : ∀ r a b, 0 ≤ MH r a b)
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hDH : ∀ r a b c, 0 ≤ DH r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hHH : ∀ r a b i j, 0 ≤ HH r a b i j)
    (hMlocal : ∀ y ∈ K, ∀ r a b,
      ParabolicC0AlphaWith (MB r a b) (MH r a b) α (fun z => M r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hNlocal : ∀ y ∈ K, ∀ r a b,
      ParabolicC0AlphaWith (MB r a b) (MH r a b) α (fun z => N r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hDlocal : ∀ y ∈ K, ∀ r a b c,
      ParabolicC0AlphaWith (DB r a b c) (DH r a b c) α
        (fun z => D r z a b c)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hElocal : ∀ y ∈ K, ∀ r a b c,
      ParabolicC0AlphaWith (DB r a b c) (DH r a b c) α
        (fun z => E r z a b c)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hHclocal : ∀ y ∈ K, ∀ r a b i j,
      ParabolicC0AlphaWith (HB r a b i j) (HH r a b i j) α
        (fun z => Hc r z a b i j)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hKclocal : ∀ y ∈ K, ∀ r a b i j,
      ParabolicC0AlphaWith (HB r a b i j) (HH r a b i j) α
        (fun z => Kc r z a b i j)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hdetM_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (M r z).det ≠ 0)
    (hdetN_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (N r z).det ≠ 0)
    (hηM : ∀ r, ηM0 r ≤ ηM r) (hηD : ∀ r, ηD0 r ≤ ηD r)
    (hηH : ∀ r i j, ηH0 r i j ≤ ηH r i j)
    (hηD0 : ∀ r, 0 ≤ ηD0 r)
    (hMdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ K → ‖M r z - N r z‖ ≤ ηM0 r)
    (hDdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ K → ∀ a b c,
      ‖D r z a b c - E r z a b c‖ ≤ ηD0 r)
    (hHdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ K → ∀ i j,
      ‖((fun a b => Hc r z a b i j) : Matrix n n 𝕜) -
          ((fun a b => Kc r z a b i j) : Matrix n n 𝕜)‖ ≤ ηH0 r i j) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M r z).det‖) ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(N r z).det‖) ∧
      ∃ MHg : κ → n → n → ℝ, ∃ DHg : κ → n → n → n → ℝ,
        ∃ HHg : κ → n → n → n → n → ℝ,
        (∀ r a b, 0 ≤ MHg r a b) ∧
        (∀ r a b c, 0 ≤ DHg r a b c) ∧
        (∀ r a b i j, 0 ≤ HHg r a b i j) ∧
        ∀ r,
          ParabolicC0AlphaWith
            (ricciDeTurckSchematicDiffBoundConst
              (𝕜 := 𝕜) δ (MB r) (DB r) (HB r) (ηM r) (ηD r) (ηH r))
            (ricciDeTurckSchematicDiffHolderConst
              (𝕜 := 𝕜) δ (MB r) (MHg r) (DB r) (DHg r) (HB r) (HHg r))
            α
            (fun z : ℝ × X =>
              ricciDeTurckSchematicMatrix (M r z) (D r z) (Hc r z) -
                ricciDeTurckSchematicMatrix (N r z) (E r z) (Kc r z)) K := by
  rcases
    ricciDeTurckSchematicMatrix_sub_with_family_of_isCompact_of_local_closedCylinder_variable
      (K := K) (ηM := ηM0) (ηD := ηD0) (ηH := ηH0)
      (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
      hK hα timeRadius spaceRadius htime_pos hspace_pos
      hMB hMH hDB hDH hHB hHH
      hMlocal hNlocal hDlocal hElocal hHclocal hKclocal
      hdetM_ne hdetN_ne hηD0 hMdiff hDdiff hHdiff with
    ⟨δ, hδpos, hdetM, hdetN, MHg, DHg, HHg, hMHg, hDHg, hHHg, hctrl⟩
  refine ⟨δ, hδpos, hdetM, hdetN, MHg, DHg, HHg, hMHg, hDHg, hHHg, ?_⟩
  intro r
  exact (hctrl r).mono_const
    (ricciDeTurckSchematicDiffBoundConst_mono
      (𝕜 := 𝕜) hδpos (hDB r) (hHB r) (hηM r) (hηD r) (hηH r))
    le_rfl

/-- Existential point-local product-cylinder quantitative primitive estimates globalize
finite-family compact-domain schematic Ricci-DeTurck RHS difference estimates. -/
theorem ricciDeTurckSchematicMatrix_sub_with_family_of_isCompact_of_exists_local_closedCylinder
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {K : Set (ℝ × X)}
    {MB MH : κ → n → n → ℝ}
    {DB DH : κ → n → n → n → ℝ}
    {HB HH : κ → n → n → n → n → ℝ}
    {ηM ηD : κ → ℝ} {ηH : κ → n → n → ℝ}
    {M N : κ → ℝ × X → Matrix n n 𝕜}
    {D E : κ → ℝ × X → n → n → n → 𝕜}
    {Hc Kc : κ → ℝ × X → n → n → n → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hMB : ∀ r a b, 0 ≤ MB r a b) (hMH : ∀ r a b, 0 ≤ MH r a b)
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hDH : ∀ r a b c, 0 ≤ DH r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hHH : ∀ r a b i j, 0 ≤ HH r a b i j)
    (hlocal : ∀ y ∈ K, ∃ timeRadius > 0, ∃ spaceRadius > 0,
      (∀ r a b,
        ParabolicC0AlphaWith (MB r a b) (MH r a b) α (fun z => M r z a b)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ r a b,
        ParabolicC0AlphaWith (MB r a b) (MH r a b) α (fun z => N r z a b)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ r a b c,
        ParabolicC0AlphaWith (DB r a b c) (DH r a b c) α
          (fun z => D r z a b c)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ r a b c,
        ParabolicC0AlphaWith (DB r a b c) (DH r a b c) α
          (fun z => E r z a b c)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ r a b i j,
        ParabolicC0AlphaWith (HB r a b i j) (HH r a b i j) α
          (fun z => Hc r z a b i j)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ r a b i j,
        ParabolicC0AlphaWith (HB r a b i j) (HH r a b i j) α
          (fun z => Kc r z a b i j)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))))
    (hdetM_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (M r z).det ≠ 0)
    (hdetN_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (N r z).det ≠ 0)
    (hηD : ∀ r, 0 ≤ ηD r)
    (hMdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ K → ‖M r z - N r z‖ ≤ ηM r)
    (hDdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ K → ∀ a b c,
      ‖D r z a b c - E r z a b c‖ ≤ ηD r)
    (hHdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ K → ∀ i j,
      ‖((fun a b => Hc r z a b i j) : Matrix n n 𝕜) -
          ((fun a b => Kc r z a b i j) : Matrix n n 𝕜)‖ ≤ ηH r i j) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M r z).det‖) ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(N r z).det‖) ∧
      ∃ MHg : κ → n → n → ℝ, ∃ DHg : κ → n → n → n → ℝ,
        ∃ HHg : κ → n → n → n → n → ℝ,
        (∀ r a b, 0 ≤ MHg r a b) ∧
        (∀ r a b c, 0 ≤ DHg r a b c) ∧
        (∀ r a b i j, 0 ≤ HHg r a b i j) ∧
        ∀ r,
          ParabolicC0AlphaWith
            (ricciDeTurckSchematicDiffBoundConst
              (𝕜 := 𝕜) δ (MB r) (DB r) (HB r) (ηM r) (ηD r) (ηH r))
            (ricciDeTurckSchematicDiffHolderConst
              (𝕜 := 𝕜) δ (MB r) (MHg r) (DB r) (DHg r) (HB r) (HHg r))
            α
            (fun z : ℝ × X =>
              ricciDeTurckSchematicMatrix (M r z) (D r z) (Hc r z) -
                ricciDeTurckSchematicMatrix (N r z) (E r z) (Kc r z)) K := by
  classical
  let timeRadius : ℝ × X → ℝ := fun y =>
    if hy : y ∈ K then Classical.choose (hlocal y hy) else 1
  let spaceRadius : ℝ × X → ℝ := fun y =>
    if hy : y ∈ K then Classical.choose (Classical.choose_spec (hlocal y hy)).2 else 1
  have htime_pos : ∀ y ∈ K, 0 < timeRadius y := by
    intro y hy
    dsimp [timeRadius]
    rw [dif_pos hy]
    exact (Classical.choose_spec (hlocal y hy)).1
  have hspace_pos : ∀ y ∈ K, 0 < spaceRadius y := by
    intro y hy
    dsimp [spaceRadius]
    rw [dif_pos hy]
    exact (Classical.choose_spec (Classical.choose_spec (hlocal y hy)).2).1
  have hMlocal : ∀ y ∈ K, ∀ r a b,
      ParabolicC0AlphaWith (MB r a b) (MH r a b) α (fun z => M r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)) := by
    intro y hy r a b
    dsimp [timeRadius, spaceRadius]
    rw [dif_pos hy, dif_pos hy]
    exact (Classical.choose_spec (Classical.choose_spec (hlocal y hy)).2).2.1 r a b
  have hNlocal : ∀ y ∈ K, ∀ r a b,
      ParabolicC0AlphaWith (MB r a b) (MH r a b) α (fun z => N r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)) := by
    intro y hy r a b
    dsimp [timeRadius, spaceRadius]
    rw [dif_pos hy, dif_pos hy]
    exact (Classical.choose_spec (Classical.choose_spec (hlocal y hy)).2).2.2.1 r a b
  have hDlocal : ∀ y ∈ K, ∀ r a b c,
      ParabolicC0AlphaWith (DB r a b c) (DH r a b c) α
        (fun z => D r z a b c)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)) := by
    intro y hy r a b c
    dsimp [timeRadius, spaceRadius]
    rw [dif_pos hy, dif_pos hy]
    exact (Classical.choose_spec (Classical.choose_spec (hlocal y hy)).2).2.2.2.1 r a b c
  have hElocal : ∀ y ∈ K, ∀ r a b c,
      ParabolicC0AlphaWith (DB r a b c) (DH r a b c) α
        (fun z => E r z a b c)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)) := by
    intro y hy r a b c
    dsimp [timeRadius, spaceRadius]
    rw [dif_pos hy, dif_pos hy]
    exact (Classical.choose_spec (Classical.choose_spec (hlocal y hy)).2).2.2.2.2.1 r a b c
  have hHclocal : ∀ y ∈ K, ∀ r a b i j,
      ParabolicC0AlphaWith (HB r a b i j) (HH r a b i j) α
        (fun z => Hc r z a b i j)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)) := by
    intro y hy r a b i j
    dsimp [timeRadius, spaceRadius]
    rw [dif_pos hy, dif_pos hy]
    exact (Classical.choose_spec (Classical.choose_spec (hlocal y hy)).2).2.2.2.2.2.1
      r a b i j
  have hKclocal : ∀ y ∈ K, ∀ r a b i j,
      ParabolicC0AlphaWith (HB r a b i j) (HH r a b i j) α
        (fun z => Kc r z a b i j)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)) := by
    intro y hy r a b i j
    dsimp [timeRadius, spaceRadius]
    rw [dif_pos hy, dif_pos hy]
    exact (Classical.choose_spec (Classical.choose_spec (hlocal y hy)).2).2.2.2.2.2.2
      r a b i j
  exact ricciDeTurckSchematicMatrix_sub_with_family_of_isCompact_of_local_closedCylinder_variable
    (K := K) (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
    hK hα timeRadius spaceRadius htime_pos hspace_pos
    hMB hMH hDB hDH hHB hHH
    hMlocal hNlocal hDlocal hElocal hHclocal hKclocal
    hdetM_ne hdetN_ne hηD hMdiff hDdiff hHdiff

/-- Existential point-local product-cylinder quantitative primitive estimates globalize
finite-family compact-domain schematic Ricci-DeTurck RHS difference estimates, while promoting the
primitive difference constants to coarser chart constants. -/
theorem ricciDeTurckSchematicMatrix_sub_with_family_of_isCompact_of_exists_local_closedCylinder_of_primitive_le
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {K : Set (ℝ × X)}
    {MB MH : κ → n → n → ℝ}
    {DB DH : κ → n → n → n → ℝ}
    {HB HH : κ → n → n → n → n → ℝ}
    {ηM0 ηD0 ηM ηD : κ → ℝ} {ηH0 ηH : κ → n → n → ℝ}
    {M N : κ → ℝ × X → Matrix n n 𝕜}
    {D E : κ → ℝ × X → n → n → n → 𝕜}
    {Hc Kc : κ → ℝ × X → n → n → n → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hMB : ∀ r a b, 0 ≤ MB r a b) (hMH : ∀ r a b, 0 ≤ MH r a b)
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hDH : ∀ r a b c, 0 ≤ DH r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hHH : ∀ r a b i j, 0 ≤ HH r a b i j)
    (hlocal : ∀ y ∈ K, ∃ timeRadius > 0, ∃ spaceRadius > 0,
      (∀ r a b,
        ParabolicC0AlphaWith (MB r a b) (MH r a b) α (fun z => M r z a b)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ r a b,
        ParabolicC0AlphaWith (MB r a b) (MH r a b) α (fun z => N r z a b)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ r a b c,
        ParabolicC0AlphaWith (DB r a b c) (DH r a b c) α
          (fun z => D r z a b c)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ r a b c,
        ParabolicC0AlphaWith (DB r a b c) (DH r a b c) α
          (fun z => E r z a b c)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ r a b i j,
        ParabolicC0AlphaWith (HB r a b i j) (HH r a b i j) α
          (fun z => Hc r z a b i j)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ r a b i j,
        ParabolicC0AlphaWith (HB r a b i j) (HH r a b i j) α
          (fun z => Kc r z a b i j)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))))
    (hdetM_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (M r z).det ≠ 0)
    (hdetN_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (N r z).det ≠ 0)
    (hηM : ∀ r, ηM0 r ≤ ηM r) (hηD : ∀ r, ηD0 r ≤ ηD r)
    (hηH : ∀ r i j, ηH0 r i j ≤ ηH r i j)
    (hηD0 : ∀ r, 0 ≤ ηD0 r)
    (hMdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ K → ‖M r z - N r z‖ ≤ ηM0 r)
    (hDdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ K → ∀ a b c,
      ‖D r z a b c - E r z a b c‖ ≤ ηD0 r)
    (hHdiff : ∀ r ⦃z : ℝ × X⦄, z ∈ K → ∀ i j,
      ‖((fun a b => Hc r z a b i j) : Matrix n n 𝕜) -
          ((fun a b => Kc r z a b i j) : Matrix n n 𝕜)‖ ≤ ηH0 r i j) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M r z).det‖) ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(N r z).det‖) ∧
      ∃ MHg : κ → n → n → ℝ, ∃ DHg : κ → n → n → n → ℝ,
        ∃ HHg : κ → n → n → n → n → ℝ,
        (∀ r a b, 0 ≤ MHg r a b) ∧
        (∀ r a b c, 0 ≤ DHg r a b c) ∧
        (∀ r a b i j, 0 ≤ HHg r a b i j) ∧
        ∀ r,
          ParabolicC0AlphaWith
            (ricciDeTurckSchematicDiffBoundConst
              (𝕜 := 𝕜) δ (MB r) (DB r) (HB r) (ηM r) (ηD r) (ηH r))
            (ricciDeTurckSchematicDiffHolderConst
              (𝕜 := 𝕜) δ (MB r) (MHg r) (DB r) (DHg r) (HB r) (HHg r))
            α
            (fun z : ℝ × X =>
              ricciDeTurckSchematicMatrix (M r z) (D r z) (Hc r z) -
                ricciDeTurckSchematicMatrix (N r z) (E r z) (Kc r z)) K := by
  rcases
    ricciDeTurckSchematicMatrix_sub_with_family_of_isCompact_of_exists_local_closedCylinder
      (K := K) (ηM := ηM0) (ηD := ηD0) (ηH := ηH0)
      (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
      hK hα hMB hMH hDB hDH hHB hHH
      hlocal hdetM_ne hdetN_ne hηD0 hMdiff hDdiff hHdiff with
    ⟨δ, hδpos, hdetM, hdetN, MHg, DHg, HHg, hMHg, hDHg, hHHg, hctrl⟩
  refine ⟨δ, hδpos, hdetM, hdetN, MHg, DHg, HHg, hMHg, hDHg, hHHg, ?_⟩
  intro r
  exact (hctrl r).mono_const
    (ricciDeTurckSchematicDiffBoundConst_mono
      (𝕜 := 𝕜) hδpos (hDB r) (hHB r) (hηM r) (hηD r) (hηH r))
    le_rfl

/-- Compact-domain finite-family quantitative schematic Ricci-DeTurck RHS differences from
entrywise primitive-input difference controls, with one determinant lower bound shared by both
metric families. -/
theorem ricciDeTurckSchematicMatrix_sub_with_entrywise_family_of_isCompact_det_ne_zero
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {K : Set (ℝ × X)}
    {MB MH MBd MHd : κ → n → n → ℝ}
    {DB DH DDB DDH : κ → n → n → n → ℝ}
    {HB HH HBd HHd : κ → n → n → n → n → ℝ}
    {M N : κ → ℝ × X → Matrix n n 𝕜}
    {D E : κ → ℝ × X → n → n → n → 𝕜}
    {Hc Kc : κ → ℝ × X → n → n → n → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hMB : ∀ r a b, 0 ≤ MB r a b) (hMH : ∀ r a b, 0 ≤ MH r a b)
    (hMBd : ∀ r a b, 0 ≤ MBd r a b)
    (hMHd : ∀ r a b, 0 ≤ MHd r a b)
    (hDB : ∀ r a b c, 0 ≤ DB r a b c)
    (hDH : ∀ r a b c, 0 ≤ DH r a b c)
    (hDDB : ∀ r a b c, 0 ≤ DDB r a b c)
    (hDDH : ∀ r a b c, 0 ≤ DDH r a b c)
    (hHB : ∀ r a b i j, 0 ≤ HB r a b i j)
    (hHH : ∀ r a b i j, 0 ≤ HH r a b i j)
    (hHBd : ∀ r a b i j, 0 ≤ HBd r a b i j)
    (hHHd : ∀ r a b i j, 0 ≤ HHd r a b i j)
    (hM : ∀ r a b,
      ParabolicC0AlphaWith (MB r a b) (MH r a b) α (fun z => M r z a b) K)
    (hN : ∀ r a b,
      ParabolicC0AlphaWith (MB r a b) (MH r a b) α (fun z => N r z a b) K)
    (hMdiff : ∀ r a b,
      ParabolicC0AlphaWith (MBd r a b) (MHd r a b) α
        (fun z => M r z a b - N r z a b) K)
    (hD : ∀ r a b c,
      ParabolicC0AlphaWith (DB r a b c) (DH r a b c) α
        (fun z => D r z a b c) K)
    (hE : ∀ r a b c,
      ParabolicC0AlphaWith (DB r a b c) (DH r a b c) α
        (fun z => E r z a b c) K)
    (hDdiff : ∀ r a b c,
      ParabolicC0AlphaWith (DDB r a b c) (DDH r a b c) α
        (fun z => D r z a b c - E r z a b c) K)
    (hKc : ∀ r a b i j,
      ParabolicC0AlphaWith (HB r a b i j) (HH r a b i j) α
        (fun z => Kc r z a b i j) K)
    (hHdiff : ∀ r a b i j,
      ParabolicC0AlphaWith (HBd r a b i j) (HHd r a b i j) α
        (fun z => Hc r z a b i j - Kc r z a b i j) K)
    (hdetM_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (M r z).det ≠ 0)
    (hdetN_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (N r z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M r z).det‖) ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(N r z).det‖) ∧
      ∀ r,
        ParabolicC0AlphaWith
          (ricciDeTurckSchematicEntrywiseSubBoundConst
            (𝕜 := 𝕜) δ (MB r) (MBd r) (DB r) (DDB r) (HB r) (HBd r))
          (ricciDeTurckSchematicEntrywiseSubHolderConst
            (𝕜 := 𝕜) δ (MB r) (MH r) (MBd r) (MHd r) (DB r) (DH r)
              (DDB r) (DDH r) (HB r) (HH r) (HBd r) (HHd r))
          α
          (fun z : ℝ × X =>
            ricciDeTurckSchematicMatrix (M r z) (D r z) (Hc r z) -
              ricciDeTurckSchematicMatrix (N r z) (E r z) (Kc r z)) K := by
  have hMctrl : ∀ r a b, ParabolicC0AlphaOn α (fun z => M r z a b) K := by
    intro r a b
    exact ⟨MB r a b, hMB r a b, MH r a b, hMH r a b, hM r a b⟩
  have hNctrl : ∀ r a b, ParabolicC0AlphaOn α (fun z => N r z a b) K := by
    intro r a b
    exact ⟨MB r a b, hMB r a b, MH r a b, hMH r a b, hN r a b⟩
  rcases matrix_det_pair_family_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) (N := N) hK hα hMctrl hNctrl hdetM_ne hdetN_ne with
    ⟨δ, hδpos, hdetM, hdetN⟩
  refine ⟨δ, hδpos, hdetM, hdetN, ?_⟩
  intro r
  exact ricciDeTurckSchematicMatrix_sub_with_entrywise
    (M := M r) (N := N r) (D := D r) (E := E r) (Hc := Hc r) (Kc := Kc r)
    (hMH r) (hMBd r) (hMHd r) (hDB r) (hDH r) (hDDB r) (hDDH r)
    (hHB r) (hHH r) (hHBd r) (hHHd r) (hM r) (hN r) (hMdiff r)
    (hD r) (hE r) (hDdiff r) (hKc r) (hHdiff r) hδpos (hdetM r) (hdetN r)

/-- Compact-domain finite-family schematic Ricci-DeTurck RHS differences preserve existential
parabolic `C^{0,α}` control from entrywise primitive-input difference controls, with one
determinant lower bound shared by both metric families. -/
theorem ricciDeTurckSchematicMatrix_sub_entrywise_family_of_isCompact_det_ne_zero
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {K : Set (ℝ × X)}
    {M N : κ → ℝ × X → Matrix n n 𝕜}
    {D E : κ → ℝ × X → n → n → n → 𝕜}
    {Hc Kc : κ → ℝ × X → n → n → n → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hM : ∀ r a b, ParabolicC0AlphaOn α (fun z => M r z a b) K)
    (hN : ∀ r a b, ParabolicC0AlphaOn α (fun z => N r z a b) K)
    (hMdiff : ∀ r a b, ParabolicC0AlphaOn α (fun z => M r z a b - N r z a b) K)
    (hD : ∀ r a b c, ParabolicC0AlphaOn α (fun z => D r z a b c) K)
    (hE : ∀ r a b c, ParabolicC0AlphaOn α (fun z => E r z a b c) K)
    (hDdiff : ∀ r a b c,
      ParabolicC0AlphaOn α (fun z => D r z a b c - E r z a b c) K)
    (hKc : ∀ r a b i j, ParabolicC0AlphaOn α (fun z => Kc r z a b i j) K)
    (hHdiff : ∀ r a b i j,
      ParabolicC0AlphaOn α (fun z => Hc r z a b i j - Kc r z a b i j) K)
    (hdetM_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (M r z).det ≠ 0)
    (hdetN_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (N r z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M r z).det‖) ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(N r z).det‖) ∧
      ∀ r,
        ParabolicC0AlphaOn α
          (fun z : ℝ × X =>
            ricciDeTurckSchematicMatrix (M r z) (D r z) (Hc r z) -
              ricciDeTurckSchematicMatrix (N r z) (E r z) (Kc r z)) K := by
  rcases matrix_det_pair_family_exists_pos_norm_lower_bound_of_isCompact
      (K := K) (M := M) (N := N) hK hα hM hN hdetM_ne hdetN_ne with
    ⟨δ, hδpos, hdetM, hdetN⟩
  refine ⟨δ, hδpos, hdetM, hdetN, ?_⟩
  intro r
  exact ricciDeTurckSchematicMatrix_sub_entrywise
    (M := M r) (N := N r) (D := D r) (E := E r) (Hc := Hc r) (Kc := Kc r)
    (hM r) (hN r) (hMdiff r) (hD r) (hE r) (hDdiff r) (hKc r) (hHdiff r)
    hδpos (hdetM r) (hdetN r)

/-- Local finite product-cylinder primitive-difference estimates globalize finite-family compact
schematic Ricci-DeTurck RHS difference closure, with one determinant lower bound shared by both
metric families. -/
theorem ricciDeTurckSchematicMatrix_sub_entrywise_family_of_finset_parabolicCylinder_cover_closedCylinder_variable
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {K : Set (ℝ × X)}
    {M N : κ → ℝ × X → Matrix n n 𝕜}
    {D E : κ → ℝ × X → n → n → n → 𝕜}
    {Hc Kc : κ → ℝ × X → n → n → n → n → 𝕜}
    (S : Finset (ℝ × X)) (timeRadius spaceRadius : ℝ × X → ℝ)
    (hK : IsCompact K) (hα : 0 < α)
    (htime_pos : ∀ y ∈ S, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ S, 0 < spaceRadius y)
    (hcover : K ⊆ ⋃ y ∈ S, parabolicCylinder y (timeRadius y) (spaceRadius y))
    (hMlocal : ∀ y ∈ S, ∀ r a b,
      ParabolicC0AlphaOn α (fun z => M r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hNlocal : ∀ y ∈ S, ∀ r a b,
      ParabolicC0AlphaOn α (fun z => N r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hMdiffLocal : ∀ y ∈ S, ∀ r a b,
      ParabolicC0AlphaOn α (fun z => M r z a b - N r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hDlocal : ∀ y ∈ S, ∀ r a b c,
      ParabolicC0AlphaOn α (fun z => D r z a b c)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hElocal : ∀ y ∈ S, ∀ r a b c,
      ParabolicC0AlphaOn α (fun z => E r z a b c)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hDdiffLocal : ∀ y ∈ S, ∀ r a b c,
      ParabolicC0AlphaOn α (fun z => D r z a b c - E r z a b c)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hKclocal : ∀ y ∈ S, ∀ r a b i j,
      ParabolicC0AlphaOn α (fun z => Kc r z a b i j)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hHdiffLocal : ∀ y ∈ S, ∀ r a b i j,
      ParabolicC0AlphaOn α (fun z => Hc r z a b i j - Kc r z a b i j)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hdetM_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (M r z).det ≠ 0)
    (hdetN_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (N r z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M r z).det‖) ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(N r z).det‖) ∧
      ∀ r,
        ParabolicC0AlphaOn α
          (fun z : ℝ × X =>
            ricciDeTurckSchematicMatrix (M r z) (D r z) (Hc r z) -
              ricciDeTurckSchematicMatrix (N r z) (E r z) (Kc r z)) K := by
  have hM : ∀ r a b, ParabolicC0AlphaOn α (fun z => M r z a b) K := by
    intro r a b
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hMlocal y hy r a b)
  have hN : ∀ r a b, ParabolicC0AlphaOn α (fun z => N r z a b) K := by
    intro r a b
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hNlocal y hy r a b)
  have hMdiff : ∀ r a b, ParabolicC0AlphaOn α (fun z => M r z a b - N r z a b) K := by
    intro r a b
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hMdiffLocal y hy r a b)
  have hD : ∀ r a b c, ParabolicC0AlphaOn α (fun z => D r z a b c) K := by
    intro r a b c
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hDlocal y hy r a b c)
  have hE : ∀ r a b c, ParabolicC0AlphaOn α (fun z => E r z a b c) K := by
    intro r a b c
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hElocal y hy r a b c)
  have hDdiff : ∀ r a b c,
      ParabolicC0AlphaOn α (fun z => D r z a b c - E r z a b c) K := by
    intro r a b c
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hDdiffLocal y hy r a b c)
  have hKc : ∀ r a b i j, ParabolicC0AlphaOn α (fun z => Kc r z a b i j) K := by
    intro r a b i j
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hKclocal y hy r a b i j)
  have hHdiff : ∀ r a b i j,
      ParabolicC0AlphaOn α (fun z => Hc r z a b i j - Kc r z a b i j) K := by
    intro r a b i j
    exact ParabolicC0AlphaOn.of_finset_parabolicCylinder_cover_closedCylinder_variable
      S timeRadius spaceRadius hα htime_pos hspace_pos hcover
      (fun y hy => hHdiffLocal y hy r a b i j)
  exact ricciDeTurckSchematicMatrix_sub_entrywise_family_of_isCompact_det_ne_zero
    (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
    hK hα hM hN hMdiff hD hE hDdiff hKc hHdiff hdetM_ne hdetN_ne

/-- Point-dependent local product-cylinder primitive-difference estimates globalize finite-family
compact schematic Ricci-DeTurck RHS difference closure, with one determinant lower bound shared by
both metric families. -/
theorem ricciDeTurckSchematicMatrix_sub_entrywise_family_of_isCompact_of_local_closedCylinder_variable
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {K : Set (ℝ × X)}
    {M N : κ → ℝ × X → Matrix n n 𝕜}
    {D E : κ → ℝ × X → n → n → n → 𝕜}
    {Hc Kc : κ → ℝ × X → n → n → n → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (timeRadius spaceRadius : ℝ × X → ℝ)
    (htime_pos : ∀ y ∈ K, 0 < timeRadius y)
    (hspace_pos : ∀ y ∈ K, 0 < spaceRadius y)
    (hMlocal : ∀ y ∈ K, ∀ r a b,
      ParabolicC0AlphaOn α (fun z => M r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hNlocal : ∀ y ∈ K, ∀ r a b,
      ParabolicC0AlphaOn α (fun z => N r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hMdiffLocal : ∀ y ∈ K, ∀ r a b,
      ParabolicC0AlphaOn α (fun z => M r z a b - N r z a b)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hDlocal : ∀ y ∈ K, ∀ r a b c,
      ParabolicC0AlphaOn α (fun z => D r z a b c)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hElocal : ∀ y ∈ K, ∀ r a b c,
      ParabolicC0AlphaOn α (fun z => E r z a b c)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hDdiffLocal : ∀ y ∈ K, ∀ r a b c,
      ParabolicC0AlphaOn α (fun z => D r z a b c - E r z a b c)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hKclocal : ∀ y ∈ K, ∀ r a b i j,
      ParabolicC0AlphaOn α (fun z => Kc r z a b i j)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hHdiffLocal : ∀ y ∈ K, ∀ r a b i j,
      ParabolicC0AlphaOn α (fun z => Hc r z a b i j - Kc r z a b i j)
        (parabolicClosedCylinder y (2 * timeRadius y) (2 * spaceRadius y)))
    (hdetM_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (M r z).det ≠ 0)
    (hdetN_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (N r z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M r z).det‖) ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(N r z).det‖) ∧
      ∀ r,
        ParabolicC0AlphaOn α
          (fun z : ℝ × X =>
            ricciDeTurckSchematicMatrix (M r z) (D r z) (Hc r z) -
              ricciDeTurckSchematicMatrix (N r z) (E r z) (Kc r z)) K := by
  have hM : ∀ r a b, ParabolicC0AlphaOn α (fun z => M r z a b) K := by
    intro r a b
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hK hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hMlocal y hy r a b)
  have hN : ∀ r a b, ParabolicC0AlphaOn α (fun z => N r z a b) K := by
    intro r a b
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hK hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hNlocal y hy r a b)
  have hMdiff : ∀ r a b, ParabolicC0AlphaOn α (fun z => M r z a b - N r z a b) K := by
    intro r a b
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hK hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hMdiffLocal y hy r a b)
  have hD : ∀ r a b c, ParabolicC0AlphaOn α (fun z => D r z a b c) K := by
    intro r a b c
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hK hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hDlocal y hy r a b c)
  have hE : ∀ r a b c, ParabolicC0AlphaOn α (fun z => E r z a b c) K := by
    intro r a b c
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hK hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hElocal y hy r a b c)
  have hDdiff : ∀ r a b c,
      ParabolicC0AlphaOn α (fun z => D r z a b c - E r z a b c) K := by
    intro r a b c
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hK hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hDdiffLocal y hy r a b c)
  have hKc : ∀ r a b i j, ParabolicC0AlphaOn α (fun z => Kc r z a b i j) K := by
    intro r a b i j
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hK hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hKclocal y hy r a b i j)
  have hHdiff : ∀ r a b i j,
      ParabolicC0AlphaOn α (fun z => Hc r z a b i j - Kc r z a b i j) K := by
    intro r a b i j
    exact ParabolicC0AlphaOn.of_isCompact_of_local_closedCylinder_variable
      hK hα timeRadius spaceRadius htime_pos hspace_pos
      (fun y hy => hHdiffLocal y hy r a b i j)
  exact ricciDeTurckSchematicMatrix_sub_entrywise_family_of_isCompact_det_ne_zero
    (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
    hK hα hM hN hMdiff hD hE hDdiff hKc hHdiff hdetM_ne hdetN_ne

/-- Existential point-local product-cylinder primitive-difference estimates globalize
finite-family compact schematic Ricci-DeTurck RHS difference closure, with one determinant lower
bound shared by both metric families. -/
theorem ricciDeTurckSchematicMatrix_sub_entrywise_family_of_isCompact_of_exists_local_closedCylinder
    {κ n 𝕜 : Type*} [Fintype κ] [Fintype n] [DecidableEq n] [NormedField 𝕜]
    {K : Set (ℝ × X)}
    {M N : κ → ℝ × X → Matrix n n 𝕜}
    {D E : κ → ℝ × X → n → n → n → 𝕜}
    {Hc Kc : κ → ℝ × X → n → n → n → n → 𝕜}
    (hK : IsCompact K) (hα : 0 < α)
    (hlocal : ∀ y ∈ K, ∃ timeRadius > 0, ∃ spaceRadius > 0,
      (∀ r a b,
        ParabolicC0AlphaOn α (fun z => M r z a b)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ r a b,
        ParabolicC0AlphaOn α (fun z => N r z a b)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ r a b,
        ParabolicC0AlphaOn α (fun z => M r z a b - N r z a b)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ r a b c,
        ParabolicC0AlphaOn α (fun z => D r z a b c)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ r a b c,
        ParabolicC0AlphaOn α (fun z => E r z a b c)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ r a b c,
        ParabolicC0AlphaOn α (fun z => D r z a b c - E r z a b c)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ r a b i j,
        ParabolicC0AlphaOn α (fun z => Kc r z a b i j)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))) ∧
      (∀ r a b i j,
        ParabolicC0AlphaOn α (fun z => Hc r z a b i j - Kc r z a b i j)
          (parabolicClosedCylinder y (2 * timeRadius) (2 * spaceRadius))))
    (hdetM_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (M r z).det ≠ 0)
    (hdetN_ne : ∀ r ⦃z : ℝ × X⦄, z ∈ K → (N r z).det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(M r z).det‖) ∧
      (∀ r ⦃z : ℝ × X⦄, z ∈ K → δ ≤ ‖(N r z).det‖) ∧
      ∀ r,
        ParabolicC0AlphaOn α
          (fun z : ℝ × X =>
            ricciDeTurckSchematicMatrix (M r z) (D r z) (Hc r z) -
              ricciDeTurckSchematicMatrix (N r z) (E r z) (Kc r z)) K := by
  have hM : ∀ r a b, ParabolicC0AlphaOn α (fun z => M r z a b) K := by
    intro r a b
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hK hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.1 r a b⟩)
  have hN : ∀ r a b, ParabolicC0AlphaOn α (fun z => N r z a b) K := by
    intro r a b
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hK hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.2.1 r a b⟩)
  have hMdiff : ∀ r a b, ParabolicC0AlphaOn α (fun z => M r z a b - N r z a b) K := by
    intro r a b
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hK hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.2.2.1 r a b⟩)
  have hD : ∀ r a b c, ParabolicC0AlphaOn α (fun z => D r z a b c) K := by
    intro r a b c
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hK hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.2.2.2.1 r a b c⟩)
  have hE : ∀ r a b c, ParabolicC0AlphaOn α (fun z => E r z a b c) K := by
    intro r a b c
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hK hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.2.2.2.2.1 r a b c⟩)
  have hDdiff : ∀ r a b c,
      ParabolicC0AlphaOn α (fun z => D r z a b c - E r z a b c) K := by
    intro r a b c
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hK hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.2.2.2.2.2.1 r a b c⟩)
  have hKc : ∀ r a b i j, ParabolicC0AlphaOn α (fun z => Kc r z a b i j) K := by
    intro r a b i j
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hK hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace, hdata.2.2.2.2.2.2.1 r a b i j⟩)
  have hHdiff : ∀ r a b i j,
      ParabolicC0AlphaOn α (fun z => Hc r z a b i j - Kc r z a b i j) K := by
    intro r a b i j
    exact ParabolicC0AlphaOn.of_isCompact_of_exists_local_closedCylinder hK hα
      (fun y hy => by
        rcases hlocal y hy with ⟨timeRadius, htime, spaceRadius, hspace, hdata⟩
        exact ⟨timeRadius, htime, spaceRadius, hspace,
          hdata.2.2.2.2.2.2.2 r a b i j⟩)
  exact ricciDeTurckSchematicMatrix_sub_entrywise_family_of_isCompact_det_ne_zero
    (M := M) (N := N) (D := D) (E := E) (Hc := Hc) (Kc := Kc)
    hK hα hM hN hMdiff hD hE hDdiff hKc hHdiff hdetM_ne hdetN_ne

end ParabolicC0AlphaOn

namespace parabolicC0AlphaSubmodule

variable {X : Type*} [PseudoMetricSpace X]
variable {α : ℝ} {s : Set (ℝ × X)}

/-- Coordinate projection from a matrix-valued parabolic `C^{0,α}` submodule. -/
def matrixApplyLinearMap {m n A : Type*} [Fintype m] [Fintype n]
    [NormedAddCommGroup A] [NormedSpace ℝ A] (i : m) (j : n) :
    parabolicC0AlphaSubmodule X (Matrix m n A) α s →ₗ[ℝ]
      parabolicC0AlphaSubmodule X A α s :=
  continuousLinearMap (X := X) (E := Matrix m n A) (α := α) (s := s)
    ((ContinuousLinearMap.proj j : (n → A) →L[ℝ] A).comp
      (ContinuousLinearMap.proj i : Matrix m n A →L[ℝ] n → A))

@[simp]
theorem matrixApplyLinearMap_apply {m n A : Type*} [Fintype m] [Fintype n]
    [NormedAddCommGroup A] [NormedSpace ℝ A] (i : m) (j : n)
    (u : parabolicC0AlphaSubmodule X (Matrix m n A) α s) (z : ℝ × X) :
    matrixApplyLinearMap (X := X) (α := α) (s := s) i j u z = u z i j :=
  rfl

/-- Assemble matrix-valued parabolic `C^{0,α}` submodule elements from their entries. -/
def matrixOfEntriesLinearMap {m n A : Type*} [Fintype m] [Fintype n]
    [NormedAddCommGroup A] [NormedSpace ℝ A] :
    (m → n → parabolicC0AlphaSubmodule X A α s) →ₗ[ℝ]
      parabolicC0AlphaSubmodule X (Matrix m n A) α s where
  toFun u := ⟨fun z i j => u i j z,
    ParabolicC0AlphaOn.matrix_of_entries (X := X) (α := α) (s := s)
      fun i j => (u i j).2⟩
  map_add' := by
    intro u v
    ext z i j
    rfl
  map_smul' := by
    intro c u
    ext z i j
    rfl

@[simp]
theorem matrixOfEntriesLinearMap_apply {m n A : Type*} [Fintype m] [Fintype n]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    (u : m → n → parabolicC0AlphaSubmodule X A α s) (z : ℝ × X)
    (i : m) (j : n) :
    matrixOfEntriesLinearMap (X := X) (α := α) (s := s) u z i j = u i j z :=
  rfl

end parabolicC0AlphaSubmodule

end AnalyticPDE
end RicciFlow
