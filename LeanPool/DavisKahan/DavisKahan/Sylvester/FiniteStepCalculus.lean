/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.SelfAdjointBorelCalculus
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum


/-!
# Finite spectral-step calculus

This file provides the finite measurable functional-calculus identities used by
the separated Sylvester reconstruction.  It is independent of the compact-cover
construction: the compiler-side topology helpers only need to produce a finite
measurable disjoint cover and representatives.

**Promoted 2026-07-30 under lane `EXP-PROMOTE-SYL`** from
`DavisKahan/Experimental/InfiniteDimensional/Sylvester/FiniteStepCalculus.lean`,
into `defaultTargets` — which it was not compiled by before.  Nothing is
restated: every declaration keeps its name and its namespace
(`TauCeti.DavisKahanExt`).

**Why this one and not its six siblings.**  Promotion is not "the module
compiles"; `check_dependency_layers.py` rule 4 forbids production importing
`DavisKahan.*`, so the test is that the module's *transitive import
closure contains no Experimental module*.  Measured across the seven modules the
lane row listed as promotable, this is the only one that passes: it imports
`DavisKahan.SpectralTheory.SelfAdjointBorelCalculus` and nothing else.  The other
six carry 1, 2, 3, 4, 8 and 24 Experimental modules in closure and stay where
they are until those clear.
-/

namespace TauCeti
namespace DavisKahan.Sylvester

open TauCeti.DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open MeasureTheory Set Filter
open scoped InnerProductSpace BigOperators

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Complex-valued finite step symbol attached to measurable cells. -/
noncomputable def finiteStepSymbol {n : ℕ}
    (cell : Fin n → Set ℝ) (rep : Fin n → ℝ) : ℝ → ℂ :=
  fun x => ∑ i, Set.indicator (cell i) (fun _ => (rep i : ℂ)) x

/-- The finite step symbol is measurable. -/
theorem measurable_finiteStepSymbol {n : ℕ}
    (cell : Fin n → Set ℝ) (hcell : ∀ i, MeasurableSet (cell i))
    (rep : Fin n → ℝ) : Measurable (finiteStepSymbol cell rep) := by
  unfold finiteStepSymbol
  exact Finset.measurable_sum _ fun i _ => measurable_const.indicator (hcell i)

/-- A crude global bound for the finite step symbol. -/
theorem bounded_finiteStepSymbol {n : ℕ}
    (cell : Fin n → Set ℝ) (rep : Fin n → ℝ) :
    ∃ C : ℝ, ∀ x, ‖finiteStepSymbol cell rep x‖ ≤ C := by
  refine ⟨∑ i, |rep i|, fun x => ?_⟩
  unfold finiteStepSymbol
  calc
    ‖∑ i, Set.indicator (cell i) (fun _ => (rep i : ℂ)) x‖
        ≤ ∑ i, ‖Set.indicator (cell i) (fun _ => (rep i : ℂ)) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, |rep i| := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hx : x ∈ cell i
      · rw [Set.indicator_of_mem hx, Complex.norm_real, Real.norm_eq_abs]
      · rw [Set.indicator_of_notMem hx, norm_zero]
        exact abs_nonneg _

/-- Sums of globally bounded symbols are globally bounded. -/
theorem bounded_add {f g : ℝ → ℂ} (hf : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hg : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C) : ∃ C : ℝ, ∀ x, ‖f x + g x‖ ≤ C := by
  obtain ⟨Cf, hCf⟩ := hf
  obtain ⟨Cg, hCg⟩ := hg
  exact ⟨Cf + Cg, fun x => (norm_add_le _ _).trans (add_le_add (hCf x) (hCg x))⟩

/-- A scaled indicator symbol is globally bounded by the scale's norm. -/
theorem bounded_indicator_const (s : Set ℝ) (c : ℂ) :
    ∃ C : ℝ, ∀ x, ‖Set.indicator s (fun _ => c) x‖ ≤ C := by
  refine ⟨‖c‖, fun x => ?_⟩
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, norm_zero]
    exact norm_nonneg c

/-- The calculus of a single scaled indicator is the scaled spectral projection. -/
theorem boundedSelfAdjointBorelCalculusC_indicator_smul
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (s : Set ℝ) (hs : MeasurableSet s) (c : ℂ)
    (hm : Measurable (Set.indicator s fun _ => c))
    (hb : ∃ C : ℝ, ∀ x, ‖Set.indicator s (fun _ => c) x‖ ≤ C) :
    boundedSelfAdjointBorelCalculusC A hA (Set.indicator s fun _ => c) hm hb
      = c • boundedSelfAdjointSpectralProjection A hA s hs := by
  have hfun : (Set.indicator s fun _ => c) =
      fun x => c * Set.indicator s (fun _ => (1 : ℂ)) x := by
    funext x
    by_cases hx : x ∈ s <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  have hcm : Measurable (fun x => c * Set.indicator s (fun _ => (1 : ℂ)) x) :=
    measurable_const.mul (measurable_const.indicator hs)
  have hcb : ∃ C : ℝ, ∀ x, ‖c * Set.indicator s (fun _ => (1 : ℂ)) x‖ ≤ C := by
    refine ⟨‖c‖, fun x => ?_⟩
    rw [norm_mul]
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx, norm_one, mul_one]
    · rw [Set.indicator_of_notMem hx, norm_zero, mul_zero]
      exact norm_nonneg c
  rw [boundedSelfAdjointBorelCalculusC_congr A hA hfun hm hb hcm hcb,
    boundedSelfAdjointBorelCalculusC_smul A hA c (measurable_const.indicator hs)
      (bounded_indicator_const s 1) hcm hcb,
    boundedSelfAdjointBorelCalculusC_indicator A hA s hs]

/-- The bounded calculus is additive over a finite step function. -/
theorem boundedSelfAdjointBorelCalculusC_finiteStep
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    {n : ℕ} (cell : Fin n → Set ℝ)
    (hcell : ∀ i, MeasurableSet (cell i)) (rep : Fin n → ℝ) :
    boundedSelfAdjointBorelCalculusC A hA
      (finiteStepSymbol cell rep)
      (measurable_finiteStepSymbol cell hcell rep)
      (bounded_finiteStepSymbol cell rep) =
      ∑ i, (rep i : ℂ) •
        boundedSelfAdjointSpectralProjection A hA (cell i) (hcell i) := by
  classical
  induction n with
  | zero =>
      rw [Finset.univ_eq_empty, Finset.sum_empty]
      have h0 : finiteStepSymbol cell rep = fun _ => (0 : ℂ) := by
        funext x; simp [finiteStepSymbol]
      rw [boundedSelfAdjointBorelCalculusC_congr A hA h0
        (measurable_finiteStepSymbol cell hcell rep) (bounded_finiteStepSymbol cell rep)
        measurable_const ⟨0, fun _ => by simp⟩]
      exact boundedSelfAdjointBorelCalculusC_zero A hA _ _
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      have hHm : Measurable (Set.indicator (cell 0) fun _ => (rep 0 : ℂ)) :=
        measurable_const.indicator (hcell 0)
      have hHb := bounded_indicator_const (cell 0) (rep 0 : ℂ)
      have hTm : Measurable
          (finiteStepSymbol (fun i => cell i.succ) (fun i => rep i.succ)) :=
        measurable_finiteStepSymbol (fun i => cell i.succ) (fun i => hcell i.succ)
          (fun i => rep i.succ)
      have hTb := bounded_finiteStepSymbol (fun i => cell i.succ) (fun i => rep i.succ)
      have hsplit : finiteStepSymbol cell rep = fun x =>
          Set.indicator (cell 0) (fun _ => (rep 0 : ℂ)) x +
            finiteStepSymbol (fun i => cell i.succ) (fun i => rep i.succ) x := by
        funext x
        simp only [finiteStepSymbol, Fin.sum_univ_succ]
      rw [boundedSelfAdjointBorelCalculusC_congr A hA hsplit
          (measurable_finiteStepSymbol cell hcell rep) (bounded_finiteStepSymbol cell rep)
          (hHm.add hTm) (bounded_add hHb hTb),
        boundedSelfAdjointBorelCalculusC_add A hA hHm hHb hTm hTb
          (hHm.add hTm) (bounded_add hHb hTb),
        boundedSelfAdjointBorelCalculusC_indicator_smul A hA (cell 0) (hcell 0) (rep 0 : ℂ) hHm hHb,
        ih (fun i => cell i.succ) (fun i => hcell i.succ) (fun i => rep i.succ)]

/-- Two measurable spectral projections depend only on the intersection of the
sets with the real spectrum. -/
theorem spectralPVM_proj_congr_of_inter_spectrum_eq
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    {s t : Set ℝ} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : s ∩ realSpectrum A = t ∩ realSpectrum A) :
    boundedSelfAdjointSpectralProjection A hA s hs =
      boundedSelfAdjointSpectralProjection A hA t ht := by
  rw [← boundedSelfAdjointBorelCalculusC_indicator A hA s hs,
    ← boundedSelfAdjointBorelCalculusC_indicator A hA t ht]
  apply boundedSelfAdjointBorelCalculusC_congr_on_spectrum A hA
  intro x hx
  have : x ∈ s ↔ x ∈ t := by
    have hmem : x ∈ s ∩ realSpectrum A ↔ x ∈ t ∩ realSpectrum A := by rw [hst]
    simpa [hx] using hmem
  by_cases hxs : x ∈ s
  · have hxt : x ∈ t := this.mp hxs
    simp [Set.indicator_of_mem hxs, Set.indicator_of_mem hxt]
  · have hxt : x ∉ t := fun h => hxs (this.mpr h)
    simp [Set.indicator_of_notMem hxs, Set.indicator_of_notMem hxt]

/-- Pairwise disjoint measurable cells give pairwise orthogonal spectral
projections. -/
theorem spectralProjection_pairwise_orthogonal
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    {n : ℕ} (cell : Fin n → Set ℝ)
    (hcell : ∀ i, MeasurableSet (cell i))
    (hdisj : Set.PairwiseDisjoint Set.univ cell) :
    ∀ i j, i ≠ j →
      boundedSelfAdjointSpectralProjection A hA (cell i) (hcell i) ∘L
        boundedSelfAdjointSpectralProjection A hA (cell j) (hcell j) = 0 := by
  intro i j hij
  let P := boundedSelfAdjointSpectralPVM A hA
  change P.proj (cell i) (hcell i) * P.proj (cell j) (hcell j) = 0
  rw [P.proj_inter]
  have hd : Disjoint (cell i) (cell j) := hdisj (Set.mem_univ i) (Set.mem_univ j) hij
  have hinter : cell i ∩ cell j = ∅ := Set.disjoint_iff_inter_eq_empty.mp hd
  exact (P.proj_congr hinter (hcell i |>.inter (hcell j)) MeasurableSet.empty).trans
    P.proj_empty

/-- Finite additivity of a projection-valued measure over a pairwise disjoint
family: the projection of the union is the sum of the projections. -/
theorem pvm_proj_iUnion_fin
    (P : TauCeti.ProjValMeasure H) {n : ℕ} (cell : Fin n → Set ℝ)
    (hcell : ∀ i, MeasurableSet (cell i))
    (hdisj : Set.PairwiseDisjoint Set.univ cell) :
    ∑ i, P.proj (cell i) (hcell i) =
      P.proj (⋃ i, cell i) (MeasurableSet.iUnion hcell) := by
  induction n with
  | zero =>
      rw [Finset.univ_eq_empty, Finset.sum_empty,
        P.proj_congr (show (⋃ i : Fin 0, cell i) = ∅ by simp)
          (MeasurableSet.iUnion hcell) MeasurableSet.empty, P.proj_empty]
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      have htaildisj : Set.PairwiseDisjoint Set.univ (fun i : Fin n => cell i.succ) := by
        intro i _ j _ hij
        exact hdisj (Set.mem_univ i.succ) (Set.mem_univ j.succ)
          (fun h => hij (Fin.succ_injective _ h))
      have hdisjHT : Disjoint (cell 0) (⋃ i : Fin n, cell i.succ) := by
        rw [Set.disjoint_iUnion_right]
        intro i
        exact hdisj (Set.mem_univ 0) (Set.mem_univ i.succ)
          (Ne.symm (Fin.succ_ne_zero i))
      have hset : (⋃ i : Fin (n + 1), cell i) = cell 0 ∪ ⋃ i : Fin n, cell i.succ := by
        ext x
        simp only [Set.mem_iUnion, Set.mem_union, Fin.exists_fin_succ]
      rw [ih (fun i : Fin n => cell i.succ) (fun i : Fin n => hcell i.succ) htaildisj,
        P.proj_congr hset (MeasurableSet.iUnion hcell)
          ((hcell 0).union (MeasurableSet.iUnion fun i : Fin n => hcell i.succ)),
        P.proj_union (hcell 0) (MeasurableSet.iUnion fun i : Fin n => hcell i.succ) hdisjHT]

/-- A finite disjoint spectral cover sums to the identity. -/
theorem spectralProjection_finset_sum_eq_id
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    {n : ℕ} (cell : Fin n → Set ℝ)
    (hcell : ∀ i, MeasurableSet (cell i))
    (hdisj : Set.PairwiseDisjoint Set.univ cell)
    (hcover : realSpectrum A ⊆ ⋃ i, cell i) :
    ∑ i, boundedSelfAdjointSpectralProjection A hA (cell i) (hcell i) =
      ContinuousLinearMap.id ℂ H := by
  let P := boundedSelfAdjointSpectralPVM A hA
  have hunion : P.proj (⋃ i, cell i) (MeasurableSet.iUnion hcell) =
      P.proj Set.univ MeasurableSet.univ := by
    apply spectralPVM_proj_congr_of_inter_spectrum_eq A hA
    ext x
    constructor
    · intro hx
      exact ⟨Set.mem_univ x, hx.2⟩
    · intro hx
      exact ⟨hcover hx.2, hx.2⟩
  rw [← P.proj_univ, ← hunion]
  exact pvm_proj_iUnion_fin P cell hcell hdisj

/-- Left multiplication by a spectral block selects its own coefficient from a
finite spectral step. -/
theorem spectralProjection_select_left
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    {n : ℕ} (cell : Fin n → Set ℝ)
    (hcell : ∀ i, MeasurableSet (cell i))
    (rep : Fin n → ℂ)
    (hdisj : Set.PairwiseDisjoint Set.univ cell) (i : Fin n) :
    boundedSelfAdjointSpectralProjection A hA (cell i) (hcell i) ∘L
      (∑ j, rep j • boundedSelfAdjointSpectralProjection A hA (cell j) (hcell j)) =
      rep i • boundedSelfAdjointSpectralProjection A hA (cell i) (hcell i) := by
  rw [ContinuousLinearMap.comp_finsetSum,
    Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · rw [ContinuousLinearMap.comp_smul]
    let P := boundedSelfAdjointSpectralPVM A hA
    change rep i • (P.proj (cell i) (hcell i) * P.proj (cell i) (hcell i)) =
      rep i • P.proj (cell i) (hcell i)
    rw [P.proj_idem]
  · intro j _ hji
    rw [ContinuousLinearMap.comp_smul,
      spectralProjection_pairwise_orthogonal A hA cell hcell hdisj i j hji.symm]
    simp

/-- Right multiplication by a spectral block selects its own coefficient. -/
theorem spectralProjection_select_right
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    {n : ℕ} (cell : Fin n → Set ℝ)
    (hcell : ∀ i, MeasurableSet (cell i))
    (rep : Fin n → ℂ)
    (hdisj : Set.PairwiseDisjoint Set.univ cell) (i : Fin n) :
    (∑ j, rep j • boundedSelfAdjointSpectralProjection A hA (cell j) (hcell j)) ∘L
      boundedSelfAdjointSpectralProjection A hA (cell i) (hcell i) =
      rep i • boundedSelfAdjointSpectralProjection A hA (cell i) (hcell i) := by
  rw [ContinuousLinearMap.finsetSum_comp,
    Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · rw [ContinuousLinearMap.smul_comp]
    let P := boundedSelfAdjointSpectralPVM A hA
    change rep i • (P.proj (cell i) (hcell i) * P.proj (cell i) (hcell i)) =
      rep i • P.proj (cell i) (hcell i)
    rw [P.proj_idem]
  · intro j _ hji
    rw [ContinuousLinearMap.smul_comp]
    have hzero := spectralProjection_pairwise_orthogonal A hA cell hcell hdisj j i hji
    rw [hzero]
    simp

open Classical in
/-- The choice-based real step symbol used by the original finite-step file. -/
noncomputable def chosenFiniteStepSymbol {n : ℕ}
    (cell : Fin n → Set ℝ) (rep : Fin n → ℝ) (x : ℝ) : ℝ :=
  if hx : ∃ i, x ∈ cell i then rep (Classical.choose hx) else x

/-- On a pairwise disjoint cover, the choice-based step symbol equals the
finite indicator sum at every covered point. -/
theorem chosenFiniteStepSymbol_eq {n : ℕ}
    (cell : Fin n → Set ℝ) (rep : Fin n → ℝ)
    (hdisj : Set.PairwiseDisjoint Set.univ cell)
    {x : ℝ} (hcover : x ∈ ⋃ i, cell i) :
    ((chosenFiniteStepSymbol cell rep x : ℝ) : ℂ) =
      finiteStepSymbol cell rep x := by
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hcover
  have hex : ∃ j, x ∈ cell j := ⟨i, hxi⟩
  have hxj : x ∈ cell (Classical.choose hex) := Classical.choose_spec hex
  have hji : Classical.choose hex = i := by
    by_contra hne
    exact Set.disjoint_left.mp
      (hdisj (Set.mem_univ (Classical.choose hex)) (Set.mem_univ i) hne) hxj hxi
  rw [chosenFiniteStepSymbol, dite_eq_left hex, hji, finiteStepSymbol, Finset.sum_eq_single i]
  · rw [Set.indicator_of_mem hxi]
  · intro k _ hki
    have hxk : x ∉ cell k := by
      intro hxk
      exact Set.disjoint_left.mp
        (hdisj (Set.mem_univ k) (Set.mem_univ i) hki) hxk hxi
    rw [Set.indicator_of_notMem hxk]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The choice-based real step symbol is measurable: it is the piecewise
combination of a finite measurable step function on the cover and the identity
off it. -/
theorem measurable_chosenFiniteStepSymbol {n : ℕ}
    (cell : Fin n → Set ℝ) (hcell : ∀ i, MeasurableSet (cell i))
    (hdisj : Set.PairwiseDisjoint Set.univ cell) (rep : Fin n → ℝ) :
    Measurable (chosenFiniteStepSymbol cell rep) := by
  classical
  have hstep : Measurable (fun x : ℝ => ∑ i, (cell i).indicator (fun _ => rep i) x) :=
    Finset.measurable_sum _ fun i _ => measurable_const.indicator (hcell i)
  have heq : chosenFiniteStepSymbol cell rep =
      (⋃ i, cell i).piecewise
        (fun x => ∑ i, (cell i).indicator (fun _ => rep i) x) (fun x => x) := by
    funext x
    by_cases hx : x ∈ ⋃ i, cell i
    · rw [Set.piecewise_eq_of_mem _ _ _ hx]
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      have hex : ∃ j, x ∈ cell j := ⟨i, hxi⟩
      have hxj : x ∈ cell (Classical.choose hex) := Classical.choose_spec hex
      have hji : Classical.choose hex = i := by
        by_contra hne
        exact Set.disjoint_left.mp
          (hdisj (Set.mem_univ (Classical.choose hex)) (Set.mem_univ i) hne) hxj hxi
      rw [chosenFiniteStepSymbol, dite_eq_left hex, hji, Finset.sum_eq_single i]
      · rw [Set.indicator_of_mem hxi]
      · intro k _ hki
        have hxk : x ∉ cell k := fun hxk =>
          Set.disjoint_left.mp
            (hdisj (Set.mem_univ k) (Set.mem_univ i) hki) hxk hxi
        rw [Set.indicator_of_notMem hxk]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    · rw [Set.piecewise_eq_of_notMem _ _ _ hx]
      have hnex : ¬ ∃ i, x ∈ cell i := fun ⟨i, hxi⟩ =>
        hx (Set.mem_iUnion.mpr ⟨i, hxi⟩)
      rw [chosenFiniteStepSymbol, dite_eq_right hnex]
  rw [heq]
  exact Measurable.piecewise (MeasurableSet.iUnion hcell) hstep measurable_id

/-- The exact finite-step Borel identity required by the Sylvester file. -/
theorem boundedSelfAdjointBorelCalculus_eq_finset_sum_indicator 
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    {n : ℕ} (cell : Fin n → Set ℝ)
    (hcell : ∀ i, MeasurableSet (cell i))
    (hdisj : Set.PairwiseDisjoint Set.univ cell)
    (rep : Fin n → ℝ)
    (hcover : realSpectrum A ⊆ ⋃ i, cell i) :
    boundedSelfAdjointBorelCalculus A hA
      (chosenFiniteStepSymbol cell rep)
      (measurable_chosenFiniteStepSymbol cell hcell hdisj rep)
      (by
        refine ⟨∑ i, |rep i|, Finset.sum_nonneg fun i _ => abs_nonneg _, fun x hx => ?_⟩
        have hcov := hcover hx
        obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hcov
        have hex : ∃ j, x ∈ cell j := ⟨i, hxi⟩
        rw [chosenFiniteStepSymbol, dite_eq_left hex]
        exact Finset.single_le_sum (fun j _ => abs_nonneg (rep j)) (Finset.mem_univ _)) =
      ∑ i, (rep i : ℂ) •
        boundedSelfAdjointSpectralProjection A hA (cell i) (hcell i) := by
  classical
  have hbounded : BoundedOnSpectrum A (chosenFiniteStepSymbol cell rep) := by
    refine ⟨∑ i, |rep i|, Finset.sum_nonneg fun i _ => abs_nonneg _, fun x hx => ?_⟩
    have hcov := hcover hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hcov
    have hex : ∃ j, x ∈ cell j := ⟨i, hxi⟩
    rw [chosenFiniteStepSymbol, dite_eq_left hex]
    exact Finset.single_le_sum (fun j _ => abs_nonneg (rep j)) (Finset.mem_univ _)
  change boundedSelfAdjointBorelCalculusC A hA
      (spectrumRestrictedSymbol A (chosenFiniteStepSymbol cell rep))
      (measurable_spectrumRestrictedSymbol A hA (chosenFiniteStepSymbol cell rep)
        (measurable_chosenFiniteStepSymbol cell hcell hdisj rep))
      (bounded_spectrumRestrictedSymbol A (chosenFiniteStepSymbol cell rep) hbounded) = _
  rw [boundedSelfAdjointBorelCalculusC_congr_on_spectrum A hA
      (measurable_spectrumRestrictedSymbol A hA (chosenFiniteStepSymbol cell rep)
        (measurable_chosenFiniteStepSymbol cell hcell hdisj rep))
      (bounded_spectrumRestrictedSymbol A (chosenFiniteStepSymbol cell rep) hbounded)
      (measurable_finiteStepSymbol cell hcell rep) (bounded_finiteStepSymbol cell rep)
      (by
        intro x hx
        rw [spectrumRestrictedSymbol, Set.indicator_of_mem hx]
        exact chosenFiniteStepSymbol_eq cell rep hdisj (hcover hx)),
    boundedSelfAdjointBorelCalculusC_finiteStep A hA cell hcell rep]

end
end DavisKahan.Sylvester
end TauCeti
