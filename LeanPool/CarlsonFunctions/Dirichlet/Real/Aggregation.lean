/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Real.Moments

public import Mathlib.Probability.Moments.Variance
public import LeanPool.CarlsonFunctions.Dirichlet.Real
public import LeanPool.CarlsonFunctions.StdSimplexMeasure.MomentDetermination

import LeanPool.CarlsonFunctions.Pochhammer.Gamma
import LeanPool.CarlsonFunctions.Pochhammer.Vandermonde
import all LeanPool.CarlsonFunctions.StdSimplexMeasure.Measure.Basic

/-! # Aggregation of the real Dirichlet distribution -/

open Real MeasureTheory MeasureTheory.Measure
open scoped ENNReal

@[expose] public noncomputable section DirichletDistribution

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]

open scoped Classical

/-- Aggregating a Dirichlet parameter vector along a surjection stays in the
positive parameter domain. -/
theorem mem_mvRealBetaDomain_stdSimplexAggregate
    {κ : Type*} [Fintype κ] {f : ι → κ} (hf : Function.Surjective f)
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) :
    stdSimplexAggregate f b ∈ mvRealBetaDomain :=
  stdSimplexAggregate_pos hf hb

/-- Coordinate aggregation is continuous, as a linear map on a finite product. -/
theorem continuous_stdSimplexAggregate {κ : Type*} [Fintype κ] (f : ι → κ) :
    Continuous (stdSimplexAggregate (R := ℝ) f) :=
  _root_.continuous_stdSimplexAggregate f

/-- Pushing a Dirichlet monomial forward under coordinate aggregation yields the
Dirichlet monomial for the aggregated parameters. This is the moment form of the
multinomial Chu–Vandermonde identity. -/
theorem integral_dirichletMeasure_comp_stdSimplexAggregate_monomial
    [Nonempty ι] {κ : Type*} [Fintype κ] {f : ι → κ} (hf : Function.Surjective f)
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (m : κ → ℕ) :
    ∫ u, (∏ k, stdSimplexAggregate f u k ^ m k) ∂(dirichletMeasure b) =
      ∫ v, (∏ k, v k ^ m k) ∂(dirichletMeasure (stdSimplexAggregate f b)) := by
  classical
  have : Nonempty κ := ⟨f (Classical.arbitrary ι)⟩
  let fiber (k : κ) : Finset ι := Finset.univ.filter (fun i => f i = k)
  have hAgg (u : ι → ℝ) (k : κ) :
      stdSimplexAggregate f u k = ∑ i ∈ fiber k, u i := by
    simp [fiber, stdSimplexAggregate, FunOnFinite.linearMap_apply_apply]
  have hb' : stdSimplexAggregate f b ∈ mvRealBetaDomain :=
    mem_mvRealBetaDomain_stdSimplexAggregate hf hb
  have hsum_b : ∑ i, b i = ∑ k, stdSimplexAggregate f b k := by
    simp_rw [hAgg]
    exact (Finset.sum_fiberwise (Finset.univ : Finset ι) f b).symm
  have hexpand (u : ι → ℝ) :
      ∏ k, stdSimplexAggregate f u k ^ m k =
        ∑ p ∈ Fintype.piFinset (fun k => Finset.piAntidiag (fiber k) (m k)),
          (∏ k, (Nat.multinomial (fiber k) (p k) : ℝ)) *
            ∏ i, u i ^ p (f i) i := by
    simp_rw [hAgg]
    have hbinoms (k : κ) :
        (∑ i ∈ fiber k, u i) ^ m k =
          ∑ α ∈ Finset.piAntidiag (fiber k) (m k),
            (Nat.multinomial (fiber k) α : ℝ) * ∏ i ∈ fiber k, u i ^ α i :=
      Finset.sum_pow_eq_sum_piAntidiag (fiber k) (fun i => u i) (m k)
    simp_rw [hbinoms]
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.prod_mul_distrib]
    congr 1
    have hcoord :
        ∏ k, ∏ i ∈ fiber k, u i ^ p k i =
          ∏ k, ∏ i ∈ fiber k, u i ^ p (f i) i := by
      refine Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun i hi => ?_
      have hik : f i = k := (Finset.mem_filter.mp hi).2
      simp [hik]
    rw [hcoord, Finset.prod_fiberwise (Finset.univ : Finset ι) f]
  have hdeg (p : κ → (ι → ℕ))
      (hp : p ∈ Fintype.piFinset (fun k => Finset.piAntidiag (fiber k) (m k))) :
      ∑ i, p (f i) i = ∑ k, m k := by
    have hp' : ∀ k, p k ∈ Finset.piAntidiag (fiber k) (m k) := by
      simpa [Fintype.mem_piFinset] using hp
    calc
      ∑ i, p (f i) i
          = ∑ k, ∑ i ∈ fiber k, p (f i) i :=
            (Finset.sum_fiberwise (Finset.univ : Finset ι) f
              (fun i => p (f i) i)).symm
      _ = ∑ k, ∑ i ∈ fiber k, p k i := by
            refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i hi => ?_
            have hik : f i = k := (Finset.mem_filter.mp hi).2
            simp [hik]
      _ = ∑ k, m k := by
            refine Finset.sum_congr rfl fun k _ => ?_
            exact (Finset.mem_piAntidiag.mp (hp' k)).1
  have hsum_pos : 0 < ∑ i, b i :=
    Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  have hDpos :
      0 < (ascPochhammer ℝ (∑ k, m k)).eval (∑ i, b i) := by
    rw [← gamma_add_nat_div_gamma_eq_ascPochhammer _ hsum_pos]
    positivity
  have hDne : (ascPochhammer ℝ (∑ k, m k)).eval (∑ i, b i) ≠ 0 := ne_of_gt hDpos
  have hN (p : κ → (ι → ℕ)) :
      ∏ i, (ascPochhammer ℝ (p (f i) i)).eval (b i) =
        ∏ k, ∏ i ∈ fiber k, (ascPochhammer ℝ (p k i)).eval (b i) := by
    have hcoord :
        ∏ k, ∏ i ∈ fiber k, (ascPochhammer ℝ (p (f i) i)).eval (b i) =
          ∏ k, ∏ i ∈ fiber k, (ascPochhammer ℝ (p k i)).eval (b i) := by
      refine Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun i hi => ?_
      have hik : f i = k := (Finset.mem_filter.mp hi).2
      simp [hik]
    rw [← hcoord, Finset.prod_fiberwise (Finset.univ : Finset ι) f]
  rw [integral_congr_ae (Filter.Eventually.of_forall hexpand)]
  have hterm (p : κ → (ι → ℕ)) :
      Integrable (fun u : ι → ℝ =>
        (∏ k, (Nat.multinomial (fiber k) (p k) : ℝ)) *
          ∏ i, u i ^ p (f i) i) (dirichletMeasure b) := by
    let : IsProbabilityMeasure (dirichletMeasure b) :=
      isProbabilityMeasure_dirichletMeasure hb
    exact (integrable_of_continuous_of_restrict_stdSimplex
      (dirichletMeasure_restrict b) (by fun_prop)).const_mul _
  rw [integral_finsetSum _ fun p _ => hterm p]
  simp_rw [integral_const_mul]
  have hsum :
      ∑ p ∈ Fintype.piFinset (fun k => Finset.piAntidiag (fiber k) (m k)),
          (∏ k, (Nat.multinomial (fiber k) (p k) : ℝ)) *
            ∫ u, (∏ i, u i ^ p (f i) i) ∂(dirichletMeasure b) =
        (∏ k, (ascPochhammer ℝ (m k)).eval (stdSimplexAggregate f b k)) /
          (ascPochhammer ℝ (∑ k, m k)).eval (∑ i, b i) := by
    have hinter (p : κ → ι → ℕ)
        (hp : p ∈ Fintype.piFinset (fun k => Finset.piAntidiag (fiber k) (m k))) :
        ∫ u, (∏ i, u i ^ p (f i) i) ∂(dirichletMeasure b) =
          (∏ i, (ascPochhammer ℝ (p (f i) i)).eval (b i)) /
            (ascPochhammer ℝ (∑ k, m k)).eval (∑ i, b i) := by
      rw [integral_dirichletMeasure_monomial hb (fun i => p (f i) i), hdeg p hp]
    have h1 :
        ∑ p ∈ Fintype.piFinset (fun k => Finset.piAntidiag (fiber k) (m k)),
            (∏ k, (Nat.multinomial (fiber k) (p k) : ℝ)) *
              ∫ u, (∏ i, u i ^ p (f i) i) ∂(dirichletMeasure b) =
          ∑ p ∈ Fintype.piFinset (fun k => Finset.piAntidiag (fiber k) (m k)),
            (∏ k, (Nat.multinomial (fiber k) (p k) : ℝ)) *
              ((∏ i, (ascPochhammer ℝ (p (f i) i)).eval (b i)) /
                (ascPochhammer ℝ (∑ k, m k)).eval (∑ i, b i)) :=
      Finset.sum_congr rfl fun p hp => by rw [hinter p hp]
    rw [h1]
    have hvander :
        ∑ p ∈ Fintype.piFinset (fun k => Finset.piAntidiag (fiber k) (m k)),
            (∏ k, (Nat.multinomial (fiber k) (p k) : ℝ)) *
              ∏ i, (ascPochhammer ℝ (p (f i) i)).eval (b i) =
          ∏ k, (ascPochhammer ℝ (m k)).eval (stdSimplexAggregate f b k) := by
      have hprod (p : κ → ι → ℕ) :
          (∏ k, (Nat.multinomial (fiber k) (p k) : ℝ)) *
              ∏ i, (ascPochhammer ℝ (p (f i) i)).eval (b i) =
            ∏ k, ((Nat.multinomial (fiber k) (p k) : ℝ) *
              ∏ i ∈ fiber k, (ascPochhammer ℝ (p k i)).eval (b i)) := by
        rw [hN p, ← Finset.prod_mul_distrib]
      rw [Finset.sum_congr rfl fun p _ => hprod p]
      rw [← Finset.prod_univ_sum
        (t := fun k => Finset.piAntidiag (fiber k) (m k))
        (f := fun k α =>
          (Nat.multinomial (fiber k) α : ℝ) *
            ∏ i ∈ fiber k, (ascPochhammer ℝ (α i)).eval (b i))]
      refine Finset.prod_congr rfl fun k _ => ?_
      simpa [hAgg] using
        (ascPochhammer_eval_sum (fiber k) b (m k)).symm
    have h2 :
        ∑ p ∈ Fintype.piFinset (fun k => Finset.piAntidiag (fiber k) (m k)),
            (∏ k, (Nat.multinomial (fiber k) (p k) : ℝ)) *
              ((∏ i, (ascPochhammer ℝ (p (f i) i)).eval (b i)) /
                (ascPochhammer ℝ (∑ k, m k)).eval (∑ i, b i)) =
          (∑ p ∈ Fintype.piFinset (fun k => Finset.piAntidiag (fiber k) (m k)),
              (∏ k, (Nat.multinomial (fiber k) (p k) : ℝ)) *
                ∏ i, (ascPochhammer ℝ (p (f i) i)).eval (b i)) /
            (ascPochhammer ℝ (∑ k, m k)).eval (∑ i, b i) := by
      have h2a :
          ∑ p ∈ Fintype.piFinset (fun k => Finset.piAntidiag (fiber k) (m k)),
              (∏ k, (Nat.multinomial (fiber k) (p k) : ℝ)) *
                ((∏ i, (ascPochhammer ℝ (p (f i) i)).eval (b i)) /
                  (ascPochhammer ℝ (∑ k, m k)).eval (∑ i, b i)) =
            ∑ p ∈ Fintype.piFinset (fun k => Finset.piAntidiag (fiber k) (m k)),
              ((∏ k, (Nat.multinomial (fiber k) (p k) : ℝ)) *
                ∏ i, (ascPochhammer ℝ (p (f i) i)).eval (b i)) *
                ((ascPochhammer ℝ (∑ k, m k)).eval (∑ i, b i))⁻¹ :=
        Finset.sum_congr rfl fun p _ => by rw [div_eq_mul_inv, mul_assoc]
      rw [h2a, ← Finset.sum_mul, ← div_eq_mul_inv]
    rw [h2, hvander]
  rw [hsum, integral_dirichletMeasure_monomial hb' m, hsum_b]

/-- Dirichlet measure is closed under marginalisation or coarsening: pushing
`dirichletMeasure b` forward along `stdSimplexAggregate f` gives the Dirichlet
measure for the aggregated parameter vector. -/
theorem measurePreserving_stdSimplexAggregate_dirichletMeasure
    {κ : Type*} [Fintype κ] {f : ι → κ} (hf : Function.Surjective f)
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) :
    MeasurePreserving (stdSimplexAggregate f)
      (dirichletMeasure b) (dirichletMeasure (stdSimplexAggregate f b)) := by
  classical
  have hT : Continuous (stdSimplexAggregate (R := ℝ) f) :=
    continuous_stdSimplexAggregate f
  refine ⟨hT.measurable, ?_⟩
  cases isEmpty_or_nonempty ι with
  | inl _ =>
      have : IsEmpty κ := ⟨fun k => (hf k).elim fun a _ => isEmptyElim a⟩
      unfold dirichletMeasure
      simp [stdSimplexMeasure_empty]
  | inr _ =>
      have : Nonempty κ := ⟨f (Classical.arbitrary ι)⟩
      have hb' : stdSimplexAggregate f b ∈ mvRealBetaDomain :=
        mem_mvRealBetaDomain_stdSimplexAggregate hf hb
      let : IsProbabilityMeasure (dirichletMeasure b) :=
        isProbabilityMeasure_dirichletMeasure hb
      let : IsProbabilityMeasure (dirichletMeasure (stdSimplexAggregate f b)) :=
        isProbabilityMeasure_dirichletMeasure hb'
      refine eq_of_forall_monomial_integral_eq_of_restrict_stdSimplex ?_ ?_ ?_
      · refine Measure.restrict_eq_self_of_ae_mem ?_
        rw [ae_iff]
        change Measure.map (stdSimplexAggregate f) (dirichletMeasure b)
          (Convexity.StdSimplex.coordinateSet ℝ κ)ᶜ = 0
        rw [Measure.map_apply hT.measurable
          (Convexity.StdSimplex.isClosed_coordinateSet ℝ κ).measurableSet.compl]
        have hsub : Convexity.StdSimplex.coordinateSet ℝ ι ⊆ stdSimplexAggregate f ⁻¹' Convexity.StdSimplex.coordinateSet ℝ κ := by
          intro u hu
          exact stdSimplexAggregate_mem_stdSimplex hu
        refine measure_mono_null (fun u hu huι => hu (hsub huι)) ?_
        change dirichletMeasure b (Convexity.StdSimplex.coordinateSet ℝ ι)ᶜ = 0
        have hs := (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
        have h' := congrArg (fun η : Measure (ι → ℝ) => η (Convexity.StdSimplex.coordinateSet ℝ ι)ᶜ)
          (dirichletMeasure_restrict (ι := ι) b)
        rw [Measure.restrict_apply hs.compl] at h'
        simpa [Set.inter_compl_self] using h'.symm
      · exact dirichletMeasure_restrict _
      · intro m
        have hcont : Continuous (fun v : κ → ℝ => ∏ k, v k ^ m k) := by fun_prop
        rw [integral_map hT.aemeasurable hcont.aestronglyMeasurable]
        exact integral_dirichletMeasure_comp_stdSimplexAggregate_monomial hf hb m

/-- Coordinate aggregation restated via the explicit density, unfolding
`measurePreserving_stdSimplexAggregate_dirichletMeasure` in terms of `stdSimplexMeasure` and
`dirichletPdf` directly rather than the bundled `dirichletMeasure`. -/
theorem stdSimplexAggregate_withDensity
    {κ : Type*} [Fintype κ] {f : ι → κ} (hf : Function.Surjective f)
    {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) :
    Measure.map (stdSimplexAggregate f)
      (stdSimplexMeasure.withDensity (fun u ↦ ENNReal.ofReal (dirichletPdfReal b u))) =
      stdSimplexMeasure.withDensity
        (fun v ↦ ENNReal.ofReal (dirichletPdfReal (stdSimplexAggregate f b) v)) :=
  (measurePreserving_stdSimplexAggregate_dirichletMeasure hf hb).map_eq

end ProbabilityTheory

end DirichletDistribution
