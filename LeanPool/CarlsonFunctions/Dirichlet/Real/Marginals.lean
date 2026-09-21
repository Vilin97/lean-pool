/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Real.Aggregation

public import Mathlib.Probability.Distributions.Beta
public import Mathlib.Probability.Moments.Variance
public import LeanPool.CarlsonFunctions.Dirichlet.Real
public import LeanPool.CarlsonFunctions.StdSimplexMeasure.MomentDetermination

import LeanPool.CarlsonFunctions.Pochhammer.Gamma
import LeanPool.CarlsonFunctions.Pochhammer.Vandermonde
import all LeanPool.CarlsonFunctions.StdSimplexMeasure.Measure.Basic

/-! # Beta marginals of the real Dirichlet distribution -/

open Real MeasureTheory MeasureTheory.Measure
open scoped ENNReal

@[expose] public noncomputable section DirichletDistribution

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]


/- Specializations to the two-variable Dirichlet (Beta) density and measure that is defined
in Mathlib `ProbabilityTheory.betaMeasure`. -/

/-- For two parameters, `mvRealBetaDomain` is just positivity of both parameters. -/
@[simp] theorem mem_mvRealBetaDomain_fin_two (α β : ℝ) :
    (![α, β] : Fin 2 → ℝ) ∈ mvRealBetaDomain ↔
      0 < α ∧ 0 < β := by
  simp [mvRealBetaDomain]

/-- In the two-variable case, `mvRealBeta` is the ordinary beta function. -/
@[simp] theorem mvRealBeta_fin_two (α β : ℝ) :
    mvRealBeta (![α, β] : Fin 2 → ℝ) = beta α β := by
  simp [mvRealBeta, beta]

/-- Under `x ↦ ![x, 1 - x]`, the relative interior of the two-coordinate simplex
corresponds to the open unit interval. -/
@[simp] theorem mem_stdSimplexInterior_fin_two (x : ℝ) :
    (![x, 1 - x] : Fin 2 → ℝ) ∈ stdSimplexInterior ↔
      0 < x ∧ x < 1 := by
  constructor
  · intro h
    constructor
    · simpa using h.2 (0 : Fin 2)
    · have h1 : 0 < 1 - x := by
        simpa using h.2 (1 : Fin 2)
      exact sub_pos.mp h1
  · rintro ⟨hx0, hx1⟩
    constructor
    · change
        (∀ i : Fin 2, 0 ≤ (![x, 1 - x] : Fin 2 → ℝ) i) ∧
          ∑ i : Fin 2, (![x, 1 - x] : Fin 2 → ℝ) i = 1
      constructor
      · rw [Fin.forall_fin_two]
        constructor
        · simpa using hx0.le
        · simpa using (sub_pos.mpr hx1).le
      · simp
    · rw [Fin.forall_fin_two]
      constructor
      · simpa using hx0
      · simpa using sub_pos.mpr hx1

/-- The two-variable real Dirichlet density is the beta density under the
parametrization `x ↦ ![x, 1 - x]`. -/
@[simp] theorem dirichletPdfReal_fin_two (α β x : ℝ) :
    dirichletPdfReal (![α, β] : Fin 2 → ℝ) ![x, 1 - x] =
      betaPDFReal α β x := by
  rw [dirichletPdfReal, betaPDFReal, mvRealBeta_fin_two]
  by_cases hx : 0 < x ∧ x < 1
  · simp [hx, mul_assoc]
  · rw [ite_eq_right hx]
    simp [mem_stdSimplexInterior_fin_two, hx]

/-- The two-variable `ENNReal`-valued Dirichlet density is the beta density. -/
@[simp] theorem dirichletPdf_fin_two (α β x : ℝ) :
    dirichletPdf (![α, β] : Fin 2 → ℝ) ![x, 1 - x] = betaPDF α β x := by
  simp [dirichletPdf, betaPDF]

/-- Projection onto the first coordinate sends the coordinate measure on the
two-coordinate affine simplex to Lebesgue measure. -/
private theorem map_stdSimplexMeasure_fin_two :
    Measure.map (fun u : Fin 2 → ℝ => u 0)
      (stdSimplexMeasure (ι := Fin 2)) = volume := by
  let _ : DecidableEq (Fin 2) := Classical.decEq _
  rw [stdSimplexMeasure_eq_at (1 : Fin 2)]
  unfold stdSimplexMeasureAt
  rw [Measure.map_map]
  · let A := {j : Fin 2 // j ≠ 1}
    let e : A ≃ Fin 1 :=
      Fintype.equivOfCardEq (by simp [A, Fintype.card_subtype_compl])
    let T := MeasurableEquiv.piCongrLeft (fun _ : A => ℝ) e.symm
    have hT : Measure.map T volume = volume :=
      (volume_measurePreserving_piCongrLeft (fun _ : A => ℝ) e.symm).map_eq
    let U := MeasurableEquiv.funUnique (Fin 1) ℝ
    have hU : Measure.map U volume = volume :=
      (volume_preserving_funUnique (Fin 1) ℝ).map_eq
    rw [← hU]
    calc
      Measure.map ((fun u : Fin 2 → ℝ => u 0) ∘ stdSimplexCoordMap 1)
          (volume : Measure (A → ℝ)) =
          Measure.map ((fun u : Fin 2 → ℝ => u 0) ∘ stdSimplexCoordMap 1)
            (Measure.map T volume) := by rw [hT]
      _ = Measure.map
          (((fun u : Fin 2 → ℝ => u 0) ∘ stdSimplexCoordMap 1) ∘ T) volume :=
        Measure.map_map
          ((measurable_pi_apply 0).comp (measurable_stdSimplexCoordMap 1)) T.measurable
      _ = Measure.map U volume := by
        congr 1
        funext x
        simp only [Function.comp_apply]
        rw [stdSimplexCoordMap_apply_of_ne (R := ℝ) (1 : Fin 2) (0 : Fin 2) (by omega)]
        have he : (⟨0, by omega⟩ : A) = e.symm (e ⟨0, by omega⟩) := by simp
        rw [he, MeasurableEquiv.piCongrLeft_apply_apply]
        change x (e ⟨0, by omega⟩) = x default
        exact congrArg x (Subsingleton.elim _ _)
  · exact measurable_pi_apply 0
  · exact measurable_stdSimplexCoordMap (1 : Fin 2)

/-- The first-coordinate push-forward of a two-coordinate Dirichlet measure is Mathlib's
beta measure. -/
private theorem map_dirichletMeasure_fin_two_direct (a b : ℝ) :
    Measure.map (fun u : Fin 2 → ℝ => u 0)
      (dirichletMeasure (![a, b])) = betaMeasure a b := by
  let _ : DecidableEq (Fin 2) := Classical.decEq _
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply 0) hs]
  rw [dirichletMeasure, withDensity_apply _ ((measurable_pi_apply 0) hs)]
  rw [betaMeasure, withDensity_apply _ hs]
  rw [← map_stdSimplexMeasure_fin_two]
  rw [← lintegral_indicator hs]
  have hpdf : Measurable (betaPDF a b) :=
    ENNReal.measurable_ofReal.comp (measurable_betaPDFReal a b)
  rw [lintegral_map (hpdf.indicator hs) (measurable_pi_apply 0)]
  rw [← lintegral_indicator ((measurable_pi_apply 0) hs)]
  apply lintegral_congr_ae
  have hmem : ∀ᵐ u ∂(stdSimplexMeasure (ι := Fin 2)),
      u ∈ stdSimplexAffineSet (R := ℝ) := by
    rw [stdSimplexMeasure_restrict_stdSimplexAffineSet]
    exact self_mem_ae_restrict isClosed_stdSimplexAffineSet.measurableSet
  filter_upwards [hmem] with u hu
  by_cases hus : u ∈ (fun u : Fin 2 → ℝ => u 0) ⁻¹' s
  · simp only [Set.mem_preimage] at hus
    simp [hus]
    have hu1 : u 1 = 1 - u 0 := by
      have hsum : ∑ i, u i = 1 := mem_fintypeAffineCoords_iff_sum.mp hu
      simpa [Fin.sum_univ_two] using congrArg (fun x => x - u 0) hsum
    have huv : u = ![u 0, 1 - u 0] := by
      funext j
      fin_cases j <;> simp [hu1]
    rw [huv]
    exact dirichletPdf_fin_two a b _
  · simp only [Set.mem_preimage] at hus
    simp [hus]

open scoped Classical in
/-- Marginalization of the Dirichlet density with respect to the `i` coordinate. -/
theorem betaMarginal [Nontrivial ι] {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) (i : ι) :
    Measure.map (fun u ↦ u i) (dirichletMeasure b) =
      betaMeasure (b i) (∑ j ∈ Finset.univ.erase i, b j) := by
  classical
  let q : ι → Fin 2 := fun j => if j = i then 0 else 1
  have hq : Function.Surjective q := by
    intro k
    fin_cases k
    · exact ⟨i, by simp [q]⟩
    · obtain ⟨j, hji⟩ := exists_ne i
      exact ⟨j, by simp [q, hji]⟩
  have hcoord (u : ι → ℝ) : stdSimplexAggregate q u 0 = u i := by
    change (FunOnFinite.linearMap ℝ ℝ q) u 0 = u i
    rw [FunOnFinite.linearMap_apply_apply]
    have hfilter : Finset.univ.filter (fun x => q x = (0 : Fin 2)) = {i} := by
      ext j
      simp [q]
    rw [hfilter]
    simp
  have hparam : stdSimplexAggregate q b =
      (![b i, ∑ j ∈ Finset.univ.erase i, b j] : Fin 2 → ℝ) := by
    funext k
    fin_cases k
    · exact hcoord b
    · change (FunOnFinite.linearMap ℝ ℝ q) b 1 = _
      rw [FunOnFinite.linearMap_apply_apply]
      have hfilter : Finset.univ.filter (fun x => q x = (1 : Fin 2)) =
          Finset.univ.erase i := by
        ext j
        simp [q]
      rw [hfilter]
      simp
  have hp := measurePreserving_stdSimplexAggregate_dirichletMeasure hq hb
  calc
    Measure.map (fun u : ι → ℝ => u i) (dirichletMeasure b) =
        Measure.map (fun v : Fin 2 → ℝ => v 0)
          (Measure.map (stdSimplexAggregate q) (dirichletMeasure b)) := by
            rw [Measure.map_map]
            · congr 1
              funext u
              exact (hcoord u).symm
            · exact measurable_pi_apply 0
            · fun_prop
    _ = Measure.map (fun v : Fin 2 → ℝ => v 0)
          (dirichletMeasure (stdSimplexAggregate q b)) := by rw [hp.map_eq]
    _ = Measure.map (fun v : Fin 2 → ℝ => v 0)
          (dirichletMeasure (![b i, ∑ j ∈ Finset.univ.erase i, b j])) := by rw [hparam]
    _ = betaMeasure (b i) (∑ j ∈ Finset.univ.erase i, b j) :=
      map_dirichletMeasure_fin_two_direct _ _

/-- The push-forward of the two-variable Dirichlet measure under the first
coordinate is the beta measure. -/
theorem map_dirichletMeasure_fin_two
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    Measure.map (fun u : Fin 2 → ℝ => u 0)
      (dirichletMeasure (![α, β])) = betaMeasure α β := by
  have hb : (![α, β] : Fin 2 → ℝ) ∈ mvRealBetaDomain := by
    simpa using And.intro hα hβ
  simpa using
    (betaMarginal (b := (![α, β] : Fin 2 → ℝ)) hb (0 : Fin 2))

/- The Gamma-ratio characterization is proved in `Dirichlet.Gamma` as
`ProbabilityTheory.iIndepFun.hasLaw_dirichlet_of_gamma`, for any common positive rate.
That file also proves the law of the total and its independence from the ratios. -/

end ProbabilityTheory

end DirichletDistribution
