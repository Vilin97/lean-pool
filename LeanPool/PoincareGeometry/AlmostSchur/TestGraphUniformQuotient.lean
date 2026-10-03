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

public import LeanPool.PoincareGeometry.AlmostSchur.TestGraphDifferenceQuotient
public import LeanPool.PoincareGeometry.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimateL2

/-! # Uniform difference-quotient bounds on actual C¹ graph closures

The compact-test estimate uses the attributed vendored FTC/Tonelli/Jensen
translation proof. Continuity then passes the estimate to the actual graph
closure, without postulating a weak Sobolev approximation theorem.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Parseval identifies the classical gradient's L² norm with the graph coordinates. -/
theorem norm_L2_gradient_eq_graph (b : OrthonormalBasis ι ℝ E)
    (φ : E → ℝ) (g : Lp E 2 (volume : Measure E))
    (D : ι → Lp ℝ 2 (volume : Measure E))
    (hg : g =ᵐ[volume] (fun z => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ φ z)))
    (hD : ∀ i, D i =ᵐ[volume] (fun z => fderiv ℝ φ z (b i))) :
    ‖g‖ = Real.sqrt (∑ i, ‖D i‖ ^ 2) := by
  have he : ‖g‖ ^ 2 = ∑ i, ‖D i‖ ^ 2 := by
    simp_rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    rw [← integral_finsetSum _ (fun i _ => L2.integrable_inner (D i) (D i))]
    apply integral_congr_ae
    filter_upwards [hg, ae_all_iff.mpr hD] with z hz hd
    simp only [real_inner_self_eq_norm_sq]
    rw [← b.repr.norm_map, EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    rw [OrthonormalBasis.repr_apply_apply, hz, real_inner_comm,
      InnerProductSpace.toDual_symm_apply, hd i, Real.norm_eq_abs, sq_abs]
  rw [← he, Real.sqrt_sq_eq_abs, abs_norm]

/-- The true compact-test bound is independent of the nonzero step size. -/
theorem norm_differenceQuotient_c1SupportedTestGraph_le (b : OrthonormalBasis ι ℝ E)
    {U : Set E} {p : Lp ℝ 2 (volume : Measure E) × (ι → Lp ℝ 2 (volume : Measure E))}
    (hp : p ∈ c1SupportedTestGraph (fun i => b i) U) (v : E) (h : ℝ) (hh : h ≠ 0) :
    ‖directionalDifferenceQuotient p.1 v h‖ ≤
      ‖v‖ * Real.sqrt (∑ i, ‖p.2 i‖ ^ 2) := by
  cases (BorelSpace.measurable_eq (α := E))
  let : MeasurableSpace E := borel E
  obtain ⟨φ, hφ, hc, hs, hpφ, hpd⟩ := hp
  let f : ↥(C1c (E := E)) := ⟨φ, hφ, hc⟩
  have hf : toL2 (μ := (volume : Measure E)) f = p.1 := by
    apply Lp.ext
    exact (memLp_of_mem_C1c (μ := (volume : Measure E)) f.property).coeFn_toLp.trans hpφ.symm
  have hg := norm_L2_gradient_eq_graph b φ (toL2Grad (μ := (volume : Measure E)) f) p.2
    (memLp_grad_of_mem_C1c (μ := (volume : Measure E)) f.property).coeFn_toLp hpd
  have ht := norm_translateL2_sub_toL2_le (μ := (volume : Measure E)) (h • v) f
  rw [hf, hg, norm_smul] at ht
  change ‖h⁻¹ • (translateL2 (μ := (volume : Measure E)) (h • v) p.1 - p.1)‖ ≤ _
  rw [norm_smul]
  calc
    _ ≤ ‖h⁻¹‖ * (‖h‖ * ‖v‖ * Real.sqrt (∑ i, ‖p.2 i‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left ht (norm_nonneg _)
    _ = _ := by rw [norm_inv]; field_simp

/-- Closedness passes the uniform estimate to genuine supported H¹ graph limits. -/
theorem norm_differenceQuotient_closure_c1SupportedTestGraph_le (b : OrthonormalBasis ι ℝ E)
    {U : Set E} {p : Lp ℝ 2 (volume : Measure E) × (ι → Lp ℝ 2 (volume : Measure E))}
    (hp : p ∈ closure (c1SupportedTestGraph (fun i => b i) U))
    (v : E) (h : ℝ) (hh : h ≠ 0) :
    ‖directionalDifferenceQuotient p.1 v h‖ ≤
      ‖v‖ * Real.sqrt (∑ i, ‖p.2 i‖ ^ 2) := by
  apply closure_minimal (t := {q | ‖directionalDifferenceQuotient q.1 v h‖ ≤
      ‖v‖ * Real.sqrt (∑ i, ‖q.2 i‖ ^ 2)}) ?_ ?_ hp
  · intro q hq
    exact norm_differenceQuotient_c1SupportedTestGraph_le b hq v h hh
  · apply isClosed_le
      (((directionalDifferenceQuotientL v h).continuous.comp continuous_fst).norm)
    exact continuous_const.mul ((continuous_finsetSum _ (fun i _ =>
      (((continuous_apply i).comp continuous_snd).norm.pow 2))).sqrt)

end AlmostSchur
