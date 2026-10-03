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

public import LeanPool.PoincareGeometry.AlmostSchur.EnergyCutoffGraph

/-! # Compact cutoff preserves admissible C¹ test-graph limits -/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Multiplication by a C¹ compact cutoff acts on the actual test graph by
the product rule, and hence preserves graph-closure admissibility. -/
theorem exists_cutoff_testGraph_operator {ι : Type*} (b : ι → E)
    (η : E → ℝ) (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η) :
    ∃ A : Lp ℝ 2 (volume : Measure E) →L[ℝ] Lp ℝ 2 (volume : Measure E),
    ∃ B : ι → Lp ℝ 2 (volume : Measure E) →L[ℝ] Lp ℝ 2 (volume : Measure E),
      (∀ u, A u =ᵐ[volume] (fun z => η z * u z)) ∧
      (∀ i u, B i u =ᵐ[volume] (fun z => fderiv ℝ η z (b i) * u z)) ∧
      ∀ (U : Set E) (p : Lp ℝ 2 (volume : Measure E) × (ι → Lp ℝ 2 (volume : Measure E))),
        p ∈ closure (c1SupportedTestGraph b U) →
        (A p.1, fun i => B i p.1 + A (p.2 i)) ∈
          closure (c1SupportedTestGraph b (tsupport η)) := by
  classical
  obtain ⟨C, hC⟩ := hcη.exists_bound_of_continuous hη.continuous
  let A := boundedL2Multiplier (μ := (volume : Measure E)) η hη.continuous.aestronglyMeasurable
    C (Eventually.of_forall hC)
  have hd (i : ι) : ∃ C : ℝ, ∀ z, ‖fderiv ℝ η z (b i)‖ ≤ C :=
    (hcη.fderiv_apply ℝ (b i)).exists_bound_of_continuous
      ((hη.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  choose Cd hCd using hd
  let B : ι → Lp ℝ 2 (volume : Measure E) →L[ℝ] Lp ℝ 2 (volume : Measure E) :=
    fun i => boundedL2Multiplier (fun z => fderiv ℝ η z (b i))
      (((hη.continuous_fderiv (by norm_num)).clm_apply continuous_const).aestronglyMeasurable)
      (Cd i) (Eventually.of_forall (hCd i))
  have hA (u) : A u =ᵐ[volume] (fun z => η z * u z) :=
    boundedL2Multiplier_ae_eq _ _ _ _ u
  have hB (i) (u) : B i u =ᵐ[volume] (fun z => fderiv ℝ η z (b i) * u z) :=
    boundedL2Multiplier_ae_eq _ _ _ _ u
  refine ⟨A, B, hA, hB, ?_⟩
  intro U p hp
  let F := fun q : Lp ℝ 2 (volume : Measure E) × (ι → Lp ℝ 2 (volume : Measure E)) =>
    (A q.1, fun i => B i q.1 + A (q.2 i))
  have hF : Continuous F := (A.continuous.comp continuous_fst).prodMk
    (continuous_pi fun i => ((B i).continuous.comp continuous_fst).add
      (A.continuous.comp ((continuous_apply i).comp continuous_snd)))
  apply closure_minimal (t := F ⁻¹' closure (c1SupportedTestGraph b (tsupport η))) ?_
    (isClosed_closure.preimage hF) hp
  intro q hq
  obtain ⟨φ, hφ, hcφ, _, hqφ, hqdφ⟩ := hq
  apply subset_closure
  refine ⟨fun z => η z * φ z, hη.mul hφ, hcη.mul_right,
    tsupport_mul_subset_left, ?_, ?_⟩
  · filter_upwards [hA q.1, hqφ] with z hz hφz
    exact hz.trans (by rw [hφz])
  · intro i
    filter_upwards [hB i q.1, hA (q.2 i), hqφ, hqdφ i,
      Lp.coeFn_add (B i q.1) (A (q.2 i))] with z hb ha hq hd hadd
    refine hadd.trans ?_
    rw [Pi.add_apply, hb, ha, hq, hd]
    have he := congrArg (fun T : E →L[ℝ] ℝ => T (b i))
      (fderiv_mul (hη.differentiable (by simp) z) (hφ.differentiable (by simp) z))
    change _ = fderiv ℝ (η * φ) z (b i)
    simpa [mul_comm, add_comm] using he.symm

end AlmostSchur
