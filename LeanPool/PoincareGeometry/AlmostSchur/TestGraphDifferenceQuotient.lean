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
public import LeanPool.PoincareGeometry.AlmostSchur.DifferenceQuotientAlgebra

/-! # Admissibility of fixed-step difference quotients of C¹ test-graph limits -/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Actual classical quotient of a C¹ function is C¹. -/
theorem contDiff_test_differenceQuotient {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ)
    (v : E) (h : ℝ) :
    ContDiff ℝ 1 (fun z => h⁻¹ * (φ (z + h • v) - φ z)) :=
  contDiff_const.mul ((hφ.comp (contDiff_id.add contDiff_const)).sub hφ)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Classical directional derivatives commute with a fixed-step quotient. -/
theorem fderiv_test_differenceQuotient {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ)
    (v w z : E) (h : ℝ) :
    fderiv ℝ (fun y => h⁻¹ * (φ (y + h • v) - φ y)) z w =
      h⁻¹ * (fderiv ℝ φ (z + h • v) w - fderiv ℝ φ z w) := by
  have ht : DifferentiableAt ℝ (fun y => φ (y + h • v)) z :=
    (hφ.comp (contDiff_id.add contDiff_const)).differentiable (by simp) z
  have hd := (ht.hasFDerivAt.sub (hφ.differentiable (by simp) z).hasFDerivAt).const_mul h⁻¹
  simpa [fderiv_comp_add_right] using congrArg (fun T : E →L[ℝ] ℝ => T w) hd.fderiv

/-- Fixed-step quotients of genuine test graphs remain genuine test graphs.
The support condition explicitly includes both the old and translated supports. -/
theorem differenceQuotient_mem_c1SupportedTestGraph {ι : Type*} (b : ι → E)
    {U V : Set E} (hU : U ⊆ V) (v : E) (h : ℝ)
    (hshift : (fun z => z + h • v) ⁻¹' U ⊆ V)
    {p : Lp ℝ 2 (volume : Measure E) × (ι → Lp ℝ 2 (volume : Measure E))}
    (hp : p ∈ c1SupportedTestGraph b U) :
    (directionalDifferenceQuotient p.1 v h,
      fun i => directionalDifferenceQuotient (p.2 i) v h) ∈ c1SupportedTestGraph b V := by
  obtain ⟨φ, hφ, hcφ, hsφ, hpφ, hpdφ⟩ := hp
  let ψ : E → ℝ := fun z => h⁻¹ * (φ (z + h • v) - φ z)
  have hct : HasCompactSupport (fun z => φ (z + h • v)) :=
    hcφ.comp_homeomorph (Homeomorph.addRight (h • v))
  have hs : tsupport ψ ⊆ V := by
    have hs' : tsupport ψ ⊆ tsupport (fun z => φ (z + h • v)) ∪ tsupport φ :=
      (tsupport_smul_subset_right (fun _ : E => h⁻¹)
        (fun z => φ (z + h • v) - φ z)).trans (tsupport_sub _ _)
    intro z hz
    rcases hs' hz with hz | hz
    · apply hshift
      apply hsφ
      exact (closure_minimal
        (show Function.support (fun z => φ (z + h • v)) ⊆
          (fun z => z + h • v) ⁻¹' tsupport φ from fun _ hz => subset_tsupport φ hz)
        ((isClosed_tsupport φ).preimage (continuous_id.add continuous_const))) hz
    · exact hU (hsφ hz)
  have hae (u : Lp ℝ 2 (volume : Measure E)) (f : E → ℝ) (hu : u =ᵐ[volume] f) :
      directionalDifferenceQuotient u v h =ᵐ[volume]
        (fun z => h⁻¹ * (f (z + h • v) - f z)) := by
    have ht := (measurePreserving_add_right (volume : Measure E) (h • v)).quasiMeasurePreserving.ae_eq_comp hu
    filter_upwards [directionalDifferenceQuotient_ae_eq u v h, hu, ht] with z hz hu ht
    have ht' : u (z + h • v) = f (z + h • v) := ht
    rwa [ht', hu] at hz
  refine ⟨ψ, contDiff_test_differenceQuotient hφ v h,
    (hct.sub hcφ).smul_left (f := fun _ => h⁻¹), hs, hae p.1 φ hpφ, ?_⟩
  intro i
  exact (hae (p.2 i) _ (hpdφ i)).trans (Filter.Eventually.of_forall fun z =>
    (fderiv_test_differenceQuotient hφ v (b i) z h).symm)

/-- Actual fixed-step quotients preserve graph-closure admissibility. -/
theorem differenceQuotient_mem_closure_c1SupportedTestGraph {ι : Type*} (b : ι → E)
    {U V : Set E} (hU : U ⊆ V) (v : E) (h : ℝ)
    (hshift : (fun z => z + h • v) ⁻¹' U ⊆ V)
    {p : Lp ℝ 2 (volume : Measure E) × (ι → Lp ℝ 2 (volume : Measure E))}
    (hp : p ∈ closure (c1SupportedTestGraph b U)) :
    (directionalDifferenceQuotient p.1 v h,
      fun i => directionalDifferenceQuotient (p.2 i) v h) ∈
        closure (c1SupportedTestGraph b V) := by
  let F := fun q : Lp ℝ 2 (volume : Measure E) × (ι → Lp ℝ 2 (volume : Measure E)) =>
    (directionalDifferenceQuotientL v h q.1, fun i => directionalDifferenceQuotientL v h (q.2 i))
  have hF : Continuous F :=
    ((directionalDifferenceQuotientL v h).continuous.comp continuous_fst).prodMk
      (continuous_pi fun i => (directionalDifferenceQuotientL v h).continuous.comp
        ((continuous_apply i).comp continuous_snd))
  apply closure_minimal (t := F ⁻¹' closure (c1SupportedTestGraph b V)) ?_
    (isClosed_closure.preimage hF) hp
  intro q hq
  exact subset_closure (differenceQuotient_mem_c1SupportedTestGraph b hU v h hshift hq)

end AlmostSchur
