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

public import LeanPool.PoincareGeometry.AlmostSchur.TestedDifferenceQuotient
public import LeanPool.PoincareGeometry.AlmostSchur.LocalWeakPoissonGraph

/-! # Actual local PDE quotient tests and support-safe flux expansion

Only the flux is extended by zero. The coefficient product rule is asserted
on an interior set whose translated points remain in the coordinate domain.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators

namespace AlmostSchur.LocalWeakPoissonData

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {b : OrthonormalBasis ι ℝ E} {K : Set E}
  {A : E → Matrix ι ι ℝ} {U F : E → ℝ} {D : ι → E → ℝ}

/-- The actual local PDE gives the tested-flux estimate with no assumed analytic bridge. -/
theorem abs_tested_flux_quotient_le (d : LocalWeakPoissonData b K A U F D)
    (hK : MeasurableSet K)
    (hA : ∀ i j, AEStronglyMeasurable (fun z => A z i j) ((volume : Measure E).restrict K))
    (C : ℝ) (hC : ∀ᵐ z ∂(volume : Measure E).restrict K, ∀ i j, ‖A z i j‖ ≤ C)
    {S : Set E} (hS : S ⊆ K) (v : E) (h : ℝ) (hh : h ≠ 0)
    (hshift : (fun z => z + (-h) • v) ⁻¹' S ⊆ K)
    {q : Lp ℝ 2 (volume : Measure E) × (ι → Lp ℝ 2 (volume : Measure E))}
    (hq : q ∈ closure (c1SupportedTestGraph (fun i => b i) S)) :
    |∑ j, inner ℝ (directionalDifferenceQuotient (d.globalFlux hK hA C hC j) v h) (q.2 j)| ≤
      ‖d.globalForcing hK‖ * (‖v‖ * Real.sqrt (∑ j, ‖q.2 j‖ ^ 2)) := by
  have hp : ∀ p ∈ c1SupportedTestGraph (fun i => b i) K,
      (∑ j, inner ℝ (d.globalFlux hK hA C hC j) (p.2 j)) =
        inner ℝ (-(-d.globalForcing hK)) p.1 := by
    intro p hp
    simpa only [neg_neg] using d.variational_on_graph_closure hK hA C hC
      (Subset.refl K) (subset_closure hp)
  simpa only [norm_neg] using abs_tested_differenceQuotient_le b hS v h hh hshift
    (d.globalFlux hK hA C hC) (-d.globalForcing hK) hp hq

/-- The coefficient commutator identity only uses values at interior endpoints.
It asserts no quotient bound across the boundary of the zero extension. -/
theorem flux_quotient_ae_on_interior (d : LocalWeakPoissonData b K A U F D)
    (hK : MeasurableSet K)
    (hA : ∀ i j, AEStronglyMeasurable (fun z => A z i j) ((volume : Measure E).restrict K))
    (C : ℝ) (hC : ∀ᵐ z ∂(volume : Measure E).restrict K, ∀ i j, ‖A z i j‖ ≤ C)
    {S : Set E} (hS : S ⊆ K) (v : E) (h : ℝ)
    (hshift : ∀ z ∈ S, z + h • v ∈ K) (j : ι) :
    ∀ᵐ z ∂(volume : Measure E), z ∈ S →
      directionalDifferenceQuotient (d.globalFlux hK hA C hC j) v h z =
        ∑ i, (A (z + h • v) i j * (h⁻¹ * (D i (z + h • v) - D i z)) +
          (h⁻¹ * (A (z + h • v) i j - A z i j)) * D i z) := by
  have hf := d.globalFlux_ae_eq hK hA C hC j
  have ht := (measurePreserving_add_right (volume : Measure E) (h • v)).quasiMeasurePreserving.ae hf
  filter_upwards [directionalDifferenceQuotient_ae_eq (d.globalFlux hK hA C hC j) v h, hf, ht]
    with z hz hf ht
  intro hs
  rw [hz, hf, ht, indicator_of_mem (hS hs), indicator_of_mem (hshift z hs)]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end AlmostSchur.LocalWeakPoissonData
