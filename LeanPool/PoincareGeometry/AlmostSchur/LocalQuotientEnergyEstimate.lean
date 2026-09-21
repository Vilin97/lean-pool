/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.LocalTestedQuotient
public import LeanPool.PoincareGeometry.AlmostSchur.WeightedFluxTest
public import LeanPool.PoincareGeometry.AlmostSchur.CutoffEnergyEstimate

/-! # The local PDE energy estimate for a represented cutoff quotient test

This theorem combines the actual variational PDE, graph admissibility,
representative identities, coefficient bounds, and scalar absorption. The
remaining application step constructs the represented fields using cutoffs.
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

/-- A represented cutoff quotient test gives an explicit coercive estimate from the actual PDE.
The matrices `Ah,Bh` are masked interior coefficient values, not derivatives of masks. -/
theorem represented_quotient_energy_bound (d : LocalWeakPoissonData b K A U F D)
    (hK : MeasurableSet K)
    (hA : ∀ i j, AEStronglyMeasurable (fun z => A z i j) ((volume : Measure E).restrict K))
    (C : ℝ) (hC : ∀ᵐ z ∂(volume : Measure E).restrict K, ∀ i j, ‖A z i j‖ ≤ C)
    {S : Set E} (hS : S ⊆ K) (v : E) (h : ℝ) (hh : h ≠ 0)
    (hshift : (fun z => z + (-h) • v) ⁻¹' S ⊆ K)
    {q : Lp ℝ 2 (volume : Measure E) × (ι → Lp ℝ 2 (volume : Measure E))}
    (hq : q ∈ closure (c1SupportedTestGraph (fun i => b i) S))
    (Ah Bh : E → Matrix ι ι ℝ)
    (hAh : ∀ i j, AEStronglyMeasurable (fun z => Ah z i j) (volume : Measure E))
    (hBh : ∀ i j, AEStronglyMeasurable (fun z => Bh z i j) (volume : Measure E))
    (r s De : Lp (EuclideanSpace ℝ ι) 2 (volume : Measure E)) (η : E → ℝ)
    {ell Lam L H R G : ℝ} (hell : 0 < ell) (hLam : 0 ≤ Lam) (hL : 0 ≤ L)
    (hH : 0 ≤ H) (hR : 0 ≤ R) (hG : 0 ≤ G)
    (hbA : ∀ᵐ z ∂(volume : Measure E), ∀ u w : EuclideanSpace ℝ ι,
      |∑ i, ∑ j, Ah z i j * u i * w j| ≤ Lam * ‖u‖ * ‖w‖)
    (hbB : ∀ᵐ z ∂(volume : Measure E), ∀ u w : EuclideanSpace ℝ ι,
      |∑ i, ∑ j, Bh z i j * u i * w j| ≤ L * ‖u‖ * ‖w‖)
    (hco : ∀ᵐ z ∂(volume : Measure E), ell * ‖r z‖ ^ 2 ≤ ∑ i, ∑ j, Ah z i j * r z i * r z j)
    (hη : ∀ᵐ z ∂(volume : Measure E), |η z| ≤ 1)
    (hqrep : ∀ᵐ z ∂(volume : Measure E), ∀ j, q.2 j z = η z * (r z j + 2 * s z j))
    (hJrep : ∀ᵐ z ∂(volume : Measure E), ∀ j,
      η z * directionalDifferenceQuotient (d.globalFlux hK hA C hC j) v h z =
        ∑ i, (Ah z i j * r z i + Bh z i j * De z i))
    (hs : ‖s‖ ≤ H * R) (hDe : ‖De‖ ≤ G) :
    ‖r‖ ≤ Real.sqrt ((2 * Lam * H * R + L * G + ‖d.globalForcing hK‖ * ‖v‖) ^ 2 +
      2 * ell * (2 * L * H * G * R + 2 * H * (‖d.globalForcing hK‖ * ‖v‖) * R)) / ell := by
  apply cutoff_energy_norm_bound Ah Bh hAh hBh r s r s De hell hLam hL hH hR hG
    hbA hbB hco hs le_rfl le_rfl hDe
  rw [← weighted_flux_test_expansion Ah Bh hAh hBh hbA hbB
    (fun j => directionalDifferenceQuotient (d.globalFlux hK hA C hC j) v h)
    q.2 r s De η hqrep hJrep]
  have ht := d.abs_tested_flux_quotient_le hK hA C hC hS v h hh hshift hq
  have hn := norm_weighted_testGraph_le q.2 r s η hη hqrep
  have hn' : Real.sqrt (∑ j, ‖q.2 j‖ ^ 2) ≤ ‖r‖ + 2 * H * R := by
    nlinarith
  exact ht.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hn'
      (mul_nonneg (norm_nonneg (d.globalForcing hK)) (norm_nonneg v)))

end AlmostSchur.LocalWeakPoissonData
