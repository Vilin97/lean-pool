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

public import LeanPool.PoincareGeometry.AlmostSchur.LocalQuotientEnergyEstimate
public import LeanPool.PoincareGeometry.AlmostSchur.CutoffQuotientFields
public import LeanPool.PoincareGeometry.AlmostSchur.InteriorCoefficientMasks
public import LeanPool.PoincareGeometry.AlmostSchur.CutoffPlateau

/-! # Constructed interior derivative-quotient bound from the actual local PDE

The approximating graph agrees with the local first derivatives on a plateau.
The η² quotient test and every weighted L² field are constructed, rather than
supplied as analytic bridge assumptions. Coefficient quotients are only bounded
on the interior support where both endpoints remain in K.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators Matrix.Norms.Elementwise

namespace AlmostSchur.LocalWeakPoissonData

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {b : OrthonormalBasis ι ℝ E} {K : Set E}
  {A : E → Matrix ι ι ℝ} {U F : E → ℝ} {D : ι → E → ℝ}

theorem exists_local_weighted_derivative_quotient_bound
    (d : LocalWeakPoissonData b K A U F D) (hK : IsCompact K) (hA : ContinuousOn A K)
    {T O : Set E} (p : Lp ℝ 2 (volume : Measure E) × (ι → Lp ℝ 2 (volume : Measure E)))
    (hp : p ∈ closure (c1SupportedTestGraph (fun i => b i) T))
    (hpD : ∀ i, ∀ᵐ x ∂(volume : Measure E), x ∈ O → p.2 i x = D i x)
    (η : E → ℝ) (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η)
    (hη1 : ∀ x, |η x| ≤ 1) (hSO : tsupport η ⊆ O) (hOK : O ⊆ K)
    (v : E) (h : ℝ) (hh : h ≠ 0)
    (hshift : ∀ x ∈ tsupport η, x + h • v ∈ O)
    (hback : (fun x => x + (-h) • v) ⁻¹' tsupport η ⊆ K)
    {ell Lam Cq H : ℝ} (hell : 0 < ell) (hLam : 0 ≤ Lam) (hCq : 0 ≤ Cq) (hH : 0 ≤ H)
    (hellA : ∀ x ∈ K, ∀ u : EuclideanSpace ℝ ι,
      ell * ‖u‖ ^ 2 ≤ ∑ i, ∑ j, A x i j * u i * u j)
    (hbil : ∀ x ∈ K, ∀ u w : EuclideanSpace ℝ ι,
      |∑ i, ∑ j, A x i j * u i * w j| ≤ Lam * ‖u‖ * ‖w‖)
    (hquot : ∀ x ∈ tsupport η, ‖h⁻¹ • (A (x + h • v) - A x)‖ ≤ Cq)
    (hdη : ∀ x, ‖(WithLp.toLp 2 (fun i => fderiv ℝ η x (b i)) : EuclideanSpace ℝ ι)‖ ≤ H) :
    let G := Real.sqrt (∑ i, ‖p.2 i‖ ^ 2)
    let R := ‖v‖ * G
    let L := (Fintype.card ι : ℝ) ^ 2 * Cq
    let Z := ‖d.globalForcing hK.measurableSet‖ * ‖v‖
    ∃ r : Lp (EuclideanSpace ℝ ι) 2 (volume : Measure E),
      (∀ᵐ x ∂(volume : Measure E), ∀ i,
        r x i = η x * (h⁻¹ * (D i (x + h • v) - D i x))) ∧
      ‖r‖ ≤ Real.sqrt ((2 * Lam * H * R + L * G + Z) ^ 2 +
        2 * ell * (2 * L * H * G * R + 2 * H * Z * R)) / ell := by
  dsimp only
  obtain ⟨q, r, s, De, hq, hr, hsrep, hDerep, hqrep, hs, hDe⟩ :=
    exists_cutoff_quotient_fields b p hp η hη hcη hη1 H hH hdη v h hh
  have hSK : tsupport η ⊆ K := hSO.trans hOK
  have hshiftK : ∀ x ∈ tsupport η, x + h • v ∈ K := fun x hx => hOK (hshift x hx)
  have hδ (i : ι) := differenceQuotient_ae_eq_of_local_agreement (p.2 i) (D i)
    (hpD i) hSO v h hshift
  have hrD : ∀ᵐ x ∂(volume : Measure E), ∀ i,
      r x i = η x * (h⁻¹ * (D i (x + h • v) - D i x)) := by
    filter_upwards [hr, ae_all_iff.mpr hδ] with x hr hδ
    intro i
    rw [hr i]
    by_cases hx : x ∈ tsupport η
    · rw [hδ i hx]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
  refine ⟨r, hrD, ?_⟩
  have hAm (i j : ι) : AEStronglyMeasurable (fun x => A x i j) ((volume : Measure E).restrict K) :=
    ((continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hA)).aestronglyMeasurable hK.measurableSet
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hA
  have hCb : ∀ᵐ x ∂(volume : Measure E).restrict K, ∀ i j, ‖A x i j‖ ≤ C := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    intro i j
    exact (Matrix.norm_entry_le_entrywise_sup_norm _).trans (hC x hx)
  let Ah := interiorShiftedMatrix (tsupport η) A v h
  let Bh := interiorQuotientMatrix (tsupport η) A v h
  have hmA := aestronglyMeasurable_interiorShiftedMatrix (isClosed_tsupport η).measurableSet A hA v h hshiftK (volume : Measure E)
  have hmB := aestronglyMeasurable_interiorQuotientMatrix (isClosed_tsupport η).measurableSet hSK A hA v h hshiftK (volume : Measure E)
  have hbA : ∀ᵐ x ∂(volume : Measure E), ∀ u w : EuclideanSpace ℝ ι,
      |∑ i, ∑ j, Ah x i j * u i * w j| ≤ Lam * ‖u‖ * ‖w‖ :=
    Eventually.of_forall fun x => interiorShiftedMatrix_bilinear_bound A v h hLam hshiftK hbil x
  have hbB : ∀ᵐ x ∂(volume : Measure E), ∀ u w : EuclideanSpace ℝ ι,
      |∑ i, ∑ j, Bh x i j * u i * w j| ≤ (Fintype.card ι : ℝ) ^ 2 * Cq * ‖u‖ * ‖w‖ :=
    Eventually.of_forall fun x => interiorQuotientMatrix_bilinear_bound A v h hCq hquot x
  have hco : ∀ᵐ x ∂(volume : Measure E), ell * ‖r x‖ ^ 2 ≤ ∑ i, ∑ j, Ah x i j * r x i * r x j := by
    filter_upwards [hr] with x hr
    by_cases hx : x ∈ tsupport η
    · simpa [Ah, interiorShiftedMatrix, hx] using hellA (x + h • v) (hshiftK x hx) (r x)
    · have hz : r x = 0 := by
        ext i
        simp only [hr i, image_eq_zero_of_notMem_tsupport hx, zero_mul, PiLp.zero_apply]
      simp [Ah, interiorShiftedMatrix, hx, hz]
  have hJ : ∀ᵐ x ∂(volume : Measure E), ∀ j,
      η x * directionalDifferenceQuotient (d.globalFlux hK.measurableSet hAm C hCb j) v h x =
        ∑ i, (Ah x i j * r x i + Bh x i j * De x i) := by
    filter_upwards [hrD, hDerep, ae_all_iff.mpr hpD,
      ae_all_iff.mpr (fun j => d.flux_quotient_ae_on_interior hK.measurableSet hAm C hCb hSK v h hshiftK j)]
      with x hr hd hp hf
    intro j
    by_cases hx : x ∈ tsupport η
    · rw [hf j hx, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Ah, Bh, interiorShiftedMatrix, interiorQuotientMatrix, indicator_of_mem hx,
        Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, hr i, hd i, hp i (hSO hx)]
      ring
    · simp [Ah, Bh, interiorShiftedMatrix, interiorQuotientMatrix, hx, image_eq_zero_of_notMem_tsupport hx]
  exact d.represented_quotient_energy_bound hK.measurableSet hAm C hCb hSK v h hh hback hq
    Ah Bh hmA hmB r s De η hell hLam (mul_nonneg (sq_nonneg _) hCq) hH
    (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    hbA hbB hco (Eventually.of_forall hη1) hqrep hJ hs hDe

end AlmostSchur.LocalWeakPoissonData
