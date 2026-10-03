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

public import LeanPool.PoincareGeometry.AlmostSchur.LocalH2QuotientBound

/-! # Uniform interior H² quotient estimates for the constructed weak Poisson solution

All coefficient bounds, graph approximation, plateau margins, and admissible
tests are obtained from the actual metric and the constructed energy solution.
-/

@[expose] public noncomputable section
open Set Bundle MeasureTheory Filter
open scoped Manifold ContDiff Topology BigOperators Matrix.Norms.Elementwise

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A compact C¹ cutoff has one finite bound on its Euclidean gradient coordinates. -/
theorem exists_cutoff_coordinate_gradient_bound (b : OrthonormalBasis ι ℝ E)
    (η : E → ℝ) (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ x,
      ‖(WithLp.toLp 2 (fun i => fderiv ℝ η x (b i)) : EuclideanSpace ℝ ι)‖ ≤ H := by
  let g : E → EuclideanSpace ℝ ι := fun x => WithLp.toLp 2 (fun i => fderiv ℝ η x (b i))
  have hg : Continuous g := (PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).comp
    (continuous_pi fun i => (hη.continuous_fderiv (by norm_num)).clm_apply (continuous_const (y := b i)))
  have hcg : HasCompactSupport g := by
    apply hcη.mono'
    intro x hx
    by_contra hn
    apply hx
    ext i
    simp [g, fderiv_of_notMem_tsupport (𝕜 := ℝ) hn]
  obtain ⟨H, hH⟩ := hcg.exists_bound_of_continuous hg
  exact ⟨max H 0, le_max_right _ _, fun x => (hH x).trans (le_max_left _ _)⟩

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [LindelofSpace M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local instance weakPoissonH2ContinuousMetric :
    IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  continuousRiemannianBundle_of_contMDiff (I := I)

/-- The actual first derivatives have uniformly bounded weighted difference quotients
on every compact convex chart neighborhood and every inner compact cutoff. -/
theorem exists_weakPoisson_weighted_derivative_quotient_bound
    (b : OrthonormalBasis ι ℝ E) (c : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target) (hconv : Convex ℝ K)
    (η : E → ℝ) (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η)
    (hη1 : ∀ x, |η x| ≤ 1) (hηK : tsupport η ⊆ interior K)
    (f : Lp ℝ 2 (riemannianVolume (I := I) (M := M)))
    (hf : (∫ x, f x ∂riemannianVolume (I := I)) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ (k : ι) (h : ℝ), h ≠ 0 → |h| < ε →
      ∃ r : Lp (EuclideanSpace ℝ ι) 2 (volume : Measure E),
        (∀ᵐ x ∂(volume : Measure E), ∀ i, r x i = η x * (h⁻¹ *
          (energyChartDerivative c hK hKt (b i) (weakPoissonSolution f) (x + h • b k) -
            energyChartDerivative c hK hKt (b i) (weakPoissonSolution f) x))) ∧ ‖r‖ ≤ C := by
  obtain ⟨χ, O, ε, hχ, hcχ, hsχ, hrχ, hO, hSO, hOW, hχ1, hε, hmargin⟩ :=
    exists_smooth_compact_plateau hcη isOpen_interior hηK
  have hχC1 : ContDiff ℝ 1 χ := hχ.of_le (by norm_num)
  obtain ⟨P, Q, hgraph, hPU, hQD, hqδ⟩ := exists_energyCutoffGraph_plateau (I := I)
    (fun i => b i) c hK hKt χ hχC1 hcχ (hsχ.trans interior_subset) hO hχ1
  let u := weakPoissonSolution f
  let p := (P u, fun i => Q i u)
  let d := weakPoissonSolution_local_data b c hK hKt f hf
  have hAc := (continuousOn_coordinateEllipticMatrix (I := I) b.toBasis c).mono hKt
  obtain ⟨ell, hell, hEll⟩ := exists_coordinateEllipticMatrix_lower_bound b.toBasis c hK hKt
  obtain ⟨Lam, hLam, hLamA⟩ := exists_uniform_matrix_bilinear_bound hK _ hAc
  obtain ⟨Cq, hCq, hCqA⟩ := exists_coordinateEllipticMatrix_quotient_bound b.toBasis c hK hKt hconv
  obtain ⟨Bη, hBη, hdη⟩ := exists_cutoff_coordinate_gradient_bound b η hη hcη
  let G := Real.sqrt (∑ i, ‖p.2 i‖ ^ 2)
  let L := (Fintype.card ι : ℝ) ^ 2 * Cq
  let Z := ‖d.globalForcing hK.measurableSet‖
  let C := Real.sqrt ((2 * Lam * Bη * G + L * G + Z) ^ 2 +
    2 * ell * (2 * L * Bη * G * G + 2 * Bη * Z * G)) / ell
  refine ⟨C, div_nonneg (Real.sqrt_nonneg _) hell.le, ε, hε, ?_⟩
  intro k h hh hsmall
  obtain ⟨hends, hplus, hminus⟩ := hmargin (b k) h (by simpa [b.norm_eq_one] using hsmall)
  have hq : ∀ x ∈ tsupport η,
      ‖h⁻¹ • (coordinateEllipticMatrix (I := I) b.toBasis c (x + h • b k) -
        coordinateEllipticMatrix (I := I) b.toBasis c x)‖ ≤ Cq := by
    intro x hx
    simpa [b.norm_eq_one] using hCqA x (b k) h hh
      (interior_subset (hηK hx)) (interior_subset (hOW (hends x hx).1))
  have he := d.exists_local_weighted_derivative_quotient_bound hK hAc p (hgraph u)
    (fun i => hQD u i) η hη hcη hη1 hSO (hOW.trans interior_subset) (b k) h hh
    (fun x hx => (hends x hx).1) (hminus.trans (hOW.trans interior_subset))
    hell hLam hCq hBη hEll hLamA hq hdη
  dsimp only at he
  obtain ⟨r, hr, hbound⟩ := he
  refine ⟨r, hr, ?_⟩
  simpa only [b.norm_eq_one, one_mul, mul_one, C, G, L, Z, p] using hbound

end AlmostSchur
