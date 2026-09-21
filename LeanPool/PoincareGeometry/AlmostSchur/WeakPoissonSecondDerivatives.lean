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

public import LeanPool.PoincareGeometry.AlmostSchur.WeakPoissonH2Bound
public import LeanPool.PoincareGeometry.AlmostSchur.LocalizedDerivativeExtraction

/-! # Actual L² weak second derivatives of the constructed Poisson solution

The first theorem extracts derivatives of compactly localized coordinate
first derivatives, with one finite bound for every pair of coordinates.
-/

@[expose] public noncomputable section
open Set Bundle MeasureTheory Filter
open scoped Manifold ContDiff Topology BigOperators

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [LindelofSpace M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M]

/-- Each localized actual first derivative has an L² weak derivative in every
coordinate direction, with a common finite norm bound. -/
theorem exists_weakPoisson_localized_second_derivatives
    (b : OrthonormalBasis ι ℝ E) (c : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target) (hconv : Convex ℝ K)
    (η : E → ℝ) (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η)
    (hη1 : ∀ x, |η x| ≤ 1) (hηK : tsupport η ⊆ interior K)
    (f : Lp ℝ 2 (riemannianVolume (I := I) (M := M)))
    (hf : (∫ x, f x ∂riemannianVolume (I := I)) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i k : ι,
      ∃ w g : Lp ℝ 2 (volume : Measure E),
        (w =ᵐ[volume] (fun x => η x * energyChartDerivative c hK hKt (b i) (weakPoissonSolution f) x)) ∧
        ‖g‖ ≤ C ∧ ∀ (φ : E → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
          (∫ x, w x * fderiv ℝ φ x (b k)) = -(∫ x, g x * φ x) := by
  obtain ⟨B, hB, δ, hδ, hbound⟩ := exists_weakPoisson_weighted_derivative_quotient_bound
    b c hK hKt hconv η hη hcη hη1 hηK f hf
  obtain ⟨χ, O, ε, hχ, hcχ, hsχ, hrχ, hO, hSO, hOW, hχ1, hε, hmargin⟩ :=
    exists_smooth_compact_plateau hcη isOpen_interior hηK
  have hχC1 : ContDiff ℝ 1 χ := hχ.of_le (by norm_num)
  obtain ⟨P, Q, hgraph, hPU, hQD, hqδ⟩ := exists_energyCutoffGraph_plateau (I := I)
    (fun i => b i) c hK hKt χ hχC1 hcχ (hsχ.trans interior_subset) hO hχ1
  obtain ⟨L, hL, hLη⟩ := exists_cutoff_differenceQuotient_bound η hη hcη
  let u := weakPoissonSolution f
  let G := Real.sqrt (∑ i, ‖Q i u‖ ^ 2)
  have hηb : ∀ᵐ x ∂(volume : Measure E), ‖η x‖ ≤ 1 :=
    Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hη1 x
  let N := boundedL2Multiplier η hη.continuous.aestronglyMeasurable 1 hηb
  have hN (a : Lp ℝ 2 (volume : Measure E)) : N a =ᵐ[volume] (fun x => η x * a x) :=
    boundedL2Multiplier_ae_eq _ _ _ _ a
  have hQi (i : ι) : ‖Q i u‖ ≤ G := by
    rw [show G = ‖l2FiniteFamily (fun i => Q i u)‖ from (norm_l2FiniteFamily _).symm]
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [l2FiniteFamily_ae_eq (fun i => Q i u)] with x hx
    have he := congrArg (fun a : EuclideanSpace ℝ ι => a i) hx
    change l2FiniteFamily (fun i => Q i u) x i = Q i u x at he
    rw [← he]
    exact PiLp.norm_apply_le _ i
  refine ⟨B + L * G, add_nonneg hB (mul_nonneg hL (Real.sqrt_nonneg _)), ?_⟩
  intro i k
  let w := N (Q i u)
  have hw : w =ᵐ[volume] (fun x => η x * energyChartDerivative c hK hKt (b i) u x) := by
    filter_upwards [hN (Q i u), hQD u i] with x hn hd
    rw [hn]
    by_cases hx : x ∈ tsupport η
    · rw [hd (hSO hx)]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
  have hmin : 0 < min δ ε := lt_min hδ hε
  have hwb : ∀ h : ℝ, h ≠ 0 → |h| < min δ ε →
      ‖directionalDifferenceQuotient w (b k) h‖ ≤ B + L * G := by
    intro h hh hsmall
    obtain ⟨r, hr, hrB⟩ := hbound k (-h) (neg_ne_zero.mpr hh)
      (by simpa only [abs_neg] using lt_of_lt_of_le hsmall (min_le_left δ ε))
    obtain ⟨hends, _, _⟩ := hmargin (b k) (-h)
      (by simpa only [abs_neg, b.norm_eq_one, mul_one] using lt_of_lt_of_le hsmall (min_le_right δ ε))
    have hdq := differenceQuotient_ae_eq_of_local_agreement (Q i u)
      (fun x => energyChartDerivative c hK hKt (b i) u x) (hQD u i) hSO (b k) (-h)
      (fun x hx => (hends x hx).1)
    have hn : ‖N (directionalDifferenceQuotient (Q i u) (b k) (-h))‖ ≤ B := by
      apply le_trans (b := ‖r‖) _ hrB
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [hN (directionalDifferenceQuotient (Q i u) (b k) (-h)), hr, hdq]
        with x hn hr hdq
      have he : N (directionalDifferenceQuotient (Q i u) (b k) (-h)) x = r x i := by
        rw [hn, hr i]
        by_cases hx : x ∈ tsupport η
        · rw [hdq hx]
        · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
      rw [he]
      exact PiLp.norm_apply_le _ i
    have hstep : ∀ᵐ x ∂(volume : Measure E), ‖h⁻¹ * (η (x + h • b k) - η x)‖ ≤ L :=
      Eventually.of_forall fun x => by simpa only [b.norm_eq_one, mul_one] using hLη x (b k) h hh
    exact (norm_differenceQuotient_cutoff_le η hη.continuous.aestronglyMeasurable 1 hηb
      (Q i u) (b k) h L hstep).trans (add_le_add hn (mul_le_mul_of_nonneg_left (hQi i) hL))
  obtain ⟨g, hg, hweak⟩ := exists_weakDerivative_of_differenceQuotient_bound_on_ball
    w (b k) (B + L * G) (min δ ε) hmin hwb
  exact ⟨w, g, hw, hg, hweak⟩

/-- On any inner compact coordinate set, every ordered pair of first/second
coordinate directions has an actual L² weak derivative with a common norm bound. -/
theorem exists_weakPoisson_second_derivatives_on_compact
    (b : OrthonormalBasis ι ℝ E) (c : M) {K : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target) (hconv : Convex ℝ K)
    {S : Set E} (hS : IsCompact S) (hSK : S ⊆ interior K)
    (f : Lp ℝ 2 (riemannianVolume (I := I) (M := M)))
    (hf : (∫ x, f x ∂riemannianVolume (I := I)) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i k : ι, ∃ g : Lp ℝ 2 (volume : Measure E),
      ‖g‖ ≤ C ∧ ∀ (φ : E → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ S →
        (∫ x in S, energyChartDerivative c hK hKt (b i) (weakPoissonSolution f) x *
          fderiv ℝ φ x (b k)) = -(∫ x in S, g x * φ x) := by
  obtain ⟨η, O, ε, hη, hcη, hsη, hrη, hO, hSO, hOW, hη1, hε, hmargin⟩ :=
    exists_smooth_compact_plateau hS isOpen_interior hSK
  have hηC1 : ContDiff ℝ 1 η := hη.of_le (by norm_num)
  have hηb : ∀ x, |η x| ≤ 1 := by
    intro x
    exact abs_le.mpr ⟨by linarith [(hrη x).1], (hrη x).2⟩
  obtain ⟨C, hC, hsecond⟩ := exists_weakPoisson_localized_second_derivatives
    b c hK hKt hconv η hηC1 hcη hηb hsη f hf
  refine ⟨C, hC, fun i k => ?_⟩
  obtain ⟨w, g, hw, hg, hweak⟩ := hsecond i k
  refine ⟨g, hg, fun φ hφ hcφ hsφ => ?_⟩
  have hz (x : E) (hx : x ∉ S) : fderiv ℝ φ x (b k) = 0 := by
    rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun hh => hx (hsφ hh))]
    rfl
  have hl : (∫ x, w x * fderiv ℝ φ x (b k)) =
      ∫ x in S, energyChartDerivative c hK hKt (b i) (weakPoissonSolution f) x * fderiv ℝ φ x (b k) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := S)
      (fun x hx => by rw [hz x hx, mul_zero])]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hw, ae_restrict_mem hS.measurableSet] with x hw hx
    rw [hw, hη1 (hSO hx), one_mul]
  have hr : (∫ x, g x * φ x) = ∫ x in S, g x * φ x := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (hsφ hh)), mul_zero]
  rw [← hl, ← hr]
  exact hweak φ hφ hcφ

end AlmostSchur
