/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.LaurentSeries
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.PolydiscTaylor
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.PowerSeriesConvergence.Analytic

/-!
# Extension to Reinhardt hulls

Power series extend analytic functions from complete Reinhardt domains. More generally, a
connected Reinhardt domain meeting every coordinate hyperplane has a power-series extension to
its geometric logarithmic hull, even if it does not contain the origin. The hull here includes
zero coordinates. This is extension between subsets of ℂⁿ; no abstract envelope or Riemann
domain is constructed.

Laurent expansion gives power-series extension to logarithmic and complete Reinhardt hulls. The
geometric inclusion of the complete hull in the logarithmic hull for open Reinhardt sets
containing zero is proved independently of Laurent expansion. Analyticity of the extended sums
follows from the proved arbitrary-coefficient convergence theorem. References:
[Korevaar–Wiegerinck][KorevaarWiegerinck2017] (2017), Corollary 2.4.3, Theorem 2.5.1, Corollary
2.5.2, and Theorem 2.8.2.

## Main results

`IsCompleteReinhardt.subset_convergenceDomain_and_eqOn_powerSeriesSum` is the Taylor series of a
holomorphic function on a complete Reinhardt domain.
`exists_extension_logarithmicReinhardtHull_of_zero_mem` and `exists_extension_completeReinhardtHull`
extend to the logarithmic and complete hulls.
`completeReinhardtHull_subset_logarithmicReinhardtHull` is the geometric inclusion when the set is
open and contains the origin.

## References

* [J. Korevaar and J. Wiegerinck, *Several Complex Variables*][KorevaarWiegerinck2017]
-/

public noncomputable section

open Set Filter
open scoped Topology NNReal

namespace SeveralComplexVariables

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Banach-valued normalized multivariate Taylor coefficients at the origin. -/
@[expose] def taylorCoefficientsAtZero (f : (Fin n → ℂ) → F) : MvPowerSeries (Fin n) F :=
  fun m => (∏ i, (m i).factorial : ℂ)⁻¹ • multiIndexDeriv m f 0

omit [CompleteSpace F] in
private theorem summable_polydiscTaylor_terms {f : (Fin n → ℂ) → F}
    (z : Fin n → ℂ) (r : Fin n → ℝ≥0) (M : ℝ)
    (hr : ∀ i, (0 : ℝ) < r i) (hM0 : 0 ≤ M)
    (hMb : ∀ y ∈ closedPolydisc 0 (fun i => (r i : ℝ)), ‖f y‖ ≤ M)
    (hq : ∀ i, ‖‖z i‖ / (r i : ℝ)‖ < 1) :
    Summable (fun m : Fin n → ℕ =>
      ‖(∏ i, z i ^ m i) • polydiscCauchyCoeffWithRadii f 0 (fun i => (r i : ℝ)) m‖) :=
  ((hasSum_pi_geometric (fun i => ‖z i‖ / (r i : ℝ)) hq).summable.mul_left M).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun m => norm_polydiscTaylor_term_le hr hM0 hMb
      (fun _ => le_rfl) m)

private theorem summable_finsupp_equiv {a : (Fin n → ℕ) → ℝ} (h : Summable a) :
    Summable (fun m : Fin n →₀ ℕ => a m) :=
  (Finsupp.equivFunOnFinite : (Fin n →₀ ℕ) ≃ (Fin n → ℕ)).summable_iff.mpr h

omit [CompleteSpace F] in
omit [NormedSpace ℂ F] in
private theorem hasSum_finsupp_equiv {a : (Fin n → ℕ) → F} {x : F} (h : HasSum a x) :
    HasSum (fun m : Fin n →₀ ℕ => a m) x :=
  (Finsupp.equivFunOnFinite : (Fin n →₀ ℕ) ≃ (Fin n → ℕ)).hasSum_iff.mpr h

private theorem taylorCoefficientsAtZero_polydisc {f : (Fin n → ℂ) → F}
    (z : Fin n → ℂ) (r : Fin n → ℝ≥0) (M : ℝ)
    (hr : ∀ i, (0 : ℝ) < r i) (hzr : ∀ i, ‖z i‖ < r i)
    (hfc : ContinuousOn f (closedPolydisc 0 (fun i => (r i : ℝ))))
    (hfa : ∀ y ∈ closedPolydisc 0 (fun i => (r i : ℝ)), ∀ i,
      AnalyticAt ℂ (fun v => f (Function.update y i v)) (y i))
    (hMb : ∀ y ∈ closedPolydisc 0 (fun i => (r i : ℝ)), ‖f y‖ ≤ M) (hM0 : 0 ≤ M) :
    Summable (fun m : Fin n →₀ ℕ => ‖(∏ i, z i ^ m i) • taylorCoefficientsAtZero f m‖) ∧
      HasSum (fun m : Fin n →₀ ℕ => (∏ i, z i ^ m i) • taylorCoefficientsAtZero f m) (f z) := by
  classical
  have he : ∀ m : Fin n →₀ ℕ, taylorCoefficientsAtZero f m =
      polydiscCauchyCoeffWithRadii f 0 (fun i => (r i : ℝ)) m :=
    fun m => (polydiscCauchyCoeffWithRadii_eq_multiIndexDeriv hr hfc hfa m).symm
  have hq : ∀ i, ‖‖z i‖ / (r i : ℝ)‖ < 1 := by
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) (hr i).le), div_lt_one (hr i)]
    exact hzr i
  have hnorm := summable_polydiscTaylor_terms z r M hr hM0 hMb hq
  have hsum := hasSum_polydiscTaylor (f := f) (c := 0) (h := z) hr (fun i => hzr i) hfc hfa hMb
  constructor
  · simp_rw [he]
    exact summable_finsupp_equiv hnorm
  · simp_rw [he]
    have hs : HasSum (fun m : Fin n → ℕ =>
        (∏ i, z i ^ m i) • polydiscCauchyCoeffWithRadii f 0 (fun i => (r i : ℝ)) m) (f z) := by
      simpa only [zero_add] using hsum
    exact hasSum_finsupp_equiv hs

/-- On a complete Reinhardt open set, the Taylor series at zero represents the function, and the
entire set lies inside its absolute-convergence domain. The proof applies the existing polydisc
Taylor theorem and coefficient estimates. -/
theorem IsCompleteReinhardt.subset_convergenceDomain_and_eqOn_powerSeriesSum {U : Set (Fin n → ℂ)}
    (ho : IsOpen U) (hc : IsCompleteReinhardt U) {f : (Fin n → ℂ) → F}
    (hf : AnalyticOnNhd ℂ f U) :
    U ⊆ powerSeriesConvergenceDomain (taylorCoefficientsAtZero f) ∧
      EqOn (powerSeriesSum (taylorCoefficientsAtZero f)) f U := by
  classical
  have hpoint : ∀ z ∈ U,
      Summable (fun m : Fin n →₀ ℕ => ‖(∏ i, z i ^ m i) • taylorCoefficientsAtZero f m‖) ∧
      HasSum (fun m : Fin n →₀ ℕ => (∏ i, z i ^ m i) • taylorCoefficientsAtZero f m) (f z) := by
    intro z hz
    obtain ⟨r, hrU, hzr⟩ := hc.isReinhardt.exists_strict_modulus_majorant ho hz
    have hr : ∀ i, (0 : ℝ) < r i := fun i => lt_of_le_of_lt (norm_nonneg _) (hzr i)
    have hBU : closedPolydisc 0 (fun i => (r i : ℝ)) ⊆ U := by
      intro y hy
      apply hc hrU
      intro i
      simpa only [Complex.norm_of_nonneg (NNReal.coe_nonneg _), Pi.zero_apply, dist_zero_right]
        using
        (mem_closedPolydisc.mp hy i)
    have hfc := hf.continuousOn.mono hBU
    have hfa : ∀ y ∈ closedPolydisc 0 (fun i => (r i : ℝ)), ∀ i,
        AnalyticAt ℂ (fun v => f (Function.update y i v)) (y i) := by
      intro y hy i
      have hd : Differentiable ℂ (fun v => Function.update y i v) :=
        fun v => (hasDerivAt_update y i v).differentiableAt
      exact (hf y (hBU hy)).comp_of_eq (hd.analyticAt (y i)) (by simp)
    obtain ⟨M, hM⟩ := (isCompact_closedPolydisc 0 (fun i => (r i : ℝ))).bddAbove_image
      hfc.norm
    have hMb : ∀ y ∈ closedPolydisc 0 (fun i => (r i : ℝ)), ‖f y‖ ≤ M :=
      fun y hy => hM ⟨y, hy, rfl⟩
    have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans
      (hMb 0 (mem_closedPolydisc.mpr (fun i => by simpa only [Pi.zero_apply, dist_self]
        using (hr i).le)))
    exact taylorCoefficientsAtZero_polydisc z r M hr hzr hfc hfa hMb hM0
  refine ⟨ho.subset_interior_iff.mpr (fun z hz => ?_), fun z hz => (hpoint z hz).2.tsum_eq⟩
  exact mem_powerSeriesAbsConvergenceSet_iff.mpr (hpoint z hz).1

/-- **Extension from a complete Reinhardt domain to its logarithmic hull.** The explicit
extension is its Taylor sum. -/
theorem analyticOnNhd_taylorSum_logarithmicReinhardtHull {U : Set (Fin n → ℂ)}
    (ho : IsOpen U) (hc : IsCompleteReinhardt U) {f : (Fin n → ℂ) → F}
    (hf : AnalyticOnNhd ℂ f U) :
    AnalyticOnNhd ℂ (powerSeriesSum (taylorCoefficientsAtZero f)) (logarithmicReinhardtHull U) ∧
      EqOn (powerSeriesSum (taylorCoefficientsAtZero f)) f U := by
  obtain ⟨hD, he⟩ := IsCompleteReinhardt.subset_convergenceDomain_and_eqOn_powerSeriesSum ho hc hf
  exact ⟨(analyticOnNhd_powerSeriesSum _).mono
    (logarithmicReinhardtHull_min hD (isReinhardt_powerSeriesConvergenceDomain _)
      (hasGeometricallyConvexModuli_powerSeriesConvergenceDomain _)), he⟩

/-- **Power-series extension from a Reinhardt domain meeting each coordinate hyperplane.**
The points on different hyperplanes need not coincide. The proof eliminates negative
Laurent coefficients and uses geometric convexity of the convergence domain; it depends
on the Laurent expansion theorem. -/
theorem exists_powerSeries_extension_of_meets_coordinateHyperplanes
    {U : Set (Fin n → ℂ)} (ho : IsOpen U) (hc : IsConnected U) (hR : IsReinhardt U)
    (hmeet : ∀ i, ∃ z ∈ U, z i = 0) {f : (Fin n → ℂ) → F} (hf : AnalyticOnNhd ℂ f U) :
    ∃ c : MvPowerSeries (Fin n) F,
      logarithmicReinhardtHull U ⊆ powerSeriesConvergenceDomain c ∧ EqOn (powerSeriesSum c) f U :=
        by
  classical
  obtain ⟨z₀, hz₀⟩ := hc.nonempty
  obtain ⟨r, hrU, hrz⟩ := hR.exists_strict_modulus_majorant ho hz₀
  have hr : ∀ i, (0 : ℝ) < r i := fun i => lt_of_le_of_lt (norm_nonneg _) (hrz i)
  obtain ⟨hsum, hnorm, hneg, _, _⟩ := multivariableLaurent_expansion ho hc.isPreconnected hR hf hr
    hrU
  let e : (Fin n →₀ ℕ) → (Fin n → ℤ) := fun m i => (m i : ℤ)
  have hinj : Function.Injective e := by
    intro m k he
    ext i
    exact_mod_cast (show (m i : ℤ) = (k i : ℤ) from congrFun he i)
  let c : MvPowerSeries (Fin n) F := fun m => multivariableLaurentCoeff f (fun i => (r i : ℝ)) (e m)
  have hterm : ∀ m z, multivariableLaurentTerm (multivariableLaurentCoeff f (fun i => (r i : ℝ)))
      (e m) z = (∏ i, z i ^ m i) • c m := by
    intro m z
    simp only [multivariableLaurentTerm, e, c, zpow_natCast]
  have hzero : ∀ k, k ∉ Set.range e → multivariableLaurentCoeff f (fun i => (r i : ℝ)) k = 0 := by
    intro k hk
    by_cases hp : ∀ i, 0 ≤ k i
    · exfalso
      apply hk
      refine ⟨Finsupp.equivFunOnFinite.symm (fun i => (k i).toNat), ?_⟩
      ext i
      simp [e, Int.toNat_of_nonneg (hp i)]
    · push Not at hp
      obtain ⟨i, hi⟩ := hp
      exact hneg k i (hmeet i) hi
  have hA : U ⊆ powerSeriesAbsConvergenceSet c := by
    intro z hz
    apply mem_powerSeriesAbsConvergenceSet_iff.mpr
    exact ((hnorm z hz).comp_injective hinj).congr (fun m => congrArg norm (hterm m z))
  refine ⟨c, logarithmicReinhardtHull_min (ho.subset_interior_iff.mpr hA)
    (isReinhardt_powerSeriesConvergenceDomain c)
    (hasGeometricallyConvexModuli_powerSeriesConvergenceDomain c), ?_⟩
  intro z hz
  have hs := (hinj.hasSum_iff (fun k hk => by
    simp only [multivariableLaurentTerm, hzero k hk, smul_zero])).mpr (hsum.hasSum hz)
  exact (hs.congr_fun (fun m => (hterm m z).symm)).tsum_eq

/-- Theorem 2.8.2: extension to the logarithmic hull when every coordinate hyperplane is met.
Depends on the Laurent expansion, and allows Banach-valued functions. -/
theorem exists_extension_logarithmicReinhardtHull_of_meets_coordinateHyperplanes
    {U : Set (Fin n → ℂ)} (ho : IsOpen U) (hc : IsConnected U) (hR : IsReinhardt U)
    (hmeet : ∀ i, ∃ z ∈ U, z i = 0) {f : (Fin n → ℂ) → F} (hf : AnalyticOnNhd ℂ f U) :
    ∃ g, AnalyticOnNhd ℂ g (logarithmicReinhardtHull U) ∧ EqOn g f U := by
  obtain ⟨c, hD, he⟩ := exists_powerSeries_extension_of_meets_coordinateHyperplanes ho hc hR hmeet
    hf
  exact ⟨powerSeriesSum c, (analyticOnNhd_powerSeriesSum c).mono hD, he⟩

/-- Corollary 2.5.2: a connected Reinhardt domain containing zero admits extension to its
logarithmic hull. Depends on the Laurent expansion. -/
theorem exists_extension_logarithmicReinhardtHull_of_zero_mem
    {U : Set (Fin n → ℂ)} (ho : IsOpen U) (hc : IsConnected U) (hR : IsReinhardt U)
    (hzero : 0 ∈ U) {f : (Fin n → ℂ) → F} (hf : AnalyticOnNhd ℂ f U) :
    ∃ g, AnalyticOnNhd ℂ g (logarithmicReinhardtHull U) ∧ EqOn g f U :=
  exists_extension_logarithmicReinhardtHull_of_meets_coordinateHyperplanes ho hc hR
    (fun _ => ⟨0, hzero, rfl⟩) hf

/-- The geometric logarithmic hull of an open Reinhardt set containing zero contains its complete
Reinhardt hull. Interpolate a strict modulus majorant with radius vectors converging to zero;
the calculation also includes vanishing coordinates. -/
theorem completeReinhardtHull_subset_logarithmicReinhardtHull
    {U : Set (Fin n → ℂ)} (ho : IsOpen U) (hR : IsReinhardt U) (hzero : 0 ∈ U) :
    completeReinhardtHull U ⊆ logarithmicReinhardtHull U := by
  rintro w ⟨z, hz, hw⟩
  obtain ⟨r, hrU, hzr⟩ := hR.exists_strict_modulus_majorant ho hz
  have hwr (i : Fin n) : ‖w i‖₊ < r i := (show ‖w i‖₊ ≤ ‖z i‖₊ from hw i).trans_lt (hzr i)
  have hr (i : Fin n) : 0 < r i := (show 0 ≤ ‖w i‖₊ from zero_le).trans_lt (hwr i)
  let v (k : ℕ) : Fin n → ℝ≥0 := fun i => r i * (‖w i‖₊ / r i) ^ k
  have hv : Tendsto (fun k i => (v k i : ℂ)) atTop (𝓝 0) := by
    apply tendsto_pi_nhds.mpr
    intro i
    have hratio : ‖w i‖₊ / r i < 1 := (div_lt_one (hr i)).mpr (hwr i)
    have h := (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hratio).const_mul (r i)
    have hreal := NNReal.tendsto_coe.mpr h
    simpa only [mul_zero, NNReal.coe_zero, Complex.ofReal_zero, Function.comp_def,
      v, Pi.zero_apply] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  obtain ⟨k, hk, hvU⟩ := ((eventually_ge_atTop 1).and (hv.eventually (ho.mem_nhds hzero))).exists
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hkle : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have ha : 0 ≤ (k : ℝ)⁻¹ := (inv_pos.mpr hkpos).le
  have hb : 0 ≤ 1 - (k : ℝ)⁻¹ := sub_nonneg.mpr (inv_le_one_of_one_le₀ hkle)
  have hm := isGeometricallyConvex_geometricConvexHull (modulusTrace U)
    (subset_geometricConvexHull _ (hR.mem_modulusTrace_iff.mpr hvU))
    (subset_geometricConvexHull _ (hR.mem_modulusTrace_iff.mpr hrU))
    ha hb (add_sub_cancel _ _)
  have he : geometricCombination (k : ℝ)⁻¹ (1 - (k : ℝ)⁻¹) (v k) r =
      fun i => ‖w i‖₊ := by
    funext i
    dsimp [geometricCombination, v]
    rw [NNReal.mul_rpow, NNReal.pow_rpow_inv_natCast _ (by omega : k ≠ 0)]
    calc
      r i ^ (k : ℝ)⁻¹ * (‖w i‖₊ / r i) * r i ^ (1 - (k : ℝ)⁻¹) =
          (r i ^ (k : ℝ)⁻¹ * r i ^ (1 - (k : ℝ)⁻¹)) * (‖w i‖₊ / r i) := by ring
      _ = r i * (‖w i‖₊ / r i) := by
        rw [← NNReal.rpow_add_of_nonneg _ ha hb, add_sub_cancel, NNReal.rpow_one]
      _ = ‖w i‖₊ := mul_div_cancel₀ _ (hr i).ne'
  change (fun i => ‖w i‖₊) ∈ geometricConvexHull (modulusTrace U)
  exact he ▸ hm

/-- Theorem 2.5.1: extension to the complete Reinhardt hull, obtained by restricting the
logarithmic-hull extension. Depends on the Laurent expansion. -/
theorem exists_extension_completeReinhardtHull
    {U : Set (Fin n → ℂ)} (ho : IsOpen U) (hc : IsConnected U) (hR : IsReinhardt U)
    (hzero : 0 ∈ U) {f : (Fin n → ℂ) → F} (hf : AnalyticOnNhd ℂ f U) :
    ∃ g, AnalyticOnNhd ℂ g (completeReinhardtHull U) ∧ EqOn g f U := by
  obtain ⟨g, hg, he⟩ := exists_extension_logarithmicReinhardtHull_of_zero_mem ho hc hR hzero hf
  exact ⟨g, hg.mono (completeReinhardtHull_subset_logarithmicReinhardtHull ho hR hzero), he⟩

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
