/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.WeakPoissonH2Jet
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! # Commutation of local second weak derivatives

Uniqueness from supported tests holds in the interior of the test domain.
For an arbitrary compact inner set we first construct the actual Poisson jet
on a larger compact neighborhood. No null-boundary assumption is needed.
-/
@[expose] public noncomputable section
open Set Bundle MeasureTheory Filter
open scoped Manifold ContDiff Topology BigOperators
namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Restricting the domain of a weak identity does not introduce boundary
terms because the test and its derivative vanish outside the smaller set. -/
theorem HasWeakDirectionalDerivativeOn.mono_domain
    {S K : Set E} (hSK : S ⊆ K) {v : E} {u du : E → ℝ}
    (h : HasWeakDirectionalDerivativeOn K v u du) :
    HasWeakDirectionalDerivativeOn S v u du := by
  intro φ hφ hc hs
  have he := h φ hφ hc (hs.trans hSK)
  have hd (z : E) (hz : z ∉ S) : fderiv ℝ φ z v = 0 := by
    rw [fderiv_of_notMem_tsupport ℝ (fun hh => hz (hs hh))]
    rfl
  have hleft (T : Set E) (hST : S ⊆ T) :
      (∫ z in T, u z * fderiv ℝ φ z v) = ∫ z, u z * fderiv ℝ φ z v :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => by rw [hd z (fun hh => hz (hST hh)), mul_zero])
  have hright (T : Set E) (hST : S ⊆ T) :
      (∫ z in T, du z * φ z) = ∫ z, du z * φ z :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport (fun hh => hz (hST (hs hh))), mul_zero])
  rw [hleft K hSK, hright K hSK] at he
  rwa [hleft S Subset.rfl, hright S Subset.rfl]

/-- Both mixed fields pair equally with every supported smooth test. -/
theorem LocalL2DerivativeJet.mixed_second_test_eq
    {ι : Type*} {b : ι → E} {K : Set E}
    (J : LocalL2DerivativeJet b K 2) (i k : ι)
    (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ K) :
    (∫ z in K, J.value [i, k] z * φ z) = ∫ z in K, J.value [k, i] z * φ z := by
  have h1 := J.weak [k] (by simp) i φ hφ hc hs
  have h2 := J.weak [i] (by simp) k φ hφ hc hs
  have h3 := J.weak [] (by simp) k (fun z => fderiv ℝ φ z (b i))
    (contDiff_smooth_test_derivative hφ (b i)) (hc.fderiv_apply ℝ (b i))
    ((tsupport_fderiv_apply_subset ℝ (b i)).trans hs)
  have h4 := J.weak [] (by simp) i (fun z => fderiv ℝ φ z (b k))
    (contDiff_smooth_test_derivative hφ (b k)) (hc.fderiv_apply ℝ (b k))
    ((tsupport_fderiv_apply_subset ℝ (b k)).trans hs)
  simp_rw [smooth_test_derivatives_commute hφ _ (b i) (b k)] at h3
  linarith

/-- Second weak derivatives commute almost everywhere in the interior.
The compact boundary need not be detectable by supported smooth tests. -/
theorem LocalL2DerivativeJet.mixed_second_ae_eq_interior
    {ι : Type*} {b : ι → E} {K : Set E}
    (J : LocalL2DerivativeJet b K 2) (i k : ι) :
    (J.value [i, k] : E → ℝ) =ᵐ[volume.restrict (interior K)] J.value [k, i] := by
  let g : E → ℝ := fun z => J.value [i, k] z - J.value [k, i] z
  have hg : LocallyIntegrable g volume :=
    ((Lp.memLp (J.value [i, k])).sub (Lp.memLp (J.value [k, i]))).locallyIntegrable
      (by norm_num)
  have he := isOpen_interior.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hg.locallyIntegrableOn (interior K)) (fun φ hφ hc hs => ?_)
  · apply (ae_restrict_iff' isOpen_interior.measurableSet).mpr
    filter_upwards [he] with z hz
    intro hzk
    exact sub_eq_zero.mp (hz hzk)
  · have ht : MemLp φ 2 (volume : Measure E) := hφ.continuous.memLp_of_hasCompactSupport hc
    have hzero (T : Set E) (hT : tsupport φ ⊆ T) (u : E → ℝ) :
        (∫ z in T, u z * φ z) = ∫ z, u z * φ z :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
        rw [image_eq_zero_of_notMem_tsupport (fun hh => hz (hT hh)), mul_zero])
    have h := J.mixed_second_test_eq i k φ hφ hc (hs.trans interior_subset)
    rw [hzero K (hs.trans interior_subset), hzero K (hs.trans interior_subset)] at h
    change (∫ z, φ z * (J.value [i, k] z - J.value [k, i] z)) = 0
    simp_rw [mul_sub, mul_comm (φ _) ]
    rw [integral_sub (f := fun z => J.value [i, k] z * φ z)
      (g := fun z => J.value [k, i] z * φ z)
      ((Lp.memLp _).integrable_mul ht) ((Lp.memLp _).integrable_mul ht), h, sub_self]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [LindelofSpace M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M]

/-- Construct the actual Poisson jet on a larger compact neighborhood, then
restrict it. Its mixed fields agree on all of the requested compact S. -/
theorem exists_weakPoisson_local_L2_jet_two_symmetric
    (b : OrthonormalBasis ι ℝ E) (c : M) {K S : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target) (hconv : Convex ℝ K)
    (hS : IsCompact S) (hSK : S ⊆ interior K)
    (f : Lp ℝ 2 (riemannianVolume (I := I) (M := M)))
    (hf : (∫ x, f x ∂riemannianVolume (I := I)) = 0) :
    ∃ J : LocalL2DerivativeJet (fun i => b i) S 2, ∃ C : ℝ, 0 ≤ C ∧
      (J.value [] =ᵐ[volume.restrict S] (fun z =>
        energyCompletionToL2 (weakPoissonSolution f) ((extChartAt I c).symm z))) ∧
      (∀ i, J.value [i] =ᵐ[volume.restrict S] (fun z =>
        energyChartDerivative c hK hKt (b i) (weakPoissonSolution f) z)) ∧
      (∀ i k, ‖J.value [k, i]‖ ≤ C) ∧
      (∀ i k, (J.value [i, k] : E → ℝ) =ᵐ[volume.restrict S] J.value [k, i]) := by
  obtain ⟨T, hT, hST, hTK⟩ := exists_compact_between hS isOpen_interior hSK
  obtain ⟨J, C, hC, hJ0, hJ1, hJ2, hweak⟩ :=
    exists_weakPoisson_local_L2_jet_two b c hK hKt hconv hT hTK f hf
  let J' : LocalL2DerivativeJet (fun i => b i) S 2 :=
    ⟨J.value, fun w hw i => (J.weak w hw i).mono_domain (hST.trans interior_subset)⟩
  have hm : volume.restrict S ≤ (volume : Measure E).restrict T :=
    Measure.restrict_mono_set _ (hST.trans interior_subset)
  refine ⟨J', C, hC, hJ0.filter_mono (ae_mono hm),
    fun i => (hJ1 i).filter_mono (ae_mono hm), hJ2, ?_⟩
  intro i k
  exact (J.mixed_second_ae_eq_interior i k).filter_mono
    (ae_mono (Measure.restrict_mono_set volume hST))

end AlmostSchur
