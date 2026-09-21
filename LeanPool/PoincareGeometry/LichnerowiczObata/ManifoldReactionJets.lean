/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.ReactionBootstrap
public import LeanPool.PoincareGeometry.LichnerowiczObata.EnergySpectrum
public import LeanPool.PoincareGeometry.AlmostSchur.AlmostSchurFinal

/-!
# Reaction-equation jets on the actual manifold

The chart assembly is adapted from AlmostSchur/ArbitraryWeakPoissonJets.lean
at commit 3faf25aefc27842a77c37ca178e8a40a20bb20c7 of
Arthur742Ramos/lean-poincare-formalization-plan. The new ingredient is the
proved reaction bootstrap: only the multiplier of the unknown function
must be smooth, not the L² forcing itself.
-/

@[expose] public noncomputable section
open Bundle Set MeasureTheory Filter Metric AlmostSchur
open scoped Manifold ContDiff Topology BigOperators Matrix.Norms.Elementwise

namespace LichnerowiczObata
open Reaction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]
  [Nonempty M] [LindelofSpace M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local instance : MeasurableSpace E := borel E
local instance : BorelSpace E := ⟨rfl⟩
local instance : MeasurableSpace M := borel M
local instance : BorelSpace M := ⟨rfl⟩
local instance : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  continuousRiemannianBundle_of_contMDiff (I := I)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_reaction_all_order_jets_on_nested_compacts
    (b : OrthonormalBasis ι ℝ E) (c : M)
    {Kbig : Set E} {K : ℕ → Set E} {S : Set E}
    (hKbig : IsCompact Kbig)
    (hKbig_target : Kbig ⊆ (extChartAt I c).target)
    (hconvbig : Convex ℝ Kbig)
    (hK0big : K 0 ⊆ interior Kbig)
    (hK : ∀ m, IsCompact (K m))
    (hconv : ∀ m, Convex ℝ (K m))
    (hstep : ∀ m, K (m + 1) ⊆ interior (K m))
    (hS : IsCompact S)
    (hSall : ∀ m, S ⊆ interior (K m))
    (f : Lp ℝ 2 (riemannianVolume (I := I) (M := M)))
    (hf : (∫ x, f x ∂riemannianVolume (I := I)) = 0)
    (F : E → ℝ)
    (hF : ContDiffOn ℝ ∞ F (extChartAt I c).target)
    (hFae : (fun z => F z * energyCompletionToL2 (weakPoissonSolution f)
      ((extChartAt I c).symm z)) =ᵐ[volume.restrict Kbig]
      (fun z => matrixDensity (coordinateMetric (I := I) b.toBasis c z) *
        f ((extChartAt I c).symm z))) :
    ∃ v : Lp ℝ 2 (volume : Measure E),
      ∀ n : ℕ, ∃ J : LocalL2DerivativeJet (fun i => b i) S n,
        ReactionHierarchy J
            (coordinateEllipticMatrix (I := I) b.toBasis c)
            F ∧ J.value [] = v ∧
          (J.value [] : E → ℝ) =ᵐ[volume.restrict S]
            (fun z => energyCompletionToL2 (weakPoissonSolution f)
              ((extChartAt I c).symm z)) := by
  let A : E → Matrix ι ι ℝ := coordinateEllipticMatrix (I := I) b.toBasis c
  let R : E → ℝ := fun z => F z * energyCompletionToL2 (weakPoissonSolution f)
    ((extChartAt I c).symm z)
  let Fraw : E → ℝ := fun z =>
    matrixDensity (coordinateMetric (I := I) b.toBasis c z) *
      f ((extChartAt I c).symm z)
  have hA : ContDiffOn ℝ ∞ A (extChartAt I c).target := by
    simpa [A] using
      (contDiffOn_coordinateEllipticMatrix_of_order (I := I) ∞ b.toBasis c)
  have hK0big' : K 0 ⊆ Kbig := hK0big.trans interior_subset
  have hK0target : K 0 ⊆ (extChartAt I c).target :=
    hK0big.trans (interior_subset.trans hKbig_target)
  obtain ⟨ell, hell, hEllbig⟩ :=
    exists_coordinateEllipticMatrix_lower_bound b.toBasis c hKbig hKbig_target
  have hEll : ∀ x ∈ K 0, ∀ u : EuclideanSpace ℝ ι,
      ell * ‖u‖ ^ 2 ≤ ∑ i, ∑ j, A x i j * u i * u j := by
    intro x hx u
    simpa [A] using hEllbig x (hK0big' hx) u
  have hAc : ContinuousOn A Kbig := by
    simpa [A] using
      (continuousOn_coordinateEllipticMatrix (I := I) b.toBasis c).mono
        hKbig_target
  obtain ⟨Lam, hLam, hbilbig⟩ := exists_uniform_matrix_bilinear_bound hKbig A hAc
  have hbil : ∀ x ∈ K 0, ∀ u w : EuclideanSpace ℝ ι,
      |∑ i, ∑ j, A x i j * u i * w j| ≤ Lam * ‖u‖ * ‖w‖ := by
    intro x hx u w
    exact hbilbig x (hK0big' hx) u w
  obtain ⟨J₂, _, _, hJ₂root, hJ₂one, _, _⟩ :=
    exists_weakPoisson_local_L2_jet_two_symmetric b c hKbig hKbig_target hconvbig
      (hK 0) hK0big f hf
  have hAij (i j : ι) : ContDiffOn ℝ ∞ (fun z => A z i j)
      (extChartAt I c).target := by
    exact contDiffOn_pi.mp (contDiffOn_pi.mp hA i) j
  have hbase : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ K 0 →
      (∑ j, ∫ z in K 0, (∑ i, A z i j * J₂.value (i :: []) z) *
        fderiv ℝ φ z (b j)) = -(∫ z in K 0, R z * φ z) := by
    intro φ hφ hcφ hsφ
    have hdata := (weakPoissonSolution_local_data b c hKbig hKbig_target f hf).variational
      φ (hφ.of_le (by norm_num)) hcφ (hsφ.trans hK0big')
    have hflux (j : ι) : Integrable
        (fun z => (∑ i, A z i j * J₂.value (i :: []) z) *
          fderiv ℝ φ z (b j)) (volume.restrict (K 0)) := by
      have hAj : MemLp (fun z => ∑ i, A z i j * J₂.value (i :: []) z) 2
          (volume.restrict (K 0)) := by
        apply memLp_finsetSum
        intro i hi
        exact memLp_mul_coefficient_on_compact (hK 0)
          ((hAij i j).continuousOn.mono hK0target)
          ((Lp.memLp (J₂.value [i])).restrict (K 0))
      have hφj : MemLp (fun z => fderiv ℝ φ z (b j)) 2
          (volume.restrict (K 0)) :=
        (((hφ.continuous_fderiv (by norm_num)).clm_apply
          (continuous_const (y := b j))).memLp_of_hasCompactSupport
          (hcφ.fderiv_apply ℝ (b j))).restrict (K 0)
      exact hAj.integrable_mul hφj
    have hzeroL (z : E) (hz : z ∉ K 0) :
        ∑ i, ∑ j, A z i j *
          energyChartDerivative c hKbig hKbig_target (b i)
            (weakPoissonSolution f) z * fderiv ℝ φ z (b j) = 0 := by
      have hdz : fderiv ℝ φ z = 0 :=
        fderiv_of_notMem_tsupport ℝ (fun hh => hz (hsφ hh))
      simp [hdz]
    have hzeroLbig (z : E) (hz : z ∉ Kbig) :
        ∑ i, ∑ j, A z i j *
          energyChartDerivative c hKbig hKbig_target (b i)
            (weakPoissonSolution f) z * fderiv ℝ φ z (b j) = 0 :=
      hzeroL z (fun hz0 => hz (hK0big' hz0))
    have hzeroR (z : E) (hz : z ∉ K 0) : R z * φ z = 0 := by
      simp [image_eq_zero_of_notMem_tsupport (fun hh => hz (hsφ hh))]
    have hzeroRbig (z : E) (hz : z ∉ Kbig) : R z * φ z = 0 :=
      hzeroR z (fun hz0 => hz (hK0big' hz0))
    have hdata0 :
        (∫ z in K 0, ∑ i, ∑ j, A z i j *
          energyChartDerivative c hKbig hKbig_target (b i)
            (weakPoissonSolution f) z * fderiv ℝ φ z (b j)) =
          -(∫ z in K 0, R z * φ z) := by
      calc
        (∫ z in K 0, ∑ i, ∑ j, A z i j *
            energyChartDerivative c hKbig hKbig_target (b i)
              (weakPoissonSolution f) z * fderiv ℝ φ z (b j)) =
            ∫ z, ∑ i, ∑ j, A z i j *
              energyChartDerivative c hKbig hKbig_target (b i)
                (weakPoissonSolution f) z * fderiv ℝ φ z (b j) :=
          setIntegral_eq_integral_of_forall_compl_eq_zero hzeroL
        _ = ∫ z in Kbig, ∑ i, ∑ j, A z i j *
              energyChartDerivative c hKbig hKbig_target (b i)
                (weakPoissonSolution f) z * fderiv ℝ φ z (b j) :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero hzeroLbig).symm
        _ = -(∫ z in Kbig, Fraw z * φ z) := hdata
        _ = -(∫ z in Kbig, R z * φ z) := by
          congr 1
          exact integral_congr_ae (hFae.mul EventuallyEq.rfl).symm
        _ = -(∫ z, R z * φ z) := by
          rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzeroRbig]
        _ = -(∫ z in K 0, R z * φ z) := by
          rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzeroR]
    calc
      (∑ j, ∫ z in K 0, (∑ i, A z i j * J₂.value (i :: []) z) *
          fderiv ℝ φ z (b j)) =
          ∫ z in K 0, ∑ j, (∑ i, A z i j * J₂.value (i :: []) z) *
            fderiv ℝ φ z (b j) := by
        rw [integral_finsetSum]
        intro j hj
        exact hflux j
      _ = ∫ z in K 0, ∑ i, ∑ j,
          A z i j * J₂.value (i :: []) z * fderiv ℝ φ z (b j) := by
        congr 1
        funext z
        simp_rw [Finset.sum_mul]
        exact Finset.sum_comm
      _ = ∫ z in K 0, ∑ i, ∑ j,
          A z i j * energyChartDerivative c hKbig hKbig_target (b i)
            (weakPoissonSolution f) z * fderiv ℝ φ z (b j) := by
        apply integral_congr_ae
        filter_upwards [ae_all_iff.mpr hJ₂one] with z hz
        apply Finset.sum_congr rfl
        intro i hi
        simp_rw [hz i]
      _ = -(∫ z in K 0, R z * φ z) := by
        exact hdata0
  have hbaseReaction : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ K 0 →
      (∑ j, ∫ z in K 0, (∑ i, A z i j * J₂.value (i :: []) z) *
        fderiv ℝ φ z (b j)) = -(∫ z in K 0, (F z * J₂.value [] z) * φ z) := by
    intro φ hφ hcφ hsφ
    rw [hbase φ hφ hcφ hsφ]
    congr 1
    apply integral_congr_ae
    filter_upwards [hJ₂root] with z hz
    dsimp only [R]
    rw [hz]
  have hJ₂hier : ReactionHierarchy J₂ A F :=
    reactionHierarchy_of_order_two_equation J₂ hbaseReaction
  have hall := exists_reaction_jets_on_nested_compacts
    (E := E) b (K := K) (S := S) (W := (extChartAt I c).target)
    hK hconv hstep hS hSall (isOpen_extChartAt_target c) hK0target
    A F hA hF hell hLam hEll hbil J₂ hJ₂hier
  have hS0 : S ⊆ K 0 := (hSall 0).trans interior_subset
  have hm : (volume : Measure E).restrict S ≤ volume.restrict (K 0) :=
    Measure.restrict_mono_set _ hS0
  refine ⟨J₂.value [], ?_⟩
  intro n
  obtain ⟨J, hJ, hpres⟩ := hall n
  refine ⟨J, hJ, hpres [] (by simp), ?_⟩
  have hpres0 : (J.value [] : E → ℝ) =ᵐ[volume.restrict S]
      (J₂.value [] : E → ℝ) := by
    have heq : (J.value [] : E → ℝ) = (J₂.value [] : E → ℝ) :=
      congrArg (fun q : Lp ℝ 2 (volume : Measure E) => (q : E → ℝ))
        (hpres [] (by simp))
    filter_upwards [] with z
    exact congrFun heq z
  exact hpres0.trans (hJ₂root.filter_mono (ae_mono hm))


end LichnerowiczObata
