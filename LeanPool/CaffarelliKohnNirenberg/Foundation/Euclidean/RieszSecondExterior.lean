/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.LpDensity
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecondOperator
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.KernelAllOrders
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.KernelAllOrdersPotential
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpApproximation
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.SupportThickening

/-!
# Riesz Second Exterior

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology Convolution Pointwise
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN
open CKN.Foundation.Heat

def rieszSecondExteriorExteriorKernel (i j : Fin 3) : Vec3 → ℝ :=
  -spatialDeriv (spatialDeriv newtonianKernel i) j

private lemma mollifier_tsupp_eq_closedBall {ε : ℝ} (hε : 0 < ε) :
    tsupport (mollifier (d := 3) ε hε) = Metric.closedBall 0 ε := by
  exact (standardMollifier ε hε).tsupport_normed_eq

private lemma thickening_separated {A U : Set Vec3}
    {δ : ℝ}
    (hsep : ∀ x ∈ U, ∀ y ∈ A, δ ≤ vec3EuclideanNorm (x - y))
    (hδ : 0 < δ) :
    ∀ x ∈ U, ∀ y ∈ Metric.closedBall (0 : Vec3) (δ / 12) + closure A,
      δ / 2 ≤ vec3EuclideanNorm (x - y) := by
  intro x hx y hy
  rcases Set.mem_add.mp hy with ⟨z, hz, a, ha, rfl⟩
  have hcl : ∀ a ∈ closure A, δ ≤ vec3EuclideanNorm (x - a) := by
    intro a ha
    apply closure_minimal (hsep x hx)
    have hcont : Continuous (fun a : Vec3 => vec3EuclideanNorm (x - a)) := by
      unfold vec3EuclideanNorm
      fun_prop
    exact isClosed_le continuous_const hcont
    exact ha
  have hz' : ‖z‖ ≤ δ / 12 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  have hza : vec3EuclideanNorm z ≤ δ / 4 := by
    calc
      vec3EuclideanNorm z ≤ 3 * ‖z‖ := euclideanNorm_le_three_mul_space_norm z
      _ ≤ 3 * (δ / 12) := by gcongr
      _ = δ / 4 := by ring
  have htri : vec3EuclideanNorm (x - a) ≤
      vec3EuclideanNorm (x - (z + a)) + vec3EuclideanNorm z := by
    have hdecomp : x - a = (x - (z + a)) + z := by abel
    rw [hdecomp]
    exact vec3EuclideanNorm_triangle _ _
  have hδhalf : 0 < δ / 2 := by positivity
  have hmain : δ ≤ vec3EuclideanNorm (x - (z + a)) + δ / 4 :=
    (hcl a ha).trans (htri.trans (add_le_add_right hza _))
  linarith only [hδhalf, hmain]

private lemma exterior_kernel_continuous (i j : Fin 3) :
    ContinuousOn (rieszSecondExteriorExteriorKernel i j) {z : Vec3 | z ≠ 0} := by
  intro z hz
  exact (newtonianKernel_spatialDeriv_second_continuousAt hz i j).neg.continuousWithinAt

private lemma exterior_kernel_symm {i j : Fin 3} {z : Vec3} (hz : z ≠ 0) :
    spatialDeriv (spatialDeriv newtonianKernel i) j z =
      spatialDeriv (spatialDeriv newtonianKernel j) i z := by
  rw [newtonianKernel_spatialDeriv_second_formula hz i j,
    newtonianKernel_spatialDeriv_second_formula hz j i]
  by_cases hij : i = j
  · simp [hij]
  · have hji : ¬j = i := fun h => hij h.symm
    simp only [hij, hji, ↓reduceIte]
    ring

private lemma kernelPotential_mixedSecond_on {i j : Fin 3} {g : Vec3 → ℝ}
    {A U : Set Vec3} {δ : ℝ} (hg : Integrable g volume) (hU : IsOpen U)
    (hg0 : ∀ y ∉ A, g y = 0) (hδ : 0 < δ)
    (hsep : ∀ x ∈ U, ∀ y ∈ A, δ ≤ vec3EuclideanNorm (x - y)) :
    Set.EqOn (mixedSecond (pressureNewtonianPotential g) i j)
      (fun x => ∫ y, rieszSecondExteriorExteriorKernel i j (x - y) * g y) U := by
  choose C₀ hC₀ hC₀b using exists_norm_iteratedFDeriv_newtonianKernel_le
  have hfdN := fderiv_kernelPotential_eqOn hC₀
    (fun n z hz => contDiffAt_newtonianKernel n hz) hC₀b hg hg0 hδ hsep
  intro x hx
  have hfdNbound : ∀ k : ℕ, ∀ z : Vec3, z ≠ 0 →
      ‖iteratedFDeriv ℝ k (fderiv ℝ newtonianKernel) z‖ ≤
        C₀ (k + 1) * (vec3EuclideanNorm z ^ (2 + k))⁻¹ := by
    intro k z hz
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (iteratedFDeriv_fderiv_bound hC₀b k z hz)
  have hfdNint : ∀ {z : Vec3}, z ∈ U → Integrable
      (fun y : Vec3 => g y • fderiv ℝ newtonianKernel (z - y)) volume := by
    intro z hz
    apply integrable_smul_kernel_shift
    · exact continuousOn_of_kernelSmooth
        (contDiffAt_fderiv_of_kernelSmooth
          (fun n w hw => contDiffAt_newtonianKernel n hw))
    · exact hg
    · exact hg0
    · intro y hy
      have hbound := kernelBound_zero
        (K := fderiv ℝ newtonianKernel) (C := fun k => C₀ (k + 1))
        (m := 2) (δ := δ) (fun k => hC₀ (k + 1)) hfdNbound hδ
      exact hbound (z - y) (hsep z hz y hy)
  have hfdNapply : ∀ {z : Vec3}, z ∈ U →
      (kernelPotential (fderiv ℝ newtonianKernel) g z) (basisVec j) =
        kernelPotential (spatialDeriv newtonianKernel j) g z := by
    intro z hz
    rw [kernelPotential, ContinuousLinearMap.integral_apply (hfdNint hz)]
    apply integral_congr_ae
    filter_upwards [] with y
    simp [spatialDeriv, smul_eq_mul]
  have hfirst : Set.EqOn (spatialDeriv (pressureNewtonianPotential g) j)
      (-kernelPotential (spatialDeriv newtonianKernel j) g) U := by
    intro z hz
    unfold spatialDeriv
    have hpressure : pressureNewtonianPotential g =
        -kernelPotential newtonianKernel g := by
      funext w
      exact pressureNewtonianPotential_eq_neg_kernelPotential g w
    rw [hpressure, fderiv_neg, hfdN hz]
    change -(kernelPotential (fderiv ℝ newtonianKernel) g z) (basisVec j) = _
    rw [hfdNapply hz]
    rfl
  choose C₁ hC₁ hC₁b using
    exists_norm_iteratedFDeriv_newtonianKernel_spatialDeriv_le j
  have hfdK : Set.EqOn
      (fderiv ℝ (kernelPotential (spatialDeriv newtonianKernel j) g))
      (kernelPotential (fderiv ℝ (spatialDeriv newtonianKernel j)) g) U :=
    fderiv_kernelPotential_eqOn hC₁
      (contDiffAt_newtonianKernel_spatialDeriv j) hC₁b hg hg0 hδ hsep
  have hfdKbound : ∀ k : ℕ, ∀ z : Vec3, z ≠ 0 →
      ‖iteratedFDeriv ℝ k
          (fderiv ℝ (spatialDeriv newtonianKernel j)) z‖ ≤
        C₁ (k + 1) * (vec3EuclideanNorm z ^ (3 + k))⁻¹ := by
    intro k z hz
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (iteratedFDeriv_fderiv_bound hC₁b k z hz)
  have hfdKint : Integrable
      (fun y : Vec3 => g y •
        fderiv ℝ (spatialDeriv newtonianKernel j) (x - y)) volume := by
    apply integrable_smul_kernel_shift
    · exact continuousOn_of_kernelSmooth
        (contDiffAt_fderiv_of_kernelSmooth
          (contDiffAt_newtonianKernel_spatialDeriv j))
    · exact hg
    · exact hg0
    · intro y hy
      have hbound := kernelBound_zero
        (K := fderiv ℝ (spatialDeriv newtonianKernel j))
        (C := fun k => C₁ (k + 1)) (m := 3) (δ := δ)
        (fun k => hC₁ (k + 1)) hfdKbound hδ
      exact hbound (x - y) (hsep x hx y hy)
  have hfdKapply :
      (kernelPotential (fderiv ℝ (spatialDeriv newtonianKernel j)) g x)
          (basisVec i) =
        kernelPotential (spatialDeriv (spatialDeriv newtonianKernel j) i) g x := by
    rw [kernelPotential, ContinuousLinearMap.integral_apply hfdKint]
    apply integral_congr_ae
    filter_upwards [] with y
    simp [spatialDeriv, smul_eq_mul]
  have hderiv : fderiv ℝ (spatialDeriv (pressureNewtonianPotential g) j) x =
      fderiv ℝ (-kernelPotential (spatialDeriv newtonianKernel j) g) x := by
    calc
      fderiv ℝ (spatialDeriv (pressureNewtonianPotential g) j) x =
          fderivWithin ℝ (spatialDeriv (pressureNewtonianPotential g) j) U x :=
        (fderivWithin_of_isOpen hU hx).symm
      _ = fderivWithin ℝ (-kernelPotential (spatialDeriv newtonianKernel j) g) U x :=
        fderivWithin_congr' hfirst hx
      _ = fderiv ℝ (-kernelPotential (spatialDeriv newtonianKernel j) g) x :=
        fderivWithin_of_isOpen hU hx
  have htarget : -kernelPotential (spatialDeriv (spatialDeriv newtonianKernel j) i) g x =
      ∫ y, rieszSecondExteriorExteriorKernel i j (x - y) * g y := by
    rw [kernelPotential_real_eq]
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ A
    · have hxy : x - y ≠ 0 := ne_zero_of_vec3EuclideanNorm_pos
          (lt_of_lt_of_le hδ (hsep x hx y hy))
      rw [exterior_kernel_symm hxy]
      simp [rieszSecondExteriorExteriorKernel]
    · rw [hg0 y hy]
      simp
  unfold mixedSecond spatialDeriv
  change (fderiv ℝ (spatialDeriv (pressureNewtonianPotential g) j) x)
      (basisVec i) = _
  rw [hderiv, fderiv_neg, hfdK hx]
  change -(kernelPotential (fderiv ℝ (spatialDeriv newtonianKernel j)) g x)
      (basisVec i) = _
  rw [hfdKapply, htarget]

private lemma integral_norm_le_eLpNorm_of_zero_outside {f : Vec3 → ℝ}
    (hf : MemLp f (2 : ℝ≥0∞) volume) {K : Set Vec3} (hK : MeasurableSet K)
    (hKtop : volume K ≠ ⊤)
    (hzero : ∀ y ∉ K, f y = 0) :
    ∫ y, ‖f y‖ ≤
      (eLpNorm f (2 : ℝ≥0∞) volume).toReal *
        (∫ y, ‖K.indicator (fun _ : Vec3 => (1 : ℝ)) y‖ ^ (2 : ℝ)) ^
          (1 / 2 : ℝ) := by
  have h22 : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) volume := by
    simpa using hf
  have hK' : MemLp (K.indicator (fun _ : Vec3 => (1 : ℝ)))
      (ENNReal.ofReal (2 : ℝ)) volume :=
    memLp_indicator_const _ hK 1 (Or.inr hKtop)
  have hholder := integral_mul_norm_le_Lp_mul_Lq (μ := (volume : Measure Vec3))
    h22 hf' hK'
  have hprod :
      ∫ y, ‖f y‖ * ‖K.indicator (fun _ : Vec3 => (1 : ℝ)) y‖ =
        ∫ y, ‖f y‖ := by
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ K
    · simp [Set.indicator_of_mem hy]
    · have hfy : f y = 0 := hzero y hy
      simp [Set.indicator_of_notMem hy, hfy]
  have hnorm := hf.eLpNorm_eq_integral_rpow_norm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  have hnorm' : eLpNorm f (2 : ℝ≥0∞) volume =
      ENNReal.ofReal ((∫ y, ‖f y‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) := by
    simpa using hnorm
  calc
    ∫ y, ‖f y‖ =
        ∫ y, ‖f y‖ * ‖K.indicator (fun _ : Vec3 => (1 : ℝ)) y‖ := hprod.symm
    _ ≤ (∫ y, ‖f y‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        (∫ y, ‖K.indicator (fun _ : Vec3 => (1 : ℝ)) y‖ ^ (2 : ℝ)) ^
          (1 / 2 : ℝ) := hholder
    _ = (eLpNorm f (2 : ℝ≥0∞) volume).toReal *
        (∫ y, ‖K.indicator (fun _ : Vec3 => (1 : ℝ)) y‖ ^ (2 : ℝ)) ^
          (1 / 2 : ℝ) := by
      rw [hnorm']
      rw [ENNReal.toReal_ofReal]
      positivity

private lemma exterior_kernel_contDiffAt (i j : Fin 3) (k : ℕ)
    {z : Vec3} (hz : z ≠ 0) :
    ContDiffAt ℝ k (rieszSecondExteriorExteriorKernel i j) z := by
  change ContDiffAt ℝ k (fun w : Vec3 =>
    - (fderiv ℝ (spatialDeriv newtonianKernel i) w) (basisVec j)) z
  have hfd : ContDiffAt ℝ k
      (fderiv ℝ (spatialDeriv newtonianKernel i)) z :=
    (contDiffAt_newtonianKernel_spatialDeriv i (k + 1) z hz).fderiv_right_succ
  exact (hfd.clm_apply contDiffAt_const).neg

private lemma exterior_kernel_iterated_bound (i j : Fin 3) (k : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ z : Vec3, z ≠ 0 →
      ‖iteratedFDeriv ℝ k (rieszSecondExteriorExteriorKernel i j) z‖ ≤
        c * (vec3EuclideanNorm z ^ (3 + k))⁻¹ := by
  obtain ⟨c, hc0, hc⟩ :=
    exists_norm_iteratedFDeriv_newtonianKernel_spatialDeriv_le i (k + 1)
  refine ⟨c, hc0, fun z hz => ?_⟩
  have hfd : ContDiffAt ℝ k
      (fderiv ℝ (spatialDeriv newtonianKernel i)) z :=
    (contDiffAt_newtonianKernel_spatialDeriv i (k + 1) z hz).fderiv_right_succ
  have hclm := norm_iteratedFDeriv_clm_apply_const (𝕜 := ℝ) (n := k)
    (c := basisVec j) hfd le_rfl
  have hsucc : ‖iteratedFDeriv ℝ k
      (fderiv ℝ (spatialDeriv newtonianKernel i)) z‖ =
      ‖iteratedFDeriv ℝ (k + 1)
        (spatialDeriv newtonianKernel i) z‖ := norm_iteratedFDeriv_fderiv
  change ‖iteratedFDeriv ℝ k (fun w : Vec3 =>
    - (fderiv ℝ (spatialDeriv newtonianKernel i) w) (basisVec j)) z‖ ≤ _
  rw [show (fun w : Vec3 =>
      - (fderiv ℝ (spatialDeriv newtonianKernel i) w) (basisVec j)) =
      -(fun w : Vec3 =>
        (fderiv ℝ (spatialDeriv newtonianKernel i) w) (basisVec j)) by
        funext w
        rfl]
  rw [iteratedFDeriv_neg, Pi.neg_apply, norm_neg]
  calc
    ‖iteratedFDeriv ℝ k (fun w : Vec3 =>
        (fderiv ℝ (spatialDeriv newtonianKernel i) w) (basisVec j)) z‖ ≤
        ‖basisVec j‖ * ‖iteratedFDeriv ℝ k
          (fderiv ℝ (spatialDeriv newtonianKernel i)) z‖ := hclm
    _ ≤ 1 * ‖iteratedFDeriv ℝ k
          (fderiv ℝ (spatialDeriv newtonianKernel i)) z‖ := by
      exact mul_le_mul_of_nonneg_right (norm_basisVec_le_one j) (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ (k + 1)
          (spatialDeriv newtonianKernel i) z‖ := by rw [hsucc, one_mul]
    _ ≤ c * (vec3EuclideanNorm z ^ (2 + (k + 1)))⁻¹ := hc z hz
    _ = c * (vec3EuclideanNorm z ^ (3 + k))⁻¹ := by
      rw [show 2 + (k + 1) = 3 + k by ring]

theorem rieszSecondL2_exterior_potential_aestronglyMeasurable
    {i j : Fin 3} {b : Vec3 → ℝ} {A U : Set Vec3}
    (hb : Integrable b volume) (hU : IsOpen U)
    (hbA : ∀ y ∉ A, b y = 0) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ x ∈ U, ∀ y ∈ A, δ ≤ vec3EuclideanNorm (x - y)) :
    AEStronglyMeasurable
      (fun x => ∫ y, (-spatialDeriv (spatialDeriv newtonianKernel i) j) (x - y) * b y)
      (volume.restrict U) := by
  choose C hC₀ hC using fun k => exterior_kernel_iterated_bound i j k
  have hcont : ContDiffOn ℝ (0 : ℕ)
      (kernelPotential (rieszSecondExteriorExteriorKernel i j) b) U :=
    contDiffOn_kernelPotential hC₀
      (fun k z hz => exterior_kernel_contDiffAt i j k hz) hC hb hU hbA hδ hsep 0
  have hmeas := ContinuousOn.aestronglyMeasurable (μ := volume)
    hcont.continuousOn hU.measurableSet
  apply hmeas.congr
  filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
  simpa [rieszSecondExteriorExteriorKernel] using (kernelPotential_real_eq (rieszSecondExteriorExteriorKernel i j) b x)

theorem rieszSecondL2_exterior_potential_bound
    {i j : Fin 3} {b : Vec3 → ℝ} {A U : Set Vec3}
    (hb : Integrable b volume) (_ : IsOpen U)
    (hbA : ∀ y ∉ A, b y = 0) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ x ∈ U, ∀ y ∈ A, δ ≤ vec3EuclideanNorm (x - y)) {x : Vec3}
    (hx : x ∈ U) :
    ‖∫ y, (-spatialDeriv (spatialDeriv newtonianKernel i) j) (x - y) * b y‖ ≤
      4 * (4 * Real.pi)⁻¹ * ((δ / 3) ^ 3)⁻¹ * ∫ y, ‖b y‖ := by
  let Cδ : ℝ := 4 * (4 * Real.pi)⁻¹ * ((δ / 3) ^ 3)⁻¹
  have hCδ : 0 ≤ Cδ := by
    dsimp [Cδ]
    positivity
  have hKbd : ∀ y ∈ A, ‖rieszSecondExteriorExteriorKernel i j (x - y)‖ ≤ Cδ := by
    intro y hy
    have hnorm := CKN.euclideanNorm_le_three_mul_space_norm (x - y)
    have hnorm' : vec3EuclideanNorm (x - y) ≤ 3 * ‖x - y‖ := by
      simpa only [CKN.spaceEuclideanNorm, vec3EuclideanNorm] using hnorm
    have hspace : δ / 3 ≤ ‖x - y‖ := by
      linarith only [hsep x hx y hy, hnorm']
    have hne : x - y ≠ 0 := by
      intro hzero
      rw [hzero] at hspace
      simp at hspace
      exact (not_lt_of_ge hspace) (by positivity)
    have hpow := inv_pow_le_inv_pow_of_le (by positivity : 0 < δ / 3)
      hspace 3
    have hcoef : 0 ≤ 4 * (4 * Real.pi)⁻¹ := by positivity
    dsimp [rieszSecondExteriorExteriorKernel, Cδ]
    rw [abs_neg]
    calc
      |spatialDeriv (spatialDeriv newtonianKernel i) j (x - y)| ≤
          4 * (4 * Real.pi)⁻¹ * (‖x - y‖ ^ 3)⁻¹ :=
        newtonianKernel_spatialDeriv_second_size_bound hne i j
      _ ≤ 4 * (4 * Real.pi)⁻¹ * ((δ / 3) ^ 3)⁻¹ :=
        mul_le_mul_of_nonneg_left hpow hcoef
  have hInt : Integrable
      (fun y => rieszSecondExteriorExteriorKernel i j (x - y) * b y) volume := by
    simpa [smul_eq_mul, mul_comm] using
      (integrable_smul_kernel_shift (K := rieszSecondExteriorExteriorKernel i j) (g := b)
        (A := A) (x := x) (exterior_kernel_continuous i j) hb hbA hKbd)
  have hmajor : Integrable (fun y => Cδ * ‖b y‖) volume :=
    hb.norm.const_mul Cδ
  have hpoint : ∀ᵐ y ∂volume,
      ‖rieszSecondExteriorExteriorKernel i j (x - y) * b y‖ ≤ Cδ * ‖b y‖ := by
    filter_upwards [] with y
    by_cases hy : y ∈ A
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hKbd y hy) (norm_nonneg _)
    · rw [hbA y hy, mul_zero, norm_zero, mul_zero]
  change ‖∫ y, rieszSecondExteriorExteriorKernel i j (x - y) * b y‖ ≤ _
  calc
    ‖∫ y, rieszSecondExteriorExteriorKernel i j (x - y) * b y‖ ≤
        ∫ y, ‖rieszSecondExteriorExteriorKernel i j (x - y) * b y‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ y, Cδ * ‖b y‖ :=
      MeasureTheory.integral_mono_ae hInt.norm hmajor hpoint
    _ = Cδ * ∫ y, ‖b y‖ := by rw [integral_const_mul]
    _ = 4 * (4 * Real.pi)⁻¹ * ((δ / 3) ^ 3)⁻¹ * ∫ y, ‖b y‖ := by rfl

theorem rieszSecondL2_exterior_potential_integrableOn_compact
    {i j : Fin 3} {b : Vec3 → ℝ} (hb : Integrable b volume)
    {A U C : Set Vec3} (hU : IsOpen U)
    (hbA : ∀ y ∉ A, b y = 0) (_ : Bornology.IsBounded A) {δ : ℝ}
    (hδ : 0 < δ) (hsep : ∀ x ∈ U, ∀ y ∈ A,
      δ ≤ vec3EuclideanNorm (x - y)) (hC : IsCompact C) (hCU : C ⊆ U) :
    IntegrableOn
      (fun x => ∫ y, (-spatialDeriv (spatialDeriv newtonianKernel i) j) (x - y) * b y)
      C volume := by
  have hmeas := rieszSecondL2_exterior_potential_aestronglyMeasurable
    (i := i) (j := j) hb hU hbA hδ hsep
  have hmeasC : AEStronglyMeasurable
      (fun x => ∫ y, (-spatialDeriv (spatialDeriv newtonianKernel i) j) (x - y) * b y)
      (volume.restrict C) :=
    hmeas.mono_measure (Measure.restrict_mono_set volume hCU)
  apply IntegrableOn.of_bound hC.measure_lt_top hmeasC
    (4 * (4 * Real.pi)⁻¹ * ((δ / 3) ^ 3)⁻¹ * ∫ y, ‖b y‖)
  filter_upwards [ae_restrict_mem hC.measurableSet] with x hx
  exact rieszSecondL2_exterior_potential_bound hb hU hbA hδ hsep
    (hCU hx)

theorem rieszSecondL2_exterior_representation {i j : Fin 3}
    (hL2 : RieszSecondL2Input i j) {b : Vec3 → ℝ}
    (hb₂ : MemLp b (2 : ℝ≥0∞) volume) {A U : Set Vec3} (hU : IsOpen U)
    (hbA : ∀ y ∉ A, b y = 0) (hAb : Bornology.IsBounded A) {δ : ℝ}
    (hδ : 0 < δ)
    (hsep : ∀ x ∈ U, ∀ y ∈ A, δ ≤ vec3EuclideanNorm (x - y)) :
    rieszSecondL2MeasurableOperator hL2 (MemLp.toLp b hb₂) =ᵐ[volume.restrict U]
      (fun x => ∫ y,
        (-spatialDeriv (spatialDeriv newtonianKernel i) j) (x - y) * b y) := by
  let Kset : Set Vec3 := Metric.closedBall (0 : Vec3) (δ / 12) + closure A
  have hKcompact : IsCompact Kset := by
    exact CKN.thickening_compact hAb
  have hKmeas : MeasurableSet Kset := hKcompact.measurableSet
  have hKtop : volume Kset ≠ ⊤ := hKcompact.measure_lt_top.ne
  haveI : IsFiniteMeasure (volume.restrict Kset) :=
    isFiniteMeasure_restrict.mpr hKtop
  have hsepK : ∀ x ∈ U, ∀ y ∈ Kset,
      δ / 2 ≤ vec3EuclideanNorm (x - y) := by
    intro x hx y hy
    exact thickening_separated hsep hδ x hx y hy
  have hbzeroK : ∀ y ∉ Kset, b y = 0 := by
    intro y hy
    have hycl : y ∉ closure A := by
      intro hycl
      apply hy
      exact ⟨0, by simp [Metric.mem_closedBall]; positivity, y, hycl, by simp⟩
    exact hbA y (fun hya => hycl (subset_closure hya))
  have hbKmem : MemLp b (2 : ℝ≥0∞) (volume.restrict Kset) :=
    hb₂.mono_measure Measure.restrict_le_self
  have hbint : Integrable b volume := by
    have hOn : IntegrableOn b Kset volume := MemLp.integrable (by norm_num) hbKmem
    exact hOn.integrable_of_forall_notMem_eq_zero hbzeroK
  let ε : ℕ → ℝ := fun n => δ / 12 * (1 / ((n : ℝ) + 1))
  have hεpos : ∀ n, 0 < ε n := by
    intro n
    dsimp [ε]
    positivity
  have hεzero : Tendsto ε atTop (nhds 0) := by
    simpa [ε] using
      (tendsto_const_nhds.mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  let bₙ : ℕ → Vec3 → ℝ := fun n => mollify b (ε n) (hεpos n)
  have hbₙsupp : ∀ n, Function.support (bₙ n) ⊆ Kset := by
    intro n
    exact CKN.mollify_support_subset (A := A) (δ := δ / 12) (ε := ε n)
      (hεpos n) hbA (by
        dsimp [ε]
        have hden : 0 < (n : ℝ) + 1 := by positivity
        have hone : 1 / ((n : ℝ) + 1) ≤ 1 := by
          rw [div_le_iff₀ hden]
          norm_num
        simpa using
          (mul_le_mul_of_nonneg_left hone (show 0 ≤ δ / 12 by positivity)))
  have hbₙcont : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (bₙ n) := by
    intro n
    exact mollify_contDiff (hεpos n) (hb₂.locallyIntegrable (by norm_num))
  have hbₙcomp : ∀ n, HasCompactSupport (bₙ n) := by
    intro n
    exact HasCompactSupport.of_support_subset_isCompact hKcompact (hbₙsupp n)
  have hbₙmem : ∀ n, MemLp (bₙ n) (2 : ℝ≥0∞) volume := by
    intro n
    exact (hbₙcont n).continuous.memLp_of_hasCompactSupport (hbₙcomp n)
  have hbₙint : ∀ n, Integrable (bₙ n) volume := by
    intro n
    have hmemK : MemLp (bₙ n) (2 : ℝ≥0∞) (volume.restrict Kset) :=
      (hbₙmem n).mono_measure Measure.restrict_le_self
    have hOn : IntegrableOn (bₙ n) Kset volume :=
      MemLp.integrable (by norm_num) hmemK
    exact hOn.integrable_of_forall_notMem_eq_zero (fun y hy => by
        by_contra hne
        exact hy (hbₙsupp n hne))
  have hsource : Tendsto
      (fun n => eLpNorm (bₙ n - b) (2 : ℝ≥0∞) volume) atTop (nhds 0) := by
    change Tendsto (fun n => eLpNorm (fun x => bₙ n x - b x)
      (2 : ℝ≥0∞) volume) atTop (nhds 0)
    simpa [bₙ] using
      (tendsto_eLpNorm_sub_zero_mollify (p := (2 : ENNReal)) (by norm_num)
        (by norm_num) hb₂ hεzero hεpos)
  let uₙ : ℕ → rieszSecondL2 := fun n =>
    MemLp.toLp (bₙ n) (hbₙmem n)
  let u₀ : rieszSecondL2 := MemLp.toLp b hb₂
  have hTsource : Tendsto
      (fun n => eLpNorm
        (rieszSecondL2MeasurableOperator hL2 (uₙ n) -
          rieszSecondL2MeasurableOperator hL2 u₀)
        (2 : ℝ≥0∞) volume) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsource
    · intro n
      exact bot_le
    · intro n
      have hdiffmem : MemLp (bₙ n - b) (2 : ℝ≥0∞) volume :=
        (hbₙmem n).sub hb₂
      have hdiff : MemLp.toLp (bₙ n - b) hdiffmem = uₙ n - u₀ := by
        simpa [uₙ, u₀] using MemLp.toLp_sub (hbₙmem n) hb₂
      have hadd := rieszSecondL2MeasurableOperator_add_ae hL2
        (uₙ n - u₀) u₀
      have hTdiff :
          rieszSecondL2MeasurableOperator hL2 (uₙ n - u₀) =ᵐ[volume]
            rieszSecondL2MeasurableOperator hL2 (uₙ n) -
              rieszSecondL2MeasurableOperator hL2 u₀ := by
        rw [show (uₙ n - u₀) + u₀ = uₙ n by abel] at hadd
        filter_upwards [hadd] with x hx
        calc
          rieszSecondL2MeasurableOperator hL2 (uₙ n - u₀) x =
              (rieszSecondL2MeasurableOperator hL2 (uₙ n - u₀) x +
                rieszSecondL2MeasurableOperator hL2 u₀ x) -
                rieszSecondL2MeasurableOperator hL2 u₀ x := by ring
          _ = rieszSecondL2MeasurableOperator hL2 (uₙ n) x -
              rieszSecondL2MeasurableOperator hL2 u₀ x := by
            have hx' : rieszSecondL2MeasurableOperator hL2 (uₙ n) x =
                rieszSecondL2MeasurableOperator hL2 (uₙ n - u₀) x +
                  rieszSecondL2MeasurableOperator hL2 u₀ x := by
              simpa only [Pi.add_apply] using hx
            rw [← hx']
      calc
        eLpNorm
            (rieszSecondL2MeasurableOperator hL2 (uₙ n) -
              rieszSecondL2MeasurableOperator hL2 u₀)
            (2 : ℝ≥0∞) volume =
            eLpNorm (rieszSecondL2MeasurableOperator hL2
              (uₙ n - u₀)) (2 : ℝ≥0∞) volume :=
          eLpNorm_congr_ae hTdiff.symm
        _ ≤ eLpNorm (MemLp.toLp (bₙ n - b) hdiffmem : Vec3 → ℝ)
            (2 : ℝ≥0∞) volume := by
          have hop := rieszSecondL2MeasurableOperator_eLpNorm_le hL2 (uₙ n - u₀)
          rw [← hdiff] at hop
          exact hop
        _ = eLpNorm (bₙ n - b) (2 : ℝ≥0∞) volume := by
          exact eLpNorm_congr_ae (MemLp.coeFn_toLp hdiffmem)
  have hreal : Tendsto
      (fun n => (eLpNorm (fun y => bₙ n y - b y)
        (2 : ℝ≥0∞) volume).toReal)
      atTop (nhds 0) := by
    apply (ENNReal.tendsto_toReal_zero_iff
      (fun n => ((hbₙmem n).sub hb₂).eLpNorm_ne_top)).mpr
    simpa only [Pi.sub_apply] using hsource
  let C_K : ℝ :=
    (∫ y, ‖Kset.indicator (fun _ : Vec3 => (1 : ℝ)) y‖ ^ (2 : ℝ)) ^
      (1 / 2 : ℝ)
  have hL1bound : ∀ n, ∫ y, ‖bₙ n y - b y‖ ≤
      (eLpNorm (fun y => bₙ n y - b y)
        (2 : ℝ≥0∞) volume).toReal * C_K := by
    intro n
    have hdiffzero : ∀ y ∉ Kset, bₙ n y - b y = 0 := by
      intro y hy
      have hbnzero : bₙ n y = 0 := by
        by_contra hne
        exact hy (hbₙsupp n hne)
      rw [hbnzero, hbzeroK y hy, sub_zero]
    simpa [C_K] using
      (integral_norm_le_eLpNorm_of_zero_outside
        (f := fun y => bₙ n y - b y) ((hbₙmem n).sub hb₂)
        hKmeas hKtop hdiffzero)
  have hL1 : Tendsto (fun n => ∫ y, ‖bₙ n y - b y‖)
      atTop (nhds 0) := by
    have hL1' : Tendsto (fun n => ∫ y, ‖bₙ n y - b y‖)
        atTop (nhds (0 * C_K)) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (hreal.mul tendsto_const_nhds)
      · intro n
        simpa only [zero_mul] using
          (integral_nonneg (fun y => norm_nonneg (bₙ n y - b y)))
      · exact hL1bound
    simpa only [zero_mul] using hL1'
  let M : ℝ := 4 * (4 * Real.pi)⁻¹ * ((δ / 6) ^ 3)⁻¹
  have hMnonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have hKbd : ∀ x ∈ U, ∀ y ∈ Kset,
      ‖rieszSecondExteriorExteriorKernel i j (x - y)‖ ≤ M := by
    intro x hx y hy
    have hsep' := hsepK x hx y hy
    have hspace : δ / 6 ≤ ‖x - y‖ := by
      have hnorm := CKN.euclideanNorm_le_three_mul_space_norm (x - y)
      have hnorm' : vec3EuclideanNorm (x - y) ≤ 3 * ‖x - y‖ := by
        simpa only [CKN.spaceEuclideanNorm, vec3EuclideanNorm] using hnorm
      linarith only [hsep', hnorm']
    have hne : x - y ≠ 0 := by
      intro hzero
      rw [hzero] at hspace
      simp at hspace
      exact (not_lt_of_ge hspace) (by positivity)
    have hpow := inv_pow_le_inv_pow_of_le (by positivity : 0 < δ / 6)
      hspace 3
    have hcoef : 0 ≤ 4 * (4 * Real.pi)⁻¹ := by positivity
    dsimp [rieszSecondExteriorExteriorKernel, M]
    rw [abs_neg]
    calc
      |spatialDeriv (spatialDeriv newtonianKernel i) j (x - y)| ≤
          4 * (4 * Real.pi)⁻¹ * (‖x - y‖ ^ 3)⁻¹ :=
        newtonianKernel_spatialDeriv_second_size_bound hne i j
      _ ≤ 4 * (4 * Real.pi)⁻¹ * ((δ / 6) ^ 3)⁻¹ :=
        mul_le_mul_of_nonneg_left hpow hcoef
  have hIntB : ∀ x ∈ U, Integrable
      (fun y => rieszSecondExteriorExteriorKernel i j (x - y) * b y) volume := by
    intro x hx
    simpa [smul_eq_mul, mul_comm] using
      (integrable_smul_kernel_shift (K := rieszSecondExteriorExteriorKernel i j) (g := b)
        (A := Kset) (x := x) (exterior_kernel_continuous i j) hbint hbzeroK
        (hKbd x hx))
  have hIntBn : ∀ n x, x ∈ U → Integrable
      (fun y => rieszSecondExteriorExteriorKernel i j (x - y) * bₙ n y) volume := by
    intro n x hx
    simpa [smul_eq_mul, mul_comm] using
      (integrable_smul_kernel_shift (K := rieszSecondExteriorExteriorKernel i j) (g := bₙ n)
        (A := Kset) (x := x) (exterior_kernel_continuous i j) (hbₙint n)
        (fun y hy => by
          by_contra hne
          exact hy (hbₙsupp n hne)) (hKbd x hx))
  have hIntDiff : ∀ n x, x ∈ U → Integrable
      (fun y => rieszSecondExteriorExteriorKernel i j (x - y) * (bₙ n y - b y)) volume := by
    intro n x hx
    simpa [smul_eq_mul, mul_comm] using
      (integrable_smul_kernel_shift (K := rieszSecondExteriorExteriorKernel i j)
        (g := fun y => bₙ n y - b y) (A := Kset) (x := x)
        (exterior_kernel_continuous i j) ((hbₙint n).sub hbint)
        (fun y hy => by
          have hbnzero : bₙ n y = 0 := by
            by_contra hne
            exact hy (hbₙsupp n hne)
          rw [hbnzero, hbzeroK y hy, sub_zero]) (hKbd x hx))
  have hsplit : ∀ n x, ∀ hx : x ∈ U,
      (∫ y, rieszSecondExteriorExteriorKernel i j (x - y) * bₙ n y) -
          ∫ y, rieszSecondExteriorExteriorKernel i j (x - y) * b y =
        ∫ y, rieszSecondExteriorExteriorKernel i j (x - y) * (bₙ n y - b y) := by
    intro n x hx
    rw [← integral_sub (hIntBn n x hx) (hIntB x hx)]
    apply integral_congr_ae
    filter_upwards [] with y
    ring
  have hnorm_kernel_diff : ∀ n x, ∀ hx : x ∈ U,
      ‖(∫ y, rieszSecondExteriorExteriorKernel i j (x - y) * bₙ n y) -
          ∫ y, rieszSecondExteriorExteriorKernel i j (x - y) * b y‖ ≤
        M * ∫ y, ‖bₙ n y - b y‖ := by
    intro n x hx
    have hmajor : Integrable (fun y => M * ‖bₙ n y - b y‖) volume := by
      simpa [mul_comm] using (((hbₙint n).sub hbint).norm.const_mul M)
    have hpoint : ∀ᵐ y ∂volume,
        ‖rieszSecondExteriorExteriorKernel i j (x - y) * (bₙ n y - b y)‖ ≤
          M * ‖bₙ n y - b y‖ := by
      filter_upwards [] with y
      by_cases hy : y ∈ Kset
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hKbd x hx y hy) (norm_nonneg _)
      · have hzero : bₙ n y - b y = 0 := by
          have hbnzero : bₙ n y = 0 := by
            by_contra hne
            exact hy (hbₙsupp n hne)
          rw [hbnzero, hbzeroK y hy, sub_zero]
        rw [hzero, mul_zero, norm_zero, mul_zero]
    calc
      ‖(∫ y, rieszSecondExteriorExteriorKernel i j (x - y) * bₙ n y) -
          ∫ y, rieszSecondExteriorExteriorKernel i j (x - y) * b y‖ =
          ‖∫ y, rieszSecondExteriorExteriorKernel i j (x - y) * (bₙ n y - b y)‖ := by
            rw [hsplit n x hx]
      _ ≤ ∫ y, ‖rieszSecondExteriorExteriorKernel i j (x - y) * (bₙ n y - b y)‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ y, M * ‖bₙ n y - b y‖ :=
        MeasureTheory.integral_mono_ae (hIntDiff n x hx).norm hmajor hpoint
      _ = M * ∫ y, ‖bₙ n y - b y‖ := by
        rw [integral_const_mul]
  have hKernelTendsto : ∀ x ∈ U, Tendsto
      (fun n => ∫ y, rieszSecondExteriorExteriorKernel i j (x - y) * bₙ n y) atTop
      (nhds (∫ y, rieszSecondExteriorExteriorKernel i j (x - y) * b y)) := by
    intro x hx
    have hQ : Tendsto (fun n => M * ∫ y, ‖bₙ n y - b y‖)
        atTop (nhds 0) := by
      simpa only [mul_zero] using (tendsto_const_nhds.mul hL1)
    have hD : Tendsto
        (fun n => (∫ y, rieszSecondExteriorExteriorKernel i j (x - y) * bₙ n y) -
          ∫ y, rieszSecondExteriorExteriorKernel i j (x - y) * b y) atTop (nhds 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le
        (by simpa only [neg_zero] using hQ.neg) hQ
      · intro n
        have hn := hnorm_kernel_diff n x hx
        have habs : |(∫ y, rieszSecondExteriorExteriorKernel i j (x - y) * bₙ n y) -
            ∫ y, rieszSecondExteriorExteriorKernel i j (x - y) * b y| ≤
            M * ∫ y, ‖bₙ n y - b y‖ := by
          simpa only [Real.norm_eq_abs] using hn
        exact neg_le_of_abs_le habs
      · intro n
        have hn := hnorm_kernel_diff n x hx
        have habs : |(∫ y, rieszSecondExteriorExteriorKernel i j (x - y) * bₙ n y) -
            ∫ y, rieszSecondExteriorExteriorKernel i j (x - y) * b y| ≤
            M * ∫ y, ‖bₙ n y - b y‖ := by
          simpa only [Real.norm_eq_abs] using hn
        exact le_of_abs_le habs
    have hsum := hD.add
      (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
        ∫ y, rieszSecondExteriorExteriorKernel i j (x - y) * b y) atTop
        (nhds (∫ y, rieszSecondExteriorExteriorKernel i j (x - y) * b y)))
    simpa only [sub_add_cancel, zero_add] using hsum
  have hTn_kernel : ∀ n, rieszSecondL2MeasurableOperator hL2 (uₙ n) =ᵐ[
      volume.restrict U] (fun x =>
        ∫ y, rieszSecondExteriorExteriorKernel i j (x - y) * bₙ n y) := by
    intro n
    obtain ⟨hmem, hext⟩ := rieszSecondL2Extension_smooth_hessian hL2
      (hbₙcont n) (hbₙcomp n)
    have hext' : rieszSecondL2Extension hL2 (uₙ n) =
        MemLp.toLp (mixedSecond (pressureNewtonianPotential (bₙ n)) i j) hmem := by
      simpa [uₙ] using hext
    have hrep : rieszSecondL2MeasurableOperator hL2 (uₙ n) =ᵐ[volume]
        mixedSecond (pressureNewtonianPotential (bₙ n)) i j := by
      filter_upwards [rieszSecondL2MeasurableOperator_ae_eq_extension hL2
          (uₙ n), MemLp.coeFn_toLp hmem] with x hx₁ hx₂
      rw [hx₁, hext', hx₂]
    have hmix := kernelPotential_mixedSecond_on (i := i) (j := j)
      (g := bₙ n) (A := Kset) (U := U) (δ := δ / 2) (hbₙint n) hU
      (fun y hy => by
        by_contra hne
        exact hy (hbₙsupp n hne)) (by positivity) hsepK
    filter_upwards [ae_restrict_of_ae hrep,
      ae_restrict_mem hU.measurableSet] with x hxrep hxU
    rw [hxrep, hmix hxU]
  have hTn_all : ∀ᵐ x ∂volume.restrict U, ∀ n,
      rieszSecondL2MeasurableOperator hL2 (uₙ n) x =
        ∫ y, rieszSecondExteriorExteriorKernel i j (x - y) * bₙ n y := by
    exact ae_all_iff.mpr (fun n => hTn_kernel n)
  obtain ⟨ns, hnsmono, hTae⟩ :=
    ae_subsequence_of_eLpNorm_tendsto_zero (p := (2 : ℝ≥0∞))
      (by norm_num) (f := fun n =>
        rieszSecondL2MeasurableOperator hL2 (uₙ n))
      (g := rieszSecondL2MeasurableOperator hL2 u₀) (by
        simpa only [Pi.sub_apply] using hTsource)
  have hIae : ∀ᵐ x ∂volume.restrict U, Tendsto
      (fun n => ∫ y, rieszSecondExteriorExteriorKernel i j (x - y) * bₙ (ns n) y) atTop
      (nhds (∫ y, rieszSecondExteriorExteriorKernel i j (x - y) * b y)) := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact (hKernelTendsto x hx).comp hnsmono.tendsto_atTop
  filter_upwards [ae_restrict_of_ae hTae, hTn_all, hIae] with x hxT hxall hxI
  have hxT' : Tendsto
      (fun n => ∫ y, rieszSecondExteriorExteriorKernel i j (x - y) * bₙ (ns n) y) atTop
      (nhds (rieszSecondL2MeasurableOperator hL2 (u₀) x)) := by
    apply hxT.congr'
    exact Eventually.of_forall (fun n => hxall (ns n))
  have hxlim := tendsto_nhds_unique hxT' hxI
  simpa [u₀, rieszSecondExteriorExteriorKernel] using hxlim

end CKN.Foundation.Euclidean
