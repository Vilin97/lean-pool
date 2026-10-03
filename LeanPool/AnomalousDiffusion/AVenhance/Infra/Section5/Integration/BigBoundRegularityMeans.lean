/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.CoarseCoeff.Representation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.BigBound
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.Energy.AnsatzRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesDiffusion
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TIterateSmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowGlobalJointSmoothness
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowSpatialPeriodicity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ChiMKCorrector
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.StreamFlowPiola
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FlowPiolaIdentity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.DivergenceLinearity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.GradientChain
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FrozenAnsatzTime
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SMatRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.ResidualPointwiseConstructor
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.CorrectorFluxGradient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.MatrixFluxProduct
public import Mathlib.Analysis.Matrix.Normed

/-! Mean-zero identities for the Section 5 residual terms. -/

@[expose] public section

noncomputable section

open Filter Homogenization MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

namespace AVenhance.Infra.Section5.Integration

open AVenhance AVenhance.Infra.Section5

theorem BigBoundRegularityMeans.meanZeroOn_vecDiv_of_contDiff_periodic {F : Vec 2 → Vec 2}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hper : IsZ2Periodic F) :
    MeanZeroOn unitCube (fun x => vecDiv F x) := by
  unfold MeanZeroOn
  have hconst : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec 2 => (1 : ℝ)) := contDiff_const
  have hconstPer : IsZ2Periodic (fun _ : Vec 2 => (1 : ℝ)) := by
    intro k x
    rfl
  have hparts := AVenhance.Infra.Section4.iterate_divergence_pairing
    hconst hconstPer hF hper
  have hgrad : (fun x => spaceGrad (fun _ : Vec 2 => (1 : ℝ)) x) =
      fun _ => (0 : Vec 2) := by
    funext x
    funext i
    simp [spaceGrad, fderiv_const_apply]
  calc
    (∫ x in unitCube, vecDiv F x) =
        ∫ x in unitCube, (1 : ℝ) * vecDiv F x := by
          congr 1
          funext x
          ring
    _ = 0 := by rw [hparts]; simp [hgrad, vecDot]

theorem BigBoundRegularityMeans.vecDiv_scalar_mul {q : Vec 2 → ℝ} {F : Vec 2 → Vec 2} {x : Vec 2}
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    vecDiv (fun y => q y • F y) x =
      vecDot (spaceGrad q x) (F x) + q x * vecDiv F x := by
  have hqDiff := hq.differentiable (by simp) x
  unfold vecDiv vecDot
  have hterm (i : Fin 2) :
      spaceGrad (fun y => q y • F y i) x i =
        spaceGrad q x i * F x i + q x * spaceGrad (fun y => F y i) x i := by
    change fderiv ℝ (fun y => q y * F y i) x (basisVec i) = _
    have hFi : ContDiff ℝ (⊤ : ℕ∞) (fun y => F y i) :=
      contDiff_pi.mp hF i
    have hmul := fderiv_mul hqDiff (hFi.differentiable (by simp) x)
    have hfun : (fun y => q y * F y i) = q * (fun y => F y i) := by
      funext y
      rfl
    have hmul' : fderiv ℝ (fun y => q y * F y i) x =
        q x • fderiv ℝ (fun y => F y i) x +
          F x i • fderiv ℝ q x := by
      rw [hfun, hmul]
    rw [hmul']
    simp [spaceGrad, smul_eq_mul]
    ring
  calc
    (∑ i : Fin 2, spaceGrad (fun y => q y • F y i) x i) =
        ∑ i : Fin 2, (spaceGrad q x i * F x i +
          q x * spaceGrad (fun y => F y i) x i) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hterm i
    _ = (∑ i : Fin 2, spaceGrad q x i * F x i) +
        q x * ∑ i : Fin 2, spaceGrad (fun y => F y i) x i := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]

theorem BigBoundRegularityMeans.sigmaGrad_div_zero {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec 2) :
    vecDiv (fun y => sigmaMat.mulVec (spaceGrad f y)) x = 0 := by
  have hcomm := Infra.Section4.iterate_coordinate_derivatives_commute hf
    (0 : Fin 2) 1 x
  unfold vecDiv
  simp only [Fin.sum_univ_two]
  have h0 : (fun y => sigmaMat.mulVec (spaceGrad f y) 0) =
      fun y => -spaceGrad f y 1 := by
    funext y
    simp [sigmaMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h1 : (fun y => sigmaMat.mulVec (spaceGrad f y) 1) =
      fun y => spaceGrad f y 0 := by
    funext y
    simp [sigmaMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [h0, h1]
  have hneg : spaceGrad (fun y => -(spaceGrad f y 1)) x 0 =
      -spaceGrad (fun y => spaceGrad f y 1) x 0 := by simp [spaceGrad]
  rw [hneg, hcomm]
  ring

theorem BigBoundRegularityMeans.chiMK_div_zero {β : ℝ} (I : Ingredients β)
    (m : ℕ) (κ : ℝ) (k : ℤ) (t : ℝ) (x : Vec 2) :
    vecDiv (fun y => I.chiMK κ m k t y) x = 0 := by
  have hε : epsilon β I.Λ m ≠ 0 :=
    ne_of_gt (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le)
  have hu (y : Vec 2) := Infra.Section3.uShear_eq_sigma_spaceGrad
    (β := β) (Λ := I.Λ) (m := m) k y hε
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (psi β I.Λ m k) := by
    unfold psi
    have hprofile : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec 2 => psi0 k ((epsilon β I.Λ m)⁻¹ • x)) := by
      unfold psi0
      split_ifs <;> fun_prop
    exact contDiff_const.mul hprofile
  have huEq : uShear β I.Λ m k =
      fun y => sigmaMat.mulVec (spaceGrad (psi β I.Λ m k) y) := by
    funext y
    exact hu y
  have hfield : (fun y => I.chiMK κ m k t y) =
      fun y => (-(I.corrTime κ m k t)) •
        (sigmaMat.mulVec (spaceGrad (psi β I.Λ m k) y)) := by
    funext y
    rw [show I.chiMK κ m k t y =
      (-(I.corrTime κ m k t)) • uShear β I.Λ m k y by rfl, huEq]
  rw [hfield]
  have hF : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => sigmaMat.mulVec (spaceGrad (psi β I.Λ m k) y)) := by
    have hgrad := Infra.Section4.iterate_gradient_smooth hψ
    apply contDiff_pi.mpr
    intro i
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun y => ∑ j : Fin 2, sigmaMat i j * spaceGrad
        (psi β I.Λ m k) y j)
    apply ContDiff.sum
    intro j hj
    exact contDiff_const.mul (contDiff_pi.mp hgrad j)
  have hmul := BigBoundRegularityMeans.vecDiv_scalar_mul
    (q := fun _ : Vec 2 => -(I.corrTime κ m k t))
    (F := fun y => sigmaMat.mulVec (spaceGrad (psi β I.Λ m k) y))
    (x := x) contDiff_const hF
  rw [hmul, BigBoundRegularityMeans.sigmaGrad_div_zero hψ x]
  simp [spaceGrad, fderiv_const_apply, vecDot]

/-- Corrector flux in flow coordinates used in the mean-value regularity estimates. -/
def BigBoundRegularityMeans.chiPushforwardFlux {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (k : ℤ) (t : ℝ) : Vec 2 → Vec 2 :=
  fun x => (I.flowGrad hΦ m (lIdx β I.Λ m k) t x).transpose.mulVec
    (I.chiTilde hΦ m κ k t x)

theorem BigBoundRegularityMeans.chiTilde_isZ2Periodic {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (k : ℤ) (t : ℝ) :
    IsZ2Periodic (I.chiTilde hΦ m κ k t) := by
  intro z x
  have hinv := Infra.Section4.amnr_xFlowInv_lattice_equivariant I hΦ m
    (lIdx β I.Λ m k) t z x
  have hu := uShear_isZ2Periodic β I.Λ m k z
    (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)
  simp only [Ingredients.chiTilde, Ingredients.chiMK]
  rw [hinv, hu]

theorem BigBoundRegularityMeans.chiPushforwardFlux_regular {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (k : ℤ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (BigBoundRegularityMeans.chiPushforwardFlux I hΦ m κ k t) ∧
      IsZ2Periodic (BigBoundRegularityMeans.chiPushforwardFlux I hΦ m κ k t) ∧
      (∀ x, vecDiv (BigBoundRegularityMeans.chiPushforwardFlux I hΦ m κ k t) x = 0) := by
  have hFij (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => I.flowGrad hΦ m (lIdx β I.Λ m k) t x i j) :=
    (Infra.Section4.amnr_flowGrad_joint_contDiff_infty I hΦ m
      (lIdx β I.Λ m k) i j).comp
        (by fun_prop : ContDiff ℝ (⊤ : ℕ∞)
          (fun x : Vec 2 => (t, x)))
  have hχ : ContDiff ℝ (⊤ : ℕ∞) (I.chiTilde hΦ m κ k t) := by
    have hY : ContDiff ℝ (⊤ : ℕ∞)
        (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) :=
      (Infra.Section4.amnr_xFlowInv_joint_contDiff_infty I hΦ m
        (lIdx β I.Λ m k)).comp
        (by fun_prop : ContDiff ℝ (⊤ : ℕ∞)
          (fun x : Vec 2 => (t, x)))
    apply contDiff_pi.mpr
    intro i
    have hu : ContDiff ℝ (⊤ : ℕ∞)
        (fun x => uShear β I.Λ m k
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) i) := by
      exact (contDiff_apply ℝ ℝ i).comp
        ((contDiff_uShear' β I.Λ m k).comp hY)
    simpa [Ingredients.chiTilde, Ingredients.chiMK] using
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
        (fun _ : Vec 2 => -(I.corrTime κ m k t))).mul hu
  have hFper : IsZ2Periodic (I.flowGrad hΦ m (lIdx β I.Λ m k) t) := by
    intro z x
    ext i j
    exact Infra.Section4.amnr_flowGrad_spatial_periodic I hΦ m
      (lIdx β I.Λ m k) t i j z x
  have hχper : IsZ2Periodic (I.chiTilde hΦ m κ k t) := by
    exact BigBoundRegularityMeans.chiTilde_isZ2Periodic I hΦ m κ k t
  have hcofactor (x : Vec 2) :
      rowCofactor (gradMatrix (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) x) =
        (I.flowGrad hΦ m (lIdx β I.Λ m k) t x).transpose :=
    Infra.Section5.xFlowInv_rowCofactor_eq_flowGrad_transpose I hΦ m
      (lIdx β I.Λ m k) t x
      (Infra.Section5.streamVel_spatialDivergence_eq_zero I hΦ m)
  constructor
  · apply contDiff_pi.mpr
    intro i
    change ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ j : Fin 2,
      (I.flowGrad hΦ m (lIdx β I.Λ m k) t x).transpose i j *
        I.chiTilde hΦ m κ k t x j)
    apply ContDiff.sum
    intro j hj
    exact (hFij j i).mul
      (contDiff_pi.mp hχ j)
  constructor
  · intro z x
    funext i
    change (∑ j : Fin 2,
      (I.flowGrad hΦ m (lIdx β I.Λ m k) t (x + latticeShift z)).transpose i j *
        I.chiTilde hΦ m κ k t (x + latticeShift z) j) =
      ∑ j : Fin 2,
        (I.flowGrad hΦ m (lIdx β I.Λ m k) t x).transpose i j *
          I.chiTilde hΦ m κ k t x j
    apply Finset.sum_congr rfl
    intro j hj
    rw [hFper z x, hχper z x]
  · intro x
    have hχ2 : ContDiff ℝ 2 (fun y => I.chiMK κ m k t y) := by
      apply contDiff_pi.mpr
      intro i
      exact (Infra.Section3.chiMK_component_contDiff_two I κ k i).comp
        (by fun_prop : ContDiff ℝ 2 (fun y : Vec 2 => (t, y)))
    have hpiola := Infra.Section5.xFlowInv_cofactorPiola_of_streamSeq
      I hΦ m (lIdx β I.Λ m k) t x
      ((hχ2.differentiable (by norm_num) _).hasFDerivAt)
    have hflux : BigBoundRegularityMeans.chiPushforwardFlux I hΦ m κ k t = fun y =>
        (rowCofactor (gradMatrix
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) y)).mulVec
          (I.chiMK κ m k t
            (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y)) := by
      funext y
      change (I.flowGrad hΦ m (lIdx β I.Λ m k) t y).transpose.mulVec _ = _
      rw [hcofactor y]
      rfl
    rw [hflux]
    simpa using hpiola.trans
      (BigBoundRegularityMeans.chiMK_div_zero I m κ k t (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))

theorem BigBoundRegularityMeans.meanZeroOn_finite_weighted_divergence
    {ι : Type*} (U : Finset ι) (c : ι → ℝ)
    (F : ι → Vec 2 → Vec 2)
    (hFsm : ∀ i ∈ U, ContDiff ℝ (⊤ : ℕ∞) (F i))
    (hFper : ∀ i ∈ U, IsZ2Periodic (F i)) :
    MeanZeroOn unitCube (fun x => vecDiv (fun y =>
      ∑ i ∈ U, c i • F i y) x) := by
  classical
  have hWsm : ContDiff ℝ (⊤ : ℕ∞) (fun y => ∑ i ∈ U, c i • F i y) := by
    apply ContDiff.sum
    intro i hi
    exact (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec 2 => c i)).smul
      (hFsm i hi)
  have hWper : IsZ2Periodic (fun y => ∑ i ∈ U, c i • F i y) := by
    intro z x
    funext j
    change (∑ i ∈ U, c i • F i (x + latticeShift z)) j =
      (∑ i ∈ U, c i • F i x) j
    simp only [Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun v : Vec 2 => c i • v j) (hFper i hi z x)
  exact BigBoundRegularityMeans.meanZeroOn_vecDiv_of_contDiff_periodic hWsm hWper

theorem BigBoundRegularityMeans.meanZeroOn_weighted_grad_pairing
    {ι : Type*} (U : Finset ι) (c : ι → ℝ)
    (q : ι → Vec 2 → ℝ) (P : ι → Vec 2 → Vec 2)
    (hqsm : ∀ i ∈ U, ContDiff ℝ (⊤ : ℕ∞) (q i))
    (hqper : ∀ i ∈ U, IsZ2Periodic (q i))
    (hPsm : ∀ i ∈ U, ContDiff ℝ (⊤ : ℕ∞) (P i))
    (hPper : ∀ i ∈ U, IsZ2Periodic (P i))
    (hPdiv : ∀ i ∈ U, ∀ x, vecDiv (P i) x = 0) :
    MeanZeroOn unitCube (fun x => ∑ i ∈ U,
      c i * vecDot (spaceGrad (q i) x) (P i x)) := by
  classical
  let F : ι → Vec 2 → Vec 2 := fun i x => q i x • P i x
  have hFsm (i : ι) (hi : i ∈ U) : ContDiff ℝ (⊤ : ℕ∞) (F i) :=
    (hqsm i hi).smul (hPsm i hi)
  have hFper (i : ι) (hi : i ∈ U) : IsZ2Periodic (F i) := by
    intro z x
    change q i (x + latticeShift z) • P i (x + latticeShift z) = _
    rw [hqper i hi z x, hPper i hi z x]
  have hsum := BigBoundRegularityMeans.meanZeroOn_finite_weighted_divergence U c F hFsm hFper
  have hdiv (i : ι) (hi : i ∈ U) (x : Vec 2) :
      vecDiv (F i) x = vecDot (spaceGrad (q i) x) (P i x) := by
    change vecDiv (fun y => q i y • P i y) x = _
    rw [BigBoundRegularityMeans.vecDiv_scalar_mul (hqsm i hi) (hPsm i hi), hPdiv i hi x]
    simp
  have hderiv (i : ι) (hi : i ∈ U) (x : Vec 2) :
      HasFDerivAt (F i) (fderiv ℝ (F i) x) x :=
    ((hFsm i hi).differentiable (by simp) x).hasFDerivAt
  have hpoint (x : Vec 2) :
      vecDiv (fun y => ∑ i ∈ U, c i • F i y) x =
        ∑ i ∈ U, c i * vecDot (spaceGrad (q i) x) (P i x) := by
    rw [Infra.Section5.vecDiv_finite_weighted_sum U c F x
      (fun i hi => hderiv i hi x)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hdiv i hi x]
  unfold MeanZeroOn at hsum ⊢
  have hfun : (fun x => ∑ i ∈ U,
      c i * vecDot (spaceGrad (q i) x) (P i x)) =
      fun x => vecDiv (fun y => ∑ i ∈ U, c i • F i y) x := by
    funext x
    exact (hpoint x).symm
  rw [hfun]
  exact hsum

theorem BigBoundRegularityMeans.xFlowInv_right_inverse {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (l : ℤ) (t : ℝ) (x : Vec 2) :
    I.xFlow hΦ m l t (I.xFlowInv hΦ m l t x) = x := by
  let b := streamVel (Φ (m - 1))
  let F := flow b (hΦ.adm_pred m).vel_continuous
    (hΦ.adm_pred m).vel_lipschitz
  have hF : IsFlow b F := flow_isFlow b
    (hΦ.adm_pred m).vel_continuous (hΦ.adm_pred m).vel_lipschitz
  let s := (l : ℝ) * tauPP β I.Λ m
  change F t (F s x t) s = x
  calc
    F t (F s x t) s = F t x t :=
      Infra.Flow.flow_group_law b (hΦ.adm_pred m).vel_lipschitz hF x t s t
    _ = x := hF.1 x t

theorem BigBoundRegularityMeans.vecDot_matrixMulVec_transpose (A : Matrix (Fin 2) (Fin 2) ℝ)
    (u v : Vec 2) :
    vecDot u (A.mulVec v) = vecDot (A.transpose.mulVec u) v := by
  simp [vecDot, Matrix.mulVec, dotProduct, Matrix.transpose, Fin.sum_univ_two]
  ring

theorem BigBoundRegularityMeans.vecDot_comm (u v : Vec 2) : vecDot u v = vecDot v u := by
  simp [vecDot, Fin.sum_univ_two, mul_comm]

theorem BigBoundRegularityMeans.G_pairing_pushforward {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (k : ℤ) (t : ℝ) (x : Vec 2)
    (hT : ContDiff ℝ 1 (T t)) :
    vecDot (I.chiTilde hΦ m κ k t x)
        (G I hΦ m T (lIdx β I.Λ m k) t x) =
      vecDot (BigBoundRegularityMeans.chiPushforwardFlux I hΦ m κ k t x)
        (spaceGrad (T t) x) := by
  have hG := G_eq_flowGrad_mulVec I hΦ m T (lIdx β I.Λ m k) t x
    ((hT.differentiable (by norm_num) x).hasFDerivAt)
    ((xFlow_spatial_contDiff_two I hΦ m (lIdx β I.Λ m k) t).differentiable
      (by norm_num) (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)).hasFDerivAt
    (BigBoundRegularityMeans.xFlowInv_right_inverse I hΦ m (lIdx β I.Λ m k) t x)
  calc
    _ = vecDot (I.chiTilde hΦ m κ k t x)
        ((I.flowGrad hΦ m (lIdx β I.Λ m k) t x).mulVec
          (spaceGrad (T t) x)) := by rw [hG]
    _ = vecDot ((I.flowGrad hΦ m (lIdx β I.Λ m k) t x).transpose.mulVec
        (I.chiTilde hΦ m κ k t x)) (spaceGrad (T t) x) :=
      BigBoundRegularityMeans.vecDot_matrixMulVec_transpose _ _ _
    _ = vecDot (BigBoundRegularityMeans.chiPushforwardFlux I hΦ m κ k t x)
        (spaceGrad (T t) x) := rfl

theorem BigBoundRegularityMeans.vecDiv_contDiff_infty {F : Vec 2 → Vec 2}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => vecDiv F x) := by
  have hgrad (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞)
      (spaceGrad (fun x => F x i)) :=
    Infra.Section4.iterate_gradient_smooth ((contDiff_pi.mp hF) i)
  unfold vecDiv
  exact ContDiff.sum (fun i _ => contDiff_pi.mp (hgrad i) i)

theorem BigBoundRegularityMeans.vecDiv_isZ2Periodic {F : Vec 2 → Vec 2}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hper : IsZ2Periodic F) :
    IsZ2Periodic (fun x => vecDiv F x) := by
  have hgrad (i : Fin 2) : IsZ2Periodic
      (spaceGrad (fun x => F x i)) :=
    Infra.Section4.iterate_gradient_periodic
      ((contDiff_pi.mp hF i).of_le (by simp))
      (fun z x => congrFun (hper z x) i)
  intro z x
  unfold vecDiv
  apply Finset.sum_congr rfl
  intro i hi
  exact congrFun (hgrad i z x) i

theorem BigBoundRegularityMeans.flowGradK_contDiff_infty {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (k : ℤ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (flowGradK I hΦ m k t) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact (Infra.Section4.amnr_flowGrad_joint_contDiff_infty I hΦ m
    (lIdx β I.Λ m k) i j).comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec 2 => (t, x)))

theorem BigBoundRegularityMeans.flowGradK_isZ2Periodic {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (k : ℤ) (t : ℝ) : IsZ2Periodic (flowGradK I hΦ m k t) := by
  intro z x
  ext i j
  exact Infra.Section4.amnr_flowGrad_spatial_periodic I hΦ m
    (lIdx β I.Λ m k) t i j z x

/-- Componentwise time derivative of the cell corrector for the mean-value estimates. -/
def BigBoundRegularityMeans.chiMKTimeDerivative {β : ℝ} (I : Ingredients β)
    (m : ℕ) (κ : ℝ) (k : ℤ) (t : ℝ) : Vec 2 → Vec 2 :=
  fun y j => deriv (fun s => I.chiMK κ m k s y j) t

theorem BigBoundRegularityMeans.chiMKTimeDerivative_eq_shear {β : ℝ} (I : Ingredients β)
    (m : ℕ) (κ : ℝ) (k : ℤ) (t : ℝ) :
    BigBoundRegularityMeans.chiMKTimeDerivative I m κ k t = fun y =>
      (-(I.zetaProd m k t -
        (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) *
          I.corrTime κ m k t)) • uShear β I.Λ m k y := by
  funext y j
  exact (Infra.Section3.chiMK_component_hasDerivAt I κ k t y j).deriv

theorem BigBoundRegularityMeans.chiMKTimeDerivative_regular {β : ℝ} (I : Ingredients β)
    (m : ℕ) (κ : ℝ) (k : ℤ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (BigBoundRegularityMeans.chiMKTimeDerivative I m κ k t) ∧
      IsZ2Periodic (BigBoundRegularityMeans.chiMKTimeDerivative I m κ k t) ∧
      (∀ x, vecDiv (BigBoundRegularityMeans.chiMKTimeDerivative I m κ k t) x = 0) := by
  have hrep := BigBoundRegularityMeans.chiMKTimeDerivative_eq_shear I m κ k t
  have hu : ContDiff ℝ (⊤ : ℕ∞) (uShear β I.Λ m k) :=
    contDiff_uShear' β I.Λ m k
  have huper := uShear_isZ2Periodic β I.Λ m k
  have hε : epsilon β I.Λ m ≠ 0 :=
    ne_of_gt (Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le)
  have husigma (x : Vec 2) := Infra.Section3.uShear_eq_sigma_spaceGrad
    (β := β) (Λ := I.Λ) (m := m) k x hε
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (psi β I.Λ m k) := by
    unfold psi
    have hprofile : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec 2 => psi0 k ((epsilon β I.Λ m)⁻¹ • x)) := by
      unfold psi0
      split_ifs <;> fun_prop
    exact contDiff_const.mul hprofile
  have huEq : uShear β I.Λ m k =
      fun x => sigmaMat.mulVec (spaceGrad (psi β I.Λ m k) x) := by
    funext x
    exact husigma x
  have hdivu (x : Vec 2) : vecDiv (uShear β I.Λ m k) x = 0 := by
    rw [huEq]
    exact BigBoundRegularityMeans.sigmaGrad_div_zero hψ x
  constructor
  · rw [hrep]
    exact (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
      (fun _ : Vec 2 => -(I.zetaProd m k t -
        (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) *
          I.corrTime κ m k t))).smul hu
  constructor
  · rw [hrep]
    intro z x
    change (-(I.zetaProd m k t -
        (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) *
          I.corrTime κ m k t)) • uShear β I.Λ m k (x + latticeShift z) =
      (-(I.zetaProd m k t -
        (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) *
          I.corrTime κ m k t)) • uShear β I.Λ m k x
    rw [huper z x]
  · intro x
    rw [hrep]
    have hmul := BigBoundRegularityMeans.vecDiv_scalar_mul
      (q := fun _ : Vec 2 => -(I.zetaProd m k t -
        (4 * Real.pi ^ 2 * κ / epsilon β I.Λ m ^ 2) *
          I.corrTime κ m k t)) (F := uShear β I.Λ m k) (x := x)
      contDiff_const hu
    rw [hmul, hdivu x]
    simp [spaceGrad, fderiv_const_apply, vecDot]

/-- Corrector time derivative in flow coordinates for the mean-value estimates. -/
def BigBoundRegularityMeans.chiTimePushforwardFlux {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (k : ℤ) (t : ℝ) : Vec 2 → Vec 2 :=
  fun x => (flowGradK I hΦ m k t x).transpose.mulVec
    (BigBoundRegularityMeans.chiMKTimeDerivative I m κ k t
      (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))

theorem BigBoundRegularityMeans.chiTimePushforwardFlux_regular {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (k : ℤ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (BigBoundRegularityMeans.chiTimePushforwardFlux I hΦ m κ k t) ∧
      IsZ2Periodic (BigBoundRegularityMeans.chiTimePushforwardFlux I hΦ m κ k t) ∧
      (∀ x, vecDiv (BigBoundRegularityMeans.chiTimePushforwardFlux I hΦ m κ k t) x = 0) := by
  have hFsm := BigBoundRegularityMeans.flowGradK_contDiff_infty I hΦ m k t
  have hFper := BigBoundRegularityMeans.flowGradK_isZ2Periodic I hΦ m k t
  have hdot := BigBoundRegularityMeans.chiMKTimeDerivative_regular I m κ k t
  have hYsm : ContDiff ℝ (⊤ : ℕ∞)
      (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) :=
    (Infra.Section4.amnr_xFlowInv_joint_contDiff_infty I hΦ m
      (lIdx β I.Λ m k)).comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)))
  have hYper := Infra.Section4.amnr_xFlowInv_lattice_equivariant
    I hΦ m (lIdx β I.Λ m k) t
  have hcomp : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => BigBoundRegularityMeans.chiMKTimeDerivative I m κ k t
        (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)) :=
    hdot.1.comp hYsm
  have hcompPer : IsZ2Periodic
      (fun x => BigBoundRegularityMeans.chiMKTimeDerivative I m κ k t
        (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)) := by
    intro z x
    change BigBoundRegularityMeans.chiMKTimeDerivative I m κ k t
        (I.xFlowInv hΦ m (lIdx β I.Λ m k) t (x + latticeShift z)) =
      BigBoundRegularityMeans.chiMKTimeDerivative I m κ k t
        (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)
    rw [hYper z x]
    exact hdot.2.1 z _
  have hcofactor : ∀ x,
      rowCofactor (gradMatrix (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) x) =
        (I.flowGrad hΦ m (lIdx β I.Λ m k) t x).transpose := by
    intro x
    exact Infra.Section5.xFlowInv_rowCofactor_eq_flowGrad_transpose
      I hΦ m (lIdx β I.Λ m k) t x
      (Infra.Section5.streamVel_spatialDivergence_eq_zero I hΦ m)
  constructor
  · apply contDiff_pi.mpr
    intro i
    change ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ j : Fin 2,
      (flowGradK I hΦ m k t x).transpose i j *
        BigBoundRegularityMeans.chiMKTimeDerivative I m κ k t
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x) j)
    apply ContDiff.sum
    intro j hj
    exact (contDiff_pi.mp (contDiff_pi.mp hFsm j) i).mul
      (contDiff_pi.mp hcomp j)
  constructor
  · intro z x
    change (flowGradK I hΦ m k t (x + latticeShift z)).transpose.mulVec
        (BigBoundRegularityMeans.chiMKTimeDerivative I m κ k t
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t (x + latticeShift z))) =
      (flowGradK I hΦ m k t x).transpose.mulVec
      (BigBoundRegularityMeans.chiMKTimeDerivative I m κ k t
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))
    rw [hFper z x]
    exact congrArg (fun v : Vec 2 =>
      (flowGradK I hΦ m k t x).transpose.mulVec v) (hcompPer z x)
  · intro x
    have hχ : ContDiff ℝ 2 (BigBoundRegularityMeans.chiMKTimeDerivative I m κ k t) :=
      (hdot.1.of_le (by norm_num))
    have hpiola := Infra.Section5.xFlowInv_cofactorPiola_of_streamSeq
      I hΦ m (lIdx β I.Λ m k) t x
      ((hχ.differentiable (by norm_num) _).hasFDerivAt)
    have hfield : BigBoundRegularityMeans.chiTimePushforwardFlux I hΦ m κ k t = fun y =>
        (rowCofactor (gradMatrix
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) y)).mulVec
          (BigBoundRegularityMeans.chiMKTimeDerivative I m κ k t
            (I.xFlowInv hΦ m (lIdx β I.Λ m k) t y)) := by
      funext y
      change (I.flowGrad hΦ m (lIdx β I.Λ m k) t y).transpose.mulVec _ = _
      rw [hcofactor y]
    rw [hfield]
    simpa using hpiola.trans
      (hdot.2.2 (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))

theorem BigBoundRegularityMeans.timeDerivative_pairing_pushforward {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (k : ℤ) (t : ℝ) (x : Vec 2)
    (hT : ContDiff ℝ 1 (T t)) :
    vecDot (BigBoundRegularityMeans.chiMKTimeDerivative I m κ k t
        (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))
        (G I hΦ m T (lIdx β I.Λ m k) t x) =
      vecDot (BigBoundRegularityMeans.chiTimePushforwardFlux I hΦ m κ k t x)
        (spaceGrad (T t) x) := by
  have hG := G_eq_flowGrad_mulVec I hΦ m T (lIdx β I.Λ m k) t x
    ((hT.differentiable (by norm_num) x).hasFDerivAt)
    ((xFlow_spatial_contDiff_two I hΦ m (lIdx β I.Λ m k) t).differentiable
      (by norm_num) (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)).hasFDerivAt
    (BigBoundRegularityMeans.xFlowInv_right_inverse I hΦ m (lIdx β I.Λ m k) t x)
  calc
    _ = vecDot (BigBoundRegularityMeans.chiMKTimeDerivative I m κ k t
        (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x))
        ((I.flowGrad hΦ m (lIdx β I.Λ m k) t x).mulVec (spaceGrad (T t) x)) := by
          rw [hG]
    _ = vecDot ((I.flowGrad hΦ m (lIdx β I.Λ m k) t x).transpose.mulVec
        (BigBoundRegularityMeans.chiMKTimeDerivative I m κ k t
          (I.xFlowInv hΦ m (lIdx β I.Λ m k) t x)))
        (spaceGrad (T t) x) := BigBoundRegularityMeans.vecDot_matrixMulVec_transpose _ _ _
    _ = _ := rfl

/-- Finite set of odd indices whose underlying integer belongs to a supplied finite set. -/
noncomputable def BigBoundRegularityMeans.oddPreimageFinset (S : Finset ℤ) :
    Finset {k : ℤ // Odd k} :=
  (S.finite_toSet.preimage (fun _ _ _ _ h => Subtype.ext h)).toFinset

theorem BigBoundRegularityMeans.oddTsum_eq_preimage_sum
    (S : Finset ℤ) (F : {k : ℤ // Odd k} → ℝ)
    (hzero : ∀ k, k.1 ∉ S → F k = 0) :
    (∑' k : {k : ℤ // Odd k}, F k) =
      ∑ k ∈ BigBoundRegularityMeans.oddPreimageFinset S, F k := by
  classical
  apply tsum_eq_sum
  intro k hk
  have hnot : k.1 ∉ S := by
    intro hmem
    apply hk
    simp [BigBoundRegularityMeans.oddPreimageFinset, Set.Finite.mem_toFinset,
      Set.mem_preimage, hmem]
  exact hzero k hnot

/-- The cutoff derivative term has zero mean because every mode pairs a
pulled gradient with a divergence-free Piola push-forward of its shear. -/
theorem cutoff1_meanZero_of_slice {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) {t : ℝ}
    (hTsm : ContDiff ℝ (⊤ : ℕ∞) (T t)) (hTper : IsZ2Periodic (T t)) :
    MeanZeroOn unitCube (cutoff1 I hΦ m κ T t) := by
  classical
  let S := xiMKNearSupportFinset I m t 1
  let U := BigBoundRegularityMeans.oddPreimageFinset S
  have hxiDerivZero (k : ℤ) (hk : k ∉ S) : deriv (I.xiMK m k) t = 0 := by
    have hlocal : (I.xiMK m k) =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_Ioo.mem_nhds
        ⟨sub_lt_self t zero_lt_one, lt_add_of_pos_right t zero_lt_one⟩] with s hs
      by_contra hne
      have hmem : k ∈ xiMKNearSupport I m t 1 := ⟨s, hs, hne⟩
      exact hk ((xiMKNearSupport_finite I m t 1).mem_toFinset.mpr hmem)
    have hz : HasDerivAt (I.xiMK m k) 0 t :=
      (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hlocal
    simpa using hz.deriv
  have hrep : cutoff1 I hΦ m κ T t = fun x =>
      ∑ k ∈ U, deriv (I.xiMK m k.1) t *
        vecDot (I.chiTilde hΦ m κ k.1 t x)
          (G I hΦ m T (lIdx β I.Λ m k.1) t x) := by
    funext x
    unfold cutoff1
    exact BigBoundRegularityMeans.oddTsum_eq_preimage_sum S _ (fun k hk => by
      simp [hxiDerivZero k.1 hk])
  have hqsm : ContDiff ℝ (⊤ : ℕ∞) (T t) := hTsm
  have hqper : IsZ2Periodic (T t) := hTper
  have hPsm (k : {k : ℤ // Odd k}) (hk : k ∈ U) :
      ContDiff ℝ (⊤ : ℕ∞) (BigBoundRegularityMeans.chiPushforwardFlux I hΦ m κ k.1 t) :=
    (BigBoundRegularityMeans.chiPushforwardFlux_regular I hΦ m κ k.1 t).1
  have hPper (k : {k : ℤ // Odd k}) (hk : k ∈ U) :
      IsZ2Periodic (BigBoundRegularityMeans.chiPushforwardFlux I hΦ m κ k.1 t) :=
    (BigBoundRegularityMeans.chiPushforwardFlux_regular I hΦ m κ k.1 t).2.1
  have hPdiv (k : {k : ℤ // Odd k}) (hk : k ∈ U) (x : Vec 2) :
      vecDiv (BigBoundRegularityMeans.chiPushforwardFlux I hΦ m κ k.1 t) x = 0 :=
    (BigBoundRegularityMeans.chiPushforwardFlux_regular I hΦ m κ k.1 t).2.2 x
  have hpair (x : Vec 2) : cutoff1 I hΦ m κ T t x =
      ∑ k ∈ U, deriv (I.xiMK m k.1) t *
        vecDot (spaceGrad (T t) x)
          (BigBoundRegularityMeans.chiPushforwardFlux I hΦ m κ k.1 t x) := by
    rw [hrep]
    apply Finset.sum_congr rfl
    intro k hk
    calc
      _ = deriv (I.xiMK m k.1) t *
          vecDot (BigBoundRegularityMeans.chiPushforwardFlux I hΦ m κ k.1 t x) (spaceGrad (T t) x)
              :=
            congrArg (fun v => deriv (I.xiMK m k.1) t * v)
              (BigBoundRegularityMeans.G_pairing_pushforward I hΦ m κ T k.1 t x
                (hTsm.of_le (by norm_num)))
      _ = deriv (I.xiMK m k.1) t *
          vecDot (spaceGrad (T t) x) (BigBoundRegularityMeans.chiPushforwardFlux I hΦ m κ k.1 t x)
              := by
            rw [BigBoundRegularityMeans.vecDot_comm]
  unfold MeanZeroOn
  have hmean := BigBoundRegularityMeans.meanZeroOn_weighted_grad_pairing U
    (fun k => deriv (I.xiMK m k.1) t) (fun _ => T t)
    (fun k => BigBoundRegularityMeans.chiPushforwardFlux I hΦ m κ k.1 t)
    (fun _ _ => hqsm) (fun _ _ => hqper) hPsm hPper hPdiv
  calc
    (∫ x in unitCube, cutoff1 I hΦ m κ T t x) =
        ∫ x in unitCube, ∑ k ∈ U,
          deriv (I.xiMK m k.1) t *
            vecDot (spaceGrad (T t) x)
              (BigBoundRegularityMeans.chiPushforwardFlux I hΦ m κ k.1 t x) := by
          congr 1
          funext x
          exact hpair x
    _ = 0 := hmean

/-- The transport term is a finite weighted divergence of `Q P_k`, where
`Q = div((K+s)∇T)` and each Piola field `P_k` is divergence free. -/
theorem twistie1_meanZero_of_slice {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (hm : 1 ≤ m) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    {t : ℝ}
    (hTsm : ContDiff ℝ (⊤ : ℕ∞) (T t)) (hTper : IsZ2Periodic (T t)) :
    MeanZeroOn unitCube (twistie1 I hΦ m κ T t) := by
  classical
  let Tlast := T t
  let Q : Vec 2 → ℝ := fun x => vecDiv (fun y =>
    (I.Kmat κ m t + I.sMat hΦ m κ t y).mulVec (spaceGrad Tlast y)) x
  let U := (Infra.Section3.xiMK_odd_support_finite I hm t).toFinset
  have hflowSm (l : ℤ) : ContDiff ℝ (⊤ : ℕ∞)
      (I.flowGrad hΦ m l t) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact (Infra.Section4.amnr_flowGrad_joint_contDiff_infty I hΦ m l i j).comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)))
  have hflowPer (l : ℤ) : IsZ2Periodic (I.flowGrad hΦ m l t) := by
    intro z x
    ext i j
    exact Infra.Section4.amnr_flowGrad_spatial_periodic I hΦ m l t i j z x
  have hSsm : ContDiff ℝ (⊤ : ℕ∞) (I.sMat hΦ m κ t) :=
    Infra.Section5.sMat_spatial_contDiff I hΦ m hm κ t hflowSm
  have hSper : IsZ2Periodic (I.sMat hΦ m κ t) := by
    exact (Infra.Section4.sMat_coarseCoeffForm I hΦ m κ).periodic t hflowPer
  have hVsm : ContDiff ℝ (⊤ : ℕ∞) (fun y =>
      (I.Kmat κ m t + I.sMat hΦ m κ t y).mulVec (spaceGrad Tlast y)) := by
    apply contDiff_pi.mpr
    intro i
    change ContDiff ℝ (⊤ : ℕ∞) (fun y => ∑ j : Fin 2,
      (I.Kmat κ m t + I.sMat hΦ m κ t y) i j * spaceGrad Tlast y j)
    apply ContDiff.sum
    intro j hj
    exact ((contDiff_pi.mp (contDiff_pi.mp (contDiff_const.add hSsm) i)) j).mul
      (contDiff_pi.mp (Infra.Section4.iterate_gradient_smooth hTsm) j)
  have hVper : IsZ2Periodic (fun y =>
      (I.Kmat κ m t + I.sMat hΦ m κ t y).mulVec (spaceGrad Tlast y)) := by
    intro z x
    have hgradper := Infra.Section4.iterate_gradient_periodic
      ((contDiff_infty.mp hTsm) 1) hTper
    change (I.Kmat κ m t + I.sMat hΦ m κ t (x + latticeShift z)).mulVec
        (spaceGrad Tlast (x + latticeShift z)) =
      (I.Kmat κ m t + I.sMat hΦ m κ t x).mulVec (spaceGrad Tlast x)
    rw [hSper z x, hgradper z x]
  have hQsm : ContDiff ℝ (⊤ : ℕ∞) Q := by
    exact BigBoundRegularityMeans.vecDiv_contDiff_infty hVsm
  have hQper : IsZ2Periodic Q := BigBoundRegularityMeans.vecDiv_isZ2Periodic hVsm hVper
  have hrepr : twistie1 I hΦ m κ T t = fun x =>
      ∑ k ∈ U, I.xiMK m k.1 t *
        vecDot (spaceGrad Q x) (BigBoundRegularityMeans.chiPushforwardFlux I hΦ m κ k.1 t x) := by
    funext x
    unfold twistie1
    have hsum := xiMK_odd_tsum_eq_subtype_support_sum I m hm t
      (fun k => vecDot (I.chiTilde hΦ m κ k.1 t x)
        ((flowGradK I hΦ m k.1 t x).mulVec (gradDiv
          (fun s y => (I.Kmat κ m s + I.sMat hΦ m κ s y).mulVec
            (spaceGrad (T s) y)) t x)))
    rw [show (∑' k : {k : ℤ // Odd k}, I.xiMK m k.1 t *
        vecDot (I.chiTilde hΦ m κ k.1 t x)
          ((flowGradK I hΦ m k.1 t x).mulVec (gradDiv
            (fun s y => (I.Kmat κ m s + I.sMat hΦ m κ s y).mulVec
              (spaceGrad (T s) y)) t x))) =
        ∑ k ∈ U, I.xiMK m k.1 t *
          vecDot (I.chiTilde hΦ m κ k.1 t x)
            ((flowGradK I hΦ m k.1 t x).mulVec (gradDiv
              (fun s y => (I.Kmat κ m s + I.sMat hΦ m κ s y).mulVec
                (spaceGrad (T s) y)) t x)) from by
          simpa only [smul_eq_mul] using hsum]
    apply Finset.sum_congr rfl
    intro k hk
    have hG := G_eq_flowGrad_mulVec I hΦ m
      (fun _ y => Q y) (lIdx β I.Λ m k.1) t x
      ((hQsm.differentiable (by norm_num) x).hasFDerivAt)
      ((xFlow_spatial_contDiff_two I hΦ m (lIdx β I.Λ m k.1) t).differentiable
        (by norm_num) (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t x)).hasFDerivAt
      (BigBoundRegularityMeans.xFlowInv_right_inverse I hΦ m (lIdx β I.Λ m k.1) t x)
    have hpair := BigBoundRegularityMeans.G_pairing_pushforward I hΦ m κ (fun _ y => Q y)
      k.1 t x (hQsm.of_le (by norm_num))
    have hG' : G I hΦ m (fun _ y => Q y) (lIdx β I.Λ m k.1) t x =
        (flowGradK I hΦ m k.1 t x).mulVec (spaceGrad Q x) := by
      simpa [flowGradK] using hG
    change I.xiMK m k.1 t * vecDot
      (I.chiTilde hΦ m κ k.1 t x)
      ((flowGradK I hΦ m k.1 t x).mulVec (spaceGrad Q x)) = _
    calc
      _ = I.xiMK m k.1 t * vecDot
          (I.chiTilde hΦ m κ k.1 t x)
          (G I hΦ m (fun _ y => Q y) (lIdx β I.Λ m k.1) t x) := by
            rw [← hG']
      _ = I.xiMK m k.1 t *
          vecDot (BigBoundRegularityMeans.chiPushforwardFlux I hΦ m κ k.1 t x) (spaceGrad Q x) :=
            congrArg (fun v => I.xiMK m k.1 t * v) hpair
      _ = I.xiMK m k.1 t *
          vecDot (spaceGrad Q x) (BigBoundRegularityMeans.chiPushforwardFlux I hΦ m κ k.1 t x) := by
            rw [BigBoundRegularityMeans.vecDot_comm]
  have hPdiv (k : {k : ℤ // Odd k}) (hk : k ∈ U) (x : Vec 2) :
      vecDiv (BigBoundRegularityMeans.chiPushforwardFlux I hΦ m κ k.1 t) x = 0 :=
    (BigBoundRegularityMeans.chiPushforwardFlux_regular I hΦ m κ k.1 t).2.2 x
  have hmean := BigBoundRegularityMeans.meanZeroOn_weighted_grad_pairing U
    (fun k => I.xiMK m k.1 t) (fun _ => Q)
    (fun k => BigBoundRegularityMeans.chiPushforwardFlux I hΦ m κ k.1 t)
    (fun _ _ => hQsm) (fun _ _ => hQper)
    (fun k _ => (BigBoundRegularityMeans.chiPushforwardFlux_regular I hΦ m κ k.1 t).1)
    (fun k _ => (BigBoundRegularityMeans.chiPushforwardFlux_regular I hΦ m κ k.1 t).2.1) hPdiv
  unfold MeanZeroOn at hmean ⊢
  rw [hrepr]
  exact hmean

/-- The forcing term is the divergence of `d+e+Σ ξ_k (div e)P_k`; no
separate mean condition on either source error is needed. -/
theorem tiny_meanZero_of_slice {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (hm : 1 ≤ m) (κ : ℝ) (d e : ℝ → Vec 2 → Vec 2)
    {t : ℝ}
    (hdsm : ContDiff ℝ (⊤ : ℕ∞) (d t)) (hdper : IsZ2Periodic (d t))
    (hesm : ContDiff ℝ (⊤ : ℕ∞) (e t)) (heper : IsZ2Periodic (e t)) :
    MeanZeroOn unitCube (tiny I hΦ m κ d e t) := by
  classical
  let Q : Vec 2 → ℝ := fun x => vecDiv (e t) x
  let U := (Infra.Section3.xiMK_odd_support_finite I hm t).toFinset
  have hQsm : ContDiff ℝ (⊤ : ℕ∞) Q := BigBoundRegularityMeans.vecDiv_contDiff_infty hesm
  have hQper : IsZ2Periodic Q := BigBoundRegularityMeans.vecDiv_isZ2Periodic hesm heper
  have hrepr :
      (fun x => tiny I hΦ m κ d e t x) = fun x =>
        vecDiv (fun y => d t y + e t y) x +
          ∑ k ∈ U, I.xiMK m k.1 t *
            vecDot (spaceGrad Q x)
              (BigBoundRegularityMeans.chiPushforwardFlux I hΦ m κ k.1 t x) := by
    funext x
    unfold tiny
    have hsum := xiMK_odd_tsum_eq_subtype_support_sum I m hm t
      (fun k => vecDot (I.chiTilde hΦ m κ k.1 t x)
        ((flowGradK I hΦ m k.1 t x).mulVec (gradDiv e t x)))
    rw [show (∑' k : {k : ℤ // Odd k}, I.xiMK m k.1 t *
        vecDot (I.chiTilde hΦ m κ k.1 t x)
          ((flowGradK I hΦ m k.1 t x).mulVec (gradDiv e t x))) =
        ∑ k ∈ U, I.xiMK m k.1 t *
          vecDot (I.chiTilde hΦ m κ k.1 t x)
            ((flowGradK I hΦ m k.1 t x).mulVec (gradDiv e t x)) from by
          simpa only [smul_eq_mul] using hsum]
    apply congrArg (fun r : ℝ => vecDiv (fun y => d t y + e t y) x + r)
    apply Finset.sum_congr rfl
    intro k hk
    have hG := G_eq_flowGrad_mulVec I hΦ m
      (fun _ y => Q y) (lIdx β I.Λ m k.1) t x
      ((hQsm.differentiable (by norm_num) x).hasFDerivAt)
      ((xFlow_spatial_contDiff_two I hΦ m (lIdx β I.Λ m k.1) t).differentiable
        (by norm_num) (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t x)).hasFDerivAt
      (BigBoundRegularityMeans.xFlowInv_right_inverse I hΦ m (lIdx β I.Λ m k.1) t x)
    have hpair := BigBoundRegularityMeans.G_pairing_pushforward I hΦ m κ (fun _ y => Q y)
      k.1 t x (hQsm.of_le (by norm_num))
    have hG' : G I hΦ m (fun _ y => Q y) (lIdx β I.Λ m k.1) t x =
        (flowGradK I hΦ m k.1 t x).mulVec (spaceGrad Q x) := by
      simpa [flowGradK] using hG
    change I.xiMK m k.1 t *
      vecDot (I.chiTilde hΦ m κ k.1 t x)
        ((flowGradK I hΦ m k.1 t x).mulVec (spaceGrad Q x)) = _
    calc
      _ = I.xiMK m k.1 t * vecDot
          (I.chiTilde hΦ m κ k.1 t x)
          (G I hΦ m (fun _ y => Q y) (lIdx β I.Λ m k.1) t x) := by
            rw [← hG']
      _ = I.xiMK m k.1 t *
          vecDot (BigBoundRegularityMeans.chiPushforwardFlux I hΦ m κ k.1 t x) (spaceGrad Q x) :=
            congrArg (fun v => I.xiMK m k.1 t * v) hpair
      _ = I.xiMK m k.1 t *
          vecDot (spaceGrad Q x) (BigBoundRegularityMeans.chiPushforwardFlux I hΦ m κ k.1 t x) := by
            rw [BigBoundRegularityMeans.vecDot_comm]
  let H : {k : ℤ // Odd k} → Vec 2 → Vec 2 := fun k y =>
    Q y • BigBoundRegularityMeans.chiPushforwardFlux I hΦ m κ k.1 t y
  let W : Vec 2 → Vec 2 := fun y => d t y + e t y +
    ∑ k ∈ U, I.xiMK m k.1 t • H k y
  have hHsm (k : {k : ℤ // Odd k}) (_hk : k ∈ U) :
      ContDiff ℝ (⊤ : ℕ∞) (H k) := by
    exact hQsm.smul (BigBoundRegularityMeans.chiPushforwardFlux_regular I hΦ m κ k.1 t).1
  have hHper (k : {k : ℤ // Odd k}) (_hk : k ∈ U) : IsZ2Periodic (H k) := by
    intro z x
    change Q (x + latticeShift z) •
        BigBoundRegularityMeans.chiPushforwardFlux I hΦ m κ k.1 t (x + latticeShift z) = _
    rw [hQper z x, (BigBoundRegularityMeans.chiPushforwardFlux_regular I hΦ m κ k.1 t).2.1 z x]
  have hBaseSm : ContDiff ℝ (⊤ : ℕ∞) (fun y => d t y + e t y) := hdsm.add hesm
  have hBasePer : IsZ2Periodic (fun y => d t y + e t y) := by
    intro z x
    change d t (x + latticeShift z) + e t (x + latticeShift z) =
      d t x + e t x
    rw [hdper z x, heper z x]
  have hSumSm : ContDiff ℝ (⊤ : ℕ∞) (fun y =>
      ∑ k ∈ U, I.xiMK m k.1 t • H k y) := by
    apply ContDiff.sum
    intro k hk
    exact (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
      (fun _ : Vec 2 => I.xiMK m k.1 t)).smul (hHsm k hk)
  have hSumPer : IsZ2Periodic (fun y =>
      ∑ k ∈ U, I.xiMK m k.1 t • H k y) := by
    intro z x
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply]
    change (∑ k ∈ U, I.xiMK m k.1 t * H k (x + latticeShift z) i) =
      ∑ k ∈ U, I.xiMK m k.1 t * H k x i
    apply Finset.sum_congr rfl
    intro k hk
    rw [congrFun (hHper k hk z x) i]
  have hWsm : ContDiff ℝ (⊤ : ℕ∞) W := hBaseSm.add hSumSm
  have hWper : IsZ2Periodic W := by
    intro z x
    change (fun y => d t y + e t y) (x + latticeShift z) +
        (fun y => ∑ k ∈ U, I.xiMK m k.1 t • H k y) (x + latticeShift z) = _
    rw [hBasePer z x, hSumPer z x]
  have hsumDer (x : Vec 2) : HasFDerivAt
      (fun y => ∑ k ∈ U, I.xiMK m k.1 t • H k y)
      (fderiv ℝ (fun y => ∑ k ∈ U, I.xiMK m k.1 t • H k y) x) x :=
    (hSumSm.differentiable (by simp) x).hasFDerivAt
  have hbaseDer (x : Vec 2) : HasFDerivAt (fun y => d t y + e t y)
      (fderiv ℝ (fun y => d t y + e t y) x) x :=
    (hBaseSm.differentiable (by simp) x).hasFDerivAt
  have hHder (k : {k : ℤ // Odd k}) (hk : k ∈ U) (x : Vec 2) :
      HasFDerivAt (H k) (fderiv ℝ (H k) x) x :=
    (hHsm k hk).differentiable (by simp) x |>.hasFDerivAt
  have hPdiv (k : {k : ℤ // Odd k}) (hk : k ∈ U) (x : Vec 2) :
      vecDiv (BigBoundRegularityMeans.chiPushforwardFlux I hΦ m κ k.1 t) x = 0 :=
    (BigBoundRegularityMeans.chiPushforwardFlux_regular I hΦ m κ k.1 t).2.2 x
  have hpoint (x : Vec 2) : vecDiv W x =
      vecDiv (fun y => d t y + e t y) x +
        ∑ k ∈ U, I.xiMK m k.1 t *
          vecDot (spaceGrad Q x) (BigBoundRegularityMeans.chiPushforwardFlux I hΦ m κ k.1 t x) := by
    rw [vecDiv_add_of_hasFDerivAt (hbaseDer x) (hsumDer x)]
    rw [vecDiv_finite_weighted_sum U (fun k => I.xiMK m k.1 t) H x
      (fun k hk => hHder k hk x)]
    apply congrArg (fun r : ℝ => vecDiv (fun y => d t y + e t y) x + r)
    apply Finset.sum_congr rfl
    intro k hk
    have hdiv : vecDiv (H k) x =
        vecDot (spaceGrad Q x) (BigBoundRegularityMeans.chiPushforwardFlux I hΦ m κ k.1 t x) := by
      change vecDiv (fun y => Q y • BigBoundRegularityMeans.chiPushforwardFlux I hΦ m κ k.1 t y) x
          = _
      rw [BigBoundRegularityMeans.vecDiv_scalar_mul hQsm
          (BigBoundRegularityMeans.chiPushforwardFlux_regular I hΦ m κ k.1 t).1,
        hPdiv k hk x]
      simp
    rw [hdiv]
  have hfun : (fun x => tiny I hΦ m κ d e t x) = fun x => vecDiv W x := by
    funext x
    rw [congrFun hrepr x, hpoint x]
  have hmean := BigBoundRegularityMeans.meanZeroOn_vecDiv_of_contDiff_periodic hWsm hWper
  unfold MeanZeroOn
  rw [hfun]
  exact hmean

end AVenhance.Infra.Section5.Integration

end
