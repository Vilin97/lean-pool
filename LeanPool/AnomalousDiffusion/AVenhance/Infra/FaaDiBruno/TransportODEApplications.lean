/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.TransportTimeAnalyticityEstimate
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.InverseC1
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.Liouville
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.GradientDeviation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.FieldTaylor
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.Laws
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.TransportSharpEstimate

/-! # Transport ODEApplications

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped ContDiff Topology

noncomputable section

namespace AVenhance.FaaDiBruno

/-- Real two-by-two matrices representing spatial flow derivatives. -/
abbrev FlowMatrix := Fin 2 → Fin 2 → ℝ

/-- The transposed cofactor of a two by two matrix. -/
def flowMatrixCofactorTranspose (A : FlowMatrix) : FlowMatrix := fun i j =>
  if i.val = 0 then
    if j.val = 0 then A 1 1 else -A 0 1
  else if j.val = 0 then -A 1 0 else A 0 0

theorem TransportODEApplications.flowLinearMap_apply_two (A : Vec 2 →L[ℝ] Vec 2) (v : Vec 2)
    (i : Fin 2) :
    A v i = A (coordinateVector 2 0) i * v 0 +
      A (coordinateVector 2 1) i * v 1 := by
  have hv : v = v 0 • coordinateVector 2 0 + v 1 • coordinateVector 2 1 := by
    ext j
    fin_cases j <;> simp [coordinateVector]
  rw [hv, map_add, map_smul, map_smul]
  change v 0 * A (coordinateVector 2 0) i + v 1 * A (coordinateVector 2 1) i = _
  simp [coordinateVector]
  ring

theorem TransportODEApplications.flowContinuousLinearMap_det_two (A : Vec 2 →L[ℝ] Vec 2) :
    A.det = A (coordinateVector 2 0) 0 * A (coordinateVector 2 1) 1 -
      A (coordinateVector 2 1) 0 * A (coordinateVector 2 0) 1 := by
  change LinearMap.det A.toLinearMap = _
  rw [← LinearMap.det_toMatrix' A.toLinearMap, Matrix.det_fin_two]
  simp [LinearMap.toMatrix'_apply, coordinateVector]

/-- For a divergence-free smooth periodic field, the forward flow Jacobian at
the inverse point is the transposed cofactor of the inverse-flow Jacobian.
This is the finite-dimensional identity used in Proposition `p.ODE.flow`. -/
theorem flow_spatialGradientMatrix_composed_inverse_eq_cofactor
    {b : ℝ → Vec 2 → Vec 2} (hb : AVenhance.Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (hdiv : ∀ t x, AVenhance.Infra.Flow.spatialDivergence b t x = 0)
    (t : ℝ) (x : Vec 2) :
    spatialGradientMatrix (fun y => X t y 0) (X 0 x t) =
      flowMatrixCofactorTranspose (spatialGradientMatrix (fun y => X 0 y t) x) := by
  let F : Vec 2 → Vec 2 := fun y => X t y 0
  let G : Vec 2 → Vec 2 := fun y => X 0 y t
  let A : FlowMatrix := spatialGradientMatrix G x
  let B : FlowMatrix := spatialGradientMatrix F (G x)
  obtain ⟨hF, hG, hGF, hFG⟩ :=
    AVenhance.Infra.Flow.flow_fixed_time_maps_are_C1_inverses hb hX 0 t
  have hcomp : (fderiv ℝ F (G x)).comp (fderiv ℝ G x) = 1 := by
    have hfdF : HasFDerivAt F (fderiv ℝ F (G x)) (G x) :=
      (hF.differentiable (by norm_num) (G x)).hasFDerivAt
    have hfdG : HasFDerivAt G (fderiv ℝ G x) x :=
      (hG.differentiable (by norm_num) x).hasFDerivAt
    have hchain := hfdF.comp x hfdG
    have hidentity : F ∘ G = fun y => y := by
      funext y
      exact hFG y
    have hchain' : HasFDerivAt (fun y : Vec 2 => y)
        ((fderiv ℝ F (G x)).comp (fderiv ℝ G x)) x := by
      simpa only [hidentity] using hchain
    have hderivId := hchain'.fderiv
    have hfid : fderiv ℝ (fun y : Vec 2 => y) x = 1 := by
      calc
        _ = ContinuousLinearMap.id ℝ (Vec 2) := (hasFDerivAt_id x).fderiv
        _ = 1 := by ext v; rfl
    exact hderivId.symm.trans hfid
  have hdetCLM : (fderiv ℝ G x).det = 1 :=
    AVenhance.Infra.Flow.flow_spatial_jacobian_det_eq_one_of_divergence_free
      hb hX hdiv x t 0
  have hdetA : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have hdet' : A 0 0 * A 1 1 - A 0 1 * A 1 0 =
        (fderiv ℝ G x).det := by
      simpa [A, spatialGradientMatrix] using
        (TransportODEApplications.flowContinuousLinearMap_det_two (fderiv ℝ G x)).symm
    exact hdet'.trans hdetCLM
  have hentry (i j : Fin 2) :
      B i 0 * A 0 j + B i 1 * A 1 j = if i = j then 1 else 0 := by
    have h := congrArg (fun L : Vec 2 →L[ℝ] Vec 2 => L (coordinateVector 2 j) i) hcomp
    change fderiv ℝ F (G x) (fderiv ℝ G x (coordinateVector 2 j)) i =
      coordinateVector 2 j i at h
    rw [TransportODEApplications.flowLinearMap_apply_two] at h
    have hbasis : coordinateVector 2 j i = if i = j then 1 else 0 := by
      by_cases hEq : i = j
      · subst j
        simp [coordinateVector]
      · simp [coordinateVector, hEq]
    rw [hbasis] at h
    simpa [A, B, spatialGradientMatrix] using h
  have hB00 : B 0 0 = A 1 1 := by
    have h₀₀ := hentry 0 0
    have h₀₁ := hentry 0 1
    norm_num at h₀₀ h₀₁
    have hdet' : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := hdetA
    linear_combination A 1 1 * h₀₀ - A 1 0 * h₀₁ - B 0 0 * hdet'
  have hB01 : B 0 1 = -A 0 1 := by
    have h₀₀ := hentry 0 0
    have h₀₁ := hentry 0 1
    norm_num at h₀₀ h₀₁
    have hdet' : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := hdetA
    linear_combination A 0 0 * h₀₁ - A 0 1 * h₀₀ - B 0 1 * hdet'
  have hB10 : B 1 0 = -A 1 0 := by
    have h₁₀ := hentry 1 0
    have h₁₁ := hentry 1 1
    norm_num at h₁₀ h₁₁
    have hdet' : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := hdetA
    linear_combination A 1 1 * h₁₀ - A 1 0 * h₁₁ - B 1 0 * hdet'
  have hB11 : B 1 1 = A 0 0 := by
    have h₁₀ := hentry 1 0
    have h₁₁ := hentry 1 1
    norm_num at h₁₀ h₁₁
    have hdet' : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := hdetA
    linear_combination A 0 0 * h₁₁ - A 0 1 * h₁₀ - B 1 1 * hdet'
  ext i j
  fin_cases i <;> fin_cases j
  · change B 0 0 = A 1 1
    exact hB00
  · change B 0 1 = -A 0 1
    exact hB01
  · change B 1 0 = -A 1 0
    exact hB10
  · change B 1 1 = A 0 0
    exact hB11

/-- The coordinate cofactor map is linear and does not increase the entrywise
sup norm on two by two matrices. -/
noncomputable def flowCofactorCLM : FlowMatrix →L[ℝ] FlowMatrix :=
  ContinuousLinearMap.mk
    { toFun := flowMatrixCofactorTranspose
      map_add' := by
        intro A B
        ext i j
        fin_cases i <;> fin_cases j
        · simp [flowMatrixCofactorTranspose]
        · simp [flowMatrixCofactorTranspose]
          ring
        · simp [flowMatrixCofactorTranspose]
          ring
        · simp [flowMatrixCofactorTranspose]
      map_smul' := by
        intro c A
        ext i j
        fin_cases i <;> fin_cases j
        all_goals simp [flowMatrixCofactorTranspose] }
    (by
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      fin_cases i <;> fin_cases j
      all_goals
        simp only [flowMatrixCofactorTranspose]
        split_ifs <;> fun_prop)

theorem flowCofactorCLM_norm_le : ‖flowCofactorCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro A
  rw [pi_norm_le_iff_of_nonempty]
  intro i
  rw [pi_norm_le_iff_of_nonempty]
  intro j
  fin_cases i <;> fin_cases j
  · change ‖A 1 1‖ ≤ 1 * ‖A‖
    calc
      ‖A 1 1‖ ≤ ‖A 1‖ := norm_le_pi_norm _ _
      _ ≤ ‖A‖ := norm_le_pi_norm _ _
      _ = 1 * ‖A‖ := by ring
  · change ‖-A 0 1‖ ≤ 1 * ‖A‖
    simpa only [norm_neg] using (show ‖A 0 1‖ ≤ 1 * ‖A‖ from
      (norm_le_pi_norm (A 0) 1).trans (by
        calc ‖A 0‖ ≤ ‖A‖ := norm_le_pi_norm A 0
        _ = 1 * ‖A‖ := by ring))
  · change ‖-A 1 0‖ ≤ 1 * ‖A‖
    simpa only [norm_neg] using (show ‖A 1 0‖ ≤ 1 * ‖A‖ from
      (norm_le_pi_norm (A 1) 0).trans (by
        calc ‖A 1‖ ≤ ‖A‖ := norm_le_pi_norm A 1
        _ = 1 * ‖A‖ := by ring))
  · change ‖A 0 0‖ ≤ 1 * ‖A‖
    calc
      ‖A 0 0‖ ≤ ‖A 0‖ := norm_le_pi_norm _ _
      _ ≤ ‖A‖ := norm_le_pi_norm _ _
      _ = 1 * ‖A‖ := by ring

theorem TransportODEApplications.orderedPartial_postCLM
    {n : ℕ} (L : FlowMatrix →L[ℝ] FlowMatrix)
    (f : Vec 2 → FlowMatrix) (hf : ContDiff ℝ n f)
    (x : Vec 2) (I : Fin n → Fin 2) :
    orderedPartial n (fun y => L (f y)) x I =
      L (orderedPartial n f x I) := by
  let z : VecOne 2 := WithLp.toLp 1 x
  let T := iteratedFDeriv ℝ n (liftVecOne f) z
  have hcomp := L.iteratedFDeriv_comp_left (f := liftVecOne f)
    (contDiff_liftVecOne hf).contDiffAt (i := n) (by exact le_rfl) (x := z)
  have hcomp' :
      iteratedFDeriv ℝ n (liftVecOne (fun y => L (f y))) z =
        L.compContinuousMultilinearMap T := by
    simpa [liftVecOne, Function.comp_def, T, z] using hcomp
  have heval := congrArg (fun D => D (fun j => coordinateVectorOne 2 (I j))) hcomp'
  simpa [orderedPartial, z, T] using heval

theorem TransportODEApplications.derivativeSup_postCLM_le
    {n : ℕ} (L : FlowMatrix →L[ℝ] FlowMatrix) (f : Vec 2 → FlowMatrix)
    (hf : ContDiff ℝ n f) (hL : ‖L‖ ≤ 1) :
    derivativeSup n (fun x => L (f x)) ≤ derivativeSup n f := by
  classical
  unfold derivativeSup
  refine iSup_le fun I => ?_
  calc
    partialSup n (fun x => L (f x)) I ≤ partialSup n f I := by
      unfold partialSup
      apply eLpNormEssSup_mono_enorm_ae
      filter_upwards with x
      rw [TransportODEApplications.orderedPartial_postCLM L f hf x I]
      have hnorm : ‖L (orderedPartial n f x I)‖ ≤ ‖orderedPartial n f x I‖ := by
        calc
          ‖L (orderedPartial n f x I)‖ ≤
              ‖L‖ * ‖orderedPartial n f x I‖ := L.le_opNorm _
          _ ≤ 1 * ‖orderedPartial n f x I‖ :=
            mul_le_mul_of_nonneg_right hL (norm_nonneg _)
          _ = ‖orderedPartial n f x I‖ := by ring
      simpa [Real.enorm_eq_ofReal_abs] using ENNReal.ofReal_le_ofReal hnorm
    _ ≤ derivativeSup n f := le_iSup_of_le I le_rfl

theorem TransportODEApplications.derivativeSup_add_le
    {n : ℕ} (f g : Vec 2 → FlowMatrix)
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    derivativeSup n (fun x => f x + g x) ≤ derivativeSup n f + derivativeSup n g := by
  classical
  unfold derivativeSup
  refine iSup_le fun I => ?_
  calc
    partialSup n (fun x => f x + g x) I ≤ partialSup n f I + partialSup n g I := by
      unfold partialSup
      have hadd : liftVecOne (fun x => f x + g x) = liftVecOne f + liftVecOne g := by
        funext z
        rfl
      have hpart (x : Vec 2) :
          orderedPartial n (fun x => f x + g x) x I =
            orderedPartial n f x I + orderedPartial n g x I := by
        simp only [orderedPartial, hadd]
        rw [iteratedFDeriv_add_apply
          (contDiff_liftVecOne hf).contDiffAt
          (contDiff_liftVecOne hg).contDiffAt]
        rfl
      have hfun : (fun x => orderedPartial n (fun x => f x + g x) x I) =
          (fun x => orderedPartial n f x I) + (fun x => orderedPartial n g x I) := by
        funext x
        exact hpart x
      rw [hfun]
      exact eLpNormEssSup_add_le
    _ ≤ derivativeSup n f + derivativeSup n g :=
      add_le_add (le_iSup_of_le I le_rfl) (le_iSup_of_le I le_rfl)

theorem TransportODEApplications.snorm_neg_eq {n : ℕ} {R : ℝ} (f : Vec 2 → Vec 2) :
    snorm (fun x => -f x) n R = snorm f n R := by
  have hpartial (I : Fin n → Fin 2) :
      partialSup n (fun x => -f x) I = partialSup n f I := by
    unfold partialSup
    rw [eLpNormEssSup_eq_essSup_enorm, eLpNormEssSup_eq_essSup_enorm]
    apply essSup_congr_ae
    filter_upwards with x
    have h : orderedPartial n (fun x => -f x) x I = -orderedPartial n f x I := by
      change iteratedFDeriv ℝ n
        (fun z : VecOne 2 => -f ((vecOneEquiv 2) z)) (WithLp.toLp 1 x)
          (fun j => coordinateVectorOne 2 (I j)) =
        -iteratedFDeriv ℝ n
          (fun z : VecOne 2 => f ((vecOneEquiv 2) z)) (WithLp.toLp 1 x)
            (fun j => coordinateVectorOne 2 (I j))
      rw [show (fun z : VecOne 2 => -f ((vecOneEquiv 2) z)) =
        -(fun z : VecOne 2 => f ((vecOneEquiv 2) z)) by rfl, iteratedFDeriv_neg]
      rfl
    rw [h]
    simp
  have hderiv : derivativeSup n (fun x => -f x) = derivativeSup n f := by
    unfold derivativeSup
    apply le_antisymm
    · apply iSup_le
      intro I
      rw [hpartial I]
      exact le_iSup_of_le I le_rfl
    · apply iSup_le
      intro I
      rw [← hpartial I]
      exact le_iSup_of_le I le_rfl
  unfold snorm
  rw [hderiv]

theorem TransportODEApplications.snorm_postCLM_le
    {n : ℕ} {R : ℝ} (L : FlowMatrix →L[ℝ] FlowMatrix)
    (f : Vec 2 → FlowMatrix) (hf : ContDiff ℝ n f) (hL : ‖L‖ ≤ 1) :
    snorm (fun x => L (f x)) n R ≤ snorm f n R := by
  unfold snorm
  gcongr
  exact TransportODEApplications.derivativeSup_postCLM_le L f hf hL

theorem TransportODEApplications.snorm_add_le
    {n : ℕ} {R : ℝ} (f g : Vec 2 → FlowMatrix)
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    snorm (fun x => f x + g x) n R ≤ snorm f n R + snorm g n R := by
  unfold snorm
  have hD := TransportODEApplications.derivativeSup_add_le f g hf hg
  let c := ENNReal.ofReal (((n + 1 : ℝ) ^ 2) / (n.factorial : ℝ)) *
    (ENNReal.ofReal R)⁻¹ ^ n
  calc
    _ ≤ c * (derivativeSup n f + derivativeSup n g) := by
      dsimp [c]
      gcongr
    _ = _ := by
      dsimp [c]
      rw [mul_add]

theorem TransportODEApplications.snorm_const_matrix_le_one (n : ℕ) (R : ℝ) :
    snorm (fun _ : Vec 2 => (fun i j : Fin 2 => if i = j then (1 : ℝ) else 0)) n R ≤
      ENNReal.ofReal 1 := by
  classical
  let I : FlowMatrix := fun i j => if i = j then 1 else 0
  have hnormI : ‖I‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonempty]
    intro i
    rw [pi_norm_le_iff_of_nonempty]
    intro j
    by_cases h : i = j <;> simp [I, h]
  have hpartialZero (J : Fin n → Fin 2) (x : Vec 2) (hn : n ≠ 0) :
      orderedPartial n (fun _ : Vec 2 => I) x J = 0 := by
    have hiter := iteratedFDeriv_const_of_ne (𝕜 := ℝ) (E := VecOne 2)
      (F := FlowMatrix) hn I
    have hiterAt := congrFun hiter (WithLp.toLp 1 x)
    change (iteratedFDeriv ℝ n (fun _ : VecOne 2 => I)
      (WithLp.toLp 1 x) (fun j => coordinateVectorOne 2 (J j))) = 0
    exact congrArg (fun T => T (fun j => coordinateVectorOne 2 (J j))) hiterAt
  have hD : derivativeSup n (fun _ : Vec 2 => I) ≤ ENNReal.ofReal 1 := by
    unfold derivativeSup
    refine iSup_le fun J => ?_
    unfold partialSup
    apply eLpNormEssSup_le_of_ae_bound
    filter_upwards with x
    by_cases hn : n = 0
    · subst n
      simpa [orderedPartial, liftVecOne, I] using hnormI
    · have hzero : orderedPartial n (fun _ : Vec 2 => I) x J = 0 := by
        exact hpartialZero J x hn
      rw [hzero]
      simp
  by_cases hn : n = 0
  · subst n
    simpa [snorm] using hD
  · have hzero : derivativeSup n (fun _ : Vec 2 => I) = 0 := by
      apply le_antisymm
      · unfold derivativeSup
        refine iSup_le fun J => ?_
        unfold partialSup
        have hpartial : partialSup n (fun _ : Vec 2 => I) J = 0 := by
          unfold partialSup
          rw [eLpNormEssSup_eq_zero_iff]
          filter_upwards with x
          exact hpartialZero J x hn
        exact hpartial.le
      · exact bot_le
    change snorm (fun _ : Vec 2 => I) n R ≤ ENNReal.ofReal 1
    rw [snorm, hzero]
    simp

theorem TransportODEApplications.flowMatrixCofactor_add_identity (A : FlowMatrix) :
    flowMatrixCofactorTranspose (fun i j => (if i = j then (1 : ℝ) else 0) + A i j) =
      fun i j => (if i = j then (1 : ℝ) else 0) +
        flowMatrixCofactorTranspose A i j := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flowMatrixCofactorTranspose]

/-- If the full time-space flow is smooth, its inverse displacement solves
the backward transport equation with source `-b`. The remaining flow-ODE
regularity task is to derive this smoothness witness from `IsFlow`. -/
theorem flow_inverse_displacement_isTransportSolution_of_jointSmooth
    {b : ℝ → Vec 2 → Vec 2} (hb : AVenhance.Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (hXsmooth : ContDiff ℝ ∞
      (fun p : (ℝ × Vec 2) × ℝ => X p.1.1 p.1.2 p.2)) :
    IsClassicalTransportSolution b (fun t x => -b t x)
      (fun t x => X 0 x t - x) := by
  let F : ℝ × Vec 2 → Vec 2 := fun p => X 0 p.2 p.1
  let G : ℝ × Vec 2 → Vec 2 := fun p => X p.1 p.2 0
  have hF : ContDiff ℝ ∞ F := by
    have hmap : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => (((0 : ℝ), p.2), p.1)) := by
      fun_prop
    exact hXsmooth.comp hmap
  have hG : ContDiff ℝ ∞ G := by
    have hmap : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => ((p.1, p.2), (0 : ℝ))) := by
      fun_prop
    exact hXsmooth.comp hmap
  have hLip := AVenhance.Infra.Flow.exists_global_spatial_lipschitz hb
  obtain ⟨L, hL0, hL⟩ := hLip
  have hGroup (t : ℝ) (y : Vec 2) : X 0 (X t y 0) t = y := by
    have h := AVenhance.Infra.Flow.flow_group_law b ⟨L, hL⟩ hX y 0 t 0
    simpa [hX.1] using h
  let K : ℝ × Vec 2 → ℝ × Vec 2 := fun p => (p.1, G p)
  have hK : ContDiff ℝ ∞ K := by
    have hfst : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => p.1) := contDiff_fst
    exact hfst.prodMk hG
  let Q : ℝ × Vec 2 → Vec 2 := F ∘ K
  have hQfun : Q = fun p => p.2 := by
    funext p
    dsimp [Q, Function.comp_def, K, F, G]
    exact hGroup p.1 p.2
  have hGtime (p : ℝ × Vec 2) :
      fderiv ℝ G p (1, 0) = b p.1 (G p) := by
    let c : ℝ → ℝ × Vec 2 := fun r => (r, p.2)
    have hc : HasFDerivAt c
        (ContinuousLinearMap.inl ℝ ℝ (Vec 2)) p.1 :=
      hasFDerivAt_prodMk_left p.1 p.2
    have hGdiff : DifferentiableAt ℝ G p := hG.differentiable (by simp) p
    have hcomp := hGdiff.hasFDerivAt.comp p.1 hc
    have hcurve : HasDerivAt (fun r => X r p.2 0)
        (b p.1 (X p.1 p.2 0)) p.1 := hX.2 p.2 0 p.1
    have hcompDeriv : HasDerivAt (fun r => X r p.2 0)
        (((fderiv ℝ G p).comp (ContinuousLinearMap.inl ℝ ℝ (Vec 2))) 1) p.1 := by
      simpa [c, G, Function.comp_def] using hcomp.hasDerivAt
    have hcomp' : HasDerivAt (fun r => X r p.2 0)
        (fderiv ℝ G p (1, 0)) p.1 := by
      convert hcompDeriv using 1
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
    have heq := HasDerivAt.unique hcomp' hcurve
    simpa [G] using heq
  have hKdir (p : ℝ × Vec 2) : fderiv ℝ K p (1, 0) = (1, b p.1 (G p)) := by
    have hprod := DifferentiableAt.fderiv_prodMk
      (differentiableAt_fst (𝕜 := ℝ))
      (hG.differentiable (by simp) p)
    rw [hprod]
    simp [hGtime p, fderiv_fst]
  have hchainDir (p : ℝ × Vec 2) :
      fderiv ℝ F (K p) (1, b p.1 (G p)) = 0 := by
    have hFdiff : DifferentiableAt ℝ F (K p) := hF.differentiable (by simp) (K p)
    have hKdiff : DifferentiableAt ℝ K p := hK.differentiable (by simp) p
    have hcomp := hFdiff.hasFDerivAt.comp p hKdiff.hasFDerivAt
    have hQderiv : HasFDerivAt Q
        ((fderiv ℝ F (K p)).comp (fderiv ℝ K p)) p := by
      simpa [Q, Function.comp_def] using hcomp
    have hzero : fderiv ℝ Q p (1, 0) = 0 := by
      rw [hQfun, fderiv_snd]
      simp
    calc
      fderiv ℝ F (K p) (1, b p.1 (G p)) =
          ((fderiv ℝ F (K p)).comp (fderiv ℝ K p)) (1, 0) := by
            rw [ContinuousLinearMap.comp_apply, hKdir]
      _ = fderiv ℝ Q p (1, 0) := by rw [hQderiv.fderiv]
      _ = 0 := hzero
  have hFtransport (t : ℝ) (x : Vec 2) :
      fderiv ℝ F (t, x) (1, b t x) = 0 := by
    let y : Vec 2 := X 0 x t
    have hflow : X t y 0 = x := by
      have h := AVenhance.Infra.Flow.flow_group_law b ⟨L, hL⟩ hX x t 0 t
      simpa [y, hX.1] using h
    have h := hchainDir (t, y)
    simpa [K, F, G, y, hflow] using h
  have hYsmooth : ContDiff ℝ ∞
      (Function.uncurry (fun t x => X 0 x t - x)) := by
    have hspace : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => p.2) := contDiff_snd
    change ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => F p - p.2)
    exact hF.sub hspace
  refine ⟨hYsmooth, ?_, ?_⟩
  · intro t x
    have hsub := fderiv_sub
      (hF.differentiable (by simp) (t, x))
      (differentiableAt_snd (p := (t, x)))
    have hFzero := hFtransport t x
    change fderiv ℝ (F - Prod.snd) (t, x)
      (1, b t x) = -b t x
    rw [hsub]
    rw [sub_apply, hFzero, fderiv_snd]
    simp
  · intro x
    simp [hX.1]

/-- The `n=1` induction base used in Proposition `p.ODE.flow.2`, specialized
to dimension two. It uses only the paper's order-one field seminorm bound and
does not require divergence freeness. -/
theorem flow_spatialFirstOrder_snorm_Dn_base
    {N : ℕ} (hN : 1 ≤ N)
    {b : ℝ → Vec 2 → Vec 2} (hb : AVenhance.Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {C_f R_f : ℝ} (hCf : 0 < C_f) (hRf : 0 < R_f)
    (hB : ∀ r k, 1 ≤ k → k ≤ N →
      snorm (b r) k R_f ≤ ENNReal.ofReal C_f)
    {t : ℝ} (ht : |t| ≤ 1 / (8 * C_f * R_f)) :
    snorm (fun x => X t x 0) 1
      (8 * 2 * R_f * (1 + (8 * 2 * C_f * R_f) * |t|)) ≤
        ENNReal.ofReal (1 / (2 * 2 * R_f)) := by
  have hB1 : ∀ r, snorm (b r) 1 R_f ≤ ENNReal.ofReal C_f := by
    intro r
    exact hB r 1 (by norm_num) hN
  have htime : |t| ≤ 1 / (4 * 2 * C_f * R_f) := by
    simpa [show (4 : ℝ) * 2 = 8 by norm_num] using ht
  have hdev := AVenhance.Infra.Flow.flow_fderiv_deviation_of_snorm
    hb hX hCf hRf hB1 (t := t) htime
  have hslice : ContDiff ℝ 1 (fun x => X t x 0) :=
    (AVenhance.Infra.Flow.flow_fixed_time_maps_are_C1_inverses hb hX 0 t).1
  let M : ℝ := 1 + 2 * C_f * R_f * |t|
  have hderiv : ∀ x, ‖fderiv ℝ (fun y => X t y 0) x‖ ≤ M := by
    intro x
    calc
      ‖fderiv ℝ (fun y => X t y 0) x‖ =
          ‖(fderiv ℝ (fun y => X t y 0) x - 1) + 1‖ := by
            rw [sub_add_cancel]
      _ ≤ ‖fderiv ℝ (fun y => X t y 0) x - 1‖ + ‖(1 : Vec 2 →L[ℝ] Vec 2)‖ :=
        norm_add_le _ _
      _ ≤ 2 * C_f * R_f * |t| + 1 := by
        have hId : ‖(1 : Vec 2 →L[ℝ] Vec 2)‖ = 1 := by simp
        rw [hId]
        exact add_le_add (hdev x).1 le_rfl
      _ = M := by dsimp [M]; ring
  have hD := derivativeSup_one_le_of_fderiv_norm_le
    (fun x => X t x 0) hslice hderiv
  let Rflow : ℝ := 8 * 2 * R_f * (1 + (8 * 2 * C_f * R_f) * |t|)
  have hRflow : 0 < Rflow := by
    dsimp [Rflow]
    positivity
  have hseminorm := snorm_one_le_of_derivativeSup_le
    (fun x => X t x 0) hRflow hD
  have htarget : 4 * M / Rflow ≤ 1 / (4 * R_f) := by
    have ha : 0 ≤ C_f * R_f * |t| := by positivity
    have hden : 0 < (8 * 2 * R_f) * (1 + (8 * 2 * C_f * R_f) * |t|) := by
      positivity
    have hRpos : 0 < 4 * R_f := by positivity
    dsimp [M, Rflow]
    rw [div_le_div_iff₀ hden hRpos]
    nlinarith [ha]
  have hfinal : ENNReal.ofReal (4 * M / Rflow) ≤
      ENNReal.ofReal (1 / (4 * R_f)) := ENNReal.ofReal_le_ofReal htarget
  have hfinal' : ENNReal.ofReal (4 * M / Rflow) ≤
      ENNReal.ofReal (1 / (2 * 2 * R_f)) := by
    have hdenom : (2 : ℝ) * 2 = 4 := by norm_num
    simpa [hdenom] using hfinal
  have hnorm : Rflow = 8 * 2 * R_f * (1 + (8 * 2 * C_f * R_f) * |t|) := rfl
  rw [← hnorm]
  exact hseminorm.trans hfinal'

/-- The positive coefficient in the paper's signed half-binomial induction,
with index `n` corresponding to derivative order `n+1`. -/
def flowHalfBinomialCoeff (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * Ring.choose (1 / 2 : ℝ) (n + 1)

theorem flowHalfBinomialCoeff_one : flowHalfBinomialCoeff 1 = 1 / 8 := by
  unfold flowHalfBinomialCoeff
  have hchoose2 : Ring.choose (1 / 2 : ℝ) 2 = (-1 / 8 : ℝ) := by
    rw [Ring.choose_eq_smul]
    rw [show descPochhammer ℤ 2 = Polynomial.X * (Polynomial.X - 1) by
      simp [descPochhammer]]
    simp only [Polynomial.smeval_mul, Polynomial.smeval_X, Polynomial.smeval_sub,
      Nat.factorial_two, Nat.cast_ofNat, Polynomial.smeval_one]
    ring
  norm_num [hchoose2]

theorem flowHalfBinomialCoeff_succ (n : ℕ) :
    flowHalfBinomialCoeff (n + 1) =
      ((n : ℝ) + 1 / 2) / (n + 2 : ℝ) * flowHalfBinomialCoeff n := by
  have hblock := orderedPartitionHalfBinomialBlockWeight_succ (n + 1)
  have hblock'base : orderedPartitionHalfBinomialBlockWeight (n + 2) =
      (1 / 2 - (n + 1 : ℝ)) *
        orderedPartitionHalfBinomialBlockWeight (n + 1) := by
    simpa [show n + 1 + 1 = n + 2 by omega] using hblock
  change ((n + 2).factorial : ℝ) * Ring.choose (1 / 2 : ℝ) (n + 2) =
      (1 / 2 - (n + 1 : ℝ)) *
        (((n + 1).factorial : ℝ) * Ring.choose (1 / 2 : ℝ) (n + 1)) at hblock'base
  have hfac : ((n + 2).factorial : ℝ) =
      (n + 2 : ℝ) * ((n + 1).factorial : ℝ) := by
    rw [Nat.factorial_succ]
    norm_cast
  let F : ℝ := ((n + 1).factorial : ℝ)
  have hF : 0 < F := by dsimp [F]; positivity
  have hblock' : (n + 2 : ℝ) * F * Ring.choose (1 / 2 : ℝ) (n + 2) =
      (1 / 2 - (n + 1 : ℝ)) * F * Ring.choose (1 / 2 : ℝ) (n + 1) := by
    simpa [F, hfac, mul_assoc] using hblock'base
  have hden : (n + 2 : ℝ) * F ≠ 0 := ne_of_gt (mul_pos (by positivity) hF)
  have hchoose : Ring.choose (1 / 2 : ℝ) (n + 2) =
      -(((n : ℝ) + 1 / 2) / (n + 2 : ℝ)) *
        Ring.choose (1 / 2 : ℝ) (n + 1) := by
    have hdiv := congrArg (fun z : ℝ => z / ((n + 2 : ℝ) * F)) hblock'
    field_simp [hden, ne_of_gt hF] at hdiv
    field_simp [ne_of_gt (show 0 < (n + 2 : ℝ) by positivity)]
    nlinarith [hdiv]
  unfold flowHalfBinomialCoeff
  rw [hchoose, pow_succ]
  ring

theorem flowHalfBinomialCoeff_nonneg {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ flowHalfBinomialCoeff n := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hzero : n = 0
      · subst n
        rw [flowHalfBinomialCoeff_one]
        norm_num
      · rw [flowHalfBinomialCoeff_succ]
        exact mul_nonneg (by positivity) (ih (by omega))

theorem flowHalfBinomialCoeff_le_inverse {n : ℕ} (hn : 1 ≤ n) :
    flowHalfBinomialCoeff n ≤ 1 / (4 * ((n : ℝ) + 1)) := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hzero : n = 0
      · subst n
        rw [flowHalfBinomialCoeff_one]
        norm_num
      · rw [flowHalfBinomialCoeff_succ]
        have hn' : 1 ≤ n := by omega
        have hratio : 0 ≤ ((n : ℝ) + 1 / 2) / (n + 2 : ℝ) := by positivity
        have hratio' : ((n : ℝ) + 1 / 2) / (n + 2 : ℝ) ≤
            ((n : ℝ) + 1) / (n + 2 : ℝ) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          linarith
        calc
          ((n : ℝ) + 1 / 2) / (n + 2 : ℝ) * flowHalfBinomialCoeff n ≤
              ((n : ℝ) + 1 / 2) / (n + 2 : ℝ) *
                (1 / ((4 : ℝ) * ((n : ℝ) + 1))) :=
                  mul_le_mul_of_nonneg_left (ih hn') hratio
          _ ≤ ((n : ℝ) + 1) / (n + 2 : ℝ) *
                (1 / ((4 : ℝ) * ((n : ℝ) + 1))) :=
                  mul_le_mul_of_nonneg_right hratio' (by positivity)
          _ = 1 / ((4 : ℝ) * ((n : ℝ) + 2)) := by
            field_simp
          _ = 1 / ((4 : ℝ) * (((n + 1 : ℕ) : ℝ) + 1)) := by
            congr 1
            norm_cast

/-- Along a jointly smooth flow, every ordered spatial coordinate jet obeys
the time derivative obtained by applying the same jet to the vector field
composed with the flow. -/
theorem flow_orderedPartial_hasDerivAt
    {b : ℝ → Vec 2 → Vec 2} (hb : AVenhance.Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (hXsmooth : ContDiff ℝ ∞
      (fun p : (ℝ × Vec 2) × ℝ => X p.1.1 p.1.2 p.2))
    (s t : ℝ) (x : Vec 2) {n : ℕ} (I : Fin n → Fin 2) :
    HasDerivAt (fun r => orderedPartial n (fun y => X r y s) x I)
      (orderedPartial n (fun y => b t (X t y s)) x I) t := by
  let F : ℝ × Vec 2 → Vec 2 := fun p => X p.1 p.2 s
  let Q : ℝ × Vec 2 → Vec 2 := fun p => b p.1 (F p)
  let V : List (Vec 2) := List.ofFn (fun j => coordinateVector 2 (I j))
  have hF : ContDiff ℝ ∞ F := by
    have hmap : ContDiff ℝ ∞
        (fun p : ℝ × Vec 2 => ((p.1, p.2), s)) := by
      fun_prop
    exact hXsmooth.comp hmap
  have hQ : ContDiff ℝ ∞ Q := by
    have hmap : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => (p.1, F p)) :=
      contDiff_fst.prodMk hF
    simpa [Q, Function.uncurry, Function.comp_def] using hb.smooth.comp hmap
  have hODE : jointTimeDerivative F = Q := by
    funext p
    rcases p with ⟨r, y⟩
    let c : ℝ → ℝ × Vec 2 := fun q => (q, y)
    have hc : HasFDerivAt c
        (ContinuousLinearMap.inl ℝ ℝ (Vec 2)) r :=
      hasFDerivAt_prodMk_left r y
    have hFdiff : DifferentiableAt ℝ F (r, y) := hF.differentiable (by simp) (r, y)
    have hcomp := hFdiff.hasFDerivAt.comp r hc
    have hflow : HasDerivAt (fun q => X q y s) (b r (X r y s)) r :=
      hX.2 y s r
    have hcompDeriv : HasDerivAt (fun q => X q y s)
        (((fderiv ℝ F (r, y)).comp (ContinuousLinearMap.inl ℝ ℝ (Vec 2))) 1) r := by
      simpa [c, F, Function.comp_def] using hcomp.hasDerivAt
    have hcomp' : HasDerivAt (fun q => X q y s)
        (fderiv ℝ F (r, y) (1, 0)) r := by
      convert hcompDeriv using 1
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
    have heq := HasDerivAt.unique hcomp' hflow
    simpa [jointTimeDerivative, Q, F] using heq
  let J : ℝ × Vec 2 → Vec 2 := transportSpatialJet V F
  have hJ : ContDiff ℝ ∞ J := transportSpatialJet_contDiff V F hF
  have hpath : HasDerivAt (fun r => J (r, x))
      (jointTimeDerivative J (t, x)) t := by
    let c : ℝ → ℝ × Vec 2 := fun r => (r, x)
    have hc : HasFDerivAt c
        (ContinuousLinearMap.inl ℝ ℝ (Vec 2)) t :=
      hasFDerivAt_prodMk_left t x
    have hJdiff : DifferentiableAt ℝ J (t, x) :=
      hJ.differentiable (by simp) (t, x)
    have hcomp := hJdiff.hasFDerivAt.comp t hc
    have hcompDeriv : HasDerivAt (fun r => J (r, x))
        (((fderiv ℝ J (t, x)).comp (ContinuousLinearMap.inl ℝ ℝ (Vec 2))) 1) t := by
      simpa [c, Function.comp_def] using hcomp.hasDerivAt
    have hcomp' : HasDerivAt (fun r => J (r, x))
        (fderiv ℝ J (t, x) (1, 0)) t := by
      convert hcompDeriv using 1
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
    simpa [jointTimeDerivative] using hcomp'
  have hJdir : J = directionalJet (jointSpatialDirections V) F :=
    transportSpatialJet_eq_jointDirectionalJet V F
  have hcomm := directionalJet_jointTime_commute V F hF
  have htimeJet : jointTimeDerivative J = transportSpatialJet V Q := by
    calc
      jointTimeDerivative J =
          jointTimeDerivative (directionalJet (jointSpatialDirections V) F) :=
            congrArg jointTimeDerivative hJdir
      _ = directionalJet (jointSpatialDirections V) (jointTimeDerivative F) :=
            hcomm.symm
      _ = directionalJet (jointSpatialDirections V) Q := by rw [hODE]
      _ = transportSpatialJet V Q := by
            rw [transportSpatialJet_eq_jointDirectionalJet]
  have hLhs : (fun r => J (r, x)) =
      (fun r => orderedPartial n (fun y => X r y s) x I) := by
    funext r
    change transportSpatialJet V
      (Function.uncurry (fun q y => X q y s)) (r, x) = _
    exact transportSpatialJet_coordinate_eq_orderedPartial I
      (fun q y => X q y s) (by change ContDiff ℝ ∞ F; exact hF) r x
  have hRhs : transportSpatialJet V Q (t, x) =
      orderedPartial n (fun y => b t (X t y s)) x I := by
    change transportSpatialJet V
      (Function.uncurry (fun q y => b q (X q y s))) (t, x) = _
    exact transportSpatialJet_coordinate_eq_orderedPartial I
      (fun q y => b q (X q y s)) (by change ContDiff ℝ ∞ Q; exact hQ) t x
  rw [hLhs] at hpath
  have hderivVal : jointTimeDerivative J (t, x) =
      orderedPartial n (fun y => b t (X t y s)) x I := by
    rw [htimeJet, hRhs]
  simpa [hderivVal] using hpath

/-- The final reduction step in `p.ODE.flow.2`: the paper's level `n+1`
bound on the flow itself implies its level-`n` gradient bound. The input
coefficient is the signed half-binomial coefficient, for which
`4 * A ≤ 1 / (n + 1)`; the resulting dimension-two bound is at most 6, hence
the paper's target 12. -/
theorem flow_spatialGradient_snorm_of_Dn
    {n : ℕ} {b : ℝ → Vec 2 → Vec 2}
    {X : ℝ → Vec 2 → ℝ → Vec 2} (_hX : AVenhance.IsFlow b X)
    (hXsmooth : ContDiff ℝ ∞
      (fun p : (ℝ × Vec 2) × ℝ => X p.1.1 p.1.2 p.2))
    {C_f R_f A : ℝ} (hCf : 0 < C_f) (hRf : 0 < R_f)
    (hA : 0 ≤ A) (hAhalf : 4 * A ≤ 1 / (n + 1 : ℝ))
    {t : ℝ} (ht : |t| ≤ 1 / (8 * C_f * R_f))
    (hDn : snorm (fun x => X t x 0) (n + 1)
      (8 * 2 * R_f * (1 + (8 * 2 * C_f * R_f) * |t|)) ≤
        ENNReal.ofReal (A / (2 * R_f))) :
    snorm (spatialGradientMatrix (fun y => X t y 0)) n
      (8 * 2 * R_f * (1 + (8 * 2 * C_f * R_f) * |t|)) ≤ ENNReal.ofReal 12 := by
  let f : Vec 2 → Vec 2 := fun x => X t x 0
  let Rflow : ℝ := 8 * 2 * R_f * (1 + (8 * 2 * C_f * R_f) * |t|)
  have hRflow : 0 < Rflow := by dsimp [Rflow]; positivity
  have hf : ContDiff ℝ ∞ f := by
    have hmap : ContDiff ℝ ∞ (fun x : Vec 2 => ((t, x), (0 : ℝ))) := by
      fun_prop
    exact hXsmooth.comp hmap
  have hDnext := derivativeSup_le_of_snorm_le f hRflow hDn
  have hDgrad : derivativeSup n (spatialGradientMatrix f) ≤
      ENNReal.ofReal
        (A / (2 * R_f) * (n + 1).factorial * Rflow ^ (n + 1) /
          ((n + 1 : ℕ) + 1 : ℝ) ^ 2) := by
    calc
      derivativeSup n (spatialGradientMatrix f) ≤ derivativeSup (n + 1) f :=
        spatialGradientMatrix_derivativeSup_le f hf n
      _ ≤ ENNReal.ofReal
          (A / (2 * R_f) * (n + 1).factorial * Rflow ^ (n + 1) /
            ((n + 1 : ℕ) + 1 : ℝ) ^ 2) := hDnext
  let Cgrad : ℝ := (A / (2 * R_f)) * Rflow *
    ((n + 1 : ℝ) ^ 3 / (n + 2 : ℝ) ^ 2)
  have hscale : A / (2 * R_f) * (n + 1).factorial * Rflow ^ (n + 1) /
      ((n + 1 : ℕ) + 1 : ℝ) ^ 2 ≤ Cgrad * Rflow ^ n * n.factorial /
        ((n : ℝ) + 1) ^ 2 := by
    have hfac : ((n + 1).factorial : ℝ) = (n + 1 : ℝ) * n.factorial := by
      rw [Nat.factorial_succ]
      norm_cast
    rw [hfac]
    dsimp [Cgrad]
    have hq : (n + 2 : ℝ) = (n + 1 : ℝ) + 1 := by ring
    rw [hq]
    have hRne : Rflow ≠ 0 := ne_of_gt hRflow
    have hRpow : Rflow ^ (n + 1) = Rflow ^ n * Rflow := by rw [pow_succ]
    rw [hRpow]
    field_simp
    push_cast
    rfl
  have hDgrad' : derivativeSup n (spatialGradientMatrix f) ≤
      ENNReal.ofReal
        (Cgrad * Rflow ^ n * n.factorial / (n + 1 : ℝ) ^ 2) := by
    exact hDgrad.trans (ENNReal.ofReal_le_ofReal hscale)
  have hgrad := snorm_le_of_derivativeSup_le
    (spatialGradientMatrix f) hRflow hDgrad'
  have hqpos : 0 < (n + 1 : ℝ) := by positivity
  have hqratio : (n + 1 : ℝ) ^ 3 / (n + 2 : ℝ) ^ 2 ≤ (n + 1 : ℝ) := by
    rw [show (n + 2 : ℝ) = (n + 1 : ℝ) + 1 by ring]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg ((n + 1 : ℝ) - 1)]
  have hRupper : Rflow ≤ 48 * R_f := by
    have habs : 16 * C_f * R_f * |t| ≤ 2 := by
      have hden : 0 < 8 * C_f * R_f := by positivity
      have hsmall' : |t| * (8 * C_f * R_f) ≤ 1 :=
        (le_div_iff₀ hden).mp ht
      have hsmall : (8 * C_f * R_f) * |t| ≤ 1 := by
        simpa [mul_comm] using hsmall'
      nlinarith [hsmall]
    dsimp [Rflow]
    nlinarith [habs, hRf.le]
  have hCgrad : Cgrad ≤ 6 := by
    have hA' : A * (n + 1 : ℝ) ≤ 1 / 4 := by
      have hmul : (4 * A) * (n + 1 : ℝ) ≤ 1 :=
        (le_div_iff₀ hqpos).mp hAhalf
      nlinarith [hmul]
    dsimp [Cgrad]
    have hfirst : (A / (2 * R_f)) * Rflow ≤
        (A / (2 * R_f)) * (48 * R_f) :=
      mul_le_mul_of_nonneg_left hRupper (by positivity)
    have hsecond : (A / (2 * R_f)) * (48 * R_f) *
        ((n + 1 : ℝ) ^ 3 / (n + 2 : ℝ) ^ 2) ≤
        (A / (2 * R_f)) * (48 * R_f) * (n + 1 : ℝ) :=
      mul_le_mul_of_nonneg_left hqratio (by positivity)
    calc
      (A / (2 * R_f)) * Rflow *
          ((n + 1 : ℝ) ^ 3 / (n + 2 : ℝ) ^ 2) ≤
        (A / (2 * R_f)) * (48 * R_f) *
          ((n + 1 : ℝ) ^ 3 / (n + 2 : ℝ) ^ 2) := by
            exact mul_le_mul_of_nonneg_right hfirst (by positivity)
      _ ≤ (A / (2 * R_f)) * (48 * R_f) * (n + 1 : ℝ) := hsecond
      _ = 24 * (A * (n + 1 : ℝ)) := by
        have hRne : R_f ≠ 0 := ne_of_gt hRf
        field_simp
        ring
      _ ≤ 6 := by nlinarith [hA']
  have hgrad' : ENNReal.ofReal Cgrad ≤ ENNReal.ofReal 12 :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have hnorm : Rflow = 8 * 2 * R_f *
      (1 + (8 * 2 * C_f * R_f) * |t|) := rfl
  rw [← hnorm]
  exact hgrad.trans hgrad'

/-- The reduction in `p.ODE.flow.2` with the paper's actual signed
half-binomial coefficient at order `n+1`. -/
theorem flow_spatialGradient_snorm_of_flowDn
    {n : ℕ} (hn : 1 ≤ n) {b : ℝ → Vec 2 → Vec 2}
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (hXsmooth : ContDiff ℝ ∞
      (fun p : (ℝ × Vec 2) × ℝ => X p.1.1 p.1.2 p.2))
    {C_f R_f : ℝ} (hCf : 0 < C_f) (hRf : 0 < R_f)
    {t : ℝ} (ht : |t| ≤ 1 / (8 * C_f * R_f))
    (hDn : snorm (fun x => X t x 0) (n + 1)
      (8 * 2 * R_f * (1 + (8 * 2 * C_f * R_f) * |t|)) ≤
        ENNReal.ofReal (flowHalfBinomialCoeff n / (2 * R_f))) :
    snorm (spatialGradientMatrix (fun y => X t y 0)) n
      (8 * 2 * R_f * (1 + (8 * 2 * C_f * R_f) * |t|)) ≤ ENNReal.ofReal 12 := by
  have hA : 0 ≤ flowHalfBinomialCoeff n := flowHalfBinomialCoeff_nonneg hn
  have hAhalf : 4 * flowHalfBinomialCoeff n ≤ 1 / (n + 1 : ℝ) := by
    have hsmall := flowHalfBinomialCoeff_le_inverse hn
    have hmul := mul_le_mul_of_nonneg_left hsmall
      (show 0 ≤ (4 : ℝ) by norm_num)
    have hbound : 4 * flowHalfBinomialCoeff n ≤ 1 / ((n : ℝ) + 1) := by
      calc
        _ ≤ 4 * (1 / ((4 : ℝ) * ((n : ℝ) + 1))) := hmul
        _ = 1 / ((n : ℝ) + 1) := by field_simp
    simpa [Nat.cast_add, Nat.cast_one] using hbound
  exact flow_spatialGradient_snorm_of_Dn hX hXsmooth hCf hRf hA hAhalf ht hDn

/-- For an arbitrary starting time, the inverse displacement solves the
transport equation for the time-shifted velocity. This is the characteristic
identity needed to apply Lemma 10577 at each center `s` in the stream
recursion; the smoothness witness remains explicit. -/
theorem flow_inverse_displacement_at_start_isTransportSolution_of_jointSmooth
    {b : ℝ → Vec 2 → Vec 2} (hb : AVenhance.Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (hXsmooth : ContDiff ℝ ∞
      (fun p : (ℝ × Vec 2) × ℝ => X p.1.1 p.1.2 p.2)) (s : ℝ) :
    IsClassicalTransportSolution
      (fun t x => b (s + t) x)
      (fun t x => -b (s + t) x)
      (fun t x => X s x (s + t) - x) := by
  let bs : ℝ → Vec 2 → Vec 2 := fun t x => b (s + t) x
  let Xs : ℝ → Vec 2 → ℝ → Vec 2 := fun t x r => X (s + t) x (s + r)
  have hbs : AVenhance.Infra.Flow.SmoothPeriodicField bs := by
    refine ⟨?_, ?_⟩
    · have hmap : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 => (s + p.1, p.2)) := by
        fun_prop
      change ContDiff ℝ ∞
        (Function.uncurry b ∘ fun p : ℝ × Vec 2 => (s + p.1, p.2))
      exact hb.smooth.comp hmap
    · intro m k t x
      calc
        b (s + (t + (m : ℝ))) (x + AVenhance.latticeShift k) =
            b ((s + t) + (m : ℝ)) (x + AVenhance.latticeShift k) := by
          congr 1
          ring
        _ = b (s + t) x := hb.periodic m k (s + t) x
  have hXs : AVenhance.IsFlow bs Xs := by
    refine ⟨?_, ?_⟩
    · intro x r
      dsimp [Xs]
      exact hX.1 x (s + r)
    · intro x r t
      have hbase : HasDerivAt (fun q => X q x (s + r))
          (b (t + s) (X (t + s) x (s + r))) (t + s) := by
        simpa [add_comm] using hX.2 x (s + r) (s + t)
      have h := hbase.comp_add_const t s
      convert h using 1 <;> simp [Xs, bs, add_comm]
  have hXsSmooth : ContDiff ℝ ∞
      (fun p : (ℝ × Vec 2) × ℝ => Xs p.1.1 p.1.2 p.2) := by
    have hmap : ContDiff ℝ ∞
      (fun p : (ℝ × Vec 2) × ℝ => ((s + p.1.1, p.1.2), s + p.2)) := by
      fun_prop
    change ContDiff ℝ ∞
      ((fun p : (ℝ × Vec 2) × ℝ => X p.1.1 p.1.2 p.2) ∘
        fun p : (ℝ × Vec 2) × ℝ =>
        ((s + p.1.1, p.1.2), s + p.2))
    exact hXsmooth.comp hmap
  have hsolution := flow_inverse_displacement_isTransportSolution_of_jointSmooth
    hbs hXs hXsSmooth
  simpa [bs, Xs] using hsolution

end AVenhance.FaaDiBruno

end
