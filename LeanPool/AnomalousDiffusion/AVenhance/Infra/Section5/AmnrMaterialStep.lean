/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.MaterialGradient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.QMNRRecursion
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureCoefficientBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureEnergyIntegrability
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureFluxBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.DriftCommutatorExpansion
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureMaterialInduction
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TensorNorm
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.SeedMultiplierSourceBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureIterateClassicalFamily
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.DissipationCoordinateL2
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsThetaAnalytic
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureCoefficientTopSourceBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.SourceSmallnessThreshold
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Construction.StreamRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.LRecurse

/-! Differentiating spatial divergence under the `A` material
recursion. -/

@[expose] public section

open Homogenization
open Filter
open scoped ContDiff Topology

noncomputable section

namespace AVenhance.Infra.Section5

open AVenhance

/-- Joint time-space domain for the two-dimensional residual calculation. -/
abbrev ST := ℝ × Vec 2

/-- Spatial divergence of a vector field on joint time-space. -/
def stDiv (F : ST → Vec 2) (p : ST) : ℝ :=
  ∑ i : Fin 2, (fderiv ℝ F p (0, basisVec i)) i

/-- Spatial divergence is unchanged when vector fields agree near the
space-time point. -/
theorem stDiv_congr_of_eventuallyEq
    {F G : ST → Vec 2} {p : ST}
    (hF : DifferentiableAt ℝ F p)
    (hEq : F =ᶠ[𝓝 p] G) :
    stDiv F p = stDiv G p := by
  have hF' : HasFDerivAt F (fderiv ℝ F p) p := hF.hasFDerivAt
  have hG' : HasFDerivAt G (fderiv ℝ F p) p :=
    hF'.congr_of_eventuallyEq hEq.symm
  have hderiv : fderiv ℝ F p = fderiv ℝ G p :=
    hF'.fderiv.trans hG'.fderiv.symm
  simp only [stDiv, hderiv]

/-- Material derivative of a vector field along the prescribed drift. -/
def stMaterial (F b : ST → Vec 2) (p : ST) : Vec 2 :=
  fderiv ℝ F p (1, b p)

/-- Jacobian of the drift applied to a vector field, the correction in the Lie derivative. -/
def stCorrection (F b : ST → Vec 2) (p : ST) : Vec 2 :=
  fun i => ∑ j : Fin 2, (fderiv ℝ b p (0, basisVec j)) i * F p j

/-- Lie derivative obtained by subtracting the drift-Jacobian correction from material
transport. -/
def stLieDerivative (F b : ST → Vec 2) (p : ST) : Vec 2 :=
  stMaterial F b p - stCorrection F b p

/-- Continuous linear differential of the spatial divergence, expressed using second
derivatives. -/
def AmnrMaterialStep.stDivDerivative (F : ST → Vec 2) (p : ST) : ST →L[ℝ] ℝ :=
  ∑ i : Fin 2, (ContinuousLinearMap.proj i).comp
    ((fderiv ℝ (fderiv ℝ F) p).flip (0, basisVec i))

/-- Differential of the drift-Jacobian correction, expressed by the product rule. -/
def AmnrMaterialStep.stCorrectionDerivative (F b : ST → Vec 2) (p : ST) :
    ST →L[ℝ] Vec 2 := by
  let DF : ST →L[ℝ] Vec 2 := fderiv ℝ F p
  let D2b : ST →L[ℝ] (ST →L[ℝ] Vec 2) := fderiv ℝ (fderiv ℝ b) p
  exact ContinuousLinearMap.pi fun i : Fin 2 =>
    ((fderiv ℝ b p (0, basisVec 0) i) •
        ((ContinuousLinearMap.proj 0).comp DF) +
      (F p 0) • ((ContinuousLinearMap.proj i).comp
        (D2b.flip (0, basisVec 0)))) +
    ((fderiv ℝ b p (0, basisVec 1) i) •
        ((ContinuousLinearMap.proj 1).comp DF) +
      (F p 1) • ((ContinuousLinearMap.proj i).comp
        (D2b.flip (0, basisVec 1))))

theorem stDiv_hasFDerivAt
    {F : ST → Vec 2} {p : ST} (hF : ContDiffAt ℝ 2 F p) :
    HasFDerivAt (stDiv F) (AmnrMaterialStep.stDivDerivative F p) p := by
  let D2 : ST →L[ℝ] (ST →L[ℝ] Vec 2) := fderiv ℝ (fderiv ℝ F) p
  have hDFcont : ContDiffAt ℝ 1 (fderiv ℝ F) p :=
    hF.fderiv_right (m := 1) (by norm_num)
  have hDF : HasFDerivAt (fderiv ℝ F) D2 p :=
    (hDFcont.differentiableAt (by norm_num)).hasFDerivAt
  have hpart (i : Fin 2) :
      HasFDerivAt (fun q => (fderiv ℝ F q (0, basisVec i)) i)
        ((ContinuousLinearMap.proj i).comp (D2.flip (0, basisVec i))) p := by
    have hclm : HasFDerivAt (fun q => fderiv ℝ F q (0, basisVec i))
        (D2.flip (0, basisVec i)) p := by
      simpa [D2, ContinuousLinearMap.comp_zero] using
        hDF.clm_apply (hasFDerivAt_const (0, basisVec i) p)
    have hproj := (ContinuousLinearMap.proj i).hasFDerivAt.comp p hclm
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using hproj
  have h := (hpart 0).add (hpart 1)
  have heq : stDiv F = (fun q =>
      (fderiv ℝ F q (0, basisVec 0)) 0 +
        (fderiv ℝ F q (0, basisVec 1)) 1) := by
    funext q
    simp [stDiv, Fin.sum_univ_two]
  rw [heq]
  have h' : HasFDerivAt (fun q =>
      (fderiv ℝ F q (0, basisVec 0)) 0 +
        (fderiv ℝ F q (0, basisVec 1)) 1)
      ((ContinuousLinearMap.proj 0).comp (D2.flip (0, basisVec 0)) +
        (ContinuousLinearMap.proj 1).comp (D2.flip (0, basisVec 1))) p := by
    apply h.congr_of_eventuallyEq
    filter_upwards [] with q
    rfl
  simpa [AmnrMaterialStep.stDivDerivative, D2, Fin.sum_univ_two] using h'

theorem AmnrMaterialStep.stMaterial_hasFDerivAt
    {F b : ST → Vec 2} {p : ST}
    (hF : ContDiffAt ℝ 2 F p) (hb : ContDiffAt ℝ 2 b p) :
    HasFDerivAt (fun q => stMaterial F b q)
      ((fderiv ℝ F p).comp
          ((0 : ST →L[ℝ] ℝ).prod (fderiv ℝ b p)) +
        (fderiv ℝ (fderiv ℝ F) p).flip (1, b p)) p := by
  let D2 : ST →L[ℝ] (ST →L[ℝ] Vec 2) := fderiv ℝ (fderiv ℝ F) p
  let LV : ST →L[ℝ] ST := (0 : ST →L[ℝ] ℝ).prod (fderiv ℝ b p)
  have hDFcont : ContDiffAt ℝ 1 (fderiv ℝ F) p :=
    hF.fderiv_right (m := 1) (by norm_num)
  have hDF : HasFDerivAt (fderiv ℝ F) D2 p :=
    (hDFcont.differentiableAt (by norm_num)).hasFDerivAt
  have hb' : HasFDerivAt b (fderiv ℝ b p) p :=
    (hb.differentiableAt (by norm_num)).hasFDerivAt
  have hV : HasFDerivAt (fun q => (1, b q)) LV p := by
    simpa [LV] using (hasFDerivAt_const (1 : ℝ) p).prodMk hb'
  have h := hDF.clm_apply hV
  convert h using 1
  simp [stMaterial]

theorem AmnrMaterialStep.stCorrection_hasFDerivAt
    {F b : ST → Vec 2} {p : ST}
    (hF : ContDiffAt ℝ 2 F p) (hb : ContDiffAt ℝ 2 b p) :
    HasFDerivAt (fun q => stCorrection F b q)
      (AmnrMaterialStep.stCorrectionDerivative F b p) p := by
  let D2b : ST →L[ℝ] (ST →L[ℝ] Vec 2) := fderiv ℝ (fderiv ℝ b) p
  have hDbcont : ContDiffAt ℝ 1 (fderiv ℝ b) p :=
    hb.fderiv_right (m := 1) (by norm_num)
  have hDb : HasFDerivAt (fderiv ℝ b) D2b p :=
    (hDbcont.differentiableAt (by norm_num)).hasFDerivAt
  have hBpart (i j : Fin 2) :
      HasFDerivAt (fun q => (fderiv ℝ b q (0, basisVec j)) i)
        ((ContinuousLinearMap.proj i).comp (D2b.flip (0, basisVec j))) p := by
    have hclm : HasFDerivAt (fun q => fderiv ℝ b q (0, basisVec j))
        (D2b.flip (0, basisVec j)) p := by
      simpa [D2b, ContinuousLinearMap.comp_zero] using
        hDb.clm_apply (hasFDerivAt_const (0, basisVec j) p)
    have hproj := (ContinuousLinearMap.proj i).hasFDerivAt.comp p hclm
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using hproj
  have hFpart (j : Fin 2) :
      HasFDerivAt (fun q => F q j)
        ((ContinuousLinearMap.proj j).comp (fderiv ℝ F p)) p := by
    have h := (ContinuousLinearMap.proj j).hasFDerivAt.comp p
      ((hF.differentiableAt (by norm_num)).hasFDerivAt)
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using h
  have hentry (i : Fin 2) (j : Fin 2) :
      HasFDerivAt (fun q => (fderiv ℝ b q (0, basisVec j)) i * F q j)
        ((fderiv ℝ b p (0, basisVec j) i) •
            ((ContinuousLinearMap.proj j).comp (fderiv ℝ F p)) +
          (F p j) • ((ContinuousLinearMap.proj i).comp
            (D2b.flip (0, basisVec j)))) p := by
    have h := (hBpart i j).mul (hFpart j)
    exact h
  have hcorrection (i : Fin 2) :
      HasFDerivAt (fun q =>
        (fderiv ℝ b q (0, basisVec 0)) i * F q 0 +
          (fderiv ℝ b q (0, basisVec 1)) i * F q 1)
        (((fderiv ℝ b p (0, basisVec 0) i) •
              ((ContinuousLinearMap.proj 0).comp (fderiv ℝ F p)) +
            (F p 0) • ((ContinuousLinearMap.proj i).comp
              (D2b.flip (0, basisVec 0)))) +
          ((fderiv ℝ b p (0, basisVec 1) i) •
              ((ContinuousLinearMap.proj 1).comp (fderiv ℝ F p)) +
            (F p 1) • ((ContinuousLinearMap.proj i).comp
              (D2b.flip (0, basisVec 1))))) p := by
    have h := (hentry i 0).add (hentry i 1)
    convert h using 1
  have hpi : HasFDerivAt (fun q => stCorrection F b q)
      (AmnrMaterialStep.stCorrectionDerivative F b p) p := by
    convert hasFDerivAt_pi.2 hcorrection using 1
    · funext q i
      simp [stCorrection, Fin.sum_univ_two]
    · rfl
  exact hpi

theorem AmnrMaterialStep.stLieDerivative_hasFDerivAt
    {F b : ST → Vec 2} {p : ST}
    (hF : ContDiffAt ℝ 2 F p) (hb : ContDiffAt ℝ 2 b p) :
    HasFDerivAt (fun q => stLieDerivative F b q)
      ((fderiv ℝ F p).comp
          ((0 : ST →L[ℝ] ℝ).prod (fderiv ℝ b p)) +
        (fderiv ℝ (fderiv ℝ F) p).flip (1, b p) -
          AmnrMaterialStep.stCorrectionDerivative F b p) p := by
  exact (AmnrMaterialStep.stMaterial_hasFDerivAt hF hb).sub
      (AmnrMaterialStep.stCorrection_hasFDerivAt hF hb)

/-- The row-corrected material derivative is differentiable whenever the
flux and velocity have two derivatives at the point. -/
theorem stLieDerivative_differentiableAt
    {F b : ST → Vec 2} {p : ST}
    (hF : ContDiffAt ℝ 2 F p) (hb : ContDiffAt ℝ 2 b p) :
    DifferentiableAt ℝ (stLieDerivative F b) p :=
  (AmnrMaterialStep.stLieDerivative_hasFDerivAt hF hb).differentiableAt

/-- Vector flux formed by fixing two tensor indices and multiplying by the time coefficient. -/
def AmnrMaterialStep.tensorPairFlux
    (A : ST → Fin 2 → Fin 2 → Fin 2 → ℝ)
    (q : ℝ → Fin 2 → Fin 2 → ℝ) (j k : Fin 2) : ST → Vec 2 :=
  fun z i => A z i j k * q z.1 j k

/-- For one pair of tensor indices, the row-corrected material derivative of
`A^{·jk} q⁺^{jk}` is `A⁺^{·jk} q⁺^{jk} - A^{·jk} q^{jk}`. The recurrence
hypothesis is the coefficient form of the source's recursion; the proof
is just the product rule and the time primitive derivative. -/
theorem tensorPair_correctedMaterial
    {A Aplus : ST → Fin 2 → Fin 2 → Fin 2 → ℝ}
    {q qplus : ℝ → Fin 2 → Fin 2 → ℝ}
    {b : ST → Vec 2} {p : ST}
    {LA : Fin 2 → Fin 2 → Fin 2 → ST →L[ℝ] ℝ}
    (j k : Fin 2)
    (hA : ∀ i, HasFDerivAt (fun z => A z i j k) (LA i j k) p)
    (hq : HasDerivAt (fun s => qplus s j k) (-(q p.1 j k)) p.1)
    (hrec : ∀ i, Aplus p i j k =
      LA i j k (1, b p) -
        ∑ ℓ : Fin 2,
          (fderiv ℝ b p (0, basisVec ℓ) i) * A p ℓ j k) :
    stLieDerivative (AmnrMaterialStep.tensorPairFlux A qplus j k) b p =
      fun i => Aplus p i j k * qplus p.1 j k - A p i j k * q p.1 j k := by
  let fstD : ST →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (Vec 2)
  let Lq : ST →L[ℝ] ℝ :=
    (ContinuousLinearMap.toSpanSingleton ℝ (-(q p.1 j k))).comp fstD
  have hqLift : HasFDerivAt (fun z : ST => qplus z.1 j k)
      Lq p := by
    have h := hq.hasFDerivAt.comp p
      (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := Vec 2))
    simpa [fstD, Function.comp_def] using h
  have hqDir : Lq (1, b p) = -(q p.1 j k) := by
    simp [Lq, fstD, ContinuousLinearMap.comp_apply]
  let LP : ST →L[ℝ] Vec 2 := ContinuousLinearMap.pi fun i =>
    A p i j k • Lq + qplus p.1 j k • LA i j k
  have hflux : HasFDerivAt (AmnrMaterialStep.tensorPairFlux A qplus j k) LP p := by
    apply hasFDerivAt_pi.2
    intro i
    have h := (hA i).mul hqLift
    convert h using 1
    · ext z
      rfl
  have hcomponent (i : Fin 2) :
    fderiv ℝ (AmnrMaterialStep.tensorPairFlux A qplus j k) p (1, b p) i =
        qplus p.1 j k * (LA i j k (1, b p)) - A p i j k * q p.1 j k := by
    rw [hflux.fderiv]
    simp [LP, Lq, hqDir, ContinuousLinearMap.pi_apply,
      smul_apply, smul_eq_mul]
    ring
  ext i
  change fderiv ℝ (AmnrMaterialStep.tensorPairFlux A qplus j k) p (1, b p) i -
      ∑ ℓ : Fin 2,
        (fderiv ℝ b p (0, basisVec ℓ) i) *
          AmnrMaterialStep.tensorPairFlux A qplus j k p ℓ = _
  rw [hcomponent i, hrec i]
  simp only [AmnrMaterialStep.tensorPairFlux, Fin.sum_univ_two]
  ring

/-- The AMNR recursion and the primitive recursion for `q` give the corrected
material derivative of each `Amnr` row and each fixed `(j,k)` pair. The only
regularity inputs are differentiability of that `A_r` coefficient and of the
previous stream velocity at the spacetime point. -/
theorem frozen_amnrPair_correctedMaterial
    {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (n r : ℕ) (T : ℝ → Vec 2 → ℝ)
    (t : ℝ) (x : Vec 2) (j k : Fin 2)
    (hA : ∀ i : Fin 2, DifferentiableAt ℝ
      (Function.uncurry (fun s y => I.Amnr hΦ m κ n T r s y i j k)) (t, x))
    (hb : DifferentiableAt ℝ
      (Function.uncurry (fun s y => AVenhance.streamVel (Φ (m - 1)) s y)) (t, x)) :
    stLieDerivative
      (AmnrMaterialStep.tensorPairFlux
        (fun z i j k => I.Amnr hΦ m κ n T r z.1 z.2 i j k)
        (fun s j k => I.qMNR κ m n (r + 1) s j k) j k)
      (fun z => AVenhance.streamVel (Φ (m - 1)) z.1 z.2) (t, x) =
      fun i => I.Amnr hΦ m κ n T (r + 1) t x i j k *
          I.qMNR κ m n (r + 1) t j k -
        I.Amnr hΦ m κ n T r t x i j k * I.qMNR κ m n r t j k := by
  let A : ST → Fin 2 → Fin 2 → Fin 2 → ℝ :=
    fun z i j k => I.Amnr hΦ m κ n T r z.1 z.2 i j k
  let Aplus : ST → Fin 2 → Fin 2 → Fin 2 → ℝ :=
    fun z i j k => I.Amnr hΦ m κ n T (r + 1) z.1 z.2 i j k
  let q : ℝ → Fin 2 → Fin 2 → ℝ := fun s j k => I.qMNR κ m n r s j k
  let qplus : ℝ → Fin 2 → Fin 2 → ℝ :=
    fun s j k => I.qMNR κ m n (r + 1) s j k
  let b : ST → Vec 2 := fun z => AVenhance.streamVel (Φ (m - 1)) z.1 z.2
  let LA : Fin 2 → Fin 2 → Fin 2 → ST →L[ℝ] ℝ := fun i j k =>
    fderiv ℝ (fun z : ST => A z i j k) (t, x)
  have hA' (i : Fin 2) : HasFDerivAt (fun z : ST => A z i j k)
      (LA i j k) (t, x) := by
    convert (hA i).hasFDerivAt using 1 <;> rfl
  have hmaterial (i : Fin 2) :
      AVenhance.Infra.Section4.amnrMaterial
          (AVenhance.streamVel (Φ (m - 1)))
          (fun s y => I.Amnr hΦ m κ n T r s y i j k) t x =
        LA i j k (1, b (t, x)) := by
    have h := materialDerivative_eq_advective_of_hasFDerivAt
      (b := fun s y => AVenhance.streamVel (Φ (m - 1)) s y) (hA i).hasFDerivAt
    rw [materialDerivative] at h
    change deriv (fun s => I.Amnr hΦ m κ n T r s x i j k) t +
        vecDot (AVenhance.streamVel (Φ (m - 1)) t x)
          (spaceGrad (fun y => I.Amnr hΦ m κ n T r t y i j k) x) =
      (fderiv ℝ (fun z : ST => A z i j k) (t, x)) (1, b (t, x))
    convert h.symm using 1
    rfl
  have hgrad (i ℓ : Fin 2) :
      spaceGrad (fun y => AVenhance.streamVel (Φ (m - 1)) t y i) x ℓ =
        (fderiv ℝ b (t, x) (0, basisVec ℓ)) i := by
    let B := fun s y => AVenhance.streamVel (Φ (m - 1)) s y
    have hslice : DifferentiableAt ℝ (B t) x := by
      have h := hb.comp x (hasFDerivAt_prodMk_right t x).differentiableAt
      simpa [B, Function.uncurry, Function.comp_def] using h
    have hproj : HasFDerivAt (fun y => B t y i)
        ((ContinuousLinearMap.proj i).comp (fderiv ℝ (B t) x)) x := by
      exact (ContinuousLinearMap.proj i).hasFDerivAt.comp x hslice.hasFDerivAt
    have hcomponent : spaceGrad (fun y => B t y i) x ℓ =
        (fderiv ℝ (B t) x (basisVec ℓ)) i := by
      rw [spaceGrad, hproj.fderiv]
      simp [ContinuousLinearMap.comp_apply]
    have h := congrArg (fun w : Vec 2 => w i)
      (fderiv_uncurry_vector_spatial (B := fun s y =>
        AVenhance.streamVel (Φ (m - 1)) s y) (t := t) (x := x)
        (v := basisVec ℓ) hb)
    rw [hcomponent]
    convert h.symm using 1
    rfl
  have hrec (i : Fin 2) :
      Aplus (t, x) i j k =
        LA i j k (1, b (t, x)) -
          ∑ ℓ : Fin 2, (fderiv ℝ b (t, x) (0, basisVec ℓ)) i *
            A (t, x) ℓ j k := by
    change I.Amnr hΦ m κ n T (r + 1) t x i j k = _
    rw [AVenhance.Infra.Section4.Amnr_succ]
    rw [← hmaterial i]
    congr 1
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    rw [hgrad i ℓ]
  simpa [A, Aplus, q, qplus, b] using
    (tensorPair_correctedMaterial (A := A) (Aplus := Aplus)
      (q := q) (qplus := qplus) (b := b) (p := (t, x)) (LA := LA)
      j k (fun i => hA' i)
      (AVenhance.Infra.Section3.qMNR_hasDerivAt I κ m n r t j k) hrec)

/-- The row-corrected material derivative commutes with divergence when the
velocity is divergence-free. This is the differential identity encoded by the recursion. -/
theorem stDiv_material_eq_stDiv_lieDerivative
    {F b : ST → Vec 2} {p : ST}
    (hF : ContDiffAt ℝ 2 F p) (hb : ContDiffAt ℝ 2 b p)
    (hdiv : ∀ q : ST, stDiv b q = 0) :
    fderiv ℝ (stDiv F) p (1, b p) = stDiv (stLieDerivative F b) p := by
  let DF : ST →L[ℝ] Vec 2 := fderiv ℝ F p
  let D2F : ST →L[ℝ] (ST →L[ℝ] Vec 2) := fderiv ℝ (fderiv ℝ F) p
  let D2b : ST →L[ℝ] (ST →L[ℝ] Vec 2) := fderiv ℝ (fderiv ℝ b) p
  let LV : ST →L[ℝ] ST := (0 : ST →L[ℝ] ℝ).prod (fderiv ℝ b p)
  let V : ST := (1, b p)
  have hdivFun : stDiv b = fun _ => 0 := by
    funext q
    exact hdiv q
  have hdivDeriv : AmnrMaterialStep.stDivDerivative b p = 0 := by
    have h₁ := stDiv_hasFDerivAt hb
    rw [hdivFun] at h₁
    have h₂ : HasFDerivAt (fun _ : ST => (0 : ℝ)) (0 : ST →L[ℝ] ℝ) p :=
      hasFDerivAt_const 0 p
    exact h₁.unique h₂
  have htrace (j : Fin 2) :
      ∑ i : Fin 2, (D2b.flip (0, basisVec i) (0, basisVec j)) i = 0 := by
    have h := congrArg (fun L : ST →L[ℝ] ℝ => L (0, basisVec j)) hdivDeriv
    simpa [AmnrMaterialStep.stDivDerivative, D2b, Fin.sum_univ_two,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using h
  have hsymmB := hb.isSymmSndFDerivAt (by norm_num)
  have htraceCorr (j : Fin 2) :
      ∑ i : Fin 2, (D2b.flip (0, basisVec j) (0, basisVec i)) i = 0 := by
    calc
      (∑ i : Fin 2, (D2b.flip (0, basisVec j) (0, basisVec i)) i) =
          ∑ i : Fin 2, (D2b.flip (0, basisVec i) (0, basisVec j)) i := by
        apply Finset.sum_congr rfl
        intro i hi
        have h := hsymmB (0, basisVec j) (0, basisVec i)
        simpa [D2b] using (congrArg (fun w : Vec 2 => w i) h).symm
      _ = 0 := htrace j
  have hsymmF := hF.isSymmSndFDerivAt (by norm_num)
  have hessF (i : Fin 2) :
      D2F.flip (0, basisVec i) V = D2F.flip V (0, basisVec i) := by
    simpa [D2F, V] using hsymmF V (0, basisVec i)
  have hspaceDecomp (w : Vec 2) :
      (0, w) = ∑ j : Fin 2, w j • ((0 : ℝ), basisVec j) := by
    apply Prod.ext
    · simp
    · funext j
      fin_cases j <;> simp [Fin.sum_univ_two, basisVec]
  have hfirst (i : Fin 2) :
      (DF.comp LV) (0, basisVec i) i =
        ∑ j : Fin 2,
          (fderiv ℝ b p (0, basisVec i) j) *
            (fderiv ℝ F p (0, basisVec j)) i := by
    have hd := hspaceDecomp (fderiv ℝ b p (0, basisVec i))
    have he : DF (0, fderiv ℝ b p (0, basisVec i)) =
        ∑ j : Fin 2,
          (fderiv ℝ b p (0, basisVec i) j) • DF (0, basisVec j) := by
      rw [hd]
      simp only [map_sum, map_smul]
    have he' := congrArg (fun w : Vec 2 => w i) he
    simpa [DF, LV, ContinuousLinearMap.comp_apply, Fin.sum_univ_two,
      smul_eq_mul] using he'
  have hcross :
      (∑ i : Fin 2, ∑ j : Fin 2,
          (fderiv ℝ b p (0, basisVec i) j) *
            (fderiv ℝ F p (0, basisVec j)) i) =
        ∑ i : Fin 2, ∑ j : Fin 2,
          (fderiv ℝ b p (0, basisVec j) i) *
            (fderiv ℝ F p (0, basisVec i)) j := by
    simp only [Fin.sum_univ_two]
    ring
  have hcrossZero :
      (∑ i : Fin 2, (DF.comp LV) (0, basisVec i) i) -
        ∑ i : Fin 2, AmnrMaterialStep.stCorrectionDerivative F b p (0, basisVec i) i = 0 := by
    have hfirstSum :
        (∑ i : Fin 2, (DF.comp LV) (0, basisVec i) i) =
          ∑ i : Fin 2, ∑ j : Fin 2,
            (fderiv ℝ b p (0, basisVec i) j) *
              (fderiv ℝ F p (0, basisVec j)) i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hfirst i
    have hCorrFormula (i : Fin 2) :
        AmnrMaterialStep.stCorrectionDerivative F b p (0, basisVec i) i =
          (∑ j : Fin 2,
              (fderiv ℝ b p (0, basisVec j) i) *
                (fderiv ℝ F p (0, basisVec i)) j) +
            ∑ j : Fin 2,
              (D2b.flip (0, basisVec j) (0, basisVec i)) i * F p j := by
      simp [AmnrMaterialStep.stCorrectionDerivative, Fin.sum_univ_two,
        ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.proj_apply, D2b]
      ring
    have hCorrSum :
        (∑ i : Fin 2, AmnrMaterialStep.stCorrectionDerivative F b p (0, basisVec i) i) =
          (∑ i : Fin 2, ∑ j : Fin 2,
            (fderiv ℝ b p (0, basisVec j) i) *
              (fderiv ℝ F p (0, basisVec i)) j) +
            ∑ j : Fin 2,
              (∑ i : Fin 2,
                (D2b.flip (0, basisVec j) (0, basisVec i)) i) * F p j := by
      simp_rw [hCorrFormula]
      simp only [Fin.sum_univ_two]
      ring
    have ht0 := htraceCorr 0
    have ht1 := htraceCorr 1
    have hcrossExpanded := hcross
    simp only [Fin.sum_univ_two] at hcrossExpanded
    simp only [Fin.sum_univ_two] at ht0 ht1
    rw [hfirstSum, hCorrSum]
    simp only [Fin.sum_univ_two]
    rw [ht0, ht1]
    rw [hcrossExpanded]
    ring
  have hmain :
      AmnrMaterialStep.stDivDerivative F p V = stDiv (stLieDerivative F b) p := by
    have hlie := AmnrMaterialStep.stLieDerivative_hasFDerivAt hF hb
    have hleft :
        AmnrMaterialStep.stDivDerivative F p V =
          ∑ i : Fin 2, (D2F.flip (0, basisVec i) V) i := by
      simp [AmnrMaterialStep.stDivDerivative, D2F, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.proj_apply]
    have hright :
        stDiv (stLieDerivative F b) p =
          (∑ i : Fin 2, (DF.comp LV) (0, basisVec i) i) +
            (∑ i : Fin 2, (D2F.flip V) (0, basisVec i) i) -
              (∑ i : Fin 2, AmnrMaterialStep.stCorrectionDerivative F b p
                (0, basisVec i) i) := by
      unfold stDiv
      rw [hlie.fderiv]
      simp only [add_apply, sub_apply, ContinuousLinearMap.comp_apply,
        Pi.add_apply, Pi.sub_apply]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have hessSum :
        (∑ i : Fin 2, (D2F.flip (0, basisVec i) V) i) =
          (∑ i : Fin 2, (D2F.flip V) (0, basisVec i) i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact congrArg (fun w : Vec 2 => w i) (hessF i)
    have hcancel :
        (∑ i : Fin 2, (DF.comp LV) (0, basisVec i) i) =
          (∑ i : Fin 2, AmnrMaterialStep.stCorrectionDerivative F b p
            (0, basisVec i) i) :=
      sub_eq_zero.mp hcrossZero
    rw [hleft, hright]
    calc
      (∑ i : Fin 2, (D2F.flip (0, basisVec i) V) i) =
          (∑ i : Fin 2, (D2F.flip V) (0, basisVec i) i) := hessSum
      _ = (∑ i : Fin 2, (DF.comp LV) (0, basisVec i) i) +
            (∑ i : Fin 2, (D2F.flip V) (0, basisVec i) i) -
              (∑ i : Fin 2, AmnrMaterialStep.stCorrectionDerivative F b p
                (0, basisVec i) i) := by
          rw [hcancel]
          ring
  rw [stDiv_hasFDerivAt hF |>.fderiv]
  exact hmain

end AVenhance.Infra.Section5

end
