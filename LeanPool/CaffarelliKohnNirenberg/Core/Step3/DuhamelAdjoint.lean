/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalEquationRepresentation
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.BackwardPotentialKernelBridge
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.SpaceTime

/-!
# Duhamel Adjoint

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric


noncomputable section

namespace CKN.Core.Step3

open CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Core.HeatPotential

theorem canonical_spaceTime_cutoff_box {r R t₀ : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) :
    let χ : Vec3 × ℝ → ℝ := CKN.spaceTimeCutoff (0 : Vec3) t₀ r R
    χ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ ∧
      (∀ z : Vec3 × ℝ, z.1 ∈ euclideanBall (0 : Vec3) r →
        z.2 ∈ Icc (t₀ - r ^ 2) t₀ → χ z = 1) := by
  dsimp
  let χ : Vec3 × ℝ → ℝ := CKN.spaceTimeCutoff (0 : Vec3) t₀ r R
  have hχdiff : ContDiff ℝ (⊤ : ℕ∞) χ := by
    exact spaceTimeCutoff_smooth (0 : Vec3) t₀ r R hr hrR
  have hχcompact : HasCompactSupport χ := by
    apply HasCompactSupport.intro
      (show IsCompact (euclideanClosedBall (0 : Vec3) R ×ˢ
        Icc (t₀ - R ^ 2) (t₀ + (R ^ 2 - r ^ 2))) from
          (isCompact_euclideanClosedBall (0 : Vec3) (R := R)
            (lt_of_le_of_lt hr hrR).le).prod isCompact_Icc)
    intro z hz
    by_contra hne
    have hsupp : z ∈ Function.support χ := hne
    have hout := spaceTimeCutoff_support_subset
      (x₀ := (0 : Vec3)) (t₀ := t₀) (r := r) (R := R) hr hrR hsupp
    by_cases hzx : z.1 ∈ euclideanClosedBall (0 : Vec3) R
    · by_cases hzt : z.2 ∈ Icc (t₀ - R ^ 2) (t₀ + (R ^ 2 - r ^ 2))
      · exact hz ⟨hzx, hzt⟩
      · exact hzt ⟨le_of_lt hout.2.1, le_of_lt hout.2.2⟩
    · apply hzx
      change euclideanSqDist z.1 0 ≤ R ^ 2
      exact le_of_lt hout.1
  have hχsupport : tsupport χ ⊆ spaceTimeSet Set.univ Set.univ := by
    simp [spaceTimeSet]
  refine ⟨⟨hχdiff, hχcompact, hχsupport⟩, ?_⟩
  intro z hzx hzt
  exact spaceTimeCutoff_eq_one_on hr hrR hzx hzt

private lemma canonical_cutoff_potential_agreement
    {ζ : Vec3 × ℝ → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) {χ : Vec3 × ℝ → ℝ}
    (hχ : χ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ)
    {r t₀ : ℝ}
    (hχone : ∀ z : Vec3 × ℝ, z.1 ∈ euclideanBall (0 : Vec3) r →
      z.2 ∈ Icc (t₀ - r ^ 2) t₀ → χ z = 1)
    {z : Vec3 × ℝ}
    (hzx : z.1 ∈ euclideanBall (0 : Vec3) r)
    (hzt : z.2 ∈ Ioo (t₀ - r ^ 2) t₀) :
    χ z = 1 ∧
      timePartial (fun w => χ w * backwardTestPotential ζ w) z =
        timePartial (fun w => backwardTestPotential ζ w) z ∧
      (∀ j : Fin 3,
        spatialSecondPartial
            (fun w => χ w * backwardTestPotential ζ w) j j z =
          spatialSecondPartial (fun w => backwardTestPotential ζ w) j j z) ∧
      (∀ j : Fin 3,
        spatialPartial (fun w => χ w * backwardTestPotential ζ w) j z =
          spatialPartial (fun w => backwardTestPotential ζ w) j z) := by
  let B : Vec3 × ℝ → ℝ := fun w => backwardTestPotential ζ w
  let P : Vec3 × ℝ → ℝ := fun w => χ w * B w
  have hBdiff : ContDiff ℝ (⊤ : ℕ∞) B := by
    exact backwardTestPotential_smooth hζ hζc
  have hPdiff : ContDiff ℝ (⊤ : ℕ∞) P := by
    dsimp [P]
    exact hχ.1.mul hBdiff
  have hopenx : IsOpen (euclideanBall (0 : Vec3) r) := by
    change IsOpen {x : Vec3 | euclideanSqDist x 0 < r ^ 2}
    exact isOpen_lt (contDiff_euclideanSqDist_left (0 : Vec3)).continuous
      continuous_const
  have hopen : IsOpen (euclideanBall (0 : Vec3) r ×ˢ Ioo (t₀ - r ^ 2) t₀) :=
    hopenx.prod isOpen_Ioo
  have hzU : z ∈ euclideanBall (0 : Vec3) r ×ˢ Ioo (t₀ - r ^ 2) t₀ :=
    ⟨hzx, hzt⟩
  have hplateau : ∀ {w : Vec3 × ℝ},
      w ∈ euclideanBall (0 : Vec3) r ×ˢ Ioo (t₀ - r ^ 2) t₀ →
      (fun q => χ q) =ᶠ[𝓝 w] (fun _ => 1) := by
    intro w hw
    filter_upwards [hopen.mem_nhds hw] with q hq
    exact hχone q hq.1 ⟨hq.2.1.le, hq.2.2.le⟩
  have hPeq : (fun q => P q) =ᶠ[𝓝 z] (fun q => B q) := by
    filter_upwards [hplateau hzU] with q hq
    simp [P, B, hq]
  have hvalue : χ z = 1 := hχone z hzx ⟨hzt.1.le, hzt.2.le⟩
  have htime : timePartial P z = timePartial B z := by
    rw [timePartial_eq_fderiv_apply hPdiff z.1 z.2,
      timePartial_eq_fderiv_apply hBdiff z.1 z.2]
    exact congrArg (fun L : (Vec3 × ℝ) →L[ℝ] ℝ => L (0, 1)) hPeq.fderiv_eq
  have hspatial : ∀ j : Fin 3, spatialPartial P j z = spatialPartial B j z := by
    intro j
    rw [spatialPartial_eq_fderiv_apply hPdiff j z.1 z.2,
      spatialPartial_eq_fderiv_apply hBdiff j z.1 z.2]
    exact congrArg (fun L : (Vec3 × ℝ) →L[ℝ] ℝ =>
      L (basisVec j, 0)) hPeq.fderiv_eq
  have hfirst : ∀ j : Fin 3,
      (fun x : Vec3 => spatialPartial P j (x, z.2)) =ᶠ[𝓝 z.1]
        (fun x : Vec3 => spatialPartial B j (x, z.2)) := by
    intro j
    filter_upwards [hopenx.mem_nhds hzx] with x hx
    have hxU : (x, z.2) ∈
        euclideanBall (0 : Vec3) r ×ˢ Ioo (t₀ - r ^ 2) t₀ :=
      ⟨hx, hzt⟩
    have hPx : (fun q => P q) =ᶠ[𝓝 (x, z.2)] (fun q => B q) :=
      hplateau hxU |>.mono fun q hq => by simp [P, B, hq]
    rw [spatialPartial_eq_fderiv_apply hPdiff j x z.2,
      spatialPartial_eq_fderiv_apply hBdiff j x z.2]
    exact congrArg (fun L : (Vec3 × ℝ) →L[ℝ] ℝ =>
      L (basisVec j, 0)) hPx.fderiv_eq
  have hsecond : ∀ j : Fin 3,
      spatialSecondPartial P j j z = spatialSecondPartial B j j z := by
    intro j
    unfold spatialSecondPartial
    change (fderiv ℝ (fun x : Vec3 => spatialPartial P j (x, z.2)) z.1)
        (basisVec j) =
      (fderiv ℝ (fun x : Vec3 => spatialPartial B j (x, z.2)) z.1)
        (basisVec j)
    exact congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec j))
      (hfirst j).fderiv_eq
  refine ⟨hvalue, ?_, ?_, ?_⟩
  · exact htime
  · exact hsecond
  · exact hspatial

/-! The causal heat potential with a divergence-form source. -/

/-- Vector Duhamel potential with the sign convention for the localized divergence equation. -/
@[expose]
def duhamelPotential (g : ParabolicPoint → Vec3)
    (h : Fin 3 → ParabolicPoint → Vec3) (z : ParabolicPoint) : Vec3 :=
  fun i =>
    (∫ v, heatPotentialKernel z v * g v i) -
      ∑ j, ∫ v, heatPotentialSpatialKernel j z v * h j v i

/-- Common interior cylinder containing the supports needed for the localized Duhamel argument. -/
structure DuhamelSupportData
    (v g : ParabolicPoint → Vec3)
    (h : Fin 3 → ParabolicPoint → Vec3) where
  /-- Inner radius on which the common Duhamel cutoff is one. -/
  r : ℝ
  /-- Outer radius containing the supports of all localized sources. -/
  R : ℝ
  /-- Reference time for the common Duhamel support cylinder. -/
  t₀ : ℝ
  hr : 0 ≤ r
  hrR : r < R
  v_support : ∀ i : Fin 3, ∀ z ∈ tsupport (fun w => v w i),
    z.1 ∈ euclideanBall (0 : Vec3) r ∧ z.2 ∈ Ioo (t₀ - r ^ 2) t₀
  g_support : ∀ i : Fin 3, ∀ z ∈ tsupport (fun w => g w i),
    z.1 ∈ euclideanBall (0 : Vec3) r ∧ z.2 ∈ Ioo (t₀ - r ^ 2) t₀
  h_support : ∀ j i : Fin 3, ∀ z ∈ tsupport (fun w => h j w i),
    z.1 ∈ euclideanBall (0 : Vec3) r ∧ z.2 ∈ Ioo (t₀ - r ^ 2) t₀

theorem duhamelPotential_pairing
    {ζ : ParabolicPoint → ℝ} {g : ParabolicPoint → Vec3}
    {h : Fin 3 → ParabolicPoint → Vec3} (i : Fin 3)
    (hFg : Integrable (fun q : ParabolicPoint × ParabolicPoint =>
      backwardHeatKernel q.1 q.2 * ζ q.1 * g q.2 i)
      ((volume : Measure ParabolicPoint).prod volume))
    (hFh : ∀ j : Fin 3, Integrable (fun q : ParabolicPoint × ParabolicPoint =>
      backwardHeatSpatialKernel j q.1 q.2 * ζ q.1 * h j q.2 i)
      ((volume : Measure ParabolicPoint).prod volume)) :
    ∫ z, ζ z * duhamelPotential g h z i =
      (∫ v, g v i * backwardHeatPotential ζ v) +
        ∑ j, (∫ v, h j v i * backwardHeatPotentialSpatial j ζ v) := by
  let _ : SFinite (volume : Measure ParabolicPoint) := by
    rw [Integration.volume_parabolicPoint_eq_prod]
    exact Measure.prod.instSFinite
  have hleftG : Integrable (fun z =>
      ζ z * (∫ v, backwardHeatKernel z v * g v i)) volume := by
    have hh := hFg.integral_prod_left
    apply hh.congr
    filter_upwards [] with z
    rw [show (∫ v, backwardHeatKernel z v * ζ z * g v i) =
        ∫ v, ζ z * (backwardHeatKernel z v * g v i) by
          apply integral_congr_ae
          filter_upwards [] with v
          ring, integral_const_mul]
  have hrightG : Integrable (fun v =>
      g v i * (∫ z, backwardHeatKernel z v * ζ z)) volume := by
    have hh := hFg.integral_prod_right
    apply hh.congr
    filter_upwards [] with v
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    ring
  have hleftH : ∀ j, Integrable (fun z =>
      ζ z * (∫ v, backwardHeatSpatialKernel j z v * h j v i)) volume := by
    intro j
    have hh := (hFh j).integral_prod_left
    apply hh.congr
    filter_upwards [] with z
    rw [show (∫ v, backwardHeatSpatialKernel j z v * ζ z * h j v i) =
        ∫ v, ζ z * (backwardHeatSpatialKernel j z v * h j v i) by
          apply integral_congr_ae
          filter_upwards [] with v
          ring, integral_const_mul]
  have hrightH : ∀ j, Integrable (fun v =>
      h j v i * (∫ z, backwardHeatSpatialKernel j z v * ζ z)) volume := by
    intro j
    have hh := (hFh j).integral_prod_right
    apply hh.congr
    filter_upwards [] with v
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    ring
  have hsumleft : Integrable (fun z =>
      ∑ j, ζ z * (∫ v, backwardHeatSpatialKernel j z v * h j v i)) volume :=
    integrable_finsetSum Finset.univ (fun j hj => hleftH j)
  unfold duhamelPotential
  change ∫ z, ζ z * ((∫ v, backwardHeatKernel z v * g v i) -
      ∑ j, ∫ v, backwardHeatSpatialKernel j z v * h j v i) = _
  have hrewrite : (fun z => ζ z * ((∫ v, backwardHeatKernel z v * g v i) -
      ∑ j, ∫ v, backwardHeatSpatialKernel j z v * h j v i)) =
      (fun z => ζ z * (∫ v, backwardHeatKernel z v * g v i) -
        ∑ j, ζ z * (∫ v, backwardHeatSpatialKernel j z v * h j v i)) := by
    funext z
    rw [mul_sub, Finset.mul_sum]
  rw [hrewrite, integral_sub hleftG hsumleft,
    integral_finsetSum Finset.univ (fun j hj => hleftH j)]
  have hg := backwardHeatPotential_pairing (f := fun v => g v i)
    (ζ := ζ) hFg
  have hh := fun j => backwardHeatPotential_spatial_pairing
    (i := j) (f := fun v => h j v i) (ζ := ζ) (hF := hFh j)
  have hleftG' : (∫ z, ζ z * (∫ v, backwardHeatKernel z v * g v i)) =
      ∫ v, g v i * backwardHeatPotential ζ v := by
    calc
      (∫ z, ζ z * (∫ v, backwardHeatKernel z v * g v i)) =
          ∫ z, (∫ v, backwardHeatKernel z v * g v i) * ζ z := by
        apply integral_congr_ae
        filter_upwards [] with z
        ring
      _ = ∫ v, g v i * backwardHeatPotential ζ v := hg.symm
  have hleftH' : ∀ j, (∫ z, ζ z * (∫ v,
      backwardHeatSpatialKernel j z v * h j v i)) =
      -∫ v, h j v i * backwardHeatPotentialSpatial j ζ v := by
    intro j
    calc
      (∫ z, ζ z * (∫ v, backwardHeatSpatialKernel j z v * h j v i)) =
          ∫ z, (∫ v, backwardHeatSpatialKernel j z v * h j v i) * ζ z := by
        apply integral_congr_ae
        filter_upwards [] with z
        ring
      _ = -∫ v, h j v i * backwardHeatPotentialSpatial j ζ v := by
        rw [hh j]
        ring
  rw [hleftG']
  rw [show (∑ j, ∫ z, ζ z * (∫ v,
      backwardHeatSpatialKernel j z v * h j v i)) =
      ∑ j, (-∫ v, h j v i * backwardHeatPotentialSpatial j ζ v) by
        apply Finset.sum_congr rfl
        intro j hj
        exact hleftH' j]
  rw [Finset.sum_neg_distrib]
  simp only [sub_neg_eq_add]

theorem duhamel_of_adjoint_identity
    {v g : ParabolicPoint → Vec3}
    {h : Fin 3 → ParabolicPoint → Vec3}
    (hv : ∀ i : Fin 3,
      LocallyIntegrable (fun z : Vec3 × ℝ => v z i)
        (volume : Measure (Vec3 × ℝ)))
    (hpotential : ∀ i : Fin 3,
      LocallyIntegrable (fun z : Vec3 × ℝ => duhamelPotential g h z i)
        (volume : Measure (Vec3 × ℝ)))
    (hadjoint : ∀ (ζ : Vec3 × ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) ζ →
      HasCompactSupport ζ → ∀ i : Fin 3,
        (∫ z : Vec3 × ℝ, ζ z * v z i) =
          ∫ z : Vec3 × ℝ, ζ z * duhamelPotential g h z i) :
    ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)),
      v z = duhamelPotential g h z := by
  have hcoord : ∀ i : Fin 3,
      ∀ᵐ z ∂volume, v z i = duhamelPotential g h z i := by
    intro i
    apply ae_eq_of_integral_contDiff_smul_eq (hv i) (hpotential i)
    intro ζ hζ hζc
    have h := hadjoint ζ hζ hζc i
    simpa only [smul_eq_mul] using h
  filter_upwards [hcoord 0, hcoord 1, hcoord 2] with z h0 h1 h2
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem duhamel_of_cutoff_localized_equation
    {v g : ParabolicPoint → Vec3}
    {h : Fin 3 → ParabolicPoint → Vec3}
    (hv : ∀ i : Fin 3,
      LocallyIntegrable (fun z : Vec3 × ℝ => v z i)
        (volume : Measure (Vec3 × ℝ)))
    (hpotential : ∀ i : Fin 3,
      LocallyIntegrable (fun z : Vec3 × ℝ => duhamelPotential g h z i)
        (volume : Measure (Vec3 × ℝ)))
    (hFg : ∀ (ζ : Vec3 × ℝ → ℝ)
        (_hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (_hζc : HasCompactSupport ζ)
        (i : Fin 3),
      Integrable
        (fun q : ParabolicPoint × ParabolicPoint =>
          backwardHeatKernel q.1 q.2 * ζ q.1 * g q.2 i)
        ((volume : Measure ParabolicPoint).prod volume))
    (hFh : ∀ (ζ : Vec3 × ℝ → ℝ)
        (_hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (_hζc : HasCompactSupport ζ)
        (j i : Fin 3),
      Integrable
        (fun q : ParabolicPoint × ParabolicPoint =>
          backwardHeatSpatialKernel j q.1 q.2 * ζ q.1 * h j q.2 i)
        ((volume : Measure ParabolicPoint).prod volume))
    (hweak : ∀ i : Fin 3, ∀ ψ : ParabolicPoint → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
      (∫ z, v z i *
          (-(timePartial ψ z) -
            ∑ j, spatialSecondPartial ψ j j z)) =
        (∫ z, g z i * ψ z) +
          ∑ j, ∫ z, h j z i * spatialPartial ψ j z)
    (hsupport : DuhamelSupportData v g h) :
    ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)),
      v z = duhamelPotential g h z := by
  have hadjoint : ∀ (ζ : Vec3 × ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) ζ →
      HasCompactSupport ζ → ∀ i : Fin 3,
        (∫ z : Vec3 × ℝ, ζ z * v z i) =
          ∫ z : Vec3 × ℝ, ζ z * duhamelPotential g h z i := by
    intro ζ hζ hζc i
    have hcut : ∃ χ : Vec3 × ℝ → ℝ,
        χ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ ∧
        (∀ i : Fin 3, ∀ z ∈ tsupport (fun w => v w i),
          χ z = 1 ∧
            timePartial (fun w => χ w * backwardTestPotential ζ w) z =
              timePartial (fun w => backwardTestPotential ζ w) z ∧
            ∀ j : Fin 3,
              spatialSecondPartial
                  (fun w => χ w * backwardTestPotential ζ w) j j z =
                spatialSecondPartial
                  (fun w => backwardTestPotential ζ w) j j z) ∧
        (∀ i : Fin 3, ∀ z ∈ tsupport (fun w => g w i), χ z = 1) ∧
        (∀ j i : Fin 3, ∀ z ∈ tsupport (fun w => h j w i),
          χ z = 1 ∧
            ∀ k : Fin 3,
              spatialPartial
                  (fun w => χ w * backwardTestPotential ζ w) k z =
                spatialPartial
                (fun w => backwardTestPotential ζ w) k z) := by
      let χ : Vec3 × ℝ → ℝ :=
        CKN.spaceTimeCutoff (0 : Vec3) hsupport.t₀ hsupport.r hsupport.R
      have hcanonical :
          χ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ ∧
            (∀ z : Vec3 × ℝ, z.1 ∈ euclideanBall (0 : Vec3) hsupport.r →
              z.2 ∈ Icc (hsupport.t₀ - hsupport.r ^ 2) hsupport.t₀ →
                χ z = 1) := by
        simpa [χ] using
          (canonical_spaceTime_cutoff_box hsupport.hr hsupport.hrR)
      rcases hcanonical with ⟨hχ, hχone⟩
      refine ⟨χ, hχ, ?_, ?_, ?_⟩
      · intro k z hz
        rcases hsupport.v_support k z hz with ⟨hzx, hzt⟩
        rcases canonical_cutoff_potential_agreement hζ hζc hχ hχone hzx hzt with
          ⟨hvalue, htime, hsecond, -⟩
        exact ⟨hvalue, htime, hsecond⟩
      · intro k z hz
        rcases hsupport.g_support k z hz with ⟨hzx, hzt⟩
        exact hχone z hzx ⟨hzt.1.le, hzt.2.le⟩
      · intro j k z hz
        rcases hsupport.h_support j k z hz with ⟨hzx, hzt⟩
        rcases canonical_cutoff_potential_agreement hζ hζc hχ hχone hzx hzt with
          ⟨hvalue, -, -, hspatial⟩
        exact ⟨hvalue, hspatial⟩
    rcases hcut with ⟨χ, hχ, hvχ, hgχ, hhχ⟩
    let P : Vec3 × ℝ → ℝ := fun z => χ z * backwardTestPotential ζ z
    have hχdiff : ContDiff ℝ (⊤ : ℕ∞) χ := hχ.1
    have hχcompact : HasCompactSupport χ := hχ.2.1
    have hPdiff : ContDiff ℝ (⊤ : ℕ∞) P := by
      dsimp [P]
      exact hχdiff.mul (backwardTestPotential_smooth hζ hζc)
    have hPcompact : HasCompactSupport P := by
      apply HasCompactSupport.intro hχcompact.isCompact
      intro z hz
      have hzχ : χ z = 0 := image_eq_zero_of_notMem_tsupport hz
      simp [P, hzχ]
    have hPtest : (show ParabolicPoint → ℝ from P) ∈
        spaceTimeTestFunction (V := ℝ) Set.univ Set.univ := by
      refine ⟨hPdiff, hPcompact, ?_⟩
      simp [spaceTimeSet]
    have htest := hweak i (show ParabolicPoint → ℝ from P) hPtest
    have hleft :
        (∫ z, v z i *
            (-(timePartial (show ParabolicPoint → ℝ from P) z) -
              ∑ j, spatialSecondPartial
                (show ParabolicPoint → ℝ from P) j j z)) =
          ∫ z, v z i *
            (-(timePartial (fun w => backwardTestPotential ζ w) z) -
              ∑ j, spatialSecondPartial
                (fun w => backwardTestPotential ζ w) j j z) := by
      change (∫ z, v z i *
          (-(timePartial (fun w => χ w * backwardTestPotential ζ w) z) -
            ∑ j, spatialSecondPartial
              (fun w => χ w * backwardTestPotential ζ w) j j z)) = _
      apply integral_congr_ae
      filter_upwards [] with z
      by_cases hz : z ∈ tsupport (fun w => v w i)
      · rcases hvχ i z hz with ⟨-, htime, hsecond⟩
        rw [htime]
        congr 2
        apply Finset.sum_congr rfl
        intro j hj
        exact hsecond j
      · have hzv : v z i = 0 :=
          image_eq_zero_of_notMem_tsupport (f := fun w => v w i) hz
        simp [hzv]
    have hright :
        (∫ z, g z i * P z) +
            ∑ j, ∫ z, h j z i * spatialPartial
              (show ParabolicPoint → ℝ from P) j z =
          (∫ z, g z i * backwardTestPotential ζ z) +
            ∑ j, ∫ z, h j z i *
              spatialPartial (fun w => backwardTestPotential ζ w) j z := by
      have hg : (∫ z, g z i * P z) =
          ∫ z, g z i * backwardTestPotential ζ z := by
        apply integral_congr_ae
        filter_upwards [] with z
        by_cases hz : z ∈ tsupport (fun w => g w i)
        · have hχz := hgχ i z hz
          simp [P, hχz]
        · have hzg : g z i = 0 :=
            image_eq_zero_of_notMem_tsupport (f := fun w => g w i) hz
          simp [hzg]
      rw [hg]
      apply congrArg (fun q => (∫ z, g z i * backwardTestPotential ζ z) + q)
      apply Finset.sum_congr rfl
      intro j hj
      apply integral_congr_ae
      filter_upwards [] with z
      by_cases hz : z ∈ tsupport (fun w => h j w i)
      · rcases hhχ j i z hz with ⟨hχz, hsp⟩
        change h j z i * spatialPartial
            (fun w => χ w * backwardTestPotential ζ w) j z =
          h j z i * spatialPartial
            (fun w => backwardTestPotential ζ w) j z
        exact congrArg (fun q => h j z i * q) (hsp j)
      · have hzh : h j z i = 0 :=
          image_eq_zero_of_notMem_tsupport (f := fun w => h j w i) hz
        simp [hzh]
    have hscalar := htest
    rw [hleft, hright] at hscalar
    have hvalue : (∫ z, ζ z * v z i) =
        (∫ z, g z i * backwardTestPotential ζ z) +
          ∑ j, ∫ z, h j z i *
            backwardHeatPotentialSpatial j
              (show ParabolicPoint → ℝ from ζ) z := by
      calc
        (∫ z, ζ z * v z i) =
            ∫ z, v z i *
              (-(timePartial (fun w => backwardTestPotential ζ w) z) -
                ∑ j, spatialSecondPartial
                  (fun w => backwardTestPotential ζ w) j j z) := by
          apply integral_congr_ae
          filter_upwards [] with z
          rw [backwardTestPotential_heat_equation hζ hζc]
          ring
        _ = (∫ z, g z i * backwardTestPotential ζ z) +
              ∑ j, ∫ z, h j z i *
                spatialPartial (fun w => backwardTestPotential ζ w) j z := hscalar
        _ = (∫ z, g z i * backwardTestPotential ζ z) +
              ∑ j, ∫ z, h j z i *
                backwardHeatPotentialSpatial j
                  (show ParabolicPoint → ℝ from ζ) z := by
          apply congrArg (fun q => (∫ z, g z i * backwardTestPotential ζ z) + q)
          apply Finset.sum_congr rfl
          intro j hj
          apply integral_congr_ae
          filter_upwards [] with z
          exact congrArg (fun q => h j z i * q)
            (backwardTestPotential_spatialPartial_eq_backwardHeatPotentialSpatial
              hζ hζc j z.1 z.2)
    have hpair := duhamelPotential_pairing (g := g) (h := h) i
      (hFg ζ hζ hζc i) (fun j => hFh ζ hζ hζc j i)
    have hforward :
        (∫ z, g z i * backwardTestPotential ζ z) +
            ∑ j, ∫ z, h j z i *
              backwardHeatPotentialSpatial j
                (show ParabolicPoint → ℝ from ζ) z =
          (∫ z, g z i * backwardHeatPotential
              (show ParabolicPoint → ℝ from ζ) z) +
            ∑ j, ∫ z, h j z i *
              backwardHeatPotentialSpatial j
                (show ParabolicPoint → ℝ from ζ) z := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with z
      exact congrArg (fun q => g z i * q)
        (backwardTestPotential_eq_backwardHeatPotential ζ
          (show Vec3 × ℝ from z))
    calc
      (∫ z, ζ z * v z i) =
          (∫ z, g z i * backwardTestPotential ζ z) +
            ∑ j, ∫ z, h j z i *
              backwardHeatPotentialSpatial j
                (show ParabolicPoint → ℝ from ζ) z := hvalue
      _ = (∫ z, g z i * backwardHeatPotential
              (show ParabolicPoint → ℝ from ζ) z) +
            ∑ j, ∫ z, h j z i *
              backwardHeatPotentialSpatial j
                (show ParabolicPoint → ℝ from ζ) z := hforward
      _ = ∫ z, ζ z * duhamelPotential g h z i := hpair.symm
  exact duhamel_of_adjoint_identity hv hpotential hadjoint

theorem duhamel_of_localized_velocity
    {φ : ParabolicPoint → ℝ} {u : ParabolicPoint → Vec3}
    {g : ParabolicPoint → Vec3} {h : Fin 3 → ParabolicPoint → Vec3}
    (hv : ∀ i : Fin 3,
      LocallyIntegrable (fun z : Vec3 × ℝ => localizedVelocity φ u z i)
        (volume : Measure (Vec3 × ℝ)))
    (hpotential : ∀ i : Fin 3,
      LocallyIntegrable (fun z : Vec3 × ℝ => duhamelPotential g h z i)
        (volume : Measure (Vec3 × ℝ)))
    (hFg : ∀ (ζ : Vec3 × ℝ → ℝ)
        (_hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (_hζc : HasCompactSupport ζ)
        (i : Fin 3),
      Integrable
        (fun q : ParabolicPoint × ParabolicPoint =>
          backwardHeatKernel q.1 q.2 * ζ q.1 * g q.2 i)
        ((volume : Measure ParabolicPoint).prod volume))
    (hFh : ∀ (ζ : Vec3 × ℝ → ℝ)
        (_hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (_hζc : HasCompactSupport ζ)
        (j i : Fin 3),
      Integrable
        (fun q : ParabolicPoint × ParabolicPoint =>
          backwardHeatSpatialKernel j q.1 q.2 * ζ q.1 * h j q.2 i)
        ((volume : Measure ParabolicPoint).prod volume))
    (hweak : ∀ i : Fin 3, ∀ ψ : ParabolicPoint → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) Set.univ Set.univ →
      (∫ z, localizedVelocity φ u z i *
          (-(timePartial ψ z) -
            ∑ j, spatialSecondPartial ψ j j z)) =
        (∫ z, g z i * ψ z) +
          ∑ j, ∫ z, h j z i * spatialPartial ψ j z)
    (hsupport : DuhamelSupportData (localizedVelocity φ u) g h) :
    ∀ᵐ z ∂(volume : Measure (Vec3 × ℝ)),
      localizedVelocity φ u z = duhamelPotential g h z := by
  simpa only [localizedVelocity] using
      (duhamel_of_cutoff_localized_equation
      (v := localizedVelocity φ u) (g := g) (h := h) hv hpotential
      hFg hFh hweak hsupport)

end CKN.Core.Step3
