/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.AxisHolomorphic
public import LeanPool.NavierStokesAndEuler.NavierStokes.CauchyRestriction
public import LeanPool.NavierStokesAndEuler.NavierStokes.CompactSmoothFamily
import LeanPool.NavierStokesAndEuler.NavierStokes.HolomorphicFamily

/-!
# Joint smoothness of the actual holomorphic axis profile

The uniform bounds for the next radial derivative imply continuity in the
supremum norm on every closed parameter disk. A uniform mean-value remainder
then identifies the actual derivative of the disk-valued curve. Iterating this
argument and using the fixed-contour holomorphic-family theorem proves joint
real smoothness of the constructed extension.
-/

@[expose] public section


noncomputable section

open Set Metric Filter Asymptotics
open scoped Topology ContDiff
open NavierStokes.AxisCoefficientSpace NavierStokes.AxisEvaluation
open NavierStokes.AxisHolomorphic NavierStokes.CauchyRestriction

namespace NavierStokes.AxisHolomorphicJoint

/-- A continuous derivative in the supremum norm and the actual coordinate
derivatives give the actual derivative of a compact-family curve. -/
theorem hasDerivAt_compactFamily {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set ℝ} (hS : IsOpen S) (V V' : ℝ → C(K, E))
    (hc : ContinuousOn V' S)
    (hd : ∀ y ∈ S, ∀ z : K, HasDerivAt (fun q => V q z) (V' y z) y)
    {y : ℝ} (hy : y ∈ S) : HasDerivAt V (V' y) y := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  apply isLittleO_iff.mpr
  intro ε hε
  have hsmall : ∀ᶠ q in 𝓝 y, ‖V' q - V' y‖ < ε := by
    simpa only [dist_eq_norm] using
      (Metric.tendsto_nhds.mp (hc.continuousAt (hS.mem_nhds hy)) ε hε)
  have hin : ∀ᶠ q in 𝓝 y, q ∈ S := hS.mem_nhds hy
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp (hin.and hsmall)
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with v hv
  have hyv : y + v ∈ ball y δ := by
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hv
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg v))).mpr
  intro z
  simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply]
  have hder : ∀ q ∈ ball y δ,
      HasDerivWithinAt (fun q => V q z - q • V' y z)
        (V' q z - V' y z) (ball y δ) q := by
    intro q hq
    simpa only [one_smul, id_eq] using
      ((hd q (hnear hq).1 z).fun_sub ((hasDerivAt_id q).smul_const (V' y z))).hasDerivWithinAt
  have hbound : ∀ q ∈ ball y δ, ‖V' q z - V' y z‖ ≤ ε := by
    intro q hq
    exact ((V' q - V' y).norm_coe_le_norm z).trans (hnear hq).2.le
  have hmean := (convex_ball y δ).norm_image_sub_le_of_norm_hasDerivWithin_le
    hder hbound (mem_ball_self hδ) hyv
  have heq : V (y + v) z - V y z - v • V' y z =
      (V (y + v) z - (y + v) • V' y z) - (V y z - y • V' y z) := by
    rw [add_smul]
    abel
  rw [heq]
  simpa only [add_sub_cancel_left] using hmean

/-- The actual holomorphic profile restricted to a closed parameter disk.
The zero fallback in `family` is used only outside the proved radial domain. -/
noncomputable def diskProfile (I : Window) (ε : ℝ) (A : AxisSpace I ε)
    (c : ℂ) (σ : ℝ) (k : ℕ) : ℝ → C(Disk c σ, ℂ) :=
  CompactSmoothFamily.family (closedBall c σ)
    (fun p : ℝ × ℂ => complexProfile I ε A k p.1 p.2)

theorem diskProfile_apply (I : Window) {ε R s : ℝ} (hε : 0 < ε)
    (hR : 1 ≤ R) (hs : R / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε)
    (c : ℂ) (σ : ℝ) (hK : closedBall c σ ⊆ parameterStrip I (ε * (1 - s)))
    (k : ℕ) {Y : ℝ} (hY : |Y| ≤ R) (z : Disk c σ) :
    diskProfile I ε A c σ k Y z = complexProfile I ε A k Y z := by
  apply CompactSmoothFamily.family_apply
  exact (complexProfile_analytic I hε hR hs hs1 A k hY).continuousOn.comp_continuous
    continuous_subtype_val (fun z => hK z.2)

/-- The next radial derivative controls a whole disk in the supremum norm. -/
theorem diskProfile_norm_sub_le (I : Window) {ε R s : ℝ} (hε : 0 < ε)
    (hR : 1 ≤ R) (hs : R / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε)
    (c : ℂ) (σ : ℝ) (hK : closedBall c σ ⊆ parameterStrip I (ε * (1 - s)))
    (k : ℕ) {Y Y' : ℝ} (hY : |Y| < R) (hY' : |Y'| < R) :
    ‖diskProfile I ε A c σ k Y' - diskProfile I ε A c σ k Y‖ ≤
      ((2 * jetConstant R s (k + 1)) * ‖A‖) * ‖Y' - Y‖ := by
  have hB : 0 ≤ (2 * jetConstant R s (k + 1)) * ‖A‖ :=
    mul_nonneg (mul_nonneg (by norm_num) (jetConstant_nonneg hR hs hs1 _)) (norm_nonneg A)
  apply (ContinuousMap.norm_le _ (mul_nonneg hB (norm_nonneg (Y' - Y)))).mpr
  intro z
  simp only [ContinuousMap.sub_apply,
    diskProfile_apply I hε hR hs hs1 A c σ hK k hY.le z,
    diskProfile_apply I hε hR hs hs1 A c σ hK k hY'.le z]
  apply (convex_Ioo (-R) R).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f' := fun y => complexProfile I ε A (k + 1) y z)
    (fun y hy => (complexProfile_hasDerivAt_Y I hε hR hs hs1 A k
      (abs_lt.mpr hy) (hK z.2)).hasDerivWithinAt)
    (fun y hy => complexProfile_bound I hε hR hs hs1 A (k + 1)
      (abs_lt.mpr hy).le (hK z.2).2.le)
    (abs_lt.mp hY) (abs_lt.mp hY')

theorem diskProfile_continuousOn (I : Window) {ε R s : ℝ} (hε : 0 < ε)
    (hR : 1 ≤ R) (hs : R / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε)
    (c : ℂ) (σ : ℝ) (hK : closedBall c σ ⊆ parameterStrip I (ε * (1 - s)))
    (k : ℕ) : ContinuousOn (diskProfile I ε A c σ k) (Ioo (-R) R) := by
  let B : NNReal := ⟨(2 * jetConstant R s (k + 1)) * ‖A‖,
    mul_nonneg (mul_nonneg (by norm_num) (jetConstant_nonneg hR hs hs1 _)) (norm_nonneg A)⟩
  have hLip : LipschitzOnWith B (diskProfile I ε A c σ k) (Ioo (-R) R) := by
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro Y hY Y' hY'
    exact diskProfile_norm_sub_le I hε hR hs hs1 A c σ hK k
      (abs_lt.mpr hY') (abs_lt.mpr hY)
  exact hLip.continuousOn

/-- The derivative in the disk supremum norm is the already constructed
next radial derivative, with no regularity assumption on the output family. -/
theorem diskProfile_hasDerivAt (I : Window) {ε R s : ℝ} (hε : 0 < ε)
    (hR : 1 ≤ R) (hs : R / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε)
    (c : ℂ) (σ : ℝ) (hK : closedBall c σ ⊆ parameterStrip I (ε * (1 - s)))
    (k : ℕ) {Y : ℝ} (hY : |Y| < R) :
    HasDerivAt (diskProfile I ε A c σ k) (diskProfile I ε A c σ (k + 1) Y) Y := by
  apply hasDerivAt_compactFamily isOpen_Ioo _ _
    (diskProfile_continuousOn I hε hR hs hs1 A c σ hK (k + 1)) _ (abs_lt.mp hY)
  intro y hy z
  have hy' : |y| < R := abs_lt.mpr hy
  rw [diskProfile_apply I hε hR hs hs1 A c σ hK (k + 1) hy'.le z]
  apply (complexProfile_hasDerivAt_Y I hε hR hs hs1 A k hy' (hK z.2)).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hy] with q hq
  exact diskProfile_apply I hε hR hs hs1 A c σ hK k (abs_lt.mpr hq).le z

theorem diskProfile_contDiffOn_nat (I : Window) {ε R s : ℝ} (hε : 0 < ε)
    (hR : 1 ≤ R) (hs : R / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε)
    (c : ℂ) (σ : ℝ) (hK : closedBall c σ ⊆ parameterStrip I (ε * (1 - s)))
    (n : ℕ) : ∀ k : ℕ, ContDiffOn ℝ n (diskProfile I ε A c σ k) (Ioo (-R) R) := by
  induction n with
  | zero =>
    intro k
    exact contDiffOn_zero.mpr (diskProfile_continuousOn I hε hR hs hs1 A c σ hK k)
  | succ n ih =>
    intro k
    have hd (y : ℝ) (hy : y ∈ Ioo (-R) R) :=
      diskProfile_hasDerivAt I hε hR hs hs1 A c σ hK k (abs_lt.mpr hy)
    have hout : ContDiffOn ℝ ((n : WithTop ℕ∞) + 1)
        (diskProfile I ε A c σ k) (Ioo (-R) R) := by
      apply (contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo).mpr
      refine ⟨fun y hy => (hd y hy).differentiableAt.differentiableWithinAt, ?_, ?_⟩
      · simp
      · exact (ih (k + 1)).congr (fun y hy => (hd y hy).deriv)
    simpa only [Nat.cast_add, Nat.cast_one] using hout

theorem diskProfile_contDiffOn (I : Window) {ε R s : ℝ} (hε : 0 < ε)
    (hR : 1 ≤ R) (hs : R / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε)
    (c : ℂ) (σ : ℝ) (hK : closedBall c σ ⊆ parameterStrip I (ε * (1 - s)))
    (k : ℕ) : ContDiffOn ℝ ∞ (diskProfile I ε A c σ k) (Ioo (-R) R) := by
  apply contDiffOn_infty.mpr
  intro n
  exact diskProfile_contDiffOn_nat I hε hR hs hs1 A c σ hK n k

/-- Genuine joint real smoothness of every radial jet of the holomorphic axis
profile on the same radial interval and the same parameter strip. -/
theorem complexProfile_joint_smooth (I : Window) {ε R s : ℝ} (hε : 0 < ε)
    (hR : 1 ≤ R) (hs : R / 20 < s) (hs1 : s < 1) (A : AxisSpace I ε) (k : ℕ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => complexProfile I ε A k p.1 p.2)
      (Ioo (-R) R ×ˢ parameterStrip I (ε * (1 - s))) := by
  intro p hp
  obtain ⟨σ, hσ, hK⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((parameterStrip_isOpen I (ε * (1 - s))).mem_nhds hp.2)
  have hlocal := HolomorphicFamily.contDiffOn_of_disk_family p.2 hσ
    (diskProfile I ε A p.2 σ k) (complexProfile I ε A k)
    (diskProfile_contDiffOn I hε hR hs hs1 A p.2 σ hK k)
    (fun y hy => (complexProfile_analytic I hε hR hs hs1 A k (abs_lt.mpr
        hy).le).differentiableOn.mono
      (ball_subset_closedBall.trans hK))
    (fun y hy z => diskProfile_apply I hε hR hs hs1 A p.2 σ hK k (abs_lt.mpr hy).le z)
  exact (hlocal.contDiffAt ((isOpen_Ioo.prod isOpen_ball).mem_nhds
    ⟨hp.1, mem_ball_self hσ⟩)).contDiffWithinAt

/-- Every tube contained in the constructed strip inherits joint smoothness. -/
theorem complexProfile_joint_smooth_tube (I J : Window) {ε R s δ : ℝ}
    (hε : 0 < ε) (hR : 1 ≤ R) (hs : R / 20 < s) (hs1 : s < 1)
    (htube : parameterTube J δ ⊆ parameterStrip I (ε * (1 - s)))
    (A : AxisSpace I ε) (k : ℕ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => complexProfile I ε A k p.1 p.2)
      (Ioo (-R) R ×ˢ parameterTube J δ) :=
  (complexProfile_joint_smooth I hε hR hs hs1 A k).mono
    (Set.prod_mono Subset.rfl htube)

/-- The jointly smooth extension is exactly the original real radial jet on
the real slice, rather than a separately selected continuation. -/
theorem complexProfile_joint_real_agreement (I : Window) (ε : ℝ)
    (A : AxisSpace I ε) (k : ℕ) (Y x : ℝ) :
    complexProfile I ε A k Y (x : ℂ) = (mixedSeries I ε A k 0 (Y, x) : ℂ) :=
  complexProfile_ofReal I ε A k Y x

theorem complexProfile_joint_zero_real_agreement (I : Window) (ε : ℝ)
    (A : AxisSpace I ε) (Y x : ℝ) :
    complexProfile I ε A 0 Y (x : ℂ) = (profile I ε A (Y, x) : ℂ) :=
  complexProfile_zero_ofReal I ε A Y x

/-- A common positive tube and a genuine open radial neighborhood work for
every coefficient vector and every radial derivative order. The extension is
jointly real smooth, holomorphic in the complex parameter, uniformly bounded,
and agrees with all actual real parameter jets. -/
theorem exists_common_joint_extension (I J : Window) (hleft : I.left < J.left)
    (hright : J.right < I.right) {ε R : ℝ} (hε : 0 < ε) (hR20 : R < 20) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ S : ℝ, R < S ∧ S < 20 ∧ ∃ B : ℕ → ℝ,
      (∀ k, 0 ≤ B k) ∧ ∀ (A : AxisSpace I ε) (k : ℕ),
        ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => complexProfile I ε A k p.1 p.2)
          (Ioo (-S) S ×ˢ parameterTube J δ) ∧
        ∀ Y : ℝ, |Y| ≤ R →
          AnalyticOnNhd ℂ (complexProfile I ε A k Y) (parameterTube J δ) ∧
          (∀ z ∈ parameterTube J δ, ‖complexProfile I ε A k Y z‖ ≤ B k * ‖A‖) ∧
          (∀ z ∈ parameterTube J δ,
            iteratedDeriv k (fun y => complexProfile I ε A 0 y z) Y =
              complexProfile I ε A k Y z) ∧
          (∀ (m : ℕ) (x : ℝ), x ∈ J.interval →
            iteratedDeriv m (complexProfile I ε A k Y) (x : ℂ) =
              (mixedSeries I ε A k m (Y, x) : ℂ)) := by
  obtain ⟨S, hS, hS20⟩ := exists_between (max_lt (by norm_num : (1 : ℝ) < 20) hR20)
  have hS1 : 1 ≤ S := (le_max_left 1 R).trans hS.le
  have hRS : R < S := (le_max_right 1 R).trans_lt hS
  obtain ⟨s, hs, hs1⟩ := exists_between (show S / 20 < 1 by linarith)
  have ha : 0 < ε * (1 - s) := mul_pos hε (by linarith)
  obtain ⟨δ, hδ, htube⟩ := exists_parameterTube_subset I J hleft hright ha
  refine ⟨δ, hδ, S, hRS, hS20, (fun k => 2 * jetConstant S s k), ?_, ?_⟩
  · intro k
    exact mul_nonneg (by norm_num) (jetConstant_nonneg hS1 hs hs1 k)
  · intro A k
    refine ⟨complexProfile_joint_smooth_tube I J hε hS1 hs hs1 htube A k, ?_⟩
    intro Y hY
    have hYS : |Y| < S := hY.trans_lt hRS
    refine ⟨(complexProfile_analytic I hε hS1 hs hs1 A k hYS.le).mono htube, ?_, ?_, ?_⟩
    · intro z hz
      exact complexProfile_bound I hε hS1 hs hs1 A k hYS.le (htube hz).2.le
    · intro z hz
      simpa only [Nat.zero_add] using
        complexProfile_iteratedDeriv_Y I hε hS1 hs hs1 A 0 k hYS (htube hz)
    · intro m x hx
      exact complexProfile_iteratedDeriv_ofReal I hε hS1 hs hs1 A k m hYS.le
        ⟨hleft.trans_le hx.1, hx.2.trans_lt hright⟩

end NavierStokes.AxisHolomorphicJoint
