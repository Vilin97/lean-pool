/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import LeanPool.Rado.Surface.Perron
import LeanPool.Rado.Complex.PlanarConnected

/-!
# The two-disk configuration and its barriers

Step 5 of `Rado/PLAN.md`: the fixed configuration in a chart whose target
contains `ball 0 8` — remove the preimages of the closed unit disks at `±4`
(`configY`), take the Perron family with boundary condition `≤ 0` on the disk
at `-4` (`configFamily`), and force nonconstancy of its upper envelope with
two explicit log-barriers on the annuli `1 ≤ |ζ ∓ 4| ≤ 2`: values `≥ 3/4`
resp. `≤ 1/4` at the witness points `±4 + 2^(1/4)`.
-/

open Set Topology Metric MeasureTheory InnerProductSpace Complex Filter

namespace Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## The two-disk configuration and its barriers

Fixed configuration in a chart `e` whose target contains `ball 0 8`: the
removed disks are the preimages of the closed unit disks at `±4`, the barriers
live on the annuli `1 ≤ |ζ ∓ 4| ≤ 2` (`Rado/Complex/PlanarConnected.lean`).
-/

section Config

variable (e : OpenPartialHomeomorph X ℂ)

/-- The surface `X` minus the two closed configuration disks. -/
def configY : Set X :=
  univ \ (e.symm '' closedBall (-4) 1 ∪ e.symm '' closedBall 4 1)

/-- The Perron family for the configuration: subharmonic on `configY`,
`[0,1]`-valued there, continuous up to the closure, and `≤ 0` on the boundary
circle of the disk at `-4`. -/
def configFamily : Set (X → ℝ) :=
  {g | SurfaceSubharmonicOn g (configY e) ∧ (∀ x ∈ closure (configY e), g x ∈ Icc (0 : ℝ) 1)
      ∧ ContinuousOn g (closure (configY e))
      ∧ ∀ x ∈ closure (configY e) ∩ e.symm '' closedBall (-4) 1, g x ≤ 0}

/-- Both configuration disks (in fact, both surrounding annuli) lie inside the
standard ball. -/
theorem closedBall_config_subset {c : ℂ} (hc : ‖c‖ = 4) {r : ℝ} (hr : r ≤ 2) :
    closedBall c r ⊆ ball (0 : ℂ) 8 := by
  intro z hz
  rw [mem_closedBall] at hz
  rw [mem_ball]
  calc dist z 0 ≤ dist z c + dist c 0 := dist_triangle z c 0
    _ ≤ r + 4 := add_le_add hz (le_of_eq (by rw [dist_zero_right, hc]))
    _ < 8 := by linarith

private theorem norm_two_cpow_quarter :
    ‖(2 : ℂ) ^ ((1 : ℂ) / 4)‖ = (2 : ℝ) ^ ((1 : ℝ) / 4) := by
  have h1 : ((1 : ℂ) / 4) = (((1 : ℝ) / 4 : ℝ) : ℂ) := by norm_num
  have h2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  rw [h1, h2, norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ) < 2), Complex.ofReal_re]

private theorem one_lt_two_rpow_quarter : 1 < (2 : ℝ) ^ ((1 : ℝ) / 4) :=
  (Real.one_lt_rpow_iff_of_pos (by norm_num)).mpr (Or.inl ⟨by norm_num, by norm_num⟩)

private theorem two_rpow_quarter_lt_two : (2 : ℝ) ^ ((1 : ℝ) / 4) < 2 := by
  nth_rewrite 2 [← Real.rpow_one 2]
  exact (Real.rpow_lt_rpow_left_iff (by norm_num)).mpr (by norm_num)

variable {e} (he : e ∈ riemannAtlas X) (hb : ball (0 : ℂ) 8 ⊆ e.target)

omit [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- A point of the big ball whose distance to a disk center exceeds the radius
does not land in the disk preimage. -/
private theorem notMem_image_of_dist_gt (hb : ball (0 : ℂ) 8 ⊆ e.target) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) 8) {c : ℂ} (hc : closedBall c 1 ⊆ ball (0 : ℂ) 8)
    (hdist : 1 < dist w c) : e.symm w ∉ e.symm '' closedBall c 1 := by
  rintro ⟨w', hw', heq⟩
  have h1 : w' ∈ e.target := hb (hc hw')
  have h2 : w ∈ e.target := hb hw
  have hww : w' = w := by
    have h3 := congrArg e heq
    rwa [e.right_inv h1, e.right_inv h2] at h3
  rw [hww] at hw'
  exact absurd (mem_closedBall.mp hw') (not_le.mpr hdist)

include he hb

omit he [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- `configY` is open. -/
theorem isOpen_configY [T2Space X] : IsOpen (configY e) := by
  have hb₁ : closedBall (-4 : ℂ) 1 ⊆ e.target :=
    (closedBall_config_subset (by simp) (by norm_num)).trans hb
  have hb₂ : closedBall (4 : ℂ) 1 ⊆ e.target :=
    (closedBall_config_subset (by simp) (by norm_num)).trans hb
  have hc₁ : IsCompact (e.symm '' closedBall (-4 : ℂ) 1) :=
    (isCompact_closedBall _ _).image_of_continuousOn
      (e.symm.continuousOn.mono (by simpa using hb₁))
  have hc₂ : IsCompact (e.symm '' closedBall (4 : ℂ) 1) :=
    (isCompact_closedBall _ _).image_of_continuousOn
      (e.symm.continuousOn.mono (by simpa using hb₂))
  have hcl : IsClosed (e.symm '' closedBall (-4 : ℂ) 1 ∪ e.symm '' closedBall (4 : ℂ) 1) :=
    hc₁.isClosed.union hc₂.isClosed
  rw [configY, ← Set.compl_eq_univ_sdiff]
  exact hcl.isOpen_compl

omit he [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- Both witness points lie in `configY`. -/
theorem witness_mem_configY :
    e.symm (4 + (2 : ℂ) ^ ((1 : ℂ) / 4)) ∈ configY e ∧
      e.symm (-4 + (2 : ℂ) ^ ((1 : ℂ) / 4)) ∈ configY e := by
  set t := (2 : ℂ) ^ ((1 : ℂ) / 4) with ht
  have hnorm : ‖t‖ = (2:ℝ) ^ ((1:ℝ)/4) := norm_two_cpow_quarter
  have h1 : 1 < ‖t‖ := by rw [hnorm]; exact one_lt_two_rpow_quarter
  have h2 : ‖t‖ < 2 := by rw [hnorm]; exact two_rpow_quarter_lt_two
  have h8 : ‖(8:ℂ)‖ = 8 := by simp
  have hb₁ : closedBall (-4 : ℂ) 1 ⊆ ball (0:ℂ) 8 :=
    closedBall_config_subset (by simp) (by norm_num)
  have hb₂ : closedBall (4 : ℂ) 1 ⊆ ball (0:ℂ) 8 :=
    closedBall_config_subset (by simp) (by norm_num)
  have hw₁ : (4 + t) ∈ ball (0:ℂ) 8 := by
    rw [mem_ball, dist_zero_right]
    have h4 : ‖(4:ℂ)‖ = 4 := by simp
    calc ‖4 + t‖ ≤ ‖(4:ℂ)‖ + ‖t‖ := norm_add_le _ _
      _ < 8 := by rw [h4]; linarith
  have hw₂ : (-4 + t) ∈ ball (0:ℂ) 8 := by
    rw [mem_ball, dist_zero_right]
    have h4 : ‖(-4:ℂ)‖ = 4 := by simp
    calc ‖-4 + t‖ ≤ ‖(-4:ℂ)‖ + ‖t‖ := norm_add_le _ _
      _ < 8 := by rw [h4]; linarith
  have hd₁ : 1 < dist (4 + t) 4 := by
    rw [dist_eq_norm, add_sub_cancel_left]; exact h1
  have hd₂ : 1 < dist (4 + t) (-4) := by
    rw [dist_eq_norm]
    have hrw : (4 + t) - (-4) = 8 + t := by ring
    rw [hrw]
    have hlow := norm_sub_norm_le (8:ℂ) (-t)
    rw [sub_neg_eq_add, norm_neg] at hlow
    linarith
  have hd₃ : 1 < dist (-4 + t) (-4) := by
    rw [dist_eq_norm]
    have hrw : (-4 + t) - (-4) = t := by ring
    rw [hrw]; exact h1
  have hd₄ : 1 < dist (-4 + t) 4 := by
    rw [dist_eq_norm]
    have hrw : (-4 + t) - 4 = t - 8 := by ring
    rw [hrw, norm_sub_rev]
    have hlow := norm_sub_norm_le (8:ℂ) t
    linarith
  constructor
  · refine ⟨mem_univ _, ?_⟩
    rintro (hmem | hmem)
    · exact notMem_image_of_dist_gt hb hw₁ hb₁ hd₂ hmem
    · exact notMem_image_of_dist_gt hb hw₁ hb₂ hd₁ hmem
  · refine ⟨mem_univ _, ?_⟩
    rintro (hmem | hmem)
    · exact notMem_image_of_dist_gt hb hw₂ hb₁ hd₃ hmem
    · exact notMem_image_of_dist_gt hb hw₂ hb₂ hd₄ hmem

omit he [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- `configY` is connected when `X` is (clopen argument through the chart,
using `isPathConnected_ball_diff_two_disks`). -/
theorem isConnected_configY [ConnectedSpace X] [T2Space X] : IsConnected (configY e) := by
  have hYo : IsOpen (configY e) := isOpen_configY hb
  -- the connected chart core `P`
  set P : Set X := e.symm '' (ball (0 : ℂ) 8 \ (closedBall (-4 : ℂ) 1 ∪ closedBall (4 : ℂ) 1))
    with hP_def
  have hsub8 : ball (0 : ℂ) 8 \ (closedBall (-4 : ℂ) 1 ∪ closedBall (4 : ℂ) 1) ⊆ e.target :=
    fun w hw ↦ hb hw.1
  have hPY : P ⊆ configY e := by
    rintro x ⟨w, hw, rfl⟩
    refine ⟨mem_univ _, ?_⟩
    rintro (hmem | hmem)
    · have hd : 1 < dist w (-4 : ℂ) := by
        by_contra hle
        push Not at hle
        exact hw.2 (Or.inl (mem_closedBall.mpr hle))
      exact notMem_image_of_dist_gt hb hw.1
        (closedBall_config_subset (by simp) (by norm_num)) hd hmem
    · have hd : 1 < dist w (4 : ℂ) := by
        by_contra hle
        push Not at hle
        exact hw.2 (Or.inr (mem_closedBall.mpr hle))
      exact notMem_image_of_dist_gt hb hw.1
        (closedBall_config_subset (by simp) (by norm_num)) hd hmem
  have hPconn : IsPreconnected P :=
    ((isPathConnected_ball_diff_two_disks.isConnected).image _
      (e.symm.continuousOn.mono (by simpa using hsub8))).isPreconnected
  have hPne : P.Nonempty := by
    refine ⟨e.symm 0, 0, ⟨mem_ball_self (by norm_num), ?_⟩, rfl⟩
    rintro (hmem | hmem)
    · rw [mem_closedBall] at hmem
      have h4 : dist (0 : ℂ) (-4) = 4 := by
        rw [dist_eq_norm, zero_sub, norm_neg]
        simp
      rw [h4] at hmem
      norm_num at hmem
    · rw [mem_closedBall] at hmem
      have h4 : dist (0 : ℂ) 4 = 4 := by
        rw [dist_eq_norm, zero_sub, norm_neg]
        simp
      rw [h4] at hmem
      norm_num at hmem
  refine ⟨⟨_, (witness_mem_configY hb).1⟩, ?_⟩
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hcov hdisj
  -- the key step, symmetric in `u` and `v`
  have key : ∀ u' v' : Set X, IsOpen u' → IsOpen v' → configY e ⊆ u' ∪ v' →
      configY e ∩ (u' ∩ v') = ∅ → P ⊆ u' → configY e ⊆ u' := by
    intro u' v' hu' hv' hcov' hdisj' hPu
    have hdisj'' : ∀ z, z ∈ configY e → z ∈ u' → z ∈ v' → False := fun z h1 h2 h3 ↦
      eq_empty_iff_forall_notMem.mp hdisj' z ⟨h1, h2, h3⟩
    -- `Y ∩ v'` is clopen in `X`
    have hTopen : IsOpen (configY e ∩ v') := hYo.inter hv'
    have hTclosed : IsClosed (configY e ∩ v') := by
      refine isClosed_of_closure_subset ?_
      intro z hz
      by_cases hzY : z ∈ configY e
      · rcases hcov' hzY with hzu | hzv
        · exfalso
          obtain ⟨y, hyu, hyT⟩ := mem_closure_iff.mp hz u' hu' hzu
          exact hdisj'' y hyT.1 hyu hyT.2
        · exact ⟨hzY, hzv⟩
      · -- limit points inside the removed disks are impossible: near them,
        -- `Y` is contained in `P ⊆ u'`
        exfalso
        have hzK : z ∈ e.symm '' closedBall (-4 : ℂ) 1 ∪ e.symm '' closedBall (4 : ℂ) 1 := by
          by_contra hcon
          exact hzY ⟨mem_univ _, hcon⟩
        have hzN : z ∈ e.symm '' ball (0 : ℂ) 8 := by
          rcases hzK with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
          · exact ⟨w, closedBall_config_subset (by simp) (by norm_num) hw, rfl⟩
          · exact ⟨w, closedBall_config_subset (by simp) (by norm_num) hw, rfl⟩
        have hNopen : IsOpen (e.symm '' ball (0 : ℂ) 8) :=
          e.symm.isOpen_image_of_subset_source isOpen_ball (by simpa using hb)
        have hNY : ∀ y ∈ e.symm '' ball (0 : ℂ) 8, y ∈ configY e → y ∈ P := by
          rintro y ⟨w, hw, rfl⟩ hyY
          refine ⟨w, ⟨hw, ?_⟩, rfl⟩
          rintro (hmem | hmem)
          · exact hyY.2 (Or.inl ⟨w, hmem, rfl⟩)
          · exact hyY.2 (Or.inr ⟨w, hmem, rfl⟩)
        obtain ⟨y, hyN, hyT⟩ := mem_closure_iff.mp hz _ hNopen hzN
        exact hdisj'' y hyT.1 (hPu (hNY y hyN hyT.1)) hyT.2
    rcases isClopen_iff.mp ⟨hTclosed, hTopen⟩ with hT0 | hT1
    · intro z hz
      rcases hcov' hz with hzu | hzv
      · exact hzu
      · exact absurd (show z ∈ configY e ∩ v' from ⟨hz, hzv⟩)
          (by rw [hT0]; exact notMem_empty z)
    · exfalso
      obtain ⟨p, hp⟩ := hPne
      have hpT : p ∈ configY e ∩ v' := by rw [hT1]; exact mem_univ p
      exact hdisj'' p (hPY hp) (hPu hp) hpT.2
  have hPuv : P ⊆ u ∪ v := hPY.trans hcov
  have hPdisj : P ∩ (u ∩ v) = ∅ :=
    eq_empty_iff_forall_notMem.mpr fun z hz ↦
      eq_empty_iff_forall_notMem.mp hdisj z ⟨hPY hz.1, hz.2⟩
  rcases isPreconnected_iff_subset_of_disjoint.mp hPconn u v hu hv hPuv hPdisj with hPu | hPv
  · exact Or.inl (key u v hu hv hcov hdisj hPu)
  · refine Or.inr (key v u hv hu ?_ ?_ hPv)
    · rwa [union_comm]
    · rwa [inter_comm v u]

omit he [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- The configuration family is a Perron family. -/
theorem isPerronFamily_configFamily [T2Space X] :
    IsPerronFamily (configFamily e) (configY e) := by
  have hYo : IsOpen (configY e) := isOpen_configY hb
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- nonempty: the zero function belongs to the family
    refine ⟨fun _ ↦ 0, ⟨continuousOn_const, fun e' _ ↦ SubMeanOn.const⟩, ?_, ?_, ?_⟩
    · exact fun x _ ↦ ⟨le_rfl, zero_le_one⟩
    · exact continuousOn_const
    · exact fun x _ ↦ le_rfl
  · exact fun g hg ↦ hg.1
  · exact fun g hg x hx ↦ hg.2.1 x (subset_closure hx)
  · -- closed under pairwise max
    rintro g₁ ⟨h₁sub, h₁icc, h₁cont, h₁bd⟩ g₂ ⟨h₂sub, h₂icc, h₂cont, h₂bd⟩
    refine ⟨h₁sub.max h₂sub, ?_, ContinuousOn.sup h₁cont h₂cont, ?_⟩
    · intro x hx
      exact ⟨le_trans (h₁icc x hx).1 (le_max_left _ _),
        max_le (h₁icc x hx).2 (h₂icc x hx).2⟩
    · intro x hx
      exact max_le (h₁bd x hx) (h₂bd x hx)
  · -- closed under harmonic replacement
    rintro g ⟨hgsub, hgicc, hgcont, hgbd⟩ e' c' r' hd
    have hDY : e'.symm '' closedBall c' r' ⊆ configY e := hd.preimage_subset
    have hDclosed : IsClosed (e'.symm '' closedBall c' r') := hd.compact_preimage.isClosed
    have hgsub' : SurfaceSubharmonicOn (surfaceReplace g e' c' r') (configY e) :=
      surfaceReplace_surfaceSubharmonicOn hYo hgsub hd
    have hicc' : ∀ x ∈ configY e, surfaceReplace g e' c' r' x ∈ Icc (0 : ℝ) 1 :=
      surfaceReplace_mem_Icc hgsub hd fun x hx ↦ hgicc x (subset_closure hx)
    refine ⟨hgsub', ?_, ?_, ?_⟩
    · -- values in `[0, 1]` on the closure
      intro x hx
      by_cases hxD : x ∈ e'.symm '' closedBall c' r'
      · exact hicc' x (hDY hxD)
      · rw [surfaceReplace_eqOn_compl hxD]
        exact hgicc x hx
    · -- continuity on the closure
      intro x hx
      by_cases hxY : x ∈ configY e
      · exact (hgsub'.continuousOn.continuousAt (hYo.mem_nhds hxY)).continuousWithinAt
      · have hxD : x ∉ e'.symm '' closedBall c' r' := fun hcon ↦ hxY (hDY hcon)
        have hev : surfaceReplace g e' c' r' =ᶠ[𝓝 x] g := by
          filter_upwards [hDclosed.isOpen_compl.mem_nhds hxD] with y hy
          exact surfaceReplace_eqOn_compl hy
        exact (hgcont x hx).congr_of_eventuallyEq
          (hev.filter_mono nhdsWithin_le_nhds) hev.self_of_nhds
    · -- boundary condition at the disk `K₀`
      intro x hx
      have hxY : x ∉ configY e := fun hcon ↦ hcon.2 (Or.inl hx.2)
      have hxD : x ∉ e'.symm '' closedBall c' r' := fun hcon ↦ hxY (hDY hcon)
      rw [surfaceReplace_eqOn_compl hxD]
      exact hgbd x hx

/-- The lower barrier: forced value `≥ 3/4` at the witness point near the disk
at `+4` (the function `max 0 (log(2/|ζ-4|)/log 2)` belongs to the family). -/
theorem perronSup_ge_witness [T2Space X] :
    3 / 4 ≤ perronSup (configFamily e) (e.symm (4 + (2 : ℂ) ^ ((1 : ℂ) / 4))) := by
  classical
  have hYo : IsOpen (configY e) := isOpen_configY hb
  -- the lower barrier
  set β : X → ℝ := fun x ↦
    if x ∈ e.source then Max.max 0 ((Real.log 2 - Real.log ‖e x - 4‖) / Real.log 2) else 0
    with hβ_def
  have hβ0 : ∀ x, x ∉ e.source → β x = 0 := fun x hx ↦ ite_eq_right hx
  have hβin : ∀ x ∈ e.source,
      β x = Max.max 0 ((Real.log 2 - Real.log ‖e x - 4‖) / Real.log 2) := fun x hx ↦ ite_eq_left hx
  have hβnn : ∀ x, 0 ≤ β x := by
    intro x
    by_cases hx : x ∈ e.source
    · rw [hβin x hx]; exact le_max_left _ _
    · rw [hβ0 x hx]
  -- points of `Y` in the chart keep distance `> 1` from the disk center `4`
  have hK₁ : ∀ y ∈ e.source, y ∈ configY e → 1 < ‖e y - 4‖ := by
    intro y hys hyY
    by_contra hle
    push Not at hle
    have h1 : e y ∈ closedBall (4 : ℂ) 1 := by rwa [mem_closedBall, dist_eq_norm]
    exact hyY.2 (Or.inr ⟨e y, h1, e.left_inv hys⟩)
  -- ... and distance `≥ 1` on the closure of `Y`
  have hnorm1 : ∀ x ∈ closure (configY e), x ∈ e.source → 1 ≤ ‖e x - 4‖ := by
    intro x hx hxe
    have hcl : x ∈ closure (e.source ∩ configY e) :=
      e.open_source.inter_closure ⟨hxe, hx⟩
    have : (𝓝[e.source ∩ configY e] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
    have hcont : ContinuousWithinAt (fun y ↦ ‖e y - 4‖) (e.source ∩ configY e) x :=
      (((e.continuousAt hxe).sub continuousAt_const).norm).continuousWithinAt
    refine ge_of_tendsto hcont ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hK₁ y hy.1 hy.2).le
  have hβle1 : ∀ x ∈ closure (configY e), β x ≤ 1 := by
    intro x hx
    by_cases hxe : x ∈ e.source
    · rw [hβin x hxe]
      have h1 : 1 ≤ ‖e x - 4‖ := hnorm1 x hx hxe
      have h2 : 0 ≤ Real.log ‖e x - 4‖ := Real.log_nonneg h1
      have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
      refine max_le zero_le_one ?_
      rw [div_le_one hlog2]
      linarith
    · rw [hβ0 x hxe]; exact zero_le_one
  -- `β` vanishes off the compact preimage of `closedBall 4 2`
  have hC_sub : closedBall (4 : ℂ) 2 ⊆ ball (0 : ℂ) 8 :=
    closedBall_config_subset (by simp) le_rfl
  have hCclosed : IsClosed (e.symm '' closedBall (4 : ℂ) 2) :=
    ((isCompact_closedBall _ _).image_of_continuousOn
      (e.symm.continuousOn.mono (by simpa using hC_sub.trans hb))).isClosed
  have hβ_zero_off : ∀ y, y ∉ e.symm '' closedBall (4 : ℂ) 2 → β y = 0 := by
    intro y hyC
    by_cases hys : y ∈ e.source
    · rw [hβin y hys]
      have h1 : e y ∉ closedBall (4 : ℂ) 2 := fun hcon ↦ hyC ⟨e y, hcon, e.left_inv hys⟩
      have h2 : 2 < ‖e y - 4‖ := by
        rw [mem_closedBall, dist_eq_norm, not_le] at h1
        exact h1
      have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
      have h3 : Real.log 2 < Real.log ‖e y - 4‖ := Real.log_lt_log two_pos h2
      exact max_eq_left (div_nonpos_iff.mpr (Or.inr ⟨by linarith, hlog2.le⟩))
    · exact hβ0 y hys
  -- continuity of `β` on the closure of `Y`
  have hβcont : ContinuousOn β (closure (configY e)) := by
    intro x hx
    by_cases hxe : x ∈ e.source
    · have h1 : 1 ≤ ‖e x - 4‖ := hnorm1 x hx hxe
      have hne : ‖e x - 4‖ ≠ 0 := by positivity
      have hcont1 : ContinuousAt
          (fun y ↦ Max.max 0 ((Real.log 2 - Real.log ‖e y - 4‖) / Real.log 2)) x := by
        refine Filter.Tendsto.max continuousAt_const ?_
        refine ContinuousAt.div ?_ continuousAt_const (Real.log_pos one_lt_two).ne'
        refine ContinuousAt.sub continuousAt_const ?_
        exact (((e.continuousAt hxe).sub continuousAt_const).norm).log hne
      refine (hcont1.congr ?_).continuousWithinAt
      filter_upwards [e.open_source.mem_nhds hxe] with y hy
      exact (hβin y hy).symm
    · have hxC : x ∉ e.symm '' closedBall (4 : ℂ) 2 := by
        rintro ⟨w, hw, rfl⟩
        exact hxe (e.map_target (hb (hC_sub hw)))
      have hev : β =ᶠ[𝓝 x] fun _ ↦ 0 := by
        filter_upwards [hCclosed.isOpen_compl.mem_nhds hxC] with y hy
        exact hβ_zero_off y hy
      exact continuousWithinAt_const.congr_of_eventuallyEq
        (hev.filter_mono nhdsWithin_le_nhds) hev.self_of_nhds
  -- subharmonicity of `β` on `Y`, by locality
  have hβsub : SurfaceSubharmonicOn β (configY e) := by
    refine SurfaceSubharmonicOn.of_locally ?_
    intro x hxY
    by_cases hxe : x ∈ e.source
    · -- on `e.source ∩ Y`, `β = max 0 (harmonic)`
      refine ⟨e.source ∩ configY e, e.open_source.inter hYo, ⟨hxe, hxY⟩,
        inter_subset_right, ?_⟩
      have hharm : SurfaceHarmonicOn
          (fun y ↦ (Real.log 2 - Real.log ‖e y - 4‖) / Real.log 2)
          (e.source ∩ configY e) := by
        refine SurfaceHarmonicOn.of_chartwise ?_
        rintro y ⟨hys, hyY⟩
        refine ⟨e, he, hys, ?_⟩
        have hy4 : e y ≠ 4 := by
          intro hcon
          have h1 := hK₁ y hys hyY
          rw [hcon] at h1
          simp at h1
          norm_num at h1
        have hexp : HarmonicAt
            (fun w : ℂ ↦ (Real.log 2 - Real.log ‖w - 4‖) / Real.log 2) (e y) := by
          have h1 : AnalyticAt ℂ (fun w : ℂ ↦ w - 4) (e y) := by fun_prop
          have h2 : (fun w : ℂ ↦ w - 4) (e y) ≠ 0 := sub_ne_zero.mpr hy4
          have hlog := h1.harmonicAt_log_norm h2
          have hsub : HarmonicAt (fun w : ℂ ↦ Real.log 2 - Real.log ‖w - 4‖) (e y) :=
            (harmonicAt_const _).sub hlog
          have heq : (fun w : ℂ ↦ (Real.log 2 - Real.log ‖w - 4‖) / Real.log 2)
              = (Real.log 2)⁻¹ • fun w : ℂ ↦ Real.log 2 - Real.log ‖w - 4‖ := by
            funext w
            simp [div_eq_inv_mul]
          rw [heq]
          exact hsub.const_smul
        refine (harmonicAt_congr_nhds ?_).mpr hexp
        filter_upwards [e.open_target.mem_nhds (e.map_source hys)] with w hw
        simp only [Function.comp_apply]
        rw [e.right_inv hw]
      have hmax := SurfaceSubharmonicOn.max
        (⟨continuousOn_const, fun e' _ ↦ SubMeanOn.const⟩ :
          SurfaceSubharmonicOn (fun _ ↦ (0 : ℝ)) (e.source ∩ configY e))
        hharm.surfaceSubharmonicOn
      refine surfaceSubharmonicOn_congr hmax ?_
      intro y hy
      exact hβin y hy.1
    · -- off the source, `β` vanishes on a neighbourhood
      have hxC : x ∉ e.symm '' closedBall (4 : ℂ) 2 := by
        rintro ⟨w, hw, rfl⟩
        exact hxe (e.map_target (hb (hC_sub hw)))
      refine ⟨(e.symm '' closedBall (4 : ℂ) 2)ᶜ ∩ configY e,
        hCclosed.isOpen_compl.inter hYo, ⟨hxC, hxY⟩, inter_subset_right, ?_⟩
      refine surfaceSubharmonicOn_congr
        (⟨continuousOn_const, fun e' _ ↦ SubMeanOn.const⟩ :
          SurfaceSubharmonicOn (fun _ ↦ (0 : ℝ)) _) ?_
      intro y hy
      exact hβ_zero_off y hy.1
  -- boundary condition at the disk `K₀`
  have hβbd : ∀ x ∈ closure (configY e) ∩ e.symm '' closedBall (-4 : ℂ) 1, β x ≤ 0 := by
    rintro x ⟨-, w, hw, rfl⟩
    have hwt : w ∈ e.target := hb (closedBall_config_subset (by simp) (by norm_num) hw)
    refine le_of_eq (hβ_zero_off _ ?_)
    rintro ⟨w', hw', heq⟩
    have h1 : w' ∈ e.target := hb (hC_sub hw')
    have hww : w' = w := by
      have h3 := congrArg e heq
      rwa [e.right_inv h1, e.right_inv hwt] at h3
    rw [hww] at hw'
    have d1 : dist w (4 : ℂ) ≤ 2 := mem_closedBall.mp hw'
    have d2 : dist w (-4 : ℂ) ≤ 1 := mem_closedBall.mp hw
    have d3 : dist (-4 : ℂ) (4 : ℂ) = 8 := by
      rw [dist_eq_norm, show ((-4 : ℂ) - 4) = -8 by ring, norm_neg]
      simp
    have htri := dist_triangle (-4 : ℂ) w 4
    rw [dist_comm (-4 : ℂ) w] at htri
    linarith
  -- `β` belongs to the family
  have hβmem : β ∈ configFamily e :=
    ⟨hβsub, fun x hx ↦ ⟨hβnn x, hβle1 x hx⟩, hβcont, hβbd⟩
  -- value at the witness point
  have hval : β (e.symm (4 + (2 : ℂ) ^ ((1 : ℂ) / 4))) = 3 / 4 := by
    set t := (2 : ℂ) ^ ((1 : ℂ) / 4) with ht
    have hnt : ‖t‖ = (2 : ℝ) ^ ((1 : ℝ) / 4) := norm_two_cpow_quarter
    have h2t : ‖t‖ < 2 := by rw [hnt]; exact two_rpow_quarter_lt_two
    have hw₁ : (4 + t) ∈ ball (0 : ℂ) 8 := by
      rw [mem_ball, dist_zero_right]
      have h4 : ‖(4 : ℂ)‖ = 4 := by simp
      calc ‖4 + t‖ ≤ ‖(4 : ℂ)‖ + ‖t‖ := norm_add_le _ _
        _ < 8 := by rw [h4]; linarith
    have hwt : (4 + t) ∈ e.target := hb hw₁
    have hxs : e.symm (4 + t) ∈ e.source := e.map_target hwt
    rw [hβin _ hxs, e.right_inv hwt, show (4 + t) - 4 = t by ring, hnt,
      Real.log_rpow two_pos]
    have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    have hcalc : (Real.log 2 - 1 / 4 * Real.log 2) / Real.log 2 = 3 / 4 := by
      field_simp
      ring
    rw [hcalc]
    exact max_eq_right (by norm_num)
  calc (3 : ℝ) / 4 = β (e.symm (4 + (2 : ℂ) ^ ((1 : ℂ) / 4))) := hval.symm
    _ ≤ perronSup (configFamily e) (e.symm (4 + (2 : ℂ) ^ ((1 : ℂ) / 4))) :=
        (isPerronFamily_configFamily hb).le_perronSup hβmem _
          (witness_mem_configY hb).1

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- The upper barrier: forced value `≤ 1/4` at the witness point near the disk
at `-4` (every family member is dominated on the annulus by
`1 - log(2/|ζ+4|)/log 2`, by the boundary comparison principle). -/
theorem perronSup_le_witness [T2Space X] :
    perronSup (configFamily e) (e.symm (-4 + (2 : ℂ) ^ ((1 : ℂ) / 4))) ≤ 1 / 4 := by
  have hYo : IsOpen (configY e) := isOpen_configY hb
  set t := (2 : ℂ) ^ ((1 : ℂ) / 4) with ht
  have hnt : ‖t‖ = (2 : ℝ) ^ ((1 : ℝ) / 4) := norm_two_cpow_quarter
  have h1t : 1 < ‖t‖ := by rw [hnt]; exact one_lt_two_rpow_quarter
  have h2t : ‖t‖ < 2 := by rw [hnt]; exact two_rpow_quarter_lt_two
  -- the annulus and the upper barrier
  set A : Set ℂ := {w | 1 < ‖w + 4‖ ∧ ‖w + 4‖ < 2} with hA_def
  set γ : ℂ → ℝ := fun w ↦ Real.log ‖w + 4‖ / Real.log 2 with hγ_def
  have hcontf : Continuous fun w : ℂ ↦ ‖w + 4‖ := by fun_prop
  have hAopen : IsOpen A := isOpen_Ioo.preimage hcontf
  have hclA : closure A ⊆ {w : ℂ | 1 ≤ ‖w + 4‖ ∧ ‖w + 4‖ ≤ 2} :=
    closure_minimal (fun w hw ↦ ⟨hw.1.le, hw.2.le⟩) (isClosed_Icc.preimage hcontf)
  have hAbd : Bornology.IsBounded A := by
    refine (isBounded_ball (x := (-4 : ℂ)) (r := 2)).subset ?_
    intro w hw
    rw [mem_ball, dist_eq_norm, show w - (-4 : ℂ) = w + 4 by ring]
    exact hw.2
  -- annulus points stay in the big ball and in `Y`
  have hAball : ∀ w : ℂ, ‖w + 4‖ ≤ 2 → w ∈ ball (0 : ℂ) 8 := by
    intro w hw
    rw [mem_ball, dist_zero_right]
    have h1 : ‖w‖ ≤ ‖w + 4‖ + ‖(-4 : ℂ)‖ := by
      calc ‖w‖ = ‖(w + 4) + (-4)‖ := by ring_nf
        _ ≤ ‖w + 4‖ + ‖(-4 : ℂ)‖ := norm_add_le _ _
    have h4 : ‖(-4 : ℂ)‖ = 4 := by simp
    linarith
  have hAY : ∀ w ∈ A, e.symm w ∈ configY e := by
    intro w hw
    have hwb : w ∈ ball (0 : ℂ) 8 := hAball w hw.2.le
    refine ⟨mem_univ _, ?_⟩
    rintro (hmem | hmem)
    · have hd : 1 < dist w (-4 : ℂ) := by
        rw [dist_eq_norm, show w - (-4 : ℂ) = w + 4 by ring]
        exact hw.1
      exact notMem_image_of_dist_gt hb hwb
        (closedBall_config_subset (by simp) (by norm_num)) hd hmem
    · have hd : 1 < dist w (4 : ℂ) := by
        rw [dist_eq_norm, show w - (4 : ℂ) = (w + 4) - 8 by ring, norm_sub_rev]
        have hlow := norm_sub_norm_le (8 : ℂ) (w + 4)
        have h8 : ‖(8 : ℂ)‖ = 8 := by simp
        linarith [hw.2]
      exact notMem_image_of_dist_gt hb hwb
        (closedBall_config_subset (by simp) (by norm_num)) hd hmem
  have hAchart : A ⊆ chartImage e (configY e) := by
    intro w hw
    have hwt : w ∈ e.target := hb (hAball w hw.2.le)
    exact ⟨e.symm w, ⟨hAY w hw, e.map_target hwt⟩, e.right_inv hwt⟩
  -- closure points map into the closure of `Y`
  have hclAY : ∀ w ∈ closure A, e.symm w ∈ closure (configY e) := by
    intro w hw
    have hwt : w ∈ e.target := hb (hAball w (hclA hw).2)
    have hcont : ContinuousWithinAt e.symm A w :=
      (e.symm.continuousAt (by simpa using hwt)).continuousWithinAt
    refine closure_mono ?_ (hcont.mem_closure_image hw)
    rintro y ⟨w', hw', rfl⟩
    exact hAY w' hw'
  -- the barrier is harmonic on the annulus
  have hγharm : HarmonicOnNhd γ A := by
    intro w hw
    have hne : w + 4 ≠ 0 := by
      intro hcon
      have h1 := hw.1
      rw [hcon] at h1
      simp at h1
      norm_num at h1
    have h1 : AnalyticAt ℂ (fun w : ℂ ↦ w + 4) w := by fun_prop
    have hlog := h1.harmonicAt_log_norm hne
    have heq : γ = (Real.log 2)⁻¹ • fun w : ℂ ↦ Real.log ‖w + 4‖ := by
      funext w
      simp [hγ_def, div_eq_inv_mul]
    rw [heq]
    exact hlog.const_smul
  -- continuity of the barrier up to the closure
  have hγcont : ContinuousOn γ (closure A) := by
    intro w hw
    have h1 : 1 ≤ ‖w + 4‖ := (hclA hw).1
    have hne : ‖w + 4‖ ≠ 0 := by positivity
    exact ((hcontf.continuousAt.log hne).div_const _).continuousWithinAt
  -- every family member is dominated by the barrier on the annulus
  have hkey : ∀ g ∈ configFamily e, g (e.symm (-4 + t)) ≤ 1 / 4 := by
    rintro g ⟨hgsub, hgicc, hgcont, hgbd⟩
    have hgsm : SubMeanOn (g ∘ e.symm) A := (hgsub.subMeanOn e he).mono hAchart
    have hγmeq : MeanEqOn γ A := HarmonicOnNhd.meanEqOn hγharm
    have hsm : SubMeanOn ((g ∘ e.symm) + -γ) A := hgsm.add_meanEq hγmeq.neg
    have hcont2 : ContinuousOn ((g ∘ e.symm) + -γ) (closure A) := by
      refine ContinuousOn.add ?_ hγcont.neg
      refine hgcont.comp (e.symm.continuousOn.mono ?_) fun w hw ↦ hclAY w hw
      have hsub : closure A ⊆ e.target := fun w hw ↦ hb (hAball w (hclA hw).2)
      simpa using hsub
    have hfr : ∀ w ∈ frontier A, ((g ∘ e.symm) + -γ) w ≤ 0 := by
      intro w hw
      have hwcl : w ∈ closure A := frontier_subset_closure hw
      have hwc := hclA hwcl
      have hnA : w ∉ A := by
        intro hcon
        rw [← hAopen.interior_eq] at hcon
        exact hw.2 hcon
      have hcases : ‖w + 4‖ = 1 ∨ ‖w + 4‖ = 2 := by
        rcases eq_or_lt_of_le hwc.1 with heq | hlt1
        · exact Or.inl heq.symm
        rcases eq_or_lt_of_le hwc.2 with heq | hlt2
        · exact Or.inr heq
        · exact absurd ⟨hlt1, hlt2⟩ hnA
      simp only [Pi.add_apply, Pi.neg_apply, Function.comp_apply]
      rcases hcases with h1 | h2
      · -- inner circle: the barrier vanishes and `g ≤ 0`
        have hγ0 : γ w = 0 := by
          change Real.log ‖w + 4‖ / Real.log 2 = 0
          rw [h1]
          simp
        have hK : e.symm w ∈ e.symm '' closedBall (-4 : ℂ) 1 :=
          ⟨w, by rw [mem_closedBall, dist_eq_norm, show w - (-4 : ℂ) = w + 4 by ring, h1], rfl⟩
        have hgw : g (e.symm w) ≤ 0 := hgbd _ ⟨hclAY w hwcl, hK⟩
        rw [hγ0]
        linarith
      · -- outer circle: the barrier is `1` and `g ≤ 1`
        have hγ1 : γ w = 1 := by
          change Real.log ‖w + 4‖ / Real.log 2 = 1
          rw [h2]
          exact div_self (Real.log_pos one_lt_two).ne'
        have hgw : g (e.symm w) ≤ 1 := (hgicc _ (hclAY w hwcl)).2
        rw [hγ1]
        linarith
    have hle := hsm.le_of_frontier_le hAopen hAbd hcont2 hfr
    have hwA : (-4 + t) ∈ A := by
      change 1 < ‖(-4 + t) + 4‖ ∧ ‖(-4 + t) + 4‖ < 2
      rw [show (-4 + t) + 4 = t by ring]
      exact ⟨h1t, h2t⟩
    have hval := hle _ (subset_closure hwA)
    simp only [Pi.add_apply, Pi.neg_apply, Function.comp_apply] at hval
    have hγw : γ (-4 + t) = 1 / 4 := by
      change Real.log ‖(-4 + t) + 4‖ / Real.log 2 = 1 / 4
      rw [show (-4 + t) + 4 = t by ring, hnt, Real.log_rpow two_pos]
      have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
      field_simp
    rw [hγw] at hval
    linarith
  exact (isPerronFamily_configFamily hb).perronSup_le hkey

end Config

end Rado
