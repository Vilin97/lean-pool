/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import LeanPool.Rado.Surface.Harmonic
import Mathlib.Analysis.Complex.Harmonic.Poisson

/-!
# Harmonic replacement and Perron's principle

Step 4 of `Rado/PLAN.md`: `surfaceReplace` (replace a subharmonic function
inside a chart disk by the Dirichlet solution of its boundary values, Anghel–
Stan Remark 4 — Hausdorffness genuinely needed, see the counterexample at
`surfaceReplace_surfaceSubharmonicOn`), Perron families, Harnack's principle
for monotone sequences of harmonic functions, and **Perron's principle**: the
upper envelope of a Perron family is harmonic
(`IsPerronFamily.surfaceHarmonicOn_perronSup`; Anghel–Stan Theorem 6, Hubbard
Prop. 1.2.3).
-/

open Set Topology Metric MeasureTheory InnerProductSpace Complex Filter

namespace Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## Harmonic replacement and Perron families -/

open Classical in
/-- Replace `g` inside the closed disk `e.symm '' closedBall c r` by the
Dirichlet solution with `g`'s boundary values, read through the chart. -/
noncomputable def surfaceReplace (g : X → ℝ) (e : OpenPartialHomeomorph X ℂ)
    (c : ℂ) (r : ℝ) : X → ℝ := fun x ↦
  if _h : x ∈ e.source ∧ e x ∈ closedBall c r then
    poissonExtension (g ∘ e.symm) c r (e x)
  else g x

section Replace

variable {g : X → ℝ} {s : Set X} {e : OpenPartialHomeomorph X ℂ} {c : ℂ} {r : ℝ}

/-- Data for a legal replacement disk: a maximal-atlas chart and a closed disk
in its target whose preimage lies in `s`. -/
structure IsReplaceDisk (e : OpenPartialHomeomorph X ℂ) (c : ℂ) (r : ℝ) (s : Set X) :
    Prop where
  mem_atlas : e ∈ riemannAtlas X
  r_pos : 0 < r
  closedBall_subset : closedBall c r ⊆ e.target
  preimage_subset : e.symm '' closedBall c r ⊆ s

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
theorem IsReplaceDisk.compact_preimage (hd : IsReplaceDisk e c r s) :
    IsCompact (e.symm '' closedBall c r) :=
  (isCompact_closedBall c r).image_of_continuousOn
    (e.symm.continuousOn.mono (by simpa using hd.closedBall_subset))

omit [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- The replacement agrees with `g` off the closed replacement disk. -/
theorem surfaceReplace_eqOn_compl :
    EqOn (surfaceReplace g e c r) g (e.symm '' closedBall c r)ᶜ := by
  intro x hx
  rw [surfaceReplace, dite_eq_right]
  rintro ⟨hxs, hxb⟩
  exact hx ⟨e x, hxb, e.left_inv hxs⟩

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
private theorem IsReplaceDisk.closedBall_subset_chartImage (hd : IsReplaceDisk e c r s) :
    closedBall c r ⊆ chartImage e s := fun w hw ↦
  ⟨e.symm w, ⟨hd.preimage_subset ⟨w, hw, rfl⟩, e.map_target (hd.closedBall_subset hw)⟩,
    e.right_inv (hd.closedBall_subset hw)⟩

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
private theorem IsReplaceDisk.isOpen_ball_image (hd : IsReplaceDisk e c r s) :
    IsOpen (e.symm '' ball c r) :=
  e.symm.isOpen_image_of_subset_source isOpen_ball
    (by simpa using ball_subset_closedBall.trans hd.closedBall_subset)

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
private theorem IsReplaceDisk.continuousOn_sphere (hd : IsReplaceDisk e c r s)
    (hg : SurfaceSubharmonicOn g s) : ContinuousOn (g ∘ e.symm) (sphere c r) :=
  (continuousOn_comp_chart_symm e hg.continuousOn).mono
    (sphere_subset_closedBall.trans hd.closedBall_subset_chartImage)

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- `g` is dominated by its replacement (comparison principle); helper form. -/
private theorem le_surfaceReplace_aux (hg : SurfaceSubharmonicOn g s)
    (hd : IsReplaceDisk e c r s) : ∀ x ∈ s, g x ≤ surfaceReplace g e c r x := by
  intro x hx
  by_cases hxD : x ∈ e.symm '' closedBall c r
  · obtain ⟨w, hwb, rfl⟩ := hxD
    have hwt : w ∈ e.target := hd.closedBall_subset hwb
    have hxsrc : e.symm w ∈ e.source := e.map_target hwt
    have hew : e (e.symm w) = w := e.right_inv hwt
    have hle := (hg.subMeanOn e hd.mem_atlas).le_poissonExtension_on
      hd.r_pos hd.closedBall_subset_chartImage w hwb
    rw [surfaceReplace, dite_eq_left ⟨hxsrc, by rw [hew]; exact hwb⟩, hew]
    exact hle
  · exact (surfaceReplace_eqOn_compl hxD).ge

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- The replacement is harmonic inside the disk; helper form. -/
private theorem surfaceReplace_surfaceHarmonicOn_aux (hg : SurfaceSubharmonicOn g s)
    (hd : IsReplaceDisk e c r s) :
    SurfaceHarmonicOn (surfaceReplace g e c r) (e.symm '' ball c r) := by
  have hbt : ball c r ⊆ e.target := ball_subset_closedBall.trans hd.closedBall_subset
  have hgs : ContinuousOn (g ∘ e.symm) (sphere c r) := hd.continuousOn_sphere hg
  refine SurfaceHarmonicOn.of_chartwise ?_
  rintro x ⟨w, hwb, rfl⟩
  have hwt : w ∈ e.target := hbt hwb
  have hxsrc : e.symm w ∈ e.source := e.map_target hwt
  have hew : e (e.symm w) = w := e.right_inv hwt
  refine ⟨e, hd.mem_atlas, hxsrc, ?_⟩
  rw [hew]
  have hharm := poissonExtension_harmonicOnNhd hd.r_pos hgs w hwb
  refine (harmonicAt_congr_nhds ?_).mpr hharm
  filter_upwards [isOpen_ball.mem_nhds hwb] with w' hw'
  have hwt' : w' ∈ e.target := hbt hw'
  simp only [Function.comp_apply]
  rw [surfaceReplace, dite_eq_left ⟨e.map_target hwt',
    by rw [e.right_inv hwt']; exact ball_subset_closedBall hw'⟩, e.right_inv hwt']

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- The replacement is subharmonic (Anghel–Stan Remark 4): with `[T2Space X]`
the compact replacement disk is closed, and the replacement is subharmonic on
`s` — harmonic inside the disk, equal to `g` outside, and the sub-mean
inequality glues across the circle because `g ≤ surfaceReplace g` there.

The Hausdorff hypothesis is genuinely needed: on the plane with doubled
origin, with `g = ‖chart value‖²`, the replacement on the copy-1 unit disk is
`≡ 1` on the shared punctured disk but `0` at the doubled origin, which lies
in the closure of the replacement disk but outside `e.source` — so the
replacement fails to be continuous, let alone subharmonic. -/
theorem surfaceReplace_surfaceSubharmonicOn [T2Space X] (hs : IsOpen s)
    (hg : SurfaceSubharmonicOn g s) (hd : IsReplaceDisk e c r s) :
    SurfaceSubharmonicOn (surfaceReplace g e c r) s := by
  classical
  have hgs : ContinuousOn (g ∘ e.symm) (sphere c r) := hd.continuousOn_sphere hg
  have hrepg : ContinuousOn (g ∘ e.symm) (chartImage e s) :=
    continuousOn_comp_chart_symm e hg.continuousOn
  -- the chart-side glued function is continuous on `chartImage e s`
  have hh : ContinuousOn (fun w ↦ if w ∈ closedBall c r
      then poissonExtension (g ∘ e.symm) c r w else (g ∘ e.symm) w) (chartImage e s) := by
    refine ContinuousOn.if ?_ ?_ ?_
    · intro a ha
      have h2 := ha.2
      simp only [Set.ofPred_mem_eq] at h2
      rw [frontier_closedBall c hd.r_pos.ne'] at h2
      exact poissonExtension_eqOn_sphere hd.r_pos hgs h2
    · refine (poissonExtension_continuousOn hd.r_pos hgs).mono ?_
      refine inter_subset_right.trans ?_
      simp only [Set.ofPred_mem_eq]
      rw [isClosed_closedBall.closure_eq]
    · exact hrepg.mono inter_subset_left
  -- continuity of the replacement on `s`
  have hcont : ContinuousOn (surfaceReplace g e c r) s := by
    intro x hx
    by_cases hxsrc : x ∈ e.source
    · have hex : e x ∈ chartImage e s := mem_chartImage_of_mem hx hxsrc
      have h1 : ContinuousAt (fun w ↦ if w ∈ closedBall c r
          then poissonExtension (g ∘ e.symm) c r w else (g ∘ e.symm) w) (e x) :=
        hh.continuousAt ((isOpen_chartImage e hs).mem_nhds hex)
      have h2 : ContinuousAt ((fun w ↦ if w ∈ closedBall c r
          then poissonExtension (g ∘ e.symm) c r w else (g ∘ e.symm) w) ∘ e) x :=
        h1.comp (e.continuousAt hxsrc)
      refine (h2.congr ?_).continuousWithinAt
      filter_upwards [e.open_source.mem_nhds hxsrc] with y hy
      by_cases hyb : e y ∈ closedBall c r
      · simp only [Function.comp_apply, ite_eq_left hyb]
        rw [surfaceReplace, dite_eq_left ⟨hy, hyb⟩]
      · simp only [Function.comp_apply, ite_eq_right hyb]
        rw [surfaceReplace, dite_eq_right fun hcon ↦ hyb hcon.2]
        simp only [e.left_inv hy]
    · -- off the chart source: the disk is closed (T2), so the replacement
      -- agrees with `g` on a neighbourhood
      have hxD : x ∉ e.symm '' closedBall c r := by
        rintro ⟨w, hw, rfl⟩
        exact hxsrc (e.map_target (hd.closedBall_subset hw))
      have hDc : IsClosed (e.symm '' closedBall c r) := hd.compact_preimage.isClosed
      have hev : surfaceReplace g e c r =ᶠ[𝓝 x] g := by
        filter_upwards [hDc.isOpen_compl.mem_nhds hxD] with y hy
        exact surfaceReplace_eqOn_compl hy
      exact (hg.continuousOn x hx).congr_of_eventuallyEq
        (hev.filter_mono nhdsWithin_le_nhds) hev.self_of_nhds
  -- the sub-mean inequality in every chart, on small circles
  refine ⟨hcont, fun e' he' ↦ ?_⟩
  refine SubMeanLocalOn.subMeanOn ?_
  refine ⟨continuousOn_comp_chart_symm e' hcont, ?_⟩
  rintro w ⟨x, ⟨hxs, hxe⟩, rfl⟩
  by_cases hxB : x ∈ e.symm '' ball c r
  · -- interior of the disk: harmonic, hence the mean-value equality
    have hharm : HarmonicOnNhd (surfaceReplace g e c r ∘ e'.symm)
        (chartImage e' (e.symm '' ball c r)) :=
      surfaceReplace_surfaceHarmonicOn_aux hg hd e' he'
    have hMeq : MeanEqOn (surfaceReplace g e c r ∘ e'.symm)
        (chartImage e' (e.symm '' ball c r)) :=
      HarmonicOnNhd.meanEqOn hharm
    have hmem : e' x ∈ chartImage e' (e.symm '' ball c r) := mem_chartImage_of_mem hxB hxe
    obtain ⟨ρ, hρ, hball⟩ :=
      Metric.isOpen_iff.mp (isOpen_chartImage e' hd.isOpen_ball_image) _ hmem
    filter_upwards [Ioo_mem_nhdsGT hρ] with r' hr'
    exact (hMeq.mean_eq (e' x) r' hr'.1 ((closedBall_subset_ball hr'.2).trans hball)).ge
  · -- on the circle or outside: the replacement equals `g` at the point and
    -- dominates `g` on the circles
    have hux : surfaceReplace g e c r x = g x := by
      by_cases hxD : x ∈ e.symm '' closedBall c r
      · obtain ⟨w', hw', rfl⟩ := hxD
        have hwt : w' ∈ e.target := hd.closedBall_subset hw'
        have hxsrc : e.symm w' ∈ e.source := e.map_target hwt
        have hew : e (e.symm w') = w' := e.right_inv hwt
        have hsph : w' ∈ sphere c r := by
          rw [mem_sphere]
          rcases lt_or_eq_of_le (mem_closedBall.mp hw') with hlt | heq'
          · exact absurd ⟨w', mem_ball.mpr hlt, rfl⟩ hxB
          · exact heq'
        rw [surfaceReplace, dite_eq_left ⟨hxsrc, by rw [hew]; exact hw'⟩, hew,
          poissonExtension_eqOn_sphere hd.r_pos hgs hsph]
        simp
      · exact surfaceReplace_eqOn_compl hxD
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp (isOpen_chartImage e' hs) _
      (mem_chartImage_of_mem hxs hxe)
    filter_upwards [Ioo_mem_nhdsGT hρ] with r' hr'
    have hcb : closedBall (e' x) r' ⊆ chartImage e' s :=
      (closedBall_subset_ball hr'.2).trans hball
    have hsph_sub : sphere (e' x) r' ⊆ chartImage e' s := sphere_subset_closedBall.trans hcb
    have hig : CircleIntegrable (g ∘ e'.symm) (e' x) r' :=
      ((hg.subMeanOn e' he').continuousOn.mono hsph_sub).circleIntegrable hr'.1.le
    have hiu : CircleIntegrable (surfaceReplace g e c r ∘ e'.symm) (e' x) r' :=
      ((continuousOn_comp_chart_symm e' hcont).mono hsph_sub).circleIntegrable hr'.1.le
    have hle1 : (g ∘ e'.symm) (e' x) ≤ Real.circleAverage (g ∘ e'.symm) (e' x) r' :=
      (hg.subMeanOn e' he').submean (e' x) r' hr'.1 hcb
    have hle2 : Real.circleAverage (g ∘ e'.symm) (e' x) r'
        ≤ Real.circleAverage (surfaceReplace g e c r ∘ e'.symm) (e' x) r' := by
      refine Real.circleAverage_mono hig hiu ?_
      intro z hz
      rw [abs_of_pos hr'.1] at hz
      obtain ⟨y, ⟨hys, hye⟩, rfl⟩ := hsph_sub hz
      simp only [Function.comp_apply]
      rw [e'.left_inv hye]
      exact le_surfaceReplace_aux hg hd y hys
    have hval : (surfaceReplace g e c r ∘ e'.symm) (e' x) = (g ∘ e'.symm) (e' x) := by
      simp only [Function.comp_apply, e'.left_inv hxe, hux]
    rw [hval]
    exact hle1.trans hle2

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- `g` is dominated by its replacement (comparison principle). -/
theorem le_surfaceReplace (hg : SurfaceSubharmonicOn g s)
    (hd : IsReplaceDisk e c r s) : ∀ x ∈ s, g x ≤ surfaceReplace g e c r x :=
  le_surfaceReplace_aux hg hd

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- The replacement is harmonic in the open replacement disk. -/
theorem surfaceReplace_surfaceHarmonicOn (hg : SurfaceSubharmonicOn g s)
    (hd : IsReplaceDisk e c r s) :
    SurfaceHarmonicOn (surfaceReplace g e c r) (e.symm '' ball c r) :=
  surfaceReplace_surfaceHarmonicOn_aux hg hd

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- The replacement stays in `[0,1]` if `g` does (on `s`). -/
theorem surfaceReplace_mem_Icc (hg : SurfaceSubharmonicOn g s)
    (hd : IsReplaceDisk e c r s) (hb : ∀ x ∈ s, g x ∈ Icc (0 : ℝ) 1) :
    ∀ x ∈ s, surfaceReplace g e c r x ∈ Icc (0 : ℝ) 1 := by
  intro x hx
  by_cases hxD : x ∈ e.symm '' closedBall c r
  · obtain ⟨w, hwb, rfl⟩ := hxD
    have hwt : w ∈ e.target := hd.closedBall_subset hwb
    have hxsrc : e.symm w ∈ e.source := e.map_target hwt
    have hew : e (e.symm w) = w := e.right_inv hwt
    have hbd : ∀ z ∈ sphere c r, (g ∘ e.symm) z ∈ Icc (0:ℝ) 1 := fun z hz ↦
      hb _ (hd.preimage_subset ⟨z, sphere_subset_closedBall hz, rfl⟩)
    have hval := poissonExtension_mem_Icc hd.r_pos (hd.continuousOn_sphere hg) hbd w hwb
    rw [surfaceReplace, dite_eq_left ⟨hxsrc, by rw [hew]; exact hwb⟩, hew]
    exact hval
  · rw [surfaceReplace_eqOn_compl hxD]
    exact hb x hx

end Replace

/-- A Perron family on `s`: a nonempty set of `[0,1]`-valued subharmonic
functions, closed under pairwise `max` and under harmonic replacement on disks
inside `s` (Anghel–Stan Definition 5, with the `[0,1]` normalization that
suffices for Radó). -/
structure IsPerronFamily (𝓕 : Set (X → ℝ)) (s : Set X) : Prop where
  nonempty : 𝓕.Nonempty
  subharmonic : ∀ g ∈ 𝓕, SurfaceSubharmonicOn g s
  bounds : ∀ g ∈ 𝓕, ∀ x ∈ s, g x ∈ Icc (0 : ℝ) 1
  max_mem : ∀ g₁ ∈ 𝓕, ∀ g₂ ∈ 𝓕, (fun x ↦ Max.max (g₁ x) (g₂ x)) ∈ 𝓕
  replace_mem : ∀ g ∈ 𝓕, ∀ e c r, IsReplaceDisk e c r s → surfaceReplace g e c r ∈ 𝓕

/-- The upper envelope of a family of functions. -/
noncomputable def perronSup (𝓕 : Set (X → ℝ)) : X → ℝ := fun x ↦
  sSup ((fun g ↦ g x) '' 𝓕)

/-! ### Harnack's principle for monotone sequences of harmonic functions -/

/-- **Harnack's inequality**, upper bound: a nonnegative harmonic function on a
closed disk is controlled at interior points by its value at the center. -/
private theorem harnack_le {h : ℂ → ℝ} {z₀ w : ℂ} {R : ℝ} (hR : 0 < R)
    (hh : HarmonicOnNhd h (closedBall z₀ R))
    (hpos : ∀ z ∈ closedBall z₀ R, 0 ≤ h z) (hw : w ∈ ball z₀ R) :
    h w ≤ (R + ‖w - z₀‖) / (R - ‖w - z₀‖) * h z₀ := by
  have hcont : ContinuousOn h (sphere z₀ R) := fun z hz ↦
    ((hh z (sphere_subset_closedBall hz)).1.continuousAt).continuousWithinAt
  have hker : ContinuousOn (poissonKernel z₀ w) (sphere z₀ R) :=
    poissonKernel_continuousOn_sphere hw
  have hrep : Real.circleAverage (poissonKernel z₀ w • h) z₀ R = h w :=
    hh.circleAverage_poissonKernel_smul hw
  have hmv : Real.circleAverage h z₀ R = h z₀ := by
    apply InnerProductSpace.HarmonicOnNhd.circleAverage_eq
    rwa [abs_of_pos hR]
  have hint1 : CircleIntegrable (poissonKernel z₀ w • h) z₀ R :=
    (hker.smul hcont).circleIntegrable hR.le
  have hint2 : CircleIntegrable
      (fun z ↦ (R + ‖w - z₀‖) / (R - ‖w - z₀‖) * h z) z₀ R :=
    (continuousOn_const.mul hcont).circleIntegrable hR.le
  have hmono : Real.circleAverage (poissonKernel z₀ w • h) z₀ R
      ≤ Real.circleAverage (fun z ↦ (R + ‖w - z₀‖) / (R - ‖w - z₀‖) * h z) z₀ R := by
    refine Real.circleAverage_mono hint1 hint2 ?_
    intro z hz
    rw [abs_of_pos hR] at hz
    have hkb : poissonKernel z₀ w z ≤ (R + ‖w - z₀‖) / (R - ‖w - z₀‖) := by
      have h1 := re_herglotzRieszKernel_le hz hw
      rw [poissonKernel_eq_re_herglotzRieszKernel]
      simpa [herglotzRieszKernel_def] using h1
    have h0 : 0 ≤ h z := hpos z (sphere_subset_closedBall hz)
    calc (poissonKernel z₀ w • h) z = poissonKernel z₀ w z * h z := rfl
      _ ≤ (R + ‖w - z₀‖) / (R - ‖w - z₀‖) * h z := mul_le_mul_of_nonneg_right hkb h0
  have havg : Real.circleAverage (fun z ↦ (R + ‖w - z₀‖) / (R - ‖w - z₀‖) * h z) z₀ R
      = (R + ‖w - z₀‖) / (R - ‖w - z₀‖) * h z₀ := by
    have h1 : Real.circleAverage (fun z ↦ ((R + ‖w - z₀‖) / (R - ‖w - z₀‖)) • h z) z₀ R
        = ((R + ‖w - z₀‖) / (R - ‖w - z₀‖)) • Real.circleAverage h z₀ R :=
      Real.circleAverage_fun_smul
    simpa [smul_eq_mul, hmv] using h1
  calc h w = Real.circleAverage (poissonKernel z₀ w • h) z₀ R := hrep.symm
    _ ≤ Real.circleAverage (fun z ↦ (R + ‖w - z₀‖) / (R - ‖w - z₀‖) * h z) z₀ R := hmono
    _ = (R + ‖w - z₀‖) / (R - ‖w - z₀‖) * h z₀ := havg

/-- **Harnack's principle** (bounded case): the pointwise supremum of a
monotone sequence of `[0,1]`-valued harmonic functions on an open set is
harmonic. Continuity comes from Harnack's inequality applied to the
differences, the mean value property passes to the limit by dominated
convergence. -/
private theorem harmonicOnNhd_ciSup_of_monotone {h : ℕ → ℂ → ℝ} {U : Set ℂ}
    (hU : IsOpen U) (hharm : ∀ n, HarmonicOnNhd (h n) U)
    (hmono : ∀ z ∈ U, ∀ m n : ℕ, m ≤ n → h m z ≤ h n z)
    (hbd : ∀ n, ∀ z ∈ U, h n z ∈ Icc (0 : ℝ) 1) :
    HarmonicOnNhd (fun z ↦ ⨆ n, h n z) U := by
  set W : ℂ → ℝ := fun z ↦ ⨆ n, h n z with hWdef
  have hWapp : ∀ z, W z = ⨆ n, h n z := fun z ↦ rfl
  have hbdd : ∀ z ∈ U, BddAbove (range fun n ↦ h n z) := fun z hz ↦
    ⟨1, by rintro v ⟨n, rfl⟩; exact (hbd n z hz).2⟩
  have hle : ∀ n, ∀ z ∈ U, h n z ≤ W z := fun n z hz ↦ le_ciSup (hbdd z hz) n
  have htend : ∀ z ∈ U, Tendsto (fun n ↦ h n z) atTop (𝓝 (W z)) := fun z hz ↦
    tendsto_atTop_ciSup (fun m n hmn ↦ hmono z hz m n hmn) (hbdd z hz)
  -- continuity of the supremum, via Harnack's inequality
  have hWc : ContinuousOn W U := by
    intro z₀ hz₀
    apply ContinuousAt.continuousWithinAt
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨R, hR, hRU⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hz₀)
    obtain ⟨m, hm⟩ : ∃ m, W z₀ - ε / 8 < h m z₀ := by
      have h1 : W z₀ - ε / 8 < ⨆ n, h n z₀ := by
        rw [← hWapp]; exact sub_lt_self _ (by linarith)
      exact exists_lt_of_lt_ciSup h1
    have hcm : ContinuousAt (h m) z₀ := (hharm m z₀ hz₀).1.continuousAt
    rw [Metric.continuousAt_iff] at hcm
    obtain ⟨δ₁, hδ₁, hδ₁p⟩ := hcm (ε / 8) (by linarith)
    -- Harnack control of the tail on the half ball
    have hkey : ∀ x ∈ ball z₀ (R / 2), W x - h m x ≤ 3 * (W z₀ - h m z₀) := by
      intro x hx
      have hxR : x ∈ ball z₀ R := ball_subset_ball (by linarith) hx
      have hxU : x ∈ U := hRU (ball_subset_closedBall hxR)
      have htends : Tendsto (fun n ↦ h n x - h m x) atTop (𝓝 (W x - h m x)) :=
        (htend x hxU).sub tendsto_const_nhds
      refine le_of_tendsto htends ?_
      filter_upwards [eventually_ge_atTop m] with n hn
      have hdiff : HarmonicOnNhd (fun z ↦ h n z - h m z) (closedBall z₀ R) := fun z hz ↦
        (hharm n z (hRU hz)).sub (hharm m z (hRU hz))
      have hnonneg : ∀ z ∈ closedBall z₀ R, 0 ≤ h n z - h m z := fun z hz ↦
        sub_nonneg.mpr (hmono z (hRU hz) m n hn)
      have hHar := harnack_le hR hdiff hnonneg hxR
      have hd2 : ‖x - z₀‖ < R / 2 := mem_ball_iff_norm.mp hx
      have hd0 : (0 : ℝ) ≤ ‖x - z₀‖ := norm_nonneg _
      have hfrac : (R + ‖x - z₀‖) / (R - ‖x - z₀‖) ≤ 3 := by
        rw [div_le_iff₀ (by linarith)]
        linarith
      have h0 : 0 ≤ h n z₀ - h m z₀ := sub_nonneg.mpr (hmono z₀ hz₀ m n hn)
      have hWn : h n z₀ ≤ W z₀ := hle n z₀ hz₀
      calc h n x - h m x ≤ (R + ‖x - z₀‖) / (R - ‖x - z₀‖) * (h n z₀ - h m z₀) := hHar
        _ ≤ 3 * (h n z₀ - h m z₀) := mul_le_mul_of_nonneg_right hfrac h0
        _ ≤ 3 * (W z₀ - h m z₀) := by linarith
    refine ⟨min δ₁ (R / 2), lt_min hδ₁ (by linarith), ?_⟩
    intro x hx
    have hx1 : dist x z₀ < δ₁ := lt_of_lt_of_le hx (min_le_left _ _)
    have hx2 : x ∈ ball z₀ (R / 2) := mem_ball.mpr (lt_of_lt_of_le hx (min_le_right _ _))
    have hxU : x ∈ U := hRU (ball_subset_closedBall (ball_subset_ball (by linarith) hx2))
    have k1 := hkey x hx2
    have k2 : 0 ≤ W x - h m x := sub_nonneg.mpr (hle m x hxU)
    have k3 : |h m x - h m z₀| < ε / 8 := by
      have := hδ₁p hx1
      rwa [Real.dist_eq] at this
    have k4 : 0 ≤ W z₀ - h m z₀ := sub_nonneg.mpr (hle m z₀ hz₀)
    rw [Real.dist_eq, abs_lt]
    rw [abs_lt] at k3
    constructor
    · linarith [k3.1]
    · linarith [k3.2]
  -- the mean value property passes to the limit
  have hmean : MeanEqOn W U := by
    refine ⟨hWc, fun a ρ hρ hsub ↦ ?_⟩
    have haU : a ∈ U := hsub (mem_closedBall_self hρ.le)
    have hsph : sphere a ρ ⊆ U := sphere_subset_closedBall.trans hsub
    have hcm : ∀ n, Continuous fun θ : ℝ ↦ h n (circleMap a ρ θ) := by
      intro n
      refine continuous_iff_continuousAt.mpr fun θ ↦ ?_
      exact ((hharm n _ (hsph (circleMap_mem_sphere a hρ.le θ))).1.continuousAt).comp
        (continuous_circleMap a ρ).continuousAt
    have hci : Tendsto (fun n ↦ ∫ θ in (0 : ℝ)..2 * Real.pi, h n (circleMap a ρ θ)) atTop
        (𝓝 (∫ θ in (0 : ℝ)..2 * Real.pi, W (circleMap a ρ θ))) := by
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (fun _ ↦ (1 : ℝ)) (Filter.Eventually.of_forall fun n ↦ (hcm n).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun n ↦ ae_of_all _ fun θ _ ↦ ?_)
        intervalIntegrable_const (ae_of_all _ fun θ _ ↦ ?_)
      · have hmem := hbd n _ (hsph (circleMap_mem_sphere a hρ.le θ))
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [hmem.1], hmem.2⟩
      · exact htend _ (hsph (circleMap_mem_sphere a hρ.le θ))
    have h2 : Tendsto (fun n ↦ Real.circleAverage (h n) a ρ) atTop
        (𝓝 (Real.circleAverage W a ρ)) := by
      simp only [Real.circleAverage_def]
      exact hci.const_smul _
    have h3 : Tendsto (fun n ↦ Real.circleAverage (h n) a ρ) atTop (𝓝 (W a)) :=
      Filter.Tendsto.congr
        (fun n ↦ ((HarmonicOnNhd.meanEqOn (hharm n)).mean_eq a ρ hρ hsub).symm)
        (htend a haU)
    exact tendsto_nhds_unique h2 h3
  exact hmean.harmonicOnNhd hU

/-! ### The Perron approximation sequence -/

/-- Pointwise maximum of the first `j + 1` members of a sequence of
functions. -/
private def maxUpTo (f : ℕ → X → ℝ) : ℕ → X → ℝ
  | 0 => f 0
  | j + 1 => fun y ↦ Max.max (maxUpTo f j y) (f (j + 1) y)

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
private theorem maxUpTo_mem {𝓕 : Set (X → ℝ)} {s : Set X} (h𝓕 : IsPerronFamily 𝓕 s)
    {f : ℕ → X → ℝ} (hf : ∀ j, f j ∈ 𝓕) : ∀ j, maxUpTo f j ∈ 𝓕 := by
  intro j
  induction j with
  | zero => rw [maxUpTo]; exact hf 0
  | succ j ih => rw [maxUpTo]; exact h𝓕.max_mem _ ih _ (hf (j + 1))

omit [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
private theorem le_maxUpTo {f : ℕ → X → ℝ} {i j : ℕ} (hij : i ≤ j) (y : X) :
    f i y ≤ maxUpTo f j y := by
  induction j with
  | zero =>
    obtain rfl : i = 0 := Nat.le_zero.mp hij
    rw [maxUpTo]
  | succ j ih =>
    rw [maxUpTo]
    rcases eq_or_lt_of_le hij with rfl | hlt
    · exact le_max_right _ _
    · exact (ih (Nat.lt_succ_iff.mp hlt)).trans (le_max_left _ _)

/-- The recursive Perron approximation sequence: harmonic replacements of the
running maxima of a given sequence of family members. -/
private noncomputable def perronSeq (e : OpenPartialHomeomorph X ℂ) (c : ℂ) (r : ℝ)
    (b : ℕ → X → ℝ) : ℕ → X → ℝ
  | 0 => surfaceReplace (b 0) e c r
  | n + 1 => surfaceReplace
      (fun y ↦ Max.max (perronSeq e c r b n y) (b (n + 1) y)) e c r

section PerronSeq

variable {𝓕 : Set (X → ℝ)} {s : Set X} {e : OpenPartialHomeomorph X ℂ} {c : ℂ} {r : ℝ}
  {b : ℕ → X → ℝ}

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
private theorem perronSeq_mem (h𝓕 : IsPerronFamily 𝓕 s) (hd : IsReplaceDisk e c r s)
    (hb : ∀ n, b n ∈ 𝓕) : ∀ n, perronSeq e c r b n ∈ 𝓕 := by
  intro n
  induction n with
  | zero =>
    rw [perronSeq]
    exact h𝓕.replace_mem _ (hb 0) e c r hd
  | succ n ih =>
    rw [perronSeq]
    exact h𝓕.replace_mem _ (h𝓕.max_mem _ ih _ (hb (n + 1))) e c r hd

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
private theorem le_perronSeq (h𝓕 : IsPerronFamily 𝓕 s)
    (hd : IsReplaceDisk e c r s) (hb : ∀ n, b n ∈ 𝓕) (n : ℕ) :
    ∀ y ∈ s, b n y ≤ perronSeq e c r b n y := by
  intro y hy
  cases n with
  | zero =>
    rw [perronSeq]
    exact le_surfaceReplace (h𝓕.subharmonic _ (hb 0)) hd y hy
  | succ n =>
    rw [perronSeq]
    refine le_trans (le_max_right (perronSeq e c r b n y) (b (n + 1) y)) ?_
    exact le_surfaceReplace (h𝓕.subharmonic _
      (h𝓕.max_mem _ (perronSeq_mem h𝓕 hd hb n) _ (hb (n + 1)))) hd y hy

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
private theorem perronSeq_le_succ (h𝓕 : IsPerronFamily 𝓕 s)
    (hd : IsReplaceDisk e c r s) (hb : ∀ n, b n ∈ 𝓕) (n : ℕ) :
    ∀ y ∈ s, perronSeq e c r b n y ≤ perronSeq e c r b (n + 1) y := by
  intro y hy
  rw [perronSeq]
  refine le_trans (le_max_left (perronSeq e c r b n y) (b (n + 1) y)) ?_
  exact le_surfaceReplace (h𝓕.subharmonic _
    (h𝓕.max_mem _ (perronSeq_mem h𝓕 hd hb n) _ (hb (n + 1)))) hd y hy

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
private theorem perronSeq_mono (h𝓕 : IsPerronFamily 𝓕 s)
    (hd : IsReplaceDisk e c r s) (hb : ∀ n, b n ∈ 𝓕) {m n : ℕ} (hmn : m ≤ n) :
    ∀ y ∈ s, perronSeq e c r b m y ≤ perronSeq e c r b n y := by
  intro y hy
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hmn ih => exact ih.trans (perronSeq_le_succ h𝓕 hd hb n y hy)

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
private theorem perronSeq_surfaceHarmonicOn (h𝓕 : IsPerronFamily 𝓕 s)
    (hd : IsReplaceDisk e c r s) (hb : ∀ n, b n ∈ 𝓕) (n : ℕ) :
    SurfaceHarmonicOn (perronSeq e c r b n) (e.symm '' ball c r) := by
  cases n with
  | zero =>
    rw [perronSeq]
    exact surfaceReplace_surfaceHarmonicOn (h𝓕.subharmonic _ (hb 0)) hd
  | succ n =>
    rw [perronSeq]
    exact surfaceReplace_surfaceHarmonicOn (h𝓕.subharmonic _
      (h𝓕.max_mem _ (perronSeq_mem h𝓕 hd hb n) _ (hb (n + 1)))) hd

end PerronSeq

/-- **Perron's principle** (Anghel–Stan Theorem 6, Hubbard Prop. 1.2.3): the
upper envelope of a Perron family is harmonic. -/
theorem IsPerronFamily.surfaceHarmonicOn_perronSup {𝓕 : Set (X → ℝ)} {s : Set X}
    (hs : IsOpen s) (h𝓕 : IsPerronFamily 𝓕 s) :
    SurfaceHarmonicOn (perronSup 𝓕) s := by
  refine SurfaceHarmonicOn.of_chartwise fun x hx ↦ ?_
  set e := chartAt ℂ x with he_def
  have he : e ∈ riemannAtlas X := chartAt_mem_riemannAtlas x
  have hxe : x ∈ e.source := mem_chart_source ℂ x
  refine ⟨e, he, hxe, ?_⟩
  -- choose a legal replacement disk around `e x`
  have hmem : e x ∈ chartImage e s := mem_chartImage_of_mem hx hxe
  obtain ⟨r, hr, hcb⟩ := nhds_basis_closedBall.mem_iff.mp
    ((isOpen_chartImage e hs).mem_nhds hmem)
  set c : ℂ := e x with hc_def
  have hd : IsReplaceDisk e c r s :=
    ⟨he, hr, hcb.trans (chartImage_subset_target e s), by
      rintro y ⟨w, hw, rfl⟩
      exact mapsTo_symm_chartImage (hcb hw)⟩
  have hBmem : ∀ w ∈ ball c r, e.symm w ∈ s := fun w hw ↦
    hd.preimage_subset ⟨w, ball_subset_closedBall hw, rfl⟩
  have hball_sub : ball c r ⊆ chartImage e (e.symm '' ball c r) := by
    intro w hw
    have hwt : w ∈ e.target := hd.closedBall_subset (ball_subset_closedBall hw)
    exact ⟨e.symm w, ⟨⟨w, hw, rfl⟩, e.map_target hwt⟩, e.right_inv hwt⟩
  -- unfolded form of the envelope
  have hPS : ∀ y : X, perronSup 𝓕 y = sSup ((fun g ↦ g y) '' 𝓕) := fun y ↦ rfl
  have hPSbdd : ∀ y ∈ s, BddAbove ((fun g ↦ g y) '' 𝓕) := fun y hy ↦
    ⟨1, by rintro v ⟨g', hg', rfl⟩; exact (h𝓕.bounds g' hg' y hy).2⟩
  -- a dense sequence in the disk
  have hnB : Nonempty (ball c r) := ⟨⟨c, mem_ball_self hr⟩⟩
  set zs : ℕ → ℂ := fun j ↦ (TopologicalSpace.denseSeq (ball c r) j : ℂ) with hzs_def
  have hzs_mem : ∀ j, zs j ∈ ball c r := fun j ↦ (TopologicalSpace.denseSeq (ball c r) j).2
  have hzs_dense : ∀ w ∈ ball c r, w ∈ closure (range zs) := by
    intro w hw
    have h1 : (⟨w, hw⟩ : ball c r) ∈ closure (range (TopologicalSpace.denseSeq (ball c r))) :=
      TopologicalSpace.denseRange_denseSeq (ball c r) _
    have h2 : MapsTo (Subtype.val : ball c r → ℂ)
        (range (TopologicalSpace.denseSeq (ball c r))) (range zs) := by
      rintro q ⟨j, rfl⟩
      exact ⟨j, rfl⟩
    exact map_mem_closure continuous_subtype_val h1 h2
  -- near-optimal family members at the dense points
  have hopt : ∀ j n : ℕ, ∃ g ∈ 𝓕,
      perronSup 𝓕 (e.symm (zs j)) - 1 / ((n : ℝ) + 1) < g (e.symm (zs j)) := by
    intro j n
    have h1 : perronSup 𝓕 (e.symm (zs j)) - 1 / ((n : ℝ) + 1)
        < sSup ((fun g ↦ g (e.symm (zs j))) '' 𝓕) := by
      rw [← hPS]
      exact sub_lt_self _ (by positivity)
    obtain ⟨v, ⟨g, hg, rfl⟩, hv⟩ := exists_lt_of_lt_csSup (h𝓕.nonempty.image _) h1
    exact ⟨g, hg, hv⟩
  choose fj hfj𝓕 hfjval using hopt
  -- running maxima of the near-optimal members
  set cseq : ℕ → X → ℝ := fun n ↦ maxUpTo (fun i ↦ fj i n) n with hcseq_def
  have hcseq_mem : ∀ n, cseq n ∈ 𝓕 := fun n ↦ maxUpTo_mem h𝓕 (fun i ↦ hfj𝓕 i n) n
  have hcseq_dom : ∀ j n : ℕ, j ≤ n → ∀ y, fj j n y ≤ cseq n y := by
    intro j n hjn y
    rw [hcseq_def]
    exact le_maxUpTo (f := fun i ↦ fj i n) hjn y
  -- boundedness of the approximating suprema
  have hbddW : ∀ b : ℕ → X → ℝ, (∀ n, b n ∈ 𝓕) → ∀ w ∈ ball c r,
      BddAbove (range fun n ↦ perronSeq e c r b n (e.symm w)) := fun b hb w hw ↦
    ⟨1, by
      rintro v ⟨n, rfl⟩
      exact (h𝓕.bounds _ (perronSeq_mem h𝓕 hd hb n) _ (hBmem w hw)).2⟩
  -- harmonicity of the suprema (Harnack's principle)
  have hWharm : ∀ b : ℕ → X → ℝ, (∀ n, b n ∈ 𝓕) →
      HarmonicOnNhd (fun w ↦ ⨆ n, perronSeq e c r b n (e.symm w)) (ball c r) := by
    intro b hb
    refine harmonicOnNhd_ciSup_of_monotone isOpen_ball (fun n ↦ ?_) ?_ ?_
    · intro w hw
      exact perronSeq_surfaceHarmonicOn h𝓕 hd hb n e he w (hball_sub hw)
    · intro w hw m n hmn
      exact perronSeq_mono h𝓕 hd hb hmn (e.symm w) (hBmem w hw)
    · intro n w hw
      exact h𝓕.bounds _ (perronSeq_mem h𝓕 hd hb n) _ (hBmem w hw)
  -- the suprema are dominated by the Perron envelope
  have hWle : ∀ b : ℕ → X → ℝ, (∀ n, b n ∈ 𝓕) → ∀ w ∈ ball c r,
      (⨆ n, perronSeq e c r b n (e.symm w)) ≤ perronSup 𝓕 (e.symm w) := by
    intro b hb w hw
    refine ciSup_le fun n ↦ ?_
    rw [hPS]
    exact le_csSup (hPSbdd _ (hBmem w hw)) ⟨_, perronSeq_mem h𝓕 hd hb n, rfl⟩
  -- at the dense points, any supremum built from a dominating sequence attains
  -- the envelope
  have hWge : ∀ b : ℕ → X → ℝ, (∀ n, b n ∈ 𝓕) →
      (∀ j n : ℕ, j ≤ n → ∀ y, fj j n y ≤ b n y) → ∀ j : ℕ,
      (⨆ n, perronSeq e c r b n (e.symm (zs j))) = perronSup 𝓕 (e.symm (zs j)) := by
    intro b hb hdom j
    refine le_antisymm (hWle b hb (zs j) (hzs_mem j)) ?_
    by_contra hlt
    push Not at hlt
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
    set m := Max.max j n with hm_def
    have h1 := hfjval j m
    have h2 : fj j m (e.symm (zs j)) ≤ b m (e.symm (zs j)) :=
      hdom j m (le_max_left j n) _
    have h3 : b m (e.symm (zs j)) ≤ perronSeq e c r b m (e.symm (zs j)) :=
      le_perronSeq h𝓕 hd hb m _ (hBmem (zs j) (hzs_mem j))
    have h4 : perronSeq e c r b m (e.symm (zs j))
        ≤ ⨆ k, perronSeq e c r b k (e.symm (zs j)) :=
      le_ciSup (hbddW b hb (zs j) (hzs_mem j)) m
    have h5 : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr (le_max_right j n)
      linarith
    linarith
  -- the supremum for the running-maxima sequence
  have hW₁harm : HarmonicOnNhd (fun w ↦ ⨆ n, perronSeq e c r cseq n (e.symm w))
      (ball c r) := hWharm cseq hcseq_mem
  -- the Perron envelope agrees with this harmonic function on the disk
  have hfinal : ∀ w ∈ ball c r,
      perronSup 𝓕 (e.symm w) = ⨆ n, perronSeq e c r cseq n (e.symm w) := by
    intro w hw
    refine le_antisymm ?_ (hWle cseq hcseq_mem w hw)
    rw [hPS]
    refine csSup_le (h𝓕.nonempty.image _) ?_
    rintro v ⟨g, hg, rfl⟩
    -- the second sequence, dominating both `g` and the first sequence
    have hb₂mem : ∀ n, (fun n' y ↦ Max.max (g y) (cseq n' y)) n ∈ 𝓕 := fun n ↦
      h𝓕.max_mem _ hg _ (hcseq_mem n)
    have hb₂dom : ∀ j n : ℕ, j ≤ n → ∀ y,
        fj j n y ≤ (fun n' y ↦ Max.max (g y) (cseq n' y)) n y := fun j n hjn y ↦
      (hcseq_dom j n hjn y).trans (le_max_right _ _)
    have hW₂harm := hWharm _ hb₂mem
    -- the two suprema agree on the dense sequence, hence at `w`
    have heq : (⨆ n, perronSeq e c r (fun n' y ↦ Max.max (g y) (cseq n' y)) n (e.symm w))
        = ⨆ n, perronSeq e c r cseq n (e.symm w) := by
      have h1 : Tendsto (fun w' ↦ ⨆ n, perronSeq e c r cseq n (e.symm w'))
          (𝓝[range zs] w) (𝓝 (⨆ n, perronSeq e c r cseq n (e.symm w))) :=
        ((hW₁harm w hw).1.continuousAt).continuousWithinAt
      have h2 : Tendsto
          (fun w' ↦ ⨆ n, perronSeq e c r (fun n' y ↦ Max.max (g y) (cseq n' y)) n (e.symm w'))
          (𝓝[range zs] w)
          (𝓝 (⨆ n, perronSeq e c r (fun n' y ↦ Max.max (g y) (cseq n' y)) n (e.symm w))) :=
        ((hW₂harm w hw).1.continuousAt).continuousWithinAt
      have : (𝓝[range zs] w).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hzs_dense w hw)
      have hcongr :
          (fun w' ↦ ⨆ n, perronSeq e c r (fun n' y ↦ Max.max (g y) (cseq n' y)) n (e.symm w'))
          =ᶠ[𝓝[range zs] w] fun w' ↦ ⨆ n, perronSeq e c r cseq n (e.symm w') := by
        filter_upwards [self_mem_nhdsWithin] with w' hw'
        obtain ⟨j, rfl⟩ := hw'
        exact (hWge _ hb₂mem hb₂dom j).trans (hWge cseq hcseq_mem hcseq_dom j).symm
      exact tendsto_nhds_unique (h2.congr' hcongr) h1
    -- `g` is dominated by the second supremum
    have hgle : g (e.symm w)
        ≤ ⨆ n, perronSeq e c r (fun n' y ↦ Max.max (g y) (cseq n' y)) n (e.symm w) := by
      refine le_trans (le_max_left (g (e.symm w)) (cseq 0 (e.symm w))) ?_
      refine le_trans (le_perronSeq h𝓕 hd hb₂mem 0 _ (hBmem w hw)) ?_
      exact le_ciSup (hbddW _ hb₂mem w hw) 0
    exact le_of_le_of_eq hgle heq
  -- conclude via congruence on the open disk
  have hcongr : (perronSup 𝓕 ∘ e.symm) =ᶠ[𝓝 c]
      fun w ↦ ⨆ n, perronSeq e c r cseq n (e.symm w) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with w hw
    exact hfinal w hw
  exact (harmonicAt_congr_nhds hcongr).mpr (hW₁harm c (mem_ball_self hr))

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
theorem IsPerronFamily.le_perronSup {𝓕 : Set (X → ℝ)} {s : Set X}
    (h𝓕 : IsPerronFamily 𝓕 s) {g : X → ℝ} (hg : g ∈ 𝓕) :
    ∀ x ∈ s, g x ≤ perronSup 𝓕 x := fun x hx ↦
  le_csSup ⟨1, fun _ ⟨g', hg', hgx⟩ ↦ hgx ▸ (h𝓕.bounds g' hg' x hx).2⟩ ⟨g, hg, rfl⟩

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
theorem IsPerronFamily.perronSup_le {𝓕 : Set (X → ℝ)} {s : Set X}
    (h𝓕 : IsPerronFamily 𝓕 s) {M : ℝ} {x : X}
    (hM : ∀ g ∈ 𝓕, g x ≤ M) : perronSup 𝓕 x ≤ M :=
  csSup_le (h𝓕.nonempty.image _) fun _ ⟨g, hg, hgx⟩ ↦ hgx ▸ hM g hg

/-- `SubMeanOn` transfers along equality on the domain. -/
theorem subMeanOn_congr {g₁ g₂ : ℂ → ℝ} {s : Set ℂ} (hg : SubMeanOn g₁ s)
    (h : EqOn g₂ g₁ s) : SubMeanOn g₂ s := by
  refine ⟨hg.continuousOn.congr h, fun c r hr hsub ↦ ?_⟩
  have havg : Real.circleAverage g₂ c r = Real.circleAverage g₁ c r := by
    refine Real.circleAverage_congr_sphere fun z hz ↦ ?_
    rw [abs_of_pos hr] at hz
    exact h (hsub (sphere_subset_closedBall hz))
  rw [h (hsub (mem_closedBall_self hr.le)), havg]
  exact hg.submean c r hr hsub

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- `SurfaceSubharmonicOn` transfers along equality on the domain. -/
theorem surfaceSubharmonicOn_congr {g₁ g₂ : X → ℝ} {s : Set X}
    (hg : SurfaceSubharmonicOn g₁ s) (h : EqOn g₂ g₁ s) : SurfaceSubharmonicOn g₂ s := by
  refine ⟨hg.continuousOn.congr h, fun e' he' ↦ ?_⟩
  refine subMeanOn_congr (hg.subMeanOn e' he') ?_
  rintro w ⟨x, ⟨hxs, hxe⟩, rfl⟩
  simp only [Function.comp_apply]
  rw [e'.left_inv hxe]
  exact h hxs

end Rado
