/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.DivergenceFreeSlice
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.TsupportSpatialBox
public import Mathlib.Topology.Bases
public import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Slices

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

/-- The slice divergence identity holds simultaneously for every member of any
countable family of admissible spatial test functions. -/
theorem divfree_slice_weak_countable
    {Ω : Set Vec3} {I : Set ℝ} {u : ParabolicPoint → Vec3}
    (hS2 : ∀ ψ : Vec3 × ℝ → ℝ, ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I →
      IntegrableOn (fun z => ∑ i, u z i * spatialPartial ψ i z) (tsupport ψ) volume ∧
      ∫ z in spaceTimeSet Ω I, ∑ i, u z i * spatialPartial ψ i z = 0)
    (hI : IsOpen I) {C : Set (Vec3 → ℝ)} (hC : C.Countable)
    (hCtest : ∀ ψ ∈ C, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ Ω) :
    ∀ᵐ s ∂volume.restrict I, ∀ ψ ∈ C,
      ∫ x in Ω, ∑ i, u (x, s) i * (fderiv ℝ ψ x) (basisVec i) = 0 := by
  haveI : Countable {ψ // ψ ∈ C} := hC.to_subtype
  have hsub : ∀ᵐ s ∂volume.restrict I, ∀ ψ : C,
      ∫ x in Ω, ∑ i, u (x, s) i * (fderiv ℝ ψ x) (basisVec i) = 0 := by
    rw [ae_all_iff]
    intro ψ
    obtain ⟨hψ, hψc, hψΩ⟩ := hCtest ψ ψ.property
    exact divfree_slice_weak hS2 hI ψ hψ hψc hψΩ
  filter_upwards [hsub] with s hs ψ hψ
  exact hs ⟨ψ, hψ⟩

private theorem fderiv_zero_outside_support {ψ : Vec3 → ℝ} {K : Set Vec3}
    (hK : tsupport ψ ⊆ K) {x : Vec3} (hx : x ∉ K) :
    fderiv ℝ ψ x = 0 := by
  have hx' : x ∉ tsupport ψ := fun hmem => hx (hK hmem)
  have hev : ψ =ᶠ[𝓝 x] (fun _ : Vec3 => (0 : ℝ)) :=
    Filter.eventually_of_mem ((isClosed_tsupport ψ).isOpen_compl.mem_nhds hx')
      (fun y hy => by
        by_contra hne
        exact hy (subset_tsupport ψ (Function.mem_support.mpr hne)))
  rw [Filter.EventuallyEq.fderiv_eq hev, fderiv_const_apply]

private theorem exists_time_radius {I : Set ℝ} (hI : IsOpen I) {s : ℝ}
    (hs : s ∈ I) : ∃ r : ℝ, 0 < r ∧ closedBall s r ⊆ I := by
  obtain ⟨ε, hε, hεI⟩ := Metric.mem_nhds_iff.mp (hI.mem_nhds hs)
  refine ⟨ε / 2, by linarith only [hε], ?_⟩
  exact (closedBall_subset_ball (by linarith only [hε])).trans hεI

/-- For a fixed compactly supported smooth test function, the local weak-gradient
clause of a suitable weak solution holds for almost every time in the full
interval, after integrating by parts on the fixed spatial support. -/
theorem weakGradient_slice_ae_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (h : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψΩ : tsupport ψ ⊆ Ω) :
    ∀ᵐ s ∂volume.restrict I, ∀ i j : Fin 3,
      ∫ x in Ω, u (x, s) i * (fderiv ℝ ψ x) (basisVec j) =
        -∫ x in Ω, Du (x, s) i j * ψ x := by
  classical
  rcases h with ⟨hΩ, hI, _hIord, _hq, _hf, hdata, _hS2, _hS3, _hS4⟩
  obtain ⟨Ω', hΩ'open, hKΩ', hΩ'compact, hΩ'Ω⟩ :=
    CKN.exists_spatial_box_of_tsupport_subset hΩ hψΩ hψc
  let r : ℝ → ℝ := fun s => if hs : s ∈ I then
    Classical.choose (exists_time_radius hI hs) else 1
  have hr_pos : ∀ s ∈ I, 0 < r s := by
    intro s hs
    simp only [r, dite_eq_left hs]
    exact (Classical.choose_spec (exists_time_radius hI hs)).1
  have hr_sub : ∀ s ∈ I, closedBall s (r s) ⊆ I := by
    intro s hs
    simp only [r, dite_eq_left hs]
    exact (Classical.choose_spec (exists_time_radius hI hs)).2
  let V : ℝ → Set ℝ := fun s => ball s (r s)
  obtain ⟨T, hTsub, hTcount, hcover⟩ :=
    TopologicalSpace.countable_cover_nhdsWithin
      (s := I) (f := V) (by
        intro s hs
        refine mem_nhdsWithin.mpr ⟨V s, isOpen_ball, mem_ball_self (hr_pos s hs), ?_⟩
        exact inter_subset_left)
  have hlocal : ∀ s ∈ T, ∀ᵐ t ∂volume.restrict (closedBall s (r s)),
      ∀ i j : Fin 3,
        ∫ x in Ω, u (x, t) i * (fderiv ℝ ψ x) (basisVec j) =
          -∫ x in Ω, Du (x, t) i j * ψ x := by
    intro s hs
    have hsI : s ∈ I := hTsub hs
    let J : Set ℝ := closedBall s (r s)
    have hJsub : J ⊆ I := hr_sub s hsI
    have hJcompact : IsCompact (closure J) := by
      rw [Metric.closure_closedBall]
      exact ProperSpace.isCompact_closedBall s (r s)
    have hJord : J.OrdConnected := by
      rw [show J = Icc (s - r s) (s + r s) by
        ext t
        simp only [J, mem_closedBall, Real.dist_eq, mem_Icc, abs_le]
        constructor
        · rintro ⟨h₁, h₂⟩
          constructor <;> linarith only [h₁, h₂]
        · rintro ⟨h₁, h₂⟩
          constructor <;> linarith only [h₁, h₂]]
      exact ordConnected_Icc
    have hJsub' : closure J ⊆ I := by
      simpa only [J, Metric.closure_closedBall] using hJsub
    have hbox : localBox Ω I Ω' J := by
      exact ⟨hΩ'open, hΩ'compact, hΩ'Ω, hJord, hJcompact, hJsub'⟩
    have hgrad : ∀ i : Fin 3, ∀ᵐ t ∂volume.restrict J,
        HasWeakGradientOn Ω' (fun x => u (x, t) i)
          (fun x => Du (x, t) i) :=
      (hdata Ω' J hbox).2.2.2.2.2.2.2.2
    have hgrad_all : ∀ᵐ t ∂volume.restrict J, ∀ i j : Fin 3,
        HasWeakPartialDerivOn Ω' j (fun x => u (x, t) i)
          (fun x => Du (x, t) i j) := by
      rw [ae_all_iff]
      intro i
      rw [ae_all_iff]
      intro j
      filter_upwards [hgrad i] with t ht
      exact ht j
    filter_upwards [hgrad_all] with t ht i j
    have hw := ht i j ψ hψ hψc hKΩ'
    have hu_zero_Ω : ∀ x ∉ Ω,
        u (x, t) i * (fderiv ℝ ψ x) (basisVec j) = 0 := by
      intro x hx
      rw [fderiv_zero_outside_support hψΩ hx]
      simp only [zero_apply, mul_zero]
    have hu_zero_Ω' : ∀ x ∉ Ω',
        u (x, t) i * (fderiv ℝ ψ x) (basisVec j) = 0 := by
      intro x hx
      rw [fderiv_zero_outside_support hKΩ' hx]
      simp only [zero_apply, mul_zero]
    have hDu_zero_Ω : ∀ x ∉ Ω, Du (x, t) i j * ψ x = 0 := by
      intro x hx
      have hxK : x ∉ tsupport ψ := fun hx' => hx (hψΩ hx')
      simp only [image_eq_zero_of_notMem_tsupport hxK, mul_zero]
    have hDu_zero_Ω' : ∀ x ∉ Ω', Du (x, t) i j * ψ x = 0 := by
      intro x hx
      have hxK : x ∉ tsupport ψ := fun hx' => hx (hKΩ' hx')
      simp only [image_eq_zero_of_notMem_tsupport hxK, mul_zero]
    calc
      ∫ x in Ω, u (x, t) i * (fderiv ℝ ψ x) (basisVec j) =
          ∫ x in Ω', u (x, t) i * (fderiv ℝ ψ x) (basisVec j) := by
            rw [setIntegral_eq_integral_of_forall_compl_eq_zero hu_zero_Ω,
              setIntegral_eq_integral_of_forall_compl_eq_zero hu_zero_Ω']
      _ = -∫ x in Ω', Du (x, t) i j * ψ x := hw
      _ = -∫ x in Ω, Du (x, t) i j * ψ x := by
            rw [setIntegral_eq_integral_of_forall_compl_eq_zero hDu_zero_Ω,
              setIntegral_eq_integral_of_forall_compl_eq_zero hDu_zero_Ω']
  have hlocal_ball : ∀ s ∈ T, ∀ᵐ t ∂volume.restrict (V s),
      ∀ i j : Fin 3,
        ∫ x in Ω, u (x, t) i * (fderiv ℝ ψ x) (basisVec j) =
          -∫ x in Ω, Du (x, t) i j * ψ x := by
    intro s hs
    exact ae_restrict_of_ae_restrict_of_subset
      Metric.ball_subset_closedBall (hlocal s hs)
  have hunion : ∀ᵐ t ∂volume.restrict (⋃ s ∈ T, V s),
      ∀ i j : Fin 3,
        ∫ x in Ω, u (x, t) i * (fderiv ℝ ψ x) (basisVec j) =
          -∫ x in Ω, Du (x, t) i j * ψ x :=
    (ae_restrict_biUnion_iff V hTcount _).2 hlocal_ball
  exact ae_restrict_of_ae_restrict_of_subset hcover hunion

end CKN
