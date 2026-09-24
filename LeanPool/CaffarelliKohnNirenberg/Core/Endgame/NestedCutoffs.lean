/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CutoffDerivatives

/-! # Nested one-sided cutoffs at arbitrary interior radii

A fixed cutoff is one near the closed inner cylinder and has past support
in a larger cylinder. Its domain adaptation agrees with the fixed function
as a germ at every nonpositive time, so all past derivative bounds remain
independent of the domain and of its future-time collar.
-/

@[expose] public section

open Set Metric Filter
open scoped Topology
open CKN.Foundation.Parabolic CKN.Core.Step3

noncomputable section
namespace CKN.Core.Endgame

private theorem compact_raw_cylinder {r : ℝ} (hr : 0 < r) :
    IsCompact (parabolicHomeomorph.symm ⁻¹'
      closure (parabolicCylinder (0 : Vec3) 0 r)) := by
  have hball : IsCompact {x : Vec3 | vec3EuclideanNorm (x - 0) ≤ r} := by
    have h := vec3Homeomorph.isCompact_preimage.mpr
      (isCompact_closedBall (vec3Homeomorph (0 : Vec3)) r)
    convert h using 1
    ext x
    simp only [mem_ofPred_eq, mem_preimage, mem_closedBall,
      vec3Homeomorph_apply, dist_eq_norm, ← WithLp.toLp_sub,
      ← vec3EuclideanNorm_eq_l2]
  rw [closure_parabolicCylinder hr]
  exact hball.prod isCompact_Icc

private theorem smooth_cutoff_near_compact
    {K U : Set (Vec3 × ℝ)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : Vec3 × ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) ∧
      ∀ z ∈ K, χ =ᶠ[𝓝 z] fun _ => 1 := by
  obtain ⟨V, hV, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨W, hW, hVW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure hVc hU hVU
  obtain ⟨χ, hχsmooth, hχrange, hχsupport, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hW isClosed_closure hVW
  have hts : tsupport χ = closure W := by rw [tsupport, hχsupport]
  refine ⟨χ, hχsmooth, ?_, ?_, ?_, ?_⟩
  · rw [HasCompactSupport, hts]
    exact hWc
  · rw [hts]
    exact hWU
  · intro z
    exact hχrange (mem_range_self z)
  · intro z hz
    filter_upwards [hV.mem_nhds (hKV hz)] with w hw
    exact (hχone w).mp (subset_closure hw)

/-- A fixed smooth cutoff is one near the closed radius-`a` cylinder and
has nonpositive-time support in the radius-`b` cylinder, whenever `0<a<b`. -/
theorem exists_fixed_nested_cutoff (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ ψ : Vec3 × ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧
      (∀ z ∈ tsupport ψ, z.1 ∈ vec3Ball (0 : Vec3) b) ∧
      (∀ z, 0 ≤ ψ z ∧ ψ z ≤ 1) ∧
      (∀ z : Vec3 × ℝ,
        parabolicHomeomorph.symm z ∈ closure (parabolicCylinder (0 : Vec3) 0 a) →
        ψ =ᶠ[𝓝 z] fun _ => 1) ∧
      ∀ z ∈ tsupport ψ, z.2 ≤ 0 →
        parabolicHomeomorph.symm z ∈ parabolicCylinder (0 : Vec3) 0 b := by
  let U : Set (Vec3 × ℝ) := vec3Ball (0 : Vec3) b ×ˢ Ioo (-b ^ 2) 1
  have hU : IsOpen U := (isOpen_vec3Ball _ _).prod isOpen_Ioo
  have hKU : parabolicHomeomorph.symm ⁻¹'
      closure (parabolicCylinder (0 : Vec3) 0 a) ⊆ U := by
    intro z hz
    rw [closure_parabolicCylinder ha] at hz
    change vec3EuclideanNorm (z.1 - 0) ≤ a ∧ 0 - a ^ 2 ≤ z.2 ∧ z.2 ≤ 0 at hz
    refine ⟨hz.1.trans_lt hab, ?_, hz.2.2.trans_lt zero_lt_one⟩
    have hs : a ^ 2 < b ^ 2 := sq_lt_sq' (by linarith only [ha, hab]) hab
    change -b ^ 2 < z.2
    linarith only [hs, hz.2.1]
  obtain ⟨ψ, hsmooth, hc, hsupp, hrange, hone⟩ :=
    smooth_cutoff_near_compact (compact_raw_cylinder ha) hU hKU
  refine ⟨ψ, hsmooth, hc, fun z hz => (hsupp hz).1, hrange, hone, ?_⟩
  intro z hz ht
  have hmem := hsupp hz
  change vec3EuclideanNorm (z.1 - 0) < b ∧ 0 - b ^ 2 < z.2 ∧ z.2 ≤ 0
  exact ⟨hmem.1, by simpa only [zero_sub] using hmem.2.1, ht⟩

/-- A nested fixed cutoff can be adapted to any domain containing the
closed unit cylinder, retaining all past germs and a support-containing
local product box. -/
theorem exists_domain_nested_cutoff_with_box (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (ψ : Vec3 × ℝ → ℝ) (hsmooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hspace : ∀ z ∈ tsupport ψ, z.1 ∈ vec3Ball (0 : Vec3) b)
    (hrange : ∀ z, 0 ≤ ψ z ∧ ψ z ≤ 1)
    (hone : ∀ z : Vec3 × ℝ,
      parabolicHomeomorph.symm z ∈ closure (parabolicCylinder (0 : Vec3) 0 a) →
      ψ =ᶠ[𝓝 z] fun _ => 1)
    (hsupp : ∀ z ∈ tsupport ψ, z.2 ≤ 0 →
      parabolicHomeomorph.symm z ∈ parabolicCylinder (0 : Vec3) 0 b)
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    (hunit : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I) :
    ∃ (φ : Vec3 × ℝ → ℝ) (Ω' : Set Vec3) (J : Set ℝ),
      φ ∈ spaceTimeTestFunction (V := ℝ) Ω I ∧
      localBox Ω I Ω' J ∧ tsupport φ ⊆ Ω' ×ˢ J ∧
      (∀ z, 0 ≤ φ z ∧ φ z ≤ 1) ∧
      (∀ z : Vec3 × ℝ,
        parabolicHomeomorph.symm z ∈ closure (parabolicCylinder (0 : Vec3) 0 a) →
        φ =ᶠ[𝓝 z] fun _ => 1) ∧
      (∀ z ∈ tsupport φ, z.2 ≤ 0 →
        parabolicHomeomorph.symm z ∈ parabolicCylinder (0 : Vec3) 0 b) ∧
      (∀ z ∈ tsupport φ, z.1 ∈ vec3Ball (0 : Vec3) b) ∧
      ∀ z : Vec3 × ℝ, z.2 ≤ 0 → φ =ᶠ[𝓝 z] ψ := by
  obtain ⟨Ω', J, hbox, hJ, hunit'⟩ := exists_localBox_around_closed_unit hΩ hI hunit
  have hKU : parabolicHomeomorph.symm ⁻¹'
      closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ Ω' ×ˢ J := fun _ hz => hunit' hz
  obtain ⟨χ, hχsmooth, hχcompact, hχsupport, hχrange, hχone⟩ :=
    smooth_cutoff_near_compact (compact_raw_cylinder (by norm_num : (0 : ℝ) < 1))
      (hbox.1.prod hJ) hKU
  let φ : Vec3 × ℝ → ℝ := fun z => ψ z * χ z
  have hleft : tsupport φ ⊆ tsupport ψ := tsupport_mul_subset_left
  have hright : tsupport φ ⊆ tsupport χ := tsupport_mul_subset_right
  have hagree : ∀ z : Vec3 × ℝ, z.2 ≤ 0 → φ =ᶠ[𝓝 z] ψ := by
    intro z ht
    by_cases hz : z ∈ tsupport ψ
    · have hzunit : parabolicHomeomorph.symm z ∈ closure (parabolicCylinder (0 : Vec3) 0 1) :=
        subset_closure (parabolicCylinder_mono (ha.trans hab).le hb.le (hsupp z hz ht))
      filter_upwards [hχone z hzunit] with w hw
      change ψ w * χ w = ψ w
      rw [hw, mul_one]
    · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hz] with w hw
      have hz0 : ψ w = 0 := image_eq_zero_of_notMem_tsupport hw
      change ψ w * χ w = ψ w
      rw [hz0, zero_mul]
  refine ⟨φ, Ω', J, ⟨hsmooth.mul hχsmooth,
    hχcompact.of_isClosed_subset isClosed_closure hright, ?_⟩,
    hbox, hright.trans hχsupport, ?_, ?_, ?_, fun z hz => hspace z (hleft hz), hagree⟩
  · intro z hz
    have hzbox := hχsupport (hright hz)
    exact ⟨hbox.2.2.1 (subset_closure hzbox.1), hbox.2.2.2.2.2 (subset_closure hzbox.2)⟩
  · intro z
    exact ⟨mul_nonneg (hrange z).1 (hχrange z).1,
      (mul_le_mul_of_nonneg_left (hχrange z).2 (hrange z).1).trans
        (by simpa only [mul_one] using (hrange z).2)⟩
  · intro z hz
    have hzunit := closure_mono (parabolicCylinder_mono ha.le (hab.trans hb).le) hz
    filter_upwards [hone z hz, hχone z hzunit] with w hwψ hwχ
    change ψ w * χ w = 1
    rw [hwψ, hwχ, one_mul]
  · intro z hz ht
    exact hsupp z (hleft hz) ht

/-- One fixed function and one derivative constant work for every domain,
for any nested radii `0<a<b<1`. The future cutoff may depend on the domain. -/
theorem exists_uniform_nested_cutoff_derivative_bound (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    ∃ (ψ : Vec3 × ℝ → ℝ) (C : ℝ), 0 < C ∧
      ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ), IsOpen Ω → IsOpen I →
        closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I →
        ∃ (φ : Vec3 × ℝ → ℝ) (Ω' : Set Vec3) (J : Set ℝ),
          φ ∈ spaceTimeTestFunction (V := ℝ) Ω I ∧
          localBox Ω I Ω' J ∧ tsupport φ ⊆ Ω' ×ˢ J ∧
          (∀ z, 0 ≤ φ z ∧ φ z ≤ 1) ∧
          (∀ z : Vec3 × ℝ,
            parabolicHomeomorph.symm z ∈ closure (parabolicCylinder (0 : Vec3) 0 a) →
            φ =ᶠ[𝓝 z] fun _ => 1) ∧
          (∀ z ∈ tsupport φ, z.2 ≤ 0 →
            parabolicHomeomorph.symm z ∈ parabolicCylinder (0 : Vec3) 0 b) ∧
          (∀ z ∈ tsupport φ, z.1 ∈ vec3Ball (0 : Vec3) b) ∧
          (∀ z : Vec3 × ℝ, z.2 ≤ 0 → φ =ᶠ[𝓝 z] ψ) ∧
          ∀ z : Vec3 × ℝ, z.2 ≤ 0 →
            |φ z| ≤ C ∧ |timePartial φ z| ≤ C ∧
            (∀ i, |spatialPartial φ i z| ≤ C) ∧
            |spatialLaplacian (fun x => φ (x, z.2)) z.1| ≤ C := by
  obtain ⟨ψ, hsmooth, hc, hspace, hrange, hone, hsupp⟩ := exists_fixed_nested_cutoff a b ha hab
  obtain ⟨C, hC, hbound⟩ := exists_cutoff_derivative_bound hsmooth hc
  refine ⟨ψ, C, hC, hsmooth, hc, ?_⟩
  intro Ω I hΩ hI hunit
  obtain ⟨φ, Ω', J, hφ, hbox, hφbox, hφrange, hφone, hφsupp, hφspace, hagree⟩ :=
    exists_domain_nested_cutoff_with_box a b ha hab hb ψ hsmooth hspace hrange hone hsupp hΩ hI hunit
  exact ⟨φ, Ω', J, hφ, hbox, hφbox, hφrange, hφone, hφsupp, hφspace, hagree,
    cutoff_derivative_bound_on_past_of_eventuallyEq hbound hagree⟩

end CKN.Core.Endgame
