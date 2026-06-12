/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.Definitions
import LeanPool.LeanModularForms.ValenceFormula.ModularInvariance

/-!
# Orbit Pairing Lemmas for the Valence Formula

Pure-algebra lemmas about orbit pairings under the modular group actions T (z ↦ z + 1) and
S (z ↦ -1/z). These collapse the explicit coefficient expansion of the valence formula,
pairing left/right vertical and arc contributions.

## Main results

* `sum_ord_rightVert_eq_sum_ord_leftVert`: Orders on right vertical edge equal orders on left.
* `sum_ord_rightArc_eq_sum_ord_leftArc`: Orders on right arc equal orders on left arc.
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular

attribute [local instance] Classical.propDecidable

noncomputable section

private lemma normSq_add_one_eq_of_re_neg_half (z : ℂ) (hre : z.re = -1 / 2) :
    Complex.normSq (z + 1) = Complex.normSq z := by
  simp only [normSq_apply, add_re, one_re, add_im, one_im, add_zero, hre]; ring

private lemma normSq_sub_one_eq_of_re_half (z : ℂ) (hre : z.re = 1 / 2) :
    Complex.normSq (z - 1) = Complex.normSq z := by
  simp only [normSq_apply, sub_re, one_re, sub_im, one_im, sub_zero, hre]; ring

private lemma eq_of_sq_eq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 2 = b ^ 2) : a = b := by
  have h1 : (a - b) * (a + b) = 0 := by nlinarith
  rcases mul_eq_zero.mp h1 with h2 | h2 <;> linarith

private lemma norm_eq_of_normSq_eq {z w : ℂ}
    (h : Complex.normSq z = Complex.normSq w) : ‖z‖ = ‖w‖ :=
  eq_of_sq_eq_of_nonneg (norm_nonneg z) (norm_nonneg w) (by
    have := normSq_eq_norm_sq z; have := normSq_eq_norm_sq w; linarith)

private lemma one_le_normSq_of_norm_gt_one {z : ℂ} (h : ‖z‖ > 1) :
    1 ≤ Complex.normSq z := by
  rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg z]

private lemma normSq_eq_one_of_norm_eq_one {z : ℂ} (h : ‖z‖ = 1) :
    Complex.normSq z = 1 := by
  rw [normSq_eq_norm_sq, h]; norm_num

/-- Coercion identity for T-translation: `((1 : ℝ) +ᵥ p : ℂ) = (p : ℂ) + 1`. -/
lemma vAdd_one_coe (p : ℍ) : ((1 : ℝ) +ᵥ p : ℂ) = (p : ℂ) + 1 := by
  change ((1 : ℝ) : ℂ) + (p : ℂ) = (p : ℂ) + 1; push_cast; ring

/-- T-translation shifts real part by 1. -/
lemma vAdd_one_re (p : ℍ) : ((1 : ℝ) +ᵥ p : ℍ).re = p.re + 1 := by
  change ((1 : ℝ) +ᵥ p : ℂ).re = p.re + 1
  rw [vAdd_one_coe]; simp [add_re]

/-- T-translation preserves imaginary part. -/
lemma vAdd_one_im_eq (p : ℍ) : ((1 : ℝ) +ᵥ p : ℍ).im = p.im := by
  change ((1 : ℝ) +ᵥ p : ℂ).im = p.im
  rw [vAdd_one_coe]; simp [add_im]

/-- T⁻¹-translation coercion: `((-1 : ℝ) +ᵥ p : ℂ) = (p : ℂ) - 1`. -/
lemma vAdd_neg_one_coe (p : ℍ) : ((-1 : ℝ) +ᵥ p : ℂ) = (p : ℂ) - 1 := by
  change ((-1 : ℝ) : ℂ) + (p : ℂ) = (p : ℂ) - 1; push_cast; ring

/-- T⁻¹-translation shifts real part by -1. -/
lemma vAdd_neg_one_re (p : ℍ) : ((-1 : ℝ) +ᵥ p : ℍ).re = p.re - 1 := by
  change ((-1 : ℝ) +ᵥ p : ℂ).re = p.re - 1
  rw [vAdd_neg_one_coe]; simp [sub_re]

/-- T⁻¹-translation preserves imaginary part. -/
lemma vAdd_neg_one_im_eq (p : ℍ) : ((-1 : ℝ) +ᵥ p : ℍ).im = p.im := by
  change ((-1 : ℝ) +ᵥ p : ℂ).im = p.im
  rw [vAdd_neg_one_coe]; simp [sub_im]

/-- T-translation preserves norm for left-vertical points (`re = -1/2`). -/
lemma norm_add_one_eq_of_re_neg_half (z : ℂ) (hre : z.re = -1 / 2) :
    ‖z + 1‖ = ‖z‖ :=
  norm_eq_of_normSq_eq (normSq_add_one_eq_of_re_neg_half z hre)

/-- T⁻¹-translation preserves norm for right-vertical points (`re = 1/2`). -/
lemma norm_sub_one_eq_of_re_half (z : ℂ) (hre : z.re = 1 / 2) :
    ‖z - 1‖ = ‖z‖ :=
  norm_eq_of_normSq_eq (normSq_sub_one_eq_of_re_half z hre)

/-- T-translation preserves norm for UpperHalfPlane points with `re = -1/2`. -/
lemma vAdd_one_norm_eq_of_re_neg_half (p : ℍ) (hre : (p : ℂ).re = -1 / 2) :
    ‖((1 : ℝ) +ᵥ p : ℂ)‖ = ‖(p : ℂ)‖ := by
  rw [vAdd_one_coe]; exact norm_add_one_eq_of_re_neg_half _ hre

/-- T⁻¹-translation preserves norm for UpperHalfPlane points with `re = 1/2`. -/
lemma vAdd_neg_one_norm_eq_of_re_half (p : ℍ) (hre : (p : ℂ).re = 1 / 2) :
    ‖((-1 : ℝ) +ᵥ p : ℂ)‖ = ‖(p : ℂ)‖ := by
  rw [vAdd_neg_one_coe]; exact norm_sub_one_eq_of_re_half _ hre

/-- T-translation sends left-vertical FD points to 𝒟. -/
theorem vAdd_one_mem_fd_of_left_vert (p : ℍ) (hp_fd : p ∈ 𝒟) (hre : (p : ℂ).re = -1 / 2) :
    (1 : ℝ) +ᵥ p ∈ 𝒟 := by
  obtain ⟨hnormSq, _⟩ := hp_fd
  refine ⟨?_, ?_⟩
  · rw [vAdd_one_coe, normSq_add_one_eq_of_re_neg_half _ hre]
    exact hnormSq
  · change |((1 : ℝ) +ᵥ p : ℂ).re| ≤ 1 / 2
    rw [vAdd_one_coe, add_re, one_re, hre]; norm_num

/-- T⁻¹-translation sends right-vertical FD points to 𝒟. -/
theorem vAdd_neg_one_mem_fd_of_right_vert (p : ℍ) (hp_fd : p ∈ 𝒟) (hre : (p : ℂ).re = 1 / 2) :
    (-1 : ℝ) +ᵥ p ∈ 𝒟 := by
  obtain ⟨hnormSq, _⟩ := hp_fd
  refine ⟨?_, ?_⟩
  · rw [vAdd_neg_one_coe, normSq_sub_one_eq_of_re_half _ hre]; exact hnormSq
  · change |((-1 : ℝ) +ᵥ p : ℂ).re| ≤ 1 / 2
    rw [vAdd_neg_one_coe, sub_re, one_re, hre]; norm_num

/-- `(1 : ℝ) +ᵥ ρ' = ρ'+1` as UpperHalfPlane elements. -/
theorem vAdd_one_rho_eq_rho_plus_one : (1 : ℝ) +ᵥ ellipticPointRho' = ellipticPointRhoPlusOne' := by
  apply UpperHalfPlane.ext
  rw [vAdd_one_coe]
  exact ellipticPointRho_add_one_eq

/-- `(-1 : ℝ) +ᵥ (ρ'+1) = ρ'` as UpperHalfPlane elements. -/
theorem vAdd_neg_one_rho_plus_one_eq_rho :
    (-1 : ℝ) +ᵥ ellipticPointRhoPlusOne' = ellipticPointRho' := by
  apply UpperHalfPlane.ext
  rw [vAdd_neg_one_coe, sub_eq_iff_eq_add]
  exact ellipticPointRho_add_one_eq.symm

/-- ρ+1 is in the standard fundamental domain 𝒟. -/
theorem ellipticPointRhoPlusOne_mem_fd : ellipticPointRhoPlusOne' ∈ 𝒟 := by
  rw [← vAdd_one_rho_eq_rho_plus_one]
  exact vAdd_one_mem_fd_of_left_vert ellipticPointRho' ellipticPointRho_mem_fd
    (by simp [ellipticPointRho'])

variable {k : ℤ} (f : ModularForm (Gamma 1) k)

/-- `ord(f, ρ+1) = ord(f, ρ)` via the T-translation identity. -/
theorem ord_rho_plus_one_eq_ord_rho_via_vAdd :
    orderOfVanishingAt' (⇑f) ellipticPointRhoPlusOne' =
    orderOfVanishingAt' (⇑f) ellipticPointRho' := by
  rw [← vAdd_one_rho_eq_rho_plus_one]
  exact ord_add_one_eq f ellipticPointRho'

/-- S-action coe: `(S·z : ℂ) = (-z)⁻¹`. -/
lemma S_smul_coe (p : ℍ) : ((ModularGroup.S • p : ℍ) : ℂ) = (-(p : ℂ))⁻¹ := by
  rw [UpperHalfPlane.modular_S_smul]

/-- S-action preserves norm on the unit circle. -/
theorem S_smul_norm_of_unit (p : ℍ) (hp : ‖(p : ℂ)‖ = 1) :
    ‖((ModularGroup.S • p : ℍ) : ℂ)‖ = 1 := by
  rw [S_smul_coe, norm_inv, norm_neg, hp, inv_one]

/-- S-action negates real part on the unit circle. -/
theorem S_smul_re_neg_of_unit (p : ℍ) (hp : ‖(p : ℂ)‖ = 1) :
    (ModularGroup.S • p : ℍ).re = -p.re := by
  have hns := normSq_eq_one_of_norm_eq_one hp
  change ((ModularGroup.S • p : ℍ) : ℂ).re = -p.re
  rw [S_smul_coe]
  simp only [Complex.inv_re, Complex.neg_re,
    Complex.normSq_neg, hns, div_one]; rfl

/-- S-action preserves 𝒟 for unit-circle points. -/
theorem S_smul_mem_fd_of_unit (p : ℍ) (hp_fd : p ∈ 𝒟) (hp_norm : ‖(p : ℂ)‖ = 1) :
    ModularGroup.S • p ∈ 𝒟 := by
  obtain ⟨_, habs_re⟩ := hp_fd
  have hns : Complex.normSq (p : ℂ) = 1 := normSq_eq_one_of_norm_eq_one hp_norm
  refine ⟨?_, ?_⟩
  · rw [S_smul_coe, map_inv₀, Complex.normSq_neg, hns, inv_one]
  · change |((ModularGroup.S • p : ℍ) : ℂ).re| ≤ 1 / 2
    simp only [S_smul_coe, Complex.inv_re, Complex.neg_re,
      Complex.normSq_neg, hns, div_one, abs_neg]
    exact habs_re

/-- The left-vertical filter of S: points with `re = -1/2` and `‖p‖ > 1`. -/
def sLeftVert (S : Finset ℍ) : Finset ℍ :=
  S.filter (fun p => (p : ℂ).re = -1/2 ∧ ‖(p : ℂ)‖ > 1)

/-- The right-vertical filter of S: points with `re = 1/2` and `‖p‖ > 1`. -/
def sRightVert (S : Finset ℍ) : Finset ℍ :=
  S.filter (fun p => (p : ℂ).re = 1/2 ∧ ‖(p : ℂ)‖ > 1)

/-- T-translation maps `sLeftVert S` into `sRightVert S`. -/
theorem vAdd_one_leftVert_subset_rightVert (S : Finset ℍ)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    ∀ p ∈ sLeftVert S,
      orderOfVanishingAt' (⇑f) p ≠ 0 → (1 : ℝ) +ᵥ p ∈ sRightVert S := by
  intro p hp hord
  simp only [sLeftVert, Finset.mem_filter] at hp
  obtain ⟨_, hre, hnorm⟩ := hp
  have hp_fd : p ∈ 𝒟 := by
    refine ⟨one_le_normSq_of_norm_gt_one hnorm, ?_⟩
    rw [show p.re = (p : ℂ).re from rfl, hre]; norm_num
  have hp1_fd := vAdd_one_mem_fd_of_left_vert p hp_fd hre
  have hp1_ord : orderOfVanishingAt' (⇑f) ((1 : ℝ) +ᵥ p) ≠ 0 := by
    rwa [ord_add_one_eq f p]
  have hp1_in_S := hS_complete _ hp1_fd hp1_ord
  simp only [sRightVert, Finset.mem_filter]
  refine ⟨hp1_in_S, ?_, ?_⟩
  · change ((1 : ℝ) +ᵥ p : ℂ).re = 1 / 2
    rw [vAdd_one_coe, add_re, one_re]; linarith [hre]
  · show ‖((1 : ℝ) +ᵥ p : ℂ)‖ > 1
    rw [vAdd_one_norm_eq_of_re_neg_half p hre]; exact hnorm

/-- Left-vertical sum equals sum of T-translated orders. -/
theorem sum_ord_leftVert_eq_sum_T_image (S : Finset ℍ) :
    ∑ p ∈ sLeftVert S, (orderOfVanishingAt' (⇑f) p : ℂ) =
    ∑ p ∈ sLeftVert S, (orderOfVanishingAt' (⇑f) ((1 : ℝ) +ᵥ p) : ℂ) :=
  Finset.sum_congr rfl fun p _ => by rw [ord_add_one_eq f p]

/-- T⁻¹-invariance of vanishing order: `ord(f, (-1)+ᵥp) = ord(f, p)`. -/
lemma ord_vAdd_neg_one_eq (p : ℍ) :
    orderOfVanishingAt' (⇑f) ((-1 : ℝ) +ᵥ p) = orderOfVanishingAt' (⇑f) p := by
  have h := ord_add_one_eq f ((-1 : ℝ) +ᵥ p)
  rw [show (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ p) = p from by
    ext; change ((1 : ℝ) : ℂ) + (((-1 : ℝ) : ℂ) + (p : ℂ)) = (p : ℂ)
    push_cast; ring] at h
  exact h.symm

/-- The left-arc filter: points on the unit circle with negative real part. -/
def sLeftArc (S : Finset ℍ) : Finset ℍ :=
  S.filter (fun p => ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0)

/-- The right-arc filter: points on the unit circle with positive real part. -/
def sRightArc (S : Finset ℍ) : Finset ℍ :=
  S.filter (fun p => ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re > 0)

private lemma S_mul_S : ModularGroup.S * ModularGroup.S = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [ModularGroup.S]

/-- S² acts as the identity on ℍ. -/
lemma S_smul_S_smul (p : ℍ) : ModularGroup.S • (ModularGroup.S • p) = p := by
  rw [← mul_smul, S_mul_S]
  apply UpperHalfPlane.ext
  simp only [ModularGroup.SL_neg_smul, one_smul]

/-- The S-action is injective on ℍ. -/
lemma S_smul_injective : Function.Injective (ModularGroup.S • · : ℍ → ℍ) :=
  Function.HasLeftInverse.injective ⟨(ModularGroup.S • ·), S_smul_S_smul⟩

private lemma ord_ne_zero_of_cast_ne_zero {p : ℍ} {f : ℍ → ℂ}
    (h : (orderOfVanishingAt' f p : ℂ) ≠ 0) :
    orderOfVanishingAt' f p ≠ 0 := by exact_mod_cast h

/-- Orders on right vertical edge equal orders on left vertical edge. -/
theorem sum_ord_rightVert_eq_sum_ord_leftVert (S : Finset ℍ)
    (hS : ∀ p ∈ S, p ∈ 𝒟) (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    ∑ p ∈ sRightVert S, (orderOfVanishingAt' (⇑f) p : ℂ) =
    ∑ p ∈ sLeftVert S, (orderOfVanishingAt' (⇑f) p : ℂ) := by
  rw [← Finset.sum_filter_ne_zero, ← Finset.sum_filter_ne_zero (s := sLeftVert S)]
  apply Finset.sum_nbij ((-1 : ℝ) +ᵥ ·)
  · intro p hp
    have ⟨hp_rv, hord⟩ := Finset.mem_filter.mp hp
    have ⟨hp_S, hre, hnorm⟩ := Finset.mem_filter.mp hp_rv
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨
      hS_complete _ (vAdd_neg_one_mem_fd_of_right_vert p (hS p hp_S) hre)
        (by rw [ord_vAdd_neg_one_eq f p]; exact ord_ne_zero_of_cast_ne_zero hord),
      ?_, ?_⟩, ?_⟩
    · change ((-1 : ℝ) +ᵥ p : ℂ).re = -1 / 2
      rw [vAdd_neg_one_coe, sub_re, one_re, hre]; norm_num
    · show ‖((-1 : ℝ) +ᵥ p : ℂ)‖ > 1
      rw [vAdd_neg_one_norm_eq_of_re_half p hre]; exact hnorm
    · rw [ord_vAdd_neg_one_eq f p]; exact hord
  · exact fun _ _ _ _ h => vadd_left_cancel (-1 : ℝ) h
  · intro q hq
    have ⟨hq_lv, hord⟩ := Finset.mem_filter.mp hq
    have ⟨hq_S, hre, hnorm⟩ := Finset.mem_filter.mp hq_lv
    refine ⟨(1 : ℝ) +ᵥ q, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨
      hS_complete _ (vAdd_one_mem_fd_of_left_vert q (hS q hq_S) hre)
        (by rw [ord_add_one_eq f q]; exact ord_ne_zero_of_cast_ne_zero hord),
      ?_, ?_⟩, ?_⟩, ?_⟩
    · change ((1 : ℝ) +ᵥ q : ℂ).re = 1 / 2
      rw [vAdd_one_coe, add_re, one_re, hre]; norm_num
    · show ‖((1 : ℝ) +ᵥ q : ℂ)‖ > 1
      rw [vAdd_one_norm_eq_of_re_neg_half q hre]; exact hnorm
    · rw [ord_add_one_eq f q]; exact hord
    · change (-1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ q) = q
      rw [← add_vadd, show (-1 : ℝ) + 1 = 0 from by ring, zero_vadd]
  · intro p _; rw [ord_vAdd_neg_one_eq f p]

/-- Orders on right arc equal orders on left arc (via S-action). -/
theorem sum_ord_rightArc_eq_sum_ord_leftArc (S : Finset ℍ) (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    ∑ p ∈ sRightArc S, (orderOfVanishingAt' (⇑f) p : ℂ) =
    ∑ p ∈ sLeftArc S, (orderOfVanishingAt' (⇑f) p : ℂ) := by
  rw [← Finset.sum_filter_ne_zero, ← Finset.sum_filter_ne_zero (s := sLeftArc S)]
  apply Finset.sum_nbij (ModularGroup.S • ·)
  · intro p hp
    have ⟨hp_ra, hord⟩ := Finset.mem_filter.mp hp
    have ⟨hp_S, hnorm, hre_pos⟩ := Finset.mem_filter.mp hp_ra
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨
      hS_complete _ (S_smul_mem_fd_of_unit p (hS p hp_S) hnorm)
        (by rw [ord_S_eq f p]; exact ord_ne_zero_of_cast_ne_zero hord),
      S_smul_norm_of_unit p hnorm, ?_⟩, ?_⟩
    · change (ModularGroup.S • p : ℍ).re < 0
      rw [S_smul_re_neg_of_unit p hnorm, show p.re = (p : ℂ).re from rfl]; linarith
    · rw [ord_S_eq f p]; exact hord
  · exact S_smul_injective.injOn
  · intro q hq
    have ⟨hq_la, hord⟩ := Finset.mem_filter.mp hq
    have ⟨hq_S, hnorm, hre_neg⟩ := Finset.mem_filter.mp hq_la
    refine ⟨ModularGroup.S • q, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨
      hS_complete _ (S_smul_mem_fd_of_unit q (hS q hq_S) hnorm)
        (by rw [ord_S_eq f q]; exact ord_ne_zero_of_cast_ne_zero hord),
      S_smul_norm_of_unit q hnorm, ?_⟩, ?_⟩, S_smul_S_smul q⟩
    · change (ModularGroup.S • q : ℍ).re > 0
      rw [S_smul_re_neg_of_unit q hnorm, show q.re = (q : ℂ).re from rfl]; linarith
    · rw [ord_S_eq f q]; exact hord
  · intro p _; rw [ord_S_eq f p]

end
