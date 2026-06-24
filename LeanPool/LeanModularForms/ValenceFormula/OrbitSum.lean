/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.OrbitPairing
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

/-!
# Orbit-Sum Form of the Valence Formula

`orderOfVanishingAt'` is invariant under the full modular group SL(2, ℤ). We define `ordOrbit`
on orbits and establish finite support for the orbit sum.

## Main Results

* `ord_smul_eq` — `orderOfVanishingAt' f (g • p) = orderOfVanishingAt' f p`
* `Orbit`, `ordOrbit`, `ordOrbit_mk` — well-defined lift to orbits
* `NonEllOrbit` — orbits distinct from `oi` and `orho`
* `finite_support_ordOrbit` — finitely many orbits have nonzero `ordOrbit`
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k)

/-- `orderOfVanishingAt'` is invariant under the action of any `g ∈ SL(2, ℤ)`. -/
theorem ord_smul_eq (g : SL(2, ℤ)) (p : ℍ) :
    orderOfVanishingAt' (⇑f) (g • p) = orderOfVanishingAt' (⇑f) p := by
  have hg_mem : g ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    rw [SpecialLinearGroup.SL2Z_generators]; exact Subgroup.mem_top g
  suffices h : ∀ q : ℍ, orderOfVanishingAt' (⇑f) (g • q) =
      orderOfVanishingAt' (⇑f) q from h p
  revert g hg_mem
  intro g hg_mem
  induction hg_mem using Subgroup.closure_induction with
  | mem x hx =>
    intro q
    rcases hx with rfl | rfl
    · exact ord_S_eq f q
    · rw [UpperHalfPlane.modular_T_smul]; exact ord_add_one_eq f q
  | one =>
    intro q; simp [one_smul]
  | mul x y _ _ ihx ihy =>
    intro q; rw [mul_smul, ihx (y • q)]; exact ihy q
  | inv x _ ihx =>
    intro q; have := ihx (x⁻¹ • q); rw [smul_inv_smul] at this; exact this.symm

/-- The type of orbits of `SL(2, ℤ)` acting on `ℍ`. -/
abbrev Orbit := MulAction.orbitRel.Quotient SL(2, ℤ) ℍ

/-- The canonical map from `ℍ` to its orbit. -/
def orb (p : ℍ) : Orbit := Quotient.mk'' p

/-- The order of vanishing lifted to orbits. Well-defined by `ord_smul_eq`. -/
def ordOrbit (q : Orbit) : ℤ :=
  Quotient.liftOn' q (fun p => orderOfVanishingAt' (⇑f) p) (fun a b hab => by
      rw [MulAction.orbitRel_apply] at hab
      obtain ⟨g, hg⟩ := hab
      rw [← hg]; exact ord_smul_eq f g b)

@[simp]
theorem ordOrbit_mk (p : ℍ) : ordOrbit f (orb p) = orderOfVanishingAt' (⇑f) p := rfl

/-- The orbit of `i`. -/
def oi : Orbit := orb ellipticPointI'

/-- The orbit of `ρ`. -/
def orho : Orbit := orb ellipticPointRho'

/-- A non-elliptic orbit is one distinct from both `oi` and `orho`. -/
def NonEllOrbit := {q : Orbit // q ≠ oi ∧ q ≠ orho}

/-- Every orbit has a representative in the fundamental domain `𝒟`. -/
theorem orbit_has_fd_rep (q : Orbit) : ∃ p : ℍ, orb p = q ∧ p ∈ 𝒟 := by
  induction q using Quotient.inductionOn' with
  | h z =>
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
    refine ⟨g • z, ?_, hg⟩
    exact Quotient.sound' ⟨g, rfl⟩

private theorem G_analyticAt (p : ℍ) :
    AnalyticAt ℂ (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (p : ℂ) := by
  have h_diffOn : DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex) {w | 0 < w.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp f.holo'
  apply analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds p.im_pos] with w hw
  have h_eq : ∀ᶠ u in 𝓝 w, (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) u =
        (f ∘ UpperHalfPlane.ofComplex) u := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hw] with u hu
    simp only [Function.comp_apply, dif_pos hu, UpperHalfPlane.ofComplex_apply_of_im_pos hu]
  exact ((h_diffOn w hw).differentiableAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hw)).congr_of_eventuallyEq h_eq

private theorem G_eval_eq_f (p : ℍ) :
    (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (p : ℂ) = f p := by
  simp only []
  split_ifs with h
  · congr 1
  · exact absurd p.im_pos h

/-- If `f p ≠ 0`, then `orderOfVanishingAt' f p = 0`. -/
theorem orderOfVanishingAt'_eq_zero_of_ne_zero' (p : ℍ) (hp : f p ≠ 0) :
    orderOfVanishingAt' f p = 0 := by
  unfold orderOfVanishingAt'
  have h_nf : MeromorphicNFAt _ (p : ℂ) := (G_analyticAt f p).meromorphicNFAt
  have hGp : (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (p : ℂ) ≠ 0 :=
    G_eval_eq_f f p ▸ hp
  rw [h_nf.meromorphicOrderAt_eq_zero_iff.mpr hGp]; rfl

/-- `orderOfVanishingAt' f p ≠ 0` implies `f p = 0`. -/
theorem eq_zero_of_orderOfVanishingAt'_ne_zero' (p : ℍ)
    (hp : orderOfVanishingAt' (⇑f) p ≠ 0) : f p = 0 :=
  by_contra fun h => hp (orderOfVanishingAt'_eq_zero_of_ne_zero' f p h)

/-- `f ≠ 0` and `f p = 0` implies `orderOfVanishingAt' f p ≠ 0`. -/
theorem orderOfVanishingAt'_ne_zero_of_eq_zero (hf : f ≠ 0) (p : ℍ) (hp : f p = 0) :
    orderOfVanishingAt' (⇑f) p ≠ 0 := by
  unfold orderOfVanishingAt'
  intro h_untop_eq
  have h_nf : MeromorphicNFAt _ (p : ℂ) :=
    (G_analyticAt f p).meromorphicNFAt
  have h_ord_ne : meromorphicOrderAt
      (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (↑p) ≠ (0 : WithTop ℤ) := by
    intro h0; apply h_nf.meromorphicOrderAt_eq_zero_iff.mp h0
    split_ifs with h
    · exact_mod_cast hp
    · exact absurd p.im_pos h
  have h_top := (WithTop.untop₀_eq_zero.mp h_untop_eq).resolve_left h_ord_ne
  rw [meromorphicOrderAt_eq_top_iff] at h_top
  have h_analOn : AnalyticOnNhd ℂ (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0)
      {w | 0 < w.im} := fun w hw => G_analyticAt f ⟨w, hw⟩
  have h_preconn : IsPreconnected {w : ℂ | 0 < w.im} :=
    ((convex_halfSpace_im_gt 0).isConnected ⟨I, by simp [I_im]⟩).isPreconnected
  apply hf; ext z
  change f z = 0
  exact (G_eval_eq_f f z).symm.trans
    (h_analOn.eqOn_zero_of_preconnected_of_frequently_eq_zero
      h_preconn p.im_pos h_top.frequently z.im_pos)

private theorem modularFormCompOfComplex_eq' (p : ℍ) :
    modularFormCompOfComplex f (p : ℂ) = f p := by
  simp [modularFormCompOfComplex, UpperHalfPlane.ofComplex_apply_of_im_pos p.im_pos]

theorem fd_im_gt_half (p : ℍ) (hp : p ∈ 𝒟) : (1 : ℝ)/2 < (p : ℂ).im := by
  by_contra h_le; push Not at h_le
  obtain ⟨hnormSq, habs_re⟩ := hp
  have hre_bridge : UpperHalfPlane.re p = (↑p : ℂ).re := rfl
  have him_bridge : p.im = (↑p : ℂ).im := rfl
  have h_nsq : 1 ≤ (p : ℂ).re * (p : ℂ).re + (p : ℂ).im * (p : ℂ).im := by
    have := normSq_apply (↑p : ℂ); linarith [this]
  have h_re_sq : (p : ℂ).re * (p : ℂ).re ≤ 1/4 := by
    have hre := abs_le.mp habs_re
    nlinarith [mul_self_nonneg (p : ℂ).re, hre_bridge]
  have him_sq : (p : ℂ).im * (p : ℂ).im ≤ 1/4 := by nlinarith [p.im_pos, him_bridge]
  linarith

private theorem no_zeros_above_height' (hf : f ≠ 0) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ (p : ℍ), H₀ ≤ (p : ℂ).im → f p ≠ 0 := by
  obtain ⟨H₀, hH₀_gt, hH₀_nonvan⟩ := exists_height_cusp_nonvanishing f hf
  refine ⟨H₀, hH₀_gt, fun p hp hfp => ?_⟩
  have h_eq := SlashInvariantFormClass.eq_cuspFunction f p
      (by simp) one_ne_zero
  have h_qParam_mem : Function.Periodic.qParam (1 : ℝ) (↑p : ℂ) ∈
      Metric.closedBall (0 : ℂ) (Real.exp (-2 * Real.pi * H₀)) := by
    rw [Metric.mem_closedBall, dist_zero_right, Function.Periodic.norm_qParam]
    simpa only [div_one] using Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have h_qParam_ne : Function.Periodic.qParam (1 : ℝ) (↑p : ℂ) ≠ 0 := by
    simpa only [Function.Periodic.qParam, ne_eq] using Complex.exp_ne_zero _
  exact hH₀_nonvan _ h_qParam_mem h_qParam_ne (h_eq ▸ hfp)

/-- The set of zeros (with nonzero order) in `𝒟` is finite. -/
theorem finite_zeros_in_fd (hf : f ≠ 0) :
    Set.Finite {p : ℍ | p ∈ 𝒟 ∧ orderOfVanishingAt' (⇑f) p ≠ 0} := by
  apply Set.Finite.subset (s := {p : ℍ | p ∈ 𝒟 ∧ f p = 0})
  swap
  · intro p ⟨hp_fd, hp_ord⟩
    exact ⟨hp_fd, eq_zero_of_orderOfVanishingAt'_ne_zero' f p hp_ord⟩
  obtain ⟨H₀, hH₀_gt, hH₀_no_zeros⟩ := no_zeros_above_height' f hf
  have hM_half : (1 : ℝ)/2 < H₀ + 1 := by
    linarith [Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 3)]
  have h_fin := modularForm_finitely_many_zeros_in_fdBox f hf hM_half
  have h_coe_inj : Function.Injective (UpperHalfPlane.coe : ℍ → ℂ) :=
    fun _ _ h => UpperHalfPlane.ext_iff.mpr h
  apply (h_fin.preimage (h_coe_inj.injOn)).subset
  intro p ⟨hp_fd, hp_zero⟩
  change (p : ℂ) ∈ {z ∈ fdBox (H₀ + 1) | modularFormCompOfComplex f z = 0}
  have habs_re := hp_fd.2
  have him_gt := fd_im_gt_half p hp_fd
  have hre_bridge : UpperHalfPlane.re p = (↑p : ℂ).re := rfl
  have hre := abs_le.mp habs_re
  constructor
  · simp only [fdBox, Set.mem_setOf_eq]
    refine ⟨by linarith [hre_bridge], by linarith [hre_bridge], him_gt, ?_⟩
    by_contra h_ge; push Not at h_ge
    have : H₀ ≤ (↑p : ℂ).im := by linarith
    exact absurd hp_zero (hH₀_no_zeros p this)
  · exact (modularFormCompOfComplex_eq' f p).symm ▸ hp_zero

/-- The set of orbits with nonzero `ordOrbit` is finite. -/
theorem finite_support_ordOrbit (hf : f ≠ 0) :
    Set.Finite {q : Orbit | ordOrbit f q ≠ 0} := by
  choose rep hrep using fun q : Orbit => orbit_has_fd_rep q
  set S := {q : Orbit | ordOrbit f q ≠ 0}
  have h_image : rep '' S ⊆
      {p : ℍ | p ∈ 𝒟 ∧ orderOfVanishingAt' (⇑f) p ≠ 0} := by
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨(hrep q).2, by rw [← ordOrbit_mk f (rep q), (hrep q).1]; exact hq⟩
  have h_inj : Set.InjOn rep S := by
    intro q₁ _ q₂ _ h
    have : orb (rep q₁) = orb (rep q₂) := congrArg orb h
    rw [(hrep q₁).1, (hrep q₂).1] at this; exact this
  exact (finite_zeros_in_fd f hf).subset h_image |>.of_finite_image h_inj

/-- The set of non-elliptic orbits with nonzero `ordOrbit` is finite. -/
theorem finite_support_ordOrbit_nonEll (hf : f ≠ 0) :
    Set.Finite {q : NonEllOrbit | ordOrbit f q.val ≠ 0} := by
  apply Set.Finite.subset ((finite_support_ordOrbit f hf).preimage
      (fun (a : NonEllOrbit) _ (b : NonEllOrbit) _ h =>
        Subtype.val_injective h))
  intro ⟨q, hq_ne⟩ hq_ord
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at hq_ord ⊢
  exact hq_ord

/-- The canonical finite set of zeros (with nonzero order) in `𝒟`. -/
noncomputable def s₀ (hf : f ≠ 0) : Finset ℍ := (finite_zeros_in_fd f hf).toFinset

/-- Every point in `s₀` lies in the fundamental domain `𝒟`. -/
theorem s₀_mem_fd (hf : f ≠ 0) : ∀ p ∈ s₀ f hf, p ∈ 𝒟 := by
  intro p hp; rw [s₀, Set.Finite.mem_toFinset] at hp; exact hp.1

/-- `s₀` captures all points in `𝒟` with nonzero order of vanishing. -/
theorem s₀_complete (hf : f ≠ 0) :
    ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ s₀ f hf := by
  intro p hp hord; rw [s₀, Set.Finite.mem_toFinset]; exact ⟨hp, hord⟩

/-- The orbit of `ρ+1` equals the orbit of `ρ`. -/
theorem orb_rho_plus_one_eq_orb_rho :
    orb ellipticPointRhoPlusOne' = (orho : Orbit) := by
  change Quotient.mk'' ellipticPointRhoPlusOne' = Quotient.mk'' ellipticPointRho'
  rw [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨ModularGroup.T, by
    rw [UpperHalfPlane.modular_T_smul]; ext
    simp [ellipticPointRho', ellipticPointRhoPlusOne', UpperHalfPlane.coe_vadd]; ring⟩

end
