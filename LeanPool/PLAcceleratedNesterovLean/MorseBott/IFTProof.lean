/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.MorseBott.Defs
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Implicit Function Theorem Application

Proves `ift_gives_graph`: under Hessian coercivity on the normal space,
the critical set near x₀ is locally a C¹ graph over ker(Hess f(x₀)).
-/

open Filter Topology Metric Submodule Asymptotics

noncomputable section

namespace PLAcceleratedNesterovLean


variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- Restriction of fderiv to a submodule as a CLM into ℝ
private def restrictToN (N : Submodule ℝ E) :
    (E →L[ℝ] ℝ) →L[ℝ] (↥N →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ ↥N E ℝ).flip N.subtypeL

omit [FiniteDimensional ℝ E] in
@[simp]
private lemma restrictToN_apply (N : Submodule ℝ E) (L : E →L[ℝ] ℝ) (w : ↥N) :
    restrictToN N L w = L ↑w := by
  simp only [restrictToN, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply]

omit [FiniteDimensional ℝ E] in
private lemma restrictToN_eq_zero_iff (N : Submodule ℝ E) (L : E →L[ℝ] ℝ) :
    restrictToN N L = 0 ↔ ∀ w : ↥N, L ↑w = 0 := by
  constructor
  · intro h w
    have := ContinuousLinearMap.ext_iff.mp h w
    rwa [restrictToN_apply, zero_apply] at this
  · intro h; ext w
    rw [restrictToN_apply, zero_apply]
    exact h w

private lemma isInvertible_of_bijective_finiteDimensional
    {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
    (L : A →L[ℝ] B) (hL : Function.Bijective L) :
    L.IsInvertible := by
  refine ⟨(LinearEquiv.ofBijective L.toLinearMap ?_).toContinuousLinearEquiv, ?_⟩
  · exact hL
  · ext x
    rfl

omit [FiniteDimensional ℝ E] in
private lemma comp_inl_eq_zero_of_ker
    {T N : Submodule ℝ E}
    (compR : (E →L[ℝ] ℝ) →L[ℝ] (↥N →L[ℝ] ℝ))
    (ι : ↥T × ↥N →L[ℝ] E)
    (H : E →L[ℝ] E →L[ℝ] ℝ)
    (hcompR : ∀ (L : E →L[ℝ] ℝ) (w : ↥N), compR L w = L ↑w)
    (hι_inl : ∀ (t : ↥T), ι (t, 0) = ↑t)
    (hker : ∀ t : ↥T, H (↑t) = 0) :
    (compR.comp (H.comp ι)).comp
      (ContinuousLinearMap.inl ℝ ↥T ↥N) = 0 := by
  ext ⟨t, ht⟩ w
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    zero_apply]
  rw [hι_inl, hker ⟨t, ht⟩, hcompR, zero_apply]

-- Helper: if F(t, φ(t)) is locally zero and F'∘inl = 0 and F'∘inr is injective, then Dφ(0) = 0
private lemma fderiv_eq_zero_of_locally_const_comp
    {A B C : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    {F : A × B → C} {F' : A × B →L[ℝ] C}
    {φ : A → B}
    (hF_hfd : HasFDerivAt F F' (0, 0))
    (hφ_diff : DifferentiableAt ℝ φ 0)
    (hφ_zero : φ 0 = 0)
    (hF'_inl_zero : F'.comp (ContinuousLinearMap.inl ℝ A B) = 0)
    (hF_inj : Function.Injective (F'.comp (ContinuousLinearMap.inr ℝ A B)))
    (hcomp_eq : ∀ᶠ t in 𝓝 (0 : A), F (t, φ t) = 0) :
    fderiv ℝ φ 0 = 0 := by
  have hcomp_fderiv : fderiv ℝ (fun t => F (t, φ t)) 0 = 0 := by
    have h : (fun t => F (t, φ t)) =ᶠ[𝓝 0] fun _ => (0 : C) := hcomp_eq
    rw [h.fderiv_eq]; simp only [fderiv_fun_const, Pi.zero_apply]
  have hpair : HasFDerivAt (fun t => (t, φ t))
      ((ContinuousLinearMap.id ℝ A).prod (fderiv ℝ φ 0)) 0 :=
    (hasFDerivAt_id (0 : A)).prodMk hφ_diff.hasFDerivAt
  have hF_hfd' : HasFDerivAt F F' ((0 : A), φ (0 : A)) := by
    rw [hφ_zero]; exact hF_hfd
  have hchain := hF_hfd'.comp (0 : A) hpair
  have hkey : F'.comp ((ContinuousLinearMap.id ℝ A).prod (fderiv ℝ φ 0)) = 0 := by
    rw [← hchain.fderiv]; exact hcomp_fderiv
  ext dt
  have h1 := ContinuousLinearMap.ext_iff.mp hkey dt
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply] at h1
  have h2 : F' (ContinuousLinearMap.inl ℝ A B dt) +
            F' (ContinuousLinearMap.inr ℝ A B (fderiv ℝ φ 0 dt)) = 0 := by
    rw [← F'.map_add]
    convert h1 using 1
    simp only [ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.inr_apply,
      Prod.mk_add_mk, add_zero, zero_add,
      ContinuousLinearMap.coe_id', id_eq]
  have h3 : F' (ContinuousLinearMap.inl ℝ A B dt) = 0 := by
    have := ContinuousLinearMap.ext_iff.mp hF'_inl_zero dt
    simp only [ContinuousLinearMap.comp_apply, zero_apply] at this
    exact this
  rw [h3, zero_add] at h2
  have h4 : fderiv ℝ φ 0 dt = 0 :=
    hF_inj (by simp only [ContinuousLinearMap.comp_apply, map_zero]; exact h2)
  simp only [h4, zero_apply]

-- Needed: nlinarith/linarith proofs exceed default heartbeat limit
lemma ift_gives_graph_impl (f : E → ℝ) (μ : ℝ) (x₀ : E) (hμ : 0 < μ)
    (hf : ContDiffAt ℝ 2 f x₀)
    (hgrad : fderiv ℝ f x₀ = 0)
    (hcoer : ∀ v ∈ (hessianKer f x₀).orthogonal,
      hessian f x₀ v v ≥ μ * ‖v‖ ^ 2) :
    ∃ (U : Set E) (_ : U ∈ 𝓝 x₀)
      (φ : (hessianKer f x₀) → (hessianKer f x₀).orthogonal),
      ContDiffAt ℝ 1 φ 0 ∧ φ 0 = 0 ∧ fderiv ℝ φ 0 = 0 ∧
      ∀ x ∈ U,
        (∀ w : (hessianKer f x₀).orthogonal, fderiv ℝ f x (w : E) = 0) ↔
        (orthogonalProjectionOnto (hessianKer f x₀).orthogonal (x - x₀) : E) =
          ((φ (orthogonalProjectionOnto (hessianKer f x₀) (x - x₀))) : E) := by
  set T := hessianKer f x₀ with hT_def
  set N := T.orthogonal with hN_def
  set H := hessian f x₀ with hH_def
  haveI : CompleteSpace ↥T := FiniteDimensional.complete ℝ ↥T
  haveI : CompleteSpace ↥N := FiniteDimensional.complete ℝ ↥N
  haveI : CompleteSpace (↥N →L[ℝ] ℝ) := FiniteDimensional.complete ℝ _
  -- ═══ The product-decomposition map F : T × N → (N →L[ℝ] ℝ) ═══
  let compR := (ContinuousLinearMap.compL ℝ ↥N E ℝ).flip N.subtypeL
  have hcompR_eq : ∀ (L : E →L[ℝ] ℝ) (w : ↥N), compR L w = L ↑w :=
    fun L w => restrictToN_apply N L w
  let ι := T.subtypeL.coprod N.subtypeL
  let F : ↥T × ↥N → (↥N →L[ℝ] ℝ) := fun p => compR (fderiv ℝ f (x₀ + ι p))
  let F' := compR.comp (H.comp ι)
  have hι0 : ι (0 : ↥T × ↥N) = 0 := by
    simp only [ι, map_zero]
  -- F(0,0) = 0
  have hF0 : F (0, 0) = 0 := by
    change compR (fderiv ℝ f (x₀ + ι (0, 0))) = 0
    rw [show ι (0, 0) = (0 : E) from hι0, add_zero, hgrad, map_zero]
  -- HasFDerivAt F F' (0,0)
  have hF_hfd : HasFDerivAt F F' (0, 0) := by
    change HasFDerivAt (compR ∘ fun p : ↥T × ↥N => fderiv ℝ f (x₀ + ι p))
      (compR.comp (H.comp ι)) (0 : ↥T × ↥N)
    have h_aff : HasFDerivAt (fun p : ↥T × ↥N => x₀ + ι p) ι (0, 0) := by
      have := (hasFDerivAt_const x₀ (0 : ↥T × ↥N)).add ι.hasFDerivAt
      rwa [zero_add] at this
    have hfdr : ContDiffAt ℝ 1 (fderiv ℝ f) x₀ :=
      hf.fderiv_right (by norm_cast : (1 : WithTop ℕ∞) + 1 ≤ 2)
    have h_fdr : HasFDerivAt (fderiv ℝ f) H x₀ :=
      (hfdr.differentiableAt one_ne_zero).hasFDerivAt
    have h_fdr' : HasFDerivAt (fderiv ℝ f) H (x₀ + ι (0 : ↥T × ↥N)) := by
      rwa [hι0, add_zero]
    have h_comp1 : HasFDerivAt (fun p => fderiv ℝ f (x₀ + ι p)) (H.comp ι) (0, 0) :=
      h_fdr'.comp (0 : ↥T × ↥N) h_aff
    exact compR.hasFDerivAt.comp (0 : ↥T × ↥N) h_comp1
  -- ContDiffAt
  have hF_cda : ContDiffAt ℝ 1 F (0, 0) := by
    change ContDiffAt ℝ 1 (fun p => compR (fderiv ℝ f (x₀ + ι p))) (0, 0)
    have hfdr : ContDiffAt ℝ 1 (fderiv ℝ f) x₀ :=
      hf.fderiv_right (by norm_cast : (1 : WithTop ℕ∞) + 1 ≤ 2)
    have h1 : ContDiffAt ℝ 1 (fun p => fderiv ℝ f (x₀ + ι p)) (0, 0) := by
      have hfdr_at : ContDiffAt ℝ 1 (fderiv ℝ f) (x₀ + ι (0 : ↥T × ↥N)) := by
        rw [hι0, add_zero]; exact hfdr
      apply ContDiffAt.comp (f := fun p : ↥T × ↥N => x₀ + ι p)
      · exact hfdr_at
      · exact (contDiff_const.add ι.contDiff).contDiffAt
    exact compR.contDiff.contDiffAt.comp _ h1
  -- Helper: the map n ↦ F'(0,n) is injective (from coercivity)
  have hF_inj : Function.Injective (F'.comp (ContinuousLinearMap.inr ℝ ↥T ↥N)) := by
    intro n₁ n₂ heq
    have h0 : (F'.comp (ContinuousLinearMap.inr ℝ ↥T ↥N)) (n₁ - n₂) = 0 := by
      rw [map_sub, heq, sub_self]
    have hmem : (↑(n₁ - n₂) : E) ∈ N := Submodule.sub_mem _ n₁.2 n₂.2
    -- Evaluate F'(0, n₁-n₂) at the element ⟨↑(n₁-n₂), hmem⟩ ∈ N
    have heval : (F'.comp (ContinuousLinearMap.inr ℝ ↥T ↥N)) (n₁ - n₂)
        ⟨↑(n₁ - n₂), hmem⟩ = 0 := by rw [h0]; rfl
    -- Unfold F' to extract H(↑(n₁-n₂))(↑(n₁-n₂))
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] at heval
    -- heval : (F' (0, n₁ - n₂)) ⟨↑(n₁ - n₂), hmem⟩ = 0
    -- F' = compR.comp (H.comp ι), need to unfold this
    change compR (H (ι (0, n₁ - n₂))) ⟨↑(n₁ - n₂), hmem⟩ = 0 at heval
    simp only [ι, ContinuousLinearMap.coprod_apply, Submodule.subtypeL_apply, map_zero,
      zero_add] at heval
    -- Simplify compR application
    rw [show compR = restrictToN N from rfl, restrictToN_apply] at heval
    -- heval : H(↑(n₁-n₂))(↑(n₁-n₂)) = 0
    have hcoer' := hcoer (↑(n₁ - n₂)) hmem
    have h_norm : ‖(↑(n₁ - n₂) : E)‖ = 0 := by
      by_contra h_ne
      have h_pos : (0 : ℝ) < ‖(↑(n₁ - n₂) : E)‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm h_ne)
      have h1 := hcoer'
      rw [heval] at h1
      linarith [mul_pos hμ (pow_pos h_pos 2)]
    have h_sub_zero : n₁ - n₂ = 0 := by
      apply_fun ((↑) : ↥N → E) using Subtype.coe_injective
      simpa using norm_eq_zero.mp h_norm
    exact sub_eq_zero.mp h_sub_zero
  -- Bijectivity of F'.comp(inr)
  have hF_bij : Function.Bijective (F'.comp (ContinuousLinearMap.inr ℝ ↥T ↥N)) := by
    refine ⟨hF_inj, ?_⟩
    have hdim : Module.finrank ℝ ↥N = Module.finrank ℝ (↥N →L[ℝ] ℝ) :=
      (InnerProductSpace.toDual ℝ ↥N).toLinearEquiv.finrank_eq
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hF_inj
  -- ═══ Apply the implicit function theorem ═══
  have hF_right_inv : (F'.comp (ContinuousLinearMap.inr ℝ ↥T ↥N)).IsInvertible :=
    isInvertible_of_bijective_finiteDimensional
      (F'.comp (ContinuousLinearMap.inr ℝ ↥T ↥N)) hF_bij
  have hF_partial_inv :
      (fderiv ℝ F (0, 0) ∘L ContinuousLinearMap.inr ℝ ↥T ↥N).IsInvertible := by
    rw [hF_hfd.fderiv]
    exact hF_right_inv
  set φ := hF_cda.implicitFunction one_ne_zero hF_partial_inv with hφ_def
  -- Properties of φ
  have hφ_smooth : ContDiffAt ℝ 1 φ 0 := by
    rw [hφ_def]
    exact hF_cda.contDiffAt_implicitFunction one_ne_zero hF_partial_inv
  have hφ_zero : φ 0 = 0 := by
    rw [hφ_def]
    exact hF_cda.implicitFunction_apply_self one_ne_zero hF_partial_inv
  -- F' ∘ inl = 0 (since T = ker(H))
  have hF'_inl_zero : F'.comp (ContinuousLinearMap.inl ℝ ↥T ↥N) = 0 := by
    have hker : ∀ t : ↥T, H (↑t) = 0 := by
      intro ⟨t, ht⟩
      have : t ∈ hessianKer f x₀ := ht
      rwa [hessianKer, LinearMap.mem_ker] at this
    have hι_inl : ∀ (t : ↥T), ι (t, (0 : ↥N)) = (↑t : E) := by
      intro t
      simp only [ι, ContinuousLinearMap.coprod_apply, Submodule.subtypeL_apply,
        map_zero, add_zero]
    exact comp_inl_eq_zero_of_ker compR ι H hcompR_eq hι_inl hker
  -- Dφ(0) = 0
  have hφ_deriv : fderiv ℝ φ 0 = 0 := by
    have hcomp_eq : ∀ᶠ t in 𝓝 (0 : ↥T), F (t, φ t) = 0 :=
      (by
        rw [hφ_def]
        exact (hF_cda.eventually_apply_implicitFunction one_ne_zero hF_partial_inv).mono
          fun _ ht => ht.trans hF0)
    exact fderiv_eq_zero_of_locally_const_comp hF_hfd
      (hφ_smooth.differentiableAt one_ne_zero) hφ_zero
      hF'_inl_zero hF_inj hcomp_eq
  -- ═══ Projection maps and their continuity ═══
  have hproj_fst : Filter.Tendsto
      (fun x : E => (orthogonalProjectionOnto T (x - x₀) : ↥T)) (𝓝 x₀) (𝓝 0) := by
    rw [show (0 : ↥T) =
      orthogonalProjectionOnto T ((x₀ : E) - x₀) from by
        simp only [sub_self, map_zero]]
    exact ((orthogonalProjectionOnto T).continuous.comp
      (continuous_id.sub continuous_const)).continuousAt
  have hproj_snd : Filter.Tendsto
      (fun x : E => (orthogonalProjectionOnto N (x - x₀) : ↥N)) (𝓝 x₀) (𝓝 0) := by
    rw [show (0 : ↥N) =
      orthogonalProjectionOnto N ((x₀ : E) - x₀) from by
        simp only [sub_self, map_zero]]
    exact ((orthogonalProjectionOnto N).continuous.comp
      (continuous_id.sub continuous_const)).continuousAt
  have hproj_tend : Filter.Tendsto
      (fun x : E => (orthogonalProjectionOnto T (x - x₀),
                      orthogonalProjectionOnto N (x - x₀)))
      (𝓝 x₀) (𝓝 (0, 0)) := by
    exact hproj_fst.prodMk_nhds hproj_snd
  -- ═══ Orthogonal decomposition ═══
  have h_decomp : ∀ x : E, x₀ + ι (orthogonalProjectionOnto T (x - x₀),
      orthogonalProjectionOnto N (x - x₀)) = x := by
    intro x
    simp only [ι, ContinuousLinearMap.coprod_apply, Submodule.subtypeL_apply]
    -- ↑(πT(x-x₀)) + ↑(πN(x-x₀)) = x - x₀
    have h : (↑(orthogonalProjectionOnto T (x - x₀)) : E) +
        ↑(orthogonalProjectionOnto N (x - x₀)) = x - x₀ :=
      T.starProjection_add_starProjection_orthogonal (x - x₀)
    rw [h]; abel
  -- ═══ The iff characterization ═══
  have h_fwd_local :
      ∀ᶠ p in 𝓝 (0 : ↥T × ↥N), F p = F (0, 0) ↔ φ p.1 = p.2 := by
    rw [hφ_def]
    exact hF_cda.eventually_apply_eq_iff_implicitFunction one_ne_zero hF_partial_inv
  have h_bwd_local : ∀ᶠ t in 𝓝 (0 : ↥T), F (t, φ t) = F (0, 0) := by
    rw [hφ_def]
    exact hF_cda.eventually_apply_implicitFunction one_ne_zero hF_partial_inv
  have h_fwd := hproj_tend.eventually h_fwd_local
  have h_bwd := hproj_fst.eventually h_bwd_local
  have h_iff : ∀ᶠ x in 𝓝 x₀,
      (∀ w : ↥N, fderiv ℝ f x (↑w) = 0) ↔
      (orthogonalProjectionOnto N (x - x₀) : E) =
        (φ (orthogonalProjectionOnto T (x - x₀)) : E) := by
    filter_upwards [h_fwd, h_bwd] with x hfwd hbwd
    rw [hF0] at hfwd hbwd
    constructor
    · intro hvanish
      have hFx : F (orthogonalProjectionOnto T (x - x₀),
          orthogonalProjectionOnto N (x - x₀)) = 0 := by
        change compR (fderiv ℝ f (x₀ + ι (orthogonalProjectionOnto T (x - x₀),
          orthogonalProjectionOnto N (x - x₀)))) = 0
        rw [h_decomp]
        exact (restrictToN_eq_zero_iff N (fderiv ℝ f x)).mpr hvanish
      exact congrArg Subtype.val (hfwd.mp hFx).symm
    · intro heq
      have h_eq_N : orthogonalProjectionOnto N (x - x₀) =
          φ (orthogonalProjectionOnto T (x - x₀)) := Subtype.val_injective heq
      intro w
      have hFx := hbwd
      change F (orthogonalProjectionOnto T (x - x₀),
        φ (orthogonalProjectionOnto T (x - x₀))) = 0 at hFx
      rw [← h_eq_N] at hFx
      have hFx' : compR (fderiv ℝ f (x₀ + ι (orthogonalProjectionOnto T (x - x₀),
          orthogonalProjectionOnto N (x - x₀)))) = 0 := hFx
      rw [h_decomp] at hFx'
      exact (restrictToN_eq_zero_iff N (fderiv ℝ f x)).mp hFx' w
  obtain ⟨U, hU, hUprop⟩ := h_iff.exists_mem
  exact ⟨U, hU, φ, hφ_smooth, hφ_zero, hφ_deriv, fun x hx => hUprop x hx⟩

/-- C³ version: when `f` is C³ at `x₀`, the IFT gives a C² graph. -/
lemma ift_gives_graph_impl₂ (f : E → ℝ) (μ : ℝ) (x₀ : E) (hμ : 0 < μ)
    (hf : ContDiffAt ℝ 3 f x₀)
    (hgrad : fderiv ℝ f x₀ = 0)
    (hcoer : ∀ v ∈ (hessianKer f x₀).orthogonal,
      hessian f x₀ v v ≥ μ * ‖v‖ ^ 2) :
    ∃ (U : Set E) (_ : U ∈ 𝓝 x₀)
      (φ : (hessianKer f x₀) → (hessianKer f x₀).orthogonal),
      ContDiffAt ℝ 2 φ 0 ∧ φ 0 = 0 ∧ fderiv ℝ φ 0 = 0 ∧
      ∀ x ∈ U,
        (∀ w : (hessianKer f x₀).orthogonal, fderiv ℝ f x (w : E) = 0) ↔
        (orthogonalProjectionOnto (hessianKer f x₀).orthogonal (x - x₀) : E) =
          ((φ (orthogonalProjectionOnto (hessianKer f x₀) (x - x₀))) : E) := by
  set T := hessianKer f x₀ with hT_def
  set N := T.orthogonal with hN_def
  set H := hessian f x₀ with hH_def
  haveI : CompleteSpace ↥T := FiniteDimensional.complete ℝ ↥T
  haveI : CompleteSpace ↥N := FiniteDimensional.complete ℝ ↥N
  haveI : CompleteSpace (↥N →L[ℝ] ℝ) := FiniteDimensional.complete ℝ _
  let compR := (ContinuousLinearMap.compL ℝ ↥N E ℝ).flip N.subtypeL
  have hcompR_eq : ∀ (L : E →L[ℝ] ℝ) (w : ↥N), compR L w = L ↑w :=
    fun L w => restrictToN_apply N L w
  let ι := T.subtypeL.coprod N.subtypeL
  let F : ↥T × ↥N → (↥N →L[ℝ] ℝ) := fun p => compR (fderiv ℝ f (x₀ + ι p))
  let F' := compR.comp (H.comp ι)
  have hι0 : ι (0 : ↥T × ↥N) = 0 := by
    simp only [ι, map_zero]
  have hF0 : F (0, 0) = 0 := by
    change compR (fderiv ℝ f (x₀ + ι (0, 0))) = 0
    rw [show ι (0, 0) = (0 : E) from hι0, add_zero, hgrad, map_zero]
  have hF_hfd : HasFDerivAt F F' (0, 0) := by
    change HasFDerivAt (compR ∘ fun p : ↥T × ↥N => fderiv ℝ f (x₀ + ι p))
      (compR.comp (H.comp ι)) (0 : ↥T × ↥N)
    have h_aff : HasFDerivAt (fun p : ↥T × ↥N => x₀ + ι p) ι (0, 0) := by
      have := (hasFDerivAt_const x₀ (0 : ↥T × ↥N)).add ι.hasFDerivAt
      rwa [zero_add] at this
    have hfdr : ContDiffAt ℝ 2 (fderiv ℝ f) x₀ :=
      hf.fderiv_right (by norm_cast : (2 : WithTop ℕ∞) + 1 ≤ 3)
    have h_fdr : HasFDerivAt (fderiv ℝ f) H x₀ :=
      (hfdr.differentiableAt (by norm_cast : (2 : WithTop ℕ∞) ≠ 0)).hasFDerivAt
    have h_fdr' : HasFDerivAt (fderiv ℝ f) H (x₀ + ι (0 : ↥T × ↥N)) := by
      rwa [hι0, add_zero]
    have h_comp1 : HasFDerivAt (fun p => fderiv ℝ f (x₀ + ι p)) (H.comp ι) (0, 0) :=
      h_fdr'.comp (0 : ↥T × ↥N) h_aff
    exact compR.hasFDerivAt.comp (0 : ↥T × ↥N) h_comp1
  have hF_cda : ContDiffAt ℝ 2 F (0, 0) := by
    change ContDiffAt ℝ 2 (fun p => compR (fderiv ℝ f (x₀ + ι p))) (0, 0)
    have hfdr : ContDiffAt ℝ 2 (fderiv ℝ f) x₀ :=
      hf.fderiv_right (by norm_cast : (2 : WithTop ℕ∞) + 1 ≤ 3)
    have h1 : ContDiffAt ℝ 2 (fun p => fderiv ℝ f (x₀ + ι p)) (0, 0) := by
      have hfdr_at : ContDiffAt ℝ 2 (fderiv ℝ f) (x₀ + ι (0 : ↥T × ↥N)) := by
        rw [hι0, add_zero]
        exact hfdr
      apply ContDiffAt.comp (f := fun p : ↥T × ↥N => x₀ + ι p)
      · exact hfdr_at
      · exact (contDiff_const.add ι.contDiff).contDiffAt
    exact compR.contDiff.contDiffAt.comp _ h1
  have hF_inj : Function.Injective (F'.comp (ContinuousLinearMap.inr ℝ ↥T ↥N)) := by
    intro n₁ n₂ heq
    have h0 : (F'.comp (ContinuousLinearMap.inr ℝ ↥T ↥N)) (n₁ - n₂) = 0 := by
      rw [map_sub, heq, sub_self]
    have hmem : (↑(n₁ - n₂) : E) ∈ N := Submodule.sub_mem _ n₁.2 n₂.2
    have heval : (F'.comp (ContinuousLinearMap.inr ℝ ↥T ↥N)) (n₁ - n₂)
        ⟨↑(n₁ - n₂), hmem⟩ = 0 := by rw [h0]; rfl
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] at heval
    change compR (H (ι (0, n₁ - n₂))) ⟨↑(n₁ - n₂), hmem⟩ = 0 at heval
    simp only [ι, ContinuousLinearMap.coprod_apply, Submodule.subtypeL_apply, map_zero,
      zero_add] at heval
    rw [show compR = restrictToN N from rfl, restrictToN_apply] at heval
    have hcoer' := hcoer (↑(n₁ - n₂)) hmem
    have h_norm : ‖(↑(n₁ - n₂) : E)‖ = 0 := by
      by_contra h_ne
      have h_pos : (0 : ℝ) < ‖(↑(n₁ - n₂) : E)‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm h_ne)
      have h1 := hcoer'
      rw [heval] at h1
      linarith [mul_pos hμ (pow_pos h_pos 2)]
    have h_sub_zero : n₁ - n₂ = 0 := by
      apply_fun ((↑) : ↥N → E) using Subtype.coe_injective
      simpa using norm_eq_zero.mp h_norm
    exact sub_eq_zero.mp h_sub_zero
  have hF_bij : Function.Bijective (F'.comp (ContinuousLinearMap.inr ℝ ↥T ↥N)) := by
    refine ⟨hF_inj, ?_⟩
    have hdim : Module.finrank ℝ ↥N = Module.finrank ℝ (↥N →L[ℝ] ℝ) :=
      (InnerProductSpace.toDual ℝ ↥N).toLinearEquiv.finrank_eq
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hF_inj
  have hF_right_inv : (F'.comp (ContinuousLinearMap.inr ℝ ↥T ↥N)).IsInvertible :=
    isInvertible_of_bijective_finiteDimensional
      (F'.comp (ContinuousLinearMap.inr ℝ ↥T ↥N)) hF_bij
  have hF_partial_inv :
      (fderiv ℝ F (0, 0) ∘L ContinuousLinearMap.inr ℝ ↥T ↥N).IsInvertible := by
    rw [hF_hfd.fderiv]
    exact hF_right_inv
  set φ := hF_cda.implicitFunction two_ne_zero hF_partial_inv with hφ_def
  have hφ_smooth : ContDiffAt ℝ 2 φ 0 := by
    rw [hφ_def]
    exact hF_cda.contDiffAt_implicitFunction two_ne_zero hF_partial_inv
  have hφ_zero : φ 0 = 0 := by
    rw [hφ_def]
    exact hF_cda.implicitFunction_apply_self two_ne_zero hF_partial_inv
  have hF'_inl_zero : F'.comp (ContinuousLinearMap.inl ℝ ↥T ↥N) = 0 := by
    have hker : ∀ t : ↥T, H (↑t) = 0 := by
      intro ⟨t, ht⟩
      have : t ∈ hessianKer f x₀ := ht
      rwa [hessianKer, LinearMap.mem_ker] at this
    have hι_inl : ∀ (t : ↥T), ι (t, (0 : ↥N)) = (↑t : E) := by
      intro t
      simp only [ι, ContinuousLinearMap.coprod_apply, Submodule.subtypeL_apply,
        map_zero, add_zero]
    exact comp_inl_eq_zero_of_ker compR ι H hcompR_eq hι_inl hker
  have hφ_deriv : fderiv ℝ φ 0 = 0 := by
    have hcomp_eq : ∀ᶠ t in 𝓝 (0 : ↥T), F (t, φ t) = 0 :=
      (by
        rw [hφ_def]
        exact (hF_cda.eventually_apply_implicitFunction two_ne_zero hF_partial_inv).mono
          fun _ ht => ht.trans hF0)
    exact fderiv_eq_zero_of_locally_const_comp hF_hfd
      (hφ_smooth.differentiableAt two_ne_zero) hφ_zero
      hF'_inl_zero hF_inj hcomp_eq
  have hproj_fst : Filter.Tendsto
      (fun x : E => (orthogonalProjectionOnto T (x - x₀) : ↥T)) (𝓝 x₀) (𝓝 0) := by
    rw [show (0 : ↥T) =
      orthogonalProjectionOnto T ((x₀ : E) - x₀) from by
        simp only [sub_self, map_zero]]
    exact ((orthogonalProjectionOnto T).continuous.comp
      (continuous_id.sub continuous_const)).continuousAt
  have hproj_snd : Filter.Tendsto
      (fun x : E => (orthogonalProjectionOnto N (x - x₀) : ↥N)) (𝓝 x₀) (𝓝 0) := by
    rw [show (0 : ↥N) =
      orthogonalProjectionOnto N ((x₀ : E) - x₀) from by
        simp only [sub_self, map_zero]]
    exact ((orthogonalProjectionOnto N).continuous.comp
      (continuous_id.sub continuous_const)).continuousAt
  have hproj_tend : Filter.Tendsto
      (fun x : E => (orthogonalProjectionOnto T (x - x₀),
                      orthogonalProjectionOnto N (x - x₀)))
      (𝓝 x₀) (𝓝 (0, 0)) := by
    exact hproj_fst.prodMk_nhds hproj_snd
  have h_decomp : ∀ x : E, x₀ + ι (orthogonalProjectionOnto T (x - x₀),
      orthogonalProjectionOnto N (x - x₀)) = x := by
    intro x
    simp only [ι, ContinuousLinearMap.coprod_apply, Submodule.subtypeL_apply]
    have h : (↑(orthogonalProjectionOnto T (x - x₀)) : E) +
        ↑(orthogonalProjectionOnto N (x - x₀)) = x - x₀ :=
      T.starProjection_add_starProjection_orthogonal (x - x₀)
    rw [h]
    abel
  have h_fwd_local :
      ∀ᶠ p in 𝓝 (0 : ↥T × ↥N), F p = F (0, 0) ↔ φ p.1 = p.2 := by
    rw [hφ_def]
    exact hF_cda.eventually_apply_eq_iff_implicitFunction two_ne_zero hF_partial_inv
  have h_bwd_local : ∀ᶠ t in 𝓝 (0 : ↥T), F (t, φ t) = F (0, 0) := by
    rw [hφ_def]
    exact hF_cda.eventually_apply_implicitFunction two_ne_zero hF_partial_inv
  have h_fwd := hproj_tend.eventually h_fwd_local
  have h_bwd := hproj_fst.eventually h_bwd_local
  have h_iff : ∀ᶠ x in 𝓝 x₀,
      (∀ w : ↥N, fderiv ℝ f x (↑w) = 0) ↔
      (orthogonalProjectionOnto N (x - x₀) : E) =
        (φ (orthogonalProjectionOnto T (x - x₀)) : E) := by
    filter_upwards [h_fwd, h_bwd] with x hfwd hbwd
    rw [hF0] at hfwd hbwd
    constructor
    · intro hvanish
      have hFx : F (orthogonalProjectionOnto T (x - x₀),
          orthogonalProjectionOnto N (x - x₀)) = 0 := by
        change compR (fderiv ℝ f (x₀ + ι (orthogonalProjectionOnto T (x - x₀),
          orthogonalProjectionOnto N (x - x₀)))) = 0
        rw [h_decomp]
        exact (restrictToN_eq_zero_iff N (fderiv ℝ f x)).mpr hvanish
      exact congrArg Subtype.val (hfwd.mp hFx).symm
    · intro heq
      have h_eq_N : orthogonalProjectionOnto N (x - x₀) =
          φ (orthogonalProjectionOnto T (x - x₀)) := Subtype.val_injective heq
      intro w
      have hFx := hbwd
      change F (orthogonalProjectionOnto T (x - x₀),
        φ (orthogonalProjectionOnto T (x - x₀))) = 0 at hFx
      rw [← h_eq_N] at hFx
      have hFx' : compR (fderiv ℝ f (x₀ + ι (orthogonalProjectionOnto T (x - x₀),
          orthogonalProjectionOnto N (x - x₀)))) = 0 := hFx
      rw [h_decomp] at hFx'
      exact (restrictToN_eq_zero_iff N (fderiv ℝ f x)).mp hFx' w
  obtain ⟨U, hU, hUprop⟩ := h_iff.exists_mem
  exact ⟨U, hU, φ, hφ_smooth, hφ_zero, hφ_deriv, fun x hx => hUprop x hx⟩

end PLAcceleratedNesterovLean
