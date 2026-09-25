/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.TanTheta.Vector
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.SpectralRestriction
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.BoundedFromSpectrum
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Geometry

/-!
# The unbounded Davis--Kahan tangent theorem, per-vector form

The bounded infinite-dimensional tangent theorem uses the ambient operator only
on the test subspace, the complementary exact subspace, and differences of
vectors from those two subspaces.  This module records that domain information
explicitly and repeats the geometric argument for an unbounded operator, as a
partial map.

The first theorem accepts a symmetric partial map together with:

* inclusion of the test subspace in the operator domain;
* inclusion and invariance of the complementary exact subspace;
* a centered norm bound on that complementary exact subspace;
* coercivity of the compressed action on the test subspace;
* a columnwise residual bound on the test subspace.

The second theorem specializes the complementary exact subspace to the
canonical Spectra range of the bounded interval `Set.Icc alpha beta`.  Spectral
calculus supplies its full-domain inclusion, invariance, and sharp centered
norm bound.  The resulting exact target is the orthogonal complement of that
interval spectral range.
-/

@[expose] public section

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace TanTheta


/-- On a closed interval the absolute value is bounded by the larger endpoint
modulus.  Local replacement for the donor lemma of the same name, which reached
this file through `open Spectra.QuantumMechanics.SpectralTheory`. -/
private theorem abs_le_max_of_mem_Icc {a b s : ℝ} (hs : s ∈ Set.Icc a b) :
    |s| ≤ max |a| |b| := by
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · exact le_trans
      (le_trans (neg_le_neg (le_max_left |a| |b|)) (neg_abs_le a)) hs.1
  · exact le_trans hs.2 (le_trans (le_abs_self b) (le_max_right |a| |b|))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
/-- A residual bound on a domain-contained test subspace transfers to the
opposite block of a symmetric partial map.  Closedness is not needed and is not
assumed; only the particular vector in the orthogonal complement is required to
lie in the operator domain. -/
theorem norm_starProjection_symmetricPMap_le_of_mem_orthogonal
    (A : H →ₗ.[ℂ] H) (hA : TauCeti.LinearPMap.IsSymmetric A)
    {Z : Submodule ℂ H} [Z.HasOrthogonalProjection]
    (hZdom : Z ≤ A.domain)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ∀ x : H, ∀ hx : x ∈ Z,
      ‖A ⟨x, hZdom hx⟩ -
          Z.starProjection (A ⟨x, hZdom hx⟩)‖ ≤ ρ * ‖x‖)
    {w : H} (hwdom : w ∈ A.domain) (hw : w ∈ Zᗮ) :
    ‖Z.starProjection (A ⟨w, hwdom⟩)‖ ≤ ρ * ‖w‖ := by
  set z : H := Z.starProjection (A ⟨w, hwdom⟩) with hz
  have hzZ : z ∈ Z := Z.starProjection_apply_mem _
  have hzdom : z ∈ A.domain := hZdom hzZ
  have hsq : ‖z‖ ^ 2 ≤ ρ * ‖w‖ * ‖z‖ := by
    have h0 : ⟪z, z⟫_ℂ = ⟪A ⟨w, hwdom⟩, z⟫_ℂ := by
      conv_lhs => rw [hz]
      rw [Z.inner_starProjection_left_eq_right,
        Submodule.starProjection_eq_self_iff.mpr hzZ]
    have h1 : ⟪A ⟨w, hwdom⟩, z⟫_ℂ =
        ⟪w, A ⟨z, hzdom⟩ -
          Z.starProjection (A ⟨z, hzdom⟩)⟫_ℂ := by
      calc
        ⟪A ⟨w, hwdom⟩, z⟫_ℂ =
            ⟪w, A ⟨z, hzdom⟩⟫_ℂ :=
          hA ⟨w, hwdom⟩ ⟨z, hzdom⟩
        _ = ⟪w, A ⟨z, hzdom⟩ -
            Z.starProjection (A ⟨z, hzdom⟩)⟫_ℂ := by
          rw [inner_sub_right,
            Submodule.inner_left_of_mem_orthogonal
              (Z.starProjection_apply_mem (A ⟨z, hzdom⟩)) hw,
            sub_zero]
    calc
      ‖z‖ ^ 2 = RCLike.re ⟪z, z⟫_ℂ := (inner_self_eq_norm_sq z).symm
      _ = RCLike.re ⟪w, A ⟨z, hzdom⟩ -
          Z.starProjection (A ⟨z, hzdom⟩)⟫_ℂ := by
        rw [h0, h1]
      _ ≤ ‖⟪w, A ⟨z, hzdom⟩ -
          Z.starProjection (A ⟨z, hzdom⟩)⟫_ℂ‖ :=
        RCLike.re_le_norm _
      _ ≤ ‖w‖ * ‖A ⟨z, hzdom⟩ -
          Z.starProjection (A ⟨z, hzdom⟩)‖ :=
        norm_inner_le_norm _ _
      _ ≤ ‖w‖ * (ρ * ‖z‖) := by
        have hzres := hρ z hzZ
        gcongr
      _ = ρ * ‖w‖ * ‖z‖ := by ring
  rcases eq_or_ne ‖z‖ 0 with h0 | h0
  · rw [h0]
    positivity
  · have hzpos : 0 < ‖z‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith [hsq, hzpos]

omit [CompleteSpace H] in
/-- The domain-aware, per-vector Davis--Kahan tangent theorem.

The exact target is `V`; its orthogonal complement is required to lie in the
operator domain and to satisfy the centered interval estimate.  The test
subspace `Z` also lies in the domain.  This is precisely the domain footprint
of the bounded proof, so the conclusion is unchanged:

`delta * ‖x - P_V x‖ <= rho * ‖P_V x‖` for every `x` in `Z`.
-/
theorem tanTheta_unbounded_vector_of_centered_bounds
    (A : H →ₗ.[ℂ] H) (hA : TauCeti.LinearPMap.IsSymmetric A)
    {Z V : Submodule ℂ H} [Z.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hZdom : Z ≤ A.domain)
    (hVperpdom : Vᗮ ≤ A.domain)
    (hVperpinv : ∀ u : H, ∀ hu : u ∈ Vᗮ,
      A ⟨u, hVperpdom hu⟩ ∈ Vᗮ)
    {center halfWidth δ ρ : ℝ}
    (hhalf : 0 ≤ halfWidth) (hδ : 0 < δ) (hρ0 : 0 ≤ ρ)
    (hZcoercive : ∀ x : H, ∀ hx : x ∈ Z,
      (halfWidth + δ) * ‖x‖ ≤
        ‖Z.starProjection (A ⟨x, hZdom hx⟩) -
          (center : ℂ) • x‖)
    (hVperpcentered : ∀ u : H, ∀ hu : u ∈ Vᗮ,
      ‖A ⟨u, hVperpdom hu⟩ - (center : ℂ) • u‖ ≤
        halfWidth * ‖u‖)
    (hρ : ∀ x : H, ∀ hx : x ∈ Z,
      ‖A ⟨x, hZdom hx⟩ -
          Z.starProjection (A ⟨x, hZdom hx⟩)‖ ≤ ρ * ‖x‖) :
    ∀ x : H, ∀ _hx : x ∈ Z,
      δ * ‖x - V.starProjection x‖ ≤ ρ * ‖V.starProjection x‖ := by
  set Wop : (↥Vᗮ) →L[ℂ] H := Z.starProjection ∘L Vᗮ.subtypeL with hWop
  set κ : ℝ := ‖Wop‖ with hκdef
  have hκ0 : 0 ≤ κ := by
    rw [hκdef]
    exact norm_nonneg Wop
  have hmax : ∀ v : H, ∀ hv : v ∈ Vᗮ,
      ‖Z.starProjection v‖ ≤ κ * ‖v‖ := by
    intro v hv
    exact Wop.le_opNorm ⟨v, hv⟩
  have hκ1 : κ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    rw [one_mul]
    exact Z.norm_starProjection_apply_le (v : H)
  have hchain : ∀ u₀ : H, ∀ hu₀V : u₀ ∈ Vᗮ, ‖u₀‖ ≤ 1 →
      (halfWidth + δ) * ‖Z.starProjection u₀‖ ≤
        κ * halfWidth + ρ * ‖u₀ - Z.starProjection u₀‖ := by
    intro u₀ hu₀V hu₀n
    have hpZ : Z.starProjection u₀ ∈ Z := Z.starProjection_apply_mem u₀
    have huDom : u₀ ∈ A.domain := hVperpdom hu₀V
    have hpDom : Z.starProjection u₀ ∈ A.domain := hZdom hpZ
    have hwDom : u₀ - Z.starProjection u₀ ∈ A.domain :=
      A.domain.sub_mem huDom hpDom
    have h1 := hZcoercive (Z.starProjection u₀) hpZ
    have hAu :
        A ⟨u₀, huDom⟩ =
          A ⟨Z.starProjection u₀, hpDom⟩ +
            A ⟨u₀ - Z.starProjection u₀, hwDom⟩ := by
      have hsub : (⟨u₀, huDom⟩ : A.domain) =
          ⟨Z.starProjection u₀, hpDom⟩ +
            ⟨u₀ - Z.starProjection u₀, hwDom⟩ := by
        apply Subtype.ext
        simp
      rw [hsub, LinearPMap.map_add]
    have hsplit :
        Z.starProjection
            (A ⟨Z.starProjection u₀, hpDom⟩) -
            (center : ℂ) • Z.starProjection u₀ =
          Z.starProjection
              (A ⟨u₀, huDom⟩ - (center : ℂ) • u₀) -
            Z.starProjection
              (A ⟨u₀ - Z.starProjection u₀, hwDom⟩) := by
      calc
        Z.starProjection
              (A ⟨Z.starProjection u₀, hpDom⟩) -
            (center : ℂ) • Z.starProjection u₀ =
            Z.starProjection
                ((A ⟨Z.starProjection u₀, hpDom⟩ +
                    A ⟨u₀ - Z.starProjection u₀, hwDom⟩) -
                  (center : ℂ) •
                    (Z.starProjection u₀ +
                      (u₀ - Z.starProjection u₀))) -
              Z.starProjection
                (A ⟨u₀ - Z.starProjection u₀, hwDom⟩) := by
          simp only [map_sub, map_add, map_smul]
          rw [Submodule.starProjection_eq_self_iff.mpr hpZ]
          abel_nf
        _ = Z.starProjection
              (A ⟨u₀, huDom⟩ - (center : ℂ) • u₀) -
            Z.starProjection
              (A ⟨u₀ - Z.starProjection u₀, hwDom⟩) := by
          rw [← hAu, show Z.starProjection u₀ +
            (u₀ - Z.starProjection u₀) = u₀ by abel]
    have hcenterMem :
        A ⟨u₀, huDom⟩ - (center : ℂ) • u₀ ∈ Vᗮ :=
      Submodule.sub_mem _ (hVperpinv u₀ hu₀V) (Vᗮ.smul_mem _ hu₀V)
    have h2 :
        ‖Z.starProjection
            (A ⟨u₀, huDom⟩ - (center : ℂ) • u₀)‖ ≤
          κ * halfWidth := by
      calc
        ‖Z.starProjection
            (A ⟨u₀, huDom⟩ - (center : ℂ) • u₀)‖ ≤
            κ * ‖A ⟨u₀, huDom⟩ - (center : ℂ) • u₀‖ :=
          hmax _ hcenterMem
        _ ≤ κ * (halfWidth * ‖u₀‖) := by
          have hstrip := hVperpcentered u₀ hu₀V
          gcongr
        _ ≤ κ * (halfWidth * 1) := by gcongr
        _ = κ * halfWidth := by ring
    have h3 :
        ‖Z.starProjection
            (A ⟨u₀ - Z.starProjection u₀, hwDom⟩)‖ ≤
          ρ * ‖u₀ - Z.starProjection u₀‖ :=
      norm_starProjection_symmetricPMap_le_of_mem_orthogonal
        A hA hZdom hρ0 hρ hwDom
        (Z.sub_starProjection_mem_orthogonal u₀)
    calc
      (halfWidth + δ) * ‖Z.starProjection u₀‖ ≤
          ‖Z.starProjection
              (A ⟨Z.starProjection u₀, hpDom⟩) -
            (center : ℂ) • Z.starProjection u₀‖ := h1
      _ = ‖Z.starProjection
              (A ⟨u₀, huDom⟩ - (center : ℂ) • u₀) -
            Z.starProjection
              (A ⟨u₀ - Z.starProjection u₀, hwDom⟩)‖ := by
        rw [hsplit]
      _ ≤ ‖Z.starProjection
              (A ⟨u₀, huDom⟩ - (center : ℂ) • u₀)‖ +
            ‖Z.starProjection
              (A ⟨u₀ - Z.starProjection u₀, hwDom⟩)‖ :=
        norm_sub_le _ _
      _ ≤ κ * halfWidth + ρ * ‖u₀ - Z.starProjection u₀‖ :=
        add_le_add h2 h3
  have hκineq : δ * κ ≤ ρ * Real.sqrt (1 - κ ^ 2) :=
    TauCeti.DavisKahanExt.mul_le_mul_sqrt_one_sub_sq_of_chain Wop hκdef hκ0 hhalf hδ hρ0
      (fun x => rfl) (fun u₀ hu₀V hu₀n => hchain u₀ hu₀V hu₀n)
  have hkey : ∀ u : H, ∀ hu : u ∈ Vᗮ,
      δ * ‖Z.starProjection u‖ ≤ ρ * ‖u - Z.starProjection u‖ := fun u hu =>
    TauCeti.DavisKahanExt.mul_norm_starProjection_le_of_compression_bound
      hκ0 hκ1 hδ hρ0 hmax hκineq u hu
  intro x hxZ
  have huV : x - V.starProjection x ∈ Vᗮ :=
    V.sub_starProjection_mem_orthogonal x
  rcases eq_or_ne (x - V.starProjection x) 0 with h0 | h0
  · rw [h0, norm_zero, mul_zero]
    positivity
  · have hCS : ‖x - V.starProjection x‖ ^ 2 ≤
        ‖x‖ * ‖Z.starProjection (x - V.starProjection x)‖ := by
      have e1 : ⟪x - V.starProjection x, x - V.starProjection x⟫_ℂ =
          ⟪x, x - V.starProjection x⟫_ℂ := by
        conv_lhs => rw [inner_sub_left]
        rw [Submodule.inner_right_of_mem_orthogonal
          (V.starProjection_apply_mem x) huV, sub_zero]
      have e2 : ⟪x, x - V.starProjection x⟫_ℂ =
          ⟪x, Z.starProjection (x - V.starProjection x)⟫_ℂ := by
        rw [← Z.inner_starProjection_left_eq_right,
          Submodule.starProjection_eq_self_iff.mpr hxZ]
      calc
        ‖x - V.starProjection x‖ ^ 2 =
            RCLike.re ⟪x - V.starProjection x,
              x - V.starProjection x⟫_ℂ :=
          (inner_self_eq_norm_sq _).symm
        _ = RCLike.re ⟪x,
            Z.starProjection (x - V.starProjection x)⟫_ℂ := by
          rw [e1, e2]
        _ ≤ ‖⟪x, Z.starProjection (x - V.starProjection x)⟫_ℂ‖ :=
          RCLike.re_le_norm _
        _ ≤ ‖x‖ * ‖Z.starProjection (x - V.starProjection x)‖ :=
          norm_inner_le_norm _ _
    have hk := hkey _ huV
    have hpyZu : ‖Z.starProjection (x - V.starProjection x)‖ ^ 2 +
          ‖(x - V.starProjection x) -
              Z.starProjection (x - V.starProjection x)‖ ^ 2 =
        ‖x - V.starProjection x‖ ^ 2 :=
      norm_sq_starProjection_add_norm_sq_sub Z _
    have hpyVx : ‖V.starProjection x‖ ^ 2 +
        ‖x - V.starProjection x‖ ^ 2 = ‖x‖ ^ 2 :=
      norm_sq_starProjection_add_norm_sq_sub V x
    have hq : (0 : ℝ) < ‖x - V.starProjection x‖ := norm_pos_iff.mpr h0
    set q : ℝ := ‖x - V.starProjection x‖ with hqdef
    set pz : ℝ := ‖Z.starProjection (x - V.starProjection x)‖ with hpzdef
    set pw : ℝ := ‖(x - V.starProjection x) -
      Z.starProjection (x - V.starProjection x)‖ with hpwdef
    set pv : ℝ := ‖V.starProjection x‖ with hpvdef
    have hfin : (δ * q) ^ 2 ≤ (ρ * pv) ^ 2 := by
      have hAineq : (δ * pz) ^ 2 ≤ (ρ * pw) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hδ.le (norm_nonneg _)) hk 2
      have hBineq : (q ^ 2) ^ 2 ≤ (‖x‖ * pz) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg _) hCS 2
      have hCineq : δ ^ 2 * (q ^ 2) ^ 2 ≤
          ρ ^ 2 * pv ^ 2 * (q ^ 2) := by
        calc
          δ ^ 2 * (q ^ 2) ^ 2 ≤ δ ^ 2 * (‖x‖ * pz) ^ 2 :=
            mul_le_mul_of_nonneg_left hBineq (sq_nonneg δ)
          _ = ‖x‖ ^ 2 * (δ * pz) ^ 2 := by ring
          _ ≤ ‖x‖ ^ 2 * (ρ * pw) ^ 2 :=
            mul_le_mul_of_nonneg_left hAineq (sq_nonneg _)
          _ = ρ ^ 2 * ‖x‖ ^ 2 * pw ^ 2 := by ring
          _ = ρ ^ 2 * ‖x‖ ^ 2 * q ^ 2 -
              ρ ^ 2 * (‖x‖ ^ 2 * pz ^ 2) := by
            rw [show pw ^ 2 = q ^ 2 - pz ^ 2 by linarith [hpyZu]]
            ring
          _ ≤ ρ ^ 2 * ‖x‖ ^ 2 * q ^ 2 -
              ρ ^ 2 * (q ^ 2) ^ 2 := by
            have h5 : ρ ^ 2 * (q ^ 2) ^ 2 ≤
                ρ ^ 2 * (‖x‖ * pz) ^ 2 :=
              mul_le_mul_of_nonneg_left hBineq (sq_nonneg ρ)
            have h6 : ρ ^ 2 * (‖x‖ * pz) ^ 2 =
                ρ ^ 2 * (‖x‖ ^ 2 * pz ^ 2) := by ring
            linarith
          _ = ρ ^ 2 * (‖x‖ ^ 2 - q ^ 2) * q ^ 2 := by ring
          _ = ρ ^ 2 * pv ^ 2 * q ^ 2 := by
            rw [show ‖x‖ ^ 2 - q ^ 2 = pv ^ 2 by linarith [hpyVx]]
      have hq2 : (0 : ℝ) < q ^ 2 := by positivity
      nlinarith [hCineq, hq2]
    have hsqrt := Real.sqrt_le_sqrt hfin
    rwa [Real.sqrt_sq (mul_nonneg hδ.le (norm_nonneg _)),
      Real.sqrt_sq (mul_nonneg hρ0 (norm_nonneg _))] at hsqrt

/-- Every vector in the canonical interval spectral range lies in the domain of
the unbounded self-adjoint operator. -/
theorem selfAdjointSpectralIcc_mem_domain
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    {α β : ℝ} (_hαβ : α ≤ β)
    {x : H}
    (hx : x ∈ selfAdjointSpectralSubspace A hA (Set.Icc α β)
      measurableSet_Icc) :
    x ∈ A.domain :=
  TauCeti.LinearPMap.mem_domain_of_mem_specRange_of_bounded hA _ measurableSet_Icc
    (M := max |α| |β|) (fun _ hs => abs_le_max_of_mem_Icc hs) hx

/-- The canonical interval spectral range satisfies the sharp centered norm
bound required by the unbounded tangent theorem. -/
theorem selfAdjointSpectralIcc_centered_norm_le
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    {α β : ℝ} (hαβ : α ≤ β)
    {x : H}
    (hx : x ∈ selfAdjointSpectralSubspace A hA (Set.Icc α β)
      measurableSet_Icc) :
    ‖A
          ⟨x, selfAdjointSpectralIcc_mem_domain A hA hαβ hx⟩ -
        (((α + β) / 2 : ℝ) : ℂ) • x‖ ≤
      (β - α) / 2 * ‖x‖ :=
  TauCeti.LinearPMap.norm_sub_smul_le_of_mem_specRange hA _ measurableSet_Icc
    (M := max |α| |β|) (fun _ hs => abs_le_max_of_mem_Icc hs)
    (by linarith)
    (fun s hs => by
      rw [abs_le]
      exact ⟨by linarith [hs.1, hs.2], by linarith [hs.1, hs.2]⟩)
    hx _

/-- Canonical exact-subspace specialization of the unbounded tangent theorem.

The bounded interval spectral range `E_A([alpha,beta])H` is the complementary
exact component.  Its orthogonal complement is the exact target subspace.  The
only remaining hypotheses concern the test subspace: domain inclusion,
coercivity of its compressed action, and a columnwise residual bound.
-/
theorem tanTheta_unbounded_exactSpectralIcc
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    {Z : Submodule ℂ H} [Z.HasOrthogonalProjection]
    {α β δ ρ : ℝ} (hαβ : α ≤ β) (hδ : 0 < δ) (hρ0 : 0 ≤ ρ)
    (hZdom : Z ≤ A.domain)
    (hZcoercive : ∀ x : H, ∀ hx : x ∈ Z,
      ((β - α) / 2 + δ) * ‖x‖ ≤
        ‖Z.starProjection (A ⟨x, hZdom hx⟩) -
          (((α + β) / 2 : ℝ) : ℂ) • x‖)
    (hρ : ∀ x : H, ∀ hx : x ∈ Z,
      ‖A ⟨x, hZdom hx⟩ -
          Z.starProjection (A ⟨x, hZdom hx⟩)‖ ≤ ρ * ‖x‖) :
    let W := selfAdjointSpectralSubspace A hA (Set.Icc α β)
      measurableSet_Icc
    ∀ x : H, ∀ _hx : x ∈ Z,
      δ * ‖x - Wᗮ.starProjection x‖ ≤ ρ * ‖Wᗮ.starProjection x‖ := by
  let W := selfAdjointSpectralSubspace A hA (Set.Icc α β)
    measurableSet_Icc
  have hdouble : (Wᗮ)ᗮ = W := by
    rw [Submodule.orthogonal_orthogonal]
  have hVperpdom : (Wᗮ)ᗮ ≤ A.domain := by
    intro u hu
    have huW : u ∈ W := (le_of_eq hdouble) hu
    exact selfAdjointSpectralIcc_mem_domain A hA hαβ huW
  have hVperpinv : ∀ u : H, ∀ hu : u ∈ (Wᗮ)ᗮ,
      A ⟨u, hVperpdom hu⟩ ∈ (Wᗮ)ᗮ := by
    intro u hu
    have huW : u ∈ W := (le_of_eq hdouble) hu
    have himage : A ⟨u, hVperpdom hu⟩ ∈ W :=
      selfAdjoint_maps_spectralSubspace A hA measurableSet_Icc
        ⟨u, hVperpdom hu⟩ huW
    exact (le_of_eq hdouble.symm) himage
  have hcenter : ∀ u : H, ∀ hu : u ∈ (Wᗮ)ᗮ,
      ‖A ⟨u, hVperpdom hu⟩ -
          (((α + β) / 2 : ℝ) : ℂ) • u‖ ≤
        (β - α) / 2 * ‖u‖ := by
    intro u hu
    have huW : u ∈ W := (le_of_eq hdouble) hu
    have h := selfAdjointSpectralIcc_centered_norm_le A hA hαβ huW
    have hdomEq :
        (⟨u, hVperpdom hu⟩ : A.domain) =
          ⟨u, selfAdjointSpectralIcc_mem_domain A hA hαβ huW⟩ :=
      Subtype.ext rfl
    rw [hdomEq]
    exact h
  exact tanTheta_unbounded_vector_of_centered_bounds
    (V := Wᗮ) (Z := Z) A (TauCeti.LinearPMap.isSymmetric_of_isSelfAdjoint hA) hZdom hVperpdom hVperpinv
      (halfWidth := (β - α) / 2)
      (center := (α + β) / 2)
      (δ := δ) (ρ := ρ)
      (by linarith) hδ hρ0 hZcoercive hcenter hρ

end TanTheta
end DavisKahan
end TauCeti
