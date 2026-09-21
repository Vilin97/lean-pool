/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
import LeanPool.DavisKahan.DavisKahan.TanTheta.Vector
import LeanPool.DavisKahan.DavisKahan.Sylvester.Spectrum
import LeanPool.DavisKahan.ForTauCeti.Analysis.CStarAlgebra.SelfAdjointGapInverse

/-! # Spectrum -/

open TauCeti.DavisKahan.Sylvester

/-!
# The `tan Θ` theorem with genuine spectra

The per-vector `tan Θ` theorem of `TanTheta/Vector.lean` consumes a
quadratic-form strip on the invariant complement and a coercivity bound on
the test compression.  This module discharges both from honest Banach
algebra spectra of the compressions, giving the bounded genuine-spectrum
`tan Θ` theorem: for self-adjoint `T` with `T`-invariant `V`,
`σ(T|_{Vᗮ}) ⊆ [α, β]`, and the test compression spectrum avoiding
`(α - δ, β + δ)`, the columnwise residual bound `ρ` gives
`δ ‖x - P_V x‖ ≤ ρ ‖P_V x‖` on `Z`.

The two spectral bridges: interval spectrum of a compression gives the
quadratic-form strip (through the centered norm bound
`IsSelfAdjoint.norm_le_of_spectrum_subset_Icc`), and exterior spectrum
gives coercivity (through the two-sided inverse
`IsSelfAdjoint.exists_two_sided_inverse_of_spectrum_gap`).
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan

open scoped InnerProductSpace
open scoped TauCeti.CompleteSubspace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
/-- **Shifting a self-adjoint operator by a real scalar keeps it self-adjoint.**

Derived three times across this file and `UnboundedSpectrum.lean`, each time
over a differently-named space. -/
theorem isSelfAdjoint_sub_algebraMap {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] {M : K →L[ℂ] K}
    (hM : IsSelfAdjoint M) (c : ℝ) :
    IsSelfAdjoint (M - algebraMap ℝ (K →L[ℂ] K) c) :=
  IsSelfAdjoint.sub (R := K →L[ℂ] K) hM
    (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all _))

/-- **Quadratic-form strip from an interval compression spectrum.**  If the
spectrum of the compression `T|_W` lies in `[α, β]`, then the quadratic
form of `T` on `W` lies in the same strip. -/
theorem formBounds_of_compress_spectrum_subset_Icc
    {T : E →L[ℂ] E} (hT : IsSelfAdjoint T)
    {W : Submodule ℂ E} [W.HasOrthogonalProjection] [CompleteSpace W]
    {α β : ℝ} (hαβ : α ≤ β)
    (hspec : spectrum ℝ (compressOperator W T) ⊆ Set.Icc α β) :
    (∀ u ∈ W, α * ‖u‖ ^ 2 ≤ RCLike.re ⟪T u, u⟫_ℂ) ∧
      ∀ u ∈ W, RCLike.re ⟪T u, u⟫_ℂ ≤ β * ‖u‖ ^ 2 := by
  have he0 : (0 : ℝ) ≤ (β - α) / 2 := by linarith
  have hMsa := isSelfAdjoint_compressOperator hT W
  set M₁ : W →L[ℂ] W := compressOperator W T -
    algebraMap ℝ (W →L[ℂ] W) ((α + β) / 2) with hM₁def
  have hM₁sa : IsSelfAdjoint M₁ := by
    rw [hM₁def]
    exact isSelfAdjoint_sub_algebraMap hMsa _
  have hM₁spec : spectrum ℝ M₁ ⊆
      Set.Icc (-((β - α) / 2)) ((β - α) / 2) := by
    intro x hx
    rw [hM₁def, ← spectrum.sub_singleton_eq] at hx
    obtain ⟨y, hy, z, hz, hyz⟩ := Set.mem_sub.mp hx
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have hmem := hspec hy
    rw [Set.mem_Icc] at hmem
    rw [← hyz, Set.mem_Icc]
    constructor <;> [linarith [hmem.1]; linarith [hmem.2]]
  have hM₁norm : ‖M₁‖ ≤ (β - α) / 2 :=
    (TauCeti.IsSelfAdjoint.norm_le_iff_spectrum_subset_Icc
      (A := ↥W →L[ℂ] ↥W) hM₁sa he0).mpr hM₁spec
  have key : ∀ u : E, ∀ hu : u ∈ W,
      |RCLike.re ⟪T u, u⟫_ℂ - (α + β) / 2 * ‖u‖ ^ 2| ≤
        (β - α) / 2 * ‖u‖ ^ 2 := by
    intro u hu
    set x : W := ⟨u, hu⟩ with hx
    have h1 : M₁ x = compressOperator W T x - ((α + β) / 2 : ℝ) • x := by
      rw [hM₁def, sub_apply, Algebra.algebraMap_eq_smul_one, smul_apply,
        one_apply_eq_self]
    have h3 : RCLike.re ⟪compressOperator W T x, x⟫_ℂ =
        RCLike.re ⟪T u, u⟫_ℂ := by
      rw [Submodule.coe_inner,
        show ((compressOperator W T x : ↥W) : E) =
          W.starProjection (T u) from rfl,
        W.inner_starProjection_left_eq_right,
        Submodule.starProjection_eq_self_iff.mpr hu]
    have h2 : RCLike.re ⟪M₁ x, x⟫_ℂ =
        RCLike.re ⟪T u, u⟫_ℂ - (α + β) / 2 * ‖u‖ ^ 2 := by
      rw [h1, inner_sub_left, map_sub, h3]
      congr 1
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left,
        RCLike.conj_ofReal, ← RCLike.real_smul_eq_coe_mul, RCLike.smul_re,
        inner_self_eq_norm_sq]
      rfl
    have h4 : |RCLike.re ⟪M₁ x, x⟫_ℂ| ≤ (β - α) / 2 * ‖u‖ ^ 2 := by
      refine le_trans (RCLike.abs_re_le_norm _) ?_
      refine le_trans (norm_inner_le_norm _ _) ?_
      have hxn : ‖x‖ = ‖u‖ := rfl
      calc ‖M₁ x‖ * ‖x‖ ≤ (‖M₁‖ * ‖x‖) * ‖x‖ :=
            mul_le_mul_of_nonneg_right (M₁.le_opNorm x) (norm_nonneg _)
        _ ≤ ((β - α) / 2 * ‖x‖) * ‖x‖ := by
            have := mul_le_mul_of_nonneg_right hM₁norm (norm_nonneg x)
            exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
        _ = (β - α) / 2 * ‖u‖ ^ 2 := by rw [hxn]; ring
    rw [h2] at h4
    exact h4
  constructor
  · intro u hu
    have h := (abs_le.mp (key u hu)).1
    have hring : (α + β) / 2 * ‖u‖ ^ 2 - (β - α) / 2 * ‖u‖ ^ 2 =
        α * ‖u‖ ^ 2 := by ring
    linarith
  · intro u hu
    have h := (abs_le.mp (key u hu)).2
    have hring : (α + β) / 2 * ‖u‖ ^ 2 + (β - α) / 2 * ‖u‖ ^ 2 =
        β * ‖u‖ ^ 2 := by ring
    linarith
/-- **Centring an exterior spectrum pushes it off zero.**

Subtracting the midpoint `(α + β)/2` from an operator whose spectrum avoids
`(α - δ, β + δ)` leaves a spectrum at distance at least `(β - α)/2 + δ` from
zero.  Derived here and in `UnboundedSpectrum.lean`.

`Sylvester/Spectrum.lean` carries `shifted_spectrum_exterior`, the same fact in
that tree's own phrasing; the two trees share no ancestor, so they are stated
twice rather than shared. -/
theorem le_abs_of_spectrum_exterior {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] {M : K →L[ℂ] K} {α β δ : ℝ}
    (hspec : ∀ x ∈ spectrum ℝ M, x ≤ α - δ ∨ β + δ ≤ x) :
    ∀ x ∈ spectrum ℝ (M - algebraMap ℝ (K →L[ℂ] K) ((α + β) / 2)),
      (β - α) / 2 + δ ≤ |x| := by
  intro x hx
  rw [← spectrum.sub_singleton_eq] at hx
  obtain ⟨y, hy, z, hz, hyz⟩ := Set.mem_sub.mp hx
  rw [Set.mem_singleton_iff] at hz
  rw [hz] at hyz
  rw [← hyz]
  rcases hspec y hy with h1 | h1
  · have hle : y - (α + β) / 2 ≤ -((β - α) / 2 + δ) := by linarith
    calc (β - α) / 2 + δ ≤ -(y - (α + β) / 2) := by linarith
      _ ≤ |y - (α + β) / 2| := neg_le_abs _
  · have hge : (β - α) / 2 + δ ≤ y - (α + β) / 2 := by linarith
    exact hge.trans (le_abs_self _)

/-- **Coercivity from an exterior compression spectrum.**  If the spectrum
of the compression `T|_Z` avoids `(α - δ, β + δ)`, then the centered
compression is coercive at distance `(β - α)/2 + δ` from the midpoint. -/
theorem coercive_of_compress_spectrum_exterior
    {T : E →L[ℂ] E} (hT : IsSelfAdjoint T)
    {Z : Submodule ℂ E} [Z.HasOrthogonalProjection] [CompleteSpace Z]
    {α β δ : ℝ} (hαβ : α ≤ β) (hδ : 0 < δ)
    (hspec : ∀ x ∈ spectrum ℝ (compressOperator Z T),
      x ≤ α - δ ∨ β + δ ≤ x) :
    ∀ x ∈ Z, ((β - α) / 2 + δ) * ‖x‖ ≤
      ‖Z.starProjection (T x) - (((α + β) / 2 : ℝ) : ℂ) • x‖ := by
  have hrd : (0 : ℝ) < (β - α) / 2 + δ := by linarith
  have hMsa := isSelfAdjoint_compressOperator hT Z
  set M₁ : Z →L[ℂ] Z := compressOperator Z T -
    algebraMap ℝ (Z →L[ℂ] Z) ((α + β) / 2) with hM₁def
  have hM₁sa : IsSelfAdjoint M₁ := by
    rw [hM₁def]
    exact isSelfAdjoint_sub_algebraMap hMsa _
  have hM₁spec : ∀ x ∈ spectrum ℝ M₁, (β - α) / 2 + δ ≤ |x| := by
    rw [hM₁def]
    exact le_abs_of_spectrum_exterior hspec
  have hM₁unit : IsUnit M₁ :=
    TauCeti.isUnit_of_forall_le_abs (A := ↥Z →L[ℂ] ↥Z) hrd hM₁spec
  set J : ↥Z →L[ℂ] ↥Z := Ring.inverse M₁
  have hJ1 : J * M₁ = 1 := Ring.inverse_mul_cancel _ hM₁unit
  have hJnorm : ‖J‖ ≤ ((β - α) / 2 + δ)⁻¹ :=
    TauCeti.IsSelfAdjoint.norm_ringInverse_le (A := ↥Z →L[ℂ] ↥Z) hM₁sa hrd hM₁spec
  intro x hx
  set v : Z := ⟨x, hx⟩ with hv
  have hJv : J (M₁ v) = v := by
    have := DFunLike.congr_fun hJ1 v
    exact this
  have hcoer : ((β - α) / 2 + δ) * ‖v‖ ≤ ‖M₁ v‖ := by
    have h1 : ‖v‖ ≤ ((β - α) / 2 + δ)⁻¹ * ‖M₁ v‖ := by
      calc ‖v‖ = ‖J (M₁ v)‖ := by rw [hJv]
        _ ≤ ‖J‖ * ‖M₁ v‖ := J.le_opNorm _
        _ ≤ ((β - α) / 2 + δ)⁻¹ * ‖M₁ v‖ :=
            mul_le_mul_of_nonneg_right hJnorm (norm_nonneg _)
    calc ((β - α) / 2 + δ) * ‖v‖
        ≤ ((β - α) / 2 + δ) * (((β - α) / 2 + δ)⁻¹ * ‖M₁ v‖) :=
          mul_le_mul_of_nonneg_left h1 hrd.le
      _ = ‖M₁ v‖ := by
          rw [← mul_assoc, mul_inv_cancel₀ hrd.ne', one_mul]
  have hval : ((M₁ v : ↥Z) : E) =
      Z.starProjection (T x) - (((α + β) / 2 : ℝ) : ℂ) • x := by
    have h1 : M₁ v = compressOperator Z T v - ((α + β) / 2 : ℝ) • v := by
      rw [hM₁def, sub_apply, Algebra.algebraMap_eq_smul_one, smul_apply,
        one_apply_eq_self]
    rw [h1, AddSubgroupClass.coe_sub,
      show ((compressOperator Z T v : ↥Z) : E) =
        Z.starProjection (T x) from rfl,
      show ((((α + β) / 2 : ℝ) • v : ↥Z) : E) =
        ((α + β) / 2 : ℝ) • x from rfl,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  calc ((β - α) / 2 + δ) * ‖x‖
      = ((β - α) / 2 + δ) * ‖v‖ := rfl
    _ ≤ ‖M₁ v‖ := hcoer
    _ = ‖Z.starProjection (T x) - (((α + β) / 2 : ℝ) : ℂ) • x‖ := by
        rw [show ‖M₁ v‖ = ‖((M₁ v : ↥Z) : E)‖ from rfl, hval]

/-- **The bounded Davis--Kahan `tan Θ` theorem with genuine spectra.**
For self-adjoint `T`, a `T`-invariant subspace `V` with the spectrum of
the compression `T|_{Vᗮ}` in `[α, β]`, and a test subspace `Z` whose
compression spectrum avoids `(α - δ, β + δ)`, a columnwise residual bound
`ρ` over `Z` gives `δ ‖x - P_V x‖ ≤ ρ ‖P_V x‖` for every `x ∈ Z` — the
per-vector `tan ∠(Z, V) ≤ ρ/δ`, forcing `Z ∩ Vᗮ = 0`. -/
theorem tanTheta_spectrum
    {T : E →L[ℂ] E} (hT : IsSelfAdjoint T)
    {Z V : Submodule ℂ E} [Z.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hVinv : ∀ x ∈ V, T x ∈ V)
    {α β δ ρ : ℝ} (hαβ : α ≤ β) (hδ : 0 < δ) (hρ0 : 0 ≤ ρ)
    (hVspec : spectrum ℝ (compressOperator Vᗮ T) ⊆ Set.Icc α β)
    (hZspec : ∀ x ∈ spectrum ℝ (compressOperator Z T),
      x ≤ α - δ ∨ β + δ ≤ x)
    (hρ : ∀ x ∈ Z, ‖T x - Z.starProjection (T x)‖ ≤ ρ * ‖x‖) :
    ∀ x ∈ Z, δ * ‖x - V.starProjection x‖ ≤ ρ * ‖V.starProjection x‖ := by
  have : CompleteSpace Z :=
    (Z.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  have : CompleteSpace (Vᗮ : Submodule ℂ E) :=
    (Vᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  obtain ⟨hVa, hVb⟩ :=
    formBounds_of_compress_spectrum_subset_Icc hT hαβ hVspec
  have hZcoer := coercive_of_compress_spectrum_exterior hT hαβ hδ hZspec
  exact tan_theta_le' hT.isSymmetric hVinv hαβ hδ hρ0 hZcoer hVa hVb hρ

section OneSided

/- The two local instances below are load-bearing, exactly as in
`Sources/DavisKahan1970/SineTheta/CosineAngle.lean`: without the
`CompleteSpace` coercion instance and the C⋆-algebra instance recorded in
the submodule shape, any statement mixing `spectrum ℝ C` with `‖C‖` for a
compression `C : ↥W →L[ℂ] ↥W` sends `isDefEq` into a deterministic
heartbeat blow-up (pending instance syntheses fail, so definitional
unfolding of the `Submodule` algebra structures takes over).  With them in
scope the same statements elaborate at ordinary heartbeats. -/

/-- The local C-star algebra structure on bounded endomorphisms of the closed subspace. -/
noncomputable local instance instCStarAlgebraSubspaceCoordinateGenuineTanTheta
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G]
    (U : Submodule ℂ G) [U.HasOrthogonalProjection] :
    CStarAlgebra (↥U →L[ℂ] ↥U) :=
  inferInstance

/-- **The bounded `tan Θ` theorem in the source's one-sided orientation.**
Theorem 6.3 of Davis--Kahan 1970 places the two spectra on one axis: the
test compression spectrum lies below `α₀` and the unwanted compression
spectrum lies in `[α₀ + δ, ∞)`.  A bounded self-adjoint compression is
norm-bounded, so its spectrum is automatically capped; this reduces the
one-sided placement to the interval/exterior form
`tanTheta_spectrum` with `[α, β] = [α₀ + δ, max ‖T|_{Vᗮ}‖ (α₀ + δ)]`. -/
theorem tanTheta_spectrum_oneSided
    {T : E →L[ℂ] E} (hT : IsSelfAdjoint T)
    {Z V : Submodule ℂ E} [Z.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hVinv : ∀ x ∈ V, T x ∈ V)
    {α₀ δ ρ : ℝ} (hδ : 0 < δ) (hρ0 : 0 ≤ ρ)
    (hZspec : ∀ x ∈ spectrum ℝ (compressOperator Z T), x ≤ α₀)
    (hVspec : ∀ x ∈ spectrum ℝ (compressOperator Vᗮ T), α₀ + δ ≤ x)
    (hρ : ∀ x ∈ Z, ‖T x - Z.starProjection (T x)‖ ≤ ρ * ‖x‖) :
    ∀ x ∈ Z, δ * ‖x - V.starProjection x‖ ≤ ρ * ‖V.starProjection x‖ := by
  have hcap : ∀ y ∈ spectrum ℝ (compressOperator Vᗮ T),
      y ≤ max ‖compressOperator Vᗮ T‖ (α₀ + δ) := by
    intro y hy
    have hone : ‖(1 : ↥Vᗮ →L[ℂ] ↥Vᗮ)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have habs : ‖y‖ ≤ ‖compressOperator Vᗮ T‖ * ‖(1 : ↥Vᗮ →L[ℂ] ↥Vᗮ)‖ :=
      spectrum.norm_le_norm_mul_of_mem hy
    rw [Real.norm_eq_abs] at habs
    refine le_max_of_le_left ((le_abs_self y).trans (habs.trans ?_))
    calc ‖compressOperator Vᗮ T‖ * ‖(1 : ↥Vᗮ →L[ℂ] ↥Vᗮ)‖
        ≤ ‖compressOperator Vᗮ T‖ * 1 :=
          mul_le_mul_of_nonneg_left hone (norm_nonneg _)
      _ = ‖compressOperator Vᗮ T‖ := mul_one _
  refine tanTheta_spectrum hT hVinv (α := α₀ + δ)
    (β := max ‖compressOperator Vᗮ T‖ (α₀ + δ))
    (le_max_right _ _) hδ hρ0
    (fun y hy => Set.mem_Icc.mpr ⟨hVspec y hy, hcap y hy⟩)
    (fun x hx => Or.inl ?_) hρ
  have := hZspec x hx
  linarith

end OneSided

end DavisKahanExt
end TauCeti
