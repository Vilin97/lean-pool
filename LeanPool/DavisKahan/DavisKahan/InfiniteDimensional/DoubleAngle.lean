/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Reflection
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.CompatibilitySinTwoTheta
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.General
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum

/-! # Double Angle -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Infinite-dimensional `sin 2Θ` and generic double-angle bounds

Literature writeup: local TeX, Sections 14--15, including Seelmann's general
spectral-separation form.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Foundation

open DavisKahan

open scoped InnerProductSpace
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [CompleteSpace F]
-- `reflectionDefect` and its three lemmas were a verbatim copy of
-- `DavisKahan/BoundedOperator/Reflection.lean`, which this file did not import.  They are
-- imported now; the copy is gone.  `open DavisKahan` below is what brings them into scope,
-- since this file is in `TauCeti.DavisKahanExt` and the originals are in `TauCeti.DavisKahan`.

/-! ## Reflected subspaces and the double-angle operator

The one-sided ambient double-angle operator, the mirror image of a subspace,
and the reflection-transport lemmas the `sin 2Θ` theorems consume.  The
transports whose proofs require restricted-spectrum invariance under unitary
conjugation or the two-projection double-angle calculus are isolated as leaf
obligations.
-/

/-- The ambient one-sided double-angle sine operator `2 P_{Uᗮ} P_V P_U`,
matching the finite-dimensional normalization. -/
noncomputable def sinTwoAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  (2 : 𝕜) • ((Uᗮ).starProjection ∘L V.starProjection ∘L U.starProjection)

/-- The mirror image of a subspace under the reflection through another. -/
noncomputable def reflectedSubspace (V U : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] : Submodule 𝕜 E :=
  U.map (V.reflectionOperator : E →L[𝕜] E).toLinearMap

omit [CompleteSpace E] in
/-- The reflection is an involution, applied pointwise. -/
theorem reflectionOperator_apply_apply
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection] (x : E) :
    V.reflectionOperator (V.reflectionOperator x) = x := by
  have h := congrArg (fun T : E →L[𝕜] E => T x) (Submodule.reflectionOperator_involutive V)
  simpa using h

/-- The reflection through a subspace is self-adjoint: it is `2 P - 1`. -/
theorem isSelfAdjoint_reflectionOperator
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection] :
    IsSelfAdjoint (V.reflectionOperator : E →L[𝕜] E) := by
  have hP : IsSelfAdjoint (V.starProjection : E →L[𝕜] E) :=
    isSelfAdjoint_starProjection V
  have hform : (V.reflectionOperator : E →L[𝕜] E) =
      (2 : 𝕜) • V.starProjection - 1 := by
    ext x
    simp [Submodule.reflectionOperator_apply]
  rw [hform, IsSelfAdjoint, star_sub, star_smul, star_ofNat, hP.star_eq,
    star_one]

/-- The reflection through `V` exchanges orthogonal complements with mirror
images: it is a self-adjoint involution. -/
theorem reflectedSubspace_orthogonal
    (V U : Submodule 𝕜 E) [V.HasOrthogonalProjection] :
    (reflectedSubspace V U)ᗮ = reflectedSubspace V Uᗮ := by
  have hJsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (isSelfAdjoint_reflectionOperator V)
  ext y
  constructor
  · intro hy
    refine Submodule.mem_map.mpr
      ⟨V.reflectionOperator y, ?_, reflectionOperator_apply_apply V y⟩
    rw [Submodule.mem_orthogonal]
    intro u hu
    have h := (Submodule.mem_orthogonal _ y).mp hy (V.reflectionOperator u)
      (Submodule.mem_map.mpr ⟨u, hu, rfl⟩)
    have h2 : ⟪V.reflectionOperator u, y⟫_𝕜 =
        ⟪u, V.reflectionOperator y⟫_𝕜 := hJsym u y
    rw [← h2]
    exact h
  · intro hy
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hy
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨u, hu, rfl⟩
    calc ⟪V.reflectionOperator u, V.reflectionOperator w⟫_𝕜
        = ⟪u, V.reflectionOperator (V.reflectionOperator w)⟫_𝕜 :=
          hJsym u (V.reflectionOperator w)
      _ = ⟪u, w⟫_𝕜 := by rw [reflectionOperator_apply_apply V w]
      _ = 0 := Submodule.inner_right_of_mem_orthogonal hu hw

/-- The mirror image of a subspace with an orthogonal projection has one:
the conjugated projection is an idempotent with the reflected range. -/
noncomputable instance reflectedSubspace_hasOrthogonalProjection
    (V U : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    [U.HasOrthogonalProjection] :
    (reflectedSubspace V U).HasOrthogonalProjection := by
  set P : E →L[𝕜] E :=
    V.reflectionOperator ∘L U.starProjection ∘L V.reflectionOperator with hP
  have hPapp : ∀ x, P x = V.reflectionOperator
      (U.starProjection (V.reflectionOperator x)) := fun x => rfl
  have hidem : IsIdempotentElem P := by
    change P * P = P
    ext x
    change P (P x) = P x
    rw [hPapp, hPapp, reflectionOperator_apply_apply,
      Submodule.starProjection_eq_self_iff.mpr
        (U.starProjection_apply_mem (V.reflectionOperator x))]
  have hrange : LinearMap.range (P : E →ₗ[𝕜] E) = reflectedSubspace V U := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact Submodule.mem_map.mpr
        ⟨U.starProjection (V.reflectionOperator x),
          U.starProjection_apply_mem _, rfl⟩
    · intro y hy
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hy
      refine ⟨V.reflectionOperator u, ?_⟩
      change P (V.reflectionOperator u) =
        (V.reflectionOperator : E →L[𝕜] E) u
      rw [hPapp, reflectionOperator_apply_apply,
        Submodule.starProjection_eq_self_iff.mpr hu]
  exact hrange ▸
    ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range hidem

/-- Conjugation by the reflection preserves self-adjointness. -/
theorem isSymmetric_reflectionConjugate
    {A : E →L[𝕜] E} (hA : A.IsSymmetric)
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection] :
    (V.reflectionOperator ∘L A ∘L V.reflectionOperator).IsSymmetric := by
  have hAsa : IsSelfAdjoint A :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA
  have hJsa : IsSelfAdjoint (V.reflectionOperator : E →L[𝕜] E) :=
    isSelfAdjoint_reflectionOperator V
  have hstar : IsSelfAdjoint
      (V.reflectionOperator ∘L A ∘L V.reflectionOperator) := by
    change star (V.reflectionOperator * A * V.reflectionOperator) =
      V.reflectionOperator * A * V.reflectionOperator
    rw [star_mul, star_mul, hJsa.star_eq, hAsa.star_eq, mul_assoc]
  exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hstar

/-- The mirror image of a reducing subspace reduces the conjugated
operator. -/
theorem reduces_reflectedSubspace
    {A : E →L[𝕜] E} {U : Submodule 𝕜 E} {V : Submodule 𝕜 E}
     [V.HasOrthogonalProjection]
    (hU : A.Reduces U) :
    ContinuousLinearMap.Reduces (V.reflectionOperator ∘L A ∘L V.reflectionOperator)
      (reflectedSubspace V U) := by
  constructor
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hy
    change V.reflectionOperator (A (V.reflectionOperator
      (V.reflectionOperator u))) ∈ reflectedSubspace V U
    rw [reflectionOperator_apply_apply]
    exact Submodule.mem_map.mpr ⟨A u, hU.1 u hu, rfl⟩
  · intro y hy
    rw [reflectedSubspace_orthogonal] at hy ⊢
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hy
    change V.reflectionOperator (A (V.reflectionOperator
      (V.reflectionOperator w))) ∈ reflectedSubspace V Uᗮ
    rw [reflectionOperator_apply_apply]
    exact Submodule.mem_map.mpr ⟨A w, hU.2 w hw, rfl⟩

omit [CompleteSpace E] in
/-- Double reflection conjugation is the identity on operators. -/
theorem reflection_conjugate_conjugate (A : E →L[𝕜] E) (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] :
    V.reflectionOperator ∘L (V.reflectionOperator ∘L A ∘L V.reflectionOperator)
      ∘L V.reflectionOperator = A := by
  ext x
  change V.reflectionOperator (V.reflectionOperator (A (V.reflectionOperator
    (V.reflectionOperator x)))) = A x
  rw [reflectionOperator_apply_apply, reflectionOperator_apply_apply]

omit [CompleteSpace E] in
/-- Double reflection is the identity on subspaces. -/
theorem reflectedSubspace_reflectedSubspace (V U : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] :
    reflectedSubspace V (reflectedSubspace V U) = U := by
  have hcomp : ((V.reflectionOperator : E →L[𝕜] E) :
      E →ₗ[𝕜] E).comp ((V.reflectionOperator : E →L[𝕜] E) : E →ₗ[𝕜] E) =
      LinearMap.id := by
    ext x
    exact reflectionOperator_apply_apply V x
  unfold reflectedSubspace
  rw [← Submodule.map_comp, hcomp, Submodule.map_id]

omit [CompleteSpace E] in
/-- Conjugation by the reflection carries invariance to the mirror image. -/
theorem invariantFor_reflection_conjugate
    {A : E →L[𝕜] E} {U : Submodule 𝕜 E} (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] (hU : InvariantFor A U) :
    InvariantFor (V.reflectionOperator ∘L A ∘L V.reflectionOperator)
      (reflectedSubspace V U) := by
  intro x hx
  obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
  change V.reflectionOperator (A (V.reflectionOperator
    (V.reflectionOperator u))) ∈ reflectedSubspace V U
  rw [reflectionOperator_apply_apply]
  exact Submodule.mem_map.mpr ⟨A u, hU u hu, rfl⟩

omit [CompleteSpace E] in
/-- Invariance of the mirror image forces invariance of the original. -/
theorem invariantFor_of_reflection_conjugate
    {A : E →L[𝕜] E} {U : Submodule 𝕜 E} (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection]
    (hU' : InvariantFor (V.reflectionOperator ∘L A ∘L V.reflectionOperator)
      (reflectedSubspace V U)) :
    InvariantFor A U := by
  have h := invariantFor_reflection_conjugate V hU'
  rwa [reflection_conjugate_conjugate, reflectedSubspace_reflectedSubspace] at h

/-- Two-sided intertwiners transport invertibility. -/
private theorem isUnit_conj_of_isUnit {G H : Type*}
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    (Φ : G →L[𝕜] H) (Ψ : H →L[𝕜] G)
    (hΨΦ : ∀ x, Ψ (Φ x) = x) (hΦΨ : ∀ y, Φ (Ψ y) = y)
    {T : G →L[𝕜] G} (hT : IsUnit T) :
    IsUnit (Φ ∘L T ∘L Ψ) := by
  obtain ⟨w, rfl⟩ := hT
  refine ⟨⟨Φ ∘L (w : G →L[𝕜] G) ∘L Ψ, Φ ∘L ((↑w⁻¹ : G →L[𝕜] G)) ∘L Ψ, ?_, ?_⟩, rfl⟩
  · ext y
    have h1 : (w : G →L[𝕜] G) ((↑w⁻¹ : G →L[𝕜] G) (Ψ y)) = Ψ y :=
      congrArg (fun S : G →L[𝕜] G => S (Ψ y)) w.mul_inv
    change (Φ : G → H) ((w : G →L[𝕜] G) (Ψ (Φ ((↑w⁻¹ : G →L[𝕜] G) (Ψ y))))) = y
    rw [hΨΦ, h1, hΦΨ]
  · ext y
    have h1 : (↑w⁻¹ : G →L[𝕜] G) ((w : G →L[𝕜] G) (Ψ y)) = Ψ y :=
      congrArg (fun S : G →L[𝕜] G => S (Ψ y)) w.inv_mul
    change (Φ : G → H) ((↑w⁻¹ : G →L[𝕜] G) (Ψ (Φ ((w : G →L[𝕜] G) (Ψ y))))) = y
    rw [hΨΦ, h1, hΦΨ]

/-- Conjugation by a two-sided intertwiner pair preserves invertibility. -/
private theorem isUnit_conj_iff {G H : Type*}
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    (Φ : G →L[𝕜] H) (Ψ : H →L[𝕜] G)
    (hΨΦ : ∀ x, Ψ (Φ x) = x) (hΦΨ : ∀ y, Φ (Ψ y) = y)
    (T : G →L[𝕜] G) :
    IsUnit (Φ ∘L T ∘L Ψ) ↔ IsUnit T := by
  constructor
  · intro h
    have h2 := isUnit_conj_of_isUnit Ψ Φ hΦΨ hΨΦ h
    have he : Ψ ∘L (Φ ∘L T ∘L Ψ) ∘L Φ = T := by
      ext x
      change (Ψ : H → G) (Φ (T (Ψ (Φ x)))) = T x
      rw [hΨΦ, hΨΦ]
    rwa [he] at h2
  · exact isUnit_conj_of_isUnit Φ Ψ hΨΦ hΦΨ

omit [CompleteSpace E] in
/-- Restricting the conjugated operator to the mirror image gives the same
spectrum as restricting the original operator to the original subspace. -/
private theorem spectrum_restrict_reflection_conjugate
    (A : E →L[𝕜] E) (U V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    (hU : InvariantFor A U)
    (hU' : InvariantFor (V.reflectionOperator ∘L A ∘L V.reflectionOperator)
      (reflectedSubspace V U)) :
    spectrum 𝕜 ((V.reflectionOperator ∘L A ∘L V.reflectionOperator).restrict hU')
      = spectrum 𝕜 (A.restrict hU) := by
  have hΦmem : ∀ x : ↥U,
      ((V.reflectionOperator : E →L[𝕜] E) ∘L U.subtypeL) x ∈
        reflectedSubspace V U := fun x =>
    Submodule.mem_map.mpr ⟨(x : E), x.2, rfl⟩
  have hΨmem : ∀ y : ↥(reflectedSubspace V U),
      ((V.reflectionOperator : E →L[𝕜] E) ∘L
        (reflectedSubspace V U).subtypeL) y ∈ U := by
    intro y
    obtain ⟨u, hu, huy⟩ := Submodule.mem_map.mp y.2
    have hval : ((V.reflectionOperator : E →L[𝕜] E) ∘L
        (reflectedSubspace V U).subtypeL) y = u := by
      change V.reflectionOperator (y : E) = u
      rw [← huy]
      exact reflectionOperator_apply_apply V u
    rw [hval]
    exact hu
  set Φ : ↥U →L[𝕜] ↥(reflectedSubspace V U) :=
    ((V.reflectionOperator : E →L[𝕜] E) ∘L U.subtypeL).codRestrict
      (reflectedSubspace V U) hΦmem with hΦdef
  set Ψ : ↥(reflectedSubspace V U) →L[𝕜] ↥U :=
    ((V.reflectionOperator : E →L[𝕜] E) ∘L
      (reflectedSubspace V U).subtypeL).codRestrict U hΨmem with hΨdef
  have hcoeΦ : ∀ x : ↥U, (Φ x : E) = V.reflectionOperator (x : E) := fun _ => rfl
  have hcoeΨ : ∀ y : ↥(reflectedSubspace V U),
      (Ψ y : E) = V.reflectionOperator (y : E) := fun _ => rfl
  have hΨΦ : ∀ x : ↥U, Ψ (Φ x) = x := by
    intro x
    apply Subtype.ext
    rw [hcoeΨ, hcoeΦ]
    exact reflectionOperator_apply_apply V (x : E)
  have hΦΨ : ∀ y : ↥(reflectedSubspace V U), Φ (Ψ y) = y := by
    intro y
    apply Subtype.ext
    rw [hcoeΦ, hcoeΨ]
    exact reflectionOperator_apply_apply V (y : E)
  ext z
  rw [spectrum.mem_iff, spectrum.mem_iff, not_iff_not]
  have hz : algebraMap 𝕜
        (↥(reflectedSubspace V U) →L[𝕜] ↥(reflectedSubspace V U)) z -
        (V.reflectionOperator ∘L A ∘L V.reflectionOperator).restrict hU' =
      Φ ∘L (algebraMap 𝕜 (↥U →L[𝕜] ↥U) z - A.restrict hU) ∘L Ψ := by
    ext y
    simp only [sub_apply, ContinuousLinearMap.comp_apply,
      Submodule.coe_sub, Algebra.algebraMap_eq_smul_one,
      smul_apply, one_apply_eq_self,
      Submodule.coe_smul, ContinuousLinearMap.coe_restrict_apply,
      hcoeΦ, hcoeΨ, map_sub, map_smul, reflectionOperator_apply_apply]
  rw [hz]
  exact isUnit_conj_iff Φ Ψ hΨΦ hΦΨ _

omit [CompleteSpace E] in
/-- **Restricted-spectrum invariance under reflection conjugation.**  The
mirror image of an invariant subspace carries the same restricted spectrum
for the conjugated operator. -/
theorem restrictedSpectrum_reflection_conjugate
    (A : E →L[𝕜] E) (U V : Submodule 𝕜 E) [V.HasOrthogonalProjection] :
    DavisKahan.Foundation.restrictedSpectrum
        (V.reflectionOperator ∘L A ∘L V.reflectionOperator)
        (reflectedSubspace V U) =
      DavisKahan.Foundation.restrictedSpectrum A U := by
  ext r
  constructor
  · rintro ⟨hU', hr⟩
    have hU : InvariantFor A U := invariantFor_of_reflection_conjugate V hU'
    exact ⟨hU, by
      rwa [spectrum_restrict_reflection_conjugate A U V hU hU'] at hr⟩
  · rintro ⟨hU, hr⟩
    have hU' := invariantFor_reflection_conjugate (A := A) V hU
    exact ⟨hU', by
      rwa [spectrum_restrict_reflection_conjugate A U V hU hU']⟩

/-- A finite-gap configuration yields both mixed interval/exterior
separations against its own reflection through `V`, with ordered interval
endpoints: conjugation by the reflection preserves every restricted
spectrum. -/
theorem finiteGap_mixedIntervalExterior
    {A : E →L[𝕜] E} {U : Submodule 𝕜 E} (V : Submodule 𝕜 E)
     [V.HasOrthogonalProjection] {d : ℝ}
    (hfinite : FiniteGapConfiguration A U d) :
    ∃ l r l' r', l ≤ r ∧ l' ≤ r' ∧
      IntervalExteriorSeparated A U
        (V.reflectionOperator ∘L A ∘L V.reflectionOperator)
        (reflectedSubspace V U)ᗮ l r d ∧
      IntervalExteriorSeparated
        (V.reflectionOperator ∘L A ∘L V.reflectionOperator)
        (reflectedSubspace V U) A Uᗮ l' r' d := by
  obtain ⟨l, r, hlr, hUin, hUcout⟩ := hfinite
  refine ⟨l, r, l, r, hlr, hlr, ⟨hUin, ?_, ?_⟩, ⟨?_, ?_⟩, hUcout⟩
  · rw [reflectedSubspace_orthogonal]
    exact invariantFor_reflection_conjugate V hUcout.1
  · rw [reflectedSubspace_orthogonal, restrictedSpectrum_reflection_conjugate]
    exact hUcout.2
  · exact invariantFor_reflection_conjugate V hUin.1
  · rw [restrictedSpectrum_reflection_conjugate]
    exact hUin.2

/-- The internal gap transports to the hybrid gap against the reflected
configuration: both restricted spectra are invariant under reflection
conjugation. -/
theorem internalGap_reflection_transport
    {A : E →L[𝕜] E} {U : Submodule 𝕜 E} {V : Submodule 𝕜 E}
     [V.HasOrthogonalProjection] {d : ℝ}
    (hgap : InternalGap A U d) :
    HybridGap A (V.reflectionOperator ∘L A ∘L V.reflectionOperator)
      U (reflectedSubspace V U) d := by
  obtain ⟨hInvU, hInvUc, hsep⟩ := hgap
  refine ⟨hInvU, ?_, ?_⟩
  · rw [reflectedSubspace_orthogonal]
    exact invariantFor_reflection_conjugate V hInvUc
  · intro a ha b hb
    rw [reflectedSubspace_orthogonal,
      restrictedSpectrum_reflection_conjugate] at hb
    exact hsep a ha b hb

/-- The projection onto the mirror image is the conjugated projection. -/
theorem starProjection_reflectedSubspace
    (V U : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] [U.HasOrthogonalProjection] :
    (reflectedSubspace V U).starProjection =
      V.reflectionOperator ∘L U.starProjection ∘L V.reflectionOperator := by
  ext x
  change (reflectedSubspace V U).starProjection x =
    V.reflectionOperator (U.starProjection (V.reflectionOperator x))
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact Submodule.mem_map.mpr
      ⟨U.starProjection (V.reflectionOperator x),
        U.starProjection_apply_mem _, rfl⟩
  · rw [reflectedSubspace_orthogonal]
    refine Submodule.mem_map.mpr
      ⟨V.reflectionOperator x - U.starProjection (V.reflectionOperator x),
        Submodule.sub_starProjection_mem_orthogonal _, ?_⟩
    change V.reflectionOperator (V.reflectionOperator x -
      U.starProjection (V.reflectionOperator x)) =
      x - V.reflectionOperator (U.starProjection (V.reflectionOperator x))
    rw [map_sub, reflectionOperator_apply_apply]

/-- The projection onto the mirror image's complement is the conjugated
complementary projection. -/
theorem starProjection_orthogonal_reflectedSubspace
    (V U : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] [U.HasOrthogonalProjection] :
    ((reflectedSubspace V U)ᗮ).starProjection =
      V.reflectionOperator ∘L Uᗮ.starProjection ∘L V.reflectionOperator := by
  rw [Submodule.starProjection_orthogonal' (reflectedSubspace V U),
    starProjection_reflectedSubspace, Submodule.starProjection_orthogonal' U]
  ext x
  change x - V.reflectionOperator (U.starProjection (V.reflectionOperator x)) =
    V.reflectionOperator (V.reflectionOperator x -
      U.starProjection (V.reflectionOperator x))
  rw [map_sub, reflectionOperator_apply_apply]

omit [CompleteSpace E] in
/-- **Cross-block identity.**  The complementary block of the reflection
between the two projections is exactly the one-sided double-angle
operator. -/
theorem complementary_comp_reflection_comp_projection
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Uᗮ.starProjection ∘L V.reflectionOperator ∘L U.starProjection =
      sinTwoAngleOperator U V := by
  ext x
  change Uᗮ.starProjection (V.reflectionOperator (U.starProjection x)) =
    (2 : 𝕜) • Uᗮ.starProjection (V.starProjection (U.starProjection x))
  rw [Submodule.reflectionOperator_apply, map_sub, map_smul]
  have h0 : Uᗮ.starProjection (U.starProjection x) = 0 := by
    rw [Submodule.starProjection_orthogonal_apply U (U.starProjection x),
      show U.starProjection (U.starProjection x) = U.starProjection x from
        Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem x),
      sub_self]
  rw [h0, sub_zero]

omit [CompleteSpace E] in
/-- Left composition with the reflection preserves the operator norm. -/
theorem norm_reflection_comp (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    (T : E →L[𝕜] E) : ‖V.reflectionOperator ∘L T‖ = ‖T‖ := by
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) fun x => ?_
    change ‖V.reflectionOperator (T x)‖ ≤ ‖T‖ * ‖x‖
    rw [V.reflectionOperator_norm_map]
    exact T.le_opNorm x
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    calc ‖T x‖ = ‖V.reflectionOperator (T x)‖ :=
        (V.reflectionOperator_norm_map (T x)).symm
      _ = ‖(V.reflectionOperator ∘L T) x‖ := rfl
      _ ≤ ‖V.reflectionOperator ∘L T‖ * ‖x‖ :=
        ContinuousLinearMap.le_opNorm _ x

omit [CompleteSpace E] in
/-- Right composition with the reflection preserves the operator norm. -/
theorem norm_comp_reflection (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    (T : E →L[𝕜] E) : ‖T ∘L V.reflectionOperator‖ = ‖T‖ := by
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) fun x => ?_
    change ‖T (V.reflectionOperator x)‖ ≤ ‖T‖ * ‖x‖
    calc ‖T (V.reflectionOperator x)‖ ≤ ‖T‖ * ‖V.reflectionOperator x‖ :=
        T.le_opNorm _
      _ = ‖T‖ * ‖x‖ := by rw [V.reflectionOperator_norm_map]
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    calc ‖T x‖
        = ‖T (V.reflectionOperator (V.reflectionOperator x))‖ := by
          rw [reflectionOperator_apply_apply]
      _ = ‖(T ∘L V.reflectionOperator) (V.reflectionOperator x)‖ := rfl
      _ ≤ ‖T ∘L V.reflectionOperator‖ * ‖V.reflectionOperator x‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖T ∘L V.reflectionOperator‖ * ‖x‖ := by
          rw [V.reflectionOperator_norm_map]

/-- The two-projection double-angle identity: the gap to the mirror image is
the norm of the one-sided double-angle operator.  Both directed blocks of the
projector difference are the double-angle operator up to composition with the
reflection, which is unitary. -/
theorem sinAngle_reflected_eq_sinTwoAngle
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.projectionGap (reflectedSubspace V U) = ‖sinTwoAngleOperator U V‖ := by
  have hgap : U.projectionGap (reflectedSubspace V U) =
      ‖(U.starProjection -
        (reflectedSubspace V U).starProjection : E →L[𝕜] E)‖ := rfl
  rw [hgap, Submodule.norm_starProjection_sub_eq_max]
  have h1 : (1 - (reflectedSubspace V U).starProjection : E →L[𝕜] E) ∘L
      U.starProjection =
      V.reflectionOperator ∘L
        (Uᗮ.starProjection ∘L V.reflectionOperator ∘L U.starProjection) := by
    rw [← Submodule.starProjection_orthogonal' (reflectedSubspace V U),
      starProjection_orthogonal_reflectedSubspace]
    ext x
    rfl
  have h2 : (1 - U.starProjection : E →L[𝕜] E) ∘L
      (reflectedSubspace V U).starProjection =
      (Uᗮ.starProjection ∘L V.reflectionOperator ∘L U.starProjection) ∘L
        V.reflectionOperator := by
    rw [← Submodule.starProjection_orthogonal' U,
      starProjection_reflectedSubspace]
    ext x
    rfl
  rw [h1, h2, complementary_comp_reflection_comp_projection,
    norm_reflection_comp, norm_comp_reflection, max_self]

/-- The directed form of the double-angle identity. -/
theorem doubleAngle_directedGap_identity
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖sinTwoAngleOperator U V‖ = U.directedProjectionGap (reflectedSubspace V U) := by
  have hgap : U.directedProjectionGap (reflectedSubspace V U) =
      ‖((reflectedSubspace V U)ᗮ).starProjection ∘L U.starProjection‖ := rfl
  rw [hgap, starProjection_orthogonal_reflectedSubspace]
  have hassoc : (V.reflectionOperator ∘L Uᗮ.starProjection ∘L
      V.reflectionOperator) ∘L U.starProjection =
      V.reflectionOperator ∘L
        (Uᗮ.starProjection ∘L V.reflectionOperator ∘L U.starProjection) := by
    ext x
    rfl
  rw [hassoc, complementary_comp_reflection_comp_projection,
    norm_reflection_comp]

/-- **The one-sided double-angle operator is a two-sided multiple of the
projector difference to the mirror image**, with both multipliers of norm at
most one: `2 P_Uᗮ P_V P_U = R_V (P_U - P_W) P_U` for `W = R_V U`.

This is the ideal-theoretic form of `sinAngle_reflected_eq_sinTwoAngle`, and it
is what an arbitrary symmetric norm ideal can actually use: `ideal_mem` and
`ideal_bound` see a two-sided multiple, whereas the gap identity only speaks
about operator norms. -/
theorem reflection_comp_projectionDifference_comp_projection
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    V.reflectionOperator ∘L
        ((U.starProjection - (reflectedSubspace V U).starProjection : E →L[𝕜] E) ∘L
          U.starProjection) =
      sinTwoAngleOperator U V := by
  have hidem (x : E) : U.starProjection (U.starProjection x) = U.starProjection x :=
    Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem x)
  have h1 : (1 - (reflectedSubspace V U).starProjection : E →L[𝕜] E) ∘L
      U.starProjection =
      V.reflectionOperator ∘L
        (Uᗮ.starProjection ∘L V.reflectionOperator ∘L U.starProjection) := by
    rw [← Submodule.starProjection_orthogonal' (reflectedSubspace V U),
      starProjection_orthogonal_reflectedSubspace]
    ext x
    rfl
  calc V.reflectionOperator ∘L
        ((U.starProjection - (reflectedSubspace V U).starProjection : E →L[𝕜] E) ∘L
          U.starProjection)
      = V.reflectionOperator ∘L
          ((1 - (reflectedSubspace V U).starProjection : E →L[𝕜] E) ∘L
            U.starProjection) := by
        congr 1
        ext x
        simp [hidem x]
    _ = V.reflectionOperator ∘L (V.reflectionOperator ∘L
          (Uᗮ.starProjection ∘L V.reflectionOperator ∘L U.starProjection)) := by
        rw [h1]
    _ = Uᗮ.starProjection ∘L V.reflectionOperator ∘L U.starProjection := by
        ext x
        simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
          reflectionOperator_apply_apply]
    _ = sinTwoAngleOperator U V :=
        complementary_comp_reflection_comp_projection U V

/-- **The one-sided double-angle operator lies in every symmetric norm ideal
that contains the projector difference to the mirror image, with no larger
gauge.**

Both halves are the ideal axioms applied to
`reflection_comp_projectionDifference_comp_projection`: `ideal_mem` for
membership, `ideal_bound` for the gauge, using `‖R_V‖ ≤ 1` and `‖P_U‖ ≤ 1`.

**The reverse inequality is false**, which is why this is stated one-sidedly;
see `norm_sinAngle_reflected_eq_norm_sinTwoAngle` below for the counterexample
and for what survives at the level of the operator norm. -/
theorem SymmetricNormIdeal.sinTwoAngle_mem_and_gauge_le
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E)) (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hmem : I.mem
      (U.starProjection - (reflectedSubspace V U).starProjection : E →L[𝕜] E)) :
    I.mem (sinTwoAngleOperator U V) ∧
      I.gauge (sinTwoAngleOperator U V) ≤
        I.gauge
          (U.starProjection - (reflectedSubspace V U).starProjection : E →L[𝕜] E) := by
  have hid := reflection_comp_projectionDifference_comp_projection U V
  refine ⟨hid ▸ I.ideal_mem (V.reflectionOperator) U.starProjection hmem, ?_⟩
  have hb := I.ideal_bound (V.reflectionOperator) U.starProjection hmem
  rw [hid] at hb
  refine hb.trans ?_
  have h0 : 0 ≤ I.gauge
      (U.starProjection - (reflectedSubspace V U).starProjection : E →L[𝕜] E) :=
    I.nonneg hmem
  calc ‖V.reflectionOperator‖ * I.gauge
        (U.starProjection - (reflectedSubspace V U).starProjection : E →L[𝕜] E) *
        ‖U.starProjection‖
      ≤ 1 * I.gauge
          (U.starProjection - (reflectedSubspace V U).starProjection : E →L[𝕜] E) * 1 := by
        gcongr
        · exact Submodule.norm_reflectionOperator_le_one V
        · exact U.starProjection_norm_le
    _ = _ := by ring

/-- **The full sine of the angle to the mirror image has the same norm as the
one-sided double-angle operator.**

This is `sinAngle_reflected_eq_sinTwoAngle` stated for the sine operator itself
rather than for the gap, using `ContinuousLinearMap.norm_modulus`.

## What this replaced, and why it is a norm statement and not a gauge statement

Until 2026-07-30 this position held a leaf obligation asserting the same thing
for *every symmetric norm ideal* — equal membership and equal gauge — on the
stated grounds that "their singular values agree".  **They do not.  They agree
up to a factor of two in multiplicity, and no amount of proof effort was going
to close that obligation.**

In the generic two-subspace block at angle `θ`, `|P_U - P_W|` for `W = R_V U`
carries the singular value `sin 2θ` **twice**, once on `U ∩ Wᗮ` and once on
`Uᗮ ∩ W`, while `2 P_Uᗮ P_V P_U` carries it **once**.  Concretely in `ℂ²`, with
`U = span e₁` and `V = span (e₁ + e₂)`: reflection in `V` carries `U` to `Uᗮ`,
so `P_U - P_W = diag (1, -1)`, whose absolute value is `1` and whose Frobenius
gauge is `√2`; while `2 P_Uᗮ P_V P_U = e₂ e₁⋆` has Frobenius gauge `1`.

The operator norm is exactly the gauge that cannot see this, since `max` of a
doubled multiset is unchanged — which is why the two norm identities directly
above go through and the ideal statement could not.  A true ideal-level
statement would be the two-sided bound
`gauge (sin 2Θ) ≤ gauge |P_U - P_W| ≤ 2 * gauge (sin 2Θ)`.  This theorem records
only the operator-norm identity. -/
theorem norm_sinAngle_reflected_eq_norm_sinTwoAngle
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖sinAngleOperator U (reflectedSubspace V U)‖ = ‖sinTwoAngleOperator U V‖ := by
  rw [show sinAngleOperator U (reflectedSubspace V U) =
      (U.starProjection - (reflectedSubspace V U).starProjection).modulus from rfl,
    ContinuousLinearMap.norm_modulus]
  exact sinAngle_reflected_eq_sinTwoAngle U V

omit [CompleteSpace E] in
/-- The reflection defect is `-2` times the sum of the two off-diagonal
blocks: `J A J - A = -2 (P_{Vᗮ} A P_V + P_V A P_{Vᗮ})`. -/
theorem reflectionDefect_eq_neg_two_smul_offdiag (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] (A : E →L[𝕜] E) :
    reflectionDefect V A =
      (-2 : 𝕜) • (Vᗮ.starProjection ∘L A ∘L V.starProjection +
        V.starProjection ∘L A ∘L Vᗮ.starProjection) := by
  ext x
  change V.reflectionOperator (A (V.reflectionOperator x)) - A x =
    (-2 : 𝕜) • (Vᗮ.starProjection (A (V.starProjection x)) +
      V.starProjection (A (Vᗮ.starProjection x)))
  rw [Submodule.reflectionOperator_apply, Submodule.reflectionOperator_apply,
    Submodule.starProjection_orthogonal' V]
  simp only [map_sub, map_smul, sub_apply, one_apply_eq_self]
  module

/-- The two off-diagonal blocks are mutually adjoint for self-adjoint `A`. -/
theorem offdiag_adjoint (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    {A : E →L[𝕜] E} (hA : IsSelfAdjoint A) :
    (Vᗮ.starProjection ∘L A ∘L V.starProjection).adjoint =
      V.starProjection ∘L A ∘L Vᗮ.starProjection := by
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ← ContinuousLinearMap.star_eq_adjoint,
    ← ContinuousLinearMap.star_eq_adjoint,
    ← ContinuousLinearMap.star_eq_adjoint,
    (isSelfAdjoint_starProjection V).star_eq,
    (isSelfAdjoint_starProjection Vᗮ).star_eq, hA.star_eq,
    ContinuousLinearMap.comp_assoc]

/-- **Sharp reflection-defect estimate through the off-diagonal block.**
For self-adjoint `A`, `‖J_V A J_V - A‖ ≤ 2 ‖P_{Vᗮ} A P_V‖` — no reduction
hypothesis on `V`.  This is the analytic input for the residual form of the
`sin 2Θ` theorem. -/
theorem norm_reflectionDefect_le_two_mul_norm_cross (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] {A : E →L[𝕜] E} (hA : IsSelfAdjoint A) :
    ‖reflectionDefect V A‖ ≤
      2 * ‖Vᗮ.starProjection ∘L A ∘L V.starProjection‖ := by
  set T₁ : E →L[𝕜] E := Vᗮ.starProjection ∘L A ∘L V.starProjection
    with hT₁
  set T₂ : E →L[𝕜] E := V.starProjection ∘L A ∘L Vᗮ.starProjection
    with hT₂
  have hnormT₂ : ‖T₂‖ = ‖T₁‖ := by
    rw [hT₂, ← offdiag_adjoint V hA, ← ContinuousLinearMap.star_eq_adjoint]
    exact norm_star T₁
  -- the sum of the off-diagonal blocks is bounded by the larger block
  have hsum : ‖T₁ + T₂‖ ≤ ‖T₁‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => ?_
    have h1out : T₁ z ∈ Vᗮ := by
      rw [hT₁]
      exact Vᗮ.starProjection_apply_mem _
    have h2out : T₂ z ∈ V := by
      rw [hT₂]
      exact V.starProjection_apply_mem _
    have horth : ⟪T₂ z, T₁ z⟫_𝕜 = 0 :=
      (Submodule.mem_orthogonal V _).mp h1out _ h2out
    have hpyth : ‖(T₁ + T₂) z‖ ^ 2 = ‖T₂ z‖ ^ 2 + ‖T₁ z‖ ^ 2 := by
      have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        (T₂ z) (T₁ z) horth
      have hadd : (T₁ + T₂) z = T₂ z + T₁ z := by
        rw [add_apply]
        abel
      rw [hadd, sq, sq, sq]
      linarith
    have hin1 : ‖T₁ z‖ ≤ ‖T₁‖ * ‖V.starProjection z‖ := by
      have hfac : T₁ z = T₁ (V.starProjection z) := by
        rw [hT₁]
        change Vᗮ.starProjection (A (V.starProjection z)) =
          Vᗮ.starProjection (A (V.starProjection (V.starProjection z)))
        rw [show V.starProjection (V.starProjection z) =
          V.starProjection z from
            Submodule.starProjection_eq_self_iff.mpr
              (V.starProjection_apply_mem z)]
      rw [hfac]
      exact T₁.le_opNorm _
    have hin2 : ‖T₂ z‖ ≤ ‖T₁‖ * ‖Vᗮ.starProjection z‖ := by
      have hfac : T₂ z = T₂ (Vᗮ.starProjection z) := by
        rw [hT₂]
        change V.starProjection (A (Vᗮ.starProjection z)) =
          V.starProjection (A (Vᗮ.starProjection (Vᗮ.starProjection z)))
        rw [show Vᗮ.starProjection (Vᗮ.starProjection z) =
          Vᗮ.starProjection z from
            Submodule.starProjection_eq_self_iff.mpr
              (Vᗮ.starProjection_apply_mem z)]
      rw [hfac]
      calc ‖T₂ (Vᗮ.starProjection z)‖
          ≤ ‖T₂‖ * ‖Vᗮ.starProjection z‖ := T₂.le_opNorm _
        _ = ‖T₁‖ * ‖Vᗮ.starProjection z‖ := by rw [hnormT₂]
    have hzdecomp : ‖z‖ ^ 2 =
        ‖V.starProjection z‖ ^ 2 + ‖Vᗮ.starProjection z‖ ^ 2 := by
      have horth' : ⟪V.starProjection z, Vᗮ.starProjection z⟫_𝕜 = 0 :=
        (Submodule.mem_orthogonal V _).mp
          (Vᗮ.starProjection_apply_mem z) _ (V.starProjection_apply_mem z)
      have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        (V.starProjection z) (Vᗮ.starProjection z) horth'
      rw [V.starProjection_add_starProjection_orthogonal z] at h
      rw [sq, sq, sq]
      linarith
    have hsq : ‖(T₁ + T₂) z‖ ^ 2 ≤ (‖T₁‖ * ‖z‖) ^ 2 := by
      rw [hpyth]
      have h1 := mul_self_le_mul_self (norm_nonneg (T₁ z)) hin1
      have h2 := mul_self_le_mul_self (norm_nonneg (T₂ z)) hin2
      have key : ‖T₂ z‖ ^ 2 + ‖T₁ z‖ ^ 2 ≤
          ‖T₁‖ ^ 2 * (‖V.starProjection z‖ ^ 2 +
            ‖Vᗮ.starProjection z‖ ^ 2) := by
        nlinarith [h1, h2]
      calc ‖T₂ z‖ ^ 2 + ‖T₁ z‖ ^ 2
          ≤ ‖T₁‖ ^ 2 * (‖V.starProjection z‖ ^ 2 +
              ‖Vᗮ.starProjection z‖ ^ 2) := key
        _ = (‖T₁‖ * ‖z‖) ^ 2 := by rw [← hzdecomp]; ring
    have hs := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg z))] at hs
  calc ‖reflectionDefect V A‖
      = ‖(-2 : 𝕜) • (T₁ + T₂)‖ := by
        rw [reflectionDefect_eq_neg_two_smul_offdiag]
    _ = 2 * ‖T₁ + T₂‖ := by
        rw [norm_smul]
        norm_num
    _ ≤ 2 * ‖T₁‖ := by linarith [hsum]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The off-diagonal block is bounded by the residual.**  If the trial
subspace `V` is the range of an isometric embedding `X` and
`R = A X - X M` is the residual of the approximate intertwining
relation `A X ≈ X M`, then `‖P_{Vᗮ} A P_V‖ ≤ ‖R‖`: on `v = X u ∈ V`,
`(1 - P_V) A v = (1 - P_V) (X (M u)) + (1 - P_V) (R u) = (1 - P_V) (R u)`,
and the isometry converts `‖u‖` back to `‖v‖`. -/
theorem norm_cross_le_norm_residual
    {X : F →L[𝕜] E} (hX : DavisKahan.IsometricEmbedding X)
    (A : E →L[𝕜] E) (M : F →L[𝕜] F)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection]
    (hmem : ∀ u, X u ∈ V) (hsurj : ∀ v ∈ V, ∃ u, X u = v) :
    ‖Vᗮ.starProjection ∘L A ∘L V.starProjection‖ ≤
      ‖A ∘L X - X ∘L M‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => ?_
  obtain ⟨u, hu⟩ := hsurj (V.starProjection z) (V.starProjection_apply_mem z)
  have hunorm : ‖u‖ = ‖V.starProjection z‖ := by rw [← hX u, hu]
  have hperp0 : Vᗮ.starProjection (X (M u)) = 0 := by
    rw [Submodule.starProjection_orthogonal' V]
    have hfix : V.starProjection (X (M u)) = X (M u) :=
      Submodule.starProjection_eq_self_iff.mpr (hmem (M u))
    rw [sub_apply, one_apply_eq_self, hfix, sub_self]
  have hsplit : A (X u) = X (M u) + (A ∘L X - X ∘L M) u := by
    change A (X u) = X (M u) + (A (X u) - X (M u))
    rw [add_sub_cancel]
  have hcalc : (Vᗮ.starProjection ∘L A ∘L V.starProjection) z =
      Vᗮ.starProjection ((A ∘L X - X ∘L M) u) := by
    change Vᗮ.starProjection (A (V.starProjection z)) = _
    rw [← hu, hsplit, map_add, hperp0, zero_add]
  rw [hcalc]
  calc ‖Vᗮ.starProjection ((A ∘L X - X ∘L M) u)‖
      ≤ ‖(A ∘L X - X ∘L M) u‖ :=
        Vᗮ.norm_starProjection_apply_le _
    _ ≤ ‖A ∘L X - X ∘L M‖ * ‖u‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖A ∘L X - X ∘L M‖ * ‖V.starProjection z‖ := by rw [hunorm]
    _ ≤ ‖A ∘L X - X ∘L M‖ * ‖z‖ :=
        mul_le_mul_of_nonneg_left (V.norm_starProjection_apply_le z)
          (norm_nonneg _)

omit [CompleteSpace F] in
/-- **Leaf obligation.** The reflection defect through the closed trial range
is at most twice the residual: the defect is twice the off-diagonal block of
`A`, which the residual dominates. -/
theorem reflectionDefect_range_le_residual
    {A : E →L[𝕜] E} (hA : A.IsSymmetric)
    (X : F →L[𝕜] E) (hX : IsometricEmbedding X)
    [(LinearMap.range X.toLinearMap).HasOrthogonalProjection]
    {M : F →L[𝕜] F} (_hM : M.IsSymmetric) :
    ‖reflectionDefect (LinearMap.range X.toLinearMap) A‖ ≤
      2 * ‖residual A X M‖ := by
  have hAsa : IsSelfAdjoint A :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA
  set V := LinearMap.range X.toLinearMap with hV
  have hmem : ∀ u, X u ∈ V := fun u => ⟨u, rfl⟩
  have hsurj : ∀ v ∈ V, ∃ u, X u = v := fun v hv => hv
  have hcross := norm_cross_le_norm_residual hX A M hmem hsurj
  calc ‖reflectionDefect V A‖
      ≤ 2 * ‖Vᗮ.starProjection ∘L A ∘L V.starProjection‖ :=
        norm_reflectionDefect_le_two_mul_norm_cross V hAsa
    _ ≤ 2 * ‖residual A X M‖ := by
        have hres : residual A X M = A ∘L X - X ∘L M := rfl
        rw [hres]
        linarith

-- `hasOrthogonalProjection_range_of_isometric` stood here: a second proof of
-- `DavisKahan/BoundedOperator/IsometricRangeProjection.lean`'s `rangeHasOrthogonalProjection`,
-- under a different name and with no consumer anywhere in the repository.  Dead and
-- duplicated, so removed rather than repointed.

/-- Reflection-defect `sin 2Θ` theorem.

This is the theorem previously named `sinTwoTheta_residual`. The old name was
misleading: its right-hand side is a mirror defect, not the residual of an
approximate invariant pair.

Lean proof route for a weaker agent:

1. Let `J` be the reflection through `V` and compare `A` with `JAJ`.
2. The spectral subspace `JU` reduces `JAJ` and has the same internal gap.
3. Apply the symmetric `sinTheta` theorem to `A` and `JAJ`.
4. Use the two-projection identity relating the angle between `U` and `JU` to `sin(2Θ(U,V))`.


Ext-agent signature audit (GPT 5.6 High): `FiniteGapConfiguration` already supplies the
structured internal separation at positive `d`; the former separate `InternalGap`
hypothesis was redundant. The reflection-defect target is the correct sharp residual
form.

Preferred dependency route: Use reflection conjugation to reduce to `sin Θ`; keep
finite-gap constant-one geometry separate from generic separated-spectrum estimates.
-/
theorem sinTwoTheta_reflectionDefect
    {A : E →L[𝕜] E} (hA : A.IsSymmetric)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U) {d : ℝ} (hd : 0 < d)
    (hfinite : FiniteGapConfiguration A U d) :
    d * ‖sinTwoAngleOperator U V‖ ≤
      ‖reflectionDefect V A‖ := by
  let A' := V.reflectionOperator ∘L A ∘L V.reflectionOperator
  let U' := reflectedSubspace V U
  have hA' : A'.IsSymmetric := isSymmetric_reflectionConjugate hA V
  have hU' : A'.Reduces U' := reduces_reflectedSubspace hU
  obtain ⟨l, r, l', r', hlr, hlr', hUU', hU'U⟩ :=
    finiteGap_mixedIntervalExterior V hfinite
  have hsin := sinTheta_symmetric hA hA' hU hU' hlr hlr' hd hUU' hU'U
  have hgapid : U.projectionGap U' = ‖sinTwoAngleOperator U V‖ :=
    sinAngle_reflected_eq_sinTwoAngle U V
  calc d * ‖sinTwoAngleOperator U V‖
      = d * U.projectionGap U' := by rw [hgapid]
    _ ≤ ‖A' - A‖ := hsin
    _ = ‖reflectionDefect V A‖ := rfl

omit [CompleteSpace F] in
/-- Approximate-invariant-pair residual form of `sin 2Θ`.

This is the genuine residual theorem missing from the earlier scaffold.  The
proof should reflect through the closed range of `X`, identify its mirror
defect with twice the off-diagonal residual, and apply
`sinTwoTheta_reflectionDefect`.

Lean proof route for a weaker agent:

1. Prove that an isometric embedding has closed range and construct the
   orthogonal projection onto that range.
2. Show that self-adjointness of `M` makes `X ∘ M ∘ X⁻¹` reduce the trial
   range.
3. Express the reflection defect of `A` through the trial range in terms of
   `residual A X M` and its adjoint block.
4. Bound that defect by twice the residual norm and invoke the
   reflection-defect theorem.
-/
theorem sinTwoTheta_residual
    {A : E →L[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : A.Reduces U) (X : F →L[𝕜] E) (hX : IsometricEmbedding X)
    [(LinearMap.range X.toLinearMap).HasOrthogonalProjection]
    {M : F →L[𝕜] F} (hM : M.IsSymmetric)
    {d : ℝ} (hd : 0 < d) (hfinite : FiniteGapConfiguration A U d) :
    d * ‖sinTwoThetaEmbedding U X‖ ≤ 2 * ‖residual A X M‖ := by
  let V := LinearMap.range X.toLinearMap
  have hangle : sinTwoThetaEmbedding U X = sinTwoAngleOperator U V :=
    sinTwoThetaEmbedding_eq_rangeAngle U X hX
  calc
    d * ‖sinTwoThetaEmbedding U X‖
        = d * ‖sinTwoAngleOperator U V‖ := by rw [hangle]
    _ ≤ ‖reflectionDefect V A‖ :=
      sinTwoTheta_reflectionDefect hA hU hd hfinite
    _ ≤ 2 * ‖residual A X M‖ :=
      reflectionDefect_range_le_residual hA X hX hM

/-- Perturbation form of the `sin 2Θ` theorem.

Ext-agent signature audit (GPT 5.6 High): Correct under finite-gap geometry. Reduction
of `B` by `V` is essential for cancellation of its reflection defect. Self-adjointness
of `B` is not needed for this reflection argument and was removed from the signature.
-/
theorem sinTwoTheta_perturbation
    {A B : E →L[𝕜] E}
    (hA : A.IsSymmetric)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : B.Reduces V)
    {d : ℝ} (hd : 0 < d)
    (hfinite : FiniteGapConfiguration A U d) :
    d * ‖sinTwoAngleOperator U V‖ ≤ 2 * ‖B - A‖ := by
  calc
    d * ‖sinTwoAngleOperator U V‖ ≤ ‖reflectionDefect V A‖ :=
      sinTwoTheta_reflectionDefect hA hU hd hfinite
    _ ≤ 2 * ‖A - B‖ := norm_reflectionDefect_le_two_mul A B V hV
    _ = 2 * ‖B - A‖ := by rw [norm_sub_rev]

/-- General spectral-separation `sin 2Θ` theorem.

Lean proof route for a weaker agent:

1. Apply the general separated-spectrum Sylvester estimate to the reflection defect.
2. Identify the resulting cross block with `sin(2Θ)` through the two-projection calculus.
3. Bound the defect by `2‖B-A‖`; combine constants to obtain the factor `π`.
4. Keep the result at the operator level: `sin (2·maximalAngle)` is not the
   norm of `sinTwoAngleOperator` when the angle spectrum crosses `π/4`.


Ext-agent signature audit (GPT 5.6 High): The corrected operator-norm conclusion is the
meaningful generic theorem. `sin (2·maximalAngle)` alone can miss intermediate angle
spectrum when angles cross `π/4`.

Preferred dependency route: Use reflection conjugation to reduce to `sin Θ`; keep
finite-gap constant-one geometry separate from generic separated-spectrum estimates.
-/
theorem sinTwoTheta_generalSeparation
    {A B : E →L[𝕜] E}
    (hA : A.IsSymmetric) (_hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : B.Reduces V)
    {d : ℝ} (hd : 0 < d) (hgap : InternalGap A U d) :
    d * ‖sinTwoAngleOperator U V‖ ≤ Real.pi * ‖B - A‖ := by
  let A' := V.reflectionOperator ∘L A ∘L V.reflectionOperator
  let U' := reflectedSubspace V U
  have hA' : A'.IsSymmetric := isSymmetric_reflectionConjugate hA V
  have hU' : A'.Reduces U' := reduces_reflectedSubspace hU
  have hhybrid : HybridGap A A' U U' d :=
    internalGap_reflection_transport hgap
  have hsin := sinTheta_generalSeparation hA hA' hU hU' hd hhybrid
  have hdefect : ‖reflectionDefect V A‖ ≤ 2 * ‖B - A‖ := by
    rw [norm_sub_rev B A]
    exact norm_reflectionDefect_le_two_mul A B V hV
  calc
    d * ‖sinTwoAngleOperator U V‖
        = d * U.directedProjectionGap U' := by
          rw [doubleAngle_directedGap_identity U V]
    _ ≤ (Real.pi/2) * ‖A'-A‖ := hsin
    _ = (Real.pi/2) * ‖reflectionDefect V A‖ := rfl
    _ ≤ (Real.pi/2) * (2 * ‖B-A‖) := by gcongr
    _ = Real.pi * ‖B-A‖ := by ring

end DavisKahanExt
end TauCeti
