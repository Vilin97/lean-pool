/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.DirectRotation.Majorization
public import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.Core.AngleOperators
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SinTheta.UnitarilyInvariant
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.MoorePenroseInverse

/-!
# Finite direct rotation: trigonometric and extremal formulas

This module completes the finite Section 4 route from the canonical polar
intertwiner.  It deliberately does not reintroduce the historical
`FiniteTwoProjection` namespace: the trigonometric factorization is obtained
from the positive cosine `|S|`, the full sine `|P_U-P_V|`, and the
Moore--Penrose initial projection.

The valid extremal endpoints are the full displacement-square majorization
and the unrestricted source-restricted displacement theorem.  The historical
real `pi / 3` claim for the full displacement is false when principal-angle
multiplicity spaces are mixed by the competitor; it is not reintroduced.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan.FiniteDimensional

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The global positive cosine of the direct rotation.  Unlike
`cosAngleOperator = |P_VP_U|`, this operator is the identity on the common
orthogonal complement and therefore participates in the full-space formula
`R = C + J S`. -/
noncomputable def directRotationCosine (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  TauCeti.operatorAbs (canonicalIntertwiner U V)

/-- **Davis--Kahan's intertwiner `J`**: the partial complex structure on the
nonzero-angle space.  Total Moore--Penrose inversion makes it zero on the
zero-angle space, matching the paper's convention "its values elsewhere will not
matter, so we arbitrarily set `J = 0` on `Null Θ`".

The paper builds `J` from the polar resolution `S₀ = J₀ sin Θ₀` of the
off-diagonal block and then sets `J ≐ [[0, -J₀⋆], [J₀, 0]]`.  Here `J` is built
instead from the skew part of the direct rotation, which
`directRotation_sub_cosine_eq_half_smul_sub` identifies with `(U - U⁻¹)/2` and
hence with that block; `directRotation_eq_cos_add_J_sin` is the paper's
`U = cos Θ + J sin Θ`, and `angleComplexStructure_symm` is Corollary 3.2. -/
noncomputable def angleComplexStructure (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) : E →ₗ[𝕜] E :=
  ((directRotation U V hacute).toLinearMap - directRotationCosine U V) ∘ₗ
    TauCeti.moorePenroseInverse (sinAngleOperator U V)

/-- The zero-angle space of the full sine is contained in the zero space of
`R-C`. -/
theorem ker_sinAngleOperator_le_ker_directRotation_sub_cosine
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (sinAngleOperator U V).ker ≤
      ((directRotation U V hacute).toLinearMap - directRotationCosine U V).ker := by
  intro x hx
  have hxD : x ∈ (projection U - projection V).ker := by
    simpa [sinAngleOperator, ker_operatorAbs] using hx
  have hproj : projection U x = projection V x :=
    sub_eq_zero.mp (by
      simpa [LinearMap.sub_apply] using LinearMap.mem_ker.mp hxD)
  have hR := directRotation_apply_eq_self_of_projection_eq U V hacute hproj
  have hC := abs_canonicalIntertwiner_apply_eq_self_of_projection_eq U V hproj
  apply LinearMap.mem_ker.mpr
  have hRx : polarFactor (canonicalIntertwiner U V) x = x := hR
  simp [LinearMap.sub_apply, directRotationCosine, hRx, hC]

/-- Reversing the pair gives the inverse rotation. -/
theorem directRotation_symm (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    directRotation V U hacute.symm = (directRotation U V hacute).symm := by
  have hstar : (canonicalIntertwiner U V).adjoint = canonicalIntertwiner V U :=
    adjoint_canonicalIntertwiner U V
  have hpolar := polarFactor_adjoint_of_isUnit
    (canonicalIntertwiner_isUnit_of_acute U V hacute)
  apply LinearIsometryEquiv.ext
  intro x
  have h1 : directRotation V U hacute.symm x
      = polarFactor (canonicalIntertwiner V U) x := rfl
  have h2 : (directRotation U V hacute).symm x
      = LinearMap.adjoint (polarFactor (canonicalIntertwiner U V)) x :=
    (LinearMap.congr_fun
      (directRotation U V hacute).adjoint_toLinearMap_eq_symm x).symm
  rw [h1, h2, ← hstar, hpolar]

/-- The direct rotation is the identity on the common and doubly-orthogonal
parts. -/
theorem directRotation_apply_eq_self_of_mem_common (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) {x : E}
    (hx : x ∈ U ⊓ V ⊔ (U ⊔ V)ᗮ) :
    directRotation U V hacute x = x := by
  obtain ⟨x₀, hx₀, x₁, hx₁, rfl⟩ := Submodule.mem_sup.mp hx
  have hproj0 : projection U x₀ = projection V x₀ := by
    simp [projection_apply_of_mem hx₀.1, projection_apply_of_mem hx₀.2]
  have hx₁U : x₁ ∈ Uᗮ := Submodule.orthogonal_le le_sup_left hx₁
  have hx₁V : x₁ ∈ Vᗮ := Submodule.orthogonal_le le_sup_right hx₁
  have hproj1 : projection U x₁ = projection V x₁ := by
    simp [projection_apply_of_mem_orthogonal hx₁U,
      projection_apply_of_mem_orthogonal hx₁V]
  rw [map_add,
    directRotation_apply_eq_self_of_projection_eq U V hacute hproj0,
    directRotation_apply_eq_self_of_projection_eq U V hacute hproj1]

/-- The direct rotation is definitionally the polar factor of the canonical
intertwiner. -/
theorem directRotation_eq_polarFactor (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (directRotation U V hacute).toLinearMap =
      polarFactor (canonicalIntertwiner U V) :=
  rfl

/-- Full-space trigonometric factorization `R = C + J sin Θ`. -/
theorem directRotation_eq_cos_add_J_sin (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (directRotation U V hacute).toLinearMap =
      directRotationCosine U V +
        angleComplexStructure U V hacute ∘ₗ sinAngleOperator U V := by
  let A := sinAngleOperator U V
  let B := (directRotation U V hacute).toLinearMap - directRotationCosine U V
  have hfactor : B ∘ₗ TauCeti.moorePenroseInverse A ∘ₗ A = B :=
    TauCeti.comp_moorePenroseInverse_comp_eq_of_ker_le A B
      (ker_sinAngleOperator_le_ker_directRotation_sub_cosine U V hacute)
  ext x
  have hx := LinearMap.congr_fun hfactor x
  simpa [A, B, angleComplexStructure, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.comp_apply] using congrArg
      (fun y => directRotationCosine U V x + y) hx.symm

/-- The direct rotation commutes with the global positive cosine. -/
theorem directRotation_comm_cosine (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (directRotation U V hacute).toLinearMap ∘ₗ directRotationCosine U V =
      directRotationCosine U V ∘ₗ (directRotation U V hacute).toLinearMap := by
  simpa [directRotationCosine] using
    directRotation_comm_abs_canonicalIntertwiner U V hacute

/-- Polar uniqueness: any unitary-positive factorization of the canonical
intertwiner uses the direct rotation as its unitary factor. -/
theorem directRotation_unique (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (W : E ≃ₗᵢ[𝕜] E) (H : E →ₗ[𝕜] E)
    (hH : H.IsPositive)
    (hdecomp : canonicalIntertwiner U V = W.toLinearMap ∘ₗ H) :
    W = directRotation U V hacute := by
  have hpolar := polarFactor_eq_of_isUnit_eq_comp_positive
    (canonicalIntertwiner_isUnit_of_acute U V hacute) W hH hdecomp
  apply LinearIsometryEquiv.ext
  intro x
  exact LinearMap.congr_fun hpolar.symm x

/-- Davis--Kahan Proposition 4.3: the direct rotation minimizes every UI norm
of the positive displacement square. -/
theorem directRotation_minimizes_displacementSquare_uiNorm
    (N : UnitarilyInvariantSeminorm 𝕜 E E) (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (W : E ≃ₗᵢ[𝕜] E)
    (hmap : U.map W.toLinearMap = V) :
    N (displacementSquare (directRotation U V hacute).toLinearMap) ≤
      N (displacementSquare W.toLinearMap) :=
  directRotation_displacementSquare_uiNorm N U V hacute W hmap

/-- Davis--Kahan Corollary 4.1: the direct rotation minimizes every unitarily
invariant norm of the displacement restricted to the source subspace.

This is the sound replacement for the historical full-displacement `pi / 3`
candidate: what is dropped is the *largest-angle threshold*, not every angle
condition.  `IsAcute` remains, and is not a weakening of the result — it is the
hypothesis under which `directRotation U V hacute` exists at all
(`IsAcute` says no principal angle is a quarter turn, in either direction).

The `IsAcute` here is `TauCeti.IsAcute`, Davis--Kahan's printed Definition 3.2.
This module is finite dimensional throughout, where that predicate is
equivalent to the quantitative `TauCeti.DavisKahan.IsUniformlyAcute` by
`TauCeti.isAcute_iff_projectionGap_lt_one`; the earlier reference here was to
`DavisKahan.FiniteDimensional.IsAcute`, a name that has never existed. -/
theorem directRotation_minimizes_restrictedDisplacement_uiNorm
    (N : UnitarilyInvariantSeminorm 𝕜 E E) (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (W : E ≃ₗᵢ[𝕜] E)
    (hmap : U.map W.toLinearMap = V) :
    N ((LinearMap.id - (directRotation U V hacute).toLinearMap) ∘ₗ
        projection U) ≤
      N ((LinearMap.id - W.toLinearMap) ∘ₗ projection U) :=
  uiNorm_restrictedDisplacement_le N U V hacute W hmap

/-- Pointwise maximum-displacement extremality, obtained from Proposition 4.3
with the operator norm and `‖A⋆A‖ = ‖A‖²`. -/
theorem directRotation_minimizes_max_displacement
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsAcute U V)
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) :
    ‖((directRotation U V hacute).toLinearMap - LinearMap.id).toContinuousLinearMap‖ ≤
      ‖(W.toLinearMap - LinearMap.id).toContinuousLinearMap‖ := by
  have h := directRotation_minimizes_displacementSquare_uiNorm
    (UnitarilyInvariantSeminorm.opNorm (𝕜 := 𝕜) (E := E) (F := E)) U V hacute W hmap
  have key : ∀ X : E →ₗ[𝕜] E,
      UnitarilyInvariantSeminorm.opNorm (𝕜 := 𝕜) (E := E) (F := E) (displacementSquare X) =
        ‖(X - LinearMap.id).toContinuousLinearMap‖ ^ 2 := by
    intro X
    have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
    have hD : displacementSquare X =
        LinearMap.adjoint (LinearMap.id - X) ∘ₗ (LinearMap.id - X) := by
      simp only [displacementSquare, map_sub, LinearMap.adjoint_id]
    have hCLM : (LinearMap.adjoint (LinearMap.id - X) ∘ₗ
          (LinearMap.id - X)).toContinuousLinearMap =
        ContinuousLinearMap.adjoint
            (LinearMap.id - X).toContinuousLinearMap ∘L
          (LinearMap.id - X).toContinuousLinearMap := by
      ext x
      rfl
    have hneg : (X - LinearMap.id).toContinuousLinearMap
        = -((LinearMap.id - X).toContinuousLinearMap) := by
      ext x
      simp
    change ‖(displacementSquare X).toContinuousLinearMap‖ = _
    rw [hD, hCLM, ContinuousLinearMap.norm_adjoint_comp_self, hneg, norm_neg, sq]
  rw [key, key] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- Orthonormal-basis displacement energy is minimized by the direct rotation.
This is Proposition 4.2, equivalently the nuclear-norm specialization of the
positive displacement-square majorization. -/
theorem directRotation_minimizes_sum_sq_basis_angles
    {n : ℕ} (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsAcute U V)
    (b : OrthonormalBasis (Fin n) 𝕜 E) (W : E ≃ₗᵢ[𝕜] E)
    (hmap : U.map W.toLinearMap = V) :
    ∑ i, ‖directRotation U V hacute (b i) - b i‖ ^ 2 ≤
      ∑ i, ‖W (b i) - b i‖ ^ 2 := by
  have hn : n = finrank 𝕜 E := by
    simpa using (Module.finrank_eq_card_basis b.toBasis).symm
  subst hn
  let R := (directRotation U V hacute).toLinearMap
  let AR := LinearMap.id - R
  let AW := LinearMap.id - W.toLinearMap
  let N : UnitarilyInvariantSeminorm 𝕜 E E :=
    (UnitarilyInvariantSeminorm.nuclear
      (𝕜 := 𝕜) (E := E) (F := E))
  have h := directRotation_minimizes_displacementSquare_uiNorm
    N U V hacute W hmap
  have hdispR : displacementSquare R = AR.adjoint ∘ₗ AR := by
    ext x
    simp [displacementSquare, AR, R, map_sub,
      LinearMap.comp_apply]
  have hdispW : displacementSquare W.toLinearMap = AW.adjoint ∘ₗ AW := by
    ext x
    simp [displacementSquare, AW, map_sub,
      LinearMap.comp_apply]
  change UnitarilyInvariantSeminorm.nuclear (displacementSquare R) ≤
    UnitarilyInvariantSeminorm.nuclear
      (displacementSquare W.toLinearMap) at h
  rw [hdispR, hdispW,
    UnitarilyInvariantSeminorm.nuclear_adjoint_comp_self_eq_sum_sq_norm AR b,
    UnitarilyInvariantSeminorm.nuclear_adjoint_comp_self_eq_sum_sq_norm AW b] at h
  have h' : (∑ i, ‖b i - directRotation U V hacute (b i)‖ ^ 2)
      ≤ ∑ i, ‖b i - W (b i)‖ ^ 2 := h
  simpa [norm_sub_rev] using h'

/-! ### The intertwiner `J`, the angle operator `Θ`, and Corollary 3.2

Davis--Kahan write the direct rotation as `U = cos Θ + J sin Θ`, with `J` the
polar isometry factor of the off-diagonal block `S₀ = J₀ sin Θ₀`.  On the full
space `angleComplexStructure` is that `J` and `directRotation_eq_cos_add_J_sin`
is that equation; the results here supply the properties the paper states about
the pair `(Θ, J)`: the skew-part reading of `J sin Θ`, the operator Pythagoras
identity, Proposition 3.5's commutation statements, and Corollary 3.2 in its
printed `J ↦ -J` form.

`Θ` commutes with `J` (`angleOperator_comm_angleComplexStructure`) and `J` is a
complex structure on the nonzero-angle space
(`angleComplexStructure_comp_self`); both rest on
`TauCeti.moorePenroseInverse_comm_of_isSymmetric`, the staging library's
commutation lemma for the pseudoinverse of a self-adjoint map.

The exponential form `U = exp (J Θ)` is proved downstream, in
`DavisKahan/FiniteDimensional/DirectRotation/Exponential.lean`, on top of these
two results. -/

/-- **The positive cosine is the Hermitian part of the direct rotation.**

`cos Θ = (U + U⁻¹)/2`, the halved form of `two_smul_abs_canonicalIntertwiner`.
It is the identity that makes the paper's `U = cos Θ + J sin Θ` readable as a
splitting of `U` into its Hermitian and skew parts. -/
theorem directRotationCosine_eq_half_smul_add (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    directRotationCosine U V =
      (2 : 𝕜)⁻¹ • ((directRotation U V hacute).toLinearMap +
        (directRotation U V hacute).symm.toLinearMap) := by
  have h := two_smul_abs_canonicalIntertwiner U V hacute
  have h2 : (2 : 𝕜) ≠ 0 := two_ne_zero
  rw [← h, directRotationCosine, smul_smul, inv_mul_cancel₀ h2, one_smul]

/-- **`J sin Θ` is the skew part of the direct rotation**: `U - cos Θ = (U - U⁻¹)/2`.

Davis--Kahan build `J` from the polar resolution `S₀ = J₀ sin Θ₀` of the
off-diagonal block.  On the full space that block is exactly the skew-Hermitian
part of `U`, so `angleComplexStructure` composed with `sin Θ` recovers it; this
lemma is that identification. -/
theorem directRotation_sub_cosine_eq_half_smul_sub (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (directRotation U V hacute).toLinearMap - directRotationCosine U V =
      (2 : 𝕜)⁻¹ • ((directRotation U V hacute).toLinearMap -
        (directRotation U V hacute).symm.toLinearMap) := by
  rw [directRotationCosine_eq_half_smul_add U V hacute]
  module

/-- **`Θ` is unchanged when the roles of `P` and `Q` are interchanged** — the
first half of Davis--Kahan Corollary 3.2, at the level of `sin Θ`.

`|P_U - P_V| = |P_V - P_U|`, because the modulus does not see a sign. -/
theorem sinAngleOperator_comm (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    sinAngleOperator V U = sinAngleOperator U V := by
  have hneg : (projection V - projection U : E →ₗ[𝕜] E) =
      -(projection U - projection V) := by abel
  rw [sinAngleOperator, sinAngleOperator, hneg, TauCeti.operatorAbs_neg]

/-- The positive cosine is symmetric in the two subspaces.

`S(V,U) = S(U,V)⋆` and, in the acute case, `S(U,V)` is normal, so the two moduli
agree.  Together with `sinAngleOperator_comm` this is "`Θ` remains the same"
of Corollary 3.2. -/
theorem directRotationCosine_comm (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    directRotationCosine V U = directRotationCosine U V := by
  rw [directRotationCosine, directRotationCosine, ← adjoint_canonicalIntertwiner U V,
    TauCeti.operatorAbs_adjoint_of_normal
      (canonicalIntertwiner_normal_of_acute U V hacute)]

/-- **Davis--Kahan Corollary 3.2, in the paper's printed form: interchanging
`P` and `Q` leaves `Θ` unchanged and replaces `J` by `-J`.**

The census recorded this row as narrowed to `U ↦ U⋆`.  That form
(`directRotation_symm`) is the input, not the conclusion: from
`U(V,U) = U(U,V)⁻¹` and `2 cos Θ = U + U⁻¹` one gets
`U(V,U) - cos Θ = -(U(U,V) - cos Θ)`, and the Moore--Penrose factor is the same
on both sides because `Θ` is symmetric.  The `Θ` half is
`sinAngleOperator_comm`, `directRotationCosine_comm` and `angleOperator_comm`. -/
theorem angleComplexStructure_symm (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    angleComplexStructure V U hacute.symm = -angleComplexStructure U V hacute := by
  have hR : (directRotation V U hacute.symm).toLinearMap =
      (directRotation U V hacute).symm.toLinearMap := by
    rw [directRotation_symm U V hacute]
  rw [angleComplexStructure, angleComplexStructure, hR,
    directRotationCosine_comm U V hacute, sinAngleOperator_comm U V,
    ← LinearMap.neg_comp]
  congr 1
  rw [directRotationCosine_eq_half_smul_add U V hacute]
  module

/-- **Operator Pythagoras for the two-projection pair: `sin²Θ + cos²Θ = 1`.**

`cos Θ` is the modulus of the canonical intertwiner `S = P_V P_U + P_{Vᗮ} P_{Uᗮ}`
and `sin Θ` is `|P_U - P_V|`, so the identity reduces to
`(P-Q)² + P Q P + (1-P)(1-Q)(1-P) = 1`, which holds for any two idempotents and
needs no acuteness hypothesis.  Everything below that says "`Θ` commutes with
`X`" is this identity together with the corresponding statement for `cos Θ`. -/
theorem sq_sinAngleOperator_add_sq_directRotationCosine (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    sinAngleOperator U V ∘ₗ sinAngleOperator U V +
        directRotationCosine U V ∘ₗ directRotationCosine U V = LinearMap.id := by
  have hDadj : (projection U - projection V : E →ₗ[𝕜] E).adjoint
      = projection U - projection V := by
    rw [map_sub, (projection_isSymmetric U).adjoint_eq,
      (projection_isSymmetric V).adjoint_eq]
  have hsin : sinAngleOperator U V ∘ₗ sinAngleOperator U V
      = (projection U - projection V) ∘ₗ (projection U - projection V) := by
    rw [sinAngleOperator, TauCeti.operatorAbs_mul_self, hDadj]
  have hcos : directRotationCosine U V ∘ₗ directRotationCosine U V
      = projection U ∘ₗ projection V ∘ₗ projection U +
        complementaryProjection U ∘ₗ complementaryProjection V ∘ₗ
          complementaryProjection U := by
    rw [directRotationCosine, TauCeti.operatorAbs_mul_self,
      canonicalIntertwiner_adjoint_comp_self]
  rw [hsin, hcos, complementaryProjection_eq_id_sub U,
    complementaryProjection_eq_id_sub V]
  set p : E →ₗ[𝕜] E := projection U with hpdef
  set q : E →ₗ[𝕜] E := projection V with hqdef
  have hp : p * p = p := by
    ext x
    change projection U (projection U x) = projection U x
    exact Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem x)
  have hq : q * q = q := by
    ext x
    change projection V (projection V x) = projection V x
    exact Submodule.starProjection_eq_self_iff.mpr (V.starProjection_apply_mem x)
  have hmul : ∀ f g : E →ₗ[𝕜] E, f ∘ₗ g = f * g := fun _ _ => rfl
  have hone : (LinearMap.id : E →ₗ[𝕜] E) = 1 := rfl
  simp only [hmul, hone]
  have key : (p - q) * (p - q) +
      (p * (q * p) + (1 - p) * ((1 - q) * (1 - p))) - 1
      = 2 * (p * p - p) + (q * q - q) := by
    noncomm_ring
  rw [hp, hq] at key
  simp only [sub_self, mul_zero, add_zero] at key
  exact sub_eq_zero.mp key

/-- **`Θ` commutes with `U`** (Davis--Kahan Proposition 3.5), at the level of
`sin Θ`.

`U` commutes with `cos Θ` (`directRotation_comm_cosine`), hence with `cos²Θ`,
hence with `sin²Θ = 1 - cos²Θ`, and commutation passes to the positive square
root. -/
theorem directRotation_comm_sinAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (directRotation U V hacute).toLinearMap ∘ₗ sinAngleOperator U V =
      sinAngleOperator U V ∘ₗ (directRotation U V hacute).toLinearMap := by
  have hgram : (directRotation U V hacute).toLinearMap ∘ₗ
      ((projection U - projection V : E →ₗ[𝕜] E).adjoint ∘ₗ
        (projection U - projection V)) =
      ((projection U - projection V : E →ₗ[𝕜] E).adjoint ∘ₗ
        (projection U - projection V)) ∘ₗ
        (directRotation U V hacute).toLinearMap := by
    have hsq : (projection U - projection V : E →ₗ[𝕜] E).adjoint ∘ₗ
        (projection U - projection V)
        = LinearMap.id - directRotationCosine U V ∘ₗ directRotationCosine U V := by
      have h := sq_sinAngleOperator_add_sq_directRotationCosine U V
      have hDadj : (projection U - projection V : E →ₗ[𝕜] E).adjoint
          = projection U - projection V := by
        rw [map_sub, (projection_isSymmetric U).adjoint_eq,
          (projection_isSymmetric V).adjoint_eq]
      have hsin : sinAngleOperator U V ∘ₗ sinAngleOperator U V
          = (projection U - projection V) ∘ₗ (projection U - projection V) := by
        rw [sinAngleOperator, TauCeti.operatorAbs_mul_self, hDadj]
      rw [hDadj, ← hsin]
      exact eq_sub_of_add_eq h
    have hcomm := directRotation_comm_cosine U V hacute
    rw [hsq]
    have hmul : ∀ f g : E →ₗ[𝕜] E, f ∘ₗ g = f * g := fun _ _ => rfl
    have hone : (LinearMap.id : E →ₗ[𝕜] E) = 1 := rfl
    simp only [hmul, hone] at hcomm ⊢
    have hc : Commute (directRotation U V hacute).toLinearMap
        (directRotationCosine U V) := hcomm
    exact (Commute.one_right _).sub_right (hc.mul_right hc)
  exact TauCeti.sqrt_comm
    (LinearMap.isPositive_adjoint_comp_self (projection U - projection V)) hgram

/-- **`Θ` commutes with `P`** (Davis--Kahan Proposition 3.5), at the level of
`sin Θ`.  `P_U` commutes with the Gram operator `S⋆S = cos²Θ`, and the
Pythagoras identity transfers that to `sin²Θ` and then to `sin Θ`. -/
theorem projection_comm_sinAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    projection U ∘ₗ sinAngleOperator U V =
      sinAngleOperator U V ∘ₗ projection U := by
  have hgram : projection U ∘ₗ
      ((projection U - projection V : E →ₗ[𝕜] E).adjoint ∘ₗ
        (projection U - projection V)) =
      ((projection U - projection V : E →ₗ[𝕜] E).adjoint ∘ₗ
        (projection U - projection V)) ∘ₗ projection U := by
    have hsq : (projection U - projection V : E →ₗ[𝕜] E).adjoint ∘ₗ
        (projection U - projection V)
        = LinearMap.id - directRotationCosine U V ∘ₗ directRotationCosine U V := by
      have h := sq_sinAngleOperator_add_sq_directRotationCosine U V
      have hDadj : (projection U - projection V : E →ₗ[𝕜] E).adjoint
          = projection U - projection V := by
        rw [map_sub, (projection_isSymmetric U).adjoint_eq,
          (projection_isSymmetric V).adjoint_eq]
      have hsin : sinAngleOperator U V ∘ₗ sinAngleOperator U V
          = (projection U - projection V) ∘ₗ (projection U - projection V) := by
        rw [sinAngleOperator, TauCeti.operatorAbs_mul_self, hDadj]
      rw [hDadj, ← hsin]
      exact eq_sub_of_add_eq h
    have hcomm : projection U ∘ₗ
        (directRotationCosine U V ∘ₗ directRotationCosine U V) =
        (directRotationCosine U V ∘ₗ directRotationCosine U V) ∘ₗ projection U := by
      have h := projection_comm_abs_canonicalIntertwiner U V
      have hmul : ∀ f g : E →ₗ[𝕜] E, f ∘ₗ g = f * g := fun _ _ => rfl
      simp only [hmul, directRotationCosine] at h ⊢
      have hc : Commute (projection U)
          (TauCeti.operatorAbs (canonicalIntertwiner U V)) := h
      exact hc.mul_right hc
    rw [hsq]
    have hmul : ∀ f g : E →ₗ[𝕜] E, f ∘ₗ g = f * g := fun _ _ => rfl
    have hone : (LinearMap.id : E →ₗ[𝕜] E) = 1 := rfl
    simp only [hmul, hone] at hcomm ⊢
    have hc2 : Commute (projection U)
        (directRotationCosine U V ∘ₗ directRotationCosine U V) := hcomm
    exact (Commute.one_right _).sub_right hc2
  exact TauCeti.sqrt_comm
    (LinearMap.isPositive_adjoint_comp_self (projection U - projection V)) hgram

/-- **`Θ` commutes with `Q`** (Davis--Kahan Proposition 3.5), at the level of
`sin Θ`, by the symmetry of `sin Θ` in the two subspaces. -/
theorem projection_right_comm_sinAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    projection V ∘ₗ sinAngleOperator U V =
      sinAngleOperator U V ∘ₗ projection V := by
  have h := projection_comm_sinAngleOperator V U
  rwa [sinAngleOperator_comm U V] at h

/-- **`Θ` is symmetric in the two subspaces** — "`Θ` remains the same" of
Corollary 3.2, at the level of the angle operator itself. -/
theorem angleOperator_comm (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    angleOperator V U = angleOperator U V :=
  TauCeti.selfAdjointFunctionalCalculus_congr_op _ _
    (sinAngleOperator_comm U V) Real.arcsin

/-- **`Θ` commutes with `U`** — Davis--Kahan Proposition 3.5, stated on the
angle operator `Θ = arcsin (sin Θ)`.  Anything commuting with `sin Θ` commutes
with every real functional calculus of it. -/
theorem angleOperator_comm_directRotation (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (directRotation U V hacute).toLinearMap ∘ₗ angleOperator U V =
      angleOperator U V ∘ₗ (directRotation U V hacute).toLinearMap :=
  TauCeti.selfAdjointFunctionalCalculus_comm _ Real.arcsin
    (directRotation_comm_sinAngleOperator U V hacute)

/-- **`Θ` commutes with `P`** — Davis--Kahan Proposition 3.5, on the angle
operator. -/
theorem angleOperator_comm_projection (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    projection U ∘ₗ angleOperator U V = angleOperator U V ∘ₗ projection U :=
  TauCeti.selfAdjointFunctionalCalculus_comm _ Real.arcsin
    (projection_comm_sinAngleOperator U V)

/-- **`Θ` commutes with `Q`** — Davis--Kahan Proposition 3.5, on the angle
operator. -/
theorem angleOperator_comm_projection_right (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    projection V ∘ₗ angleOperator U V = angleOperator U V ∘ₗ projection V :=
  TauCeti.selfAdjointFunctionalCalculus_comm _ Real.arcsin
    (projection_right_comm_sinAngleOperator U V)

/-- **`cos Θ` commutes with `sin Θ`.**

The Gram operator of the canonical intertwiner is `cos²Θ`, and by operator
Pythagoras it is also `1 - sin²Θ`; the positive cosine commutes with that, hence
with its positive square root `sin Θ`.  No acuteness is needed. -/
theorem directRotationCosine_comm_sinAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    directRotationCosine U V ∘ₗ sinAngleOperator U V =
      sinAngleOperator U V ∘ₗ directRotationCosine U V := by
  have hgram : directRotationCosine U V ∘ₗ
      ((projection U - projection V : E →ₗ[𝕜] E).adjoint ∘ₗ
        (projection U - projection V)) =
      ((projection U - projection V : E →ₗ[𝕜] E).adjoint ∘ₗ
        (projection U - projection V)) ∘ₗ directRotationCosine U V := by
    have hDadj : (projection U - projection V : E →ₗ[𝕜] E).adjoint
        = projection U - projection V := by
      rw [map_sub, (projection_isSymmetric U).adjoint_eq,
        (projection_isSymmetric V).adjoint_eq]
    have hsin : sinAngleOperator U V ∘ₗ sinAngleOperator U V
        = (projection U - projection V) ∘ₗ (projection U - projection V) := by
      rw [sinAngleOperator, TauCeti.operatorAbs_mul_self, hDadj]
    have hsq : (projection U - projection V : E →ₗ[𝕜] E).adjoint ∘ₗ
        (projection U - projection V)
        = LinearMap.id - directRotationCosine U V ∘ₗ directRotationCosine U V := by
      rw [hDadj, ← hsin]
      exact eq_sub_of_add_eq (sq_sinAngleOperator_add_sq_directRotationCosine U V)
    rw [hsq]
    have hmul : ∀ f g : E →ₗ[𝕜] E, f ∘ₗ g = f * g := fun _ _ => rfl
    have hone : (LinearMap.id : E →ₗ[𝕜] E) = 1 := rfl
    simp only [hmul, hone]
    noncomm_ring
  exact TauCeti.sqrt_comm
    (LinearMap.isPositive_adjoint_comp_self (projection U - projection V)) hgram

/-- **`Θ` commutes with `cos Θ`** — Davis--Kahan Proposition 3.5, on the angle
operator. -/
theorem angleOperator_comm_directRotationCosine (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    directRotationCosine U V ∘ₗ angleOperator U V =
      angleOperator U V ∘ₗ directRotationCosine U V :=
  TauCeti.selfAdjointFunctionalCalculus_comm _ Real.arcsin
    (directRotationCosine_comm_sinAngleOperator U V)

/-- `sin Θ` commutes with itself, restated as commutation with `Θ`. -/
theorem angleOperator_comm_sinAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    sinAngleOperator U V ∘ₗ angleOperator U V =
      angleOperator U V ∘ₗ sinAngleOperator U V :=
  TauCeti.selfAdjointFunctionalCalculus_comm _ Real.arcsin rfl

/-- **`Θ` commutes with the Moore--Penrose inverse of `sin Θ`.**

`sin Θ` is self-adjoint, so `TauCeti.moorePenroseInverse_comm_of_isSymmetric`
carries the commutation of `Θ` with `sin Θ` across the pseudoinverse. -/
theorem angleOperator_comm_moorePenroseInverse_sinAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    angleOperator U V ∘ₗ TauCeti.moorePenroseInverse (sinAngleOperator U V) =
      TauCeti.moorePenroseInverse (sinAngleOperator U V) ∘ₗ angleOperator U V :=
  TauCeti.moorePenroseInverse_comm_of_isSymmetric
    (TauCeti.isPositive_operatorAbs (projection U - projection V)).isSymmetric
    (angleOperator_comm_sinAngleOperator U V).symm

/-- **`Θ` commutes with `J`** — the remaining commutation statement of
Davis--Kahan Proposition 3.5.

`J = (U - cos Θ) (sin Θ)⁺`, and `Θ` commutes with each of the three factors:
with `U` (`angleOperator_comm_directRotation`), with `cos Θ`
(`angleOperator_comm_directRotationCosine`), and with `(sin Θ)⁺`
(`angleOperator_comm_moorePenroseInverse_sinAngleOperator`). -/
theorem angleOperator_comm_angleComplexStructure (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    angleComplexStructure U V hacute ∘ₗ angleOperator U V =
      angleOperator U V ∘ₗ angleComplexStructure U V hacute := by
  have hmul : ∀ f g : E →ₗ[𝕜] E, f ∘ₗ g = f * g := fun _ _ => rfl
  have hR : (directRotation U V hacute).toLinearMap * angleOperator U V =
      angleOperator U V * (directRotation U V hacute).toLinearMap := by
    simpa [hmul] using angleOperator_comm_directRotation U V hacute
  have hC : directRotationCosine U V * angleOperator U V =
      angleOperator U V * directRotationCosine U V := by
    simpa [hmul] using angleOperator_comm_directRotationCosine U V
  have hG : angleOperator U V * TauCeti.moorePenroseInverse (sinAngleOperator U V) =
      TauCeti.moorePenroseInverse (sinAngleOperator U V) * angleOperator U V := by
    simpa [hmul] using angleOperator_comm_moorePenroseInverse_sinAngleOperator U V
  have hdiff : ((directRotation U V hacute).toLinearMap - directRotationCosine U V) *
      angleOperator U V =
      angleOperator U V *
        ((directRotation U V hacute).toLinearMap - directRotationCosine U V) := by
    rw [sub_mul, mul_sub, hR, hC]
  change (((directRotation U V hacute).toLinearMap - directRotationCosine U V) ∘ₗ
      TauCeti.moorePenroseInverse (sinAngleOperator U V)) ∘ₗ angleOperator U V = _
  simp only [hmul, angleComplexStructure]
  calc ((directRotation U V hacute).toLinearMap - directRotationCosine U V) *
        TauCeti.moorePenroseInverse (sinAngleOperator U V) * angleOperator U V
      = ((directRotation U V hacute).toLinearMap - directRotationCosine U V) *
        (TauCeti.moorePenroseInverse (sinAngleOperator U V) * angleOperator U V) := by
        noncomm_ring
    _ = ((directRotation U V hacute).toLinearMap - directRotationCosine U V) *
        (angleOperator U V * TauCeti.moorePenroseInverse (sinAngleOperator U V)) := by
        rw [hG]
    _ = (((directRotation U V hacute).toLinearMap - directRotationCosine U V) *
        angleOperator U V) * TauCeti.moorePenroseInverse (sinAngleOperator U V) := by
        noncomm_ring
    _ = (angleOperator U V *
        ((directRotation U V hacute).toLinearMap - directRotationCosine U V)) *
        TauCeti.moorePenroseInverse (sinAngleOperator U V) := by rw [hdiff]
    _ = angleOperator U V *
        (((directRotation U V hacute).toLinearMap - directRotationCosine U V) *
          TauCeti.moorePenroseInverse (sinAngleOperator U V)) := by noncomm_ring

/-- The inverse rotation also commutes with the positive cosine.

`U(V,U) = U(U,V)⁻¹` and `cos Θ` is symmetric in the pair, so this is
`directRotation_comm_cosine` read at the swapped pair. -/
theorem directRotation_symm_comm_cosine (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    (directRotation U V hacute).symm.toLinearMap ∘ₗ directRotationCosine U V =
      directRotationCosine U V ∘ₗ (directRotation U V hacute).symm.toLinearMap := by
  have h := directRotation_comm_cosine V U hacute.symm
  rwa [directRotation_symm U V hacute, directRotationCosine_comm U V hacute] at h

/-- **The skew part of the direct rotation squares to `-sin²Θ`.**

`U - cos Θ = -(U⁻¹ - cos Θ)` because `U + U⁻¹ = 2 cos Θ`, and
`(U⁻¹ - cos Θ)(U - cos Θ) = 1 - cos²Θ = sin²Θ` because `cos Θ` commutes with
both `U` and `U⁻¹`.  This is the operator identity behind the paper's assertion
that `J` is a complex structure. -/
theorem directRotation_sub_cosine_comp_self (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    ((directRotation U V hacute).toLinearMap - directRotationCosine U V) ∘ₗ
        ((directRotation U V hacute).toLinearMap - directRotationCosine U V) =
      -(sinAngleOperator U V ∘ₗ sinAngleOperator U V) := by
  have hmul : ∀ f g : E →ₗ[𝕜] E, f ∘ₗ g = f * g := fun _ _ => rfl
  have hone : (LinearMap.id : E →ₗ[𝕜] E) = 1 := rfl
  set R := (directRotation U V hacute).toLinearMap with hRdef
  set S := (directRotation U V hacute).symm.toLinearMap with hSdef
  set C := directRotationCosine U V with hCdef
  have hSR : S * R = 1 := by
    have happ : ∀ x : E, S (R x) = x := fun x =>
      (directRotation U V hacute).symm_apply_apply x
    ext x
    exact happ x
  have hCR : C * R = R * C := (directRotation_comm_cosine U V hacute).symm
  have hCS : C * S = S * C := (directRotation_symm_comm_cosine U V hacute).symm
  have hsum : R + S = (2 : 𝕜) • C := by
    have h := directRotationCosine_eq_half_smul_add U V hacute
    rw [← hCdef, ← hRdef, ← hSdef] at h
    rw [h, smul_smul, mul_inv_cancel₀ (two_ne_zero : (2 : 𝕜) ≠ 0), one_smul]
  have hpyth : sinAngleOperator U V * sinAngleOperator U V = 1 - C * C := by
    have h := sq_sinAngleOperator_add_sq_directRotationCosine U V
    rw [← hCdef] at h
    simp only [hmul, hone] at h
    exact eq_sub_of_add_eq h
  have hprod : (S - C) * (R - C) = 1 - C * C := by
    have expand : (S - C) * (R - C) = S * R - S * C - C * R + C * C := by noncomm_ring
    rw [expand, hSR, ← hCS]
    have hgroup : (1 : E →ₗ[𝕜] E) - C * S - C * R + C * C
        = 1 - C * (R + S) + C * C := by noncomm_ring
    rw [hgroup, hsum, mul_smul_comm, two_smul]
    noncomm_ring
  have hneg : R - C = -(S - C) := by
    rw [neg_sub]
    refine eq_sub_of_add_eq ?_
    have hcc : C + C = R + S := by
      rw [← two_smul 𝕜 C]
      exact hsum.symm
    rw [sub_add_eq_add_sub, ← hcc]
    abel
  simp only [hmul]
  calc (R - C) * (R - C) = (-(S - C)) * (R - C) := by rw [← hneg]
    _ = -((S - C) * (R - C)) := by rw [neg_mul]
    _ = -(1 - C * C) := by rw [hprod]
    _ = -(sinAngleOperator U V * sinAngleOperator U V) := by rw [hpyth]

/-- **`J` is a complex structure on the nonzero-angle space**: `J² = -(sin Θ)(sin Θ)⁺`,
the negative of the orthogonal projection onto the range of `sin Θ`.

This is the precise form of Davis--Kahan's `J² = -1`: the paper sets `J = 0` on
`Null Θ`, so the identity can only hold on the orthogonal complement of that
space, which is exactly the Penrose projection `(sin Θ)(sin Θ)⁺`.

`(sin Θ)⁺` commutes with `U - cos Θ` because `sin Θ` does and `sin Θ` is
self-adjoint, so `J² = (U - cos Θ)² ((sin Θ)⁺)² = -(sin Θ)²((sin Θ)⁺)²`, and the
Penrose identities collapse the right-hand factor to the projection. -/
theorem angleComplexStructure_comp_self (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    angleComplexStructure U V hacute ∘ₗ angleComplexStructure U V hacute =
      -(sinAngleOperator U V ∘ₗ
        TauCeti.moorePenroseInverse (sinAngleOperator U V)) := by
  have hmul : ∀ f g : E →ₗ[𝕜] E, f ∘ₗ g = f * g := fun _ _ => rfl
  have hsym : (sinAngleOperator U V).IsSymmetric :=
    (TauCeti.isPositive_operatorAbs (projection U - projection V)).isSymmetric
  set D := (directRotation U V hacute).toLinearMap - directRotationCosine U V with hDdef
  set A := sinAngleOperator U V with hAdef
  set G := TauCeti.moorePenroseInverse (sinAngleOperator U V) with hGdef
  -- `sin Θ` commutes with the skew part, hence so does its pseudoinverse.
  have hAD : A * D = D * A := by
    have hR : A * (directRotation U V hacute).toLinearMap =
        (directRotation U V hacute).toLinearMap * A := by
      simpa [hmul, hAdef] using (directRotation_comm_sinAngleOperator U V hacute).symm
    have hC : A * directRotationCosine U V = directRotationCosine U V * A := by
      simpa [hmul, hAdef] using (directRotationCosine_comm_sinAngleOperator U V).symm
    rw [hDdef, mul_sub, sub_mul, hR, hC]
  have hGD : G * D = D * G := by
    have h := TauCeti.moorePenroseInverse_comm_of_isSymmetric hsym
      (show D ∘ₗ sinAngleOperator U V = sinAngleOperator U V ∘ₗ D by
        simpa [hmul, hAdef] using hAD.symm)
    simpa [hmul, hGdef, hAdef] using h.symm
  have hD2 : D * D = -(A * A) := by
    simpa [hmul, hDdef, hAdef] using directRotation_sub_cosine_comp_self U V hacute
  have hAG : A * G = G * A := by
    simpa [hmul, hAdef, hGdef] using
      TauCeti.comp_moorePenroseInverse_comm_of_isSymmetric hsym
  have hGAG : G * A * G = G := by
    simpa [hmul, hAdef, hGdef, mul_assoc] using
      TauCeti.moorePenroseInverse_comp_comp (sinAngleOperator U V)
  have hproj : A * A * (G * G) = A * G := by
    calc A * A * (G * G) = A * (A * G) * G := by noncomm_ring
      _ = A * (G * A) * G := by rw [hAG]
      _ = A * (G * A * G) := by noncomm_ring
      _ = A * G := by rw [hGAG]
  change (D ∘ₗ G) ∘ₗ (D ∘ₗ G) = _
  simp only [hmul]
  calc D * G * (D * G) = D * (G * D) * G := by noncomm_ring
    _ = D * (D * G) * G := by rw [hGD]
    _ = D * D * (G * G) := by noncomm_ring
    _ = -(A * A) * (G * G) := by rw [hD2]
    _ = -(A * A * (G * G)) := by noncomm_ring
    _ = -(A * G) := by rw [hproj]
end DavisKahan.FiniteDimensional
end TauCeti
