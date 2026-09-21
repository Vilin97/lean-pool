/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.DoubleAngleTangentOperator
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.TanTwoTheta.BoundedOffDiagonalRiccati
import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.OperatorAngleComplex
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.GraphSubspace
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.OperatorModulus
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.SubspaceSingularTransport

/-! # Canonical Tangent Bridge -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Canonical ambient tangent versus the graph-coordinate tangent

For a quarter-acute pair `U,V`, let `Y` be the canonical ambient angular
operator and `X : U -> U-perp` its rectangular coordinate.  The projection
onto `V = graph(Y)` has the normal-equation formula

`Q = (P+Y) (1+Y*Y)^-1 (P+Y*)`.

Writing `G=Y*Y`, its two source compressions are

`PQP = (1+G)^-1 P`,
`P(1-Q)P = G(1+G)^-1 P`.

Consequently, on `U`,

`sin(2Theta) = 2 sqrt(G) (1+G)^-1`,
`cos(2Theta) = (1-G)(1+G)^-1`,

and both operators vanish on `U-perp`.  Since `||Y||<1`, the extended cosine
is invertible and therefore

`tan(2Theta) = 2 sqrt(G) (1-G)^-1`.

The right side is exactly the modulus of the ambient graph-coordinate operator
`2Y(1-Y*Y)^-1`.  Extending the rectangular coordinate operator by zero gives
that ambient operator, so the canonical tangent and the rectangular graph
tangent have the same complete approximation-number sequence.

*Moved, not restated.*  Promoted verbatim out of the non-default
`FinishTanTwoTheta` completion lane; only the namespace changed
(`TauCeti.DavisKahan.FinishTanTwoTheta` to `TauCeti.DavisKahan`).
-/

namespace TauCeti
namespace DavisKahan

open scoped InnerProductSpace
open TauCeti.DavisKahanExt
open TauCeti.DavisKahan.ExactSinTheta
-- `doubleAngleTangentOperator` and its denominator API live in the *sibling*
-- namespace `TauCeti.FinishTanTwoTheta` (see `FunctionalCalculus/DoubleAngleTangent.lean`),
-- not under `TauCeti.DavisKahan.FinishTanTwoTheta`, so they are not in scope here by
-- enclosure. `SharpIdeal.lean` fully qualifies every use instead; this open is the
-- same fix in one line. The namespace split itself is a library-organisation defect.
-- `DoubleAngleTangentOperator` moved to `DavisKahan/Sources/DavisKahan1970/` on 2026-07-31
-- (lane `FTT-PROMOTE-DAT`), taking its declarations into `TauCeti.DavisKahan`; the old
-- namespace is no longer in this module's import closure at all, so opening it is an error
-- rather than a no-op.
open TauCeti.DavisKahan

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- An orthogonally complemented subspace is complete.  `DavisKahan.SinTheta.Natural.Reducing`
declares the same instance, but `local`, so it is not exported to importing modules and has to
be repeated here.  Without it every `ContinuousLinearMap.adjoint` on a subspace in this file
fails to elaborate with `failed to synthesize CompleteSpace ↥U`. -/
noncomputable local instance completeSpaceOfHasOrthogonalProjection
    (W : Submodule ℂ E) [W.HasOrthogonalProjection] : CompleteSpace W :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection W).completeSpace_coe

/-- `J⋆ J = 1` for the inclusion `J = W.subtypeL` of an orthogonally complemented
subspace.  This is the *only* coercion-level fact the block decompositions below
need: with it, and with `J J⋆ = W.starProjection` (which is definitional, since
`starProjection` *is* `subtypeL ∘L orthogonalProjectionOnto`), every block identity
becomes operator algebra in `E` with no `⟨_, _⟩` bookkeeping. -/
private theorem adjoint_subtypeL_comp_subtypeL
    (W : Submodule ℂ E) [W.HasOrthogonalProjection] :
    W.subtypeL.adjoint ∘L W.subtypeL = ContinuousLinearMap.id ℂ W := by
  ext x
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    Submodule.adjoint_subtypeL, Submodule.subtypeL_apply]
  -- `ext` has already descended to the coercion level, so take the coercion of
  -- the subspace-level identity.
  exact congrArg (fun z : W => (z : E))
    (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x)

/-- `J J⋆ = P`, the projection onto `W`.  True by definition of `starProjection`
once `adjoint_subtypeL` rewrites `J⋆` to `orthogonalProjectionOnto`. -/
private theorem subtypeL_comp_adjoint_subtypeL
    (W : Submodule ℂ E) [W.HasOrthogonalProjection] :
    W.subtypeL ∘L W.subtypeL.adjoint = W.starProjection := by
  rw [Submodule.adjoint_subtypeL]
  rfl

private theorem ambientAngularOperator_eq_extendCoordinate
    (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (Y : E →L[ℂ] E) (hY : IsAngularOperator U Y) :
    Y = Uᗮ.subtypeL ∘L subspaceAngularCoordinate U Y ∘L U.subtypeL.adjoint := by
  apply ContinuousLinearMap.ext
  intro x
  have hYP : Y (U.starProjection x) = Y x := by
    have h := DFunLike.congr_fun hY.1 x
    -- `h : (Y ∘ P) x = Y x` is already the right way round -- the `.symm` was
    -- backwards -- and `IsAngularOperator` states its field with
    -- `DavisKahan.projection`, so that abbreviation has to be unfolded for the
    -- goal's `U.starProjection` to match.
    simpa only [ContinuousLinearMap.comp_apply] using h
  -- Rewrite the ambient right-hand side instead of `change`-ing the goal.  The
  -- adjoint of `subtypeL` is the orthogonal projection *into* the subspace
  -- (`Submodule.adjoint_subtypeL`) and its coercion back to `E` is
  -- `starProjection`; neither step is definitional, so `change` cannot bridge
  -- them and the old `⟨U.starProjection x, _⟩` pattern never matched.
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply,
    coe_subspaceAngularCoordinate_apply U Y hY (U.subtypeL.adjoint x),
    Submodule.adjoint_subtypeL, ← Submodule.starProjection_apply, hYP]

/-- The ambient graph tangent `2 Y (1 − Y⋆Y)⁻¹` is the zero-extension of the
rectangular coordinate tangent `2 X (1 − X⋆X)⁻¹`.  Made public because the
whole-space `tan 2Θ` theorem identifies the *off-diagonal corner* of its block
representative with the ambient graph tangent and then transports the sharp
Ky Fan estimate, which is stated for the coordinate operator. -/
theorem ambient_doubleAngleTangent_eq_extendCoordinate
    (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (Y : E →L[ℂ] E) (hY : IsAngularOperator U Y)
    (hcontractive : ‖Y‖ < 1) :
    doubleAngleTangentOperator Y hcontractive =
      Uᗮ.subtypeL ∘L
        doubleAngleTangentOperator (subspaceAngularCoordinate U Y)
          ((norm_subspaceAngularCoordinate_le U Y).trans_lt hcontractive) ∘L
        U.subtypeL.adjoint := by
  let X : U →L[ℂ] Uᗮ := subspaceAngularCoordinate U Y
  let P : E →L[ℂ] E := U.starProjection
  have hYext : Y = Uᗮ.subtypeL ∘L X ∘L U.subtypeL.adjoint :=
    ambientAngularOperator_eq_extendCoordinate U Y hY
  have hYP : Y ∘L P = Y := hY.1
  have hPY : P ∘L Y = 0 := hY.2
  -- `star_mul` cannot fire on `P ∘L Y`: for endomorphisms `∘L` is *defeq* to `*`
  -- but not syntactically equal, so `simp only` never matches.  Go through
  -- `adjoint_comp`, which is stated for `∘L` directly.
  have hPadj : ContinuousLinearMap.adjoint P = P := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using
      (isSelfAdjoint_starProjection U).star_eq
  have hYstarP : Y.adjoint ∘L P = 0 := by
    have h := congrArg ContinuousLinearMap.adjoint hPY
    rwa [ContinuousLinearMap.adjoint_comp, hPadj, map_zero] at h
  have hPYstar : P ∘L Y.adjoint = Y.adjoint := by
    have h := congrArg ContinuousLinearMap.adjoint hYP
    rwa [ContinuousLinearMap.adjoint_comp, hPadj] at h
  let G : E →L[ℂ] E := Y.adjoint ∘L Y
  let D : E →L[ℂ] E := doubleAngleDenominator Y
  let DX : U →L[ℂ] U := doubleAngleDenominator X
  have hGP : G ∘L P = G := by
    dsimp [G]
    rw [ContinuousLinearMap.comp_assoc, hYP]
  have hPG : P ∘L G = G := by
    dsimp [G]
    rw [← ContinuousLinearMap.comp_assoc, hPYstar]
  -- `Y⋆` in block form: `(J⊥ X J⋆)⋆ = J X⋆ J⊥⋆`.
  have hYadj : Y.adjoint
      = U.subtypeL ∘L X.adjoint ∘L Uᗮ.subtypeL.adjoint := by
    rw [hYext, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.comp_assoc]
  -- `J⊥⋆ J⊥ = 1`, stated pointwise so that it can be used as a `simp` rule
  -- inside applications (where composition brackets are not an obstacle).
  have hperp : ∀ y : Uᗮ, Uᗮ.subtypeL.adjoint (Uᗮ.subtypeL y) = y := by
    intro y
    have h := congrArg (fun T : Uᗮ →L[ℂ] Uᗮ => T y)
      (adjoint_subtypeL_comp_subtypeL Uᗮ)
    simpa using h
  -- `G = Y⋆Y = J X⋆X J⋆`: the `J⊥` factors cancel.
  have hG : G = U.subtypeL ∘L (X.adjoint ∘L X) ∘L U.subtypeL.adjoint := by
    ext x
    show Y.adjoint (Y x)
      = U.subtypeL ((X.adjoint ∘L X) (U.subtypeL.adjoint x))
    rw [hYadj, hYext]
    simp only [ContinuousLinearMap.comp_apply, hperp]
  -- `P + P⊥ = 1` as operators.
  have hPsum : U.starProjection + Uᗮ.starProjection
      = ContinuousLinearMap.id ℂ E := by
    ext x
    rw [add_apply, ContinuousLinearMap.id_apply]
    exact U.starProjection_add_starProjection_orthogonal x
  -- Now the block identity is pure algebra: `J DX J⋆ = J J⋆ - J X⋆X J⋆ = P - G`,
  -- so `D = 1 - G = (P - G) + P⊥` reduces to `P + P⊥ = 1`.  No coercions.
  have hDblock : D =
      U.subtypeL ∘L DX ∘L U.subtypeL.adjoint + Uᗮ.starProjection := by
    have hJDXJ : U.subtypeL ∘L DX ∘L U.subtypeL.adjoint
        = U.starProjection - G := by
      show U.subtypeL ∘L (ContinuousLinearMap.id ℂ U - X.adjoint ∘L X) ∘L
          U.subtypeL.adjoint = U.starProjection - G
      rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
        ContinuousLinearMap.id_comp,
        subtypeL_comp_adjoint_subtypeL U, hG]
    show ContinuousLinearMap.id ℂ E - G
        = U.subtypeL ∘L DX ∘L U.subtypeL.adjoint + Uᗮ.starProjection
    rw [hJDXJ, ← hPsum]
    abel
  have hDunit := isUnit_doubleAngleDenominator Y hcontractive
  have hDXcontractive : ‖X‖ < 1 :=
    (norm_subspaceAngularCoordinate_le U Y).trans_lt hcontractive
  have hDXunit := isUnit_doubleAngleDenominator X hDXcontractive
  -- Every cancellation is stated POINTWISE: under application the brackets are
  -- automatic, whereas no associativity convention brackets `J⋆ J` together
  -- inside a composition chain.  Same technique as `hG` above.
  have hJU : ∀ u : U, U.subtypeL.adjoint (U.subtypeL u) = u := by
    intro u
    have h := congrArg (fun T : U →L[ℂ] U => T u)
      (adjoint_subtypeL_comp_subtypeL U)
    simpa using h
  have hJJadjApp : ∀ y : E,
      U.subtypeL (U.subtypeL.adjoint y) = U.starProjection y := by
    intro y
    have h := congrArg (fun T : E →L[ℂ] E => T y)
      (subtypeL_comp_adjoint_subtypeL U)
    simpa using h
  have hJadjPerpApp : ∀ y : E,
      U.subtypeL.adjoint (Uᗮ.starProjection y) = 0 := by
    intro y
    apply Subtype.ext
    rw [Submodule.adjoint_subtypeL, ← Submodule.starProjection_apply]
    simpa using (Submodule.starProjection_apply_eq_zero_iff (K := U)).mpr
      (Uᗮ.starProjection_apply_mem y)
  have hPerpJApp : ∀ u : U, Uᗮ.starProjection (U.subtypeL u) = 0 := by
    intro u
    rw [Submodule.subtypeL_apply]
    exact (Submodule.starProjection_apply_eq_zero_iff (K := Uᗮ)).mpr
      (Submodule.le_orthogonal_orthogonal U u.2)
  have hDXinv : ∀ u : U, DX (Ring.inverse DX u) = u := by
    intro u
    have h := congrArg (fun T : U →L[ℂ] U => T u)
      (Ring.mul_inverse_cancel DX hDXunit)
    simpa using h
  have hPerpIdem : ∀ y : E,
      Uᗮ.starProjection (Uᗮ.starProjection y) = Uᗮ.starProjection y := by
    intro y
    exact Submodule.starProjection_eq_self_iff.mpr
      (Uᗮ.starProjection_apply_mem y)
  have hDinvblock : Ring.inverse D =
      U.subtypeL ∘L Ring.inverse DX ∘L U.subtypeL.adjoint +
        Uᗮ.starProjection := by
    have hcandidate :
        D ∘L (U.subtypeL ∘L Ring.inverse DX ∘L U.subtypeL.adjoint +
          Uᗮ.starProjection) = ContinuousLinearMap.id ℂ E := by
      ext x
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        add_apply, hDblock]
      simp only [add_apply, ContinuousLinearMap.comp_apply,
        map_add, hJU, hJadjPerpApp, hPerpJApp, hDXinv, hPerpIdem, hJJadjApp,
        map_zero, add_zero, zero_add]
      exact U.starProjection_add_starProjection_orthogonal x
    -- From `D B = 1` and `D⁻¹ D = 1`, cancel `D` on the left.  The old script
    -- applied *injectivity* of `D` (`isUnit_iff_bijective.mp hDunit |>.1`) to an
    -- *equation*, and that conclusion shape cannot match the goal.
    calc Ring.inverse D
        = Ring.inverse D * 1 := (mul_one _).symm
      _ = Ring.inverse D *
            (D * (U.subtypeL ∘L Ring.inverse DX ∘L U.subtypeL.adjoint +
              Uᗮ.starProjection)) := by
          rw [show D * (U.subtypeL ∘L Ring.inverse DX ∘L U.subtypeL.adjoint +
            Uᗮ.starProjection) = 1 from hcandidate]
      _ = (Ring.inverse D * D) *
            (U.subtypeL ∘L Ring.inverse DX ∘L U.subtypeL.adjoint +
              Uᗮ.starProjection) := (mul_assoc _ _ _).symm
      _ = 1 * (U.subtypeL ∘L Ring.inverse DX ∘L U.subtypeL.adjoint +
              Uᗮ.starProjection) := by
          rw [Ring.inverse_mul_cancel D hDunit]
      _ = _ := one_mul _
  -- Finish POINTWISE.  At operator level neither rewrite order works: `hYext`
  -- first also rewrites the `Y` hidden inside `X := subspaceAngularCoordinate U Y`
  -- (making it self-referential), and `hDinvblock` first leaves `Ring.inverse D`
  -- unmatched because `D = doubleAngleDenominator Y` still mentions `Y`.
  -- Applying to a vector sidesteps both.
  have hYPerpApp : ∀ y : E, Y (Uᗮ.starProjection y) = 0 := by
    intro y
    have h := DFunLike.congr_fun hYP (Uᗮ.starProjection y)
    rw [ContinuousLinearMap.comp_apply,
      (Submodule.starProjection_apply_eq_zero_iff (K := U)).mpr
        (Uᗮ.starProjection_apply_mem y)] at h
    simpa using h.symm
  apply ContinuousLinearMap.ext
  intro x
  have hDinvApp : Ring.inverse D x
      = U.subtypeL (Ring.inverse DX (U.subtypeL.adjoint x))
        + Uᗮ.starProjection x := by
    have h := congrArg (fun T : E →L[ℂ] E => T x) hDinvblock
    simpa using h
  have hYJ : Y (U.subtypeL (Ring.inverse DX (U.subtypeL.adjoint x)))
      = Uᗮ.subtypeL (X (Ring.inverse DX (U.subtypeL.adjoint x))) := by
    rw [hYext]
    simp only [ContinuousLinearMap.comp_apply, hJU]
  show (2 : ℂ) • Y (Ring.inverse D x)
      = Uᗮ.subtypeL ((2 : ℂ) • X (Ring.inverse DX (U.subtypeL.adjoint x)))
  rw [hDinvApp, map_add, hYPerpApp, add_zero, hYJ, map_smul]

-- This proof carries about forty `have`s over operators on `E`, several of them
-- `Ring.inverse` and `CFC` terms whose defeq checks are expensive; it exhausts the
-- default heartbeat budget during `whnf`.  The budget is raised rather than the
-- proof weakened -- nothing here is left incomplete or `simp`-blasted.
/-- The canonical ambient double-angle tangent is the modulus of the ambient
extension of the graph-coordinate double-angle tangent. -/
private theorem directedTanTwoAngleOperatorC_eq_modulus_ambientGraphTangent
    (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hquarter : IsQuarterAcute U V) :
    directedTanTwoAngleOperatorC U V hquarter =
      ContinuousLinearMap.modulus
        (doubleAngleTangentOperator
          (quarterAcuteAngularOperator U V hquarter)
          (norm_quarterAcuteAngularOperator_lt_one U V hquarter)) := by
  let Y : E →L[ℂ] E := quarterAcuteAngularOperator U V hquarter
  let P : E →L[ℂ] E := U.starProjection
  let Q : E →L[ℂ] E := V.starProjection
  let G : E →L[ℂ] E := Y.adjoint ∘L Y
  let N : E →L[ℂ] E := ContinuousLinearMap.id ℂ E + G
  let R : E →L[ℂ] E := Ring.inverse N
  let D : E →L[ℂ] E := ContinuousLinearMap.id ℂ E - G
  let M : E →L[ℂ] E := ContinuousLinearMap.modulus
    (doubleAngleTangentOperator Y
      (norm_quarterAcuteAngularOperator_lt_one U V hquarter))
  have hY : IsAngularOperator U Y :=
    quarterAcuteAngularOperator_isAngularOperator U V hquarter
  have hYP : Y ∘L P = Y := hY.1
  have hPY : P ∘L Y = 0 := hY.2
  -- See the note on the same pair in `ambientAngularOperator_eq_extendCoordinate`:
  -- `star_mul` does not match `P ∘L Y`, so route through `adjoint_comp`.
  have hPadj : ContinuousLinearMap.adjoint P = P := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using
      (isSelfAdjoint_starProjection U).star_eq
  have hYstarP : Y.adjoint ∘L P = 0 := by
    have h := congrArg ContinuousLinearMap.adjoint hPY
    rwa [ContinuousLinearMap.adjoint_comp, hPadj, map_zero] at h
  have hPYstar : P ∘L Y.adjoint = Y.adjoint := by
    have h := congrArg ContinuousLinearMap.adjoint hYP
    rwa [ContinuousLinearMap.adjoint_comp, hPadj] at h
  have hGnonneg : (0 : E →L[ℂ] E) ≤ G := by
    dsimp [G]
    exact (ContinuousLinearMap.nonneg_iff_isPositive (f := _)).2
      (ContinuousLinearMap.isPositive_adjoint_comp_self Y)
  have hGP : G ∘L P = G := by
    dsimp [G]
    rw [ContinuousLinearMap.comp_assoc, hYP]
  have hPG : P ∘L G = G := by
    dsimp [G]
    rw [← ContinuousLinearMap.comp_assoc, hPYstar]
  have hNunit : IsUnit N := by
    refine TauCeti.ContinuousLinearMap.isUnit_of_coercive one_pos ?_
    intro x
    -- Compute the form value first, then conclude numerically.  Doing it with a
    -- `rw` chain does not work: `isUnit_of_coercive` states its hypothesis with
    -- `RCLike.re`, `dsimp` collapses that to `Complex.re`, and after the collapse
    -- neither `map_add` (which wants a bundled additive map) nor
    -- `inner_self_eq_norm_sq` (which is stated for `RCLike.re`) can match.
    have hval : RCLike.re ⟪N x, x⟫_ℂ = ‖x‖ ^ 2 + ‖Y x‖ ^ 2 := by
      have hN : N x = x + Y.adjoint (Y x) := by
        show (ContinuousLinearMap.id ℂ E + Y.adjoint ∘L Y) x
            = x + Y.adjoint (Y x)
        rw [add_apply, ContinuousLinearMap.id_apply,
          ContinuousLinearMap.comp_apply]
      rw [hN]
      -- `← ofReal_pow` pulls `(↑‖x‖) ^ 2` back to `↑(‖x‖ ^ 2)` so that
      -- `Complex.ofReal_re` can strip the coercion.
      simp [inner_add_left, ContinuousLinearMap.adjoint_inner_left,
        ← Complex.ofReal_pow]
    rw [hval]
    nlinarith [sq_nonneg ‖Y x‖, norm_nonneg x]
  have hNR : N ∘L R = ContinuousLinearMap.id ℂ E :=
    Ring.mul_inverse_cancel N hNunit
  have hRN : R ∘L N = ContinuousLinearMap.id ℂ E :=
    Ring.inverse_mul_cancel N hNunit
  have hPR : P ∘L R = R ∘L P := by
    have hPN : P ∘L N = N ∘L P := by
      dsimp [N]
      rw [ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp,
        ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp, hPG, hGP]
    calc
      P ∘L R = (R ∘L N) ∘L (P ∘L R) := by rw [hRN, ContinuousLinearMap.id_comp]
      _ = R ∘L ((N ∘L P) ∘L R) := by simp only [ContinuousLinearMap.comp_assoc]
      _ = R ∘L ((P ∘L N) ∘L R) := by rw [hPN]
      _ = (R ∘L P) ∘L (N ∘L R) := by simp only [ContinuousLinearMap.comp_assoc]
      _ = R ∘L P := by rw [hNR, ContinuousLinearMap.comp_id]
  have hGR : G ∘L R = R ∘L G := by
    have hGN : G ∘L N = N ∘L G := by
      dsimp [N]
      rw [ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp,
        ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp]
    calc
      G ∘L R = (R ∘L N) ∘L (G ∘L R) := by rw [hRN, ContinuousLinearMap.id_comp]
      _ = R ∘L ((N ∘L G) ∘L R) := by simp only [ContinuousLinearMap.comp_assoc]
      _ = R ∘L ((G ∘L N) ∘L R) := by rw [hGN]
      _ = (R ∘L G) ∘L (N ∘L R) := by simp only [ContinuousLinearMap.comp_assoc]
      _ = R ∘L G := by rw [hNR, ContinuousLinearMap.comp_id]
  have hQformula : Q = (P + Y) ∘L R ∘L (P + Y.adjoint) := by
    -- Transporting `projection (graphSubspace U Y)` to `projection V` needs care:
    -- `rw` fails with "motive is not type correct" because `projection` carries a
    -- `HasOrthogonalProjection` instance *for the submodule being rewritten*, and
    -- `simp only [lemma]` fails to match because `Y` is a `let`-bound fvar while
    -- the lemma's LHS mentions `quarterAcuteAngularOperator` explicitly.  Naming
    -- the equation as a local hypothesis fixes both: simp rewrites with an fvar
    -- equation directly, and `HasOrthogonalProjection` is a `Prop` class, so the
    -- instance argument is proof-irrelevant and congruence goes through.
    have hV : graphSubspace U Y = V :=
      graphSubspace_quarterAcuteAngularOperator U V hquarter
    have hgraph : V.starProjection = graphProjectionFormula U Y := by
      simpa only [hV] using projection_graphSubspace_formula U Y hY
    -- `graphProjectionFormula` produces every factor decorated with `P`:
    --   (P + Y P) · (1 + P Y⋆ (Y P))⁻¹ · (P + P Y⋆)
    -- and the decorations collapse by `Y P = Y` and `P Y⋆ = Y⋆`, which are
    -- exactly the two angular-operator identities.  `1` and `id` are the same
    -- element of the endomorphism algebra, so the tail is `rfl`.
    have hcollapse :
        graphProjectionFormula U Y = (P + Y) ∘L R ∘L (P + Y.adjoint) := by
      -- A literal `show` cannot state the expansion: it mixes two spellings of
      -- the same operator (`DavisKahan.projection U` in some factors,
      -- `U.starProjection` in others), so no single hand-written pattern matches.
      -- Let `simp only` do the unfolding and the two collapses together.
      show (P + Y * P) *
            (Ring.inverse (1 + star (Y * P) * (Y * P)) * star (P + Y * P))
          = (P + Y) ∘L R ∘L (P + Y.adjoint)
      rw [show Y * P = Y from hYP, star_add,
        ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
        hPadj]
      -- `R`, `N`, `G` are `let`-bound, and `1`/`id` and `*`/`∘SL` differ only up
      -- to unfolding, so finish by definitional equality.
      show (P + Y) * (Ring.inverse (1 + Y.adjoint * Y) * (P + Y.adjoint))
          = (P + Y) * (Ring.inverse (1 + Y.adjoint * Y) * (P + Y.adjoint))
      rfl
    exact hgraph.trans hcollapse
  -- Done as a ring computation rather than by `simp` normalisation.  No
  -- associativity convention works here: right-association hides `P ∘ P` from
  -- `hPP`, left-association hides `Y⋆ ∘ P` from `hYstarP`.  Collapsing the two
  -- outer factors *first* avoids the choice entirely.
  have hPP : P ∘L P = P := U.isIdempotentElem_starProjection
  have hPQP : P ∘L Q ∘L P = R ∘L P := by
    have hleft : P ∘L (P + Y) = P := by
      rw [ContinuousLinearMap.comp_add, hPP, hPY, add_zero]
    have hright : (P + Y.adjoint) ∘L P = P := by
      rw [ContinuousLinearMap.add_comp, hPP, hYstarP, add_zero]
    show P * (Q * P) = R * P
    rw [hQformula]
    calc P * (((P + Y) * (R * (P + Y.adjoint))) * P)
        = (P * (P + Y)) * (R * ((P + Y.adjoint) * P)) := by noncomm_ring
      _ = P * (R * P) := by
            rw [show P * (P + Y) = P from hleft,
              show (P + Y.adjoint) * P = P from hright]
      _ = (P * R) * P := by rw [mul_assoc]
      _ = (R * P) * P := by rw [show P * R = R * P from hPR]
      _ = R * (P * P) := by rw [mul_assoc]
      _ = R * P := by rw [show P * P = P from hPP]
  have hPQperpP : P ∘L Vᗮ.starProjection ∘L P = G ∘L R ∘L P := by
    -- `starProjection_orthogonal'` yields `1 - Q` (not `id - Q`), so stay in
    -- ring notation and let `noncomm_ring` distribute; that sidesteps both the
    -- `1` vs `id` mismatch and the bracketing of `P ∘ ((1 - Q) ∘ P)`.
    rw [Submodule.starProjection_orthogonal' V]
    have hexpand : P * ((1 - Q) * P) = P * P - P * (Q * P) := by noncomm_ring
    show P * ((1 - Q) * P) = G * (R * P)
    rw [hexpand, show P * P = P from hPP, show P * (Q * P) = R * P from hPQP]
    have hidentity : P - R ∘L P = G ∘L R ∘L P := by
      have hNRP := congrArg (fun T : E →L[ℂ] E => T ∘L P) hNR
      dsimp [N] at hNRP
      simp only [ContinuousLinearMap.add_comp,
        ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_assoc] at hNRP
      -- `hNRP : R P + G R P = P`.  The `rw [hGR]` that used to sit here was
      -- superfluous and could not fire; the goal is pure additive rearrangement.
      calc P - R ∘L P = (R ∘L P + G ∘L R ∘L P) - R ∘L P := by rw [hNRP]
        _ = G ∘L R ∘L P := by abel
    exact hidentity
  let Cang : E →L[ℂ] E := directedCosAngleOperatorC U V
  let Sang : E →L[ℂ] E := directedSinAngleOperatorC U V
  -- `modulus_mul_self` is stated with `*`; these goals carry `∘SL`, which is
  -- defeq but not syntactically equal, so `← mul_def` has to bridge it first.
  -- Then `|Q P|² = (QP)⋆(QP) = P Q Q P = P Q P` by self-adjointness and
  -- idempotence of the two star-projections, which is exactly `hPQP`.
  have hQQ : V.starProjection ∘L V.starProjection = V.starProjection :=
    V.isIdempotentElem_starProjection
  have hQperpQperp :
      Vᗮ.starProjection ∘L Vᗮ.starProjection = Vᗮ.starProjection :=
    Vᗮ.isIdempotentElem_starProjection
  have hCangSq : Cang ∘L Cang = R ∘L P := by
    dsimp [Cang, directedCosAngleOperatorC]
    rw [← ContinuousLinearMap.mul_def, ContinuousLinearMap.modulus_mul_self,
      ContinuousLinearMap.adjoint_comp,
      (isSelfAdjoint_starProjection U).adjoint_eq,
      (isSelfAdjoint_starProjection V).adjoint_eq,
      ContinuousLinearMap.comp_assoc,
      ← ContinuousLinearMap.comp_assoc V.starProjection V.starProjection
        U.starProjection, hQQ]
    exact hPQP
  have hSangSq : Sang ∘L Sang = G ∘L R ∘L P := by
    dsimp [Sang, directedSinAngleOperatorC]
    rw [← ContinuousLinearMap.mul_def, ContinuousLinearMap.modulus_mul_self,
      ContinuousLinearMap.adjoint_comp,
      (isSelfAdjoint_starProjection U).adjoint_eq,
      (isSelfAdjoint_starProjection Vᗮ).adjoint_eq,
      ContinuousLinearMap.comp_assoc,
      ← ContinuousLinearMap.comp_assoc Vᗮ.starProjection Vᗮ.starProjection
        U.starProjection, hQperpQperp]
    exact hPQperpP
  have hSCcomm : Commute Sang Cang :=
    commute_directedSinAngleOperatorC_directedCosAngleOperatorC U V
  have hSinTwo : directedSinTwoAngleOperatorC U V = (2 : ℂ) • (Sang ∘L Cang) := rfl
  have hCosTwo : cosTwoAngleOperatorC U V = D ∘L R ∘L P := by
    -- `dsimp` unfolds the `let`s, after which `hCangSq`/`hSangSq` (stated in terms
    -- of `Cang`/`Sang`) no longer match.  Keep the abbreviations and restate the
    -- squares with `*` instead.
    show Cang * Cang - Sang * Sang = D ∘L R ∘L P
    rw [show Cang * Cang = R ∘L P from hCangSq,
      show Sang * Sang = G ∘L R ∘L P from hSangSq]
    -- state the identity with `1`, not `ContinuousLinearMap.id`: they are the same
    -- element, but `noncomm_ring` only knows `one_mul` for the former.
    show R * P - G * (R * P) = ((1 : E →L[ℂ] E) - G) * (R * P)
    noncomm_ring
  have hDunit : IsUnit D :=
    isUnit_doubleAngleDenominator Y
      (norm_quarterAcuteAngularOperator_lt_one U V hquarter)
  have hDcommG : D ∘L G = G ∘L D := by
    dsimp [D]
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
      ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
  -- `Commute.units_inv_left` is stated for a `Units` coercion, not for
  -- `Ring.inverse`; `Ring.inverse_of_isUnit` converts between them.
  have hDinvcommG : Ring.inverse D ∘L G = G ∘L Ring.inverse D := by
    have hu : Commute ((hDunit.unit : E →L[ℂ] E)) G := by
      rw [hDunit.unit_spec]; exact hDcommG
    rw [Ring.inverse_of_isUnit hDunit]
    exact hu.units_inv_left
  have hTformula :
      doubleAngleTangentOperator Y
          (norm_quarterAcuteAngularOperator_lt_one U V hquarter) =
        (2 : ℂ) • (Y ∘L Ring.inverse D) := rfl
  -- Hoisted above `hMsq`.  `hMsq` needs the self-adjointness of `D⁻¹` and the
  -- commutation `[|Y|, D⁻¹] = 0`; both were originally proved *below*, inside
  -- `hCandidateNonneg`, i.e. after their first use.
  have hmodYnonneg : (0 : E →L[ℂ] E) ≤ ContinuousLinearMap.modulus Y :=
    ContinuousLinearMap.modulus_nonneg Y
  have hDnonneg : (0 : E →L[ℂ] E) ≤ D := by
    rw [ContinuousLinearMap.nonneg_iff_isPositive]
    refine ⟨ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp ?_, ?_⟩
    · -- Stay in the `ContinuousLinearMap` star instance throughout: the route via
      -- `IsSelfAdjoint.algebraMap` states the fact at a *different* `Star`
      -- instance on the same type, which is why it failed to typecheck.
      show IsSelfAdjoint (ContinuousLinearMap.id ℂ E - G)
      have hidsa : IsSelfAdjoint (ContinuousLinearMap.id ℂ E) := by
        show star (ContinuousLinearMap.id ℂ E) = ContinuousLinearMap.id ℂ E
        rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_id]
      exact hidsa.sub
        (ContinuousLinearMap.isPositive_adjoint_comp_self Y).isSelfAdjoint
    · intro x
      rw [ContinuousLinearMap.reApplyInnerSelf_apply]
      -- Same trap as in `hNunit`: compute the form value as its own `have` with
      -- `simp`, because once a `dsimp` collapses `RCLike.re` to `Complex.re`
      -- neither `map_sub` nor `inner_self_eq_norm_sq` can match.
      have hval : RCLike.re ⟪D x, x⟫_ℂ = ‖x‖ ^ 2 - ‖Y x‖ ^ 2 := by
        have hD : D x = x - Y.adjoint (Y x) := by
          show (ContinuousLinearMap.id ℂ E - G) x = x - Y.adjoint (Y x)
          rw [sub_apply, ContinuousLinearMap.id_apply,
            ContinuousLinearMap.comp_apply]
        rw [hD]
        simp [inner_sub_left, ContinuousLinearMap.adjoint_inner_left,
          ← Complex.ofReal_pow]
      rw [hval]
      have hle : ‖Y x‖ ≤ ‖x‖ :=
        calc ‖Y x‖ ≤ ‖Y‖ * ‖x‖ := Y.le_opNorm x
          _ ≤ 1 * ‖x‖ :=
              mul_le_mul_of_nonneg_right
                (norm_quarterAcuteAngularOperator_lt_one U V hquarter).le
                (norm_nonneg x)
          _ = ‖x‖ := one_mul _
      nlinarith [hle, norm_nonneg (Y x), norm_nonneg x]
  have hDsp : IsStrictlyPositive D := ⟨hDnonneg, hDunit⟩
  have hDinvNonneg : (0 : E →L[ℂ] E) ≤ Ring.inverse D := by
    rw [CFC.inverse_eq_rpow_neg_one hDsp]
    exact CFC.rpow_nonneg
  have hDinvSA : IsSelfAdjoint (Ring.inverse D) := hDinvNonneg.isSelfAdjoint
  have hcomm : Commute (ContinuousLinearMap.modulus Y) (Ring.inverse D) := by
    have hmodG : Commute (ContinuousLinearMap.modulus Y) G := by
      show Commute (ContinuousLinearMap.modulus Y) (Y.adjoint ∘L Y)
      rw [← ContinuousLinearMap.modulus_mul_self Y]
      exact (Commute.refl _).mul_right (Commute.refl _)
    have hmodD : Commute (ContinuousLinearMap.modulus Y) D := by
      show Commute (ContinuousLinearMap.modulus Y)
        (ContinuousLinearMap.id ℂ E - G)
      exact (Commute.one_right _).sub_right hmodG
    have hu : Commute (ContinuousLinearMap.modulus Y)
        ((hDunit.unit : E →L[ℂ] E)) := by
      rw [hDunit.unit_spec]; exact hmodD
    rw [Ring.inverse_of_isUnit hDunit]
    exact hu.units_inv_right
  have hMsq : M ∘L M =
      (4 : ℂ) • (ContinuousLinearMap.modulus Y ∘L
        Ring.inverse D ∘L ContinuousLinearMap.modulus Y ∘L Ring.inverse D) := by
    -- `|T|² = T⋆ T` with `T = 2 • (Y D⁻¹)`, hence
    --   T⋆ T = 4 • (D⁻¹ Y⋆ Y D⁻¹) = 4 • (D⁻¹ |Y| |Y| D⁻¹) = 4 • (|Y| D⁻¹ |Y| D⁻¹),
    -- the last step by `[|Y|, D⁻¹] = 0`.  The old script called `star_smul` and
    -- `star_mul` *after* `modulus_mul_self` had already put the goal in `adjoint`
    -- form, so neither could ever fire.
    have hDinvAdj :
        ContinuousLinearMap.adjoint (Ring.inverse D) = Ring.inverse D := by
      simpa only [ContinuousLinearMap.star_eq_adjoint] using hDinvSA.star_eq
    have hYsq : ContinuousLinearMap.adjoint Y * Y
        = ContinuousLinearMap.modulus Y * ContinuousLinearMap.modulus Y :=
      (ContinuousLinearMap.modulus_mul_self Y).symm
    dsimp [M]
    rw [← ContinuousLinearMap.mul_def, ContinuousLinearMap.modulus_mul_self,
      hTformula]
    -- `adjoint` is a *conjugate*-linear isometry equiv (`≃ₗᵢ⋆`), so the scalar
    -- comes out through `map_smulₛₗ` as `star 2`, not as `2`.
    rw [map_smulₛₗ, ContinuousLinearMap.adjoint_comp, hDinvAdj]
    show (starRingEnd ℂ) 2 • (Ring.inverse D * ContinuousLinearMap.adjoint Y) *
          ((2 : ℂ) • (Y * Ring.inverse D))
        = (4 : ℂ) • (ContinuousLinearMap.modulus Y *
            (Ring.inverse D * (ContinuousLinearMap.modulus Y * Ring.inverse D)))
    rw [map_ofNat, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [show (2 : ℂ) * 2 = 4 by norm_num]
    congr 1
    calc Ring.inverse D * ContinuousLinearMap.adjoint Y * (Y * Ring.inverse D)
        = Ring.inverse D * (ContinuousLinearMap.adjoint Y * Y) * Ring.inverse D := by
          noncomm_ring
      _ = Ring.inverse D * (ContinuousLinearMap.modulus Y *
            ContinuousLinearMap.modulus Y) * Ring.inverse D := by rw [hYsq]
      _ = (Ring.inverse D * ContinuousLinearMap.modulus Y) *
            (ContinuousLinearMap.modulus Y * Ring.inverse D) := by noncomm_ring
      _ = (ContinuousLinearMap.modulus Y * Ring.inverse D) *
            (ContinuousLinearMap.modulus Y * Ring.inverse D) := by
          rw [hcomm.symm.eq]
      _ = ContinuousLinearMap.modulus Y *
            (Ring.inverse D * (ContinuousLinearMap.modulus Y * Ring.inverse D)) := by
          noncomm_ring
  have hCandidateNonneg :
      (0 : E →L[ℂ] E) ≤
        (2 : ℂ) • (ContinuousLinearMap.modulus Y ∘L Ring.inverse D) := by
    have hprod : (0 : E →L[ℂ] E) ≤
        ContinuousLinearMap.modulus Y ∘L Ring.inverse D :=
      hcomm.mul_nonneg hmodYnonneg hDinvNonneg
    -- The scalar is ℂ, so `smul_nonneg` -- which supplies the ℝ-action -- is the
    -- wrong lemma.  The two statements print *identically* and differ only in the
    -- `SMul` instance, which is why the mismatch looked like a no-op.
    rw [ContinuousLinearMap.nonneg_iff_isPositive]
    -- `0 ≤ (2 : ℂ)` is an order on ℂ (`re` compared, `im` equal), so it needs
    -- `Complex.le_def`; `norm_num` alone does not unfold it.
    exact ((ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mp hprod).smul_of_nonneg
      (by simp [Complex.le_def])
  have hMformula :
      M = (2 : ℂ) • (ContinuousLinearMap.modulus Y ∘L Ring.inverse D) := by
    -- the lemma concludes `b = |T|`, the goal is `|T| = b`, hence `.symm`
    refine (ContinuousLinearMap.eq_modulus_of_nonneg_of_mul_self_eq
      hCandidateNonneg ?_).symm
    rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.modulus_mul_self]
    -- `hMsq` is stated with `∘SL`; restate it with `*` so it matches here.
    rw [show M * M = (4 : ℂ) • (ContinuousLinearMap.modulus Y ∘L
          Ring.inverse D ∘L ContinuousLinearMap.modulus Y ∘L Ring.inverse D)
        from hMsq]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul,
      show (2 : ℂ) * 2 = 4 by norm_num]
    -- `congr 1` discharges the remaining associativity itself; no `noncomm_ring`
    -- is needed (adding one reports "no goals to be solved").
    congr 1
  have hSCformula : Sang ∘L Cang =
      ContinuousLinearMap.modulus Y ∘L R ∘L P := by
    -- `Commute G (R P)` from `G R = R G` and `G P = G = P G`; then
    -- `Commute |Y| (R P)` because `|Y| = CFC.sqrt G` and `Commute.cfcₙ_nnreal`
    -- transports commutation through the functional calculus.
    have hGRP : Commute G (R ∘L P) := by
      show G * (R * P) = (R * P) * G
      calc G * (R * P) = (G * R) * P := (mul_assoc _ _ _).symm
        _ = (R * G) * P := by rw [show G * R = R * G from hGR]
        _ = R * (G * P) := mul_assoc _ _ _
        _ = R * G := by rw [show G * P = G from hGP]
        _ = R * (P * G) := by rw [show P * G = G from hPG]
        _ = (R * P) * G := (mul_assoc _ _ _).symm
    have hmodRP : Commute (ContinuousLinearMap.modulus Y) (R ∘L P) :=
      Commute.cfcₙ_nnreal hGRP _
    have hRPnonneg : (0 : E →L[ℂ] E) ≤ R ∘L P := by
      rw [show R ∘L P = Cang ∘L Cang from hCangSq.symm]
      exact (Commute.refl Cang).mul_nonneg (directedCosAngleOperatorC_nonneg U V)
        (directedCosAngleOperatorC_nonneg U V)
    have hleftNonneg : (0 : E →L[ℂ] E) ≤ Sang ∘L Cang :=
      hSCcomm.mul_nonneg (directedSinAngleOperatorC_nonneg U V)
        (directedCosAngleOperatorC_nonneg U V)
    have hrightNonneg : (0 : E →L[ℂ] E) ≤
        ContinuousLinearMap.modulus Y ∘L R ∘L P :=
      hmodRP.mul_nonneg hmodYnonneg hRPnonneg
    -- Both sides are nonnegative with the same square, so they agree.
    -- Stay in `*` notation throughout: the goal carries `∘L`, which is defeq but
    -- not syntactically equal, so mixing the two makes every `rw` miss.
    have hsq : (Sang * Cang) * (Sang * Cang)
        = (ContinuousLinearMap.modulus Y * (R * P)) *
          (ContinuousLinearMap.modulus Y * (R * P)) := by
      have hL : (Sang * Cang) * (Sang * Cang)
          = (Sang * Sang) * (Cang * Cang) := by
        rw [mul_assoc, ← mul_assoc Cang Sang Cang,
          show Cang * Sang = Sang * Cang from hSCcomm.eq.symm, mul_assoc,
          ← mul_assoc]
      have hR : (ContinuousLinearMap.modulus Y * (R * P)) *
            (ContinuousLinearMap.modulus Y * (R * P))
          = (ContinuousLinearMap.modulus Y * ContinuousLinearMap.modulus Y) *
            ((R * P) * (R * P)) := by
        rw [mul_assoc, ← mul_assoc (R * P) (ContinuousLinearMap.modulus Y),
          show (R * P) * ContinuousLinearMap.modulus Y
            = ContinuousLinearMap.modulus Y * (R * P) from hmodRP.eq.symm,
          mul_assoc, ← mul_assoc]
      rw [hL, hR, show Sang * Sang = G * (R * P) from hSangSq,
        show Cang * Cang = R * P from hCangSq,
        show ContinuousLinearMap.modulus Y * ContinuousLinearMap.modulus Y = G
          from ContinuousLinearMap.modulus_mul_self Y]
      noncomm_ring
    have h1 : CFC.sqrt ((Sang * Cang) * (Sang * Cang)) = Sang * Cang :=
      CFC.sqrt_unique rfl hleftNonneg
    have h2 : CFC.sqrt ((ContinuousLinearMap.modulus Y * (R * P)) *
          (ContinuousLinearMap.modulus Y * (R * P)))
        = ContinuousLinearMap.modulus Y * (R * P) :=
      CFC.sqrt_unique rfl hrightNonneg
    show Sang * Cang = ContinuousLinearMap.modulus Y * (R * P)
    rw [← h1, ← h2, hsq]
  have hCandidateComp :
      M ∘L cosTwoAngleExtendedC U V = directedSinTwoAngleOperatorC U V := by
    rw [hMformula, cosTwoAngleExtendedC, hCosTwo, hSinTwo, hSCformula]
    have hMperp : ContinuousLinearMap.modulus Y ∘L Uᗮ.starProjection = 0 := by
      apply ContinuousLinearMap.ext
      intro x
      -- `zero_apply` is needed: after `comp_apply` the right-hand side is still
      -- `(0 : E →L[ℂ] E) x`, so `modulus_apply_eq_zero_iff` has nothing to match.
      rw [ContinuousLinearMap.comp_apply, zero_apply,
        ContinuousLinearMap.modulus_apply_eq_zero_iff]
      have hzero : Y (Uᗮ.starProjection x) = 0 := by
        have h := DFunLike.congr_fun hYP (Uᗮ.starProjection x)
        rw [ContinuousLinearMap.comp_apply,
          (Submodule.starProjection_apply_eq_zero_iff (K := U)).mpr
            (Uᗮ.starProjection_apply_mem x)] at h
        simpa using h.symm
      exact hzero
    -- `D` is the identity on `Uᗮ` (because `G` kills it), hence so is `D⁻¹`; that
    -- is what makes the `Uᗮ` block of the product vanish.  `hMperp` alone cannot
    -- fire: the second summand is `(2 • |Y| D⁻¹) ∘ P⊥`, in which `|Y| ∘ P⊥` is not
    -- a subterm.
    have hPsumOp : P + Uᗮ.starProjection = ContinuousLinearMap.id ℂ E := by
      ext z
      rw [add_apply, ContinuousLinearMap.id_apply]
      exact U.starProjection_add_starProjection_orthogonal z
    have hGPerp : G ∘L Uᗮ.starProjection = 0 := by
      have h : G ∘L P + G ∘L Uᗮ.starProjection = G := by
        rw [← ContinuousLinearMap.comp_add, hPsumOp,
          ContinuousLinearMap.comp_id]
      rw [hGP] at h
      -- `h : G P⊥ + G = G`, so `(G P⊥ + G) - G = 0`, i.e. `G P⊥ = 0`.
      simpa using sub_eq_zero_of_eq h
    have hDPerp : D ∘L Uᗮ.starProjection = Uᗮ.starProjection := by
      show (ContinuousLinearMap.id ℂ E - G) ∘L Uᗮ.starProjection = _
      rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.id_comp, hGPerp,
        sub_zero]
    have hDinvPerp : Ring.inverse D ∘L Uᗮ.starProjection
        = Uᗮ.starProjection := by
      -- keep `∘L` in the first step: `hDPerp` is stated with `∘L`, and `*` would
      -- not match it syntactically.
      calc Ring.inverse D ∘L Uᗮ.starProjection
          = Ring.inverse D ∘L (D ∘L Uᗮ.starProjection) := by rw [hDPerp]
        _ = (Ring.inverse D * D) * Uᗮ.starProjection := by noncomm_ring
        _ = Uᗮ.starProjection := by
            rw [Ring.inverse_mul_cancel D hDunit, one_mul]
    rw [ContinuousLinearMap.comp_add]
    rw [show ((2 : ℂ) • (ContinuousLinearMap.modulus Y ∘L Ring.inverse D)) ∘L
          Uᗮ.starProjection = 0 by
      rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_assoc,
        hDinvPerp, hMperp, smul_zero], add_zero]
    show ((2 : ℂ) • (ContinuousLinearMap.modulus Y * Ring.inverse D)) *
        (D * (R * P))
      = (2 : ℂ) • (ContinuousLinearMap.modulus Y * (R * P))
    rw [smul_mul_assoc]
    congr 1
    calc (ContinuousLinearMap.modulus Y * Ring.inverse D) * (D * (R * P))
        = ContinuousLinearMap.modulus Y * ((Ring.inverse D * D) * (R * P)) := by
          noncomm_ring
      _ = ContinuousLinearMap.modulus Y * (R * P) := by
          rw [Ring.inverse_mul_cancel D hDunit, one_mul]
  have hcanonical := directedTanTwoAngleOperatorC_comp_cosTwoAngleExtendedC U V hquarter
  have hcosSurj : Function.Surjective (cosTwoAngleExtendedC U V) := by
    -- `range_eq_top` is stated for `LinearMap`; the goal's coercion is the
    -- `ContinuousLinearMap` one, so rewrite backwards through `.mp` instead.
    exact LinearMap.range_eq_top.mp
      (cosTwoAngleExtendedC_ker_bot_range_top U V hquarter).2
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := hcosSurj x
  have h1 := DFunLike.congr_fun hcanonical y
  have h2 := DFunLike.congr_fun hCandidateComp y
  exact h1.trans h2.symm

/-- The canonical ambient `tan 2Theta` and the rectangular graph-coordinate
operator have the same full approximation-number sequence. -/
theorem canonicalTanTwoAngle_hasSameApproximationNumbers_graphCoordinate
    (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hquarter : IsQuarterAcute U V) :
    (directedTanTwoAngleOperatorC U V hquarter).HasSameApproximationNumbers
      (doubleAngleTangentOperator
        (quarterAcuteAngularCoordinate U V hquarter)
        (norm_quarterAcuteAngularCoordinate_lt_one U V hquarter)) := by
  let Y : E →L[ℂ] E := quarterAcuteAngularOperator U V hquarter
  let X : U →L[ℂ] Uᗮ := quarterAcuteAngularCoordinate U V hquarter
  let hYc : ‖Y‖ < 1 := norm_quarterAcuteAngularOperator_lt_one U V hquarter
  let hXc : ‖X‖ < 1 := norm_quarterAcuteAngularCoordinate_lt_one U V hquarter
  have hcanonical : directedTanTwoAngleOperatorC U V hquarter =
      ContinuousLinearMap.modulus (doubleAngleTangentOperator Y hYc) := by
    simpa only [Y, hYc] using
      directedTanTwoAngleOperatorC_eq_modulus_ambientGraphTangent U V hquarter
  have hambient : doubleAngleTangentOperator Y hYc =
      Uᗮ.subtypeL ∘L doubleAngleTangentOperator X hXc ∘L U.subtypeL.adjoint := by
    simpa only [Y, X, hYc, hXc, quarterAcuteAngularCoordinate] using
      ambient_doubleAngleTangent_eq_extendCoordinate U Y
        (quarterAcuteAngularOperator_isAngularOperator U V hquarter) hYc
  rw [hcanonical]
  exact
    (modulus_hasSameApproximationNumbers
      (doubleAngleTangentOperator Y hYc)).trans
      (by
        rw [hambient]
        exact sameApproximationSingularValues_ambientSubspaceBlock U Uᗮ
          (doubleAngleTangentOperator X hXc))

end

end DavisKahan
end TauCeti
