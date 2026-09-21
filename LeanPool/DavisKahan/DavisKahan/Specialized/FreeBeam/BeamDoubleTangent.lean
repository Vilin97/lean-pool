/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamTangent
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.DoubleAngle.SpectralCutoff

/-! # Beam Double Tangent -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Section 9, equation (9.7): the double-angle tangent, on the genuine operator

`BeamTangent` proved equation (9.6) for the free-beam example by feeding the
Rayleigh--Ritz data to the unbounded Theorem 6.3.  Equation (9.7) needs the paper's
extra step:

> For the `tan 2Θ` theorem we also replace `A₁` by `Â₁ = E₁* (A + H) E₁`.  Since
> `Â₁ - A₁ = E₁* H E₁ ≥ 0`, still `Â₁ > 500`.

That is: the comparison operator is no longer the free beam but the *block-diagonal*
part of the perturbed beam relative to the trial splitting,

    Â = E₀ Â₀ E₀* + E₁ Â₁ E₁*,   B = (A + ε t) - Â = R̂ ⊕ R̂*,

and `B` is fully off-diagonal, which is exactly the hypothesis the residual-form
`tan 2Θ` theorem takes.  This module builds `Â` and `B` for the genuine beam and
reads off the printed bound.

## What is proved

* `beamComparison ε` — `Â`, a bounded perturbation of the free beam, self-adjoint,
  block-diagonal for `beamTrial ⊕ beamTrialᗮ`.
* `norm_beamRitzOffDiagonal_le` — `‖B‖ ≤ ε/√15`, the paper's `‖R̂‖`.  An off-diagonal
  operator's norm is the larger of its two blocks; the lower block *is* the
  Rayleigh--Ritz residual and the upper block is its adjoint.
* `beamComparison_form_le_of_mem_beamTrial` and
  `beamComparison_form_ge_of_mem_orthogonal` — `Â₀ ≤ α̂₂` and `Â₁ ≥ 500.5`, the paper's
  `Â₀ < 0.7887 ε` and `Â₁ > 500`.
* `beamTanTwoTheta_le` and `beamTanTwoTheta_lt_printed` — equation (9.7).

## Scope

This is the **bound-norm** half of (9.7).  The paper's following sentence, "with the
same right side bounding `tan 2θ₁ + tan 2θ₂` in the 2-norm", is
`beamTanTwoThetaSum_le` in
`DavisKahan/Sources/DavisKahan1970/Section9/BeamDoubleTangentKyFan.lean`: it needs
the Ky Fan prefix form of the unbounded residual `tan 2Θ` theorem, which is a
source facade this generic-foundation module may not import.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. 7 (1970), 1--46, Section 9, equation (9.7).
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Model


open DavisKahan1970.Section9

noncomputable section

/-- The block-diagonal part of the perturbation relative to the trial splitting. -/
def beamRitzDiagonal (ε : ℝ) : BeamL2 →L[ℂ] BeamL2 :=
  beamTrial.diagonalPart (beamPerturbation ε)

/-- The block-off-diagonal part: the paper's `R̂` together with its adjoint. -/
def beamRitzOffDiagonal (ε : ℝ) : BeamL2 →L[ℂ] BeamL2 :=
  beamTrial.offDiagonalPart (beamPerturbation ε)

/-- The block-diagonal part of a symmetric operator is symmetric. -/
theorem beamRitzDiagonal_isSelfAdjoint (ε : ℝ) :
    (beamRitzDiagonal ε).IsSymmetric := by
  intro x y
  have hd : ∀ z : BeamL2, beamRitzDiagonal ε z
      = beamTrial.starProjection (beamPerturbation ε (beamTrial.starProjection z))
        + beamTrialᗮ.starProjection (beamPerturbation ε (beamTrialᗮ.starProjection z)) :=
    fun z => rfl
  have hsym : ∀ u v : BeamL2,
      ⟪beamPerturbation ε u, v⟫_ℂ = ⟪u, beamPerturbation ε v⟫_ℂ :=
    fun u v => beamPerturbation_isSelfAdjoint ε u v
  show ⟪beamRitzDiagonal ε x, y⟫_ℂ = ⟪x, beamRitzDiagonal ε y⟫_ℂ
  rw [hd, hd, inner_add_left, inner_add_right]
  congr 1
  · rw [Submodule.inner_starProjection_left_eq_right, hsym,
      Submodule.inner_starProjection_left_eq_right]
  · rw [Submodule.inner_starProjection_left_eq_right, hsym,
      Submodule.inner_starProjection_left_eq_right]

/-- The block-off-diagonal part of a symmetric operator is symmetric. -/
theorem beamRitzOffDiagonal_isSelfAdjoint (ε : ℝ) :
    (beamRitzOffDiagonal ε).IsSymmetric := by
  intro x y
  have hsym : ∀ u v : BeamL2,
      ⟪beamPerturbation ε u, v⟫_ℂ = ⟪u, beamPerturbation ε v⟫_ℂ :=
    fun u v => beamPerturbation_isSelfAdjoint ε u v
  have hdsym : ∀ u v : BeamL2,
      ⟪beamRitzDiagonal ε u, v⟫_ℂ = ⟪u, beamRitzDiagonal ε v⟫_ℂ :=
    fun u v => beamRitzDiagonal_isSelfAdjoint ε u v
  have hoff : ∀ z : BeamL2, beamRitzOffDiagonal ε z
      = beamPerturbation ε z - beamRitzDiagonal ε z := fun z => rfl
  show ⟪beamRitzOffDiagonal ε x, y⟫_ℂ = ⟪x, beamRitzOffDiagonal ε y⟫_ℂ
  rw [hoff, hoff, inner_sub_left, inner_sub_right, hsym, hdsym]

/-- **The lower off-diagonal block is the Rayleigh--Ritz residual.**  On the trial
subspace the part of `ε t x` orthogonal to it is the residual `R̂`. -/
theorem norm_beamRitzOffDiagonal_lower_le (ε : ℝ) {x : BeamL2} (hx : x ∈ beamTrial) :
    ‖beamTrialᗮ.starProjection (beamPerturbation ε x)‖
      ≤ orthogonalResidualSingularValue ε * ‖x‖ := by
  have h := norm_beamRitzResidual_le ε ⟨x, hx⟩
  have hres : beamResidual ε ⟨x, hx⟩ = beamPerturbation ε x := rfl
  rw [hres] at h
  rw [Submodule.starProjection_orthogonal_apply]
  exact h

/-- **The upper off-diagonal block has the same norm**, by adjointness: it is
`R̂*`. -/
theorem norm_beamRitzOffDiagonal_upper_le (ε : ℝ) {y : BeamL2} (hy : y ∈ beamTrialᗮ) :
    ‖beamTrial.starProjection (beamPerturbation ε y)‖
      ≤ orthogonalResidualSingularValue ε * ‖y‖ := by
  have hσ0 : (0 : ℝ) ≤ orthogonalResidualSingularValue ε := by
    unfold orthogonalResidualSingularValue; positivity
  have hsym : ∀ u v : BeamL2,
      ⟪beamPerturbation ε u, v⟫_ℂ = ⟪u, beamPerturbation ε v⟫_ℂ :=
    fun u v => beamPerturbation_isSelfAdjoint ε u v
  set u : BeamL2 := beamTrial.starProjection (beamPerturbation ε y) with hu
  have humem : u ∈ beamTrial := beamTrial.starProjection_apply_mem _
  have key : ⟪u, u⟫_ℂ = ⟪y, beamTrialᗮ.starProjection (beamPerturbation ε u)⟫_ℂ := by
    calc ⟪u, u⟫_ℂ = ⟪beamPerturbation ε y, u⟫_ℂ := by
          rw [hu, Submodule.inner_starProjection_left_eq_right,
            Submodule.starProjection_eq_self_iff.2 humem]
      _ = ⟪y, beamPerturbation ε u⟫_ℂ := hsym _ _
      _ = ⟪beamTrialᗮ.starProjection y, beamPerturbation ε u⟫_ℂ := by
          rw [Submodule.starProjection_eq_self_iff.2 hy]
      _ = ⟪y, beamTrialᗮ.starProjection (beamPerturbation ε u)⟫_ℂ := by
          rw [Submodule.inner_starProjection_left_eq_right]
  have hsq : ‖u‖ ^ 2 ≤ ‖y‖ * (orthogonalResidualSingularValue ε * ‖u‖) := by
    have hre : ‖u‖ ^ 2 = RCLike.re (⟪y, beamTrialᗮ.starProjection
        (beamPerturbation ε u)⟫_ℂ) := by
      rw [← key]
      exact (inner_self_eq_norm_sq (𝕜 := ℂ) u).symm
    rw [hre]
    refine le_trans (re_inner_le_norm (𝕜 := ℂ) y _) ?_
    exact mul_le_mul_of_nonneg_left
      (norm_beamRitzOffDiagonal_lower_le ε humem) (norm_nonneg y)
  rcases eq_or_lt_of_le (norm_nonneg u) with h0 | hpos
  · rw [← h0]
    exact mul_nonneg hσ0 (norm_nonneg y)
  · refine le_of_mul_le_mul_right ?_ hpos
    nlinarith [hsq]

/-- The off-diagonal part in its two blocks. -/
theorem beamRitzOffDiagonal_apply (ε : ℝ) (v : BeamL2) :
    beamRitzOffDiagonal ε v
      = beamTrialᗮ.starProjection (beamPerturbation ε (beamTrial.starProjection v))
        + beamTrial.starProjection (beamPerturbation ε (beamTrialᗮ.starProjection v)) := by
  have h1 : beamRitzOffDiagonal ε v
      = beamPerturbation ε v
        - (beamTrial.starProjection (beamPerturbation ε (beamTrial.starProjection v))
          + beamTrialᗮ.starProjection
              (beamPerturbation ε (beamTrialᗮ.starProjection v))) := rfl
  have hv : beamTrial.starProjection v + beamTrialᗮ.starProjection v = v := by
    rw [Submodule.starProjection_orthogonal_apply]
    abel
  have hHv : beamPerturbation ε v
      = beamPerturbation ε (beamTrial.starProjection v)
        + beamPerturbation ε (beamTrialᗮ.starProjection v) := by
    rw [← map_add, hv]
  have e1 : beamTrialᗮ.starProjection (beamPerturbation ε (beamTrial.starProjection v))
      = beamPerturbation ε (beamTrial.starProjection v)
        - beamTrial.starProjection (beamPerturbation ε (beamTrial.starProjection v)) :=
    Submodule.starProjection_orthogonal_apply _ _
  have e2 : beamTrial.starProjection (beamPerturbation ε (beamTrialᗮ.starProjection v))
      = beamPerturbation ε (beamTrialᗮ.starProjection v)
        - beamTrialᗮ.starProjection
            (beamPerturbation ε (beamTrialᗮ.starProjection v)) := by
    rw [Submodule.starProjection_orthogonal_apply beamTrial
      (beamPerturbation ε (beamTrialᗮ.starProjection v))]
    abel
  rw [h1, hHv, e1, e2]
  abel

private theorem beam_le_of_sq_le_sq {A B : ℝ} (_hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : A ^ 2 ≤ B ^ 2) : A ≤ B := by nlinarith

/-- **The off-diagonal perturbation has the residual's norm.**  This is the paper's
`‖R̂‖ = ε/√15`: an off-diagonal operator's norm is the larger of its two blocks, and
both blocks are the Rayleigh--Ritz residual and its adjoint. -/
theorem norm_beamRitzOffDiagonal_le (ε : ℝ) :
    ‖beamRitzOffDiagonal ε‖ ≤ orthogonalResidualSingularValue ε := by
  have hσ0 : (0 : ℝ) ≤ orthogonalResidualSingularValue ε := by
    unfold orthogonalResidualSingularValue; positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hσ0 fun v => ?_
  set a := beamTrialᗮ.starProjection (beamPerturbation ε (beamTrial.starProjection v))
    with ha
  set b := beamTrial.starProjection (beamPerturbation ε (beamTrialᗮ.starProjection v))
    with hb
  have hamem : a ∈ beamTrialᗮ := beamTrialᗮ.starProjection_apply_mem _
  have hbmem : b ∈ beamTrial := beamTrial.starProjection_apply_mem _
  have hba : ⟪b, a⟫_ℂ = 0 := hamem b hbmem
  have hab : ⟪a, b⟫_ℂ = 0 := by
    rw [← inner_conj_symm (𝕜 := ℂ) a b, hba, map_zero]
  have hnormsq : ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    rw [norm_add_sq (𝕜 := ℂ), hab]
    simp
  have hv : beamTrial.starProjection v + beamTrialᗮ.starProjection v = v := by
    rw [Submodule.starProjection_orthogonal_apply]
    abel
  have hcross : ⟪beamTrial.starProjection v, beamTrialᗮ.starProjection v⟫_ℂ = 0 :=
    (beamTrialᗮ.starProjection_apply_mem v) _ (beamTrial.starProjection_apply_mem v)
  have hvsq : ‖v‖ ^ 2 = ‖beamTrial.starProjection v‖ ^ 2
      + ‖beamTrialᗮ.starProjection v‖ ^ 2 := by
    rw [← hv, norm_add_sq (𝕜 := ℂ), hcross]
    simp
  have ha_le : ‖a‖ ≤ orthogonalResidualSingularValue ε * ‖beamTrial.starProjection v‖ :=
    norm_beamRitzOffDiagonal_lower_le ε (beamTrial.starProjection_apply_mem v)
  have hb_le : ‖b‖
      ≤ orthogonalResidualSingularValue ε * ‖beamTrialᗮ.starProjection v‖ :=
    norm_beamRitzOffDiagonal_upper_le ε (beamTrialᗮ.starProjection_apply_mem v)
  rw [beamRitzOffDiagonal_apply, ← ha, ← hb]
  refine beam_le_of_sq_le_sq (norm_nonneg _)
    (mul_nonneg hσ0 (norm_nonneg v)) ?_
  rw [hnormsq, mul_pow, hvsq]
  nlinarith [ha_le, hb_le, norm_nonneg a, norm_nonneg b, hσ0,
    norm_nonneg (beamTrial.starProjection v), norm_nonneg (beamTrialᗮ.starProjection v)]

/-! ## The Rayleigh--Ritz comparison operator -/

/-- **The paper's comparison operator** `Â = Â₀ ⊕ Â₁`, obtained from `A + ε t` by
deleting its off-diagonal blocks relative to the trial splitting. -/
def beamComparison (ε : ℝ) : BeamL2 →ₗ.[ℂ] BeamL2 :=
  TauCeti.LinearPMap.addBounded beamOperator (beamRitzDiagonal ε)

/-- `Â` is self-adjoint: it is the self-adjoint free beam plus a bounded symmetric
operator. -/
theorem beamComparison_isSelfAdjoint (ε : ℝ) : _root_.IsSelfAdjoint (beamComparison ε) :=
  addBounded_isSelfAdjoint beamOperator beamOperator_isSelfAdjoint _
    (beamRitzDiagonal_isSelfAdjoint ε)

/-- `Â` acts as the free beam plus the diagonal block of the perturbation. -/
theorem beamComparison_apply (ε : ℝ) {x : BeamL2} (hx : x ∈ beamOperator.domain) :
    (beamComparison ε) ⟨x, hx⟩
      = beamOperator ⟨x, hx⟩ + beamRitzDiagonal ε x := rfl

/-- `Â + B = A + ε t`: deleting the off-diagonal blocks and restoring them. -/
theorem beamComparison_add_offDiagonal (ε : ℝ) {x : BeamL2}
    (hx : x ∈ beamOperator.domain) :
    (beamComparison ε) ⟨x, hx⟩ + beamRitzOffDiagonal ε x
      = (beamPerturbed ε) ⟨x, hx⟩ := by
  have h2 : (beamPerturbed ε) ⟨x, hx⟩
      = beamOperator ⟨x, hx⟩ + beamPerturbation ε x := rfl
  have h3 : beamRitzOffDiagonal ε x
      = beamPerturbation ε x - beamRitzDiagonal ε x := rfl
  rw [beamComparison_apply, h2, h3]
  abel

/-- The free beam maps into the orthogonal complement of its kernel. -/
theorem beamOperator_apply_mem_orthogonal (x : beamOperator.domain) :
    beamOperator x ∈ beamTrialᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  have hudom : u ∈ beamOperator.domain := beamTrial_le_domain hu
  have hsym : ⟪beamOperator x, u⟫_ℂ
      = ⟪(x : BeamL2), beamOperator ⟨u, hudom⟩⟫_ℂ :=
    (TauCeti.LinearPMap.isSymmetric_of_isSelfAdjoint beamOperator_isSelfAdjoint)
      x ⟨u, hudom⟩
  have hzero : beamOperator ⟨u, hudom⟩ = 0 :=
    beamOperator_apply_trial hu hudom
  rw [← inner_conj_symm (𝕜 := ℂ) u (beamOperator x), hsym, hzero,
    inner_zero_right, map_zero]

/-- The trial projection of a vector of the trial subspace is itself, and its
complementary projection vanishes. -/
theorem starProjection_orthogonal_eq_zero_of_mem_beamTrial {x : BeamL2}
    (hx : x ∈ beamTrial) : beamTrialᗮ.starProjection x = 0 := by
  rw [Submodule.starProjection_orthogonal_apply,
    Submodule.starProjection_eq_self_iff.2 hx, sub_self]

/-- The trial projection of a vector orthogonal to the trial subspace vanishes. -/
theorem starProjection_eq_zero_of_mem_beamTrial_orthogonal {x : BeamL2}
    (hx : x ∈ beamTrialᗮ) : beamTrial.starProjection x = 0 := by
  have h := Submodule.starProjection_orthogonal_apply beamTrial x
  rw [Submodule.starProjection_eq_self_iff.2 hx] at h
  have : x - beamTrial.starProjection x = x := h.symm
  simpa using this

/-- On the trial subspace the comparison operator is the Ritz compression. -/
theorem beamComparison_apply_of_mem_beamTrial (ε : ℝ) {x : BeamL2}
    (hx : x ∈ beamTrial) (hxd : x ∈ beamOperator.domain) :
    (beamComparison ε) ⟨x, hxd⟩
      = beamTrial.starProjection (beamPerturbation ε x) := by
  have hd : beamRitzDiagonal ε x
      = beamTrial.starProjection (beamPerturbation ε (beamTrial.starProjection x))
        + beamTrialᗮ.starProjection
            (beamPerturbation ε (beamTrialᗮ.starProjection x)) := rfl
  rw [beamComparison_apply, beamOperator_apply_trial hx hxd, zero_add, hd,
    Submodule.starProjection_eq_self_iff.2 hx,
    starProjection_orthogonal_eq_zero_of_mem_beamTrial hx, map_zero, map_zero,
    add_zero]

/-- Off the trial subspace the comparison operator is the free beam plus the
compressed perturbation. -/
theorem beamComparison_apply_of_mem_orthogonal (ε : ℝ) {x : BeamL2}
    (hx : x ∈ beamTrialᗮ) (hxd : x ∈ beamOperator.domain) :
    (beamComparison ε) ⟨x, hxd⟩
      = beamOperator ⟨x, hxd⟩
        + beamTrialᗮ.starProjection (beamPerturbation ε x) := by
  have hd : beamRitzDiagonal ε x
      = beamTrial.starProjection (beamPerturbation ε (beamTrial.starProjection x))
        + beamTrialᗮ.starProjection
            (beamPerturbation ε (beamTrialᗮ.starProjection x)) := rfl
  rw [beamComparison_apply, hd,
    Submodule.starProjection_eq_self_iff.2 hx,
    starProjection_eq_zero_of_mem_beamTrial_orthogonal hx, map_zero, map_zero,
    zero_add]

/-! ## The trial subspace reduces the comparison operator -/

/-- **The trial subspace reduces `Â`.**  Both projections preserve the domain, and both
summands are invariant, because `Â` was built block-diagonal and the free beam maps the
complement into itself. -/
theorem beamComparison_reduces (ε : ℝ) :
    TauCeti.LinearPMap.ReducesSubspace (beamComparison ε) beamTrial := by
  refine TauCeti.LinearPMap.ReducesSubspace.of_components ?_ ?_ ?_ ?_
  · intro x
    exact beamTrial_le_domain (beamTrial.starProjection_apply_mem (x : BeamL2))
  · intro x
    have hxd : (x : BeamL2) ∈ beamOperator.domain := x.2
    rw [Submodule.starProjection_orthogonal_apply]
    exact beamOperator.domain.sub_mem hxd
      (beamTrial_le_domain (beamTrial.starProjection_apply_mem _))
  · intro x hx
    have hxd : (x : BeamL2) ∈ beamOperator.domain := x.2
    have heq : (beamComparison ε) x
        = beamTrial.starProjection (beamPerturbation ε (x : BeamL2)) :=
      beamComparison_apply_of_mem_beamTrial ε hx hxd
    rw [heq]
    exact beamTrial.starProjection_apply_mem _
  · intro x hx
    have hxd : (x : BeamL2) ∈ beamOperator.domain := x.2
    have heq : (beamComparison ε) x
        = beamOperator ⟨(x : BeamL2), hxd⟩
          + beamTrialᗮ.starProjection (beamPerturbation ε (x : BeamL2)) :=
      beamComparison_apply_of_mem_orthogonal ε hx hxd
    rw [heq]
    exact beamTrialᗮ.add_mem (beamOperator_apply_mem_orthogonal ⟨_, hxd⟩)
      (beamTrialᗮ.starProjection_apply_mem _)

/-- **`B` is fully off-diagonal**, the source's `H₀ = H₁ = 0`. -/
theorem beamRitzOffDiagonal_isOddFor (ε : ℝ) :
    TauCeti.IsOddFor beamTrial (beamRitzOffDiagonal ε) := by
  constructor
  · intro x hx
    rw [beamRitzOffDiagonal_apply, Submodule.starProjection_eq_self_iff.2 hx,
      starProjection_orthogonal_eq_zero_of_mem_beamTrial hx, map_zero, map_zero,
      add_zero]
    exact beamTrialᗮ.starProjection_apply_mem _
  · intro x hx
    rw [beamRitzOffDiagonal_apply, Submodule.starProjection_eq_self_iff.2 hx,
      starProjection_eq_zero_of_mem_beamTrial_orthogonal hx, map_zero, map_zero,
      zero_add]
    exact beamTrial.starProjection_apply_mem _

/-- **`Â₀ ≤ α̂₂`**: the comparison operator's form on the trial subspace is the Ritz
compression, bounded by the upper Ritz value. -/
theorem beamComparison_form_le_of_mem_beamTrial (ε : ℝ) (hε : 0 ≤ ε)
    (x : (beamComparison ε).domain) (hx : (x : BeamL2) ∈ beamTrial) :
    (⟪(beamComparison ε) x, (x : BeamL2)⟫_ℂ).re
      ≤ ritzHigh ε * ‖(x : BeamL2)‖ ^ 2 := by
  have hxd : (x : BeamL2) ∈ beamOperator.domain := x.2
  have heq : (beamComparison ε) x
      = beamTrial.starProjection (beamPerturbation ε (x : BeamL2)) :=
    beamComparison_apply_of_mem_beamTrial ε hx hxd
  rw [heq, Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.2 hx]
  exact beamRitz_form_le ε hε (⟨(x : BeamL2), hx⟩ : beamTrial)

/-- **`Â₁ > 500`**: the comparison operator's form off the trial subspace still carries
the sharp free-beam gap `500.5`, because `Â₁ - A₁ = E₁* (ε t) E₁ ≥ 0`. -/
theorem beamComparison_form_ge_of_mem_orthogonal (ε : ℝ) (hε : 0 ≤ ε)
    (x : (beamComparison ε).domain) (hx : (x : BeamL2) ∈ beamTrialᗮ) :
    (1001 / 2 : ℝ) * ‖(x : BeamL2)‖ ^ 2
      ≤ (⟪(beamComparison ε) x, (x : BeamL2)⟫_ℂ).re := by
  have hxd : (x : BeamL2) ∈ beamOperator.domain := x.2
  have heq : (beamComparison ε) x
      = beamOperator ⟨(x : BeamL2), hxd⟩
        + beamTrialᗮ.starProjection (beamPerturbation ε (x : BeamL2)) :=
    beamComparison_apply_of_mem_orthogonal ε hx hxd
  rw [heq, inner_add_left, Complex.add_re]
  have h1 := beamOperator_form_ge_of_mem_orthogonal ⟨(x : BeamL2), hxd⟩ hx
  have h2 : (⟪beamTrialᗮ.starProjection (beamPerturbation ε (x : BeamL2)),
      (x : BeamL2)⟫_ℂ).re = (⟪beamPerturbation ε (x : BeamL2), (x : BeamL2)⟫_ℂ).re := by
    rw [Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.2 hx]
  rw [h2]
  have h3 := re_inner_beamPerturbation_nonneg ε hε (x : BeamL2)
  linarith

/-- **The bounded cutoff for the trial subspace.**  The trial subspace is
finite-dimensional and inside the domain, so the orthogonal projection onto it is
already a cutoff: no limiting family is needed. -/
def beamTrialCutoff (ε : ℝ) :
    TauCeti.BoundedCutoff (beamComparison ε) beamTrial
      ‖beamPerturbation ε‖ where
  toProj := beamTrial.starProjection
  isSelfAdjoint := isSelfAdjoint_starProjection beamTrial
  isIdempotentElem := beamTrial.isIdempotentElem_starProjection
  mem_subspace v := beamTrial.starProjection_apply_mem v
  mem_domain v := beamTrial_le_domain (beamTrial.starProjection_apply_mem v)
  norm_apply_le v := by
    have heq : (beamComparison ε)
        ⟨beamTrial.starProjection v,
          beamTrial_le_domain (beamTrial.starProjection_apply_mem v)⟩
        = beamTrial.starProjection
            (beamPerturbation ε (beamTrial.starProjection v)) :=
      beamComparison_apply_of_mem_beamTrial ε
        (beamTrial.starProjection_apply_mem v) _
    rw [heq]
    refine le_trans (beamTrial.norm_starProjection_apply_le _) ?_
    exact (beamPerturbation ε).le_opNorm _
  apply_mem_range v := by
    have heq : (beamComparison ε)
        ⟨beamTrial.starProjection v,
          beamTrial_le_domain (beamTrial.starProjection_apply_mem v)⟩
        = beamTrial.starProjection
            (beamPerturbation ε (beamTrial.starProjection v)) :=
      beamComparison_apply_of_mem_beamTrial ε
        (beamTrial.starProjection_apply_mem v) _
    rw [heq]
    exact Submodule.starProjection_eq_self_iff.2 (beamTrial.starProjection_apply_mem _)

/-! ## The reducing reflection of the perturbed beam -/

/-- The spectral projection of `A + ε t` onto `(-∞, 500]`. -/
abbrev beamLowProjection (ε : ℝ) : BeamL2 →L[ℂ] BeamL2 :=
  TauCeti.LinearPMap.specProjection (beamPerturbed_isSelfAdjoint ε)
    (Set.Iic 500) measurableSet_Iic

/-- The reducing reflection `Z = 2Q - 1` of the perturbed beam at the cut `500`. -/
def beamLowReflection (ε : ℝ) : BeamL2 →L[ℂ] BeamL2 :=
  (2 : ℂ) • beamLowProjection ε - 1

/-- The reflection, pointwise. -/
theorem beamLowReflection_apply (ε : ℝ) (x : BeamL2) :
    beamLowReflection ε x = (2 : ℂ) • beamLowProjection ε x - x := rfl

/-- The reflection is self-adjoint. -/
theorem beamLowReflection_isSelfAdjoint (ε : ℝ) :
    IsSelfAdjoint (beamLowReflection ε) := by
  have h2 : IsSelfAdjoint (2 : ℂ) := by
    show star (2 : ℂ) = 2
    simp
  have hone : IsSelfAdjoint (1 : BeamL2 →L[ℂ] BeamL2) := star_one _
  have hQ : IsSelfAdjoint (beamLowProjection ε) :=
    TauCeti.LinearPMap.isSelfAdjoint_specProjection _ _ _
  exact (h2.smul hQ).sub hone

/-- The reflection is an involution. -/
theorem beamLowReflection_sq (ε : ℝ) :
    beamLowReflection ε * beamLowReflection ε = 1 := by
  have hQ := TauCeti.LinearPMap.specProjection_apply_self
    (beamPerturbed_isSelfAdjoint ε) (Set.Iic 500) measurableSet_Iic
  refine ContinuousLinearMap.ext fun x => ?_
  show beamLowReflection ε (beamLowReflection ε x) = x
  have hstep : beamLowProjection ε (beamLowReflection ε x) = beamLowProjection ε x := by
    rw [beamLowReflection_apply, map_sub, map_smul, hQ x]
    module
  rw [beamLowReflection_apply ε (beamLowReflection ε x), hstep,
    beamLowReflection_apply ε x]
  module

/-- The reflection preserves the domain: spectral projections do. -/
theorem beamLowReflection_mem_domain (ε : ℝ) {x : BeamL2}
    (hx : x ∈ (beamPerturbed ε).domain) :
    beamLowReflection ε x ∈ (beamPerturbed ε).domain := by
  have hQ : beamLowProjection ε x ∈ (beamPerturbed ε).domain :=
    TauCeti.LinearPMap.specProjection_mem_domain (beamPerturbed_isSelfAdjoint ε)
      _ _ ⟨x, hx⟩
  rw [beamLowReflection_apply]
  exact (beamPerturbed ε).domain.sub_mem
    ((beamPerturbed ε).domain.smul_mem _ hQ) hx

/-- The reflection preserves the domain of `Â`, which is the domain of the free beam. -/
theorem beamLowReflection_mapsDomain (ε : ℝ) :
    TauCeti.LinearPMap.MapsDomainTo (beamComparison ε)
      (beamComparison ε) (beamLowReflection ε) := fun x =>
  beamLowReflection_mem_domain ε x.2

/-- The reflection reduces the *perturbed* operator: that is what makes it the paper's
`Z`. -/
theorem beamPerturbed_comm_beamLowReflection (ε : ℝ)
    (x : (beamPerturbed ε).domain)
    (hzd : beamLowReflection ε (x : BeamL2) ∈ (beamPerturbed ε).domain) :
    (beamPerturbed ε) ⟨beamLowReflection ε (x : BeamL2), hzd⟩
      = beamLowReflection ε ((beamPerturbed ε) x) := by
  have hQd : beamLowProjection ε (x : BeamL2) ∈ (beamPerturbed ε).domain :=
    TauCeti.LinearPMap.specProjection_mem_domain (beamPerturbed_isSelfAdjoint ε) _ _ x
  have hsplit : (⟨beamLowReflection ε (x : BeamL2), hzd⟩ :
        (beamPerturbed ε).domain)
      = (2 : ℂ) • (⟨beamLowProjection ε (x : BeamL2), hQd⟩ :
          (beamPerturbed ε).domain) - x := by
    apply Subtype.ext
    exact beamLowReflection_apply ε (x : BeamL2)
  have hcomm := TauCeti.LinearPMap.specProjection_apply_domain
    (beamPerturbed_isSelfAdjoint ε) (Set.Iic 500) measurableSet_Iic x
  rw [hsplit, _root_.LinearPMap.map_sub, _root_.LinearPMap.map_smul, hcomm,
    beamLowReflection_apply]

/-- The commutation hypothesis in the shape the block estimates take: `Z` commutes with
`Â + B = A + ε t` on the domain. -/
theorem beamLowReflection_comm (ε : ℝ)
    (x : (beamComparison ε).domain) :
    (beamComparison ε)
        ⟨beamLowReflection ε (x : BeamL2), beamLowReflection_mapsDomain ε x⟩
      + beamRitzOffDiagonal ε (beamLowReflection ε (x : BeamL2))
      = beamLowReflection ε ((beamComparison ε) x)
        + beamLowReflection ε (beamRitzOffDiagonal ε (x : BeamL2)) := by
  have hxd : (x : BeamL2) ∈ beamOperator.domain := x.2
  have hxp : (x : BeamL2) ∈ (beamPerturbed ε).domain := hxd
  have hzd : beamLowReflection ε (x : BeamL2) ∈ beamOperator.domain :=
    beamLowReflection_mem_domain ε hxp
  have hL : (beamComparison ε) ⟨beamLowReflection ε (x : BeamL2), hzd⟩
      + beamRitzOffDiagonal ε (beamLowReflection ε (x : BeamL2))
      = (beamPerturbed ε) ⟨beamLowReflection ε (x : BeamL2), hzd⟩ :=
    beamComparison_add_offDiagonal ε hzd
  have hR : (beamComparison ε) ⟨(x : BeamL2), hxd⟩
      + beamRitzOffDiagonal ε (x : BeamL2)
      = (beamPerturbed ε) ⟨(x : BeamL2), hxd⟩ :=
    beamComparison_add_offDiagonal ε hxd
  have hZadd : beamLowReflection ε ((beamComparison ε) ⟨(x : BeamL2), hxd⟩)
      + beamLowReflection ε (beamRitzOffDiagonal ε (x : BeamL2))
      = beamLowReflection ε ((beamPerturbed ε) ⟨(x : BeamL2), hxd⟩) := by
    rw [← map_add, hR]
  have hkey : (beamPerturbed ε) ⟨beamLowReflection ε (x : BeamL2), hzd⟩
      = beamLowReflection ε ((beamPerturbed ε) ⟨(x : BeamL2), hxd⟩) :=
    beamPerturbed_comm_beamLowReflection ε ⟨(x : BeamL2), hxp⟩
      (beamLowReflection_mem_domain ε hxp)
  show (beamComparison ε) ⟨beamLowReflection ε (x : BeamL2), hzd⟩
      + beamRitzOffDiagonal ε (beamLowReflection ε (x : BeamL2))
      = beamLowReflection ε ((beamComparison ε) ⟨(x : BeamL2), hxd⟩)
        + beamLowReflection ε (beamRitzOffDiagonal ε (x : BeamL2))
  rw [hL, hZadd, hkey]

/-! ## Equation (9.7): the double-angle tangent, on the genuine operator -/

/-- The tangent of the double angle `2θ` at a trial vector: the ratio of the odd and
even blocks of the reducing reflection `Z`, relative to the trial splitting. -/
def beamTanTwoThetaAt (ε : ℝ) (x : BeamL2) : ℝ :=
  ‖beamTrial.offDiagonalPart (beamLowReflection ε) x‖
    / ‖beamTrial.diagonalPart (beamLowReflection ε) x‖

/-- **The largest double-angle tangent** between the affine trial subspace and the
perturbed beam's low spectral subspace. -/
def beamTanTwoTheta (ε : ℝ) : ℝ :=
  ⨆ x : beamTrial, beamTanTwoThetaAt ε (x : BeamL2)

/-- **The double-angle tangent bound at every trial vector.**  This is the pointwise form
of equation (9.7): the odd block of `Z` over its even block is at most `2‖R̂‖/δ`. -/
theorem beamTanTwoThetaAt_le (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100)
    {x : BeamL2} (hx : x ∈ beamTrial) :
    beamTanTwoThetaAt ε x ≤ tangentTwoThetaExactBound ε := by
  have hritz : ritzHigh ε < 500 := ritzHigh_lt_five_hundred hε100
  have hgapPos : (0 : ℝ) < 500 - ritzHigh ε := by linarith
  have hδ : (0 : ℝ) < 1001 / 2 - ritzHigh ε := by linarith
  have hab : ritzHigh ε < (1001 / 2 : ℝ) := by linarith
  have hσ0 : (0 : ℝ) ≤ orthogonalResidualSingularValue ε := by
    unfold orthogonalResidualSingularValue; positivity
  have hden : (1 : ℝ) - ritzHighCoefficient / 500 * ε ≠ 0 := by
    have h : ritzHigh ε = ε * ritzHighCoefficient := rfl
    rw [h] at hritz
    intro hzero
    apply absurd hritz
    push Not
    nlinarith [hzero]
  have hbound : tangentTwoThetaExactBound ε
      = 2 * orthogonalResidualSingularValue ε / (500 - ritzHigh ε) := by
    unfold tangentTwoThetaExactBound orthogonalResidualSingularValue
    rw [abs_of_pos hε, show ritzHigh ε = ε * ritzHighCoefficient from rfl,
      div_eq_div_iff hden (by
        rw [show ritzHigh ε = ε * ritzHighCoefficient from rfl] at hgapPos
        exact ne_of_gt hgapPos)]
    ring
  have hboundnn : 0 ≤ tangentTwoThetaExactBound ε := by
    rw [hbound]
    positivity
  rcases eq_or_ne x 0 with rfl | hx0
  · simpa [beamTanTwoThetaAt] using hboundnn
  · have hfix : beamTrial.starProjection x = x :=
      Submodule.starProjection_eq_self_iff.2 hx
    have hxt : Filter.Tendsto (fun _ : ℕ => (beamTrialCutoff ε).toProj x)
        Filter.atTop (nhds x) := by
      have hproj : (beamTrialCutoff ε).toProj = beamTrial.starProjection := rfl
      simp only [hproj, hfix]
      exact tendsto_const_nhds
    have hgap := TauCeti.gap_mul_norm_offDiagonalPart_apply_le_of_tendsto
      (beamComparison_reduces ε) (beamRitzOffDiagonal_isOddFor ε)
      (beamLowReflection_isSelfAdjoint ε) (beamLowReflection_sq ε)
      (beamLowReflection_mapsDomain ε) (beamLowReflection_comm ε)
      (a := ritzHigh ε) (b := 1001 / 2)
      (fun z hz => beamComparison_form_le_of_mem_beamTrial ε hε.le z hz)
      (fun z hz => beamComparison_form_ge_of_mem_orthogonal ε hε.le z hz)
      (fun _ : ℕ => ‖beamPerturbation ε‖) (fun _ => beamTrialCutoff ε)
      (fun _ => norm_nonneg _) hab hx hxt
    have hpole := TauCeti.diagonalBlockBound_mul_le_norm_diagonalPart_apply_of_tendsto
      (beamComparison_reduces ε) (beamRitzOffDiagonal_isOddFor ε)
      (beamLowReflection_isSelfAdjoint ε) (beamLowReflection_sq ε)
      (beamLowReflection_mapsDomain ε) (beamLowReflection_comm ε)
      (a := ritzHigh ε) (b := 1001 / 2)
      (fun z hz => beamComparison_form_le_of_mem_beamTrial ε hε.le z hz)
      (fun z hz => beamComparison_form_ge_of_mem_orthogonal ε hε.le z hz)
      (fun _ : ℕ => ‖beamPerturbation ε‖) (fun _ => beamTrialCutoff ε)
      (fun _ => norm_nonneg _) hab hx hxt
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hκ : 0 < TauCeti.diagonalBlockBound ((1001 / 2 : ℝ) - ritzHigh ε)
        ‖beamRitzOffDiagonal ε‖ := by
      rw [TauCeti.diagonalBlockBound_eq]
      have hs : (0 : ℝ) < Real.sqrt (((1001 / 2 : ℝ) - ritzHigh ε) ^ 2
          + 4 * ‖beamRitzOffDiagonal ε‖ ^ 2) :=
        Real.sqrt_pos.mpr (by positivity)
      positivity
    have hdenpos : 0 < ‖beamTrial.diagonalPart (beamLowReflection ε) x‖ :=
      lt_of_lt_of_le (by positivity) hpole
    have hboundge : 2 * ‖beamRitzOffDiagonal ε‖
        ≤ tangentTwoThetaExactBound ε * ((1001 / 2 : ℝ) - ritzHigh ε) := by
      rw [hbound, div_mul_eq_mul_div, le_div_iff₀ hgapPos]
      nlinarith [norm_beamRitzOffDiagonal_le ε, norm_nonneg (beamRitzOffDiagonal ε), hσ0]
    have hmul : 2 * ‖beamRitzOffDiagonal ε‖
          * ‖beamTrial.diagonalPart (beamLowReflection ε) x‖
        ≤ tangentTwoThetaExactBound ε * ((1001 / 2 : ℝ) - ritzHigh ε)
          * ‖beamTrial.diagonalPart (beamLowReflection ε) x‖ :=
      mul_le_mul_of_nonneg_right hboundge (norm_nonneg _)
    rw [beamTanTwoThetaAt, div_le_iff₀ hdenpos]
    nlinarith [hgap, hmul, hδ, norm_nonneg
      (beamTrial.offDiagonalPart (beamLowReflection ε) x)]

/-- **Davis--Kahan 1970, equation (9.7), for the genuine free-beam operator.**

`tan 2θ₁ ≤ tangentTwoThetaExactBound ε`, the paper's `2‖R̂‖/(500 - α̂₂)`.  The
comparison operator is the paper's own `Â = Â₀ ⊕ Â₁` with `Â₁ = E₁*(A + H)E₁`; the
residual is its off-diagonal defect, whose norm is `ε/√15`; the gap is
`Â₁ ≥ 500.5 > 500 > α̂₂ ≥ Â₀`. -/
theorem beamTanTwoTheta_le (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    beamTanTwoTheta ε ≤ tangentTwoThetaExactBound ε :=
  ciSup_le fun x => beamTanTwoThetaAt_le ε hε hε100 x.2

/-- **Equation (9.7) as printed.** -/
theorem beamTanTwoTheta_lt_printed (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    beamTanTwoTheta ε
      < ((1291 : ℝ) / 1250000 * ε) / (1 - (7887 : ℝ) / 5000000 * ε) :=
  equation_9_7 ε (beamTanTwoTheta ε) hε hε100 (beamTanTwoTheta_le ε hε hε100)


end

end Model
end FreeBeam
end DavisKahan
end TauCeti
