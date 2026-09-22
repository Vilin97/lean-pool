/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.Theorem81UnboundedConverse
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.Theorem81UnboundedCompression
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TanTwoThetaUnboundedGramReal
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Complexification.LinearPMapSpectralDescent

/-!
# Theorem 8.1 at unbounded scope over a real Hilbert space

Davis and Kahan work on a Hilbert space over either scalar field, and Theorem 8.1
inherits the `tan 2θ` theorem's unbounded ambient scope.  The complex unbounded
endpoints are in `Theorem81UnboundedBranch`, `Theorem81UnboundedCompression` and
`Theorem81UnboundedConverse`; this module gives their real siblings.

They are separate exact endpoints, not an `RCLike` generalization: the branch is a
spectral subspace, and the spectral measure lives on the complexification.  The
route is therefore the one Theorem 8.2's real endpoints take -- run the complex
theorem on complexified data and descend -- with one addition, that the real
spectral range `realSpecRange` is already a first-class object, so the real branch
is defined directly rather than being produced by the transport.

Every hypothesis transports up (`re_inner_complexifyReal_le_of_forall_mem`,
`le_re_inner_complexifyReal_of_forall_mem_orthogonal`, `isOddFor_complexifySubmodule`,
`reducesSubspace_complexifyReal`) and every conclusion transports down (the form
bounds by evaluating on the real copy, the angle by `subspaceGap_complexifySubmodule`,
the branch identification by `complexifySubmodule_injective`).
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan1970
namespace Section8

open DavisKahan
open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification

noncomputable section

universe v

variable {Er : Type v} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er]
  [CompleteSpace Er]

/-! ### Descending a form bound to the real copy -/

omit [CompleteSpace Er] in
/-- **An upper form bound on a complexified subspace descends.**  Evaluate on the
real copy of a real domain vector. -/
theorem re_inner_le_of_complexifyReal_le {A : Er →ₗ.[ℝ] Er} {U : Submodule ℝ Er}
     {a : ℝ}
    (h : ∀ z : (TauCeti.LinearPMap.complexifyReal A).domain,
      (z : RealComplexification Er) ∈ complexifySubmodule U →
        RCLike.re ⟪TauCeti.LinearPMap.complexifyReal A z,
          (z : RealComplexification Er)⟫_ℂ
          ≤ a * ‖(z : RealComplexification Er)‖ ^ 2) :
    ∀ x : A.domain, (x : Er) ∈ U → ⟪A x, (x : Er)⟫_ℝ ≤ a * ‖(x : Er)‖ ^ 2 := by
  intro x hx
  have hmem : ((TauCeti.LinearPMap.complexifyRealOfRealDomain A x :
      (TauCeti.LinearPMap.complexifyReal A).domain) : RealComplexification Er)
      ∈ complexifySubmodule U := by
    rw [TauCeti.LinearPMap.complexifyRealOfRealDomain_coe, mem_complexifySubmodule]
    simp only [re_ofReal, im_ofReal]
    exact ⟨hx, U.zero_mem⟩
  have hz := h (TauCeti.LinearPMap.complexifyRealOfRealDomain A x) hmem
  rw [TauCeti.LinearPMap.complexifyReal_apply_ofReal,
    TauCeti.LinearPMap.complexifyRealOfRealDomain_coe, inner_ofReal] at hz
  simpa using hz

omit [CompleteSpace Er] in
/-- **A lower form bound on the complement of a complexified subspace descends.** -/
theorem le_re_inner_of_le_complexifyReal {A : Er →ₗ.[ℝ] Er} {U : Submodule ℝ Er}
     {b : ℝ}
    (h : ∀ z : (TauCeti.LinearPMap.complexifyReal A).domain,
      (z : RealComplexification Er) ∈ (complexifySubmodule U)ᗮ →
        b * ‖(z : RealComplexification Er)‖ ^ 2 ≤
          RCLike.re ⟪TauCeti.LinearPMap.complexifyReal A z,
            (z : RealComplexification Er)⟫_ℂ) :
    ∀ x : A.domain, (x : Er) ∈ Uᗮ → b * ‖(x : Er)‖ ^ 2 ≤ ⟪A x, (x : Er)⟫_ℝ := by
  intro x hx
  have hmem : ((TauCeti.LinearPMap.complexifyRealOfRealDomain A x :
      (TauCeti.LinearPMap.complexifyReal A).domain) : RealComplexification Er)
      ∈ (complexifySubmodule U)ᗮ := by
    rw [← complexifySubmodule_orthogonal,
      TauCeti.LinearPMap.complexifyRealOfRealDomain_coe, mem_complexifySubmodule]
    simp only [re_ofReal, im_ofReal]
    exact ⟨hx, Uᗮ.zero_mem⟩
  have hz := h (TauCeti.LinearPMap.complexifyRealOfRealDomain A x) hmem
  rw [TauCeti.LinearPMap.complexifyReal_apply_ofReal,
    TauCeti.LinearPMap.complexifyRealOfRealDomain_coe, inner_ofReal] at hz
  simpa using hz

omit [CompleteSpace Er] in
/-- The maximal principal angle is unchanged by complexification. -/
theorem maximalAngle_complexifySubmodule (U V : Submodule ℝ Er)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    TauCeti.DavisKahanExt.maximalAngle (complexifySubmodule U) (complexifySubmodule V)
      = TauCeti.DavisKahanExt.maximalAngle U V :=
  congrArg Real.arcsin (subspaceGap_complexifySubmodule U V)

omit [CompleteSpace Er] in
/-- The upper form-bound descent, with the complexified data given up to equality
rather than syntactically.  `subst` does the rest. -/
theorem re_inner_le_of_complexifyReal_le_of_eq {A : Er →ₗ.[ℝ] Er}
    {Ac : RealComplexification Er →ₗ.[ℂ] RealComplexification Er}
    (heq : Ac = TauCeti.LinearPMap.complexifyReal A)
    {U : Submodule ℝ Er}
    {Uc : Submodule ℂ (RealComplexification Er)} [Uc.HasOrthogonalProjection]
    (hU : Uc = complexifySubmodule U) {a : ℝ}
    (h : ∀ z : Ac.domain, (z : RealComplexification Er) ∈ Uc →
      RCLike.re ⟪Ac z, (z : RealComplexification Er)⟫_ℂ
        ≤ a * ‖(z : RealComplexification Er)‖ ^ 2) :
    ∀ x : A.domain, (x : Er) ∈ U → ⟪A x, (x : Er)⟫_ℝ ≤ a * ‖(x : Er)‖ ^ 2 := by
  subst heq
  subst hU
  exact re_inner_le_of_complexifyReal_le h

omit [CompleteSpace Er] in
/-- The lower form-bound descent, with the complexified data given up to equality. -/
theorem le_re_inner_of_le_complexifyReal_of_eq {A : Er →ₗ.[ℝ] Er}
    {Ac : RealComplexification Er →ₗ.[ℂ] RealComplexification Er}
    (heq : Ac = TauCeti.LinearPMap.complexifyReal A)
    {U : Submodule ℝ Er}
    {Uc : Submodule ℂ (RealComplexification Er)} [Uc.HasOrthogonalProjection]
    (hU : Uc = complexifySubmodule U) {b : ℝ}
    (h : ∀ z : Ac.domain, (z : RealComplexification Er) ∈ Ucᗮ →
      b * ‖(z : RealComplexification Er)‖ ^ 2 ≤
        RCLike.re ⟪Ac z, (z : RealComplexification Er)⟫_ℂ) :
    ∀ x : A.domain, (x : Er) ∈ Uᗮ → b * ‖(x : Er)‖ ^ 2 ≤ ⟪A x, (x : Er)⟫_ℝ := by
  subst heq
  subst hU
  exact le_re_inner_of_le_complexifyReal h

omit [CompleteSpace Er] in
/-- The angle descent, with the complexified subspaces given up to equality. -/
theorem maximalAngle_le_of_complexifySubmodule_le {U V : Submodule ℝ Er}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {Uc Vc : Submodule ℂ (RealComplexification Er)}
    [Uc.HasOrthogonalProjection] [Vc.HasOrthogonalProjection]
    (hU : Uc = complexifySubmodule U) (hV : Vc = complexifySubmodule V) {t : ℝ}
    (h : TauCeti.DavisKahanExt.maximalAngle Uc Vc ≤ t) :
    TauCeti.DavisKahanExt.maximalAngle U V ≤ t := by
  subst hU
  subst hV
  rwa [maximalAngle_complexifySubmodule] at h

/-! ### The printed characterization over a real Hilbert space -/

/-- **Davis--Kahan 1970, Theorem 8.1's printed characterization, at unbounded
ambient scope over a real Hilbert space.**

`Θ(P, M) ≤ π/4` exactly when the chosen reducing blocks of `A + H` are placed as
the paper prescribes, read as the ordered form bounds `Λ₀ ≤ α` and
`Λ₁ ≥ α + δ`. -/
theorem theorem8_1_maximalAngle_le_iff_orderedFormGap_unbounded_real
    {A : Er →ₗ.[ℝ] Er} {Hop : Er →L[ℝ] Er} {P : Submodule ℝ Er}
    [P.HasOrthogonalProjection] {alpha delta : ℝ}
    (hA : IsSelfAdjoint A) (hH : Hop.IsSymmetric)
    (hredPperp : TauCeti.LinearPMap.ReducesSubspace A Pᗮ)
    (hPlow : ∀ x : A.domain, (x : Er) ∈ P →
      ⟪A x, (x : Er)⟫_ℝ ≤ alpha * ‖(x : Er)‖ ^ 2)
    (hPhigh : ∀ x : A.domain, (x : Er) ∈ Pᗮ →
      (alpha + delta) * ‖(x : Er)‖ ^ 2 ≤ ⟪A x, (x : Er)⟫_ℝ)
    (hHP : ∀ x ∈ P, Hop x ∈ Pᗮ) (hHPperp : ∀ x ∈ Pᗮ, Hop x ∈ P)
    (hdelta : 0 < delta)
    (M : Submodule ℝ Er) [M.HasOrthogonalProjection]
    (hM : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A Hop) M) :
    TauCeti.DavisKahanExt.maximalAngle P M ≤ Real.pi / 4 ↔
      ((∀ x : (TauCeti.LinearPMap.addBounded A Hop).domain, (x : Er) ∈ M →
          ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : Er)⟫_ℝ ≤ alpha * ‖(x : Er)‖ ^ 2) ∧
        ∀ x : (TauCeti.LinearPMap.addBounded A Hop).domain, (x : Er) ∈ Mᗮ →
          (alpha + delta) * ‖(x : Er)‖ ^ 2 ≤
            ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : Er)⟫_ℝ) := by
  classical
  have hAC : IsSelfAdjoint (TauCeti.LinearPMap.complexifyReal A) :=
    TauCeti.LinearPMap.isSelfAdjoint_complexifyReal hA
  have hHC : (complexify Hop).IsSymmetric :=
    (TauCeti.RealComplexification.complexify_isSymmetric_iff Hop).mpr hH
  have hsum : TauCeti.LinearPMap.addBounded (TauCeti.LinearPMap.complexifyReal A)
      (complexify Hop)
      = TauCeti.LinearPMap.complexifyReal (TauCeti.LinearPMap.addBounded A Hop) :=
    (TauCeti.DavisKahan1970.complexifyReal_addBounded A Hop).symm
  have hredPperpC : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.complexifyReal A) (complexifySubmodule P)ᗮ := by
    simpa only [complexifySubmodule_orthogonal] using
      TauCeti.DavisKahan1970.reducesSubspace_complexifyReal hredPperp
  have hMC : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded (TauCeti.LinearPMap.complexifyReal A) (complexify Hop))
      (complexifySubmodule M) := by
    rw [hsum]
    exact TauCeti.DavisKahan1970.reducesSubspace_complexifyReal hM
  have hodd : TauCeti.IsOddFor (complexifySubmodule P) (complexify Hop) :=
    TauCeti.DavisKahan1970.isOddFor_complexifySubmodule ⟨hHP, hHPperp⟩
  have hiff := theorem8_1_maximalAngle_le_iff_orderedFormGap_unbounded
    (A := TauCeti.LinearPMap.complexifyReal A) (Hop := complexify Hop)
    (P := complexifySubmodule P) (alpha := alpha) (delta := delta)
    hAC hHC hredPperpC
    (TauCeti.DavisKahan1970.re_inner_complexifyReal_le_of_forall_mem hPlow)
    (TauCeti.DavisKahan1970.le_re_inner_complexifyReal_of_forall_mem_orthogonal
      (U := P) hPhigh)
    hodd.1 hodd.2 hdelta (complexifySubmodule M) hMC
  rw [maximalAngle_complexifySubmodule, hsum] at hiff
  constructor
  · intro hangle
    obtain ⟨hlow, hhigh⟩ := hiff.1 hangle
    exact ⟨re_inner_le_of_complexifyReal_le (U := M) hlow,
      le_re_inner_of_le_complexifyReal (U := M) hhigh⟩
  · rintro ⟨hlow, hhigh⟩
    exact hiff.2 ⟨TauCeti.DavisKahan1970.re_inner_complexifyReal_le_of_forall_mem hlow,
      TauCeti.DavisKahan1970.le_re_inner_complexifyReal_of_forall_mem_orthogonal
        (U := M) hhigh⟩

/-! ### The canonical branch over a real Hilbert space -/

/-- **Theorem 8.1's canonical branch at unbounded scope over a real Hilbert
space**: the real spectral subspace of the perturbed operator for the closed
half-line `Iic α`.

It is defined directly, not transported: `realSpecRange` descends the complex
spectral projection through the canonical conjugation, and
`complexifySubmodule_realSpecRange` says the two agree. -/
def canonicalLowBranchUnboundedReal {B : Er →ₗ.[ℝ] Er} (hB : IsSelfAdjoint B)
    (alpha : ℝ) : Submodule ℝ Er :=
  TauCeti.LinearPMap.realSpecRange hB (Set.Iic alpha) measurableSet_Iic

/-- The real branch is a real spectral range, hence orthogonally complemented. -/
instance canonicalLowBranchUnboundedReal_hasOrthogonalProjection
    {B : Er →ₗ.[ℝ] Er} (hB : IsSelfAdjoint B) (alpha : ℝ) :
    (canonicalLowBranchUnboundedReal hB alpha).HasOrthogonalProjection :=
  TauCeti.LinearPMap.instHasOrthogonalProjection_realSpecRange hB _ _

/-- The real branch reduces the perturbed operator. -/
theorem canonicalLowBranchUnboundedReal_reduces
    {B : Er →ₗ.[ℝ] Er} (hB : IsSelfAdjoint B) (alpha : ℝ) :
    TauCeti.LinearPMap.ReducesSubspace B (canonicalLowBranchUnboundedReal hB alpha) :=
  TauCeti.LinearPMap.realSpecRange_reduces hB _ _

/-- The complexified real branch is the complex branch. -/
theorem complexifySubmodule_canonicalLowBranchUnboundedReal
    {B : Er →ₗ.[ℝ] Er} (hB : IsSelfAdjoint B) (alpha : ℝ) :
    complexifySubmodule (canonicalLowBranchUnboundedReal hB alpha)
      = canonicalLowBranchUnbounded
          (TauCeti.LinearPMap.isSelfAdjoint_complexifyReal hB) alpha :=
  complexifySubmodule_realSpecRange hB _ _

/-- The complex branch depends on the operator, not on the self-adjointness
proof; this is the transport across the two spellings of the perturbed
complexification. -/
theorem canonicalLowBranchUnbounded_congr {Hc : Type v} [NormedAddCommGroup Hc]
    [InnerProductSpace ℂ Hc] [CompleteSpace Hc] {B₁ B₂ : Hc →ₗ.[ℂ] Hc} (h : B₁ = B₂)
    (h₁ : IsSelfAdjoint B₁) (h₂ : IsSelfAdjoint B₂) (alpha : ℝ) :
    canonicalLowBranchUnbounded h₁ alpha = canonicalLowBranchUnbounded h₂ alpha := by
  subst h
  rfl

/-- **Davis--Kahan 1970, Theorem 8.1's branch, at unbounded ambient scope over a
real Hilbert space.**

`A` is at most `α` on `P` and at least `α + δ` on `Pᗮ`, and `H` is fully
off-diagonal.  The branch `Q` reduces `A + H`, carries `Λ₀ ≤ α` and
`Λ₁ ≥ α + δ`, and satisfies the printed `Θ(P, Q) ≤ π/4`. -/
theorem theorem8_1_canonicalBranchUnbounded_printed_real
    {A : Er →ₗ.[ℝ] Er} {Hop : Er →L[ℝ] Er} {P : Submodule ℝ Er}
    [P.HasOrthogonalProjection] {alpha delta : ℝ}
    (hA : IsSelfAdjoint A) (hH : Hop.IsSymmetric)
    (hredPperp : TauCeti.LinearPMap.ReducesSubspace A Pᗮ)
    (hPlow : ∀ x : A.domain, (x : Er) ∈ P →
      ⟪A x, (x : Er)⟫_ℝ ≤ alpha * ‖(x : Er)‖ ^ 2)
    (hPhigh : ∀ x : A.domain, (x : Er) ∈ Pᗮ →
      (alpha + delta) * ‖(x : Er)‖ ^ 2 ≤ ⟪A x, (x : Er)⟫_ℝ)
    (hHP : ∀ x ∈ P, Hop x ∈ Pᗮ) (hHPperp : ∀ x ∈ Pᗮ, Hop x ∈ P)
    (hdelta : 0 < delta) :
    TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A Hop)
        (canonicalLowBranchUnboundedReal
          (DavisKahan.addBounded_isSelfAdjoint A hA Hop hH) alpha) ∧
      (∀ x : (TauCeti.LinearPMap.addBounded A Hop).domain,
        (x : Er) ∈ canonicalLowBranchUnboundedReal
            (DavisKahan.addBounded_isSelfAdjoint A hA Hop hH) alpha →
        ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : Er)⟫_ℝ ≤
          alpha * ‖(x : Er)‖ ^ 2) ∧
      (∀ x : (TauCeti.LinearPMap.addBounded A Hop).domain,
        (x : Er) ∈ (canonicalLowBranchUnboundedReal
            (DavisKahan.addBounded_isSelfAdjoint A hA Hop hH) alpha)ᗮ →
        (alpha + delta) * ‖(x : Er)‖ ^ 2 ≤
          ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : Er)⟫_ℝ) ∧
      TauCeti.DavisKahanExt.maximalAngle P
        (canonicalLowBranchUnboundedReal
          (DavisKahan.addBounded_isSelfAdjoint A hA Hop hH) alpha)
        ≤ Real.pi / 4 := by
  classical
  have hB : IsSelfAdjoint (TauCeti.LinearPMap.addBounded A Hop) :=
    DavisKahan.addBounded_isSelfAdjoint A hA Hop hH
  have hAC : IsSelfAdjoint (TauCeti.LinearPMap.complexifyReal A) :=
    TauCeti.LinearPMap.isSelfAdjoint_complexifyReal hA
  have hHC : (complexify Hop).IsSymmetric :=
    (TauCeti.RealComplexification.complexify_isSymmetric_iff Hop).mpr hH
  have hsum : TauCeti.LinearPMap.addBounded (TauCeti.LinearPMap.complexifyReal A)
      (complexify Hop)
      = TauCeti.LinearPMap.complexifyReal (TauCeti.LinearPMap.addBounded A Hop) :=
    (TauCeti.DavisKahan1970.complexifyReal_addBounded A Hop).symm
  have hredPperpC : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.complexifyReal A) (complexifySubmodule P)ᗮ := by
    simpa only [complexifySubmodule_orthogonal] using
      TauCeti.DavisKahan1970.reducesSubspace_complexifyReal hredPperp
  have hodd : TauCeti.IsOddFor (complexifySubmodule P) (complexify Hop) :=
    TauCeti.DavisKahan1970.isOddFor_complexifySubmodule ⟨hHP, hHPperp⟩
  have hconc := theorem8_1_canonicalBranchUnbounded_printed
    (A := TauCeti.LinearPMap.complexifyReal A) (Hop := complexify Hop)
    (P := complexifySubmodule P) (alpha := alpha) (delta := delta)
    hAC hHC hredPperpC
    (TauCeti.DavisKahan1970.re_inner_complexifyReal_le_of_forall_mem hPlow)
    (TauCeti.DavisKahan1970.le_re_inner_complexifyReal_of_forall_mem_orthogonal
      (U := P) hPhigh)
    hodd.1 hodd.2 hdelta
  have hbranch : canonicalLowBranchUnbounded (isSelfAdjoint_perturbed hAC hHC) alpha
      = complexifySubmodule (canonicalLowBranchUnboundedReal hB alpha) := by
    rw [complexifySubmodule_canonicalLowBranchUnboundedReal]
    exact canonicalLowBranchUnbounded_congr hsum _ _ alpha
  refine ⟨canonicalLowBranchUnboundedReal_reduces hB alpha, ?_, ?_, ?_⟩
  · exact re_inner_le_of_complexifyReal_le_of_eq
      (A := TauCeti.LinearPMap.addBounded A Hop) hsum hbranch hconc.2.1
  · exact le_re_inner_of_le_complexifyReal_of_eq
      (A := TauCeti.LinearPMap.addBounded A Hop) hsum hbranch hconc.2.2.1
  · exact maximalAngle_le_of_complexifySubmodule_le rfl hbranch hconc.2.2.2

/-- **Theorem 8.1's uniqueness of the branch, at unbounded ambient scope over a
real Hilbert space.**

A reducing subspace of `A + H` inside the closed quarter turn from `P` is the
canonical spectral branch.  This is the converse half of the printed `iff`;
`complexifySubmodule_injective` brings the complex identification back down. -/
theorem theorem8_1_eq_canonicalBranchUnbounded_of_maximalAngle_le_real
    {A : Er →ₗ.[ℝ] Er} {Hop : Er →L[ℝ] Er} {P : Submodule ℝ Er}
    [P.HasOrthogonalProjection] {alpha delta : ℝ}
    (hA : IsSelfAdjoint A) (hH : Hop.IsSymmetric)
    (hredPperp : TauCeti.LinearPMap.ReducesSubspace A Pᗮ)
    (hPlow : ∀ x : A.domain, (x : Er) ∈ P →
      ⟪A x, (x : Er)⟫_ℝ ≤ alpha * ‖(x : Er)‖ ^ 2)
    (hPhigh : ∀ x : A.domain, (x : Er) ∈ Pᗮ →
      (alpha + delta) * ‖(x : Er)‖ ^ 2 ≤ ⟪A x, (x : Er)⟫_ℝ)
    (hHP : ∀ x ∈ P, Hop x ∈ Pᗮ) (hHPperp : ∀ x ∈ Pᗮ, Hop x ∈ P)
    (hdelta : 0 < delta)
    (M : Submodule ℝ Er) [M.HasOrthogonalProjection]
    (hM : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A Hop) M)
    (hMangle : TauCeti.DavisKahanExt.maximalAngle P M ≤ Real.pi / 4) :
    M = canonicalLowBranchUnboundedReal
      (DavisKahan.addBounded_isSelfAdjoint A hA Hop hH) alpha := by
  classical
  have hB : IsSelfAdjoint (TauCeti.LinearPMap.addBounded A Hop) :=
    DavisKahan.addBounded_isSelfAdjoint A hA Hop hH
  have hAC : IsSelfAdjoint (TauCeti.LinearPMap.complexifyReal A) :=
    TauCeti.LinearPMap.isSelfAdjoint_complexifyReal hA
  have hHC : (complexify Hop).IsSymmetric :=
    (TauCeti.RealComplexification.complexify_isSymmetric_iff Hop).mpr hH
  have hsum : TauCeti.LinearPMap.addBounded (TauCeti.LinearPMap.complexifyReal A)
      (complexify Hop)
      = TauCeti.LinearPMap.complexifyReal (TauCeti.LinearPMap.addBounded A Hop) :=
    (TauCeti.DavisKahan1970.complexifyReal_addBounded A Hop).symm
  have hredPperpC : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.complexifyReal A) (complexifySubmodule P)ᗮ := by
    simpa only [complexifySubmodule_orthogonal] using
      TauCeti.DavisKahan1970.reducesSubspace_complexifyReal hredPperp
  have hMC : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded (TauCeti.LinearPMap.complexifyReal A) (complexify Hop))
      (complexifySubmodule M) := by
    rw [hsum]
    exact TauCeti.DavisKahan1970.reducesSubspace_complexifyReal hM
  have hodd : TauCeti.IsOddFor (complexifySubmodule P) (complexify Hop) :=
    TauCeti.DavisKahan1970.isOddFor_complexifySubmodule ⟨hHP, hHPperp⟩
  have hangleC : TauCeti.DavisKahanExt.maximalAngle (complexifySubmodule P)
      (complexifySubmodule M) ≤ Real.pi / 4 := by
    rwa [maximalAngle_complexifySubmodule]
  have hMQ := theorem8_1_eq_canonicalBranchUnbounded_of_maximalAngle_le
    (A := TauCeti.LinearPMap.complexifyReal A) (Hop := complexify Hop)
    (P := complexifySubmodule P) (alpha := alpha) (delta := delta)
    hAC hHC hredPperpC
    (TauCeti.DavisKahan1970.re_inner_complexifyReal_le_of_forall_mem hPlow)
    (TauCeti.DavisKahan1970.le_re_inner_complexifyReal_of_forall_mem_orthogonal
      (U := P) hPhigh)
    hodd.1 hodd.2 hdelta (complexifySubmodule M) hMC hangleC
  have hbranch : canonicalLowBranchUnbounded (isSelfAdjoint_perturbed hAC hHC) alpha
      = complexifySubmodule (canonicalLowBranchUnboundedReal hB alpha) := by
    rw [complexifySubmodule_canonicalLowBranchUnboundedReal]
    exact canonicalLowBranchUnbounded_congr hsum _ _ alpha
  refine complexifySubmodule_injective ?_
  rw [hMQ, hbranch]

/-! ### Part (i) over a real Hilbert space

Part (i) is projection algebra and does not touch the spectral measure, so the
real endpoint is the same argument over `ℝ` rather than a transport. -/

omit [CompleteSpace Er] in
/-- **The energy splits along a reducing subspace**, over a real Hilbert space. -/
theorem re_inner_split_of_reduces_real {B : Er →ₗ.[ℝ] Er} {Q : Submodule ℝ Er}
    [Q.HasOrthogonalProjection] (hred : TauCeti.LinearPMap.ReducesSubspace B Q)
    (x : B.domain) :
    ⟪B x, (x : Er)⟫_ℝ
      = ⟪B ⟨Q.starProjection (x : Er), hred.projection_mem_domain x⟩,
          Q.starProjection (x : Er)⟫_ℝ
        + ⟪B ⟨Qᗮ.starProjection (x : Er), hred.orthogonalProjection_mem_domain x⟩,
            Qᗮ.starProjection (x : Er)⟫_ℝ := by
  have hxeq : x = (⟨Q.starProjection (x : Er), hred.projection_mem_domain x⟩ : B.domain)
      + ⟨Qᗮ.starProjection (x : Er), hred.orthogonalProjection_mem_domain x⟩ :=
    Subtype.ext (by
      change (x : Er) = Q.starProjection (x : Er) + Qᗮ.starProjection (x : Er)
      rw [Submodule.starProjection_orthogonal_apply]
      abel)
  have hcross1 : ⟪B (⟨Q.starProjection (x : Er), hred.projection_mem_domain x⟩ : B.domain),
      Qᗮ.starProjection (x : Er)⟫_ℝ = 0 :=
    (Submodule.mem_orthogonal Q _).mp (Qᗮ.starProjection_apply_mem _) _
      (hred.invariant _ (Q.starProjection_apply_mem _))
  have hcross2 : ⟪B (⟨Qᗮ.starProjection (x : Er),
      hred.orthogonalProjection_mem_domain x⟩ : B.domain),
      Q.starProjection (x : Er)⟫_ℝ = 0 := by
    refine (Submodule.mem_orthogonal Qᗮ _).mp ?_ _
      (hred.orthogonal_invariant _ (Qᗮ.starProjection_apply_mem _))
    rw [Submodule.orthogonal_orthogonal]
    exact Q.starProjection_apply_mem _
  have hstep : ⟪B x, (x : Er)⟫_ℝ
      = ⟪B ((⟨Q.starProjection (x : Er), hred.projection_mem_domain x⟩ : B.domain)
            + ⟨Qᗮ.starProjection (x : Er), hred.orthogonalProjection_mem_domain x⟩),
          (((⟨Q.starProjection (x : Er), hred.projection_mem_domain x⟩ : B.domain)
            + ⟨Qᗮ.starProjection (x : Er),
                hred.orthogonalProjection_mem_domain x⟩ : B.domain) : Er)⟫_ℝ :=
    congrArg (fun z : B.domain => ⟪B z, (z : Er)⟫_ℝ) hxeq
  rw [hstep, _root_.LinearPMap.map_add]
  change ⟪_ + _, (Q.starProjection (x : Er) + Qᗮ.starProjection (x : Er))⟫_ℝ = _
  rw [inner_add_left, inner_add_right, inner_add_right, hcross1, hcross2]
  ring

omit [CompleteSpace Er] in
/-- **Davis--Kahan 1970, Theorem 8.1 part (i), upper block, at unbounded scope
over a real Hilbert space.** -/
theorem theorem8_1_upperCompressionRepulsion_unbounded_real
    {B : Er →ₗ.[ℝ] Er} {Q : Submodule ℝ Er} [Q.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace B Q) {alpha : ℝ}
    (hQlow : ∀ y : B.domain, (y : Er) ∈ Q →
      ⟪B y, (y : Er)⟫_ℝ ≤ alpha * ‖(y : Er)‖ ^ 2)
    (x : B.domain) :
    ⟪B x, (x : Er)⟫_ℝ - alpha * ‖(x : Er)‖ ^ 2 ≤
      ⟪B ⟨Qᗮ.starProjection (x : Er), hred.orthogonalProjection_mem_domain x⟩,
        Qᗮ.starProjection (x : Er)⟫_ℝ
        - alpha * ‖Qᗮ.starProjection (x : Er)‖ ^ 2 := by
  have hsplit := re_inner_split_of_reduces_real hred x
  have hnorm : ‖(x : Er)‖ ^ 2
      = ‖Q.starProjection (x : Er)‖ ^ 2 + ‖Qᗮ.starProjection (x : Er)‖ ^ 2 :=
    Submodule.norm_sq_eq_add_norm_sq_starProjection (x : Er) Q
  have hlow := hQlow ⟨Q.starProjection (x : Er), hred.projection_mem_domain x⟩
    (Q.starProjection_apply_mem _)
  rw [hsplit, hnorm]
  nlinarith [hlow]

omit [CompleteSpace Er] in
/-- **Theorem 8.1 part (i), lower block, at unbounded scope over a real Hilbert
space.** -/
theorem theorem8_1_lowerCompressionRepulsion_unbounded_real
    {B : Er →ₗ.[ℝ] Er} {Q : Submodule ℝ Er} [Q.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace B Q) {c : ℝ}
    (hQhigh : ∀ y : B.domain, (y : Er) ∈ Qᗮ →
      c * ‖(y : Er)‖ ^ 2 ≤ ⟪B y, (y : Er)⟫_ℝ)
    (x : B.domain) :
    c * ‖(x : Er)‖ ^ 2 - ⟪B x, (x : Er)⟫_ℝ ≤
      c * ‖Q.starProjection (x : Er)‖ ^ 2
        - ⟪B ⟨Q.starProjection (x : Er), hred.projection_mem_domain x⟩,
            Q.starProjection (x : Er)⟫_ℝ := by
  have hsplit := re_inner_split_of_reduces_real hred x
  have hnorm : ‖(x : Er)‖ ^ 2
      = ‖Q.starProjection (x : Er)‖ ^ 2 + ‖Qᗮ.starProjection (x : Er)‖ ^ 2 :=
    Submodule.norm_sq_eq_add_norm_sq_starProjection (x : Er) Q
  have hhigh := hQhigh
    ⟨Qᗮ.starProjection (x : Er), hred.orthogonalProjection_mem_domain x⟩
    (Qᗮ.starProjection_apply_mem _)
  rw [hsplit, hnorm]
  nlinarith [hhigh]

end

end Section8
end DavisKahan1970
end TauCeti
