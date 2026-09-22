/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.ReducingSubspace
import LeanPool.DavisKahan.DavisKahan.Sylvester.ClosedSylvesterEquation
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.CanonicalRealView
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions
import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.AbstractSpectrum
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.PartialMap.BoundedRealization
import LeanPool.DavisKahan.DavisKahan.Sylvester.Gap
import LeanPool.DavisKahan.DavisKahan.Sylvester.Unbounded.Neumann
import LeanPool.DavisKahan.ForTauCeti.Analysis.CStarAlgebra.SelfAdjointGapInverse
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.Projector
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks

/-! # Spectrum -/


open TauCeti.DavisKahan.Sylvester

/-!
# The genuine-spectrum Sylvester estimate and the general `sin Θ` theorem

Hypotheses here are phrased through the Banach-algebra spectrum, either of the
ambient operator or of its compression to a reducing subspace.

**The `genuine` in these names is now historical, and this paragraph used to say
so wrongly.**  It read: *"The separation predicates in `Core/AbstractSpectrum.lean`
are point-spectrum based and therefore vacuous for operators with empty point
spectrum; the theorems stated over them are unprovable in infinite dimensions …
This module is the honest layer."*  Every clause of that was true on 2026-07-15
and none of it is true now:

* the statement-soundness finding of 2026-07-15 was **repaired in place, not
  worked around** — `docs/planning/davis-kahan-full-paper-goal.md` records that
  the repaired layer defines `realSpectrum` from the `RCLike` Banach-algebra
  spectrum and carries invariance explicitly, *"which removes the counterexample
  that made the Sylvester, `sin Θ`, ideal, off-diagonal and Riccati declarations
  false as stated"*;
* `DavisKahan/SpectralTheory/AbstractSpectrum.lean`, the live layer, is
  therefore already the honest one;
* `Core/AbstractSpectrum.lean` **does not exist**: it was deleted on 2026-07-24
  in `e91ef142`, empty, as a retired facade.

So there is no vacuous sibling that these theorems are distinguishing themselves
from, and the prefix marks nothing.  Dropping it across the `genuine` family is
lane `DK-NAME`, which was **blocked on sequestering a layer that had already
been repaired** — a block this docstring caused.  Measured 2026-07-30 under lane
`DK-FAILED`.

Main results, all fully proved:

* `norm_sylvester_le_of_spectrum_intervalExterior`: the constant-one
  interval/exterior Sylvester estimate.  If the self-adjoint `B` has spectrum
  in `[a, b]` while the self-adjoint `A` has spectrum outside
  `(a - d, b + d)`, then `A X - X B = C` forces `d ‖X‖ ≤ ‖C‖`.  The proof is
  the shift-and-invert argument: center at `c = (a+b)/2`, invert `A - c`
  through the continuous functional calculus with inverse norm at most
  `(r + d)⁻¹` where `r = (b-a)/2`, bound `‖B - c‖ ≤ r`, and absorb.
* `sinTheta_spectrum`: the fully general bounded operator-norm
  Davis--Kahan `sin Θ` theorem with genuine spectra: if `U` reduces the
  self-adjoint `A` with the spectrum of the compression `A|_U` in `[a, b]`,
  and `V` reduces the self-adjoint `B` with the spectrum of `B|_{Vᗮ}` outside
  `(a - d, b + d)`, then `d * directedGap U V ≤ ‖B - A‖`.

Complex scalars are required because Mathlib registers the continuous
functional calculus on Hilbert-space operators only over `ℂ`; the real case
is expected to follow by a norm-preserving complexification transfer.
-/

namespace TauCeti
namespace DavisKahan.Sylvester



open DavisKahan.Foundation

open DavisKahan

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]
/-- **Shifting by the interval midpoint pushes an exterior spectrum off zero.** -/
private theorem shifted_spectrum_exterior {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] {S : G →L[ℂ] G} {a b d c r : ℝ}
    (hc : c = (a + b) / 2) (hr : r = (b - a) / 2)
    (hspec : ∀ x ∈ spectrum ℝ S, x ≤ a - d ∨ b + d ≤ x) :
    ∀ x ∈ spectrum ℝ (S - algebraMap ℝ (G →L[ℂ] G) c), r + d ≤ |x| := by
  intro x hx
  rw [← spectrum.sub_singleton_eq] at hx
  obtain ⟨y, hy, z, hz, hyz⟩ := Set.mem_sub.mp hx
  rw [Set.mem_singleton_iff] at hz
  rw [hz] at hyz
  rw [← hyz]
  rcases hspec y hy with h1 | h1
  · have hle : y - c ≤ -(r + d) := by rw [hc, hr]; linarith
    calc r + d ≤ -(y - c) := by linarith
      _ ≤ |y - c| := neg_le_abs _
  · have hge : r + d ≤ y - c := by rw [hc, hr]; linarith
    exact hge.trans (le_abs_self _)

/-- **...and centres an interior spectrum on `[-r, r]`.**

Both Sylvester bounds in this file derived the pair inline. -/
private theorem shifted_spectrum_interior {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] {S : G →L[ℂ] G} {a b c r : ℝ}
    (hc : c = (a + b) / 2) (hr : r = (b - a) / 2)
    (hspec : spectrum ℝ S ⊆ Set.Icc a b) :
    spectrum ℝ (S - algebraMap ℝ (G →L[ℂ] G) c) ⊆ Set.Icc (-r) r := by
  intro x hx
  rw [← spectrum.sub_singleton_eq] at hx
  obtain ⟨y, hy, z, hz, hyz⟩ := Set.mem_sub.mp hx
  rw [Set.mem_singleton_iff] at hz
  rw [hz] at hyz
  have hmem := hspec hy
  rw [Set.mem_Icc] at hmem
  rw [← hyz, Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · rw [hc, hr]; linarith [hmem.1]
  · rw [hc, hr]; linarith [hmem.2]

/-- **Constant-one interval/exterior Sylvester estimate, genuine spectra.**
If the spectrum of the self-adjoint `B` lies in `[a, b]` while the spectrum
of the self-adjoint `A` avoids `(a - d, b + d)`, then any solution of
`A X - X B = C` satisfies `d ‖X‖ ≤ ‖C‖`. -/
theorem norm_sylvester_le_of_spectrum_intervalExterior
    {A : F →L[ℂ] F} {B : E →L[ℂ] E} {X C : E →L[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hBspec : spectrum ℝ B ⊆ Set.Icc a b)
    (hAspec : ∀ x ∈ spectrum ℝ A, x ≤ a - d ∨ b + d ≤ x)
    (hEq : A ∘L X - X ∘L B = C) :
    d * ‖X‖ ≤ ‖C‖ := by
  set c : ℝ := (a + b) / 2 with hc
  set r : ℝ := (b - a) / 2 with hrdef
  have hr0 : 0 ≤ r := by rw [hrdef]; linarith
  have hrd : (0 : ℝ) < r + d := by linarith
  set A₁ : F →L[ℂ] F := A - algebraMap ℝ (F →L[ℂ] F) c with hA₁
  set B₁ : E →L[ℂ] E := B - algebraMap ℝ (E →L[ℂ] E) c with hB₁
  have hA₁sa : IsSelfAdjoint A₁ :=
    hA.sub (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all c))
  have hB₁sa : IsSelfAdjoint B₁ :=
    hB.sub (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all c))
  -- spectral position of the shifted operators
  have hA₁spec : ∀ x ∈ spectrum ℝ A₁, r + d ≤ |x| :=
    shifted_spectrum_exterior hc hrdef hAspec
  have hB₁spec : spectrum ℝ B₁ ⊆ Set.Icc (-r) r :=
    shifted_spectrum_interior hc hrdef hBspec
  have hB₁norm : ‖B₁‖ ≤ r :=
    (TauCeti.IsSelfAdjoint.norm_le_iff_spectrum_subset_Icc hB₁sa hr0).mpr hB₁spec
  have hA₁unit : IsUnit A₁ := TauCeti.isUnit_of_forall_le_abs hrd hA₁spec
  set J : F →L[ℂ] F := Ring.inverse A₁
  have hJ1 : J * A₁ = 1 := Ring.inverse_mul_cancel _ hA₁unit
  have hJnorm : ‖J‖ ≤ (r + d)⁻¹ :=
    TauCeti.IsSelfAdjoint.norm_ringInverse_le hA₁sa hrd hA₁spec
  -- the shifted Sylvester equation
  have hEq₁ : A₁ ∘L X - X ∘L B₁ = C := by
    have h1 : algebraMap ℝ (F →L[ℂ] F) c ∘L X =
        X ∘L algebraMap ℝ (E →L[ℂ] E) c := by
      ext x
      simp [Algebra.algebraMap_eq_smul_one]
    calc A₁ ∘L X - X ∘L B₁
        = (A ∘L X - X ∘L B) -
            (algebraMap ℝ (F →L[ℂ] F) c ∘L X -
              X ∘L algebraMap ℝ (E →L[ℂ] E) c) := by
          rw [hA₁, hB₁, ContinuousLinearMap.sub_comp,
            ContinuousLinearMap.comp_sub]
          abel
      _ = C := by rw [h1, sub_self, sub_zero, hEq]
  -- absorb through the inverse
  have hJ1' : J ∘L A₁ = ContinuousLinearMap.id ℂ F := by
    rw [← ContinuousLinearMap.mul_def, hJ1, ContinuousLinearMap.one_def]
  have hXeq : X = J ∘L (C + X ∘L B₁) := by
    have h2 : A₁ ∘L X = C + X ∘L B₁ := by rw [← hEq₁]; abel
    calc X = (J ∘L A₁) ∘L X := by
          rw [hJ1', ContinuousLinearMap.id_comp]
      _ = J ∘L (A₁ ∘L X) := by rw [ContinuousLinearMap.comp_assoc]
      _ = J ∘L (C + X ∘L B₁) := by rw [h2]
  have hnorm : ‖X‖ ≤ (r + d)⁻¹ * (‖C‖ + ‖X‖ * r) := by
    calc ‖X‖ = ‖J ∘L (C + X ∘L B₁)‖ := by rw [← hXeq]
      _ ≤ ‖J‖ * ‖C + X ∘L B₁‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖J‖ * (‖C‖ + ‖X‖ * ‖B₁‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact (norm_add_le _ _).trans
            (add_le_add le_rfl (ContinuousLinearMap.opNorm_comp_le _ _))
      _ ≤ (r + d)⁻¹ * (‖C‖ + ‖X‖ * r) := by
          refine mul_le_mul hJnorm ?_ (by positivity)
            (inv_nonneg.mpr hrd.le)
          exact add_le_add le_rfl
            (mul_le_mul_of_nonneg_left hB₁norm (norm_nonneg _))
  have hkey := mul_le_mul_of_nonneg_left hnorm hrd.le
  rw [← mul_assoc, mul_inv_cancel₀ hrd.ne', one_mul] at hkey
  nlinarith [norm_nonneg X]

section Compression

/-- Compression of an ambient operator to a subspace admitting an orthogonal
projection.  For a reducing subspace of a self-adjoint operator this is the
honest restriction, and its Banach-algebra spectrum is the correct
interpretation of "the spectrum of `A` on `U`". -/
noncomputable def compressOperator
    {𝕜 G : Type*} [RCLike 𝕜] [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (U : Submodule 𝕜 G) [U.HasOrthogonalProjection]
    (T : G →L[𝕜] G) : U →L[𝕜] U :=
  U.orthogonalProjectionOnto ∘L T ∘L U.subtypeL

/-- On an invariant orthogonally complemented subspace, orthogonal compression is
exactly the continuous-linear restriction.

This projection-geometric statement is scalar-generic over `RCLike`; the
complex-only Sylvester/spectrum arguments below merely instantiate it at `ℂ`.
Keeping the compression primitive here scalar-generic lets the real Halmos and
Davis--Kahan layers share the same restriction API. -/
theorem compressOperator_eq_restrict_of_invariant
    {𝕜 G : Type*} [RCLike 𝕜] [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (T : G →L[𝕜] G) (U : Submodule 𝕜 G) [U.HasOrthogonalProjection]
    (hU : InvariantFor T U) :
    compressOperator U T = T.restrict hU := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  change U.starProjection (T (u : G)) = T (u : G)
  exact Submodule.starProjection_eq_self_iff.mpr (hU (u : G) u.property)

/-- Compression preserves self-adjointness. -/
theorem isSelfAdjoint_compressOperator
    {𝕜 G : Type*} [RCLike 𝕜] [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [CompleteSpace G]
    {T : G →L[𝕜] G} (hT : IsSelfAdjoint T)
    (U : Submodule 𝕜 G) [U.HasOrthogonalProjection] [CompleteSpace U] :
    IsSelfAdjoint (compressOperator U T) := by
  -- Left as a `rw` chain on purpose: `simp only` with this same list leaves the goal unsolved: at
  -- least one lemma here has to fire at one occurrence, in order, and simp's normal form loses the
  -- intermediate shape.
  rw [ContinuousLinearMap.isSelfAdjoint_iff', compressOperator,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    Submodule.adjoint_subtypeL, Submodule.adjoint_orthogonalProjectionOnto,
    ← ContinuousLinearMap.star_eq_adjoint, hT.star_eq,
    ContinuousLinearMap.comp_assoc]

omit [CompleteSpace E] in
/-- The orthogonal complement of a reducing subspace is reducing. -/
theorem _root_.ContinuousLinearMap.Reduces.orthogonalComplement {T : E →L[ℂ] E} {V : Submodule ℂ E}
    [V.HasOrthogonalProjection] (hV : T.Reduces V) : T.Reduces Vᗮ := by
  refine ⟨hV.2, ?_⟩
  intro y hy
  rw [Submodule.orthogonal_orthogonal] at hy ⊢
  exact hV.1 y hy

omit [CompleteSpace E] in
/-- The cross-block compression satisfies the Sylvester equation between the
two diagonal compressions. -/
theorem compress_sylvester_of_reduces
    {A B : E →L[ℂ] E} {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : B.Reduces V) :
    compressOperator Vᗮ B ∘L (Vᗮ.orthogonalProjectionOnto ∘L U.subtypeL) -
        (Vᗮ.orthogonalProjectionOnto ∘L U.subtypeL) ∘L compressOperator U A =
      Vᗮ.orthogonalProjectionOnto ∘L (B - A) ∘L U.subtypeL := by
  have hVperp : B.Reduces Vᗮ := hV.orthogonalComplement
  ext x
  simp only [ContinuousLinearMap.comp_apply, sub_apply,
    compressOperator, AddSubgroupClass.coe_sub, Submodule.subtypeL_apply,
    Submodule.coe_orthogonalProjectionOnto_apply]
  rw [← ContinuousLinearMap.starProjection_apply_comm_of_reduces B Vᗮ hVperp,
    Submodule.starProjection_eq_self_iff.mpr
      (Vᗮ.starProjection_apply_mem (B (x : E))),
    ContinuousLinearMap.starProjection_apply_comm_of_reduces A U hU,
    Submodule.starProjection_eq_self_iff.mpr x.2, map_sub]

omit [CompleteSpace E] in
/-- The cross-block compression has the norm of the directed projection
composition. -/
theorem norm_crossCompression_eq
    (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    ‖Vᗮ.orthogonalProjectionOnto ∘L U.subtypeL‖ =
      ‖Vᗮ.starProjection ∘L U.starProjection‖ := by
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg _) fun x => ?_
    have hkey : ((Vᗮ.orthogonalProjectionOnto ((x : E)) : ↥Vᗮ) : E) =
        (Vᗮ.starProjection ∘L U.starProjection) (x : E) := by
      change Vᗮ.starProjection (x : E) =
        Vᗮ.starProjection (U.starProjection (x : E))
      rw [Submodule.starProjection_eq_self_iff.mpr x.2]
    change ‖((Vᗮ.orthogonalProjectionOnto ((x : E)) : ↥Vᗮ) : E)‖ ≤
      ‖Vᗮ.starProjection ∘L U.starProjection‖ * ‖(x : E)‖
    rw [hkey]
    exact (Vᗮ.starProjection ∘L U.starProjection).le_opNorm _
  · refine ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg _) fun y => ?_
    have hkey : (Vᗮ.starProjection ∘L U.starProjection) y =
        (((Vᗮ.orthogonalProjectionOnto ∘L U.subtypeL)
          (U.orthogonalProjectionOnto y) : ↥Vᗮ) : E) := rfl
    rw [hkey]
    calc ‖(((Vᗮ.orthogonalProjectionOnto ∘L U.subtypeL)
          (U.orthogonalProjectionOnto y) : ↥Vᗮ) : E)‖
        = ‖(Vᗮ.orthogonalProjectionOnto ∘L U.subtypeL)
            (U.orthogonalProjectionOnto y)‖ := rfl
      _ ≤ ‖Vᗮ.orthogonalProjectionOnto ∘L U.subtypeL‖ *
            ‖U.orthogonalProjectionOnto y‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖Vᗮ.orthogonalProjectionOnto ∘L U.subtypeL‖ * ‖y‖ := by
          refine mul_le_mul_of_nonneg_left ?_
            (ContinuousLinearMap.opNorm_nonneg _)
          change ‖((U.orthogonalProjectionOnto y : ↥U) : E)‖ ≤ ‖y‖
          exact U.norm_starProjection_apply_le y

end Compression

/-- **The fully general bounded operator-norm Davis--Kahan `sin Θ` theorem,
genuine spectra.**  If `U` reduces the self-adjoint `A` with the spectrum of
the compression `A|_U` contained in `[a, b]`, and `V` reduces the
self-adjoint `B` with the spectrum of the compression `B|_{Vᗮ}` outside the
open interval `(a - d, b + d)`, then `d * directedGap U V ≤ ‖B - A‖`. -/
theorem sinTheta_spectrum
    {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : B.Reduces V)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hUspec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc a b)
    (hVspec : ∀ x ∈ spectrum ℝ (compressOperator Vᗮ B),
      x ≤ a - d ∨ b + d ≤ x) :
    d * U.directedProjectionGap V ≤ ‖B - A‖ := by
  have : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  have : CompleteSpace (Vᗮ : Submodule ℂ E) :=
    (Vᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  have hsyl := compress_sylvester_of_reduces hU hV
  have hest := norm_sylvester_le_of_spectrum_intervalExterior
    (isSelfAdjoint_compressOperator hB Vᗮ)
    (isSelfAdjoint_compressOperator hA U)
    hd hab hUspec hVspec hsyl
  have hCnorm : ‖Vᗮ.orthogonalProjectionOnto ∘L (B - A) ∘L U.subtypeL‖ ≤
      ‖B - A‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg _) fun x => ?_
    change ‖((Vᗮ.orthogonalProjectionOnto ((B - A) (x : E)) : ↥Vᗮ) : E)‖ ≤
      ‖B - A‖ * ‖(x : E)‖
    calc ‖((Vᗮ.orthogonalProjectionOnto ((B - A) (x : E)) : ↥Vᗮ) : E)‖
        = ‖Vᗮ.starProjection ((B - A) (x : E))‖ := rfl
      _ ≤ ‖(B - A) (x : E)‖ := Vᗮ.norm_starProjection_apply_le _
      _ ≤ ‖B - A‖ * ‖(x : E)‖ := (B - A).le_opNorm _
  calc d * U.directedProjectionGap V
      = d * ‖Vᗮ.orthogonalProjectionOnto ∘L U.subtypeL‖ := by
        rw [norm_crossCompression_eq]
        rfl
    _ ≤ ‖Vᗮ.orthogonalProjectionOnto ∘L (B - A) ∘L U.subtypeL‖ := hest
    _ ≤ ‖B - A‖ := hCnorm

/-- **Symmetric two-sided genuine-spectrum `sin Θ` theorem.**  When both
directed spectral configurations hold — the spectrum of `A|_U` in `[a, b]`
with `B|_{Vᗮ}` outside `(a - d, b + d)`, and the spectrum of `B|_V` in
`[a', b']` with `A|_{Uᗮ}` outside `(a' - d, b' + d)` — the full projection
gap (the maximum of the two directed gaps) obeys the same bound:
`d * subspaceGap U V ≤ ‖B - A‖`. -/
theorem sinTheta_spectrum_symmetric
    {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : B.Reduces V)
    {a b a' b' d : ℝ} (hd : 0 < d) (hab : a ≤ b) (hab' : a' ≤ b')
    (hUspec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc a b)
    (hVspec : ∀ x ∈ spectrum ℝ (compressOperator Vᗮ B),
      x ≤ a - d ∨ b + d ≤ x)
    (hVspec' : spectrum ℝ (compressOperator V B) ⊆ Set.Icc a' b')
    (hUspec' : ∀ x ∈ spectrum ℝ (compressOperator Uᗮ A),
      x ≤ a' - d ∨ b' + d ≤ x) :
    d * U.projectionGap V ≤ ‖B - A‖ := by
  have h1 : d * U.directedProjectionGap V ≤ ‖B - A‖ :=
    sinTheta_spectrum hA hB hU hV hd hab hUspec hVspec
  have h2 : d * V.directedProjectionGap U ≤ ‖A - B‖ :=
    sinTheta_spectrum hB hA hV hU hd hab' hVspec' hUspec'
  rw [show A - B = -(B - A) by abel, norm_neg] at h2
  have hmax : U.projectionGap V = max (U.directedProjectionGap V) (V.directedProjectionGap U) :=
    U.projectionGap_eq_max_directedProjectionGap V
  rw [hmax, mul_max_of_nonneg _ _ hd.le]
  exact max_le h1 h2

section IdealScope


universe v'

variable {E₁ F₁ : Type v'}
  [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [CompleteSpace F₁]
/-- **Ideal-gauge interval/exterior Sylvester estimate, genuine spectra.**
If the spectrum of the self-adjoint `B` lies in `[a, b]` while the spectrum
of the self-adjoint `A` avoids `(a - d, b + d)`, and `C` lies in a
rectangular symmetric ideal family, then any solution of `A X - X B = C`
lies in the family with `d · gauge X ≤ gauge C` — through the
shift-and-invert data and the Neumann-iteration ideal engine. -/
theorem mem_and_gauge_sylvester_le_of_spectrum_intervalExterior
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, v'} ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    {A : F₁ →L[ℂ] F₁} {B : E₁ →L[ℂ] E₁} {X C : E₁ →L[ℂ] F₁}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hBspec : spectrum ℝ B ⊆ Set.Icc a b)
    (hAspec : ∀ x ∈ spectrum ℝ A, x ≤ a - d ∨ b + d ≤ x)
    (hEq : A ∘L X - X ∘L B = C)
    (hC : N.Mem C) :
    N.Mem X ∧ d * N.gaugeReal X ≤ N.gaugeReal C := by
  set c : ℝ := (a + b) / 2 with hc
  set r : ℝ := (b - a) / 2 with hrdef
  have hr0 : 0 ≤ r := by rw [hrdef]; linarith
  have hrd : (0 : ℝ) < r + d := by linarith
  set A₁ : F₁ →L[ℂ] F₁ := A - algebraMap ℝ (F₁ →L[ℂ] F₁) c with hA₁
  set B₁ : E₁ →L[ℂ] E₁ := B - algebraMap ℝ (E₁ →L[ℂ] E₁) c with hB₁
  have hA₁sa : IsSelfAdjoint A₁ :=
    hA.sub (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all c))
  have hB₁sa : IsSelfAdjoint B₁ :=
    hB.sub (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all c))
  have hA₁spec : ∀ x ∈ spectrum ℝ A₁, r + d ≤ |x| :=
    shifted_spectrum_exterior hc hrdef hAspec
  have hB₁spec : spectrum ℝ B₁ ⊆ Set.Icc (-r) r :=
    shifted_spectrum_interior hc hrdef hBspec
  have hB₁norm : ‖B₁‖ ≤ r :=
    (TauCeti.IsSelfAdjoint.norm_le_iff_spectrum_subset_Icc hB₁sa hr0).mpr hB₁spec
  have hA₁unit : IsUnit A₁ := TauCeti.isUnit_of_forall_le_abs hrd hA₁spec
  set J : F₁ →L[ℂ] F₁ := Ring.inverse A₁
  have hJ1 : J * A₁ = 1 := Ring.inverse_mul_cancel _ hA₁unit
  have hJ2 : A₁ * J = 1 := Ring.mul_inverse_cancel _ hA₁unit
  have hJnorm : ‖J‖ ≤ (r + d)⁻¹ :=
    TauCeti.IsSelfAdjoint.norm_ringInverse_le hA₁sa hrd hA₁spec
  have hEq₁ : A₁ ∘L X - X ∘L B₁ = C := by
    have h1 : algebraMap ℝ (F₁ →L[ℂ] F₁) c ∘L X =
        X ∘L algebraMap ℝ (E₁ →L[ℂ] E₁) c := by
      ext x
      simp [Algebra.algebraMap_eq_smul_one]
    calc A₁ ∘L X - X ∘L B₁
        = (A ∘L X - X ∘L B) -
            (algebraMap ℝ (F₁ →L[ℂ] F₁) c ∘L X -
              X ∘L algebraMap ℝ (E₁ →L[ℂ] E₁) c) := by
          rw [hA₁, hB₁, ContinuousLinearMap.sub_comp,
            ContinuousLinearMap.comp_sub]
          abel
      _ = C := by rw [h1, sub_self, sub_zero, hEq]
  -- package the inverse for the Neumann ideal engine
  have hEq' : TauCeti.LinearPMap.SylvesterEquation
      (A₁.toLinearMap.toPMap ⊤) (B₁.toLinearMap.toPMap ⊤) X C :=
    TauCeti.LinearPMap.SylvesterEquation.ofBounded hEq₁
  refine Sylvester_mem_and_gauge_le_of_unbounded_bound_inverse N
    ⟨J, fun y => Submodule.mem_top, ?_, ?_⟩ B₁ hr0 hd hJnorm hB₁norm hEq' hC
  · intro y
    change A₁ (J y) = y
    simpa using DFunLike.congr_fun hJ2 y
  · intro x
    change J (A₁ (x : F₁)) = (x : F₁)
    simpa using DFunLike.congr_fun hJ1 (x : F₁)

end IdealScope

section SinThetaIdealScope

open TauCeti.DavisKahan.ExactSinTheta

/-- **The bounded Davis--Kahan `sin Θ` theorem at unitary-invariant ideal
scope, genuine spectra.**  Under the directed spectral configuration of
`sinTheta_spectrum`, if the perturbation `B - A` lies in a
rectangular symmetric ideal family, then so does the directed projection
composition `P_{Vᗮ} P_U`, with `d · gauge (P_{Vᗮ} P_U) ≤ gauge (B - A)` —
the ideal-gauge strengthening of `d * directedGap U V ≤ ‖B - A‖`. -/
theorem sinTheta_spectrum_gauge
    (N : TauCeti.SymmetricOperatorIdealFamily ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : B.Reduces V)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hUspec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc a b)
    (hVspec : ∀ x ∈ spectrum ℝ (compressOperator Vᗮ B),
      x ≤ a - d ∨ b + d ≤ x)
    (hMem : N.Mem (B - A)) :
    N.Mem (Vᗮ.starProjection ∘L U.starProjection) ∧
      d * N.gaugeReal (Vᗮ.starProjection ∘L U.starProjection) ≤
        N.gaugeReal (B - A) := by
  have : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  have : CompleteSpace (Vᗮ : Submodule ℂ E) :=
    (Vᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  have hsyl := compress_sylvester_of_reduces hU hV
  have hCmem : N.Mem (Vᗮ.orthogonalProjectionOnto ∘L (B - A) ∘L U.subtypeL) :=
    N.comp_mem _ _ hMem
  have hmain := mem_and_gauge_sylvester_le_of_spectrum_intervalExterior N
    (isSelfAdjoint_compressOperator hB Vᗮ)
    (isSelfAdjoint_compressOperator hA U)
    hd hab hUspec hVspec hsyl hCmem
  have hfact : Vᗮ.starProjection ∘L U.starProjection =
      Vᗮ.subtypeL ∘L (Vᗮ.orthogonalProjectionOnto ∘L U.subtypeL) ∘L
        U.orthogonalProjectionOnto := by
    ext x
    rfl
  constructor
  · rw [hfact]
    exact N.comp_mem _ _ hmain.1
  · have hgle : N.gaugeReal (Vᗮ.starProjection ∘L U.starProjection) ≤
        N.gaugeReal (Vᗮ.orthogonalProjectionOnto ∘L U.subtypeL) := by
      rw [hfact]
      exact N.gaugeReal_comp_le_of_contractions _ _ hmain.1
        Vᗮ.norm_subtypeL_le U.orthogonalProjectionOnto_norm_le
    have hCle : N.gaugeReal (Vᗮ.orthogonalProjectionOnto ∘L (B - A) ∘L U.subtypeL)
        ≤ N.gaugeReal (B - A) :=
      N.gaugeReal_comp_le_of_contractions _ _ hMem
        Vᗮ.orthogonalProjectionOnto_norm_le U.norm_subtypeL_le
    calc d * N.gaugeReal (Vᗮ.starProjection ∘L U.starProjection)
        ≤ d * N.gaugeReal (Vᗮ.orthogonalProjectionOnto ∘L U.subtypeL) :=
          mul_le_mul_of_nonneg_left hgle hd.le
      _ ≤ N.gaugeReal (Vᗮ.orthogonalProjectionOnto ∘L (B - A) ∘L U.subtypeL) :=
          hmain.2
      _ ≤ N.gaugeReal (B - A) := hCle

/-- The projector difference decomposes into the two directed cross blocks:
`P_U - P_V = P_{Vᗮ} P_U - (P_{Uᗮ} P_V)⋆`. -/
theorem starProjection_sub_eq_cross_sub_cross_adjoint
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.starProjection - V.starProjection =
      Vᗮ.starProjection ∘L U.starProjection -
        (Uᗮ.starProjection ∘L V.starProjection).adjoint := by
  have hadj : (Uᗮ.starProjection ∘L V.starProjection).adjoint =
      V.starProjection ∘L Uᗮ.starProjection := by
    rw [ContinuousLinearMap.adjoint_comp,
      ← ContinuousLinearMap.star_eq_adjoint,
      ← ContinuousLinearMap.star_eq_adjoint,
      (isSelfAdjoint_starProjection V).star_eq,
      (isSelfAdjoint_starProjection Uᗮ).star_eq]
  rw [hadj, Submodule.starProjection_orthogonal' V,
    Submodule.starProjection_orthogonal' U]
  ext x
  simp only [ContinuousLinearMap.comp_apply, sub_apply, one_apply_eq_self, map_sub]
  abel

/-- **The symmetric two-sided bounded `sin Θ` theorem at unitary-invariant
ideal scope, genuine spectra.**  Both directed spectral configurations and
`B - A` in the family give ideal membership of the projector difference with
`d · gauge (P_U - P_V) ≤ 2 · gauge (B - A)`, by decomposing the projector
difference into the two directed cross blocks. -/
theorem sinTheta_spectrum_gauge_symmetric
    (N : TauCeti.SymmetricOperatorIdealFamily ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : A.Reduces U) (hV : B.Reduces V)
    {a b a' b' d : ℝ} (hd : 0 < d) (hab : a ≤ b) (hab' : a' ≤ b')
    (hUspec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc a b)
    (hVspec : ∀ x ∈ spectrum ℝ (compressOperator Vᗮ B),
      x ≤ a - d ∨ b + d ≤ x)
    (hVspec' : spectrum ℝ (compressOperator V B) ⊆ Set.Icc a' b')
    (hUspec' : ∀ x ∈ spectrum ℝ (compressOperator Uᗮ A),
      x ≤ a' - d ∨ b' + d ≤ x)
    (hMem : N.Mem (B - A)) :
    N.Mem (U.starProjection - V.starProjection) ∧
      d * N.gaugeReal (U.starProjection - V.starProjection) ≤
        2 * N.gaugeReal (B - A) := by
  have h1 := sinTheta_spectrum_gauge N hA hB hU hV hd hab
    hUspec hVspec hMem
  have hMem' : N.Mem (A - B) := by
    rw [show A - B = -(B - A) from by abel]
    exact N.neg_mem hMem
  have h2 := sinTheta_spectrum_gauge N hB hA hV hU hd hab'
    hVspec' hUspec' hMem'
  have hgAB : N.gaugeReal (A - B) = N.gaugeReal (B - A) := by
    rw [show A - B = -(B - A) from by abel]
    exact N.gaugeReal_neg hMem
  rw [hgAB] at h2
  have hdecomp := starProjection_sub_eq_cross_sub_cross_adjoint U V
  have hMemAdj : N.Mem ((Uᗮ.starProjection ∘L V.starProjection).adjoint) :=
    N.adjoint_mem h2.1
  have hgAdj : N.gaugeReal ((Uᗮ.starProjection ∘L V.starProjection).adjoint) =
      N.gaugeReal (Uᗮ.starProjection ∘L V.starProjection) :=
    N.gaugeReal_adjoint h2.1
  constructor
  · rw [hdecomp]
    exact N.sub_mem h1.1 hMemAdj
  · calc d * N.gaugeReal (U.starProjection - V.starProjection)
        ≤ d * (N.gaugeReal (Vᗮ.starProjection ∘L U.starProjection) +
            N.gaugeReal ((Uᗮ.starProjection ∘L V.starProjection).adjoint)) := by
          refine mul_le_mul_of_nonneg_left ?_ hd.le
          rw [hdecomp]
          exact N.gaugeReal_sub_le h1.1 hMemAdj
      _ = d * N.gaugeReal (Vᗮ.starProjection ∘L U.starProjection) +
            d * N.gaugeReal (Uᗮ.starProjection ∘L V.starProjection) := by
          rw [hgAdj]; ring
      _ ≤ N.gaugeReal (B - A) + N.gaugeReal (B - A) := add_le_add h1.2 h2.2
      _ = 2 * N.gaugeReal (B - A) := by ring

end SinThetaIdealScope

end DavisKahan.Sylvester
end TauCeti
