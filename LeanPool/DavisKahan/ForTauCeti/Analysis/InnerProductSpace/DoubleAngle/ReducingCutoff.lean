/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.DoubleAngle.SpectralCutoff

/-!
# Every reducing subspace carries the Appendix's cutoff family

`ForTauCeti/Analysis/InnerProductSpace/DoubleAngle/UnboundedPole.lean` proves the
pole-exclusion estimates for an **arbitrary** reducing subspace `U` of a
self-adjoint `A`, given a family of `TauCeti.BoundedCutoff`s converging strongly
to the identity on `U`.  `…/SpectralCutoff.lean` then supplies that family in one
case only: `U = 1_{(-∞,c]}(A)`, using the bands `1_{[-τ,c]}(A)`.

That restriction is an artefact of the construction, not of the mathematics.  A
reducing subspace carries its own self-adjoint operator `A|_U`, and *its*
spectral bands `1_{[-n,n]}(A|_U)` are a cutoff family for `A` on `U`: their
ranges lie in `U` by construction, in `D(A)` because a bounded band of a
self-adjoint operator does, and they exhaust `U` because the spectral measure of
`A|_U` is a resolution of the identity of `U`.

So the pole exclusion, and with it the unbounded `sin 2Θ` and `tan 2Θ`
endpoints, need no spectral *selection* of the trial subspace — only that it
reduces `A`.  This is what makes those source theorems statable at the paper's
hypothesis, which is a splitting of the spectrum, not a choice of half-line.

## Main results

* `TauCeti.BoundedCutoff.ofReducingRestriction` — transport of a cutoff for the
  restriction `A|_U` on all of `U` to a cutoff for `A` on `U`.
* `TauCeti.spectralBandCutoff` — the bands `1_{[-τ,τ]}(A)` as a cutoff on `⊤`.
* `TauCeti.reducingCutoffSeq`, `TauCeti.tendsto_reducingCutoffSeq` — the family
  for an arbitrary reducing subspace, and its strong convergence on `U`.
* `TauCeti.norm_offDiagonalPart_lt_one_reducing`,
  `TauCeti.norm_offDiagonalPart_apply_le_reducing`,
  `TauCeti.gap_mul_norm_offDiagonalPart_apply_le_reducing` — the pole exclusion
  itself, with the spectral selection of the trial subspace removed.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46, Appendix to Section 6.
-/

@[expose] public section

namespace TauCeti

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-! ### Transporting a cutoff along a reducing restriction -/

section Transport

variable {𝕜 : Type*} [RCLike 𝕜] {G : Type*} [NormedAddCommGroup G]
  [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- A subspace admitting an orthogonal projection inside a complete ambient
space is itself complete. -/
local instance instCompleteSpaceCoeReducingCutoff
    (U : Submodule 𝕜 G) [U.HasOrthogonalProjection] : CompleteSpace U :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe

private theorem adjoint_subtypeL_subtypeL_apply
    (U : Submodule 𝕜 G) [U.HasOrthogonalProjection] (y : U) :
    U.subtypeL.adjoint (U.subtypeL y) = y := by
  refine Subtype.ext ?_
  rw [Submodule.adjoint_subtypeL, Submodule.coe_orthogonalProjectionOnto_apply]
  exact Submodule.starProjection_eq_self_iff.mpr y.2

private theorem adjoint_subtypeL_apply_of_mem
    (U : Submodule 𝕜 G) [U.HasOrthogonalProjection] {x : G} (hx : x ∈ U) :
    U.subtypeL.adjoint x = ⟨x, hx⟩ :=
  adjoint_subtypeL_subtypeL_apply U ⟨x, hx⟩

/-- The lift of an operator on a subspace to the ambient space, by the inclusion
and its adjoint.  Named so that the structure fields below can be rewritten with
`liftProj_apply` rather than fighting the composition's dependent proofs. -/
private noncomputable def liftProj (U : Submodule 𝕜 G) [U.HasOrthogonalProjection]
    (P : U →L[𝕜] U) : G →L[𝕜] G :=
  U.subtypeL ∘L P ∘L U.subtypeL.adjoint

private theorem liftProj_apply (U : Submodule 𝕜 G) [U.HasOrthogonalProjection]
    (P : U →L[𝕜] U) (v : G) :
    liftProj U P v = ((P (U.subtypeL.adjoint v) : U) : G) := rfl

/-- **A cutoff for the restriction is a cutoff for the ambient operator.**

`A|_U` is an operator on `U`; a `BoundedCutoff` for it on the whole of `U`
becomes a `BoundedCutoff` for `A` on `U` by conjugating with the inclusion.
Every field transports directly, because the inclusion is an isometry with
`ι⋆ ι = 1` and `A` acts on `U`-vectors of `D(A)` exactly as `A|_U` does. -/
noncomputable def BoundedCutoff.ofReducingRestriction
    {A : G →ₗ.[𝕜] G} {U : Submodule 𝕜 G} [U.HasOrthogonalProjection]
    (hred : LinearPMap.ReducesSubspace A U) {τ : ℝ}
    (Ω : BoundedCutoff (LinearPMap.reducingRestriction A U hred) ⊤ τ) :
    BoundedCutoff A U τ where
  toProj := liftProj U Ω.toProj
  isSelfAdjoint := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff', liftProj,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.isSelfAdjoint_iff'.mp Ω.isSelfAdjoint]
    rfl
  isIdempotentElem := by
    have hidem : ∀ w : U, Ω.toProj (Ω.toProj w) = Ω.toProj w := fun w => by
      have h := congrArg (fun T : U →L[𝕜] U => T w) Ω.isIdempotentElem
      simpa using h
    refine ContinuousLinearMap.ext fun x => ?_
    simp only [_root_.mul_apply_eq_comp, liftProj_apply]
    rw [show ((Ω.toProj (U.subtypeL.adjoint x) : U) : G)
        = U.subtypeL (Ω.toProj (U.subtypeL.adjoint x)) from rfl,
      adjoint_subtypeL_subtypeL_apply, hidem]
    rfl
  mem_subspace := fun v => by
    rw [liftProj_apply]
    exact (Ω.toProj (U.subtypeL.adjoint v)).2
  mem_domain := fun v => by
    rw [liftProj_apply]
    exact (LinearPMap.mem_reducingRestriction_domain_iff A U hred _).mp
      (Ω.mem_domain (U.subtypeL.adjoint v))
  norm_apply_le := fun v => by
    have hw : ((Ω.toProj (U.subtypeL.adjoint v) : U) : G) ∈ A.domain :=
      (LinearPMap.mem_reducingRestriction_domain_iff A U hred _).mp
        (Ω.mem_domain (U.subtypeL.adjoint v))
    simp only [liftProj_apply]
    rw [← LinearPMap.coe_reducingRestriction_apply A U hred
      (Ω.toProj (U.subtypeL.adjoint v)) hw]
    simpa using Ω.norm_apply_le (U.subtypeL.adjoint v)
  apply_mem_range := fun v => by
    have hw : ((Ω.toProj (U.subtypeL.adjoint v) : U) : G) ∈ A.domain :=
      (LinearPMap.mem_reducingRestriction_domain_iff A U hred _).mp
        (Ω.mem_domain (U.subtypeL.adjoint v))
    have hrange := Ω.apply_mem_range (U.subtypeL.adjoint v)
    simp only [liftProj_apply]
    rw [← LinearPMap.coe_reducingRestriction_apply A U hred
      (Ω.toProj (U.subtypeL.adjoint v)) hw]
    rw [show ((LinearPMap.reducingRestriction A U hred
          ⟨Ω.toProj (U.subtypeL.adjoint v),
            Ω.mem_domain (U.subtypeL.adjoint v)⟩ : U) : G)
        = U.subtypeL (LinearPMap.reducingRestriction A U hred
          ⟨Ω.toProj (U.subtypeL.adjoint v),
            Ω.mem_domain (U.subtypeL.adjoint v)⟩) from rfl,
      adjoint_subtypeL_subtypeL_apply]
    exact congrArg (fun y : U => (y : G)) hrange

/-- The projection of a transported cutoff, applied to a vector of `U`. -/
theorem BoundedCutoff.ofReducingRestriction_toProj_apply
    {A : G →ₗ.[𝕜] G} {U : Submodule 𝕜 G} [U.HasOrthogonalProjection]
    (hred : LinearPMap.ReducesSubspace A U) {τ : ℝ}
    (Ω : BoundedCutoff (LinearPMap.reducingRestriction A U hred) ⊤ τ)
    {x : G} (hx : x ∈ U) :
    (BoundedCutoff.ofReducingRestriction hred Ω).toProj x =
      ((Ω.toProj ⟨x, hx⟩ : U) : G) := by
  have hcomp : (BoundedCutoff.ofReducingRestriction hred Ω).toProj x =
      liftProj U Ω.toProj x := rfl
  rw [hcomp, liftProj_apply, adjoint_subtypeL_apply_of_mem U hx]

end Transport

/-! ### The symmetric spectral band as a cutoff on the whole space -/

section Band

variable {A : H →ₗ.[ℂ] H}

private theorem abs_le_of_mem_Icc_symm {T s : ℝ} (hs : s ∈ Set.Icc (-T) T) :
    |s| ≤ T := abs_le.mpr ⟨(Set.mem_Icc.mp hs).1, (Set.mem_Icc.mp hs).2⟩

/-- **The symmetric spectral band `1_{[-τ,τ]}(A)` is a bounded cutoff on the
whole space.**  Unlike `TauCeti.spectralCutoff` it selects no half-line, so it
applies to any self-adjoint operator with no reference to a cut point. -/
noncomputable def spectralBandCutoff (hA : IsSelfAdjoint A) {T : ℝ} (hT : 0 ≤ T) :
    BoundedCutoff A ⊤ T where
  toProj := LinearPMap.specProjection hA (Set.Icc (-T) T) measurableSet_Icc
  isSelfAdjoint := LinearPMap.isSelfAdjoint_specProjection hA _ measurableSet_Icc
  isIdempotentElem :=
    LinearPMap.isIdempotentElem_specProjection hA _ measurableSet_Icc
  mem_subspace := fun _ => Submodule.mem_top
  mem_domain := fun v =>
    LinearPMap.mem_domain_of_mem_specRange_of_bounded hA _ measurableSet_Icc
      (fun _ hs => abs_le_of_mem_Icc_symm hs)
      (LinearPMap.specProjection_mem_specRange hA _ measurableSet_Icc v)
  norm_apply_le := fun v => by
    have h := LinearPMap.norm_sub_smul_le_of_mem_specRange hA _ measurableSet_Icc
      (M := T) (c := 0) (r := T) (fun _ hs => abs_le_of_mem_Icc_symm hs) hT
      (fun _ hs => by simpa using abs_le_of_mem_Icc_symm hs)
      (LinearPMap.specProjection_mem_specRange hA _ measurableSet_Icc v)
      (LinearPMap.mem_domain_of_mem_specRange_of_bounded hA _ measurableSet_Icc
        (fun _ hs => abs_le_of_mem_Icc_symm hs)
        (LinearPMap.specProjection_mem_specRange hA _ measurableSet_Icc v))
    simpa only [Complex.ofReal_zero, zero_smul, sub_zero] using h
  apply_mem_range := fun v => by
    have hidem := LinearPMap.specProjection_apply_specProjection_of_subset hA
      measurableSet_Icc measurableSet_Icc (subset_refl (Set.Icc (-T) T)) v
    have hmem : LinearPMap.specProjection hA (Set.Icc (-T) T) measurableSet_Icc v
        ∈ A.domain :=
      LinearPMap.mem_domain_of_mem_specRange_of_bounded hA _ measurableSet_Icc
        (fun _ hs => abs_le_of_mem_Icc_symm hs)
        (LinearPMap.specProjection_mem_specRange hA _ measurableSet_Icc v)
    have h := LinearPMap.specProjection_apply_domain hA (Set.Icc (-T) T)
      measurableSet_Icc ⟨_, hmem⟩
    have hsub : (⟨LinearPMap.specProjection hA (Set.Icc (-T) T) measurableSet_Icc
          (LinearPMap.specProjection hA (Set.Icc (-T) T) measurableSet_Icc v),
        LinearPMap.specProjection_mem_domain hA _ measurableSet_Icc
          ⟨_, hmem⟩⟩ : A.domain) = ⟨_, hmem⟩ := Subtype.ext hidem
    rw [hsub] at h
    exact h.symm

/-- The projection underlying the symmetric band cutoff. -/
theorem spectralBandCutoff_toProj (hA : IsSelfAdjoint A) {T : ℝ} (hT : 0 ≤ T) :
    (spectralBandCutoff hA hT).toProj =
      LinearPMap.specProjection hA (Set.Icc (-T) T) measurableSet_Icc := by
  simp only [spectralBandCutoff]

end Band

/-! ### The cutoff family of an arbitrary reducing subspace -/

section Reducing

variable {A : H →ₗ.[ℂ] H} {U : Submodule ℂ H} [U.HasOrthogonalProjection]

/-- A subspace admitting an orthogonal projection inside a complete ambient space
is itself complete; reinstalled in this section over `ℂ`. -/
local instance instCompleteSpaceCoeReducingCutoffC
    (W : Submodule ℂ H) [W.HasOrthogonalProjection] : CompleteSpace W :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection W).completeSpace_coe

/-- The restriction of a self-adjoint operator to a reducing subspace is
self-adjoint.  A self-adjoint partial map is densely defined, so the density
hypothesis of `LinearPMap.reducingRestriction_isSelfAdjoint` is automatic. -/
theorem isSelfAdjoint_reducingRestriction (hA : IsSelfAdjoint A)
    (hred : LinearPMap.ReducesSubspace A U) :
    IsSelfAdjoint (LinearPMap.reducingRestriction A U hred) :=
  LinearPMap.reducingRestriction_isSelfAdjoint A U hred hA.dense_domain hA

/-- **The cutoff family of an arbitrary reducing subspace**: the spectral bands
`1_{[-n,n]}(A|_U)` of the restriction, carried into the ambient space. -/
noncomputable def reducingCutoffSeq (hA : IsSelfAdjoint A)
    (hred : LinearPMap.ReducesSubspace A U) (n : ℕ) :
    BoundedCutoff A U (n : ℝ) :=
  BoundedCutoff.ofReducingRestriction hred
    (spectralBandCutoff (isSelfAdjoint_reducingRestriction hA hred)
      (Nat.cast_nonneg n))

/-- **The cutoffs converge strongly to the identity on the reducing subspace.**
This is the `τ → ∞` input the pole-exclusion endpoints need, now available for
every reducing subspace rather than only for a spectral half-line. -/
theorem tendsto_reducingCutoffSeq (hA : IsSelfAdjoint A)
    (hred : LinearPMap.ReducesSubspace A U) {x : H} (hx : x ∈ U) :
    Filter.Tendsto (fun n : ℕ => (reducingCutoffSeq hA hred n).toProj x)
      Filter.atTop (nhds x) := by
  have hAU := isSelfAdjoint_reducingRestriction hA hred
  have hshift : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hband : Filter.Tendsto
      (fun n : ℕ => LinearPMap.specProjection hAU
        (Set.Icc (-(n : ℝ)) (n : ℝ)) measurableSet_Icc ⟨x, hx⟩)
      Filter.atTop (nhds (⟨x, hx⟩ : U)) :=
    (LinearPMap.tendsto_specProjection_Icc hAU ⟨x, hx⟩).comp hshift
  have hcoe : Filter.Tendsto
      (fun n : ℕ => ((LinearPMap.specProjection hAU
        (Set.Icc (-(n : ℝ)) (n : ℝ)) measurableSet_Icc ⟨x, hx⟩ : U) : H))
      Filter.atTop (nhds x) := by
    have := (continuous_subtype_val.tendsto (⟨x, hx⟩ : U)).comp hband
    simpa [Function.comp_def] using this
  refine hcoe.congr fun n => ?_
  exact (BoundedCutoff.ofReducingRestriction_toProj_apply hred
    (spectralBandCutoff hAU (Nat.cast_nonneg n)) hx).symm

end Reducing


/-! ### Unconditional pole exclusion at an arbitrary reducing subspace -/

section Unconditional

variable {A : H →ₗ.[ℂ] H} {B Z : H →L[ℂ] H} {U : Submodule ℂ H}
  [U.HasOrthogonalProjection] {a b : ℝ}

variable (hA : IsSelfAdjoint A) (hred : LinearPMap.ReducesSubspace A U)
  (hB : IsOddFor U B) (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
  (hZdom : LinearPMap.MapsDomainTo A A Z)
  (hZcomm : ∀ x : A.domain,
    A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
  (hUa : ∀ x : A.domain, (x : H) ∈ U →
    (⟪A x, (x : H)⟫_ℂ).re ≤ a * ‖(x : H)‖ ^ 2)
  (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
    b * ‖(x : H)‖ ^ 2 ≤ (⟪A x, (x : H)⟫_ℂ).re)
  (hab : a < b)

include hA hred hB hZsa hZ2 hZdom hZcomm hUa hUb hab

/-- **The cross block is a strict contraction, for any reducing subspace.**

`TauCeti.norm_offDiagonalPart_lt_one_of_tendsto` with the cutoff family of
`reducingCutoffSeq`: the trial subspace need only reduce `A` and carry the two
form bounds.  Selecting it as a spectral half-line, as
`TauCeti.norm_offDiagonalPart_apply_le_specRange` does, is not needed. -/
theorem norm_offDiagonalPart_lt_one_reducing :
    ‖U.offDiagonalPart Z‖ < 1 :=
  norm_offDiagonalPart_lt_one_of_tendsto hred hB hZsa hZ2 hZdom hZcomm hUa hUb
    (fun n : ℕ => (n : ℝ)) (fun n => reducingCutoffSeq hA hred n)
    (fun n => Nat.cast_nonneg n) hab
    (fun _ hx => tendsto_reducingCutoffSeq hA hred hx)

/-- The uniform cross-block bound `‖sin 2Θ₀‖ ≤ 2‖B‖/√(δ² + 4‖B‖²)`, for any
reducing subspace. -/
theorem norm_offDiagonalPart_le_reducing :
    ‖U.offDiagonalPart Z‖ ≤ crossBlockBound (b - a) ‖B‖ :=
  norm_offDiagonalPart_le_of_tendsto hred hB hZsa hZ2 hZdom hZcomm hUa hUb
    (fun n : ℕ => (n : ℝ)) (fun n => reducingCutoffSeq hA hred n)
    (fun n => Nat.cast_nonneg n) hab
    (fun _ hx => tendsto_reducingCutoffSeq hA hred hx)

/-- The pointwise cross-block bound on the trial subspace, for any reducing
subspace: `‖sin 2Θ₀ x‖ ≤ (2‖B‖/√(δ² + 4‖B‖²)) ‖x‖` for `x ∈ U`. -/
theorem norm_offDiagonalPart_apply_le_reducing {x : H} (hx : x ∈ U) :
    ‖U.offDiagonalPart Z x‖ ≤ crossBlockBound (b - a) ‖B‖ * ‖x‖ :=
  norm_offDiagonalPart_apply_le_of_tendsto hred hB hZsa hZ2 hZdom hZcomm hUa hUb
    (fun n : ℕ => (n : ℝ)) (fun n => reducingCutoffSeq hA hred n)
    (fun n => Nat.cast_nonneg n) hab (tendsto_reducingCutoffSeq hA hred hx)

/-- **Pole exclusion, for any reducing subspace**: `κ ‖x‖ ≤ ‖cos 2Θ₀ x‖` with
`κ = δ/√(δ² + 4‖B‖²) > 0`. -/
theorem diagonalBlockBound_mul_le_norm_diagonalPart_apply_reducing {x : H}
    (hx : x ∈ U) :
    diagonalBlockBound (b - a) ‖B‖ * ‖x‖ ≤ ‖U.diagonalPart Z x‖ :=
  diagonalBlockBound_mul_le_norm_diagonalPart_apply_of_tendsto hred hB hZsa hZ2
    hZdom hZcomm hUa hUb (fun n : ℕ => (n : ℝ))
    (fun n => reducingCutoffSeq hA hred n) (fun n => Nat.cast_nonneg n) hab hx
    (tendsto_reducingCutoffSeq hA hred hx)

/-- **The branch-free `tan 2Θ₀` inequality, for any reducing subspace**:
`δ ‖sin 2Θ₀ x‖ ≤ 2 ‖B‖ ‖cos 2Θ₀ x‖` on `U`. -/
theorem gap_mul_norm_offDiagonalPart_apply_le_reducing {x : H} (hx : x ∈ U) :
    (b - a) * ‖U.offDiagonalPart Z x‖ ≤ 2 * ‖B‖ * ‖U.diagonalPart Z x‖ :=
  gap_mul_norm_offDiagonalPart_apply_le_of_tendsto hred hB hZsa hZ2 hZdom hZcomm
    hUa hUb (fun n : ℕ => (n : ℝ)) (fun n => reducingCutoffSeq hA hred n)
    (fun n => Nat.cast_nonneg n) hab hx (tendsto_reducingCutoffSeq hA hred hx)

end Unconditional

end TauCeti
