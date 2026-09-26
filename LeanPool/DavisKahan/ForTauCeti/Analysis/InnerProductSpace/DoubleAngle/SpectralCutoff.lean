/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.DoubleAngle.UnboundedPole
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralMeasure

/-!
# The canonical bounded cutoff, and unconditional pole exclusion

`ForTauCeti/Analysis/InnerProductSpace/DoubleAngle/UnboundedPole.lean` proves
the pole-exclusion bound from a `TauCeti.BoundedCutoff`: an orthogonal
projection inside the trial subspace and inside `D(A)`, invariant under `A`, on
which `A` is bounded.  This module *builds* that data for the only case that
matters, so the pole exclusion carries no cutoff hypothesis at all.

Let `A` be self-adjoint and let `U = specRange hA (Iic c)` be its spectral
subspace below a cut point `c`.  Then

* `U` reduces `A` (`TauCeti.LinearPMap.reducesSubspace_specRange`);
* `1_{[-(|c| + n), c]}(A)` is a bounded cutoff at level `|c| + n`
  (`TauCeti.spectralCutoff`); and
* those cutoffs converge strongly to the identity on `U`
  (`TauCeti.tendsto_spectralCutoff`).

Everything comes from the spectral measure already in
`…LinearPMap/SpectralMeasure.lean`: the cutoff's range lies in `U` because
spectral projections multiply (`proj_inter` at `Icc (-T) c ⊆ Iic c`), it lies in
`D(A)` because the set is bounded, `A` is bounded by `T` on it because the set
lies within `T` of `0`, and it is invariant because spectral projections
intertwine `A`.

## Main results

* `TauCeti.LinearPMap.specProjection_eq_starProjection_specRange`.
* `TauCeti.LinearPMap.reducesSubspace_specRange`.
* `TauCeti.spectralCutoff`, `TauCeti.tendsto_spectralCutoff`.
* `TauCeti.norm_offDiagonalPart_apply_le_specRange` and
  `TauCeti.diagonalBlockBound_mul_le_norm_diagonalPart_apply_specRange`: the
  pole exclusion `‖sin 2Θ₀ x‖ ≤ q⋆ ‖x‖`, `κ ‖x‖ ≤ ‖cos 2Θ₀ x‖`, **with no
  cutoff hypothesis**.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46, Appendix to Section 6: the
  spectral cutoffs `1_{[-τ, α]}(A₀)` and the limiting argument.
-/

@[expose] public section

namespace TauCeti

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

namespace LinearPMap

section SpectralRange

variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (B : Set ℝ)
  (hB : MeasurableSet B)

/-- Spectral projections of nested sets multiply to the inner one. -/
theorem specProjection_mul_specProjection_of_subset {B₁ B₂ : Set ℝ}
    (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂) (h : B₂ ⊆ B₁) :
    specProjection hA B₁ hB₁ * specProjection hA B₂ hB₂ =
      specProjection hA B₂ hB₂ := by
  simp only [specProjection_def]
  rw [(spectralPVM hA).proj_inter B₁ B₂ hB₁ hB₂]
  exact (spectralPVM hA).proj_congr (Set.inter_eq_right.mpr h) _ _

omit hB in
/-- Pointwise form of `specProjection_mul_specProjection_of_subset`. -/
theorem specProjection_apply_specProjection_of_subset {B₁ B₂ : Set ℝ}
    (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂) (h : B₂ ⊆ B₁) (v : H) :
    specProjection hA B₁ hB₁ (specProjection hA B₂ hB₂ v) =
      specProjection hA B₂ hB₂ v := by
  have hmul := congrArg (fun T : H →L[ℂ] H => T v)
    (specProjection_mul_specProjection_of_subset hA hB₁ hB₂ h)
  simpa only [_root_.mul_apply_eq_comp] using hmul

end SpectralRange

end LinearPMap

/-! ### The canonical cutoff family -/

section Cutoff

variable {A : H →ₗ.[ℂ] H}

private theorem Icc_neg_subset_Iic (c T : ℝ) : Set.Icc (-T) c ⊆ Set.Iic c :=
  fun _ hs => (Set.mem_Icc.mp hs).2

private theorem abs_le_of_mem_Icc_neg {c T s : ℝ} (hcT : |c| ≤ T)
    (hs : s ∈ Set.Icc (-T) c) : |s| ≤ T := by
  rw [Set.mem_Icc] at hs
  rw [abs_le]
  exact ⟨hs.1, le_trans hs.2 (le_trans (le_abs_self c) hcT)⟩

/-- **The canonical bounded cutoff.**  For `A` self-adjoint and `U` its spectral
subspace below `c`, the spectral projection of `[-T, c]` is a bounded cutoff at
level `T`, whenever `|c| ≤ T`.

This is the data that `TauCeti.opNorm_offDiagonalPart_comp_le` consumes, and it
is exactly the family `1_{[-τ, α]}(A₀)` of the Appendix to Section 6. -/
noncomputable def spectralCutoff (hA : IsSelfAdjoint A) (c : ℝ) {T : ℝ}
    (hcT : |c| ≤ T) :
    BoundedCutoff A (LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) T where
  toProj := LinearPMap.specProjection hA (Set.Icc (-T) c) measurableSet_Icc
  isSelfAdjoint := LinearPMap.isSelfAdjoint_specProjection hA _ measurableSet_Icc
  isIdempotentElem :=
    LinearPMap.isIdempotentElem_specProjection hA _ measurableSet_Icc
  mem_subspace := fun v => by
    rw [LinearPMap.mem_specRange_iff]
    exact LinearPMap.specProjection_apply_specProjection_of_subset hA
      measurableSet_Iic measurableSet_Icc (Icc_neg_subset_Iic c T) v
  mem_domain := fun v => by
    exact LinearPMap.mem_domain_of_mem_specRange_of_bounded hA _ measurableSet_Icc
      (fun _ hs => abs_le_of_mem_Icc_neg hcT hs)
      (LinearPMap.specProjection_mem_specRange hA _ measurableSet_Icc v)
  norm_apply_le := fun v => by
    have hT : (0 : ℝ) ≤ T := le_trans (abs_nonneg c) hcT
    have h := LinearPMap.norm_sub_smul_le_of_mem_specRange hA _ measurableSet_Icc
      (M := T) (c := 0) (r := T) (fun _ hs => abs_le_of_mem_Icc_neg hcT hs) hT
      (fun _ hs => by simpa using abs_le_of_mem_Icc_neg hcT hs)
      (LinearPMap.specProjection_mem_specRange hA _ measurableSet_Icc v)
      (LinearPMap.mem_domain_of_mem_specRange_of_bounded hA _ measurableSet_Icc
        (fun _ hs => abs_le_of_mem_Icc_neg hcT hs)
        (LinearPMap.specProjection_mem_specRange hA _ measurableSet_Icc v))
    simpa only [Complex.ofReal_zero, zero_smul, sub_zero] using h
  apply_mem_range := fun v => by
    have hidem := LinearPMap.specProjection_apply_specProjection_of_subset hA
      measurableSet_Icc measurableSet_Icc (subset_refl (Set.Icc (-T) c)) v
    have hmem : LinearPMap.specProjection hA (Set.Icc (-T) c) measurableSet_Icc v
        ∈ A.domain :=
      LinearPMap.mem_domain_of_mem_specRange_of_bounded hA _ measurableSet_Icc
        (fun _ hs => abs_le_of_mem_Icc_neg hcT hs)
        (LinearPMap.specProjection_mem_specRange hA _ measurableSet_Icc v)
    have h := LinearPMap.specProjection_apply_domain hA (Set.Icc (-T) c)
      measurableSet_Icc ⟨_, hmem⟩
    have hsub : (⟨LinearPMap.specProjection hA (Set.Icc (-T) c) measurableSet_Icc
          (LinearPMap.specProjection hA (Set.Icc (-T) c) measurableSet_Icc v),
        LinearPMap.specProjection_mem_domain hA _ measurableSet_Icc
          ⟨_, hmem⟩⟩ : A.domain) = ⟨_, hmem⟩ := Subtype.ext hidem
    rw [hsub] at h
    exact h.symm

/-- The underlying projection of the canonical cutoff. -/
theorem spectralCutoff_toProj (hA : IsSelfAdjoint A) (c : ℝ) {T : ℝ}
    (hcT : |c| ≤ T) :
    (spectralCutoff hA c hcT).toProj =
      LinearPMap.specProjection hA (Set.Icc (-T) c) measurableSet_Icc := by
  simp only [spectralCutoff]

/-- The cutoff family indexed by the naturals, at level `|c| + n`. -/
noncomputable def spectralCutoffSeq (hA : IsSelfAdjoint A) (c : ℝ) (n : ℕ) :
    BoundedCutoff A (LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic)
      (|c| + n) :=
  spectralCutoff hA c (le_add_of_nonneg_right (Nat.cast_nonneg n))

/-- The underlying projection of the cutoff family. -/
theorem spectralCutoffSeq_toProj (hA : IsSelfAdjoint A) (c : ℝ) (n : ℕ) :
    (spectralCutoffSeq hA c n).toProj =
      LinearPMap.specProjection hA (Set.Icc (-(|c| + n)) c) measurableSet_Icc := by
  rw [spectralCutoffSeq, spectralCutoff_toProj]

/-- **The cutoffs converge strongly to the identity on the spectral subspace.**
This is the `τ → ∞` input the pole-exclusion endpoint needs, and it is the
Appendix's `Ω_τ → I`. -/
theorem tendsto_spectralCutoff (hA : IsSelfAdjoint A) (c : ℝ) {x : H}
    (hx : x ∈ LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) :
    Filter.Tendsto (fun n : ℕ => (spectralCutoffSeq hA c n).toProj x)
      Filter.atTop (nhds x) := by
  classical
  have hxfix : LinearPMap.specProjection hA (Set.Iic c) measurableSet_Iic x = x :=
    (LinearPMap.mem_specRange_iff hA _ _ x).mp hx
  have hshift : Filter.Tendsto (fun n : ℕ => |c| + (n : ℝ)) Filter.atTop
      Filter.atTop :=
    Filter.tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have hcomp := (LinearPMap.tendsto_specProjection_Icc hA x).comp hshift
  refine hcomp.congr fun n => ?_
  set T : ℝ := |c| + (n : ℝ) with hTdef
  have hcT : c ≤ T := by
    have h1 : c ≤ |c| := le_abs_self c
    have h2 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [hTdef]; linarith
  have hset : Set.Icc (-T) T ∩ Set.Iic c = Set.Icc (-T) c := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic]
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, le_trans h2 hcT⟩, h2⟩
  have hop : LinearPMap.specProjection hA (Set.Icc (-T) c) measurableSet_Icc =
      LinearPMap.specProjection hA (Set.Icc (-T) T) measurableSet_Icc *
        LinearPMap.specProjection hA (Set.Iic c) measurableSet_Iic := by
    simp only [LinearPMap.specProjection_def]
    rw [(LinearPMap.spectralPVM hA).proj_inter _ _ measurableSet_Icc
      measurableSet_Iic]
    exact (LinearPMap.spectralPVM hA).proj_congr hset.symm _ _
  have happ := congrArg (fun P : H →L[ℂ] H => P x) hop
  simp only [_root_.mul_apply_eq_comp] at happ
  rw [spectralCutoffSeq_toProj, ← hTdef, happ, hxfix]
  simp only [Function.comp_apply, ← hTdef]

end Cutoff

/-! ### Unconditional pole exclusion -/

section Unconditional

variable {A : H →ₗ.[ℂ] H} {B Z : H →L[ℂ] H} {a b c : ℝ}

variable (hA : IsSelfAdjoint A)
  (hB : IsOddFor (LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) B)
  (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
  (hZdom : LinearPMap.MapsDomainTo A A Z)
  (hZcomm : ∀ x : A.domain,
    A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
  (hUa : ∀ x : A.domain,
    (x : H) ∈ LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic →
    (⟪A x, (x : H)⟫_ℂ).re ≤ a * ‖(x : H)‖ ^ 2)
  (hUb : ∀ x : A.domain,
    (x : H) ∈ (LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic)ᗮ →
    b * ‖(x : H)‖ ^ 2 ≤ (⟪A x, (x : H)⟫_ℂ).re)
  (hab : a < b)

include hA hB hZsa hZ2 hZdom hZcomm hUa hUb hab

/-- **The cross block is uniformly separated from `1`, with no cutoff
hypothesis.**  `‖sin 2Θ₀ x‖ ≤ (2‖B‖ / √(δ² + 4‖B‖²)) ‖x‖` for `x` in the
spectral subspace, `δ = b - a`. -/
theorem norm_offDiagonalPart_apply_le_specRange {x : H}
    (hx : x ∈ LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) :
    ‖(LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic).offDiagonalPart Z x‖ ≤
      crossBlockBound (b - a) ‖B‖ * ‖x‖ :=
  norm_offDiagonalPart_apply_le_of_tendsto
    (LinearPMap.reducesSubspace_specRange hA (Set.Iic c) measurableSet_Iic) hB
    hZsa hZ2 hZdom hZcomm hUa hUb (fun n : ℕ => |c| + n)
    (fun n => spectralCutoffSeq hA c n) (fun n => by positivity) hab
    (tendsto_spectralCutoff hA c hx)

/-- **Pole exclusion for a self-adjoint operator, unconditional.**

For `A` self-adjoint with spectral subspace `U = 1_{(-∞, c]}(A)`, quadratic form
at most `a` on `U` and at least `b` on `Uᗮ`, and `B` bounded and fully
off-diagonal,

`κ ‖x‖ ≤ ‖cos 2Θ₀ x‖`   for `x ∈ U`,   `κ = δ / √(δ² + 4‖B‖²) > 0`,
`δ = b - a`.

**No cutoff data is assumed**: the family `1_{[-(|c| + n), c]}(A)` is supplied by
`TauCeti.spectralCutoff`.  So the denominator of `tan 2Θ₀` is bounded below by an
explicit positive constant, and the pole is excluded as a theorem before the
tangent is defined. -/
theorem diagonalBlockBound_mul_le_norm_diagonalPart_apply_specRange {x : H}
    (hx : x ∈ LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) :
    diagonalBlockBound (b - a) ‖B‖ * ‖x‖ ≤
      ‖(LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic).diagonalPart Z x‖ :=
  diagonalBlockBound_mul_le_norm_diagonalPart_apply_of_tendsto
    (LinearPMap.reducesSubspace_specRange hA (Set.Iic c) measurableSet_Iic) hB
    hZsa hZ2 hZdom hZcomm hUa hUb (fun n : ℕ => |c| + n)
    (fun n => spectralCutoffSeq hA c n) (fun n => by positivity) hab hx
    (tendsto_spectralCutoff hA c hx)

/-- **The branch-free `tan 2Θ₀` inequality at the operator norm, for a
self-adjoint operator, with no cutoff hypothesis.**

`δ ‖sin 2Θ₀ x‖ ≤ 2 ‖B‖ ‖cos 2Θ₀ x‖` on the spectral subspace, `δ = b - a`.
Together with `diagonalBlockBound_mul_le_norm_diagonalPart_apply_specRange`,
whose right-hand side is bounded below by `κ ‖x‖ > 0`, this is
`δ |tan 2θ| ≤ 2 ‖B‖` with the **residual** `B` on the right and the sharp
constant `2`. -/
theorem gap_mul_norm_offDiagonalPart_apply_le_specRange {x : H}
    (hx : x ∈ LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) :
    (b - a) *
        ‖(LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic).offDiagonalPart Z x‖ ≤
      2 * ‖B‖ *
        ‖(LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic).diagonalPart Z x‖ :=
  gap_mul_norm_offDiagonalPart_apply_le_of_tendsto
    (LinearPMap.reducesSubspace_specRange hA (Set.Iic c) measurableSet_Iic) hB
    hZsa hZ2 hZdom hZcomm hUa hUb (fun n : ℕ => |c| + n)
    (fun n => spectralCutoffSeq hA c n) (fun n => by positivity) hab hx
    (tendsto_spectralCutoff hA c hx)

end Unconditional

end TauCeti
