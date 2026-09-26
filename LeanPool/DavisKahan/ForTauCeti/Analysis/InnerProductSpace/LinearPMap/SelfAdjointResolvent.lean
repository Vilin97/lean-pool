/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Shift
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary

/-!
# A self-adjoint operator has real spectrum

The basic criterion: for a self-adjoint `A : E →ₗ.[ℂ] E` and `z` off the real
axis, `A - z` has a bounded two-sided inverse, with `‖(A - z)⁻¹‖ ≤ |Im z|⁻¹`.
Hence `spectrum A ⊆ ℝ`.

The argument is the classical one, in three steps:

1. **the estimate** `‖(A - z) x‖ ≥ |Im z| ‖x‖` — because `⟪A x, x⟫` is real, the
   cross term in `‖(A - Re z) x - i (Im z) x‖²` is purely imaginary and drops
   out, leaving `‖(A - Re z)x‖² + (Im z)² ‖x‖²`;
2. **closed range** — the estimate plus closedness of `A` (self-adjoint
   operators are closed) makes the range of `A - z` closed;
3. **dense range** — a vector orthogonal to the range is an eigenvector of `A`
   for the eigenvalue `conj z`, and self-adjointness forces its eigenvalues to
   be real, so it vanishes.

## Provenance

* **Extraction class:** *new*.  Statement and proof are ours.
* **Spectra influence:** Spectra proves the same criterion
  (`Spectra.YosidaHille.isSelfAdjoint_to_surjective`,
  `Spectra.Resolvent.mem_resolventSet_of_im_ne_zero`) and that is what told us
  the criterion was needed here; per
  the completed Tau Ceti adaptation, theorem
  selection is attributable even when the proof is independent.  The proof below
  was written against Mathlib's `LinearPMap` adjoint API and shares no lemma with
  Spectra's, which routes through the Cayley transform and Yosida--Hille.
-/

@[expose] public section

namespace TauCeti
namespace LinearPMap

open scoped InnerProductSpace ComplexConjugate ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

section Estimate
-- The estimate needs no completeness; `Star` on `LinearPMap` does, so the
-- self-adjointness results below open their own section.

/-- **The exact norm identity.**  `‖(A - z)x‖² = ‖(A - Re z)x‖² + (Im z)²‖x‖²`.

The cross term vanishes because `⟪A x - (Re z) x, x⟫` is real while the vector
subtracted from it is `i (Im z) x`. -/
theorem norm_sub_smul_sq {A : E →ₗ.[ℂ] E} (hsym : A.IsFormalAdjoint A)
    (z : ℂ) (x : A.domain) :
    ‖A x - z • (x : E)‖ ^ 2
      = ‖A x - (z.re : ℂ) • (x : E)‖ ^ 2 + (z.im) ^ 2 * ‖(x : E)‖ ^ 2 := by
  set u : E := A x - (z.re : ℂ) • (x : E) with hu
  have hsplit : A x - z • (x : E) = u - ((z.im : ℂ) * Complex.I) • (x : E) := by
    rw [hu]
    have : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := (Complex.re_add_im z).symm
    rw [show z • (x : E) = ((z.re : ℂ) + (z.im : ℂ) * Complex.I) • (x : E) by rw [← this]]
    rw [add_smul]
    abel
  -- `⟪u, x⟫` is real
  have hreal : (starRingEnd ℂ) ⟪u, (x : E)⟫_ℂ = ⟪u, (x : E)⟫_ℂ := by
    rw [hu, inner_sub_left, inner_smul_left, map_sub, map_mul]
    rw [inner_apply_self_isReal hsym x]
    simp [Complex.conj_ofReal]
  -- the cross term is purely imaginary
  have hcross : RCLike.re ⟪u, (((z.im : ℂ) * Complex.I) • (x : E))⟫_ℂ = 0 := by
    have hr : (⟪u, (x : E)⟫_ℂ).im = 0 := Complex.conj_eq_iff_im.mp hreal
    rw [inner_smul_right]
    simp [hr]
  rw [hsplit, @norm_sub_sq ℂ, hcross, norm_smul]
  simp [Complex.norm_I, Complex.norm_real, mul_pow, sq_abs]

/-- **The basic estimate.**  `‖(A - z) x‖ ≥ |Im z| ‖x‖` for symmetric `A`. -/
theorem norm_sub_smul_ge_abs_im {A : E →ₗ.[ℂ] E} (hsym : A.IsFormalAdjoint A)
    (z : ℂ) (x : A.domain) :
    |z.im| * ‖(x : E)‖ ≤ ‖A x - z • (x : E)‖ := by
  have hsq := norm_sub_smul_sq hsym z x
  nlinarith [norm_nonneg (A x - z • (x : E)), norm_nonneg (A x - (z.re : ℂ) • (x : E)),
    norm_nonneg ((x : E)), abs_nonneg z.im, sq_abs z.im,
    sq_nonneg ‖A x - (z.re : ℂ) • (x : E)‖, hsq,
    mul_nonneg (abs_nonneg z.im) (norm_nonneg ((x : E)))]

end Estimate

section SelfAdjoint

variable [CompleteSpace E]

/-- **Dense range.**  A vector orthogonal to the range of `A - z` would make
`z ⟪y, y⟫` real; since `⟪y, y⟫` is a nonnegative real, a non-real `z` forces
`y = 0`.

This is the usual "a self-adjoint operator has no non-real eigenvalue" argument,
arranged so that it never has to name the eigenvector equation — only the
quadratic form appears, which avoids transporting `A† = A` under a dependent
domain membership. -/
theorem eq_zero_of_orthogonal_shiftRange {A : E →ₗ.[ℂ] E}
    (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0) {y : E}
    (hy : ∀ x : A.domain, ⟪y, A x - z • (x : E)⟫_ℂ = 0) : y = 0 := by
  have hdense : Dense (A.domain : Set E) := hA.dense_domain
  -- `⟪conj z • y, x⟫ = ⟪y, A x⟫`, which puts `y` in the adjoint's domain
  have hEq : ∀ x : A.domain, ⟪(starRingEnd ℂ) z • y, (x : E)⟫_ℂ = ⟪y, A x⟫_ℂ :=
    inner_conj_smul_eq_of_orthogonal_shiftRange hy
  have hmem : y ∈ (_root_.LinearPMap.adjoint A).domain :=
    _root_.LinearPMap.mem_adjoint_domain_of_exists _ ⟨(starRingEnd ℂ) z • y, hEq⟩
  have hmemA : y ∈ A.domain := by
    rwa [_root_.LinearPMap.isSelfAdjoint_def.mp hA] at hmem
  have hsym : A.IsFormalAdjoint A := by
    have h := _root_.LinearPMap.adjoint_isFormalAdjoint (T := A) hdense
    rwa [_root_.LinearPMap.isSelfAdjoint_def.mp hA] at h
  -- `⟪y, A y⟫` is real, and equals `z * ⟪y, y⟫`
  have hkey : (starRingEnd ℂ) ⟪y, A ⟨y, hmemA⟩⟫_ℂ = ⟪y, A ⟨y, hmemA⟩⟫_ℂ := by
    rw [inner_conj_symm]
    exact hsym ⟨y, hmemA⟩ ⟨y, hmemA⟩
  have hzy : z * ⟪y, y⟫_ℂ = ⟪y, A ⟨y, hmemA⟩⟫_ℂ := by
    have h := hEq ⟨y, hmemA⟩
    rwa [inner_smul_left, starRingEnd_self_apply] at h
  rw [← hzy, map_mul, inner_self_conj] at hkey
  -- `conj z * ⟪y,y⟫ = z * ⟪y,y⟫`
  by_contra hy0
  have hnz : ⟪y, y⟫_ℂ ≠ 0 := by
    simpa [inner_self_eq_zero] using hy0
  have : (starRingEnd ℂ) z = z := mul_right_cancel₀ hnz hkey
  exact hz (Complex.conj_eq_iff_im.mp this)

/-- **Closed range.**  The estimate turns a convergent sequence in the range into
a Cauchy sequence of preimages; closedness of `A` (which self-adjointness
supplies) identifies the limit. -/
theorem isClosed_range_shiftMap {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A)
    {z : ℂ} (hz : z.im ≠ 0) :
    IsClosed (Set.range (shiftMap A z)) := by
  have hsym : A.IsFormalAdjoint A := by
    have h := _root_.LinearPMap.adjoint_isFormalAdjoint (T := A) hA.dense_domain
    rwa [_root_.LinearPMap.isSelfAdjoint_def.mp hA] at h
  exact isClosed_range_shiftMap_of_lower_bound hA (abs_pos.mpr hz)
    (norm_sub_smul_ge_abs_im hsym z)

omit [CompleteSpace E] in
/-- The shifted map `A - z` is injective for non-real `z`: the imaginary part of the quadratic form
bounds it below. -/
theorem injective_shiftMap {A : E →ₗ.[ℂ] E} (hsym : A.IsFormalAdjoint A)
    {z : ℂ} (hz : z.im ≠ 0) : Function.Injective (shiftMap A z) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  have h := norm_sub_smul_ge_abs_im hsym z x
  rw [show A x - z • (x : E) = shiftMap A z x from rfl, hx, norm_zero] at h
  have hxz : ‖(x : E)‖ = 0 := by
    nlinarith [abs_pos.mpr hz, norm_nonneg ((x : E))]
  exact Subtype.ext (by simpa using hxz)

/-- The shifted map is surjective.  This is the harder half -- it needs closed range, which comes
from the same lower bound plus closedness of `A`. -/
theorem surjective_shiftMap {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A)
    {z : ℂ} (hz : z.im ≠ 0) : Function.Surjective (shiftMap A z) := by
  have hclosed := isClosed_range_shiftMap hA hz
  set K : Submodule ℂ E := LinearMap.range (shiftMap A z) with hK
  have hKclosed : IsClosed (K : Set E) := hclosed
  have : K.HasOrthogonalProjection :=
    haveI : CompleteSpace K := hKclosed.completeSpace_coe
    inferInstance
  have hperp : Kᗮ = ⊥ :=
    orthogonal_range_shiftMap_eq_bot fun _ hy => eq_zero_of_orthogonal_shiftRange hA hz hy
  have hKtop : K = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hperp
  intro y
  have : y ∈ K := hKtop ▸ Submodule.mem_top
  exact this

/-- **A self-adjoint operator has real spectrum**, quantitatively: every `z` off
the real axis lies in the resolvent set. -/
theorem mem_resolventSet_of_im_ne_zero {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A)
    {z : ℂ} (hz : z.im ≠ 0) : z ∈ resolventSet A := by
  have hsym : A.IsFormalAdjoint A := by
    have h := _root_.LinearPMap.adjoint_isFormalAdjoint (T := A) hA.dense_domain
    rwa [_root_.LinearPMap.isSelfAdjoint_def.mp hA] at h
  have habs : 0 < |z.im| := abs_pos.mpr hz
  -- The canonical resolvent inverts `z • I - A`, which is `-(shiftMap A z)`; negating a
  -- bijection is a bijection, so the equivalence is the one built from `shiftMap` composed
  -- with negation.
  set sm : A.domain →ₗ[ℂ] E := -(shiftMap A z) with hsm
  have hsmapp : ∀ x : A.domain, sm x = z • (x : E) - A x := by
    intro x
    rw [hsm]
    simp only [LinearMap.neg_apply, shiftMap_apply]
    module
  have hbij : Function.Bijective sm := by
    constructor
    · intro a b hab
      exact injective_shiftMap hsym hz (neg_injective (by simpa [hsm] using hab))
    · intro y
      obtain ⟨x, hx⟩ := surjective_shiftMap hA hz (-y)
      exact ⟨x, by rw [hsm]; simp [hx]⟩
  let e : A.domain ≃ₗ[ℂ] E := LinearEquiv.ofBijective sm hbij
  have hesymm : ∀ y : E, sm (e.symm y) = y := fun y => e.apply_symm_apply y
  set Rlin : E →ₗ[ℂ] E := A.domain.subtype ∘ₗ (e.symm : E →ₗ[ℂ] A.domain) with hRlin
  have hbound : ∀ y : E, ‖Rlin y‖ ≤ |z.im|⁻¹ * ‖y‖ := by
    intro y
    have h := norm_sub_smul_ge_abs_im hsym z (e.symm y)
    have hy : A (e.symm y) - z • ((e.symm y : A.domain) : E) = -y := by
      have h0 := hesymm y
      rw [hsmapp] at h0
      linear_combination (norm := module) -h0
    rw [hy, norm_neg] at h
    have hRn : ‖Rlin y‖ = ‖((e.symm y : A.domain) : E)‖ := (rfl)
    rw [hRn]
    rw [inv_mul_eq_div, le_div_iff₀ habs, mul_comm]
    exact h
  refine mem_resolventSet_iff.mpr
    ⟨Rlin.mkContinuous (|z.im|⁻¹) hbound, fun φ => (e.symm φ).2, fun φ => ?_, fun ψ => ?_⟩
  · -- right inverse: `(z • I - A) (R φ) = φ`, which is `sm (e.symm φ) = φ`
    have h := hesymm φ
    rw [hsmapp] at h
    exact h
  · -- left inverse on the domain: `R ((z • I - A) ψ) = ψ`
    have hinv : e.symm (sm ψ) = ψ := e.symm_apply_apply ψ
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change ((e.symm (z • (ψ : E) - A ψ) : A.domain) : E) = (ψ : E)
    rw [show z • (ψ : E) - A ψ = sm ψ from (hsmapp ψ).symm, hinv]

/-- **The spectrum of a self-adjoint operator is real.** -/
theorem spectrum_subset_real {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) :
    spectrum A ⊆ Complex.ofReal '' Set.univ := by
  intro z hz
  have him : z.im = 0 := by
    by_contra him
    exact (mem_spectrum_iff.mp hz) (mem_resolventSet_of_im_ne_zero hA him)
  exact ⟨z.re, Set.mem_univ _, by simp [Complex.ext_iff, him]⟩

/-- The resolvent of a self-adjoint operator at a non-real point is bounded by
the reciprocal distance to the real axis. -/
theorem norm_resolvent_le_of_im_ne_zero {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A)
    {z : ℂ} (hz : z.im ≠ 0) :
    ‖resolvent A z‖ ≤ |z.im|⁻¹ := by
  have hsym : A.IsFormalAdjoint A := by
    have h := _root_.LinearPMap.adjoint_isFormalAdjoint (T := A) hA.dense_domain
    rwa [_root_.LinearPMap.isSelfAdjoint_def.mp hA] at h
  have habs : 0 < |z.im| := abs_pos.mpr hz
  set hmem := mem_resolventSet_of_im_ne_zero hA hz
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  have hdom : resolvent A z y ∈ A.domain := resolvent_mem_domain hmem y
  have hsolve : z • resolvent A z y - A ⟨resolvent A z y, hdom⟩ = y :=
    smul_sub_apply_resolvent hmem y
  have h := norm_sub_smul_ge_abs_im hsym z ⟨resolvent A z y, hdom⟩
  have hflip : A (⟨resolvent A z y, hdom⟩ : A.domain)
      - z • ((⟨resolvent A z y, hdom⟩ : A.domain) : E) = -y := by
    linear_combination (norm := module) -hsolve
  rw [hflip, norm_neg] at h
  rw [inv_mul_eq_div, le_div_iff₀ habs, mul_comm]
  exact h

/-- The resolvent of a self-adjoint operator at a **real** point is a
self-adjoint bounded operator. -/
theorem isSelfAdjoint_resolvent_ofReal {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A)
    {c : ℝ} (hc : (c : ℂ) ∈ resolventSet A) :
    _root_.IsSelfAdjoint (resolvent A (c : ℂ)) := by
  have hsym : A.IsFormalAdjoint A := by
    have h := _root_.LinearPMap.adjoint_isFormalAdjoint (T := A) hA.dense_domain
    rwa [_root_.LinearPMap.isSelfAdjoint_def.mp hA] at h
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  -- write both arguments as `(c • I - A)` of a domain point and use symmetry
  set px : A.domain := ⟨resolvent A (c : ℂ) x, resolvent_mem_domain hc x⟩ with hpx
  set py : A.domain := ⟨resolvent A (c : ℂ) y, resolvent_mem_domain hc y⟩ with hpy
  have hx : (c : ℂ) • (px : E) - A px = x := smul_sub_apply_resolvent hc x
  have hy : (c : ℂ) • (py : E) - A py = y := smul_sub_apply_resolvent hc y
  have hstep : ⟪(px : E), (c : ℂ) • (py : E) - A py⟫_ℂ
      = ⟪(c : ℂ) • (px : E) - A px, (py : E)⟫_ℂ := by
    rw [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal, hsym px py]
  calc ⟪resolvent A (c : ℂ) x, y⟫_ℂ
      = ⟪(px : E), (c : ℂ) • (py : E) - A py⟫_ℂ := by rw [hy]
    _ = ⟪(c : ℂ) • (px : E) - A px, (py : E)⟫_ℂ := hstep
    _ = ⟪x, resolvent A (c : ℂ) y⟫_ℂ := by rw [hx]

/-- **The adjoint of the resolvent is the resolvent at the conjugate point:**
`R(z)⋆ = R(conj(z))`.

Both sides are pinned by the two-sided inverse property: writing `u = R(z) x` and
`v = R(conj(z)) y`, symmetry of `A` turns `⟪u, (z • I - A) v⟫` into `⟪(conj(z) • I - A) u, v⟫`. -/
theorem adjoint_resolvent {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z ∈ resolventSet A) (hzc : (starRingEnd ℂ) z ∈ resolventSet A) :
    ContinuousLinearMap.adjoint (resolvent A z) = resolvent A ((starRingEnd ℂ) z) := by
  have hsym : A.IsFormalAdjoint A := by
    have h := _root_.LinearPMap.adjoint_isFormalAdjoint (T := A) hA.dense_domain
    rwa [_root_.LinearPMap.isSelfAdjoint_def.mp hA] at h
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  set u : A.domain := ⟨resolvent A ((starRingEnd ℂ) z) x, resolvent_mem_domain hzc x⟩ with hu
  set v : A.domain := ⟨resolvent A z y, resolvent_mem_domain hz y⟩ with hv
  have hux : (starRingEnd ℂ) z • (u : E) - A u = x := smul_sub_apply_resolvent hzc x
  have hvy : z • (v : E) - A v = y := smul_sub_apply_resolvent hz y
  calc ⟪resolvent A ((starRingEnd ℂ) z) x, y⟫_ℂ
      = ⟪(u : E), z • (v : E) - A v⟫_ℂ := by rw [hvy]
    _ = ⟪(starRingEnd ℂ) z • (u : E) - A u, (v : E)⟫_ℂ := by
        rw [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
          starRingEnd_self_apply, hsym u v]
    _ = ⟪x, resolvent A z y⟫_ℂ := by rw [hux]

/-- **The Davis--Kahan gap-resolvent bound.**  If the spectrum of a self-adjoint
`A` avoids the open interval `(c - s, c + s)` then `c • I - A` has a bounded
two-sided inverse of norm at most `s⁻¹`.

The inverse exhibited is the canonical resolvent `resolvent A c`, which inverts
`c • I - A`; the norm bound is insensitive to that choice of sign.

The proof is a C⋆-algebra argument about the *bounded* operator `R`: spectral
mapping puts `spectrum R \ {0}` inside `(c - ·)⁻¹ '' spectrum A`, the gap bounds
that by `s⁻¹`, and for a self-adjoint element the norm *is* the spectral radius.
No projection-valued measure and no functional calculus appear. -/
theorem exists_norm_le_two_sided_shifted_inverse_of_spectrum_gap
    {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) {c s : ℝ} (hs : 0 < s)
    (hgap : ∀ lam ∈ Set.Ioo (c - s) (c + s), (lam : ℂ) ∉ spectrum A) :
    ∃ R : E →L[ℂ] E, ‖R‖ ≤ s⁻¹ ∧
      (∀ ψ : A.domain, R ((c : ℂ) • (ψ : E) - A ψ) = (ψ : E)) ∧
      ∀ φ : E, ∃ hmem : R φ ∈ A.domain,
        (c : ℂ) • R φ - A ⟨R φ, hmem⟩ = φ := by
  have hcmem : c ∈ Set.Ioo (c - s) (c + s) := ⟨by linarith, by linarith⟩
  have hc : (c : ℂ) ∈ resolventSet A := notMem_spectrum_iff.mp (hgap c hcmem)
  refine ⟨resolvent A (c : ℂ), ?_, fun ψ => resolvent_smul_sub_apply hc ψ, fun φ =>
    ⟨resolvent_mem_domain hc φ, smul_sub_apply_resolvent hc φ⟩⟩
  -- every spectral point of the bounded resolvent has modulus at most `s⁻¹`
  have hspec : ∀ μ ∈ _root_.spectrum ℂ (resolvent A (c : ℂ)), ‖μ‖ ≤ s⁻¹ := by
    intro μ hμ
    rcases eq_or_ne μ 0 with rfl | hμ0
    · simpa using (by positivity : (0:ℝ) ≤ s⁻¹)
    · -- `c + μ⁻¹` is a spectral point of `A`, hence real and outside the gap
      have hnot : (c : ℂ) - μ⁻¹ ∉ resolventSet A := fun hmem =>
        notMem_spectrum_resolvent hc hμ0 hmem hμ
      obtain ⟨r, -, hr⟩ := spectrum_subset_real hA (mem_spectrum_iff.mpr hnot)
      have hrspec : (r : ℂ) ∈ spectrum A := by rw [hr]; exact mem_spectrum_iff.mpr hnot
      have hrgap : r ∉ Set.Ioo (c - s) (c + s) := fun hmem => hgap r hmem hrspec
      have hge : s ≤ |c - r| := by
        rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hrgap
        rcases hrgap with h | h
        · rw [abs_of_nonneg (by linarith)]; linarith
        · rw [abs_of_nonpos (by linarith)]; linarith
      have hinvnorm : ‖μ‖⁻¹ = |c - r| := by
        rw [← norm_inv, show μ⁻¹ = (c : ℂ) - (r : ℂ) by rw [hr]; ring,
          ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have hpos : 0 < ‖μ‖ := norm_pos_iff.mpr hμ0
      have hsle : s ≤ ‖μ‖⁻¹ := hinvnorm ▸ hge
      have hcancel : ‖μ‖⁻¹ * ‖μ‖ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
      rw [show s⁻¹ = 1 / s by ring, le_div_iff₀ hs]
      nlinarith [hsle, hpos, hcancel]
  -- for a self-adjoint element the norm *is* the spectral radius
  have hsa : _root_.IsSelfAdjoint (resolvent A (c : ℂ)) := isSelfAdjoint_resolvent_ofReal hA hc
  have hrad : spectralRadius ℂ (resolvent A (c : ℂ)) ≤ ENNReal.ofReal s⁻¹ := by
    rw [spectralRadius_eq_of_unital]
    refine iSup₂_le fun μ hμ => ?_
    calc (‖μ‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖μ‖ := by
          rw [← ENNReal.ofReal_coe_nnreal]; norm_cast
      _ ≤ ENNReal.ofReal s⁻¹ := ENNReal.ofReal_le_ofReal (hspec μ hμ)
  calc ‖resolvent A (c : ℂ)‖
      = (spectralRadius ℂ (resolvent A (c : ℂ))).toReal :=
        hsa.toReal_spectralRadius_complex_eq_norm.symm
    _ ≤ s⁻¹ := ENNReal.toReal_le_of_le_ofReal (by positivity) hrad

/-! ### The Cayley transform

`U = (A - i)(A + i)⁻¹`, written as `1 - 2i·R(-i)` so that boundedness is manifest
and no domain bookkeeping is needed.  It is the bridge from the unbounded
self-adjoint `A` to a *bounded unitary*, where Mathlib's continuous functional
calculus applies. -/

/-- `-i` is a resolvent point of a self-adjoint operator. -/
theorem negI_mem_resolventSet {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) :
    (-Complex.I) ∈ resolventSet A :=
  mem_resolventSet_of_im_ne_zero hA (by simp)

/-- `i` is a resolvent point of a self-adjoint operator. -/
theorem I_mem_resolventSet {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) :
    Complex.I ∈ resolventSet A :=
  mem_resolventSet_of_im_ne_zero hA (by simp)

/-- **The Cayley transform** `(A - i)(A + i)⁻¹`, in the manifestly bounded form
`1 + 2i·R(-i)`.

The canonical resolvent inverts `-i • I - A`, so `(A + i)⁻¹ = -R(-i)` and the
`-2i` of the `(A - z)` convention becomes `+2i` here. -/
@[expose]
noncomputable def cayley {A : E →ₗ.[ℂ] E} (_hA : IsSelfAdjoint A) : E →L[ℂ] E :=
  1 + (2 * Complex.I) • resolvent A (-Complex.I)

/-- Rewrite form of `cayley`, so call sites need not unfold the definition.

Added 2026-07-30: `SpectralMeasure/Construction` was doing `simp [cayley]`, which needs
the body exposed. Tau Ceti's `api-design` rubric asks for the lemma instead. -/
theorem cayley_def {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) :
    cayley hA = 1 + (2 * Complex.I) • resolvent A (-Complex.I) := (rfl)

/-- On a vector, `U ξ = (i • I - A) R(-i) ξ`, i.e. `(A - i)` applied to the
preimage of `ξ` under `A + i`, that preimage being `-R(-i) ξ`.

Deliberately **not** `@[simp]`: it rewrites the Cayley
transform into a resolvent expression, which is not a normal form — downstream proofs
work with `cayley` folded and unfold it by name where they mean to. -/
theorem cayley_apply {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) (ξ : E) :
    cayley hA ξ
      = Complex.I • resolvent A (-Complex.I) ξ
        - A ⟨resolvent A (-Complex.I) ξ,
            resolvent_mem_domain (negI_mem_resolventSet hA) ξ⟩ := by
  set h := negI_mem_resolventSet hA with hh
  set x := resolvent A (-Complex.I) ξ with hx
  have hmem : x ∈ A.domain := resolvent_mem_domain h ξ
  have hsolve : (-Complex.I) • x - A ⟨x, hmem⟩ = ξ := smul_sub_apply_resolvent h ξ
  have hAx : A ⟨x, hmem⟩ = -(Complex.I • x) - ξ := by
    rw [← hsolve]; module
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change ξ + (2 * Complex.I) • x = Complex.I • x - A ⟨x, hmem⟩
  rw [hAx]
  module

/-- **The Cayley transform is isometric.**  Both `‖(A - i)x‖²` and `‖(A + i)x‖²`
equal `‖Ax‖² + ‖x‖²`, by the exact norm identity. -/
@[simp]
theorem norm_cayley_apply {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) (ξ : E) :
    ‖cayley hA ξ‖ = ‖ξ‖ := by
  have hsym : A.IsFormalAdjoint A := by
    have h := _root_.LinearPMap.adjoint_isFormalAdjoint (T := A) hA.dense_domain
    rwa [_root_.LinearPMap.isSelfAdjoint_def.mp hA] at h
  set h := negI_mem_resolventSet hA with hh
  set x := resolvent A (-Complex.I) ξ with hx
  have hmem : x ∈ A.domain := resolvent_mem_domain h ξ
  have hsolve : (-Complex.I) • x - A ⟨x, hmem⟩ = ξ := smul_sub_apply_resolvent h ξ
  -- both shifts have the same norm, by the exact identity at `z = ±i`
  have hplus := norm_sub_smul_sq hsym (-Complex.I) ⟨x, hmem⟩
  have hminus := norm_sub_smul_sq hsym Complex.I ⟨x, hmem⟩
  simp only [Complex.neg_re, Complex.I_re, neg_zero, Complex.neg_im, Complex.I_im,
    Complex.ofReal_zero, zero_smul, sub_zero, neg_one_sq, one_pow, one_mul] at hplus hminus
  have hsq : ‖cayley hA ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
    -- do not rewrite `ξ` in the goal: it occurs inside `x = R(-i) ξ`
    have hxi : ‖ξ‖ ^ 2 = ‖A ⟨x, hmem⟩ - (-Complex.I) • x‖ ^ 2 := by
      rw [← hsolve, norm_sub_rev]
    rw [cayley_apply hA ξ, norm_sub_rev, hxi, hminus, hplus]
  have h2 := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h2

/-- The Cayley transform preserves inner products (polarisation of isometry). -/
theorem inner_cayley {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) (ξ η : E) :
    ⟪cayley hA ξ, cayley hA η⟫_ℂ = ⟪ξ, η⟫_ℂ := by
  let L : E →ₗᵢ[ℂ] E :=
    { toLinearMap := (cayley hA : E →ₗ[ℂ] E)
      norm_map' := norm_cayley_apply hA }
  exact L.inner_map_map ξ η

/-- **The Cayley transform is surjective.**  Given `η`, solve `(i • I - A) y = η` —
possible because `i` is a resolvent point — and take `ξ = (-i • I - A) y`, which is
`-(A + i) y`. -/
theorem surjective_cayley {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) :
    Function.Surjective (cayley hA) := by
  intro η
  set hi := I_mem_resolventSet hA with hhi
  set hni := negI_mem_resolventSet hA with hhni
  set y : E := resolvent A Complex.I η with hy
  have hymem : y ∈ A.domain := resolvent_mem_domain hi η
  have hsolve : Complex.I • y - A ⟨y, hymem⟩ = η := smul_sub_apply_resolvent hi η
  -- `ξ := (-i • I - A) y`
  refine ⟨(-Complex.I) • y - A ⟨y, hymem⟩, ?_⟩
  -- `R(-i)` inverts `-i • I - A` on the domain
  have hR : resolvent A (-Complex.I) ((-Complex.I) • y - A ⟨y, hymem⟩) = y :=
    resolvent_smul_sub_apply hni ⟨y, hymem⟩
  rw [cayley_apply hA]
  -- both the operator application and the shift collapse via `hR`
  have hdom : (⟨resolvent A (-Complex.I) ((-Complex.I) • y - A ⟨y, hymem⟩),
      resolvent_mem_domain hni _⟩ : A.domain) = ⟨y, hymem⟩ := Subtype.ext hR
  rw [hdom, hR]
  exact hsolve

/-- **The Cayley transform of a self-adjoint operator is unitary.** -/
theorem cayley_mem_unitary {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) :
    cayley hA ∈ unitary (E →L[ℂ] E) := by
  have hstar : ContinuousLinearMap.adjoint (cayley hA) * cayley hA = 1 := by
    refine ContinuousLinearMap.ext fun ξ => ?_
    refine ext_inner_right ℂ fun η => ?_
    calc ⟪(ContinuousLinearMap.adjoint (cayley hA) * cayley hA) ξ, η⟫_ℂ
        = ⟪cayley hA ξ, cayley hA η⟫_ℂ := by
          rw [show (ContinuousLinearMap.adjoint (cayley hA) * cayley hA) ξ
              = ContinuousLinearMap.adjoint (cayley hA) (cayley hA ξ) from rfl,
            ContinuousLinearMap.adjoint_inner_left]
      _ = ⟪ξ, η⟫_ℂ := inner_cayley hA ξ η
      _ = ⟪(1 : E →L[ℂ] E) ξ, η⟫_ℂ := (rfl)
  have hmul : cayley hA * ContinuousLinearMap.adjoint (cayley hA) = 1 := by
    refine ContinuousLinearMap.ext fun ξ => ?_
    obtain ⟨ζ, rfl⟩ := surjective_cayley hA ξ
    have : ContinuousLinearMap.adjoint (cayley hA) (cayley hA ζ) = ζ := by
      have := congrArg (fun T : E →L[ℂ] E => T ζ) hstar
      simpa using this
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change cayley hA (ContinuousLinearMap.adjoint (cayley hA) (cayley hA ζ)) = _
    rw [this]
    rfl
  rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint]
  exact ⟨hstar, hmul⟩

/-- The Cayley transform is star-normal, so Mathlib's continuous functional
calculus applies to it. -/
instance isStarNormal_cayley {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A) :
    IsStarNormal (cayley hA) :=
  isStarNormal_of_mem_unitary (cayley_mem_unitary hA)

end SelfAdjoint

end LinearPMap
end TauCeti
