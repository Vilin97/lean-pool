/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralVectorBounds
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.ProjValMeasure.Additivity

/-!
# Rayleigh--Ritz: a trial subspace certifies a spectral gap

An unbounded self-adjoint operator `A`, a finite-dimensional trial subspace `K`
inside its domain, and two form bounds — the Ritz bound `⟪A u, u⟫ ≤ α‖u‖²` on
`K`, and coercivity `β‖u‖² ≤ ⟪A u, u⟫` on `Kᗮ` — force `A` to have no spectrum
in `(α, β)`.

This is the classical min--max/Rayleigh--Ritz counting argument, stated so that
it never mentions a rank: the Ritz bound puts at least `dim K` dimensions of
spectral mass at or below `α`, coercivity puts at most `dim K` dimensions below
`β`, and a vector of spectral mass strictly inside `(α, β)` would make one
dimension too many.  The `dim K + 1` witnesses are exhibited as an explicit
subspace and the pigeonhole is rank--nullity of the compression to `K`.

## The strictness that makes the counting work

The counting needs the *strict* vector-local form bounds:

* `lt_re_inner_of_specProjection_Iic_apply_eq_zero` — a nonzero vector with no
  spectral mass in `(-∞, c]` has form strictly above `c‖x‖²`;
* `re_inner_lt_of_specProjection_Ici_apply_eq_zero` — dually.

Without them the argument stalls at equality rather than a contradiction, which
is exactly what happens for a trial vector realising the top Ritz value: the
Ritz bound is attained, so the non-strict bound gives no information.  The
strict versions are not an epsilon-refinement of the non-strict ones; they need
the diagonal measure, split at a level `d > c` chosen where the mass actually
sits, and the energy split across that level.

## Sources

*Follows nothing in particular*: Rayleigh--Ritz and min--max for unbounded
self-adjoint operators, in the form-bound shape a trial subspace supplies, with
the conclusion stated as the vanishing of a spectral projection rather than as
an eigenvalue inequality (there need be no eigenvalues).

## Provenance

*New.*
-/

public section

open scoped InnerProductSpace ENNReal
open MeasureTheory

namespace TauCeti
namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

/-! ## Reading a spectral projection through its diagonal measure -/

/-- A spectral projection annihilates a vector exactly when the vector's diagonal
measure gives the set no mass.  Everything about *which* sets matter for a fixed
vector is a statement about an honest Borel measure, and this is the bridge. -/
theorem specProjection_apply_eq_zero_iff_diag (B : Set ℝ) (hB : MeasurableSet B) (x : H) :
    specProjection hA B hB x = 0 ↔ (spectralPVM hA).diag x B = 0 := by
  rw [← ProjValMeasure.enorm_sq_proj_apply (spectralPVM hA) B hB x, ← specProjection_def]
  simp [pow_eq_zero_iff]

/-- Composition of spectral projections is the projection of the intersection,
applied to a vector. -/
theorem specProjection_apply_specProjection {B C : Set ℝ} (hB : MeasurableSet B)
    (hC : MeasurableSet C) (x : H) :
    specProjection hA B hB (specProjection hA C hC x)
      = specProjection hA (B ∩ C) (hB.inter hC) x := by
  have h := congrArg (fun T : H →L[ℂ] H => T x) ((spectralPVM hA).proj_inter B C hB hC)
  simpa only [specProjection_def, _root_.mul_apply_eq_comp] using h

/-- A vector with no spectral mass on `C` has none on a subset of `C`. -/
theorem specProjection_apply_eq_zero_of_subset {B C : Set ℝ} (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hsub : B ⊆ C) {x : H}
    (hx : specProjection hA C hC x = 0) :
    specProjection hA B hB x = 0 := by
  rw [specProjection_apply_eq_zero_iff_diag] at hx ⊢
  exact measure_mono_null hsub hx

/-- A spectral projection vanishing on `C` vanishes on every subset of `C`. -/
theorem specProjection_eq_zero_of_subset {B C : Set ℝ} (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hsub : B ⊆ C) (h : specProjection hA C hC = 0) :
    specProjection hA B hB = 0 := by
  ext x
  have hx : specProjection hA C hC x = 0 := by rw [h]; rfl
  simpa using specProjection_apply_eq_zero_of_subset hA hB hC hsub hx

/-- The projections of a set and its complement recompose the vector. -/
theorem specProjection_add_compl_apply {B : Set ℝ} (hB : MeasurableSet B) (x : H) :
    specProjection hA B hB x + specProjection hA Bᶜ hB.compl x = x := by
  have h := congrArg (fun T : H →L[ℂ] H => T x) ((spectralPVM hA).proj_compl B hB)
  simp only [specProjection_def] at h ⊢
  rw [h]
  simp

/-- Spectral projections are orthogonal projections: the image of one vector is
orthogonal to the complementary part of another. -/
theorem inner_specProjection_sub_specProjection {B : Set ℝ} (hB : MeasurableSet B) (u v : H) :
    ⟪specProjection hA B hB u, v - specProjection hA B hB v⟫_ℂ = 0 := by
  have hadj : (specProjection hA B hB).adjoint = specProjection hA B hB :=
    (isSelfAdjoint_specProjection hA B hB).adjoint_eq
  have hidem : specProjection hA B hB (specProjection hA B hB v) = specProjection hA B hB v := by
    have h := congrArg (fun T : H →L[ℂ] H => T v) (isIdempotentElem_specProjection hA B hB)
    simpa only [_root_.mul_apply_eq_comp] using h
  have hmove : ∀ w : H,
      ⟪specProjection hA B hB u, w⟫_ℂ = ⟪u, specProjection hA B hB w⟫_ℂ := by
    intro w
    nth_rewrite 1 [← hadj]
    exact ContinuousLinearMap.adjoint_inner_left _ _ _
  rw [hmove, map_sub, hidem, sub_self, inner_zero_right]

/-! ## The energy split across a spectral projection -/

/-- The spectral projection of a domain vector, as a domain vector. -/
@[expose]
noncomputable def specProjectionDomain (B : Set ℝ) (hB : MeasurableSet B) (x : A.domain) :
    A.domain :=
  ⟨specProjection hA B hB (x : H), specProjection_mem_domain hA B hB x⟩

/-- The underlying set of the spectral-projection domain. -/
@[simp]
theorem specProjectionDomain_coe (B : Set ℝ) (hB : MeasurableSet B) (x : A.domain) :
    ((specProjectionDomain hA B hB x : A.domain) : H) = specProjection hA B hB (x : H) := rfl

/-- **The quadratic form splits across a spectral projection.**  The cross terms
vanish because the projection commutes with `A` on the domain and is an
orthogonal projection. -/
theorem re_inner_eq_add_specProjection (B : Set ℝ) (hB : MeasurableSet B) (x : A.domain) :
    (⟪A x, (x : H)⟫_ℂ).re
      = (⟪A (specProjectionDomain hA B hB x),
            (specProjection hA B hB (x : H))⟫_ℂ).re
        + (⟪A (x - specProjectionDomain hA B hB x),
            ((x : H) - specProjection hA B hB (x : H))⟫_ℂ).re := by
  set y : A.domain := specProjectionDomain hA B hB x with hy
  have hyc : (y : H) = specProjection hA B hB (x : H) := rfl
  have hAy : A y = specProjection hA B hB (A x) :=
    specProjection_apply_domain hA B hB x
  have hz : ((x - y : A.domain) : H) = (x : H) - specProjection hA B hB (x : H) := by
    rw [← hyc]; rfl
  have hAz : A (x - y) = A x - specProjection hA B hB (A x) := by
    rw [_root_.LinearPMap.map_sub, hAy]
  have hcross₁ : ⟪A y, (x : H) - specProjection hA B hB (x : H)⟫_ℂ = 0 := by
    rw [hAy]
    exact inner_specProjection_sub_specProjection hA hB (A x) (x : H)
  have hcross₂ : ⟪A (x - y), specProjection hA B hB (x : H)⟫_ℂ = 0 := by
    rw [hAz, ← inner_conj_symm,
      show ⟪specProjection hA B hB (x : H), A x - specProjection hA B hB (A x)⟫_ℂ = 0 from
        inner_specProjection_sub_specProjection hA hB (x : H) (A x)]
    simp
  have hsplit : ⟪A x, (x : H)⟫_ℂ
      = ⟪A y, specProjection hA B hB (x : H)⟫_ℂ
        + ⟪A (x - y), (x : H) - specProjection hA B hB (x : H)⟫_ℂ := by
    calc ⟪A x, (x : H)⟫_ℂ
        = ⟪A y + A (x - y),
            specProjection hA B hB (x : H)
              + ((x : H) - specProjection hA B hB (x : H))⟫_ℂ := by
          congr 1
          · rw [hAz, hAy]; abel
          · abel
      _ = ⟪A y, specProjection hA B hB (x : H)⟫_ℂ
            + ⟪A (x - y), (x : H) - specProjection hA B hB (x : H)⟫_ℂ := by
          rw [inner_add_left, inner_add_right, inner_add_right, hcross₁, hcross₂]
          ring
  rw [hsplit, Complex.add_re]

/-- The squared norm splits across a spectral projection. -/
theorem norm_sq_eq_add_specProjection (B : Set ℝ) (hB : MeasurableSet B) (x : H) :
    ‖x‖ ^ 2 = ‖specProjection hA B hB x‖ ^ 2 + ‖x - specProjection hA B hB x‖ ^ 2 := by
  have hortho : ⟪specProjection hA B hB x, x - specProjection hA B hB x⟫_ℂ = 0 :=
    inner_specProjection_sub_specProjection hA hB x x
  calc ‖x‖ ^ 2
      = ‖specProjection hA B hB x + (x - specProjection hA B hB x)‖ ^ 2 := by
        rw [add_sub_cancel]
    _ = ‖specProjection hA B hB x‖ ^ 2 + ‖x - specProjection hA B hB x‖ ^ 2 := by
        simpa only [sq] using
          norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hortho

/-! ## The strict vector-local form bounds -/

/-- A projection over an empty set annihilates everything. -/
theorem specProjection_apply_eq_zero_of_eq_empty {B : Set ℝ} (hB : MeasurableSet B)
    (hemp : B = ∅) (x : H) : specProjection hA B hB x = 0 := by
  rw [specProjection_apply_eq_zero_iff_diag, hemp, measure_empty]

/-- The projection depends only on the set, not on the measurability witness. -/
theorem specProjection_apply_congr {B C : Set ℝ} (h : B = C) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (x : H) :
    specProjection hA B hB x = specProjection hA C hC x := by
  subst h; rfl

/-- A spectral projection fixes its own image. -/
theorem specProjection_apply_self (B : Set ℝ) (hB : MeasurableSet B) (x : H) :
    specProjection hA B hB (specProjection hA B hB x) = specProjection hA B hB x := by
  rw [specProjection_apply_specProjection]
  exact specProjection_apply_congr hA (Set.inter_self _) _ _ x

/-- The complementary part of a vector is the projection of the complement. -/
theorem sub_specProjection_apply {B : Set ℝ} (hB : MeasurableSet B) (x : H) :
    x - specProjection hA B hB x = specProjection hA Bᶜ hB.compl x :=
  sub_eq_of_eq_add' (specProjection_add_compl_apply hA hB x).symm

/-- **Strict vector-local lower energy bound.**  A nonzero domain vector with no
spectral mass in `(-∞, c]` has quadratic form *strictly* above `c‖x‖²`.

The non-strict bound cannot be improved by an epsilon argument: the strictness
comes from locating a level `d > c` that carries some of the vector's mass —
which exists because the mass has to sit somewhere — and splitting the energy
there. -/
theorem lt_re_inner_of_specProjection_Iic_apply_eq_zero {c : ℝ} (x : A.domain)
    (hz : specProjection hA (Set.Iic c) measurableSet_Iic (x : H) = 0)
    (hx : (x : H) ≠ 0) :
    c * ‖(x : H)‖ ^ 2 < (⟪A x, (x : H)⟫_ℂ).re := by
  classical
  obtain ⟨n, hn⟩ : ∃ n : ℕ,
      (spectralPVM hA).diag (x : H) (Set.Ici (c + 1 / (n + 1 : ℝ))) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hcover : Set.Ioi c ⊆ ⋃ n : ℕ, Set.Ici (c + 1 / (n + 1 : ℝ)) := by
      intro t ht
      have htc : (0 : ℝ) < t - c := by
        have : c < t := ht
        linarith
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt htc
      exact Set.mem_iUnion.2 ⟨m, by simp only [Set.mem_Ici]; linarith⟩
    have hIoi : (spectralPVM hA).diag (x : H) (Set.Ioi c) = 0 :=
      measure_mono_null hcover (measure_iUnion_null hcon)
    have hIic : (spectralPVM hA).diag (x : H) (Set.Iic c) = 0 :=
      (specProjection_apply_eq_zero_iff_diag hA _ measurableSet_Iic (x : H)).1 hz
    have huniv : (spectralPVM hA).diag (x : H) Set.univ = 0 := by
      rw [← Set.Iic_union_Ioi (a := c)]
      exact measure_union_null hIic hIoi
    rw [ProjValMeasure.diag_univ] at huniv
    exact hx (by simpa using huniv)
  have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
  set d : ℝ := c + 1 / (n + 1 : ℝ) with hd
  set e : ℝ := (c + d) / 2 with he
  have hce : c < e := by rw [he, hd]; linarith
  have hed : e < d := by rw [he, hd]; linarith
  set y : A.domain := specProjectionDomain hA (Set.Ici d) measurableSet_Ici x with hy
  have hyc : (y : H) = specProjection hA (Set.Ici d) measurableSet_Ici (x : H) := rfl
  have hyne : (y : H) ≠ 0 := fun h0 =>
    hn ((specProjection_apply_eq_zero_iff_diag hA _ measurableSet_Ici (x : H)).1 (hyc ▸ h0))
  -- the high piece: no mass at or below `e`
  have hylow : specProjection hA (Set.Iic e) measurableSet_Iic (y : H) = 0 := by
    rw [hyc, specProjection_apply_specProjection]
    refine specProjection_apply_eq_zero_of_eq_empty hA _ ?_ _
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ici, Set.mem_empty_iff_false, iff_false,
      not_and, not_le]
    intro ht
    linarith
  -- the low piece: still no mass at or below `c`
  have hzc : ((x - y : A.domain) : H)
      = specProjection hA (Set.Ici d)ᶜ measurableSet_Ici.compl (x : H) := by
    change (x : H) - (y : H) = _
    rw [hyc, sub_specProjection_apply]
  have hzlow : specProjection hA (Set.Iic c) measurableSet_Iic ((x - y : A.domain) : H) = 0 := by
    rw [hzc, specProjection_apply_specProjection]
    rw [specProjection_apply_congr hA (C := Set.Iic c) ?_ _ measurableSet_Iic]
    · exact hz
    · ext t
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_compl_iff, Set.mem_Ici, not_le,
        and_iff_left_iff_imp]
      intro ht
      linarith
  have hybound : e * ‖(y : H)‖ ^ 2 ≤ (⟪A y, (y : H)⟫_ℂ).re :=
    le_re_inner_of_specProjection_Iic_apply_eq_zero hA (c := e) y hylow
  have hzbound : c * ‖(x : H) - (y : H)‖ ^ 2
      ≤ (⟪A (x - y), (x : H) - (y : H)⟫_ℂ).re :=
    le_re_inner_of_specProjection_Iic_apply_eq_zero hA (c := c) (x - y) hzlow
  have hform : (⟪A x, (x : H)⟫_ℂ).re
      = (⟪A y, (y : H)⟫_ℂ).re + (⟪A (x - y), (x : H) - (y : H)⟫_ℂ).re :=
    re_inner_eq_add_specProjection hA (Set.Ici d) measurableSet_Ici x
  have hnorm : ‖(x : H)‖ ^ 2 = ‖(y : H)‖ ^ 2 + ‖(x : H) - (y : H)‖ ^ 2 :=
    norm_sq_eq_add_specProjection hA (Set.Ici d) measurableSet_Ici (x : H)
  have hypos : 0 < ‖(y : H)‖ ^ 2 := by positivity
  have hprod : c * ‖(y : H)‖ ^ 2 < e * ‖(y : H)‖ ^ 2 :=
    mul_lt_mul_of_pos_right hce hypos
  have hcnorm : c * ‖(x : H)‖ ^ 2
      = c * ‖(y : H)‖ ^ 2 + c * ‖(x : H) - (y : H)‖ ^ 2 := by
    rw [hnorm]; ring
  linarith [hform, hybound, hzbound, hprod, hcnorm]

/-- **Strict vector-local upper energy bound.**  Dual to
`lt_re_inner_of_specProjection_Iic_apply_eq_zero`. -/
theorem re_inner_lt_of_specProjection_Ici_apply_eq_zero {c : ℝ} (x : A.domain)
    (hz : specProjection hA (Set.Ici c) measurableSet_Ici (x : H) = 0)
    (hx : (x : H) ≠ 0) :
    (⟪A x, (x : H)⟫_ℂ).re < c * ‖(x : H)‖ ^ 2 := by
  classical
  obtain ⟨n, hn⟩ : ∃ n : ℕ,
      (spectralPVM hA).diag (x : H) (Set.Iic (c - 1 / (n + 1 : ℝ))) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hcover : Set.Iio c ⊆ ⋃ n : ℕ, Set.Iic (c - 1 / (n + 1 : ℝ)) := by
      intro t ht
      have htc : (0 : ℝ) < c - t := by
        have : t < c := ht
        linarith
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt htc
      exact Set.mem_iUnion.2 ⟨m, by simp only [Set.mem_Iic]; linarith⟩
    have hIio : (spectralPVM hA).diag (x : H) (Set.Iio c) = 0 :=
      measure_mono_null hcover (measure_iUnion_null hcon)
    have hIci : (spectralPVM hA).diag (x : H) (Set.Ici c) = 0 :=
      (specProjection_apply_eq_zero_iff_diag hA _ measurableSet_Ici (x : H)).1 hz
    have huniv : (spectralPVM hA).diag (x : H) Set.univ = 0 := by
      rw [← Set.Iio_union_Ici (a := c)]
      exact measure_union_null hIio hIci
    rw [ProjValMeasure.diag_univ] at huniv
    exact hx (by simpa using huniv)
  have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
  set d : ℝ := c - 1 / (n + 1 : ℝ) with hd
  set e : ℝ := (c + d) / 2 with he
  have hde : d < e := by rw [he, hd]; linarith
  have hec : e < c := by rw [he, hd]; linarith
  set y : A.domain := specProjectionDomain hA (Set.Iic d) measurableSet_Iic x with hy
  have hyc : (y : H) = specProjection hA (Set.Iic d) measurableSet_Iic (x : H) := rfl
  have hyne : (y : H) ≠ 0 := fun h0 =>
    hn ((specProjection_apply_eq_zero_iff_diag hA _ measurableSet_Iic (x : H)).1 (hyc ▸ h0))
  have hyhigh : specProjection hA (Set.Ici e) measurableSet_Ici (y : H) = 0 := by
    rw [hyc, specProjection_apply_specProjection]
    refine specProjection_apply_eq_zero_of_eq_empty hA _ ?_ _
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Iic, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, h2⟩
    linarith
  have hzc : ((x - y : A.domain) : H)
      = specProjection hA (Set.Iic d)ᶜ measurableSet_Iic.compl (x : H) := by
    change (x : H) - (y : H) = _
    rw [hyc, sub_specProjection_apply]
  have hzhigh : specProjection hA (Set.Ici c) measurableSet_Ici ((x - y : A.domain) : H) = 0 := by
    rw [hzc, specProjection_apply_specProjection]
    rw [specProjection_apply_congr hA (C := Set.Ici c) ?_ _ measurableSet_Ici]
    · exact hz
    · ext t
      simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_compl_iff, Set.mem_Iic, not_le,
        and_iff_left_iff_imp]
      intro ht
      linarith
  have hybound : (⟪A y, (y : H)⟫_ℂ).re ≤ e * ‖(y : H)‖ ^ 2 :=
    re_inner_le_of_specProjection_Ici_apply_eq_zero hA (c := e) y hyhigh
  have hzbound : (⟪A (x - y), (x : H) - (y : H)⟫_ℂ).re
      ≤ c * ‖(x : H) - (y : H)‖ ^ 2 :=
    re_inner_le_of_specProjection_Ici_apply_eq_zero hA (c := c) (x - y) hzhigh
  have hform : (⟪A x, (x : H)⟫_ℂ).re
      = (⟪A y, (y : H)⟫_ℂ).re + (⟪A (x - y), (x : H) - (y : H)⟫_ℂ).re :=
    re_inner_eq_add_specProjection hA (Set.Iic d) measurableSet_Iic x
  have hnorm : ‖(x : H)‖ ^ 2 = ‖(y : H)‖ ^ 2 + ‖(x : H) - (y : H)‖ ^ 2 :=
    norm_sq_eq_add_specProjection hA (Set.Iic d) measurableSet_Iic (x : H)
  have hypos : 0 < ‖(y : H)‖ ^ 2 := by positivity
  have hprod : e * ‖(y : H)‖ ^ 2 < c * ‖(y : H)‖ ^ 2 :=
    mul_lt_mul_of_pos_right hec hypos
  have hcnorm : c * ‖(x : H)‖ ^ 2
      = c * ‖(y : H)‖ ^ 2 + c * ‖(x : H) - (y : H)‖ ^ 2 := by
    rw [hnorm]; ring
  linarith [hform, hybound, hzbound, hprod, hcnorm]

/-! ## The Rayleigh--Ritz gap theorem -/

/-- A projection over an empty set is the zero operator. -/
theorem specProjection_eq_zero_of_eq_empty {B : Set ℝ} (hB : MeasurableSet B) (hemp : B = ∅) :
    specProjection hA B hB = 0 := by
  ext x
  simpa using specProjection_apply_eq_zero_of_eq_empty hA hB hemp x

/-- **The Ritz bound makes the low spectral compression injective on the trial
space.**  A nonzero trial vector cannot have all its spectral mass strictly
above `α`: the strict form bound would put its energy above `α‖u‖²`, and the
Ritz bound puts it at or below.

This is where strictness is indispensable.  A trial vector realising the top
Ritz value satisfies the Ritz bound with equality, so the non-strict energy
bound is consistent with all its mass sitting above `α`. -/
theorem eq_zero_of_specProjection_Iic_apply_eq_zero_of_form_le
    {K : Submodule ℂ H} {α : ℝ} (hKdom : K ≤ A.domain)
    (hRitz : ∀ x : A.domain, (x : H) ∈ K → (⟪A x, (x : H)⟫_ℂ).re ≤ α * ‖(x : H)‖ ^ 2)
    {u : H} (hu : u ∈ K)
    (h0 : specProjection hA (Set.Iic α) measurableSet_Iic u = 0) :
    u = 0 := by
  by_contra hne
  exact absurd (lt_re_inner_of_specProjection_Iic_apply_eq_zero hA
      (⟨u, hKdom hu⟩ : A.domain) h0 hne)
    (not_lt.2 (hRitz ⟨u, hKdom hu⟩ hu))

/-- **Rayleigh--Ritz: a trial subspace with a coercive complement certifies a
spectral gap.**

`K` is a finite-dimensional trial subspace inside the domain of the self-adjoint
operator `A`.  If the quadratic form is at most `α‖·‖²` on `K` — the Ritz bound —
and at least `β‖·‖²` on `Kᗮ` — coercivity off the trial space — then `A` has no
spectrum in the open interval `(α, β)`.

Neither hypothesis alone says anything about the spectrum between `α` and `β`:
the Ritz bound is an upper bound on `dim K` eigenvalues, coercivity is a lower
bound on the rest, and the conclusion is that the two families cannot overlap.
The proof exhibits `dim K + 1` independent vectors on which the form stays
strictly below `β` — the `dim K` low compressions of a basis of `K`, plus one
vector of spectral mass inside `(α, β)` — and rank--nullity of the compression
to `K` produces a nonzero one in `Kᗮ`, contradicting coercivity. -/
theorem specProjection_Ioo_eq_zero_of_rayleighRitz
    {K : Submodule ℂ H} [K.HasOrthogonalProjection] [FiniteDimensional ℂ K]
    {α β : ℝ} (hKdom : K ≤ A.domain)
    (hRitz : ∀ x : A.domain, (x : H) ∈ K → (⟪A x, (x : H)⟫_ℂ).re ≤ α * ‖(x : H)‖ ^ 2)
    (hCoercive : ∀ x : A.domain, (x : H) ∈ Kᗮ →
      β * ‖(x : H)‖ ^ 2 ≤ (⟪A x, (x : H)⟫_ℂ).re) :
    specProjection hA (Set.Ioo α β) measurableSet_Ioo = 0 := by
  classical
  rcases le_or_gt β α with hβα | hαβ
  · exact specProjection_eq_zero_of_eq_empty hA _ (Set.Ioo_eq_empty (not_lt.2 hβα))
  by_contra hne
  -- a nonzero spectral vector strictly inside the gap, produced from the dense domain
  obtain ⟨v, hvdom, hv⟩ :
      ∃ v : H, v ∈ A.domain ∧ specProjection hA (Set.Ioo α β) measurableSet_Ioo v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hne (ContinuousLinearMap.ext_on (s := (A.domain : Set H))
      (by rw [Submodule.span_eq]; exact hA.dense_domain) ?_)
    intro w hw
    simpa using hcon w hw
  set P : H →L[ℂ] H := specProjection hA (Set.Ioo α β) measurableSet_Ioo with hP
  set Q : H →L[ℂ] H := specProjection hA (Set.Iic α) measurableSet_Iic with hQ
  set x : H := P v with hx
  have hxne : x ≠ 0 := hv
  have hxdom : x ∈ A.domain := specProjection_mem_domain hA _ _ ⟨v, hvdom⟩
  have hxfix : P x = x := by
    rw [hx, hP]
    exact specProjection_apply_self hA _ _ v
  -- everything in `W` has its spectral mass strictly below `β`
  set W : Submodule ℂ H := (Submodule.span ℂ ({x} : Set H)) ⊔ (K.map (Q : H →ₗ[ℂ] H)) with hW
  have hxIci : specProjection hA (Set.Ici β) measurableSet_Ici x = 0 := by
    rw [hx, hP, specProjection_apply_specProjection]
    refine specProjection_apply_eq_zero_of_eq_empty hA _ ?_ _
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioo, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, -, h3⟩
    linarith
  have hQIci : ∀ u : H, specProjection hA (Set.Ici β) measurableSet_Ici (Q u) = 0 := by
    intro u
    rw [hQ, specProjection_apply_specProjection]
    refine specProjection_apply_eq_zero_of_eq_empty hA _ ?_ _
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Iic, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, h2⟩
    linarith
  have hWIci : ∀ w ∈ W, specProjection hA (Set.Ici β) measurableSet_Ici w = 0 := by
    have hsub : W ≤ LinearMap.ker
        ((specProjection hA (Set.Ici β) measurableSet_Ici : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
      refine sup_le ?_ ?_
      · rw [Submodule.span_singleton_le_iff_mem]
        exact hxIci
      · rintro w ⟨u, -, rfl⟩
        exact hQIci u
    exact fun w hw => hsub hw
  have hWdom : ∀ w ∈ W, w ∈ A.domain := by
    have hsub : W ≤ A.domain := by
      refine sup_le ?_ ?_
      · rw [Submodule.span_singleton_le_iff_mem]
        exact hxdom
      · rintro w ⟨u, hu, rfl⟩
        exact specProjection_mem_domain hA _ _ ⟨u, hKdom hu⟩
    exact fun w hw => hsub hw
  -- `W` has one dimension more than `K`
  have hQinj : Function.Injective ((Q : H →ₗ[ℂ] H) ∘ₗ K.subtype) := by
    rw [← LinearMap.ker_eq_bot] at *
    rw [Submodule.eq_bot_iff]
    rintro ⟨u, hu⟩ hker
    have h0 : Q u = 0 := hker
    exact Subtype.ext (eq_zero_of_specProjection_Iic_apply_eq_zero_of_form_le hA hKdom hRitz hu h0)
  have hrangeQ : LinearMap.range ((Q : H →ₗ[ℂ] H) ∘ₗ K.subtype) = K.map (Q : H →ₗ[ℂ] H) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hfinrankQ : Module.finrank ℂ (K.map (Q : H →ₗ[ℂ] H)) = Module.finrank ℂ K := by
    rw [← hrangeQ]
    exact (LinearEquiv.finrank_eq (LinearEquiv.ofInjective _ hQinj)).symm
  have : FiniteDimensional ℂ (K.map (Q : H →ₗ[ℂ] H)) := by
    rw [← hrangeQ]
    infer_instance
  have : FiniteDimensional ℂ (Submodule.span ℂ ({x} : Set H)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_singleton x)
  have hinf : (Submodule.span ℂ ({x} : Set H)) ⊓ (K.map (Q : H →ₗ[ℂ] H)) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro w ⟨hw1, hw2⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw1
    obtain ⟨u, -, hu⟩ := hw2
    have hQfix : Q (a • x) = a • x := by
      rw [← hu]
      simp only [ContinuousLinearMap.coe_coe, hQ]
      exact specProjection_apply_self hA _ _ u
    have hPfix : P (a • x) = a • x := by rw [map_smul, hxfix]
    have : a • x = 0 := by
      calc a • x = P (a • x) := hPfix.symm
        _ = P (Q (a • x)) := by rw [hQfix]
        _ = specProjection hA (Set.Ioo α β ∩ Set.Iic α)
              (measurableSet_Ioo.inter measurableSet_Iic) (a • x) := by
          rw [hP, hQ, specProjection_apply_specProjection]
        _ = 0 := by
          refine specProjection_apply_eq_zero_of_eq_empty hA _ ?_ _
          ext t
          simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Iic, Set.mem_empty_iff_false,
            iff_false, not_and, not_le]
          rintro ⟨h1, -⟩
          exact h1
    exact this
  have : FiniteDimensional ℂ W := by
    rw [hW]
    infer_instance
  have hfinrankW : Module.finrank ℂ W = Module.finrank ℂ K + 1 := by
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq
      (Submodule.span ℂ ({x} : Set H)) (K.map (Q : H →ₗ[ℂ] H))
    rw [hinf, finrank_bot, finrank_span_singleton hxne, hfinrankQ, ← hW] at hsum
    omega
  -- rank--nullity: some nonzero vector of `W` is orthogonal to `K`
  set g : W →ₗ[ℂ] K :=
    (K.orthogonalProjectionOnto : H →L[ℂ] K).toLinearMap ∘ₗ W.subtype with hg
  have hkerne : LinearMap.ker g ≠ ⊥ := by
    intro h0
    have hrn := LinearMap.finrank_range_add_finrank_ker g
    rw [h0, finrank_bot, hfinrankW] at hrn
    have hle : Module.finrank ℂ (LinearMap.range g) ≤ Module.finrank ℂ K :=
      Submodule.finrank_le _
    omega
  obtain ⟨w, hwker, hwne⟩ := Submodule.ne_bot_iff _ |>.1 hkerne
  have hwHne : ((w : W) : H) ≠ 0 := fun h0 => hwne (Subtype.ext h0)
  have hwperp : ((w : W) : H) ∈ Kᗮ := by
    rw [← Submodule.orthogonalProjectionOnto_eq_zero_iff]
    exact hwker
  have hwdom : ((w : W) : H) ∈ A.domain := hWdom _ w.property
  have hlow := re_inner_lt_of_specProjection_Ici_apply_eq_zero hA
    (⟨((w : W) : H), hwdom⟩ : A.domain) (hWIci _ w.property) hwHne
  have hhigh := hCoercive ⟨((w : W) : H), hwdom⟩ hwperp
  exact absurd hlow (not_lt.2 hhigh)

/-! ## The dimension count

The gap theorem above discards the dimension bookkeeping once the contradiction
is reached.  Stated on its own, that bookkeeping says: coercivity off a
finite-dimensional trial subspace caps the dimension of every low spectral
range, and the Ritz bound realises the cap.  This is the min--max eigenvalue
count in the form a spectral-subspace argument uses. -/

/-- **Rayleigh--Ritz dimension count, upper half.**  If the form is at least
`β‖·‖²` on `Kᗮ`, no finite-dimensional subspace of a spectral range below `c < β`
has more dimensions than `K`. -/
theorem finrank_le_of_le_specRange_Iic
    {K : Submodule ℂ H} [K.HasOrthogonalProjection] [FiniteDimensional ℂ K]
    {β c : ℝ} (hcβ : c < β)
    (hCoercive : ∀ x : A.domain, (x : H) ∈ Kᗮ →
      β * ‖(x : H)‖ ^ 2 ≤ (⟪A x, (x : H)⟫_ℂ).re)
    (hdom : ∀ x ∈ specRange hA (Set.Iic c) measurableSet_Iic, x ∈ A.domain)
    {W : Submodule ℂ H} [FiniteDimensional ℂ W]
    (hW : W ≤ specRange hA (Set.Iic c) measurableSet_Iic) :
    Module.finrank ℂ W ≤ Module.finrank ℂ K := by
  classical
  set g : W →ₗ[ℂ] K :=
    (K.orthogonalProjectionOnto : H →L[ℂ] K).toLinearMap ∘ₗ W.subtype with hg
  have hinj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro w hw
    by_contra hne
    have hwH : ((w : W) : H) ≠ 0 := fun h0 => hne (Subtype.ext h0)
    have hwdom : ((w : W) : H) ∈ A.domain := hdom _ (hW w.property)
    have hwperp : ((w : W) : H) ∈ Kᗮ := by
      rw [← Submodule.orthogonalProjectionOnto_eq_zero_iff]
      exact hw
    -- the spectral range below `c` has form at most `c‖·‖²`
    have hIci : specProjection hA (Set.Ici β) measurableSet_Ici ((w : W) : H) = 0 := by
      have hfix : specProjection hA (Set.Iic c) measurableSet_Iic ((w : W) : H)
          = ((w : W) : H) := (mem_specRange_iff hA _ _ _).1 (hW w.property)
      rw [← hfix, specProjection_apply_specProjection]
      refine specProjection_apply_eq_zero_of_eq_empty hA _ ?_ _
      ext t
      simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Iic, Set.mem_empty_iff_false,
        iff_false]
      rintro ⟨h1, h2⟩
      linarith
    have hlow := re_inner_lt_of_specProjection_Ici_apply_eq_zero hA
      (⟨((w : W) : H), hwdom⟩ : A.domain) hIci hwH
    have hhigh := hCoercive ⟨((w : W) : H), hwdom⟩ hwperp
    exact absurd hlow (not_lt.2 hhigh)
  simpa using LinearMap.finrank_le_finrank_of_injective (f := g) hinj

/-- **Rayleigh--Ritz dimension count, lower half.**  The Ritz bound embeds the
trial subspace into the low spectral range. -/
theorem finrank_le_finrank_of_le_specRange_Iic
    {K : Submodule ℂ H} [K.HasOrthogonalProjection] [FiniteDimensional ℂ K]
    {α : ℝ} (hKdom : K ≤ A.domain)
    (hRitz : ∀ x : A.domain, (x : H) ∈ K → (⟪A x, (x : H)⟫_ℂ).re ≤ α * ‖(x : H)‖ ^ 2)
    {W : Submodule ℂ H} [FiniteDimensional ℂ W]
    (hW : specRange hA (Set.Iic α) measurableSet_Iic ≤ W) :
    Module.finrank ℂ K ≤ Module.finrank ℂ W := by
  classical
  set Q : H →L[ℂ] H := specProjection hA (Set.Iic α) measurableSet_Iic with hQ
  set f : K →ₗ[ℂ] W :=
    { toFun := fun u => ⟨Q (u : H), hW (specProjection_mem_specRange hA _ _ _)⟩
      map_add' := fun u v => by apply Subtype.ext; simp
      map_smul' := fun a u => by apply Subtype.ext; simp } with hf
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨u, hu⟩ hker
    have h0 : Q u = 0 := congrArg Subtype.val hker
    exact Subtype.ext
      (eq_zero_of_specProjection_Iic_apply_eq_zero_of_form_le hA hKdom hRitz hu h0)
  simpa using LinearMap.finrank_le_finrank_of_injective (f := f) hinj

end LinearPMap
end TauCeti
