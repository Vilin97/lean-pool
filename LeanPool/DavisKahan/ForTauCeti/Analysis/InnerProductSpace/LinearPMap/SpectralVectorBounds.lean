/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralFormBounds

/-!
# Vector-local form bounds from a half-line spectral condition

`SpectralFormBounds.lean` assumes an entire half-line projection is the zero
*operator*.  Min--max arguments need the sharper local form: a particular
domain vector is annihilated by the unwanted half-line projection, and only
that vector's quadratic form is controlled.  The proof is the same cutoff
argument as the global one, run along that vector and its image under `A`.

## Provenance

*Moved, not restated.*  These four theorems and the private truncation lemma
they share were written in
`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/GramSpectralRank.lean`,
whose own module docstring records that by dependency the material "is not
approximation-number material at all".  It is not: it is the vector-local
companion of `SpectralFormBounds.lean`, needs exactly that file plus
`Constructions.lean`, and is consumed by the Rayleigh--Ritz rank counting in
`RayleighRitz.lean` as well as by the Gram cutoffs it was written for.
Statements and proofs are unchanged; the namespace moved from
`TauCeti.ApproximationNumber.LinearPMap` to `TauCeti.LinearPMap`.
-/

@[expose] public section

namespace TauCeti
namespace LinearPMap

open scoped InnerProductSpace
open Set

section LocalHalfLine

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

/-- **A vector fixed by the projection for `S` is the limit of its truncations.**

`tendsto_specProjection_Icc` says the symmetric truncations `Set.Icc (-τ) τ` converge
strongly to the identity.  If `v` is already fixed by the projection for `S`, the
truncations may be intersected with `S` first and still converge to `v`.

The two half-line bounds below are exactly this at `S = Set.Ici c` and `S = Set.Iic c`,
whose truncations are `Set.Icc c τ` and `Set.Icc (-τ) c`.  **Only the set algebra differs
between them**, and that is what `hset` takes as an argument -- everything after it, the
`proj_congr`/`proj_inter` calculation, was written out twice. -/
private theorem tendsto_specProjection_inter_of_fix
    {S : Set ℝ} (hS : MeasurableSet S) {T : ℝ → Set ℝ} (hT : ∀ τ, MeasurableSet (T τ))
    (hset : ∀ᶠ τ : ℝ in Filter.atTop, Set.Icc (-τ) τ ∩ S = T τ)
    (v : H) (hv : specProjection hA S hS v = v) :
    Filter.Tendsto (fun τ : ℝ => specProjection hA (T τ) (hT τ) v)
      Filter.atTop (nhds v) := by
  refine (tendsto_specProjection_Icc hA v).congr' ?_
  filter_upwards [hset] with τ hτset
  set P := spectralPVM hA with hP
  simp only [specProjection_def]
  symm
  calc
    P.proj (T τ) (hT τ) v =
        P.proj (Set.Icc (-τ) τ ∩ S) (measurableSet_Icc.inter hS) v := by
      exact congrArg (fun R : H →L[ℂ] H => R v)
        (P.proj_congr hτset.symm (hT τ) (measurableSet_Icc.inter hS))
    _ = (P.proj (Set.Icc (-τ) τ) measurableSet_Icc * P.proj S hS) v := by
      rw [P.proj_inter]
    _ = P.proj (Set.Icc (-τ) τ) measurableSet_Icc v := by
      rw [mul_apply_eq_comp]
      simp only [specProjection_def] at hv
      rw [hv]

/-! ## Vector-local half-line bounds

The global lemmas above assume an entire half-line projection is the zero
operator.  Min--max arguments need the sharper local form: a particular domain
vector is annihilated by the unwanted half-line projection.  The proof is the
same cutoff argument, but only along that vector and its image under `A`.
-/

/-- If the low closed half-line annihilates `x`, then the complementary high
closed half-line fixes `x`. -/
theorem specProjection_Ici_apply_eq_self_of_Iic_apply_eq_zero {c : ℝ} (x : H)
    (hz : specProjection hA (Set.Iic c) measurableSet_Iic x = 0) :
    specProjection hA (Set.Ici c) measurableSet_Ici x = x := by
  set P := spectralPVM hA with hP
  have hIio : P.proj (Set.Iio c) measurableSet_Iio x = 0 := by
    have hset : Set.Iio c ∩ Set.Iic c = Set.Iio c := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Iic]
      constructor
      · exact fun hs => hs.1
      · intro hs
        exact ⟨hs, hs.le⟩
    calc
      P.proj (Set.Iio c) measurableSet_Iio x =
          (P.proj (Set.Iio c) measurableSet_Iio *
            P.proj (Set.Iic c) measurableSet_Iic) x := by
        rw [P.proj_inter]
        exact (congrArg (fun T : H →L[ℂ] H => T x)
          (P.proj_congr hset (measurableSet_Iio.inter measurableSet_Iic)
            measurableSet_Iio)).symm
      _ = 0 := by
        simp only [specProjection_def, ← hP] at hz
        rw [mul_apply_eq_comp, hz, map_zero]
  have hcompl : (Set.Iio c)ᶜ = Set.Ici c := Set.compl_Iio
  simp only [specProjection_def]
  calc
    P.proj (Set.Ici c) measurableSet_Ici x =
        P.proj (Set.Iio c)ᶜ measurableSet_Iio.compl x := by
      exact congrArg (fun T : H →L[ℂ] H => T x)
        (P.proj_congr hcompl.symm measurableSet_Ici measurableSet_Iio.compl)
    _ = (ContinuousLinearMap.id ℂ H - P.proj (Set.Iio c) measurableSet_Iio) x := by
      rw [P.proj_compl]
    _ = x := by
      rw [sub_apply, ContinuousLinearMap.id_apply, hIio, sub_zero]

/-- If the high closed half-line annihilates `x`, then the complementary low
closed half-line fixes `x`. -/
theorem specProjection_Iic_apply_eq_self_of_Ici_apply_eq_zero {c : ℝ} (x : H)
    (hz : specProjection hA (Set.Ici c) measurableSet_Ici x = 0) :
    specProjection hA (Set.Iic c) measurableSet_Iic x = x := by
  set P := spectralPVM hA with hP
  have hIoi : P.proj (Set.Ioi c) measurableSet_Ioi x = 0 := by
    have hset : Set.Ioi c ∩ Set.Ici c = Set.Ioi c := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici]
      constructor
      · exact fun hs => hs.1
      · intro hs
        exact ⟨hs, hs.le⟩
    calc
      P.proj (Set.Ioi c) measurableSet_Ioi x =
          (P.proj (Set.Ioi c) measurableSet_Ioi *
            P.proj (Set.Ici c) measurableSet_Ici) x := by
        rw [P.proj_inter]
        exact (congrArg (fun T : H →L[ℂ] H => T x)
          (P.proj_congr hset (measurableSet_Ioi.inter measurableSet_Ici)
            measurableSet_Ioi)).symm
      _ = 0 := by
        simp only [specProjection_def, ← hP] at hz
        rw [mul_apply_eq_comp, hz, map_zero]
  have hcompl : (Set.Ioi c)ᶜ = Set.Iic c := Set.compl_Ioi
  simp only [specProjection_def]
  calc
    P.proj (Set.Iic c) measurableSet_Iic x =
        P.proj (Set.Ioi c)ᶜ measurableSet_Ioi.compl x := by
      exact congrArg (fun T : H →L[ℂ] H => T x)
        (P.proj_congr hcompl.symm measurableSet_Iic measurableSet_Ioi.compl)
    _ = (ContinuousLinearMap.id ℂ H - P.proj (Set.Ioi c) measurableSet_Ioi) x := by
      rw [P.proj_compl]
    _ = x := by
      rw [sub_apply, ContinuousLinearMap.id_apply, hIoi, sub_zero]

/-- **Vector-local lower energy bound.** If a domain vector has no spectral
component in `(-∞, c]`, its quadratic form is at least `c ‖x‖²`. -/
theorem le_re_inner_of_specProjection_Iic_apply_eq_zero {c : ℝ} (x : A.domain)
    (hz : specProjection hA (Set.Iic c) measurableSet_Iic (x : H) = 0) :
    c * ‖(x : H)‖ ^ 2 ≤ (⟪A x, (x : H)⟫_ℂ).re := by
  have hfix : specProjection hA (Set.Ici c) measurableSet_Ici (x : H) = (x : H) :=
    specProjection_Ici_apply_eq_self_of_Iic_apply_eq_zero hA (x : H) hz
  have hzA : specProjection hA (Set.Iic c) measurableSet_Iic (A x) = 0 := by
    rw [← specProjection_apply_domain hA (Set.Iic c) measurableSet_Iic x]
    have hsub :
        (⟨specProjection hA (Set.Iic c) measurableSet_Iic (x : H),
          specProjection_mem_domain hA (Set.Iic c) measurableSet_Iic x⟩ : A.domain) = 0 :=
      Subtype.ext hz
    rw [hsub, _root_.LinearPMap.map_zero]
  have hfixA : specProjection hA (Set.Ici c) measurableSet_Ici (A x) = A x :=
    specProjection_Ici_apply_eq_self_of_Iic_apply_eq_zero hA (A x) hzA
  have hlim_of_fix : ∀ (v : H),
      specProjection hA (Set.Ici c) measurableSet_Ici v = v →
      Filter.Tendsto
        (fun τ : ℝ => specProjection hA (Set.Icc c τ) measurableSet_Icc v)
        Filter.atTop (nhds v) :=
    tendsto_specProjection_inter_of_fix hA measurableSet_Ici
      (fun _ => measurableSet_Icc) <| by
        filter_upwards [Filter.eventually_ge_atTop |c|] with τ hτ
        obtain ⟨hτ1, hτ2⟩ := abs_le.mp hτ
        ext s
        simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ici]
        constructor
        · rintro ⟨⟨hs1, hs2⟩, hs3⟩
          exact ⟨hs3, hs2⟩
        · rintro ⟨hs1, hs2⟩
          exact ⟨⟨by linarith, hs2⟩, hs1⟩
  have hbound : ∀ τ : ℝ,
      c * ‖specProjection hA (Set.Icc c τ) measurableSet_Icc (x : H)‖ ^ 2
        ≤ (⟪specProjection hA (Set.Icc c τ) measurableSet_Icc (A x),
            specProjection hA (Set.Icc c τ) measurableSet_Icc (x : H)⟫_ℂ).re :=
    fun τ => (re_inner_specProjection_Icc_bounds hA (α := τ) (β := c) x).1
  have hlx := hlim_of_fix (x : H) hfix
  have hlA := hlim_of_fix (A x) hfixA
  exact le_of_tendsto_of_tendsto'
    (((hlx.norm).pow 2).const_mul c)
    ((Complex.continuous_re.tendsto _).comp (hlA.inner hlx)) hbound

/-- **Vector-local upper energy bound.** If a domain vector has no spectral
component in `[c, ∞)`, its quadratic form is at most `c ‖x‖²`. -/
theorem re_inner_le_of_specProjection_Ici_apply_eq_zero {c : ℝ} (x : A.domain)
    (hz : specProjection hA (Set.Ici c) measurableSet_Ici (x : H) = 0) :
    (⟪A x, (x : H)⟫_ℂ).re ≤ c * ‖(x : H)‖ ^ 2 := by
  have hfix : specProjection hA (Set.Iic c) measurableSet_Iic (x : H) = (x : H) :=
    specProjection_Iic_apply_eq_self_of_Ici_apply_eq_zero hA (x : H) hz
  have hzA : specProjection hA (Set.Ici c) measurableSet_Ici (A x) = 0 := by
    rw [← specProjection_apply_domain hA (Set.Ici c) measurableSet_Ici x]
    have hsub :
        (⟨specProjection hA (Set.Ici c) measurableSet_Ici (x : H),
          specProjection_mem_domain hA (Set.Ici c) measurableSet_Ici x⟩ : A.domain) = 0 :=
      Subtype.ext hz
    rw [hsub, _root_.LinearPMap.map_zero]
  have hfixA : specProjection hA (Set.Iic c) measurableSet_Iic (A x) = A x :=
    specProjection_Iic_apply_eq_self_of_Ici_apply_eq_zero hA (A x) hzA
  have hlim_of_fix : ∀ (v : H),
      specProjection hA (Set.Iic c) measurableSet_Iic v = v →
      Filter.Tendsto
        (fun τ : ℝ => specProjection hA (Set.Icc (-τ) c) measurableSet_Icc v)
        Filter.atTop (nhds v) :=
    tendsto_specProjection_inter_of_fix hA measurableSet_Iic
      (fun _ => measurableSet_Icc) <| by
        filter_upwards [Filter.eventually_ge_atTop |c|] with τ hτ
        obtain ⟨hτ1, hτ2⟩ := abs_le.mp hτ
        ext s
        simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic]
        constructor
        · rintro ⟨⟨hs1, hs2⟩, hs3⟩
          exact ⟨hs1, hs3⟩
        · rintro ⟨hs1, hs2⟩
          exact ⟨⟨hs1, by linarith⟩, hs2⟩
  have hbound : ∀ τ : ℝ,
      (⟪specProjection hA (Set.Icc (-τ) c) measurableSet_Icc (A x),
          specProjection hA (Set.Icc (-τ) c) measurableSet_Icc (x : H)⟫_ℂ).re
        ≤ c * ‖specProjection hA (Set.Icc (-τ) c) measurableSet_Icc (x : H)‖ ^ 2 :=
    fun τ => (re_inner_specProjection_Icc_bounds hA (α := c) (β := -τ) x).2
  have hlx := hlim_of_fix (x : H) hfix
  have hlA := hlim_of_fix (A x) hfixA
  exact le_of_tendsto_of_tendsto'
    ((Complex.continuous_re.tendsto _).comp (hlA.inner hlx))
    (((hlx.norm).pow 2).const_mul c) hbound

end LocalHalfLine

end LinearPMap
end TauCeti
