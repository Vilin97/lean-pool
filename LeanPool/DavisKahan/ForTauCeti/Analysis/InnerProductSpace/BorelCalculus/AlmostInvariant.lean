/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.PVM
public import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Almost-invariant finite-dimensional enlargements

For a bounded self-adjoint operator `T` on a complex Hilbert space, every
finite-dimensional subspace `F₀` is contained in a finite-dimensional subspace `F` that is
almost invariant under `T`: the part of `T x` leaking out of `F` is at most `ε * ‖x‖` for
every `x ∈ F`.

This is the finite-projector selection step of the Davis--Kahan 1970 Appendix limiting
argument.  The paper's cutoff passage applies finite-trial Ky Fan inequalities on such
subspaces and lets the leakage tolerance tend to zero; nothing about `T` is assumed beyond
boundedness and self-adjointness — in particular no compactness, so the construction also
serves trial subspaces whose compressions have continuous spectrum.

The construction partitions an interval carrying the spectrum into finitely many short
subintervals, applies the spectral projections of `boundedPVM` to a finite spanning set of
`F₀`, and spans `F` by the resulting vectors.  Almost-invariance is the Pythagorean
combination of one band estimate per subinterval.

## Main results

* `TauCeti.BorelCalculus.norm_borelCalculus_le_of_forall_norm_le`: the operator norm of a
  Borel calculus value is at most twice any uniform bound of its symbol;
* `TauCeti.BorelCalculus.norm_comp_boundedPVM_proj_sub_smul_le`: the band estimate — on the
  range of a spectral projection of a short set, `T` deviates from the scalar `lam` by at
  most twice the band radius;
* `TauCeti.BorelCalculus.exists_finiteDimensional_le_almostInvariant`: the selection
  theorem.  The leakage bound is phrased through an approximating vector `y ∈ F`, so the
  statement needs no orthogonal-projection instance on the abstract `F`; consumers with
  `FiniteDimensional` in scope recover the projection form by minimality.
-/

public section

open scoped InnerProductSpace
open MeasureTheory

namespace TauCeti
namespace BorelCalculus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- The Pythagorean identity for a finite family of pairwise orthogonal vectors. -/
theorem norm_sq_sum_of_pairwise_inner_eq_zero {ι : Type*} (s : Finset ι) (v : ι → H)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪v i, v j⟫_ℂ = 0) :
    ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 := by
  have hinner : ⟪∑ i ∈ s, v i, ∑ j ∈ s, v j⟫_ℂ = ∑ i ∈ s, ⟪v i, v i⟫_ℂ := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [inner_sum]
    exact Finset.sum_eq_single_of_mem i hi fun j hj hji => h i hi j hj (Ne.symm hji)
  have hre : (⟪∑ i ∈ s, v i, ∑ j ∈ s, v j⟫_ℂ).re = ∑ i ∈ s, (⟪v i, v i⟫_ℂ).re := by
    rw [hinner, Complex.re_sum]
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), RCLike.re_eq_complex_re, hre]
  exact Finset.sum_congr rfl fun i _ => by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), RCLike.re_eq_complex_re]

/-- The Borel calculus of a symbol with an explicit uniform bound `M` has operator norm at
most `2 * M`.  This is the explicit-bound form of `norm_borelCalculus_le`, whose bound is
the packaged `chooseBound` of the admissibility witness. -/
theorem norm_borelCalculus_le_of_forall_norm_le {a : H →L[ℂ] H} (ha : IsStarNormal a)
    {f : spectrum ℂ a → ℂ} (hf : IsBddMeasurable f) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, ‖f x‖ ≤ M) :
    ‖borelCalculus ha hf‖ ≤ 2 * M := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun ξ => ?_
  have hsq : ‖borelCalculus ha hf ξ‖ ^ 2 ≤
      2 * M * ‖borelCalculus ha hf ξ‖ * ‖ξ‖ := by
    have hnorm : (‖borelCalculus ha hf ξ‖ ^ 2 : ℝ) =
        ‖⟪borelCalculus ha hf ξ, borelCalculus ha hf ξ⟫_ℂ‖ := by
      rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), norm_pow, RCLike.norm_ofReal, abs_norm]
    rw [hnorm, inner_borelCalculus ha hf (borelCalculus ha hf ξ) ξ]
    exact norm_pair_le ha hf.measurable hM hb _ ξ
  rcases eq_or_lt_of_le (norm_nonneg (borelCalculus ha hf ξ)) with h0 | hpos
  · rw [← h0]
    positivity
  · have h2 : ‖borelCalculus ha hf ξ‖ * ‖borelCalculus ha hf ξ‖ ≤
        (2 * M * ‖ξ‖) * ‖borelCalculus ha hf ξ‖ := by
      calc
        ‖borelCalculus ha hf ξ‖ * ‖borelCalculus ha hf ξ‖
            = ‖borelCalculus ha hf ξ‖ ^ 2 := (pow_two _).symm
        _ ≤ 2 * M * ‖borelCalculus ha hf ξ‖ * ‖ξ‖ := hsq
        _ = (2 * M * ‖ξ‖) * ‖borelCalculus ha hf ξ‖ := by ring
    exact le_of_mul_le_mul_right h2 hpos

section BoundedSelfAdjoint

variable {T : H →L[ℂ] H}

/-- **The band estimate.**  If every point of `B` lies within `r` of `lam`, then on the
range of the spectral projection of `B` the operator `T` deviates from the scalar `lam` by
at most `2 * r` in operator norm. -/
theorem norm_comp_boundedPVM_proj_sub_smul_le (hT : IsSelfAdjoint T)
    {B : Set ℝ} (hB : MeasurableSet B) {lam r : ℝ} (hr : 0 ≤ r)
    (hband : ∀ t ∈ B, |t - lam| ≤ r) :
    ‖T ∘L (boundedPVM hT).proj B hB -
      ((lam : ℝ) : ℂ) • (boundedPVM hT).proj B hB‖ ≤ 2 * r := by
  have hind : IsBddMeasurable
      ((reCoord ⁻¹' B).indicator (fun _ => (1 : ℂ))) :=
    isBddMeasurable_indicator (a := T) (measurable_reCoord (T := T) hB)
  have hcoord : IsBddMeasurable (fun w : spectrum ℂ T => (w : ℂ)) :=
    isBddMeasurable_coord
  have hsym : IsBddMeasurable (fun w : spectrum ℂ T =>
      (w : ℂ) * (reCoord ⁻¹' B).indicator (fun _ => (1 : ℂ)) w +
        (-((lam : ℝ) : ℂ)) * (reCoord ⁻¹' B).indicator (fun _ => (1 : ℂ)) w) :=
    (hcoord.mul hind).add (hind.const_smul (-((lam : ℝ) : ℂ)))
  have hcalc : borelCalculus hT.isStarNormal hsym =
      T ∘L (boundedPVM hT).proj B hB -
        ((lam : ℝ) : ℂ) • (boundedPVM hT).proj B hB := by
    rw [borelCalculus_add hT.isStarNormal (hcoord.mul hind)
        (hind.const_smul (-((lam : ℝ) : ℂ))),
      borelCalculus_mul hT.isStarNormal hcoord hind,
      borelCalculus_const_smul hT.isStarNormal (-((lam : ℝ) : ℂ)) hind,
      borelCalculus_coord hT.isStarNormal, ← boundedPVM_proj hT B hB, neg_smul,
      ← sub_eq_add_neg]
    rfl
  rw [← hcalc]
  refine norm_borelCalculus_le_of_forall_norm_le hT.isStarNormal hsym hr fun w => ?_
  by_cases hw : w ∈ reCoord (T := T) ⁻¹' B
  · have hind1 : (reCoord ⁻¹' B).indicator (fun _ => (1 : ℂ)) w = 1 :=
      Set.indicator_of_mem hw _
    have hre : ((w : ℂ)) = (((w : ℂ).re : ℝ) : ℂ) := hT.mem_spectrum_eq_re w.2
    have hmem : (w : ℂ).re ∈ B := by
      have h := hw
      rwa [Set.mem_preimage, reCoord_apply] at h
    calc
      ‖(w : ℂ) * (reCoord ⁻¹' B).indicator (fun _ => (1 : ℂ)) w +
          (-((lam : ℝ) : ℂ)) * (reCoord ⁻¹' B).indicator (fun _ => (1 : ℂ)) w‖
          = ‖(w : ℂ) - ((lam : ℝ) : ℂ)‖ := by
            rw [hind1, mul_one, mul_one, ← sub_eq_add_neg]
      _ = ‖((((w : ℂ).re - lam : ℝ)) : ℂ)‖ := by rw [hre]; norm_cast
      _ = |(w : ℂ).re - lam| := by rw [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ r := hband _ hmem
  · have hind0 : (reCoord ⁻¹' B).indicator (fun _ => (1 : ℂ)) w = 0 :=
      Set.indicator_of_notMem hw _
    rw [hind0, mul_zero, mul_zero, add_zero, norm_zero]
    exact hr

/-- The equal-width half-open bands cover every point in the open interval. -/
private theorem mem_uniform_interval (R d : ℝ) {m : ℕ}
    (hd : 0 < d) (hmd : (m : ℝ) * d = 2 * R) {t : ℝ}
    (htR : -R < t ∧ t < R) :
    ∃ j : Fin m, t ∈ Set.Ico (-R + (j : ℕ) * d) (-R + ((j : ℕ) + 1) * d) := by
  have hnn : (0 : ℝ) ≤ (t + R) / d := by
    apply div_nonneg _ hd.le
    linarith [htR.1]
  have hlt : ⌊(t + R) / d⌋₊ < m := by
    rw [Nat.floor_lt hnn, div_lt_iff₀ hd]
    have h2R : t + R < 2 * R := by linarith [htR.2]
    linarith [hmd]
  refine ⟨⟨⌊(t + R) / d⌋₊, hlt⟩, ?_⟩
  have hfl : (⌊(t + R) / d⌋₊ : ℝ) ≤ (t + R) / d := Nat.floor_le hnn
  have hfu : (t + R) / d < (⌊(t + R) / d⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hl : (⌊(t + R) / d⌋₊ : ℝ) * d ≤ t + R := by
    rw [← le_div_iff₀ hd]
    exact hfl
  have hu : t + R < ((⌊(t + R) / d⌋₊ : ℝ) + 1) * d := by
    rw [← div_lt_iff₀ hd]
    exact hfu
  simp only [Set.mem_Ico]
  constructor <;> [linarith; linarith]

/-- Spectral projections for a measurable disjoint cover sum to the identity. -/
private theorem sum_boundedPVM_proj_eq_id (hT : IsSelfAdjoint T) {m : ℕ}
    (I : Fin m → Set ℝ) (hImeas : ∀ j, MeasurableSet (I j))
    (hIdisj : ∀ i j : Fin m, i ≠ j → Disjoint (I i) (I j))
    (hcover : ∀ w : spectrum ℂ T, ∃ j : Fin m, reCoord (T := T) w ∈ I j) :
    (∑ j : Fin m, (boundedPVM hT).proj (I j) (hImeas j)) =
      ContinuousLinearMap.id ℂ H := by
  classical
  let p : Fin m → (H →L[ℂ] H) := fun j => (boundedPVM hT).proj (I j) (hImeas j)
  change (∑ j : Fin m, p j) = ContinuousLinearMap.id ℂ H
  refine op_ext_of_inner_self fun ξ => ?_
  rw [sum_apply, inner_sum]
  have hterm : ∀ j ∈ Finset.univ (α := Fin m),
      ⟪ξ, p j ξ⟫_ℂ = ((((boundedPVM hT).diag ξ) (I j)).toReal : ℂ) :=
    fun j _ => (boundedPVM hT).inner_proj (I j) (hImeas j) ξ
  rw [Finset.sum_congr rfl hterm]
  have hU : MeasurableSet (⋃ j ∈ Finset.univ (α := Fin m), I j) :=
    Finset.measurableSet_biUnion _ fun j _ => hImeas j
  have hmeasU : ((boundedPVM hT).diag ξ) (⋃ j ∈ Finset.univ (α := Fin m), I j) =
      ∑ j : Fin m, ((boundedPVM hT).diag ξ) (I j) := by
    refine measure_biUnion_finset ?_ fun j _ => hImeas j
    intro i _ j _ hij
    exact hIdisj i j hij
  have hUc : ((boundedPVM hT).diag ξ) (⋃ j ∈ Finset.univ (α := Fin m), I j)ᶜ = 0 := by
    rw [boundedPVM_diag hT ξ, Measure.map_apply (measurable_reCoord (T := T)) hU.compl]
    have hpre : reCoord (T := T) ⁻¹' (⋃ j ∈ Finset.univ (α := Fin m), I j)ᶜ =
        (∅ : Set (spectrum ℂ T)) := by
      ext w
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false,
        iff_false, not_not]
      obtain ⟨j, hj⟩ := hcover w
      exact Set.mem_biUnion (Finset.mem_univ j) hj
    rw [hpre]
    exact measure_empty
  have hUuniv : ((boundedPVM hT).diag ξ) (⋃ j ∈ Finset.univ (α := Fin m), I j) =
      ((boundedPVM hT).diag ξ) Set.univ := by
    rw [← measure_add_measure_compl hU, hUc, add_zero]
  have huniv : ⟪ξ, ContinuousLinearMap.id ℂ H ξ⟫_ℂ =
      ((((boundedPVM hT).diag ξ) Set.univ).toReal : ℂ) := by
    have h := (boundedPVM hT).inner_proj Set.univ MeasurableSet.univ ξ
    rwa [(boundedPVM hT).proj_univ] at h
  rw [huniv, ← hUuniv, hmeasU, ENNReal.toReal_sum (fun j _ => measure_ne_top _ _),
    Complex.ofReal_sum]

/-- **Almost-invariant finite-dimensional enlargement.**  Every finite-dimensional
subspace of a complex Hilbert space is contained in a finite-dimensional subspace that a
given bounded self-adjoint operator leaves invariant up to a prescribed tolerance: for
every `x` in the enlargement `F` there is `y ∈ F` with `‖T x - y‖ ≤ ε * ‖x‖`.

This is the selection step of the Davis--Kahan 1970 Appendix cutoff argument: the
enlargement is spanned by spectral-projection slices of a spanning set, so the operator
moves each slice within its own spectral band and the leakage out of the enlargement is
controlled by the band width. -/
theorem exists_finiteDimensional_le_almostInvariant (hT : IsSelfAdjoint T)
    (F₀ : Submodule ℂ H) [FiniteDimensional ℂ F₀] {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Submodule ℂ H, FiniteDimensional ℂ F ∧ F₀ ≤ F ∧
      ∀ x ∈ F, ∃ y ∈ F, ‖T x - y‖ ≤ ε * ‖x‖ := by
  classical
  rcases subsingleton_or_nontrivial H with hsub | hnontriv
  · refine ⟨F₀, inferInstance, le_rfl, fun x _ => ⟨0, Submodule.zero_mem _, ?_⟩⟩
    have hzero : T x - 0 = 0 := Subsingleton.elim _ _
    rw [hzero, norm_zero]
    positivity
  -- Geometry of the partition.
  set R : ℝ := ‖T‖ + 1 with hR_def
  have hR : 0 < R := by positivity
  set m : ℕ := max 1 ⌈2 * R / ε⌉₊ with hm_def
  have hm0 : 0 < m := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm0
  set d : ℝ := 2 * R / (m : ℝ) with hd_def
  have hd : 0 < d := div_pos (by positivity) hmR
  have hmd : (m : ℝ) * d = 2 * R := by
    rw [hd_def, mul_div_cancel₀ _ hmR.ne']
  have hdε : d ≤ ε := by
    rw [hd_def, div_le_iff₀ hmR]
    have hceil : 2 * R / ε ≤ (⌈2 * R / ε⌉₊ : ℝ) := Nat.le_ceil _
    have hcm : ((⌈2 * R / ε⌉₊ : ℕ) : ℝ) ≤ (m : ℝ) :=
      Nat.cast_le.mpr (le_max_right _ _)
    have h1 : 2 * R / ε ≤ (m : ℝ) := hceil.trans hcm
    calc 2 * R = ε * (2 * R / ε) := by field_simp
      _ ≤ ε * (m : ℝ) := mul_le_mul_of_nonneg_left h1 hε.le
  set I : Fin m → Set ℝ :=
    fun j => Set.Ico (-R + (j : ℕ) * d) (-R + ((j : ℕ) + 1) * d) with hI_def
  have hImeas : ∀ j, MeasurableSet (I j) := fun j => measurableSet_Ico
  set lam : Fin m → ℝ := fun j => -R + (j : ℕ) * d + d / 2 with hlam_def
  have hIband : ∀ j : Fin m, ∀ t ∈ I j, |t - lam j| ≤ d / 2 := by
    intro j t ht
    rcases ht with ⟨h1, h2⟩
    have h2' : t < -R + (j : ℕ) * d + d := by
      have heq : -R + ((j : ℕ) + 1) * d = -R + (j : ℕ) * d + d := by ring
      linarith [heq ▸ h2]
    rw [hlam_def, abs_le]
    constructor <;> [simp only; simp only] <;> linarith
  have hIdisj : ∀ i j : Fin m, i ≠ j → Disjoint (I i) (I j) := by
    have key : ∀ i j : Fin m, (i : ℕ) < (j : ℕ) → Disjoint (I i) (I j) := by
      intro i j hij
      rw [Set.disjoint_left]
      rintro t hti htj
      have hcast : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hij
      have hmul : (((i : ℕ) : ℝ) + 1) * d ≤ ((j : ℕ) : ℝ) * d :=
        mul_le_mul_of_nonneg_right hcast hd.le
      simp only [hI_def, Set.mem_Ico] at hti htj
      linarith [hti.2, htj.1]
    intro i j hij
    rcases lt_or_gt_of_ne (fun h => hij (Fin.ext h)) with h | h
    · exact key i j h
    · exact (key j i h).symm
  -- Spectral projections of the bands.
  set p : Fin m → (H →L[ℂ] H) :=
    fun j => (boundedPVM hT).proj (I j) (hImeas j) with hp_def
  have hpsa : ∀ j, IsSelfAdjoint (p j) := fun j =>
    (boundedPVM hT).isSelfAdjoint_proj (I j) (hImeas j)
  have hpp : ∀ i j : Fin m, i ≠ j → p i * p j = 0 := by
    intro i j hij
    rw [hp_def]
    rw [(boundedPVM hT).proj_inter (I i) (I j) (hImeas i) (hImeas j),
      (boundedPVM hT).proj_congr ((hIdisj i j hij).inter_eq)
        ((hImeas i).inter (hImeas j)) MeasurableSet.empty,
      (boundedPVM hT).proj_empty]
  have hidem : ∀ j : Fin m, p j * p j = p j := fun j =>
    (boundedPVM hT).proj_idem (I j) (hImeas j)
  have hcomm : ∀ j : Fin m, T * p j = p j * T := fun j =>
    boundedPVM_proj_comm hT (I j) (hImeas j)
  have hband : ∀ j : Fin m,
      ‖T ∘L p j - ((lam j : ℝ) : ℂ) • p j‖ ≤ d := by
    intro j
    have h := norm_comp_boundedPVM_proj_sub_smul_le hT (hImeas j)
      (by positivity : (0 : ℝ) ≤ d / 2) (hIband j)
    have h2 : 2 * (d / 2) = d := by ring
    rw [h2] at h
    exact h
  -- The spectrum is covered by the bands.
  have hcover : ∀ w : spectrum ℂ T, ∃ j : Fin m, reCoord (T := T) w ∈ I j := by
    intro w
    have habs : |reCoord (T := T) w| ≤ ‖T‖ := by
      rw [reCoord_apply]
      exact (Complex.abs_re_le_norm _).trans (spectrum.norm_le_norm_of_mem w.2)
    set t : ℝ := reCoord (T := T) w with ht_def
    have htR : -R < t ∧ t < R := by
      rw [abs_le] at habs
      constructor <;> [simp only [hR_def]; simp only [hR_def]] <;>
        linarith [habs.1, habs.2]
    exact mem_uniform_interval R d hd hmd htR
  -- The band projections sum to the identity.
  have hsum : (∑ j : Fin m, p j) = ContinuousLinearMap.id ℂ H :=
    sum_boundedPVM_proj_eq_id hT I hImeas hIdisj hcover
  -- The enlargement.
  obtain ⟨s, hs⟩ : F₀.FG := (Submodule.fg_iff_finiteDimensional F₀).mpr inferInstance
  set G : Set H := ⋃ j : Fin m, (p j) '' (↑s : Set H) with hG_def
  have hGfin : G.Finite := Set.finite_iUnion fun j => s.finite_toSet.image (p j)
  refine ⟨Submodule.span ℂ G, FiniteDimensional.span_of_finite ℂ hGfin, ?_, ?_⟩
  · -- `F₀ ≤ span G`.
    rw [← hs]
    refine Submodule.span_le.mpr fun x hx => ?_
    have hxsum : x = ∑ j : Fin m, p j x := by
      have h := congrArg (fun L : H →L[ℂ] H => L x) hsum
      simpa [sum_apply] using h.symm
    rw [hxsum]
    refine Submodule.sum_mem _ fun j _ => Submodule.subset_span ?_
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_image_of_mem _ hx⟩
  · -- Almost-invariance.
    -- Each band projection maps the enlargement into itself.
    have hinv : ∀ j : Fin m, ∀ x ∈ Submodule.span ℂ G, p j x ∈ Submodule.span ℂ G := by
      intro j x hx
      have hmapped : (p j : H →ₗ[ℂ] H) '' G ⊆ ↑(Submodule.span ℂ G) := by
        rintro _ ⟨y, hy, rfl⟩
        obtain ⟨j', z, hz, rfl⟩ : ∃ j' : Fin m, ∃ z ∈ (↑s : Set H), p j' z = y := by
          simpa only [hG_def, Set.mem_iUnion, Set.mem_image] using hy
        by_cases hjj : j = j'
        · subst hjj
          have hid : p j (p j z) = p j z := by
            have h := congrArg (fun L : H →L[ℂ] H => L z) (hidem j)
            simpa using h
          rw [ContinuousLinearMap.coe_coe, hid]
          exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨j, Set.mem_image_of_mem _ hz⟩)
        · have hz0 : p j (p j' z) = 0 := by
            have h := congrArg (fun L : H →L[ℂ] H => L z) (hpp j j' hjj)
            simpa using h
          rw [ContinuousLinearMap.coe_coe, hz0]
          exact Submodule.zero_mem _
      have hmap : (Submodule.span ℂ G).map (p j : H →ₗ[ℂ] H) ≤ Submodule.span ℂ G := by
        rw [Submodule.map_span]
        exact Submodule.span_le.mpr hmapped
      exact hmap ⟨x, hx, rfl⟩
    intro x hx
    -- Split `x` into its band components.
    have hxsum : ∑ j : Fin m, p j x = x := by
      have h := congrArg (fun L : H →L[ℂ] H => L x) hsum
      simpa [sum_apply] using h
    -- Band components of any pair of vectors are pairwise orthogonal.
    have horthog : ∀ u u' : H, ∀ i j : Fin m, i ≠ j → ⟪p i u, p j u'⟫_ℂ = 0 := by
      intro u u' i j hij
      have hadj : ⟪p i u, p j u'⟫_ℂ = ⟪u, p i (p j u')⟫_ℂ := by
        conv_lhs => rw [← (hpsa i).adjoint_eq]
        exact ContinuousLinearMap.adjoint_inner_left (p i) (p j u') u
      have hzero : p i (p j u') = 0 := by
        have h := congrArg (fun L : H →L[ℂ] H => L u') (hpp i j hij)
        simpa using h
      rw [hadj, hzero, inner_zero_right]
    -- The centered image of each band component.
    set w : Fin m → H := fun j => T (p j x) - ((lam j : ℝ) : ℂ) • p j x with hw_def
    have hwnorm : ∀ j : Fin m, ‖w j‖ ≤ d * ‖p j x‖ := by
      intro j
      have hidemx : p j (p j x) = p j x := by
        have h := congrArg (fun L : H →L[ℂ] H => L x) (hidem j)
        simpa using h
      have happly : (T ∘L p j - ((lam j : ℝ) : ℂ) • p j) (p j x) = w j := by
        simp only [sub_apply, ContinuousLinearMap.comp_apply, smul_apply, hidemx, hw_def]
      calc
        ‖w j‖ = ‖(T ∘L p j - ((lam j : ℝ) : ℂ) • p j) (p j x)‖ := by rw [happly]
        _ ≤ ‖T ∘L p j - ((lam j : ℝ) : ℂ) • p j‖ * ‖p j x‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ d * ‖p j x‖ := mul_le_mul_of_nonneg_right (hband j) (norm_nonneg _)
    -- Each centered image lies in its own band range.
    have hwproj : ∀ j : Fin m, w j = p j (T x - ((lam j : ℝ) : ℂ) • x) := by
      intro j
      have hTp : T (p j x) = p j (T x) := by
        have h := congrArg (fun L : H →L[ℂ] H => L x) (hcomm j)
        simpa using h
      rw [hw_def]
      simp only [map_sub, map_smul, hTp]
    have hworthog : ∀ i j : Fin m, i ≠ j → ⟪w i, w j⟫_ℂ = 0 := by
      intro i j hij
      rw [hwproj i, hwproj j]
      exact horthog _ _ i j hij
    -- Pythagoras on both decompositions.
    have hpyth_w : ‖∑ j : Fin m, w j‖ ^ 2 = ∑ j : Fin m, ‖w j‖ ^ 2 :=
      norm_sq_sum_of_pairwise_inner_eq_zero Finset.univ w
        (fun i _ j _ hij => hworthog i j hij)
    have hpyth_x : ∑ j : Fin m, ‖p j x‖ ^ 2 = ‖x‖ ^ 2 := by
      have h := norm_sq_sum_of_pairwise_inner_eq_zero Finset.univ (fun j => p j x)
        (fun i _ j _ hij => horthog x x i j hij)
      rw [← h, hxsum]
    -- The comparison vector inside the enlargement.
    refine ⟨∑ j : Fin m, ((lam j : ℝ) : ℂ) • p j x,
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hinv j x hx), ?_⟩
    have hTxy : T x - ∑ j : Fin m, ((lam j : ℝ) : ℂ) • p j x = ∑ j : Fin m, w j := by
      have hTx : T x = ∑ j : Fin m, T (p j x) := by
        conv_lhs => rw [← hxsum]
        rw [map_sum]
      rw [hTx, ← Finset.sum_sub_distrib]
    rw [hTxy]
    -- Assemble.
    have hnorm_sq : ‖∑ j : Fin m, w j‖ ^ 2 ≤ (d * ‖x‖) ^ 2 := by
      rw [hpyth_w]
      calc
        ∑ j : Fin m, ‖w j‖ ^ 2 ≤ ∑ j : Fin m, (d * ‖p j x‖) ^ 2 :=
          Finset.sum_le_sum fun j _ =>
            pow_le_pow_left₀ (norm_nonneg _) (hwnorm j) 2
        _ = d ^ 2 * ∑ j : Fin m, ‖p j x‖ ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
        _ = (d * ‖x‖) ^ 2 := by rw [hpyth_x]; ring
    have hnorm : ‖∑ j : Fin m, w j‖ ≤ d * ‖x‖ := by
      have hd0 : 0 ≤ d * ‖x‖ := by positivity
      nlinarith [norm_nonneg (∑ j : Fin m, w j)]
    calc
      ‖∑ j : Fin m, w j‖ ≤ d * ‖x‖ := hnorm
      _ ≤ ε * ‖x‖ := mul_le_mul_of_nonneg_right hdε (norm_nonneg _)

end BoundedSelfAdjoint

end BorelCalculus
end TauCeti
