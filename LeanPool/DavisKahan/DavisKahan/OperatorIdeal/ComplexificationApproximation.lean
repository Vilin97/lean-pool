/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.PartialMap.Complexification
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric

/-!
# Approximation-number transport through real complexification

A bounded real operator and its coordinatewise complexification have the same
approximation singular values.  The upper inequality complexifies finite-rank
approximants.  The lower inequality uses the real finite-dimensional min--max
witness and complexifies its linearly independent family without changing its
cardinality or lower modulus.

Consequently every finite Ky Fan gauge is preserved exactly.  This is the
scalar bridge needed to apply a complex Sylvester theorem at each finite Ky Fan
gauge and descend the resulting majorization through an arbitrary real
Ky-Fan-dominant unitarily invariant ideal family.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta
namespace ComplexificationApproximation

open scoped InnerProductSpace
open TauCeti.RealComplexification
-- the namespace is split across the two libraries: `Basic` is in `ForTauCeti`, `Subspace` here
open TauCeti.DavisKahan.Foundation.RealComplexification

noncomputable section

universe v vF

variable {E : Type v} {F : Type vF}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The range of a complexified operator is the complexification of its real
range. -/
theorem range_complexify
    (T : E →L[ℝ] F) :
    LinearMap.range (RealComplexification.complexify T).toLinearMap =
      complexifySubmodule (LinearMap.range T.toLinearMap) := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    rw [mem_complexifySubmodule]
    exact ⟨⟨re w, rfl⟩, ⟨im w, rfl⟩⟩
  · intro hz
    rw [mem_complexifySubmodule] at hz
    rcases hz with ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    refine ⟨mk x y, ?_⟩
    apply RealComplexification.ext
    · simpa using hx
    · simpa using hy

/-- The real coordinate map commutes with finite sums. -/
theorem re_sum {V : Type*} [AddCommGroup V] {κ : Type*} (s : Finset κ)
    (f : κ → RealComplexification V) :
    re (∑ j ∈ s, f j) = ∑ j ∈ s, re (f j) :=
  map_sum ({ toFun := re, map_zero' := rfl, map_add' := fun _ _ => rfl } :
    RealComplexification V →+ V) f s

/-- The imaginary coordinate map commutes with finite sums. -/
theorem im_sum {V : Type*} [AddCommGroup V] {κ : Type*} (s : Finset κ)
    (f : κ → RealComplexification V) :
    im (∑ j ∈ s, f j) = ∑ j ∈ s, im (f j) :=
  map_sum ({ toFun := im, map_zero' := rfl, map_add' := fun _ _ => rfl } :
    RealComplexification V →+ V) f s

/-- A basis of a real space gives a complex basis of its concrete
complexification by embedding every basis vector in the real copy. -/
noncomputable def complexificationBasis {ι : Type*}
    {V : Type v} [AddCommGroup V] [Module ℝ V]
    (b : Module.Basis ι ℝ V) :
    Module.Basis ι ℂ (RealComplexification V) := by
  classical
  refine Module.Basis.mk (v := fun i => mk (b i) 0) ?_ ?_
  · rw [linearIndependent_iff']
    intro s l hs i hi
    have hre' : ∑ j ∈ s, (l j).re • b j = 0 := by
      have h := congrArg re hs
      rw [re_sum] at h
      simpa using h
    have him' : ∑ j ∈ s, (l j).im • b j = 0 := by
      have h := congrArg im hs
      rw [im_sum] at h
      simpa using h
    have hr := (linearIndependent_iff'.mp b.linearIndependent)
      s (fun j => (l j).re) hre' i hi
    have hii := (linearIndependent_iff'.mp b.linearIndependent)
      s (fun j => (l j).im) him' i hi
    refine Complex.ext ?_ ?_
    · simpa using hr
    · simpa using hii
  · intro z _
    have realCopy_mem (x : V) :
        mk x (0 : V) ∈ Submodule.span ℂ (Set.range fun i => mk (b i) (0 : V)) := by
      have hx : x ∈ Submodule.span ℝ (Set.range b) := by
        rw [b.span_eq]
        exact Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        exact Submodule.subset_span ⟨i, rfl⟩
      | zero =>
        have hzero : mk (0 : V) (0 : V) = 0 := by
          apply RealComplexification.ext <;> simp
        rw [hzero]
        exact Submodule.zero_mem _
      | add x y _ _ ihx ihy =>
        have hadd : mk (x + y) (0 : V) = mk x (0 : V) + mk y (0 : V) := by
          apply RealComplexification.ext <;> simp
        rw [hadd]
        exact Submodule.add_mem _ ihx ihy
      | smul r x _ ih =>
        have hsmul : mk (r • x) (0 : V) = (r : ℂ) • mk x (0 : V) := by
          apply RealComplexification.ext <;>
            simp only [re_mk, im_mk, re_complex_smul, im_complex_smul,
              Complex.ofReal_re, Complex.ofReal_im, zero_smul, smul_zero,
              sub_zero, add_zero]
        rw [hsmul]
        exact Submodule.smul_mem _ _ ih
    have hz : z = mk (re z) (0 : V) + Complex.I • mk (im z) (0 : V) := by
      apply RealComplexification.ext <;> simp
    rw [hz]
    exact Submodule.add_mem _ (realCopy_mem (re z))
      (Submodule.smul_mem _ Complex.I (realCopy_mem (im z)))

/-- Complexification does not change module dimension. -/
theorem rank_complexification
    {V : Type v} [AddCommGroup V] [Module ℝ V] :
    Module.rank ℂ (RealComplexification V) = Module.rank ℝ V := by
  classical
  let b := Module.Free.chooseBasis ℝ V
  calc
    Module.rank ℂ (RealComplexification V) =
        Cardinal.mk (Module.Free.ChooseBasisIndex ℝ V) :=
      by simpa using (complexificationBasis b).mk_eq_rank.symm
    _ = Module.rank ℝ V := by simpa using b.mk_eq_rank

omit [CompleteSpace E] in
/-- Complexifying a real submodule preserves its dimension. -/
theorem rank_complexifySubmodule
    (U : Submodule ℝ E) :
    Module.rank ℂ (complexifySubmodule U) = Module.rank ℝ U := by
  let e : RealComplexification U ≃ₗ[ℂ] complexifySubmodule U :=
    { toFun := fun z =>
        ⟨mk ((re z : U) : E) ((im z : U) : E), by
          rw [mem_complexifySubmodule]
          exact ⟨(re z : U).property, (im z : U).property⟩⟩
      invFun := fun z => mk
        ⟨re (z : RealComplexification E),
          (mem_complexifySubmodule.mp z.property).1⟩
        ⟨im (z : RealComplexification E),
          (mem_complexifySubmodule.mp z.property).2⟩
      left_inv := fun z => by apply RealComplexification.ext <;> rfl
      right_inv := fun z => by apply Subtype.ext; apply RealComplexification.ext <;> rfl
      map_add' := fun z w => by apply Subtype.ext; apply RealComplexification.ext <;> simp
      map_smul' := fun c z => by apply Subtype.ext; apply RealComplexification.ext <;> simp }
  calc
    Module.rank ℂ (complexifySubmodule U) =
        Module.rank ℂ (RealComplexification U) := e.rank_eq.symm
    _ = Module.rank ℝ U := rank_complexification

omit [CompleteSpace E] [CompleteSpace F] in
/-- Complexification preserves the rank of a bounded operator. -/
theorem rank_complexify
    (T : E →L[ℝ] F) :
    (RealComplexification.complexify T).rank = T.rank := by
  change Module.rank ℂ (LinearMap.range
      (RealComplexification.complexify T).toLinearMap) =
    Module.rank ℝ (LinearMap.range T.toLinearMap)
  rw [range_complexify, rank_complexifySubmodule]

omit [CompleteSpace E] in
/-- A real linearly independent family remains complex linearly independent in
the real copy of the complexification. -/
theorem linearIndependent_ofReal
    {ι : Type*} {v : ι → E} (hv : LinearIndependent ℝ v) :
    LinearIndependent ℂ (fun i => ofReal (v i)) := by
  rw [linearIndependent_iff']
  intro s l hs i hi
  have hre' : ∑ j ∈ s, (l j).re • v j = 0 := by
    have h := congrArg re hs
    rw [re_sum] at h
    simpa using h
  have him' : ∑ j ∈ s, (l j).im • v j = 0 := by
    have h := congrArg im hs
    rw [im_sum] at h
    simpa using h
  have hr := (linearIndependent_iff'.mp hv)
    s (fun j => (l j).re) hre' i hi
  have hii := (linearIndependent_iff'.mp hv)
    s (fun j => (l j).im) him' i hi
  refine Complex.ext ?_ ?_
  · simpa using hr
  · simpa using hii

omit [CompleteSpace E] in
/-- The complex span of real copies has real and imaginary coordinates in the
corresponding real span. -/
theorem coordinates_mem_real_span
    {ι : Type*} [Fintype ι] (v : ι → E)
    {z : RealComplexification E}
    (hz : z ∈ Submodule.span ℂ (Set.range fun i => ofReal (v i))) :
    re z ∈ Submodule.span ℝ (Set.range v) ∧
      im z ∈ Submodule.span ℝ (Set.range v) := by
  induction hz using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    exact ⟨Submodule.subset_span ⟨i, rfl⟩, by simp⟩
  | zero => exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
  | add x y _ _ ihx ihy =>
    exact ⟨Submodule.add_mem _ ihx.1 ihy.1,
      Submodule.add_mem _ ihx.2 ihy.2⟩
  | smul c x _ ih =>
    exact ⟨
      Submodule.sub_mem _
        (Submodule.smul_mem _ c.re ih.1)
        (Submodule.smul_mem _ c.im ih.2),
      Submodule.add_mem _
        (Submodule.smul_mem _ c.im ih.1)
        (Submodule.smul_mem _ c.re ih.2)⟩

omit [CompleteSpace E] [CompleteSpace F] in
/-- A real lower modulus on a real span becomes the same complex lower modulus
on the complex span. -/
theorem lowerBound_complex_span
    {ι : Type*} [Fintype ι]
    (T : E →L[ℝ] F) (v : ι → E) {s : ℝ} (hs : 0 ≤ s)
    (hV : ∀ x ∈ Submodule.span ℝ (Set.range v),
      s * ‖x‖ ≤ ‖T x‖) :
    ∀ z ∈ Submodule.span ℂ (Set.range fun i => ofReal (v i)),
      s * ‖z‖ ≤ ‖RealComplexification.complexify T z‖ := by
  intro z hz
  have hcoord := coordinates_mem_real_span v hz
  have hr := hV (re z) hcoord.1
  have hi := hV (im z) hcoord.2
  rw [← sq_le_sq₀ (mul_nonneg hs (norm_nonneg _)) (norm_nonneg _)]
  rw [RealComplexification.norm_sq, mul_pow,
    RealComplexification.norm_sq]
  have hrsq : s ^ 2 * ‖re z‖ ^ 2 ≤ ‖T (re z)‖ ^ 2 := by
    have h := pow_le_pow_left₀ (mul_nonneg hs (norm_nonneg (re z))) hr 2
    rwa [mul_pow] at h
  have hisq : s ^ 2 * ‖im z‖ ^ 2 ≤ ‖T (im z)‖ ^ 2 := by
    have h := pow_le_pow_left₀ (mul_nonneg hs (norm_nonneg (im z))) hi 2
    rwa [mul_pow] at h
  change s ^ 2 * (‖re z‖ ^ 2 + ‖im z‖ ^ 2) ≤
    ‖T (re z)‖ ^ 2 + ‖T (im z)‖ ^ 2
  nlinarith

omit [CompleteSpace E] [CompleteSpace F] in
/-- Complexification cannot increase an approximation number: complexify a
near-optimal real approximant and preserve both its rank and error norm. -/
theorem approximationNumber_complexify_le
    (T : E →L[ℝ] F) (n : ℕ) :
    (RealComplexification.complexify T).approximationNumber n ≤
      T.approximationNumber n := by
  rw [T.approximationNumber_eq_iInf]
  apply le_ciInf
  rintro ⟨R, hR⟩
  have hRc : (RealComplexification.complexify R).rank ≤ (n : Cardinal) := by
    rw [rank_complexify]
    exact hR
  calc
    (RealComplexification.complexify T).approximationNumber n ≤
        ‖RealComplexification.complexify T -
          RealComplexification.complexify R‖ :=
      (RealComplexification.complexify T).approximationNumber_le_norm_sub hRc
    _ = ‖T - R‖ := by
      rw [← RealComplexification.complexify_sub,
        RealComplexification.norm_complexify]

/-- The real approximation number cannot exceed the complexified one.  A strict
real lower threshold supplies an `(n+1)`-vector min--max witness, and that
witness complexifies with the same lower modulus. -/
theorem approximationNumber_le_complexify
    (T : E →L[ℝ] F) (n : ℕ) :
    T.approximationNumber n ≤
      (RealComplexification.complexify T).approximationNumber n := by
  apply le_of_forall_lt
  intro r hr
  by_cases hr0 : 0 ≤ r
  case neg =>
    exact (lt_of_not_ge hr0).trans_le
      (ContinuousLinearMap.approximationNumber_nonneg _ n)
  obtain ⟨s, hrs, v, hv, hV⟩ :=
    TauCeti.ApproximationNumber.exists_linearIndependent_lowerBound_of_lt_approximationNumber_real
      T n hr0 hr
  have hs0 : 0 ≤ s := hr0.trans hrs.le
  have hvC : LinearIndependent ℂ (fun i => ofReal (v i)) :=
    linearIndependent_ofReal hv
  have hlower := lowerBound_complex_span T v hs0 hV
  have hsNN : s ≤
      (RealComplexification.complexify T).approximationNumber n := by
    apply ContinuousLinearMap.le_approximationNumber_of_linearIndependent
      (RealComplexification.complexify T) n (fun i => ofReal (v i)) hvC
    intro z hz hnorm
    change s ≤ ‖RealComplexification.complexify T z‖
    calc
      s = s * ‖z‖ := by rw [hnorm, mul_one]
      _ ≤ ‖RealComplexification.complexify T z‖ := hlower z hz
  have hrsNN : r < (⟨s, hs0⟩ : NNReal) := by
    exact_mod_cast hrs
  exact hrsNN.trans_le hsNN

/-- Approximation numbers are exactly preserved by real complexification. -/
theorem approximationNumber_complexify
    (T : E →L[ℝ] F) (n : ℕ) :
    (RealComplexification.complexify T).approximationNumber n =
      T.approximationNumber n :=
  le_antisymm (approximationNumber_complexify_le T n)
    (approximationNumber_le_complexify T n)

/-- Approximation singular values are exactly preserved by real
complexification. -/
theorem approximationSingularValue_complexify
    (T : E →L[ℝ] F) (n : ℕ) :
    approximationSingularValue n (RealComplexification.complexify T) =
      approximationSingularValue n T := by
  exact approximationNumber_complexify T n

/-- Every finite Ky Fan approximation gauge is exactly preserved by real
complexification. -/
theorem kyFanApproximationGauge_complexify
    (T : E →L[ℝ] F) (k : ℕ) :
    kyFanApproximationGauge k (RealComplexification.complexify T) =
      kyFanApproximationGauge k T := by
  unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
  apply Finset.sum_congr rfl
  intro n hn
  exact approximationSingularValue_complexify T n

end

end ComplexificationApproximation
end ExactSinTheta
end DavisKahan
end TauCeti
