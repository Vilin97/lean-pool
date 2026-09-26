/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Probability.IndependentSums.Rosenthal.Symmetric

/-! # Symmetrization -/

@[expose] public section

namespace Homogenization
namespace IndependentSums

open MeasureTheory ProbabilityTheory
open Set
open scoped Topology

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- First symmetrization step for Rosenthal's inequality: the absolute `L^p`
norm of the centered finite sum is bounded by the corresponding `L^p` norm of
the symmetrized difference sum on the product probability space. -/
theorem integral_abs_centeredFinsetSum_pow_le_integral_abs_symmetrizedFinsetSum_pow
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {p : ℕ}
    (hp : 1 ≤ p)
    (hX_int : ∀ i ∈ s, Integrable (X i) μ)
    (hsymm_int :
      Integrable (fun ω : Ω × Ω => |symmetrizedFinsetSum X s ω| ^ p) (μ.prod μ)) :
    ∫ ω, |centeredFinsetSum X μ s ω| ^ p ∂μ ≤
      ∫ ω : Ω × Ω, |symmetrizedFinsetSum X s ω| ^ p ∂(μ.prod μ) := by
  have hp_pos : 0 < p := Nat.succ_le_iff.mp hp
  let F : Ω → Ω → ℝ := fun x y => symmetrizedFinsetSum X s (x, y)
  have hconv :
      ConvexOn ℝ Set.univ (fun t : ℝ => ‖t‖ ^ p) := by
    simpa using!
      (convexOn_univ_norm : ConvexOn ℝ Set.univ (norm : ℝ → ℝ)).pow
        (fun _ _ => norm_nonneg _) p
  have hcont :
      ContinuousOn (fun t : ℝ => ‖t‖ ^ p) Set.univ :=
    (continuous_norm.pow p).continuousOn
  have hF_int : Integrable (Function.uncurry F) (μ.prod μ) := by
    change Integrable (symmetrizedFinsetSum X s) (μ.prod μ)
    refine integrable_finsetSum s ?_
    intro i hi
    exact ((hX_int i hi).comp_fst μ).sub ((hX_int i hi).comp_snd μ)
  have hF_int_right : ∀ x, Integrable (fun y => F x y) μ := by
    intro x
    refine integrable_finsetSum s ?_
    intro i hi
    exact (integrable_const (X i x)).sub (hX_int i hi)
  have hF_integral :
      ∀ x, ∫ y, F x y ∂μ = centeredFinsetSum X μ s x := by
    intro x
    change ∫ y, ∑ i ∈ s, (X i x - X i y) ∂μ = centeredFinsetSum X μ s x
    rw [centeredFinsetSum, integral_finsetSum]
    · refine Finset.sum_congr rfl ?_
      intro i hi
      rw [integral_sub (integrable_const _) (hX_int i hi), integral_const]
      simp
    · intro i hi
      exact (integrable_const (X i x)).sub (hX_int i hi)
  have hjensen :
      ∀ᵐ x ∂μ, |∫ y, F x y ∂μ| ^ p ≤ ∫ y, |F x y| ^ p ∂μ := by
    filter_upwards [hsymm_int.prod_right_ae] with x hx
    have hmem : ∀ᵐ y ∂μ, F x y ∈ (Set.univ : Set ℝ) := by
      exact Filter.Eventually.of_forall (fun _ => Set.mem_univ _)
    have hpoint :=
      hconv.map_integral_le
        hcont
        isClosed_univ
        hmem
        (hF_int_right x)
        (by simpa [F, symmetrizedFinsetSum, Real.norm_eq_abs] using! hx)
    simpa [Real.norm_eq_abs] using hpoint
  have hright_int :
      Integrable (fun x => ∫ y, |F x y| ^ p ∂μ) μ := by
    simpa [Function.uncurry, F, symmetrizedFinsetSum] using hsymm_int.integral_prod_left
  have hleft_ae :
      AEStronglyMeasurable (fun x => |∫ y, F x y ∂μ| ^ p) μ := by
    simpa [Function.uncurry, F, Real.norm_eq_abs] using!
      (hF_int.integral_prod_left.aestronglyMeasurable.norm.pow p)
  have hleft_int :
      Integrable (fun x => |∫ y, F x y ∂μ| ^ p) μ := by
    refine hright_int.mono' hleft_ae ?_
    filter_upwards [hjensen] with x hx
    simpa using hx
  calc
    ∫ ω, |centeredFinsetSum X μ s ω| ^ p ∂μ
      = ∫ x, |∫ y, F x y ∂μ| ^ p ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun x => by simp [hF_integral x])
    _ ≤ ∫ x, ∫ y, |F x y| ^ p ∂μ ∂μ := by
          exact integral_mono_ae hleft_int hright_int hjensen
    _ = ∫ ω : Ω × Ω, |symmetrizedFinsetSum X s ω| ^ p ∂(μ.prod μ) := by
          have hpowF_int :
              Integrable (Function.uncurry (fun x y => |F x y| ^ p)) (μ.prod μ) := by
            simpa [Function.uncurry, F, symmetrizedFinsetSum] using! hsymm_int
          simpa [Function.uncurry, F, symmetrizedFinsetSum] using
            (integral_integral (f := fun x y => |F x y| ^ p) hpowF_int)

section

omit [MeasurableSpace Ω]

/-- Pointwise `L^p` control of the symmetrized finite sum by the two coordinate
copies of the original finite sum. -/
theorem abs_symmetrizedFinsetSum_pow_le
    {X : ι → Ω → ℝ} {s : Finset ι} {p : ℕ} (ω : Ω × Ω) :
    |symmetrizedFinsetSum X s ω| ^ p ≤
      (2 ^ (p - 1) : ℝ) *
        (|∑ i ∈ s, X i ω.1| ^ p + |∑ i ∈ s, X i ω.2| ^ p) := by
  let A : ℝ := ∑ i ∈ s, X i ω.1
  let B : ℝ := ∑ i ∈ s, X i ω.2
  have hsymm : symmetrizedFinsetSum X s ω = A - B := by
    simp [symmetrizedFinsetSum, A, B, Finset.sum_sub_distrib]
  have habs : |A - B| ≤ |A| + |B| := by
    simpa [sub_eq_add_neg] using abs_add_le A (-B)
  have hpow :
      |A - B| ^ p ≤ (|A| + |B|) ^ p := by
    exact pow_le_pow_left₀ (abs_nonneg _) habs p
  have hadd :
      (|A| + |B|) ^ p ≤ (2 ^ (p - 1) : ℝ) * (|A| ^ p + |B| ^ p) := by
    exact add_pow_le (abs_nonneg A) (abs_nonneg B) p
  rw [hsymm]
  exact le_trans hpow hadd

end

/-- Integrability of the symmetrized `p`-moment follows from integrability of
the original finite-sum `p`-moment. -/
theorem integrable_abs_symmetrizedFinsetSum_pow_of_integrable_abs_finsetSum_pow
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {p : ℕ}
    (hX_meas : ∀ i ∈ s, Measurable (X i))
    (hsum_int : Integrable (fun ω => |∑ i ∈ s, X i ω| ^ p) μ) :
    Integrable (fun ω : Ω × Ω => |symmetrizedFinsetSum X s ω| ^ p) (μ.prod μ) := by
  let G : Ω × Ω → ℝ := fun ω =>
    (2 ^ (p - 1) : ℝ) * (|∑ i ∈ s, X i ω.1| ^ p + |∑ i ∈ s, X i ω.2| ^ p)
  have hfst : Integrable (fun ω : Ω × Ω => |∑ i ∈ s, X i ω.1| ^ p) (μ.prod μ) :=
    hsum_int.comp_fst μ
  have hsnd : Integrable (fun ω : Ω × Ω => |∑ i ∈ s, X i ω.2| ^ p) (μ.prod μ) :=
    hsum_int.comp_snd μ
  have hG_int : Integrable G (μ.prod μ) := by
    simpa [G] using (hfst.add hsnd).const_mul ((2 ^ (p - 1) : ℕ) : ℝ)
  have hsymm_meas : Measurable (symmetrizedFinsetSum X s) := by
    refine Finset.measurable_sum s ?_
    intro i hi
    exact ((hX_meas i hi).comp measurable_fst).sub ((hX_meas i hi).comp measurable_snd)
  have hsymm_ae :
      AEStronglyMeasurable (fun ω : Ω × Ω => |symmetrizedFinsetSum X s ω| ^ p) (μ.prod μ) := by
    simpa [Real.norm_eq_abs] using
      ((hsymm_meas.aemeasurable.norm.pow_const p).aestronglyMeasurable)
  refine hG_int.mono' hsymm_ae ?_
  filter_upwards with ω
  have hω := abs_symmetrizedFinsetSum_pow_le (X := X) (s := s) (p := p) ω
  have hnonneg : 0 ≤ |symmetrizedFinsetSum X s ω| ^ p := by positivity
  simpa [G, Real.norm_eq_abs, abs_of_nonneg hnonneg] using hω

/-- Product-space `L^p` control of the symmetrized finite sum by the original
finite sum. This is the note-facing symmetrization estimate with the standard
`2^p` factor. -/
theorem integral_abs_symmetrizedFinsetSum_pow_le_two_pow_mul_integral_abs_finsetSum_pow
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {p : ℕ}
    (hp : 1 ≤ p)
    (hX_meas : ∀ i ∈ s, Measurable (X i))
    (hsum_int : Integrable (fun ω => |∑ i ∈ s, X i ω| ^ p) μ) :
    ∫ ω : Ω × Ω, |symmetrizedFinsetSum X s ω| ^ p ∂(μ.prod μ) ≤
      (2 : ℝ) ^ p * ∫ ω, |∑ i ∈ s, X i ω| ^ p ∂μ := by
  let S : Ω → ℝ := fun ω => ∑ i ∈ s, X i ω
  let G : Ω × Ω → ℝ := fun ω =>
    (2 ^ (p - 1) : ℝ) * (|S ω.1| ^ p + |S ω.2| ^ p)
  have hsymm_int :
      Integrable (fun ω : Ω × Ω => |symmetrizedFinsetSum X s ω| ^ p) (μ.prod μ) :=
    integrable_abs_symmetrizedFinsetSum_pow_of_integrable_abs_finsetSum_pow
      (μ := μ) hX_meas hsum_int
  have hfst : Integrable (fun ω : Ω × Ω => |S ω.1| ^ p) (μ.prod μ) :=
    hsum_int.comp_fst μ
  have hsnd : Integrable (fun ω : Ω × Ω => |S ω.2| ^ p) (μ.prod μ) :=
    hsum_int.comp_snd μ
  have hG_int : Integrable G (μ.prod μ) := by
    simpa [G] using (hfst.add hsnd).const_mul ((2 ^ (p - 1) : ℕ) : ℝ)
  have hpoint :
      ∀ᵐ ω : Ω × Ω ∂(μ.prod μ),
        |symmetrizedFinsetSum X s ω| ^ p ≤ G ω :=
    Filter.Eventually.of_forall fun ω => by
      simpa [G, S] using abs_symmetrizedFinsetSum_pow_le (X := X) (s := s) (p := p) ω
  have hS_meas : Measurable S := by
    refine Finset.measurable_sum s ?_
    intro i hi
    exact hX_meas i hi
  have hid :
      IdentDistrib
        (fun ω : Ω × Ω => |S ω.1| ^ p)
        (fun ω : Ω × Ω => |S ω.2| ^ p)
    (μ.prod μ)
        (μ.prod μ) := by
    simpa [S, Function.comp_def] using
      (identDistrib_comp_fst_comp_snd_prod (μ := μ) (X := S) hS_meas.aemeasurable).comp
        (continuous_abs.measurable.pow_const p)
  have hfst_eq :
      ∫ ω : Ω × Ω, |S ω.1| ^ p ∂(μ.prod μ) = ∫ ω, |S ω| ^ p ∂μ := by
    simpa [S] using
      (integral_fun_fst (μ := μ) (ν := μ) (f := fun ω : Ω => |S ω| ^ p))
  have hsnd_eq : ∫ ω : Ω × Ω, |S ω.2| ^ p ∂(μ.prod μ) = ∫ ω : Ω × Ω, |S ω.1| ^ p ∂(μ.prod μ) := by
    simpa using hid.integral_eq.symm
  have hpow_two : (2 : ℝ) ^ (p - 1) * 2 = (2 : ℝ) ^ p := by
    rcases Nat.exists_eq_add_of_le hp with ⟨n, rfl⟩
    simpa [Nat.add_comm, mul_comm] using (pow_succ' (2 : ℝ) n).symm
  calc
    ∫ ω : Ω × Ω, |symmetrizedFinsetSum X s ω| ^ p ∂(μ.prod μ)
        ≤ ∫ ω : Ω × Ω, G ω ∂(μ.prod μ) := by
            exact integral_mono_ae hsymm_int hG_int hpoint
    _ = (2 ^ (p - 1) : ℝ) *
          (∫ ω : Ω × Ω, |S ω.1| ^ p ∂(μ.prod μ) +
            ∫ ω : Ω × Ω, |S ω.2| ^ p ∂(μ.prod μ)) := by
          rw [show (∫ ω : Ω × Ω, G ω ∂(μ.prod μ)) =
            ∫ ω : Ω × Ω,
              (2 ^ (p - 1) : ℝ) * (|S ω.1| ^ p + |S ω.2| ^ p) ∂(μ.prod μ) by rfl]
          rw [integral_const_mul]
          congr 1
          exact integral_add hfst hsnd
    _ = (2 ^ (p - 1) : ℝ) *
          (2 * ∫ ω, |S ω| ^ p ∂μ) := by
          rw [hsnd_eq, two_mul, hfst_eq]
    _ = (2 : ℝ) ^ p * ∫ ω, |S ω| ^ p ∂μ := by
          calc
            (2 ^ (p - 1) : ℝ) * (2 * ∫ ω, |S ω| ^ p ∂μ)
                = (((2 : ℝ) ^ (p - 1)) * 2) * ∫ ω, |S ω| ^ p ∂μ := by
                    ring_nf
            _ = (2 : ℝ) ^ p * ∫ ω, |S ω| ^ p ∂μ := by rw [hpow_two]
    _ = (2 : ℝ) ^ p * ∫ ω, |∑ i ∈ s, X i ω| ^ p ∂μ := by
          rfl

/-- Moment symmetrization inequality for the centered finite sum. -/
theorem integral_abs_centeredFinsetSum_pow_le_two_pow_mul_integral_abs_finsetSum_pow
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {p : ℕ}
    (hp : 1 ≤ p)
    (hX_meas : ∀ i ∈ s, Measurable (X i))
    (hX_int : ∀ i ∈ s, Integrable (X i) μ)
    (hsum_int : Integrable (fun ω => |∑ i ∈ s, X i ω| ^ p) μ) :
    ∫ ω, |centeredFinsetSum X μ s ω| ^ p ∂μ ≤
      (2 : ℝ) ^ p * ∫ ω, |∑ i ∈ s, X i ω| ^ p ∂μ := by
  have hsymm_int :
      Integrable (fun ω : Ω × Ω => |symmetrizedFinsetSum X s ω| ^ p) (μ.prod μ) :=
    integrable_abs_symmetrizedFinsetSum_pow_of_integrable_abs_finsetSum_pow
      (μ := μ) hX_meas hsum_int
  exact
    (integral_abs_centeredFinsetSum_pow_le_integral_abs_symmetrizedFinsetSum_pow
      (μ := μ) (X := X) (s := s) (p := p) hp hX_int hsymm_int).trans
      (integral_abs_symmetrizedFinsetSum_pow_le_two_pow_mul_integral_abs_finsetSum_pow
        (μ := μ) (X := X) (s := s) (p := p) hp hX_meas hsum_int)

/-- First symmetrization step for real `L^p` exponents. -/
theorem integral_abs_centeredFinsetSum_rpow_le_integral_abs_symmetrizedFinsetSum_rpow
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {p : ℝ}
    (hp : 1 ≤ p)
    (hX_int : ∀ i ∈ s, Integrable (X i) μ)
    (hsymm_int :
      Integrable (fun ω : Ω × Ω => |symmetrizedFinsetSum X s ω| ^ p) (μ.prod μ)) :
    ∫ ω, |centeredFinsetSum X μ s ω| ^ p ∂μ ≤
      ∫ ω : Ω × Ω, |symmetrizedFinsetSum X s ω| ^ p ∂(μ.prod μ) := by
  have hp_nonneg : 0 ≤ p := le_trans zero_le_one hp
  let F : Ω → Ω → ℝ := fun x y => symmetrizedFinsetSum X s (x, y)
  have hconv :
      ConvexOn ℝ Set.univ (fun t : ℝ => |t| ^ p) := by
    have hnorm : ConvexOn ℝ Set.univ (fun t : ℝ => |t|) := by
      simpa [Real.norm_eq_abs] using!
        (convexOn_univ_norm : ConvexOn ℝ Set.univ (norm : ℝ → ℝ))
    have hrpow : ConvexOn ℝ (Set.Ici 0) (fun t : ℝ => t ^ p) := convexOn_rpow hp
    have hmono : MonotoneOn (fun t : ℝ => t ^ p) (Set.Ici 0) := by
      intro a ha b hb hab
      exact Real.rpow_le_rpow ha hab hp_nonneg
    have himage : (fun t : ℝ => |t|) '' Set.univ ⊆ Set.Ici 0 := by
      rintro t ⟨u, -, rfl⟩
      exact abs_nonneg u
    have himage_convex : Convex ℝ ((fun t : ℝ => |t|) '' Set.univ) := by
      have heq : (fun t : ℝ => |t|) '' Set.univ = Set.Ici 0 := by
        ext t
        simp only [Set.mem_image, Set.mem_univ, true_and, Set.mem_Ici]
        constructor
        · rintro ⟨u, rfl⟩
          exact abs_nonneg u
        · intro ht
          exact ⟨t, abs_of_nonneg ht⟩
      rw [heq]
      exact convex_Ici 0
    exact (hrpow.subset himage himage_convex).comp hnorm (hmono.mono himage)
  have hcont :
      ContinuousOn (fun t : ℝ => |t| ^ p) Set.univ := by
    exact (continuous_abs.rpow_const fun _ => Or.inr hp_nonneg).continuousOn
  have hF_int : Integrable (Function.uncurry F) (μ.prod μ) := by
    change Integrable (symmetrizedFinsetSum X s) (μ.prod μ)
    refine integrable_finsetSum s ?_
    intro i hi
    exact ((hX_int i hi).comp_fst μ).sub ((hX_int i hi).comp_snd μ)
  have hF_int_right : ∀ x, Integrable (fun y => F x y) μ := by
    intro x
    refine integrable_finsetSum s ?_
    intro i hi
    exact (integrable_const (X i x)).sub (hX_int i hi)
  have hF_integral :
      ∀ x, ∫ y, F x y ∂μ = centeredFinsetSum X μ s x := by
    intro x
    change ∫ y, ∑ i ∈ s, (X i x - X i y) ∂μ = centeredFinsetSum X μ s x
    rw [centeredFinsetSum, integral_finsetSum]
    · refine Finset.sum_congr rfl ?_
      intro i hi
      rw [integral_sub (integrable_const _) (hX_int i hi), integral_const]
      simp
    · intro i hi
      exact (integrable_const (X i x)).sub (hX_int i hi)
  have hjensen :
      ∀ᵐ x ∂μ, |∫ y, F x y ∂μ| ^ p ≤ ∫ y, |F x y| ^ p ∂μ := by
    filter_upwards [hsymm_int.prod_right_ae] with x hx
    have hmem : ∀ᵐ y ∂μ, F x y ∈ (Set.univ : Set ℝ) := by
      exact Filter.Eventually.of_forall (fun _ => Set.mem_univ _)
    exact hconv.map_integral_le hcont isClosed_univ hmem (hF_int_right x) (by simpa [F] using! hx)
  have hright_int :
      Integrable (fun x => ∫ y, |F x y| ^ p ∂μ) μ := by
    simpa [Function.uncurry, F, symmetrizedFinsetSum] using hsymm_int.integral_prod_left
  have hleft_ae :
      AEStronglyMeasurable (fun x => |∫ y, F x y ∂μ| ^ p) μ := by
    apply AEMeasurable.aestronglyMeasurable
    exact AEMeasurable.comp_aemeasurable
      ((continuous_abs.rpow_const fun _ => Or.inr hp_nonneg).measurable.aemeasurable)
      hF_int.integral_prod_left.aestronglyMeasurable.aemeasurable
  have hleft_int :
      Integrable (fun x => |∫ y, F x y ∂μ| ^ p) μ := by
    refine hright_int.mono' hleft_ae ?_
    filter_upwards [hjensen] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using hx
  calc
    ∫ ω, |centeredFinsetSum X μ s ω| ^ p ∂μ
        = ∫ x, |∫ y, F x y ∂μ| ^ p ∂μ := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall (fun x => by
              change |centeredFinsetSum X μ s x| ^ p = |∫ y, F x y ∂μ| ^ p
              rw [← hF_integral x])
    _ ≤ ∫ x, ∫ y, |F x y| ^ p ∂μ ∂μ := by
          exact integral_mono_ae hleft_int hright_int hjensen
    _ = ∫ ω : Ω × Ω, |symmetrizedFinsetSum X s ω| ^ p ∂(μ.prod μ) := by
          have hpowF_int :
              Integrable (Function.uncurry (fun x y => |F x y| ^ p)) (μ.prod μ) := by
            simpa [Function.uncurry, F, symmetrizedFinsetSum] using! hsymm_int
          simpa [Function.uncurry, F, symmetrizedFinsetSum] using
            (integral_integral (f := fun x y => |F x y| ^ p) hpowF_int)

section

omit [MeasurableSpace Ω]

/-- Pointwise real-`L^p` control of the symmetrized finite sum by the two
coordinate copies of the original finite sum. -/
theorem abs_symmetrizedFinsetSum_rpow_le
    {X : ι → Ω → ℝ} {s : Finset ι} {p : ℝ} (hp : 1 ≤ p) (ω : Ω × Ω) :
    |symmetrizedFinsetSum X s ω| ^ p ≤
      (2 : ℝ) ^ (p - 1) *
        (|∑ i ∈ s, X i ω.1| ^ p + |∑ i ∈ s, X i ω.2| ^ p) := by
  have hp_nonneg : 0 ≤ p := le_trans zero_le_one hp
  let A : ℝ := ∑ i ∈ s, X i ω.1
  let B : ℝ := ∑ i ∈ s, X i ω.2
  have hsymm : symmetrizedFinsetSum X s ω = A - B := by
    simp [symmetrizedFinsetSum, A, B, Finset.sum_sub_distrib]
  have habs : |A - B| ≤ |A| + |B| := by
    simpa [sub_eq_add_neg] using abs_add_le A (-B)
  have hrpow :
      |A - B| ^ p ≤ (|A| + |B|) ^ p := by
    exact Real.rpow_le_rpow (abs_nonneg _) habs hp_nonneg
  have hadd :
      (|A| + |B|) ^ p ≤ (2 : ℝ) ^ (p - 1) * (|A| ^ p + |B| ^ p) := by
    have hnn := NNReal.rpow_add_le_mul_rpow_add_rpow (⟨|A|, abs_nonneg A⟩ : NNReal)
      (⟨|B|, abs_nonneg B⟩ : NNReal) hp
    exact_mod_cast hnn
  rw [hsymm]
  exact hrpow.trans hadd

end

/-- Integrability of the symmetrized real `p`-moment follows from integrability
of the original finite-sum real `p`-moment. -/
theorem integrable_abs_symmetrizedFinsetSum_rpow_of_integrable_abs_finsetSum_rpow
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {p : ℝ}
    (hp : 1 ≤ p)
    (hX_meas : ∀ i ∈ s, Measurable (X i))
    (hsum_int : Integrable (fun ω => |∑ i ∈ s, X i ω| ^ p) μ) :
    Integrable (fun ω : Ω × Ω => |symmetrizedFinsetSum X s ω| ^ p) (μ.prod μ) := by
  have hp_nonneg : 0 ≤ p := le_trans zero_le_one hp
  let G : Ω × Ω → ℝ := fun ω =>
    (2 : ℝ) ^ (p - 1) * (|∑ i ∈ s, X i ω.1| ^ p + |∑ i ∈ s, X i ω.2| ^ p)
  have hfst : Integrable (fun ω : Ω × Ω => |∑ i ∈ s, X i ω.1| ^ p) (μ.prod μ) :=
    hsum_int.comp_fst μ
  have hsnd : Integrable (fun ω : Ω × Ω => |∑ i ∈ s, X i ω.2| ^ p) (μ.prod μ) :=
    hsum_int.comp_snd μ
  have hG_int : Integrable G (μ.prod μ) := by
    simpa [G] using (hfst.add hsnd).const_mul ((2 : ℝ) ^ (p - 1))
  have hsymm_meas : Measurable (symmetrizedFinsetSum X s) := by
    refine Finset.measurable_sum s ?_
    intro i hi
    exact ((hX_meas i hi).comp measurable_fst).sub ((hX_meas i hi).comp measurable_snd)
  have hsymm_ae :
      AEStronglyMeasurable (fun ω : Ω × Ω => |symmetrizedFinsetSum X s ω| ^ p) (μ.prod μ) := by
    exact ((continuous_abs.rpow_const fun _ => Or.inr hp_nonneg).measurable.comp
      hsymm_meas).aestronglyMeasurable
  refine hG_int.mono' hsymm_ae ?_
  filter_upwards with ω
  have hω := abs_symmetrizedFinsetSum_rpow_le (X := X) (s := s) (p := p) hp ω
  have hnonneg : 0 ≤ |symmetrizedFinsetSum X s ω| ^ p :=
    Real.rpow_nonneg (abs_nonneg _) _
  simpa [G, abs_of_nonneg hnonneg] using hω

/-- Product-space real-`L^p` control of the symmetrized finite sum by the
original finite sum. -/
theorem integral_abs_symmetrizedFinsetSum_rpow_le_two_rpow_mul_integral_abs_finsetSum_rpow
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {p : ℝ}
    (hp : 1 ≤ p)
    (hX_meas : ∀ i ∈ s, Measurable (X i))
    (hsum_int : Integrable (fun ω => |∑ i ∈ s, X i ω| ^ p) μ) :
    ∫ ω : Ω × Ω, |symmetrizedFinsetSum X s ω| ^ p ∂(μ.prod μ) ≤
      (2 : ℝ) ^ p * ∫ ω, |∑ i ∈ s, X i ω| ^ p ∂μ := by
  have hp_nonneg : 0 ≤ p := le_trans zero_le_one hp
  let S : Ω → ℝ := fun ω => ∑ i ∈ s, X i ω
  let G : Ω × Ω → ℝ := fun ω =>
    (2 : ℝ) ^ (p - 1) * (|S ω.1| ^ p + |S ω.2| ^ p)
  have hsymm_int :
      Integrable (fun ω : Ω × Ω => |symmetrizedFinsetSum X s ω| ^ p) (μ.prod μ) :=
    integrable_abs_symmetrizedFinsetSum_rpow_of_integrable_abs_finsetSum_rpow
      (μ := μ) hp hX_meas hsum_int
  have hfst : Integrable (fun ω : Ω × Ω => |S ω.1| ^ p) (μ.prod μ) :=
    hsum_int.comp_fst μ
  have hsnd : Integrable (fun ω : Ω × Ω => |S ω.2| ^ p) (μ.prod μ) :=
    hsum_int.comp_snd μ
  have hG_int : Integrable G (μ.prod μ) := by
    simpa [G] using (hfst.add hsnd).const_mul ((2 : ℝ) ^ (p - 1))
  have hpoint :
      ∀ᵐ ω : Ω × Ω ∂(μ.prod μ),
        |symmetrizedFinsetSum X s ω| ^ p ≤ G ω :=
    Filter.Eventually.of_forall fun ω => by
      simpa [G, S] using abs_symmetrizedFinsetSum_rpow_le (X := X) (s := s) (p := p) hp ω
  have hS_meas : Measurable S := by
    refine Finset.measurable_sum s ?_
    intro i hi
    exact hX_meas i hi
  have hid :
      IdentDistrib
        (fun ω : Ω × Ω => |S ω.1| ^ p)
        (fun ω : Ω × Ω => |S ω.2| ^ p)
        (μ.prod μ)
        (μ.prod μ) := by
    simpa [S, Function.comp_def] using
      (identDistrib_comp_fst_comp_snd_prod (μ := μ) (X := S) hS_meas.aemeasurable).comp
        ((continuous_abs.rpow_const fun _ => Or.inr hp_nonneg).measurable)
  have hfst_eq :
      ∫ ω : Ω × Ω, |S ω.1| ^ p ∂(μ.prod μ) = ∫ ω, |S ω| ^ p ∂μ := by
    simpa [S] using
      (integral_fun_fst (μ := μ) (ν := μ) (f := fun ω : Ω => |S ω| ^ p))
  have hsnd_eq :
      ∫ ω : Ω × Ω, |S ω.2| ^ p ∂(μ.prod μ) =
        ∫ ω : Ω × Ω, |S ω.1| ^ p ∂(μ.prod μ) := by
    simpa using hid.integral_eq.symm
  have htwo_rpow : (2 : ℝ) ^ (p - 1) * 2 = (2 : ℝ) ^ p := by
    calc
      (2 : ℝ) ^ (p - 1) * 2 = (2 : ℝ) ^ (p - 1) * (2 : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = (2 : ℝ) ^ ((p - 1) + 1) := by
        rw [← Real.rpow_add (by norm_num : 0 < (2 : ℝ))]
      _ = (2 : ℝ) ^ p := by ring_nf
  calc
    ∫ ω : Ω × Ω, |symmetrizedFinsetSum X s ω| ^ p ∂(μ.prod μ)
        ≤ ∫ ω : Ω × Ω, G ω ∂(μ.prod μ) := by
            exact integral_mono_ae hsymm_int hG_int hpoint
    _ = (2 : ℝ) ^ (p - 1) *
          (∫ ω : Ω × Ω, |S ω.1| ^ p ∂(μ.prod μ) +
            ∫ ω : Ω × Ω, |S ω.2| ^ p ∂(μ.prod μ)) := by
          rw [show (∫ ω : Ω × Ω, G ω ∂(μ.prod μ)) =
            ∫ ω : Ω × Ω, (2 : ℝ) ^ (p - 1) * (|S ω.1| ^ p + |S ω.2| ^ p) ∂(μ.prod μ) by rfl]
          rw [integral_const_mul]
          congr 1
          exact integral_add hfst hsnd
    _ = (2 : ℝ) ^ (p - 1) * (2 * ∫ ω, |S ω| ^ p ∂μ) := by
          rw [hsnd_eq, two_mul, hfst_eq]
    _ = (2 : ℝ) ^ p * ∫ ω, |S ω| ^ p ∂μ := by
          calc
            (2 : ℝ) ^ (p - 1) * (2 * ∫ ω, |S ω| ^ p ∂μ) =
                ((2 : ℝ) ^ (p - 1) * 2) * ∫ ω, |S ω| ^ p ∂μ := by ring_nf
            _ = (2 : ℝ) ^ p * ∫ ω, |S ω| ^ p ∂μ := by rw [htwo_rpow]
    _ = (2 : ℝ) ^ p * ∫ ω, |∑ i ∈ s, X i ω| ^ p ∂μ := by
          rfl

/-- Real-exponent moment symmetrization inequality for the centered finite sum. -/
theorem integral_abs_centeredFinsetSum_rpow_le_two_rpow_mul_integral_abs_finsetSum_rpow
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {p : ℝ}
    (hp : 1 ≤ p)
    (hX_meas : ∀ i ∈ s, Measurable (X i))
    (hX_int : ∀ i ∈ s, Integrable (X i) μ)
    (hsum_int : Integrable (fun ω => |∑ i ∈ s, X i ω| ^ p) μ) :
    ∫ ω, |centeredFinsetSum X μ s ω| ^ p ∂μ ≤
      (2 : ℝ) ^ p * ∫ ω, |∑ i ∈ s, X i ω| ^ p ∂μ := by
  have hsymm_int :
      Integrable (fun ω : Ω × Ω => |symmetrizedFinsetSum X s ω| ^ p) (μ.prod μ) :=
    integrable_abs_symmetrizedFinsetSum_rpow_of_integrable_abs_finsetSum_rpow
      (μ := μ) hp hX_meas hsum_int
  exact
    (integral_abs_centeredFinsetSum_rpow_le_integral_abs_symmetrizedFinsetSum_rpow
      (μ := μ) (X := X) (s := s) (p := p) hp hX_int hsymm_int).trans
      (integral_abs_symmetrizedFinsetSum_rpow_le_two_rpow_mul_integral_abs_finsetSum_rpow
        (μ := μ) (X := X) (s := s) (p := p) hp hX_meas hsum_int)


end
end IndependentSums
end Homogenization
