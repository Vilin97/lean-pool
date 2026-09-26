/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Beta.Complex.Basic

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

public import Mathlib.MeasureTheory.Integral.Pi
public import LeanPool.CarlsonFunctions.Pochhammer.Gamma
public import LeanPool.CarlsonFunctions.Pochhammer.BetaIntegral
public import LeanPool.CarlsonFunctions.Pochhammer.ComplexPowMeasurable
public import LeanPool.CarlsonFunctions.StdSimplexMeasure.FiniteDimensionalHyperplane
public import LeanPool.CarlsonFunctions.StdSimplexMeasure.PiSnoc
public import LeanPool.CarlsonFunctions.StdSimplexMeasure.ProdSlices

/-! # Solid-simplex integral evaluation of multivariate beta -/

open Fintype

@[expose] public noncomputable section MvBeta

namespace Complex

variable {ι : Type*} [Fintype ι]

section SolidSimplexIntegral

open MeasureTheory MeasurableEquiv

/-- The solid standard `n`-simplex used in the DLMF multivariate Beta integrals. -/
def mvBetaSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

/-- The solid standard simplex is a measurable set. -/
theorem measurableSet_mvBetaSimplex (n : ℕ) : MeasurableSet (mvBetaSimplex n) := by
  apply IsClosed.measurableSet
  apply IsClosed.inter
  · change IsClosed ({x : Fin n → ℝ | ∀ i, 0 ≤ x i} : Set (Fin n → ℝ))
    rw [show {x : Fin n → ℝ | ∀ i, 0 ≤ x i} = ⋂ i, {x | 0 ≤ x i} by ext x; simp]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  · exact isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const

/-- Splitting off the last coordinate identifies a solid-simplex section with an interval
whose upper endpoint is the remaining slack coordinate. -/
private theorem snoc_mem_mvBetaSimplex_iff {n : ℕ} (y : Fin n → ℝ) (t : ℝ) :
    Fin.snoc y t ∈ mvBetaSimplex (n + 1) ↔
      (∀ i, 0 ≤ y i) ∧ 0 ≤ t ∧ t ≤ 1 - ∑ i, y i := by
  simp only [mvBetaSimplex, Set.mem_ofPred_eq, Fin.forall_fin_succ', Fin.snoc_last,
    Fin.snoc_castSucc, Fin.sum_univ_castSucc]
  constructor
  · rintro ⟨⟨hy, ht⟩, hsum⟩
    exact ⟨hy, ht, by linarith⟩
  · rintro ⟨hy, ht, hsum⟩
    exact ⟨⟨hy, ht⟩, by linarith⟩

/-- The solid-coordinate multivariate Beta integral. The parameter `b₀` belongs to the slack
coordinate `1 - ∑ i, x i`, while `b i` belongs to `x i`. This is the integral on the left-hand
side of DLMF 5.14.2. -/
def mvBetaIntegral {n : ℕ} (b₀ : ℂ) (b : Fin n → ℂ) : ℂ :=
  ∫ x in mvBetaSimplex n,
    ((1 - ∑ i, x i : ℝ) : ℂ) ^ (b₀ - 1) * ∏ i, (x i : ℂ) ^ (b i - 1)

/-- The solid-coordinate integral in DLMF 5.14.1, in which the slack coordinate has exponent
zero. -/
def mvBetaIntegralOne {n : ℕ} (b : Fin n → ℂ) : ℂ :=
  ∫ x in mvBetaSimplex n, ∏ i, (x i : ℂ) ^ (b i - 1)

/-- The integrand occurring in the solid-coordinate multivariate Beta integral. This private
name keeps the slicing proofs readable without enlarging the public API. -/
private abbrev mvBetaIntegrand {n : ℕ} (b₀ : ℂ) (b : Fin n → ℂ) (x : Fin n → ℝ) : ℂ :=
  ((1 - ∑ i, x i : ℝ) : ℂ) ^ (b₀ - 1) * ∏ i, (x i : ℂ) ^ (b i - 1)

/-- The zero-dimensional solid-coordinate integral has the expected value. -/
private theorem mvBetaIntegral_zero {b₀ : ℂ} (hb₀ : 0 < b₀.re) :
    mvBetaIntegral (n := 0) b₀ Fin.elim0 = mvBeta (Fin.cons b₀ Fin.elim0) := by
  have hG : Gamma b₀ ≠ 0 := Gamma_ne_zero_of_re_pos hb₀
  simp [mvBetaIntegral, mvBetaSimplex, mvBeta, hG, measureReal_def, volume_pi]

/-- The solid-simplex Dirichlet monomial is measurable. -/
private theorem measurable_mvBetaIntegrand {n : ℕ} (b₀ : ℂ) (b : Fin n → ℂ) :
    Measurable fun x : Fin n → ℝ =>
      ((1 - ∑ i, x i : ℝ) : ℂ) ^ (b₀ - 1) * ∏ i, (x i : ℂ) ^ (b i - 1) := by
  refine ((measurable_ofReal_cpow_const (b₀ - 1)).comp ?_).mul ?_
  · exact measurable_const.sub (Finset.univ.measurable_sum fun i _ => measurable_pi_apply i)
  · exact Finset.univ.measurable_prod fun i _ =>
      (measurable_ofReal_cpow_const (b i - 1)).comp (measurable_pi_apply i)

/-- Interior points of the solid simplex have strictly positive coordinates and slack. -/
private theorem interior_mvBetaSimplex_subset (n : ℕ) :
    interior (mvBetaSimplex n) ⊆ {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1} := by
  intro x hx
  have hxmem : x ∈ mvBetaSimplex n := interior_subset hx
  obtain ⟨ε, εpos, hε⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  refine ⟨fun i => ?_, ?_⟩
  · by_contra hi
    have hi0 : x i = 0 := le_antisymm (not_lt.mp hi) (hxmem.1 i)
    let y : Fin n → ℝ := x - (ε / 2) • Pi.single i (1 : ℝ)
    have hydist : dist y x < ε := by
      rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Pi.norm_single]
      simp [abs_of_pos εpos]
      linarith
    have : y ∈ mvBetaSimplex n := hε hydist
    have hyi : y i < 0 := by
      simp [y, hi0]
      linarith [εpos]
    exact hyi.not_ge (this.1 i)
  · by_contra hs
    have hs1 : ∑ i, x i = 1 := le_antisymm hxmem.2 (not_lt.mp hs)
    cases n with
    | zero => simp at hs1
    | succ n =>
        let y : Fin (n + 1) → ℝ := x + (ε / 2) • Pi.single (0 : Fin (n + 1)) (1 : ℝ)
        have hydist : dist y x < ε := by
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Pi.norm_single]
          simp [abs_of_pos εpos]
          linarith
        have hymem : y ∈ mvBetaSimplex n.succ := hε hydist
        have hsum : ∑ i, y i = 1 + ε / 2 := by
          simp only [y, Pi.add_apply, Finset.sum_add_distrib, Pi.smul_apply, smul_eq_mul, hs1]
          rw [← Finset.mul_sum, Finset.sum_eq_single (0 : Fin (n + 1))]
          · simp
          · intro i _ hi
            simp [Pi.single_eq_of_ne hi]
          · simp
        have hnot : ¬ ∑ i, y i ≤ 1 := by
          rw [hsum]
          linarith [εpos]
        exact hnot hymem.2

/-- Combining the last coordinate against the slack parameter recovers `mvBeta`. -/
private theorem mvBeta_cons_mul_betaIntegral {n : ℕ} {b₀ : ℂ} {b : Fin (n + 1) → ℂ}
    (hb₀ : 0 < b₀.re) (hb : ∀ i, 0 < (b i).re) :
    mvBeta (Fin.cons (b₀ + b (Fin.last n)) (fun i => b (Fin.castSucc i))) *
      betaIntegral (b (Fin.last n)) b₀ =
    mvBeta (Fin.cons b₀ b) := by
  have hbl : 0 < (b (Fin.last n)).re := hb _
  have hsum : 0 < (b₀ + b (Fin.last n)).re := by
    rw [add_re]
    exact add_pos hb₀ hbl
  have hΓ : Gamma (b₀ + b (Fin.last n)) ≠ 0 := Gamma_ne_zero_of_re_pos hsum
  have hβ := betaIntegral_eq_Gamma_mul_div (b (Fin.last n)) b₀ hbl hb₀
  simp only [mvBeta, hβ]
  rw [Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.prod_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [Fin.prod_univ_castSucc (fun i => Gamma (b i)), Fin.sum_univ_castSucc b]
  have hcomm : b₀ + b (Fin.last n) = b (Fin.last n) + b₀ := add_comm _ _
  have hadd : b₀ + b (Fin.last n) + ∑ i : Fin n, b (Fin.castSucc i) =
      b₀ + (∑ i : Fin n, b (Fin.castSucc i) + b (Fin.last n)) := by ac_rfl
  have hΓ' : Gamma (b (Fin.last n) + b₀) ≠ 0 := by rwa [add_comm] at hΓ
  rw [hadd, hcomm]
  field_simp [hΓ', Gamma_ne_zero_of_re_pos hb₀, Gamma_ne_zero_of_re_pos hbl]

private theorem piFinSnoc_preimage_mvBetaSimplex (n : ℕ) :
    piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ) ⁻¹' mvBetaSimplex (n + 1) =
      {p : (Fin n → ℝ) × ℝ |
        p.1 ∈ mvBetaSimplex n ∧ p.2 ∈ Set.Icc 0 (1 - ∑ i, p.1 i)} := by
  ext p
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, piFinSnoc_apply]
  rw [snoc_mem_mvBetaSimplex_iff]
  simp only [mvBetaSimplex, Set.mem_Icc, Set.mem_ofPred_eq]
  constructor
  · intro ⟨hy, ht, hsum⟩
    refine ⟨⟨hy, ?_⟩, ht, hsum⟩
    linarith
  · intro ⟨⟨hy, _hys⟩, ht, hsum⟩
    exact ⟨hy, ht, hsum⟩

/-- For fixed leading coordinates, the last-coordinate section of the solid-simplex
Dirichlet integrand is integrable. Inside the smaller solid simplex this is a scaled Euler
Beta kernel; outside it the section vanishes. -/
private theorem integrable_mvBetaIntegrand_snoc_slice {n : ℕ} {b₀ : ℂ}
    {b : Fin (n + 1) → ℂ} (hb₀ : 0 < b₀.re) (hbl : 0 < (b (Fin.last n)).re)
    (y : Fin n → ℝ) :
    Integrable fun t : ℝ =>
      (piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ) ⁻¹' mvBetaSimplex (n + 1)).indicator
        (mvBetaIntegrand b₀ b ∘ piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ)) (y, t) := by
  by_cases hy : y ∈ mvBetaSimplex n
  · have hs : 0 ≤ 1 - ∑ i, y i := sub_nonneg.mpr hy.2
    have hβint := intervalIntegrable_betaKernel_scaled hbl hb₀ hs
    have hIcc : IntegrableOn
        (fun t : ℝ => (t : ℂ) ^ (b (Fin.last n) - 1) *
          ((1 - ∑ i, y i - t : ℝ) : ℂ) ^ (b₀ - 1))
        (Set.Icc 0 (1 - ∑ i, y i)) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hs).mp (by
        convert hβint using 1
        ext t
        simp)
    have hmul : IntegrableOn
        (fun t : ℝ => (∏ i, (y i : ℂ) ^ (b i.castSucc - 1)) *
          ((t : ℂ) ^ (b (Fin.last n) - 1) *
            ((1 - ∑ i, y i - t : ℝ) : ℂ) ^ (b₀ - 1)))
        (Set.Icc 0 (1 - ∑ i, y i)) :=
      hIcc.const_mul _
    have hfun : (fun t : ℝ =>
        (piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ) ⁻¹' mvBetaSimplex (n + 1)).indicator
          (mvBetaIntegrand b₀ b ∘ piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ)) (y, t)) =
        (Set.Icc 0 (1 - ∑ i, y i)).indicator (fun t =>
          (∏ i, (y i : ℂ) ^ (b i.castSucc - 1)) *
            ((t : ℂ) ^ (b (Fin.last n) - 1) *
              ((1 - ∑ i, y i - t : ℝ) : ℂ) ^ (b₀ - 1))) := by
      funext t
      by_cases ht : t ∈ Set.Icc 0 (1 - ∑ i, y i)
      · have hmem : (y, t) ∈ piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ) ⁻¹' mvBetaSimplex (n + 1) := by
          rw [piFinSnoc_preimage_mvBetaSimplex]
          exact ⟨hy, ht⟩
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem ht]
        simp only [mvBetaIntegrand, Function.comp_apply, piFinSnoc_apply,
          Fin.sum_univ_castSucc, Fin.prod_univ_castSucc,
          Fin.snoc_last, Fin.snoc_castSucc]
        push_cast
        ring
      · have hnmem : (y, t) ∉ piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ) ⁻¹' mvBetaSimplex (n + 1) := by
          rw [piFinSnoc_preimage_mvBetaSimplex]
          exact fun h => ht h.2
        simp [Set.indicator_of_notMem hnmem, Set.indicator_of_notMem ht]
    rw [hfun]
    exact (integrable_indicator_iff measurableSet_Icc).mpr hmul
  · have h0 : ∀ t,
        (piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ) ⁻¹' mvBetaSimplex (n + 1)).indicator
          (mvBetaIntegrand b₀ b ∘ piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ)) (y, t) = 0 := by
      intro t
      apply Set.indicator_of_notMem
      rw [piFinSnoc_preimage_mvBetaSimplex]
      exact fun h => hy h.1
    have heq : (fun t : ℝ =>
        (piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ) ⁻¹' mvBetaSimplex (n + 1)).indicator
          (mvBetaIntegrand b₀ b ∘ piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ)) (y, t)) = 0 :=
      funext h0
    rw [heq]
    exact integrable_zero ℝ ℂ volume

/-- Evaluation of a last-coordinate section of the solid-simplex Dirichlet integrand. -/
private theorem integral_mvBetaIntegrand_snoc_slice {n : ℕ} {b₀ : ℂ}
    {b : Fin (n + 1) → ℂ} (y : Fin n → ℝ) (hs : 0 < 1 - ∑ i, y i) :
    ∫ t in Set.Icc 0 (1 - ∑ i, y i),
        mvBetaIntegrand b₀ b (piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ) (y, t)) =
      (∏ i, (y i : ℂ) ^ (b i.castSucc - 1)) *
        ((1 - ∑ i, y i : ℝ) : ℂ) ^ (b₀ + b (Fin.last n) - 1) *
          betaIntegral (b (Fin.last n)) b₀ := by
  have hs0 : 0 ≤ 1 - ∑ i, y i := hs.le
  have hmul (t : ℝ) :
      mvBetaIntegrand b₀ b (piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ) (y, t)) =
        (∏ i, (y i : ℂ) ^ (b i.castSucc - 1)) *
          ((t : ℂ) ^ (b (Fin.last n) - 1) *
            (((1 - ∑ i, y i : ℝ) : ℂ) - t) ^ (b₀ - 1)) := by
    simp only [mvBetaIntegrand, piFinSnoc_apply, Fin.sum_univ_castSucc, Fin.prod_univ_castSucc,
      Fin.snoc_last, Fin.snoc_castSucc]
    push_cast
    ring
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs0]
  simp_rw [hmul]
  rw [intervalIntegral.integral_const_mul,
    betaIntegral_scaled (b (Fin.last n)) b₀ hs]
  ring_nf

/-- Integrability of the solid-simplex Dirichlet monomial, together with DLMF 5.14.2. -/
private theorem mvBetaIntegral_eq_mvBeta_aux {n : ℕ} {b₀ : ℂ} {b : Fin n → ℂ}
    (hb₀ : 0 < b₀.re) (hb : ∀ i, 0 < (b i).re) :
    IntegrableOn (fun x : Fin n → ℝ =>
        ((1 - ∑ i, x i : ℝ) : ℂ) ^ (b₀ - 1) * ∏ i, (x i : ℂ) ^ (b i - 1))
      (mvBetaSimplex n) ∧
    mvBetaIntegral b₀ b = mvBeta (Fin.cons b₀ b) := by
  induction n generalizing b₀ with
  | zero =>
      refine ⟨?_, mvBetaIntegral_zero hb₀⟩
      have hfun :
          (fun x : Fin 0 → ℝ =>
              ((1 - ∑ i, x i : ℝ) : ℂ) ^ (b₀ - 1) * ∏ i, (x i : ℂ) ^ (b i - 1)) =
            fun _ => 1 := by
        funext x
        simp
      rw [hfun]
      refine (integrableOn_const_iff).2 (Or.inr ?_)
      simp [mvBetaSimplex]
  | succ n ih =>
      have hb' : ∀ i : Fin n, 0 < (b i.castSucc).re := fun i => hb _
      have hbl : 0 < (b (Fin.last n)).re := hb _
      have hb₀' : 0 < (b₀ + b (Fin.last n)).re := by
        rw [add_re]
        exact add_pos hb₀ hbl
      have ih' := ih hb₀' hb'
      set f : (Fin (n + 1) → ℝ) → ℂ := mvBetaIntegrand b₀ b
      set f' : (Fin n → ℝ) → ℂ := fun y =>
        ((1 - ∑ i, y i : ℝ) : ℂ) ^ (b₀ + b (Fin.last n) - 1) *
          ∏ i, (y i : ℂ) ^ (b i.castSucc - 1)
      have hfmeas : Measurable f := by
        simpa only [f, mvBetaIntegrand] using measurable_mvBetaIntegrand b₀ b
      have hmp := volume_preserving_piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ)
      have hme := (piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ)).measurableEmbedding
      have hR := piFinSnoc_preimage_mvBetaSimplex n
      have hRmeas : MeasurableSet (piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ) ⁻¹' mvBetaSimplex (n + 1)) :=
        hmp.measurable (measurableSet_mvBetaSimplex _)
      have hf_comp : ∀ y t,
          f (piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ) (y, t)) =
            ((1 - ∑ i, y i - t : ℝ) : ℂ) ^ (b₀ - 1) *
              ((t : ℂ) ^ (b (Fin.last n) - 1) *
                ∏ i, (y i : ℂ) ^ (b i.castSucc - 1)) := by
        intro y t
        simp [f, mvBetaIntegrand, piFinSnoc_apply, Fin.sum_univ_castSucc,
          Fin.prod_univ_castSucc]
        ring
      have hslice (y : Fin n → ℝ) :
          Integrable fun t : ℝ =>
            (piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ) ⁻¹' mvBetaSimplex (n + 1)).indicator (f ∘
              piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ)) (y, t) := by
        change Integrable fun t : ℝ =>
          (piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ) ⁻¹' mvBetaSimplex (n + 1)).indicator
            (mvBetaIntegrand b₀ b ∘ piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ)) (y, t)
        exact integrable_mvBetaIntegrand_snoc_slice hb₀ hbl y
      have hfR : IntegrableOn (f ∘ piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ))
          (piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ) ⁻¹' mvBetaSimplex (n + 1)) volume := by
        rw [Measure.volume_eq_prod]
        have hASM : AEStronglyMeasurable
            ((piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ) ⁻¹' mvBetaSimplex (n + 1)).indicator (f ∘
              piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ)))
            (volume.prod volume) :=
          (hfmeas.comp hmp.measurable).aestronglyMeasurable.indicator hRmeas
        refine (integrable_indicator_iff hRmeas).1 ?_
        rw [integrable_prod_iff hASM]
        refine ⟨Filter.Eventually.of_forall hslice, ?_⟩
        -- The inner-norm integral is controlled by the inductive integrand.
        let C : ℝ :=
          ∫ t in (0 : ℝ)..1, ‖(t : ℂ) ^ (b (Fin.last n) - 1) * (1 - (t : ℂ)) ^ (b₀ - 1)‖
        have hbound : Integrable fun y : Fin n → ℝ =>
            ∫ t : ℝ, ‖(piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ) ⁻¹' mvBetaSimplex (n + 1)).indicator
              (f ∘ piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ)) (y, t)‖ := by
          have hf'n : IntegrableOn (fun y => ‖f' y‖) (mvBetaSimplex n) := ih'.1.norm
          have hsum0 : ∀ᵐ (y : Fin n → ℝ), ∑ i, y i ≠ (1 : ℝ) := by
            cases n with
            | zero => simp
            | succ n =>
                simpa [ae_iff] using
                  Measure.volume_setOf_fin_sum_eq (Nat.succ_pos n) (1 : ℝ)
          have hcoord0 : ∀ᵐ (y : Fin n → ℝ), ∀ i : Fin n, y i ≠ 0 := by
            have h := measure_iUnion_null fun i : Fin n =>
              Measure.volume_setOf_eval_eq i (0 : ℝ)
            rw [ae_iff]
            convert h
            ext y
            simp
          have hEq :
              (fun y => ∫ t, ‖(piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ) ⁻¹' mvBetaSimplex (n +
                1)).indicator
                  (f ∘ piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ)) (y, t)‖) =ᵐ[volume]
                (mvBetaSimplex n).indicator (fun y => C * ‖f' y‖) := by
            filter_upwards [hsum0, hcoord0] with y hsum hcoord
            by_cases hy : y ∈ mvBetaSimplex n
            · have hs : 0 < 1 - ∑ i, y i :=
                lt_of_le_of_ne (sub_nonneg.mpr hy.2) (fun h => hsum (by linarith [h]))
              have hscale := integral_norm_betaKernel_scaled (b (Fin.last n)) b₀ hs
              have hs0 : 0 ≤ 1 - ∑ i, y i := le_of_lt hs
              have hfun : (fun t =>
                  ‖(piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ) ⁻¹' mvBetaSimplex (n + 1)).indicator
                    (f ∘ piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ)) (y, t)‖) =
                  (Set.Icc 0 (1 - ∑ i, y i)).indicator (fun t =>
                    ‖∏ i, (y i : ℂ) ^ (b i.castSucc - 1)‖ *
                      ‖(t : ℂ) ^ (b (Fin.last n) - 1) *
                        ((1 - ∑ i, y i - t : ℝ) : ℂ) ^ (b₀ - 1)‖) := by
                funext t
                by_cases ht : t ∈ Set.Icc 0 (1 - ∑ i, y i)
                · have hmem : (y, t) ∈ piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ) ⁻¹' mvBetaSimplex (n +
                  1) := by
                    rw [hR]; exact ⟨hy, ht⟩
                  rw [Set.indicator_of_mem hmem, Set.indicator_of_mem ht]
                  simp only [Function.comp_apply, hf_comp, norm_mul]
                  ring
                · have hnmem : (y, t) ∉ piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ) ⁻¹' mvBetaSimplex (n +
                  1) := by
                    rw [hR]; exact fun h => ht h.2
                  simp [Set.indicator_of_notMem hnmem, Set.indicator_of_notMem ht]
              have hI :
                  ∫ t, ‖(piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ) ⁻¹' mvBetaSimplex (n + 1)).indicator
                      (f ∘ piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ)) (y, t)‖ =
                    ‖∏ i, (y i : ℂ) ^ (b i.castSucc - 1)‖ *
                      ∫ t in (0 : ℝ)..(1 - ∑ i, y i),
                        ‖(t : ℂ) ^ (b (Fin.last n) - 1) *
                          (((1 - ∑ i, y i : ℝ) : ℂ) - t) ^ (b₀ - 1)‖ := by
                rw [hfun, integral_indicator measurableSet_Icc, intervalIntegral.integral_of_le hs0,
                  ← integral_const_mul, integral_Icc_eq_integral_Ioc]
                apply setIntegral_congr_fun measurableSet_Ioc
                intro t _
                simp only [ofReal_sub]
              have hf'eq : ‖f' y‖ =
                  (1 - ∑ i, y i : ℝ) ^ ((b₀ + b (Fin.last n)).re - 1) *
                    ‖∏ i, (y i : ℂ) ^ (b i.castSucc - 1)‖ := by
                simp only [f', norm_mul]
                rw [norm_cpow_eq_rpow_re_of_pos hs, sub_re, add_re, one_re]
              rw [hI, hscale, Set.indicator_of_mem hy, hf'eq]
              simp only [C, add_re]
              ring
            · have h0 : ∀ t,
                  (piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ) ⁻¹' mvBetaSimplex (n + 1)).indicator
                    (f ∘ piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ)) (y, t) = 0 := by
                intro t
                apply Set.indicator_of_notMem
                rw [hR]
                exact fun h => hy h.1
              simp [h0, Set.indicator_of_notMem hy, integral_zero]
          exact (integrable_congr hEq).mpr
            ((integrable_indicator_iff (measurableSet_mvBetaSimplex n)).mpr (hf'n.const_mul C))
        exact hbound
      have hfΔ : IntegrableOn f (mvBetaSimplex (n + 1)) :=
        (hmp.integrableOn_comp_preimage hme).1 hfR
      refine ⟨hfΔ, ?_⟩
      have hFubini :=
        (hmp.setIntegral_preimage_emb hme f (mvBetaSimplex (n + 1))).symm
      have hprod :
          ∫ p in piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ) ⁻¹' mvBetaSimplex (n + 1), f (piFinSnoc (fun
            _ : Fin (n + 1) ↦ ℝ) p) =
            ∫ y in mvBetaSimplex n, ∫ t in Set.Icc 0 (1 - ∑ i, y i),
              f (piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ) (y, t)) := by
        rw [hR]
        exact setIntegral_prod_Icc_slice_volume (measurableSet_mvBetaSimplex n)
          (measurable_const : Measurable (fun _ : Fin n → ℝ => (0 : ℝ)))
          (measurable_const.sub
            (Finset.univ.measurable_sum fun i _ => measurable_pi_apply i))
          (fun p => f (piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ) p)) (hR ▸ hfR)
      have hinter (y : Fin n → ℝ) (_hy : y ∈ mvBetaSimplex n)
          (hs : 0 < 1 - ∑ i, y i) :
          ∫ t in Set.Icc 0 (1 - ∑ i, y i), f (piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ) (y, t)) =
            (∏ i, (y i : ℂ) ^ (b i.castSucc - 1)) *
              ((1 - ∑ i, y i : ℝ) : ℂ) ^ (b₀ + b (Fin.last n) - 1) *
                betaIntegral (b (Fin.last n)) b₀ := by
        change ∫ t in Set.Icc 0 (1 - ∑ i, y i),
            mvBetaIntegrand b₀ b (piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ) (y, t)) = _
        exact integral_mvBetaIntegrand_snoc_slice y hs
      simp only [mvBetaIntegral]
      rw [hFubini, hprod]
      have houter :
          ∫ y in mvBetaSimplex n, ∫ t in Set.Icc 0 (1 - ∑ i, y i),
              f (piFinSnoc (fun _ : Fin (n + 1) ↦ ℝ) (y, t)) =
            betaIntegral (b (Fin.last n)) b₀ * ∫ y in mvBetaSimplex n, f' y := by
        have hnull : ∀ᵐ (y : Fin n → ℝ), ∑ i, y i ≠ (1 : ℝ) := by
          cases n with
          | zero => simp
          | succ n =>
              simpa [ae_iff] using
                Measure.volume_setOf_fin_sum_eq (Nat.succ_pos n) (1 : ℝ)
        rw [← integral_const_mul]
        refine setIntegral_congr_ae (measurableSet_mvBetaSimplex n) ?_
        filter_upwards [hnull] with y hy
        intro hymem
        by_cases hs : 0 < 1 - ∑ i, y i
        · rw [hinter y hymem hs]
          simp [f']
          ring_nf
        · have hs0 : 1 - ∑ i, y i = 0 :=
            le_antisymm (not_lt.mp hs) (sub_nonneg.mpr hymem.2)
          exact (hy (sub_eq_zero.mp hs0).symm).elim
      rw [houter, ← mvBetaIntegral, ih'.2, mul_comm]
      exact mvBeta_cons_mul_betaIntegral hb₀ hb

/-- DLMF 5.14.2: the solid-coordinate Dirichlet integral equals the multivariate Beta function.
The slack parameter is placed first in `Fin.cons`; parameter symmetry identifies this convention
with the DLMF convention, where it is displayed last. -/
theorem mvBetaIntegral_eq_mvBeta {n : ℕ} {b₀ : ℂ} {b : Fin n → ℂ}
    (hb₀ : 0 < b₀.re) (hb : ∀ i, 0 < (b i).re) :
    mvBetaIntegral b₀ b = mvBeta (Fin.cons b₀ b) :=
  (mvBetaIntegral_eq_mvBeta_aux hb₀ hb).2

/-- DLMF 5.14.1: the solid-simplex integral without a slack-coordinate factor equals the
multivariate Beta function with slack parameter one. -/
theorem mvBetaIntegralOne_eq_mvBeta {n : ℕ} {b : Fin n → ℂ} (hb : ∀ i, 0 < (b i).re) :
    mvBetaIntegralOne b = mvBeta (Fin.cons 1 b) := by
  simpa [mvBetaIntegralOne, mvBetaIntegral] using
    (mvBetaIntegral_eq_mvBeta (b₀ := (1 : ℂ)) (b := b) (by norm_num) hb)

end SolidSimplexIntegral

end Complex

end MvBeta
