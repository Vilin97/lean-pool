/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.HighSetLaw
import LeanPool.Feige.BoundaryNull
import LeanPool.Feige.TwoPointMixture

/-!
# Product laws for two-point random variables
-/

open scoped BigOperators ENNReal
open Set MeasureTheory ProbabilityTheory

namespace Feige

noncomputable section

/-- The Bernoulli law assigning mass `p` to `true`. -/
def boolHighMeasure (p : ℝ) : Measure Bool :=
  ENNReal.ofReal (1 - p) • Measure.dirac false +
    ENNReal.ofReal p • Measure.dirac true

theorem boolHighMeasure_isProbability {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (boolHighMeasure p) := by
  constructor
  simp [boolHighMeasure, ← ENNReal.ofReal_add (sub_nonneg.mpr hp1) hp0]

/-- The coordinates at which a Boolean vector takes the high value. -/
def boolHighSet {m : ℕ} (ω : Fin m → Bool) : Finset (Fin m) :=
  Finset.univ.filter fun i ↦ ω i

theorem measurable_boolHighSet {m : ℕ} :
    Measurable (boolHighSet : (Fin m → Bool) → Finset (Fin m)) :=
  measurable_of_finite _

theorem boolHighSet_injective {m : ℕ} :
    Function.Injective (boolHighSet : (Fin m → Bool) → Finset (Fin m)) := by
  intro ω η h
  funext i
  have hi : (i ∈ boolHighSet ω) = (i ∈ boolHighSet η) := by
    rw [h]
  simpa [boolHighSet] using hi

theorem boolHighSet_surjective {m : ℕ} :
    Function.Surjective
      (boolHighSet : (Fin m → Bool) → Finset (Fin m)) := by
  intro S
  refine ⟨fun i ↦ decide (i ∈ S), ?_⟩
  ext i
  simp [boolHighSet]

theorem boolHighMeasure_singleton (p : ℝ) (b : Bool) :
    boolHighMeasure p {b} =
      ENNReal.ofReal (if b then p else 1 - p) := by
  cases b <;> simp [boolHighMeasure]

theorem map_boolHighSet_pi_eq_highSetMeasure {m : ℕ}
    (p : Fin m → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1) :
    Measure.map boolHighSet
        (Measure.pi fun i ↦ boolHighMeasure (p i)) =
      highSetMeasure p hp0 hp1 := by
  let : ∀ i, IsProbabilityMeasure (boolHighMeasure (p i)) :=
    fun i ↦ boolHighMeasure_isProbability (hp0 i) (hp1 i)
  apply Measure.ext_of_singleton
  intro S
  let ω : Fin m → Bool :=
    (boolHighSet_surjective (m := m) S).choose
  have hω : boolHighSet ω = S :=
    (boolHighSet_surjective (m := m) S).choose_spec
  rw [Measure.map_apply measurable_boolHighSet
    (measurableSet_singleton S)]
  have hpre :
      boolHighSet ⁻¹' ({S} : Set (Finset (Fin m))) =
        {ω} := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    constructor
    · exact hω
    · intro η hη
      exact boolHighSet_injective (hη.trans hω.symm)
  rw [hpre, Measure.pi_singleton]
  rw [show highSetMeasure p hp0 hp1 {S} =
      ENNReal.ofReal (highSetMass p S) by
        simpa using highSetMeasure_apply_finset p hp0 hp1 {S}]
  simp_rw [boolHighMeasure_singleton]
  rw [← ENNReal.ofReal_prod_of_nonneg]
  · congr 1
    classical
    have hfactor :
        (∏ i, if i ∈ S then p i else 1 - p i) =
          highSetMass p S := by
      unfold highSetMass
      rw [Finset.prod_ite]
      have hfilter :
          Finset.univ.filter (fun i : Fin m ↦ i ∈ S) = S := by
        ext i
        simp
      have hfilterc :
          Finset.univ.filter (fun i : Fin m ↦ ¬i ∈ S) =
            Finset.univ \ S := by
        ext i
        simp
      rw [hfilter, hfilterc]
    rw [← hfactor]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ S
    · have hb :
          ω i = true := by
        have := congrArg (fun T : Finset (Fin m) ↦ i ∈ T) hω
        simpa [boolHighSet, hi] using this
      simp [hb, hi]
    · have hb :
          ω i = false := by
        cases h : ω i with
        | false => rfl
        | true =>
            exfalso
            have := congrArg (fun T : Finset (Fin m) ↦ i ∈ T) hω
            simp [boolHighSet, hi, h] at this
      simp [hb, hi]
  · intro i _
    split
    · exact hp0 i
    · exact sub_nonneg.mpr (hp1 i)

theorem map_boolHighMeasure_twoPoint
    {γ β : ℝ} (hγ : 0 ≤ γ) (hβ : 0 < β) :
    Measure.map
        (fun b : Bool ↦ if b then highValue β else lowValue γ)
        (boolHighMeasure (highProbability γ β)) =
      twoPointMeasure (lowValue γ) (highValue β) := by
  have hsum : γ + β ≠ 0 :=
    (add_pos_of_nonneg_of_pos hγ hβ).ne'
  have hlo :
      twoPointLowerWeight (lowValue γ) (highValue β) =
        1 - highProbability γ β := by
    rw [show twoPointLowerWeight (lowValue γ) (highValue β) =
        β / (γ + β) by
      unfold twoPointLowerWeight lowValue highValue
      congr 1 <;> ring]
    exact (one_sub_highProbability hsum).symm
  have hhi :
      twoPointUpperWeight (lowValue γ) (highValue β) =
        highProbability γ β := by
    unfold twoPointUpperWeight lowValue highValue highProbability
    congr 1 <;> ring
  rw [boolHighMeasure, Measure.map_add, Measure.map_smul,
    Measure.map_smul, Measure.map_dirac, Measure.map_dirac]
  · simp [twoPointMeasure, hlo, hhi]
  all_goals fun_prop

theorem map_canonicalTwoPointPiVector {m : ℕ}
    (γ β : Fin m → ℝ) (hγ : ∀ i, 0 ≤ γ i)
    (hβ : ∀ i, 0 < β i) :
    Measure.map (canonicalTwoPointPiVector γ β)
        (Measure.pi fun i ↦
          boolHighMeasure (twoPointHighProbability γ β i)) =
      Measure.pi (fun i ↦
        twoPointMeasure (lowValue (γ i)) (highValue (β i))) := by
  let : ∀ i, IsProbabilityMeasure
      (boolHighMeasure (twoPointHighProbability γ β i)) :=
    fun i ↦ boolHighMeasure_isProbability
      (twoPointHighProbability_nonneg hγ hβ i)
      (twoPointHighProbability_le_one hγ hβ i)
  let f := fun i : Fin m ↦
    fun b : Bool ↦ if b then highValue (β i) else lowValue (γ i)
  have hfun :
      canonicalTwoPointPiVector γ β =
        fun ω i ↦ f i (ω i) := by rfl
  rw [hfun, Measure.pi_map_pi]
  · congr 1
    funext i
    exact map_boolHighMeasure_twoPoint (hγ i) (hβ i)
  · intro i
    exact (measurable_of_finite _).aemeasurable

theorem measurableSet_dirichletK_le {m : ℕ} (α : ℝ) :
    MeasurableSet {y : Fin m → ℝ | dirichletK y ≤ α} :=
  isClosed_Iic.measurableSet.preimage continuous_dirichletK.measurable

theorem twoPointProductLaw_rejection {m : ℕ}
    (γ β : Fin m → ℝ) (hγ : ∀ i, 0 ≤ γ i)
    (hβ : ∀ i, 0 < β i) (α : ℝ) :
    (Measure.pi (fun i ↦
      twoPointMeasure (lowValue (γ i)) (highValue (β i)))).real
        {y | dirichletK y ≤ α} =
      twoPointRejectionMass γ β α := by
  let p := twoPointHighProbability γ β
  let μ := Measure.pi fun i ↦ boolHighMeasure (p i)
  have hmap :
      Measure.map (canonicalTwoPointPiVector γ β) μ =
        Measure.pi (fun i ↦
          twoPointMeasure (lowValue (γ i)) (highValue (β i))) := by
    exact map_canonicalTwoPointPiVector γ β hγ hβ
  rw [← hmap]
  rw [map_measureReal_apply
    (by unfold canonicalTwoPointPiVector; fun_prop)
    (measurableSet_dirichletK_le α)]
  have hevent :
      canonicalTwoPointPiVector γ β ⁻¹' {y | dirichletK y ≤ α} =
        boolHighSet ⁻¹'
          (twoPointRejectionEvent γ β α : Set (Finset (Fin m))) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq,
      twoPointRejectionEvent, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and]
    have hv :
        canonicalTwoPointPiVector γ β ω =
          twoPointVector γ β (boolHighSet ω : Set (Fin m)) := by
      funext i
      simp [canonicalTwoPointPiVector, twoPointVector, boolHighSet]
    rw [hv]
    rfl
  rw [hevent]
  have hp0 := twoPointHighProbability_nonneg (hγ := hγ) (hβ := hβ)
  have hp1 := twoPointHighProbability_le_one (hγ := hγ) (hβ := hβ)
  rw [← map_measureReal_apply measurable_boolHighSet
    (by simp only [MeasurableSpace.measurableSet_top])]
  rw [map_boolHighSet_pi_eq_highSetMeasure p hp0 hp1]
  exact highSetMeasure_rejectionEvent γ β hγ hβ α

end

end Feige
