/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.Gain
import LeanPool.BeyondBethe.BeyondBethe.PairedCertificate
import Mathlib.Tactic

/-! # Clean Witness -/

open scoped BigOperators

namespace BeyondBethe

def outsideColumnFinset
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι) : Finset ι :=
  (Finset.univ.erase a).erase b

abbrev OutsideColumn
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι) :=
  {j // j ∈ outsideColumnFinset a b}

theorem OutsideColumn.ne_a
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι} (l : OutsideColumn a b) : l.1 ≠ a := by
  exact (Finset.mem_erase.mp (Finset.mem_erase.mp l.2).2).1

theorem OutsideColumn.ne_b
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι} (l : OutsideColumn a b) : l.1 ≠ b := by
  exact (Finset.mem_erase.mp l.2).1

theorem two_lt_card_of_outsideMassTwo_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → ℝ} {a b : ι} (hab : a ≠ b)
    (hρ : 0 < outsideMassTwo p a b) :
    2 < Fintype.card ι := by
  have houtside : (outsideColumnFinset a b).Nonempty := by
    by_contra hempty
    have hzero : outsideMassTwo p a b = 0 := by
      rw [outsideMassTwo, show (Finset.univ.erase a).erase b = ∅ by
        exact Finset.not_nonempty_iff_eq_empty.mp hempty]
      simp
    linarith
  obtain ⟨l, hl⟩ := houtside
  let lo : OutsideColumn a b := ⟨l, hl⟩
  exact Fintype.two_lt_card_iff.mpr
    ⟨a, b, lo.1, hab, Ne.symm lo.ne_a, Ne.symm lo.ne_b⟩

theorem pairAlpha_coreDeficit_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℝ} (hX : IsDoublyStochastic X)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    {r s a b : ι} (hrs : r ≠ s) (hab : a ≠ b)
    (hρ : 0 < outsideMassTwo (pairAlpha X r s) a b) :
    0 < 1 - pairAlpha X r s a ∧ 0 < 1 - pairAlpha X r s b := by
  have hcard := two_lt_card_of_outsideMassTwo_pos hab hρ
  have hXpos : ∀ i j, 0 < X i j := fun i j ↦ (hXint i).2 j |>.1
  exact ⟨sub_pos.mpr (pairAlpha_lt_one_of_positive hX hXpos hcard hrs a),
    sub_pos.mpr (pairAlpha_lt_one_of_positive hX hXpos hcard hrs b)⟩

noncomputable def cleanWitnessExponent
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι) :
    CapacityWitnessEdge (OutsideColumn a b) → ι → ℕ
  | Sum.inl _, j => if j = a ∨ j = b then 1 else 0
  | Sum.inr (Sum.inl l), j => if j = a ∨ j = l.1 then 1 else 0
  | Sum.inr (Sum.inr l), j => if j = b ∨ j = l.1 then 1 else 0

/-- The unordered pair of columns represented by a clean-witness atom. -/
noncomputable def cleanWitnessEndpoints
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι) :
    CapacityWitnessEdge (OutsideColumn a b) → ι × ι
  | Sum.inl _ => (a, b)
  | Sum.inr (Sum.inl l) => (a, l.1)
  | Sum.inr (Sum.inr l) => (b, l.1)

/-- Give a witness edge either of its two ordered orientations. -/
noncomputable def cleanWitnessOrientedPair
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι) :
    CapacityWitnessEdge (OutsideColumn a b) × Bool → ι × ι :=
  fun eo ↦ if eo.2 then (cleanWitnessEndpoints a b eo.1).swap
    else cleanWitnessEndpoints a b eo.1

theorem cleanWitnessOrientedPair_injective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι} (hab : a ≠ b) :
    Function.Injective (cleanWitnessOrientedPair a b) := by
  intro x y h
  rcases x with ⟨e, o⟩
  rcases y with ⟨f, p⟩
  rcases e with e | e <;> rcases f with f | f
  · cases e
    cases f
    cases o <;> cases p <;>
      simp_all [cleanWitnessOrientedPair, cleanWitnessEndpoints, hab]
  · rcases f with l | l <;> cases e
    all_goals cases o <;> cases p <;>
      simp_all [cleanWitnessOrientedPair, cleanWitnessEndpoints, hab,
        l.ne_a, l.ne_b, Ne.symm l.ne_a, Ne.symm l.ne_b]
  · rcases e with l | l <;> cases f
    all_goals cases o <;> cases p <;>
      simp_all [cleanWitnessOrientedPair, cleanWitnessEndpoints, hab,
        l.ne_a, l.ne_b, Ne.symm l.ne_a, Ne.symm l.ne_b]
  · rcases e with l | l <;> rcases f with m | m
    all_goals cases o <;> cases p <;>
      simp_all [cleanWitnessOrientedPair, cleanWitnessEndpoints, hab,
        l.ne_a, l.ne_b, m.ne_a, m.ne_b, Ne.symm l.ne_a,
        Ne.symm l.ne_b, Ne.symm m.ne_a, Ne.symm m.ne_b]

/-- The actual coefficient in the pair polynomial of a witness edge. -/
noncomputable def cleanWitnessCoefficient
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v : ι → ℝ) (a b : ι) :
    CapacityWitnessEdge (OutsideColumn a b) → ℝ := fun e ↦
  let p := cleanWitnessEndpoints a b e
  u p.1 * v p.2 + u p.2 * v p.1

noncomputable def expectedLogCoefficient
    {κ : Type*} [Fintype κ] (θ c : κ → ℝ) : ℝ :=
  ∑ e, θ e * Real.log (c e)

theorem entropyCapacityCertificate_eq_expectedLogCoefficient_add_entropy
    {κ : Type*} [Fintype κ] {θ c : κ → ℝ}
    (hc : ∀ e, 0 < c e) :
    entropyCapacityCertificate θ c =
      expectedLogCoefficient θ c + shannonEntropy θ := by
  rw [entropyCapacityCertificate, expectedLogCoefficient, shannonEntropy,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hθ : θ e = 0
  · simp [hθ, Real.negMulLog_def]
  · rw [Real.log_div (hc e).ne' hθ, Real.negMulLog_def]
    ring

theorem cleanWitnessExponent_eq_endpoints
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι) (e : CapacityWitnessEdge (OutsideColumn a b)) (j : ι) :
    cleanWitnessExponent a b e j =
      if j = (cleanWitnessEndpoints a b e).1 ∨
          j = (cleanWitnessEndpoints a b e).2 then 1 else 0 := by
  rcases e with _ | e
  · rfl
  · rcases e with l | l <;> rfl

theorem cleanWitnessEndpoints_ne
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι} (hab : a ≠ b)
    (e : CapacityWitnessEdge (OutsideColumn a b)) :
    (cleanWitnessEndpoints a b e).1 ≠
      (cleanWitnessEndpoints a b e).2 := by
  rcases e with _ | e
  · exact hab
  · rcases e with l | l
    · exact Ne.symm l.ne_a
    · exact Ne.symm l.ne_b

theorem natMonomial_pair
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι → ℝ) {a b : ι} (hab : a ≠ b) :
    natMonomial z (fun j ↦ if j = a ∨ j = b then 1 else 0) =
      z a * z b := by
  rw [natMonomial]
  simp only [pow_ite, pow_one, pow_zero]
  rw [Finset.prod_ite]
  have hfilter :
      Finset.univ.filter (fun j ↦ j = a ∨ j = b) = {a, b} := by
    ext j
    simp [eq_comm]
  rw [hfilter]
  simp [hab]

theorem natMonomial_cleanWitnessExponent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι} (hab : a ≠ b) (z : ι → ℝ)
    (e : CapacityWitnessEdge (OutsideColumn a b)) :
    natMonomial z (cleanWitnessExponent a b e) =
      z (cleanWitnessEndpoints a b e).1 *
        z (cleanWitnessEndpoints a b e).2 := by
  have hexp : cleanWitnessExponent a b e = fun j ↦
      if j = (cleanWitnessEndpoints a b e).1 ∨
          j = (cleanWitnessEndpoints a b e).2 then 1 else 0 :=
    funext (cleanWitnessExponent_eq_endpoints a b e)
  rw [hexp]
  exact natMonomial_pair z (cleanWitnessEndpoints_ne hab e)

/-- The sparse witness polynomial is exactly the sum over both orientations
of its selected two-column sets. -/
theorem finitePolynomial_cleanWitness_eq_oriented_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι} (hab : a ≠ b) (u v z : ι → ℝ) :
    finitePolynomial (cleanWitnessCoefficient u v a b)
        (cleanWitnessExponent a b) z =
      ∑ eo : CapacityWitnessEdge (OutsideColumn a b) × Bool,
        u (cleanWitnessOrientedPair a b eo).1 *
          v (cleanWitnessOrientedPair a b eo).2 *
          z (cleanWitnessOrientedPair a b eo).1 *
          z (cleanWitnessOrientedPair a b eo).2 := by
  rw [finitePolynomial, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _
  rw [natMonomial_cleanWitnessExponent hab]
  simp [cleanWitnessCoefficient, cleanWitnessOrientedPair]
  ring

theorem cleanWitnessOrientedPair_mem_offDiag
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι} (hab : a ≠ b)
    (eo : CapacityWitnessEdge (OutsideColumn a b) × Bool) :
    cleanWitnessOrientedPair a b eo ∈
      (Finset.univ : Finset ι).offDiag := by
  rcases eo with ⟨e, o⟩
  cases o
  · simp [cleanWitnessOrientedPair, cleanWitnessEndpoints_ne hab e]
  · simp [cleanWitnessOrientedPair, (cleanWitnessEndpoints_ne hab e).symm]

/-- The witness polynomial consists of distinct monomials from the full pair
polynomial, so its value is pointwise no larger on the nonnegative orthant. -/
theorem finitePolynomial_cleanWitness_le_pairPolynomial_eval
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι} (hab : a ≠ b)
    {u v z : ι → ℝ} (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j)
    (hz : ∀ j, 0 ≤ z j) :
    finitePolynomial (cleanWitnessCoefficient u v a b)
        (cleanWitnessExponent a b) z ≤
      (pairPolynomial u v).eval z := by
  let f : ι × ι → ℝ := fun e ↦
    u e.1 * v e.2 * z e.1 * z e.2
  let orient := cleanWitnessOrientedPair a b
  have himage :
      (∑ eo : CapacityWitnessEdge (OutsideColumn a b) × Bool,
          f (orient eo)) =
        ∑ e ∈ Finset.image orient Finset.univ, f e := by
    symm
    simpa only [Finset.mem_univ, Set.mem_setOf_eq] using
      (Finset.sum_image (s := Finset.univ) (f := f)
        (g := orient) (cleanWitnessOrientedPair_injective hab).injOn)
  have hsubset : Finset.image orient Finset.univ ⊆
      (Finset.univ : Finset ι).offDiag := by
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨eo, _, rfl⟩ := he
    exact cleanWitnessOrientedPair_mem_offDiag hab eo
  rw [finitePolynomial_cleanWitness_eq_oriented_sum hab]
  change (∑ eo, f (orient eo)) ≤ _
  rw [himage, pairPolynomial_eval]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
    intro e _ _
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (hu e.1) (hv e.2)) (hz e.1)) (hz e.2))

theorem cleanWitnessCoefficient_nonnegative
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {u v : ι → ℝ} (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j)
    (a b : ι) : ∀ e, 0 ≤ cleanWitnessCoefficient u v a b e := by
  intro e
  exact add_nonneg
    (mul_nonneg (hu _) (hv _)) (mul_nonneg (hu _) (hv _))

theorem cleanWitnessCoefficient_positive
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {u v : ι → ℝ} (hu : ∀ j, 0 < u j) (hv : ∀ j, 0 < v j)
    (a b : ι) : ∀ e, 0 < cleanWitnessCoefficient u v a b e := by
  intro e
  exact add_pos (mul_pos (hu _) (hv _)) (mul_pos (hu _) (hv _))

theorem cleanWitnessCoefficient_core_lower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {u v : ι → ℝ} {a b : ι} {w : ℝ} (hw : 0 ≤ w)
    (hua : w ≤ u a) (hub : w ≤ u b)
    (hva : w ≤ v a) (hvb : w ≤ v b) :
    2 * w ^ 2 ≤
      cleanWitnessCoefficient u v a b (Sum.inl ()) := by
  simp only [cleanWitnessCoefficient, cleanWitnessEndpoints]
  have h₁ : w * w ≤ u a * v b := mul_le_mul hua hvb hw (hw.trans hua)
  have h₂ : w * w ≤ u b * v a := mul_le_mul hub hva hw (hw.trans hub)
  nlinarith

theorem cleanWitnessCoefficient_left_lower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {u v : ι → ℝ} {a b : ι} {w : ℝ}
    (hua : w ≤ u a) (hva : w ≤ v a)
    (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j)
    (l : OutsideColumn a b) :
    w * (u l.1 + v l.1) ≤
      cleanWitnessCoefficient u v a b (Sum.inr (Sum.inl l)) := by
  simp only [cleanWitnessCoefficient, cleanWitnessEndpoints]
  have h₁ := mul_le_mul_of_nonneg_right hua (hv l.1)
  have h₂ := mul_le_mul_of_nonneg_right hva (hu l.1)
  nlinarith

theorem cleanWitnessCoefficient_right_lower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {u v : ι → ℝ} {a b : ι} {w : ℝ}
    (hub : w ≤ u b) (hvb : w ≤ v b)
    (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j)
    (l : OutsideColumn a b) :
    w * (u l.1 + v l.1) ≤
      cleanWitnessCoefficient u v a b (Sum.inr (Sum.inr l)) := by
  simp only [cleanWitnessCoefficient, cleanWitnessEndpoints]
  have h₁ := mul_le_mul_of_nonneg_right hub (hv l.1)
  have h₂ := mul_le_mul_of_nonneg_right hvb (hu l.1)
  nlinarith

/-- Paper (57): the expected log coefficient of the clean witness.  The
proof keeps the two outside families separate and then uses
`delta_a + delta_b = rho`; this is exactly where their normalizing factors
cancel. -/
theorem cleanWitness_expectedLogCoefficient_lower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {u v : ι → ℝ} {a b : ι} {w ρ δa δb : ℝ}
    {α : OutsideColumn a b → ℝ}
    (hw : 0 < w) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hδa : 0 ≤ δa) (hδb : 0 ≤ δb)
    (hδsum : δa + δb = ρ) (hα : ∀ l, 0 ≤ α l)
    (hαsum : ∑ l, α l = ρ)
    (hu : ∀ j, 0 < u j) (hv : ∀ j, 0 < v j)
    (hua : w ≤ u a) (hub : w ≤ u b)
    (hva : w ≤ v a) (hvb : w ≤ v b) :
    (1 - ρ) * Real.log (2 * w ^ 2) + ρ * Real.log w +
        ∑ l, α l * Real.log (u l.1 + v l.1) ≤
      expectedLogCoefficient (capacityWitnessMass ρ δa δb α)
        (cleanWitnessCoefficient u v a b) := by
  let V : OutsideColumn a b → ℝ := fun l ↦ u l.1 + v l.1
  have hV : ∀ l, 0 < V l := fun l ↦ add_pos (hu l.1) (hv l.1)
  have hcoreLower := cleanWitnessCoefficient_core_lower hw.le
    hua hub hva hvb
  have hcoreBase : 0 < 2 * w ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos hw)
  have hcoreLog : Real.log (2 * w ^ 2) ≤
      Real.log (cleanWitnessCoefficient u v a b (Sum.inl ())) :=
    Real.log_le_log hcoreBase hcoreLower
  have hleftLog : ∀ l,
      Real.log (w * V l) ≤ Real.log
        (cleanWitnessCoefficient u v a b (Sum.inr (Sum.inl l))) := by
    intro l
    apply Real.log_le_log (mul_pos hw (hV l))
    exact cleanWitnessCoefficient_left_lower hua hva
      (fun j ↦ (hu j).le) (fun j ↦ (hv j).le) l
  have hrightLog : ∀ l,
      Real.log (w * V l) ≤ Real.log
        (cleanWitnessCoefficient u v a b (Sum.inr (Sum.inr l))) := by
    intro l
    apply Real.log_le_log (mul_pos hw (hV l))
    exact cleanWitnessCoefficient_right_lower hub hvb
      (fun j ↦ (hu j).le) (fun j ↦ (hv j).le) l
  have hcoreWeighted :
      (1 - ρ) * Real.log (2 * w ^ 2) ≤
        (1 - ρ) * Real.log
          (cleanWitnessCoefficient u v a b (Sum.inl ())) :=
    mul_le_mul_of_nonneg_left hcoreLog (sub_nonneg.mpr hρ1)
  have hleftWeighted :
      (∑ l, (δb / ρ * α l) * Real.log (w * V l)) ≤
        ∑ l, (δb / ρ * α l) * Real.log
          (cleanWitnessCoefficient u v a b (Sum.inr (Sum.inl l))) := by
    apply Finset.sum_le_sum
    intro l _
    exact mul_le_mul_of_nonneg_left (hleftLog l)
      (mul_nonneg (div_nonneg hδb hρ.le) (hα l))
  have hrightWeighted :
      (∑ l, (δa / ρ * α l) * Real.log (w * V l)) ≤
        ∑ l, (δa / ρ * α l) * Real.log
          (cleanWitnessCoefficient u v a b (Sum.inr (Sum.inr l))) := by
    apply Finset.sum_le_sum
    intro l _
    exact mul_le_mul_of_nonneg_left (hrightLog l)
      (mul_nonneg (div_nonneg hδa hρ.le) (hα l))
  have hlowerIdentity :
      (1 - ρ) * Real.log (2 * w ^ 2) + ρ * Real.log w +
          ∑ l, α l * Real.log (V l) =
        (1 - ρ) * Real.log (2 * w ^ 2) +
          (∑ l, (δb / ρ * α l) * Real.log (w * V l)) +
          ∑ l, (δa / ρ * α l) * Real.log (w * V l) := by
    simp_rw [Real.log_mul hw.ne' (hV _).ne', mul_add,
      Finset.sum_add_distrib]
    rw [show (∑ l, δb / ρ * α l * Real.log w) =
        (δb / ρ) * ρ * Real.log w by
      calc
        (∑ l, δb / ρ * α l * Real.log w) =
            (δb / ρ * Real.log w) * ∑ l, α l := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          ring
        _ = (δb / ρ) * ρ * Real.log w := by rw [hαsum]; ring]
    rw [show (∑ l, δa / ρ * α l * Real.log w) =
        (δa / ρ) * ρ * Real.log w by
      calc
        (∑ l, δa / ρ * α l * Real.log w) =
            (δa / ρ * Real.log w) * ∑ l, α l := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          ring
        _ = (δa / ρ) * ρ * Real.log w := by rw [hαsum]; ring]
    rw [show (∑ l, δb / ρ * α l * Real.log (V l)) =
        (δb / ρ) * ∑ l, α l * Real.log (V l) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring]
    rw [show (∑ l, δa / ρ * α l * Real.log (V l)) =
        (δa / ρ) * ∑ l, α l * Real.log (V l) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring]
    field_simp [hρ.ne']
    linear_combination
      -(ρ * Real.log w + ∑ x, α x * Real.log (V x)) * hδsum
  rw [hlowerIdentity]
  rw [expectedLogCoefficient]
  simp only [Fintype.sum_sum_type, Fintype.sum_unique,
    capacityWitnessMass]
  linarith

/-- Paper (58): exact entropy of the clean witness in the positive-leakage
case. -/
theorem shannonEntropy_capacityWitnessMass
    {ι : Type*} [Fintype ι]
    {ρ δa δb : ℝ} {α : ι → ℝ}
    (hρ : 0 < ρ) (hδa : 0 < δa) (hδb : 0 < δb)
    (hδsum : δa + δb = ρ) (hα : ∀ l, 0 < α l)
    (hαsum : ∑ l, α l = ρ) :
    shannonEntropy (capacityWitnessMass ρ δa δb α) =
      -(1 - ρ) * Real.log (1 - ρ) -
        (∑ l, α l * Real.log (α l)) -
        δa * Real.log (δa / ρ) -
        δb * Real.log (δb / ρ) := by
  have hleft :
      (∑ l, -(δb / ρ * α l) * Real.log (δb / ρ * α l)) =
        -δb * Real.log (δb / ρ) -
          (δb / ρ) * ∑ l, α l * Real.log (α l) := by
    simp_rw [Real.log_mul (div_pos hδb hρ).ne' (hα _).ne', mul_add,
      Finset.sum_add_distrib]
    rw [show (∑ l, -(δb / ρ * α l) * Real.log (δb / ρ)) =
        -δb * Real.log (δb / ρ) by
      calc
        (∑ l, -(δb / ρ * α l) * Real.log (δb / ρ)) =
            (-(δb / ρ) * Real.log (δb / ρ)) * ∑ l, α l := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          ring
        _ = -δb * Real.log (δb / ρ) := by
          rw [hαsum]
          field_simp [hρ.ne']]
    rw [show (∑ l, -(δb / ρ * α l) * Real.log (α l)) =
        -(δb / ρ) * ∑ l, α l * Real.log (α l) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring]
    ring
  have hright :
      (∑ l, -(δa / ρ * α l) * Real.log (δa / ρ * α l)) =
        -δa * Real.log (δa / ρ) -
          (δa / ρ) * ∑ l, α l * Real.log (α l) := by
    simp_rw [Real.log_mul (div_pos hδa hρ).ne' (hα _).ne', mul_add,
      Finset.sum_add_distrib]
    rw [show (∑ l, -(δa / ρ * α l) * Real.log (δa / ρ)) =
        -δa * Real.log (δa / ρ) by
      calc
        (∑ l, -(δa / ρ * α l) * Real.log (δa / ρ)) =
            (-(δa / ρ) * Real.log (δa / ρ)) * ∑ l, α l := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          ring
        _ = -δa * Real.log (δa / ρ) := by
          rw [hαsum]
          field_simp [hρ.ne']]
    rw [show (∑ l, -(δa / ρ * α l) * Real.log (α l)) =
        -(δa / ρ) * ∑ l, α l * Real.log (α l) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring]
    ring
  rw [shannonEntropy]
  simp only [Fintype.sum_sum_type, Fintype.sum_unique,
    capacityWitnessMass, Real.negMulLog_def]
  rw [hleft, hright]
  field_simp [hρ.ne']
  linear_combination
    -(∑ l, α l * Real.log (α l)) * hδsum

/-- Summed form of paper (56). -/
theorem sum_alpha_log_pairTransfer_lower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι} {τ ρ : ℝ} (hτ : 0 ≤ τ)
    {p q : ι → ℝ} (hp : IsInteriorProbabilityVector p)
    (hq : IsInteriorProbabilityVector q)
    (hρ : ∑ l : OutsideColumn a b, (p l.1 + q l.1) = ρ) :
    -τ * ρ * Real.log 2 +
        (1 + τ) *
          (∑ l : OutsideColumn a b,
            (p l.1 + q l.1) * Real.log (p l.1 + q l.1)) ≤
      ∑ l : OutsideColumn a b,
        (p l.1 + q l.1) *
          Real.log (transferU τ p l.1 + transferU τ q l.1) := by
  have hα : ∀ l : OutsideColumn a b, 0 < p l.1 + q l.1 :=
    fun l ↦ add_pos (hp.2 l.1).1 (hq.2 l.1).1
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hterm : ∀ l : OutsideColumn a b,
      -τ * Real.log 2 + (1 + τ) * Real.log (p l.1 + q l.1) ≤
        Real.log (transferU τ p l.1 + transferU τ q l.1) := by
    intro l
    have hlower := pairTransferSum_lower hτ hp hq l.1
    have hlowerPos : 0 < (2 : ℝ) ^ (-τ) *
        (p l.1 + q l.1) ^ (1 + τ) :=
      mul_pos (Real.rpow_pos_of_pos htwo _) (Real.rpow_pos_of_pos (hα l) _)
    have hlog := Real.log_le_log hlowerPos hlower
    rw [Real.log_mul (Real.rpow_pos_of_pos htwo _).ne'
      (Real.rpow_pos_of_pos (hα l) _).ne',
      Real.log_rpow htwo, Real.log_rpow (hα l)] at hlog
    linarith
  calc
    -τ * ρ * Real.log 2 + (1 + τ) *
          (∑ l : OutsideColumn a b,
            (p l.1 + q l.1) * Real.log (p l.1 + q l.1)) =
        ∑ l : OutsideColumn a b, (p l.1 + q l.1) *
          (-τ * Real.log 2 +
            (1 + τ) * Real.log (p l.1 + q l.1)) := by
      rw [show (∑ l : OutsideColumn a b, (p l.1 + q l.1) *
          (-τ * Real.log 2 +
            (1 + τ) * Real.log (p l.1 + q l.1))) =
          (∑ l : OutsideColumn a b, (p l.1 + q l.1)) *
              (-τ * Real.log 2) +
            (1 + τ) * ∑ l : OutsideColumn a b,
              (p l.1 + q l.1) * Real.log (p l.1 + q l.1) by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.mul_sum]
        apply congrArg₂ (· + ·) rfl
        apply Finset.sum_congr rfl
        intro l _
        ring]
      rw [hρ]
      ring
    _ ≤ ∑ l : OutsideColumn a b,
        (p l.1 + q l.1) *
          Real.log (transferU τ p l.1 + transferU τ q l.1) := by
      apply Finset.sum_le_sum
      intro l _
      exact mul_le_mul_of_nonneg_left (hterm l) (hα l).le

/-- The quantitative lower bound used in paper (59) already holds for the
explicit sparse entropy certificate itself.  Keeping this stronger form
visible is what permits the numerical algorithm to evaluate the witness
directly, without optimizing a capacity. -/
theorem cleanWitness_capacity_theta_lower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι} (hab : a ≠ b)
    {u v : ι → ℝ} {w ρ δa δb τ : ℝ}
    {α : OutsideColumn a b → ℝ}
    (hw : 0 < w) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hδa : 0 < δa) (hδb : 0 < δb)
    (hδsum : δa + δb = ρ)
    (hα : ∀ l, 0 < α l) (hαsum : ∑ l, α l = ρ)
    (hu : ∀ j, 0 < u j) (hv : ∀ j, 0 < v j)
    (hua : w ≤ u a) (hub : w ≤ u b)
    (hva : w ≤ v a) (hvb : w ≤ v b)
    (houtside :
      -τ * ρ * Real.log 2 +
          (1 + τ) * (∑ l, α l * Real.log (α l)) ≤
        ∑ l, α l * Real.log (u l.1 + v l.1)) :
    (1 - ρ) * Real.log ((2 * w ^ 2) / (1 - ρ)) +
        ρ * Real.log w - τ * ρ * Real.log 2 +
        τ * (∑ l, α l * Real.log (α l)) -
        δa * Real.log (δa / ρ) -
        δb * Real.log (δb / ρ) ≤
      entropyCapacityCertificate (capacityWitnessMass ρ δa δb α)
        (cleanWitnessCoefficient u v a b) := by
  let θ := capacityWitnessMass ρ δa δb α
  have hcoeff : ∀ e, 0 < cleanWitnessCoefficient u v a b e :=
    cleanWitnessCoefficient_positive hu hv a b
  have hexpected := cleanWitness_expectedLogCoefficient_lower
    hw hρ hρ1.le hδa.le hδb.le hδsum (fun l ↦ (hα l).le)
    hαsum hu hv hua hub hva hvb
  have hentropy := shannonEntropy_capacityWitnessMass
    hρ hδa hδb hδsum hα hαsum
  have hcertEq :=
    entropyCapacityCertificate_eq_expectedLogCoefficient_add_entropy
      (θ := θ) hcoeff
  have hratio : Real.log ((2 * w ^ 2) / (1 - ρ)) =
      Real.log (2 * w ^ 2) - Real.log (1 - ρ) := by
    rw [Real.log_div (mul_pos (by norm_num) (sq_pos_of_pos hw)).ne'
      (sub_pos.mpr hρ1).ne']
  have hlower :
      (1 - ρ) * Real.log ((2 * w ^ 2) / (1 - ρ)) +
          ρ * Real.log w - τ * ρ * Real.log 2 +
          τ * (∑ l, α l * Real.log (α l)) -
          δa * Real.log (δa / ρ) -
          δb * Real.log (δb / ρ) ≤
        entropyCapacityCertificate θ
          (cleanWitnessCoefficient u v a b) := by
    rw [hcertEq, hentropy, hratio]
    dsimp only [θ] at hexpected ⊢
    linarith
  simpa only [θ] using hlower

/-- Paper (59), separated from its particular transfer-vector
instantiation.  This theorem composes the explicit witness bound with the
one-sided entropy certificate for polynomial capacity. -/
theorem cleanWitness_capacity_theta_bound_of_certificate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι} (hab : a ≠ b)
    {u v αfull : ι → ℝ} {w ρ δa δb τ : ℝ}
    {α : OutsideColumn a b → ℝ}
    (hw : 0 < w) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hδa : 0 < δa) (hδb : 0 < δb)
    (hδsum : δa + δb = ρ)
    (hα : ∀ l, 0 < α l) (hαsum : ∑ l, α l = ρ)
    (hu : ∀ j, 0 < u j) (hv : ∀ j, 0 < v j)
    (hua : w ≤ u a) (hub : w ≤ u b)
    (hva : w ≤ v a) (hvb : w ≤ v b)
    (hmoment : ∀ j,
      exponentMoment (capacityWitnessMass ρ δa δb α)
        (cleanWitnessExponent a b) j = αfull j)
    (hcertUpper :
      entropyCapacityCertificate (capacityWitnessMass ρ δa δb α)
          (cleanWitnessCoefficient u v a b) ≤
        Real.log (polynomialCapacity αfull (pairPolynomial u v)))
    (houtside :
      -τ * ρ * Real.log 2 +
          (1 + τ) * (∑ l, α l * Real.log (α l)) ≤
        ∑ l, α l * Real.log (u l.1 + v l.1)) :
    (1 - ρ) * Real.log ((2 * w ^ 2) / (1 - ρ)) +
        ρ * Real.log w - τ * ρ * Real.log 2 +
        τ * (∑ l, α l * Real.log (α l)) -
        δa * Real.log (δa / ρ) -
        δb * Real.log (δb / ρ) ≤
      Real.log (polynomialCapacity αfull (pairPolynomial u v)) := by
  exact (cleanWitness_capacity_theta_lower hab hw hρ hρ1 hδa hδb
    hδsum hα hαsum hu hv hua hub hva hvb houtside).trans hcertUpper

/-- The sparse-witness capacity is bounded by the capacity of the full pair
polynomial.  This is the omitted subpolynomial step in paper Lemma 19. -/
theorem cleanWitnessCapacity_le_pairPolynomialCapacity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι} (hab : a ≠ b) {u v α : ι → ℝ}
    (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j) :
    finitePolynomialCapacity (cleanWitnessCoefficient u v a b)
        (cleanWitnessExponent a b) α ≤
      polynomialCapacity α (pairPolynomial u v) := by
  exact finitePolynomialCapacity_le_polynomialCapacity_of_eval_le
    (cleanWitnessCoefficient_nonnegative hu hv a b)
    (fun z hz ↦ finitePolynomial_cleanWitness_le_pairPolynomial_eval
      hab hu hv hz)

/-- A feasible clean witness certifies the capacity of the full pair
polynomial, not merely the sparse polynomial supported on the witness. -/
theorem cleanWitnessEntropyCertificate_le_log_pairPolynomialCapacity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι} (hab : a ≠ b) {u v α : ι → ℝ}
    {θ : CapacityWitnessEdge (OutsideColumn a b) → ℝ}
    (hθ : ∀ e, 0 ≤ θ e) (hθsum : ∑ e, θ e = 1)
    (hcoeff : ∀ e, 0 < cleanWitnessCoefficient u v a b e)
    (hmoment : ∀ j,
      exponentMoment θ (cleanWitnessExponent a b) j = α j)
    (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j) :
    entropyCapacityCertificate θ (cleanWitnessCoefficient u v a b) ≤
      Real.log (polynomialCapacity α (pairPolynomial u v)) := by
  have hfinite := entropyCapacityCertificate_le_log_finitePolynomialCapacity
    hθ hθsum hcoeff hmoment
  have hexp := exp_entropyCapacityCertificate_le_finitePolynomialCapacity
    hθ hθsum hcoeff hmoment
  have hfinitePos : 0 < finitePolynomialCapacity
      (cleanWitnessCoefficient u v a b) (cleanWitnessExponent a b) α :=
    (Real.exp_pos _).trans_le hexp
  have hcap := cleanWitnessCapacity_le_pairPolynomialCapacity
    hab hu hv (α := α)
  exact hfinite.trans (Real.log_le_log hfinitePos hcap)

/-- Paper (59) for the full pair polynomial. -/
theorem cleanWitness_capacity_theta_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι} (hab : a ≠ b)
    {u v αfull : ι → ℝ} {w ρ δa δb τ : ℝ}
    {α : OutsideColumn a b → ℝ}
    (hw : 0 < w) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hδa : 0 < δa) (hδb : 0 < δb)
    (hδsum : δa + δb = ρ)
    (hα : ∀ l, 0 < α l) (hαsum : ∑ l, α l = ρ)
    (hu : ∀ j, 0 < u j) (hv : ∀ j, 0 < v j)
    (hua : w ≤ u a) (hub : w ≤ u b)
    (hva : w ≤ v a) (hvb : w ≤ v b)
    (hmoment : ∀ j,
      exponentMoment (capacityWitnessMass ρ δa δb α)
        (cleanWitnessExponent a b) j = αfull j)
    (houtside :
      -τ * ρ * Real.log 2 +
          (1 + τ) * (∑ l, α l * Real.log (α l)) ≤
        ∑ l, α l * Real.log (u l.1 + v l.1)) :
    (1 - ρ) * Real.log ((2 * w ^ 2) / (1 - ρ)) +
        ρ * Real.log w - τ * ρ * Real.log 2 +
        τ * (∑ l, α l * Real.log (α l)) -
        δa * Real.log (δa / ρ) -
        δb * Real.log (δb / ρ) ≤
      Real.log (polynomialCapacity αfull (pairPolynomial u v)) := by
  have hθnonneg : ∀ e,
      0 ≤ capacityWitnessMass ρ δa δb α e :=
    capacityWitness_nonnegative hρ hρ1.le hδa.le hδb.le
      (fun l ↦ (hα l).le)
  have hθsum : ∑ e, capacityWitnessMass ρ δa δb α e = 1 :=
    capacityWitness_sum hρ hδsum hαsum
  have hcoeff : ∀ e, 0 < cleanWitnessCoefficient u v a b e :=
    cleanWitnessCoefficient_positive hu hv a b
  have hcert :=
    cleanWitnessEntropyCertificate_le_log_pairPolynomialCapacity hab
      hθnonneg hθsum hcoeff hmoment
      (fun j ↦ (hu j).le) (fun j ↦ (hv j).le)
  exact cleanWitness_capacity_theta_bound_of_certificate hab hw hρ hρ1
    hδa hδb hδsum hα hαsum hu hv hua hub hva hvb hmoment hcert
    houtside

theorem cleanWitness_coreA_moment
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι} (hab : a ≠ b)
    {ρ δa δb αa : ℝ} {α : OutsideColumn a b → ℝ}
    (hρ : 0 < ρ) (hαsum : ∑ l, α l = ρ)
    (hδa : δa + αa = 1) (hδsum : δa + δb = ρ) :
    exponentMoment (capacityWitnessMass ρ δa δb α)
      (cleanWitnessExponent a b) a = αa := by
  rw [exponentMoment]
  simp only [Fintype.sum_sum_type, Fintype.sum_unique,
    cleanWitnessExponent, ite_eq_left (Or.inl rfl), Nat.cast_one, mul_one]
  have hright : ∀ l : OutsideColumn a b,
      ((if a = b ∨ a = l.1 then 1 else 0 : ℕ) : ℝ) = 0 := by
    intro l
    simp [hab, l.ne_a.symm]
  simp_rw [hright, mul_zero, Finset.sum_const_zero, add_zero]
  simp only [true_or, or_true, if_true, Nat.cast_one, mul_one]
  exact capacityWitness_coreA_marginal hρ hαsum hδa hδsum

theorem cleanWitness_coreB_moment
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι} (hab : a ≠ b)
    {ρ δa δb αb : ℝ} {α : OutsideColumn a b → ℝ}
    (hρ : 0 < ρ) (hαsum : ∑ l, α l = ρ)
    (hδb : δb + αb = 1) (hδsum : δa + δb = ρ) :
    exponentMoment (capacityWitnessMass ρ δa δb α)
      (cleanWitnessExponent a b) b = αb := by
  rw [exponentMoment]
  simp only [Fintype.sum_sum_type, Fintype.sum_unique,
    cleanWitnessExponent, ite_eq_left (Or.inr rfl), Nat.cast_one, mul_one]
  have hleft : ∀ l : OutsideColumn a b,
      ((if b = a ∨ b = l.1 then 1 else 0 : ℕ) : ℝ) = 0 := by
    intro l
    simp [hab.symm, l.ne_b.symm]
  simp_rw [hleft, mul_zero, Finset.sum_const_zero, zero_add]
  simp only [true_or, or_true, if_true, Nat.cast_one, mul_one]
  exact capacityWitness_coreB_marginal hρ hαsum hδb hδsum

theorem cleanWitness_outside_moment
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι} {ρ δa δb : ℝ} {α : OutsideColumn a b → ℝ}
    (hρ : 0 < ρ) (hδsum : δa + δb = ρ)
    (l : OutsideColumn a b) :
    exponentMoment (capacityWitnessMass ρ δa δb α)
      (cleanWitnessExponent a b) l.1 = α l := by
  rw [exponentMoment]
  simp only [Fintype.sum_sum_type, Fintype.sum_unique,
    cleanWitnessExponent]
  have hcore : ¬(l.1 = a ∨ l.1 = b) := by
    exact fun h ↦ h.elim l.ne_a l.ne_b
  rw [ite_eq_right hcore, Nat.cast_zero, mul_zero, zero_add]
  have hleft :
      (∑ x : OutsideColumn a b,
        capacityWitnessMass ρ δa δb α (Sum.inr (Sum.inl x)) *
          ((if l.1 = a ∨ l.1 = x.1 then 1 else 0 : ℕ) : ℝ)) =
        capacityWitnessMass ρ δa δb α (Sum.inr (Sum.inl l)) := by
    let f : OutsideColumn a b → ℝ := fun x ↦
      capacityWitnessMass ρ δa δb α (Sum.inr (Sum.inl x)) *
        ((if l.1 = a ∨ l.1 = x.1 then 1 else 0 : ℕ) : ℝ)
    have hsingle : (∑ x, f x) = f l := Fintype.sum_eq_single l (by
      intro x hxl
      have hne : l.1 ≠ x.1 := by
        intro heq
        apply hxl
        exact Subtype.ext heq.symm
      have hcond : ¬(l.1 = a ∨ l.1 = x.1) :=
        fun h ↦ h.elim l.ne_a hne
      have hlx : l ≠ x := Ne.symm hxl
      simp [f, hcond, l.ne_a, hlx])
    simpa [f, l.ne_a] using hsingle
  have hright :
      (∑ x : OutsideColumn a b,
        capacityWitnessMass ρ δa δb α (Sum.inr (Sum.inr x)) *
          ((if l.1 = b ∨ l.1 = x.1 then 1 else 0 : ℕ) : ℝ)) =
        capacityWitnessMass ρ δa δb α (Sum.inr (Sum.inr l)) := by
    let f : OutsideColumn a b → ℝ := fun x ↦
      capacityWitnessMass ρ δa δb α (Sum.inr (Sum.inr x)) *
        ((if l.1 = b ∨ l.1 = x.1 then 1 else 0 : ℕ) : ℝ)
    have hsingle : (∑ x, f x) = f l := Fintype.sum_eq_single l (by
      intro x hxl
      have hne : l.1 ≠ x.1 := by
        intro heq
        apply hxl
        exact Subtype.ext heq.symm
      have hcond : ¬(l.1 = b ∨ l.1 = x.1) :=
        fun h ↦ h.elim l.ne_b hne
      have hlx : l ≠ x := Ne.symm hxl
      simp [f, hcond, l.ne_b, hlx])
    simpa [f, l.ne_b] using hsingle
  rw [hleft, hright]
  exact capacityWitness_outside_marginal hρ hδsum l

/-- The distribution in paper (52) has the claimed mean exponent vector. -/
theorem cleanWitness_moment
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b : ι} (hab : a ≠ b)
    {ρ δa δb : ℝ} {α : ι → ℝ}
    (hρ : 0 < ρ)
    (hαsum : ∑ l : OutsideColumn a b, α l.1 = ρ)
    (hδa : δa + α a = 1) (hδb : δb + α b = 1)
    (hδsum : δa + δb = ρ) :
    ∀ j,
      exponentMoment
        (capacityWitnessMass ρ δa δb (fun l ↦ α l.1))
        (cleanWitnessExponent a b) j = α j := by
  intro j
  by_cases hja : j = a
  · subst j
    exact cleanWitness_coreA_moment hab hρ hαsum hδa hδsum
  by_cases hjb : j = b
  · subst j
    exact cleanWitness_coreB_moment hab hρ hαsum hδb hδsum
  · let l : OutsideColumn a b := ⟨j, by
      simp [outsideColumnFinset, hja, hjb]⟩
    simpa [l] using cleanWitness_outside_moment
      (α := fun l : OutsideColumn a b ↦ α l.1) hρ hδsum l

theorem sum_outsideColumn_eq_outsideMassTwo
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (a b : ι) :
    (∑ l : OutsideColumn a b, p l.1) = outsideMassTwo p a b := by
  change (∑ l : ↥(outsideColumnFinset a b), p l.1) =
    ∑ j ∈ outsideColumnFinset a b, p j
  exact Finset.sum_coe_sort (outsideColumnFinset a b) (fun j ↦ p j)

/-- The paper's witness has mean `alpha_j = X_rj + X_sj` once its parameters
`rho`, `delta_a`, and `delta_b` are instantiated. -/
theorem cleanWitness_pairAlpha_moment
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℝ} (hX : IsDoublyStochastic X)
    {r s a b : ι} (hab : a ≠ b)
    (hρ : 0 < outsideMassTwo (pairAlpha X r s) a b) :
    let α := pairAlpha X r s
    let ρ := outsideMassTwo α a b
    let δa := 1 - α a
    let δb := 1 - α b
    ∀ j,
      exponentMoment
        (capacityWitnessMass ρ δa δb
          (fun l : OutsideColumn a b ↦ α l.1))
        (cleanWitnessExponent a b) j = α j := by
  dsimp only
  apply cleanWitness_moment hab hρ
  · exact sum_outsideColumn_eq_outsideMassTwo _ _ _
  · ring
  · ring
  · have hsplit := twoCore_add_outsideMassTwo_eq_sum
      (pairAlpha X r s) hab
    rw [sum_pairAlpha hX r s] at hsplit
    linarith

/-- Nonnegativity and normalization of the clean witness in the `rho > 0`
case. -/
theorem cleanWitness_pairAlpha_isProbabilityVector
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℝ} (hX : IsDoublyStochastic X)
    {r s a b : ι} (hrs : r ≠ s) (hab : a ≠ b)
    (hρ : 0 < outsideMassTwo (pairAlpha X r s) a b)
    (hρ1 : outsideMassTwo (pairAlpha X r s) a b ≤ 1) :
    let α := pairAlpha X r s
    let ρ := outsideMassTwo α a b
    let δa := 1 - α a
    let δb := 1 - α b
    IsProbabilityVector
      (capacityWitnessMass ρ δa δb
        (fun l : OutsideColumn a b ↦ α l.1)) := by
  dsimp only
  have hδa : 0 ≤ 1 - pairAlpha X r s a :=
    sub_nonneg.mpr (pairAlpha_le_one hX hrs a)
  have hδb : 0 ≤ 1 - pairAlpha X r s b :=
    sub_nonneg.mpr (pairAlpha_le_one hX hrs b)
  have hα : ∀ l : OutsideColumn a b, 0 ≤ pairAlpha X r s l.1 :=
    fun l ↦ pairAlpha_nonneg hX r s l.1
  have hsplit := twoCore_add_outsideMassTwo_eq_sum
    (pairAlpha X r s) hab
  rw [sum_pairAlpha hX r s] at hsplit
  have hδsum : (1 - pairAlpha X r s a) +
      (1 - pairAlpha X r s b) =
        outsideMassTwo (pairAlpha X r s) a b := by
    linarith
  constructor
  · exact capacityWitness_nonnegative hρ hρ1 hδa hδb hα
  · exact capacityWitness_sum hρ hδsum
      (sum_outsideColumn_eq_outsideMassTwo _ _ _)

/-- The capacity portion of paper Lemma 19, through displayed equation (59),
for the actual transfer vectors and pair marginals. -/
theorem pairTransfer_capacity_theta_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {τ κ : ℝ} (hτ : 0 ≤ τ)
    {X : Matrix ι ι ℝ} (hX : IsDoublyStochastic X)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    {r s a b : ι} (hrs : r ≠ s) (hab : a ≠ b)
    (hcost : fourCoreTransferCost τ X r s a b ≤ κ)
    (hρ : 0 < outsideMassTwo (pairAlpha X r s) a b)
    (hρ1 : outsideMassTwo (pairAlpha X r s) a b < 1) :
    let α := pairAlpha X r s
    let ρ := outsideMassTwo α a b
    let δa := 1 - α a
    let δb := 1 - α b
    let Ur := fun j ↦ transferU τ (X r) j
    let Us := fun j ↦ transferU τ (X s) j
    (1 - ρ) * Real.log ((2 * (Real.exp (-κ)) ^ 2) / (1 - ρ)) +
        ρ * Real.log (Real.exp (-κ)) - τ * ρ * Real.log 2 +
        τ * (∑ l : OutsideColumn a b, α l.1 * Real.log (α l.1)) -
        δa * Real.log (δa / ρ) - δb * Real.log (δb / ρ) ≤
      Real.log (polynomialCapacity α (pairPolynomial Ur Us)) := by
  dsimp only
  let α := pairAlpha X r s
  let ρ := outsideMassTwo α a b
  let δa := 1 - α a
  let δb := 1 - α b
  let Ur : ι → ℝ := fun j ↦ transferU τ (X r) j
  let Us : ι → ℝ := fun j ↦ transferU τ (X s) j
  have hcore := fourCoreTransfer_lower hτ hXint hcost
  have hδpos := pairAlpha_coreDeficit_pos hX hXint hrs hab hρ
  have hαpos : ∀ l : OutsideColumn a b, 0 < α l.1 := by
    intro l
    exact add_pos ((hXint r).2 l.1).1 ((hXint s).2 l.1).1
  have hαsum : ∑ l : OutsideColumn a b, α l.1 = ρ :=
    sum_outsideColumn_eq_outsideMassTwo α a b
  have hδsum : δa + δb = ρ := by
    have hsplit := twoCore_add_outsideMassTwo_eq_sum α hab
    rw [show ∑ j, α j = 2 by
      simpa only [α] using sum_pairAlpha hX r s] at hsplit
    dsimp only [δa, δb, ρ]
    linarith
  have hmoment : ∀ j,
      exponentMoment
        (capacityWitnessMass ρ δa δb
          (fun l : OutsideColumn a b ↦ α l.1))
        (cleanWitnessExponent a b) j = α j := by
    simpa only [α, ρ, δa, δb] using
      cleanWitness_pairAlpha_moment hX hab hρ
  have houtside :
      -τ * ρ * Real.log 2 +
          (1 + τ) *
            (∑ l : OutsideColumn a b,
              α l.1 * Real.log (α l.1)) ≤
        ∑ l : OutsideColumn a b,
          α l.1 * Real.log (Ur l.1 + Us l.1) := by
    exact sum_alpha_log_pairTransfer_lower (a := a) (b := b)
      hτ (hXint r) (hXint s) (by simpa only [α, ρ, pairAlpha] using hαsum)
  have hUr : ∀ j, 0 < Ur j := fun j ↦ transferU_pos (hXint r) j
  have hUs : ∀ j, 0 < Us j := fun j ↦ transferU_pos (hXint s) j
  apply cleanWitness_capacity_theta_bound hab (Real.exp_pos _) hρ hρ1
    hδpos.1 hδpos.2 hδsum hαpos hαsum hUr hUs
  · exact hcore.1
  · exact hcore.2.1
  · exact hcore.2.2.1
  · exact hcore.2.2.2
  · exact hmoment
  · exact houtside

end BeyondBethe
