/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.FiniteProbability
public import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.SlabArithmetic

/-!
# Concentration of finite exchange samples

Pair differences find centres in the individual fibres. Product sampling
then turns concentration of an exchange sum into a bounded relation among
those centres.
-/

@[expose] public section

open scoped BigOperators

namespace EGZ.Expansion

theorem exists_center_of_pair_concentration {A : Type*} [Fintype A] [Nonempty A]
    {p W : ℕ} (v : A → ZMod p) {η : ℝ}
    (h : finiteProb (fun x : A × A ↦
      ¬ HasBoundedRepresentative p W (v x.2 - v x.1)) ≤ η) :
    ∃ r : ZMod p, finiteProb (fun x ↦ ¬ HasBoundedRepresentative p W (v x - r)) ≤ η := by
  rw [finiteProb_prod] at h
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_expect_le Finset.univ_nonempty h
  exact ⟨v a, ha⟩

/-- If the samples usually lie near their individual centres, and their
signed sum usually lies in a central slab, then the same is true of the
signed sum of centres, at a wider deterministic radius. -/
theorem bounded_center_sum_of_concentration {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    {p W : ℕ} (v : ∀ i, A i → ZMod p) (r : I → ZMod p) (a : I → ℤ)
    {η : ℝ}
    (hcoord : ∀ i, finiteProb (fun x ↦ ¬ HasBoundedRepresentative p W (v i x - r i)) ≤ η)
    (hsum : finiteProb (fun x : ∀ i, A i ↦
      ¬ HasBoundedRepresentative p W (∑ i, (a i : ZMod p) * v i (x i))) ≤ η)
    (hsmall : ((Fintype.card I : ℝ) + 1) * η < 1) :
    HasBoundedRepresentative p ((1 + ∑ i, (a i).natAbs) * W)
      (∑ i, (a i : ZMod p) * r i) := by
  classical
  let bad : Option I → (∀ i, A i) → Prop := fun o x ↦
    match o with
    | none => ¬ HasBoundedRepresentative p W (∑ i, (a i : ZMod p) * v i (x i))
    | some i => ¬ HasBoundedRepresentative p W (v i (x i) - r i)
  have hbad : (∑ o, finiteProb (bad o)) < 1 := by
    calc
      (∑ o, finiteProb (bad o)) = finiteProb (bad none) + ∑ i, finiteProb (bad (some i)) :=
        Fintype.sum_option _
      _ ≤ η + ∑ _i : I, η := by
        apply add_le_add hsum
        apply Finset.sum_le_sum
        intro i _
        change finiteProb (fun x : ∀ j, A j ↦
          ¬ HasBoundedRepresentative p W (v i (x i) - r i)) ≤ η
        rw [finiteProb_pi_eval A i (fun y ↦ ¬ HasBoundedRepresentative p W (v i y - r i))]
        exact hcoord i
      _ = ((Fintype.card I : ℝ) + 1) * η := by simp; ring
      _ < 1 := hsmall
  obtain ⟨x, hx⟩ := exists_forall_not_of_sum_finiteProb_lt_one bad hbad
  have hsample : HasBoundedRepresentative p W (∑ i, (a i : ZMod p) * v i (x i)) := by
    simpa only [bad, not_not] using hx none
  have herror : HasBoundedRepresentative p ((∑ i, (a i).natAbs) * W)
      (∑ i, (a i : ZMod p) * (v i (x i) - r i)) := by
    rw [Finset.sum_mul]
    apply HasBoundedRepresentative.sum
    intro i _
    apply HasBoundedRepresentative.int_mul
    simpa only [bad, not_not] using hx (some i)
  have heq : (∑ i, (a i : ZMod p) * v i (x i)) -
      (∑ i, (a i : ZMod p) * (v i (x i) - r i)) = ∑ i, (a i : ZMod p) * r i := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    abel
  simpa only [heq, add_mul, one_mul] using hsample.sub herror

end EGZ.Expansion
