/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import LeanPool.FullyDynamicMatching.FD1D.V5.CostBounds

/-!
# Balanced initial count laws for every inventory size

For arbitrary `m`, divisibility by the leaf count need not hold.  We avoid
that restriction by taking the uniform law on the finite set of global
maximizers of the harmonic tree potential.  Child-subtree swaps preserve the
potential, so this law is tree invariant.  Its initial expected potential is
maximal, which removes the endpoint term from the finite-horizon energy
telescope.
-/

namespace FD1D.V5.Balanced

noncomputable section

open scoped BigOperators

variable {L m : ℕ}

private theorem descendantLevelPotential_inventoryPerm_subtreeSwap
    {d n m : ℕ} (v : DyadicNode d)
    (x : InventoryState (DyadicNode ((d + 1) + n)) m)
    (a : ℝ) {r : ℕ} (hrn : r ≤ n) :
    (∑ w : DyadicNode ((d + 1) + r),
        (nodeMass ((d + 1) + r) w) ^ 2 *
          harmonicPotential (a / 2)
            ((Dynamics.aggregatedInventory
              (FD1D.TreeSymmetry.inventoryPerm
                (FD1D.TreeSymmetry.subtreeSwap v n) x)).count
                  ((d + 1) + r) w)) =
      ∑ w : DyadicNode ((d + 1) + r),
        (nodeMass ((d + 1) + r) w) ^ 2 *
          harmonicPotential (a / 2)
            ((Dynamics.aggregatedInventory x).count
              ((d + 1) + r) w) := by
  rw [← Equiv.sum_comp
    (FD1D.TreeSymmetry.subtreeSwap v r)
    (fun w : DyadicNode ((d + 1) + r) =>
      (nodeMass ((d + 1) + r) w) ^ 2 *
        harmonicPotential (a / 2)
          ((Dynamics.aggregatedInventory
            (FD1D.TreeSymmetry.inventoryPerm
              (FD1D.TreeSymmetry.subtreeSwap v n) x)).count
                ((d + 1) + r) w))]
  apply Finset.sum_congr rfl
  intro w hw
  have hcount :=
    FD1D.TreeSymmetry.stateAggregate_count_subtreeSwap
      v x hrn w
  have hmass :
      nodeMass ((d + 1) + r)
          (FD1D.TreeSymmetry.subtreeSwap v r w) =
        nodeMass ((d + 1) + r) w := by
    simp [nodeMass]
  rw [hmass]
  congr 2

private theorem levelPotential_inventoryPerm_subtreeSwap
    {d n m : ℕ} (v : DyadicNode d)
    (x : InventoryState (DyadicNode ((d + 1) + n)) m)
    (a : ℝ) (j : ℕ) (hj : j < (d + 1) + n) :
    (∑ w : DyadicNode (j + 1),
        (nodeMass (j + 1) w) ^ 2 *
          harmonicPotential (a / 2)
            ((Dynamics.aggregatedInventory
              (FD1D.TreeSymmetry.inventoryPerm
                (FD1D.TreeSymmetry.subtreeSwap v n) x)).count
                  (j + 1) w)) =
      ∑ w : DyadicNode (j + 1),
        (nodeMass (j + 1) w) ^ 2 *
          harmonicPotential (a / 2)
            ((Dynamics.aggregatedInventory x).count (j + 1) w) := by
  by_cases hjd : j < d
  · apply Finset.sum_congr rfl
    intro w hw
    congr 2
    simpa only
        [← FD1D.TreeSymmetry.stateAggregate_eq_aggregatedInventory] using
      FD1D.TreeSymmetry.stateAggregate_count_aboveSwap
        v x (show j + 1 ≤ d by omega) w
  · have hdj : d ≤ j := by omega
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hdj
    have hrn : r ≤ n := by omega
    have hdepth : (d + r) + 1 = (d + 1) + r := by omega
    have h :=
      descendantLevelPotential_inventoryPerm_subtreeSwap v x a hrn
    rw [← hdepth] at h
    exact h

private theorem statePotential_inventoryPerm_subtreeSwap
    {d n m : ℕ} (v : DyadicNode d)
    (x : InventoryState (DyadicNode ((d + 1) + n)) m)
    (a : ℝ) :
    Dynamics.statePotential a
        (FD1D.TreeSymmetry.inventoryPerm
          (FD1D.TreeSymmetry.subtreeSwap v n) x) =
      Dynamics.statePotential a x := by
  unfold Dynamics.statePotential globalHarmonicPotential Dynamics.countLabel
  apply Finset.sum_congr rfl
  intro j hj
  exact levelPotential_inventoryPerm_subtreeSwap
    v x a j (Finset.mem_range.mp hj)

/-- Swapping two child subtrees preserves the V5 harmonic tree potential. -/
theorem statePotential_inventorySwap
    {d L m : ℕ} (hdL : d < L) (v : DyadicNode d)
    (a : ℝ) (x : InventoryState (DyadicNode L) m) :
    Dynamics.statePotential a
        (FD1D.TreeSymmetry.inventorySwap hdL v x) =
      Dynamics.statePotential a x := by
  obtain ⟨r, rfl⟩ :=
    Nat.exists_eq_add_of_le (show d + 1 ≤ L by omega)
  have hleaf :
      FD1D.TreeSymmetry.leafSwap
          (show d < (d + 1) + r by omega) v =
        FD1D.TreeSymmetry.subtreeSwap v r := by
    unfold FD1D.TreeSymmetry.leafSwap
    simp using
      (FD1D.TreeSymmetry.leafSwapWithGap_rfl (n := r) v)
  rw [FD1D.TreeSymmetry.inventorySwap, hleaf]
  exact statePotential_inventoryPerm_subtreeSwap v x a

/-! ## The invariant law on potential maximizers -/

/-- All count states attaining the largest V5 tree potential. -/
def potentialMaximizers (L m : ℕ) (a : ℝ) :
    Finset (InventoryState (DyadicNode L) m) :=
  Finset.univ.filter fun x =>
    ∀ y : InventoryState (DyadicNode L) m,
      Dynamics.statePotential a y ≤ Dynamics.statePotential a x

theorem mem_potentialMaximizers_iff
    (a : ℝ) (x : InventoryState (DyadicNode L) m) :
    x ∈ potentialMaximizers L m a ↔
      ∀ y : InventoryState (DyadicNode L) m,
        Dynamics.statePotential a y ≤ Dynamics.statePotential a x := by
  simp [potentialMaximizers]

theorem potentialMaximizers_nonempty (L m : ℕ) (a : ℝ) :
    (potentialMaximizers L m a).Nonempty := by
  classical
  obtain ⟨x, _hx, hmax⟩ :=
    Finset.exists_max_image
      (Finset.univ : Finset (InventoryState (DyadicNode L) m))
      (Dynamics.statePotential a) (by simp)
  refine ⟨x, (mem_potentialMaximizers_iff a x).2 ?_⟩
  intro y
  exact hmax y (by simp)

/-- Uniform probability law on the finite set of potential maximizers. -/
def law (L m : ℕ) (a : ℝ) :
    FiniteLaw (InventoryState (DyadicNode L) m) where
  mass x :=
    if x ∈ potentialMaximizers L m a then
      1 / ((potentialMaximizers L m a).card : ℝ)
    else 0
  mass_nonneg x := by
    split_ifs <;> positivity
  sum_mass := by
    classical
    let S := potentialMaximizers L m a
    have hS : S.Nonempty := potentialMaximizers_nonempty L m a
    have hcard : ((S.card : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_ne_zero.mpr hS)
    change
      (∑ x : InventoryState (DyadicNode L) m,
        if x ∈ S then 1 / (S.card : ℝ) else 0) = 1
    calc
      (∑ x : InventoryState (DyadicNode L) m,
          if x ∈ S then 1 / (S.card : ℝ) else 0) =
          (1 / (S.card : ℝ)) *
            ∑ x : InventoryState (DyadicNode L) m,
              if x ∈ S then (1 : ℝ) else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        split_ifs <;> ring
      _ = (1 / (S.card : ℝ)) * (S.card : ℝ) := by
        congr 1
        simp using
          (Finset.sum_boole
            (R := ℝ) (fun x : InventoryState (DyadicNode L) m => x ∈ S)
            Finset.univ)
      _ = 1 := by field_simp

@[simp]
theorem law_mass (L m : ℕ) (a : ℝ)
    (x : InventoryState (DyadicNode L) m) :
    (law L m a).mass x =
      if x ∈ potentialMaximizers L m a then
        1 / ((potentialMaximizers L m a).card : ℝ)
      else 0 :=
  rfl

/-- The maximizer law is invariant under every child-subtree swap. -/
theorem lawInvariant_inventorySwap
    {d L m : ℕ} (hdL : d < L) (v : DyadicNode d) (a : ℝ) :
    FiniteKernel.LawInvariant (law L m a)
      (FD1D.TreeSymmetry.inventorySwap hdL v) := by
  intro x
  have hmem :
      FD1D.TreeSymmetry.inventorySwap hdL v x ∈
          potentialMaximizers L m a ↔
        x ∈ potentialMaximizers L m a := by
    rw [mem_potentialMaximizers_iff, mem_potentialMaximizers_iff,
      statePotential_inventorySwap hdL v a x]
  simp only [law_mass]
  rw [if_congr hmem rfl rfl]

/-- Every state potential is bounded by the maximizer law's expectation. -/
theorem statePotential_le_law_expect
    (L m : ℕ) (a : ℝ)
    (x : InventoryState (DyadicNode L) m) :
    Dynamics.statePotential a x ≤
      (law L m a).expect (Dynamics.statePotential a) := by
  classical
  obtain ⟨z, hz⟩ := potentialMaximizers_nonempty L m a
  have hzmax :=
    (mem_potentialMaximizers_iff a z).1 hz
  have hexpect :
      (law L m a).expect (Dynamics.statePotential a) =
        Dynamics.statePotential a z := by
    unfold FiniteLaw.expect
    calc
      (∑ y, (law L m a).mass y * Dynamics.statePotential a y) =
          ∑ y, (law L m a).mass y * Dynamics.statePotential a z := by
        apply Finset.sum_congr rfl
        intro y hy
        by_cases hymem : y ∈ potentialMaximizers L m a
        · have hymax :=
            (mem_potentialMaximizers_iff a y).1 hymem
          have heq : Dynamics.statePotential a y =
              Dynamics.statePotential a z :=
            le_antisymm (hzmax y) (hymax z)
          rw [heq]
        · rw [law_mass, ite_eq_right hymem]
          simp
      _ = Dynamics.statePotential a z := by
        rw [← Finset.sum_mul, (law L m a).sum_mass, one_mul]
  rw [hexpect]
  exact hzmax x

/-! ## All-horizon energy and squared-cost bounds -/

/--
The V5 master-energy estimate has no endpoint penalty when the initial
expected potential globally majorizes every state potential.
-/
theorem finite_transport_energy_estimate_of_maximal_potential
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (haL : 2000 * (L : ℝ) ≤ a)
    (mu0 : FiniteLaw (InventoryState (DyadicNode L) m))
    (hmax : ∀ x : InventoryState (DyadicNode L) m,
      Dynamics.statePotential a x ≤
        mu0.expect (Dynamics.statePotential a))
    (T : ℕ) (hT : 0 < T) :
    (∑ t ∈ Finset.range T,
        ((Dynamics.kernel a ha hm).iterate t mu0).expect
          (Dynamics.stateTransportEnergy a)) / (T : ℝ) ≤
      501 * a ^ 2 / (m : ℝ) ^ 2 := by
  have hmaster :=
    Dynamics.master_energy_estimate a ha hm haL mu0 T hT
  have hdrop :
      (∑ t ∈ Finset.range T,
          ((Dynamics.kernel a ha hm).iterate t mu0).expect
            (Dynamics.stateTransportEnergy a)) / (T : ℝ) ≤
        (∑ t ∈ Finset.range T,
          ((Dynamics.kernel a ha hm).iterate t mu0).expect
            (Dynamics.combinedEnergy a)) / (T : ℝ) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Finset.sum_le_sum
    intro t ht
    apply FiniteLaw.expect_mono
    intro x
    unfold Dynamics.combinedEnergy
    have hH := Dynamics.stateRateEnergy_nonneg a x L
    nlinarith [sq_nonneg a]
  have hterminal :
      ((Dynamics.kernel a ha hm).iterate T mu0).expect
          (Dynamics.statePotential a) ≤
        mu0.expect (Dynamics.statePotential a) := by
    calc
      ((Dynamics.kernel a ha hm).iterate T mu0).expect
          (Dynamics.statePotential a) ≤
        ((Dynamics.kernel a ha hm).iterate T mu0).expect
          (fun _ => mu0.expect (Dynamics.statePotential a)) :=
        ((Dynamics.kernel a ha hm).iterate T mu0).expect_mono hmax
      _ = mu0.expect (Dynamics.statePotential a) :=
        FiniteLaw.expect_const _ _
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hcoef : 0 ≤ 1000 * a / (T : ℝ) := by positivity
  calc
    (∑ t ∈ Finset.range T,
        ((Dynamics.kernel a ha hm).iterate t mu0).expect
          (Dynamics.stateTransportEnergy a)) / (T : ℝ) ≤
      (∑ t ∈ Finset.range T,
        ((Dynamics.kernel a ha hm).iterate t mu0).expect
          (Dynamics.combinedEnergy a)) / (T : ℝ) := hdrop
    _ ≤ 501 * a ^ 2 / (m : ℝ) ^ 2 +
        1000 * a / (T : ℝ) *
          (((Dynamics.kernel a ha hm).iterate T mu0).expect
              (Dynamics.statePotential a) -
            mu0.expect (Dynamics.statePotential a)) := hmaster
    _ ≤ 501 * a ^ 2 / (m : ℝ) ^ 2 := by
      have hdiff :
          ((Dynamics.kernel a ha hm).iterate T mu0).expect
                (Dynamics.statePotential a) -
              mu0.expect (Dynamics.statePotential a) ≤ 0 :=
        sub_nonpos.mpr hterminal
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hcoef hdiff]

/-- The maximizer law has the stationary-strength transport bound for every horizon. -/
theorem law_finite_transport_energy_estimate
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (haL : 2000 * (L : ℝ) ≤ a)
    (T : ℕ) (hT : 0 < T) :
    (∑ t ∈ Finset.range T,
        ((Dynamics.kernel a ha hm).iterate t (law L m a)).expect
          (Dynamics.stateTransportEnergy a)) / (T : ℝ) ≤
      501 * a ^ 2 / (m : ℝ) ^ 2 :=
  finite_transport_energy_estimate_of_maximal_potential
    a ha hm haL (law L m a)
    (statePotential_le_law_expect L m a) T hT

/-- Count-envelope RMS bound from the balanced maximizer law. -/
theorem law_average_rms_squaredCostEnvelope_le
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (haL : 2000 * (L : ℝ) ≤ a)
    (T : ℕ) (hT : 0 < T) :
    Real.sqrt
        ((∑ t ∈ Finset.range T,
          ((Dynamics.kernel a ha hm).iterate t (law L m a)).expect
            (Transport.stateSquaredCostEnvelope a)) / (T : ℝ)) ≤
      dyadicCellWidth L +
        Real.sqrt ((1 / 12) *
          (501 * a ^ 2 / (m : ℝ) ^ 2)) := by
  have hrms :=
    Transport.sqrt_average_stateSquaredCostEnvelope_le
      a (fun t => (Dynamics.kernel a ha hm).iterate t (law L m a))
      T hT
      (by
        intro t d v
        exact Transport.iterate_lawInvariant_of_swapInvariant
          a ha hm (law L m a)
          (fun d v => lawInvariant_inventorySwap d.isLt v a)
          t d v)
  calc
    Real.sqrt
        ((∑ t ∈ Finset.range T,
          ((Dynamics.kernel a ha hm).iterate t (law L m a)).expect
            (Transport.stateSquaredCostEnvelope a)) / (T : ℝ)) ≤
      dyadicCellWidth L +
        Real.sqrt ((1 / 12) *
          ((∑ t ∈ Finset.range T,
            ((Dynamics.kernel a ha hm).iterate t (law L m a)).expect
              (Dynamics.stateTransportEnergy a)) / (T : ℝ))) := hrms
    _ ≤ dyadicCellWidth L +
        Real.sqrt ((1 / 12) *
          (501 * a ^ 2 / (m : ℝ) ^ 2)) := by
      exact add_le_add le_rfl
        (Real.sqrt_le_sqrt
          (mul_le_mul_of_nonneg_left
            (law_finite_transport_energy_estimate a ha hm haL T hT)
            (by norm_num)))

/-- The manuscript-parameter balanced initial count law. -/
def parameterizedLaw (m : ℕ) :
    FiniteLaw (InventoryState (DyadicNode (treeDepth m)) m) :=
  law (treeDepth m) m (parameterA m : ℝ)

/--
Balanced-initial-inventory corollary: for every positive horizon, the RMS
count-state squared-cost envelope has the stationary constant
`2 + sqrt(501/12)`.
-/
theorem parameterizedLaw_average_rms_squaredCostEnvelope_le
    {m T : ℕ} (hm : 1 ≤ m) (hT : 0 < T) :
    Real.sqrt
        ((∑ t ∈ Finset.range T,
          ((parameterizedKernel m hm).iterate t
            (parameterizedLaw m)).expect
              (parameterizedSquaredCostEnvelope m)) / (T : ℝ)) ≤
      (2 + Real.sqrt (501 / 12)) *
        (parameterA m : ℝ) / (m : ℝ) := by
  have hmpos : 0 < m := by omega
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have ha := parameterA_cast_pos hm
  have hgeneric :=
    law_average_rms_squaredCostEnvelope_le
      (L := treeDepth m) (m := m)
      (parameterA m : ℝ) ha hmpos
      (parameterA_cast_ge_treeDepth hm) T hT
  have hcell :
      dyadicCellWidth (treeDepth m) ≤
        2 * (parameterA m : ℝ) / (m : ℝ) := by
    simpa [dyadicCellWidth, leafCount] using
      one_div_leafCount_le_two_mul_parameterA_div hm
  have hsqrt :
      Real.sqrt ((1 / 12) *
          (501 * (parameterA m : ℝ) ^ 2 / (m : ℝ) ^ 2)) ≤
        Real.sqrt (501 / 12) *
          (parameterA m : ℝ) / (m : ℝ) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · have hsquare :
          Real.sqrt (501 / 12) ^ 2 = (501 / 12 : ℝ) :=
        Real.sq_sqrt (by norm_num)
      field_simp [hmreal.ne']
      nlinarith
  change
    Real.sqrt
        ((∑ t ∈ Finset.range T,
          ((Dynamics.kernel
            (L := treeDepth m) (m := m)
            (parameterA m : ℝ) ha hmpos).iterate t
              (law (treeDepth m) m (parameterA m : ℝ))).expect
                (Transport.stateSquaredCostEnvelope
                  (parameterA m : ℝ))) / (T : ℝ)) ≤ _
  calc
    Real.sqrt
        ((∑ t ∈ Finset.range T,
          ((Dynamics.kernel
            (L := treeDepth m) (m := m)
            (parameterA m : ℝ) ha hmpos).iterate t
              (law (treeDepth m) m (parameterA m : ℝ))).expect
                (Transport.stateSquaredCostEnvelope
                  (parameterA m : ℝ))) / (T : ℝ)) ≤
      dyadicCellWidth (treeDepth m) +
        Real.sqrt ((1 / 12) *
          (501 * (parameterA m : ℝ) ^ 2 / (m : ℝ) ^ 2)) :=
      hgeneric
    _ ≤ 2 * (parameterA m : ℝ) / (m : ℝ) +
        Real.sqrt (501 / 12) *
          (parameterA m : ℝ) / (m : ℝ) :=
      add_le_add hcell hsqrt
    _ = (2 + Real.sqrt (501 / 12)) *
        (parameterA m : ℝ) / (m : ℝ) := by ring

end

end FD1D.V5.Balanced
