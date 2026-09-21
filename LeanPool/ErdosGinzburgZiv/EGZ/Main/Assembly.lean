/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Main.Coefficients
import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.AffineApplication
import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Existence

/-!
# The main theorem from the two remaining analytic inputs

All structural ingredients are proved.  The only hypotheses of the final
deduction are the relative expansion statement and the balanced-combination
statement.  Thresholds are selected before the decomposition, with the final
prime bound taken over its uniformly bounded node radii.
-/

open scoped BigOperators

namespace EGZ

open MainProof Expansion

/-- The finite target follows from expansion and balanced combinations,
using the proved flag decomposition, Helly bound, and centerpoint theorem. -/
theorem eventualCeilZeroSum_of_expansion_balanced
    (hExpansion : RelativeExpansionStatement) (hBalanced : BalancedCombinationLemma)
    (d : ℕ) (hd : 0 < d) : EventualCeilZeroSum d := by
  classical
  intro ζ hζ hζ1
  let ε : ℝ := errorScale (hollowBound d) ζ
  have hε : 0 < ε := errorScale_pos (Nat.cast_nonneg _) hζ
  have hε1 : ε < 1 := (errorScale_le (Nat.cast_nonneg _) hζ1.le).trans_lt (by norm_num)
  obtain ⟨δ, Bcard, hδ, hdecomp⟩ := flag_decomposition_lemma d ε hε
  obtain ⟨P⟩ := exists_coefficientParameters hBalanced d hδ hζ hζ1.le
  have hthresholds (K : ℕ) : ∃ T₀ p₀ : ℕ, 1 ≤ K →
      ∀ T : ℕ, T₀ ≤ T → ∀ p : ℕ,
        ∀ (_ : Fact p.Prime) (_ : NeZero p), p₀ ≤ p →
          AffineExpansionAt d K (P.expansionScale K) T p := by
    by_cases hK : 1 ≤ K
    · obtain ⟨T₀, p₀, h⟩ := hExpansion.affine_thresholds d K hK
        (P.expansionScale K) (P.expansionScale_pos hδ hζ hK)
      exact ⟨T₀, p₀, fun _ ↦ h⟩
    · exact ⟨0, 0, fun h ↦ (hK h).elim⟩
  choose widths primes hExp using hthresholds
  let g := drivingFunction widths
  obtain ⟨pDecomp, BK, hpDecomp, hBK, hdecompP⟩ :=
    hdecomp g (drivingFunction_isGrowing widths)
  let Q : ℕ := (Finset.range (BK + 1)).sup fun K ↦ max (P.threshold K) (primes K)
  refine ⟨max pDecomp (max Q 2), ?_⟩
  intro p hp hprime
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  intro f hmass
  have hpD : pDecomp < p := (le_max_left _ _).trans_lt hprime
  have hpQ : Q < p := (le_max_left Q 2).trans_lt ((le_max_right _ _).trans_lt hprime)
  have hp2 : 2 < p := (le_max_right Q 2).trans_lt ((le_max_right _ _).trans_lt hprime)
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨hf, hpMass, hinput_lower, hinput_upper⟩ :=
    normalized_input_bounds hp hd hζ hζ1.le f hmass
  obtain ⟨Φ, T, K, _hcard, _hanti, hK, hbounded, hcomplete, hwidth, hgap, hretained⟩ :=
    hdecompP p hp hpD f hf
  have hthreshold (x : Φ.flag.Node) : P.threshold (K x) < p := by
    have hsup : max (P.threshold (K x)) (primes (K x)) ≤ Q :=
      Finset.le_sup (f := fun k ↦ max (P.threshold k) (primes k))
        (Finset.mem_range.mpr (by have h := (hK x).2; omega))
    exact (le_max_left _ _).trans_lt (hsup.trans_lt hpQ)
  have hprimes (x : Φ.flag.Node) : primes (K x) ≤ p := by
    have hsup : max (P.threshold (K x)) (primes (K x)) ≤ Q :=
      Finset.le_sup (f := fun k ↦ max (P.threshold k) (primes k))
        (Finset.mem_range.mpr (by have h := (hK x).2; omega))
    exact (le_max_right _ _).trans (hsup.trans hpQ.le)
  have hW : (hollowConstant p d : ℝ) ≤ hollowBound d := by
    exact_mod_cast hollowConstant_le_choose_add_one hp hd
  have hretained' : (1 - ε) * ((hollowConstant p d : ℝ) + ζ) * p ≤
      (Φ.retainedMass : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hinput_lower (sub_pos.mpr hε1).le
    calc
      (1 - ε) * ((hollowConstant p d : ℝ) + ζ) * p =
          (1 - ε) * (((hollowConstant p d : ℝ) + ζ) * p) := by ring
      _ ≤ (1 - ε) * (natMass f : ℝ) := h
      _ ≤ (Φ.retainedMass : ℝ) := hretained
  obtain ⟨D, a, hsum, hweighted, hlower, hupper⟩ :=
    P.exists_selected_coefficients Φ hodd hδ hζ hζ1.le hW
      (fun x ↦ (hK x).1) hthreshold hcomplete hbounded hpMass hinput_upper hretained' hgap
  have hgapP (q : Φ.liftedSupport D.node) :
      gapScale d δ (K D.node) * p ≤ (Φ.hat D.node q : ℝ) := by
    apply (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hpMass)
      (gapScale_pos hδ (hK D.node).1).le).trans
    exact (hgap D.node).trans (Nat.cast_le.mpr
      (Φ.gap_le_hat D.node q ((Φ.liftedSupport_spec D.node q).mp q.property)))
  have hslack := P.expansion_slack (K D.node) p
    (fun q : Φ.liftedSupport D.node ↦ Φ.hat D.node q) a hζ hgapP hlower hupper
  have hT : widths (K D.node) ≤ T D.node :=
    (threshold_lt_drivingFunction widths (K D.node)).le.trans (hwidth D.node)
  have hexp := hExp (K D.node) (hK D.node).1 (T D.node) hT p
    inferInstance inferInstance (hprimes D.node)
  exact AffineExpansionAt.decomposition hexp Φ hodd D.node (Φ.representation.rank_le D.node)
    (fun q hq ↦ mem_latticeBox.mp (D.support_subset_box hq))
    D.center (mem_latticeBox.mp D.center_mem_box) a hweighted hsum hslack
    D.complete (P.expansionScale_le_delta (K D.node))

/-- The upper estimate, with exactly the two unproved paper ingredients
as explicit hypotheses. -/
theorem mainUpperBound_of_expansion_balanced
    (hExpansion : RelativeExpansionStatement) (hBalanced : BalancedCombinationLemma)
    (d : ℕ) (hd : 0 < d) : MainUpperBound d :=
  mainUpperBound_of_eventualCeilZeroSum d
    (eventualCeilZeroSum_of_expansion_balanced hExpansion hBalanced d hd)

/-- Conditional assembly of Theorem 1.2. No additional geometric,
rounding, coordinate-change, or uniformity hypotheses are required. -/
theorem mainAsymptotic_of_expansion_balanced
    (hExpansion : RelativeExpansionStatement) (hBalanced : BalancedCombinationLemma)
    (d : ℕ) (hd : 0 < d) : MainAsymptotic d :=
  mainAsymptotic_of_mainUpperBound d hd
    (mainUpperBound_of_expansion_balanced hExpansion hBalanced d hd)

end EGZ
