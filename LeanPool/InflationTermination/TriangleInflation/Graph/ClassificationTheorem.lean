/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/

import LeanPool.InflationTermination.TriangleInflation.Graph.Classification
import LeanPool.InflationTermination.TriangleInflation.Graph.DoubleStarForest
import LeanPool.InflationTermination.TriangleInflation.Graph.FivePathWitness
import LeanPool.InflationTermination.TriangleInflation.Graph.CycleObstruction

/-!
# The classification theorem (A7)

Theorem `thm:classification`: for a pair-source scenario with binary observations, some finite order of the Navascués–Wolfe test (equivalently of the ancestral-independence test, equivalently of the recursively expressible test) equals the compatible set iff every connected component is a double-star (`classification_NW_lib`, `classification_AI`, `classification_exp`), with the nontermination half `nontermination_of_not_doubleStar` assembled from the cycle and five-path witnesses, transport, exhaustion, and local flips. Everything here is proved.
-/

namespace TriangleInflation.Graph

open Finset TriangleInflation

variable {Γ : PairGraph} {t : ℕ}

/-- AUDIT-NOTES A7, the nontermination half. A pair graph with a component that is not a
double star carries, at every order, a full-support target that passes the recursively
expressible test and is incompatible. Full support comes from independent local flips at
every copied observation, which preserve symmetry and all AI products. -/
theorem nontermination_of_not_doubleStar (Γ : PairGraph) (hnot : ¬ IsDoubleStarForest Γ.G)
    (t : ℕ) (ht : 1 ≤ t) :
    ∃ P : GTarget Γ, IsLaw P ∧ (∀ w, 0 < P w) ∧ GExpFeasible Γ t P ∧ ¬ GCompatible Γ P := by
  -- It is enough to find a connected induced sub-scenario carrying a positive, AI feasible,
  -- incompatible law: transport moves it to `Γ`.
  suffices hgen : ∃ (H : PairGraph) (φ : H.V → Γ.V), Function.Injective φ ∧
      (∀ u v : H.V, H.G.Adj u v ↔ Γ.G.Adj (φ u) (φ v)) ∧ H.G.Connected ∧
      ∃ Q : GTarget H, (∀ w, 0 < Q w) ∧ GAIFeasible H t Q ∧ ¬ GCompatible H Q by
    obtain ⟨H, φ, hφ, hind, hconn, Q, hQpos, hQai, hQinc⟩ := hgen
    obtain ⟨hai, hinc⟩ := induced_transport Γ H φ hφ hind hconn t Q hQai hQinc
    refine ⟨transportTarget Γ H φ Q, isLaw_of_gAIFeasible Γ t ht _ hai, fun w => ?_,
      (gExpFeasible_iff_gAIFeasible Γ t _).mpr hai, hinc⟩
    have hp : (0:ℝ) < (1 / 2 : ℝ) ^ (Fintype.card Γ.V - Fintype.card H.V) := by positivity
    change (0:ℝ) < Q (fun u => w (φ u)) * (1 / 2 : ℝ) ^ (Fintype.card Γ.V - Fintype.card H.V)
    exact mul_pos (hQpos _) hp
  -- Some component is not a double star; it is connected, so exhaustion applies to it.
  obtain ⟨C, hC⟩ := exists_bad_component Γ hnot
  obtain ⟨ρ, hρ, hρind⟩ := componentPairGraph_embed Γ C
  have hKconn : (componentPairGraph Γ C).G.Connected :=
    SimpleGraph.ConnectedComponent.connected_toSimpleGraph C
  have ht0 : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
  have ht1 : (1:ℝ) ≤ (t:ℝ) ^ 2 := by nlinarith
  rcases exhaustion (componentPairGraph Γ C) hKconn hC with
    ⟨m, hm, ψ, hψ, hψind⟩ | ⟨ψ, hψ, hψind⟩
  · -- an induced cycle: the cycle target, flipped enough to be positive but not enough to
    -- become compatible
    have hm3 : (3:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    have hm0 : (0:ℝ) < (m:ℝ) := by linarith
    set q : ℝ := 1 / (4 * (m:ℝ) ^ 2 * (t:ℝ) ^ 2) with hqdef
    have hq0 : 0 < q := by rw [hqdef]; positivity
    have hmq : (m:ℝ) ^ 2 * q = 1 / (4 * (t:ℝ) ^ 2) := by
      rw [hqdef]; field_simp
    have hqm : (m:ℝ) ^ 2 * q ≤ 1 / 4 := by
      rw [hmq]
      have : (1:ℝ) / (4 * (t:ℝ) ^ 2) ≤ 1 / 4 :=
        one_div_le_one_div_of_le (by norm_num) (by nlinarith)
      linarith
    have hq4 : q ≤ 1 / 4 := by nlinarith
    set η : ℝ := q / (24 * (m:ℝ)) with hηdef
    have hη0 : 0 < η := by rw [hηdef]; positivity
    have hη1 : η < 1 := by
      rw [hηdef, div_lt_one (by positivity)]
      linarith
    have hlaw0 : IsLaw (cycleTarget m q) := cycleTarget_isLaw m hm q hq0.le hqm
    refine ⟨cycle m hm, fun i => ρ (ψ i), fun a b hab => hψ (hρ hab),
      fun u v => (hψind u v).trans (hρind _ _), cycleAdj_connected m hm,
      flipLaw η (cycleTarget m q), flip_full_support η hη0 hη1 _ hlaw0,
      flip_gAIFeasible (cycle m hm) t (cycleTarget m q) η hη0.le hη1.le
        (cycle_witness m t hm ht q hqdef), ?_⟩
    intro hcomp
    have hd1 := cycle_distance m hm q hq0 hqm
    have hd2 := distToCompatible_le (cycle m hm) (cycleTarget m q) _ hcomp
    have hd3 := dTV_flipLaw_le (ι := (cycle m hm).V) η hη0.le hη1.le (cycleTarget m q) hlaw0
    have hcard : Fintype.card (cycle m hm).V = m := Fintype.card_fin m
    rw [hcard] at hd3
    have hmη : (m:ℝ) * η = q / 24 := by rw [hηdef]; field_simp
    linarith
  · -- an induced five-path: the five-path target is already bounded away from zero
    set s : ℝ := 1 / (16 * (t:ℝ) ^ 2) with hsdef
    have hs0 : 0 < s := by rw [hsdef]; positivity
    have hs1 : s < 1 := by
      rw [hsdef, div_lt_one (by positivity)]
      nlinarith
    obtain ⟨hlaw5, hlb5⟩ := fivePathTarget_isLaw s hs0.le hs1
    refine ⟨fivePathGraph, fun i => ρ (ψ i), fun a b hab => hψ (hρ hab),
      fun u v => (hψind u v).trans (hρind _ _), pathAdj_five_connected,
      fivePathTarget s, fun w => lt_of_lt_of_le ?_ (hlb5 w),
      fivePath_witness t ht s hsdef, fivePath_not_compatible s hs0 hs1⟩
    linarith

/-- AUDIT-NOTES A7, the classification theorem for the Navascués–Wolfe hierarchy: some finite
order of the hierarchy equals the compatible set exactly when every connected component of
the graph is a double star.

The plain name `TriangleInflation.Graph.classification_NW` is reserved for the registry
statement, which `PalomarSolutions/TriangleInflationClassification.lean` declares and
discharges by this theorem; Comparator identifies the Challenge and the Solution by that one
name. -/
theorem classification_NW_lib (Γ : PairGraph) :
    (∃ t : ℕ, 1 ≤ t ∧ ∀ P : GTarget Γ, IsLaw P → (GNWFeasible Γ t P ↔ GCompatible Γ P))
      ↔ IsDoubleStarForest Γ.G := by
  constructor
  · rintro ⟨t, ht, h⟩
    by_contra hnot
    obtain ⟨P, hlaw, -, hexp, hincomp⟩ := nontermination_of_not_doubleStar Γ hnot t ht
    exact hincomp ((h P hlaw).mp
      (gNWFeasible_of_gAIFeasible Γ t P (gAIFeasible_of_gExpFeasible Γ t P hexp)))
  · intro hG
    exact ⟨2, by norm_num, fun P hP => doubleStar_terminates Γ hG P hP⟩

/-- AUDIT-NOTES A7 for the ancestral-independence hierarchy. -/
theorem classification_AI (Γ : PairGraph) :
    (∃ t : ℕ, 1 ≤ t ∧ ∀ P : GTarget Γ, IsLaw P → (GAIFeasible Γ t P ↔ GCompatible Γ P))
      ↔ IsDoubleStarForest Γ.G := by
  constructor
  · rintro ⟨t, ht, h⟩
    by_contra hnot
    obtain ⟨P, hlaw, -, hexp, hincomp⟩ := nontermination_of_not_doubleStar Γ hnot t ht
    exact hincomp ((h P hlaw).mp (gAIFeasible_of_gExpFeasible Γ t P hexp))
  · intro hG
    refine ⟨2, by norm_num, fun P hP => ⟨fun hAI => ?_, fun hc => compatible_gAIFeasible Γ 2 P hc⟩⟩
    exact (doubleStar_terminates Γ hG P hP).mp (gNWFeasible_of_gAIFeasible Γ 2 P hAI)

/-- AUDIT-NOTES A7 for the recursively expressible hierarchy. -/
theorem classification_exp (Γ : PairGraph) :
    (∃ t : ℕ, 1 ≤ t ∧ ∀ P : GTarget Γ, IsLaw P → (GExpFeasible Γ t P ↔ GCompatible Γ P))
      ↔ IsDoubleStarForest Γ.G := by
  constructor
  · rintro ⟨t, ht, h⟩
    by_contra hnot
    obtain ⟨P, hlaw, -, hexp, hincomp⟩ := nontermination_of_not_doubleStar Γ hnot t ht
    exact hincomp ((h P hlaw).mp hexp)
  · intro hG
    refine ⟨2, by norm_num,
      fun P hP => ⟨fun hexp => ?_, fun hc => compatible_gExpFeasible Γ 2 P hc⟩⟩
    exact (doubleStar_terminates Γ hG P hP).mp
      (gNWFeasible_of_gAIFeasible Γ 2 P (gAIFeasible_of_gExpFeasible Γ 2 P hexp))


end TriangleInflation.Graph
