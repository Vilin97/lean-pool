/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Tricycle.Degree5
import LeanPool.BrillNoetherGraphs.Tricycle.UpperBounds
import LeanPool.BrillNoetherGraphs.Tricycle.RegularSubdivisionBridge
import Mathlib.Tactic

/-!
# Theorem 3.9 and the tricycle gap

The lower half of van Dobben de Bruyn–Smit–van der Wegen's Theorem 3.9 —
`dgon(G) ≥ 6` for every *tricycle* graph, i.e. every subdivision of `T_m` whose
three transition edges are **not** subdivided — and the assembly of the
counterexample.

Given Lemma 3.6, the argument is short.  On a tricycle a chip on a transition
path must sit on a transition vertex, so the outer ring carries exactly three
chips, all on transition vertices, and each cycle carries at most two.  Three is
odd, so some cycle carries exactly one; firing at that cycle's chip-free
transition vertex burns the whole cycle and then leaks one step along the
adjacent transition edge, giving **three** burned transition vertices.  Lemma
3.5(b) charges three chips to the centre and three spoke interiors, but the
centre has two and the spoke interiors have none.

## What is and is not claimed

`baker_subdivision_conjecture_false` refutes Baker, *Specialization of linear
systems from curves to graphs*, Conjecture 3.14(a) at `r = 1` and `k = 2`:
`dgon(σ_k(G)) = dgon(G)` for all `k ≥ 1`.  Conjecture 3.14(b),
`dgon(Γ(G)) = dgon(G)`, follows from (a) by the source's Theorem 1.5
(`dgon(Γ(G)) = min_k dgon(σ_k(G))`), which is **not** formalized here; see
`Utilities/Gonality/GonalityTransport.lean` for why the invariant is named
`regularSubdivisionGonality` rather than `metricGonality`.
-/

namespace Utilities.Tricycle

open Finset

open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec
open Utilities.Gonality

variable {spec : Spec 7 15} {D : CFDiv spec.graph} {w : spec.Vertex}

/-! ## An unsubdivided slot has no interior chips -/

theorem slotInteriorChips_of_length_one {n p : ℕ} {sp : Spec n p} {E : CFDiv sp.graph}
    {e : Fin p} (h : sp.length e = 1) : sp.slotInteriorChips E e = 0 := by
  refine Finset.sum_eq_zero fun j _ => ?_
  exact absurd j.isLt (by omega)

/-! ## Chip-free propagation with explicit hypotheses -/

/-- The fire runs up a chip-free transition path. -/
theorem burned_head_of_chipFree (hcore : spec.core = tricycleCore) (hEff : effective D)
    (i : Fin 3) (hic : spec.slotInteriorChips D (transitionSlot i) = 0)
    (hhead : D (spec.coreVertex (vMinus (i + 1))) = 0)
    (hb : spec.coreVertex (vPlus i) ∈ burned spec.graph D w) :
    spec.coreVertex (vMinus (i + 1)) ∈ burned spec.graph D w := by
  have ha : spec.slotVertex (transitionSlot i) 0 ∈ burned spec.graph D w := by
    rw [slotVertex_zero, transitionSlot_tail hcore]; exact hb
  have hres := mem_burned_slotVertex_of_chipFree_up ha
    (Nat.zero_le (spec.length (transitionSlot i))) (le_refl _) ?_
  · rwa [slotVertex_length, transitionSlot_head hcore] at hres
  · intro k hk0 hkle
    rcases eq_or_lt_of_le hkle with heq | hlt
    · rw [heq, slotVertex_length, transitionSlot_head hcore]; omega
    · have := apply_slotVertex_le_slotInteriorChips hEff (edge := transitionSlot i) hk0 hlt
      omega

/-- The fire runs down a chip-free transition path. -/
theorem burned_tail_of_chipFree (hcore : spec.core = tricycleCore) (hEff : effective D)
    (i : Fin 3) (hic : spec.slotInteriorChips D (transitionSlot i) = 0)
    (htail : D (spec.coreVertex (vPlus i)) = 0)
    (hb : spec.coreVertex (vMinus (i + 1)) ∈ burned spec.graph D w) :
    spec.coreVertex (vPlus i) ∈ burned spec.graph D w := by
  have ha : spec.slotVertex (transitionSlot i) (spec.length (transitionSlot i))
      ∈ burned spec.graph D w := by
    rw [slotVertex_length, transitionSlot_head hcore]; exact hb
  have hres := mem_burned_slotVertex_of_chipFree_down ha
    (Nat.zero_le (spec.length (transitionSlot i))) (le_refl _) ?_
  · rwa [slotVertex_zero, transitionSlot_tail hcore] at hres
  · intro k hk0 hklt
    rcases Nat.eq_zero_or_pos k with hz | hpos
    · rw [hz, slotVertex_zero, transitionSlot_tail hcore]; omega
    · have := apply_slotVertex_le_slotInteriorChips hEff (edge := transitionSlot i) hpos hklt
      omega

/-! ## Three burned transition vertices -/

/-- Three burned transition vertices cost three chips on the centre and their
three spoke interiors. -/
theorem three_le_of_three_burned (hcore : spec.core = tricycleCore)
    (hEff : effective D)
    (hred : qReduced spec.graph (spec.coreVertex centre) D)
    (hrank : rank spec.graph D ≥ 1) (hw : D w = 0)
    {j₁ j₂ j₃ : Fin 6} (h12 : j₁ ≠ j₂) (h13 : j₁ ≠ j₃) (h23 : j₂ ≠ j₃)
    (hb1 : spec.coreVertex (transitionOf j₁) ∈ burned spec.graph D w)
    (hb2 : spec.coreVertex (transitionOf j₂) ∈ burned spec.graph D w)
    (hb3 : spec.coreVertex (transitionOf j₃) ∈ burned spec.graph D w) :
    3 ≤ D (spec.coreVertex 0) + spec.slotInteriorChips D (spokeOf j₁)
      + spec.slotInteriorChips D (spokeOf j₂)
      + spec.slotInteriorChips D (spokeOf j₃) := by
  classical
  have hmem : ∀ j ∈ ({j₁, j₂, j₃} : Finset (Fin 6)),
      spec.coreVertex (transitionOf j) ∈ burned spec.graph D w := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl <;> assumption
  have h := helper_lemma_b hcore hEff hred hrank hw
    ({j₁, j₂, j₃} : Finset (Fin 6)) hmem
  have hnot1 : j₁ ∉ ({j₂, j₃} : Finset (Fin 6)) := by simp [h12, h13]
  have hnot2 : j₂ ∉ ({j₃} : Finset (Fin 6)) := by simp [h23]
  rw [Finset.card_insert_of_notMem hnot1, Finset.card_insert_of_notMem hnot2,
    Finset.card_singleton, Finset.sum_insert hnot1, Finset.sum_insert hnot2,
    Finset.sum_singleton] at h
  have hcentre : spec.coreVertex centre = spec.coreVertex 0 := rfl
  rw [hcentre] at h
  push_cast at h
  omega

/-! ## The two burning cases of Theorem 3.9 -/

/-- The cycle `Cᵢ`'s single chip sits on `vᵢ⁺`: firing at `vᵢ⁻` burns `vᵢ⁻`,
`vᵢ⁺` and `vᵢ₊₁⁻`. -/
theorem three_burned_forward (hcore : spec.core = tricycleCore) (hEff : effective D)
    (i : Fin 3) (hcy : cycleChips spec D i ≤ 1)
    (_hm : D (spec.coreVertex (vMinus i)) = 0)
    (hic : spec.slotInteriorChips D (transitionSlot i) = 0)
    (hnext : D (spec.coreVertex (vMinus (i + 1))) = 0) :
    spec.coreVertex (vMinus i) ∈ burned spec.graph D (spec.coreVertex (vMinus i)) ∧
      spec.coreVertex (vPlus i) ∈ burned spec.graph D (spec.coreVertex (vMinus i)) ∧
      spec.coreVertex (vMinus (i + 1))
        ∈ burned spec.graph D (spec.coreVertex (vMinus i)) := by
  have h1 : spec.coreVertex (vMinus i)
      ∈ burned spec.graph D (spec.coreVertex (vMinus i)) := mem_burned_self
  have h2 : spec.coreVertex (vPlus i)
      ∈ burned spec.graph D (spec.coreVertex (vMinus i)) := by
    by_contra hcon
    have := two_le_cycleChips_of_minus_burned hcore hEff i h1 hcon
    omega
  exact ⟨h1, h2, burned_head_of_chipFree hcore hEff i hic hnext h2⟩

/-- The cycle `Cᵢ`'s single chip sits on `vᵢ⁻`: firing at `vᵢ⁺` burns `vᵢ⁺`,
`vᵢ⁻` and `vᵢ₊₂⁺`. -/
theorem three_burned_backward (hcore : spec.core = tricycleCore) (hEff : effective D)
    (i : Fin 3) (hcy : cycleChips spec D i ≤ 1)
    (_hp : D (spec.coreVertex (vPlus i)) = 0)
    (hic : spec.slotInteriorChips D (transitionSlot (i + 2)) = 0)
    (hprev : D (spec.coreVertex (vPlus (i + 2))) = 0) :
    spec.coreVertex (vPlus i) ∈ burned spec.graph D (spec.coreVertex (vPlus i)) ∧
      spec.coreVertex (vMinus i) ∈ burned spec.graph D (spec.coreVertex (vPlus i)) ∧
      spec.coreVertex (vPlus (i + 2))
        ∈ burned spec.graph D (spec.coreVertex (vPlus i)) := by
  have h1 : spec.coreVertex (vPlus i)
      ∈ burned spec.graph D (spec.coreVertex (vPlus i)) := mem_burned_self
  have h2 : spec.coreVertex (vMinus i)
      ∈ burned spec.graph D (spec.coreVertex (vPlus i)) := by
    by_contra hcon
    have := two_le_cycleChips_of_plus_burned hcore hEff i h1 hcon
    omega
  refine ⟨h1, h2, ?_⟩
  refine burned_tail_of_chipFree hcore hEff (i + 2) hic hprev ?_
  rw [fin3_add_two_add_one]
  exact h2

/-! ## Theorem 3.9, lower half -/

/-- The fifteen slot-interior totals, written out. -/
theorem sum_slotInteriorChips_expand (spec : Spec 7 15) (D : CFDiv spec.graph) :
    ∑ e : Fin 15, spec.slotInteriorChips D e =
      spec.slotInteriorChips D 0 + spec.slotInteriorChips D 1
        + spec.slotInteriorChips D 2 + spec.slotInteriorChips D 3
        + spec.slotInteriorChips D 4 + spec.slotInteriorChips D 5
        + spec.slotInteriorChips D 6 + spec.slotInteriorChips D 7
        + spec.slotInteriorChips D 8 + spec.slotInteriorChips D 9
        + spec.slotInteriorChips D 10 + spec.slotInteriorChips D 11
        + spec.slotInteriorChips D 12 + spec.slotInteriorChips D 13
        + spec.slotInteriorChips D 14 := by
  simp [Fin.sum_univ_succ]
  ring

/-- The parity step of Theorem 3.9: the outer ring's three chips sit on the six
transition vertices, one per transition path, so some cycle carries exactly one
chip — and then one of its two transition vertices is chip-free. -/
theorem tricycle_parity_split {c1 c2 c3 c4 c5 c6 : ℤ}
    (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (h3 : 0 ≤ c3) (h4 : 0 ≤ c4) (h5 : 0 ≤ c5)
    (h6 : 0 ≤ c6) (e1 : c2 + c3 = 1) (e2 : c4 + c5 = 1) (e3 : c6 + c1 = 1) :
    (c1 = 0 ∧ c2 = 1) ∨ (c1 = 1 ∧ c2 = 0) ∨ (c3 = 0 ∧ c4 = 1)
      ∨ (c3 = 1 ∧ c4 = 0) ∨ (c5 = 0 ∧ c6 = 1) ∨ (c5 = 1 ∧ c6 = 0) := by
  omega

/-- **Theorem 3.9, lower half.**  Every tricycle graph — every subdivision of
the minimal tricycle whose three transition edges are unsubdivided — has
divisorial gonality at least six. -/
theorem six_le_divisorialGonality (hcore : spec.core = tricycleCore)
    (htri : IsTricycle spec.length) (hconn : graphConnected spec.graph) :
    6 ≤ divisorialGonality spec.graph := by
  refine le_divisorialGonality_of_no_small hconn ?_
  intro E hEeff hEdeg hErank
  obtain ⟨D, hequiv, hred⟩ :=
    exists_q_reduced_representative hconn (spec.coreVertex centre) E
  have hrank : rank spec.graph D ≥ 1 := by
    rwa [← Utilities.rank_eq_of_linear_equiv spec.graph hequiv]
  have hwin : winnable spec.graph D :=
    (rank_nonneg_iff_winnable spec.graph D).mp
      ((rank_geq_iff spec.graph D 0).mpr (by omega))
  have hEff : effective D :=
    effective_of_winnable_and_q_reduced spec.graph _ D hwin hred
  have hdeg : deg D = 5 := by
    rw [← linear_equiv_preserves_deg spec.graph E D hequiv]
    simpa using hEdeg
  obtain ⟨hc, htp0, htp1, htp2⟩ := lemma_graad5 hcore hEff hred hrank (by omega)
  have hicT : ∀ i : Fin 3, spec.slotInteriorChips D (transitionSlot i) = 0 :=
    fun i => slotInteriorChips_of_length_one (htri i)
  have hcn : ∀ v : Fin 7, 0 ≤ D (spec.coreVertex v) := fun v => hEff _
  have hin : ∀ e : Fin 15, 0 ≤ spec.slotInteriorChips D e := fun e =>
    slotInteriorChips_nonneg hEff e
  have hd := deg_expand spec D
  have hs := sum_slotInteriorChips_expand spec D
  have hT0 := hicT 0
  have hT1 := hicT 1
  have hT2 := hicT 2
  simp only [transitionSlot_0, transitionSlot_1, transitionSlot_2] at hT0 hT1 hT2
  simp only [transitionPathChips, vMinus_0, vMinus_1, vMinus_2, vPlus_0, vPlus_1,
    vPlus_2, transitionSlot_0, transitionSlot_1, transitionSlot_2,
    fin3_01, fin3_11, fin3_21] at htp0 htp1 htp2
  -- every slot interior is empty of chips
  have hsum0 : ∑ e : Fin 15, spec.slotInteriorChips D e = 0 := by
    rw [hs]
    omega
  have hzero : ∀ e : Fin 15, spec.slotInteriorChips D e = 0 := by
    intro e
    have hle := Finset.single_le_sum
      (f := fun e : Fin 15 => spec.slotInteriorChips D e)
      (fun e _ => hin e) (Finset.mem_univ e)
    have := hin e
    omega
  -- the contradiction driver
  have hcontra : ∀ (j₁ j₂ j₃ : Fin 6) (u₁ u₂ u₃ : Fin 7) (v : spec.Vertex),
      spec.coreVertex u₁ ∈ burned spec.graph D v →
      spec.coreVertex u₂ ∈ burned spec.graph D v →
      spec.coreVertex u₃ ∈ burned spec.graph D v →
      D v = 0 → j₁ ≠ j₂ → j₁ ≠ j₃ → j₂ ≠ j₃ →
      transitionOf j₁ = u₁ → transitionOf j₂ = u₂ → transitionOf j₃ = u₃ →
      False := by
    rintro j₁ j₂ j₃ u₁ u₂ u₃ v hb1 hb2 hb3 hv h12 h13 h23 rfl rfl rfl
    have h := three_le_of_three_burned hcore hEff hred hrank hv h12 h13 h23
      hb1 hb2 hb3
    have e1 := hzero (spokeOf j₁)
    have e2 := hzero (spokeOf j₂)
    have e3 := hzero (spokeOf j₃)
    omega
  -- the outer ring carries three chips, all on transition vertices, and each
  -- cycle carries at most two; three is odd, so some cycle carries exactly one
  have hsplit :
      (D (spec.coreVertex 1) = 0 ∧ D (spec.coreVertex 2) = 1) ∨
      (D (spec.coreVertex 1) = 1 ∧ D (spec.coreVertex 2) = 0) ∨
      (D (spec.coreVertex 3) = 0 ∧ D (spec.coreVertex 4) = 1) ∨
      (D (spec.coreVertex 3) = 1 ∧ D (spec.coreVertex 4) = 0) ∨
      (D (spec.coreVertex 5) = 0 ∧ D (spec.coreVertex 6) = 1) ∨
      (D (spec.coreVertex 5) = 1 ∧ D (spec.coreVertex 6) = 0) := by
    refine tricycle_parity_split (hcn 1) (hcn 2) (hcn 3) (hcn 4) (hcn 5) (hcn 6)
      ?_ ?_ ?_ <;> omega
  have hz0 := hzero 6
  have hz1 := hzero 7
  have hz2 := hzero 8
  have hz3 := hzero 9
  have hz4 := hzero 10
  have hz5 := hzero 11
  rcases hsplit with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · -- `C₁`'s chip is on `v₁⁺`
    have hcy : cycleChips spec D 0 ≤ 1 := by
      simp only [cycleChips, vMinus_0, vPlus_0, cycleSlot_00, cycleSlot_01]; omega
    obtain ⟨hb1, hb2, hb3⟩ := three_burned_forward hcore hEff 0 hcy
      (by rw [vMinus_0]; exact ha) (hicT 0)
      (by rw [fin3_01, vMinus_1]; omega)
    exact hcontra 0 1 2 _ _ _ _ hb1 hb2 hb3 (by rw [vMinus_0]; exact ha)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · -- `C₁`'s chip is on `v₁⁻`
    have hcy : cycleChips spec D 0 ≤ 1 := by
      simp only [cycleChips, vMinus_0, vPlus_0, cycleSlot_00, cycleSlot_01]; omega
    obtain ⟨hb1, hb2, hb3⟩ := three_burned_backward hcore hEff 0 hcy
      (by rw [vPlus_0]; exact hb) (by rw [fin3_02]; exact hicT 2)
      (by rw [fin3_02, vPlus_2]; omega)
    exact hcontra 1 0 5 _ _ _ _ hb1 hb2 hb3 (by rw [vPlus_0]; exact hb)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · -- `C₂`'s chip is on `v₂⁺`
    have hcy : cycleChips spec D 1 ≤ 1 := by
      simp only [cycleChips, vMinus_1, vPlus_1, cycleSlot_10, cycleSlot_11]; omega
    obtain ⟨hb1, hb2, hb3⟩ := three_burned_forward hcore hEff 1 hcy
      (by rw [vMinus_1]; exact ha) (hicT 1)
      (by rw [fin3_11, vMinus_2]; omega)
    exact hcontra 2 3 4 _ _ _ _ hb1 hb2 hb3 (by rw [vMinus_1]; exact ha)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · -- `C₂`'s chip is on `v₂⁻`
    have hcy : cycleChips spec D 1 ≤ 1 := by
      simp only [cycleChips, vMinus_1, vPlus_1, cycleSlot_10, cycleSlot_11]; omega
    obtain ⟨hb1, hb2, hb3⟩ := three_burned_backward hcore hEff 1 hcy
      (by rw [vPlus_1]; exact hb) (by rw [fin3_12]; exact hicT 0)
      (by rw [fin3_12, vPlus_0]; omega)
    exact hcontra 3 2 1 _ _ _ _ hb1 hb2 hb3 (by rw [vPlus_1]; exact hb)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · -- `C₃`'s chip is on `v₃⁺`
    have hcy : cycleChips spec D 2 ≤ 1 := by
      simp only [cycleChips, vMinus_2, vPlus_2, cycleSlot_20, cycleSlot_21]; omega
    obtain ⟨hb1, hb2, hb3⟩ := three_burned_forward hcore hEff 2 hcy
      (by rw [vMinus_2]; exact ha) (hicT 2)
      (by rw [fin3_21, vMinus_0]; omega)
    exact hcontra 4 5 0 _ _ _ _ hb1 hb2 hb3 (by rw [vMinus_2]; exact ha)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · -- `C₃`'s chip is on `v₃⁻`
    have hcy : cycleChips spec D 2 ≤ 1 := by
      simp only [cycleChips, vMinus_2, vPlus_2, cycleSlot_20, cycleSlot_21]; omega
    obtain ⟨hb1, hb2, hb3⟩ := three_burned_backward hcore hEff 2 hcy
      (by rw [vPlus_2]; exact hb) (by rw [fin3_22]; exact hicT 1)
      (by rw [fin3_22, vPlus_1]; omega)
    exact hcontra 5 4 3 _ _ _ _ hb1 hb2 hb3 (by rw [vPlus_2]; exact hb)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ## Two specifications with the same core and the same lengths -/

/-- Two subdivision specifications over the same core with the same slot lengths
present the same graph.  (`Spec` is a structure, so this is not `rfl`: the two
length functions are only pointwise equal.) -/
def sameLengthRelabeling {n p : ℕ} (s t : Spec n p) (hc : s.core = t.core)
    (hl : ∀ e, s.length e = t.length e) : s.Relabeling t where
  coreEquiv := Equiv.refl _
  slotEquiv := Equiv.refl _
  reversed := fun _ => false
  length_eq := hl
  tail_eq := by intro e; rw [hc]; simp
  head_eq := by intro e; rw [hc]; simp

/-! ## The minimal tricycle and its `2`-subdivision -/

theorem Tm_core : Tm.core = tricycleCore := rfl

theorem Tm2_core : Tm2.core = tricycleCore := rfl

theorem Tm_isTricycle : IsTricycle Tm.length := fun _ => rfl

/-- **`dgon(T_m) = 6`.**  Theorem 3.9 for the minimal tricycle. -/
theorem divisorialGonality_Tm : divisorialGonality Tm.graph = 6 :=
  le_antisymm divisorialGonality_Tm_le_six
    (six_le_divisorialGonality Tm_core Tm_isTricycle Tm_connected)

/-- **`dgon(σ₂(T_m)) = 5`.**  Proposition 3.3 together with Corollary 3.7. -/
theorem divisorialGonality_Tm2 : divisorialGonality Tm2.graph = 5 :=
  le_antisymm divisorialGonality_Tm2_le_five
    (five_le_divisorialGonality Tm2_core Tm2_connected)

/-- Scaling `T_m` by two is `σ₂(T_m)`. -/
theorem divisorialGonality_Tm_scale_two (hk : 0 < 2) :
    divisorialGonality (Tm.scale 2 hk).graph = 5 := by
  rw [divisorialGonality_of_laplacianEquiv
    (Spec.laplacianEquiv _ _
      (sameLengthRelabeling (Tm.scale 2 hk) Tm2 rfl (fun _ => rfl)))]
  exact divisorialGonality_Tm2

/-- Every `σ_k(T_m)` is a subdivision of the tricycle core, hence connected. -/
theorem Tm_scale_connected (k : ℕ) (hk : 0 < k) :
    graphConnected (Tm.scale k hk).graph :=
  (Tm.scale k hk).graph_connected_of_coreConnected tricycleCore_connected

/-! ## The gap -/

/-- **`min_{k ≥ 1} dgon(σ_k(T_m)) = 5`.**  The upper bound is `k = 2`
(Proposition 3.3); the lower bound is Corollary 3.7, which holds at *every* `k`
— and must, since `k ↦ dgon(σ_k(T_m))` is not monotone (`dgon(σ₃) = 6`). -/
theorem Tm_regularSubdivisionGonality : Tm.regularSubdivisionGonality = 5 := by
  refine le_antisymm ?_ ?_
  · exact Tm.regularSubdivisionGonality_le (k := 2) (by omega)
      (divisorialGonality_Tm_scale_two (by omega))
  · refine Tm.le_regularSubdivisionGonality ?_
    intro k hk
    exact five_le_divisorialGonality (spec := Tm.scale k hk) rfl (Tm_scale_connected k hk)

/-- **The tricycle gap.**  The minimal tricycle `T_m` — a connected loopless
multigraph on seven vertices with fifteen edges and cyclomatic genus nine —
satisfies `min_{k ≥ 1} dgon(σ_k(T_m)) = 5 < 6 = dgon(T_m)`. -/
theorem tricycle_gap :
    Tm.regularSubdivisionGonality < divisorialGonality Tm.graph := by
  rw [Tm_regularSubdivisionGonality, divisorialGonality_Tm]
  omega

/-- **Baker's Conjecture 3.14(a) is false.**  Baker, *Specialization of linear
systems from curves to graphs*, Conjecture 3.14(a) asserts
`dgon_r(σ_k(G)) = dgon_r(G)` for every connected loopless multigraph `G`, every
`r ≥ 1` and every `k ≥ 1`.  It already fails at `r = 1` and `k = 2`, on the
minimal tricycle.

Conjecture 3.14(b), `dgon_r(Γ(G)) = dgon_r(G)`, follows from (a) through the
source's Theorem 1.5, `dgon_r(Γ(G)) = min_k dgon_r(σ_k(G))`, which is deliberately
**not** formalized here — see `Utilities/Gonality/GonalityTransport.lean`. -/
theorem baker_subdivision_conjecture_false :
    ¬ ∀ (n p : ℕ) (sp : Spec n p) (k : ℕ) (hk : 0 < k),
        graphConnected sp.graph →
        divisorialGonality (sp.scale k hk).graph = divisorialGonality sp.graph := by
  intro h
  have hk : (0 : ℕ) < 2 := by omega
  have hfail := h 7 15 Tm 2 hk Tm_connected
  rw [divisorialGonality_Tm_scale_two hk, divisorialGonality_Tm] at hfail
  omega

/-! ## The gap at the level of an arbitrary `CFGraph`

`regularSubdivisionGonality : CFGraph → ℕ` builds `σ_k` on the *occurrence
presentation* of its argument, which labels vertices and edge occurrences by
arbitrary bijections.  `Tricycle/RegularSubdivisionBridge.lean`
identifies that construction with slot scaling for a unit-length specification,
which lets the whole statement be made without mentioning `Spec`. -/

theorem Tm_unitLength : ∀ e : Fin 15, Tm.length e = 1 := fun _ => rfl

/-- **`min_{k ≥ 1} dgon(σ_k(T_m)) = 5`**, with `σ_k` built on the occurrence
presentation of `T_m` rather than on the tricycle core. -/
theorem regularSubdivisionGonality_Tm :
    regularSubdivisionGonality Tm.graph = 5 := by
  rw [Spec.regularSubdivisionGonality_graph Tm Tm_unitLength]
  exact Tm_regularSubdivisionGonality

/-- **The tricycle gap**, with both sides invariants of the bare graph. -/
theorem tricycle_gap_graph :
    regularSubdivisionGonality Tm.graph < divisorialGonality Tm.graph := by
  rw [regularSubdivisionGonality_Tm, divisorialGonality_Tm]
  omega

/-- **Baker's Conjecture 3.14(a) is false**, stated for an arbitrary connected
loopless multigraph and the canonical `σ_k` construction.

Baker, *Specialization of linear systems from curves to graphs*,
Conjecture 3.14(a): `dgon_r(σ_k(G)) = dgon_r(G)` for every connected loopless
multigraph `G`, every `r ≥ 1` and every `k ≥ 1`.  It fails already at `r = 1`
and `k = 2`, on the minimal tricycle. -/
theorem baker_conjecture_3_14a_false :
    ¬ ∀ (G : CFGraph.{0}) (k : ℕ) (hk : 0 < k), graphConnected G →
        divisorialGonality (regularSubdivision G k hk) = divisorialGonality G := by
  intro h
  have hk : (0 : ℕ) < 2 := by omega
  have hfail := h Tm.graph 2 hk Tm_connected
  rw [Spec.divisorialGonality_regularSubdivision Tm Tm_unitLength 2 hk,
    divisorialGonality_Tm_scale_two hk, divisorialGonality_Tm] at hfail
  omega

end Utilities.Tricycle
