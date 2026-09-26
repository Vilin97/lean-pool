/-
Copyright (c) 2026 ukiyois, OpenCode agent sessions. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ukiyois, OpenCode agent sessions
-/
module

public import LeanPool.HardSphereNBC.HardSphereTreeEdges


/-!
# HardSphereCompound

Graph, coordinate, and measure constructions for the hard-sphere NBC volume identity.
-/

@[expose] public section

namespace HsVirial

open Set
open Metric
open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- An ordered triple used to name an order-compatible fork `(a,b,c)` with
`a < b < c`, where `a` is the center and `b,c` are the leaves. -/
abbrev HardSphereForkTriple (k : Nat) := Fin k × Fin k × Fin k

/-- The three vertices supporting an order-compatible fork triple. -/
def hardSphereForkSupport {k : Nat} (f : HardSphereForkTriple k) : Finset (Fin k) :=
  {f.1, f.2.1, f.2.2}

/-- The event associated with an order-compatible fork triple. -/
def hardSphereForkEventOfTriple {k : Nat} [NeZero k]
    (T : Finset (Sym2 (Fin k))) (f : HardSphereForkTriple k) :
    Set (HardSphereConfiguration k 3) :=
  hardSphereForkEvent T f.1 f.2.1 f.2.2

/-- A finite family of pairwise vertex-disjoint, order-compatible forks in a tree. -/
def hardSphereForkPacking {k : Nat}
    (T : Finset (Sym2 (Fin k))) (P : Finset (HardSphereForkTriple k)) : Prop :=
  (∀ f ∈ P, hardSphereFork T f.1 f.2.1 f.2.2) ∧
    (∀ f ∈ P, ∀ g ∈ P, f ≠ g →
      ∀ x, x ∈ hardSphereForkSupport f →
        x ∈ hardSphereForkSupport g → False)

lemma hardSphereForkSupport_card_of_mem_forkPacking {k : Nat}
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hP : hardSphereForkPacking T P)
    {f : HardSphereForkTriple k} (hf : f ∈ P) :
    (hardSphereForkSupport f).card = 3 := by
  have hfork := hP.1 f hf
  rcases f with ⟨a, b, c⟩
  simp only [hardSphereForkSupport] at *
  simp [ne_of_lt hfork.1, ne_of_lt hfork.2.1,
    ne_of_lt (lt_trans hfork.1 hfork.2.1)]

lemma hardSphereForkPacking_three_mul_card_le {k : Nat}
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hP : hardSphereForkPacking T P) :
    3 * P.card ≤ k := by
  classical
  have hdisj : (P : Set (HardSphereForkTriple k)).PairwiseDisjoint
      hardSphereForkSupport := by
    intro f hf g hg hfg
    change Disjoint (hardSphereForkSupport f) (hardSphereForkSupport g)
    apply Finset.disjoint_left.mpr
    exact fun x hxf hxg => hP.2 f hf g hg hfg x hxf hxg
  have hsum : ∑ f ∈ P, (hardSphereForkSupport f).card = 3 * P.card := by
    calc
      ∑ f ∈ P, (hardSphereForkSupport f).card = ∑ _f ∈ P, 3 := by
        apply Finset.sum_congr rfl
        intro f hf
        exact hardSphereForkSupport_card_of_mem_forkPacking hP hf
      _ = 3 * P.card := by simp [Nat.mul_comm]
  calc
    3 * P.card = (P.biUnion hardSphereForkSupport).card := by
      rw [Finset.card_biUnion hdisj, hsum]
    _ ≤ (Finset.univ : Finset (Fin k)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = k := by simp

lemma hardSphereForkPacking_two_mul_card_le_pred {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hP : hardSphereForkPacking T P) :
    2 * P.card ≤ k - 1 := by
  have hkpos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hthree := hardSphereForkPacking_three_mul_card_le hP
  omega

/-- The finite region avoiding every order-compatible fork event in a selected
packing. -/
def hardSphereForkAvoidanceRegion {k : Nat} [NeZero k]
    (T : Finset (Sym2 (Fin k))) (P : Finset (HardSphereForkTriple k)) :
    Set (HardSphereConfiguration k 3) :=
  ⋂ f ∈ P, (hardSphereForkEventOfTriple T f)ᶜ

lemma measurableSet_hardSphereForkAvoidanceRegion {k : Nat} [NeZero k]
    (T : Finset (Sym2 (Fin k))) (P : Finset (HardSphereForkTriple k)) :
    MeasurableSet (hardSphereForkAvoidanceRegion T P) := by
  rw [show hardSphereForkAvoidanceRegion T P =
      ⋂ f ∈ P, (hardSphereForkEventOfTriple T f)ᶜ by rfl]
  exact P.measurableSet_biInter (fun f hf =>
    (measurableSet_hardSphereForkEvent T f.1 f.2.1 f.2.2).compl)

lemma hardSphere_nbc_region_subset_forkAvoidance
    {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hP : hardSphereForkPacking T P) :
    nbcRegion (V := Fin k)
        (hardSphereActiveExact (k := k) (d := 3)) T ⊆
      hardSphereForkAvoidanceRegion T P := by
  intro r hr
  rw [hardSphereForkAvoidanceRegion]
  simp only [mem_iInter]
  intro f hf hrf
  exact Set.disjoint_left.mp
    (hardSphere_nbc_region_disjoint_forkEvent (T := T) (hP.1 f hf)) hr hrf

lemma hardSphere_nbc_region_measure_le_forkAvoidance
    {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hP : hardSphereForkPacking T P) :
    (volume : Measure (HardSphereConfiguration k 3))
        (nbcRegion (V := Fin k)
          (hardSphereActiveExact (k := k) (d := 3)) T) ≤
      volume (hardSphereForkAvoidanceRegion T P) := by
  exact measure_mono (hardSphere_nbc_region_subset_forkAvoidance hP)

lemma hardSphere_treeRegion_mem_separatedPair_of_not_forkEvent
    {k : Nat} [NeZero k] {r : HardSphereConfiguration k 3}
    {T : Finset (Sym2 (Fin k))} {a b c : Fin k}
    (hr : r ∈ hardSphereTreeRegion T)
    (hf : hardSphereFork T a b c)
    (havoid : r ∉ hardSphereForkEvent T a b c) :
    hardSphereForkRelativePair r a b c ∈ hardSphereSeparatedPairRegion := by
  have habactive := hr (s(a, b)) hf.2.2.1
  have hacactive := hr (s(a, c)) hf.2.2.2
  rw [hardSphereActiveExact_mk] at habactive hacactive
  have habnorm : ‖hardSpherePosition r b - hardSpherePosition r a‖ < (1 : ℝ) := by
    rw [norm_sub_rev]
    exact of_decide_eq_true habactive
  have hacnorm : ‖hardSpherePosition r c - hardSpherePosition r a‖ < (1 : ℝ) := by
    rw [norm_sub_rev]
    exact of_decide_eq_true hacactive
  have hbcnot : ¬ ‖hardSpherePosition r b - hardSpherePosition r c‖ < (1 : ℝ) := by
    intro hbc
    apply havoid
    exact ⟨hr, hbc⟩
  rw [hardSphereForkRelativePair, hardSphereSeparatedPairRegion]
  simp only [Set.mem_ofPred_eq]
  rw [show (hardSpherePosition r b - hardSpherePosition r a) -
      (hardSpherePosition r c - hardSpherePosition r a) =
      hardSpherePosition r b - hardSpherePosition r c by abel]
  refine ⟨?_, ?_, le_of_not_gt hbcnot⟩
  · rw [mem_ball_iff_norm]
    simpa [sub_zero] using habnorm
  · rw [mem_ball_iff_norm]
    simpa [sub_zero] using hacnorm

lemma hardSphere_treeRegion_mem_separatedPair_of_mem_forkAvoidance
    {k : Nat} [NeZero k] {r : HardSphereConfiguration k 3}
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hP : hardSphereForkPacking T P)
    (hr : r ∈ hardSphereTreeRegion T)
    (hrAvoid : r ∈ hardSphereForkAvoidanceRegion T P)
    {f : HardSphereForkTriple k} (hf : f ∈ P) :
    hardSphereForkRelativePair r f.1 f.2.1 f.2.2 ∈
      hardSphereSeparatedPairRegion := by
  apply hardSphere_treeRegion_mem_separatedPair_of_not_forkEvent hr
    (hP.1 f hf)
  rw [hardSphereForkAvoidanceRegion] at hrAvoid
  simp only [mem_iInter] at hrAvoid
  exact hrAvoid f hf

/-- The simultaneous separated-pair constraints associated with an
order-compatible fork packing. -/
def hardSphereForkPackingSeparatedRegion {k : Nat} [NeZero k]
    (P : Finset (HardSphereForkTriple k)) :
    Set (HardSphereConfiguration k 3) :=
  {r | ∀ f ∈ P,
    hardSphereForkRelativePair r f.1 f.2.1 f.2.2 ∈
      hardSphereSeparatedPairRegion}

lemma measurableSet_hardSphereForkPackingSeparatedRegion {k : Nat} [NeZero k]
    (P : Finset (HardSphereForkTriple k)) :
    MeasurableSet (hardSphereForkPackingSeparatedRegion P) := by
  rw [show hardSphereForkPackingSeparatedRegion P =
      ⋂ f ∈ P, (fun r : HardSphereConfiguration k 3 =>
        hardSphereForkRelativePair r f.1 f.2.1 f.2.2) ⁻¹'
          hardSphereSeparatedPairRegion by
    ext r
    simp [hardSphereForkPackingSeparatedRegion]]
  exact P.measurableSet_biInter (fun f hf =>
    MeasurableSet.preimage measurableSet_hardSphereSeparatedPairRegion
      (((((continuous_hardSpherePosition (k := k) (d := 3) f.2.1).sub
        (continuous_hardSpherePosition (k := k) (d := 3) f.1)).prodMk
        ((continuous_hardSpherePosition (k := k) (d := 3) f.2.2).sub
          (continuous_hardSpherePosition (k := k) (d := 3) f.1))).measurable)))

lemma hardSphere_nbc_region_subset_forkPackingSeparatedRegion
    {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hP : hardSphereForkPacking T P) :
    nbcRegion (V := Fin k)
        (hardSphereActiveExact (k := k) (d := 3)) T ⊆
      hardSphereForkPackingSeparatedRegion P := by
  intro r hr f hf
  exact hardSphere_treeRegion_mem_separatedPair_of_mem_forkAvoidance hP
    (hardSphere_nbc_region_subset_tree_region hr)
    (hardSphere_nbc_region_subset_forkAvoidance hP hr) hf

lemma hardSphere_nbc_region_real_volume_le_of_separatedBlockMap
    {k m q : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (φ : HardSphereConfiguration k 3 →
      ((Fin m → (HSPosition 3 × HSPosition 3)) ×
        (Fin q → HSPosition 3)))
    (hφ : MeasurePreserving φ
      (volume : Measure (HardSphereConfiguration k 3))
      (volume : Measure ((Fin m → (HSPosition 3 × HSPosition 3)) ×
        (Fin q → HSPosition 3))))
    (hsubset : nbcRegion (V := Fin k)
        (hardSphereActiveExact (k := k) (d := 3)) T ⊆
      φ ⁻¹' hardSphereSeparatedBlockProductRegion m q) :
    (volume : Measure (HardSphereConfiguration k 3)).real
        (nbcRegion (V := Fin k)
          (hardSphereActiveExact (k := k) (d := 3)) T) ≤
      ((volume : Measure (HSPosition 3 × HSPosition 3)).real
          hardSphereSeparatedPairRegion) ^ m * hardSphereKappa ^ q := by
  have hball : (volume : Measure (HSPosition 3))
      (ball (0 : HSPosition 3) 1) < ∞ := measure_ball_lt_top
  have hballPair : (volume : Measure (HSPosition 3 × HSPosition 3))
      (ball (0 : HSPosition 3) 1 ×ˢ ball (0 : HSPosition 3) 1) < ∞ := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top hball hball
  have hsep : (volume : Measure (HSPosition 3 × HSPosition 3))
      hardSphereSeparatedPairRegion < ∞ := by
    apply lt_of_le_of_lt
      (measure_mono (by
        intro p hp
        exact ⟨hp.1, hp.2.1⟩))
      hballPair
  have hsepProduct : (volume : Measure
      (Fin m → (HSPosition 3 × HSPosition 3)))
        (hardSphereSeparatedPairProductRegion m) < ∞ := by
    rw [show hardSphereSeparatedPairProductRegion m =
        Set.univ.pi (fun _ : Fin m => hardSphereSeparatedPairRegion) by
      ext x
      simp [hardSphereSeparatedPairProductRegion], volume_pi_pi]
    exact ENNReal.prod_lt_top (fun _ _ => hsep)
  have hballProduct : (volume : Measure (Fin q → HSPosition 3))
      (hardSphereProductBallRegion q) < ∞ := by
    rw [show hardSphereProductBallRegion q =
        Set.univ.pi (fun _ : Fin q => ball (0 : HSPosition 3) 1) by
      ext x
      simp [hardSphereProductBallRegion], volume_pi_pi]
    exact ENNReal.prod_lt_top (fun _ _ => hball)
  have htarget : (volume : Measure
      ((Fin m → (HSPosition 3 × HSPosition 3)) ×
        (Fin q → HSPosition 3)))
        (hardSphereSeparatedBlockProductRegion m q) < ∞ := by
    rw [hardSphereSeparatedBlockProductRegion, Measure.volume_eq_prod,
      Measure.prod_prod]
    exact ENNReal.mul_lt_top hsepProduct hballProduct
  have hpreimage : (volume : Measure (HardSphereConfiguration k 3))
      (φ ⁻¹' hardSphereSeparatedBlockProductRegion m q) =
      (volume : Measure
          ((Fin m → (HSPosition 3 × HSPosition 3)) ×
            (Fin q → HSPosition 3)))
          (hardSphereSeparatedBlockProductRegion m q) := by
    calc
      (volume : Measure (HardSphereConfiguration k 3))
          (φ ⁻¹' hardSphereSeparatedBlockProductRegion m q) =
        (Measure.map φ (volume : Measure (HardSphereConfiguration k 3)))
          (hardSphereSeparatedBlockProductRegion m q) := by
        rw [Measure.map_apply hφ.measurable
          (measurableSet_hardSphereSeparatedBlockProductRegion m q)]
      _ = (volume : Measure
          ((Fin m → (HSPosition 3 × HSPosition 3)) ×
            (Fin q → HSPosition 3)))
          (hardSphereSeparatedBlockProductRegion m q) := by
        rw [hφ.map_eq]
  have hpreimage_ne_top : (volume : Measure (HardSphereConfiguration k 3))
      (φ ⁻¹' hardSphereSeparatedBlockProductRegion m q) ≠ ∞ := by
    rw [hpreimage]
    exact htarget.ne
  calc
    (volume : Measure (HardSphereConfiguration k 3)).real
        (nbcRegion (V := Fin k)
          (hardSphereActiveExact (k := k) (d := 3)) T) ≤
      (volume : Measure (HardSphereConfiguration k 3)).real
        (φ ⁻¹' hardSphereSeparatedBlockProductRegion m q) := by
      exact ENNReal.toReal_mono hpreimage_ne_top (measure_mono hsubset)
    _ = (volume : Measure
          ((Fin m → (HSPosition 3 × HSPosition 3)) ×
            (Fin q → HSPosition 3))).real
        (hardSphereSeparatedBlockProductRegion m q) := by
      exact congrArg ENNReal.toReal hpreimage
    _ = ((volume : Measure (HSPosition 3 × HSPosition 3)).real
          hardSphereSeparatedPairRegion) ^ m * hardSphereKappa ^ q :=
      hardSphereSeparatedBlockProductRegion_volume m q

/-- All finite order-compatible fork packings of a fixed tree. -/
noncomputable def hardSphereForkPackings {k : Nat}
    (T : Finset (Sym2 (Fin k))) :
    Finset (Finset (HardSphereForkTriple k)) := by
  classical
  exact (Finset.univ.powerset).filter (hardSphereForkPacking T)

/-- The maximum cardinality of a pairwise vertex-disjoint, order-compatible fork packing. -/
noncomputable def hardSphereNu {k : Nat}
    (T : Finset (Sym2 (Fin k))) : Nat :=
  (hardSphereForkPackings T).sup Finset.card

lemma hardSphereForkPackings_nonempty {k : Nat}
    (T : Finset (Sym2 (Fin k))) :
    (hardSphereForkPackings T).Nonempty := by
  classical
  rw [hardSphereForkPackings]
  refine ⟨∅, Finset.mem_filter.mpr
    ⟨Finset.empty_mem_powerset (Finset.univ : Finset (HardSphereForkTriple k)), ?_⟩⟩
  simp [hardSphereForkPacking]

lemma hardSphereForkPacking_card_le_nu {k : Nat}
    {T : Finset (Sym2 (Fin k))}
    {P : Finset (HardSphereForkTriple k)}
    (hP : hardSphereForkPacking T P) :
    P.card ≤ hardSphereNu T := by
  classical
  apply Finset.le_sup
  rw [hardSphereForkPackings]
  exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ P), hP⟩

lemma hardSphere_exists_forkPacking_card_eq_nu {k : Nat}
    (T : Finset (Sym2 (Fin k))) :
    ∃ P, hardSphereForkPacking T P ∧ P.card = hardSphereNu T := by
  classical
  obtain ⟨P, hP, hcard⟩ := Finset.exists_mem_eq_sup
    (hardSphereForkPackings T) (hardSphereForkPackings_nonempty T) Finset.card
  refine ⟨P, (Finset.mem_filter.mp hP).2, ?_⟩
  simpa [hardSphereNu] using hcard.symm

end

end HsVirial
