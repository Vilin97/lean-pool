/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationEvents
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LineageMassMaps
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.FaceMassChain
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationConstants
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationIntervalBounds
public import Mathlib.Data.Finset.Sort

/-!
# Face events on a surviving lineage

A resolved face event cannot repeat along its surviving low-level lineage:
parent injectivity identifies the surviving child with the resolved target,
and composed subdivisions preserve realization. This is the geometric
no-repeat input for the uniform face-chain bound.
-/

@[expose] public section

namespace EGZ.Lineages

open scoped BigOperators

/-- Count finite event times by their ancestor labels, using a bound for
each increasing sequence of events with one common label. -/
theorem card_eventTimes_le_of_ordered_bound {R : Type*} [Fintype R]
    (T : Finset ℕ) (label : ℕ → R) (C : ℕ)
    (hlineage : ∀ N (time : Fin (N + 1) ↪o ℕ),
      (∀ i, time i ∈ T) → (∀ i j, label (time i) = label (time j)) → N + 1 ≤ C) :
    T.card ≤ Fintype.card R * C := by
  classical
  have hcount (r : R) : (T.filter fun i ↦ label i = r).card ≤ C := by
    let U := T.filter fun i ↦ label i = r
    change U.card ≤ C
    cases hcard : U.card with
    | zero => exact Nat.zero_le C
    | succ N =>
      apply hlineage N (U.orderEmbOfFin hcard)
      · intro i
        exact (Finset.mem_filter.mp (U.orderEmbOfFin_mem hcard i)).1
      · intro i j
        exact (Finset.mem_filter.mp (U.orderEmbOfFin_mem hcard i)).2.trans
          (Finset.mem_filter.mp (U.orderEmbOfFin_mem hcard j)).2.symm
  calc
    T.card = ∑ r : R, (T.filter fun i ↦ label i = r).card := by
      simpa using (Finset.card_eq_sum_card_fiberwise
        (s := T) (t := (Finset.univ : Finset R)) (f := label) (by simp))
    _ ≤ ∑ _r : R, C := Finset.sum_le_sum (fun r _ ↦ hcount r)
    _ = Fintype.card R * C := by simp

end EGZ.Lineages

namespace EGZ.FlagDecomposition

variable {p d : ℕ} [NeZero p] [Fact p.Prime] {f : FpCoord p d → ℕ}

omit [Fact p.Prime] in
theorem faceAtNode_carrier (Φ : FlagDecomposition p d f) {x y : Φ.flag.Node}
    (Γ : (Φ.flag.polytope x).Face) (h : y = x) :
    (Φ.faceAtNode Γ h).carrier = h.symm ▸ Γ.carrier := by
  subst y
  rfl

namespace SubdivisionMap

omit [Fact p.Prime] in
/-- Changing the subdivision by an equality also changes its dependent
source-node face by the same equality. -/
theorem preimage_faceAtNode_congr {Φ Ψ : FlagDecomposition p d f}
    {S T : SubdivisionMap Φ Ψ} (h : S = T) (z : Ψ.flag.Node) (x : Φ.flag.Node)
    (Γ : (Φ.flag.polytope x).Face) (hS : S.node z = x) (hT : T.node z = x) :
    S.fibre z ⁻¹' (Φ.faceAtNode Γ hS).carrier = T.fibre z ⁻¹' (Φ.faceAtNode Γ hT).carrier := by
  subst T
  rfl

omit [Fact p.Prime] in
/-- A face which is realized after the first subdivision remains realized
under a composite subdivision. Nonemptiness of the final pullback supplies
nonemptiness of both intermediate pullbacks. -/
theorem comp_isRealizedFace {Φ Ψ Ω : FlagDecomposition p d f}
    (S : SubdivisionMap Φ Ψ) (T : SubdivisionMap Ψ Ω) (z : Ω.flag.Node)
    (Γ : (Φ.flag.polytope ((S.comp T).node z)).Face)
    (hne : ((Ω.flag.polytope z).carrier ∩ (S.comp T).fibre z ⁻¹' Γ.carrier).Nonempty)
    (hresolved : ∀ hfirst : ((Ψ.flag.polytope (T.node z)).carrier ∩
        S.fibre (T.node z) ⁻¹' Γ.carrier).Nonempty,
      Ψ.IsRealizedFace (T.node z) (S.face (T.node z) Γ hfirst)) :
    Ω.IsRealizedFace z ((S.comp T).face z Γ hne) := by
  obtain ⟨q, hq, hΓq⟩ := hne
  have hfirst : ((Ψ.flag.polytope (T.node z)).carrier ∩
      S.fibre (T.node z) ⁻¹' Γ.carrier).Nonempty :=
    ⟨T.fibre z q, T.polytope_mem z hq, hΓq⟩
  have hsecond : ((Ω.flag.polytope z).carrier ∩
      T.fibre z ⁻¹' (S.face (T.node z) Γ hfirst).carrier).Nonempty :=
    ⟨q, hq, T.polytope_mem z hq, hΓq⟩
  have hface : T.face z (S.face (T.node z) Γ hfirst) hsecond =
      (S.comp T).face z Γ ⟨q, hq, hΓq⟩ := by
    apply RationalPolytope.Face.ext
    ext r
    constructor
    · rintro ⟨hr, _, hΓr⟩
      exact ⟨hr, hΓr⟩
    · rintro ⟨hr, hΓr⟩
      exact ⟨hr, T.polytope_mem z hr, hΓr⟩
  rw [← hface]
  exact T.isRealizedFace z _ hsecond (hresolved hfirst)

end SubdivisionMap

namespace Iteration.Progress

variable {s t u : Iteration.State p d f} {ε δ : ℝ} {g : ℕ → ℕ}

/-- A later unrealized face cannot equal the pullback of a resolved face
when the surviving child remains below the selected level. -/
theorem face_no_repeat (P : Iteration.Progress s t ε δ g)
    (x : s.decomposition.flag.Node) (Γ : (s.decomposition.flag.polytope x).Face)
    (hevent : P.event = .face x Γ)
    (T : SubdivisionMap t.decomposition u.decomposition) (z : u.decomposition.flag.Node)
    (hnode : P.subdivision.node (T.node z) = x)
    (hlevel : t.decomposition.level (T.node z) ≤ s.decomposition.level x)
    (Δ : (u.decomposition.flag.polytope z).Face)
    (hunrealized : ¬ u.decomposition.IsRealizedFace z Δ) :
    (u.decomposition.flag.polytope z).carrier ∩
      (P.subdivision.comp T).fibre z ⁻¹' (s.decomposition.faceAtNode Γ hnode).carrier ≠
        Δ.carrier := by
  have hres := P.resolves
  rw [hevent] at hres
  obtain ⟨y, hy, hylevel, hyresolved⟩ := hres
  have hcutoff : P.event.cutoff = s.decomposition.level x := by rw [hevent]; rfl
  have heqy : y = T.node z := P.parent_injective
    (by change t.decomposition.level y ≤ P.event.cutoff; rw [hcutoff, hylevel])
    (by change t.decomposition.level (T.node z) ≤ P.event.cutoff; rwa [hcutoff])
    (hy.trans hnode.symm)
  subst y
  intro heq
  have hne : ((u.decomposition.flag.polytope z).carrier ∩
      (P.subdivision.comp T).fibre z ⁻¹'
        (s.decomposition.faceAtNode Γ hnode).carrier).Nonempty := by
    rw [heq]
    exact Δ.nonempty
  have hreal := P.subdivision.comp_isRealizedFace T z
    (s.decomposition.faceAtNode Γ hnode) hne hyresolved
  have hface : (P.subdivision.comp T).face z (s.decomposition.faceAtNode Γ hnode) hne = Δ :=
    RationalPolytope.Face.ext heq
  exact hunrealized (hface ▸ hreal)

end Iteration.Progress

namespace Iteration

/-- Odd operation colors identify face events and their exact level. -/
theorem State.Event.exists_face_of_color_eq {s : State p d f} (E : s.Event) {L : ℕ}
    (h : E.color = 2 * L + 1) :
    ∃ x Γ, E = .face x Γ ∧ s.decomposition.level x = L := by
  cases E with
  | gap => simp only [State.Event.color] at h; omega
  | complete x => simp only [State.Event.color] at h; omega
  | face x Γ =>
    refine ⟨x, Γ, rfl, ?_⟩
    simp only [State.Event.color] at h
    omega

variable {s : ℕ → State p d f} (D : LineageMassMaps (fun i ↦ (s i).decomposition))
    (L : ℕ) (ε : ℝ) (δ : ℕ → ℝ) (g : ℕ → ℕ)

/-- One actual face event, matching the comparison system at its selected
time. Progress is required only at these event times. -/
structure FaceOccurrence (i : ℕ) where
  /-- The transition in which the specified face event occurs. -/
  progress : Progress (s i) (s (i + 1)) ε (δ i) g
  /-- The node at level `L` supporting this face event. -/
  node : (s i).decomposition.flag.Node
  /-- The face selected by this occurrence of the event. -/
  face : ((s i).decomposition.flag.polytope node).Face
  level_eq : (s i).decomposition.level node = L
  event_eq : progress.event = .face node face
  subdivision_eq : progress.subdivision = D.step i

namespace FaceOccurrence

variable {D L ε δ g}

/-- Regard the occurrence's node as a node of level at most `L`. -/
abbrev lowNode {i : ℕ} (E : FaceOccurrence D L ε δ g i) : D.system.LowNode L i :=
  ⟨E.node, E.level_eq.le⟩

theorem isLargeFace {i : ℕ} (E : FaceOccurrence D L ε δ g i) :
    (s i).decomposition.IsLargeFace ε E.node E.face := by
  have hv := E.progress.valid
  rw [E.event_eq] at hv
  exact hv.1

theorem not_isRealizedFace {i : ℕ} (E : FaceOccurrence D L ε δ g i) :
    ¬ (s i).decomposition.IsRealizedFace E.node E.face := by
  have hv := E.progress.valid
  rw [E.event_eq] at hv
  exact hv.2

/-- Two ordered face occurrences with the same ancestor label cannot have
equal faces after pulling the old face through the composed subdivision. -/
theorem transport_no_repeat (hL : ∀ i, L ≤ D.cutoff i) {i j : ℕ}
    (E : FaceOccurrence D L ε δ g i) (F : FaceOccurrence D L ε δ g j) (hij : i < j)
    (heq : D.system.ancestry (D.system_injectiveBelow hL) i E.lowNode =
      D.system.ancestry (D.system_injectiveBelow hL) j F.lowNode) :
    let hnode := D.transport_node_eq_of_ancestry_eq hL hij.le E.lowNode F.lowNode heq
    ((s j).decomposition.flag.polytope F.node).carrier ∩
      (D.transport hL hij.le).subdivision.fibre F.node ⁻¹'
        ((s i).decomposition.faceAtNode E.face hnode).carrier ≠ F.face.carrier := by
  dsimp only
  let T := D.transport hL (Nat.succ_le_of_lt hij)
  have hfirst : (D.transport hL (Nat.le_succ i)).subdivision = E.progress.subdivision := by
    rw [D.transport_succ hL (le_refl i), D.transport_self hL]
    exact E.subdivision_eq.symm
  have htransport : (D.transport hL hij.le).subdivision =
      E.progress.subdivision.comp T.subdivision := by
    rw [D.transport_trans hL (Nat.le_succ i) (Nat.succ_le_of_lt hij)]
    change (D.transport hL (Nat.le_succ i)).subdivision.comp T.subdivision = _
    rw [hfirst]
  have hnode : E.progress.subdivision.node (T.subdivision.node F.node) = E.node := by
    change (E.progress.subdivision.comp T.subdivision).node F.node = E.node
    rw [← htransport]
    exact D.transport_node_eq_of_ancestry_eq hL hij.le E.lowNode F.lowNode heq
  have hlevel : (s (i + 1)).decomposition.level (T.subdivision.node F.node) ≤
      (s i).decomposition.level E.node :=
    (T.level_parent F.node).trans_eq (F.level_eq.trans E.level_eq.symm)
  have hno := E.progress.face_no_repeat E.node E.face E.event_eq T.subdivision F.node
    hnode hlevel F.face F.not_isRealizedFace
  rw [SubdivisionMap.preimage_faceAtNode_congr htransport F.node E.node E.face
    (D.transport_node_eq_of_ancestry_eq hL hij.le E.lowNode F.lowNode heq) hnode]
  exact hno

/-- The same no-repeat statement expressed in the stable map's integer
coordinate realization, ready for the face-chain counting theorem. -/
theorem massMap_no_repeat (hL : ∀ i, L ≤ D.cutoff i) {i j : ℕ}
    (E : FaceOccurrence D L ε δ g i) (F : FaceOccurrence D L ε δ g j) (hij : i < j)
    (heq : D.system.ancestry (D.system_injectiveBelow hL) i E.lowNode =
      D.system.ancestry (D.system_injectiveBelow hL) j F.lowNode) :
    ((s j).decomposition.flag.polytope F.node).carrier ∩
      (D.mapOfSameAncestry hL hij.le E.lowNode F.lowNode heq).coord.real ⁻¹' E.face.carrier ≠
        F.face.carrier := by
  rw [D.mapOfSameAncestry_real_preimage hL hij.le E.lowNode F.lowNode heq]
  simpa only [faceAtNode_carrier] using E.transport_no_repeat hL F hij heq

end FaceOccurrence

/-- Uniform bound for ordered face events on one persistent lineage.
Only the finite selected times need actual progress certificates. -/
theorem card_ordered_faceOccurrences_le {N : ℕ} (hL : ∀ i, L ≤ D.cutoff i)
    (hp : Odd p) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (time : Fin (N + 1) ↪o ℕ) (E : ∀ i, FaceOccurrence D L ε δ g (time i))
    (hsame : ∀ i j,
      D.system.ancestry (D.system_injectiveBelow hL) (time i) (E i).lowNode =
        D.system.ancestry (D.system_injectiveBelow hL) (time j) (E j).lowNode)
    (htail : ∀ i, ((s (time i)).decomposition.retainedMass : ℝ) -
      (s (time (Fin.last N))).decomposition.retainedMass ≤
        ε ^ 2 / 4 * (s (time i)).decomposition.retainedMass) :
    N + 1 ≤ faceCapacity d ε := by
  let M {i j : Fin (N + 1)} (hij : i ≤ j) :=
    D.mapOfSameAncestry hL (time.monotone hij) (E i).lowNode (E j).lowNode (hsame i j)
  have hinj {i j : Fin (N + 1)} (hij : i ≤ j) : Function.Injective (M hij).coord.real :=
    (M hij).toNodeMassMap.real_injective_of_level_eq (s (time j)).minimal
      ((E i).level_eq.trans (E j).level_eq.symm)
  have hcomp {i j k : Fin (N + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
      (M (hij.trans hjk)).coord = (M hij).coord.comp (M hjk).coord :=
    D.mapOfSameAncestry_comp_coord hL (time.monotone hij) (time.monotone hjk)
      (E i).lowNode (E j).lowNode (E k).lowNode (hsame i j) (hsame j k) (hsame i k)
  apply le_faceCapacity_of_real_le
  exact card_largeFaceChain_le (fun i ↦ (s (time i)).decomposition) (fun i ↦ (E i).node)
    (fun h ↦ M h) (fun h ↦ hinj h) (fun h h' ↦ hcomp h h') hp ε hε hεhalf
    (fun i ↦ (E i).face) (fun i ↦ (E i).isLargeFace)
    (fun i j hij ↦ (E i).massMap_no_repeat hL (E j) (time.strictMono hij) (hsame i j)) htail

/-- Group a finite set of actual face events by initial ancestor. Each
group is ordered by event time and bounded by `faceCapacity`. -/
theorem card_faceOccurrences_le (hL : ∀ i, L ≤ D.cutoff i)
    (hp : Odd p) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (T : Finset ℕ) (E : ∀ i ∈ T, FaceOccurrence D L ε δ g i)
    (htail : ∀ i ∈ T, ∀ j ∈ T, i ≤ j →
      ((s i).decomposition.retainedMass : ℝ) - (s j).decomposition.retainedMass ≤
        ε ^ 2 / 4 * (s i).decomposition.retainedMass) :
    T.card ≤ Fintype.card (s 0).decomposition.flag.Node * faceCapacity d ε := by
  classical
  let label (i : ℕ) : (s 0).decomposition.flag.Node :=
    if hi : i ∈ T then (D.system.ancestry (D.system_injectiveBelow hL) i (E i hi).lowNode).val
    else ⊤
  apply Lineages.card_eventTimes_le_of_ordered_bound T label (faceCapacity d ε)
  intro N time hmem hsame
  apply card_ordered_faceOccurrences_le D L ε δ g hL hp hε hεhalf time
    (fun i ↦ E (time i) (hmem i))
  · intro i j
    apply Subtype.ext
    simpa only [label, dite_eq_left (hmem i), dite_eq_left (hmem j)] using hsame i j
  · intro i
    exact htail (time i) (hmem i) (time (Fin.last N)) (hmem (Fin.last N))
      (time.monotone (Fin.le_last i))

/-- Face-color capacity on a genuinely finite progress interval. The
comparison sequence is restarted at `a` and extended by identities after
`b + 1`; no progress is required outside the finite run. -/
theorem card_face_events_interval_le {N a b : ℕ}
    (P : ∀ i, i < N → Progress (s i) (s (i + 1)) ε (δ i) g)
    (χ : ℕ → ℕ) (hχ : ∀ i hi, χ i = (P i hi).event.color)
    (hab : a ≤ b) (hbN : b < N) (hp : Odd p) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hcolors : ∀ i ∈ Finset.Icc a b, 2 * L + 1 ≤ χ i)
    (htail : ∀ i j, i ≤ j → j ≤ N →
      ((s i).decomposition.retainedMass : ℝ) - (s j).decomposition.retainedMass ≤
        ε ^ 2 / 4 * (s i).decomposition.retainedMass) :
    ((Finset.Icc a b).filter fun i ↦ χ i = 2 * L + 1).card ≤
      Fintype.card (s a).decomposition.flag.Node * faceCapacity d ε := by
  classical
  let n := b + 1 - a
  have hbound : a + n ≤ N := by dsimp [n]; omega
  have hLsq : L ≤ (d + 1) ^ 2 := by
    have haN : a < N := by omega
    have hlo := hcolors a (Finset.mem_Icc.mpr ⟨le_rfl, hab⟩)
    rw [hχ a haN] at hlo
    have hhi := (P a haN).event.color_lt
    omega
  let D := intervalLineageMassMaps P a n hbound
  have hcut : ∀ i, L ≤ D.cutoff i := by
    apply intervalLineageMassMaps_cutoff_ge P a n hbound hLsq
    intro i hi
    have hi' : i < b + 1 - a := hi
    have hmem : a + i ∈ Finset.Icc a b := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hc := hcolors (a + i) hmem
    rw [hχ (a + i) (by omega)] at hc
    omega
  let T := (Finset.range n).filter fun i ↦ χ (a + i) = 2 * L + 1
  have hE : ∀ i ∈ T,
      FaceOccurrence (s := fun i ↦ intervalState s a n i) D L ε (fun i ↦ δ (a + i)) g i := by
    intro i hi
    obtain ⟨hirange, hcolor⟩ := Finset.mem_filter.mp hi
    have hir : i < n := Finset.mem_range.mp hirange
    let Q := intervalProgress P a n hbound i hir
    have hcol : Q.event.color = 2 * L + 1 := by
      dsimp only [Q]
      rw [intervalProgress_event_color, ← hχ (a + i) (by omega)]
      exact hcolor
    apply Classical.choice
    obtain ⟨x, Γ, hevent, hlevel⟩ := Q.event.exists_face_of_color_eq hcol
    exact ⟨⟨Q, x, Γ, hlevel, hevent, (intervalLineageMassMaps_step P a n hbound i hir).symm⟩⟩
  have hc := card_faceOccurrences_le (s := fun i ↦ intervalState s a n i)
    D L ε (fun i ↦ δ (a + i)) g hcut hp hε hεhalf T hE
    (fun i _ j _ hij ↦ intervalState_mass_tail hbound htail i j hij)
  have hcard0 := congrArg (fun t : State p d f ↦ Fintype.card t.decomposition.flag.Node)
    (intervalState_zero s a n)
  rw [hcard0] at hc
  simpa only [T, n, card_filter_range_offset χ a b (2 * L + 1) hab] using hc

end Iteration
end EGZ.FlagDecomposition
