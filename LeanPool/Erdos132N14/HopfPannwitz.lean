/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132N14.HopfPannwitzGeometry
import Mathlib.Data.Finset.Max

/-!
# The planar diameter bound

This module formalizes the classical Perles charging proof that a finite
planar set has at most as many diameter pairs as points.  Every diameter edge
is assigned to a clockwise-extreme endpoint, and the signed-area lemmas show
that no endpoint can receive two different edges.
-/

namespace LeanPool.Erdos132N14

noncomputable section

variable {ι : Type*} [LinearOrder ι]

/-- Whether `v` is an endpoint of the increasing representative `e`. -/
def EdgeIncident (v : ι) (e : ι × ι) : Prop :=
  v = e.1 ∨ v = e.2

/-- The endpoint of `e` opposite an incident vertex `v`. -/
def otherEndpoint (e : ι × ι) (v : ι) : ι :=
  if e.1 = v then e.2 else e.1

theorem pairWith_endpoint_other
    {S : Finset ι} {e : ι × ι} {v : ι}
    (he : e ∈ pairs S) (hv : EdgeIncident v e) :
    pairWith v (otherEndpoint e v) = e := by
  have hlt : e.1 < e.2 := (Finset.mem_filter.mp he).2
  rcases hv with rfl | rfl
  · simp [otherEndpoint, pairWith, not_lt_of_ge hlt.le]
  · simp [otherEndpoint, pairWith, hlt, ne_of_lt hlt]

theorem endpoint_mem
    {S : Finset ι} {e : ι × ι} {v : ι}
    (he : e ∈ pairs S) (hv : EdgeIncident v e) :
    v ∈ S := by
  have hmembers := Finset.mem_product.mp (Finset.mem_filter.mp he).1
  rcases hv with rfl | rfl
  · exact hmembers.1
  · exact hmembers.2

theorem otherEndpoint_mem
    {S : Finset ι} {e : ι × ι} {v : ι}
    (he : e ∈ pairs S) (hv : EdgeIncident v e) :
    otherEndpoint e v ∈ S := by
  have hmembers := Finset.mem_product.mp (Finset.mem_filter.mp he).1
  have hlt : e.1 < e.2 := (Finset.mem_filter.mp he).2
  rcases hv with rfl | rfl
  · rw [show otherEndpoint e e.1 = e.2 by simp [otherEndpoint]]
    exact hmembers.2
  · rw [show otherEndpoint e e.2 = e.1 by simp [otherEndpoint, ne_of_lt hlt]]
    exact hmembers.1

theorem otherEndpoint_ne
    {S : Finset ι} {e : ι × ι} {v : ι}
    (he : e ∈ pairs S) (hv : EdgeIncident v e) :
    otherEndpoint e v ≠ v := by
  have hlt : e.1 < e.2 := (Finset.mem_filter.mp he).2
  rcases hv with rfl | rfl
  · rw [show otherEndpoint e e.1 = e.2 by simp [otherEndpoint]]
    exact ne_of_gt hlt
  · rw [show otherEndpoint e e.2 = e.1 by simp [otherEndpoint, ne_of_lt hlt]]
    exact ne_of_lt hlt

theorem dist_endpoint_other_eq_pairDistance
    (P : Configuration ι) {S : Finset ι} {e : ι × ι} {v : ι}
    (he : e ∈ pairs S) (hv : EdgeIncident v e) :
    dist (P.point v) (P.point (otherEndpoint e v)) = P.pairDistance e := by
  calc
    dist (P.point v) (P.point (otherEndpoint e v)) =
        P.pairDistance (pairWith v (otherEndpoint e v)) := by
      rw [P.pairDistance_pairWith]
    _ = P.pairDistance e := by rw [pairWith_endpoint_other he hv]

/-- The pairs in `S` that realize a specified distance. -/
def diameterEdges (P : Configuration ι) (S : Finset ι) (d : ℝ) :
    Finset (ι × ι) :=
  (pairs S).filter fun e ↦ P.pairDistance e = d

/-- Edge `e` is clockwise-extreme at `v` among the edges `E`. -/
def ClockwiseExtremeAt
    (P : Configuration ι) (E : Finset (ι × ι)) (e : ι × ι) (v : ι) : Prop :=
  ∀ f ∈ E, EdgeIncident v f →
    0 ≤ planeTurn (P.point v)
      (P.point (otherEndpoint e v)) (P.point (otherEndpoint f v))

/-- Every maximal-distance edge is clockwise-extreme at one endpoint. -/
theorem diameter_edge_extreme_at_endpoint
    (P : Configuration ι) (S : Finset ι) {d : ℝ}
    (hd : 0 < d)
    (hmax : ∀ f ∈ pairs S, P.pairDistance f ≤ d)
    {e : ι × ι} (he : e ∈ diameterEdges P S d) :
    ClockwiseExtremeAt P (diameterEdges P S d) e e.1 ∨
      ClockwiseExtremeAt P (diameterEdges P S d) e e.2 := by
  classical
  have hePairs : e ∈ pairs S := (Finset.mem_filter.mp he).1
  have heDistance : P.pairDistance e = d := (Finset.mem_filter.mp he).2
  have heFirst : EdgeIncident e.1 e := Or.inl rfl
  have heSecond : EdgeIncident e.2 e := Or.inr rfl
  by_contra hneither
  have hnotFirst :
      ¬ClockwiseExtremeAt P (diameterEdges P S d) e e.1 :=
    fun h ↦ hneither (Or.inl h)
  have hnotSecond :
      ¬ClockwiseExtremeAt P (diameterEdges P S d) e e.2 :=
    fun h ↦ hneither (Or.inr h)
  have hnotFirst' :
      ∃ f, ∃ (_ : f ∈ diameterEdges P S d) (_ : EdgeIncident e.1 f),
        planeTurn (P.point e.1) (P.point (otherEndpoint e e.1))
          (P.point (otherEndpoint f e.1)) < 0 := by
    simpa only [ClockwiseExtremeAt, not_forall, Classical.not_imp, not_le] using hnotFirst
  have hnotSecond' :
      ∃ g, ∃ (_ : g ∈ diameterEdges P S d) (_ : EdgeIncident e.2 g),
        planeTurn (P.point e.2) (P.point (otherEndpoint e e.2))
          (P.point (otherEndpoint g e.2)) < 0 := by
    simpa only [ClockwiseExtremeAt, not_forall, Classical.not_imp, not_le] using hnotSecond
  obtain ⟨f, hf, hfIncident, hfTurn⟩ := hnotFirst'
  obtain ⟨g, hg, hgIncident, hgTurn⟩ := hnotSecond'
  have hfPairs : f ∈ pairs S := (Finset.mem_filter.mp hf).1
  have hgPairs : g ∈ pairs S := (Finset.mem_filter.mp hg).1
  have huv :
      dist (P.point e.1) (P.point e.2) = d := by
    simpa [Configuration.pairDistance] using heDistance
  have huf :
      dist (P.point e.1) (P.point (otherEndpoint f e.1)) = d := by
    rw [dist_endpoint_other_eq_pairDistance P hfPairs hfIncident]
    exact (Finset.mem_filter.mp hf).2
  have hvg :
      dist (P.point e.2) (P.point (otherEndpoint g e.2)) = d := by
    rw [dist_endpoint_other_eq_pairDistance P hgPairs hgIncident]
    exact (Finset.mem_filter.mp hg).2
  have hfreeLong :
      d < dist (P.point (otherEndpoint f e.1))
        (P.point (otherEndpoint g e.2)) := by
    apply opposite_turns_force_longer_pair huv huf hvg hd
    · simpa [otherEndpoint, ne_of_lt (Finset.mem_filter.mp hePairs).2] using hfTurn
    · simpa [otherEndpoint, ne_of_lt (Finset.mem_filter.mp hePairs).2] using hgTurn
  have hfreeNe : otherEndpoint f e.1 ≠ otherEndpoint g e.2 := by
    intro h
    rw [h, dist_self] at hfreeLong
    linarith
  have hfreePair :
      pairWith (otherEndpoint f e.1) (otherEndpoint g e.2) ∈ pairs S :=
    pairWith_mem_pairs
      (otherEndpoint_mem hfPairs hfIncident)
      (otherEndpoint_mem hgPairs hgIncident) hfreeNe
  have hfreeLe :=
    hmax (pairWith (otherEndpoint f e.1) (otherEndpoint g e.2)) hfreePair
  rw [P.pairDistance_pairWith] at hfreeLe
  linarith

/-- A vertex cannot be clockwise-extreme for two different diameter edges. -/
theorem clockwiseExtremeAt_unique
    (P : Configuration ι) (S : Finset ι) {d : ℝ}
    (hd : 0 < d)
    (hmax : ∀ g ∈ pairs S, P.pairDistance g ≤ d)
    {e f : ι × ι} {v : ι}
    (he : e ∈ diameterEdges P S d) (hf : f ∈ diameterEdges P S d)
    (heIncident : EdgeIncident v e) (hfIncident : EdgeIncident v f)
    (heExtreme : ClockwiseExtremeAt P (diameterEdges P S d) e v)
    (hfExtreme : ClockwiseExtremeAt P (diameterEdges P S d) f v) :
    e = f := by
  have hePairs : e ∈ pairs S := (Finset.mem_filter.mp he).1
  have hfPairs : f ∈ pairs S := (Finset.mem_filter.mp hf).1
  have hforward := heExtreme f hf hfIncident
  have hreverse := hfExtreme e he heIncident
  rw [planeTurn_swap] at hreverse
  have hturn :
      planeTurn (P.point v) (P.point (otherEndpoint e v))
        (P.point (otherEndpoint f v)) = 0 := by
    linarith
  have heDistance :
      dist (P.point v) (P.point (otherEndpoint e v)) = d := by
    rw [dist_endpoint_other_eq_pairDistance P hePairs heIncident]
    exact (Finset.mem_filter.mp he).2
  have hfDistance :
      dist (P.point v) (P.point (otherEndpoint f v)) = d := by
    rw [dist_endpoint_other_eq_pairDistance P hfPairs hfIncident]
    exact (Finset.mem_filter.mp hf).2
  have hfreeLe :
      dist (P.point (otherEndpoint e v)) (P.point (otherEndpoint f v)) ≤ d := by
    by_cases hsame : otherEndpoint e v = otherEndpoint f v
    · simp [hsame, hd.le]
    · have hpair :
          pairWith (otherEndpoint e v) (otherEndpoint f v) ∈ pairs S :=
        pairWith_mem_pairs
          (otherEndpoint_mem hePairs heIncident)
          (otherEndpoint_mem hfPairs hfIncident) hsame
      simpa [P.pairDistance_pairWith] using
        hmax (pairWith (otherEndpoint e v) (otherEndpoint f v)) hpair
  have hother :
      otherEndpoint e v = otherEndpoint f v := by
    apply P.injective
    apply equal_rays_of_cross_eq_zero heDistance hfDistance hfreeLe hd
    simpa [planeTurn] using hturn
  calc
    e = pairWith v (otherEndpoint e v) := (pairWith_endpoint_other hePairs heIncident).symm
    _ = pairWith v (otherEndpoint f v) := by rw [hother]
    _ = f := pairWith_endpoint_other hfPairs hfIncident

/-- The endpoint to which the Perles argument charges a diameter edge. -/
def diameterOwner
    (P : Configuration ι) (S : Finset ι) (d : ℝ) (e : ι × ι) : ι := by
  classical
  exact if ClockwiseExtremeAt P (diameterEdges P S d) e e.1 then e.1 else e.2

theorem diameterOwner_incident
    (P : Configuration ι) (S : Finset ι) (d : ℝ) (e : ι × ι) :
    EdgeIncident (diameterOwner P S d e) e := by
  classical
  by_cases h : ClockwiseExtremeAt P (diameterEdges P S d) e e.1
  · have howner : diameterOwner P S d e = e.1 := by
      simp [diameterOwner, h]
    rw [howner]
    exact Or.inl rfl
  · have howner : diameterOwner P S d e = e.2 := by
      simp [diameterOwner, h]
    rw [howner]
    exact Or.inr rfl

theorem diameterOwner_extreme
    (P : Configuration ι) (S : Finset ι) {d : ℝ}
    (hd : 0 < d)
    (hmax : ∀ f ∈ pairs S, P.pairDistance f ≤ d)
    {e : ι × ι} (he : e ∈ diameterEdges P S d) :
    ClockwiseExtremeAt P (diameterEdges P S d) e (diameterOwner P S d e) := by
  classical
  rcases diameter_edge_extreme_at_endpoint P S hd hmax he with hfirst | hsecond
  · have howner : diameterOwner P S d e = e.1 := by
      simp [diameterOwner, hfirst]
    rw [howner]
    exact hfirst
  · by_cases hfirst : ClockwiseExtremeAt P (diameterEdges P S d) e e.1
    · have howner : diameterOwner P S d e = e.1 := by
        simp [diameterOwner, hfirst]
      rw [howner]
      exact hfirst
    · have howner : diameterOwner P S d e = e.2 := by
        simp [diameterOwner, hfirst]
      rw [howner]
      exact hsecond

/-- The diameter owner map is injective on maximal-distance edges. -/
theorem diameterOwner_injectiveOn
    (P : Configuration ι) (S : Finset ι) {d : ℝ}
    (hd : 0 < d)
    (hmax : ∀ f ∈ pairs S, P.pairDistance f ≤ d) :
    Set.InjOn (diameterOwner P S d) (diameterEdges P S d) := by
  intro e he f hf howners
  have heIncident := diameterOwner_incident P S d e
  have hfIncident := diameterOwner_incident P S d f
  have heExtreme := diameterOwner_extreme P S hd hmax he
  have hfExtreme := diameterOwner_extreme P S hd hmax hf
  rw [← howners] at hfIncident hfExtreme
  exact clockwiseExtremeAt_unique P S hd hmax he hf
    heIncident hfIncident heExtreme hfExtreme

/-- The number of pairs realizing a positive maximal distance is at most the
number of points. -/
theorem diameterEdges_card_le
    (P : Configuration ι) (S : Finset ι) {d : ℝ}
    (hd : 0 < d)
    (hmax : ∀ f ∈ pairs S, P.pairDistance f ≤ d) :
    (diameterEdges P S d).card ≤ S.card := by
  apply Finset.card_le_card_of_injOn (diameterOwner P S d)
  · intro e he
    exact endpoint_mem (Finset.mem_filter.mp he).1
      (diameterOwner_incident P S d e)
  · exact diameterOwner_injectiveOn P S hd hmax

/-- Every fourteen-point planar configuration has a realized distance
represented by at most fourteen unordered pairs. -/
def HopfPannwitzLowMultiplicityDistance14 : Prop :=
  ∀ P : Configuration (Fin 14),
    ∃ d ∈ P.realizedDistances Finset.univ,
      P.distanceMultiplicity Finset.univ d ≤ 14

/-- The Hopf--Pannwitz low-multiplicity input used by the fourteen-point
descent, proved by charging each diameter pair to a unique endpoint. -/
theorem hopfPannwitzLowMultiplicityDistance14 :
    HopfPannwitzLowMultiplicityDistance14 := by
  intro P
  have hnonempty :
      (pairs (Finset.univ : Finset (Fin 14))).Nonempty := by
    exact ⟨((0 : Fin 14), (1 : Fin 14)), by decide⟩
  obtain ⟨e, he, hmax⟩ :=
    Finset.exists_max_image
      (pairs (Finset.univ : Finset (Fin 14))) P.pairDistance hnonempty
  refine ⟨P.pairDistance e, ?_, ?_⟩
  · exact (P.mem_realizedDistances_iff Finset.univ _).mpr ⟨e, he, rfl⟩
  · change (diameterEdges P Finset.univ (P.pairDistance e)).card ≤ 14
    simpa using diameterEdges_card_le P Finset.univ (P.pairDistance_pos he) hmax

end

end LeanPool.Erdos132N14
