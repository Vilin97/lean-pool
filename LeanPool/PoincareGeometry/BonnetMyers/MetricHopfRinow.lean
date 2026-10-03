/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Order.Compact

/-!
# A metric Hopf--Rinow extension step

The Riemannian Hopf--Rinow bridge is separated into a metric core.  A complete
locally compact *intrinsic* metric is proper; this file starts with the local
compact-ball extension step.  The intrinsic hypothesis is expressed as an
approximate intermediate-point property, so no geodesic or minimizer is
silently assumed.
-/

@[expose] public section

noncomputable section

open Set

namespace BonnetMyersEntry
namespace MetricHopfRinow

/-- An intrinsic metric admits an approximate intermediate point whenever the
distance is strictly below the sum of two positive radii.  A Riemannian path
will later supply this property from its length, before any minimizing
geodesic has been constructed. -/
def HasApproximateIntermediate (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∀ x z : X, ∀ a b : ℝ, 0 < a → 0 < b → dist x z < a + b →
    ∃ y : X, dist x y ≤ a ∧ dist y z < b

/-- If every point has one compact closed ball, then a compact closed ball can
be enlarged by a positive amount in an intrinsic metric.  The proof takes a
finite subcover by local compact balls and uses an approximate intermediate
point to enter one of them. -/
theorem exists_isCompact_closedBall_add_of_isCompact_closedBall
    {X : Type*} [PseudoMetricSpace X]
    (hlocal : ∀ x : X, ∃ ρ : ℝ, 0 < ρ ∧ IsCompact (Metric.closedBall x ρ))
    (hintrinsic : HasApproximateIntermediate X)
    {x : X} {r : ℝ} (hr : 0 < r)
    (hcompact : IsCompact (Metric.closedBall x r)) :
    ∃ δ : ℝ, 0 < δ ∧ IsCompact (Metric.closedBall x (r + δ)) := by
  classical
  choose ρ hρpos hρcompact using hlocal
  obtain ⟨t, ht_sub, ht_cover⟩ := hcompact.elim_nhds_subcover
    (fun y ↦ Metric.ball y (ρ y / 4)) (by
      intro y hy
      exact Metric.ball_mem_nhds y (by linarith [hρpos y]))
  have hxmem : x ∈ Metric.closedBall x r := by
    rw [Metric.mem_closedBall]
    simpa using le_of_lt hr
  have ht_nonempty : t.Nonempty := by
    rcases Set.mem_iUnion₂.mp (ht_cover hxmem) with ⟨y, hyt, hy⟩
    exact ⟨y, hyt⟩
  let δ : ℝ := (t.inf' ht_nonempty ρ) / 8
  have hδpos : 0 < δ := by
    dsimp [δ]
    apply div_pos
    · refine (Finset.lt_inf'_iff _).2 ?_
      intro y hy
      exact hρpos y
    · norm_num
  have hδ_le (y : X) (hyt : y ∈ t) : δ ≤ ρ y / 8 := by
    dsimp [δ]
    exact div_le_div_of_nonneg_right (Finset.inf'_le ρ hyt) (by norm_num)
  have hsubset : Metric.closedBall x (r + δ) ⊆
      Metric.closedBall x r ∪ ⋃ y ∈ t, Metric.closedBall y (ρ y) := by
    intro z hz
    by_cases hzsmall : z ∈ Metric.closedBall x r
    · exact Or.inl hzsmall
    · right
      have hzx : dist x z ≤ r + δ := by
        simpa [dist_comm] using (Metric.mem_closedBall.mp hz)
      have hrz : r < dist x z := by
        apply lt_of_not_ge
        intro h
        apply hzsmall
        rw [Metric.mem_closedBall]
        simpa [dist_comm] using h
      have hlt : dist x z < r + 2 * δ := by
        linarith
      obtain ⟨y, hxy, hyz⟩ := hintrinsic x z r (2 * δ)
        hr (by linarith) hlt
      have hymem : y ∈ Metric.closedBall x r := by
        rw [Metric.mem_closedBall]
        simpa [dist_comm] using hxy
      rcases Set.mem_iUnion₂.mp (ht_cover hymem) with ⟨c, hct, hyc⟩
      refine Set.mem_iUnion₂.mpr ⟨c, hct, ?_⟩
      have hyc' : dist c y < ρ c / 4 := by
        simpa [dist_comm] using (Metric.mem_ball.mp hyc)
      have hbound : 2 * δ + ρ c / 4 ≤ ρ c := by
        nlinarith [hδ_le c hct, hρpos c]
      rw [Metric.mem_closedBall]
      exact (calc
        dist z c ≤ dist z y + dist y c := dist_triangle _ _ _
        _ < 2 * δ + ρ c / 4 := by
          gcongr
          · simpa [dist_comm] using hyz
          · simpa [dist_comm] using hyc'
        _ ≤ ρ c := hbound).le
  have hfinite : IsCompact (⋃ y ∈ t, Metric.closedBall y (ρ y)) :=
    t.isCompact_biUnion fun y hy ↦ hρcompact y
  refine ⟨δ, hδpos, ?_⟩
  exact (hcompact.union hfinite).of_isClosed_subset
    Metric.isClosed_closedBall hsubset

/-- A compact ball which is within one positive error of a larger ball gives a
finite cover of that larger ball.  Approximate intermediate points are enough:
the intermediate point lies in the compact ball and the remaining error is
absorbed by its finite cover. -/
theorem exists_finite_cover_closedBall_of_isCompact_of_lt_add
    {X : Type*} [PseudoMetricSpace X]
    (hintrinsic : HasApproximateIntermediate X)
    {x : X} {R q ε : ℝ} (hq : 0 < q)
    (hcompact : IsCompact (Metric.closedBall x q))
    (hε : 0 < ε) (hR : R < q + ε / 2) :
    ∃ t : Set X, t.Finite ∧
      Metric.closedBall x R ⊆ ⋃ c ∈ t, Metric.ball c ε := by
  obtain ⟨t, htfinite, htcover⟩ :=
    (Metric.totallyBounded_iff.mp hcompact.totallyBounded) (ε / 2) (by linarith)
  refine ⟨t, htfinite, ?_⟩
  intro y hy
  have hxyR : dist x y ≤ R := by
    simpa [dist_comm] using (Metric.mem_closedBall.mp hy)
  obtain ⟨z, hxz, hzy⟩ := hintrinsic x y q (ε / 2) hq (by linarith)
    (lt_of_le_of_lt hxyR hR)
  have hzq : z ∈ Metric.closedBall x q := by
    rw [Metric.mem_closedBall]
    simpa [dist_comm] using hxz
  rcases Set.mem_iUnion₂.mp (htcover hzq) with ⟨c, hct, hzc⟩
  refine Set.mem_iUnion₂.mpr ⟨c, hct, ?_⟩
  rw [Metric.mem_ball]
  have hyz : dist y z < ε / 2 := by
    simpa [dist_comm] using hzy
  have hzc' : dist z c < ε / 2 := Metric.mem_ball.mp hzc
  calc
    dist y c ≤ dist y z + dist z c := dist_triangle _ _ _
    _ < ε := by linarith

/-- A complete locally compact intrinsic metric is proper.  The proof makes
the Hopf--Rinow compactness step explicit: compact radii have a supremum;
approximate intermediates make the supremum ball totally bounded, completeness
makes it compact, and the local extension lemma contradicts maximality. -/
theorem properSpace_of_complete_of_localCompact_of_approximateIntermediate
    {X : Type*} [PseudoMetricSpace X] [CompleteSpace X]
    (hlocal : ∀ x : X, ∃ ρ : ℝ, 0 < ρ ∧ IsCompact (Metric.closedBall x ρ))
    (hintrinsic : HasApproximateIntermediate X) : ProperSpace X := by
  classical
  refine ⟨fun x r ↦ ?_⟩
  let S : Set ℝ := {s | 0 < s ∧ IsCompact (Metric.closedBall x s)}
  rcases hlocal x with ⟨r₀, hr₀, hr₀compact⟩
  have hr₀S : r₀ ∈ S := ⟨hr₀, hr₀compact⟩
  have hSnonempty : S.Nonempty := ⟨r₀, hr₀S⟩
  have hSunbounded : ¬ BddAbove S := by
    intro hSbounded
    let R : ℝ := sSup S
    have hRpos : 0 < R :=
      lt_of_lt_of_le hr₀ (by simpa only [R] using le_csSup hSbounded hr₀S)
    have hRtotallyBounded : TotallyBounded (Metric.closedBall x R) := by
      refine Metric.totallyBounded_iff.mpr ?_
      intro ε hε
      have hbefore : R - ε / 2 < sSup S := by
        dsimp [R]
        linarith
      obtain ⟨q, hqS, hqgt⟩ := exists_lt_of_lt_csSup hSnonempty hbefore
      exact exists_finite_cover_closedBall_of_isCompact_of_lt_add hintrinsic
        hqS.1 hqS.2 hε (by linarith)
    have hRcompact : IsCompact (Metric.closedBall x R) :=
      hRtotallyBounded.isCompact_of_isClosed Metric.isClosed_closedBall
    obtain ⟨δ, hδ, hRδcompact⟩ :=
      exists_isCompact_closedBall_add_of_isCompact_closedBall hlocal hintrinsic
        hRpos hRcompact
    have hRδS : R + δ ∈ S := ⟨by linarith, hRδcompact⟩
    have hRδle : R + δ ≤ R := by
      dsimp [R]
      exact le_csSup hSbounded hRδS
    linarith
  obtain ⟨q, hqS, hrq⟩ : ∃ q ∈ S, r < q := by
    by_contra h
    apply hSunbounded
    refine ⟨r, ?_⟩
    intro q hqS
    exact le_of_not_gt fun hrq ↦ h ⟨q, hqS, hrq⟩
  exact hqS.2.of_isClosed_subset Metric.isClosed_closedBall
    (Metric.closedBall_subset_closedBall hrq.le)

/-- Proper intrinsic metrics have exact midpoints.  Compactness replaces the
usual unproved appeal to a limiting minimizing path: minimize the distance to
the endpoint on a half-radius compact ball, then use approximate intermediates
to rule out any slack. -/
theorem exists_midpoint_of_properSpace
    {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    (hintrinsic : HasApproximateIntermediate X) (x z : X) :
    ∃ y : X, dist x y = dist x z / 2 ∧ dist y z = dist x z / 2 := by
  let d : ℝ := dist x z
  by_cases hdzero : d = 0
  · refine ⟨x, ?_, ?_⟩ <;> simp [d, hdzero]
  have hdpos : 0 < d := lt_of_le_of_ne dist_nonneg (Ne.symm hdzero)
  let a : ℝ := d / 2
  have hapos : 0 < a := by
    dsimp [a]
    linarith
  have hballnonempty : (Metric.closedBall x a).Nonempty := by
    refine ⟨x, ?_⟩
    rw [Metric.mem_closedBall]
    simp [hapos.le]
  obtain ⟨y, hyball, hmin⟩ :=
    (isCompact_closedBall x a).exists_isMinOn hballnonempty
      (continuous_dist.comp
        (continuous_id.prodMk (continuous_const : Continuous fun _ : X ↦ z))).continuousOn
  have hxy : dist x y ≤ a := by
    simpa [dist_comm] using (Metric.mem_closedBall.mp hyball)
  have hlower : d - a ≤ dist y z := by
    dsimp [d]
    linarith [dist_triangle x y z]
  have hupper : dist y z ≤ d - a := by
    by_contra hnot
    have hstrict : d - a < dist y z := lt_of_not_ge hnot
    let ε : ℝ := (dist y z - (d - a)) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    have hrespos : 0 < d - a + ε := by
      dsimp [a]
      linarith
    obtain ⟨w, hxw, hwz⟩ := hintrinsic x z a (d - a + ε) hapos hrespos
      (by dsimp [d]; linarith)
    have hwball : w ∈ Metric.closedBall x a := by
      rw [Metric.mem_closedBall]
      simpa [dist_comm] using hxw
    have hminw : dist y z ≤ dist w z := hmin hwball
    have htoo : dist y z < d - a + ε := lt_of_le_of_lt hminw hwz
    dsimp [ε] at htoo
    linarith
  have hyz : dist y z = d - a := le_antisymm hupper hlower
  have hxyeq : dist x y = a := by
    dsimp [d] at hyz ⊢
    linarith [dist_triangle x y z]
  refine ⟨y, ?_, ?_⟩
  · change dist x y = d / 2
    exact hxyeq
  · change dist y z = d / 2
    calc
      dist y z = d - a := hyz
      _ = d / 2 := by
        dsimp [a]
        ring

/-- Every prescribed fraction of the distance is realized by an exact
intermediate point in a proper intrinsic metric.  The choices need not yet be
coherent as a curve; this is the metric existence input from which a genuine
minimizing segment is constructed in the next Hopf--Rinow layer. -/
theorem exists_intermediate_of_properSpace
    {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    (hintrinsic : HasApproximateIntermediate X) (x z : X) {r : ℝ}
    (hr0 : 0 ≤ r) (hrd : r ≤ dist x z) :
    ∃ y : X, dist x y = r ∧ dist y z = dist x z - r := by
  let d : ℝ := dist x z
  by_cases hrzero : r = 0
  · refine ⟨x, ?_, ?_⟩
    · simp [hrzero]
    · simp [hrzero]
  have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrzero)
  have hballnonempty : (Metric.closedBall x r).Nonempty := by
    refine ⟨x, ?_⟩
    rw [Metric.mem_closedBall]
    simp [hr0]
  obtain ⟨y, hyball, hmin⟩ :=
    (isCompact_closedBall x r).exists_isMinOn hballnonempty
      (continuous_dist.comp
        (continuous_id.prodMk (continuous_const : Continuous fun _ : X ↦ z))).continuousOn
  have hxy : dist x y ≤ r := by
    simpa [dist_comm] using (Metric.mem_closedBall.mp hyball)
  have hlower : d - r ≤ dist y z := by
    dsimp [d]
    linarith [dist_triangle x y z]
  have hupper : dist y z ≤ d - r := by
    by_contra hnot
    have hstrict : d - r < dist y z := lt_of_not_ge hnot
    let ε : ℝ := (dist y z - (d - r)) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    have hrespos : 0 < d - r + ε := by
      have hresnonneg : 0 ≤ d - r := by
        dsimp [d]
        linarith
      linarith
    obtain ⟨w, hxw, hwz⟩ := hintrinsic x z r (d - r + ε) hrpos hrespos
      (by dsimp [d]; linarith)
    have hwball : w ∈ Metric.closedBall x r := by
      rw [Metric.mem_closedBall]
      simpa [dist_comm] using hxw
    have hminw : dist y z ≤ dist w z := hmin hwball
    have htoo : dist y z < d - r + ε := lt_of_le_of_lt hminw hwz
    dsimp [ε] at htoo
    linarith
  have hyz : dist y z = d - r := le_antisymm hupper hlower
  have hxyeq : dist x y = r := by
    dsimp [d] at hyz ⊢
    linarith [dist_triangle x y z]
  exact ⟨y, hxyeq, hyz⟩

end MetricHopfRinow
end BonnetMyersEntry
