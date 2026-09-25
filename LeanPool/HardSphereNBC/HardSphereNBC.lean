/-
Copyright (c) 2026 ukiyois, OpenCode agent sessions. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ukiyois, OpenCode agent sessions
-/
module

public import LeanPool.HardSphereNBC.MayerNBC
public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Sym.Sym2.Order
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace


/-! ### The canonical particle and edge conventions -/

@[expose] public section

namespace HsVirial

open Set
open Metric
open SimpleGraph
open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section



/-- The lexicographic key given by the smaller and larger endpoints of an edge. -/
def hardSphereEdgeKey {k : Nat} (e : Sym2 (Fin k)) : Fin k ×ₗ Fin k :=
  toLex (e.inf, e.sup)

/-- Order unordered edges lexicographically by their sorted endpoints. -/
@[instance_reducible]
noncomputable def hardSphereEdgeLinearOrder (k : Nat) :
    LinearOrder (Sym2 (Fin k)) :=
  LinearOrder.lift' (hardSphereEdgeKey (k := k)) (by
    intro e f h
    apply Sym2.inf_eq_inf_and_sup_eq_sup.mp
    constructor
    · simpa [hardSphereEdgeKey] using
        congrArg (fun p : Fin k ×ₗ Fin k => (ofLex p).1) h
    · simpa [hardSphereEdgeKey] using
        congrArg (fun p : Fin k ×ₗ Fin k => (ofLex p).2) h)

noncomputable instance hardSphereEdgeOrder (k : Nat) :
    LinearOrder (Sym2 (Fin k)) := hardSphereEdgeLinearOrder k

/-- Positions of the free particles, with the distinguished particle anchored at zero. -/
abbrev HardSphereConfiguration (k d : Nat) :=
  Fin (k - 1) → HSPosition d

/-- The zero-based coordinate index of a particle other than the anchored particle. -/
def hardSphereFreeIndex {k : Nat} [NeZero k]
    (i : Fin k) (hi : i ≠ 0) : Fin (k - 1) :=
  ⟨i.val - 1, by omega⟩

/-- The particle label corresponding to a free coordinate. -/
def hardSphereFreeParticleIndex {k : Nat}
    (i : Fin (k - 1)) : Fin k :=
  ⟨i.val + 1, by omega⟩

/-- Recover a particle position, assigning zero to the anchored particle. -/
def hardSpherePosition {k d : Nat} [NeZero k]
    (r : HardSphereConfiguration k d) (i : Fin k) : HSPosition d :=
  if hi : i = 0 then 0 else r (hardSphereFreeIndex i hi)

@[simp]
lemma hardSpherePosition_zero {k d : Nat} [NeZero k]
    (r : HardSphereConfiguration k d) : hardSpherePosition r 0 = 0 := by
  simp [hardSpherePosition]

@[simp]
lemma hardSpherePosition_free {k d : Nat} [NeZero k]
    (r : HardSphereConfiguration k d) (i : Fin (k - 1)) :
    hardSpherePosition r (hardSphereFreeParticleIndex i) = r i := by
  have hne : hardSphereFreeParticleIndex i ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [hardSphereFreeParticleIndex] at hv
  have hidx : hardSphereFreeIndex (hardSphereFreeParticleIndex i) hne = i := by
    apply Fin.ext
    simp [hardSphereFreeIndex, hardSphereFreeParticleIndex]
  simp [hardSpherePosition, hne, hidx]

lemma continuous_hardSpherePosition {k d : Nat} [NeZero k]
    (i : Fin k) :
    Continuous (hardSpherePosition (k := k) (d := d) · i) := by
  by_cases hi : i = 0
  · subst i
    simpa using
      (continuous_const : Continuous
        (fun _ : HardSphereConfiguration k d => (0 : HSPosition d)))
  · let j : Fin (k - 1) := hardSphereFreeIndex i hi
    rw [show (hardSpherePosition (k := k) (d := d) · i) =
      (fun r => r j) by
        funext r
        simp [hardSpherePosition, j, hi]]
    exact continuous_apply j

/-- Record whether the two endpoint positions of an edge are less than one unit apart. -/
def hardSphereActiveExact {k d : Nat} [NeZero k]
    (r : HardSphereConfiguration k d) : Sym2 (Fin k) → Bool :=
  Sym2.lift ⟨fun i j =>
    decide (‖hardSpherePosition r i - hardSpherePosition r j‖ < (1 : ℝ)), by
      intro i j
      change decide (‖hardSpherePosition r i - hardSpherePosition r j‖ < (1 : ℝ)) =
        decide (‖hardSpherePosition r j - hardSpherePosition r i‖ < (1 : ℝ))
      rw [norm_sub_rev]⟩

@[simp]
lemma hardSphereActiveExact_mk {k d : Nat} [NeZero k]
    (r : HardSphereConfiguration k d) (i j : Fin k) :
    hardSphereActiveExact r s(i, j) =
      decide (‖hardSpherePosition r i - hardSpherePosition r j‖ < (1 : ℝ)) := by
  rfl

lemma measurable_hardSphereActiveExact_edge {k d : Nat} [NeZero k]
    (e : Sym2 (Fin k)) :
    Measurable
      (fun r : HardSphereConfiguration k d => hardSphereActiveExact r e) := by
  induction e using Sym2.ind with
  | h i j =>
    rw [show (fun r => hardSphereActiveExact r s(i, j)) =
      (fun r => decide
        (‖hardSpherePosition r i - hardSpherePosition r j‖ < (1 : ℝ))) by
        funext r
        rfl]
    apply measurable_to_bool
    have hset : MeasurableSet {r : HardSphereConfiguration k d |
        ‖hardSpherePosition r i - hardSpherePosition r j‖ < (1 : ℝ)} := by
      change MeasurableSet ((fun r : HardSphereConfiguration k d =>
        ‖hardSpherePosition r i - hardSpherePosition r j‖) ⁻¹' Iio (1 : ℝ))
      apply MeasurableSet.preimage measurableSet_Iio
      exact (continuous_norm.comp
        ((continuous_hardSpherePosition i).sub
          (continuous_hardSpherePosition j))).measurable
    simpa [Set.preimage, Set.mem_singleton_iff] using hset

lemma measurable_finite_bool_comp {X E Y : Type*}
    [MeasurableSpace X] [Finite E]
    [MeasurableSpace Y]
    (active : X → E → Bool)
    (hactive : ∀ e, Measurable (fun x => active x e))
    (g : (E → Bool) → Y) :
    Measurable (fun x => g (active x)) := by
  exact (measurable_of_countable g).comp (Measurable.of_eval hactive)

lemma measurable_hardSphereOmega {k d : Nat} [NeZero k] :
    Measurable
      (fun r : HardSphereConfiguration k d =>
        (mayerKernel (hardSphereActiveExact r) : ℝ)) := by
  have hactive : ∀ e, Measurable
      (fun r : HardSphereConfiguration k d => hardSphereActiveExact r e) :=
    fun e => measurable_hardSphereActiveExact_edge e
  have hkernel : Measurable
      (fun r : HardSphereConfiguration k d =>
        mayerKernel (hardSphereActiveExact r)) :=
    measurable_finite_bool_comp
      (active := fun r : HardSphereConfiguration k d => hardSphereActiveExact r)
      hactive mayerKernel
  exact (measurable_of_countable (fun z : Int => (z : ℝ))).comp hkernel

lemma measurable_hardSphereNBCRegion {k d : Nat} [NeZero k]
    (T : Finset (Sym2 (Fin k))) :
    MeasurableSet (nbcRegion (V := Fin k)
      (hardSphereActiveExact (k := k) (d := d)) T) := by
  have hactive : ∀ e, Measurable
      (fun r : HardSphereConfiguration k d => hardSphereActiveExact r e) :=
    fun e => measurable_hardSphereActiveExact_edge e
  have hq : Measurable
      (fun r : HardSphereConfiguration k d =>
        IsExplicitNBCTree (overlapGraph (hardSphereActiveExact r)) T) :=
    measurable_finite_bool_comp
      (active := fun r : HardSphereConfiguration k d => hardSphereActiveExact r)
      hactive (fun p : Sym2 (Fin k) → Bool => IsExplicitNBCTree (overlapGraph p) T)
  simpa [nbcRegion] using hq (measurableSet_singleton True)

/-- The distance between the endpoints of an unordered edge. -/
def hardSphereEdgeDistance {V : Type*} {d : Nat}
    (position : V → HSPosition d) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun i j => ‖position i - position j‖, by
    intro i j
    change ‖position i - position j‖ = ‖position j - position i‖
    rw [norm_sub_rev]⟩ e

@[simp]
lemma hardSphereEdgeDistance_mk {V : Type*} {d : Nat}
    (position : V → HSPosition d) (i j : V) :
    hardSphereEdgeDistance position s(i, j) = ‖position i - position j‖ := by
  rfl

lemma norm_sub_le_walk_length {V : Type*} {d : Nat}
    {G : SimpleGraph V} {position : V → HSPosition d} {u v : V}
    (p : G.Walk u v)
    (hedge : ∀ e ∈ p.edges, hardSphereEdgeDistance position e < (1 : ℝ)) :
    ‖position u - position v‖ ≤ (p.length : ℝ) := by
  induction p with
  | nil => simp
  | @cons u w v hadj p ih =>
    have hhead : hardSphereEdgeDistance position s(u, w) < (1 : ℝ) := by
      exact hedge _ (by simp)
    have htail : ∀ e ∈ p.edges,
        hardSphereEdgeDistance position e < (1 : ℝ) := by
      intro e he
      exact hedge e (by simp [he])
    calc
      ‖position u - position v‖ ≤
          ‖position u - position w‖ + ‖position w - position v‖ := by
        simpa [dist_eq_norm] using
          (dist_triangle (position u) (position w) (position v))
      _ = hardSphereEdgeDistance position s(u, w) +
          ‖position w - position v‖ := by rfl
      _ ≤ 1 + (p.length : ℝ) := by
        gcongr
        exact ih htail
      _ = ((p.cons hadj).length : ℝ) := by simp [add_comm]

lemma hardSphereEdgeDistance_lt_one_of_overlap {k d : Nat} [NeZero k]
    (r : HardSphereConfiguration k d) {e : Sym2 (Fin k)}
    (he : e ∈ (overlapGraph (hardSphereActiveExact r)).edgeSet) :
    hardSphereEdgeDistance (hardSpherePosition r) e < (1 : ℝ) := by
  rw [edgeSet_overlapGraph] at he
  have hactive : activeEdge (hardSphereActiveExact r) e := by
    simpa [activeEdgeFinset] using he
  induction e using Sym2.ind with
  | h i j =>
    have htrue : hardSphereActiveExact r s(i, j) = true := hactive.2
    simpa [hardSphereEdgeDistance_mk, hardSphereActiveExact_mk] using
      (of_decide_eq_true htrue)

lemma hardSpherePosition_norm_lt_of_connected {k d : Nat} [NeZero k]
    (r : HardSphereConfiguration k d)
    (hG : (overlapGraph (hardSphereActiveExact r)).Connected)
    (i : Fin k) :
    ‖hardSpherePosition r i‖ < (k : ℝ) := by
  obtain ⟨p, hp⟩ := hG.exists_isPath i 0
  have hedge : ∀ e ∈ p.edges,
      hardSphereEdgeDistance (hardSpherePosition r) e < (1 : ℝ) := by
    intro e he
    exact hardSphereEdgeDistance_lt_one_of_overlap r
      (p.edges_subset_edgeSet he)
  have hpath := norm_sub_le_walk_length p hedge
  have hlen : (p.length : ℝ) < (k : ℝ) := by
    have hlen' : p.length < Fintype.card (Fin k) := hp.length_lt
    have hlen'' : p.length < k := by simpa using hlen'
    exact_mod_cast hlen''
  have hnorm : ‖hardSpherePosition r i‖ ≤ (p.length : ℝ) := by
    simpa only [hardSpherePosition_zero, sub_zero] using hpath
  exact hnorm.trans_lt hlen

lemma hardSphereConfiguration_mem_closedBall_of_connected
    {k d : Nat} [NeZero k]
    (r : HardSphereConfiguration k d)
    (hG : (overlapGraph (hardSphereActiveExact r)).Connected) :
    r ∈ closedBall (0 : HardSphereConfiguration k d) (k : ℝ) := by
  have hcoord : ∀ i : Fin (k - 1), ‖r i‖ < (k : ℝ) := by
    intro i
    simpa only [hardSpherePosition_free] using
      hardSpherePosition_norm_lt_of_connected r hG
        (hardSphereFreeParticleIndex i)
  have hnorm : ‖r‖ < (k : ℝ) := by
    have hkpos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
    apply (pi_norm_lt_iff (Nat.cast_pos.mpr hkpos)).2
    exact hcoord
  rw [mem_closedBall, dist_zero_right]
  exact hnorm.le

lemma hardSphereMayerKernel_zero_of_not_connected
    {k d : Nat} [NeZero k]
    (r : HardSphereConfiguration k d)
    (hG : ¬(overlapGraph (hardSphereActiveExact r)).Connected) :
    mayerKernel (hardSphereActiveExact r) = 0 := by
  have hz : (mayerKernel (hardSphereActiveExact r)).natAbs = 0 := by
    have h := abs_mayerKernel_eq_nbc (hardSphereActiveExact r)
    rw [ite_eq_right hG] at h
    simpa [intMagnitude] using h
  exact Int.natAbs_eq_zero.mp hz

/-- The signed Mayer graph sum evaluated at the configuration's overlap graph. -/
def hardSphereOmega {k d : Nat} [NeZero k]
    (r : HardSphereConfiguration k d) : ℝ :=
  (mayerKernel (hardSphereActiveExact r) : ℝ)

/-- The hard-sphere cluster integral normalized by the factorial of the particle count. -/
def hardSphereBk {k d : Nat} [NeZero k] : ℝ :=
  (k.factorial : ℝ)⁻¹ *
    ∫ r : HardSphereConfiguration k d, hardSphereOmega r

/-- The volume of configurations assigned to a fixed no-broken-circuit tree. -/
def hardSphereNBCVolume {k d : Nat} [NeZero k]
    (T : Finset (Sym2 (Fin k))) : ℝ :=
  (volume : Measure (HardSphereConfiguration k d)).real
    (nbcRegion (V := Fin k)
      (hardSphereActiveExact (k := k) (d := d)) T)

lemma hardSphereConfiguration_mem_closedBall_of_region
    {k d : Nat} [NeZero k]
    (r : HardSphereConfiguration k d)
    {T : Finset (Sym2 (Fin k))}
    (hr : r ∈ nbcRegion (V := Fin k)
      (hardSphereActiveExact (k := k) (d := d)) T) :
    r ∈ closedBall (0 : HardSphereConfiguration k d) (k : ℝ) := by
  change IsExplicitNBCTree (overlapGraph (hardSphereActiveExact r)) T at hr
  have hle : SimpleGraph.fromEdgeSet (T : Set (Sym2 (Fin k))) ≤
      overlapGraph (hardSphereActiveExact r) :=
    fromEdgeSet_le_of_graphForest hr.1
  exact hardSphereConfiguration_mem_closedBall_of_connected r
    (hr.2.1.mono hle)

lemma hardSphereOmega_zero_of_not_mem_closedBall
    {k d : Nat} [NeZero k]
    {r : HardSphereConfiguration k d}
    (hr : r ∉ closedBall (0 : HardSphereConfiguration k d) (k : ℝ)) :
    hardSphereOmega r = 0 := by
  by_cases hG : (overlapGraph (hardSphereActiveExact r)).Connected
  · exact False.elim (hr
      (hardSphereConfiguration_mem_closedBall_of_connected r hG))
  · simp [hardSphereOmega,
      hardSphereMayerKernel_zero_of_not_connected r hG]

lemma hardSphereNBCRegion_measure_ne_top {k d : Nat} [NeZero k]
    (T : Finset (Sym2 (Fin k))) :
    (volume : Measure (HardSphereConfiguration k d))
        (nbcRegion (V := Fin k)
          (hardSphereActiveExact (k := k) (d := d)) T) ≠ ∞ := by
  have hsubset : nbcRegion (V := Fin k)
        (hardSphereActiveExact (k := k) (d := d)) T ⊆
      closedBall (0 : HardSphereConfiguration k d) (k : ℝ) := by
    intro r hr
    exact hardSphereConfiguration_mem_closedBall_of_region r hr
  have hball : (volume : Measure (HardSphereConfiguration k d))
        (closedBall (0 : HardSphereConfiguration k d) (k : ℝ)) < ∞ :=
    (isCompact_closedBall (0 : HardSphereConfiguration k d) (k : ℝ)).measure_lt_top
  exact (lt_of_le_of_lt (measure_mono hsubset) hball).ne

lemma norm_bond_le_one {V : Type*} [Fintype V]
     (x : Sym2 V → Bool) (e : Sym2 V) :
    ‖(bond x e : ℝ)‖ ≤ 1 := by
  classical
  by_cases h : activeEdge x e
  · simp [bond, h]
  · simp [bond, h]

lemma norm_mayerKernel_real_le_card {V : Type*} [Fintype V] [DecidableEq V]
     (x : Sym2 V → Bool) :
    ‖(mayerKernel x : ℝ)‖ ≤
      (completeConnectedEdgeSubsets (V := V)).card := by
  have hterm : ∀ A : Finset (Sym2 V),
      ‖(∏ e ∈ A, (bond x e : ℝ))‖ ≤ (1 : ℝ) := by
    intro A
    rw [norm_prod]
    calc
      ∏ e ∈ A, ‖(bond x e : ℝ)‖ ≤ ∏ _e ∈ A, (1 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro e he
          exact norm_nonneg _
        · intro e he
          exact norm_bond_le_one x e
      _ = 1 := by simp
  calc
    ‖(mayerKernel x : ℝ)‖ =
        ‖∑ A ∈ completeConnectedEdgeSubsets (V := V),
          (∏ e ∈ A, (bond x e : ℝ))‖ := by
      simp only [mayerKernel, Int.cast_sum, Int.cast_prod]
    _ ≤ ∑ A ∈ completeConnectedEdgeSubsets (V := V),
        ‖∏ e ∈ A, (bond x e : ℝ)‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ _A ∈ completeConnectedEdgeSubsets (V := V), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro A hA
      exact hterm A
    _ = (completeConnectedEdgeSubsets (V := V)).card := by simp

lemma integrable_hardSphereOmega {k d : Nat} [NeZero k] :
    Integrable (hardSphereOmega (k := k) (d := d))
      (volume : Measure (HardSphereConfiguration k d)) := by
  have hball : (volume : Measure (HardSphereConfiguration k d))
        (closedBall (0 : HardSphereConfiguration k d) (k : ℝ)) < ∞ :=
    (isCompact_closedBall (0 : HardSphereConfiguration k d) (k : ℝ)).measure_lt_top
  have hbound : ∀ r : HardSphereConfiguration k d,
      ‖hardSphereOmega r‖ ≤
        ((completeConnectedEdgeSubsets (V := Fin k)).card : ℝ) := by
    intro r
    simpa [hardSphereOmega] using
      (norm_mayerKernel_real_le_card
        (x := hardSphereActiveExact r))
  have h_on : IntegrableOn (hardSphereOmega (k := k) (d := d))
      (closedBall (0 : HardSphereConfiguration k d) (k : ℝ))
      (volume : Measure (HardSphereConfiguration k d)) :=
    IntegrableOn.of_bound hball
      (measurable_hardSphereOmega.aestronglyMeasurable.restrict)
      ((completeConnectedEdgeSubsets (V := Fin k)).card : ℝ)
      (Filter.Eventually.of_forall hbound)
  exact h_on.integrable_of_forall_notMem_eq_zero
    (fun r hr => hardSphereOmega_zero_of_not_mem_closedBall hr)

lemma integrable_hardSphereNBC_indicator {k d : Nat} [NeZero k]
    (T : Finset (Sym2 (Fin k))) :
    Integrable
      ((nbcRegion (V := Fin k)
        (hardSphereActiveExact (k := k) (d := d)) T).indicator
        (fun _ : HardSphereConfiguration k d => (1 : ℝ)))
      (volume : Measure (HardSphereConfiguration k d)) := by
  exact (integrableOn_const
    (hardSphereNBCRegion_measure_ne_top T) (by finiteness)).integrable_indicator
      (measurable_hardSphereNBCRegion T)

lemma real_abs_mayerKernel_eq_intMagnitude
    {V : Type*} [Fintype V] [DecidableEq V]
    (x : Sym2 V → Bool) :
    |(mayerKernel x : ℝ)| = (mayerKernel x).natAbs := by
  simp [Int.cast_abs]

lemma hardSphere_absOmega_eq_region_indicator_sum
    {k d : Nat} [NeZero k]
    (r : HardSphereConfiguration k d) :
    |hardSphereOmega r| =
      ∑ T ∈ treeUniverse (V := Fin k),
        (nbcRegion (V := Fin k)
          (hardSphereActiveExact (k := k) (d := d)) T).indicator
          (fun _ : HardSphereConfiguration k d => (1 : ℝ)) r := by
  by_cases hG : (overlapGraph (hardSphereActiveExact r)).Connected
  · have hkernel : mayerKernel (hardSphereActiveExact r) =
        (-1 : Int) ^ (Fintype.card (Fin k) - 1) *
          (NBC (overlapGraph (hardSphereActiveExact r)) : Int) := by
      rw [mayerKernel_eq_m]
      exact m_eq_signed_NBC_of_connected hG
    have hdecomp := nbc_tree_decomposition_region
      (V := Fin k) (hardSphereActiveExact (k := k) (d := d)) r
    rw [ite_eq_left hG] at hdecomp
    have hdecompR := congrArg (fun n : Nat => (n : ℝ)) hdecomp
    simpa [hardSphereOmega, hkernel, Set.indicator, Int.cast_mul,
      Int.cast_pow] using hdecompR
  · have hzero := hardSphereMayerKernel_zero_of_not_connected r hG
    have hdecomp := nbc_tree_decomposition_region
      (V := Fin k) (hardSphereActiveExact (k := k) (d := d)) r
    rw [ite_eq_right hG] at hdecomp
    have hdecompR := congrArg (fun n : Nat => (n : ℝ)) hdecomp
    simpa [hardSphereOmega, hzero, Set.indicator] using hdecompR

lemma hardSphereOmega_eq_sign_mul_abs
    {k d : Nat} [NeZero k]
    (r : HardSphereConfiguration k d) :
    hardSphereOmega r = (-1 : ℝ) ^ (k - 1) * |hardSphereOmega r| := by
  by_cases hG : (overlapGraph (hardSphereActiveExact r)).Connected
  · have hkernel : mayerKernel (hardSphereActiveExact r) =
        (-1 : Int) ^ (Fintype.card (Fin k) - 1) *
          (NBC (overlapGraph (hardSphereActiveExact r)) : Int) := by
      rw [mayerKernel_eq_m]
      exact m_eq_signed_NBC_of_connected hG
    rw [hardSphereOmega, hkernel]
    simp [Int.cast_mul, Int.cast_pow]
  · have hzero := hardSphereMayerKernel_zero_of_not_connected r hG
    simp [hardSphereOmega, hzero]

lemma integral_abs_hardSphereOmega_eq_sum_volume
    {k d : Nat} [NeZero k] :
    (∫ r : HardSphereConfiguration k d, |hardSphereOmega r|) =
      ∑ T ∈ treeUniverse (V := Fin k),
        (volume : Measure (HardSphereConfiguration k d)).real
          (nbcRegion (V := Fin k)
            (hardSphereActiveExact (k := k) (d := d)) T) := by
  have hpoint :
      (fun r : HardSphereConfiguration k d => |hardSphereOmega r|) =
        (fun r => ∑ T ∈ treeUniverse (V := Fin k),
          (nbcRegion (V := Fin k)
            (hardSphereActiveExact (k := k) (d := d)) T).indicator
            (fun _ : HardSphereConfiguration k d => (1 : ℝ)) r) := by
    funext r
    exact hardSphere_absOmega_eq_region_indicator_sum r
  rw [hpoint, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro T hT
    exact integral_indicator_one (measurable_hardSphereNBCRegion T)
  · intro T hT
    exact integrable_hardSphereNBC_indicator T

lemma integral_hardSphereOmega_eq_sign_mul_abs
    {k d : Nat} [NeZero k] :
    (∫ r : HardSphereConfiguration k d, hardSphereOmega r) =
      (-1 : ℝ) ^ (k - 1) *
        ∫ r : HardSphereConfiguration k d, |hardSphereOmega r| := by
  calc
    (∫ r : HardSphereConfiguration k d, hardSphereOmega r) =
        ∫ r : HardSphereConfiguration k d,
          (-1 : ℝ) ^ (k - 1) * |hardSphereOmega r| := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (fun r => hardSphereOmega_eq_sign_mul_abs r)
    _ = (-1 : ℝ) ^ (k - 1) *
        ∫ r : HardSphereConfiguration k d, |hardSphereOmega r| := by
      rw [integral_const_mul]

lemma abs_integral_hardSphereOmega_eq_integral_abs
    {k d : Nat} [NeZero k] :
    |∫ r : HardSphereConfiguration k d, hardSphereOmega r| =
      ∫ r : HardSphereConfiguration k d, |hardSphereOmega r| := by
  rw [integral_hardSphereOmega_eq_sign_mul_abs, abs_mul]
  have hnonneg : 0 ≤
      ∫ r : HardSphereConfiguration k d, |hardSphereOmega r| :=
    integral_nonneg (fun _ => abs_nonneg _)
  simp [abs_of_nonneg hnonneg]

theorem hardSphere_nbc_volume_identity_of_neZero
    {k d : Nat} [NeZero k] (_hk : 2 ≤ k) :
    (k.factorial : ℝ) *
        |hardSphereBk (k := k) (d := d)| =
      ∑ T ∈ treeUniverse (V := Fin k),
        hardSphereNBCVolume (k := k) (d := d) T := by
  have hfacpos : 0 < (k.factorial : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos k)
  have hfacne : (k.factorial : ℝ) ≠ 0 := ne_of_gt hfacpos
  calc
    (k.factorial : ℝ) *
        |hardSphereBk (k := k) (d := d)| =
        (k.factorial : ℝ) *
          |(k.factorial : ℝ)⁻¹ *
            ∫ r : HardSphereConfiguration k d, hardSphereOmega r| := by
      rfl
    _ = ∫ r : HardSphereConfiguration k d, |hardSphereOmega r| := by
      rw [abs_mul, abs_inv, abs_of_pos hfacpos]
      rw [← mul_assoc, mul_inv_cancel₀ hfacne, one_mul]
      exact abs_integral_hardSphereOmega_eq_integral_abs
    _ = ∑ T ∈ treeUniverse (V := Fin k),
        hardSphereNBCVolume (k := k) (d := d) T := by
      exact integral_abs_hardSphereOmega_eq_sum_volume

theorem hardSphere_nbc_volume_identity
    {k d : Nat} (hk : 2 ≤ k) :
    let _ : NeZero k := ⟨by omega⟩
    (k.factorial : ℝ) *
        |hardSphereBk (k := k) (d := d)| =
      ∑ T ∈ treeUniverse (V := Fin k),
        hardSphereNBCVolume (k := k) (d := d) T := by
  exact @hardSphere_nbc_volume_identity_of_neZero k d ⟨by omega⟩ hk

end

end HsVirial
