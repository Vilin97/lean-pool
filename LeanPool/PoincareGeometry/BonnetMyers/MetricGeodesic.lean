/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.BonnetMyers.MetricHopfRinow
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Data.Finset.Sort
import Mathlib.Topology.MetricSpace.Isometry

/-!
# Coherent metric segments

This file develops the next, genuinely metric, Hopf--Rinow layer.  Properness
and exact intermediate points alone do *not* give a curve: independently
chosen intermediate points can lie on different branches.  The lemmas here
therefore keep the endpoint equalities explicit and show how to refine an
already coherent piece of a segment.  They are the finite-consistency input
for the compact-product construction of a minimizing metric segment.
-/

noncomputable section

open Set

namespace BonnetMyersEntry
namespace MetricHopfRinow

/-- Points at parameter `r` on an exact metric segment from `x` to `z`.
The two displayed equalities, rather than only membership in a ball, retain
the equality case of the triangle inequality needed for coherent refinements. -/
def segmentPointSet {X : Type*} [PseudoMetricSpace X] (x z : X) (r : ℝ) : Set X :=
  {y | dist x y = r ∧ dist y z = dist x z - r}

theorem isClosed_segmentPointSet {X : Type*} [PseudoMetricSpace X]
    (x z : X) (r : ℝ) : IsClosed (segmentPointSet x z r) := by
  change IsClosed {y | dist x y = r ∧ dist y z = dist x z - r}
  rw [show {y | dist x y = r ∧ dist y z = dist x z - r} =
      {y | dist x y = r} ∩ {y | dist y z = dist x z - r} by rfl]
  refine (isClosed_eq (continuous_const.dist continuous_id) continuous_const).inter
    (isClosed_eq (continuous_id.dist continuous_const) continuous_const)

/-- Exact intermediate points provide a point in every permitted segment
slice. -/
theorem nonempty_segmentPointSet_of_properSpace
    {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    (hintrinsic : HasApproximateIntermediate X) (x z : X) {r : ℝ}
    (hr0 : 0 ≤ r) (hrd : r ≤ dist x z) :
    (segmentPointSet x z r).Nonempty := by
  obtain ⟨y, hxy, hyz⟩ :=
    exists_intermediate_of_properSpace hintrinsic x z hr0 hrd
  exact ⟨y, hxy, hyz⟩

/-- Each segment slice is compact in a proper metric space. -/
theorem isCompact_segmentPointSet_of_properSpace
    {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    (x z : X) (r : ℝ) : IsCompact (segmentPointSet x z r) := by
  apply (isCompact_closedBall x r).of_isClosed_subset
    (isClosed_segmentPointSet x z r)
  intro y hy
  rw [Metric.mem_closedBall]
  simpa [dist_comm] using hy.1.le

/-- Two points placed at ordered parameters on an exact segment cannot be
closer than the parameter gap.  This lower bound is what rules out accidental
branch switching in the later finite-consistency construction. -/
theorem sub_le_dist_of_mem_segmentPointSet
    {X : Type*} [PseudoMetricSpace X]
    {x z y w : X} {r s : ℝ}
    (hy : y ∈ segmentPointSet x z r) (hw : w ∈ segmentPointSet x z s) :
    s - r ≤ dist y w := by
  have htriangle : dist x z ≤ dist x y + dist y w + dist w z := by
    calc
      dist x z ≤ dist x y + dist y z := dist_triangle _ _ _
      _ ≤ dist x y + (dist y w + dist w z) := by
        gcongr
        exact dist_triangle _ _ _
      _ = dist x y + dist y w + dist w z := by ring
  rw [hy.1, hw.2] at htriangle
  linarith

/-- An exact metric subsegment may be refined at any intermediate parameter.
Unlike a bare existence result, this preserves the endpoint segment equations
and the two new subsegment lengths simultaneously. -/
theorem exists_refine_segmentPointSet_of_properSpace
    {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    (hintrinsic : HasApproximateIntermediate X)
    {x z y w : X} {r s t : ℝ}
    (hy : y ∈ segmentPointSet x z r) (hw : w ∈ segmentPointSet x z s)
    (hyw : dist y w = s - r)
    (hrt : r ≤ t) (hts : t ≤ s) :
    ∃ q : X, q ∈ segmentPointSet x z t ∧
      dist y q = t - r ∧ dist q w = s - t := by
  have htr0 : 0 ≤ t - r := sub_nonneg.mpr hrt
  have htrd : t - r ≤ dist y w := by
    rw [hyw]
    linarith
  obtain ⟨q, hyq, hqw⟩ :=
    exists_intermediate_of_properSpace hintrinsic y w htr0 htrd
  have hqw' : dist q w = s - t := by
    rw [hqw, hyw]
    ring
  have hxq_le : dist x q ≤ t := by
    calc
      dist x q ≤ dist x y + dist y q := dist_triangle _ _ _
      _ = t := by rw [hy.1, hyq]; ring
  have hqz_le : dist q z ≤ dist x z - t := by
    calc
      dist q z ≤ dist q w + dist w z := dist_triangle _ _ _
      _ = dist x z - t := by rw [hqw', hw.2]; ring
  have hxq_ge : t ≤ dist x q := by
    have htriangle : dist x z ≤ dist x q + dist q z := dist_triangle _ _ _
    linarith
  have hqz_ge : dist x z - t ≤ dist q z := by
    have htriangle : dist x z ≤ dist x q + dist q z := dist_triangle _ _ _
    linarith
  exact ⟨q, ⟨le_antisymm hxq_le hxq_ge, le_antisymm hqz_le hqz_ge⟩, hyq, hqw'⟩

/-- A finite strictly ordered list of parameters has a coherent exact chain.
The construction works backwards from the penultimate parameter: first choose
that point on the full segment, then recurse on the shorter exact segment.
This is deliberately stronger than choosing each parameter independently.
-/
theorem exists_coherent_points_of_strictMono
    {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    (hintrinsic : HasApproximateIntermediate X) (x z : X) :
    ∀ n : ℕ, ∀ t : Fin (n + 2) → ℝ,
      t 0 = 0 → t (Fin.last (n + 1)) = dist x z → StrictMono t →
      ∃ p : Fin (n + 2) → X, p 0 = x ∧ p (Fin.last (n + 1)) = z ∧
        ∀ i j : Fin (n + 2), i ≤ j → dist (p i) (p j) = t j - t i := by
  intro n
  induction n generalizing z with
  | zero =>
      intro t htzero htlast _
      let p : Fin 2 → X := Fin.cons x (fun _ : Fin 1 ↦ z)
      refine ⟨p, by simp [p], by simp [p], ?_⟩
      intro i j hij
      rcases hij.eq_or_lt with rfl | hij
      · simp
      · have hiv : i.val = 0 := by omega
        have hjv : j.val = 1 := by omega
        have hi : i = 0 := Fin.ext hiv
        have hj : j = Fin.last 1 := by
          apply Fin.ext
          simpa using hjv
        subst i
        subst j
        simpa [p, htzero] using htlast.symm
  | succ n ihn =>
      intro t htzero htlast htmono
      let u : Fin (n + 2) → ℝ := fun i ↦ t i.castSucc
      let a : ℝ := t (Fin.last (n + 1)).castSucc
      have ha0 : 0 ≤ a := by
        dsimp [a]
        rw [← htzero]
        exact htmono.monotone (Fin.zero_le _)
      have had : a ≤ dist x z := by
        dsimp [a]
        rw [← htlast]
        exact htmono.monotone (Fin.castSucc_lt_last _).le
      obtain ⟨y, hy⟩ := nonempty_segmentPointSet_of_properSpace hintrinsic x z ha0 had
      have huzero : u 0 = 0 := by
        simpa [u] using htzero
      have hulast : u (Fin.last (n + 1)) = dist x y := by
        simpa [u, a] using hy.1.symm
      have humono : StrictMono u := by
        intro i j hij
        exact htmono (by simpa using hij)
      obtain ⟨p, hpzero, hplast, hpdist⟩ := ihn y u huzero hulast humono
      let q : Fin (n + 3) → X := Fin.snoc p z
      have hulast_a : u (Fin.last (n + 1)) = a := by
        calc
          u (Fin.last (n + 1)) = dist x y := hulast
          _ = a := hy.1
      have hpx (i : Fin (n + 2)) : dist x (p i) = u i := by
        calc
          dist x (p i) = dist (p 0) (p i) := by rw [hpzero]
          _ = u i - u 0 := hpdist 0 i (Fin.zero_le _)
          _ = u i := by rw [huzero]; ring
      have hpy (i : Fin (n + 2)) : dist (p i) y = a - u i := by
        calc
          dist (p i) y = dist (p i) (p (Fin.last (n + 1))) := by rw [hplast]
          _ = u (Fin.last (n + 1)) - u i :=
            hpdist i (Fin.last (n + 1)) (Fin.le_last _)
          _ = a - u i := by rw [hulast_a]
      have hpz (i : Fin (n + 2)) :
          dist (p i) z = t (Fin.last (n + 2)) - u i := by
        apply le_antisymm
        · calc
            dist (p i) z ≤ dist (p i) y + dist y z := dist_triangle _ _ _
            _ = t (Fin.last (n + 2)) - u i := by
              rw [hpy, hy.2]
              linarith [htlast]
        · have htriangle : dist x z ≤ dist x (p i) + dist (p i) z :=
            dist_triangle _ _ _
          rw [hpx] at htriangle
          linarith [htlast]
      refine ⟨q, ?_, ?_, ?_⟩
      · simpa [q] using hpzero
      · simp [q]
      · intro i j hij
        rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
        · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
          · simpa [q, u] using hpdist i j (by simpa using hij)
          · simpa [q, u] using hpz i
        · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
          · exact False.elim ((not_le_of_gt j.castSucc_lt_last) hij)
          · simp [q]

/-- Every point of a coherent finite chain lies in the corresponding exact
endpoint slice. -/
theorem mem_segmentPointSet_of_coherent_points
    {X : Type*} [PseudoMetricSpace X]
    {x z : X} {n : ℕ} {t : Fin (n + 2) → ℝ} {p : Fin (n + 2) → X}
    (htzero : t 0 = 0) (htlast : t (Fin.last (n + 1)) = dist x z)
    (hpzero : p 0 = x) (hplast : p (Fin.last (n + 1)) = z)
    (hpdist : ∀ i j : Fin (n + 2), i ≤ j → dist (p i) (p j) = t j - t i)
    (i : Fin (n + 2)) : p i ∈ segmentPointSet x z (t i) := by
  constructor
  · calc
      dist x (p i) = dist (p 0) (p i) := by rw [hpzero]
      _ = t i - t 0 := hpdist 0 i (Fin.zero_le _)
      _ = t i := by rw [htzero]; ring
  · calc
      dist (p i) z = dist (p i) (p (Fin.last (n + 1))) := by rw [hplast]
      _ = t (Fin.last (n + 1)) - t i :=
        hpdist i (Fin.last (n + 1)) (Fin.le_last _)
      _ = dist x z - t i := by rw [htlast]

/-- The finite chain is isometric on its ordered parameter set, with the
absolute-value form covering both orders of a pair of indices. -/
theorem abs_dist_eq_of_coherent_points
    {X : Type*} [PseudoMetricSpace X]
    {n : ℕ} {t : Fin (n + 2) → ℝ} {p : Fin (n + 2) → X}
    (htmono : StrictMono t)
    (hpdist : ∀ i j : Fin (n + 2), i ≤ j → dist (p i) (p j) = t j - t i)
    (i j : Fin (n + 2)) : dist (p i) (p j) = |t j - t i| := by
  rcases le_total i j with hij | hji
  · rw [hpdist i j hij, abs_of_nonneg]
    exact sub_nonneg.mpr (htmono.monotone hij)
  · calc
      dist (p i) (p j) = dist (p j) (p i) := dist_comm _ _
      _ = t i - t j := hpdist j i hji
      _ = |t j - t i| := by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (htmono.monotone hji))]

/-- The closed parameter interval for a prospective segment. -/
abbrev SegmentParameter {X : Type*} [PseudoMetricSpace X] (x z : X) :=
  Set.Icc (0 : ℝ) (dist x z)

/-- A simultaneous choice of an endpoint-slice point at every segment
parameter.  The compact-product argument below selects one which is coherent
for every pair of parameters. -/
abbrev SegmentFamily {X : Type*} [PseudoMetricSpace X] (x z : X) :=
  ∀ r : SegmentParameter x z, segmentPointSet x z (r : ℝ)

/-- One closed condition saying that a family has the correct distance at a
specified pair of parameters. -/
def coherentConstraint {X : Type*} [PseudoMetricSpace X] (x z : X)
    (r s : SegmentParameter x z) : Set (SegmentFamily x z) :=
  {f | dist (f r : X) (f s : X) = |(s : ℝ) - (r : ℝ)|}

theorem isClosed_coherentConstraint
    {X : Type*} [PseudoMetricSpace X] (x z : X)
    (r s : SegmentParameter x z) : IsClosed (coherentConstraint x z r s) := by
  change IsClosed {f : SegmentFamily x z |
    dist (f r : X) (f s : X) = |(s : ℝ) - (r : ℝ)|}
  apply isClosed_eq
  · exact ((continuous_subtype_val.comp (continuous_apply r)).dist
      (continuous_subtype_val.comp (continuous_apply s)))
  · exact continuous_const

/-- Tychonoff supplies compactness for the product of all compact endpoint
slices. -/
theorem compactSpace_segmentFamily
    {X : Type*} [PseudoMetricSpace X] [ProperSpace X] (x z : X) :
    CompactSpace (SegmentFamily x z) := by
  letI (r : SegmentParameter x z) : CompactSpace (segmentPointSet x z (r : ℝ)) :=
    isCompact_iff_compactSpace.mp (isCompact_segmentPointSet_of_properSpace x z r)
  infer_instance

/-- Any finite collection of pairwise segment-distance requirements can be
met simultaneously.  We sort the finitely many mentioned parameters and use
`exists_coherent_points_of_strictMono`; points at unmentioned parameters are
filled by arbitrary compact endpoint slices. -/
theorem finite_iInter_coherentConstraint_nonempty
    {X : Type*} [MetricSpace X] [ProperSpace X]
    (hintrinsic : HasApproximateIntermediate X) (x z : X)
    (u : Finset (SegmentParameter x z × SegmentParameter x z)) :
    (⋂ rs ∈ u, coherentConstraint x z rs.1 rs.2).Nonempty := by
  classical
  by_cases hdzero : dist x z = 0
  · have hxz : x = z := dist_eq_zero.mp hdzero
    subst z
    let f : SegmentFamily x x := fun r ↦
      ⟨x, by
        have hr : (r : ℝ) = 0 := by
          apply le_antisymm
          · simpa using r.2.2
          · exact r.2.1
        constructor <;> simp [hr]⟩
    refine ⟨f, ?_⟩
    rw [Set.mem_iInter]
    intro rs
    rw [Set.mem_iInter]
    intro _
    have hr : (rs.1 : ℝ) = 0 := by
      apply le_antisymm
      · simpa using rs.1.2.2
      · exact rs.1.2.1
    have hs : (rs.2 : ℝ) = 0 := by
      apply le_antisymm
      · simpa using rs.2.2.2
      · exact rs.2.2.1
    simp [coherentConstraint, f, hr, hs]
  · have hdpos : 0 < dist x z :=
      lt_of_le_of_ne dist_nonneg (Ne.symm hdzero)
    let r0 : SegmentParameter x z := ⟨0, le_rfl, hdpos.le⟩
    let rd : SegmentParameter x z := ⟨dist x z, dist_nonneg, le_rfl⟩
    let S : Finset (SegmentParameter x z) :=
      insert r0 (insert rd ((u.image Prod.fst) ∪ (u.image Prod.snd)))
    have hr0S : r0 ∈ S := by simp [S]
    have hrdS : rd ∈ S := by simp [S]
    have hr0ne : r0 ≠ rd := by
      intro h
      have hval := congrArg Subtype.val h
      dsimp [r0, rd] at hval
      linarith
    have hpair : ({r0, rd} : Finset (SegmentParameter x z)) ⊆ S := by
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact hr0S
      · rcases Finset.mem_singleton.mp hq with rfl
        exact hrdS
    have hcard : 2 ≤ S.card := by
      have hle := Finset.card_le_card hpair
      simpa [hr0ne] using hle
    let n : ℕ := S.card - 2
    have hncard : S.card = n + 2 := by
      dsimp [n]
      omega
    have hcardpos : 0 < n + 2 := by omega
    let e : Fin (n + 2) ↪o SegmentParameter x z := S.orderEmbOfFin hncard
    have hSnonempty : S.Nonempty := ⟨r0, hr0S⟩
    have hmin : S.min' hSnonempty = r0 := by
      apply le_antisymm
      · exact S.min'_le r0 hr0S
      · refine S.le_min' hSnonempty r0 ?_
        intro q _
        change (0 : ℝ) ≤ (q : ℝ)
        exact q.2.1
    have hmax : S.max' hSnonempty = rd := by
      apply le_antisymm
      · refine S.max'_le hSnonempty rd ?_
        intro q _
        change (q : ℝ) ≤ dist x z
        exact q.2.2
      · exact S.le_max' rd hrdS
    have hezero : e 0 = r0 := by
      change S.orderEmbOfFin hncard 0 = r0
      simpa using (Finset.orderEmbOfFin_zero (s := S) hncard hcardpos).trans hmin
    have hlastIndex : (Fin.last (n + 1) : Fin (n + 2)) =
        ⟨n + 2 - 1, Nat.sub_lt hcardpos Nat.zero_lt_one⟩ := by
      apply Fin.ext
      simp [Fin.last]
    have helast : e (Fin.last (n + 1)) = rd := by
      rw [hlastIndex]
      dsimp [e]
      exact (Finset.orderEmbOfFin_last hncard hcardpos).trans hmax
    let t : Fin (n + 2) → ℝ := fun i ↦ (e i : ℝ)
    have htzero : t 0 = 0 := by
      change (e 0 : ℝ) = 0
      rw [hezero]
    have htlast : t (Fin.last (n + 1)) = dist x z := by
      change (e (Fin.last (n + 1)) : ℝ) = dist x z
      rw [helast]
    have htmono : StrictMono t := by
      intro i j hij
      change (e i : ℝ) < (e j : ℝ)
      exact (e.lt_iff_lt).mpr hij
    obtain ⟨p, hpzero, hplast, hpdist⟩ :=
      exists_coherent_points_of_strictMono hintrinsic x z n t htzero htlast htmono
    have hpmem (i : Fin (n + 2)) : p i ∈ segmentPointSet x z (t i) :=
      mem_segmentPointSet_of_coherent_points htzero htlast hpzero hplast hpdist i
    let pointAt : ∀ r : SegmentParameter x z, r ∈ S →
        segmentPointSet x z (r : ℝ) := fun r hr ↦ by
      let i : Fin (n + 2) := (S.orderIsoOfFin hncard).symm ⟨r, hr⟩
      have hei : e i = r := by
        change (S.orderIsoOfFin hncard) i = r
        exact congrArg Subtype.val
          ((S.orderIsoOfFin hncard).apply_symm_apply ⟨r, hr⟩)
      have hti : t i = (r : ℝ) := by
        change (e i : ℝ) = (r : ℝ)
        exact congrArg Subtype.val hei
      exact ⟨p i, by simpa [hti] using hpmem i⟩
    let default : ∀ r : SegmentParameter x z, segmentPointSet x z (r : ℝ) := fun r ↦
      ⟨(nonempty_segmentPointSet_of_properSpace hintrinsic x z r.2.1 r.2.2).choose,
        (nonempty_segmentPointSet_of_properSpace hintrinsic x z r.2.1 r.2.2).choose_spec⟩
    let f : SegmentFamily x z := fun r ↦
      if hr : r ∈ S then pointAt r hr else default r
    have hf_eq (r : SegmentParameter x z) (hr : r ∈ S) :
        (f r : X) = p ((S.orderIsoOfFin hncard).symm ⟨r, hr⟩) := by
      simp only [f, dif_pos hr]
      rfl
    refine ⟨f, ?_⟩
    rw [Set.mem_iInter]
    intro rs
    rw [Set.mem_iInter]
    intro hrs
    have hrs1 : rs.1 ∈ S := by
      apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨rs, hrs, rfl⟩
    have hrs2 : rs.2 ∈ S := by
      apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨rs, hrs, rfl⟩
    let i : Fin (n + 2) := (S.orderIsoOfFin hncard).symm ⟨rs.1, hrs1⟩
    let j : Fin (n + 2) := (S.orderIsoOfFin hncard).symm ⟨rs.2, hrs2⟩
    have hei : e i = rs.1 := by
      dsimp [e, i]
      exact congrArg Subtype.val
        ((S.orderIsoOfFin hncard).apply_symm_apply ⟨rs.1, hrs1⟩)
    have hej : e j = rs.2 := by
      dsimp [e, j]
      exact congrArg Subtype.val
        ((S.orderIsoOfFin hncard).apply_symm_apply ⟨rs.2, hrs2⟩)
    have hti : t i = (rs.1 : ℝ) := by
      change (e i : ℝ) = (rs.1 : ℝ)
      exact congrArg Subtype.val hei
    have htj : t j = (rs.2 : ℝ) := by
      change (e j : ℝ) = (rs.2 : ℝ)
      exact congrArg Subtype.val hej
    change dist (f rs.1 : X) (f rs.2 : X) = |(rs.2 : ℝ) - (rs.1 : ℝ)|
    rw [hf_eq rs.1 hrs1, hf_eq rs.2 hrs2]
    change dist (p i) (p j) = |(rs.2 : ℝ) - (rs.1 : ℝ)|
    rw [abs_dist_eq_of_coherent_points htmono hpdist i j, hti, htj]

/-- A proper intrinsic metric admits a continuous exact minimizing segment
between any two points.  The proof is a compact-product/FIP construction:
finite constraints are realized by coherent chains, and Tychonoff then makes
all pairwise constraints hold at once. -/
theorem exists_metric_segment_of_properSpace
    {X : Type*} [MetricSpace X] [ProperSpace X]
    (hintrinsic : HasApproximateIntermediate X) (x z : X) :
    ∃ γ : SegmentParameter x z → X, Continuous γ ∧
      γ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x ∧
      γ ⟨dist x z, ⟨dist_nonneg, le_rfl⟩⟩ = z ∧
      ∀ r s, dist (γ r) (γ s) = |(s : ℝ) - (r : ℝ)| := by
  letI : CompactSpace (SegmentFamily x z) := compactSpace_segmentFamily x z
  obtain ⟨f, hf⟩ := CompactSpace.iInter_nonempty
    (t := fun rs : SegmentParameter x z × SegmentParameter x z ↦
      coherentConstraint x z rs.1 rs.2)
    (fun rs ↦ isClosed_coherentConstraint x z rs.1 rs.2)
    (fun u ↦ finite_iInter_coherentConstraint_nonempty hintrinsic x z u)
  let γ : SegmentParameter x z → X := fun r ↦ f r
  have hpair (r s : SegmentParameter x z) :
      dist (γ r) (γ s) = |(s : ℝ) - (r : ℝ)| := by
    simpa [γ, coherentConstraint] using Set.mem_iInter.mp hf (r, s)
  have hmetric : Isometry γ := by
    apply Isometry.of_dist_eq
    intro r s
    calc
      dist (γ r) (γ s) = |(s : ℝ) - (r : ℝ)| := hpair r s
      _ = |(r : ℝ) - (s : ℝ)| := abs_sub_comm _ _
      _ = dist r s := by rw [Subtype.dist_eq, Real.dist_eq]
  have hzero : γ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x := by
    have hslice := (f ⟨0, ⟨le_rfl, dist_nonneg⟩⟩).property.1
    have hdist : dist x (f ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ : X) = 0 := by
      simpa using hslice
    exact (dist_eq_zero.mp hdist).symm
  have hlast : γ ⟨dist x z, ⟨dist_nonneg, le_rfl⟩⟩ = z := by
    have hslice := (f ⟨dist x z, ⟨dist_nonneg, le_rfl⟩⟩).property.2
    have hdist : dist (f ⟨dist x z, ⟨dist_nonneg, le_rfl⟩⟩ : X) z = 0 := by
      simpa using hslice
    exact dist_eq_zero.mp hdist
  exact ⟨γ, hmetric.continuous, hzero, hlast, hpair⟩

end MetricHopfRinow
end BonnetMyersEntry
