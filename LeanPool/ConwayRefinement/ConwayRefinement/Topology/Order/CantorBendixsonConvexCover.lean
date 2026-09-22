/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Topology.CantorBendixsonRank
import Mathlib.Order.WellFounded
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# A disjoint convex cover controlled by Cantor–Bendixson rank

Fix a nested well-ordered family of open order-convex additive subgroups forming a neighborhood
base at zero. Every point of a closed partially well-ordered set has cosets in which it is the
largest point of the set and its unique point of maximal Cantor--Bendixson rank; along the nested
base each point has a least such level. The cosets of least level through each point are maximal
in the whole chosen family, so the maximal members cover the set, are pairwise disjoint and order
separated, and carry one center each. The centers accumulate nowhere, including at zero, because
every center owns an open coset meeting no other center.

The output forgets the subgroups: it consists of open order-convex pairwise disjoint ordered
pieces, each containing its center as the largest point of the set inside it, with every other
point of the set inside of strictly smaller rank. This is the localization used by the
well-founded cofactor construction, at arbitrary cofinality and with no countability hypothesis.
-/

open Set Filter Topology TopologicalSpace

universe u v

public noncomputable section

variable {G : Type u} {κ : Type v}
  [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [TopologicalSpace G] [OrderTopology G] [NoMinOrder G] [NoMaxOrder G]
  [LinearOrder κ] [WellFoundedLT κ]

omit [AddCommGroup G] [IsOrderedAddMonoid G] [TopologicalSpace G] [OrderTopology G]
  [NoMinOrder G] [NoMaxOrder G] [LinearOrder κ] [WellFoundedLT κ] in
/-- Two disjoint order-convex sets crossed by one ordered pair are fully order separated. -/
theorem Set.OrdConnected.forall_lt_of_disjoint {D E : Set G}
    (hD : D.OrdConnected) (hE : E.OrdConnected) (hDE : Disjoint D E)
    {d e : G} (hd : d ∈ D) (he : e ∈ E) (hde : d < e) :
    ∀ a ∈ D, ∀ b ∈ E, a < b := by
  intro a ha b hb
  by_contra hba
  have hba' : b ≤ a := not_lt.mp hba
  rcases lt_or_ge a e with hae | hea
  · exact Set.disjoint_left.mp hDE ha (hE.out hb he ⟨hba', hae.le⟩)
  · exact Set.disjoint_left.mp hDE (hD.out hd ha ⟨hde.le, hea⟩) he

namespace TopologicalSpace.Closeds

/-- A closed partially well-ordered set in a group with a nested well-ordered convex open subgroup
base has a pairwise disjoint ordered open convex cover. Each piece contains its center as the
largest member of the set inside it and as its unique member of maximal Cantor--Bendixson rank;
the centers accumulate nowhere. -/
theorem exists_disjoint_convex_cover_with_rank_lt_center_within
    (s : Closeds G) (hs : (s : Set G).IsPWO)
    (W : Set G) (hWopen : IsOpen W)
    (U : κ → AddSubgroup G)
    (hUmono : ∀ {i j : κ}, i ≤ j → (U j : Set G) ⊆ (U i : Set G))
    (hUopen : ∀ i, IsOpen (U i : Set G))
    (hUconv : ∀ i, (U i : Set G).OrdConnected)
    (hUbase : ∀ ε : G, 0 < ε → ∃ i, (U i : Set G) ⊆ Ioo (-ε) ε) :
    ∃ (X : Set G) (C : X → Set G),
      X ⊆ (s : Set G) ∩ W ∧
      (∀ x : X, (x : G) ∈ C x) ∧
      (∀ x : X, IsOpen (C x)) ∧
      (∀ x : X, (C x).OrdConnected) ∧
      (∀ x : X, C x ⊆ W) ∧
      (∀ x y : X, x ≠ y → Disjoint (C x) (C y)) ∧
      (∀ x y : X, (x : G) < (y : G) → ∀ a ∈ C x, ∀ b ∈ C y, a < b) ∧
      ((s : Set G) ∩ W ⊆ ⋃ x : X, C x) ∧
      (∀ x : X, ∀ z ∈ (s : Set G) ∩ C x, z ≤ (x : G)) ∧
      (∀ x : X, ∀ z ∈ (s : Set G) ∩ C x, z ≠ (x : G) →
        s.cantorBendixsonRank hs z < s.cantorBendixsonRank hs (x : G)) ∧
      (∀ z ∈ W, ¬ AccPt z (𝓟 X)) := by
  classical
  let T := {z : G // z ∈ (s : Set G) ∩ W}
  let coset : G → κ → Set G := fun z i ↦ (fun g ↦ z + g) '' (U i : Set G)
  have hcoset_mem : ∀ (z : G) (i : κ), z ∈ coset z i := fun z i ↦
    ⟨0, (U i).zero_mem, add_zero z⟩
  have hcoset_open : ∀ (z : G) (i : κ), IsOpen (coset z i) := by
    intro z i
    have hset : coset z i = (fun y ↦ y + -z) ⁻¹' (U i : Set G) := by
      ext y
      constructor
      · rintro ⟨u, hu, rfl⟩
        have he : (fun g ↦ z + g) u + -z = u := by
          change z + u + -z = u
          abel
        simpa only [Set.mem_preimage, he] using hu
      · intro hy
        exact ⟨y + -z, hy, by change z + (y + -z) = y; abel⟩
    rw [hset]
    exact (OrderIso.continuous (OrderIso.addRight (-z))).isOpen_preimage _ (hUopen i)
  have hcoset_conv : ∀ (z : G) (i : κ), (coset z i).OrdConnected := by
    intro z i
    constructor
    rintro a ⟨u, hu, rfl⟩ b ⟨v, hv, rfl⟩ w ⟨hwl, hwr⟩
    have hwl' : z + u ≤ w := hwl
    have hwr' : w ≤ z + v := hwr
    refine ⟨w - z, (hUconv i).out hu hv ⟨?_, ?_⟩, by change z + (w - z) = w; abel⟩
    · rwa [le_sub_iff_add_le, add_comm]
    · rwa [sub_le_iff_le_add, add_comm]
  -- Step 1: every point of the set has a valid level.
  have hlevel : ∀ z : T, ∃ i : κ, coset (z : G) i ⊆ W ∧
      (∀ w ∈ (s : Set G), w ∈ coset (z : G) i → w ≤ (z : G)) ∧
      (∀ w ∈ (s : Set G), w ∈ coset (z : G) i → w ≠ (z : G) →
        s.cantorBendixsonRank hs w < s.cantorBendixsonRank hs (z : G)) := by
    rintro ⟨z, hz⟩
    have hnearW := (hs.eventually_le z).and (s.cantorBendixsonRank_locally_lt hs z)
    have hnear : {y : G | (y ∈ (s : Set G) → y ≤ z) ∧
        (y ∈ s → y ≠ z → s.cantorBendixsonRank hs y < s.cantorBendixsonRank hs z)} ∩ W ∈
        𝓝 z := Filter.inter_mem hnearW (hWopen.mem_nhds hz.2)
    obtain ⟨a, b, ⟨haz, hzb⟩, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnear
    obtain ⟨i, hi⟩ := hUbase (min (z - a) (b - z))
      (lt_min (sub_pos.mpr haz) (sub_pos.mpr hzb))
    have hmem : ∀ w ∈ coset z i, w ∈ Ioo a b := by
      rintro w ⟨u, hu, rfl⟩
      have hu' := hi hu
      constructor
      · have h1 : -(z - a) < u := (neg_le_neg (min_le_left _ _)).trans_lt hu'.1
        have h2 := add_lt_add_left h1 z
        have e1 : -(z - a) + z = a := by abel
        rw [e1, add_comm u z] at h2
        exact h2
      · have h1 : u < b - z := hu'.2.trans_le (min_le_right _ _)
        have h2 := add_lt_add_left h1 z
        have e1 : b - z + z = b := by abel
        rw [e1, add_comm u z] at h2
        exact h2
    exact ⟨i, fun w hwm ↦ (hab (hmem w hwm)).2,
      fun w hw hwm ↦ (hab (hmem w hwm)).1.1 hw,
      fun w hw hwm ↦ (hab (hmem w hwm)).1.2 hw⟩
  -- Step 2: the least valid level and its coset.
  let good : T → Set κ := fun z ↦ {i : κ | coset (z : G) i ⊆ W ∧
    (∀ w ∈ (s : Set G), w ∈ coset (z : G) i → w ≤ (z : G)) ∧
    (∀ w ∈ (s : Set G), w ∈ coset (z : G) i → w ≠ (z : G) →
      s.cantorBendixsonRank hs w < s.cantorBendixsonRank hs (z : G))}
  have hne : ∀ z : T, (good z).Nonempty := fun z ↦ hlevel z
  let idx : T → κ := fun z ↦ wellFounded_lt.min (good z) (hne z)
  have hidx : ∀ z : T, idx z ∈ good z := fun z ↦ wellFounded_lt.min_mem (good z) (hne z)
  let B : T → Set G := fun z ↦ coset (z : G) (idx z)
  have hBmem : ∀ z : T, (z : G) ∈ B z := fun z ↦ hcoset_mem (z : G) (idx z)
  -- Cosets of comparable levels through a common point are nested.
  have hnest : ∀ z w : T, idx w ≤ idx z → ∀ y, y ∈ B z → y ∈ B w → B z ⊆ B w := by
    rintro z w hij y ⟨u, hu, hyu⟩ ⟨v, hv, hyv⟩ p ⟨q, hq, hpq⟩
    have hyu' : (z : G) + u = y := hyu
    have hyv' : (w : G) + v = y := hyv
    have hpq' : (z : G) + q = p := hpq
    refine ⟨v - u + q, (U (idx w)).add_mem ((U (idx w)).sub_mem hv (hUmono hij hu))
      (hUmono hij hq), ?_⟩
    change (w : G) + (v - u + q) = p
    have hzw : (z : G) = (w : G) + v - u := by
      rw [eq_sub_iff_add_eq, hyu', hyv']
    rw [← hpq', hzw]
    abel
  -- Equal cosets share their largest set point.
  have hcenter_eq : ∀ z w : T, B z = B w → (z : G) = (w : G) := by
    intro z w he
    have h1 : (z : G) ∈ B w := by rw [← he]; exact hBmem z
    have h2 : (w : G) ∈ B z := by rw [he]; exact hBmem w
    exact le_antisymm ((hidx w).2.1 z z.2.1 h1) ((hidx z).2.1 w w.2.1 h2)
  -- Step 3: the maximal cosets.
  let X : Set G := {p : G | ∃ hp : p ∈ (s : Set G) ∩ W,
    ∀ v : T, B ⟨p, hp⟩ ⊆ B v → B v = B ⟨p, hp⟩}
  have hXs : X ⊆ (s : Set G) ∩ W := fun p hp ↦ hp.choose
  let C : X → Set G := fun x ↦ B ⟨(x : G), hXs x.2⟩
  have hCmax : ∀ x : X, ∀ v : T, C x ⊆ B v → B v = C x := fun x ↦ x.2.choose_spec
  have hCmem : ∀ x : X, (x : G) ∈ C x := fun x ↦ hBmem _
  -- Disjointness of distinct maximal cosets.
  have hdisj : ∀ x y : X, x ≠ y → Disjoint (C x) (C y) := by
    intro x y hxy
    rw [Set.disjoint_left]
    intro q hqx hqy
    have hxyG : (x : G) ≠ (y : G) := fun h ↦ hxy (Subtype.ext h)
    rcases le_total (idx ⟨(x : G), hXs x.2⟩) (idx ⟨(y : G), hXs y.2⟩) with h | h
    · have hsub := hnest ⟨(y : G), hXs y.2⟩ ⟨(x : G), hXs x.2⟩ h q hqy hqx
      have heq := hCmax y ⟨(x : G), hXs x.2⟩ hsub
      exact hxyG (hcenter_eq ⟨(x : G), hXs x.2⟩ ⟨(y : G), hXs y.2⟩ heq)
    · have hsub := hnest ⟨(x : G), hXs x.2⟩ ⟨(y : G), hXs y.2⟩ h q hqx hqy
      have heq := hCmax x ⟨(y : G), hXs y.2⟩ hsub
      exact hxyG (hcenter_eq ⟨(y : G), hXs y.2⟩ ⟨(x : G), hXs x.2⟩ heq).symm
  -- Coverage: the least-level coset through a point is maximal.
  have hcov : (s : Set G) ∩ W ⊆ ⋃ x : X, C x := by
    intro p hp
    let covIdx : Set κ := {j : κ | ∃ w : T, idx w = j ∧ p ∈ B w}
    have hcovne : covIdx.Nonempty := ⟨idx ⟨p, hp⟩, ⟨p, hp⟩, rfl, hBmem ⟨p, hp⟩⟩
    obtain ⟨w, hwidx, hpw⟩ := wellFounded_lt.min_mem covIdx hcovne
    have hwmax : ∀ v : T, B w ⊆ B v → B v = B w := by
      intro v hsub
      have hpv : p ∈ B v := hsub hpw
      have hmv : idx w ≤ idx v := by
        rw [hwidx]
        exact WellFoundedLT.min_le (s := covIdx) (x := idx v) ⟨v, rfl, hpv⟩
      exact le_antisymm (hnest v w hmv p hpv hpw) hsub
    have hwX : (w : G) ∈ X := ⟨w.2, hwmax⟩
    exact Set.mem_iUnion.mpr ⟨⟨(w : G), hwX⟩, hpw⟩
  -- Order separation from disjointness and convexity.
  have hconv : ∀ x : X, (C x).OrdConnected := fun x ↦ hcoset_conv _ _
  have hord : ∀ x y : X, (x : G) < (y : G) → ∀ a ∈ C x, ∀ b ∈ C y, a < b := by
    intro x y hxy
    exact Set.OrdConnected.forall_lt_of_disjoint (hconv x) (hconv y)
      (hdisj x y fun h ↦ absurd (congrArg Subtype.val h) hxy.ne)
      (hCmem x) (hCmem y) hxy
  -- The centers accumulate nowhere.
  have hdiscrete : ∀ z ∈ W, ¬ AccPt z (𝓟 X) := by
    intro z hzW hacc
    rw [accPt_iff_nhds] at hacc
    by_cases hzs : z ∈ (s : Set G) ∩ W
    · obtain ⟨x₀, hx₀⟩ := Set.mem_iUnion.mp (hcov hzs)
      have hXC : ∀ y ∈ X, y ∈ C x₀ → y = (x₀ : G) := by
        intro y hy hyC
        by_contra hne
        exact Set.disjoint_left.mp
          (hdisj ⟨y, hy⟩ x₀ fun h ↦ hne (congrArg Subtype.val h))
          (hCmem ⟨y, hy⟩) hyC
      rcases eq_or_ne (x₀ : G) z with hx0z | hx0z
      · obtain ⟨y, ⟨hyC, hyX⟩, hyz⟩ := hacc (C x₀) ((hcoset_open _ _).mem_nhds hx₀)
        exact hyz (by rw [hXC y hyX hyC, hx0z])
      · rcases lt_or_gt_of_ne hx0z with hlt | hgt
        · obtain ⟨b, hzb⟩ := exists_gt z
          obtain ⟨y, ⟨⟨hyC, hy1, _⟩, hyX⟩, hyz⟩ := hacc (C x₀ ∩ Ioo (x₀ : G) b)
            ((((hcoset_open _ _).inter isOpen_Ioo)).mem_nhds ⟨hx₀, hlt, hzb⟩)
          exact absurd (hXC y hyX hyC) (ne_of_gt hy1)
        · obtain ⟨a, haz⟩ := exists_lt z
          obtain ⟨y, ⟨⟨hyC, _, hy2⟩, hyX⟩, hyz⟩ := hacc (C x₀ ∩ Ioo a (x₀ : G))
            ((((hcoset_open _ _).inter isOpen_Ioo)).mem_nhds ⟨hx₀, haz, hgt⟩)
          exact absurd (hXC y hyX hyC) (ne_of_lt hy2)
    · have hzsc : z ∉ (s : Set G) := fun h ↦ hzs ⟨h, hzW⟩
      obtain ⟨y, ⟨hyc, hyX⟩, -⟩ := hacc ((s : Set G)ᶜ)
        (s.isClosed.isOpen_compl.mem_nhds hzsc)
      exact hyc (hXs hyX).1
  exact ⟨X, C, hXs, hCmem, fun x ↦ hcoset_open _ _, hconv,
    fun x ↦ (hidx ⟨(x : G), hXs x.2⟩).1, hdisj, hord, hcov,
    fun x z hz ↦ (hidx ⟨(x : G), hXs x.2⟩).2.1 z hz.1 hz.2,
    fun x z hz hne ↦ (hidx ⟨(x : G), hXs x.2⟩).2.2 z hz.1 hz.2 hne, hdiscrete⟩

/-- The disjoint convex cover of the whole closed set, obtained by taking the open region to be
`univ`. -/
theorem exists_disjoint_convex_cover_with_rank_lt_center (s : Closeds G) (hs : (s : Set G).IsPWO)
    (U : κ → AddSubgroup G)
    (hUmono : ∀ {i j : κ}, i ≤ j → (U j : Set G) ⊆ (U i : Set G))
    (hUopen : ∀ i, IsOpen (U i : Set G))
    (hUconv : ∀ i, (U i : Set G).OrdConnected)
    (hUbase : ∀ ε : G, 0 < ε → ∃ i, (U i : Set G) ⊆ Ioo (-ε) ε) :
    ∃ (X : Set G) (C : X → Set G),
      X ⊆ (s : Set G) ∧
      (∀ x : X, (x : G) ∈ C x) ∧
      (∀ x : X, IsOpen (C x)) ∧
      (∀ x : X, (C x).OrdConnected) ∧
      (∀ x y : X, x ≠ y → Disjoint (C x) (C y)) ∧
      (∀ x y : X, (x : G) < (y : G) → ∀ a ∈ C x, ∀ b ∈ C y, a < b) ∧
      ((s : Set G) ⊆ ⋃ x : X, C x) ∧
      (∀ x : X, ∀ z ∈ (s : Set G) ∩ C x, z ≤ (x : G)) ∧
      (∀ x : X, ∀ z ∈ (s : Set G) ∩ C x, z ≠ (x : G) →
        s.cantorBendixsonRank hs z < s.cantorBendixsonRank hs (x : G)) ∧
      (∀ z : G, ¬ AccPt z (𝓟 X)) := by
  obtain ⟨X, C, hXs, hCmem, hCopen, hCconv, -, hCdisj, hCord, hCcov, hCmax, hCrank, hXdisc⟩ :=
    exists_disjoint_convex_cover_with_rank_lt_center_within s hs Set.univ isOpen_univ U
      hUmono hUopen hUconv hUbase
  refine ⟨X, C, fun p hp ↦ (hXs hp).1, hCmem, hCopen, hCconv, hCdisj, hCord, ?_, hCmax, hCrank,
    fun z ↦ hXdisc z (Set.mem_univ z)⟩
  intro p hp
  exact hCcov ⟨hp, Set.mem_univ p⟩

end TopologicalSpace.Closeds
