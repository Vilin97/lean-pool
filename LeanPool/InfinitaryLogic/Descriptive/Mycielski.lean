/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Topology.MetricSpace.CantorScheme
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Mycielski's theorem for Cantor space

`mycielski_cantor`: for a meager set `M ⊆ (ℕ → Bool) × (ℕ → Bool)` there is a continuous
`ψ : (ℕ → Bool) → (ℕ → Bool)` with `(ψ a, ψ b) ∉ M` for all `a ≠ b`. This is Mycielski's
independent-set theorem (Kechris, CDST 19.1) specialized to Cantor space and binary relations
— step 4 of the classical category route to Silver's theorem (see
`InfinitaryLogic/Conditional/SilverCategoryRoute.lean` and `docs/silver-phase2-route.md`).

## Construction

Write the complement of `M` over a countable family of dense open sets `U k`. Build, by
recursion on levels, a family of pointed cylinders (anchor, depth) indexed by `List Bool`
nodes:

* **split**: each node `l` of level `m` gets two children `b :: l` whose anchors differ at the
  parent's depth coordinate;
* **pair-killing fold**: all (finitely many) pairs of distinct level-`(m+1)` nodes are then
  refined, one pair at a time, so that the product of their cylinders lands inside
  `⋂ k ≤ m, U k` — a dense open set (finite intersection of dense opens, dense by the Baire
  property of the complete product space).

The scheme of (closed) cylinders has vanishing diameter and contains the closures of its
children, so `CantorScheme.inducedMap` is total and continuous. For distinct branches `a ≠ b`
and any `k`, at any level `m > max (firstDiff a b) k` the branch nodes are distinct, so the
image pair lies in `U k`; hence it lies in `⋂ k, U k ⊆ Mᶜ`.

Avoidance is achieved only in the limit — for dense `M` no two cylinders can have
cross-product avoiding `M` — which is why this construction does **not** factor through
`CantorScheme.exists_antichain_map` (whose sibling cross-avoidance hypothesis is exactly
finite-stage avoidance). Injectivity of `ψ` is not claimed; downstream consumers recover it
from reflexivity of the relation being avoided.

## Implementation note

Cantor space carries the `PiNat` metric via `PiNat.metricSpaceOfDiscreteUniformity`, whose
uniformity is definitionally the product uniformity (see the warning on `PiNat.metricSpace`:
since `Bool` has a `UniformSpace` instance, the plain `PiNat.metricSpace` would create a
second, non-defeq uniform structure).
-/

open Set PiNat Filter Topology

namespace MycielskiCantor

/-- The `PiNat` metric on Cantor space; its uniformity (hence topology) is definitionally
the product one. -/
@[reducible] private noncomputable def cantorMetricSpace : MetricSpace (ℕ → Bool) :=
  PiNat.metricSpaceOfDiscreteUniformity fun _ => rfl

attribute [local instance] cantorMetricSpace

private theorem cantorCompleteSpace : CompleteSpace (ℕ → Bool) :=
  inferInstanceAs (@CompleteSpace (ℕ → Bool) (Pi.uniformSpace _))

attribute [local instance] cantorCompleteSpace

/-! ### Cylinder prerequisites -/

/-- Cylinders are closed (they are in fact clopen). -/
private lemma isClosed_cylinder (x : ℕ → Bool) (n : ℕ) : IsClosed (cylinder x n) := by
  have h : cylinder x n = ⋂ i ∈ Finset.range n, {y : ℕ → Bool | y i = x i} := by
    ext y
    simp [PiNat.mem_cylinder_iff]
  rw [h]
  exact isClosed_biInter fun i _ => isClosed_eq (continuous_apply i) continuous_const

private lemma ediam_cylinder_le (x : ℕ → Bool) (n : ℕ) :
    Metric.ediam (cylinder x n) ≤ ENNReal.ofReal ((1 / 2) ^ n) := by
  apply Metric.ediam_le
  intro y hy z hz
  rw [edist_dist, ENNReal.ofReal_le_ofReal_iff (by positivity)]
  have hyz : y ∈ cylinder z n := mem_cylinder_iff.mpr fun i hi =>
    (mem_cylinder_iff.mp hy i hi).trans (mem_cylinder_iff.mp hz i hi).symm
  exact mem_cylinder_iff_dist_le.mp hyz

/-- Every open neighborhood contains a cylinder around the point. -/
private lemma exists_cylinder_subset {V : Set (ℕ → Bool)} (hV : IsOpen V) {x : ℕ → Bool} (hx
  : x ∈ V) :
    ∃ n, cylinder x n ⊆ V := by
  obtain ⟨s, ⟨z, n, rfl⟩, hxs, hsV⟩ :=
    (isTopologicalBasis_cylinders (fun _ : ℕ => Bool)).exists_subset_of_mem_open hx hV
  exact ⟨n, by rw [mem_cylinder_iff_eq.mp hxs]; exact hsV⟩

/-! ### Pointed cylinders and refinement -/

/-- `Refines q p`: the pointed cylinder `q = (anchor, depth)` is at least as deep as `p` and
its cylinder is contained in that of `p`. -/
def Refines (q p : (ℕ → Bool) × ℕ) : Prop :=
  p.2 ≤ q.2 ∧ cylinder q.1 q.2 ⊆ cylinder p.1 p.2

lemma Refines.refl (p : (ℕ → Bool) × ℕ) : Refines p p := ⟨le_rfl, subset_rfl⟩

lemma Refines.trans {r q p : (ℕ → Bool) × ℕ} (h₁ : Refines r q) (h₂ : Refines q p) :
    Refines r p :=
  ⟨h₂.1.trans h₁.1, h₁.2.trans h₂.2⟩

/-- **Single pair-killing move**: two pointed cylinders can be refined so that the product of
their cylinders lands inside a given dense open subset of the square. -/
private lemma exists_refines_box_subset {U : Set ((ℕ → Bool) × (ℕ → Bool))}
    (hUo : IsOpen U) (hUd : Dense U) (p q : (ℕ → Bool) × ℕ) :
    ∃ p' q' : (ℕ → Bool) × ℕ, Refines p' p ∧ Refines q' q ∧
      cylinder p'.1 p'.2 ×ˢ cylinder q'.1 q'.2 ⊆ U := by
  have hbox : IsOpen (cylinder p.1 p.2 ×ˢ cylinder q.1 q.2) :=
    IsOpen.prod (isOpen_cylinder _ p.1 p.2) (isOpen_cylinder _ q.1 q.2)
  have hboxne : (cylinder p.1 p.2 ×ˢ cylinder q.1 q.2).Nonempty :=
    ⟨(p.1, q.1), self_mem_cylinder _ _, self_mem_cylinder _ _⟩
  obtain ⟨⟨x, y⟩, hmem, hU⟩ := hUd.inter_open_nonempty _ hbox hboxne
  obtain ⟨hx, hy⟩ := hmem
  obtain ⟨V₀, V₁, hV₀, hV₁, hxV₀, hyV₁, hVU⟩ := isOpen_prod_iff.mp hUo x y hU
  obtain ⟨n₀, hn₀⟩ := exists_cylinder_subset hV₀ hxV₀
  obtain ⟨n₁, hn₁⟩ := exists_cylinder_subset hV₁ hyV₁
  set N := max (max n₀ n₁) (max p.2 q.2) with hN
  have hsub₀ : cylinder x N ⊆ cylinder p.1 p.2 := by
    rw [← mem_cylinder_iff_eq.mp hx]
    exact cylinder_anti x (le_max_of_le_right (le_max_left _ _))
  have hsub₁ : cylinder y N ⊆ cylinder q.1 q.2 := by
    rw [← mem_cylinder_iff_eq.mp hy]
    exact cylinder_anti y (le_max_of_le_right (le_max_right _ _))
  refine ⟨(x, N), (y, N),
    ⟨le_max_of_le_right (le_max_left _ _), hsub₀⟩,
    ⟨le_max_of_le_right (le_max_right _ _), hsub₁⟩, ?_⟩
  refine (Set.prod_mono ?_ ?_).trans hVU
  · exact (cylinder_anti x (le_max_of_le_left (le_max_left _ _))).trans hn₀
  · exact (cylinder_anti y (le_max_of_le_left (le_max_right _ _))).trans hn₁

/-- **Pair-killing fold**: a family of pointed cylinders can be refined so that all pairs of
distinct indices from a given finite set of pairs have cylinder products inside a dense open
subset of the square. -/
private lemma exists_refines_forall_pairs {ι : Type*}
    {U : Set ((ℕ → Bool) × (ℕ → Bool))} (hUo : IsOpen U) (hUd : Dense U)
    (s : Finset (ι × ι)) (P : ι → (ℕ → Bool) × ℕ) :
    ∃ Q : ι → (ℕ → Bool) × ℕ, (∀ i, Refines (Q i) (P i)) ∧
      ∀ ab ∈ s, ab.1 ≠ ab.2 →
        cylinder (Q ab.1).1 (Q ab.1).2 ×ˢ cylinder (Q ab.2).1 (Q ab.2).2 ⊆ U := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨P, fun i => Refines.refl _, by simp⟩
  | @insert a s ha IH =>
    obtain ⟨Q, hQP, hQs⟩ := IH
    by_cases hab : a.1 = a.2
    · refine ⟨Q, hQP, fun ab hab' hne => ?_⟩
      rcases Finset.mem_insert.mp hab' with rfl | h
      · exact absurd hab hne
      · exact hQs ab h hne
    · obtain ⟨p', q', hp', hq', hbox⟩ := exists_refines_box_subset hUo hUd (Q a.1) (Q a.2)
      set Q' : ι → (ℕ → Bool) × ℕ :=
        Function.update (Function.update Q a.1 p') a.2 q' with hQ'
      have hQ'a1 : Q' a.1 = p' := by
        rw [hQ', Function.update_of_ne hab, Function.update_self]
      have hQ'a2 : Q' a.2 = q' := by rw [hQ', Function.update_self]
      have hQ'ref : ∀ i, Refines (Q' i) (Q i) := by
        intro i
        by_cases h2 : i = a.2
        · subst h2; rw [hQ'a2]; exact hq'
        · by_cases h1 : i = a.1
          · subst h1; rw [hQ'a1]; exact hp'
          · rw [hQ', Function.update_of_ne h2, Function.update_of_ne h1]
            exact Refines.refl _
      refine ⟨Q', fun i => (hQ'ref i).trans (hQP i), fun ab hab' hne => ?_⟩
      rcases Finset.mem_insert.mp hab' with rfl | h
      · rw [hQ'a1, hQ'a2]; exact hbox
      · exact (Set.prod_mono (hQ'ref ab.1).2 (hQ'ref ab.2).2).trans (hQs ab h hne)

/-! ### Level-indexed stages -/

/-- All binary lists of a given length, as a finset. -/
private def boolLists : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 => (boolLists n).biUnion fun l => {false :: l, true :: l}

private lemma mem_boolLists_of_length : ∀ {n : ℕ} {l : List Bool}, l.length = n → l ∈ boolLists n
  | 0, [], _ => by simp [boolLists]
  | 0, _ :: _, h => by simp at h
  | _ + 1, [], h => by simp at h
  | n + 1, b :: l', h => by
    have hl' : l' ∈ boolLists n := mem_boolLists_of_length (Nat.succ_injective h)
    change b :: l' ∈ (boolLists n).biUnion fun l => {false :: l, true :: l}
    refine Finset.mem_biUnion.mpr ⟨l', hl', ?_⟩
    cases b <;> simp

variable (U : ℕ → Set ((ℕ → Bool) × (ℕ → Bool)))

/-- Stage `m` of the construction: a pointed cylinder for every node, such that level-`m`
nodes have depth at least `m` and all pairs of distinct level-`m` nodes have cylinder
products inside `U k` for every `k < m`. -/
private structure Stage (m : ℕ) where
  f : List Bool → (ℕ → Bool) × ℕ
  le_depth : ∀ l : List Bool, l.length = m → m ≤ (f l).2
  avoid : ∀ l₁ l₂ : List Bool, l₁.length = m → l₂.length = m → l₁ ≠ l₂ →
    ∀ k < m, cylinder (f l₁).1 (f l₁).2 ×ˢ cylinder (f l₂).1 (f l₂).2 ⊆ U k

/-- The root stage: every node gets the full space. -/
private def base : Stage U 0 where
  f := fun _ => (fun _ => false, 0)
  le_depth := fun _ _ => Nat.zero_le _
  avoid := fun _ _ _ _ _ k hk => absurd hk (Nat.not_lt_zero k)

variable {U}

variable {m : ℕ}

/-- The split step: each child `b :: l` refines its parent `l` by fixing the coordinate at
the parent's depth to `b`. -/
private def presplit (S : Stage U m) : List Bool → (ℕ → Bool) × ℕ
  | [] => S.f []
  | b :: l => (Function.update (S.f l).1 (S.f l).2 b, (S.f l).2 + 1)

private lemma presplit_refines (S : Stage U m) (b : Bool) (l : List Bool) :
    Refines (presplit S (b :: l)) (S.f l) := by
  refine ⟨Nat.le_succ _, fun z hz => mem_cylinder_iff.mpr fun i hi => ?_⟩
  have hz' := mem_cylinder_iff.mp hz i (hi.trans (Nat.lt_succ_self _))
  rw [show (presplit S (b :: l)).1 = Function.update (S.f l).1 (S.f l).2 b from rfl] at hz'
  rw [hz', Function.update_of_ne hi.ne]

/-- The inductive step: split every node, then run the pair-killing fold against the
(dense open) intersection of the first `m + 1` dense open sets. -/
private lemma exists_step (hUo : ∀ k, IsOpen (U k)) (hUd : ∀ k, Dense (U k)) (S : Stage U m) :
    ∃ T : Stage U (m + 1), ∀ l : List Bool, ∀ b : Bool, l.length = m →
      Refines (T.f (b :: l)) (S.f l) := by
  classical
  set V : Set ((ℕ → Bool) × (ℕ → Bool)) := ⋂ k ∈ Finset.range (m + 1), U k with hV
  have hVo : IsOpen V := isOpen_biInter_finset fun k _ => hUo k
  have hVd : Dense V :=
    dense_of_mem_residual ((Filter.biInter_finset_mem _).mpr
      fun k _ => residual_of_dense_open (hUo k) (hUd k))
  obtain ⟨Q, hQref, hQav⟩ := exists_refines_forall_pairs hVo hVd
    ((boolLists (m + 1)) ×ˢ (boolLists (m + 1))) (presplit S)
  have hrefines : ∀ l : List Bool, ∀ b : Bool, l.length = m →
      Refines (Q (b :: l)) (S.f l) :=
    fun l b hl => (hQref (b :: l)).trans (presplit_refines S b l)
  refine ⟨⟨Q, ?_, ?_⟩, hrefines⟩
  · -- depth
    rintro (_ | ⟨b, l'⟩) hl
    · simp at hl
    · have hl' : l'.length = m := Nat.succ_injective hl
      have h2 := (hQref (b :: l')).1
      rw [show (presplit S (b :: l')).2 = (S.f l').2 + 1 from rfl] at h2
      exact le_trans (Nat.succ_le_succ (S.le_depth l' hl')) h2
  · -- avoidance
    intro l₁ l₂ h₁ h₂ hne k hk
    have hmem : (l₁, l₂) ∈ (boolLists (m + 1)) ×ˢ (boolLists (m + 1)) :=
      Finset.mem_product.mpr ⟨mem_boolLists_of_length h₁, mem_boolLists_of_length h₂⟩
    refine (hQav (l₁, l₂) hmem hne).trans ?_
    exact Set.biInter_subset_of_mem (Finset.mem_range.mpr hk)

variable (U) in
/-- The full tower of stages, with each level refining the previous one. -/
private noncomputable def stages (hUo : ∀ k, IsOpen (U k)) (hUd : ∀ k, Dense (U k)) :
    ∀ m, Stage U m
  | 0 => base U
  | m + 1 => Classical.choose (exists_step hUo hUd (stages hUo hUd m))

private lemma stages_refines (hUo : ∀ k, IsOpen (U k)) (hUd : ∀ k, Dense (U k))
    (m : ℕ) (l : List Bool) (b : Bool) (hl : l.length = m) :
    Refines ((stages U hUo hUd (m + 1)).f (b :: l)) ((stages U hUo hUd m).f l) :=
  Classical.choose_spec (exists_step hUo hUd (stages U hUo hUd m)) l b hl

end MycielskiCantor

open Set PiNat MycielskiCantor in
/-- **Mycielski's theorem for Cantor space**: for a meager set `M` in the square of Cantor
space, there is a continuous `ψ : (ℕ → Bool) → (ℕ → Bool)` such that `(ψ a, ψ b) ∉ M`
whenever `a ≠ b`. (Kechris, CDST 19.1, specialized.) Injectivity of `ψ` is not asserted;
when avoiding a reflexive relation it is automatic. -/
theorem mycielski_cantor {M : Set ((ℕ → Bool) × (ℕ → Bool))} (hM : IsMeagre M) :
    ∃ ψ : (ℕ → Bool) → (ℕ → Bool), Continuous ψ ∧
      ∀ a b : ℕ → Bool, a ≠ b → (ψ a, ψ b) ∉ M := by
  classical
  let : MetricSpace (ℕ → Bool) := cantorMetricSpace
  have : CompleteSpace (ℕ → Bool) := cantorCompleteSpace
  -- Extract a countable family of dense open sets with intersection inside `Mᶜ`
  obtain ⟨U, hUo, hUd, hUM⟩ : ∃ U : ℕ → Set ((ℕ → Bool) × (ℕ → Bool)),
      (∀ k, IsOpen (U k)) ∧ (∀ k, Dense (U k)) ∧ (⋂ k, U k) ⊆ Mᶜ := by
    obtain ⟨T, hTo, hTd, hTc, hTM⟩ := mem_residual_iff.mp hM
    obtain ⟨U, hU⟩ := (hTc.insert Set.univ).exists_eq_range (insert_nonempty _ _)
    have hmem : ∀ k, U k ∈ insert Set.univ T := fun k => hU ▸ mem_range_self k
    refine ⟨U, fun k => ?_, fun k => ?_, ?_⟩
    · rcases Set.mem_insert_iff.mp (hmem k) with h | h
      · rw [h]; exact isOpen_univ
      · exact hTo _ h
    · rcases Set.mem_insert_iff.mp (hmem k) with h | h
      · rw [h]; exact dense_univ
      · exact hTd _ h
    · have h1 : ⋂ k, U k = ⋂₀ insert Set.univ T := by
        rw [hU, sInter_range]
      rw [h1, sInter_insert]
      exact inter_subset_right.trans hTM
  -- The tower of stages and the associated scheme of closed cylinders
  set S : ∀ m, MycielskiCantor.Stage U m := stages U hUo hUd with hS
  set w : List Bool → (ℕ → Bool) × ℕ := fun l => (S l.length).f l with hw
  set A : List Bool → Set (ℕ → Bool) := fun l => cylinder (w l).1 (w l).2 with hA
  have hanti : CantorScheme.ClosureAntitone A := by
    apply CantorScheme.Antitone.closureAntitone
    · intro l b
      exact (stages_refines hUo hUd l.length l b rfl).2
    · intro l
      exact isClosed_cylinder _ _
  have hnonempty : ∀ l, (A l).Nonempty := fun l => ⟨(w l).1, self_mem_cylinder _ _⟩
  have hdiam : CantorScheme.VanishingDiam A := by
    intro x
    have hbound : ∀ n, Metric.ediam (A (res x n)) ≤ ENNReal.ofReal ((1 / 2) ^ n) := by
      intro n
      have hlen : (res x n).length = n := res_length _ _
      have hSx : (S (res x n).length).f (res x n) = (S n).f (res x n) := by rw [hlen]
      have hdepth : n ≤ (w (res x n)).2 := by
        simp only [hw]
        rw [hSx]
        exact (S n).le_depth (res x n) hlen
      have h1 : Metric.ediam (A (res x n)) ≤ ENNReal.ofReal ((1 / 2) ^ (w (res x n)).2) := by
        simp only [hA]
        exact ediam_cylinder_le _ _
      refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hdepth
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal ((1 / 2) ^ n)) atTop (nhds 0) := by
      have h : ∀ n : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ n) = ENNReal.ofReal (1 / 2) ^ n :=
        fun n => ENNReal.ofReal_pow (by norm_num) n
      simp only [h]
      exact ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
        (by rw [ENNReal.ofReal_lt_one]; norm_num)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => bot_le) hbound
  -- Extract the induced map
  have hdom : ∀ x : ℕ → Bool, x ∈ (CantorScheme.inducedMap A).1 := fun x => by
    rw [@CantorScheme.ClosureAntitone.map_of_vanishingDiam Bool (ℕ → Bool) A _
      cantorCompleteSpace hdiam hanti hnonempty]
    exact mem_univ x
  refine ⟨fun x => (CantorScheme.inducedMap A).2 ⟨x, hdom x⟩, ?_, ?_⟩
  · exact hdiam.map_continuous.comp (by fun_prop)
  -- Avoidance in the limit
  · intro a b hab hmem
    have hcompl : ((CantorScheme.inducedMap A).2 ⟨a, hdom a⟩,
        (CantorScheme.inducedMap A).2 ⟨b, hdom b⟩) ∈ Mᶜ := by
      apply hUM
      refine mem_iInter.mpr fun k => ?_
      set m := max (firstDiff a b + 1) (k + 1) with hm
      have hka : k < m := lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_right _ _)
      have hfd : firstDiff a b < m :=
        lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
      have hlen₁ : (res a m).length = m := res_length _ _
      have hlen₂ : (res b m).length = m := res_length _ _
      have hne : res a m ≠ res b m := by
        intro h
        exact apply_firstDiff_ne hab (res_eq_res.mp h hfd)
      have havoid := (S m).avoid (res a m) (res b m) hlen₁ hlen₂ hne k hka
      have hmema := CantorScheme.map_mem (A := A) ⟨a, hdom a⟩ m
      have hmemb := CantorScheme.map_mem (A := A) ⟨b, hdom b⟩ m
      have hSa : (S (res a m).length).f (res a m) = (S m).f (res a m) := by rw [hlen₁]
      have hSb : (S (res b m).length).f (res b m) = (S m).f (res b m) := by rw [hlen₂]
      simp only [hA, hw] at hmema hmemb
      rw [hSa] at hmema
      rw [hSb] at hmemb
      exact havoid (Set.mk_mem_prod hmema hmemb)
    exact hcompl hmem
