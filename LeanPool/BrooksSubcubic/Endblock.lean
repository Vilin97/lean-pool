/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BrooksSubcubic.CutVertex

/-!
# Subcubic Brooks theorem: Endblock

Part of the proof that a finite subcubic K₄-free graph is three-colourable.
-/

public section

section
open SimpleGraph Finset

namespace BrooksSubcubic

variable {V : Type*} [Fintype V]

omit [Fintype V] in
/-- Extract the two disequalities from membership in the complement of an unordered pair. -/
private lemma pair_compl_ne {a b x : V} (h : x ∈ (({a, b} : Set V)ᶜ)) : x ≠ a ∧ x ≠ b := by
  classical
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h
  exact h

omit [Fintype V] in
private lemma delete_pair_component_misses_an_attachment
    (G : SimpleGraph V)
    {a₀ y a b d : V}
    (ha : a ∈ (({a₀, y} : Set V)ᶜ)) (hb : b ∈ (({a₀, y} : Set V)ᶜ))
    (hcomp : (G.induce (({a₀, y} : Set V)ᶜ)).connectedComponentMk ⟨a, ha⟩ ≠
      (G.induce (({a₀, y} : Set V)ᶜ)).connectedComponentMk ⟨b, hb⟩)
    (hd : d ∈ (({a, b} : Set V)ᶜ))
    (hda₀ : (G.induce (({a, b} : Set V)ᶜ)).connectedComponentMk ⟨d, hd⟩ ≠
      (G.induce (({a, b} : Set V)ᶜ)).connectedComponentMk
        ⟨a₀, by simpa using And.intro (pair_compl_ne ha).1.symm (pair_compl_ne hb).1.symm⟩)
    (hdy : (G.induce (({a, b} : Set V)ᶜ)).connectedComponentMk ⟨d, hd⟩ ≠
      (G.induce (({a, b} : Set V)ᶜ)).connectedComponentMk
        ⟨y, by simpa using And.intro (pair_compl_ne ha).2.symm (pair_compl_ne hb).2.symm⟩) :
    (∀ (z : V) (hz : z ∈ (({a, b} : Set V)ᶜ)),
        (G.induce (({a, b} : Set V)ᶜ)).connectedComponentMk ⟨z, hz⟩ =
          (G.induce (({a, b} : Set V)ᶜ)).connectedComponentMk ⟨d, hd⟩ →
        ¬ G.Adj z a) ∨
    (∀ (z : V) (hz : z ∈ (({a, b} : Set V)ᶜ)),
        (G.induce (({a, b} : Set V)ᶜ)).connectedComponentMk ⟨z, hz⟩ =
          (G.induce (({a, b} : Set V)ᶜ)).connectedComponentMk ⟨d, hd⟩ →
        ¬ G.Adj z b) := by
  classical
  by_contra h
  push Not at h
  obtain ⟨za, hza, hzaD, hzaa⟩ := h.1
  obtain ⟨zb, hzb, hzbD, hzbb⟩ := h.2
  have hzab : (G.induce (({a, b} : Set V)ᶜ)).Reachable ⟨za, hza⟩ ⟨zb, hzb⟩ := by
    apply ConnectedComponent.eq.mp
    exact hzaD.trans hzbD.symm
  obtain ⟨p⟩ := hzab
  have hpavoid : ∀ x ∈ p.support, x.val ∈ (({a₀, y} : Set V)ᶜ) := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro hxa₀
      apply hda₀
      rw [← hzaD]
      apply ConnectedComponent.eq.mpr
      have hreach : (G.induce (({a, b} : Set V)ᶜ)).Reachable ⟨za, hza⟩ x := by
        exact ⟨p.takeUntil x hx⟩
      rw [show x =
        ⟨a₀, by simpa using And.intro (pair_compl_ne ha).1.symm (pair_compl_ne hb).1.symm⟩
        from Subtype.ext hxa₀] at hreach
      exact hreach
    · intro hxy
      apply hdy
      rw [← hzaD]
      apply ConnectedComponent.eq.mpr
      have hreach : (G.induce (({a, b} : Set V)ᶜ)).Reachable ⟨za, hza⟩ x := by
        exact ⟨p.takeUntil x hx⟩
      rw [show x = ⟨y, by simpa using And.intro (pair_compl_ne ha).2.symm (pair_compl_ne hb).2.symm⟩
        from Subtype.ext hxy] at hreach
      exact hreach
  let q := (p.map (Embedding.induce (({a, b} : Set V)ᶜ)).toHom).induce
    (({a₀, y} : Set V)ᶜ) (by
      intro x hx
      rw [SimpleGraph.Walk.support_map] at hx
      obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hx
      exact hpavoid x' hx')
  have hza_mem : za ∈ (({a₀, y} : Set V)ᶜ) := hpavoid ⟨za, hza⟩ p.start_mem_support
  have hzb_mem : zb ∈ (({a₀, y} : Set V)ᶜ) := hpavoid ⟨zb, hzb⟩ p.end_mem_support
  have haa : a ∈ (({a₀, y} : Set V)ᶜ) := ha
  have hbb : b ∈ (({a₀, y} : Set V)ᶜ) := hb
  have haedge : (G.induce (({a₀, y} : Set V)ᶜ)).Adj ⟨a, haa⟩ ⟨za, hza_mem⟩ := by
    simpa using hzaa.symm
  have hbedge : (G.induce (({a₀, y} : Set V)ᶜ)).Adj ⟨zb, hzb_mem⟩ ⟨b, hbb⟩ := by
    simpa using hzbb
  apply hcomp
  apply ConnectedComponent.eq.mpr
  exact haedge.reachable.trans (q.reachable.trans hbedge.reachable)

omit [Fintype V] in
private lemma delete_pair_component_cannot_be_closed_at_attachment
    (G : SimpleGraph V)
    {p q d s : V}
    (hconn : (G.induce ({q}ᶜ : Set V)).Connected)
    (hd : d ∈ (({p, q} : Set V)ᶜ)) (hs : s ∈ (({p, q} : Set V)ᶜ))
    (hds : (G.induce (({p, q} : Set V)ᶜ)).connectedComponentMk ⟨d, hd⟩ ≠
      (G.induce (({p, q} : Set V)ᶜ)).connectedComponentMk ⟨s, hs⟩)
    (hno : ∀ (z : V) (hz : z ∈ (({p, q} : Set V)ᶜ)),
      (G.induce (({p, q} : Set V)ᶜ)).connectedComponentMk ⟨z, hz⟩ =
        (G.induce (({p, q} : Set V)ᶜ)).connectedComponentMk ⟨d, hd⟩ →
      ¬ G.Adj z p) : False := by
  classical
  let D := (G.induce (({p, q} : Set V)ᶜ)).connectedComponentMk ⟨d, hd⟩
  let W : Set ↥({q}ᶜ : Set V) := {z | ∃ hz : z.val ∈ (({p, q} : Set V)ᶜ),
    (G.induce (({p, q} : Set V)ᶜ)).connectedComponentMk ⟨z.val, hz⟩ = D}
  have hdq : d ∈ ({q}ᶜ : Set V) := by simpa using (pair_compl_ne hd).2
  have hsq : s ∈ ({q}ᶜ : Set V) := by simpa using (pair_compl_ne hs).2
  have hdW : (⟨d, hdq⟩ : ↥({q}ᶜ : Set V)) ∈ W := ⟨hd, rfl⟩
  have hsW : (⟨s, hsq⟩ : ↥({q}ᶜ : Set V)) ∉ W := by
    rintro ⟨hs', hsD⟩
    apply hds
    exact hsD.symm
  have hclosed : ∀ z ∈ W, ∀ x, (G.induce ({q}ᶜ : Set V)).Adj z x → x ∈ W := by
    rintro z ⟨hz, hzD⟩ x hzx
    have hzxG : G.Adj z.val x.val := by simpa using hzx
    by_cases hxp : x.val = p
    · exfalso
      have hzcomp : (G.induce (({p, q} : Set V)ᶜ)).connectedComponentMk ⟨z.val, hz⟩ =
          (G.induce (({p, q} : Set V)ᶜ)).connectedComponentMk ⟨d, hd⟩ := hzD
      exact hno z.val hz hzcomp (by simpa [hxp] using hzxG)
    · have hxmem : x.val ∈ (({p, q} : Set V)ᶜ) := by
        simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hxp, x.property⟩
      refine ⟨hxmem, ?_⟩
      rw [← hzD]
      apply ConnectedComponent.eq.mpr
      exact (show (G.induce (({p, q} : Set V)ᶜ)).Adj ⟨z.val, hz⟩ ⟨x.val, hxmem⟩ by
        simpa using hzxG).reachable.symm
  obtain ⟨walk⟩ := hconn.preconnected ⟨d, hdq⟩ ⟨s, hsq⟩
  exact hsW (mem_of_walk_closed _ W hclosed walk hdW)

omit [Fintype V] in
private lemma component_of_delete_pair_contains_separator
    (G : SimpleGraph V)
    (hnocut : ∀ z, (G.induce ({z}ᶜ : Set V)).Connected)
    {a₀ y a b d : V}
    (ha : a ∈ (({a₀, y} : Set V)ᶜ)) (hb : b ∈ (({a₀, y} : Set V)ᶜ))
    (hcomp : (G.induce (({a₀, y} : Set V)ᶜ)).connectedComponentMk ⟨a, ha⟩ ≠
      (G.induce (({a₀, y} : Set V)ᶜ)).connectedComponentMk ⟨b, hb⟩)
    (hd : d ∈ (({a, b} : Set V)ᶜ)) :
    (G.induce (({a, b} : Set V)ᶜ)).connectedComponentMk ⟨d, hd⟩ =
        (G.induce (({a, b} : Set V)ᶜ)).connectedComponentMk
          ⟨a₀, by simpa using And.intro (pair_compl_ne ha).1.symm (pair_compl_ne hb).1.symm⟩ ∨
    (G.induce (({a, b} : Set V)ᶜ)).connectedComponentMk ⟨d, hd⟩ =
        (G.induce (({a, b} : Set V)ᶜ)).connectedComponentMk
          ⟨y, by simpa using And.intro (pair_compl_ne ha).2.symm (pair_compl_ne hb).2.symm⟩ := by
  classical
  by_contra h
  push Not at h
  obtain ⟨hda₀, hdy⟩ := h
  have hm := delete_pair_component_misses_an_attachment G ha hb hcomp hd hda₀ hdy
  rcases hm with hm | hm
  · -- hm: no vertex in d's component is adjacent to a
    have ha₀_mem : a₀ ∈ (({a, b} : Set V)ᶜ) := by
      simpa using And.intro (pair_compl_ne ha).1.symm (pair_compl_ne hb).1.symm
    exact delete_pair_component_cannot_be_closed_at_attachment G (hnocut b) hd ha₀_mem hda₀ hm
  · -- hm: no vertex in d's component is adjacent to b
    have hy_mem : y ∈ (({a, b} : Set V)ᶜ) := by
      simpa using And.intro (pair_compl_ne ha).2.symm (pair_compl_ne hb).2.symm
    have hcomp' : (G.induce (({a₀, y} : Set V)ᶜ)).connectedComponentMk ⟨b, hb⟩ ≠
        (G.induce (({a₀, y} : Set V)ᶜ)).connectedComponentMk ⟨a, ha⟩ := hcomp.symm
    have hd' : d ∈ (({b, a} : Set V)ᶜ) := by simpa [Set.pair_comm] using hd
    have hy' : y ∈ (({b, a} : Set V)ᶜ) := by simpa [Set.pair_comm] using hy_mem
    have hset : ({b, a} : Set V) = ({a, b} : Set V) := Set.pair_comm _ _
    have hsetc : ({b, a} : Set V)ᶜ = ({a, b} : Set V)ᶜ := hset.symm ▸ rfl
    have hsetc' : ({a, b} : Set V)ᶜ = ({b, a} : Set V)ᶜ := hsetc.symm
    let φ : G.induce ({b, a} : Set V)ᶜ →g G.induce ({a, b} : Set V)ᶜ :=
      { toFun := fun ⟨x, hx⟩ => ⟨x, hsetc'.symm ▸ hx⟩
        map_rel' := by
          intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
          exact SimpleGraph.induce_adj.mp hxy }
    let φsymm : G.induce ({a, b} : Set V)ᶜ →g G.induce ({b, a} : Set V)ᶜ :=
      { toFun := fun ⟨x, hx⟩ => ⟨x, hsetc' ▸ hx⟩
        map_rel' := by
          intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
          exact SimpleGraph.induce_adj.mp hxy }
    have heq_reach : ∀ {u v : V} {hu : u ∈ ({b, a} : Set V)ᶜ} {hv : v ∈ ({b, a} : Set V)ᶜ}
        {hu' : u ∈ ({a, b} : Set V)ᶜ} {hv' : v ∈ ({a, b} : Set V)ᶜ},
        (G.induce (({b, a} : Set V)ᶜ)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ ↔
        (G.induce (({a, b} : Set V)ᶜ)).Reachable ⟨u, hu'⟩ ⟨v, hv'⟩ := by
      intro u v hu hv hu' hv'
      constructor
      · intro ⟨w⟩
        exact ⟨w.map φ⟩
      · intro ⟨w⟩
        exact ⟨w.map φsymm⟩
    have hdy' : (G.induce (({b, a} : Set V)ᶜ)).connectedComponentMk ⟨d, hd'⟩ ≠
        (G.induce (({b, a} : Set V)ᶜ)).connectedComponentMk ⟨y, hy'⟩ := by
      intro heq
      apply hdy
      have heq_reach : (G.induce (({b, a} : Set V)ᶜ)).Reachable ⟨d, hd'⟩ ⟨y, hy'⟩ :=
        ConnectedComponent.eq.mp heq
      have heq' : (G.induce (({a, b} : Set V)ᶜ)).Reachable ⟨d, hd⟩ ⟨y, hy_mem⟩ :=
        heq_reach.elim fun w => ⟨w.map φ⟩
      exact ConnectedComponent.eq.mpr heq'
    have hm' : ∀ (z : V) (hz : z ∈ (({b, a} : Set V)ᶜ)),
        (G.induce (({b, a} : Set V)ᶜ)).connectedComponentMk ⟨z, hz⟩ =
          (G.induce (({b, a} : Set V)ᶜ)).connectedComponentMk ⟨d, hd'⟩ → ¬G.Adj z b := by
      intro z hz heq
      have hz' : z ∈ (({a, b} : Set V)ᶜ) := by simpa [Set.pair_comm] using hz
      apply hm z hz'
      have hr := ConnectedComponent.eq.mp heq
      have hr' : (G.induce (({a, b} : Set V)ᶜ)).Reachable ⟨z, hz'⟩ ⟨d, hd⟩ :=
        heq_reach.mp hr
      exact ConnectedComponent.eq.mpr hr'
    exact delete_pair_component_cannot_be_closed_at_attachment G
      (p := b) (q := a) (d := d) (s := y) (hnocut a) hd' hy' hdy' hm'

omit [Fintype V] in
/-- The prefix ending at the earlier neighbour avoids the later neighbour. -/
private lemma reachable_avoiding_later_neighbor [DecidableEq V] (G : SimpleGraph V)
    {x y a r b : V} (hxa : G.Adj x a) (hxr : G.Adj x r) (har : a ≠ r)
    (hry : r ≠ y) (hab : a ≠ b) (hrb : r ≠ b) (hxb : x ≠ b) (hyb : y ≠ b)
    (w : (G.induce ({b}ᶜ : Set V)).Walk ⟨y, hyb⟩ ⟨x, hxb⟩)
    (ham : (⟨a, hab⟩ : ↥({b}ᶜ : Set V)) ∈ w.support)
    (hrm : (⟨r, hrb⟩ : ↥({b}ᶜ : Set V)) ∈ w.support)
    (hord : (w.takeUntil ⟨a, hab⟩ ham).length < (w.takeUntil ⟨r, hrb⟩ hrm).length) :
    (G.induce (({r, b} : Set V)ᶜ)).Reachable
      ⟨x, by simp [hxr.ne, hxb]⟩ ⟨y, by simp [hry.symm, hyb]⟩ := by
  classical
  let hprefix := w.takeUntil ⟨a, hab⟩ ham
  have hprefix_avoid_r : ∀ z ∈ hprefix.support, z.val ≠ r := by
    intro z hz hzr
    have hz_eq : z = (⟨r, hrb⟩ : ↥({b}ᶜ : Set V)) := Subtype.ext hzr
    subst z
    have hle : ((w.takeUntil ⟨a, hab⟩ ham).takeUntil ⟨r, hrb⟩
        (show ⟨r, hrb⟩ ∈ (w.takeUntil ⟨a, hab⟩ ham).support by
          simpa only [hprefix] using hz)).length ≤
        (w.takeUntil ⟨a, hab⟩ ham).length :=
      SimpleGraph.Walk.length_takeUntil_le_length _ _
    rw [w.takeUntil_takeUntil ham] at hle
    exact (Nat.not_lt_of_ge hle) hord
  have hp_mem : ∀ z ∈ hprefix.support, z.val ∈ (({r, b} : Set V)ᶜ) := by
    intro z hz
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hprefix_avoid_r z hz, z.property⟩
  let pg := hprefix.map (Embedding.induce ({b}ᶜ : Set V)).toHom
  let pi := pg.induce (({r, b} : Set V)ᶜ) (by
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
    exact hp_mem z' hz')
  have hxa' : (G.induce (({r, b} : Set V)ᶜ)).Adj
      ⟨x, by simp [hxr.ne, hxb]⟩ ⟨a, by simp [har, hab]⟩ := by
    simpa using hxa
  exact hxa'.reachable.trans ⟨pi.reverse⟩

omit [Fintype V] in
private lemma parallel_neighbors_not_both_separating
    (G : SimpleGraph V)
    {x y a r b : V}
    (hconn : (G.induce ({b}ᶜ : Set V)).Connected)
    (hxa : G.Adj x a) (hxr : G.Adj x r) (har : a ≠ r)
    (hay : a ≠ y) (hry : r ≠ y)
    (hab : a ≠ b) (hrb : r ≠ b) (hxb : x ≠ b) (hyb : y ≠ b)
 :
    (G.induce (({a, b} : Set V)ᶜ)).Reachable
      ⟨x, by simp [hxa.ne, hxb]⟩ ⟨y, by simp [hay.symm, hyb]⟩ ∨
    (G.induce (({r, b} : Set V)ᶜ)).Reachable
      ⟨x, by simp [hxr.ne, hxb]⟩ ⟨y, by simp [hry.symm, hyb]⟩ := by
  classical
  let X : ↥({b}ᶜ : Set V) := ⟨x, hxb⟩
  let Y : ↥({b}ᶜ : Set V) := ⟨y, hyb⟩
  obtain ⟨w₀⟩ := hconn.preconnected Y X
  let wp := w₀.toPath
  let w : (G.induce ({b}ᶜ : Set V)).Walk Y X := wp
  let : BEq ↥({b}ᶜ : Set V) := instBEqOfDecidableEq
  have hnodup : w.support.Nodup := wp.nodup_support
  by_cases ham : (⟨a, hab⟩ : ↥({b}ᶜ : Set V)) ∈ w.support
  · by_cases hrm : (⟨r, hrb⟩ : ↥({b}ᶜ : Set V)) ∈ w.support
    · by_cases hord : w.support.idxOf ⟨a, hab⟩ < w.support.idxOf ⟨r, hrb⟩
      · right
        exact reachable_avoiding_later_neighbor G hxa hxr har hry hab hrb hxb hyb w ham hrm
          (by simpa only [w.length_takeUntil ham, w.length_takeUntil hrm] using hord)
      · left
        have hord' : w.support.idxOf ⟨r, hrb⟩ < w.support.idxOf ⟨a, hab⟩ := by
          have hne : w.support.idxOf ⟨r, hrb⟩ ≠ w.support.idxOf ⟨a, hab⟩ := by
            intro heq
            have := (List.idxOf_inj hrm).mp heq
            exact har (Subtype.ext_iff.mp this).symm
          omega
        exact reachable_avoiding_later_neighbor G hxr hxa har.symm hay hrb hab hxb hyb
          w hrm ham (by simpa only [w.length_takeUntil hrm, w.length_takeUntil ham] using hord')
    · right
      have havoidr : ∀ z ∈ w.support, z.val ∈ (({r, b} : Set V)ᶜ) := by
        intro z hz
        simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨fun hzr => by
          apply hrm
          simpa [show z = (⟨r, hrb⟩ : ↥({b}ᶜ : Set V)) from Subtype.ext hzr] using hz,
          z.property⟩
      exact ⟨(w.map (Embedding.induce ({b}ᶜ : Set V)).toHom).induce (({r, b} : Set V)ᶜ)
        (by intro z hz; rw [SimpleGraph.Walk.support_map] at hz
            obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
            exact havoidr z' hz') |>.reverse⟩
  · left
    have havida : ∀ z ∈ w.support, z.val ∈ (({a, b} : Set V)ᶜ) := by
      intro z hz
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun hza => by
        apply ham
        simpa [show z = (⟨a, hab⟩ : ↥({b}ᶜ : Set V)) from Subtype.ext hza] using hz,
        z.property⟩
    exact ⟨(w.map (Embedding.induce ({b}ᶜ : Set V)).toHom).induce (({a, b} : Set V)ᶜ)
      (by intro z hz; rw [SimpleGraph.Walk.support_map] at hz
          obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
          exact havida z' hz') |>.reverse⟩

omit [Fintype V] in
private lemma connected_delete_pair_of_separator_reachable
    (G : SimpleGraph V)
    (hnocut : ∀ z, (G.induce ({z}ᶜ : Set V)).Connected)
    {a₀ y p q : V}
    (hp : p ∈ (({a₀, y} : Set V)ᶜ)) (hq : q ∈ (({a₀, y} : Set V)ᶜ))
    (hcomp : (G.induce (({a₀, y} : Set V)ᶜ)).connectedComponentMk ⟨p, hp⟩ ≠
      (G.induce (({a₀, y} : Set V)ᶜ)).connectedComponentMk ⟨q, hq⟩)
    (hreach : (G.induce (({p, q} : Set V)ᶜ)).Reachable
      ⟨a₀, by simpa using And.intro (pair_compl_ne hp).1.symm (pair_compl_ne hq).1.symm⟩
      ⟨y, by simpa using And.intro (pair_compl_ne hp).2.symm (pair_compl_ne hq).2.symm⟩) :
    (G.induce (({p, q} : Set V)ᶜ)).Connected := by
  classical
  have : Nonempty ↥(({p, q} : Set V)ᶜ) :=
    ⟨⟨a₀, by simpa using And.intro (pair_compl_ne hp).1.symm (pair_compl_ne hq).1.symm⟩⟩
  apply SimpleGraph.Connected.mk
  intro u v
  have hu := component_of_delete_pair_contains_separator G hnocut hp hq hcomp u.property
  have hv := component_of_delete_pair_contains_separator G hnocut hp hq hcomp v.property
  rcases hu with hua | huy <;> rcases hv with hva | hvy
  · exact (ConnectedComponent.eq.mp hua).trans (ConnectedComponent.eq.mp hva).symm
  · exact ((ConnectedComponent.eq.mp hua).trans hreach).trans (ConnectedComponent.eq.mp hvy).symm
  · exact ((ConnectedComponent.eq.mp huy).trans hreach.symm).trans
      (ConnectedComponent.eq.mp hva).symm
  · exact (ConnectedComponent.eq.mp huy).trans (ConnectedComponent.eq.mp hvy).symm

omit [Fintype V] in
private lemma one_of_two_cross_pairs_connected
    (G : SimpleGraph V)
    (hnocut : ∀ z, (G.induce ({z}ᶜ : Set V)).Connected)
    {a₀ y a r b : V}
    (ha : a ∈ (({a₀, y} : Set V)ᶜ)) (hr : r ∈ (({a₀, y} : Set V)ᶜ))
    (hb : b ∈ (({a₀, y} : Set V)ᶜ)) (har_ne : a ≠ r)
    (hAa : G.Adj a₀ a) (hAr : G.Adj a₀ r) (hAb : G.Adj a₀ b)
    (hN : ∀ z, G.Adj a₀ z → z = a ∨ z = r ∨ z = b)
    (hab : (G.induce (({a₀, y} : Set V)ᶜ)).connectedComponentMk ⟨a, ha⟩ ≠
      (G.induce (({a₀, y} : Set V)ᶜ)).connectedComponentMk ⟨b, hb⟩)
    (hrbcomp : (G.induce (({a₀, y} : Set V)ᶜ)).connectedComponentMk ⟨r, hr⟩ ≠
      (G.induce (({a₀, y} : Set V)ᶜ)).connectedComponentMk ⟨b, hb⟩) :
    (G.induce (({a, b} : Set V)ᶜ)).Connected ∨
      (G.induce (({r, b} : Set V)ᶜ)).Connected := by
  classical
  have hab_ne : a ≠ b := by
    intro e
    apply hab
    subst b
    rfl
  have hrb_ne : r ≠ b := by
    intro e
    apply hrbcomp
    subst b
    rfl
  have har_ne' : a ≠ r := har_ne
  have hxb : a₀ ≠ b := hAb.ne
  have hyb : y ≠ b := (pair_compl_ne hb).2.symm
  rcases parallel_neighbors_not_both_separating G (hnocut b) hAa hAr har_ne'
      (pair_compl_ne ha).2 (pair_compl_ne hr).2 hab_ne hrb_ne hxb hyb with hreach | hreach
  · left
    exact connected_delete_pair_of_separator_reachable G hnocut ha hb hab hreach
  · right
    exact connected_delete_pair_of_separator_reachable G hnocut hr hb hrbcomp hreach

omit [Fintype V] in
private lemma component_eq_of_adj_in_induce
    (G : SimpleGraph V) {S : Set V} {x y : V}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : G.Adj x y) :
    (G.induce S).connectedComponentMk ⟨x, hx⟩ =
      (G.induce S).connectedComponentMk ⟨y, hy⟩ := by
  classical
  apply ConnectedComponent.eq.mpr
  exact (show (G.induce S).Adj ⟨x, hx⟩ ⟨y, hy⟩ by simpa using hxy).reachable

private lemma good_pair_at_separator
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a₀ y a b : V} (hdeg : G.degree a₀ = 3)
    (hnocut : ∀ z, (G.induce ({z}ᶜ : Set V)).Connected)
    (ha : a ∈ (({a₀, y} : Set V)ᶜ)) (hb : b ∈ (({a₀, y} : Set V)ᶜ))
    (hAa : G.Adj a₀ a) (hAb : G.Adj a₀ b)
    (hcomp : (G.induce (({a₀, y} : Set V)ᶜ)).connectedComponentMk ⟨a, ha⟩ ≠
      (G.induce (({a₀, y} : Set V)ᶜ)).connectedComponentMk ⟨b, hb⟩) :
    ∃ p q : V, G.Adj a₀ p ∧ G.Adj a₀ q ∧ p ≠ q ∧ ¬ G.Adj p q ∧
      (G.induce (({p, q} : Set V)ᶜ)).Connected := by
  classical
  have hcard : (G.neighborFinset a₀).card = 3 := by
    rw [G.card_neighborFinset_eq_degree, hdeg]
  have haN : a ∈ G.neighborFinset a₀ := by simpa using hAa
  have hbN : b ∈ G.neighborFinset a₀ := by simpa using hAb
  have hab_ne : a ≠ b := by
    intro e
    apply hcomp
    subst b
    rfl
  obtain ⟨r, hrN, hra, hrb, hNset⟩ : ∃ r, r ∈ G.neighborFinset a₀ ∧ r ≠ a ∧ r ≠ b ∧
      G.neighborFinset a₀ = {a, b, r} := by
    have hsub : ({a, b} : Finset V) ⊆ G.neighborFinset a₀ := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz'
      · exact haN
      · rw [Finset.mem_singleton] at hz'; subst hz'; exact hbN
    have hcard_diff : (G.neighborFinset a₀ \ {a, b}).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsub, hcard, Finset.card_pair hab_ne]
    obtain ⟨r, hr_eq⟩ := Finset.card_eq_one.mp hcard_diff
    have hrmem_diff : r ∈ G.neighborFinset a₀ \ {a, b} := by
      rw [hr_eq]; exact Finset.mem_singleton_self r
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hrmem_diff
    obtain ⟨hrN, hrab⟩ := hrmem_diff
    push Not at hrab
    refine ⟨r, hrN, hrab.1, hrab.2, ?_⟩
    have hcard_abr : ({a, b, r} : Finset V).card = 3 := by
      rw [Finset.card_insert_of_notMem (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hab_ne, fun h => hrab.1 h.symm⟩),
          Finset.card_insert_of_notMem (by
            simp only [Finset.mem_singleton]; exact fun h => hrab.2 h.symm),
          Finset.card_singleton]
    have habr_sub : ({a, b, r} : Finset V) ⊆ G.neighborFinset a₀ := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact haN
      · exact hbN
      · exact hrN
    exact (Finset.eq_of_subset_of_card_le habr_sub (by rw [hcard, hcard_abr])).symm
  have hAr : G.Adj a₀ r := by simpa using hrN
  by_cases hry_eq : r = y
  · subst r
    have hAy : G.Adj a₀ y := hAr
    have hreach : (G.induce (({a, b} : Set V)ᶜ)).Reachable
        ⟨a₀, by simpa using (And.intro (pair_compl_ne ha).1.symm
          (pair_compl_ne hb).1.symm)⟩
        ⟨y, by simpa using (And.intro (pair_compl_ne ha).2.symm
          (pair_compl_ne hb).2.symm)⟩ := by
      apply SimpleGraph.Adj.reachable
      simpa using hAy
    have hc := connected_delete_pair_of_separator_reachable G hnocut ha hb hcomp hreach
    have hnon : ¬ G.Adj a b := by
      intro e
      apply hcomp
      exact component_eq_of_adj_in_induce G ha hb e
    exact ⟨a, b, hAa, hAb, hab_ne, hnon, hc⟩
  · have hrmem : r ∈ (({a₀, y} : Set V)ᶜ) := by
      simpa using And.intro hAr.ne' hry_eq
    have hN : ∀ z, G.Adj a₀ z → z = a ∨ z = b ∨ z = r := by
      intro z hz
      have : z ∈ G.neighborFinset a₀ := by simpa using hz
      rw [hNset] at this
      simpa using this
    let Ca := (G.induce (({a₀, y} : Set V)ᶜ)).connectedComponentMk ⟨a, ha⟩
    let Cb := (G.induce (({a₀, y} : Set V)ᶜ)).connectedComponentMk ⟨b, hb⟩
    let Cr := (G.induce (({a₀, y} : Set V)ᶜ)).connectedComponentMk ⟨r, hrmem⟩
    by_cases hraComp : Ca = Cr
    · have hrb_ne_comp : Cr ≠ Cb := by
        intro h
        apply hcomp
        change Ca = Cb
        exact hraComp.trans h
      rcases one_of_two_cross_pairs_connected G hnocut ha hrmem hb hra.symm
          hAa hAr hAb (by intro z hz; rcases hN z hz with h | h | h <;> simp_all)
          hcomp hrb_ne_comp with hc | hc
      · have hnon : ¬ G.Adj a b := by
          intro e
          apply hcomp
          exact component_eq_of_adj_in_induce G ha hb e
        exact ⟨a, b, hAa, hAb, hab_ne, hnon, hc⟩
      · have hnon : ¬ G.Adj r b := by
          intro e
          apply hrb_ne_comp
          exact component_eq_of_adj_in_induce G hrmem hb e
        exact ⟨r, b, hAr, hAb, hrb, hnon, hc⟩
    · by_cases hrbComp : Cr = Cb
      · have hba : Cb ≠ Ca := by
          intro h
          exact hcomp h.symm
        have hra_ne : Cr ≠ Ca := by
          intro h
          exact hraComp h.symm
        rcases one_of_two_cross_pairs_connected G hnocut hb hrmem ha hrb.symm
            hAb hAr hAa (by intro z hz; rcases hN z hz with h | h | h <;> simp_all)
            hba hra_ne with hc | hc
        · have hnon : ¬ G.Adj b a := by
            intro e
            apply hcomp
            exact component_eq_of_adj_in_induce G ha hb e.symm
          exact ⟨b, a, hAb, hAa, hab_ne.symm, hnon, by simpa [Set.pair_comm] using hc⟩
        · have hnon : ¬ G.Adj r a := by
            intro e
            apply hraComp
            exact (component_eq_of_adj_in_induce G hrmem ha e).symm
          exact ⟨r, a, hAr, hAa, hra, hnon, hc⟩
      · have hbr : Cb ≠ Cr := fun h => hrbComp h.symm
        rcases one_of_two_cross_pairs_connected G hnocut ha hb hrmem hab_ne
            hAa hAb hAr (by intro z hz; rcases hN z hz with h | h | h <;> simp_all)
            hraComp hbr with hc | hc
        · have hnon : ¬ G.Adj a r := by
            intro e
            apply hraComp
            exact component_eq_of_adj_in_induce G ha hrmem e
          exact ⟨a, r, hAa, hAr, hra.symm, hnon, hc⟩
        · have hnon : ¬ G.Adj b r := by
            intro e
            apply hrbComp
            exact (component_eq_of_adj_in_induce G hb hrmem e).symm
          exact ⟨b, r, hAb, hAr, hrb.symm, hnon, hc⟩

/-- Lovász's endblock case: in a cubic graph with no cut vertex, if some pair `{a₀,y}`
separates the graph, an end component supplies a good triple. -/
theorem good_triple_of_two_cut
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v, G.degree v = 3)
    (hnocut : ∀ z, (G.induce ({z}ᶜ : Set V)).Connected)
    (a₀ y w : V) (hay : a₀ ≠ y) (hw : w ∉ ({a₀, y} : Set V))
    (hcut : ¬ (G.induce (({a₀, y} : Set V)ᶜ)).Connected) :
    ∃ v₀ a b : V, G.Adj v₀ a ∧ G.Adj v₀ b ∧ a ≠ b ∧ ¬ G.Adj a b ∧
      (G.induce (({a, b} : Set V)ᶜ)).Connected := by
  classical
  obtain ⟨d, e, hd, he, hde⟩ :=
    exists_unreachable_of_notConnected G ({a₀, y} : Set V) w hw hcut
  obtain ⟨a, ha, hAa, hda⟩ := a0_adj_component G hay (hnocut y) hd
  obtain ⟨b, hb, hAb, heb⟩ := a0_adj_component G hay (hnocut y) he
  have hcomp : (G.induce (({a₀, y} : Set V)ᶜ)).connectedComponentMk ⟨a, ha⟩ ≠
      (G.induce (({a₀, y} : Set V)ᶜ)).connectedComponentMk ⟨b, hb⟩ := by
    intro hab
    apply hde
    apply ConnectedComponent.eq.mp
    rw [hda, heb]
    exact hab
  obtain ⟨p, q, hAap, hAaq, hpq, hnpq, hconn'⟩ :=
    good_pair_at_separator G (hreg a₀) hnocut ha hb hAa hAb hcomp
  exact ⟨a₀, p, q, hAap, hAaq, hpq, hnpq, hconn'⟩

end BrooksSubcubic
end
