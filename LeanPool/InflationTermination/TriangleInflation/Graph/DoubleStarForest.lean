/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/
module


public import LeanPool.InflationTermination.TriangleInflation.Graph.DoubleStar

/-!
# Double-star forests carry the reconstruction data

The graph-theoretic step of the double-star reconstruction (AUDIT-NOTES A3, Theorem
`thm:doublestar` in the binary case): every double-star forest carries a `DSStruct`
(`exists_dsStruct`), and hence order-two Navascués–Wolfe feasibility characterizes
compatibility on such scenarios (`doubleStar_terminates`). Everything here is proved.
-/

@[expose] public section

namespace TriangleInflation.Graph

open Finset TriangleInflation

variable {Γ : PairGraph} {t : ℕ}

/-! ## The graph-theoretic input

The one step of AUDIT-NOTES A3 that the audited library leaves open: a double-star forest
carries the combinatorial data of a `DSStruct`.  Each component is a tree of diameter at most
three with at least two vertices, so its vertices of degree at least two are pairwise adjacent
(otherwise two private neighbours are at distance at least four) and there are at most two of
them (three would close a triangle).  Take those as the two centres when there are two; when
there is one, promote one of its neighbours to the second centre; when there is none, the
component is a single source and both of its ends are centres.  Every remaining vertex has
degree one and is joined to one of the two centres.

`DSStructAux` carries that argument: `DSStructAux.exists_centre` is the combinatorial statement
for one component, `DSStructAux.CentreData` packages the choice of centres for every component,
and `DSStructAux.CentreData.toDSStruct` reads the fields of a `DSStruct` off it. -/

namespace DSStructAux


variable {V : Type*} {G : SimpleGraph V}

/-- A vertex with two distinct neighbours. -/
def Big (G : SimpleGraph V) (v : V) : Prop := ∃ x y, G.Adj v x ∧ G.Adj v y ∧ x ≠ y

/-- In a forest, a vertex has at most one neighbour closer to a given vertex. -/
theorem down_unique (hac : G.IsAcyclic) {z u n n' : V} (hr : G.Reachable z u)
    (h1 : G.Adj u n) (h2 : G.Adj u n') (hd1 : G.dist z u = G.dist z n + 1)
    (hd2 : G.dist z u = G.dist z n' + 1) : n = n' := by
  classical
  obtain ⟨p, hp, hplen⟩ := hr.exists_path_of_dist
  have key : ∀ m, G.Adj u m → G.dist z u = G.dist z m + 1 → m = p.penultimate := by
    intro m hm hdm
    obtain ⟨q, hq, hqlen⟩ := (hr.trans hm.reachable).exists_path_of_dist
    have hu : u ∉ q.support := by
      intro huq
      have h₁ := SimpleGraph.dist_le (q.takeUntil u huq)
      have h₂ := q.length_takeUntil_le_length huq
      omega
    exact hac.eq_penultimate_of_adj_end hp hm
      (hac.mem_support_of_ne_mem_support_of_adj_of_isPath hp hq hm hu)
  rw [key n h1 hd1, key n' h2 hd2]

/-- A vertex with two neighbours has one strictly farther from any given vertex. -/
theorem exists_up (hac : G.IsAcyclic) {z u : V} (hu : Big G u) (hr : G.Reachable z u) :
    ∃ x, G.Adj u x ∧ G.dist z x = G.dist z u + 1 := by
  obtain ⟨n, n', h1, h2, hne⟩ := hu
  rcases hac.dist_eq_dist_add_one_of_adj_of_reachable z h1 hr with hA | hA
  · rcases hac.dist_eq_dist_add_one_of_adj_of_reachable z h2 hr with hB | hB
    · exact absurd (down_unique hac hr h1 h2 hA hB) hne
    · exact ⟨n', h2, hB⟩
  · exact ⟨n, h1, hA⟩

/-- Two vertices of degree at least two in a double-star forest are at distance at most one. -/
theorem dist_le_one_of_big (hac : G.IsAcyclic)
    (hdiam : ∀ u v : V, G.Reachable u v → G.dist u v ≤ 3) {u v : V}
    (hu : Big G u) (hv : Big G v) (huv : G.Reachable u v) : G.dist u v ≤ 1 := by
  obtain ⟨x, hux, hx⟩ := exists_up hac hu huv.symm
  have hrvx : G.Reachable v x := huv.symm.trans hux.reachable
  obtain ⟨y, hvy, hy⟩ := exists_up (z := x) hac hv hrvx.symm
  have hxy : G.dist x y ≤ 3 := hdiam _ _ (hrvx.symm.trans hvy.reachable)
  have e1 : G.dist x v = G.dist v x := SimpleGraph.dist_comm
  have e2 : G.dist v u = G.dist u v := SimpleGraph.dist_comm
  omega

/-- A forest has no triangle. -/
theorem no_triangle (hac : G.IsAcyclic) {a b c : V} (hab : G.Adj a b) (hac' : G.Adj a c)
    (hbc : G.Adj b c) : False := by
  have h1 : G.dist a b = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hab
  have h2 : G.dist a c = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hac'
  exact hac.dist_ne_of_adj hbc hab.reachable (h1.trans h2.symm)

/-- Two distinct vertices of degree at least two in a double-star forest are adjacent. -/
theorem adj_of_big (hac : G.IsAcyclic) (hdiam : ∀ u v : V, G.Reachable u v → G.dist u v ≤ 3)
    {u v : V} (hu : Big G u) (hv : Big G v) (huv : G.Reachable u v) (hne : u ≠ v) : G.Adj u v := by
  have h := dist_le_one_of_big hac hdiam hu hv huv
  have h0 : G.dist u v ≠ 0 := by
    intro h0
    rcases SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp h0 with h' | h'
    · exact hne h'
    · exact h' huv
  exact SimpleGraph.dist_eq_one_iff_adj.mp (by omega)

/-- The neighbour of a degree-one vertex is either the base point or has degree at least
two. -/
theorem nbr_eq_or_big {a u c : V} (hau : G.Reachable u a) (hne : u ≠ a)
    (huniq : ∀ x, G.Adj u x → x = c) : c = a ∨ Big G c := by
  obtain ⟨p, hp, hplen⟩ := hau.exists_path_of_dist
  have hd0 : G.dist u a ≠ 0 := by
    intro h0
    rcases SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp h0 with h' | h'
    · exact hne h'
    · exact h' hau
  have hlen : 1 ≤ p.length := by omega
  have hc1 : c = p.getVert 1 := by
    refine (huniq _ ?_).symm
    have := p.adj_getVert_succ (i := 0) (by omega)
    simpa using this
  rcases Nat.lt_or_ge 1 p.length with hlt | hge
  · refine Or.inr ⟨u, p.getVert 2, ?_, ?_, ?_⟩
    · rw [hc1]
      exact (by simpa using p.adj_getVert_succ (i := 0) (by omega) : G.Adj u (p.getVert 1)).symm
    · rw [hc1]; exact p.adj_getVert_succ (i := 1) hlt
    · intro h
      have h0 : p.getVert 0 = u := by simp
      have := hp.getVert_injOn (x₁ := 0) (x₂ := 2) (by simp only [Set.mem_ofPred_eq]; omega)
        (by simp only [Set.mem_ofPred_eq]; omega) (h0.trans h)
      omega
  · left
    have : p.length = 1 := by omega
    rw [hc1, ← this]
    simp

/-- A vertex that is not `Big` has exactly one neighbour. -/
theorem exists_unique_nbr (hiso : ∀ v : V, ∃ w, G.Adj v w) {u : V} (hu : ¬ Big G u) :
    ∃ c, G.Adj u c ∧ ∀ x, G.Adj u x → x = c := by
  obtain ⟨c, hc⟩ := hiso u
  refine ⟨c, hc, fun x hx => ?_⟩
  by_contra hxc
  exact hu ⟨x, c, hx, hc, hxc⟩

/-- **The combinatorics of a double-star forest.**  Every component of a double-star forest
without isolated vertices has two adjacent centres, and every other vertex of the component has
exactly one neighbour, which is one of the two centres. -/
theorem exists_centre (hac : G.IsAcyclic) (hdiam : ∀ u v : V, G.Reachable u v → G.dist u v ≤ 3)
    (hiso : ∀ v : V, ∃ w, G.Adj v w) (r : V) :
    ∃ ab : V × V, G.Adj ab.1 ab.2 ∧ G.Reachable r ab.1 ∧
      ∀ u, G.Reachable r u → u = ab.1 ∨ u = ab.2 ∨
        ∃ c, (c = ab.1 ∨ c = ab.2) ∧ G.Adj u c ∧ ∀ x, G.Adj u x → x = c := by
  classical
  by_cases hbig : ∃ a, Big G a ∧ G.Reachable r a
  · obtain ⟨a, ha, hra⟩ := hbig
    by_cases hbig2 : ∃ b, Big G b ∧ G.Reachable r b ∧ b ≠ a
    · obtain ⟨b, hb, hrb, hba⟩ := hbig2
      have hab : G.Adj a b := adj_of_big hac hdiam ha hb (hra.symm.trans hrb) (Ne.symm hba)
      refine ⟨(a, b), hab, hra, ?_⟩
      intro u hru
      by_cases hua : u = a
      · exact Or.inl hua
      by_cases hub : u = b
      · exact Or.inr (Or.inl hub)
      refine Or.inr (Or.inr ?_)
      have hnb : ¬ Big G u := fun hu =>
        no_triangle hac (adj_of_big hac hdiam hu ha (hru.symm.trans hra) hua)
          (adj_of_big hac hdiam hu hb (hru.symm.trans hrb) hub) hab
      obtain ⟨c, hc, huniq⟩ := exists_unique_nbr hiso hnb
      refine ⟨c, ?_, hc, huniq⟩
      rcases nbr_eq_or_big (hru.symm.trans hra) hua huniq with h | h
      · exact Or.inl h
      · by_cases hca : c = a
        · exact Or.inl hca
        by_cases hcb : c = b
        · exact Or.inr hcb
        have hrc : G.Reachable r c := hru.trans hc.reachable
        exact absurd (adj_of_big hac hdiam h ha (hrc.symm.trans hra) hca)
          (fun hca' => no_triangle hac hca'
            (adj_of_big hac hdiam h hb (hrc.symm.trans hrb) hcb) hab)
    · have hbig2' : ∀ x, Big G x → G.Reachable r x → x = a := by
        intro x hx hrx
        by_contra hxa
        exact hbig2 ⟨x, hx, hrx, hxa⟩
      obtain ⟨b, hab⟩ := hiso a
      refine ⟨(a, b), hab, hra, ?_⟩
      intro u hru
      by_cases hua : u = a
      · exact Or.inl hua
      by_cases hub : u = b
      · exact Or.inr (Or.inl hub)
      refine Or.inr (Or.inr ?_)
      have hnb : ¬ Big G u := fun hu => hua (hbig2' u hu hru)
      obtain ⟨c, hc, huniq⟩ := exists_unique_nbr hiso hnb
      refine ⟨c, ?_, hc, huniq⟩
      rcases nbr_eq_or_big (hru.symm.trans hra) hua huniq with h | h
      · exact Or.inl h
      · exact Or.inl (hbig2' c h (hru.trans hc.reachable))
  · obtain ⟨b, hrb⟩ := hiso r
    refine ⟨(r, b), hrb, SimpleGraph.Reachable.refl r, ?_⟩
    intro u hru
    by_cases hur : u = r
    · exact Or.inl hur
    by_cases hub : u = b
    · exact Or.inr (Or.inl hub)
    refine Or.inr (Or.inr ?_)
    have hnb : ¬ Big G u := fun hu => hbig ⟨u, hu, hru⟩
    obtain ⟨c, hc, huniq⟩ := exists_unique_nbr hiso hnb
    refine ⟨c, Or.inl ?_, hc, huniq⟩
    rcases nbr_eq_or_big hru.symm hur huniq with h | h
    · exact h
    · exact absurd (hru.trans hc.reachable) (fun hrc => hbig ⟨c, h, hrc⟩)



/-! ### Incidence -/

theorem mem_inc_iff {Γ : PairGraph} (v : Γ.V) (e : Γ.Edge) :
    e ∈ Γ.inc v ↔ v ∈ (e.1 : Sym2 Γ.V) := by
  simp [PairGraph.inc]

theorem edge_adj {Γ : PairGraph} {e : Γ.Edge} {p q : Γ.V} (h : e.1 = s(p, q)) : Γ.G.Adj p q := by
  have h2 := e.2
  rw [h] at h2
  simpa using h2

theorem reach_of_mem_edge {Γ : PairGraph} {e : Γ.Edge} {v v' : Γ.V}
    (h : v ∈ (e.1 : Sym2 Γ.V)) (h' : v' ∈ (e.1 : Sym2 Γ.V)) : Γ.G.Reachable v v' := by
  obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.mp h
  have hadj : Γ.G.Adj v w := edge_adj hw
  rw [hw, Sym2.mem_iff] at h'
  rcases h' with h' | h'
  · subst h'; exact SimpleGraph.Reachable.refl _
  · subst h'; exact hadj.reachable

/-! ### Centre data -/

/-- The two centres of the component of each vertex of a double-star forest. -/
structure CentreData (Γ : PairGraph) where
  /-- The first centre of the component. -/
  A : Γ.V → Γ.V
  /-- The second centre of the component. -/
  B : Γ.V → Γ.V
  adj : ∀ v, Γ.G.Adj (A v) (B v)
  reachA : ∀ v, Γ.G.Reachable v (A v)
  constA : ∀ u v, Γ.G.Reachable u v → A u = A v
  constB : ∀ u v, Γ.G.Reachable u v → B u = B v
  cover : ∀ v, v = A v ∨ v = B v ∨
    ∃ c, (c = A v ∨ c = B v) ∧ Γ.G.Adj v c ∧ ∀ x, Γ.G.Adj v x → x = c

/-- A chosen representative of the component of a vertex. -/
noncomputable def compRep (Γ : PairGraph) (v : Γ.V) : Γ.V :=
  (Γ.G.connectedComponentMk v).nonempty_supp.some

theorem reachable_compRep (Γ : PairGraph) (v : Γ.V) : Γ.G.Reachable v (compRep Γ v) := by
  have h := (Γ.G.connectedComponentMk v).nonempty_supp.some_mem
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at h
  exact (SimpleGraph.ConnectedComponent.eq.mp h).symm

theorem compRep_eq (Γ : PairGraph) {u v : Γ.V} (h : Γ.G.Reachable u v) :
    compRep Γ u = compRep Γ v :=
  congrArg (fun C : Γ.G.ConnectedComponent => C.nonempty_supp.some)
    (SimpleGraph.ConnectedComponent.sound h)

theorem exists_centreData (Γ : PairGraph) (hG : IsDoubleStarForest Γ.G) :
    Nonempty (CentreData Γ) := by
  classical
  obtain ⟨hac, hdiam⟩ := hG
  choose P hPadj hPreach hPcover using
    fun r : Γ.V => exists_centre hac hdiam Γ.no_isolated r
  exact ⟨{ A := fun v => (P (compRep Γ v)).1
           B := fun v => (P (compRep Γ v)).2
           adj := fun v => hPadj _
           reachA := fun v => (reachable_compRep Γ v).trans (hPreach _)
           constA := fun u v huv => by rw [compRep_eq Γ huv]
           constB := fun u v huv => by rw [compRep_eq Γ huv]
           cover := fun v => hPcover _ v (reachable_compRep Γ v).symm }⟩

namespace CentreData

variable {Γ : PairGraph} (C : CentreData Γ)

theorem reachB (v : Γ.V) : Γ.G.Reachable v (C.B v) := (C.reachA v).trans (C.adj v).reachable

theorem A_ne_B (v : Γ.V) : C.A v ≠ C.B v := (C.adj v).ne

theorem A_A (v : Γ.V) : C.A (C.A v) = C.A v := (C.constA v (C.A v) (C.reachA v)).symm

theorem B_A (v : Γ.V) : C.B (C.A v) = C.B v := (C.constB v (C.A v) (C.reachA v)).symm

theorem A_B (v : Γ.V) : C.A (C.B v) = C.A v := (C.constA v (C.B v) (C.reachB v)).symm

theorem B_B (v : Γ.V) : C.B (C.B v) = C.B v := (C.constB v (C.B v) (C.reachB v)).symm

/-- The mate of a vertex: the partner centre of a centre, the centre of a leaf. -/
def mate (v : Γ.V) : Γ.V :=
  if v = C.A v then C.B v else if v = C.B v then C.A v else
    if Γ.G.Adj v (C.A v) then C.A v else C.B v

theorem mate_ctrA (v : Γ.V) : C.mate (C.A v) = C.B v := by
  rw [mate, ite_eq_left (C.A_A v).symm, B_A]

theorem mate_ctrB (v : Γ.V) : C.mate (C.B v) = C.A v := by
  rw [mate, ite_eq_right, ite_eq_left (C.B_B v).symm, A_B]
  rw [A_B]
  exact fun h => C.A_ne_B v h.symm

theorem mate_of_leaf {v : Γ.V} (h1 : v ≠ C.A v) (h2 : v ≠ C.B v) :
    Γ.G.Adj v (C.mate v) ∧ (C.mate v = C.A v ∨ C.mate v = C.B v) ∧
      ∀ x, Γ.G.Adj v x → x = C.mate v := by
  rcases C.cover v with h | h | ⟨c, hcAB, hadj, huniq⟩
  · exact absurd h h1
  · exact absurd h h2
  · have hm : C.mate v = c := by
      rw [mate, ite_eq_right h1, ite_eq_right h2]
      by_cases h3 : Γ.G.Adj v (C.A v)
      · rw [ite_eq_left h3]
        exact huniq _ h3
      · rw [ite_eq_right h3]
        rcases hcAB with hc | hc
        · exact absurd (hc ▸ hadj) h3
        · exact hc.symm
    rw [hm]
    exact ⟨hadj, hcAB, huniq⟩

theorem mate_adj (v : Γ.V) : Γ.G.Adj v (C.mate v) := by
  by_cases h1 : v = C.A v
  · rw [h1, mate_ctrA, ← h1]
    have := C.adj v
    rw [← h1] at this
    exact this
  by_cases h2 : v = C.B v
  · rw [h2, mate_ctrB, ← h2]
    have := C.adj v
    rw [← h2] at this
    exact this.symm
  exact (C.mate_of_leaf h1 h2).1

theorem mate_mem (v : Γ.V) : C.mate v = C.A v ∨ C.mate v = C.B v := by
  by_cases h1 : v = C.A v
  · right; rw [h1, mate_ctrA, B_A]
  by_cases h2 : v = C.B v
  · left; rw [h2, mate_ctrB, A_B]
  exact (C.mate_of_leaf h1 h2).2.1

theorem mate_uniq {v : Γ.V} (h1 : v ≠ C.A v) (h2 : v ≠ C.B v) :
    ∀ x, Γ.G.Adj v x → x = C.mate v := (C.mate_of_leaf h1 h2).2.2

theorem A_mate (v : Γ.V) : C.A (C.mate v) = C.A v :=
  (C.constA v (C.mate v) (C.mate_adj v).reachable).symm

theorem B_mate (v : Γ.V) : C.B (C.mate v) = C.B v :=
  (C.constB v (C.mate v) (C.mate_adj v).reachable).symm

theorem mate_mate {v : Γ.V} (h : v = C.A v ∨ v = C.B v) : C.mate (C.mate v) = v := by
  rcases h with h | h
  · have hm : C.mate v = C.B v := by rw [mate, ite_eq_left h]
    rw [hm, C.mate_ctrB v, ← h]
  · have h1 : v ≠ C.A v := fun h1 => C.A_ne_B v (by rw [← h1, ← h])
    have hm : C.mate v = C.A v := by rw [mate, ite_eq_right h1, ite_eq_left h]
    rw [hm, C.mate_ctrA v, ← h]

/-- The edge that carries a vertex: its unique source when it is a leaf, the centre source of
its component when it is a centre. -/
def edgeAt (v : Γ.V) : Γ.Edge :=
  ⟨s(v, C.mate v), by simpa using C.mate_adj v⟩

/-- The centre source of the component of a vertex. -/
def root (v : Γ.V) : Γ.Edge := ⟨s(C.A v, C.B v), by simpa using C.adj v⟩

/-- Is the vertex a leaf? -/
def leafB (v : Γ.V) : Bool := decide (v ≠ C.A v ∧ v ≠ C.B v)

theorem leafB_true {v : Γ.V} : C.leafB v = true ↔ v ≠ C.A v ∧ v ≠ C.B v := by
  simp [leafB]

theorem leafB_false {v : Γ.V} : C.leafB v = false ↔ (v = C.A v ∨ v = C.B v) := by
  simp only [leafB, decide_eq_false_iff_not, not_and_or, not_not]

theorem edgeAt_val (v : Γ.V) : (C.edgeAt v).1 = s(v, C.mate v) := rfl

theorem edgeAt_inc (v : Γ.V) : C.edgeAt v ∈ Γ.inc v := by
  rw [mem_inc_iff, edgeAt_val]
  simp

theorem edgeAt_inc_mate (v : Γ.V) : C.edgeAt v ∈ Γ.inc (C.mate v) := by
  rw [mem_inc_iff, edgeAt_val]
  simp

theorem edgeAt_mem (v u : Γ.V) (h : C.edgeAt v ∈ Γ.inc u) : u = v ∨ u = C.mate v := by
  rw [mem_inc_iff, edgeAt_val, Sym2.mem_iff] at h
  exact h

theorem mate_not_leaf (v : Γ.V) : C.leafB (C.mate v) = false := by
  rw [leafB_false]
  rcases C.mate_mem v with h | h
  · exact Or.inl (by rw [A_mate, h])
  · exact Or.inr (by rw [B_mate, h])

theorem mate_ne (v : Γ.V) : C.mate v ≠ v := (C.mate_adj v).ne'

theorem leaf_inc {v : Γ.V} (h : C.leafB v = true) : Γ.inc v = {C.edgeAt v} := by
  obtain ⟨h1, h2⟩ := C.leafB_true.mp h
  ext e
  rw [mem_inc_iff, Finset.mem_singleton]
  constructor
  · intro hv
    obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.mp hv
    have hadj : Γ.G.Adj v w := edge_adj hw
    have hwm : w = C.mate v := C.mate_uniq h1 h2 w hadj
    apply Subtype.ext
    rw [hw, hwm, edgeAt_val]
  · intro he
    rw [he, edgeAt_val]
    simp

theorem edgeAt_eq_iff (u v : Γ.V) :
    C.edgeAt u = C.edgeAt v ↔ (u = v ∧ C.mate u = C.mate v) ∨ (u = C.mate v ∧ C.mate u = v) := by
  rw [Subtype.ext_iff, edgeAt_val, edgeAt_val, Sym2.eq_iff]

theorem fib_leaf {v : Γ.V} (h : C.leafB v = true) :
    (Finset.univ.filter fun u => C.edgeAt u = C.edgeAt v) = {v} := by
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hu
    rcases (C.edgeAt_eq_iff u v).mp hu with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact h1
    · exfalso
      have hm := C.mate_not_leaf u
      rw [h2, h] at hm
      exact Bool.noConfusion hm
  · intro hu
    rw [hu]

theorem fib_ctr {v : Γ.V} (h : C.leafB v = false) :
    (Finset.univ.filter fun u => C.edgeAt u = C.edgeAt v) = {v, C.mate v} := by
  have hc := C.leafB_false.mp h
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro hu
    rcases (C.edgeAt_eq_iff u v).mp hu with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inl h1
    · exact Or.inr h1
  · intro hu
    rcases hu with hu | hu
    · rw [hu]
    · rw [hu]
      exact (C.edgeAt_eq_iff _ _).mpr (Or.inr ⟨rfl, C.mate_mate hc⟩)

theorem root_leaf {v : Γ.V} (_h : C.leafB v = true) : C.root v = C.edgeAt (C.mate v) := by
  apply Subtype.ext
  rw [edgeAt_val]
  change s(C.A v, C.B v) = s(C.mate v, C.mate (C.mate v))
  rcases C.mate_mem v with hm | hm
  · rw [hm, C.mate_ctrA v]
  · rw [hm, C.mate_ctrB v, Sym2.eq_swap]

theorem root_ctr {v : Γ.V} (h : C.leafB v = false) : C.root v = C.edgeAt v := by
  apply Subtype.ext
  rw [edgeAt_val]
  change s(C.A v, C.B v) = s(v, C.mate v)
  rcases C.leafB_false.mp h with hv | hv
  · have hm : C.mate v = C.B v := by rw [mate, ite_eq_left hv]
    rw [hm, ← hv]
  · have h1 : v ≠ C.A v := fun h1 => C.A_ne_B v (by rw [← h1, ← hv])
    have hm : C.mate v = C.A v := by rw [mate, ite_eq_right h1, ite_eq_left hv]
    rw [hm, ← hv, Sym2.eq_swap]

theorem root_eq_of_reach {u v : Γ.V} (h : Γ.G.Reachable u v) : C.root u = C.root v := by
  apply Subtype.ext
  change s(C.A u, C.B u) = s(C.A v, C.B v)
  rw [C.constA u v h, C.constB u v h]

theorem comp_sourceDisjoint (y y' : Γ.Edge) (hy : y ≠ y') :
    Disjoint ((Finset.univ.filter fun v => C.root v = y).biUnion Γ.inc)
      ((Finset.univ.filter fun v => C.root v = y').biUnion Γ.inc) := by
  rw [Finset.disjoint_left]
  intro e he he'
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at he he'
  obtain ⟨v, hv, hev⟩ := he
  obtain ⟨v', hv', hev'⟩ := he'
  rw [mem_inc_iff] at hev hev'
  exact hy (hv ▸ hv' ▸ C.root_eq_of_reach (reach_of_mem_edge hev hev'))

theorem edgeAt_surj (e : Γ.Edge) : ∃ v, C.edgeAt v = e := by
  obtain ⟨z, hz⟩ := e
  induction z using Sym2.ind with
  | _ p q =>
    have hadj : Γ.G.Adj p q := by simpa using hz
    have key : C.mate p = q ∨ C.mate q = p := by
      by_cases hp : p = C.A p ∨ p = C.B p
      · by_cases hq : q = C.A q ∨ q = C.B q
        · -- both are centres of the same component
          left
          have hA : C.A q = C.A p := (C.constA p q hadj.reachable).symm
          have hB : C.B q = C.B p := (C.constB p q hadj.reachable).symm
          rcases hp with hp | hp
          · have hqB : q = C.B p := by
              rcases hq with hq | hq
              · exact absurd (hq.trans (hA.trans hp.symm)) hadj.ne'
              · rw [hq, hB]
            rw [mate, ite_eq_left hp, hqB]
          · have hp1 : p ≠ C.A p := fun h1 => C.A_ne_B p (by rw [← h1, ← hp])
            have hqA : q = C.A p := by
              rcases hq with hq | hq
              · rw [hq, hA]
              · exact absurd (hq.trans (hB.trans hp.symm)) hadj.ne'
            rw [mate, ite_eq_right hp1, ite_eq_left hp, hqA]
        · rw [not_or] at hq
          exact Or.inr (C.mate_uniq hq.1 hq.2 p hadj.symm).symm
      · rw [not_or] at hp
        exact Or.inl (C.mate_uniq hp.1 hp.2 q hadj).symm
    rcases key with hk | hk
    · exact ⟨p, Subtype.ext (by rw [edgeAt_val, hk])⟩
    · exact ⟨q, Subtype.ext (by rw [edgeAt_val, hk, Sym2.eq_swap])⟩

/-- The combinatorial data of a double-star forest carried by its centre data. -/
noncomputable def toDSStruct : DSStruct Γ where
  leaf := C.leafB
  edgeAt := C.edgeAt
  mate := C.mate
  root := C.root
  vtx := fun e => Classical.choose (C.edgeAt_surj e)
  vtx_edgeAt := fun e => Classical.choose_spec (C.edgeAt_surj e)
  edgeAt_inc := C.edgeAt_inc
  edgeAt_inc_mate := C.edgeAt_inc_mate
  edgeAt_mem := C.edgeAt_mem
  mate_not_leaf := C.mate_not_leaf
  mate_ne := C.mate_ne
  leaf_inc := fun _ h => C.leaf_inc h
  fib_leaf := fun _ h => C.fib_leaf h
  fib_ctr := fun _ h => C.fib_ctr h
  root_leaf := fun _ h => C.root_leaf h
  root_ctr := fun _ h => C.root_ctr h
  comp_sourceDisjoint := C.comp_sourceDisjoint

end CentreData

end DSStructAux

/-- Every double-star forest carries a `DSStruct`. -/
theorem exists_dsStruct (Γ : PairGraph) (hG : IsDoubleStarForest Γ.G) :
    Nonempty (DSStruct Γ) := by
  obtain ⟨C⟩ := DSStructAux.exists_centreData Γ hG
  exact ⟨C.toDSStruct⟩

/-! ## The double-star reconstruction -/

/-- AUDIT-NOTES A3, the double-star reconstruction, in the binary case where the alphabet
bound is `T = 2`. For a scenario whose components are all double stars, order-two
Navascués–Wolfe feasibility already characterizes compatibility. The proof reconstructs a
model: source-disjoint independence at order two makes the leaves independent, conditioning
on the event that each leaf's two copies list both symbols gives the joint conditional law of
the two centres, and that law is the source law of a fresh central source carrying the pair
of response tables. -/
theorem doubleStar_terminates (Γ : PairGraph) (hG : IsDoubleStarForest Γ.G) (P : GTarget Γ)
    (hP : IsLaw P) : GNWFeasible Γ 2 P ↔ GCompatible Γ P := by
  constructor
  · rintro ⟨Δ, hΔ, hsym, hdiag⟩
    obtain ⟨D⟩ := exists_dsStruct Γ hG
    exact D.gCompatible_of_dsStruct hP hΔ hsym hdiag
  · exact compatible_gNWFeasible Γ 2 P

end TriangleInflation.Graph
