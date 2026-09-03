/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/

import LeanPool.IsoGraph.Canon.Equivariance

/-!
# The search tree, and what the search is looking for

`IsoGraph.Canon.Equivariance` proves that the *ingredients* of the search — refinement,
individualisation, the certificate — are equivariant, and that every leaf the search records is
an honest one.  This file is about the search *tree*:

* `lexCmpU64` is shown to be `compare` on `List UInt64`, which hands us a linear order (Std's
  `OrientedOrd`/`TransOrd`/`LawfulEqOrd` instances) for free.
* `Reach` describes the leaves of the *unpruned* tree, and `key` the quantity the search
  maximises: the pair (node-invariant path, certificate), encoded as a `List (List UInt64)` so
  that lexicographic `compare` on it is the comparison `leafUpdate` performs.
* `reach_transfer` transports leaves along a renaming, and `bestKey_transfer` concludes that the
  *specification* — "the largest key of any leaf" — is an isomorphism invariant.

The bridge from the algorithm to the specification — that the search's winner really is the
largest key, i.e. that none of the three pruning rules ever discards it — is `dfsNode_dom` of
`IsoGraph/Canon/Optimal.lean`; the two are joined in `IsoGraph/Canon/Correct.lean`.
-/


namespace IsoGraph
namespace Canon

open Std

/-! ## The comparison used to pick the winner

`lexCmpU64` is `compare` on the underlying lists, so it is a linear order: antisymmetric
(`LawfulEqCmp`), total (`OrientedCmp`) and transitive (`TransCmp`). -/

theorem lexCmpFrom_eq_compare (a b : Array UInt64) : ∀ (fuel i : Nat),
    i + fuel = min a.size b.size →
    lexCmpFrom a b fuel i = compare (a.toList.drop i) (b.toList.drop i)
  | 0, i, h => by
    rw [lexCmpFrom]
    rcases Nat.lt_or_ge a.size b.size with hab | hab
    · have h1 : a.toList.drop i = [] := by
        rw [List.drop_eq_nil_iff]; simp only [Array.length_toList]; omega
      have h2 : (b.toList.drop i) ≠ [] := by
        rw [Ne, List.drop_eq_nil_iff]; simp only [Array.length_toList]; omega
      cases hb : b.toList.drop i with
      | nil => exact absurd hb h2
      | cons x xs => rw [h1, List.compare_nil_cons]; exact Nat.compare_eq_lt.2 hab
    · rcases Nat.eq_or_lt_of_le hab with hab' | hab'
      · have h1 : a.toList.drop i = [] := by
          rw [List.drop_eq_nil_iff]; simp only [Array.length_toList]; omega
        have h2 : b.toList.drop i = [] := by
          rw [List.drop_eq_nil_iff]; simp only [Array.length_toList]; omega
        rw [h1, h2, List.compare_nil_nil, hab']
        simp
      · have h1 : b.toList.drop i = [] := by
          rw [List.drop_eq_nil_iff]; simp only [Array.length_toList]; omega
        have h2 : (a.toList.drop i) ≠ [] := by
          rw [Ne, List.drop_eq_nil_iff]; simp only [Array.length_toList]; omega
        cases ha : a.toList.drop i with
        | nil => exact absurd ha h2
        | cons x xs =>
          rw [h1, List.compare_cons_nil]
          exact Nat.compare_eq_gt.2 hab'
  | fuel + 1, i, h => by
    rw [lexCmpFrom, ite_eq_left (by omega)]
    have hia : i < a.size := by omega
    have hib : i < b.size := by omega
    have hda : a.toList.drop i = a[i]! :: a.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hia), getElem!_pos a i hia]
      simp
    have hdb : b.toList.drop i = b[i]! :: b.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hib), getElem!_pos b i hib]
      simp
    rw [hda, hdb, List.compare_cons_cons]
    cases hc : compare a[i]! b[i]! with
    | eq => rw [Ordering.then, lexCmpFrom_eq_compare a b fuel (i + 1) (by omega)]
    | lt => rfl
    | gt => rfl

/-- The search's comparison is `compare` on the underlying lists. -/
theorem lexCmpU64_eq_compare (a b : Array UInt64) :
    lexCmpU64 a b = compare a.toList b.toList := by
  have h := lexCmpFrom_eq_compare a b (min a.size b.size) 0 (by omega)
  rw [lexCmpU64]
  simpa using h

theorem lexCmpU64_eq_iff {a b : Array UInt64} : lexCmpU64 a b = .eq ↔ a = b := by
  rw [lexCmpU64_eq_compare]
  constructor
  · intro h
    exact Array.toList_inj.1 (LawfulEqCmp.eq_of_compare h)
  · rintro rfl
    exact compare_self

theorem lexCmpU64_refl (a : Array UInt64) : lexCmpU64 a a = .eq :=
  lexCmpU64_eq_iff.2 rfl

/-- The key a leaf is judged by: its node-invariant path first, its certificate second.  Packing
the two as a `List (List UInt64)` makes lexicographic `compare` on the pair — exactly the
comparison `leafUpdate` performs — available with all of Std's order lemmas. -/
def leafKey (invPath cert : Array UInt64) : List (List UInt64) := [invPath.toList, cert.toList]

/-- `compare` on keys is the two-stage comparison of `leafUpdate`. -/
theorem compare_leafKey (i c i' c' : Array UInt64) :
    compare (leafKey i c) (leafKey i' c')
      = match lexCmpU64 i i' with
        | .eq => lexCmpU64 c c'
        | o => o := by
  rw [leafKey, leafKey, List.compare_cons_cons, List.compare_cons_cons, List.compare_nil_nil,
    ← lexCmpU64_eq_compare, ← lexCmpU64_eq_compare]
  cases lexCmpU64 i i' <;> cases lexCmpU64 c c' <;> rfl

theorem leafKey_inj {i c i' c' : Array UInt64} (h : leafKey i c = leafKey i' c') :
    i = i' ∧ c = c' := by
  rw [leafKey, leafKey, List.cons.injEq, List.cons.injEq] at h
  exact ⟨Array.toList_inj.1 h.1, Array.toList_inj.1 h.2.1⟩

/-! ## The search tree

`Reach n f invPath p k` says that the tree rooted at the refined partition `p` — the *unpruned*
tree, in which every vertex of the target cell is individualised in turn — has a leaf with key
`k`.  This is the search's specification: `canonical` is supposed to return the largest such key
(`BestKey`), and that is manifestly an isomorphism invariant (`bestKey_transfer`). -/

/-- The child of `p` obtained by individualising `v` and re-refining, with the trace of the
refinement.  This is exactly the step `dfsChildren` takes. -/
def child (G : Graph) (p : Part) (v : Nat) : Part × UInt64 :=
  refine G (individualize p v).1
    ((Array.replicate G.n false).set! (individualize p v).2 true) hashSeed

/-- The node invariant of that child, appended to the path invariant. -/
def childInv (G : Graph) (invPath : Array UInt64) (p : Part) (v : Nat) : Array UInt64 :=
  invPath.push (mix (child G p v).2 ((child G p v).1.shapeHash G.n))

/-- The leaves of the unpruned search tree below `p`, described by their keys. -/
inductive Reach (n : Nat) (f : Nat → Nat → Bool) :
    Array UInt64 → Part → List (List UInt64) → Prop
  | leaf {invPath : Array UInt64} {p : Part} (h : p.targetCell n = none) :
      Reach n f invPath p (leafKey invPath (certOf (Graph.ofOracle n f) p.lab))
  | step {invPath : Array UInt64} {p : Part} {c v : Nat} {k : List (List UInt64)}
      (hc : p.targetCell n = some c) (hv : v < n) (hcell : p.cst[p.pos[v]!]! = c)
      (h : Reach n f (childInv (Graph.ofOracle n f) invPath p v)
        (child (Graph.ofOracle n f) p v).1 k) :
      Reach n f invPath p k

/-! ### The tree is equivariant -/

theorem child_equiv {n : Nat} {σ : Nat → Nat} {f : Nat → Nat → Bool} {p q : Part}
    (hσ : IsPerm n σ) (hp : Part.WF n p) (hq : Part.WF n q) (h : PartEquiv n σ p q)
    {v : Nat} (hv : v < n) :
    PartEquiv n σ (child (Graph.ofOracle n f) p (σ v)).1
        (child (Graph.ofOracle n fun a b => f (σ a) (σ b)) q v).1
      ∧ (child (Graph.ofOracle n f) p (σ v)).2
        = (child (Graph.ofOracle n fun a b => f (σ a) (σ b)) q v).2 := by
  obtain ⟨he, hs⟩ := individualize_partEquiv hσ hp hq h hv
  rw [child, child, ofOracle_n, ofOracle_n, hs]
  exact refine_equiv hσ (individualize_wf' hp (hσ.maps v hv)) (individualize_wf' hq hv) he _ _

theorem childInv_equiv {n : Nat} {σ : Nat → Nat} {f : Nat → Nat → Bool} {p q : Part}
    (hσ : IsPerm n σ) (hp : Part.WF n p) (hq : Part.WF n q) (h : PartEquiv n σ p q)
    (invPath : Array UInt64) {v : Nat} (hv : v < n) :
    childInv (Graph.ofOracle n f) invPath p (σ v)
      = childInv (Graph.ofOracle n fun a b => f (σ a) (σ b)) invPath q v := by
  obtain ⟨he, hs⟩ := child_equiv hσ hp hq h hv
  rw [childInv, childInv, hs, ofOracle_n, ofOracle_n, he.shapeHash]

/-- **Leaves transport along a renaming.**  If `p` is `q` renamed by `σ`, every leaf of the tree
below `q` in the renamed graph has a leaf below `p` in the original one with the *same key*. -/
theorem reach_transfer {n : Nat} {σ : Nat → Nat} {f : Nat → Nat → Bool} (hσ : IsPerm n σ)
    {invPath : Array UInt64} {q : Part} {k : List (List UInt64)}
    (hr : Reach n (fun a b => f (σ a) (σ b)) invPath q k) :
    ∀ {p : Part}, Part.WF n p → Part.WF n q → PartEquiv n σ p q → Reach n f invPath p k := by
  induction hr with
  | leaf htc =>
    rename_i invPath q
    intro p hp hq h
    have htcp : p.targetCell n = none := h.targetCell.trans htc
    have hpd := discrete_of_targetCell_none hp htcp
    have hqd := discrete_of_targetCell_none hq htc
    rw [certOf_of_partEquiv hσ hp hq hpd hqd h f]
    exact Reach.leaf htcp
  | step hc hv hcell _ ih =>
    rename_i invPath q c v k _
    intro p hp hq h
    have hσv : σ v < n := hσ.maps v hv
    refine Reach.step (h.targetCell.trans hc) hσv ((h.cell v hv).trans hcell) ?_
    rw [childInv_equiv hσ hp hq h invPath hv]
    exact ih (refine_wf (individualize_wf' hp hσv) _ _) (refine_wf (individualize_wf' hq hv) _ _)
      (child_equiv hσ hp hq h hv).1

/-- The converse direction: a leaf below `p` gives one below `q`, again with the same key.  The
vertex to individualise is pulled back through `σ`. -/
theorem reach_transfer' {n : Nat} {σ : Nat → Nat} {f : Nat → Nat → Bool} (hσ : IsPerm n σ)
    {invPath : Array UInt64} {p : Part} {k : List (List UInt64)} (hr : Reach n f invPath p k) :
    ∀ {q : Part}, Part.WF n p → Part.WF n q → PartEquiv n σ p q →
      Reach n (fun a b => f (σ a) (σ b)) invPath q k := by
  induction hr with
  | leaf htc =>
    rename_i invPath p
    intro q hp hq h
    have htcq : q.targetCell n = none := h.targetCell.symm.trans htc
    have hpd := discrete_of_targetCell_none hp htc
    have hqd := discrete_of_targetCell_none hq htcq
    rw [← certOf_of_partEquiv hσ hp hq hpd hqd h f]
    exact Reach.leaf htcq
  | step hc hu hcell _ ih =>
    rename_i invPath p c u k _
    intro q hp hq h
    obtain ⟨v, hv, rfl⟩ := hσ.surj hu
    refine Reach.step (h.targetCell.symm.trans hc) hv ((h.cell v hv).symm.trans hcell) ?_
    rw [← childInv_equiv hσ hp hq h invPath hv]
    exact ih (refine_wf (individualize_wf' hp (hσ.maps v hv)) _ _)
      (refine_wf (individualize_wf' hq hv) _ _) (child_equiv hσ hp hq h hv).1

/-! ### The specification, and its invariance -/

/-- The root of the search: the initially refined partition and its one-entry invariant path. -/
def rootPart (n : Nat) (f : Nat → Nat → Bool) : Part :=
  (initialRefine (Graph.ofOracle n f)).1

/-- The invariant path at the root. -/
def rootInv (n : Nat) (f : Nat → Nat → Bool) : Array UInt64 :=
  #[mix (initialRefine (Graph.ofOracle n f)).2 ((rootPart n f).shapeHash n)]

/-- `k` is the key of a leaf of the whole (unpruned) search tree. -/
def Leafkey (n : Nat) (f : Nat → Nat → Bool) (k : List (List UInt64)) : Prop :=
  Reach n f (rootInv n f) (rootPart n f) k

/-- **The specification of `canonical`**: the largest key of any leaf. -/
def BestKey (n : Nat) (f : Nat → Nat → Bool) (k : List (List UInt64)) : Prop :=
  Leafkey n f k ∧ ∀ k', Leafkey n f k' → compare k' k ≠ .gt

theorem bestKey_unique {n : Nat} {f : Nat → Nat → Bool} {k k' : List (List UInt64)}
    (h : BestKey n f k) (h' : BestKey n f k') : k = k' := by
  have h1 := h.2 k' h'.1
  have h2 := h'.2 k h.1
  cases hc : compare k k' with
  | eq => exact LawfulEqCmp.eq_of_compare hc
  | lt => exact absurd (OrientedCmp.gt_of_lt hc) h1
  | gt => exact absurd hc h2

/-- **The specification is an isomorphism invariant.**  Renaming the graph does not change the
set of leaf keys, hence not the largest one. -/
theorem leafkey_transfer {n : Nat} {σ : Nat → Nat} {f : Nat → Nat → Bool} (hσ : IsPerm n σ)
    (k : List (List UInt64)) : Leafkey n (fun a b => f (σ a) (σ b)) k ↔ Leafkey n f k := by
  have hpe := (initialRefine_equiv (f := f) hσ).1
  have htr := (initialRefine_equiv (f := f) hσ).2
  have hroot : rootInv n (fun a b => f (σ a) (σ b)) = rootInv n f := by
    rw [rootInv, rootInv, ← htr, rootPart, rootPart, hpe.shapeHash]
  rw [Leafkey, Leafkey, hroot]
  exact ⟨fun h => reach_transfer hσ h (initialRefine_wf f) (initialRefine_wf _) hpe,
    fun h => reach_transfer' hσ h (initialRefine_wf f) (initialRefine_wf _) hpe⟩

theorem bestKey_transfer {n : Nat} {σ : Nat → Nat} {f : Nat → Nat → Bool} (hσ : IsPerm n σ)
    (k : List (List UInt64)) : BestKey n (fun a b => f (σ a) (σ b)) k ↔ BestKey n f k := by
  rw [BestKey, BestKey, leafkey_transfer hσ]
  exact and_congr_right fun _ =>
    ⟨fun h k' hk' => h k' ((leafkey_transfer hσ k').2 hk'),
     fun h k' hk' => h k' ((leafkey_transfer hσ k').1 hk')⟩

/-! ### The target cell really is a cell -/

theorem cenTargetFrom_cst {n : Nat} {p : Part} (hp : Part.WF n p) :
    ∀ (fuel i : Nat), (i < n → p.cst[i]! = i) → ∀ c, cenTargetFrom p.cen n fuel i = some c →
      p.cst[c]! = c
  | 0, i, _, c, h => by rw [cenTargetFrom] at h; exact absurd h (by simp)
  | fuel + 1, i, hi, c, h => by
    rw [cenTargetFrom] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hin
      split at h
      · cases h; exact hi (by omega)
      · rename_i hsize
        have hin' : i < n := by omega
        have hlt : i < p.cen[i]! := hp.ltCen i hin'
        have hcen : p.cen[i]! = i + 1 := by omega
        refine cenTargetFrom_cst hp fuel p.cen[i]! (fun hlt' => ?_) c h
        rw [hcen] at hlt' ⊢
        exact cst_succ hp hcen hlt'

/-- The target cell is a cell start. -/
theorem targetCell_cst {n : Nat} {p : Part} (hp : Part.WF n p) {c : Nat}
    (h : p.targetCell n = some c) : p.cst[c]! = c :=
  cenTargetFrom_cst hp n 0 (fun h0 => by
    have h1 := hp.cstLe 0 h0
    omega) c h

/-- The children `dfsChildren` enumerates are exactly the vertices of the target cell. -/
theorem mem_extract_cell {n : Nat} {p : Part} (hp : Part.WF n p) {c v : Nat} (hc : c < n)
    (hcst : p.cst[c]! = c) (h : v ∈ (p.lab.extract c p.cen[c]!).toList) :
    p.cst[p.pos[v]!]! = c := by
  rw [← Array.mem_def, Array.mem_iff_getElem] at h
  obtain ⟨i, hi, hv⟩ := h
  rw [Array.getElem_extract] at hv
  simp only [Array.size_extract] at hi
  have hlt : c + i < p.lab.size := by omega
  have hlt' : c + i < n := by rw [hp.labSize] at hlt; exact hlt
  have hvv : p.lab[c + i]! = v := by rw [getElem!_pos p.lab (c + i) hlt]; exact hv
  have hpos : p.pos[v]! = c + i := by rw [← hvv]; exact hp.posLab (c + i) hlt'
  rw [hpos]
  refine (hp.cellCst c hc (c + i) (by omega) ?_).trans hcst
  rw [hp.labSize] at hi
  omega

/-! ### The winner is a leaf of the tree

The induction is parametric in a predicate `P` on keys: if everything reachable below the current
node satisfies `P`, and everything the state already holds satisfies `P`, then so does everything
the state holds afterwards.  Taking `P` to be "is a leaf key of the whole tree" at the root gives
`canonical_leafkey`. -/

/-- Every leaf the state holds satisfies `P`. -/
def StP (P : List (List UInt64) → Prop) (st : St) : Prop :=
  ∀ l, st.best = some l → P (leafKey l.invPath l.cert)

theorem pruneNode_P {P : List (List UInt64) → Prop} {invPath : Array UInt64} {st st' : St}
    (h : pruneNode invPath st = some st') (hst : StP P st) : StP P st' := by
  rw [pruneNode] at h
  split at h
  · cases h; exact hst
  · split at h
    · exact absurd h (by simp)
    · cases h; intro l hl; exact absurd hl (by simp)
    · cases h; exact hst

theorem StP.addAuto {P : List (List UInt64) → Prop} {st : St} (h : StP P st) (g : Array Nat) :
    StP P (st.addAuto g) :=
  fun l hl => h l ((addAuto_best st g) ▸ hl)

theorem StP.unwind {P : List (List UInt64) → Prop} {st : St} (h : StP P st) (path : Array Nat) :
    StP P (unwind path st) :=
  fun l hl => h l ((unwind_best path st) ▸ hl)

theorem leafUpdate_P {P : List (List UInt64) → Prop} {G : Graph} {path : Array Nat}
    {invPath : Array UInt64} {lab : Array Nat} {st : St}
    (hl : P (leafKey invPath (certOf G lab))) (hst : StP P st) :
    StP P (leafUpdate G path invPath lab st) := by
  intro l hb
  rcases leafUpdate_best G path invPath lab st with h | h
  · exact hst l (h ▸ hb)
  · rw [h] at hb; cases hb; exact hl

/-- **The search only ever holds leaves of the tree below the current node.** -/
theorem dfsNode_reach (n : Nat) (f : Nat → Nat → Bool) (P : List (List UInt64) → Prop) :
    ∀ (fuel : Nat) (path : Array Nat) (invPath : Array UInt64) (p : Part) (st : St),
      Part.WF n p → (∀ k, Reach n f invPath p k → P k) → StP P st →
        StP P (dfsNode (Graph.ofOracle n f) fuel path invPath p st) := by
  refine dfsNode.induct (Graph.ofOracle n f)
    (motive1 := fun fuel path invPath p st =>
      Part.WF n p → (∀ k, Reach n f invPath p k → P k) → StP P st →
        StP P (dfsNode (Graph.ofOracle n f) fuel path invPath p st))
    (motive2 := fun fuel path invPath p verts processed orb st =>
      Part.WF n p → (∀ v ∈ verts, v < n) →
        (∀ v ∈ verts, ∀ k, Reach n f (childInv (Graph.ofOracle n f) invPath p v)
          (child (Graph.ofOracle n f) p v).1 k → P k) → StP P st →
        StP P (dfsChildren (Graph.ofOracle n f) fuel path invPath p verts processed orb st))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  case refine_1 => intro path invPath p st _ _ hst; rw [dfsNode]; exact hst
  case refine_2 =>
    intro path invPath p st fuel habort _ _ hst
    rw [dfsNode_abort habort]; exact hst
  case refine_3 =>
    intro path invPath p st fuel habort hprune _ _ hst
    rw [dfsNode_pruned (by simpa using habort) hprune]; exact hst
  case refine_4 =>
    intro path invPath p st fuel habort st1 hprune htc _ hreach hst
    have hst1 : StP P st1 := pruneNode_P hprune hst
    rw [dfsNode_leaf (by simpa using habort) hprune htc]
    exact leafUpdate_P (hreach _ (Reach.leaf htc)) hst1
  case refine_5 =>
    intro path invPath p st fuel habort st1 hprune st2 s htc verts orb ih hp hreach hst
    have hst1 : StP P st1 := pruneNode_P hprune hst
    rw [dfsNode_branch (by simpa using habort) hprune htc]
    refine ih hp (fun v hv => mem_extract_lt hp hv) (fun v hv k hk => hreach k ?_) hst1
    exact Reach.step htc (mem_extract_lt hp hv)
      (mem_extract_cell hp (targetCell_lt n p s htc) (targetCell_cst hp htc) hv) hk
  case refine_6 =>
    intro fuel path invPath p processed orb st _ _ _ hst
    rw [dfsChildren_nil]; exact hst
  case refine_7 =>
    intro fuel path invPath p processed orb st v vs habort _ _ _ hst
    rw [dfsChildren_abort habort]; exact hst
  case refine_8 =>
    intro fuel path invPath p processed orb st v vs habort orb1 hmark ih hp hverts hreach hst
    rw [dfsChildren_marked (by simpa using habort) hmark]
    exact ih hp (fun w hw => hverts w (List.mem_cons_of_mem _ hw))
      (fun w hw => hreach w (List.mem_cons_of_mem _ hw)) hst
  case refine_9 =>
    intro fuel path invPath p processed orb st v vs habort orb1 hmark p' s hind inW p'' tr href
      childInv' st1 st2 habort2 ih1 hp hverts hreach hst
    have hchild : child (Graph.ofOracle n f) p v = (p'', tr) := by rw [child, hind]; exact href
    have hcinv : childInv (Graph.ofOracle n f) invPath p v = childInv' := by
      rw [childInv, hchild]
    have hwf'' : Part.WF n p'' := by
      have h2 : p'' = (child (Graph.ofOracle n f) p v).1 := by rw [hchild]
      rw [h2, child]
      exact refine_wf (individualize_wf' hp (hverts v (by simp))) _ _
    have hr : ∀ k, Reach n f childInv' p'' k → P k := by
      intro k hk
      refine hreach v (by simp) k ?_
      rw [hcinv, hchild]
      exact hk
    rw [dfsChildren_step_stop (by simpa using habort)
      (by simp only [Bool.not_eq_true] at hmark; exact hmark) hind href habort2]
    exact (ih1 hwf'' hr hst).unwind path
  case refine_10 =>
    intro fuel path invPath p processed orb st v vs habort orb1 hmark p' s hind inW p'' tr href
      childInv' st1 st2 habort2 orb2 ih1 _ih1' ih2 hp hverts hreach hst
    have hchild : child (Graph.ofOracle n f) p v = (p'', tr) := by rw [child, hind]; exact href
    have hcinv : childInv (Graph.ofOracle n f) invPath p v = childInv' := by
      rw [childInv, hchild]
    have hwf'' : Part.WF n p'' := by
      have h2 : p'' = (child (Graph.ofOracle n f) p v).1 := by rw [hchild]
      rw [h2, child]
      exact refine_wf (individualize_wf' hp (hverts v (by simp))) _ _
    have hr : ∀ k, Reach n f childInv' p'' k → P k := by
      intro k hk
      refine hreach v (by simp) k ?_
      rw [hcinv, hchild]
      exact hk
    rw [dfsChildren_step_go (by simpa using habort)
      (by simp only [Bool.not_eq_true] at hmark; exact hmark) hind href
      (by simp only [Bool.not_eq_true] at habort2; exact habort2)]
    exact ih2 hp (fun w hw => hverts w (List.mem_cons_of_mem _ hw))
      (fun w hw => hreach w (List.mem_cons_of_mem _ hw))
      ((ih1 hwf'' hr hst).unwind path)

/-! ### The winner is a leaf of the whole tree -/

/-- The final state of the search on `Graph.ofOracle n f`. -/
def canonSt (n : Nat) (f : Nat → Nat → Bool) : St :=
  dfsNode (Graph.ofOracle n f) (n + 1) #[] (rootInv n f) (rootPart n f)
    { best := none, first := none, autos := #[], nodes := 0, abortTo := none }

theorem canonical_eq (n : Nat) (f : Nat → Nat → Bool) :
    canonical (Graph.ofOracle n f) =
      match (canonSt n f).best with
      | none => { lab := Array.range n, cert := certOf (Graph.ofOracle n f) (Array.range n),
                  autos := #[], nodes := (canonSt n f).nodes }
      | some b => { lab := b.lab, cert := b.cert, autos := (canonSt n f).autos,
                    nodes := (canonSt n f).nodes } := rfl

/-- **Soundness of the search.**  Whatever leaf the search ends up holding really is a leaf of
the (unpruned) tree. -/
theorem canonSt_leafkey (n : Nat) (f : Nat → Nat → Bool) :
    StP (Leafkey n f) (canonSt n f) :=
  dfsNode_reach n f (Leafkey n f) (n + 1) #[] (rootInv n f) (rootPart n f) _
    (initialRefine_wf f) (fun _ hk => hk) (by intro l hl; exact absurd hl (by simp))

theorem canonical_cert_leafkey (n : Nat) (f : Nat → Nat → Bool) (b : Leaf)
    (hb : (canonSt n f).best = some b) :
    (canonical (Graph.ofOracle n f)).cert = b.cert ∧ Leafkey n f (leafKey b.invPath b.cert) :=
  ⟨by rw [canonical_eq, hb], canonSt_leafkey n f b hb⟩

/-! ### Leaves extend the invariant path of the node they hang below -/

theorem reach_extends {n : Nat} {f : Nat → Nat → Bool} {invPath : Array UInt64} {p : Part}
    {k : List (List UInt64)} (h : Reach n f invPath p k) :
    ∃ tail c, k = [invPath.toList ++ tail, c] := by
  induction h with
  | @leaf invPath p h =>
    exact ⟨[], (certOf (Graph.ofOracle n f) p.lab).toList, by simp [leafKey]⟩
  | @step invPath p c v k hc hv hcell h ih =>
    obtain ⟨tail, cert, hk⟩ := ih
    refine ⟨mix (child (Graph.ofOracle n f) p v).2
      ((child (Graph.ofOracle n f) p v).1.shapeHash n) :: tail, cert, ?_⟩
    rw [hk, childInv]
    simp

/-- If a node's invariant path is already worse than the incumbent's, so is every leaf below it. -/
theorem compare_append_lt {ip b : List UInt64} (tail : List UInt64)
    (h : compare ip (b.take ip.length) = .lt) : compare (ip ++ tail) b = .lt := by
  induction ip generalizing b with
  | nil => exact absurd h (by simp)
  | cons a ip ih =>
    cases b with
    | nil => exact absurd h (by simp [List.compare_cons_nil])
    | cons x b =>
      rw [List.length_cons, List.take_succ_cons, List.compare_cons_cons] at h
      rw [List.cons_append, List.compare_cons_cons]
      cases hax : compare a x with
      | lt => rfl
      | gt => rw [hax] at h; simp at h
      | eq => rw [hax] at h; simpa using ih (by simpa using h)

theorem compare_leafKey_lt {ip b tail c c' : List UInt64}
    (h : compare ip (b.take ip.length) = .lt) : compare [ip ++ tail, c] [b, c'] = .lt := by
  rw [List.compare_cons_cons, compare_append_lt tail h]; rfl

/-! ### Invariant pruning is sound -/

/-- `k` is beaten by the leaf the state currently holds. -/
def Beaten (st : St) (k : List (List UInt64)) : Prop :=
  ∃ l, st.best = some l ∧ compare k (leafKey l.invPath l.cert) = .lt

theorem lexCmpU64_extract {a b : Array UInt64} :
    lexCmpU64 a (b.extract 0 a.size) = compare a.toList (b.toList.take a.size) := by
  rw [lexCmpU64_eq_compare]
  congr 1
  simp

/-- When `pruneNode` discards the subtree, every leaf below the node is beaten. -/
theorem pruneNode_none {n : Nat} {f : Nat → Nat → Bool} {invPath : Array UInt64} {p : Part}
    {st : St} (h : pruneNode invPath st = none) {k : List (List UInt64)}
    (hk : Reach n f invPath p k) : Beaten st k := by
  rw [pruneNode] at h
  split at h
  · exact absurd h (by simp)
  · rename_i b hb
    refine ⟨b, hb, ?_⟩
    obtain ⟨tail, c, rfl⟩ := reach_extends hk
    split at h
    · rename_i hlt
      rw [lexCmpU64_extract] at hlt
      exact compare_leafKey_lt (by simpa using hlt)
    · exact absurd h (by simp)
    · exact absurd h (by simp)

end Canon
end IsoGraph
