/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.ComposeAssoc

/-!
# Rotation of closures

The closure of a composite equals the closure of the first factor
against the rotated composite (`pairCloseComposeRotate`): for an
`(m,n)`-fragment `F`, an `(n,p)`-fragment `H`, and an
`(m+p)`-fragment `K`,

    (F ∘ H) ∗ K  ≃  F ∗ (K ∘ Hᵀ),

where `Hᵀ` transposes the boundary of `H`.  Both sides glue the
same three interface blocks over the common ambient `(F ⊔ H) ⊔ K`
— the `n`-interface between `F` and `H`, the `m`-block between
`F` and `K`, and the `p`-block between `H` and `K` — so the two
closures are equivalent closed fragments.  This is the engine of
the ideal lemma and the trace calculus (accompanying paper,
Lemma 3.3(a) and Lemma 3.5(a)).
-/

@[expose] public section

namespace RS

/-- The boundary transpose: exchange the two sides of an
`(n,p)`-boundary. -/
noncomputable def transposeEquiv (n p : ℕ) :
    Fin (n + p) ≃ Fin (p + n) :=
  (finSumFinEquiv.symm.trans
    (_root_.Equiv.sumComm (Fin n) (Fin p))).trans finSumFinEquiv

/-- The transpose sends low labels beyond the split. -/
theorem transposeEquiv_low (n p : ℕ) (j : ℕ) (hj : j < n)
    (h1 : j < n + p) (h2 : p + j < p + n) :
    transposeEquiv n p ⟨j, h1⟩ = ⟨p + j, h2⟩ := by
  unfold transposeEquiv
  have h3 : (⟨j, h1⟩ : Fin (n + p)) = Fin.castAdd p ⟨j, hj⟩ :=
    Fin.ext rfl
  rw [_root_.Equiv.trans_apply, _root_.Equiv.trans_apply, h3,
    finSumFinEquiv_symm_apply_castAdd]
  change finSumFinEquiv (Sum.inr ⟨j, hj⟩) = _
  rw [finSumFinEquiv_apply_right]
  exact Fin.ext rfl

/-- The transpose sends high labels below the split. -/
theorem transposeEquiv_high (n p : ℕ) (i : ℕ) (hi : i < p)
    (h1 : n + i < n + p) (h2 : i < p + n) :
    transposeEquiv n p ⟨n + i, h1⟩ = ⟨i, h2⟩ := by
  unfold transposeEquiv
  have h3 : (⟨n + i, h1⟩ : Fin (n + p)) = Fin.natAdd n ⟨i, hi⟩ :=
    Fin.ext rfl
  rw [_root_.Equiv.trans_apply, _root_.Equiv.trans_apply, h3,
    finSumFinEquiv_symm_apply_natAdd]
  change finSumFinEquiv (Sum.inl ⟨i, hi⟩) = _
  rw [finSumFinEquiv_apply_left]
  exact Fin.ext rfl

/-- The inverse transpose sends low labels beyond the split. -/
theorem transposeEquiv_symm_low (n p : ℕ) (l : ℕ) (hl : l < p)
    (h1 : l < p + n) (h2 : n + l < n + p) :
    (transposeEquiv n p).symm ⟨l, h1⟩ = ⟨n + l, h2⟩ :=
  (_root_.Equiv.symm_apply_eq _).mpr
    (transposeEquiv_high n p l hl h2 h1).symm

/-- The inverse transpose sends high labels below the split. -/
theorem transposeEquiv_symm_high (n p : ℕ) (j : ℕ) (hj : j < n)
    (h1 : p + j < p + n) (h2 : j < n + p) :
    (transposeEquiv n p).symm ⟨p + j, h1⟩ = ⟨j, h2⟩ :=
  (_root_.Equiv.symm_apply_eq _).mpr
    (transposeEquiv_low n p j hj h2 h1).symm

/-! ### The three interface blocks over the common ambient -/

/-- The `m`-block: the low labels of `F` against the low labels
of `K`, top pair first. -/
def mBlock (m n p : ℕ) :
    List (((Fin (m + n) ⊕ Fin (n + p)) ⊕ Fin (m + p)) ×
      ((Fin (m + n) ⊕ Fin (n + p)) ⊕ Fin (m + p))) :=
  (List.finRange m).reverse.map (fun i =>
    (Sum.inl (Sum.inl ⟨i.val, by have := i.isLt; omega⟩),
     Sum.inr ⟨i.val, by have := i.isLt; omega⟩))

/-- The `p`-block: the high labels of `H` against the high labels
of `K`, top pair first. -/
def pBlock (m n p : ℕ) :
    List (((Fin (m + n) ⊕ Fin (n + p)) ⊕ Fin (m + p)) ×
      ((Fin (m + n) ⊕ Fin (n + p)) ⊕ Fin (m + p))) :=
  (List.finRange p).reverse.map (fun ℓ =>
    (Sum.inl (Sum.inr ⟨n + ℓ.val, by have := ℓ.isLt; omega⟩),
     Sum.inr ⟨m + ℓ.val, by have := ℓ.isLt; omega⟩))

/-- The `n`-block: the high labels of `F` against the low labels
of `H`, top pair first — the embedded composition interface. -/
def nBlock (m n p : ℕ) :
    List (((Fin (m + n) ⊕ Fin (n + p)) ⊕ Fin (m + p)) ×
      ((Fin (m + n) ⊕ Fin (n + p)) ⊕ Fin (m + p))) :=
  (List.finRange n).reverse.map (fun j =>
    (Sum.inl (Sum.inl ⟨m + j.val, by have := j.isLt; omega⟩),
     Sum.inl (Sum.inr ⟨j.val, by have := j.isLt; omega⟩)))

/-- Membership in the `m`-block. -/
theorem mem_mBlock (m n p : ℕ) (q) :
    q ∈ mBlock m n p ↔
      ∃ i : Fin m,
        q = (Sum.inl (Sum.inl ⟨i.val, by have := i.isLt; omega⟩),
          Sum.inr ⟨i.val, by have := i.isLt; omega⟩) := by
  unfold mBlock
  simp only [List.mem_map, List.mem_reverse, List.mem_finRange,
    true_and]
  exact ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩

/-- Membership in the `p`-block. -/
theorem mem_pBlock (m n p : ℕ) (q) :
    q ∈ pBlock m n p ↔
      ∃ ℓ : Fin p,
        q = (Sum.inl (Sum.inr ⟨n + ℓ.val, by have := ℓ.isLt; omega⟩),
          Sum.inr ⟨m + ℓ.val, by have := ℓ.isLt; omega⟩) := by
  unfold pBlock
  simp only [List.mem_map, List.mem_reverse, List.mem_finRange,
    true_and]
  exact ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩

/-- Membership in the `n`-block. -/
theorem mem_nBlock (m n p : ℕ) (q) :
    q ∈ nBlock m n p ↔
      ∃ j : Fin n,
        q = (Sum.inl (Sum.inl ⟨m + j.val, by have := j.isLt; omega⟩),
          Sum.inl (Sum.inr ⟨j.val, by have := j.isLt; omega⟩)) := by
  unfold nBlock
  simp only [List.mem_map, List.mem_reverse, List.mem_finRange,
    true_and]
  exact ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩

/-- The `m`-block is well-formed. -/
theorem mBlock_wf (m n p : ℕ) : Fragment.PairsWF (mBlock m n p) := by
  unfold Fragment.PairsWF mBlock
  rw [List.flatMap_map, List.nodup_flatMap]
  refine ⟨fun k _ => by simp, ?_⟩
  rw [List.pairwise_reverse]
  refine (List.nodup_finRange m).pairwise_of_forall_ne ?_
  intro k _ j _ hkj x hxj hxk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hxj hxk
  rcases hxj with rfl | rfl <;> rcases hxk with h | h <;>
    (simp only [Sum.inl.injEq, Sum.inr.injEq, Fin.mk.injEq,
      reduceCtorEq] at h <;>
     exact hkj (Fin.ext (by omega)).symm)

/-- The `p`-block is well-formed. -/
theorem pBlock_wf (m n p : ℕ) : Fragment.PairsWF (pBlock m n p) := by
  unfold Fragment.PairsWF pBlock
  rw [List.flatMap_map, List.nodup_flatMap]
  refine ⟨fun k _ => by simp, ?_⟩
  rw [List.pairwise_reverse]
  refine (List.nodup_finRange p).pairwise_of_forall_ne ?_
  intro k _ j _ hkj x hxj hxk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hxj hxk
  rcases hxj with rfl | rfl <;> rcases hxk with h | h <;>
    (simp only [Sum.inl.injEq, Sum.inr.injEq, Fin.mk.injEq,
      reduceCtorEq] at h <;>
     exact hkj (Fin.ext (by omega)).symm)

/-- The `n`-block is well-formed. -/
theorem nBlock_wf (m n p : ℕ) : Fragment.PairsWF (nBlock m n p) := by
  unfold Fragment.PairsWF nBlock
  rw [List.flatMap_map, List.nodup_flatMap]
  refine ⟨fun k _ => by simp, ?_⟩
  rw [List.pairwise_reverse]
  refine (List.nodup_finRange n).pairwise_of_forall_ne ?_
  intro k _ j _ hkj x hxj hxk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hxj hxk
  rcases hxj with rfl | rfl <;> rcases hxk with h | h <;>
    (simp only [Sum.inl.injEq, Sum.inr.injEq, Fin.mk.injEq,
      reduceCtorEq] at h <;>
     exact hkj (Fin.ext (by omega)).symm)

/-- The `n`-block and `p`-block glue disjoint labels. -/
theorem nBlock_pBlock_disjoint (m n p : ℕ) :
    ∀ x ∈ (nBlock m n p).flatMap (fun q => [q.1, q.2]),
      x ∉ (pBlock m n p).flatMap (fun q => [q.1, q.2]) := by
  intro x hx hy
  obtain ⟨q₁, hq₁, hx₁⟩ := List.mem_flatMap.mp hx
  obtain ⟨q₂, hq₂, hy₂⟩ := List.mem_flatMap.mp hy
  obtain ⟨j, rfl⟩ := (mem_nBlock m n p _).mp hq₁
  obtain ⟨l, rfl⟩ := (mem_pBlock m n p _).mp hq₂
  have hj := j.isLt
  have hl := l.isLt
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx₁ hy₂
  rcases hx₁ with rfl | rfl <;> rcases hy₂ with h | h <;>
    (simp only [Sum.inl.injEq, Sum.inr.injEq, Fin.mk.injEq,
      reduceCtorEq] at h <;> omega)

/-- The `n`-block and `m`-block glue disjoint labels. -/
theorem nBlock_mBlock_disjoint (m n p : ℕ) :
    ∀ x ∈ (nBlock m n p).flatMap (fun q => [q.1, q.2]),
      x ∉ (mBlock m n p).flatMap (fun q => [q.1, q.2]) := by
  intro x hx hy
  obtain ⟨q₁, hq₁, hx₁⟩ := List.mem_flatMap.mp hx
  obtain ⟨q₂, hq₂, hy₂⟩ := List.mem_flatMap.mp hy
  obtain ⟨j, rfl⟩ := (mem_nBlock m n p _).mp hq₁
  obtain ⟨i, rfl⟩ := (mem_mBlock m n p _).mp hq₂
  have hj := j.isLt
  have hi := i.isLt
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx₁ hy₂
  rcases hx₁ with rfl | rfl <;> rcases hy₂ with h | h <;>
    (simp only [Sum.inl.injEq, Fin.mk.injEq,
      reduceCtorEq] at h <;> omega)

/-- The `p`-block and `m`-block glue disjoint labels. -/
theorem pBlock_mBlock_disjoint (m n p : ℕ) :
    ∀ x ∈ (pBlock m n p).flatMap (fun q => [q.1, q.2]),
      x ∉ (mBlock m n p).flatMap (fun q => [q.1, q.2]) := by
  intro x hx hy
  obtain ⟨q₁, hq₁, hx₁⟩ := List.mem_flatMap.mp hx
  obtain ⟨q₂, hq₂, hy₂⟩ := List.mem_flatMap.mp hy
  obtain ⟨l, rfl⟩ := (mem_pBlock m n p _).mp hq₁
  obtain ⟨i, rfl⟩ := (mem_mBlock m n p _).mp hq₂
  have hl := l.isLt
  have hi := i.isLt
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx₁ hy₂
  rcases hx₁ with rfl | rfl <;> rcases hy₂ with h | h <;>
    (simp only [Sum.inl.injEq, Sum.inr.injEq, Fin.mk.injEq,
      reduceCtorEq] at h <;> omega)

/-- The combined block list of the left association is
well-formed. -/
theorem rotatePairsL_wf (m n p : ℕ) :
    Fragment.PairsWF
      (nBlock m n p ++ (pBlock m n p ++ mBlock m n p)) := by
  unfold Fragment.PairsWF
  rw [List.flatMap_append, List.flatMap_append]
  refine List.Nodup.append (nBlock_wf m n p)
    (List.Nodup.append (pBlock_wf m n p) (mBlock_wf m n p)
      (pBlock_mBlock_disjoint m n p)) ?_
  intro x hx hy
  rcases List.mem_append.mp hy with hy | hy
  · exact nBlock_pBlock_disjoint m n p x hx hy
  · exact nBlock_mBlock_disjoint m n p x hx hy

/-- The middle-swap permutation between the two block orders. -/
theorem rotatePairs_perm (m n p : ℕ) :
    (nBlock m n p ++ (pBlock m n p ++ mBlock m n p)).Perm
      (pBlock m n p ++ (nBlock m n p ++ mBlock m n p)) :=
  ((List.perm_append_comm_assoc _ _ _))

/-- The combined block list of the right association is
well-formed. -/
theorem rotatePairsR_wf (m n p : ℕ) :
    Fragment.PairsWF
      (pBlock m n p ++ (nBlock m n p ++ mBlock m n p)) :=
  (rotatePairsL_wf m n p).perm (rotatePairs_perm m n p)

/-! ### Splitting closure lists -/

/-- `mapPairs` distributes over appends. -/
theorem mapPairs_append {α β : Type} (e : α ≃ β)
    (ps qs : List (α × α)) :
    Fragment.mapPairs e (ps ++ qs) =
      Fragment.mapPairs e ps ++ Fragment.mapPairs e qs :=
  List.map_append ..

/-- The separation of an append restricts to the left part. -/
theorem Fragment.PairsSepAll.append_left' {α : Type}
    {ps qs₁ qs₂ : List (α × α)}
    (h : Fragment.PairsSepAll ps (qs₁ ++ qs₂)) :
    Fragment.PairsSepAll ps qs₁ :=
  fun q hq => h q (List.mem_append.mpr (Or.inl hq))

/-- The separation of an append restricts to the right part. -/
theorem Fragment.PairsSepAll.append_right' {α : Type}
    {ps qs₁ qs₂ : List (α × α)}
    (h : Fragment.PairsSepAll ps (qs₁ ++ qs₂)) :
    Fragment.PairsSepAll ps qs₂ :=
  fun q hq => h q (List.mem_append.mpr (Or.inr hq))

/-- `liftPairs` distributes over appends. -/
theorem liftPairs_append {α : Type} (ps : List (α × α)) :
    ∀ (qs₁ qs₂ : List (α × α))
      (h : Fragment.PairsSepAll ps (qs₁ ++ qs₂)),
      Fragment.liftPairs ps (qs₁ ++ qs₂) h =
        Fragment.liftPairs ps qs₁ h.append_left' ++
          Fragment.liftPairs ps qs₂ h.append_right'
  | [], _, _ => rfl
  | q :: qs₁, qs₂, h => by
    simp only [List.cons_append, Fragment.liftPairs]
    exact congrArg₂ List.cons
      (Prod.ext (Subtype.ext rfl) (Subtype.ext rfl))
      (liftPairs_append ps qs₁ qs₂ _)

/-- The high half of a full-closure interface list. -/
def ipHigh (m p : ℕ) :
    List ((Fin (0 + (m + p)) ⊕ Fin (m + p + 0)) ×
      (Fin (0 + (m + p)) ⊕ Fin (m + p + 0))) :=
  (List.finRange p).reverse.map (fun ℓ =>
    (Sum.inl ⟨m + ℓ.val, by have := ℓ.isLt; omega⟩,
     Sum.inr ⟨m + ℓ.val, by have := ℓ.isLt; omega⟩))

/-- The low half of a full-closure interface list. -/
def ipLow (m p : ℕ) :
    List ((Fin (0 + (m + p)) ⊕ Fin (m + p + 0)) ×
      (Fin (0 + (m + p)) ⊕ Fin (m + p + 0))) :=
  (List.finRange m).reverse.map (fun i =>
    (Sum.inl ⟨i.val, by have := i.isLt; omega⟩,
     Sum.inr ⟨i.val, by have := i.isLt; omega⟩))

/-- A full-closure interface list splits into its high and low
halves. -/
theorem interfacePairs_closure_split (m p : ℕ) :
    interfacePairs 0 (m + p) 0 = ipHigh m p ++ ipLow m p := by
  unfold interfacePairs ipHigh ipLow
  rw [List.map_reverse, List.map_reverse, List.map_reverse,
    ← List.reverse_append]
  refine congrArg List.reverse ?_
  rw [← List.ofFn_eq_map, List.ofFn_add, List.ofFn_eq_map,
    List.ofFn_eq_map]
  refine congrArg₂ (· ++ ·)
    (List.map_congr_left fun i _ => ?_)
    (List.map_congr_left fun ℓ _ => ?_)
  · refine Prod.ext (congrArg Sum.inl (Fin.ext ?_))
      (congrArg Sum.inr (Fin.ext ?_))
    · change 0 + i.val = i.val
      omega
    · rfl
  · refine Prod.ext (congrArg Sum.inl (Fin.ext ?_))
      (congrArg Sum.inr (Fin.ext ?_))
    · change 0 + (m + ℓ.val) = m + ℓ.val
      omega
    · rfl

/-- The `n`-block is the embedded composition interface. -/
theorem nBlock_eq_inlPairs (m n p : ℕ) :
    nBlock m n p =
      Fragment.inlPairs (β := Fin (m + p))
        (interfacePairs m n p) := by
  unfold nBlock Fragment.inlPairs interfacePairs
  rw [List.map_map]
  rfl

/-! ### Lifting the closure halves -/

/-- The high closure half lifts to the `p`-block, generalized
over any transport with the expected boundary values. -/
private theorem rotate_lift_high_aux (m n p : ℕ)
    (ps₀ : List
      (((Fin (m + n) ⊕ Fin (n + p)) ⊕ Fin (m + p)) ×
        ((Fin (m + n) ⊕ Fin (n + p)) ⊕ Fin (m + p))))
    (E : (Fin (0 + (m + p)) ⊕ Fin (m + p + 0)) ≃
      Fragment.FoldSurviving
        ((Fin (m + n) ⊕ Fin (n + p)) ⊕ Fin (m + p)) ps₀)
    (hE1 : ∀ (ℓ : ℕ) (_ : ℓ < p) (h1 : m + ℓ < 0 + (m + p))
      (h2 : n + ℓ < n + p),
      (E (Sum.inl ⟨m + ℓ, h1⟩)).val =
        Sum.inl (Sum.inr ⟨n + ℓ, h2⟩))
    (hE2 : ∀ (ℓ : ℕ) (_ : ℓ < p) (h1 : m + ℓ < m + p + 0)
      (h2 : m + ℓ < m + p),
      (E (Sum.inr ⟨m + ℓ, h1⟩)).val = Sum.inr ⟨m + ℓ, h2⟩) :
    ∀ (l : List (Fin p))
      (hsep : Fragment.PairsSepAll ps₀
        (l.map (fun ℓ =>
          (Sum.inl (Sum.inr ⟨n + ℓ.val, by have := ℓ.isLt; omega⟩),
           Sum.inr ⟨m + ℓ.val, by have := ℓ.isLt; omega⟩)))),
      Fragment.mapPairs E
          (l.map (fun ℓ =>
            ((Sum.inl ⟨m + ℓ.val, by have := ℓ.isLt; omega⟩ :
                Fin (0 + (m + p)) ⊕ Fin (m + p + 0)),
             Sum.inr ⟨m + ℓ.val, by have := ℓ.isLt; omega⟩))) =
        Fragment.liftPairs _ _ hsep
  | [], _ => rfl
  | ℓ :: l, hsep => by
    simp only [List.map_cons, Fragment.mapPairs,
      Fragment.liftPairs, Prod.map]
    refine congrArg₂ List.cons (Prod.ext ?_ ?_)
      (rotate_lift_high_aux m n p ps₀ E hE1 hE2 l _)
    · exact Subtype.ext (hE1 ℓ.val ℓ.isLt
        (by have := ℓ.isLt; omega) (by have := ℓ.isLt; omega))
    · exact Subtype.ext (hE2 ℓ.val ℓ.isLt
        (by have := ℓ.isLt; omega) (by have := ℓ.isLt; omega))

/-- The low closure half lifts to the `m`-block, generalized
over any transport with the expected boundary values and any
closure size. -/
private theorem rotate_lift_low_aux (m n p T : ℕ) (hT : m ≤ T)
    (ps₀ : List
      (((Fin (m + n) ⊕ Fin (n + p)) ⊕ Fin (m + p)) ×
        ((Fin (m + n) ⊕ Fin (n + p)) ⊕ Fin (m + p))))
    (E : (Fin (0 + T) ⊕ Fin (T + 0)) ≃
      Fragment.FoldSurviving
        ((Fin (m + n) ⊕ Fin (n + p)) ⊕ Fin (m + p)) ps₀)
    (hE1 : ∀ (i : ℕ) (_ : i < m) (h1 : i < 0 + T)
      (h2 : i < m + n),
      (E (Sum.inl ⟨i, h1⟩)).val = Sum.inl (Sum.inl ⟨i, h2⟩))
    (hE2 : ∀ (i : ℕ) (_ : i < m) (h1 : i < T + 0)
      (h2 : i < m + p),
      (E (Sum.inr ⟨i, h1⟩)).val = Sum.inr ⟨i, h2⟩) :
    ∀ (l : List (Fin m))
      (hsep : Fragment.PairsSepAll ps₀
        (l.map (fun i =>
          (Sum.inl (Sum.inl ⟨i.val, by have := i.isLt; omega⟩),
           Sum.inr ⟨i.val, by have := i.isLt; omega⟩)))),
      Fragment.mapPairs E
          (l.map (fun i =>
            ((Sum.inl ⟨i.val, by have := i.isLt; omega⟩ :
                Fin (0 + T) ⊕ Fin (T + 0)),
             Sum.inr ⟨i.val, by have := i.isLt; omega⟩))) =
        Fragment.liftPairs _ _ hsep
  | [], _ => rfl
  | i :: l, hsep => by
    simp only [List.map_cons, Fragment.mapPairs,
      Fragment.liftPairs, Prod.map]
    refine congrArg₂ List.cons (Prod.ext ?_ ?_)
      (rotate_lift_low_aux m n p T hT ps₀ E hE1 hE2 l _)
    · exact Subtype.ext (hE1 i.val i.isLt
        (by have := i.isLt; omega) (by have := i.isLt; omega))
    · exact Subtype.ext (hE2 i.val i.isLt
        (by have := i.isLt; omega) (by have := i.isLt; omega))

/-- The high closure half of the right side lifts to the
`n`-block, generalized over any transport with the expected
boundary values. -/
private theorem rotate_lift_nblock_aux (m n p : ℕ)
    (ps₀ : List
      (((Fin (m + n) ⊕ Fin (n + p)) ⊕ Fin (m + p)) ×
        ((Fin (m + n) ⊕ Fin (n + p)) ⊕ Fin (m + p))))
    (E : (Fin (0 + (m + n)) ⊕ Fin (m + n + 0)) ≃
      Fragment.FoldSurviving
        ((Fin (m + n) ⊕ Fin (n + p)) ⊕ Fin (m + p)) ps₀)
    (hE1 : ∀ (i : ℕ) (_ : i < n) (h1 : m + i < 0 + (m + n))
      (h2 : m + i < m + n),
      (E (Sum.inl ⟨m + i, h1⟩)).val =
        Sum.inl (Sum.inl ⟨m + i, h2⟩))
    (hE2 : ∀ (i : ℕ) (_ : i < n) (h1 : m + i < m + n + 0)
      (h2 : i < n + p),
      (E (Sum.inr ⟨m + i, h1⟩)).val =
        Sum.inl (Sum.inr ⟨i, h2⟩)) :
    ∀ (l : List (Fin n))
      (hsep : Fragment.PairsSepAll ps₀
        (l.map (fun i =>
          (Sum.inl (Sum.inl ⟨m + i.val, by have := i.isLt; omega⟩),
           Sum.inl (Sum.inr ⟨i.val, by have := i.isLt; omega⟩))))),
      Fragment.mapPairs E
          (l.map (fun i =>
            ((Sum.inl ⟨m + i.val, by have := i.isLt; omega⟩ :
                Fin (0 + (m + n)) ⊕ Fin (m + n + 0)),
             Sum.inr ⟨m + i.val, by have := i.isLt; omega⟩))) =
        Fragment.liftPairs _ _ hsep
  | [], _ => rfl
  | i :: l, hsep => by
    simp only [List.map_cons, Fragment.mapPairs,
      Fragment.liftPairs, Prod.map]
    refine congrArg₂ List.cons (Prod.ext ?_ ?_)
      (rotate_lift_nblock_aux m n p ps₀ E hE1 hE2 l _)
    · exact Subtype.ext (hE1 i.val i.isLt
        (by have := i.isLt; omega) (by have := i.isLt; omega))
    · exact Subtype.ext (hE2 i.val i.isLt
        (by have := i.isLt; omega) (by have := i.isLt; omega))

/-- The transported closure pairs of the left side are the lifted
`p`- and `m`-blocks. -/
theorem lhs_close_pairs_eq (m n p : ℕ)
    (ps₀ : List
      (((Fin (m + n) ⊕ Fin (n + p)) ⊕ Fin (m + p)) ×
        ((Fin (m + n) ⊕ Fin (n + p)) ⊕ Fin (m + p))))
    (E : (Fin (0 + (m + p)) ⊕ Fin (m + p + 0)) ≃
      Fragment.FoldSurviving
        ((Fin (m + n) ⊕ Fin (n + p)) ⊕ Fin (m + p)) ps₀)
    (hEhi1 : ∀ (ℓ : ℕ) (_ : ℓ < p) (h1 : m + ℓ < 0 + (m + p))
      (h2 : n + ℓ < n + p),
      (E (Sum.inl ⟨m + ℓ, h1⟩)).val =
        Sum.inl (Sum.inr ⟨n + ℓ, h2⟩))
    (hEhi2 : ∀ (ℓ : ℕ) (_ : ℓ < p) (h1 : m + ℓ < m + p + 0)
      (h2 : m + ℓ < m + p),
      (E (Sum.inr ⟨m + ℓ, h1⟩)).val = Sum.inr ⟨m + ℓ, h2⟩)
    (hElo1 : ∀ (i : ℕ) (_ : i < m) (h1 : i < 0 + (m + p))
      (h2 : i < m + n),
      (E (Sum.inl ⟨i, h1⟩)).val = Sum.inl (Sum.inl ⟨i, h2⟩))
    (hElo2 : ∀ (i : ℕ) (_ : i < m) (h1 : i < m + p + 0)
      (h2 : i < m + p),
      (E (Sum.inr ⟨i, h1⟩)).val = Sum.inr ⟨i, h2⟩)
    (hsep : Fragment.PairsSepAll ps₀
      (pBlock m n p ++ mBlock m n p)) :
    Fragment.mapPairs E (interfacePairs 0 (m + p) 0) =
      Fragment.liftPairs ps₀ (pBlock m n p ++ mBlock m n p)
        hsep :=
  (congrArg (Fragment.mapPairs E)
      (interfacePairs_closure_split m p)).trans
    ((mapPairs_append E (ipHigh m p) (ipLow m p)).trans
      ((congrArg₂ (· ++ ·)
        (rotate_lift_high_aux m n p ps₀ E hEhi1 hEhi2
          (List.finRange p).reverse hsep.append_left')
        (rotate_lift_low_aux m n p (m + p) (by omega) ps₀ E
          hElo1 hElo2
          (List.finRange m).reverse hsep.append_right')).trans
      (liftPairs_append ps₀ (pBlock m n p) (mBlock m n p)
        hsep).symm))

/-! ### The inner pairs of the right side -/

/-- The rotated composition interface over `K ⊔ H`, `K`-first. -/
def khPairs (m n p : ℕ) :
    List ((Fin (m + p) ⊕ Fin (n + p)) ×
      (Fin (m + p) ⊕ Fin (n + p))) :=
  (List.finRange p).reverse.map (fun ℓ =>
    (Sum.inl ⟨m + ℓ.val, by have := ℓ.isLt; omega⟩,
     Sum.inr ⟨n + ℓ.val, by have := ℓ.isLt; omega⟩))

/-- The rotated composition interface over `K ⊔ H`, `H`-first. -/
def hkPairs (m n p : ℕ) :
    List ((Fin (m + p) ⊕ Fin (n + p)) ×
      (Fin (m + p) ⊕ Fin (n + p))) :=
  (List.finRange p).reverse.map (fun ℓ =>
    (Sum.inr ⟨n + ℓ.val, by have := ℓ.isLt; omega⟩,
     Sum.inl ⟨m + ℓ.val, by have := ℓ.isLt; omega⟩))

/-- The two orientations are component swaps of each other. -/
theorem hkPairs_swap (m n p : ℕ) :
    (hkPairs m n p).map Prod.swap = khPairs m n p := by
  unfold hkPairs khPairs
  rw [List.map_map]
  rfl

/-- The `H`-first pairs are well-formed. -/
theorem hkPairs_wf (m n p : ℕ) :
    Fragment.PairsWF (hkPairs m n p) := by
  unfold Fragment.PairsWF hkPairs
  rw [List.flatMap_map, List.nodup_flatMap]
  refine ⟨fun k _ => by simp, ?_⟩
  rw [List.pairwise_reverse]
  refine (List.nodup_finRange p).pairwise_of_forall_ne ?_
  intro k _ j _ hkj x hxj hxk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hxj hxk
  rcases hxj with rfl | rfl <;> rcases hxk with h | h <;>
    (simp only [Sum.inl.injEq, Sum.inr.injEq, Fin.mk.injEq,
      reduceCtorEq] at h <;>
     exact hkj (Fin.ext (by omega)).symm)

/-- The transpose-pullback of the rotated interface is the
`K`-first pair list (generalized over the index list). -/
private theorem kh_pullback_aux (m n p : ℕ) :
    ∀ (l : List (Fin p)),
      Fragment.mapPairs
          (_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin (m + p)))
            (transposeEquiv n p)).symm
          (l.map (fun ℓ =>
            ((Sum.inl ⟨m + ℓ.val, by have := ℓ.isLt; omega⟩ :
                Fin (m + p) ⊕ Fin (p + n)),
             Sum.inr ⟨ℓ.val, by have := ℓ.isLt; omega⟩))) =
        l.map (fun ℓ =>
          (Sum.inl ⟨m + ℓ.val, by have := ℓ.isLt; omega⟩,
           Sum.inr ⟨n + ℓ.val, by have := ℓ.isLt; omega⟩))
  | [] => rfl
  | ℓ :: l => by
    simp only [List.map_cons, Fragment.mapPairs, Prod.map]
    refine congrArg₂ List.cons (Prod.ext rfl ?_) (kh_pullback_aux m n p l)
    change Sum.inr ((transposeEquiv n p).symm ⟨ℓ.val, _⟩) = _
    exact congrArg Sum.inr
      (transposeEquiv_symm_low n p ℓ.val ℓ.isLt
        (by have := ℓ.isLt; omega) (by have := ℓ.isLt; omega))

/-- The transpose-pullback of the rotated interface is the
`K`-first pair list. -/
theorem kh_pullback (m n p : ℕ) :
    Fragment.mapPairs
        (_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin (m + p)))
          (transposeEquiv n p)).symm
        (interfacePairs m p n) = khPairs m n p :=
  kh_pullback_aux m n p (List.finRange p).reverse

/-- The associativity-and-commutativity ambient bridge. -/
noncomputable def rotBridge (m n p : ℕ) :
    (Fin (m + n) ⊕ (Fin (m + p) ⊕ Fin (n + p))) ≃
      ((Fin (m + n) ⊕ Fin (n + p)) ⊕ Fin (m + p)) :=
  (_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin (m + n)))
      (_root_.Equiv.sumComm (Fin (m + p)) (Fin (n + p)))).trans
    (_root_.Equiv.sumAssoc (Fin (m + n)) (Fin (n + p))
      (Fin (m + p))).symm

/-- The bridge-pullback of the embedded `H`-first pairs is the
`p`-block (generalized over the index list). -/
private theorem rot_ground_aux (m n p : ℕ) :
    ∀ (l : List (Fin p)),
      Fragment.mapPairs ((rotBridge m n p).symm).symm
          ((l.map (fun ℓ =>
            ((Sum.inr ⟨n + ℓ.val, by have := ℓ.isLt; omega⟩ :
                Fin (m + p) ⊕ Fin (n + p)),
             Sum.inl ⟨m + ℓ.val, by have := ℓ.isLt; omega⟩))).map
            (Prod.map Sum.inr Sum.inr)) =
        l.map (fun ℓ =>
          (Sum.inl (Sum.inr ⟨n + ℓ.val, by have := ℓ.isLt; omega⟩),
           Sum.inr ⟨m + ℓ.val, by have := ℓ.isLt; omega⟩))
  | [] => rfl
  | ℓ :: l => by
    simp only [List.map_cons, Fragment.mapPairs, Prod.map]
    exact congrArg₂ List.cons rfl (rot_ground_aux m n p l)

/-- The bridge-pullback of the embedded `H`-first pairs is the
`p`-block. -/
theorem rot_ground (m n p : ℕ) :
    Fragment.mapPairs ((rotBridge m n p).symm).symm
        (Fragment.inrPairs (α := Fin (m + n)) (hkPairs m n p)) =
      pBlock m n p :=
  rot_ground_aux m n p (List.finRange p).reverse

/-! ### The right side's transport composites -/

/-- The inner transport of the right side: from the `H`-first
fold survivors to the boundary of the rotated composition. -/
noncomputable def rotM2 (m n p : ℕ) :
    Fragment.FoldSurviving (Fin (m + p) ⊕ Fin (n + p))
        (hkPairs m n p) ≃
      Fragment.FoldSurviving (Fin (m + p) ⊕ Fin (p + n))
        (interfacePairs m p n) :=
  (Fragment.swapFoldEquiv (hkPairs m n p)).symm.trans
    ((Fragment.foldSurvivingPermEquiv
        (show ((hkPairs m n p).map Prod.swap).Perm (khPairs m n p)
          from (hkPairs_swap m n p) ▸ List.Perm.refl _)).trans
      ((Fragment.foldSurvivingPermEquiv
          (show (Fragment.mapPairs
              (_root_.Equiv.sumCongr
                (_root_.Equiv.refl (Fin (m + p)))
                (transposeEquiv n p)).symm
              (interfacePairs m p n)).Perm (khPairs m n p)
            from (kh_pullback m n p) ▸
              List.Perm.refl _)).symm.trans
        ((Fragment.foldSurvivingMapEquiv
            (_root_.Equiv.sumCongr
              (_root_.Equiv.refl (Fin (m + p)))
              (transposeEquiv n p))
            (Fragment.mapPairs
              (_root_.Equiv.sumCongr
                (_root_.Equiv.refl (Fin (m + p)))
                (transposeEquiv n p)).symm
              (interfacePairs m p n))).trans
          (Fragment.foldSurvivingPermEquiv
            (show (interfacePairs m p n).Perm
                (Fragment.mapPairs
                  (_root_.Equiv.sumCongr
                    (_root_.Equiv.refl (Fin (m + p)))
                    (transposeEquiv n p))
                  (Fragment.mapPairs
                    (_root_.Equiv.sumCongr
                      (_root_.Equiv.refl (Fin (m + p)))
                      (transposeEquiv n p)).symm
                    (interfacePairs m p n)))
              from (mapPairs_symm_cancel
                (_root_.Equiv.sumCongr
                  (_root_.Equiv.refl (Fin (m + p)))
                  (transposeEquiv n p))
                (interfacePairs m p n)).symm ▸
                List.Perm.refl _)).symm)))

/-- The outer bridge transport of the right side: from the
`p`-block survivors to the embedded `H`-first fold survivors. -/
noncomputable def rotMR (m n p : ℕ) :
    Fragment.FoldSurviving
        ((Fin (m + n) ⊕ Fin (n + p)) ⊕ Fin (m + p))
        (pBlock m n p) ≃
      Fragment.FoldSurviving
        (Fin (m + n) ⊕ (Fin (m + p) ⊕ Fin (n + p)))
        (Fragment.inrPairs (α := Fin (m + n)) (hkPairs m n p)) :=
  (Fragment.foldSurvivingPermEquiv
      ((rot_ground m n p) ▸ List.Perm.refl _)).symm.trans
    ((Fragment.foldSurvivingMapEquiv (rotBridge m n p).symm
        (Fragment.mapPairs ((rotBridge m n p).symm).symm
          (Fragment.inrPairs (α := Fin (m + n))
            (hkPairs m n p)))).trans
      (Fragment.foldSurvivingPermEquiv
        ((mapPairs_symm_cancel (rotBridge m n p).symm
          (Fragment.inrPairs (α := Fin (m + n))
            (hkPairs m n p))).symm ▸
          List.Perm.refl _)).symm)

/-- The transported boundary equivalence of the right side. -/
noncomputable def rotSigma (m n p : ℕ) :
    (Fin (m + n) ⊕
      Fragment.FoldSurviving (Fin (m + p) ⊕ Fin (p + n))
        (interfacePairs m p n)) ≃
      (Fin (0 + (m + n)) ⊕ Fin (m + n + 0)) :=
  (_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin (m + n)))
      ((interfaceSurvEquiv m p n).trans finSumFinEquiv)).trans
    ((_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin (m + n)))
        (finCongr (by omega : m + n = m + n + 0))).trans
      (_root_.Equiv.sumCongr
        (finCongr (by omega : m + n = 0 + (m + n)))
        (_root_.Equiv.refl (Fin (m + n + 0)))))

/-- The composed transport of the right side's closure pairs. -/
noncomputable def rotE (m n p : ℕ) :
    (Fin (0 + (m + n)) ⊕ Fin (m + n + 0)) ≃
      Fragment.FoldSurviving
        ((Fin (m + n) ⊕ Fin (n + p)) ⊕ Fin (m + p))
        (pBlock m n p) :=
  (rotSigma m n p).symm.trans
    ((_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin (m + n)))
        (rotM2 m n p)).symm.trans
      ((Fragment.inrFoldEquiv (α := Fin (m + n))
          (hkPairs m n p)).symm.trans
        (rotMR m n p).symm))

/-- The right side's closure pairs are the lifted blocks. -/
theorem rot_pairs_lift (m n p : ℕ) :
    Fragment.mapPairs (rotE m n p)
        (interfacePairs 0 (m + n) 0) =
      Fragment.liftPairs _ _
        ((rotatePairsR_wf m n p).append_sep) :=
  (congrArg (Fragment.mapPairs (rotE m n p))
      (interfacePairs_closure_split m n)).trans
    ((mapPairs_append (rotE m n p) (ipHigh m n) (ipLow m n)).trans
      ((congrArg₂ (· ++ ·)
        (rotate_lift_nblock_aux m n p _ (rotE m n p)
          (fun i _ _ _ =>
            congrArg (fun z => ((rotBridge m n p).symm).symm z)
              (Fragment.inrFoldEquiv_symm_inl_val
                (hkPairs m n p) _))
          (fun i hi h1 h2 =>
            congrArg (fun z => ((rotBridge m n p).symm).symm z)
              ((Fragment.inrFoldEquiv_symm_inr_val (hkPairs m n p)
                ((rotM2 m n p).symm
                  (((interfaceSurvEquiv m p n).trans
                    finSumFinEquiv).symm
                    ⟨m + i, by omega⟩))).trans
                (congrArg Sum.inr
                  ((congrArg (fun w =>
                      (_root_.Equiv.sumCongr
                        (_root_.Equiv.refl (Fin (m + p)))
                        (transposeEquiv n p)).symm w)
                    (interfaceEquiv_symm_high m p n i hi
                      (by omega) (by omega))).trans
                  (congrArg Sum.inr
                    (transposeEquiv_symm_high n p i hi
                      (by omega) h2))))))
          (List.finRange n).reverse
          ((rotatePairsR_wf m n p).append_sep).append_left')
        (rotate_lift_low_aux m n p (m + n) (by omega) _
          (rotE m n p)
          (fun j _ _ _ =>
            congrArg (fun z => ((rotBridge m n p).symm).symm z)
              (Fragment.inrFoldEquiv_symm_inl_val
                (hkPairs m n p) _))
          (fun j hj h1 h2 =>
            congrArg (fun z => ((rotBridge m n p).symm).symm z)
              ((Fragment.inrFoldEquiv_symm_inr_val (hkPairs m n p)
                ((rotM2 m n p).symm
                  (((interfaceSurvEquiv m p n).trans
                    finSumFinEquiv).symm
                    ⟨j, by omega⟩))).trans
                (congrArg Sum.inr
                  (congrArg (fun w =>
                      (_root_.Equiv.sumCongr
                        (_root_.Equiv.refl (Fin (m + p)))
                        (transposeEquiv n p)).symm w)
                    (interfaceEquiv_symm_low m p n j hj
                      (by omega) (by omega))))))
          (List.finRange m).reverse
          ((rotatePairsR_wf m n p).append_sep).append_right')).trans
      (liftPairs_append _ (nBlock m n p) (mBlock m n p)
        ((rotatePairsR_wf m n p).append_sep)).symm))

/-- The right side's closure pairs, boundary stage. -/
noncomputable def rotQ1 (m n p : ℕ) :=
  Fragment.mapPairs (rotSigma m n p).symm
    (interfacePairs 0 (m + n) 0)

/-- The right side's closure pairs, inner-transport stage. -/
noncomputable def rotQ2 (m n p : ℕ) :=
  Fragment.mapPairs
    (_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin (m + n)))
      (rotM2 m n p)).symm
    (rotQ1 m n p)

/-- The right side's closure pairs, embedded-fold stage. -/
noncomputable def rotQ3 (m n p : ℕ) :=
  Fragment.mapPairs
    (Fragment.inrFoldEquiv (α := Fin (m + n))
      (hkPairs m n p)).symm
    (rotQ2 m n p)

/-- The right side's closure pairs, ambient stage. -/
noncomputable def rotQ4 (m n p : ℕ) :=
  Fragment.mapPairs (rotMR m n p).symm (rotQ3 m n p)

/-- The fully transported closure pairs are the lifted blocks. -/
theorem rot_q4_eq (m n p : ℕ) :
    rotQ4 m n p =
      Fragment.liftPairs _ _
        ((rotatePairsR_wf m n p).append_sep) := by
  change Fragment.mapPairs (rotMR m n p).symm
      (Fragment.mapPairs
        (Fragment.inrFoldEquiv (α := Fin (m + n))
          (hkPairs m n p)).symm
        (Fragment.mapPairs
          (_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin (m + n)))
            (rotM2 m n p)).symm
          (Fragment.mapPairs (rotSigma m n p).symm
            (interfacePairs 0 (m + n) 0)))) = _
  rw [mapPairs_mapPairs, mapPairs_mapPairs, mapPairs_mapPairs]
  exact rot_pairs_lift m n p

/-! ### The left side, normalized -/

/-- The combined pair list of the left side, embedded form. -/
theorem lhsCA_wf (m n p : ℕ) :
    Fragment.PairsWF
      (Fragment.inlPairs (interfacePairs m n p) ++
        (pBlock m n p ++ mBlock m n p)) :=
  (congrArg (· ++ (pBlock m n p ++ mBlock m n p))
    (nBlock_eq_inlPairs m n p)) ▸ rotatePairsL_wf m n p

/-- The transported boundary equivalence of the left side. -/
noncomputable def lhsSigma (m n p : ℕ) :
    (Fragment.FoldSurviving (Fin (m + n) ⊕ Fin (n + p))
        (interfacePairs m n p) ⊕ Fin (m + p)) ≃
      (Fin (0 + (m + p)) ⊕ Fin (m + p + 0)) :=
  (_root_.Equiv.sumCongr
      ((interfaceSurvEquiv m n p).trans finSumFinEquiv)
      (_root_.Equiv.refl (Fin (m + p)))).trans
    ((_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin (m + p)))
        (finCongr (by omega : m + p = m + p + 0))).trans
      (_root_.Equiv.sumCongr
        (finCongr (by omega : m + p = 0 + (m + p)))
        (_root_.Equiv.refl (Fin (m + p + 0)))))

/-- The composed transport of the left side's closure pairs. -/
noncomputable def lhsE (m n p : ℕ) :
    (Fin (0 + (m + p)) ⊕ Fin (m + p + 0)) ≃
      Fragment.FoldSurviving
        ((Fin (m + n) ⊕ Fin (n + p)) ⊕ Fin (m + p))
        (Fragment.inlPairs (interfacePairs m n p)) :=
  (lhsSigma m n p).symm.trans
    (Fragment.inlFoldEquiv (β := Fin (m + p))
      (interfacePairs m n p)).symm

/-- The left side's closure pairs are the lifted blocks. -/
theorem lhs_pairs_lift (m n p : ℕ) :
    Fragment.mapPairs
        (Fragment.inlFoldEquiv (β := Fin (m + p))
          (interfacePairs m n p)).symm
        (Fragment.mapPairs (lhsSigma m n p).symm
          (interfacePairs 0 (m + p) 0)) =
      Fragment.liftPairs _ _ ((lhsCA_wf m n p).append_sep) :=
  (mapPairs_mapPairs (lhsSigma m n p).symm
      (Fragment.inlFoldEquiv (β := Fin (m + p))
        (interfacePairs m n p)).symm
      (interfacePairs 0 (m + p) 0)).trans
    (lhs_close_pairs_eq m n p _ (lhsE m n p)
      (fun ℓ hℓ h1 h2 =>
        (Fragment.inlFoldEquiv_symm_inl_val _ _).trans
          (congrArg Sum.inl
            (interfaceEquiv_symm_high m n p ℓ hℓ
              (by omega) h2)))
      (fun ℓ _ _ _ =>
        Fragment.inlFoldEquiv_symm_inr_val _ _)
      (fun i hi h1 h2 =>
        (Fragment.inlFoldEquiv_symm_inl_val _ _).trans
          (congrArg Sum.inl
            (interfaceEquiv_symm_low m n p i hi
              (by omega) h2)))
      (fun i _ _ _ =>
        Fragment.inlFoldEquiv_symm_inr_val _ _)
      ((lhsCA_wf m n p).append_sep))

/-- The left side's transported closure pairs. -/
noncomputable def lhsQs1 (m n p : ℕ) :=
  Fragment.mapPairs (lhsSigma m n p).symm
    (interfacePairs 0 (m + p) 0)

/-- The left side's closure pairs in the fold survivors. -/
noncomputable def lhsQs2 (m n p : ℕ) :=
  Fragment.mapPairs
    (Fragment.inlFoldEquiv (β := Fin (m + p))
      (interfacePairs m n p)).symm
    (lhsQs1 m n p)

/-- The composed label identification of the left side. -/
noncomputable def rotateLabelL (m n p : ℕ) :
    Fragment.FoldSurviving
        ((Fin (m + n) ⊕ Fin (n + p)) ⊕ Fin (m + p))
        (Fragment.inlPairs (interfacePairs m n p) ++
          (pBlock m n p ++ mBlock m n p)) ≃
      Fin (0 + 0) :=
  ((Fragment.appendFlatten _ _
      ((lhsCA_wf m n p).append_sep)).symm.trans
    ((Fragment.foldSurvivingPermEquiv
        ((lhs_pairs_lift m n p) ▸ List.Perm.refl _)).symm.trans
      ((Fragment.foldSurvivingMapEquiv
          (Fragment.inlFoldEquiv (β := Fin (m + p))
            (interfacePairs m n p))
          (lhsQs2 m n p)).trans
        ((Fragment.foldSurvivingPermEquiv
            ((mapPairs_symm_cancel
              (Fragment.inlFoldEquiv (β := Fin (m + p))
                (interfacePairs m n p))
              (lhsQs1 m n p)).symm ▸
              List.Perm.refl _)).symm.trans
          ((Fragment.foldSurvivingMapEquiv (lhsSigma m n p)
              (lhsQs1 m n p)).trans
            ((Fragment.foldSurvivingPermEquiv
                ((mapPairs_symm_cancel (lhsSigma m n p)
                  (interfacePairs 0 (m + p) 0)).symm ▸
                  List.Perm.refl _)).symm.trans
              ((interfaceSurvEquiv 0 (m + p) 0).trans
                finSumFinEquiv)))))))

private theorem lhsQs2_wf (m n p : ℕ) :
    Fragment.PairsWF (lhsQs2 m n p) :=
  Fragment.mapPairs_wf _ _ (Fragment.mapPairs_wf _ _ (interfacePairs_wf 0 (m + p) 0))

/-- **The left side, normalized**: the closure of a composite
against `K` is iterated gluing of the three interface blocks
over the common ambient. -/
noncomputable def rotateNormalLeft {m n p : ℕ}
    (F : Fragment (Fin (m + n))) (H : Fragment (Fin (n + p)))
    (K : Fragment (Fin (m + p))) :
    (pairClose (F.compose H) K).Equiv
      ((Fragment.glueList ((F.disjUnion H).disjUnion K)
          (Fragment.inlPairs (interfacePairs m n p) ++
            (pBlock m n p ++ mBlock m n p))
          (lhsCA_wf m n p)).relabel (rotateLabelL m n p)) := by
  -- ═══════ SETUP ═══════
  -- The two intermediate folds (`N`, `X`) over the common ambient,
  -- the relabels between them, and their well-formedness data.
  let σL := lhsSigma m n p
  let iL := Fragment.inlFoldEquiv (β := Fin (m + p))
    (interfacePairs m n p)
  let wfqs1 : Fragment.PairsWF (lhsQs1 m n p) :=
    Fragment.mapPairs_wf σL.symm _ (interfacePairs_wf 0 (m + p) 0)
  let wfqs2 : Fragment.PairsWF (lhsQs2 m n p) :=
    lhsQs2_wf m n p
  let A := (F.disjUnion H).disjUnion K
  let X := Fragment.glueList A
    (Fragment.inlPairs (interfacePairs m n p))
    ((lhsCA_wf m n p).append_left)
  let N := Fragment.glueList (F.disjUnion H)
    (interfacePairs m n p) (interfacePairs_wf m n p)
  -- ═══════ STAGE 1: THE APPEND MERGE ═══════
  -- C8: the append merge.
  have C8 :=
    (Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv X (lhs_pairs_lift m n p)
        wfqs2
        (Fragment.liftPairs_wf _ _
          ((lhsCA_wf m n p).append_right)
          ((lhsCA_wf m n p).append_sep))
        ((lhs_pairs_lift m n p) ▸ List.Perm.refl _))).trans
    ((Fragment.Equiv.relabelCongr
      (Fragment.Equiv.relabelFlip
        (Fragment.glueListAppend A
          (Fragment.inlPairs (interfacePairs m n p))
          (pBlock m n p ++ mBlock m n p)
          (lhsCA_wf m n p)))
      (Fragment.foldSurvivingPermEquiv
        ((lhs_pairs_lift m n p) ▸
          List.Perm.refl _)).symm).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- C7: the fold-survivor relabelling stage.
  have C7 := (Fragment.glueListRelabel X iL (lhsQs2 m n p)
      wfqs2).trans
    ((Fragment.Equiv.relabelCongr C8
      (Fragment.foldSurvivingMapEquiv iL (lhsQs2 m n p))).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- C6: bridge the pair list back.
  have C6 := (Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv (X.relabel iL)
        (mapPairs_symm_cancel iL (lhsQs1 m n p)).symm
        wfqs1 (Fragment.mapPairs_wf iL _ wfqs2)
        ((mapPairs_symm_cancel iL (lhsQs1 m n p)).symm ▸
          List.Perm.refl _))).trans
    ((Fragment.Equiv.relabelCongr C7
      (Fragment.foldSurvivingPermEquiv
        ((mapPairs_symm_cancel iL (lhsQs1 m n p)).symm ▸
          List.Perm.refl _)).symm).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- ═══════ STAGE 2: THE EMBEDDED FOLD ═══════
  -- E4: the glued pair is the embedded fold.
  have E4 :=
    (Fragment.Equiv.relabelFlip
      (Fragment.glueListDisjUnionLeft (F.disjUnion H) K
        (interfacePairs m n p)
        (interfacePairs_wf m n p))).trans
    ((Fragment.Equiv.relabelEq _
      (_root_.Equiv.symm_symm iL)).trans
    (Fragment.Equiv.relabelCongr
      (Fragment.glueListProofIrrel A
        (Fragment.inlPairs (interfacePairs m n p))
        (Fragment.inlPairs_wf _ (interfacePairs_wf m n p))
        ((lhsCA_wf m n p).append_left)) iL))
  -- C4: transport across E4.
  have C4 := (Fragment.glueListCongr E4 (lhsQs1 m n p)
    wfqs1).trans C6
  -- C3: the boundary relabelling stage.
  have C3 := (Fragment.glueListRelabel (N.disjUnion K) σL
      (lhsQs1 m n p) wfqs1).trans
    ((Fragment.Equiv.relabelCongr C4
      (Fragment.foldSurvivingMapEquiv σL (lhsQs1 m n p))).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- C2: bridge the closure pairs.
  have C2 := (Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv ((N.disjUnion K).relabel σL)
        (mapPairs_symm_cancel σL
          (interfacePairs 0 (m + p) 0)).symm
        (interfacePairs_wf 0 (m + p) 0)
        (Fragment.mapPairs_wf σL _ wfqs1)
        ((mapPairs_symm_cancel σL
          (interfacePairs 0 (m + p) 0)).symm ▸
          List.Perm.refl _))).trans
    ((Fragment.Equiv.relabelCongr C3
      (Fragment.foldSurvivingPermEquiv
        ((mapPairs_symm_cancel σL
          (interfacePairs 0 (m + p) 0)).symm ▸
          List.Perm.refl _)).symm).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- ═══════ STAGE 3: THE CLOSURE'S OWN INTERFACE ═══════
  -- E1: peel the closure casts and normalize the composite.
  have E1 :=
    (Fragment.relabelDisjUnionLeft (F.compose H)
      (K.relabel (finCongr (by omega : m + p = m + p + 0)))
      (finCongr (by omega : m + p = 0 + (m + p)))).trans
    ((Fragment.Equiv.relabelCongr
      (Fragment.relabelDisjUnionRight (F.compose H) K
        (finCongr (by omega : m + p = m + p + 0)))
      (_root_.Equiv.sumCongr
        (finCongr (by omega : m + p = 0 + (m + p)))
        (_root_.Equiv.refl _))).trans
    ((Fragment.Equiv.relabelTrans _ _ _).trans
    ((Fragment.Equiv.relabelCongr
      ((Fragment.Equiv.disjUnionCongr (composeNormal F H)
        (Fragment.Equiv.refl K)).trans
      (Fragment.relabelDisjUnionLeft N K
        ((interfaceSurvEquiv m n p).trans finSumFinEquiv)))
      ((_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin (m + p)))
          (finCongr (by omega : m + p = m + p + 0))).trans
        (_root_.Equiv.sumCongr
          (finCongr (by omega : m + p = 0 + (m + p)))
          (_root_.Equiv.refl _)))).trans
    (Fragment.Equiv.relabelTrans _ _ _))))
  -- C1: transport the closure gluing across E1.
  have C1 := (Fragment.glueListCongr E1
    (interfacePairs 0 (m + p) 0)
    (interfacePairs_wf 0 (m + p) 0)).trans C2
  -- ═══════ ASSEMBLY ═══════
  exact (composeNormal
      ((F.compose H).relabel
        (finCongr (by omega : m + p = 0 + (m + p))))
      (K.relabel
        (finCongr (by omega : m + p = m + p + 0)))).trans
    ((Fragment.Equiv.relabelCongr C1
      ((interfaceSurvEquiv 0 (m + p) 0).trans
        finSumFinEquiv)).trans
    (Fragment.Equiv.relabelTrans _ _ _))

/-! ### The right side, normalized -/

/-- The composed label identification of the right side. -/
noncomputable def rotateLabelR (m n p : ℕ) :
    Fragment.FoldSurviving
        ((Fin (m + n) ⊕ Fin (n + p)) ⊕ Fin (m + p))
        (pBlock m n p ++ (nBlock m n p ++ mBlock m n p)) ≃
      Fin (0 + 0) :=
  ((Fragment.appendFlatten _ _
      ((rotatePairsR_wf m n p).append_sep)).symm.trans
    ((Fragment.foldSurvivingPermEquiv
        ((rot_q4_eq m n p) ▸ List.Perm.refl _)).symm.trans
      ((Fragment.foldSurvivingMapEquiv (rotMR m n p)
          (rotQ4 m n p)).trans
        ((Fragment.foldSurvivingPermEquiv
            ((mapPairs_symm_cancel (rotMR m n p)
              (rotQ3 m n p)).symm ▸
              List.Perm.refl _)).symm.trans
          ((Fragment.foldSurvivingMapEquiv
              (Fragment.inrFoldEquiv (α := Fin (m + n))
                (hkPairs m n p))
              (rotQ3 m n p)).trans
            ((Fragment.foldSurvivingPermEquiv
                ((mapPairs_symm_cancel
                  (Fragment.inrFoldEquiv (α := Fin (m + n))
                    (hkPairs m n p))
                  (rotQ2 m n p)).symm ▸
                  List.Perm.refl _)).symm.trans
              ((Fragment.foldSurvivingMapEquiv
                  (_root_.Equiv.sumCongr
                    (_root_.Equiv.refl (Fin (m + n)))
                    (rotM2 m n p))
                  (rotQ2 m n p)).trans
                ((Fragment.foldSurvivingPermEquiv
                    ((mapPairs_symm_cancel
                      (_root_.Equiv.sumCongr
                        (_root_.Equiv.refl (Fin (m + n)))
                        (rotM2 m n p))
                      (rotQ1 m n p)).symm ▸
                      List.Perm.refl _)).symm.trans
                  ((Fragment.foldSurvivingMapEquiv
                      (rotSigma m n p) (rotQ1 m n p)).trans
                    ((Fragment.foldSurvivingPermEquiv
                        ((mapPairs_symm_cancel (rotSigma m n p)
                          (interfacePairs 0 (m + n) 0)).symm ▸
                          List.Perm.refl _)).symm.trans
                      ((interfaceSurvEquiv 0 (m + n) 0).trans
                        finSumFinEquiv)))))))))))

private theorem rotQ4_wf (m n p : ℕ) :
    Fragment.PairsWF (rotQ4 m n p) :=
  Fragment.mapPairs_wf _ _ (Fragment.mapPairs_wf _ _
    (Fragment.mapPairs_wf _ _ (Fragment.mapPairs_wf _ _ (interfacePairs_wf 0 (m + n) 0))))

/-- **The right side, normalized**: the closure of `F` against
the rotated composite is iterated gluing of the three interface
blocks over the common ambient, `p`-block first. -/
noncomputable def rotateNormalRight {m n p : ℕ}
    (F : Fragment (Fin (m + n))) (H : Fragment (Fin (n + p)))
    (K : Fragment (Fin (m + p))) :
    (pairClose F
        (K.compose (H.relabel (transposeEquiv n p)))).Equiv
      ((Fragment.glueList ((F.disjUnion H).disjUnion K)
          (pBlock m n p ++ (nBlock m n p ++ mBlock m n p))
          (rotatePairsR_wf m n p)).relabel
        (rotateLabelR m n p)) := by
  -- ═══════ SETUP ═══════
  -- The intermediate folds (`XKH`, `XR`, `N₂`, `UPB`), the relabels
  -- between them, and their well-formedness certificates.
  let σR := rotSigma m n p
  let M₂ := rotM2 m n p
  let MR := rotMR m n p
  let i' := Fragment.inrFoldEquiv (α := Fin (m + n))
    (hkPairs m n p)
  let sτ := _root_.Equiv.sumCongr (_root_.Equiv.refl (Fin (m + p)))
    (transposeEquiv n p)
  let wfq1 : Fragment.PairsWF (rotQ1 m n p) :=
    Fragment.mapPairs_wf σR.symm _ (interfacePairs_wf 0 (m + n) 0)
  let wfq2 : Fragment.PairsWF (rotQ2 m n p) :=
    Fragment.mapPairs_wf
      (_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin (m + n)))
        M₂).symm _ wfq1
  let wfq3 : Fragment.PairsWF (rotQ3 m n p) :=
    Fragment.mapPairs_wf i'.symm _ wfq2
  let wfq4 : Fragment.PairsWF (rotQ4 m n p) :=
    rotQ4_wf m n p
  let A := (F.disjUnion H).disjUnion K
  let XKH := Fragment.glueList (K.disjUnion H) (hkPairs m n p)
    (hkPairs_wf m n p)
  let XR := Fragment.glueList
    (F.disjUnion (K.disjUnion H))
    (Fragment.inrPairs (α := Fin (m + n)) (hkPairs m n p))
    (Fragment.inrPairs_wf _ (hkPairs_wf m n p))
  let N₂ := Fragment.glueList
    (K.disjUnion (H.relabel (transposeEquiv n p)))
    (interfacePairs m p n) (interfacePairs_wf m p n)
  let UPB := Fragment.glueList A (pBlock m n p)
    ((rotatePairsR_wf m n p).append_left)
  let ground := Fragment.mapPairs ((rotBridge m n p).symm).symm
    (Fragment.inrPairs (α := Fin (m + n)) (hkPairs m n p))
  let wfground : Fragment.PairsWF ground :=
    Fragment.mapPairs_wf ((rotBridge m n p).symm).symm _
      (Fragment.inrPairs_wf _ (hkPairs_wf m n p))
  -- ═══════ STAGE 1: THE APPEND MERGE AND THE AMBIENT BRIDGE ═══════
  -- CR-append: the append merge.
  have CRapp :=
    (Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv UPB (rot_q4_eq m n p)
        wfq4
        (Fragment.liftPairs_wf _ _
          ((rotatePairsR_wf m n p).append_right)
          ((rotatePairsR_wf m n p).append_sep))
        ((rot_q4_eq m n p) ▸ List.Perm.refl _))).trans
    ((Fragment.Equiv.relabelCongr
      (Fragment.Equiv.relabelFlip
        (Fragment.glueListAppend A (pBlock m n p)
          (nBlock m n p ++ mBlock m n p)
          (rotatePairsR_wf m n p)))
      (Fragment.foldSurvivingPermEquiv
        ((rot_q4_eq m n p) ▸ List.Perm.refl _)).symm).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- CRX: the ambient bridge on the p-fold.
  have BE :=
    (Fragment.disjUnionAssoc F H K).trans
    ((Fragment.Equiv.relabelCongr
      ((Fragment.Equiv.disjUnionCongr (Fragment.Equiv.refl F)
        (Fragment.disjUnionComm H K)).trans
      (Fragment.relabelDisjUnionRight F (K.disjUnion H)
        (_root_.Equiv.sumComm (Fin (m + p)) (Fin (n + p)))))
      (_root_.Equiv.sumAssoc (Fin (m + n)) (Fin (n + p))
        (Fin (m + p))).symm).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  have CRX := (Fragment.glueListCongr (Fragment.Equiv.relabelFlip BE) _ _).trans
    (glueListPullRelabelTrans A (rotBridge m n p).symm
      (Fragment.inrPairs (α := Fin (m + n)) (hkPairs m n p))
      (Fragment.inrPairs_wf _ (hkPairs_wf m n p))
      (Fragment.Equiv.relabelFlip'
        (Fragment.glueListEqEquiv A (rot_ground m n p) wfground
          ((rotatePairsR_wf m n p).append_left)
          ((rot_ground m n p) ▸ List.Perm.refl _))))
  -- ═══════ STAGE 2: THE EMBEDDED FOLD ═══════
  -- CR5: transport across the bridge.
  have CR5 := (Fragment.glueListCongr CRX (rotQ3 m n p) wfq3).trans
    (glueListPullRelabelTrans UPB MR (rotQ3 m n p) wfq3 CRapp)
  -- E5: the embedded fold.
  have E5 :=
    (Fragment.Equiv.relabelFlip
      (Fragment.glueListDisjUnionRight F (K.disjUnion H)
        (hkPairs m n p) (hkPairs_wf m n p))).trans
    (Fragment.Equiv.relabelEq XR (_root_.Equiv.symm_symm i'))
  -- CR3: the embedded-fold stage.
  have CR3 := (Fragment.glueListCongr E5 (rotQ2 m n p) wfq2).trans
    (glueListPullRelabelTrans XR i' (rotQ2 m n p) wfq2 CR5)
  -- ═══════ STAGE 3: THE TRANSPOSE AND SWAP ON THE INNER FOLD ═══════
  -- E3: the inner fold across the transpose and the swap.
  have E3 := (Fragment.glueListCongr
    (Fragment.relabelDisjUnionRight K H (transposeEquiv n p)) _ _).trans
    (glueListPullRelabelTrans (K.disjUnion H) sτ (interfacePairs m p n)
      (interfacePairs_wf m p n)
      ((Fragment.Equiv.relabelFlip'
    (Fragment.glueListEqEquiv (K.disjUnion H)
      (kh_pullback m n p)
      (Fragment.mapPairs_wf sτ.symm _
        (interfacePairs_wf m p n))
      ((hkPairs_swap m n p) ▸
        Fragment.swapPairs_wf _ (hkPairs_wf m n p))
      ((kh_pullback m n p) ▸ List.Perm.refl _))).trans
  ((Fragment.Equiv.relabelCongr
    ((Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv (K.disjUnion H)
        (hkPairs_swap m n p).symm
        ((hkPairs_swap m n p) ▸
          Fragment.swapPairs_wf _ (hkPairs_wf m n p))
        (Fragment.swapPairs_wf _ (hkPairs_wf m n p))
        ((hkPairs_swap m n p).symm ▸
          List.Perm.refl _))).trans
    ((Fragment.Equiv.relabelCongr
      (Fragment.glueListSwap (K.disjUnion H)
        (hkPairs m n p) (hkPairs_wf m n p))
      (Fragment.foldSurvivingPermEquiv
        ((hkPairs_swap m n p).symm ▸
          List.Perm.refl _)).symm).trans
    (Fragment.Equiv.relabelTrans _ _ _)))
    (Fragment.foldSurvivingPermEquiv
      ((kh_pullback m n p) ▸
        List.Perm.refl _)).symm).trans
  (Fragment.Equiv.relabelTrans _ _ _))))
  -- CR2: the inner-transport stage.
  have CR2 := (Fragment.glueListCongr
    ((Fragment.Equiv.disjUnionCongr (Fragment.Equiv.refl F) E3).trans
      (Fragment.relabelDisjUnionRight F XKH M₂)) (rotQ1 m n p) wfq1).trans
    (glueListPullRelabelTrans (F.disjUnion XKH)
      (_root_.Equiv.sumCongr (_root_.Equiv.refl _) M₂)
      (rotQ1 m n p) wfq1 CR3)
  -- ═══════ STAGE 4: THE CLOSURE'S OWN INTERFACE ═══════
  -- E1: peel the closure casts and normalize the composite.
  have E1 := pairCloseAmbientEquiv F _ (composeNormal K (H.relabel (transposeEquiv n p)))
  -- CR1: transport the closure gluing.
  have CR1 := (Fragment.glueListCongr E1
    (interfacePairs 0 (m + n) 0)
    (interfacePairs_wf 0 (m + n) 0)).trans
    (glueListPullRelabelTrans (F.disjUnion N₂) σR
      (interfacePairs 0 (m + n) 0)
      (interfacePairs_wf 0 (m + n) 0) CR2)
  -- ═══════ ASSEMBLY ═══════
  exact (composeNormal
      (F.relabel (finCongr (by omega : m + n = 0 + (m + n))))
      ((K.compose (H.relabel (transposeEquiv n p))).relabel
        (finCongr (by omega : m + n = m + n + 0)))).trans
    ((Fragment.Equiv.relabelCongr CR1
      ((interfaceSurvEquiv 0 (m + n) 0).trans
        finSumFinEquiv)).trans
    (Fragment.Equiv.relabelTrans _ _ _))

/-! ### The meet -/

/-- No label survives the full triangle gluing. -/
theorem rotate_surv_empty (m n p : ℕ)
    (x : Fragment.FoldSurviving
      ((Fin (m + n) ⊕ Fin (n + p)) ⊕ Fin (m + p))
      (pBlock m n p ++ (nBlock m n p ++ mBlock m n p))) :
    False := by
  obtain ⟨xv, hxp⟩ := x
  rcases xv with (a | g) | b
  · rcases Nat.lt_or_ge a.val m with ha | ha
    · have hmem : _ ∈ pBlock m n p ++
          (nBlock m n p ++ mBlock m n p) :=
        List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr
          ((mem_mBlock m n p _).mpr ⟨⟨a.val, ha⟩, rfl⟩))))
      exact (hxp _ hmem).1
        (congrArg (fun z => Sum.inl (Sum.inl z))
          (Fin.ext (rfl : a.val = a.val)))
    · have hk : a.val - m < n := by have := a.isLt; omega
      have hmem : _ ∈ pBlock m n p ++
          (nBlock m n p ++ mBlock m n p) :=
        List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl
          ((mem_nBlock m n p _).mpr ⟨⟨a.val - m, hk⟩, rfl⟩))))
      exact (hxp _ hmem).1
        (congrArg (fun z => Sum.inl (Sum.inl z))
          (Fin.ext (show a.val = m + (a.val - m) by omega)))
  · rcases Nat.lt_or_ge g.val n with hg | hg
    · have hmem : _ ∈ pBlock m n p ++
          (nBlock m n p ++ mBlock m n p) :=
        List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl
          ((mem_nBlock m n p _).mpr ⟨⟨g.val, hg⟩, rfl⟩))))
      exact (hxp _ hmem).2
        (congrArg (fun z => Sum.inl (Sum.inr z))
          (Fin.ext (rfl : g.val = g.val)))
    · have hk : g.val - n < p := by have := g.isLt; omega
      have hmem : _ ∈ pBlock m n p ++
          (nBlock m n p ++ mBlock m n p) :=
        List.mem_append.mpr (Or.inl
          ((mem_pBlock m n p _).mpr ⟨⟨g.val - n, hk⟩, rfl⟩))
      exact (hxp _ hmem).1
        (congrArg (fun z => Sum.inl (Sum.inr z))
          (Fin.ext (show g.val = n + (g.val - n) by omega)))
  · rcases Nat.lt_or_ge b.val m with hb | hb
    · have hmem : _ ∈ pBlock m n p ++
          (nBlock m n p ++ mBlock m n p) :=
        List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr
          ((mem_mBlock m n p _).mpr ⟨⟨b.val, hb⟩, rfl⟩))))
      exact (hxp _ hmem).2
        (congrArg Sum.inr (Fin.ext (rfl : b.val = b.val)))
    · have hk : b.val - m < p := by have := b.isLt; omega
      have hmem : _ ∈ pBlock m n p ++
          (nBlock m n p ++ mBlock m n p) :=
        List.mem_append.mpr (Or.inl
          ((mem_pBlock m n p _).mpr ⟨⟨b.val - m, hk⟩, rfl⟩))
      exact (hxp _ hmem).2
        (congrArg Sum.inr
          (Fin.ext (show b.val = m + (b.val - m) by omega)))

/-- **Rotation of closures** (accompanying paper, Lemma 3.3(a) and
Lemma 3.5(a)): the closure of a composite equals the closure of
the first factor against the rotated composite. -/
noncomputable def pairCloseComposeRotate {m n p : ℕ}
    (F : Fragment (Fin (m + n))) (H : Fragment (Fin (n + p)))
    (K : Fragment (Fin (m + p))) :
    (pairClose (F.compose H) K).Equiv
      (pairClose F
        (K.compose (H.relabel (transposeEquiv n p)))) := by
  have hnb := (congrArg (· ++ (pBlock m n p ++ mBlock m n p))
    (nBlock_eq_inlPairs m n p)).symm
  have BRIDGE : (Fragment.glueList ((F.disjUnion H).disjUnion K)
      (Fragment.inlPairs (interfacePairs m n p) ++
        (pBlock m n p ++ mBlock m n p))
      (lhsCA_wf m n p)).Equiv
      ((Fragment.glueList ((F.disjUnion H).disjUnion K)
          (pBlock m n p ++ (nBlock m n p ++ mBlock m n p))
          (rotatePairsR_wf m n p)).relabel
        ((Fragment.foldSurvivingPermEquiv
            (rotatePairs_perm m n p)).symm.trans
          (Fragment.foldSurvivingPermEquiv
            (hnb ▸ List.Perm.refl _)).symm)) :=
    (Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv
        ((F.disjUnion H).disjUnion K) hnb
        (lhsCA_wf m n p) (rotatePairsL_wf m n p)
        (hnb ▸ List.Perm.refl _))).trans
    ((Fragment.Equiv.relabelCongr
      ((Fragment.glueListPerm ((F.disjUnion H).disjUnion K)
        (rotatePairs_perm m n p)
        (rotatePairsL_wf m n p)).trans
        (Fragment.Equiv.relabelCongr
          (Fragment.glueListProofIrrel
            ((F.disjUnion H).disjUnion K)
            (pBlock m n p ++ (nBlock m n p ++ mBlock m n p))
            ((rotatePairsL_wf m n p).perm
              (rotatePairs_perm m n p))
            (rotatePairsR_wf m n p))
          (Fragment.foldSurvivingPermEquiv
            (rotatePairs_perm m n p)).symm))
      (Fragment.foldSurvivingPermEquiv
        (hnb ▸ List.Perm.refl _)).symm).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  refine (rotateNormalLeft F H K).trans ?_
  refine Fragment.Equiv.trans ?_ (rotateNormalRight F H K).symm
  refine (Fragment.Equiv.relabelCongr BRIDGE
    (rotateLabelL m n p)).trans ?_
  refine (Fragment.Equiv.relabelTrans _ _ _).trans ?_
  exact Fragment.Equiv.relabelEq _
    (_root_.Equiv.ext (fun x =>
      absurd (rotate_surv_empty m n p x) not_false))

end RS
