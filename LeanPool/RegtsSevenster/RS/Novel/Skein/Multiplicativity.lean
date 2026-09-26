/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.CompositionEquiv

/-!
# Multiplicativity from the rank bound at arity zero

An edge-rank-bounded parameter is automatically multiplicative over
disjoint unions: the arity-zero connection pairing has rank at most
one, its row at the empty graph is nonzero (the parameter is
normalized there), so every row is a scalar multiple of it, and
evaluating at the empty graph identifies the scalar.
-/

@[expose] public section

namespace RS

/-- Disjoint union of closed fragments. -/
noncomputable def ClosedFragment.union (W₁ W₂ : ClosedFragment) :
    ClosedFragment :=
  (W₁.disjUnion W₂).relabel (Equiv.equivOfIsEmpty _ _)

/-- The row of the arity-zero connection pairing at a fragment. -/
noncomputable def connectionRow (f : ClosedFragment → ℂ)
    (F : Fragment (Fin (0 + 0))) : Fragment (Fin (0 + 0)) → ℂ :=
  connectionMap f 0 (Finsupp.single F 1)

/-- The row at `F` evaluates to the pairing values. -/
theorem connectionRow_apply (f : ClosedFragment → ℂ)
    (F G : Fragment (Fin (0 + 0))) :
    connectionRow f F G = f (pairClose F G) := by
  simp [connectionRow, connectionMap, connectionPairing]

/-- Relabelling a closed fragment along any equivalence of empty
label types is trivial. -/
noncomputable def relabelZeroEquiv (W : Fragment (Fin 0))
    (e : Fin 0 ≃ Fin 0) : (W.relabel e).Equiv W where
  flagEquiv := Equiv.refl _
  vertexEquiv := Equiv.refl _
  attach_comm := fun f => by
    rcases ha : W.attach f with v | ℓ
    · have hval : (W.relabel e).attach f = (W.attach f).map id e := rfl
      change W.attach f = _
      rw [hval, ha]
      rfl
    · exact ℓ.elim0
  pairing_comm := fun _ => rfl
  circles_eq := rfl

/-- Composition at arity zero is the disjoint union, up to
equivalence: with no interface labels, no gluing happens, and any
two relabellings into the empty label type coincide. -/
noncomputable def composeZeroEquiv (F G : ClosedFragment) :
    ((F.compose (t := 0) (u := 0) G)).Equiv (F.union G) := by
  haveI : IsEmpty (Fin ((0:ℕ) + 0)) := ⟨fun x => absurd x.isLt (by omega)⟩
  have he : ((Equiv.sumCongr (finCongr (by omega : (0:ℕ) + 0 = 0))
        (finCongr (by omega : (0:ℕ) + 0 = 0))).trans finSumFinEquiv) =
      Equiv.equivOfIsEmpty (Fin (0 + 0) ⊕ Fin (0 + 0)) (Fin (0 + 0)) :=
    Equiv.ext (fun x => isEmptyElim x)
  have hobj : (F.disjUnion G).relabel
      ((Equiv.sumCongr (finCongr (by omega : (0:ℕ) + 0 = 0))
        (finCongr (by omega : (0:ℕ) + 0 = 0))).trans finSumFinEquiv) =
      F.union G := by
    have : Subsingleton ((Fin ((0:ℕ) + 0) ⊕ Fin ((0:ℕ) + 0)) ≃ Fin ((0:ℕ) + 0))
      :=
      ⟨fun a b => Equiv.ext fun x => isEmptyElim x⟩
    rw [he]
    exact congrArg _ (Subsingleton.elim _ _)
  exact (Fragment.Equiv.relabelTrans (F.disjUnion G) _ _).trans
    (hobj ▸ Fragment.Equiv.refl _)

/-- Union with the empty fragment on the left. -/
noncomputable def unionEmptyLeftEquiv (G : ClosedFragment) :
    (emptyClosedFragment.union G).Equiv G where
  flagEquiv := Equiv.emptySum Empty G.Flag
  vertexEquiv := Equiv.emptySum Empty G.Vertex
  attach_comm := fun f => by
    rcases f with e | g
    · exact e.elim
    · rcases ha : G.attach g with v | ℓ
      · have hval : (emptyClosedFragment.union G).attach (Sum.inr g) =
            ((G.attach g).map Sum.inr Sum.inr).map id
              (Equiv.equivOfIsEmpty (Fin 0 ⊕ Fin 0) (Fin 0)) := rfl
        change G.attach g = _
        rw [hval, ha]
        rfl
      · exact ℓ.elim0
  pairing_comm := fun f => by
    rcases f with e | g
    · exact e.elim
    · rfl
  circles_eq := Nat.zero_add _

/-- Union with the empty fragment on the right. -/
noncomputable def unionEmptyRightEquiv (W : ClosedFragment) :
    (W.union emptyClosedFragment).Equiv W where
  flagEquiv := Equiv.sumEmpty W.Flag Empty
  vertexEquiv := Equiv.sumEmpty W.Vertex Empty
  attach_comm := fun f => by
    rcases f with g | e
    · rcases ha : W.attach g with v | ℓ
      · have hval : (W.union emptyClosedFragment).attach (Sum.inl g) =
            ((W.attach g).map Sum.inl Sum.inl).map id
              (Equiv.equivOfIsEmpty (Fin 0 ⊕ Fin 0) (Fin 0)) := rfl
        change W.attach g = _
        rw [hval, ha]
        rfl
      · exact ℓ.elim0
    · exact e.elim
  pairing_comm := fun f => by
    rcases f with g | e
    · rfl
    · exact e.elim
  circles_eq := rfl

/-- **Multiplicativity from the rank bound** (Lemma 3.2): an
edge-rank-bounded parameter is multiplicative over disjoint
unions of closed fragments. -/
theorem EdgeRankParameter.val_union {R : ℕ} (f : EdgeRankParameter R)
    (W₁ W₂ : ClosedFragment) :
    f.val (W₁.union W₂) = f.val W₁ * f.val W₂ := by
  classical
  -- ═══════ The two rows ═══════
  set r₀ := connectionRow f.val emptyClosedFragment with hr₀
  set r₁ := connectionRow f.val W₁ with hr₁
  have hval : ∀ (F G : Fragment (Fin (0 + 0))),
      connectionRow f.val F G = f.val (ClosedFragment.union F G) := fun F G =>
        by
    rw [connectionRow_apply]
    exact f.iso_invariant _ _
      ((Fragment.composeCongr (relabelZeroEquiv F _)
        (relabelZeroEquiv G _)).trans (composeZeroEquiv F G))
  -- row values through the empty-union equivalences
  have h₀ : ∀ G, r₀ G = f.val G := fun G => by
    rw [hr₀, hval]
    exact f.iso_invariant _ _ (unionEmptyLeftEquiv G)
  have h₁empty : r₁ emptyClosedFragment = f.val W₁ := by
    rw [hr₁, hval]
    exact f.iso_invariant _ _ (unionEmptyRightEquiv W₁)
  have h₀ne : r₀ ≠ 0 := fun hzero => by
    have := h₀ emptyClosedFragment
    rw [hzero] at this
    simp only [Pi.zero_apply] at this
    rw [f.val_empty] at this
    exact one_ne_zero this.symm
  -- ═══════ Rank one forces dependence ═══════
  have hrank := f.rank_bounded 0
  rw [pow_zero] at hrank
  have hdep : ¬ LinearIndependent ℂ ![r₀, r₁] := by
    intro hind
    have hmem₀ : r₀ ∈ LinearMap.range (connectionMap f.val 0) :=
      ⟨Finsupp.single emptyClosedFragment 1, rfl⟩
    have hmem₁ : r₁ ∈ LinearMap.range (connectionMap f.val 0) :=
      ⟨Finsupp.single W₁ 1, rfl⟩
    have hsub : LinearIndependent ℂ
        (![⟨r₀, hmem₀⟩, ⟨r₁, hmem₁⟩] :
          Fin 2 → LinearMap.range (connectionMap f.val 0)) := by
      apply LinearIndependent.of_comp
        (LinearMap.range (connectionMap f.val 0)).subtype
      convert hind using 1
      ext i
      fin_cases i <;> rfl
    have htwo := hsub.cardinal_lift_le_rank
    rw [Cardinal.mk_fintype, Fintype.card_fin] at htwo
    have hle := htwo.trans (Cardinal.lift_le.mpr hrank)
    simp only [Cardinal.lift_one] at hle
    norm_num at hle
  -- ═══════ Extract the scalar ═══════
  rw [LinearIndependent.pair_iff' h₀ne] at hdep
  push Not at hdep
  obtain ⟨a, ha⟩ := hdep
  have hascalar : a = f.val W₁ := by
    have := congrFun ha emptyClosedFragment
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [h₀ emptyClosedFragment, f.val_empty, mul_one] at this
    rw [this, h₁empty]
  have := congrFun ha W₂
  simp only [Pi.smul_apply, smul_eq_mul] at this
  rw [h₀ W₂, hascalar] at this
  rw [hr₁, hval] at this
  exact this.symm

end RS
