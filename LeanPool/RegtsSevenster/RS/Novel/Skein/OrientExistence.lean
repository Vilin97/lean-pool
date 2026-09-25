/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.CanonTransport

/-!
# Orientation existence

Every boundary-relative transition system admits an orientation: the
boundary-completed walk is an involution pair, and two-colouring its
orbits by the orbit representative gives the directions.  Canonical
data therefore exist exactly when a transition system does.
-/

@[expose] public section

namespace RS


/-! ## Orientation existence

Every boundary-relative transition system admits an orientation:
complete the matching across the boundary by the path matching
(fixed-point-free by the chain-reversal parity), and two-colour the
alternating-walk orbits exactly as `buildOrientation` does — the
conjugation identity is pure group algebra of two involutions. -/

section OrientExist

open EdgeSubset

variable {α : Type} {W : Fragment α} {F : EdgeSubset W}

/-- **The path matching has no fixed points**: a chain cannot end
where it starts — folding the reversal identity into the middle
hits a pairing or matching fixed point. -/
theorem EdgeSubset.RelTransitionSystem.pathMatch_ne
    (κ : F.RelTransitionSystem) {b : W.Flag}
    (hb : b ∈ F.boundaryFlags) : κ.pathMatch b hb ≠ b := by
  intro hEq
  obtain ⟨k, -, hcont, hpm⟩ := pathMatch_chain_length κ hb
  have hrev : ∀ j, j ≤ k → iterWalk κ b j =
      W.pairing (iterWalk κ b (k - j)) := by
    intro j hj
    have h0 := iterWalk_reverse κ hcont j hj
    rw [← hpm, hEq] at h0
    exact h0
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · have h1 := hrev m (by omega)
    rw [show k - m = m from by omega] at h1
    exact W.pairing_ne (iterWalk κ b m) h1.symm
  · have h1 := hrev (m + 1) (by omega)
    rw [show k - (m + 1) = m from by omega] at h1
    have h2 : iterWalk κ b (m + 1) =
        κ.match_ (W.pairing (iterWalk κ b m)) := rfl
    have hint : W.pairing (iterWalk κ b m) ∈ F.internalFlags :=
      hcont m (by omega)
    exact κ.match_ne _ hint (h1 ▸ h2).symm

/-- Internal and boundary flags are disjoint. -/
theorem internal_not_boundary {f : W.Flag}
    (hf : f ∈ F.internalFlags) : f ∉ F.boundaryFlags := by
  intro hb
  obtain ⟨-, v, hv⟩ := mem_internalFlags_iff.mp hf
  obtain ⟨-, i, hi⟩ := Finset.mem_filter.mp hb
  rw [hv] at hi
  cases hi

/-- The matching completed across the boundary by the path
matching. -/
noncomputable def relComplete (κ : F.RelTransitionSystem)
    (f : W.Flag) : W.Flag :=
  if _hf : f ∈ F.internalFlags then κ.match_ f
  else if hb : f ∈ F.boundaryFlags then κ.pathMatch f hb
  else f

/-- The completed matching is the system's own on internal
flags. -/
theorem relComplete_internal (κ : F.RelTransitionSystem)
    {f : W.Flag} (hf : f ∈ F.internalFlags) :
    relComplete κ f = κ.match_ f := by
  unfold relComplete
  rw [dite_eq_left hf]

/-- And the path matching on boundary flags. -/
theorem relComplete_boundary (κ : F.RelTransitionSystem)
    {f : W.Flag} (hb : f ∈ F.boundaryFlags) :
    relComplete κ f = κ.pathMatch f hb := by
  unfold relComplete
  rw [dite_eq_right (fun hf => internal_not_boundary hf hb), dite_eq_left hb]

/-- Off the subset it is the identity. -/
theorem relComplete_off (κ : F.RelTransitionSystem)
    {f : W.Flag} (hf : f ∉ F.flags) : relComplete κ f = f := by
  unfold relComplete
  rw [dite_eq_right (fun h1 => hf (mem_flags_of_internalFlags F h1)),
    dite_eq_right (fun h1 => hf (mem_flags_of_boundaryFlags F h1))]

/-- The completed matching is a global involution. -/
theorem relComplete_invol (κ : F.RelTransitionSystem) :
    Function.Involutive (relComplete κ) := by
  intro f
  by_cases hf : f ∈ F.internalFlags
  · rw [relComplete_internal κ hf,
      relComplete_internal κ (κ.match_mem f hf)]
    exact κ.match_invol f hf
  · by_cases hb : f ∈ F.boundaryFlags
    · rw [relComplete_boundary κ hb,
        relComplete_boundary κ (κ.pathMatch_mem hb)]
      exact κ.pathMatch_invol hb
    · have hoff : f ∉ F.flags := by
        intro hfl
        rcases mem_internalFlags_or_boundaryFlags F hfl with
          h1 | h1
        · exact hf h1
        · exact hb h1
      rw [relComplete_off κ hoff, relComplete_off κ hoff]

/-- The completed matching preserves the participating flags. -/
theorem relComplete_mem (κ : F.RelTransitionSystem)
    {f : W.Flag} (hf : f ∈ F.flags) :
    relComplete κ f ∈ F.flags := by
  rcases mem_internalFlags_or_boundaryFlags F hf with h1 | h1
  · rw [relComplete_internal κ h1]
    exact mem_flags_of_internalFlags F (κ.match_mem f h1)
  · rw [relComplete_boundary κ h1]
    exact mem_flags_of_boundaryFlags F (κ.pathMatch_mem h1)

/-- The completed matching has no fixed points on participating
flags. -/
theorem relComplete_ne (κ : F.RelTransitionSystem)
    {f : W.Flag} (hf : f ∈ F.flags) : relComplete κ f ≠ f := by
  rcases mem_internalFlags_or_boundaryFlags F hf with h1 | h1
  · rw [relComplete_internal κ h1]
    exact κ.match_ne f h1
  · rw [relComplete_boundary κ h1]
    exact κ.pathMatch_ne h1

/-- The completed matching as a permutation of the participating
flags. -/
noncomputable def relMatchPerm (κ : F.RelTransitionSystem) :
    Equiv.Perm {f : W.Flag // f ∈ F.flags} where
  toFun x := ⟨relComplete κ x.val, relComplete_mem κ x.prop⟩
  invFun x := ⟨relComplete κ x.val, relComplete_mem κ x.prop⟩
  left_inv x := Subtype.ext (relComplete_invol κ x.val)
  right_inv x := Subtype.ext (relComplete_invol κ x.val)

/-- The completed matching as a permutation, on underlying
flags. -/
@[simp] theorem relMatchPerm_val (κ : F.RelTransitionSystem)
    (x : {f : W.Flag // f ∈ F.flags}) :
    (relMatchPerm κ x).val = relComplete κ x.val := rfl

/-- It is an involution. -/
theorem relMatchPerm_mul_self (κ : F.RelTransitionSystem) :
    relMatchPerm κ * relMatchPerm κ = 1 := by
  apply Equiv.Perm.ext
  intro x
  exact Subtype.ext (relComplete_invol κ x.val)

/-- The completed walk permutation. -/
noncomputable def relWalkPerm (κ : F.RelTransitionSystem) :
    Equiv.Perm {f : W.Flag // f ∈ F.flags} :=
  relMatchPerm κ * F.pairingPerm

/-- The walk permutation: cross the edge, then match. -/
@[simp] theorem relWalkPerm_val (κ : F.RelTransitionSystem)
    (x : {f : W.Flag // f ∈ F.flags}) :
    (relWalkPerm κ x).val =
      relComplete κ (W.pairing x.val) := by
  change (relMatchPerm κ (F.pairingPerm x)).val = _
  rw [relMatchPerm_val, EdgeSubset.pairingPerm_val]

/-- Its inverse walks the other way: match, then cross. -/
theorem relWalkPerm_inv (κ : F.RelTransitionSystem) :
    (relWalkPerm κ)⁻¹ = F.pairingPerm * relMatchPerm κ := by
  rw [relWalkPerm, mul_inv_rev, EdgeSubset.pairingPerm_inv,
    show (relMatchPerm κ)⁻¹ = relMatchPerm κ from
      mul_left_cancel (a := relMatchPerm κ)
        (by rw [mul_inv_cancel, relMatchPerm_mul_self])]

/-- The pairing conjugates the completed walk to its inverse. -/
theorem relConj (κ : F.RelTransitionSystem) :
    F.pairingPerm * relWalkPerm κ * F.pairingPerm =
      (relWalkPerm κ)⁻¹ := by
  rw [relWalkPerm_inv, relWalkPerm]
  calc F.pairingPerm * (relMatchPerm κ * F.pairingPerm) *
        F.pairingPerm
      = F.pairingPerm * relMatchPerm κ *
          (F.pairingPerm * F.pairingPerm) := by
        rw [mul_assoc, mul_assoc, mul_assoc]
    _ = F.pairingPerm * relMatchPerm κ := by
        rw [EdgeSubset.pairingPerm_mul_self, mul_one]

/-- **The mirror symmetry**: conjugating a power of the walk by the
edge pairing inverts it — traversing a chain backwards. -/
theorem relConj_zpow (κ : F.RelTransitionSystem) (n : ℤ) :
    F.pairingPerm * relWalkPerm κ ^ n * F.pairingPerm =
      relWalkPerm κ ^ (-n) := by
  have hσ_inv := EdgeSubset.pairingPerm_inv (F := F)
  calc F.pairingPerm * relWalkPerm κ ^ n * F.pairingPerm
      = F.pairingPerm * relWalkPerm κ ^ n *
          F.pairingPerm⁻¹ := by
        congr 1
        exact hσ_inv.symm
    _ = (MulAut.conj F.pairingPerm) (relWalkPerm κ ^ n) := rfl
    _ = ((MulAut.conj F.pairingPerm) (relWalkPerm κ)) ^ n :=
        map_zpow (MulAut.conj F.pairingPerm).toMonoidHom
          (relWalkPerm κ) n
    _ = (relWalkPerm κ)⁻¹ ^ n := by
        congr 1
        change F.pairingPerm * relWalkPerm κ * F.pairingPerm⁻¹ =
          (relWalkPerm κ)⁻¹
        rw [hσ_inv]
        exact relConj κ
    _ = relWalkPerm κ ^ (-n) := inv_zpow' (relWalkPerm κ) n

/-- A flag and its pairing partner are never in the same completed
walk orbit. -/
theorem relPairing_not_sameCycle (κ : F.RelTransitionSystem)
    {f : W.Flag} (hf : f ∈ F.flags) :
    ¬ (relWalkPerm κ).SameCycle ⟨f, hf⟩
      ⟨W.pairing f, F.pairing_mem f hf⟩ := by
  intro hsame
  obtain ⟨m, _hm_pos, _, hm_eq⟩ := hsame.exists_pow_eq''
  have hconj_applied : ∀ n : ℤ,
      F.pairingPerm ((relWalkPerm κ ^ n)
        (F.pairingPerm ⟨f, hf⟩)) =
        (relWalkPerm κ ^ (-n)) ⟨f, hf⟩ := fun n => by
    have h := congr_fun (congr_arg DFunLike.coe
      (relConj_zpow κ n)) ⟨f, hf⟩
    simpa only [Equiv.Perm.mul_apply] using h
  have hm' : (relWalkPerm κ ^ (m : ℤ)) ⟨f, hf⟩ =
      F.pairingPerm ⟨f, hf⟩ := by
    rw [zpow_natCast]
    exact Subtype.ext (by
      have := congrArg Subtype.val hm_eq
      simpa only [EdgeSubset.pairingPerm_val] using this)
  have hshift : ∀ n : ℤ,
      F.pairingPerm ((relWalkPerm κ ^ (n + ↑m)) ⟨f, hf⟩) =
        (relWalkPerm κ ^ (-n)) ⟨f, hf⟩ := by
    intro n
    rw [zpow_add, Equiv.Perm.mul_apply, hm']
    exact hconj_applied n
  rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
  · have key := hshift (-(j : ℤ))
    have harith : -(j : ℤ) + ↑m = (j : ℤ) := by omega
    rw [harith, neg_neg] at key
    have hval := congrArg Subtype.val key
    simp only [EdgeSubset.pairingPerm_val] at hval
    exact W.pairing_ne _ hval
  · have key := hshift (-(j : ℤ))
    have harith : -(j : ℤ) + ↑m = (j : ℤ) + 1 := by omega
    rw [harith, neg_neg] at key
    have hstep : (relWalkPerm κ ^ ((j : ℤ) + 1)) ⟨f, hf⟩ =
        relWalkPerm κ ((relWalkPerm κ ^ (j : ℤ)) ⟨f, hf⟩) := by
      conv_lhs => rw [show (j : ℤ) + 1 = 1 + (j : ℤ) from by
        ring]
      rw [zpow_add, zpow_one, Equiv.Perm.mul_apply]
    rw [hstep] at key
    set g := (relWalkPerm κ ^ (j : ℤ)) ⟨f, hf⟩
    have hval : W.pairing (relComplete κ (W.pairing g.val)) =
        g.val := by
      have := congrArg Subtype.val key
      simpa only [EdgeSubset.pairingPerm_val, relWalkPerm_val]
        using this
    have hval2 : relComplete κ (W.pairing g.val) =
        W.pairing g.val := by
      have := congrArg W.pairing hval
      rwa [W.pairing_invol] at this
    exact relComplete_ne κ (F.pairing_mem g.val g.prop) hval2

/-- An internal flag's match and its edge partner lie on the same
walk orbit. -/
theorem relMatch_sameCycle_pairing (κ : F.RelTransitionSystem)
    {f : W.Flag} (hf : f ∈ F.internalFlags) :
    (relWalkPerm κ).SameCycle
      ⟨κ.match_ f, mem_flags_of_internalFlags F
        (κ.match_mem f hf)⟩
      ⟨W.pairing f, F.pairing_mem f
        (mem_flags_of_internalFlags F hf)⟩ :=
  Equiv.Perm.SameCycle.symm ⟨1, Subtype.ext (by
    rw [zpow_one, relWalkPerm_val, W.pairing_invol,
      relComplete_internal κ hf])⟩

/-- So do the edge partner of a flag's match and the flag itself. -/
theorem relPairing_match_sameCycle (κ : F.RelTransitionSystem)
    {f : W.Flag} (hf : f ∈ F.internalFlags) :
    (relWalkPerm κ).SameCycle
      ⟨W.pairing (κ.match_ f), F.pairing_mem _
        (mem_flags_of_internalFlags F (κ.match_mem f hf))⟩
      ⟨f, mem_flags_of_internalFlags F hf⟩ :=
  ⟨1, Subtype.ext (by
    rw [zpow_one, relWalkPerm_val, W.pairing_invol,
      relComplete_internal κ (κ.match_mem f hf),
      κ.match_invol f hf])⟩

/-- `a ≠ b` flips the decidable strict comparison. -/
private theorem decide_lt_flip' {γ : Type} [LinearOrder γ]
    [DecidableRel ((· < ·) : γ → γ → Prop)]
    {a b : γ} (h : a ≠ b) : decide (a < b) = !decide (b < a) := by
  rcases lt_or_gt_of_ne h with hab | hab
  · simp [hab, show ¬ b < a from not_lt.mpr hab.le]
  · simp [hab, show ¬ a < b from not_lt.mpr hab.le]

open Classical in
/-- **Orientation existence**: every boundary-relative transition
system admits an orientation — two-colour the completed-walk
orbits by the orbit-representative comparison. -/
noncomputable def relBuildOrientation (κ : F.RelTransitionSystem) :
    κ.Orientation := by
  letI flagOrd := W.flagOrder
  letI := Classical.dec
  letI subtypeOrd : LinearOrder {f : W.Flag // f ∈ F.flags} :=
    LinearOrder.lift' Subtype.val Subtype.val_injective
  let orbitOf (x : {f : W.Flag // f ∈ F.flags}) :
      Finset {f : W.Flag // f ∈ F.flags} :=
    Finset.univ.filter (fun y => (relWalkPerm κ).SameCycle x y)
  have orbit_nonempty (x : {f : W.Flag // f ∈ F.flags}) :
      (orbitOf x).Nonempty :=
    ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Equiv.Perm.SameCycle.rfl⟩⟩
  let orbitMin (x : {f : W.Flag // f ∈ F.flags}) :
      {f : W.Flag // f ∈ F.flags} :=
    (orbitOf x).min' (orbit_nonempty x)
  have orbitMin_eq (x y : {f : W.Flag // f ∈ F.flags})
      (h : (relWalkPerm κ).SameCycle x y) :
      orbitMin x = orbitMin y := by
    simp only [orbitMin]
    congr 1
    ext z
    simp only [orbitOf, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨fun hz => h.symm.trans hz, fun hz => h.trans hz⟩
  have orbitMin_pairing_ne (x : {f : W.Flag // f ∈ F.flags}) :
      orbitMin (F.pairingPerm x) ≠ orbitMin x := by
    intro heq
    have hmin_in_x : orbitMin x ∈ orbitOf x :=
      Finset.min'_mem _ _
    have hmin_in_σx : orbitMin (F.pairingPerm x) ∈
        orbitOf (F.pairingPerm x) := Finset.min'_mem _ _
    rw [heq] at hmin_in_σx
    simp only [orbitOf, Finset.mem_filter, Finset.mem_univ,
      true_and] at hmin_in_x hmin_in_σx
    refine relPairing_not_sameCycle κ x.prop ?_
    have hx : (⟨W.pairing x.val, F.pairing_mem x.val x.prop⟩ :
        {f : W.Flag // f ∈ F.flags}) = F.pairingPerm x :=
      Subtype.ext (by simp)
    rw [show (⟨x.val, x.prop⟩ : {f : W.Flag // f ∈ F.flags}) = x
      from rfl, hx]
    exact hmin_in_x.trans hmin_in_σx.symm
  have orbitMin_match (x : {f : W.Flag // f ∈ F.flags})
      (hint : x.val ∈ F.internalFlags) :
      orbitMin ⟨κ.match_ x.val, mem_flags_of_internalFlags F
        (κ.match_mem x.val hint)⟩ =
        orbitMin (F.pairingPerm x) := by
    apply orbitMin_eq
    have h := relMatch_sameCycle_pairing κ hint
    convert h using 1
    exact Subtype.ext (by simp)
  have orbitMin_pairing_match (x : {f : W.Flag // f ∈ F.flags})
      (hint : x.val ∈ F.internalFlags) :
      orbitMin (F.pairingPerm ⟨κ.match_ x.val,
        mem_flags_of_internalFlags F (κ.match_mem x.val hint)⟩) =
        orbitMin x := by
    apply orbitMin_eq
    exact relPairing_match_sameCycle κ hint
  let isOut (g : W.Flag) : Bool :=
    if hg : g ∈ F.flags then
      decide (orbitMin (F.pairingPerm ⟨g, hg⟩) < orbitMin ⟨g, hg⟩)
    else false
  have hmatch_flip : ∀ g ∈ F.internalFlags,
      isOut (κ.match_ g) = !isOut g := by
    intro g hg
    have hgf : g ∈ F.flags := mem_flags_of_internalFlags F hg
    simp only [isOut, dite_eq_left hgf,
      dite_eq_left (mem_flags_of_internalFlags F (κ.match_mem g hg))]
    rw [orbitMin_pairing_match ⟨g, hgf⟩ hg,
      orbitMin_match ⟨g, hgf⟩ hg]
    exact decide_lt_flip' (Ne.symm (orbitMin_pairing_ne ⟨g, hgf⟩))
  have hpairing_flip : ∀ g ∈ F.internalFlags,
      W.pairing g ∈ F.internalFlags →
      isOut (W.pairing g) = !isOut g := by
    intro g hg _hpg
    have hgf : g ∈ F.flags := mem_flags_of_internalFlags F hg
    simp only [isOut, dite_eq_left hgf,
      dite_eq_left (F.pairing_mem g hgf)]
    have hσσ : F.pairingPerm ⟨W.pairing g, F.pairing_mem g hgf⟩ =
        ⟨g, hgf⟩ := Subtype.ext (by simp [W.pairing_invol g])
    have hσ_eq : (⟨W.pairing g, F.pairing_mem g hgf⟩ :
        {f : W.Flag // f ∈ F.flags}) = F.pairingPerm ⟨g, hgf⟩ :=
      Subtype.ext (by simp)
    rw [hσσ, hσ_eq]
    exact decide_lt_flip' (Ne.symm (orbitMin_pairing_ne ⟨g, hgf⟩))
  exact ⟨isOut, hmatch_flip, hpairing_flip⟩

end OrientExist

/-- **Unconditional canonicity**: every system on every subset has
a path-canonical orientation. -/
theorem nonempty_canonical_any {β : Type} [LinearOrder β]
    {V : Fragment β} {F : EdgeSubset V}
    (κ : F.RelTransitionSystem) :
    Nonempty {o : κ.Orientation // EdgeSubset.PathCanonical o} := by
  obtain ⟨o₂, hc₂⟩ := EdgeSubset.exists_pathCanonical κ
    (relBuildOrientation κ)
  exact ⟨⟨o₂, hc₂⟩⟩

/-! ## The bottom splitting

With orientation existence, canonical data reduce to bare system
existence, and the pinned term of a disjoint-union subset
factorizes side by side at the restricted systems, the value
product being threaded through the support certificates. -/

/-- Canonical data are exactly system existence. -/
theorem nonempty_canonData_iff_system {β : Type} [LinearOrder β]
    {V : Fragment β} (F : EdgeSubset V) :
    Nonempty F.CanonData ↔ Nonempty F.RelTransitionSystem := by
  constructor
  · rintro ⟨⟨κ, -⟩⟩
    exact ⟨κ⟩
  · rintro ⟨κ⟩
    obtain ⟨⟨o, hc⟩⟩ := nonempty_canonical_any κ
    exact ⟨⟨κ, o, hc⟩⟩

/-! ## The product family

The tower base as the product of the side-pinned families: the
side restrictions return the side families up to `MatchEq`, so the
bottom of the tower is side-pinned by construction — the
side-pinning covariance dissolves. -/

section ProductFamily

open EdgeSubset

variable {α β : Type}

/-- The left support transfer of a join subset. -/
theorem join_support_left [LinearOrder α] {W₁ : Fragment α} {W₂ : Fragment β}
    [instS : LinearOrder (α ⊕ β)]
    {s : Finset ((W₁.disjUnion W₂).Flag)}
    (hc : ∀ f ∈ s, (W₁.disjUnion W₂).pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc).CanonData) :
    ∃ (hcL : ∀ f ∈ leftPart s, W₁.pairing f ∈ leftPart s),
      (EdgeSubset.mk (leftPart s) hcL).Eulerian ∧
      Nonempty (EdgeSubset.mk (leftPart s) hcL).CanonData := by
  refine ⟨((pairing_closed_iff_parts s).mp hc).1, ?_, ?_⟩
  · exact ((eulerian_iff_parts s hc _
      ((pairing_closed_iff_parts s).mp hc).2).mp hE).1
  · exact (nonempty_canonData_iff_system _).mpr
      (((nonempty_canonData_iff_system _).mp hne).map
        (fun κ => leftRel κ))

/-- The right support transfer of a join subset. -/
theorem join_support_right [LinearOrder β] {W₁ : Fragment α} {W₂ : Fragment β}
    [instS : LinearOrder (α ⊕ β)]
    {s : Finset ((W₁.disjUnion W₂).Flag)}
    (hc : ∀ f ∈ s, (W₁.disjUnion W₂).pairing f ∈ s)
    (hE : (EdgeSubset.mk s hc).Eulerian)
    (hne : Nonempty (EdgeSubset.mk s hc).CanonData) :
    ∃ (hcR : ∀ f ∈ rightPart s, W₂.pairing f ∈ rightPart s),
      (EdgeSubset.mk (rightPart s) hcR).Eulerian ∧
      Nonempty (EdgeSubset.mk (rightPart s) hcR).CanonData := by
  refine ⟨((pairing_closed_iff_parts s).mp hc).2, ?_, ?_⟩
  · exact ((eulerian_iff_parts s hc
      ((pairing_closed_iff_parts s).mp hc).1 _).mp hE).2
  · exact (nonempty_canonData_iff_system _).mpr
      (((nonempty_canonData_iff_system _).mp hne).map
        (fun κ => rightRel κ))

end ProductFamily

open EdgeSubset Fragment in
/-- **Canonical data ascend the open glue.**  A lift's system glues,
and every system is orientable, so the glued subset carries canonical
data as soon as the lift does. -/
theorem nonempty_canonData_glueOpen {α : Type} [LinearOrder α]
    {W : Fragment α} {i j : α} (hij : i ≠ j)
    (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
    (s' : Finset (SurvivingFlag W i j))
    (hc' : ∀ f ∈ s', (W.gluePairOpen i j hij hopen).pairing f ∈ s')
    (hc : ∀ f ∈ liftSubsetOpen hopen s',
      W.pairing f ∈ liftSubsetOpen hopen s')
    (hne : Nonempty (EdgeSubset.mk (liftSubsetOpen hopen s')
      hc : EdgeSubset W).CanonData) :
    Nonempty (EdgeSubset.mk s' hc' : EdgeSubset
      (W.gluePairOpen i j hij hopen)).CanonData := by
  obtain ⟨⟨κ, -⟩⟩ := hne
  obtain ⟨⟨o, ho⟩⟩ := nonempty_canonical_any
    (RelTransitionSystem.glueOpen hij hopen s' hc' hc κ)
  exact ⟨⟨_, o, ho⟩⟩

end RS
