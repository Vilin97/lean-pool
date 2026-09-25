/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Coordinates.BlockCanon

/-!
# The per-vertex value

The star coordinate of a block of the flipped data colouring is
the block sorting sign times the Definition 5 vertex factor's
normalised form: the canonical permutation carries the block to
the canonical colouring, whose star coordinate the functional
`hRS` evaluates.
-/

namespace RS

open CategoryTheory Finset


variable {R : ℕ} (f : EdgeRankParameter R)
variable (P : DelignePackage (SkeinObj f))
variable {k ℓ : ℕ}
variable (e : stdSuperPair k ℓ ⟶ P.ω.obj (SkeinObj.mk 1))
variable (e' : P.ω.obj (SkeinObj.mk 1) ⟶ stdSuperPair k ℓ)

-- Raised budget: the block's star coordinate is computed through
-- the transport and matched with the vertex factor.
open Classical in
/-- **The per-vertex value** (duplicate-free case): the star
coordinate of the block is the block sorting sign times the
sign-normalised Definition 5 vertex factor. -/
theorem starCoord_block_flip_nodup
    (hee' : (e' ≫ e : P.ω.obj (SkeinObj.mk 1) ⟶
      P.ω.obj (SkeinObj.mk 1)) = 𝟙 _)
    (he'e : (e ≫ e' : stdSuperPair k ℓ ⟶ stdSuperPair k ℓ) = 𝟙 _)
    (W : ClosedFragment) (F : EdgeSubset W)
    {κ : F.TransitionSystem} (o : κ.Orientation)
    (ψ : F.EvenColouring k) (φ : F.OddColouring ℓ)
    (v : Fin (ds W).length)
    (hnd : (F.oddListAt o φ (blockVertex W v)).Nodup) :
    starCoord f P e' ((ds W).get v)
      (blockRestrict (ds W)
        (cSorted W (colouringOfFlip W F o ψ φ)) v) =
    (sortSign (oddListOf (blockRestrict (ds W)
        (cSorted W (colouringOfFlip W F o ψ φ)) v)) : ℂ) *
      ((sortSign (F.oddListAt o φ (blockVertex W v)) : ℂ) *
        (hRS f P e').evalOdd
          (F.evenColoursAt ψ (blockVertex W v))
          (F.oddListAt o φ (blockVertex W v))) := by
  set b := blockRestrict (ds W)
    (cSorted W (colouringOfFlip W F o ψ φ)) v with hb
  have hnd_b : (oddListOf b).Nodup :=
    (oddListOf_blockRestrict_nodup_iff W F o ψ φ v).mpr hnd
  obtain ⟨σ, h, comp, hsign⟩ := exists_canonPerm b hnd_b
  have h1 := starCoord_perm f P e e' hee' he'e
    ((ds W).get v) σ b
  rw [comp] at h1
  rw [starCoord_cast f P e' h] at h1
  rw [hsign] at h1
  -- h1 : starCoord (canon (eM b) (oF b)) =
  --      sortSign (oddListOf b) * starCoord b
  have hident_e := evenMultisetOf_blockRestrict W F o ψ φ v
  have hident_o := oddFinsetOf_blockRestrict W F o ψ φ v
  rw [← hb] at hident_e hident_o
  have heval := evalOdd_hRS_nodup f P e'
    (F.evenColoursAt ψ (blockVertex W v))
    (F.oddListAt o φ (blockVertex W v)) hnd
  -- rewrite the canonical star coordinate into hRS terms
  have htrans : starCoord f P e'
      ((evenMultisetOf b).card + (oddFinsetOf b).card)
      (canonColouring (evenMultisetOf b) (oddFinsetOf b)) =
    starCoord f P e'
      ((F.evenColoursAt ψ (blockVertex W v)).card +
        (F.oddListAt o φ (blockVertex W v)).toFinset.card)
      (canonColouring (F.evenColoursAt ψ (blockVertex W v))
        (F.oddListAt o φ (blockVertex W v)).toFinset) := by
    exact congrArg (fun p : Multiset (Fin k) ×
        Finset (Fin (2 * ℓ)) =>
      starCoord f P e' (p.1.card + p.2.card)
        (canonColouring p.1 p.2))
      (show (evenMultisetOf b, oddFinsetOf b) =
          (F.evenColoursAt ψ (blockVertex W v),
            (F.oddListAt o φ (blockVertex W v)).toFinset)
        from Prod.ext_iff.mpr ⟨hident_e, hident_o⟩)
  have hcanon : starCoord f P e'
      ((evenMultisetOf b).card + (oddFinsetOf b).card)
      (canonColouring (evenMultisetOf b) (oddFinsetOf b)) =
    (sortSign (F.oddListAt o φ (blockVertex W v)) : ℂ) *
      (hRS f P e').evalOdd
        (F.evenColoursAt ψ (blockVertex W v))
        (F.oddListAt o φ (blockVertex W v)) := by
    rw [htrans]
    rw [heval]
    set A := (sortSign (F.oddListAt o φ
      (blockVertex W v)) : ℂ)
    set S := starCoord f P e'
      ((F.evenColoursAt ψ (blockVertex W v)).card +
        (F.oddListAt o φ (blockVertex W v)).toFinset.card)
      (canonColouring (F.evenColoursAt ψ (blockVertex W v))
        (F.oddListAt o φ (blockVertex W v)).toFinset)
    have hA : A * A = 1 := sortSign_sq _
    calc S = (A * A) * S := by
          rw [hA, one_mul]
      _ = A * (A * S) := by ring
  rw [hcanon] at h1
  -- h1 : A*(B*evalOdd-part) = sortSign(oddListOf b) * starCoord b
  have hS : (sortSign (oddListOf b) : ℂ) *
      (sortSign (oddListOf b) : ℂ) = 1 := sortSign_sq _
  calc starCoord f P e' ((ds W).get v) b
      = ((sortSign (oddListOf b) : ℂ) *
          (sortSign (oddListOf b) : ℂ)) *
          starCoord f P e' ((ds W).get v) b := by
        rw [hS, one_mul]
    _ = (sortSign (oddListOf b) : ℂ) *
          ((sortSign (oddListOf b) : ℂ) *
            starCoord f P e' ((ds W).get v) b) := by ring
    _ = (sortSign (oddListOf b) : ℂ) *
          ((sortSign (F.oddListAt o φ
              (blockVertex W v)) : ℂ) *
            (hRS f P e').evalOdd
              (F.evenColoursAt ψ (blockVertex W v))
              (F.oddListAt o φ (blockVertex W v))) := by
        rw [← h1]

-- As for the duplicate-free case, on the vanishing branch.
open Classical in
/-- **The per-vertex vanishing** (repeated case): a repeated odd
value kills the block's star coordinate. -/
theorem starCoord_block_flip_not_nodup
    (hee' : (e' ≫ e : P.ω.obj (SkeinObj.mk 1) ⟶
      P.ω.obj (SkeinObj.mk 1)) = 𝟙 _)
    (he'e : (e ≫ e' : stdSuperPair k ℓ ⟶ stdSuperPair k ℓ) = 𝟙 _)
    (W : ClosedFragment) (F : EdgeSubset W)
    {κ : F.TransitionSystem} (o : κ.Orientation)
    (ψ : F.EvenColouring k) (φ : F.OddColouring ℓ)
    (v : Fin (ds W).length)
    (hnd : ¬ (F.oddListAt o φ (blockVertex W v)).Nodup) :
    starCoord f P e' ((ds W).get v)
      (blockRestrict (ds W)
        (cSorted W (colouringOfFlip W F o ψ φ)) v) = 0 := by
  set b := blockRestrict (ds W)
    (cSorted W (colouringOfFlip W F o ψ φ)) v with hb
  have hnd_b : ¬ (oddListOf b).Nodup := fun hn =>
    hnd ((oddListOf_blockRestrict_nodup_iff W F o ψ φ v).mp
      hn)
  have hiff : ∀ j : Fin ((ds W).get v),
      j ∈ oddSlots W F v ↔ (b j).isRight = true := fun j =>
    (mem_oddSlots j).trans
      (blockRestrict_colouringOfFlip_isRight W F o ψ φ v
        j).symm
  rw [← Multiset.coe_nodup] at hnd_b
  rw [oddListOf_coe_multiset b (oddSlots W F v) hiff]
    at hnd_b
  have hattach : ((oddSlots W F v).attach.val).Nodup := by
    rw [Finset.attach_val]
    exact Multiset.Nodup.attach ((oddSlots W F v).nodup)
  have hpair : ¬ (∀ x ∈ (oddSlots W F v).attach.val,
      ∀ y ∈ (oddSlots W F v).attach.val,
      Sum.getRight (b x.val) ((hiff x.val).mp x.prop) =
        Sum.getRight (b y.val) ((hiff y.val).mp y.prop) →
        x = y) := by
    intro hinj
    exact hnd_b (Multiset.Nodup.map_on hinj hattach)
  push Not at hpair
  obtain ⟨x, -, y, -, hval, hne⟩ := hpair
  have hextract : ∀ (z : Fin k ⊕ Fin (2 * ℓ))
      (hz : z.isRight = true) (u₀ : Fin (2 * ℓ)),
      z = Sum.inr u₀ → z.getRight hz = u₀ := by
    intro z hz u₀ he
    subst he
    rfl
  have hxr : (b x.val).isRight = true :=
    (hiff x.val).mp x.prop
  have hyr : (b y.val).isRight = true :=
    (hiff y.val).mp y.prop
  have hslot_ne : x.val ≠ y.val := fun hxy =>
    hne (Subtype.ext hxy)
  obtain ⟨u, hu⟩ : ∃ u, b x.val = Sum.inr u := by
    rcases hz : b x.val with a | u
    · rw [hz] at hxr
      exact Bool.noConfusion hxr
    · exact ⟨u, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, b y.val = Sum.inr w := by
    rcases hz : b y.val with a | w
    · rw [hz] at hyr
      exact Bool.noConfusion hyr
    · exact ⟨w, rfl⟩
  have huw : u = w := by
    have h1 := hextract _ ((hiff x.val).mp x.prop) u hu
    have h2 := hextract _ ((hiff y.val).mp y.prop) w hw
    rw [h1, h2] at hval
    exact hval
  have hbeq : b x.val = b y.val := by
    rw [hu, hw, huw]
  rcases lt_or_gt_of_ne (fun h => hslot_ne (Fin.ext h) :
      x.val.val ≠ y.val.val) with hlt | hgt
  · exact starCoord_repeat_zero f P e e' hee' he'e b
      x.val y.val hlt hxr hbeq
  · exact starCoord_repeat_zero f P e e' hee' he'e b
      y.val x.val hgt hyr hbeq.symm

end RS
