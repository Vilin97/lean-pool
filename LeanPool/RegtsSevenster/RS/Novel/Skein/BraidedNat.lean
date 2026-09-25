/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.MonoidalInstance

/-!
# Braiding naturality, fragment level

Value lemmas for the tensor swap, the braiding-naturality label
meets, and the fragment-level naturality squares.
-/

namespace RS

/-! ### Values of the tensor swap -/

/-- The tensor swap on an incoming label of the left factor. -/
theorem tensorSwapEquiv_in_left (s t u v : ℕ) (i : Fin u) :
    tensorSwapEquiv s t u v
        (Fin.castAdd (v + t) (Fin.castAdd s i)) =
      Fin.castAdd (t + v) (Fin.natAdd s i) := by
  unfold tensorSwapEquiv
  rw [_root_.Equiv.trans_apply, _root_.Equiv.trans_apply,
    interleaveEquiv_symm_low_left u v s t i]
  exact interleaveEquiv_inr_low s t u v i

/-- On an incoming label of the right factor. -/
theorem tensorSwapEquiv_in_right (s t u v : ℕ) (j : Fin s) :
    tensorSwapEquiv s t u v
        (Fin.castAdd (v + t) (Fin.natAdd u j)) =
      Fin.castAdd (t + v) (Fin.castAdd u j) := by
  unfold tensorSwapEquiv
  rw [_root_.Equiv.trans_apply, _root_.Equiv.trans_apply,
    interleaveEquiv_symm_low_right u v s t j]
  exact interleaveEquiv_inl_low s t u v j

/-- On an outgoing label of the left factor. -/
theorem tensorSwapEquiv_out_left (s t u v : ℕ) (l : Fin v) :
    tensorSwapEquiv s t u v
        (Fin.natAdd (u + s) (Fin.castAdd t l)) =
      Fin.natAdd (s + u) (Fin.natAdd t l) := by
  unfold tensorSwapEquiv
  rw [_root_.Equiv.trans_apply, _root_.Equiv.trans_apply,
    interleaveEquiv_symm_high_left u v s t l]
  exact interleaveEquiv_inr_high s t u v l

/-- On an outgoing label of the right factor. -/
theorem tensorSwapEquiv_out_right (s t u v : ℕ) (m : Fin t) :
    tensorSwapEquiv s t u v
        (Fin.natAdd (u + s) (Fin.natAdd v m)) =
      Fin.natAdd (s + u) (Fin.castAdd v m) := by
  unfold tensorSwapEquiv
  rw [_root_.Equiv.trans_apply, _root_.Equiv.trans_apply,
    interleaveEquiv_symm_high_right u v s t m]
  exact interleaveEquiv_inl_high s t u v m

/-! ### The left naturality label meet -/

/-- **The left naturality square meets on labels**: swapping then
braiding the right leg relabels the same way as braiding the left
leg then swapping. -/
theorem braidNatLeft_label (s t k : ℕ) :
    (tensorSwapEquiv s t k k).trans
      (finSumFinEquiv.symm.trans
        ((_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin (s + k)))
          (transposeEquiv t k)).trans finSumFinEquiv)) =
    finSumFinEquiv.symm.trans
      ((_root_.Equiv.sumCongr (transposeEquiv s k).symm
        (_root_.Equiv.refl (Fin (k + t)))).trans
        finSumFinEquiv) := by
  refine _root_.Equiv.ext (fun x => Fin.ext ?_)
  have hx := x.isLt
  -- ═══════ THE FOUR BLOCKS OF THE LABEL RANGE ═══════
  -- The braiding moves the `k`-block past the `s`- and `t`-blocks;
  -- each block's labels are computed in turn.
  rcases Nat.lt_or_ge x.val k with h1 | h1
  · conv_lhs => rw [show x = Fin.castAdd (k + t)
        (Fin.castAdd s ⟨x.val, h1⟩) from Fin.ext rfl,
      _root_.Equiv.trans_apply,
      tensorSwapEquiv_in_left s t k k ⟨x.val, h1⟩,
      _root_.Equiv.trans_apply,
      finSumFinEquiv_symm_apply_castAdd,
      _root_.Equiv.trans_apply]
    conv_rhs => rw [show x = Fin.castAdd (k + t)
        (Fin.castAdd s ⟨x.val, h1⟩) from Fin.ext rfl,
      _root_.Equiv.trans_apply,
      finSumFinEquiv_symm_apply_castAdd,
      _root_.Equiv.trans_apply]
    change (finSumFinEquiv (Sum.inl (Fin.natAdd s
      ⟨x.val, h1⟩))).val = (finSumFinEquiv (Sum.inl
      ((transposeEquiv s k).symm (Fin.castAdd s
        ⟨x.val, h1⟩)))).val
    rw [finSumFinEquiv_apply_left, finSumFinEquiv_apply_left,
      transposeEquiv_symm,
      show (Fin.castAdd s ⟨x.val, h1⟩ : Fin (k + s)) =
        ⟨x.val, by omega⟩ from Fin.ext rfl,
      transposeEquiv_low k s x.val h1 (by omega) (by omega)]
    rfl
  · rcases Nat.lt_or_ge x.val (k + s) with h2 | h2
    · conv_lhs => rw [show x = Fin.castAdd (k + t)
          (Fin.natAdd k ⟨x.val - k, by omega⟩) from Fin.ext (by
          change x.val = k + (x.val - k)
          omega),
        _root_.Equiv.trans_apply,
        tensorSwapEquiv_in_right s t k k ⟨x.val - k, by omega⟩,
        _root_.Equiv.trans_apply,
        finSumFinEquiv_symm_apply_castAdd,
        _root_.Equiv.trans_apply]
      conv_rhs => rw [show x = Fin.castAdd (k + t)
          (Fin.natAdd k ⟨x.val - k, by omega⟩) from Fin.ext (by
          change x.val = k + (x.val - k)
          omega),
        _root_.Equiv.trans_apply,
        finSumFinEquiv_symm_apply_castAdd,
        _root_.Equiv.trans_apply]
      change (finSumFinEquiv (Sum.inl (Fin.castAdd k
        ⟨x.val - k, by omega⟩))).val = (finSumFinEquiv (Sum.inl
        ((transposeEquiv s k).symm (Fin.natAdd k
          ⟨x.val - k, by omega⟩)))).val
      rw [finSumFinEquiv_apply_left, finSumFinEquiv_apply_left,
        transposeEquiv_symm,
        show (Fin.natAdd k ⟨x.val - k, by omega⟩ :
          Fin (k + s)) = ⟨k + (x.val - k), by omega⟩ from
          Fin.ext rfl,
        transposeEquiv_high k s (x.val - k) (by omega)
          (by omega) (by omega)]
      rfl
    · rcases Nat.lt_or_ge x.val ((k + s) + k) with h3 | h3
      · conv_lhs => rw [show x = Fin.natAdd (k + s)
            (Fin.castAdd t ⟨x.val - (k + s), by omega⟩) from
            Fin.ext (by
            change x.val = (k + s) + (x.val - (k + s))
            omega),
          _root_.Equiv.trans_apply,
          tensorSwapEquiv_out_left s t k k
            ⟨x.val - (k + s), by omega⟩,
          _root_.Equiv.trans_apply,
          finSumFinEquiv_symm_apply_natAdd,
          _root_.Equiv.trans_apply]
        conv_rhs => rw [show x = Fin.natAdd (k + s)
            (Fin.castAdd t ⟨x.val - (k + s), by omega⟩) from
            Fin.ext (by
            change x.val = (k + s) + (x.val - (k + s))
            omega),
          _root_.Equiv.trans_apply,
          finSumFinEquiv_symm_apply_natAdd,
          _root_.Equiv.trans_apply]
        change (finSumFinEquiv (Sum.inr ((transposeEquiv t k)
          (Fin.natAdd t ⟨x.val - (k + s), by omega⟩)))).val =
          (finSumFinEquiv (Sum.inr (Fin.castAdd t
            ⟨x.val - (k + s), by omega⟩))).val
        rw [finSumFinEquiv_apply_right,
          finSumFinEquiv_apply_right,
          show (Fin.natAdd t ⟨x.val - (k + s), by omega⟩ :
            Fin (t + k)) = ⟨t + (x.val - (k + s)), by omega⟩
            from Fin.ext rfl,
          transposeEquiv_high t k (x.val - (k + s)) (by omega)
            (by omega) (by omega)]
        rfl
      · conv_lhs => rw [show x = Fin.natAdd (k + s)
            (Fin.natAdd k ⟨x.val - ((k + s) + k), by omega⟩)
            from Fin.ext (by
            change x.val = (k + s) + (k + (x.val - ((k + s) + k)))
            omega),
          _root_.Equiv.trans_apply,
          tensorSwapEquiv_out_right s t k k
            ⟨x.val - ((k + s) + k), by omega⟩,
          _root_.Equiv.trans_apply,
          finSumFinEquiv_symm_apply_natAdd,
          _root_.Equiv.trans_apply]
        conv_rhs => rw [show x = Fin.natAdd (k + s)
            (Fin.natAdd k ⟨x.val - ((k + s) + k), by omega⟩)
            from Fin.ext (by
            change x.val = (k + s) + (k + (x.val - ((k + s) + k)))
            omega),
          _root_.Equiv.trans_apply,
          finSumFinEquiv_symm_apply_natAdd,
          _root_.Equiv.trans_apply]
        change (finSumFinEquiv (Sum.inr ((transposeEquiv t k)
          (Fin.castAdd k
            ⟨x.val - ((k + s) + k), by omega⟩)))).val =
          (finSumFinEquiv (Sum.inr (Fin.natAdd k
            ⟨x.val - ((k + s) + k), by omega⟩))).val
        rw [finSumFinEquiv_apply_right,
          finSumFinEquiv_apply_right,
          show (Fin.castAdd k
            ⟨x.val - ((k + s) + k), by omega⟩ :
            Fin (t + k)) = ⟨x.val - ((k + s) + k), by omega⟩
            from Fin.ext rfl,
          transposeEquiv_low t k (x.val - ((k + s) + k))
            (by omega) (by omega) (by omega)]
        rfl

/-- The left braiding-naturality square, fragment level. -/
noncomputable def braidNatLeftFrag {s t : ℕ} (k : ℕ)
    (F : Fragment (Fin (s + t))) :
    ((tensorFragment F (strandBundle k)).compose
        (bundleMap (transposeEquiv t k))).Equiv
      ((bundleMap (transposeEquiv s k)).compose
        (tensorFragment (strandBundle k) F)) := by
  refine (composeBundleMap _ _).trans ?_
  refine (Fragment.Equiv.relabelCongr
    (tensorFragmentComm F (strandBundle k)) _).trans ?_
  refine (Fragment.Equiv.relabelTrans _ _ _).trans ?_
  refine Fragment.Equiv.trans ?_ (bundleMapCompose _ _).symm
  exact Fragment.Equiv.relabelEq _ (braidNatLeft_label s t k)

/-! ### The right naturality label meet -/

/-- The mirrored square, braiding on the other side. -/
theorem braidNatRight_label (s t k : ℕ) :
    (tensorSwapEquiv k k s t).trans
      (finSumFinEquiv.symm.trans
        ((_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin (k + s)))
          (transposeEquiv k t)).trans finSumFinEquiv)) =
    finSumFinEquiv.symm.trans
      ((_root_.Equiv.sumCongr (transposeEquiv k s).symm
        (_root_.Equiv.refl (Fin (t + k)))).trans
        finSumFinEquiv) := by
  refine _root_.Equiv.ext (fun x => Fin.ext ?_)
  have hx := x.isLt
  -- ═══════ THE FOUR BLOCKS OF THE LABEL RANGE ═══════
  -- As on the left, with the `k`-block moving the other way.
  rcases Nat.lt_or_ge x.val s with h1 | h1
  · conv_lhs => rw [show x = Fin.castAdd (t + k)
        (Fin.castAdd k ⟨x.val, h1⟩) from Fin.ext rfl,
      _root_.Equiv.trans_apply,
      tensorSwapEquiv_in_left k k s t ⟨x.val, h1⟩,
      _root_.Equiv.trans_apply,
      finSumFinEquiv_symm_apply_castAdd,
      _root_.Equiv.trans_apply]
    conv_rhs => rw [show x = Fin.castAdd (t + k)
        (Fin.castAdd k ⟨x.val, h1⟩) from Fin.ext rfl,
      _root_.Equiv.trans_apply,
      finSumFinEquiv_symm_apply_castAdd,
      _root_.Equiv.trans_apply]
    change (finSumFinEquiv (Sum.inl (Fin.natAdd k
      ⟨x.val, h1⟩))).val = (finSumFinEquiv (Sum.inl
      ((transposeEquiv k s).symm (Fin.castAdd k
        ⟨x.val, h1⟩)))).val
    rw [finSumFinEquiv_apply_left, finSumFinEquiv_apply_left,
      transposeEquiv_symm,
      show (Fin.castAdd k ⟨x.val, h1⟩ : Fin (s + k)) =
        ⟨x.val, by omega⟩ from Fin.ext rfl,
      transposeEquiv_low s k x.val h1 (by omega) (by omega)]
    rfl
  · rcases Nat.lt_or_ge x.val (s + k) with h2 | h2
    · conv_lhs => rw [show x = Fin.castAdd (t + k)
          (Fin.natAdd s ⟨x.val - s, by omega⟩) from Fin.ext (by
          change x.val = s + (x.val - s)
          omega),
        _root_.Equiv.trans_apply,
        tensorSwapEquiv_in_right k k s t ⟨x.val - s, by omega⟩,
        _root_.Equiv.trans_apply,
        finSumFinEquiv_symm_apply_castAdd,
        _root_.Equiv.trans_apply]
      conv_rhs => rw [show x = Fin.castAdd (t + k)
          (Fin.natAdd s ⟨x.val - s, by omega⟩) from Fin.ext (by
          change x.val = s + (x.val - s)
          omega),
        _root_.Equiv.trans_apply,
        finSumFinEquiv_symm_apply_castAdd,
        _root_.Equiv.trans_apply]
      change (finSumFinEquiv (Sum.inl (Fin.castAdd s
        ⟨x.val - s, by omega⟩))).val = (finSumFinEquiv (Sum.inl
        ((transposeEquiv k s).symm (Fin.natAdd s
          ⟨x.val - s, by omega⟩)))).val
      rw [finSumFinEquiv_apply_left, finSumFinEquiv_apply_left,
        transposeEquiv_symm,
        show (Fin.natAdd s ⟨x.val - s, by omega⟩ :
          Fin (s + k)) = ⟨s + (x.val - s), by omega⟩ from
          Fin.ext rfl,
        transposeEquiv_high s k (x.val - s) (by omega)
          (by omega) (by omega)]
      rfl
    · rcases Nat.lt_or_ge x.val ((s + k) + t) with h3 | h3
      · conv_lhs => rw [show x = Fin.natAdd (s + k)
            (Fin.castAdd k ⟨x.val - (s + k), by omega⟩) from
            Fin.ext (by
            change x.val = (s + k) + (x.val - (s + k))
            omega),
          _root_.Equiv.trans_apply,
          tensorSwapEquiv_out_left k k s t
            ⟨x.val - (s + k), by omega⟩,
          _root_.Equiv.trans_apply,
          finSumFinEquiv_symm_apply_natAdd,
          _root_.Equiv.trans_apply]
        conv_rhs => rw [show x = Fin.natAdd (s + k)
            (Fin.castAdd k ⟨x.val - (s + k), by omega⟩) from
            Fin.ext (by
            change x.val = (s + k) + (x.val - (s + k))
            omega),
          _root_.Equiv.trans_apply,
          finSumFinEquiv_symm_apply_natAdd,
          _root_.Equiv.trans_apply]
        change (finSumFinEquiv (Sum.inr ((transposeEquiv k t)
          (Fin.natAdd k ⟨x.val - (s + k), by omega⟩)))).val =
          (finSumFinEquiv (Sum.inr (Fin.castAdd k
            ⟨x.val - (s + k), by omega⟩))).val
        rw [finSumFinEquiv_apply_right,
          finSumFinEquiv_apply_right,
          show (Fin.natAdd k ⟨x.val - (s + k), by omega⟩ :
            Fin (k + t)) = ⟨k + (x.val - (s + k)), by omega⟩
            from Fin.ext rfl,
          transposeEquiv_high k t (x.val - (s + k)) (by omega)
            (by omega) (by omega)]
        rfl
      · conv_lhs => rw [show x = Fin.natAdd (s + k)
            (Fin.natAdd t ⟨x.val - ((s + k) + t), by omega⟩)
            from Fin.ext (by
            change x.val = (s + k) + (t + (x.val - ((s + k) + t)))
            omega),
          _root_.Equiv.trans_apply,
          tensorSwapEquiv_out_right k k s t
            ⟨x.val - ((s + k) + t), by omega⟩,
          _root_.Equiv.trans_apply,
          finSumFinEquiv_symm_apply_natAdd,
          _root_.Equiv.trans_apply]
        conv_rhs => rw [show x = Fin.natAdd (s + k)
            (Fin.natAdd t ⟨x.val - ((s + k) + t), by omega⟩)
            from Fin.ext (by
            change x.val = (s + k) + (t + (x.val - ((s + k) + t)))
            omega),
          _root_.Equiv.trans_apply,
          finSumFinEquiv_symm_apply_natAdd,
          _root_.Equiv.trans_apply]
        change (finSumFinEquiv (Sum.inr ((transposeEquiv k t)
          (Fin.castAdd t
            ⟨x.val - ((s + k) + t), by omega⟩)))).val =
          (finSumFinEquiv (Sum.inr (Fin.natAdd t
            ⟨x.val - ((s + k) + t), by omega⟩))).val
        rw [finSumFinEquiv_apply_right,
          finSumFinEquiv_apply_right,
          show (Fin.castAdd t
            ⟨x.val - ((s + k) + t), by omega⟩ :
            Fin (k + t)) = ⟨x.val - ((s + k) + t), by omega⟩
            from Fin.ext rfl,
          transposeEquiv_low k t (x.val - ((s + k) + t))
            (by omega) (by omega) (by omega)]
        rfl

/-- The right braiding-naturality square, fragment level. -/
noncomputable def braidNatRightFrag {s t : ℕ} (k : ℕ)
    (F : Fragment (Fin (s + t))) :
    ((tensorFragment (strandBundle k) F).compose
        (bundleMap (transposeEquiv k t))).Equiv
      ((bundleMap (transposeEquiv k s)).compose
        (tensorFragment F (strandBundle k))) := by
  refine (composeBundleMap _ _).trans ?_
  refine (Fragment.Equiv.relabelCongr
    (tensorFragmentComm (strandBundle k) F) _).trans ?_
  refine (Fragment.Equiv.relabelTrans _ _ _).trans ?_
  refine Fragment.Equiv.trans ?_ (bundleMapCompose _ _).symm
  exact Fragment.Equiv.relabelEq _ (braidNatRight_label s t k)

end RS
