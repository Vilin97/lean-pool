/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.BraidedNat

/-!
# The symmetric skein category

Kernel descents of the braiding-naturality squares, the hexagon
label identities, and the `BraidedCategory`/`SymmetricCategory`
instances on `SkeinObj f`.
-/

namespace RS

open CategoryTheory

variable {R : ℕ} (f : EdgeRankParameter R)

/-- The left braiding-naturality difference lies in the kernel. -/
theorem mem_ker_braidNatLeft {s t : ℕ} (k : ℕ)
    (x : Fragment (Fin (s + t)) →₀ ℂ) :
    composeFinsupp (s + k) (t + k) (k + t)
        (tensorFinsupp s t k k x
          (Finsupp.single (strandBundle k) 1))
        (Finsupp.single (bundleMap (transposeEquiv t k)) 1) -
      composeFinsupp (s + k) (k + s) (k + t)
        (Finsupp.single (bundleMap (transposeEquiv s k)) 1)
        (tensorFinsupp k k s t
          (Finsupp.single (strandBundle k) 1) x) ∈
      LinearMap.ker (connectionMap f.val ((s + k) + (k + t))) := by
  induction x using Finsupp.induction_linear with
  | zero =>
    simp only [map_zero, LinearMap.zero_apply, sub_zero]
    exact Submodule.zero_mem _
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply] at ha hb ⊢
    rw [show ∀ (A B C D : (Fragment (Fin ((s + k) + (k + t)))
        →₀ ℂ)), A + B - (C + D) = (A - C) + (B - D) from
      fun A B C D => by abel]
    exact Submodule.add_mem _ ha hb
  | single F c =>
    rw [tensorFinsupp_single, tensorFinsupp_single,
      composeFinsupp_single, composeFinsupp_single,
      show (c * 1) * 1 = 1 * (1 * c) from by ring]
    exact mem_ker_single_sub_of_equiv_smul f
      (braidNatLeftFrag k F) (1 * (1 * c))

/-- The right braiding-naturality difference lies in the
kernel. -/
theorem mem_ker_braidNatRight {s t : ℕ} (k : ℕ)
    (x : Fragment (Fin (s + t)) →₀ ℂ) :
    composeFinsupp (k + s) (k + t) (t + k)
        (tensorFinsupp k k s t
          (Finsupp.single (strandBundle k) 1) x)
        (Finsupp.single (bundleMap (transposeEquiv k t)) 1) -
      composeFinsupp (k + s) (s + k) (t + k)
        (Finsupp.single (bundleMap (transposeEquiv k s)) 1)
        (tensorFinsupp s t k k x
          (Finsupp.single (strandBundle k) 1)) ∈
      LinearMap.ker (connectionMap f.val ((k + s) + (t + k))) := by
  induction x using Finsupp.induction_linear with
  | zero =>
    simp only [map_zero, LinearMap.zero_apply, sub_zero]
    exact Submodule.zero_mem _
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply] at ha hb ⊢
    rw [show ∀ (A B C D : (Fragment (Fin ((k + s) + (t + k)))
        →₀ ℂ)), A + B - (C + D) = (A - C) + (B - D) from
      fun A B C D => by abel]
    exact Submodule.add_mem _ ha hb
  | single F c =>
    rw [tensorFinsupp_single, tensorFinsupp_single,
      composeFinsupp_single, composeFinsupp_single,
      show (1 * c) * 1 = 1 * (c * 1) from by ring]
    exact mem_ker_single_sub_of_equiv_smul f
      (braidNatRightFrag k F) (1 * (c * 1))

/-- **Left braiding naturality on Hom classes.** -/
theorem braidNatLeft_class {s t : ℕ} (k : ℕ)
    (p : HomSpace f.val (s + t)) :
    HomSpace.comp f (s + k) (t + k) (k + t)
        (HomSpace.tensor f s t k k p
          (HomSpace.ofFragment f.val (strandBundle k)))
        (bundleMapClass f (transposeEquiv t k)) =
      HomSpace.comp f (s + k) (k + s) (k + t)
        (bundleMapClass f (transposeEquiv s k))
        (HomSpace.tensor f k k s t
          (HomSpace.ofFragment f.val (strandBundle k)) p) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ p
  exact (Submodule.Quotient.eq _).mpr
    (mem_ker_braidNatLeft f k x)

/-- **Right braiding naturality on Hom classes.** -/
theorem braidNatRight_class {s t : ℕ} (k : ℕ)
    (p : HomSpace f.val (s + t)) :
    HomSpace.comp f (k + s) (k + t) (t + k)
        (HomSpace.tensor f k k s t
          (HomSpace.ofFragment f.val (strandBundle k)) p)
        (bundleMapClass f (transposeEquiv k t)) =
      HomSpace.comp f (k + s) (s + k) (t + k)
        (bundleMapClass f (transposeEquiv k s))
        (HomSpace.tensor f s t k k p
          (HomSpace.ofFragment f.val (strandBundle k))) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ p
  exact (Submodule.Quotient.eq _).mpr
    (mem_ker_braidNatRight f k x)

/-- The forward hexagon label identity. -/
theorem hexagonF_label (a b c : ℕ) :
    (finCongr (by omega : (a + b) + c = a + (b + c))).trans
      ((transposeEquiv a (b + c)).trans
        (finCongr (by omega : (b + c) + a = b + (c + a)))) =
    (tensorMapEquiv (transposeEquiv a b)
        (_root_.Equiv.refl (Fin c))).trans
      ((finCongr (by omega : (b + a) + c = b + (a + c))).trans
        (tensorMapEquiv (_root_.Equiv.refl (Fin b))
          (transposeEquiv a c))) := by
  refine _root_.Equiv.ext (fun x => Fin.ext ?_)
  have hx := x.isLt
  rcases Nat.lt_or_ge x.val a with h1 | h1
  · conv_lhs => rw [_root_.Equiv.trans_apply,
      _root_.Equiv.trans_apply,
      show (finCongr (by omega : (a + b) + c = a + (b + c))) x =
        ⟨x.val, by omega⟩ from Fin.ext rfl,
      transposeEquiv_low a (b + c) x.val h1 (by omega)
        (by omega)]
    conv_rhs => rw [_root_.Equiv.trans_apply,
      _root_.Equiv.trans_apply,
      show x = Fin.castAdd c (Fin.castAdd b
        ⟨x.val, by omega⟩) from Fin.ext rfl,
      tensorMapEquiv_castAdd,
      show (transposeEquiv a b) (Fin.castAdd b
        ⟨x.val, by omega⟩) = ⟨b + x.val, by omega⟩ from by
        rw [show (Fin.castAdd b ⟨x.val, by omega⟩ :
          Fin (a + b)) = ⟨x.val, by omega⟩ from Fin.ext rfl]
        exact transposeEquiv_low a b x.val h1 (by omega)
          (by omega),
      show (finCongr (by omega : (b + a) + c = b + (a + c)))
        (Fin.castAdd c ⟨b + x.val, by omega⟩) =
        Fin.natAdd b ⟨x.val, by omega⟩ from Fin.ext (by
        change b + x.val = b + x.val
        rfl),
      tensorMapEquiv_natAdd,
      transposeEquiv_low a c x.val h1 (by omega) (by omega)]
    exact (by
      change (b + c) + x.val = b + (c + x.val)
      omega)
  · rcases Nat.lt_or_ge x.val (a + b) with h2 | h2
    · conv_lhs => rw [_root_.Equiv.trans_apply,
        _root_.Equiv.trans_apply,
        show (finCongr (by omega : (a + b) + c = a + (b + c)))
          x = ⟨a + (x.val - a), by omega⟩ from Fin.ext (by
          change x.val = a + (x.val - a)
          omega),
        transposeEquiv_high a (b + c) (x.val - a) (by omega)
          (by omega) (by omega)]
      conv_rhs => rw [_root_.Equiv.trans_apply,
        _root_.Equiv.trans_apply,
        show x = Fin.castAdd c (Fin.natAdd a
          ⟨x.val - a, by omega⟩) from Fin.ext (by
          change x.val = a + (x.val - a)
          omega),
        tensorMapEquiv_castAdd,
        show (transposeEquiv a b) (Fin.natAdd a
          ⟨x.val - a, by omega⟩) = ⟨x.val - a, by omega⟩
          from by
          rw [show (Fin.natAdd a ⟨x.val - a, by omega⟩ :
            Fin (a + b)) = ⟨a + (x.val - a), by omega⟩ from
            Fin.ext rfl]
          exact transposeEquiv_high a b (x.val - a) (by omega)
            (by omega) (by omega),
        show (finCongr (by omega : (b + a) + c = b + (a + c)))
          (Fin.castAdd c ⟨x.val - a, by omega⟩) =
          Fin.castAdd (a + c) ⟨x.val - a, by omega⟩ from
          Fin.ext rfl,
        tensorMapEquiv_castAdd]
      rfl
    · conv_lhs => rw [_root_.Equiv.trans_apply,
        _root_.Equiv.trans_apply,
        show (finCongr (by omega : (a + b) + c = a + (b + c)))
          x = ⟨a + (x.val - a), by omega⟩ from Fin.ext (by
          change x.val = a + (x.val - a)
          omega),
        transposeEquiv_high a (b + c) (x.val - a) (by omega)
          (by omega) (by omega)]
      conv_rhs => rw [_root_.Equiv.trans_apply,
        _root_.Equiv.trans_apply,
        show x = Fin.natAdd (a + b)
          ⟨x.val - (a + b), by omega⟩ from Fin.ext (by
          change x.val = (a + b) + (x.val - (a + b))
          omega),
        tensorMapEquiv_natAdd,
        show ((_root_.Equiv.refl (Fin c))
          (⟨x.val - (a + b), by omega⟩ : Fin c)) =
          ⟨x.val - (a + b), by omega⟩ from rfl,
        show (finCongr (by omega : (b + a) + c = b + (a + c)))
          (Fin.natAdd (b + a) ⟨x.val - (a + b), by omega⟩) =
          Fin.natAdd b ⟨a + (x.val - (a + b)), by omega⟩ from
          Fin.ext (by
          change (b + a) + (x.val - (a + b)) =
            b + (a + (x.val - (a + b)))
          omega),
        tensorMapEquiv_natAdd,
        show (transposeEquiv a c)
          ⟨a + (x.val - (a + b)), by omega⟩ =
          ⟨x.val - (a + b), by omega⟩ from
          transposeEquiv_high a c (x.val - (a + b)) (by omega)
            (by omega) (by omega)]
      exact (by
        change x.val - a = b + (x.val - (a + b))
        omega)

/-- The reverse hexagon label identity. -/
theorem hexagonR_label (a b c : ℕ) :
    (finCongr (by omega : a + (b + c) = (a + b) + c)).trans
      ((transposeEquiv (a + b) c).trans
        (finCongr (by omega : c + (a + b) = (c + a) + b))) =
    (tensorMapEquiv (_root_.Equiv.refl (Fin a))
        (transposeEquiv b c)).trans
      ((finCongr (by omega : a + (c + b) = (a + c) + b)).trans
        (tensorMapEquiv (transposeEquiv a c)
          (_root_.Equiv.refl (Fin b)))) := by
  refine _root_.Equiv.ext (fun x => Fin.ext ?_)
  have hx := x.isLt
  rcases Nat.lt_or_ge x.val a with h1 | h1
  · conv_lhs => rw [_root_.Equiv.trans_apply,
      _root_.Equiv.trans_apply,
      show (finCongr (by omega : a + (b + c) = (a + b) + c)) x =
        ⟨x.val, by omega⟩ from Fin.ext rfl,
      transposeEquiv_low (a + b) c x.val (by omega) (by omega)
        (by omega)]
    conv_rhs => rw [_root_.Equiv.trans_apply,
      _root_.Equiv.trans_apply,
      show x = Fin.castAdd (b + c) ⟨x.val, h1⟩ from
        Fin.ext rfl,
      tensorMapEquiv_castAdd,
      show (finCongr (by omega : a + (c + b) = (a + c) + b))
        (Fin.castAdd (c + b)
          ((_root_.Equiv.refl (Fin a)) ⟨x.val, h1⟩)) =
        Fin.castAdd b (Fin.castAdd c ⟨x.val, h1⟩) from
        Fin.ext rfl,
      tensorMapEquiv_castAdd,
      show (transposeEquiv a c) (Fin.castAdd c ⟨x.val, h1⟩) =
        ⟨c + x.val, by omega⟩ from by
        rw [show (Fin.castAdd c ⟨x.val, h1⟩ : Fin (a + c)) =
          ⟨x.val, by omega⟩ from Fin.ext rfl]
        exact transposeEquiv_low a c x.val h1 (by omega)
          (by omega)]
    rfl
  · rcases Nat.lt_or_ge x.val (a + b) with h2 | h2
    · conv_lhs => rw [_root_.Equiv.trans_apply,
        _root_.Equiv.trans_apply,
        show (finCongr (by omega : a + (b + c) = (a + b) + c))
          x = ⟨x.val, by omega⟩ from Fin.ext rfl,
        transposeEquiv_low (a + b) c x.val h2 (by omega)
          (by omega)]
      conv_rhs => rw [_root_.Equiv.trans_apply,
        _root_.Equiv.trans_apply,
        show x = Fin.natAdd a ⟨x.val - a, by omega⟩ from
          Fin.ext (by
          change x.val = a + (x.val - a)
          omega),
        tensorMapEquiv_natAdd,
        show (transposeEquiv b c) ⟨x.val - a, by omega⟩ =
          ⟨c + (x.val - a), by omega⟩ from
          transposeEquiv_low b c (x.val - a) (by omega)
            (by omega) (by omega),
        show (finCongr (by omega : a + (c + b) = (a + c) + b))
          (Fin.natAdd a ⟨c + (x.val - a), by omega⟩) =
          Fin.natAdd (a + c) ⟨x.val - a, by omega⟩ from
          Fin.ext (by
          change a + (c + (x.val - a)) = (a + c) + (x.val - a)
          omega),
        tensorMapEquiv_natAdd]
      exact (by
        change c + x.val = (c + a) + (x.val - a)
        omega)
    · conv_lhs => rw [_root_.Equiv.trans_apply,
        _root_.Equiv.trans_apply,
        show (finCongr (by omega : a + (b + c) = (a + b) + c))
          x = ⟨(a + b) + (x.val - (a + b)), by omega⟩ from
          Fin.ext (by
          change x.val = (a + b) + (x.val - (a + b))
          omega),
        transposeEquiv_high (a + b) c (x.val - (a + b))
          (by omega) (by omega) (by omega)]
      conv_rhs => rw [_root_.Equiv.trans_apply,
        _root_.Equiv.trans_apply,
        show x = Fin.natAdd a ⟨x.val - a, by omega⟩ from
          Fin.ext (by
          change x.val = a + (x.val - a)
          omega),
        tensorMapEquiv_natAdd,
        show (transposeEquiv b c) ⟨x.val - a, by omega⟩ =
          ⟨x.val - a - b, by omega⟩ from by
          rw [show (⟨x.val - a, by omega⟩ : Fin (b + c)) =
            ⟨b + (x.val - a - b), by omega⟩ from Fin.ext (by
            change x.val - a = b + (x.val - a - b)
            omega)]
          exact transposeEquiv_high b c (x.val - a - b)
            (by omega) (by omega) (by omega),
        show (finCongr (by omega : a + (c + b) = (a + c) + b))
          (Fin.natAdd a ⟨x.val - a - b, by omega⟩) =
          Fin.castAdd b (Fin.natAdd a
            ⟨x.val - a - b, by omega⟩) from Fin.ext rfl,
        tensorMapEquiv_castAdd,
        show (transposeEquiv a c) (Fin.natAdd a
          ⟨x.val - a - b, by omega⟩) =
          ⟨x.val - a - b, by omega⟩ from by
          rw [show (Fin.natAdd a ⟨x.val - a - b, by omega⟩ :
            Fin (a + c)) = ⟨a + (x.val - a - b), by omega⟩
            from Fin.ext rfl]
          exact transposeEquiv_high a c (x.val - a - b)
            (by omega) (by omega) (by omega)]
      exact (by
        change x.val - (a + b) = x.val - a - b
        omega)

/-- **The braided skein category.** -/
noncomputable instance skeinBraided :
    BraidedCategory (SkeinObj f) where
  braiding X Y := skeinBraiding f X Y
  braiding_naturality_right X {Y Z} p :=
    braidNatRight_class f X.arity p
  braiding_naturality_left {X Y} p Z :=
    braidNatLeft_class f Z.arity p
  hexagon_forward X Y Z := by
    change HomSpace.comp f _ _ _
        (bundleMapClass f (finCongr _))
        (HomSpace.comp f _ _ _
          (bundleMapClass f (transposeEquiv X.arity
            (Y.arity + Z.arity)))
          (bundleMapClass f (finCongr _))) =
      HomSpace.comp f _ _ _
        (HomSpace.tensor f _ _ _ _
          (bundleMapClass f (transposeEquiv X.arity Y.arity))
          (HomSpace.ofFragment f.val (strandBundle Z.arity)))
        (HomSpace.comp f _ _ _
          (bundleMapClass f (finCongr _))
          (HomSpace.tensor f _ _ _ _
            (HomSpace.ofFragment f.val (strandBundle Y.arity))
            (bundleMapClass f (transposeEquiv X.arity
              Z.arity))))
    rw [bundleMapClass_tensor_id_right,
      bundleMapClass_tensor_id_left,
      bundleMapClass_comp, bundleMapClass_comp,
      bundleMapClass_comp, bundleMapClass_comp]
    exact bundleMapClass_congr f
      (hexagonF_label X.arity Y.arity Z.arity)
  hexagon_reverse X Y Z := by
    change HomSpace.comp f _ _ _
        (bundleMapClass f (finCongr _))
        (HomSpace.comp f _ _ _
          (bundleMapClass f (transposeEquiv
            (X.arity + Y.arity) Z.arity))
          (bundleMapClass f (finCongr _))) =
      HomSpace.comp f _ _ _
        (HomSpace.tensor f _ _ _ _
          (HomSpace.ofFragment f.val (strandBundle X.arity))
          (bundleMapClass f (transposeEquiv Y.arity Z.arity)))
        (HomSpace.comp f _ _ _
          (bundleMapClass f (finCongr _))
          (HomSpace.tensor f _ _ _ _
            (bundleMapClass f (transposeEquiv X.arity Z.arity))
            (HomSpace.ofFragment f.val
              (strandBundle Y.arity))))
    rw [bundleMapClass_tensor_id_left,
      bundleMapClass_tensor_id_right,
      bundleMapClass_comp, bundleMapClass_comp,
      bundleMapClass_comp, bundleMapClass_comp]
    exact bundleMapClass_congr f
      (hexagonR_label X.arity Y.arity Z.arity)

/-- **The symmetric skein category.** -/
noncomputable instance skeinSymmetric :
    SymmetricCategory (SkeinObj f) where
  symmetry X Y := skeinBraiding_symmetry f X Y

end RS
