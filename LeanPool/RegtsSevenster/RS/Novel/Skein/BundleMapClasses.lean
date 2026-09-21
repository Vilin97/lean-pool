/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.SkeinCatInstance
import LeanPool.RegtsSevenster.RS.Novel.Skein.BundleTensor
import LeanPool.RegtsSevenster.RS.Novel.Skein.ComposeRelabel

/-!
# The bundle-map calculus

The strand bundle implementing an arbitrary label equivalence
`e : Fin n ≃ Fin m`: strand `k` runs from input `k` to output
`e k`.  These fragments and their Hom classes provide all the
structural morphisms of the monoidal skein category — associators
and unitors (`e` a cast) and the braiding (`e` a block
transpose) — and satisfy a single composition law: composing the
bundle maps of `e₁` and `e₂` is the bundle map of `e₁.trans e₂`.
The proof forces the arities equal (a `Fin`-equivalence fixes the
cardinality), after which everything is permutation-fragment
algebra.  Every coherence diagram of the monoidal assembly
collapses through this law into an equality of label
equivalences.
-/

namespace RS

/-- The outgoing label map of a bundle: fix the inputs, apply `e`
to the outputs. -/
def outMapEquiv {n m : ℕ} (e : Fin n ≃ Fin m) :
    Fin (n + n) ≃ Fin (n + m) :=
  finSumFinEquiv.symm.trans
    ((_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin n)) e).trans
      finSumFinEquiv)

/-- The bundle map of a label equivalence: strand `k` joins input
`k` to output `e k`. -/
noncomputable def bundleMap {n m : ℕ} (e : Fin n ≃ Fin m) :
    Fragment (Fin (n + m)) :=
  (strandBundle n).relabel (outMapEquiv e)

/-- The bundle map of the identity is the strand bundle. -/
noncomputable def bundleMapRefl (n : ℕ) :
    (bundleMap (_root_.Equiv.refl (Fin n))).Equiv
      (strandBundle n) :=
  (Fragment.Equiv.relabelEq (strandBundle n)
    (_root_.Equiv.ext (fun x => by
      show finSumFinEquiv
        ((_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin n))
          (_root_.Equiv.refl (Fin n))) (finSumFinEquiv.symm x)) =
        x
      rw [show (_root_.Equiv.sumCongr
          (_root_.Equiv.refl (Fin n))
          (_root_.Equiv.refl (Fin n))) =
          _root_.Equiv.refl (Fin n ⊕ Fin n) from
        _root_.Equiv.ext (fun y => by
          rcases y with y | y <;> rfl)]
      exact finSumFinEquiv.apply_symm_apply x))).trans
    (Fragment.Equiv.relabelRefl (strandBundle n))

/-- **The composition law of bundle maps.** -/
noncomputable def bundleMapComp {n m p : ℕ}
    (e₁ : Fin n ≃ Fin m) (e₂ : Fin m ≃ Fin p) :
    ((bundleMap e₁).compose (bundleMap e₂)).Equiv
      (bundleMap (e₁.trans e₂)) := by
  have hnm : n = m := by
    have h := Fintype.card_congr e₁
    simpa using h
  subst hnm
  have hnp : n = p := by
    have h := Fintype.card_congr e₂
    simpa using h
  subst hnp
  refine Fragment.Equiv.trans
    (Fragment.composeCongr
      (permFragmentRelabelOutPerm e₁).symm
      (permFragmentRelabelOutPerm e₂).symm) ?_
  refine (permFragmentCompose e₁ e₂).trans ?_
  exact (permFragmentRelabelOutPerm (e₂ * e₁)).trans
    (Fragment.Equiv.relabelEq _
      (_root_.Equiv.ext (fun x => rfl)))

/-- Tensoring relabelled fragments is relabelling the tensor by
the interleave-conjugated sum. -/
noncomputable def tensorFragmentRelabel
    {s t u v s' t' u' v' : ℕ}
    (X : Fragment (Fin (s + t))) (z : Fragment (Fin (u + v)))
    (r₁ : Fin (s + t) ≃ Fin (s' + t'))
    (r₂ : Fin (u + v) ≃ Fin (u' + v')) :
    (tensorFragment (X.relabel r₁) (z.relabel r₂)).Equiv
      ((tensorFragment X z).relabel
        ((interleaveEquiv s t u v).symm.trans
          ((_root_.Equiv.sumCongr r₁ r₂).trans
            (interleaveEquiv s' t' u' v')))) := by
  show (((X.relabel r₁).disjUnion (z.relabel r₂)).relabel
    (interleaveEquiv s' t' u' v')).Equiv _
  refine (Fragment.Equiv.relabelCongr
    ((Fragment.relabelDisjUnionLeft X (z.relabel r₂) r₁).trans
      ((Fragment.Equiv.relabelCongr
        (Fragment.relabelDisjUnionRight X z r₂) _).trans
        (Fragment.Equiv.relabelTrans _ _ _))) _).trans ?_
  refine (Fragment.Equiv.relabelTrans _ _ _).trans ?_
  show ((X.disjUnion z).relabel _).Equiv
    (((X.disjUnion z).relabel (interleaveEquiv s t u v)).relabel _)
  refine Fragment.Equiv.trans ?_
    (Fragment.Equiv.relabelTrans _ _ _).symm
  exact Fragment.Equiv.relabelEq _
    (_root_.Equiv.ext (fun x => by
      simp only [_root_.Equiv.trans_apply,
        _root_.Equiv.symm_apply_apply]
      rcases x with x | x <;> rfl))

/-- The outgoing map fixes input slots. -/
theorem outMapEquiv_castAdd {n m : ℕ} (e : Fin n ≃ Fin m)
    (i : Fin n) :
    outMapEquiv e (Fin.castAdd n i) = Fin.castAdd m i := by
  unfold outMapEquiv
  rw [_root_.Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd]
  exact finSumFinEquiv_apply_left i

/-- The outgoing map acts on output slots. -/
theorem outMapEquiv_natAdd {n m : ℕ} (e : Fin n ≃ Fin m)
    (k : Fin n) :
    outMapEquiv e (Fin.natAdd n k) = Fin.natAdd n (e k) := by
  unfold outMapEquiv
  rw [_root_.Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd]
  exact finSumFinEquiv_apply_right (e k)

/-- The sum of two label equivalences, on concatenated blocks. -/
def tensorMapEquiv {n₁ m₁ n₂ m₂ : ℕ}
    (e₁ : Fin n₁ ≃ Fin m₁) (e₂ : Fin n₂ ≃ Fin m₂) :
    Fin (n₁ + n₂) ≃ Fin (m₁ + m₂) :=
  finSumFinEquiv.symm.trans
    ((_root_.Equiv.sumCongr e₁ e₂).trans finSumFinEquiv)

/-- The tensor of two label equivalences on a left label. -/
theorem tensorMapEquiv_castAdd {n₁ m₁ n₂ m₂ : ℕ}
    (e₁ : Fin n₁ ≃ Fin m₁) (e₂ : Fin n₂ ≃ Fin m₂) (i : Fin n₁) :
    tensorMapEquiv e₁ e₂ (Fin.castAdd n₂ i) =
      Fin.castAdd m₂ (e₁ i) := by
  unfold tensorMapEquiv
  rw [_root_.Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd]
  exact finSumFinEquiv_apply_left (e₁ i)

/-- And on a right label. -/
theorem tensorMapEquiv_natAdd {n₁ m₁ n₂ m₂ : ℕ}
    (e₁ : Fin n₁ ≃ Fin m₁) (e₂ : Fin n₂ ≃ Fin m₂) (j : Fin n₂) :
    tensorMapEquiv e₁ e₂ (Fin.natAdd n₁ j) =
      Fin.natAdd m₁ (e₂ j) := by
  unfold tensorMapEquiv
  rw [_root_.Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd]
  exact finSumFinEquiv_apply_right (e₂ j)

/-- **The tensor law of bundle maps**: the tensor of two bundle
maps is the bundle map of the block sum. -/
noncomputable def bundleMapTensor {n₁ m₁ n₂ m₂ : ℕ}
    (e₁ : Fin n₁ ≃ Fin m₁) (e₂ : Fin n₂ ≃ Fin m₂) :
    (tensorFragment (bundleMap e₁) (bundleMap e₂)).Equiv
      (bundleMap (tensorMapEquiv e₁ e₂)) := by
  refine (tensorFragmentRelabel (strandBundle n₁)
    (strandBundle n₂) (outMapEquiv e₁) (outMapEquiv e₂)).trans
    ?_
  refine (Fragment.Equiv.relabelCongr
    (strandBundleTensor n₁ n₂).symm _).trans ?_
  refine Fragment.Equiv.relabelEq _ (_root_.Equiv.ext (fun x => ?_))
  rcases Nat.lt_or_ge x.val (n₁ + n₂) with hx | hx
  · rcases Nat.lt_or_ge x.val n₁ with hx1 | hx1
    · rw [show x = Fin.castAdd (n₁ + n₂)
          (Fin.castAdd n₂ ⟨x.val, hx1⟩) from Fin.ext rfl,
        _root_.Equiv.trans_apply,
        interleaveEquiv_symm_low_left n₁ n₁ n₂ n₂ ⟨x.val, hx1⟩,
        _root_.Equiv.trans_apply, _root_.Equiv.sumCongr_apply,
        Sum.map_inl, outMapEquiv_castAdd e₁,
        interleaveEquiv_inl_low n₁ m₁ n₂ m₂ ⟨x.val, hx1⟩,
        outMapEquiv_castAdd (tensorMapEquiv e₁ e₂)]
    · rw [show x = Fin.castAdd (n₁ + n₂)
          (Fin.natAdd n₁ ⟨x.val - n₁, by omega⟩) from
        Fin.ext (by show x.val = n₁ + (x.val - n₁); omega),
        _root_.Equiv.trans_apply,
        interleaveEquiv_symm_low_right n₁ n₁ n₂ n₂
          ⟨x.val - n₁, by omega⟩,
        _root_.Equiv.trans_apply, _root_.Equiv.sumCongr_apply,
        Sum.map_inr, outMapEquiv_castAdd e₂,
        interleaveEquiv_inr_low n₁ m₁ n₂ m₂
          ⟨x.val - n₁, by omega⟩,
        outMapEquiv_castAdd (tensorMapEquiv e₁ e₂)]
  · rcases Nat.lt_or_ge (x.val - (n₁ + n₂)) n₁ with hx1 | hx1
    · rw [show x = Fin.natAdd (n₁ + n₂)
          (Fin.castAdd n₂ ⟨x.val - (n₁ + n₂), hx1⟩) from
        Fin.ext (by
          show x.val = (n₁ + n₂) + (x.val - (n₁ + n₂))
          omega),
        _root_.Equiv.trans_apply,
        interleaveEquiv_symm_high_left n₁ n₁ n₂ n₂
          ⟨x.val - (n₁ + n₂), hx1⟩,
        _root_.Equiv.trans_apply, _root_.Equiv.sumCongr_apply,
        Sum.map_inl, outMapEquiv_natAdd e₁,
        interleaveEquiv_inl_high n₁ m₁ n₂ m₂
          (e₁ ⟨x.val - (n₁ + n₂), hx1⟩),
        outMapEquiv_natAdd (tensorMapEquiv e₁ e₂),
        tensorMapEquiv_castAdd]
    · rw [show x = Fin.natAdd (n₁ + n₂)
          (Fin.natAdd n₁ ⟨x.val - (n₁ + n₂) - n₁, by
            have := x.isLt
            omega⟩) from
        Fin.ext (by
          show x.val = (n₁ + n₂) + (n₁ + (x.val - (n₁ + n₂) - n₁))
          have := x.isLt
          omega),
        _root_.Equiv.trans_apply,
        interleaveEquiv_symm_high_right n₁ n₁ n₂ n₂
          ⟨x.val - (n₁ + n₂) - n₁, by
            have := x.isLt
            omega⟩,
        _root_.Equiv.trans_apply, _root_.Equiv.sumCongr_apply,
        Sum.map_inr, outMapEquiv_natAdd e₂,
        interleaveEquiv_inr_high n₁ m₁ n₂ m₂
          (e₂ ⟨x.val - (n₁ + n₂) - n₁, by
            have := x.isLt
            omega⟩),
        outMapEquiv_natAdd (tensorMapEquiv e₁ e₂),
        tensorMapEquiv_natAdd]

/-- Composing with a bundle map on the right relabels the
outgoing boundary. -/
noncomputable def composeBundleMap {s n m : ℕ}
    (e : Fin n ≃ Fin m) (F : Fragment (Fin (s + n))) :
    (F.compose (bundleMap e)).Equiv
      (F.relabel (finSumFinEquiv.symm.trans
        ((_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin s)) e).trans
          finSumFinEquiv))) := by
  have hnm : n = m := by
    have h := Fintype.card_congr e
    simpa using h
  subst hnm
  refine (Fragment.composeCongr (Fragment.Equiv.refl F)
    (permFragmentRelabelOutPerm e).symm).trans ?_
  refine (composePermFragment e F).trans ?_
  exact Fragment.Equiv.relabelEq F
    (_root_.Equiv.ext (fun x => rfl))

/-- Composing with a bundle map on the left relabels the
incoming boundary by the inverse. -/
noncomputable def bundleMapCompose {n m u : ℕ}
    (e : Fin n ≃ Fin m) (F : Fragment (Fin (m + u))) :
    ((bundleMap e).compose F).Equiv
      (F.relabel (finSumFinEquiv.symm.trans
        ((_root_.Equiv.sumCongr e.symm
          (_root_.Equiv.refl (Fin u))).trans finSumFinEquiv))) := by
  have hnm : n = m := by
    have h := Fintype.card_congr e
    simpa using h
  subst hnm
  refine (Fragment.composeCongr
    (permFragmentRelabelOutPerm e).symm
    (Fragment.Equiv.refl F)).trans ?_
  refine (permFragmentComposeLeft e F).trans ?_
  exact Fragment.Equiv.relabelEq F
    (_root_.Equiv.ext (fun x => rfl))

/-- The outgoing transport of a cast is a cast. -/
theorem outTransport_finCongr {s n m : ℕ} (h : n = m) :
    (finSumFinEquiv.symm.trans
      ((_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin s))
        (finCongr h)).trans finSumFinEquiv) :
      Fin (s + n) ≃ Fin (s + m)) =
    finCongr (by omega) := by
  subst h
  refine _root_.Equiv.ext (fun x => Fin.ext ?_)
  rcases Nat.lt_or_ge x.val s with hx | hx
  · rw [show x = Fin.castAdd n ⟨x.val, hx⟩ from Fin.ext rfl,
      _root_.Equiv.trans_apply,
      finSumFinEquiv_symm_apply_castAdd]
    rfl
  · rw [show x = Fin.natAdd s ⟨x.val - s, by
        have := x.isLt
        omega⟩ from Fin.ext (by
        show x.val = s + (x.val - s)
        omega),
      _root_.Equiv.trans_apply,
      finSumFinEquiv_symm_apply_natAdd]
    rfl

/-- The incoming transport of a cast is a cast. -/
theorem inTransport_finCongr {n m u : ℕ} (h : n = m) :
    (finSumFinEquiv.symm.trans
      ((_root_.Equiv.sumCongr (finCongr h)
        (_root_.Equiv.refl (Fin u))).trans finSumFinEquiv) :
      Fin (n + u) ≃ Fin (m + u)) =
    finCongr (by omega) := by
  subst h
  refine _root_.Equiv.ext (fun x => Fin.ext ?_)
  rcases Nat.lt_or_ge x.val n with hx | hx
  · rw [show x = Fin.castAdd u ⟨x.val, hx⟩ from Fin.ext rfl,
      _root_.Equiv.trans_apply,
      finSumFinEquiv_symm_apply_castAdd]
    rfl
  · rw [show x = Fin.natAdd n ⟨x.val - n, by
        have := x.isLt
        omega⟩ from Fin.ext (by
        show x.val = n + (x.val - n)
        omega),
      _root_.Equiv.trans_apply,
      finSumFinEquiv_symm_apply_natAdd]
    rfl

variable {R : ℕ} (f : EdgeRankParameter R)

/-- The bundle-map class. -/
noncomputable def bundleMapClass {n m : ℕ} (e : Fin n ≃ Fin m) :
    HomSpace f.val (n + m) :=
  HomSpace.ofFragment f.val (bundleMap e)

/-- The class of the identity bundle map is the identity class. -/
theorem bundleMapClass_refl (n : ℕ) :
    bundleMapClass f (_root_.Equiv.refl (Fin n)) =
      HomSpace.ofFragment f.val (strandBundle n) :=
  HomSpace.ofFragment_congr f (bundleMapRefl n)

/-- **Composition of bundle-map classes.** -/
theorem bundleMapClass_comp {n m p : ℕ}
    (e₁ : Fin n ≃ Fin m) (e₂ : Fin m ≃ Fin p) :
    HomSpace.comp f n m p
        (bundleMapClass f e₁) (bundleMapClass f e₂) =
      bundleMapClass f (e₁.trans e₂) := by
  rw [bundleMapClass, bundleMapClass,
    HomSpace.comp_ofFragment]
  exact HomSpace.ofFragment_congr f (bundleMapComp e₁ e₂)

/-- Congruent label equivalences give equal classes. -/
theorem bundleMapClass_congr {n m : ℕ} {e₁ e₂ : Fin n ≃ Fin m}
    (h : e₁ = e₂) :
    bundleMapClass f e₁ = bundleMapClass f e₂ := by
  rw [h]

end RS
