/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.BundleMapClasses
import LeanPool.RegtsSevenster.RS.Novel.Skein.TensorAssoc
import LeanPool.RegtsSevenster.RS.Novel.Skein.TensorUnit
import LeanPool.RegtsSevenster.RS.Novel.Skein.TensorCompClass

/-!
# Naturality of the structural morphisms, fragment level

The associator and unitor naturality squares of the monoidal
skein category, at the fragment level: composing with a cast
bundle map on either side is a boundary cast, the tensor
associativity and unit laws are relabellings by casts, and all
casts collapse through the transport lemmas.
-/

namespace RS

/-- The associator naturality square, fragment level. -/
noncomputable def assocNatFrag {s₁ t₁ s₂ t₂ s₃ t₃ : ℕ}
    (F₁ : Fragment (Fin (s₁ + t₁))) (F₂ : Fragment (Fin (s₂ + t₂)))
    (F₃ : Fragment (Fin (s₃ + t₃))) :
    ((tensorFragment (tensorFragment F₁ F₂) F₃).compose
        (bundleMap (finCongr
          (by omega : (t₁ + t₂) + t₃ = t₁ + (t₂ + t₃))))).Equiv
      ((bundleMap (finCongr
          (by omega : (s₁ + s₂) + s₃ = s₁ + (s₂ + s₃)))).compose
        (tensorFragment F₁ (tensorFragment F₂ F₃))) := by
  refine (composeBundleMap _ _).trans ?_
  refine (Fragment.Equiv.relabelCongr
    (tensorFragmentAssoc s₁ t₁ s₂ t₂ s₃ t₃ F₁ F₂ F₃) _).trans ?_
  refine (Fragment.Equiv.relabelTrans _ _ _).trans ?_
  refine Fragment.Equiv.trans ?_ (bundleMapCompose _ _).symm
  refine Fragment.Equiv.relabelEq _ ?_
  rw [outTransport_finCongr, finCongr_symm, inTransport_finCongr]
  exact _root_.Equiv.ext (fun x => Fin.ext rfl)

/-- The zero-strand bundle is the empty closed fragment. -/
noncomputable def strandBundleZeroEmpty :
    (strandBundle 0).Equiv
      (emptyClosedFragment : Fragment (Fin 0)) where
  flagEquiv :=
    haveI : IsEmpty (Fin 0 × Bool) :=
      ⟨fun p => p.1.elim0⟩
    haveI : IsEmpty (emptyClosedFragment :
        Fragment (Fin 0)).Flag :=
      inferInstanceAs (IsEmpty Empty)
    show (Fin 0 × Bool) ≃ (emptyClosedFragment :
      Fragment (Fin 0)).Flag from
      _root_.Equiv.equivOfIsEmpty _ _
  vertexEquiv :=
    haveI : IsEmpty (emptyClosedFragment :
        Fragment (Fin 0)).Vertex :=
      inferInstanceAs (IsEmpty Empty)
    haveI : IsEmpty (strandBundle 0).Vertex :=
      inferInstanceAs (IsEmpty Empty)
    _root_.Equiv.equivOfIsEmpty _ _
  attach_comm := fun g => g.1.elim0
  pairing_comm := fun g => g.1.elim0
  circles_eq := rfl

/-- The left-unitor naturality square, fragment level. -/
noncomputable def leftUnitNatFrag {s t : ℕ}
    (F : Fragment (Fin (s + t))) :
    ((tensorFragment (strandBundle 0) F).compose
        (bundleMap (finCongr (by omega : 0 + t = t)))).Equiv
      ((bundleMap (finCongr
          (by omega : 0 + s = s))).compose F) := by
  refine (Fragment.composeCongr
    (tensorFragmentCongr strandBundleZeroEmpty
      (Fragment.Equiv.refl F))
    (Fragment.Equiv.refl _)).trans ?_
  refine (Fragment.composeCongr (tensorFragmentUnitLeft F)
    (Fragment.Equiv.refl _)).trans ?_
  refine (composeBundleMap _ _).trans ?_
  refine (Fragment.Equiv.relabelTrans _ _ _).trans ?_
  refine Fragment.Equiv.trans ?_ (bundleMapCompose _ _).symm
  refine Fragment.Equiv.relabelEq _ ?_
  rw [outTransport_finCongr, finCongr_symm, inTransport_finCongr]
  exact _root_.Equiv.ext (fun x => Fin.ext rfl)

/-- The right-unitor naturality square, fragment level. -/
noncomputable def rightUnitNatFrag {s t : ℕ}
    (F : Fragment (Fin (s + t))) :
    ((tensorFragment F (strandBundle 0)).compose
        (bundleMap (finCongr (by omega : t + 0 = t)))).Equiv
      ((bundleMap (finCongr
          (by omega : s + 0 = s))).compose F) := by
  refine (Fragment.composeCongr
    (tensorFragmentCongr (Fragment.Equiv.refl F)
      strandBundleZeroEmpty)
    (Fragment.Equiv.refl _)).trans ?_
  refine (Fragment.composeCongr (tensorFragmentUnitRight F)
    (Fragment.Equiv.refl _)).trans ?_
  refine (composeBundleMap _ _).trans ?_
  refine (Fragment.Equiv.relabelTrans _ _ _).trans ?_
  refine Fragment.Equiv.trans ?_ (bundleMapCompose _ _).symm
  refine Fragment.Equiv.relabelEq _ ?_
  rw [outTransport_finCongr, finCongr_symm, inTransport_finCongr]
  exact _root_.Equiv.ext (fun x => Fin.ext rfl)

variable {R : ℕ} (f : EdgeRankParameter R)

/-- The associator-naturality difference lies in the kernel. -/
theorem mem_ker_assocNat {s₁ t₁ s₂ t₂ s₃ t₃ : ℕ}
    (x₁ : Fragment (Fin (s₁ + t₁)) →₀ ℂ)
    (x₂ : Fragment (Fin (s₂ + t₂)) →₀ ℂ)
    (x₃ : Fragment (Fin (s₃ + t₃)) →₀ ℂ) :
    composeFinsupp ((s₁ + s₂) + s₃) ((t₁ + t₂) + t₃)
        (t₁ + (t₂ + t₃))
        (tensorFinsupp (s₁ + s₂) (t₁ + t₂) s₃ t₃
          (tensorFinsupp s₁ t₁ s₂ t₂ x₁ x₂) x₃)
        (Finsupp.single (bundleMap (finCongr
          (by omega : (t₁ + t₂) + t₃ = t₁ + (t₂ + t₃)))) 1) -
      composeFinsupp ((s₁ + s₂) + s₃) (s₁ + (s₂ + s₃))
        (t₁ + (t₂ + t₃))
        (Finsupp.single (bundleMap (finCongr
          (by omega : (s₁ + s₂) + s₃ = s₁ + (s₂ + s₃)))) 1)
        (tensorFinsupp s₁ t₁ (s₂ + s₃) (t₂ + t₃) x₁
          (tensorFinsupp s₂ t₂ s₃ t₃ x₂ x₃)) ∈
      LinearMap.ker (connectionMap f.val
        (((s₁ + s₂) + s₃) + (t₁ + (t₂ + t₃)))) := by
  induction x₁ using Finsupp.induction_linear with
  | zero =>
    simp only [map_zero, LinearMap.zero_apply, sub_zero]
    exact Submodule.zero_mem _
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply] at ha hb ⊢
    rw [show ∀ (A B C D : (Fragment (Fin (((s₁ + s₂) + s₃) +
        (t₁ + (t₂ + t₃)))) →₀ ℂ)),
        A + B - (C + D) = (A - C) + (B - D) from
      fun A B C D => by abel]
    exact Submodule.add_mem _ ha hb
  | single F₁ c₁ =>
    induction x₂ using Finsupp.induction_linear with
    | zero =>
      simp only [map_zero, LinearMap.zero_apply, sub_zero]
      exact Submodule.zero_mem _
    | add a b ha hb =>
      simp only [map_add, LinearMap.add_apply] at ha hb ⊢
      rw [show ∀ (A B C D : (Fragment (Fin (((s₁ + s₂) + s₃) +
          (t₁ + (t₂ + t₃)))) →₀ ℂ)),
          A + B - (C + D) = (A - C) + (B - D) from
        fun A B C D => by abel]
      exact Submodule.add_mem _ ha hb
    | single F₂ c₂ =>
      induction x₃ using Finsupp.induction_linear with
      | zero =>
        simp only [map_zero, LinearMap.zero_apply, sub_zero]
        exact Submodule.zero_mem _
      | add a b ha hb =>
        simp only [map_add, LinearMap.add_apply] at ha hb ⊢
        rw [show ∀ (A B C D : (Fragment (Fin (((s₁ + s₂) + s₃) +
            (t₁ + (t₂ + t₃)))) →₀ ℂ)),
            A + B - (C + D) = (A - C) + (B - D) from
          fun A B C D => by abel]
        exact Submodule.add_mem _ ha hb
      | single F₃ c₃ =>
        rw [tensorFinsupp_single, tensorFinsupp_single,
          tensorFinsupp_single, tensorFinsupp_single,
          composeFinsupp_single, composeFinsupp_single,
          show ((c₁ * c₂) * c₃) * 1 = 1 * (c₁ * (c₂ * c₃))
            from by ring]
        exact mem_ker_single_sub_of_equiv_smul f
          (assocNatFrag F₁ F₂ F₃) (1 * (c₁ * (c₂ * c₃)))

/-- The left-unitor-naturality difference lies in the kernel. -/
theorem mem_ker_leftUnitNat {s t : ℕ}
    (x : Fragment (Fin (s + t)) →₀ ℂ) :
    composeFinsupp (0 + s) (0 + t) t
        (tensorFinsupp 0 0 s t
          (Finsupp.single (strandBundle 0) 1) x)
        (Finsupp.single (bundleMap (finCongr
          (by omega : 0 + t = t))) 1) -
      composeFinsupp (0 + s) s t
        (Finsupp.single (bundleMap (finCongr
          (by omega : 0 + s = s))) 1) x ∈
      LinearMap.ker (connectionMap f.val ((0 + s) + t)) := by
  induction x using Finsupp.induction_linear with
  | zero =>
    simp only [map_zero, LinearMap.zero_apply, sub_zero]
    exact Submodule.zero_mem _
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply] at ha hb ⊢
    rw [show ∀ (A B C D : (Fragment (Fin ((0 + s) + t)) →₀ ℂ)),
        A + B - (C + D) = (A - C) + (B - D) from
      fun A B C D => by abel]
    exact Submodule.add_mem _ ha hb
  | single F c =>
    rw [tensorFinsupp_single, composeFinsupp_single,
      composeFinsupp_single,
      show (1 * c) * 1 = 1 * c from by ring]
    exact mem_ker_single_sub_of_equiv_smul f
      (leftUnitNatFrag F) (1 * c)

/-- The right-unitor-naturality difference lies in the kernel. -/
theorem mem_ker_rightUnitNat {s t : ℕ}
    (x : Fragment (Fin (s + t)) →₀ ℂ) :
    composeFinsupp (s + 0) (t + 0) t
        (tensorFinsupp s t 0 0 x
          (Finsupp.single (strandBundle 0) 1))
        (Finsupp.single (bundleMap (finCongr
          (by omega : t + 0 = t))) 1) -
      composeFinsupp (s + 0) s t
        (Finsupp.single (bundleMap (finCongr
          (by omega : s + 0 = s))) 1) x ∈
      LinearMap.ker (connectionMap f.val ((s + 0) + t)) := by
  induction x using Finsupp.induction_linear with
  | zero =>
    simp only [map_zero, LinearMap.zero_apply, sub_zero]
    exact Submodule.zero_mem _
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply] at ha hb ⊢
    rw [show ∀ (A B C D : (Fragment (Fin ((s + 0) + t)) →₀ ℂ)),
        A + B - (C + D) = (A - C) + (B - D) from
      fun A B C D => by abel]
    exact Submodule.add_mem _ ha hb
  | single F c =>
    rw [tensorFinsupp_single, composeFinsupp_single,
      composeFinsupp_single,
      show (c * 1) * 1 = 1 * c from by ring]
    exact mem_ker_single_sub_of_equiv_smul f
      (rightUnitNatFrag F) (1 * c)

/-- **Associator naturality on Hom classes.** -/
theorem assocNat_class {s₁ t₁ s₂ t₂ s₃ t₃ : ℕ}
    (p₁ : HomSpace f.val (s₁ + t₁)) (p₂ : HomSpace f.val (s₂ + t₂))
    (p₃ : HomSpace f.val (s₃ + t₃)) :
    HomSpace.comp f ((s₁ + s₂) + s₃) ((t₁ + t₂) + t₃)
        (t₁ + (t₂ + t₃))
        (HomSpace.tensor f (s₁ + s₂) (t₁ + t₂) s₃ t₃
          (HomSpace.tensor f s₁ t₁ s₂ t₂ p₁ p₂) p₃)
        (bundleMapClass f (finCongr
          (by omega : (t₁ + t₂) + t₃ = t₁ + (t₂ + t₃)))) =
      HomSpace.comp f ((s₁ + s₂) + s₃) (s₁ + (s₂ + s₃))
        (t₁ + (t₂ + t₃))
        (bundleMapClass f (finCongr
          (by omega : (s₁ + s₂) + s₃ = s₁ + (s₂ + s₃))))
        (HomSpace.tensor f s₁ t₁ (s₂ + s₃) (t₂ + t₃) p₁
          (HomSpace.tensor f s₂ t₂ s₃ t₃ p₂ p₃)) := by
  obtain ⟨x₁, rfl⟩ := Submodule.Quotient.mk_surjective _ p₁
  obtain ⟨x₂, rfl⟩ := Submodule.Quotient.mk_surjective _ p₂
  obtain ⟨x₃, rfl⟩ := Submodule.Quotient.mk_surjective _ p₃
  exact (Submodule.Quotient.eq _).mpr
    (mem_ker_assocNat f x₁ x₂ x₃)

/-- **Left-unitor naturality on Hom classes.** -/
theorem leftUnitNat_class {s t : ℕ}
    (p : HomSpace f.val (s + t)) :
    HomSpace.comp f (0 + s) (0 + t) t
        (HomSpace.tensor f 0 0 s t
          (HomSpace.ofFragment f.val (strandBundle 0)) p)
        (bundleMapClass f (finCongr (by omega : 0 + t = t))) =
      HomSpace.comp f (0 + s) s t
        (bundleMapClass f (finCongr (by omega : 0 + s = s)))
        p := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ p
  exact (Submodule.Quotient.eq _).mpr (mem_ker_leftUnitNat f x)

/-- **Right-unitor naturality on Hom classes.** -/
theorem rightUnitNat_class {s t : ℕ}
    (p : HomSpace f.val (s + t)) :
    HomSpace.comp f (s + 0) (t + 0) t
        (HomSpace.tensor f s t 0 0 p
          (HomSpace.ofFragment f.val (strandBundle 0)))
        (bundleMapClass f (finCongr (by omega : t + 0 = t))) =
      HomSpace.comp f (s + 0) s t
        (bundleMapClass f (finCongr (by omega : s + 0 = s)))
        p := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ p
  exact (Submodule.Quotient.eq _).mpr (mem_ker_rightUnitNat f x)

end RS
