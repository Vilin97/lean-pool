/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.TopCellModel
/-!
# Finite top-cell atlas

The concrete Fox–Neuwirth model is a finite disjoint union of standard `(p - 1)`-simplices.  This file
records the closed and open cell components, their compactness, and the explicit simplex charts.
The later mod-`p` cycle construction replaces this disjoint atlas by the invariant glued chain.
-/

namespace NRR

variable {p : ℕ}

namespace FoxNeuwirthTopCellModelPoint

/-- Closed component indexed by a one-block barred permutation. -/
def cellCarrier (c : FoxNeuwirthTopCell p) :
    Set (FoxNeuwirthTopCellModelPoint p) :=
  {z | z.1 = c}

/-- Relative interior of a top-cell component. -/
def cellInterior (c : FoxNeuwirthTopCell p) :
    Set (FoxNeuwirthTopCellModelPoint p) :=
  {z | z.1 = c ∧ ∀ i, 0 < z.2 i}

/-- Standard simplex chart for one component. -/
def cellParam (c : FoxNeuwirthTopCell p) :
    FoxNeuwirthWeights p → FoxNeuwirthTopCellModelPoint p :=
  fun w => (c, w)

@[simp] theorem cellParam_apply
    (c : FoxNeuwirthTopCell p) (w : FoxNeuwirthWeights p) :
    cellParam c w = (c, w) :=
  rfl

 theorem continuous_cellParam (c : FoxNeuwirthTopCell p) :
    Continuous (cellParam c) :=
  continuous_const.prodMk continuous_id

 theorem injective_cellParam (c : FoxNeuwirthTopCell p) :
    Function.Injective (cellParam c) := by
  intro u v h
  exact congrArg Prod.snd h

 theorem range_cellParam (c : FoxNeuwirthTopCell p) :
    Set.range (cellParam c) = cellCarrier c := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    rfl
  · intro hz
    exact ⟨z.2, by
      apply Prod.ext
      · exact hz.symm
      · rfl⟩

 theorem isClosed_cellCarrier (c : FoxNeuwirthTopCell p) :
    IsClosed (cellCarrier c) := by
  exact isClosed_eq (continuous_fst) continuous_const

 theorem isOpen_cellCarrier (c : FoxNeuwirthTopCell p) :
    IsOpen (cellCarrier c) := by
  rw [show cellCarrier c = Prod.fst ⁻¹' {c} from rfl]
  exact (isOpen_discrete {c}).preimage continuous_fst

 theorem isCompact_cellCarrier (c : FoxNeuwirthTopCell p) :
    IsCompact (cellCarrier c) := by
  rw [← range_cellParam]
  simpa only [Set.image_univ] using
    isCompact_univ.image (continuous_cellParam c)

 theorem cellCarrier_pairwise_disjoint
    {c d : FoxNeuwirthTopCell p} (hcd : c ≠ d) :
    Disjoint (cellCarrier c) (cellCarrier d) := by
  rw [Set.disjoint_left]
  intro z hzc hzd
  change z.1 = c at hzc
  change z.1 = d at hzd
  exact hcd (hzc.symm.trans hzd)

 theorem cellCarrier_cover :
    ⋃ c : FoxNeuwirthTopCell p, cellCarrier c = Set.univ := by
  ext z
  simp [cellCarrier]

/-- The declared dimension of every maximal component. -/
def cellDimension (p : Nat)
    (_c : FoxNeuwirthTopCell p) : ℕ :=
  p - 1

 theorem cellDimension_eq
    (p : Nat) (c : FoxNeuwirthTopCell p) :
    cellDimension p c = p - 1 :=
  rfl

/-- Each component is homeomorphic to the standard simplex. -/
def cellHomeomorph (c : FoxNeuwirthTopCell p) :
    FoxNeuwirthWeights p ≃ₜ ↥(cellCarrier c) where
  toFun w := ⟨(c, w), rfl⟩
  invFun z := z.1.2
  left_inv w := rfl
  right_inv z := by
    apply Subtype.ext
    rcases z with ⟨⟨d, w⟩, hd⟩
    change d = c at hd
    subst d
    rfl
  continuous_toFun :=
    (continuous_cellParam c).subtype_mk fun _ => rfl
  continuous_invFun :=
    continuous_snd.comp continuous_subtype_val

end FoxNeuwirthTopCellModelPoint

end NRR
