/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Definitions

/-!
# Unit-prefixed associator and braiding values in SuperVect

The category **SuperVect** — finite-dimensional ℤ/2-graded complex
vector spaces with the graded tensor product and the Koszul
braiding — is defined, with its monoidal, braided, symmetric,
additive and ℂ-linear structure, in `RS/Definitions.lean`.  This
module carries the value computations the extraction consumes: the
unit-prefixed associator and inverse associator on the four graded
blocks, and the braiding on the four generator shapes, including
the Koszul sign on odd⊗odd.
-/

noncomputable section

namespace RS

open CategoryTheory
open scoped TensorProduct

namespace SuperVect

/-! ### Unit-prefixed associator and braiding values -/

/-- The unit-prefixed associator on the even-even block. -/
theorem assoc_unit_ee {V : SuperVect} (r : ℂ) (x y : V.even) :
    (associator tensorUnit V V).hom.evenMap
      (((r ⊗ₜ[ℂ] x, (0 : tensorUnit.odd ⊗[ℂ] V.odd)) ⊗ₜ[ℂ] y,
        (0 : ((tensorUnit.even ⊗[ℂ] V.odd) ×
          (tensorUnit.odd ⊗[ℂ] V.even)) ⊗[ℂ] V.odd))) =
      ((r ⊗ₜ[ℂ] ((x ⊗ₜ[ℂ] y,
          (0 : V.odd ⊗[ℂ] V.odd)) :
        (tensorObj V V).even)),
        (0 : tensorUnit.odd ⊗[ℂ] (tensorObj V V).odd)) := by
  show assocEvenEquiv tensorUnit V V _ = _
  exact assocAux_ee r x y

/-- The unit-prefixed associator on the odd-odd block. -/
theorem assoc_unit_oo {V : SuperVect} (r : ℂ) (u v : V.odd) :
    (associator tensorUnit V V).hom.evenMap
      (((0 : ((tensorUnit.even ⊗[ℂ] V.even) ×
          (tensorUnit.odd ⊗[ℂ] V.odd)) ⊗[ℂ] V.even),
        (r ⊗ₜ[ℂ] u, (0 : tensorUnit.odd ⊗[ℂ] V.even))
          ⊗ₜ[ℂ] v)) =
      ((r ⊗ₜ[ℂ] (((0 : V.even ⊗[ℂ] V.even),
          u ⊗ₜ[ℂ] v) :
        (tensorObj V V).even)),
        (0 : tensorUnit.odd ⊗[ℂ] (tensorObj V V).odd)) := by
  show assocEvenEquiv tensorUnit V V _ = _
  exact assocAux_eo r u v

/-- The unit-prefixed associator on the even-odd block. -/
theorem assoc_unit_eo {V : SuperVect} (r : ℂ)
    (x : V.even) (v : V.odd) :
    (associator tensorUnit V V).hom.oddMap
      (((r ⊗ₜ[ℂ] x, (0 : tensorUnit.odd ⊗[ℂ] V.odd))
          ⊗ₜ[ℂ] v,
        (0 : ((tensorUnit.even ⊗[ℂ] V.odd) ×
          (tensorUnit.odd ⊗[ℂ] V.even)) ⊗[ℂ] V.even))) =
      ((r ⊗ₜ[ℂ] ((x ⊗ₜ[ℂ] v,
          (0 : V.odd ⊗[ℂ] V.even)) :
        (tensorObj V V).odd)),
        (0 : tensorUnit.odd ⊗[ℂ] (tensorObj V V).even)) := by
  show assocOddEquiv tensorUnit V V _ = _
  exact assocAux_ee r x v

/-- The unit-prefixed associator on the odd-even block. -/
theorem assoc_unit_oe {V : SuperVect} (r : ℂ)
    (u : V.odd) (y : V.even) :
    (associator tensorUnit V V).hom.oddMap
      (((0 : ((tensorUnit.even ⊗[ℂ] V.even) ×
          (tensorUnit.odd ⊗[ℂ] V.odd)) ⊗[ℂ] V.odd),
        (r ⊗ₜ[ℂ] u, (0 : tensorUnit.odd ⊗[ℂ] V.even))
          ⊗ₜ[ℂ] y)) =
      ((r ⊗ₜ[ℂ] (((0 : V.even ⊗[ℂ] V.odd),
          u ⊗ₜ[ℂ] y) :
        (tensorObj V V).odd)),
        (0 : tensorUnit.odd ⊗[ℂ] (tensorObj V V).even)) := by
  show assocOddEquiv tensorUnit V V _ = _
  exact assocAux_eo r u y

/-- The braiding on the even-even block. -/
theorem koszul_ee {V W : SuperVect} (x : V.even) (w : W.even) :
    (koszulBraiding V W).evenMap
      ((x ⊗ₜ[ℂ] w, (0 : V.odd ⊗[ℂ] W.odd))) =
      ((w ⊗ₜ[ℂ] x, (0 : W.odd ⊗[ℂ] V.odd))) := by
  show koszulBraidingEven V W _ = _
  simp [koszulBraidingEven, koszulEvenAux]

/-- The braiding on the odd-odd block: the Koszul sign. -/
theorem koszul_oo {V W : SuperVect} (u : V.odd) (v : W.odd) :
    (koszulBraiding V W).evenMap
      (((0 : V.even ⊗[ℂ] W.even), u ⊗ₜ[ℂ] v)) =
      (((0 : W.even ⊗[ℂ] V.even), -(v ⊗ₜ[ℂ] u))) := by
  show koszulBraidingEven V W _ = _
  simp [koszulBraidingEven, koszulEvenAux]

/-- The braiding on the even-odd block. -/
theorem koszul_eo {V W : SuperVect} (x : V.even) (v : W.odd) :
    (koszulBraiding V W).oddMap
      ((x ⊗ₜ[ℂ] v, (0 : V.odd ⊗[ℂ] W.even))) =
      (((0 : W.even ⊗[ℂ] V.odd), v ⊗ₜ[ℂ] x)) := by
  show koszulBraidingOdd V W _ = _
  simp [koszulBraidingOdd, koszulOddAux]

/-- The braiding on the odd-even block. -/
theorem koszul_oe {V W : SuperVect} (u : V.odd) (w : W.even) :
    (koszulBraiding V W).oddMap
      (((0 : V.even ⊗[ℂ] W.odd), u ⊗ₜ[ℂ] w)) =
      ((w ⊗ₜ[ℂ] u, (0 : W.odd ⊗[ℂ] V.even))) := by
  show koszulBraidingOdd V W _ = _
  simp [koszulBraidingOdd, koszulOddAux]

/-- The unit-prefixed inverse associator on the even-even
block. -/
theorem assoc_unit_inv_ee {V : SuperVect} (r : ℂ)
    (x y : V.even) :
    (associator tensorUnit V V).inv.evenMap
      ((r ⊗ₜ[ℂ] ((x ⊗ₜ[ℂ] y,
          (0 : V.odd ⊗[ℂ] V.odd)) :
        (tensorObj V V).even)),
        (0 : tensorUnit.odd ⊗[ℂ] (tensorObj V V).odd)) =
      (((r ⊗ₜ[ℂ] x, (0 : tensorUnit.odd ⊗[ℂ] V.odd))
          ⊗ₜ[ℂ] y,
        (0 : ((tensorUnit.even ⊗[ℂ] V.odd) ×
          (tensorUnit.odd ⊗[ℂ] V.even)) ⊗[ℂ] V.odd))) := by
  show (assocEvenEquiv tensorUnit V V).symm _ = _
  exact (LinearEquiv.symm_apply_eq _).mpr (assocAux_ee r x y).symm

/-- The unit-prefixed inverse associator on the odd-odd block. -/
theorem assoc_unit_inv_oo {V : SuperVect} (r : ℂ)
    (u v : V.odd) :
    (associator tensorUnit V V).inv.evenMap
      ((r ⊗ₜ[ℂ] (((0 : V.even ⊗[ℂ] V.even),
          u ⊗ₜ[ℂ] v) :
        (tensorObj V V).even)),
        (0 : tensorUnit.odd ⊗[ℂ] (tensorObj V V).odd)) =
      (((0 : ((tensorUnit.even ⊗[ℂ] V.even) ×
          (tensorUnit.odd ⊗[ℂ] V.odd)) ⊗[ℂ] V.even),
        (r ⊗ₜ[ℂ] u, (0 : tensorUnit.odd ⊗[ℂ] V.even))
          ⊗ₜ[ℂ] v)) := by
  show (assocEvenEquiv tensorUnit V V).symm _ = _
  exact (LinearEquiv.symm_apply_eq _).mpr (assocAux_eo r u v).symm

/-- The unit-prefixed inverse associator on the even-odd block. -/
theorem assoc_unit_inv_eo {V : SuperVect} (r : ℂ)
    (x : V.even) (v : V.odd) :
    (associator tensorUnit V V).inv.oddMap
      ((r ⊗ₜ[ℂ] ((x ⊗ₜ[ℂ] v,
          (0 : V.odd ⊗[ℂ] V.even)) :
        (tensorObj V V).odd)),
        (0 : tensorUnit.odd ⊗[ℂ] (tensorObj V V).even)) =
      (((r ⊗ₜ[ℂ] x, (0 : tensorUnit.odd ⊗[ℂ] V.odd))
          ⊗ₜ[ℂ] v,
        (0 : ((tensorUnit.even ⊗[ℂ] V.odd) ×
          (tensorUnit.odd ⊗[ℂ] V.even)) ⊗[ℂ] V.even))) := by
  show (assocOddEquiv tensorUnit V V).symm _ = _
  exact (LinearEquiv.symm_apply_eq _).mpr (assocAux_ee r x v).symm

/-- The unit-prefixed inverse associator on the odd-even block. -/
theorem assoc_unit_inv_oe {V : SuperVect} (r : ℂ)
    (u : V.odd) (y : V.even) :
    (associator tensorUnit V V).inv.oddMap
      ((r ⊗ₜ[ℂ] (((0 : V.even ⊗[ℂ] V.odd),
          u ⊗ₜ[ℂ] y) :
        (tensorObj V V).odd)),
        (0 : tensorUnit.odd ⊗[ℂ] (tensorObj V V).even)) =
      (((0 : ((tensorUnit.even ⊗[ℂ] V.even) ×
          (tensorUnit.odd ⊗[ℂ] V.odd)) ⊗[ℂ] V.odd),
        (r ⊗ₜ[ℂ] u, (0 : tensorUnit.odd ⊗[ℂ] V.even))
          ⊗ₜ[ℂ] y)) := by
  show (assocOddEquiv tensorUnit V V).symm _ = _
  exact (LinearEquiv.symm_apply_eq _).mpr (assocAux_eo r u y).symm

end SuperVect

end RS
