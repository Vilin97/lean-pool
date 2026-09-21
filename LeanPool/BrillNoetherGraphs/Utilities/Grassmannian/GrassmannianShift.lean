/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Grassmannian.GrassmannianEnvelope
import LeanPool.BrillNoetherGraphs.Utilities.Transmission.TransmissionShift

/-!
# Arbitrary output shifts of Grassmannian ASP permutations

The once-marked census may be normalized to degree `g`, but the full
transmission theory naturally uses every shift `chi`.  This file derives that
family from the shift-zero Grassmannian constructor without reconstructing its
inversion set a second time.
-/

namespace Utilities

/-- The Grassmannian permutation of `lambda` with ASP shift `chi`. -/
noncomputable def shiftedGrassmannianPerm
    (lambda : YoungDiagram) (chi : ℤ) : AspPerm :=
  outputShift (grassmannianPermOfYoungDiagram lambda) chi

@[simp] theorem shiftedGrassmannianPerm_chi
    (lambda : YoungDiagram) (chi : ℤ) :
    (shiftedGrassmannianPerm lambda chi).χ = chi := by
  simp [shiftedGrassmannianPerm]

@[simp] theorem inv_set_shiftedGrassmannianPerm
    (lambda : YoungDiagram) (chi : ℤ) :
    inv_set (shiftedGrassmannianPerm lambda chi) =
      grassmannianInvSet lambda := by
  simp [shiftedGrassmannianPerm, inv_set_grassmannianPerm]

theorem ncard_inv_set_shiftedGrassmannianPerm
    (lambda : YoungDiagram) (chi : ℤ) :
    (inv_set (shiftedGrassmannianPerm lambda chi)).ncard = lambda.card := by
  rw [inv_set_shiftedGrassmannianPerm]
  rw [← inv_set_grassmannianPerm]
  exact ncard_inv_set_grassmannianPerm lambda

/-- An ASP permutation is uniquely determined by its inversion set and shift.
Thus any externally presented Grassmannian permutation with the Ferrers
inversion set of `lambda` is definitionally the canonical shifted constructor
used in this library. -/
theorem eq_shiftedGrassmannianPerm_of_inv_set_eq_of_chi_eq
    (tau : AspPerm) (lambda : YoungDiagram) (chi : ℤ)
    (hInv : inv_set tau = grassmannianInvSet lambda)
    (hChi : tau.χ = chi) :
    tau = shiftedGrassmannianPerm lambda chi := by
  apply AspPerm.eq_of_inv_set_eq_of_chi_eq
  · rw [hInv, inv_set_shiftedGrassmannianPerm]
  · rw [hChi, shiftedGrassmannianPerm_chi]

/-- The usual shifted Grassmannian formula on nonnegative inputs. -/
theorem shiftedGrassmannianPerm_apply_of_nonneg
    (lambda : YoungDiagram) (chi : ℤ) {n : ℤ} (hn : 0 ≤ n) :
    shiftedGrassmannianPerm lambda chi n =
      n - (lambda.rowLen n.toNat : ℤ) - chi := by
  simp [shiftedGrassmannianPerm,
    grassmannianPerm_apply_of_nonneg lambda hn]

/-- Every partition row retains its exact slipface value after translating
the first coordinate by `-chi`. -/
theorem shiftedGrassmannianPerm_s_at_row
    (lambda : YoungDiagram) (chi : ℤ) (i : ℕ) :
    (shiftedGrassmannianPerm lambda chi).s
        ((i : ℤ) + 1 - chi - (lambda.rowLen i : ℤ)) 0 =
      (i : ℤ) + 1 := by
  rw [shiftedGrassmannianPerm, outputShift_s]
  have hArgument :
      (i : ℤ) + 1 - chi - (lambda.rowLen i : ℤ) + chi =
        (i : ℤ) + 1 - (lambda.rowLen i : ℤ) := by
    ring
  rw [hArgument]
  exact grassmannianPerm_s_at_row lambda i

/-- Output normalization does not change existence of the associated
transmission locus; witnesses differ by `chi` chips at the first mark. -/
theorem transmissionExists_shiftedGrassmannianPerm_iff
    {G : CFGraph} (u v : G.V) (lambda : YoungDiagram) (chi : ℤ) :
    TransmissionExists G u v (shiftedGrassmannianPerm lambda chi) ↔
      TransmissionExists G u v (grassmannianPermOfYoungDiagram lambda) := by
  exact transmissionExists_outputShift_iff u v
    (grassmannianPermOfYoungDiagram lambda) chi

/-- Conditional-on-the-explicit-Ferrers-envelope form of the arbitrary-shift
Grassmannian/once-marked dictionary.  The output shift changes the normalized
degree of a transmission witness but not its existence problem. -/
theorem transmissionExists_shiftedGrassmannianPerm_iff_onceMarkedBNExists_of_negativeEnvelope
    {G : CFGraph} (hG : graph_connected G) (u v : G.V)
    (lambda : YoungDiagram) (chi : ℤ)
    (hNegative : GrassmannianNegativeEnvelope lambda) :
    TransmissionExists G u v (shiftedGrassmannianPerm lambda chi) ↔
      OnceMarkedBNExists G u lambda := by
  rw [transmissionExists_shiftedGrassmannianPerm_iff]
  exact transmissionExists_grassmannianPerm_iff_onceMarkedBNExists_of_negativeEnvelope
    hG u v lambda hNegative

/-- Arbitrary output normalization of the unconditional Grassmannian/
once-marked dictionary. -/
theorem transmissionExists_shiftedGrassmannianPerm_iff_onceMarkedBNExists
    {G : CFGraph} (hG : graph_connected G) (u v : G.V)
    (lambda : YoungDiagram) (chi : ℤ) :
    TransmissionExists G u v (shiftedGrassmannianPerm lambda chi) ↔
      OnceMarkedBNExists G u lambda := by
  rw [transmissionExists_shiftedGrassmannianPerm_iff]
  exact transmissionExists_grassmannianPerm_iff_onceMarkedBNExists
    hG u v lambda

/-- Presentation-independent dictionary.  Any ASP permutation whose inversion
set is the Ferrers set of `lambda` and whose shift is `chi` has exactly the
once-marked transmission locus, even if it was not built with the canonical
constructor. -/
theorem transmissionExists_iff_onceMarkedBNExists_of_grassmannian_inv_set
    {G : CFGraph} (hG : graph_connected G) (u v : G.V)
    (tau : AspPerm) (lambda : YoungDiagram) (chi : ℤ)
    (hInv : inv_set tau = grassmannianInvSet lambda)
    (hChi : tau.χ = chi) :
    TransmissionExists G u v tau ↔ OnceMarkedBNExists G u lambda := by
  rw [eq_shiftedGrassmannianPerm_of_inv_set_eq_of_chi_eq
    tau lambda chi hInv hChi]
  exact transmissionExists_shiftedGrassmannianPerm_iff_onceMarkedBNExists
    hG u v lambda chi

end Utilities
