/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.HomogenizationError

/-! # Homogenization Error Definitions -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-!
# Public Chapter 2.5 Homogenization-Error Theorem Surface

This file records the note-facing basic properties of
`\mathcal E_{s,\infty,1}`.  The coefficient field is the public
`TriadicCoeffFamily`, so ellipticity and cube compatibility are a.e. facts.
-/

/-- Public theorem package for
`l.multiscale.homogenization.error.basic.definitions`, in the downstream
`p = infinity`, `q = 1` form used by the Chapter 3 coarse estimates. -/
structure HomogenizationErrorInfinityOneBasicTheory {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : TriadicCoeffFamily d) (a0 : Mat d) : Prop where
  scaleResponse_nonneg :
    ∀ {k : ℤ}, k ≤ Q.scale →
      0 ≤ scaleResponseAtScale Q k .infinity a a0
  error_nonneg :
    ∀ {s : ℝ}, 0 < s →
      0 ≤ HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0
  oneCube_le_error :
    ∀ {s : ℝ}, 0 < s →
      scaleResponseAtScale Q Q.scale .infinity a a0 ≤
        HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0
  error_antitone :
    ∀ {t s : ℝ}, 0 < t → t < s →
      HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 ≤
        HomogenizationErrorOnCube Q t .infinity (.finite 1) a a0
  descendant_error_le :
    ∀ {R : TriadicCube d} {k : ℤ} {s : ℝ},
      R ∈ descendantsAtScale Q k → 0 < s →
        HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 ≤
          Real.rpow (3 : ℝ) (s * (Int.toNat (Q.scale - k) : ℝ)) *
            HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0
  descendants_error_sup_le :
    ∀ {k : ℤ} {s : ℝ}, k ≤ Q.scale → 0 < s →
      finsetSupReal (descendantsAtScale Q k)
          (fun R => HomogenizationErrorOnCube R s .infinity (.finite 1) a a0) ≤
        Real.rpow (3 : ℝ) (s * (Int.toNat (Q.scale - k) : ℝ)) *
          HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0

/-- Aggregate public theorem package for the homogenization-error part of
Sec. 2.5. -/
structure HomogenizationErrorTheory (d : ℕ) [NeZero d] : Prop where
  infinity_one_basic :
    ∀ (Q : TriadicCube d) (a : TriadicCoeffFamily d) (a0 : Mat d),
      HomogenizationErrorInfinityOneBasicTheory Q a a0

end

end Ch02
end Book
end Homogenization
