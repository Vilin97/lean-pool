/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos132ThreeChain.FourPoints

/-!
# The five-point obstruction

The four-point catalogue confines a chain configuration to one adjacent pair `{c, 3 * c}` and
forces a common anchor.  What survives is a very rigid picture: four points at squared distance
`c` from a common centre, with pairwise squared distances `c` or `3 * c`.

`no_four_on_circle` rules that picture out.  Writing `u i` for the vector from the centre to the
`i`-th point, the hypotheses give `⟪u i, u i⟫ = c` and `⟪u i, u j⟫ = ± c / 2`.  Singularity of
every three-vector Gram matrix in the plane forces each triple product `⟪u i, u j⟫ ⟪u i, u k⟫
⟪u j, u k⟫` to equal `-c ^ 3 / 8`, and then the explicit combination `c • u₁ - 2 ⟪u₁, u₂⟫ • u₂
- 2 ⟪u₁, u₃⟫ • u₃ - 2 ⟪u₁, u₄⟫ • u₄` has squared length `-2 * c ^ 3 < 0`.

This is the five-point Gram obstruction in its scale-free form.  The equivalent determinant
statement, whose value is `-27 * r ^ 4`, is recorded as `symDet4_chain_five` in
`LeanPool/Erdos132ThreeChain/Witnesses.lean`.
-/

namespace Erdos132ThreeChain

/-- Two points on the circle of squared radius `c` about `o`, at squared distance `c` or
`3 * c`, subtend an inner product of `± c / 2`. -/
theorem dot_sq_of_chain {O P Q : Point} {c : ℝ} (hP : sqDist P O = c) (hQ : sqDist Q O = c)
    (h : sqDist P Q = c ∨ sqDist P Q = 3 * c) : dotp O P Q ^ 2 = c ^ 2 / 4 := by
  have hd := two_mul_dotp O P Q
  rw [hP, hQ] at hd
  rcases h with h | h <;> rw [h] at hd
  · have : dotp O P Q = c / 2 := by linarith
    rw [this]; ring
  · have : dotp O P Q = -(c / 2) := by linarith
    rw [this]; ring

/-- Singularity of the three-vector Gram matrix pins the triple product of the three inner
products. -/
theorem dot_triple_prod {O P Q R : Point} {c : ℝ}
    (hP : sqDist P O = c) (hQ : sqDist Q O = c) (hR : sqDist R O = c)
    (hpq : dotp O P Q ^ 2 = c ^ 2 / 4) (hpr : dotp O P R ^ 2 = c ^ 2 / 4)
    (hqr : dotp O Q R ^ 2 = c ^ 2 / 4) :
    dotp O P Q * dotp O P R * dotp O Q R = -(c ^ 3 / 8) := by
  have hg := gram3_det_eq_zero O P Q R
  rw [dotp_self, dotp_self, dotp_self, hP, hQ, hR] at hg
  linear_combination (1 / 2) * hg + (c / 2) * hpq + (c / 2) * hpr + (c / 2) * hqr

/-- **No four points on a circle.**  Four points at squared distance `c > 0` from a common
centre cannot have all six pairwise squared distances in `{c, 3 * c}`. -/
theorem no_four_on_circle {O P Q R S : Point} {c : ℝ} (hc : 0 < c)
    (hP : sqDist P O = c) (hQ : sqDist Q O = c) (hR : sqDist R O = c) (hS : sqDist S O = c)
    (hPQ : sqDist P Q = c ∨ sqDist P Q = 3 * c)
    (hPR : sqDist P R = c ∨ sqDist P R = 3 * c)
    (hPS : sqDist P S = c ∨ sqDist P S = 3 * c)
    (hQR : sqDist Q R = c ∨ sqDist Q R = 3 * c)
    (hQS : sqDist Q S = c ∨ sqDist Q S = 3 * c)
    (hRS : sqDist R S = c ∨ sqDist R S = 3 * c) : False := by
  have spq := dot_sq_of_chain hP hQ hPQ
  have spr := dot_sq_of_chain hP hR hPR
  have sps := dot_sq_of_chain hP hS hPS
  have sqr := dot_sq_of_chain hQ hR hQR
  have sqs := dot_sq_of_chain hQ hS hQS
  have srs := dot_sq_of_chain hR hS hRS
  have tPQR := dot_triple_prod hP hQ hR spq spr sqr
  have tPQS := dot_triple_prod hP hQ hS spq sps sqs
  have tPRS := dot_triple_prod hP hR hS spr sps srs
  have hkey := sq_nonneg_combo O P Q R S c (-2 * dotp O P Q) (-2 * dotp O P R) (-2 * dotp O P S)
  rw [dotp_self, dotp_self, dotp_self, dotp_self, hP, hQ, hR, hS] at hkey
  have hval : c ^ 2 * c + (-2 * dotp O P Q) ^ 2 * c + (-2 * dotp O P R) ^ 2 * c
      + (-2 * dotp O P S) ^ 2 * c
      + 2 * (c * (-2 * dotp O P Q) * dotp O P Q + c * (-2 * dotp O P R) * dotp O P R
        + c * (-2 * dotp O P S) * dotp O P S
        + (-2 * dotp O P Q) * (-2 * dotp O P R) * dotp O Q R
        + (-2 * dotp O P Q) * (-2 * dotp O P S) * dotp O Q S
        + (-2 * dotp O P R) * (-2 * dotp O P S) * dotp O R S) = -2 * c ^ 3 := by
    linear_combination 8 * tPQR + 8 * tPQS + 8 * tPRS
  rw [hval] at hkey
  have hc3 : (0 : ℝ) < c ^ 3 := by positivity
  linarith


/-- **The five-point obstruction.**  Five plane points whose ten squared distances are all `c`
times a nonnegative power of three, with `c` realised by the edge `A B`, do not exist.  Since
`IsChainValue c x` forces `c ≤ x`, the hypothesis `sqDist A B = c` says exactly that `A B` is a
shortest edge. -/
theorem no_five_chain_points {A B C D E : Point} {c : ℝ} (hc : 0 < c) (hAB : sqDist A B = c)
    (hAC : IsChainValue c (sqDist A C)) (hAD : IsChainValue c (sqDist A D))
    (hAE : IsChainValue c (sqDist A E)) (hBC : IsChainValue c (sqDist B C))
    (hBD : IsChainValue c (sqDist B D)) (hBE : IsChainValue c (sqDist B E))
    (hCD : IsChainValue c (sqDist C D)) (hCE : IsChainValue c (sqDist C E))
    (hDE : IsChainValue c (sqDist D E)) : False := by
  have hne : (3 : ℝ) * c ≠ c := by intro h; linarith
  have qCD := pair_classification hc hAB hAC hBC hAD hBD hCD
  have qCE := pair_classification hc hAB hAC hBC hAE hBE hCE
  have qDE := pair_classification hc hAB hAD hBD hAE hBE hDE
  have posC := qCD.posC
  have posD := qCD.posD
  have posE := qCE.posD
  have centreB : sqDist B C = c → sqDist B D = c → sqDist B E = c → False := by
    intro hbc hbd hbe
    exact no_four_on_circle hc hAB (by rw [sqDist_comm C B]; exact hbc)
      (by rw [sqDist_comm D B]; exact hbd) (by rw [sqDist_comm E B]; exact hbe)
      posC.fromLeft posD.fromLeft posE.fromLeft qCD.distCD qCE.distCD qDE.distCD
  rcases posC.fromLeft with hac | hac
  · rcases posD.fromLeft with had | had
    · rcases posE.fromLeft with hae | hae
      · exact no_four_on_circle hc (by rw [sqDist_comm B A]; exact hAB)
          (by rw [sqDist_comm C A]; exact hac) (by rw [sqDist_comm D A]; exact had)
          (by rw [sqDist_comm E A]; exact hae) posC.fromRight posD.fromRight posE.fromRight
          qCD.distCD qCE.distCD qDE.distCD
      · exact centreB (qCE.sharedRight.resolve_right (by rw [hae]; exact hne))
          (qDE.sharedRight.resolve_right (by rw [hae]; exact hne)) (posE.nearEnd.resolve_left (by
            rw [hae]; exact hne))
    · exact centreB (qCD.sharedRight.resolve_right (by rw [had]; exact hne))
        (posD.nearEnd.resolve_left (by rw [had]; exact hne))
        (qDE.sharedLeft.resolve_left (by rw [had]; exact hne))
  · exact centreB (posC.nearEnd.resolve_left (by rw [hac]; exact hne))
      (qCD.sharedLeft.resolve_left (by rw [hac]; exact hne))
      (qCE.sharedLeft.resolve_left (by rw [hac]; exact hne))

end Erdos132ThreeChain
