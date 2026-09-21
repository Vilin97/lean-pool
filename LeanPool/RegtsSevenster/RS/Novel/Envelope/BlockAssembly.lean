/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Envelope.BlockFactor
import LeanPool.RegtsSevenster.RS.Novel.Envelope.NilpotentTrace

/-!
# The block Frobenius tower

The Frobenius character identity at every ambient arity: the
trace of a Young idempotent (in the block representation of
`S_k`) against the block-diagonal power is the dimension times
the Schur specialization of the block power traces.  The
resulting `FrobeniusTower` gives the appendix's nilpotent-trace
proof at every strand arity. The mainline semisimplicity proof
uses the factorial argument in `BlockFactorialTrace`.
-/

namespace RS

open CategoryTheory

variable {R : ℕ} (f : EdgeRankParameter R)

/-- **The block Frobenius identity** at ambient arity `n`. -/
theorem block_frobenius (P : SchurPackage.{1}) (n : ℕ)
    (μ : YoungDiagram) (g : skeinEnd f n) :
    skeinTrace f (n * μ.card)
        (blockRep f n μ.card (P.e μ) *
          blockPow f n g μ.card) =
      (P.dim μ : ℂ) *
        diagramSchur μ (fun c => skeinTrace f n (g ^ c)) := by
  classical
  have hexp : blockRep f n μ.card (P.e μ) *
      blockPow f n g μ.card =
      ((P.dim μ : ℂ) / (μ.card.factorial : ℂ)) •
        ∑ π : Equiv.Perm (Fin μ.card), P.char μ π •
          (permClass f (n * μ.card) (blockPerm n π) *
            blockPow f n g μ.card) := by
    rw [SchurPackage.e_def, charIdempotent, map_smul, map_sum,
      smul_mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [map_smul, blockRep_of, smul_mul_assoc]
  have hlin_smul : ∀ (c : ℂ) (x : skeinEnd f (n * μ.card)),
      skeinTrace f (n * μ.card) (c • x) =
        c * skeinTrace f (n * μ.card) x := fun c x =>
    (map_smul (HomSpace.traceMap f.val (n * μ.card)) c x).trans
      (smul_eq_mul _ _)
  have hlin_sum : ∀ (h : Equiv.Perm (Fin μ.card) →
        skeinEnd f (n * μ.card)),
      skeinTrace f (n * μ.card) (∑ π, h π) =
        ∑ π, skeinTrace f (n * μ.card) (h π) := fun h =>
    map_sum (HomSpace.traceMap f.val (n * μ.card)) h
      Finset.univ
  rw [hexp, hlin_smul, hlin_sum]
  rw [show (∑ π : Equiv.Perm (Fin μ.card),
      skeinTrace f (n * μ.card) (P.char μ π •
        (permClass f (n * μ.card) (blockPerm n π) *
          blockPow f n g μ.card))) =
    ∑ π : Equiv.Perm (Fin μ.card), P.char μ π *
      ((π.cycleType.map
          (fun c => skeinTrace f n (g ^ c))).prod *
        skeinTrace f n (g ^ 1) ^
          (μ.card - π.cycleType.sum)) from
    Finset.sum_congr rfl fun π _ => by
      rw [hlin_smul, skeinTrace_blockPerm_mul_pow]]
  rw [div_eq_mul_inv, mul_assoc]
  exact congrArg ((P.dim μ : ℂ) * ·)
    (P.frobenius μ (fun c => skeinTrace f n (g ^ c)))

/-- **The block Frobenius tower** at ambient arity `n`. -/
noncomputable def blockFrobeniusTower (P : SchurPackage.{1})
    (n : ℕ) :
    FrobeniusTower P (fun k => skeinEnd f (n * k)) (((R : ℝ) ^ n) ^ 2)
      (skeinEnd f n) where
  toPermTower := blockPermTower f n
  traceA := HomSpace.traceMap f.val n
  trace k := HomSpace.traceMap f.val (n * k)
  pow k g := blockPow f n g k
  frobenius μ g := block_frobenius f P n μ g

/-- **Nilpotent-trace vanishing at every arity**: every nilpotent
strand endomorphism, at any arity, has vanishing skein trace. -/
theorem skeinTrace_eq_zero_of_isNilpotent_all
    (P : SchurPackage.{1}) (n : ℕ) {g : skeinEnd f n}
    (hg : IsNilpotent g) :
    skeinTrace f n g = 0 :=
  (blockFrobeniusTower f P n).traceA_eq_zero_of_isNilpotent hg

end RS
