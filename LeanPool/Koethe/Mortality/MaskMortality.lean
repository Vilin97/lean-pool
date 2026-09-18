/-
Copyright (c) 2026 Tom Adamczewski and Epoch AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GPT-6 Astra, Tom Adamczewski
-/
module

public import LeanPool.Koethe.Mortality.Minors
public import LeanPool.Koethe.Pencil
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import LeanPool.Koethe.Mortality.Mask
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.EReal.Operations
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Mask mortality for one-row pencils over an algebraically closed field

The proof uses determinantal rank: vanishing `(r+1)`-minors is the rank
bound, and one nonzero `r`-minor is a pivot.  A long connector kills that
pivot in `P_W P_C P_W`, so all `r`-minors vanish.  Induction finishes in at
most the matrix size many strict rank reductions.

Every connector hole is independently enumerated, all chosen vectors lie
in the constant field, and all products are in the forward word convention
of `KoethePencilDefs`.  No nilness or countability hypothesis is used.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace KoetheCounterexample

namespace Mortality

variable {k : Type*} [Field k] [IsAlgClosed k] {d r : ℕ}

/-- A sufficiently long, mask-compatible connector strictly reduces a
positive determinantal rank. -/
theorem exists_rank_reducing_connector (P : Pencil k d) (M : PeriodicMask k)
    (hM : M.period < 2 * M.holes) (w : List (Triple k))
    (hr : 0 < r) (I J : Fin r → Fin (d + 1))
    (hp : ((P.wordProd w).submatrix I J).det ≠ 0)
    (hnext : MinorsVanish (P.wordProd w) (r + 1)) :
    ∃ c : List (Triple k), M.period ≤ c.length ∧ M.period ∣ c.length ∧
      (∀ z ∈ c, z ≠ 0) ∧ M.Compatible c ∧
      MinorsVanish (P.wordProd ((w ++ c) ++ w)) r := by
  classical
  -- Since `2*H-Q ≥ 1`, this deliberately simple choice suffices.
  let m := 2 * w.length + 1
  let L := m * M.period
  let N := freeCount M L
  let W : List (FormalLetter k N) :=
    ((w.map Sum.inl) ++ formalConnector M L) ++ (w.map Sum.inl)
  have hm : 0 < m := by dsimp [m]; omega
  have hH : 0 < M.holes := by omega
  have hN : 0 < N := by
    dsimp only [N, L]
    rw [freeCount_mul_period]
    exact Nat.mul_pos hm hH
  have hsize : W.length + 1 ≤ 2 * N := by
    calc
      W.length + 1 = m * (M.period + 1) := by
        simp only [W, List.length_append, List.length_map, formalConnector,
          List.length_ofFn, L, m]
        ring
      _ ≤ m * (2 * M.holes) := Nat.mul_le_mul_left m (Nat.succ_le_of_lt hM)
      _ = 2 * N := by
        dsimp only [N, L]
        rw [freeCount_mul_period]
        ring
  have hdegree : (W.map letterDegree).sum = fun _ => 1 := by
    simp only [W, List.map_append, List.sum_append, constantWord_degree,
      zero_add, add_zero]
    exact formalConnector_degree M L
  have hI : Function.Injective I :=
    injective_of_det_submatrix_ne_zero (P.wordProd w) I J hp
  obtain ⟨x, hx, hz⟩ :=
    exists_specialization_minor_zero P W I J hI hN hr hsize hdegree
  let c := (formalConnector M L).map (specializeLetter x)
  have hclen : c.length = L := by
    simp only [c, List.length_map]
    exact formalConnector_length M L
  have hz' : ((P.wordProd ((w ++ c) ++ w)).submatrix I J).det = 0 := by
    simpa only [W, List.map_append, specialize_constantWord] using hz
  refine ⟨c, ?_, ?_, specialized_connector_nonzero M L x hx,
    specialized_connector_compatible M L x, ?_⟩
  · rw [hclen]
    change M.period ≤ m * M.period
    simpa using Nat.mul_le_mul_right M.period (Nat.succ_le_of_lt hm)
  · rw [hclen]
    exact dvd_mul_left M.period m
  · have h := sandwich_minors_vanish (P.wordProd w) (P.wordProd c) I J hp hnext
      (by simpa only [Pencil.wordProd_append] using hz')
    simpa only [Pencil.wordProd_append] using h

/-- Induction on a determinantal rank bound, retaining a positive, aligned,
mask-compatible nonzero word throughout. -/
theorem mortality_of_vanishing_minors (P : Pencil k d) (M : PeriodicMask k)
    (hM : M.period < 2 * M.holes) (r : ℕ) :
    ∀ w : List (Triple k), M.period ≤ w.length → M.period ∣ w.length →
      (∀ z ∈ w, z ≠ 0) → M.Compatible w →
      MinorsVanish (P.wordProd w) (r + 1) →
      ∃ u : List (Triple k), M.period ≤ u.length ∧ M.period ∣ u.length ∧
        (∀ z ∈ u, z ≠ 0) ∧ M.Compatible u ∧ P.wordProd u = 0 := by
  induction r with
  | zero =>
    intro w hlen hdiv hnz hcomp hminor
    exact ⟨w, hlen, hdiv, hnz, hcomp, eq_zero_of_minorsVanish_one _ hminor⟩
  | succ r ih =>
    intro w hlen hdiv hnz hcomp hminor
    by_cases hsmall : MinorsVanish (P.wordProd w) (r + 1)
    · exact ih w hlen hdiv hnz hcomp hsmall
    · obtain ⟨I, J, hp⟩ : ∃ I J : Fin (r + 1) → Fin (d + 1),
          ((P.wordProd w).submatrix I J).det ≠ 0 := by
        simpa only [MinorsVanish, not_forall] using hsmall
      obtain ⟨c, _, hcdiv, hcnz, hccomp, hdrop⟩ :=
        exists_rank_reducing_connector P M hM w (Nat.succ_pos r) I J hp hminor
      apply ih ((w ++ c) ++ w) ?_ ?_ ?_ ?_ hdrop
      · simp only [List.length_append]
        omega
      · simpa only [List.length_append] using dvd_add (dvd_add hdiv hcdiv) hdiv
      · intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · rcases List.mem_append.mp hz with hz | hz
          · exact hnz z hz
          · exact hcnz z hz
        · exact hnz z hz
      · apply compatible_append M (compatible_append M hcomp hccomp hdiv) hcomp
        simpa only [List.length_append] using dvd_add hdiv hcdiv

end Mortality

/-- **Mask mortality.** A periodic mask with more than half of its residues
free admits a compatible nonzero mortal word for every one-row pencil over
an algebraically closed field. -/
theorem maskMortality (k : Type*) [Field k] [IsAlgClosed k] : MaskMortality k := by
  intro d P M hM
  obtain ⟨w, hlen, hnz, hcomp⟩ := Mortality.exists_compatible_block M
  apply Mortality.mortality_of_vanishing_minors P M hM (d + 1) w
    (by omega) (by rw [hlen]) hnz hcomp
  apply Mortality.minorsVanish_above
  simp

end KoetheCounterexample

end
