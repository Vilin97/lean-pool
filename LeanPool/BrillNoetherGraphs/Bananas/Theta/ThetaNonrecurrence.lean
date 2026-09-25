/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.EndpointInversions
public import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffDelta
public import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaArithmetic

/-!
# Rank characterizations of raw transmission permutations

This file isolates the generic bridge used by the non-recurrence argument in
Section 4 of the twice-marked banana paper.  The paper's raw transmission
permutation is the unique ASP permutation whose slipface is the marked rank
surface.  Consequently its southeast and northwest quadrant cardinalities
are exactly the two Riemann--Roch rank terms (paper Lemma `lem:tauChars`).
-/

@[expose] public section

namespace Bananas

open Utilities

/-! ## Concrete degree-twist representatives -/

/-- The degree-`d` representative at an integer marked-difference index. -/
noncomputable def degreeTwistInt
    (M : TwiceMarked) (D : CFDiv M.graph) (d b : ℤ) : CFDiv M.graph :=
  D + (d - deg D + b) • oneChip M.u - b • oneChip M.v

/-- Integer-indexed degree twists have the prescribed degree. -/
@[simp] theorem deg_degreeTwistInt
    (M : TwiceMarked) (D : CFDiv M.graph) (d b : ℤ) :
    deg (degreeTwistInt M D d b) = d := by
  unfold degreeTwistInt
  rw [deg_add_marked_twist]
  ring

/-- Varying the index translates a fixed-degree representative by the marked
difference. -/
theorem degreeTwistInt_eq_zero_add_marked_difference
    (M : TwiceMarked) (D : CFDiv M.graph) (d b : ℤ) :
    degreeTwistInt M D d b =
      degreeTwistInt M D d 0 + b • (oneChip M.u - oneChip M.v) := by
  unfold degreeTwistInt
  rw [zero_smul]
  ext w
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply]
  ring

/-- Indexing degree twists modulo a torsion witness preserves their linear
equivalence class. -/
theorem degreeTwistInt_add_torsion_linearEquiv
    {M : TwiceMarked} {k : ℕ} (hk : TorsionWitness M k)
    (D : CFDiv M.graph) (d b : ℤ) :
    linearEquiv M.graph
      (degreeTwistInt M D d (b + k))
      (degreeTwistInt M D d b) := by
  unfold degreeTwistInt
  convert linearEquiv_marked_twist_add_torsion hk D (d - deg D + b) b using 1 ;
    ring

/-- The paper's nonrecurrence condition, formulated on concrete torsion
residues instead of Picard-group quotient classes. -/
def NonRecurrent (M : TwiceMarked) (k : ℕ) : Prop :=
  ∀ (w : M.graph.V) (n m : Fin k), n.val ≠ 0 → m.val ≠ 0 →
    0 ≤ rank M.graph
      (oneChip w + (n.val : ℤ) • (oneChip M.u - oneChip M.v)) →
    0 ≤ rank M.graph
      (oneChip w + (m.val : ℤ) • (oneChip M.u - oneChip M.v)) →
    n = m

/-- A convenient finite-residue consequence of nonrecurrence: two effective
twists at the same vertex either use the zero residue or coincide. -/
theorem NonRecurrent.zero_or_eq_of_two_rank_nonneg
    {M : TwiceMarked} {k : ℕ} (hNonrec : NonRecurrent M k)
    (w : M.graph.V) (n m : Fin k)
    (hn : 0 ≤ rank M.graph
      (oneChip w + (n.val : ℤ) • (oneChip M.u - oneChip M.v)))
    (hm : 0 ≤ rank M.graph
      (oneChip w + (m.val : ℤ) • (oneChip M.u - oneChip M.v))) :
    n.val = 0 ∨ m.val = 0 ∨ n = m := by
  by_cases hn0 : n.val = 0
  · exact Or.inl hn0
  by_cases hm0 : m.val = 0
  · exact Or.inr (Or.inl hm0)
  exact Or.inr (Or.inr (hNonrec w n m hn0 hm0 hn hm))

/-! ## A no-wrap prefix calculation -/

private theorem linear_equiv_zsmul' {G : CFGraph} {A B : CFDiv G}
    (h : linearEquiv G A B) (n : ℤ) :
    linearEquiv G (n • A) (n • B) := by
  unfold linearEquiv at h ⊢
  simpa [smul_sub] using AddSubgroup.zsmul_mem (principalDivisors G) h n

private theorem linear_equiv_sub' {G : CFGraph} {A B C D : CFDiv G}
    (hAC : linearEquiv G A C) (hBD : linearEquiv G B D) :
    linearEquiv G (A - B) (C - D) := by
  unfold linearEquiv at hAC hBD ⊢
  convert (principalDivisors G).sub_mem hAC hBD using 1 ; abel

/-- Before either marked position wraps around its strand, multiplying the
marked difference simply advances both points by the same multiplier. -/
theorem theta_multiple_noWrap_linearEquiv
    (B : Banana 2) (alpha beta : Fin 3)
    (i : B.PathPosition alpha) (j : B.PathPosition beta) (n : ℕ)
    (hni : n * i.val ≤ B.length alpha)
    (hnj : n * j.val ≤ B.length beta) :
    linearEquiv B.graph
      ((n : ℤ) •
        (oneChip (strandVertex B alpha i) - oneChip (strandVertex B beta j)))
      (oneChip (strandVertex B alpha ⟨n * i.val, by omega⟩) -
        oneChip (strandVertex B beta ⟨n * j.val, by omega⟩)) := by
  let p : B.PathPosition alpha := ⟨n * i.val, by omega⟩
  let q : B.PathPosition beta := ⟨n * j.val, by omega⟩
  have hα := strand_prefix_linearEquiv B alpha i
  have hβ := strand_prefix_linearEquiv B beta j
  have hp := strand_prefix_linearEquiv B alpha p
  have hq := strand_prefix_linearEquiv B beta q
  have hαscale := linear_equiv_zsmul' hα (n : ℤ)
  have hβscale := linear_equiv_zsmul' hβ (n : ℤ)
  have hα' : linearEquiv B.graph
      ((n : ℤ) • (oneChip (strandVertex B alpha i) - oneChip (leftEndpoint B)))
      (oneChip (strandVertex B alpha p) - oneChip (leftEndpoint B)) := by
    have hscale : (n : ℤ) • ((i.val : ℤ) •
        (oneChip (strandVertex B alpha ⟨1, by
          have := B.length_pos alpha; omega⟩) - oneChip (leftEndpoint B))) =
        (p.val : ℤ) •
        (oneChip (strandVertex B alpha ⟨1, by
          have := B.length_pos alpha; omega⟩) - oneChip (leftEndpoint B)) := by
      rw [smul_smul]
      congr 1
    rw [hscale] at hαscale
    exact hαscale.symm.trans hp
  have hβ' : linearEquiv B.graph
      ((n : ℤ) • (oneChip (strandVertex B beta j) - oneChip (leftEndpoint B)))
      (oneChip (strandVertex B beta q) - oneChip (leftEndpoint B)) := by
    have hscale : (n : ℤ) • ((j.val : ℤ) •
        (oneChip (strandVertex B beta ⟨1, by
          have := B.length_pos beta; omega⟩) - oneChip (leftEndpoint B))) =
        (q.val : ℤ) •
        (oneChip (strandVertex B beta ⟨1, by
          have := B.length_pos beta; omega⟩) - oneChip (leftEndpoint B)) := by
      rw [smul_smul]
      congr 1
    rw [hscale] at hβscale
    exact hβscale.symm.trans hq
  have h := linear_equiv_sub' hα' hβ'
  have hLeft : (n : ℤ) •
      (oneChip (strandVertex B alpha i) - oneChip (strandVertex B beta j)) =
      (n : ℤ) • (oneChip (strandVertex B alpha i) - oneChip (leftEndpoint B)) -
        (n : ℤ) • (oneChip (strandVertex B beta j) - oneChip (leftEndpoint B)) := by
    rw [smul_sub]
    simp only [smul_sub]
    abel
  have hRight :
      (oneChip (strandVertex B alpha p) - oneChip (leftEndpoint B)) -
        (oneChip (strandVertex B beta q) - oneChip (leftEndpoint B)) =
      oneChip (strandVertex B alpha p) - oneChip (strandVertex B beta q) := by
    abel
  rw [← hLeft, hRight] at h
  exact h

private theorem linear_equiv_add' {G : CFGraph} {A B C D : CFDiv G}
    (hAC : linearEquiv G A C) (hBD : linearEquiv G B D) :
    linearEquiv G (A + B) (C + D) := by
  unfold linearEquiv at hAC hBD ⊢
  convert (principalDivisors G).add_mem hAC hBD using 1 ; abel

/-- A multiple of one normalized strand prefix is its quotient number of
endpoint differences plus its residue prefix. -/
theorem strand_multiple_prefix_normalForm_linearEquiv
    {g : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (i p : B.PathPosition alpha) (m t : ℕ)
    (hmp : m * i.val = t * B.length alpha + p.val) :
    linearEquiv B.graph
      ((m : ℤ) • (oneChip (strandVertex B alpha i) - oneChip (leftEndpoint B)))
      ((t : ℤ) • (oneChip (rightEndpoint B) - oneChip (leftEndpoint B)) +
        (oneChip (strandVertex B alpha p) - oneChip (leftEndpoint B))) := by
  let step : CFDiv B.graph :=
    oneChip (strandVertex B alpha ⟨1, by
      have := B.length_pos alpha
      omega⟩) - oneChip (leftEndpoint B)
  have hi := strand_prefix_linearEquiv B alpha i
  have hp := strand_prefix_linearEquiv B alpha p
  have hEnd := strand_prefix_linearEquiv B alpha
    ⟨B.length alpha, by omega⟩
  have hScaleI := linear_equiv_zsmul' hi (m : ℤ)
  have hScaleEnd := linear_equiv_zsmul' hEnd (t : ℤ)
  have hAdd := linear_equiv_add' hScaleEnd hp
  have hCoeff : ((m : ℤ) * (i.val : ℤ)) =
      (t : ℤ) * (B.length alpha : ℤ) + (p.val : ℤ) := by
    exact_mod_cast hmp
  have hLeft :
      (m : ℤ) • ((i.val : ℤ) • step) =
        ((m : ℤ) * (i.val : ℤ)) • step := by rw [smul_smul]
  have hRight :
      (t : ℤ) • ((B.length alpha : ℤ) • step) +
        (p.val : ℤ) • step =
      ((m : ℤ) * (i.val : ℤ)) • step := by
    simp only [smul_smul]
    rw [← add_smul, ← hCoeff]
  change linearEquiv B.graph
    ((m : ℤ) • ((i.val : ℤ) • step))
    ((m : ℤ) • (oneChip (strandVertex B alpha i) - oneChip (leftEndpoint B))) at hScaleI
  have hAdd' : linearEquiv B.graph
    ((t : ℤ) • ((B.length alpha : ℤ) • step) + (p.val : ℤ) • step)
    ((t : ℤ) • (oneChip (rightEndpoint B) - oneChip (leftEndpoint B)) +
      (oneChip (strandVertex B alpha p) - oneChip (leftEndpoint B))) := by
    simpa [step, strandVertex_length] using hAdd
  rw [hLeft] at hScaleI
  rw [hRight] at hAdd'
  exact hScaleI.symm.trans hAdd'

/-- If two marked strand multiples have the same quotient, their difference
is represented by the two residue positions. -/
theorem theta_multiple_residue_linearEquiv
    (B : Banana 2) (alpha beta : Fin 3)
    (i p : B.PathPosition alpha) (j q : B.PathPosition beta)
    (m t : ℕ)
    (hα : m * i.val = t * B.length alpha + p.val)
    (hβ : m * j.val = t * B.length beta + q.val) :
    linearEquiv B.graph
      ((m : ℤ) •
        (oneChip (strandVertex B alpha i) - oneChip (strandVertex B beta j)))
      (oneChip (strandVertex B alpha p) - oneChip (strandVertex B beta q)) := by
  have hA := strand_multiple_prefix_normalForm_linearEquiv B alpha i p m t hα
  have hB := strand_multiple_prefix_normalForm_linearEquiv B beta j q m t hβ
  have h := linear_equiv_sub' hA hB
  have hLeft : (m : ℤ) •
      (oneChip (strandVertex B alpha i) - oneChip (strandVertex B beta j)) =
      (m : ℤ) • (oneChip (strandVertex B alpha i) - oneChip (leftEndpoint B)) -
        (m : ℤ) • (oneChip (strandVertex B beta j) - oneChip (leftEndpoint B)) := by
    rw [smul_sub]
    simp only [smul_sub]
    abel
  have hRight :
      ((t : ℤ) • (oneChip (rightEndpoint B) - oneChip (leftEndpoint B)) +
        (oneChip (strandVertex B alpha p) - oneChip (leftEndpoint B))) -
      ((t : ℤ) • (oneChip (rightEndpoint B) - oneChip (leftEndpoint B)) +
        (oneChip (strandVertex B beta q) - oneChip (leftEndpoint B))) =
      oneChip (strandVertex B alpha p) - oneChip (strandVertex B beta q) := by
    abel
  rw [← hLeft, hRight] at h
  exact h

/-- The residue representative for an arbitrary evenly-marked theta
multiple.  This is the paper's `eq:multDiffMarkedPts` in normalized
coordinates. -/
theorem evenlyMarkedTheta_multiple_residue_linearEquiv
    (B : Banana 2) (alpha beta : Fin 3)
    (i : B.PathPosition alpha) (j : B.PathPosition beta)
    (hEven : EvenlyMarkedTheta B alpha beta i j) (m : ℕ) :
    linearEquiv B.graph
      ((m : ℤ) •
        (oneChip (strandVertex B alpha i) - oneChip (strandVertex B beta j)))
      (oneChip (strandVertex B alpha
          ⟨(m * i.val) % B.length alpha,
            by
              have h := Nat.mod_lt (m * i.val) (B.length_pos alpha)
              omega⟩) -
        oneChip (strandVertex B beta
          ⟨(m * j.val) % B.length beta,
            by
              have h := Nat.mod_lt (m * j.val) (B.length_pos beta)
              omega⟩)) := by
  let p : B.PathPosition alpha :=
    ⟨(m * i.val) % B.length alpha, by
      have h := Nat.mod_lt (m * i.val) (B.length_pos alpha)
      omega⟩
  let q : B.PathPosition beta :=
    ⟨(m * j.val) % B.length beta, by
      have h := Nat.mod_lt (m * j.val) (B.length_pos beta)
      omega⟩
  let t := m * i.val / B.length alpha
  have hdecomp := evenlyMarkedTheta_mul_residue_decompositions
    B alpha beta i j hEven m
  change linearEquiv B.graph
      ((m : ℤ) •
        (oneChip (strandVertex B alpha i) - oneChip (strandVertex B beta j)))
      (oneChip (strandVertex B alpha p) - oneChip (strandVertex B beta q))
  exact theta_multiple_residue_linearEquiv B alpha beta i p j q m t
    (by simpa [p, t] using hdecomp.1)
    (by simpa [q, t] using hdecomp.2)

/-- The canonical complement of an evenly-marked multiple has the reflected
first residue point and the second residue point as a representative. -/
theorem evenlyMarkedTheta_canonical_sub_multiple_residue_linearEquiv
    (B : Banana 2) (alpha beta : Fin 3)
    (i : B.PathPosition alpha) (j : B.PathPosition beta)
    (hEven : EvenlyMarkedTheta B alpha beta i j) (m : ℕ) :
    linearEquiv B.graph
      (canonicalDivisor B.graph - (m : ℤ) •
        (oneChip (strandVertex B alpha i) - oneChip (strandVertex B beta j)))
      (oneChip (strandVertex B alpha
          (strandMirror B alpha ⟨(m * i.val) % B.length alpha, by
            have h := Nat.mod_lt (m * i.val) (B.length_pos alpha)
            omega⟩)) +
        oneChip (strandVertex B beta ⟨(m * j.val) % B.length beta, by
          have h := Nat.mod_lt (m * j.val) (B.length_pos beta)
          omega⟩)) := by
  let p : B.PathPosition alpha := ⟨(m * i.val) % B.length alpha, by
    have h := Nat.mod_lt (m * i.val) (B.length_pos alpha)
    omega⟩
  let q : B.PathPosition beta := ⟨(m * j.val) % B.length beta, by
    have h := Nat.mod_lt (m * j.val) (B.length_pos beta)
    omega⟩
  have hMult := evenlyMarkedTheta_multiple_residue_linearEquiv
    B alpha beta i j hEven m
  change linearEquiv B.graph
      (canonicalDivisor B.graph - (m : ℤ) •
        (oneChip (strandVertex B alpha i) - oneChip (strandVertex B beta j)))
      (oneChip (strandVertex B alpha (strandMirror B alpha p)) +
        oneChip (strandVertex B beta q))
  have hCan : canonicalDivisor B.graph =
      oneChip (leftEndpoint B) + oneChip (rightEndpoint B) := by
    simpa using canonical_divisor_eq_endpoints B
  have hRef0 := endpoint_sum_linearEquiv_strand_reflection B alpha p
  have hRef : linearEquiv B.graph (canonicalDivisor B.graph)
      (oneChip (strandVertex B alpha p) +
        oneChip (strandVertex B alpha (strandMirror B alpha p))) := by
    rw [hCan]
    exact hRef0
  have hFirst : linearEquiv B.graph
      (canonicalDivisor B.graph - (m : ℤ) •
        (oneChip (strandVertex B alpha i) - oneChip (strandVertex B beta j)))
      (canonicalDivisor B.graph -
        (oneChip (strandVertex B alpha p) - oneChip (strandVertex B beta q))) := by
    unfold linearEquiv at hMult ⊢
    have hDiff :
        (canonicalDivisor B.graph -
          (oneChip (strandVertex B alpha p) - oneChip (strandVertex B beta q))) -
        (canonicalDivisor B.graph - (m : ℤ) •
          (oneChip (strandVertex B alpha i) - oneChip (strandVertex B beta j))) =
        - ((oneChip (strandVertex B alpha p) - oneChip (strandVertex B beta q)) -
          (m : ℤ) • (oneChip (strandVertex B alpha i) - oneChip (strandVertex B beta j))) := by
      abel
    rw [hDiff]
    exact (principalDivisors B.graph).neg_mem hMult
  have hSecond : linearEquiv B.graph
      (canonicalDivisor B.graph -
        (oneChip (strandVertex B alpha p) - oneChip (strandVertex B beta q)))
      ((oneChip (strandVertex B alpha p) +
        oneChip (strandVertex B alpha (strandMirror B alpha p))) -
        (oneChip (strandVertex B alpha p) - oneChip (strandVertex B beta q))) := by
    unfold linearEquiv at hRef ⊢
    have hDiff :
        ((oneChip (strandVertex B alpha p) +
          oneChip (strandVertex B alpha (strandMirror B alpha p))) -
          (oneChip (strandVertex B alpha p) - oneChip (strandVertex B beta q))) -
        (canonicalDivisor B.graph -
          (oneChip (strandVertex B alpha p) - oneChip (strandVertex B beta q))) =
        (oneChip (strandVertex B alpha p) +
          oneChip (strandVertex B alpha (strandMirror B alpha p))) -
          canonicalDivisor B.graph := by abel
    rw [hDiff]
    exact hRef
  have hCancel : linearEquiv B.graph
      (canonicalDivisor B.graph -
        (oneChip (strandVertex B alpha p) - oneChip (strandVertex B beta q)))
      (oneChip (strandVertex B alpha (strandMirror B alpha p)) +
        oneChip (strandVertex B beta q)) := by
    convert hSecond using 1 ; abel
  exact hFirst.trans hCancel

private theorem linear_equiv_sub_right' {G : CFGraph} {A B C : CFDiv G}
    (hAB : linearEquiv G A B) :
    linearEquiv G (C - A) (C - B) := by
  unfold linearEquiv at hAB ⊢
  have h : (C - B) - (C - A) = -(B - A) := by abel
  rw [h]
  exact (principalDivisors G).neg_mem hAB

private theorem linear_equiv_sub_left' {G : CFGraph} {A B C : CFDiv G}
    (hAB : linearEquiv G A B) :
    linearEquiv G (A - C) (B - C) := by
  unfold linearEquiv at hAB ⊢
  have h : (B - C) - (A - C) = B - A := by abel
  rw [h]
  exact hAB

/-- Rank support is invariant under linear equivalence of the ambient
divisor. -/
theorem rankSupport_eq_of_linearEquiv {G : CFGraph} {A B : CFDiv G}
    (hAB : linearEquiv G A B) :
    rankSupport G A = rankSupport G B := by
  ext w
  change 0 ≤ rank G (A - oneChip w) ↔ 0 ≤ rank G (B - oneChip w)
  rw [rank_eq_of_linear_equiv G
    (linear_equiv_sub_left' hAB (C := oneChip w))]

/-- In the no-wrap range, the canonical complement of a multiple of the
marked difference is represented by the reflection of the first advanced
point together with the second advanced point. -/
theorem theta_canonical_sub_multiple_noWrap_linearEquiv
    (B : Banana 2) (alpha beta : Fin 3)
    (i : B.PathPosition alpha) (j : B.PathPosition beta) (n : ℕ)
    (hni : n * i.val ≤ B.length alpha)
    (hnj : n * j.val ≤ B.length beta) :
    linearEquiv B.graph
      (canonicalDivisor B.graph - (n : ℤ) •
        (oneChip (strandVertex B alpha i) - oneChip (strandVertex B beta j)))
      (oneChip (strandVertex B alpha
          (strandMirror B alpha ⟨n * i.val, by omega⟩)) +
        oneChip (strandVertex B beta ⟨n * j.val, by omega⟩)) := by
  let p : B.PathPosition alpha := ⟨n * i.val, by omega⟩
  let q : B.PathPosition beta := ⟨n * j.val, by omega⟩
  have hMult := theta_multiple_noWrap_linearEquiv B alpha beta i j n hni hnj
  change linearEquiv B.graph
      (canonicalDivisor B.graph - (n : ℤ) •
        (oneChip (strandVertex B alpha i) - oneChip (strandVertex B beta j)))
      (oneChip (strandVertex B alpha (strandMirror B alpha p)) +
        oneChip (strandVertex B beta q))
  have hCan : canonicalDivisor B.graph =
      oneChip (leftEndpoint B) + oneChip (rightEndpoint B) := by
    simpa using canonical_divisor_eq_endpoints B
  have hRef0 := endpoint_sum_linearEquiv_strand_reflection B alpha p
  have hRef : linearEquiv B.graph (canonicalDivisor B.graph)
      (oneChip (strandVertex B alpha p) +
        oneChip (strandVertex B alpha (strandMirror B alpha p))) := by
    rw [hCan]
    exact hRef0
  have hFirst := linear_equiv_sub_right' (C := canonicalDivisor B.graph) hMult
  have hSecond := linear_equiv_sub_left' hRef
    (C := oneChip (strandVertex B alpha p) - oneChip (strandVertex B beta q))
  have hCancel : linearEquiv B.graph
      (canonicalDivisor B.graph -
        (oneChip (strandVertex B alpha p) - oneChip (strandVertex B beta q)))
      (oneChip (strandVertex B alpha (strandMirror B alpha p)) +
        oneChip (strandVertex B beta q)) := by
    convert hSecond using 1 ; abel
  exact hFirst.trans hCancel

/-- The indicator characterization makes a raw transmission permutation
unique. -/
theorem transmissionPermutation_unique
    {M : TwiceMarked} {D : CFDiv M.graph} {τ σ : ℤ → ℤ}
    (hτ : IsTransmissionPermutation M D τ)
    (hσ : IsTransmissionPermutation M D σ) :
    τ = σ := by
  funext b
  by_contra hne
  have hσb : (1 : ℤ) = rankDelta M
      (D + (σ b) • oneChip M.u - b • oneChip M.v) := by
    simpa using hσ.2 (σ b) b
  have hτb : (0 : ℤ) = rankDelta M
      (D + (σ b) • oneChip M.u - b • oneChip M.v) := by
    simpa [hne] using hτ.2 (σ b) b
  omega

/-- Any raw transmission permutation is the function underlying the ASP
permutation whose slipface is the marked rank surface. -/
theorem transmissionPermutation_rankSlipFace
    (M : TwiceMarked) (D : CFDiv M.graph)
    (hconn : _root_.graphConnected M.graph) (τ : ℤ → ℤ)
    (hτ : IsTransmissionPermutation M D τ) :
    ∃ σ : AspPerm,
      σ.func = τ ∧
        σ.s = rankSlipFace M (D - oneChip M.u) hconn := by
  have hsub :
      (rankSlipFace M (D - oneChip M.u) hconn).submodular := by
    intro a b
    rw [rankSlipFace_Delta]
    have hDiv :
        D - oneChip M.u + (a + 1) • oneChip M.u -
            b • oneChip M.v =
          D + a • oneChip M.u - b • oneChip M.v := by
      rw [add_smul, one_smul]
      abel
    rw [hDiv, ← hτ.2 a b]
    split <;> omega
  obtain ⟨σ, hσSlip⟩ :=
    (Submodular.submodular_iff_asp
      (rankSlipFace M (D - oneChip M.u) hconn)).mp hsub
  have hσ : IsTransmissionPermutation M D σ.func := by
    refine ⟨σ.bijective, ?_⟩
    intro a b
    rw [← σ.Delta_eq a b, hσSlip, rankSlipFace_Delta]
    have hDiv :
        D - oneChip M.u + (a + 1) • oneChip M.u -
            b • oneChip M.v =
          D + a • oneChip M.u - b • oneChip M.v := by
      rw [add_smul, one_smul]
      abel
    rw [hDiv]
  exact ⟨σ, transmissionPermutation_unique hσ hτ, hσSlip⟩

/-- Paper Lemma `lem:tauChars`, southeast/rank form. -/
theorem transmission_rank_eq_southeast_ncard
    (M : TwiceMarked) (D : CFDiv M.graph)
    (hconn : _root_.graphConnected M.graph) (τ : ℤ → ℤ)
    (hτ : IsTransmissionPermutation M D τ) (a b : ℤ) :
    rank M.graph (D + a • oneChip M.u - b • oneChip M.v) + 1 =
      (southeastSet τ (a + 1) b).ncard := by
  obtain ⟨σ, hστ, hσSlip⟩ :=
    transmissionPermutation_rankSlipFace M D hconn τ hτ
  have hDiv :
      D - oneChip M.u + (a + 1) • oneChip M.u -
          b • oneChip M.v =
        D + a • oneChip M.u - b • oneChip M.v := by
    rw [add_smul, one_smul]
    abel
  calc
    rank M.graph (D + a • oneChip M.u - b • oneChip M.v) + 1 =
        rankSlipFace M (D - oneChip M.u) hconn (a + 1) b := by
          rw [rankSlipFace_apply, hDiv]
    _ = σ.s (a + 1) b := by rw [hσSlip]
    _ = (southeastSet σ.func (a + 1) b).ncard := σ.s_eq_ncard _ _
    _ = (southeastSet τ (a + 1) b).ncard := by rw [hστ]

/-- Paper Lemma `lem:tauChars`, northwest/canonical-complement form. -/
theorem transmission_complement_rank_eq_northwest_ncard
    (M : TwiceMarked) (D : CFDiv M.graph)
    (hconn : _root_.graphConnected M.graph) (τ : ℤ → ℤ)
    (hτ : IsTransmissionPermutation M D τ) (a b : ℤ) :
    rank M.graph
        (canonicalDivisor M.graph - D - a • oneChip M.u +
          b • oneChip M.v) + 1 =
      (northwestSet τ (a + 1) b).ncard := by
  obtain ⟨σ, hστ, hσSlip⟩ :=
    transmissionPermutation_rankSlipFace M D hconn τ hτ
  let X : CFDiv M.graph :=
    D + a • oneChip M.u - b • oneChip M.v
  have hComplement :
      canonicalDivisor M.graph - X =
        canonicalDivisor M.graph - D - a • oneChip M.u +
          b • oneChip M.v := by
    dsimp [X]
    abel
  have hRR := riemann_roch_for_graphs hconn X
  have hDegX : deg X = deg D + a - b := by
    dsimp [X]
    rw [deg.map_sub, deg.map_add, map_zsmul, map_zsmul,
      deg_one_chip, deg_one_chip]
    simp
  have hSlipApply :
      σ.s (a + 1) b = rank M.graph X + 1 := by
    rw [hσSlip, rankSlipFace_apply]
    have hDiv :
        D - oneChip M.u + (a + 1) • oneChip M.u -
            b • oneChip M.v = X := by
      dsimp [X]
      rw [add_smul, one_smul]
      abel
    rw [hDiv]
  have hChi : σ.χ = deg D - genus M.graph := by
    have hChi' := rankSlipFace_chi M (D - oneChip M.u) hconn
    rw [← hσSlip] at hChi'
    simpa only [AspPerm.s_chi_eq] using hChi'
      |>.trans (by
        rw [deg.map_sub, deg_one_chip]
        ring)
  have hDual := σ.duality (a + 1) b
  have hRankEq :
      rank M.graph (canonicalDivisor M.graph - X) + 1 =
        (σ⁻¹).s b (a + 1) := by
    omega
  calc
    rank M.graph
        (canonicalDivisor M.graph - D - a • oneChip M.u +
          b • oneChip M.v) + 1 =
        rank M.graph (canonicalDivisor M.graph - X) + 1 := by rw [hComplement]
    _ = (σ⁻¹).s b (a + 1) := hRankEq
    _ = (northwestSet σ.func (a + 1) b).ncard := σ.s'_eq_ncard _ _
    _ = (northwestSet τ (a + 1) b).ncard := by rw [hστ]

/-! ## The geometric support input for evenly marked theta graphs -/

/-- A pair of chips on distinct interior strands of a theta has rank support
exactly at the two chip locations.  This is paper Corollary `cor:suppUV` in
the form needed for the non-recurrence argument. -/
theorem rankSupport_two_distinct_interior_strand_chips
    (B : Banana 2) (alpha beta : Fin 3)
    (p : B.PathPosition alpha) (q : B.PathPosition beta)
    (hp : B.IsInteriorPosition alpha p)
    (hq : B.IsInteriorPosition beta q) (hab : alpha ≠ beta) :
    rankSupport B.graph
        (oneChip (strandVertex B alpha p) +
          oneChip (strandVertex B beta q)) =
      {strandVertex B alpha p, strandVertex B beta q} := by
  let x := strandVertex B alpha p
  let y := strandVertex B beta q
  let E : CFDiv B.graph := oneChip x + oneChip y
  have hxy : x ≠ y := by
    intro h
    exact hab (strand_eq_of_interior_vertex_eq B alpha beta p q hp hq h)
  have hSemi : IsSemibreak B E := by
    dsimp [E, x, y]
    exact isSemibreak_two_distinct_strand_chips B alpha beta p q hp hq hab
  have hDeg : deg E ≤ (2 : ℤ) := by
    dsimp [E]
    rw [deg.map_add, deg_one_chip, deg_one_chip]
    norm_num
  ext w
  constructor
  · intro hw
    by_contra hn
    have hnx : w ≠ x := by
      intro hwx
      apply hn
      simp [x, hwx]
    have hny : w ≠ y := by
      intro hwy
      apply hn
      simp [y, hwy]
    have hEw : E w = 0 := by
      dsimp [E]
      simp only [oneChip, if_neg hnx, if_neg hny, add_zero]
    have hRank := rank_semibreak_sub_vertex_eq_neg_one B E hSemi hDeg w hEw
    have hw' : 0 ≤ rank B.graph (E - oneChip w) := by
      simpa [rankSupport, E, x, y] using hw
    omega
  · intro hw
    rcases hw with rfl | rfl
    · have hDiv : E - oneChip x = oneChip y := by
        dsimp [E]
        abel
      have hRank : rank B.graph (E - oneChip x) = 0 := by
        rw [hDiv]
        exact rank_one_chip_zero_banana_two B y
      simpa [rankSupport, E, x, y] using hRank.ge
    · have hDiv : E - oneChip y = oneChip x := by
        dsimp [E]
        abel
      have hRank : rank B.graph (E - oneChip y) = 0 := by
        rw [hDiv]
        exact rank_one_chip_zero_banana_two B x
      simpa [rankSupport, E, x, y] using hRank.ge

/-- The preceding canonical representative has exactly its two visible
interior chips as rank support. -/
theorem rankSupport_canonical_sub_multiple_noWrap
    (B : Banana 2) (alpha beta : Fin 3)
    (i : B.PathPosition alpha) (j : B.PathPosition beta) (n : ℕ)
    (hni : n * i.val ≤ B.length alpha)
    (hnj : n * j.val ≤ B.length beta) (hab : alpha ≠ beta)
    (hp : B.IsInteriorPosition alpha
      (strandMirror B alpha ⟨n * i.val, by omega⟩))
    (hq : B.IsInteriorPosition beta ⟨n * j.val, by omega⟩) :
    rankSupport B.graph
      (canonicalDivisor B.graph - (n : ℤ) •
        (oneChip (strandVertex B alpha i) - oneChip (strandVertex B beta j))) =
      {strandVertex B alpha (strandMirror B alpha ⟨n * i.val, by omega⟩),
        strandVertex B beta ⟨n * j.val, by omega⟩} := by
  let p : B.PathPosition alpha := ⟨n * i.val, by omega⟩
  let q : B.PathPosition beta := ⟨n * j.val, by omega⟩
  have hComp := theta_canonical_sub_multiple_noWrap_linearEquiv
    B alpha beta i j n hni hnj
  change rankSupport B.graph
      (canonicalDivisor B.graph - (n : ℤ) •
        (oneChip (strandVertex B alpha i) - oneChip (strandVertex B beta j))) =
      {strandVertex B alpha (strandMirror B alpha p), strandVertex B beta q}
  rw [rankSupport_eq_of_linearEquiv hComp]
  exact rankSupport_two_distinct_interior_strand_chips B alpha beta
    (strandMirror B alpha p) q hp hq hab

/-- In the nonzero part of its exact period, an evenly-marked theta multiple
has a canonical complement with rank support exactly at its two residue
points (with the first one reflected). -/
theorem rankSupport_evenlyMarkedTheta_canonical_sub_multiple_residue
    (B : Banana 2) (alpha beta : Fin 3)
    (i : B.PathPosition alpha) (j : B.PathPosition beta)
    (hEven : EvenlyMarkedTheta B alpha beta i j) (m : ℕ)
    (hm0 : 0 < m)
    (hmk : m < B.length alpha / Nat.gcd (B.length alpha) i.val) :
    rankSupport B.graph
      (canonicalDivisor B.graph - (m : ℤ) •
        (oneChip (strandVertex B alpha i) - oneChip (strandVertex B beta j))) =
      {strandVertex B alpha
          (strandMirror B alpha ⟨(m * i.val) % B.length alpha, by
            have h := Nat.mod_lt (m * i.val) (B.length_pos alpha)
            omega⟩),
        strandVertex B beta ⟨(m * j.val) % B.length beta, by
          have h := Nat.mod_lt (m * j.val) (B.length_pos beta)
          omega⟩} := by
  let p : B.PathPosition alpha := ⟨(m * i.val) % B.length alpha, by
    have h := Nat.mod_lt (m * i.val) (B.length_pos alpha)
    omega⟩
  let q : B.PathPosition beta := ⟨(m * j.val) % B.length beta, by
    have h := Nat.mod_lt (m * j.val) (B.length_pos beta)
    omega⟩
  have hres := evenlyMarkedTheta_residues_ne_zero B alpha beta i j hEven hm0 hmk
  have hp : B.IsInteriorPosition alpha p := by
    change 0 < p.val ∧ p.val < B.length alpha
    dsimp [p]
    exact ⟨Nat.pos_of_ne_zero hres.1, Nat.mod_lt _ (B.length_pos alpha)⟩
  have hpMirror : B.IsInteriorPosition alpha (strandMirror B alpha p) := by
    change 0 < B.length alpha - p.val ∧ B.length alpha - p.val < B.length alpha
    exact ⟨Nat.sub_pos_of_lt hp.2, Nat.sub_lt (B.length_pos alpha) hp.1⟩
  have hq : B.IsInteriorPosition beta q := by
    change 0 < q.val ∧ q.val < B.length beta
    dsimp [q]
    exact ⟨Nat.pos_of_ne_zero hres.2, Nat.mod_lt _ (B.length_pos beta)⟩
  have hComp := evenlyMarkedTheta_canonical_sub_multiple_residue_linearEquiv
    B alpha beta i j hEven m
  change rankSupport B.graph
      (canonicalDivisor B.graph - (m : ℤ) •
        (oneChip (strandVertex B alpha i) - oneChip (strandVertex B beta j))) =
      {strandVertex B alpha (strandMirror B alpha p), strandVertex B beta q}
  rw [rankSupport_eq_of_linearEquiv hComp]
  exact rankSupport_two_distinct_interior_strand_chips B alpha beta
    (strandMirror B alpha p) q hpMirror hq hEven.1

/-- Two cross-strand two-chip supports are disjoint when the positions on
both strands are distinct. -/
theorem disjoint_rankSupport_two_distinct_interior_strand_chips
    (B : Banana 2) (alpha beta : Fin 3)
    (p p' : B.PathPosition alpha) (q q' : B.PathPosition beta)
    (hp : B.IsInteriorPosition alpha p)
    (hp' : B.IsInteriorPosition alpha p')
    (hq : B.IsInteriorPosition beta q)
    (hq' : B.IsInteriorPosition beta q') (hab : alpha ≠ beta)
    (hpp : p.val ≠ p'.val) (hqq : q.val ≠ q'.val) :
    Disjoint
      (rankSupport B.graph
        (oneChip (strandVertex B alpha p) + oneChip (strandVertex B beta q)))
      (rankSupport B.graph
        (oneChip (strandVertex B alpha p') + oneChip (strandVertex B beta q'))) := by
  rw [rankSupport_two_distinct_interior_strand_chips B alpha beta p q hp hq hab,
    rankSupport_two_distinct_interior_strand_chips B alpha beta p' q' hp' hq' hab]
  rw [Set.disjoint_left]
  intro w hw hw'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw hw'
  rcases hw with hwp | hwq <;> rcases hw' with hwp' | hwq'
  · have hpp' := strandVertex_injective B alpha (hwp.symm.trans hwp')
    exact hpp (congrArg Fin.val hpp')
  · exact hab (strand_eq_of_interior_vertex_eq B alpha beta p q' hp hq'
      (hwp.symm.trans hwq'))
  · exact hab.symm (strand_eq_of_interior_vertex_eq B beta alpha q p' hq hp'
      (hwq.symm.trans hwp'))
  · have hqq' := strandVertex_injective B beta (hwq.symm.trans hwq')
    exact hqq (congrArg Fin.val hqq')

/-- Distinct nonzero residues in one evenly-marked theta period have disjoint
canonical rank supports.  This is the geometric nonrecurrence input of
Lemma 4.15. -/
theorem disjoint_rankSupport_evenlyMarkedTheta_canonical_sub_multiple_residue
    (B : Banana 2) (alpha beta : Fin 3)
    (i : B.PathPosition alpha) (j : B.PathPosition beta)
    (hEven : EvenlyMarkedTheta B alpha beta i j) (m n : ℕ)
    (hm0 : 0 < m) (hn0 : 0 < n)
    (hmk : m < B.length alpha / Nat.gcd (B.length alpha) i.val)
    (hnk : n < B.length alpha / Nat.gcd (B.length alpha) i.val)
    (hmn : m ≠ n) :
    Disjoint
      (rankSupport B.graph
        (canonicalDivisor B.graph - (m : ℤ) •
          (oneChip (strandVertex B alpha i) - oneChip (strandVertex B beta j))))
      (rankSupport B.graph
        (canonicalDivisor B.graph - (n : ℤ) •
          (oneChip (strandVertex B alpha i) - oneChip (strandVertex B beta j)))) := by
  let pm : B.PathPosition alpha := ⟨(m * i.val) % B.length alpha, by
    have h := Nat.mod_lt (m * i.val) (B.length_pos alpha)
    omega⟩
  let pn : B.PathPosition alpha := ⟨(n * i.val) % B.length alpha, by
    have h := Nat.mod_lt (n * i.val) (B.length_pos alpha)
    omega⟩
  let qm : B.PathPosition beta := ⟨(m * j.val) % B.length beta, by
    have h := Nat.mod_lt (m * j.val) (B.length_pos beta)
    omega⟩
  let qn : B.PathPosition beta := ⟨(n * j.val) % B.length beta, by
    have h := Nat.mod_lt (n * j.val) (B.length_pos beta)
    omega⟩
  have hpm : B.IsInteriorPosition alpha pm := by
    change 0 < pm.val ∧ pm.val < B.length alpha
    have h := evenlyMarkedTheta_residues_ne_zero B alpha beta i j hEven hm0 hmk
    dsimp [pm]
    exact ⟨Nat.pos_of_ne_zero h.1, Nat.mod_lt _ (B.length_pos alpha)⟩
  have hpn : B.IsInteriorPosition alpha pn := by
    change 0 < pn.val ∧ pn.val < B.length alpha
    have h := evenlyMarkedTheta_residues_ne_zero B alpha beta i j hEven hn0 hnk
    dsimp [pn]
    exact ⟨Nat.pos_of_ne_zero h.1, Nat.mod_lt _ (B.length_pos alpha)⟩
  have hqm : B.IsInteriorPosition beta qm := by
    change 0 < qm.val ∧ qm.val < B.length beta
    have h := evenlyMarkedTheta_residues_ne_zero B alpha beta i j hEven hm0 hmk
    dsimp [qm]
    exact ⟨Nat.pos_of_ne_zero h.2, Nat.mod_lt _ (B.length_pos beta)⟩
  have hqn : B.IsInteriorPosition beta qn := by
    change 0 < qn.val ∧ qn.val < B.length beta
    have h := evenlyMarkedTheta_residues_ne_zero B alpha beta i j hEven hn0 hnk
    dsimp [qn]
    exact ⟨Nat.pos_of_ne_zero h.2, Nat.mod_lt _ (B.length_pos beta)⟩
  have hpmPn : pm.val ≠ pn.val := by
    intro h
    apply hmn
    apply evenlyMarkedTheta_alpha_residue_injective B alpha beta i j hEven hmk hnk
    simpa [pm, pn] using h
  have hqmQn : qm.val ≠ qn.val := by
    intro h
    apply hmn
    apply evenlyMarkedTheta_beta_residue_injective B alpha beta i j hEven hmk hnk
    simpa [qm, qn] using h
  have hMirror : (strandMirror B alpha pm).val ≠
      (strandMirror B alpha pn).val := by
    simp only [strandMirror]
    omega
  rw [rankSupport_evenlyMarkedTheta_canonical_sub_multiple_residue
      B alpha beta i j hEven m hm0 hmk,
    rankSupport_evenlyMarkedTheta_canonical_sub_multiple_residue
      B alpha beta i j hEven n hn0 hnk]
  have hDisjoint := disjoint_rankSupport_two_distinct_interior_strand_chips B alpha beta
    (strandMirror B alpha pm) (strandMirror B alpha pn) qm qn
    (by
      change 0 < B.length alpha - pm.val ∧ B.length alpha - pm.val < B.length alpha
      exact ⟨Nat.sub_pos_of_lt hpm.2, Nat.sub_lt (B.length_pos alpha) hpm.1⟩)
    (by
      change 0 < B.length alpha - pn.val ∧ B.length alpha - pn.val < B.length alpha
      exact ⟨Nat.sub_pos_of_lt hpn.2, Nat.sub_lt (B.length_pos alpha) hpn.1⟩)
    hqm hqn hEven.1 hMirror hqmQn
  rw [rankSupport_two_distinct_interior_strand_chips B alpha beta
      (strandMirror B alpha pm) qm
      (by
        change 0 < B.length alpha - pm.val ∧ B.length alpha - pm.val < B.length alpha
        exact ⟨Nat.sub_pos_of_lt hpm.2, Nat.sub_lt (B.length_pos alpha) hpm.1⟩)
      hqm hEven.1,
    rankSupport_two_distinct_interior_strand_chips B alpha beta
      (strandMirror B alpha pn) qn
      (by
        change 0 < B.length alpha - pn.val ∧ B.length alpha - pn.val < B.length alpha
        exact ⟨Nat.sub_pos_of_lt hpn.2, Nat.sub_lt (B.length_pos alpha) hpn.1⟩)
      hqn hEven.1] at hDisjoint
  simpa [pm, pn, qm, qn] using hDisjoint

/-- On a genus-two banana, any effective degree-one marked twist puts its
visible chip into the rank support of the canonical complement. -/
private theorem mem_rankSupport_canonical_sub_of_rank_nonneg
    (B : Banana 2) (u v w : B.graph.V) (n : ℕ)
    (hRank : 0 ≤ rank B.graph
      (oneChip w + (n : ℤ) • (oneChip u - oneChip v))) :
    w ∈ rankSupport B.graph
      (canonicalDivisor B.graph - (n : ℤ) • (oneChip u - oneChip v)) := by
  let X : CFDiv B.graph :=
    oneChip w + (n : ℤ) • (oneChip u - oneChip v)
  have hDeg : deg X = 1 := by
    dsimp [X]
    rw [deg.map_add, deg_one_chip, map_zsmul, deg.map_sub,
      deg_one_chip, deg_one_chip]
    norm_num
  have hRR := riemann_roch_for_graphs (graphConnected B) X
  rw [B.genus_graph, hDeg] at hRR
  have hDual : rank B.graph (canonicalDivisor B.graph - X) = rank B.graph X := by
    omega
  change 0 ≤ rank B.graph
    ((canonicalDivisor B.graph - (n : ℤ) • (oneChip u - oneChip v)) -
      oneChip w)
  have hRewrite :
      (canonicalDivisor B.graph - (n : ℤ) • (oneChip u - oneChip v)) -
          oneChip w = canonicalDivisor B.graph - X := by
    dsimp [X]
    abel
  rw [hRewrite]
  rw [hDual]
  exact hRank

/-- Evenly-marked theta marks satisfy the paper's nonrecurrence condition:
no vertex is effective in two distinct nonzero torsion-residue twists. -/
theorem evenlyMarkedTheta_nonRecurrent
    (B : Banana 2) (alpha beta : Fin 3)
    (i : B.PathPosition alpha) (j : B.PathPosition beta)
    (hEven : EvenlyMarkedTheta B alpha beta i j) :
    NonRecurrent
      (mark B.graph (strandVertex B alpha i) (strandVertex B beta j))
      (B.length alpha / Nat.gcd (B.length alpha) i.val) := by
  intro w n m hn0 hm0 hn hm
  by_contra hne
  have hval : n.val ≠ m.val := by
    intro h
    apply hne
    exact Fin.ext h
  have hDisjoint :=
    disjoint_rankSupport_evenlyMarkedTheta_canonical_sub_multiple_residue
      B alpha beta i j hEven n.val m.val
      (Nat.pos_of_ne_zero hn0) (Nat.pos_of_ne_zero hm0)
      n.isLt m.isLt hval
  have hnMem := mem_rankSupport_canonical_sub_of_rank_nonneg B
    (strandVertex B alpha i) (strandVertex B beta j) w n.val hn
  have hmMem := mem_rankSupport_canonical_sub_of_rank_nonneg B
    (strandVertex B alpha i) (strandVertex B beta j) w m.val hm
  exact (Set.disjoint_left.mp hDisjoint) hnMem hmMem

/-- The two evenly-marked theta chips form a rank-zero semibreak divisor.
This is the rigidity condition that eliminates the exceptional correction in
the genus-two inversion formula. -/
theorem evenlyMarkedTheta_mark_pair_rank_zero
    (B : Banana 2) (alpha beta : Fin 3)
    (i : B.PathPosition alpha) (j : B.PathPosition beta)
    (hEven : EvenlyMarkedTheta B alpha beta i j) :
    rank B.graph
      (oneChip (strandVertex B alpha i) + oneChip (strandVertex B beta j)) = 0 := by
  have hSemi : IsSemibreak B
      (oneChip (strandVertex B alpha i) + oneChip (strandVertex B beta j)) := by
    exact isSemibreak_two_distinct_strand_chips B alpha beta i j
      ⟨hEven.2.1, hEven.2.2.1⟩ ⟨hEven.2.2.2.1, hEven.2.2.2.2.1⟩ hEven.1
  apply rank_semibreak_eq_zero B _ hSemi
  rw [deg.map_add, deg_one_chip, deg_one_chip]
  norm_num

/-- An evenly-marked pair is not linearly equivalent to the canonical
divisor. -/
theorem evenlyMarkedTheta_mark_pair_not_linearEquiv_canonical
    (B : Banana 2) (alpha beta : Fin 3)
    (i : B.PathPosition alpha) (j : B.PathPosition beta)
    (hEven : EvenlyMarkedTheta B alpha beta i j) :
    ¬ linearEquiv B.graph
      (oneChip (strandVertex B alpha i) + oneChip (strandVertex B beta j))
      (canonicalDivisor B.graph) := by
  intro hEq
  have hPair := evenlyMarkedTheta_mark_pair_rank_zero B alpha beta i j hEven
  have hRankEq := rank_eq_of_linear_equiv B.graph hEq
  have hKRank : rank B.graph (canonicalDivisor B.graph) = 1 := by
    have hRR := riemann_roch_for_graphs (graphConnected B)
      (canonicalDivisor B.graph)
    rw [sub_self, zero_divisor_rank, degree_of_canonical_divisor,
      B.genus_graph] at hRR
    omega
  omega

end Bananas
