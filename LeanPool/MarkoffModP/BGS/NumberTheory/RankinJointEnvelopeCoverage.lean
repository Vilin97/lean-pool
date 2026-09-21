/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Assembly.ExactOrderRankinEnvelope

/-!
# Finite coverage for side-erased Rankin envelopes

A generated profile need not equal the canonical profile of `p`.  It is
enough that it has a larger failure square and a smaller factorization floor.
Those two inequalities transport both kinds of terminal leaf.  This replaces
exact enumeration by domination: one checked profile can close an entire
family of exponent/floor skeletons.

The certificate below contains only data.  Lean checks every leaf, while a
separate coverage theorem must exhibit a dominating row for the actual
profile.  Thus generated arithmetic and mathematical exhaustiveness remain
distinct proof obligations.
-/

namespace BGS.NumberTheory

namespace RankinNeighborProfile

/-- `major` is a safe arithmetic representative for `actual`: its obstruction
upper bound is no smaller, and its factorization lower bound is no larger. -/
def JointEnvelopeDominates
    (major actual : RankinNeighborProfile) : Prop :=
  actual.jointEnvelopeFailureSquare ≤
      major.jointEnvelopeFailureSquare ∧
    major.jointLowerNeighborProduct ≤
      actual.jointLowerNeighborProduct

def jointEnvelopeDominatesCheck
    (major actual : RankinNeighborProfile) : Bool :=
  decide
    (actual.jointEnvelopeFailureSquare ≤
        major.jointEnvelopeFailureSquare ∧
      major.jointLowerNeighborProduct ≤
        actual.jointLowerNeighborProduct)

@[simp] theorem jointEnvelopeDominatesCheck_eq_true_iff
    (major actual : RankinNeighborProfile) :
    major.jointEnvelopeDominatesCheck actual = true ↔
      major.JointEnvelopeDominates actual := by
  simp [jointEnvelopeDominatesCheck, JointEnvelopeDominates]

theorem jointEnvelopeDominates_refl
    (profile : RankinNeighborProfile) :
    profile.JointEnvelopeDominates profile := by
  exact ⟨le_rfl, le_rfl⟩

theorem JointEnvelopeDominates.trans
    {first middle last : RankinNeighborProfile}
    (hfirst : first.JointEnvelopeDominates middle)
    (hmiddle : middle.JointEnvelopeDominates last) :
    first.JointEnvelopeDominates last := by
  exact ⟨hmiddle.1.trans hfirst.1, hfirst.2.trans hmiddle.2⟩

theorem eraseSides_jointEnvelopeDominates
    (profile : RankinNeighborProfile) :
    profile.eraseSides.JointEnvelopeDominates profile := by
  constructor
  · rw [eraseSides_jointEnvelopeFailureSquare]
  · rw [eraseSides_jointLowerNeighborProduct]

theorem jointEnvelopeClosesCutoff_of_dominates
    {major actual : RankinNeighborProfile} {cutoff : ℕ}
    (hdom : major.JointEnvelopeDominates actual)
    (hcloses : major.JointEnvelopeClosesCutoff cutoff) :
    actual.JointEnvelopeClosesCutoff cutoff := by
  exact hdom.1.trans_lt hcloses

theorem jointEnvelopeExcludesFailure_of_dominates
    {major actual : RankinNeighborProfile}
    (hdom : major.JointEnvelopeDominates actual)
    (hexcludes : major.JointEnvelopeExcludesFailure) :
    actual.JointEnvelopeExcludesFailure := by
  have hactualNonneg :
      (0 : ℚ) ≤ actual.jointEnvelopeFailureSquare := by
    rw [jointEnvelopeFailureSquare]
    positivity
  have hsquare :
      actual.jointEnvelopeFailureSquare ^ 2 ≤
        major.jointEnvelopeFailureSquare ^ 2 :=
    pow_le_pow_left₀ hactualNonneg hdom.1 2
  have hlower :
      ((64 * major.jointLowerNeighborProduct : ℕ) : ℚ) ≤
        ((64 * actual.jointLowerNeighborProduct : ℕ) : ℚ) := by
    exact_mod_cast Nat.mul_le_mul_left 64 hdom.2
  exact hsquare.trans_lt (hexcludes.trans_le hlower)

theorem jointEnvelope_leaf_of_dominates
    {major actual : RankinNeighborProfile} {cutoff : ℕ}
    (hdom : major.JointEnvelopeDominates actual)
    (hleaf : major.JointEnvelopeClosesCutoff cutoff ∨
      major.JointEnvelopeExcludesFailure) :
    actual.JointEnvelopeClosesCutoff cutoff ∨
      actual.JointEnvelopeExcludesFailure := by
  rcases hleaf with hcloses | hexcludes
  · exact Or.inl (jointEnvelopeClosesCutoff_of_dominates hdom hcloses)
  · exact Or.inr (jointEnvelopeExcludesFailure_of_dominates hdom hexcludes)

end RankinNeighborProfile

def allRankinJointEnvelopeLeavesValid
    (cutoff : ℕ) : List RankinNeighborProfile → Prop
  | [] => True
  | profile :: profiles =>
      profile.JointEnvelopeLeafValid cutoff ∧
        allRankinJointEnvelopeLeavesValid cutoff profiles

def allRankinJointEnvelopeLeavesCheck
    (cutoff : ℕ) : List RankinNeighborProfile → Bool
  | [] => true
  | profile :: profiles =>
      profile.jointEnvelopeLeafCheck cutoff &&
        allRankinJointEnvelopeLeavesCheck cutoff profiles

@[simp] theorem allRankinJointEnvelopeLeavesCheck_eq_true_iff
    (cutoff : ℕ) (profiles : List RankinNeighborProfile) :
    allRankinJointEnvelopeLeavesCheck cutoff profiles = true ↔
      allRankinJointEnvelopeLeavesValid cutoff profiles := by
  induction profiles with
  | nil =>
      simp [allRankinJointEnvelopeLeavesCheck,
        allRankinJointEnvelopeLeavesValid]
  | cons profile profiles ih =>
      simp [allRankinJointEnvelopeLeavesCheck,
        allRankinJointEnvelopeLeavesValid, ih]

private theorem jointEnvelopeLeafValid_of_all_of_mem
    {cutoff : ℕ} {profiles : List RankinNeighborProfile}
    (hall : allRankinJointEnvelopeLeavesValid cutoff profiles)
    {profile : RankinNeighborProfile} (hmem : profile ∈ profiles) :
    profile.JointEnvelopeLeafValid cutoff := by
  induction profiles with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [allRankinJointEnvelopeLeavesValid] at hall
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact hall.1
      · exact ih hall.2 hmem

/-- Pure generated data for a domination cover.  There are deliberately no
proof fields: the list is checked by reduction, and exhaustiveness is proved
separately through `Covers`. -/
structure RankinJointEnvelopeFiniteCertificate where
  cutoff : ℕ
  profiles : List RankinNeighborProfile
  deriving DecidableEq, Repr

namespace RankinJointEnvelopeFiniteCertificate

def LeavesValid (cert : RankinJointEnvelopeFiniteCertificate) : Prop :=
  allRankinJointEnvelopeLeavesValid cert.cutoff cert.profiles

def check (cert : RankinJointEnvelopeFiniteCertificate) : Bool :=
  allRankinJointEnvelopeLeavesCheck cert.cutoff cert.profiles

/-- Mathematical coverage of one actual profile by the generated rows. -/
def Covers
    (cert : RankinJointEnvelopeFiniteCertificate)
    (actual : RankinNeighborProfile) : Prop :=
  ∃ major ∈ cert.profiles, major.JointEnvelopeDominates actual

@[simp] theorem check_eq_true_iff
    (cert : RankinJointEnvelopeFiniteCertificate) :
    cert.check = true ↔ cert.LeavesValid := by
  simp [check, LeavesValid]

theorem jointEnvelope_leaf_of_check_of_covers
    {cert : RankinJointEnvelopeFiniteCertificate}
    {actual : RankinNeighborProfile}
    (hcheck : cert.check = true) (hcover : cert.Covers actual) :
    actual.JointEnvelopeClosesCutoff cert.cutoff ∨
      actual.JointEnvelopeExcludesFailure := by
  obtain ⟨major, hmem, hdom⟩ := hcover
  have hall : cert.LeavesValid := cert.check_eq_true_iff.mp hcheck
  have hmajor := jointEnvelopeLeafValid_of_all_of_mem hall hmem
  exact RankinNeighborProfile.jointEnvelope_leaf_of_dominates
    hdom hmajor.2.2

end RankinJointEnvelopeFiniteCertificate

end BGS.NumberTheory

namespace BGS.Markoff

open BGS.NumberTheory

/-- A checked finite domination cover discharges the arithmetic leaf in the
exact-order Rankin endpoint. -/
theorem prime_le_of_rankinJointEnvelopeFiniteCertificate
    {p bound : ℕ}
    (hpPrime : p.Prime) (hpTwo : 2 < p)
    (hroot :
      8 * p ≤ (combinedTruncatedOrderTotientSum p bound) ^ 2)
    (hboundWitness :
      bound ≤ 189 * (middleGameMaximalOrders p bound).card ^ 3)
    (actual : RankinNeighborProfile)
    (hactual : actual.Valid) (hmatch : actual.Matches p)
    (cert : RankinJointEnvelopeFiniteCertificate)
    (hcheck : cert.check = true) (hcover : cert.Covers actual) :
    p ≤ cert.cutoff := by
  apply prime_le_of_matching_rankinNeighborProfile_jointEnvelope_leaf
    hpPrime hpTwo hroot hboundWitness actual hactual hmatch
  exact cert.jointEnvelope_leaf_of_check_of_covers hcheck hcover

end BGS.Markoff
