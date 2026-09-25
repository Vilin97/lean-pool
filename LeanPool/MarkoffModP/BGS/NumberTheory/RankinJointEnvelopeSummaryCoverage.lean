/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.NumberTheory.RankinJointEnvelopeCoverage

/-!
# Scalar summaries for Rankin-envelope coverage

A domination leaf does not need to be a structurally valid neighbor profile.
The exact-order endpoint only uses an upper bound for the joint failure square
and a lower bound for the joint factorization product.  Recording just those
two monotone quantities lets one generated row summarize a whole box of
exponent skeletons.

The generated list remains pure data.  Lean checks every terminal inequality,
while a separate coverage theorem must prove that an actual profile is
dominated by one of the summaries.
-/

@[expose] public section

namespace BGS.NumberTheory

/-- The two scalar quantities needed to transport a joint-envelope leaf. -/
structure RankinJointEnvelopeSummary where
  /-- A rational upper bound for every represented failure square. -/
  failureSquareUpper : Rat
  /-- A natural lower bound for every represented joint neighbor product. -/
  lowerNeighborProductFloor : Nat
  deriving DecidableEq, Repr

namespace RankinJointEnvelopeSummary

/-- A summary safely contains an actual profile when its failure-square bound
is larger and its factorization floor is smaller. -/
def Dominates (summary : RankinJointEnvelopeSummary)
    (actual : RankinNeighborProfile) : Prop :=
  actual.jointEnvelopeFailureSquare <= summary.failureSquareUpper /\
    summary.lowerNeighborProductFloor <= actual.jointLowerNeighborProduct

def dominatesCheck (summary : RankinJointEnvelopeSummary)
    (actual : RankinNeighborProfile) : Bool :=
  decide
    (actual.jointEnvelopeFailureSquare <= summary.failureSquareUpper /\
      summary.lowerNeighborProductFloor <= actual.jointLowerNeighborProduct)

/-- Direct cutoff closure for a scalar summary. -/
def ClosesCutoff
    (summary : RankinJointEnvelopeSummary) (cutoff : Nat) : Prop :=
  summary.failureSquareUpper < (8 * (cutoff + 1) : Nat)

/-- Product-budget exclusion for a scalar summary. -/
def ExcludesFailure (summary : RankinJointEnvelopeSummary) : Prop :=
  summary.failureSquareUpper ^ 2 <
    (64 * summary.lowerNeighborProductFloor : Nat)

def LeafValid
    (summary : RankinJointEnvelopeSummary) (cutoff : Nat) : Prop :=
  summary.ClosesCutoff cutoff \/ summary.ExcludesFailure

def leafCheck
    (summary : RankinJointEnvelopeSummary) (cutoff : Nat) : Bool :=
  decide
    (summary.failureSquareUpper < (8 * (cutoff + 1) : Nat) \/
      summary.failureSquareUpper ^ 2 <
        (64 * summary.lowerNeighborProductFloor : Nat))

@[simp] theorem dominatesCheck_eq_true_iff
    (summary : RankinJointEnvelopeSummary)
    (actual : RankinNeighborProfile) :
    summary.dominatesCheck actual = true <-> summary.Dominates actual := by
  simp [dominatesCheck, Dominates]

@[simp] theorem leafCheck_eq_true_iff
    (summary : RankinJointEnvelopeSummary) (cutoff : Nat) :
    summary.leafCheck cutoff = true <-> summary.LeafValid cutoff := by
  simp [leafCheck, LeafValid, ClosesCutoff, ExcludesFailure]

/-- Every profile gives an exact scalar summary. -/
def ofProfile (profile : RankinNeighborProfile) :
    RankinJointEnvelopeSummary where
  failureSquareUpper := profile.jointEnvelopeFailureSquare
  lowerNeighborProductFloor := profile.jointLowerNeighborProduct

theorem ofProfile_dominates (profile : RankinNeighborProfile) :
    (ofProfile profile).Dominates profile := by
  exact And.intro le_rfl le_rfl

theorem jointEnvelopeClosesCutoff_of_dominates
    {summary : RankinJointEnvelopeSummary}
    {actual : RankinNeighborProfile} {cutoff : Nat}
    (hdom : summary.Dominates actual)
    (hcloses : summary.ClosesCutoff cutoff) :
    actual.JointEnvelopeClosesCutoff cutoff := by
  exact hdom.1.trans_lt hcloses

theorem jointEnvelopeExcludesFailure_of_dominates
    {summary : RankinJointEnvelopeSummary}
    {actual : RankinNeighborProfile}
    (hdom : summary.Dominates actual)
    (hexcludes : summary.ExcludesFailure) :
    actual.JointEnvelopeExcludesFailure := by
  have hactualNonneg :
      (0 : Rat) <= actual.jointEnvelopeFailureSquare := by
    rw [RankinNeighborProfile.jointEnvelopeFailureSquare]
    positivity
  have hsummaryNonneg : (0 : Rat) <= summary.failureSquareUpper :=
    hactualNonneg.trans hdom.1
  have hsquare :
      actual.jointEnvelopeFailureSquare ^ 2 <=
        summary.failureSquareUpper ^ 2 := by
    exact pow_le_pow_left₀ hactualNonneg hdom.1 2
  have hlower :
      ((64 * summary.lowerNeighborProductFloor : Nat) : Rat) <=
        ((64 * actual.jointLowerNeighborProduct : Nat) : Rat) := by
    exact_mod_cast Nat.mul_le_mul_left 64 hdom.2
  exact hsquare.trans_lt (hexcludes.trans_le hlower)

theorem jointEnvelope_leaf_of_dominates
    {summary : RankinJointEnvelopeSummary}
    {actual : RankinNeighborProfile} {cutoff : Nat}
    (hdom : summary.Dominates actual)
    (hleaf : summary.LeafValid cutoff) :
    actual.JointEnvelopeClosesCutoff cutoff \/
      actual.JointEnvelopeExcludesFailure := by
  rcases hleaf with hcloses | hexcludes
  · exact Or.inl (jointEnvelopeClosesCutoff_of_dominates hdom hcloses)
  · exact Or.inr (jointEnvelopeExcludesFailure_of_dominates hdom hexcludes)

end RankinJointEnvelopeSummary

def allRankinJointEnvelopeSummariesValid
    (cutoff : Nat) : List RankinJointEnvelopeSummary -> Prop
  | [] => True
  | summary :: summaries =>
      summary.LeafValid cutoff /\
        allRankinJointEnvelopeSummariesValid cutoff summaries

def allRankinJointEnvelopeSummariesCheck
    (cutoff : Nat) : List RankinJointEnvelopeSummary -> Bool
  | [] => true
  | summary :: summaries =>
      summary.leafCheck cutoff &&
        allRankinJointEnvelopeSummariesCheck cutoff summaries

@[simp] theorem allRankinJointEnvelopeSummariesCheck_eq_true_iff
    (cutoff : Nat) (summaries : List RankinJointEnvelopeSummary) :
    allRankinJointEnvelopeSummariesCheck cutoff summaries = true <->
      allRankinJointEnvelopeSummariesValid cutoff summaries := by
  induction summaries with
  | nil =>
      simp [allRankinJointEnvelopeSummariesCheck,
        allRankinJointEnvelopeSummariesValid]
  | cons summary summaries ih =>
      simp [allRankinJointEnvelopeSummariesCheck,
        allRankinJointEnvelopeSummariesValid, ih]

private theorem summaryLeafValid_of_all_of_mem
    {cutoff : Nat} {summaries : List RankinJointEnvelopeSummary}
    (hall : allRankinJointEnvelopeSummariesValid cutoff summaries)
    {summary : RankinJointEnvelopeSummary} (hmem : summary ∈ summaries) :
    summary.LeafValid cutoff := by
  induction summaries with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [allRankinJointEnvelopeSummariesValid] at hall
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact hall.1
      · exact ih hall.2 hmem

/-- Pure scalar data for a compressed domination cover. -/
structure RankinJointEnvelopeSummaryCertificate where
  cutoff : Nat
  summaries : List RankinJointEnvelopeSummary
  deriving DecidableEq, Repr

namespace RankinJointEnvelopeSummaryCertificate

def LeavesValid (cert : RankinJointEnvelopeSummaryCertificate) : Prop :=
  allRankinJointEnvelopeSummariesValid cert.cutoff cert.summaries

def check (cert : RankinJointEnvelopeSummaryCertificate) : Bool :=
  allRankinJointEnvelopeSummariesCheck cert.cutoff cert.summaries

/-- Mathematical coverage of one actual profile by the generated summaries. -/
def Covers (cert : RankinJointEnvelopeSummaryCertificate)
    (actual : RankinNeighborProfile) : Prop :=
  Exists fun summary =>
    summary ∈ cert.summaries /\ summary.Dominates actual

@[simp] theorem check_eq_true_iff
    (cert : RankinJointEnvelopeSummaryCertificate) :
    cert.check = true <-> cert.LeavesValid := by
  simp [check, LeavesValid]

theorem jointEnvelope_leaf_of_check_of_covers
    {cert : RankinJointEnvelopeSummaryCertificate}
    {actual : RankinNeighborProfile}
    (hcheck : cert.check = true) (hcover : cert.Covers actual) :
    actual.JointEnvelopeClosesCutoff cert.cutoff \/
      actual.JointEnvelopeExcludesFailure := by
  obtain ⟨summary, hmem, hdom⟩ := hcover
  have hall : cert.LeavesValid := cert.check_eq_true_iff.mp hcheck
  have hsummary := summaryLeafValid_of_all_of_mem hall hmem
  exact summary.jointEnvelope_leaf_of_dominates hdom hsummary

end RankinJointEnvelopeSummaryCertificate

end BGS.NumberTheory

namespace BGS.Markoff

open BGS.NumberTheory

/-- A checked scalar summary cover discharges the arithmetic leaf without
requiring generated rows to be valid neighbor profiles. -/
theorem prime_le_of_rankinJointEnvelopeSummaryCertificate
    {p bound : Nat}
    (hpPrime : p.Prime) (hpTwo : 2 < p)
    (hroot :
      8 * p <= (combinedTruncatedOrderTotientSum p bound) ^ 2)
    (hboundWitness :
      bound <= 189 * (middleGameMaximalOrders p bound).card ^ 3)
    (actual : RankinNeighborProfile)
    (hactual : actual.Valid) (hmatch : actual.Matches p)
    (cert : RankinJointEnvelopeSummaryCertificate)
    (hcheck : cert.check = true) (hcover : cert.Covers actual) :
    p <= cert.cutoff := by
  apply prime_le_of_matching_rankinNeighborProfile_jointEnvelope_leaf
    hpPrime hpTwo hroot hboundWitness actual hactual hmatch
  exact cert.jointEnvelope_leaf_of_check_of_covers hcheck hcover

end BGS.Markoff
