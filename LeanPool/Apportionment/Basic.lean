/-
Copyright (c) 2025 Michał Dobranowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Dobranowski
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Lift
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.Abel
import LeanPool.Apportionment.Utils

/-!
# Basic

We define basic notions related to apportionment methods, such as elections, apportionments,
apportionment rules, and properties of apportionment rules. We also prove the Balinski-Young
impossibility theorem.

All definitions follow those given in a textbook by F. Pukelsheim [Pukelsheim2017]. Distinction
between weak and strong exactness is added, following [PalomaresPukelsheimRamirez2016].

## Main definitions

* `Election`
* `Apportionment`
* `Rule`
* `IsAnonymous`
* `IsBalanced`
* `IsConcordant`
* `IsDecent`
* `IsExact`
* `IsQuotaRule`
* `IsPopulationMonotone`

## Main statements

* `Election.n_pos`: the number of parties in an election is positive.
* `IsConcordant_of_IsPopulationMonotone`: anonymity and population monotonicity imply concordance.
* `balinski_young`: Balinski-Young impossibility theorem.

## References

* [M. L. Balinski, H. P. Young, *Fair Representation: Meeting the Ideal of One Man, One Vote*
  ][BalinskiYoung1982]
* [A. Palomares, F. Pukelsheim, J. A. Ramírez, *The whole and its parts: On the coherence theorem of
  Balinski and Young*][PalomaresPukelsheimRamirez2016]
* [F. Pukelsheim, *Proportional Representation: Apportionment Methods and Their Applications*
  ][Pukelsheim2017]

-/

open BigOperators

/-- An apportionment is a vector of natural numbers representing the number of seats allocated to
each party (at the corresponding index). -/
abbrev Apportionment (n : ℕ) : Type := Vector ℕ n

namespace Apportionment

/-- An election with a vector of votes for `n` parties (at the corresponding indices) and the total
number of seats to be allocated. -/
structure Election (n : ℕ) where
  /-- The number of votes for each of the `n` parties. -/
  votes : Vector ℕ n
  /-- The total number of seats to be allocated. -/
  houseSize : ℕ+
  /-- At least one party must have received some votes. -/
  votes_sum_pos : 0 < votes.sum
  deriving DecidableEq

instance {n : ℕ} : Repr (Election n) where
  reprPrec e _ :=
    "{ votes := " ++ repr e.votes.toArray ++ ", houseSize := " ++ repr e.houseSize ++ " }"

namespace Election

/-- Create a new election by permuting the vote distribution of parties according to permutation
`σ`. -/
@[simp]
def mkByPerm {n : ℕ} (election : Election n) (σ : Equiv.Perm (Fin n)) : Election n :=
  { votes := Vector.ofFn fun i => election.votes[σ i]
    houseSize := election.houseSize
    votes_sum_pos := by
      have := election.votes_sum_pos
      simp only [sum_pos_iff_exists_pos, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta] at this ⊢
      obtain ⟨i, hi⟩ := this
      use σ.symm i
      simpa
  }

/-- Create a new election by scaling all votes by a positive constant `k`. -/
@[simp]
def mkByScale {n : ℕ} (election : Election n) (k : ℕ+) : Election n :=
  { votes := Vector.ofFn fun i => k * election.votes[i]
    houseSize := election.houseSize
    votes_sum_pos := by
      have := election.votes_sum_pos
      simpa [sum_pos_iff_exists_pos]
  }

/-- The number of parties in an election is positive. -/
lemma n_pos {n : ℕ} (election : Election n) : 0 < n := by
  by_contra h_neg
  have h_sum_zero : (Vector.sum election.votes) = 0 := by
    have h_empty : ∀ (v : Vector ℕ 0), v.sum = 0 := by decide
    aesop
  exact absurd h_sum_zero (ne_of_gt election.votes_sum_pos)

end Election

/-- An apportionment rule is a function that, given an election, returns a set of apportionments
satisfying three properties:
1. *Non-emptiness*: there is at least one apportionment returned;
2. *Inheritance of zeros*: parties with zero votes are allocated zero seats;
3. *House size feasibility*: the total number of seats allocated is equal to the house size. -/
structure Rule where
  /-- The set of apportionments produced for a given election. -/
  res : {n : ℕ} → Election n → Finset (Apportionment n)
  /-- Every election produces at least one apportionment. -/
  non_emptiness {n : ℕ} (election : Election n) : (res election).Nonempty
  /-- Parties with zero votes receive zero seats. -/
  inheritance_of_zeros {n : ℕ} (election : Election n) (i : Fin n) :
    election.votes[i] = 0 → ∀ App ∈ res election, App[i] = 0
  /-- The total number of seats allocated equals the house size. -/
  house_size_feasibility {n : ℕ} (election : Election n) :
    ∀ App ∈ res election, App.sum = election.houseSize

/-- A rule is *anonymous* if permuting the votes of the parties permutes the allocation of seats in
the same way. -/
class IsAnonymous (rule : Rule) : Prop where
  /-- Permuting the votes by `σ` permutes the resulting apportionments by `σ`. -/
  anonymous {n : ℕ} (election : Election n) (σ : Equiv.Perm (Fin n)) :
    let election' : Election n := election.mkByPerm σ
    ∀ App, App ∈ rule.res election' ↔
      ∃ App' ∈ rule.res election, ∀ i, App[i] = App'[σ i]

/-- A rule is *balanced* if whenever two parties have the same number of votes, then the difference
in the number of seats allocated to them is at most one. -/
class IsBalanced (rule : Rule) : Prop where
  /-- Equal vote counts produce seat counts that differ by at most one. -/
  balanced {n : ℕ} (election : Election n) (i j : Fin n) :
    election.votes[i] = election.votes[j] →
      ∀ App ∈ rule.res election, App[i].dist App[j] ≤ 1

/-- A rule is *concordant* if whenever one party has fewer votes than another, then it is allocated
no more seats than that other party. -/
class IsConcordant (rule : Rule) : Prop where
  /-- Strictly fewer votes implies no more seats. -/
  concordant {n : ℕ} (election : Election n) (i j : Fin n) :
    election.votes[i] < election.votes[j] →
      ∀ App ∈ rule.res election, App[i] ≤ App[j]

/-- A rule is *decent* if scaling the number of votes for each party by the same positive integer
does not change the apportionment. -/
class IsDecent (rule : Rule) : Prop where
  /-- Scaling all vote counts by a positive integer leaves the apportionment unchanged. -/
  decent {n : ℕ} (election : Election n) (k : ℕ+) :
    let election' : Election n := election.mkByScale k
    rule.res election' = rule.res election

/-- A rule is *weakly exact* if every `Apportionment`, when viewed as an input vote distribution
`Election.votes`, is reproduced as the unique solution. -/
class IsExact (rule : Rule) : Prop where
  /-- An apportionment, treated as a vote distribution, is the unique apportionment of itself. -/
  exact {n : ℕ} (election : Election n) :
    -- ∀ App ∈ rule.res election
    ∀ App : Apportionment n, (hApp : App ∈ rule.res election) →
      let election' : Election n := {
        votes := App
        houseSize := election.houseSize
        votes_sum_pos := by
          rw [rule.house_size_feasibility (n := n) election App hApp]
          exact election.houseSize.pos
      }
      rule.res election' = {App}

/-- A rule is a *quota rule* if the number of seats allocated to each party is either the floor or
the ceiling of its Hare-quota. -/
class IsQuotaRule (rule : Rule) : Prop where
  /-- Each party receives the floor or ceiling of its Hare-quota. -/
  quota_rule {n : ℕ} (election : Election n) (i : Fin n) :
    let quota := (election.votes[i] * election.houseSize : ℚ) / election.votes.sum
    ∀ App ∈ rule.res election, App[i] = ⌊quota⌋ ∨ App[i] = ⌈quota⌉

/-- A rule is *population monotone* (or *vote ratio monotone*) if population paradoxes do not occur.
A population paradox occurs when the support for party `i` increases at a faster rate than that for
party `j`, but `i` loses seats while `j` gains seats. -/
class IsPopulationMonotone (rule : Rule) : Prop where
  /-- Faster vote growth for `i` than for `j` rules out `i` losing seats while `j` gains them. -/
  population_monotone {n : ℕ} (election₁ election₂ : Election n) (i j : Fin n) :
    election₁.houseSize = election₂.houseSize →
      -- i's support grows faster than j's (multiplying crosswise to avoid ℚ)
      election₂.votes[i] * election₁.votes[j] > election₂.votes[j] * election₁.votes[i] →
        ∀ App₁ ∈ rule.res election₁, ∀ App₂ ∈ rule.res election₂,
          -- i gets less seats, j gets more seats
          ¬(App₁[i] > App₂[i] ∧ App₁[j] < App₂[j])

/-- If an anonymous rule is population monotone, then it is concordant. -/
lemma IsConcordant_of_IsPopulationMonotone (rule : Rule) [h_anon : IsAnonymous rule]
    [h_mono : IsPopulationMonotone rule] : IsConcordant rule := by
  constructor
  intro n e i j h_votes App h_App
  let σ : Equiv.Perm (Fin n) := Equiv.swap i j
  let e' : Election n := e.mkByPerm σ
  let App' := Vector.ofFn fun r => App[σ r]
  replace h_anon := h_anon.anonymous e σ App'
  have h_App' : App' ∈ rule.res e' := by
    rw [h_anon]
    use App
    exact ⟨h_App, by aesop⟩
  have h_p' : e'.votes[i] = e.votes[j] := by aesop
  have h_q' : e'.votes[j] = e.votes[i] := by aesop
  replace h_mono := h_mono.population_monotone e e' i j (by trivial)
  rw [h_p', h_q', ← pow_two, ← pow_two] at h_mono
  specialize h_mono (Nat.pow_lt_pow_left h_votes (by decide)) App h_App App' h_App'
  aesop

/-- Balinski-Young impossibility theorem: If an anonymous rule is a quota rule, then it is not
population monotone. Thus, no apportionment method can satisfy both properties simultaneously. -/
theorem balinski_young (rule : Rule) [IsAnonymous rule] [h_quota : IsQuotaRule rule] :
    ¬IsPopulationMonotone rule := by
  by_contra h_mono
  have h_concord := IsConcordant_of_IsPopulationMonotone rule
  -- first election --
  let e : Election 4 := {
    votes := #v[660, 670, 2450, 6220]
    houseSize := 8
    votes_sum_pos := by decide
  }
  obtain ⟨App, h_App⟩ := rule.non_emptiness e
  have m2_le_2 : App[2] ≤ 2 := by
    have := h_quota.quota_rule e 2 App h_App
    simp only [e] at this
    norm_num at this
    omega
  have m3_le_5 : App[3] ≤ 5 := by
    have := h_quota.quota_rule e 3 App h_App
    simp only [e] at this
    norm_num at this
    change ↑App[3] = ⌊(6220 * 8 : ℚ) / 10000⌋ ∨
      ↑App[3] = ⌈(6220 * 8 : ℚ) / 10000⌉ at this
    norm_num at this
    omega
  have m1_eq_1 : App[1] = 1 := by
    have := h_quota.quota_rule e 1 App h_App
    simp only [e] at this
    norm_num at this
    rcases this with m1_eq_0 | m1_eq_1
    · have h_sum : App.sum = 8 := rule.house_size_feasibility e App h_App
      have : App[0] ≤ App[1] := h_concord.concordant e 0 1 (by decide) App h_App
      linarith [Vector.sum_four App]
    · assumption
  -- second election --
  let e' : Election 4 := {
    votes := #v[680, 675, 700, 6200]
    houseSize := 8,
    votes_sum_pos := by decide
  }
  obtain ⟨App', h_App'⟩ := rule.non_emptiness e'
  have m3_ge_6' : App'[3] ≥ 6 := by
    have := h_quota.quota_rule e' 3 App' h_App'
    simp only [e'] at this
    norm_num at this
    change ↑App'[3] = ⌊(6200 * 8 : ℚ) / 8255⌋ ∨
      ↑App'[3] = ⌈(6200 * 8 : ℚ) / 8255⌉ at this
    norm_num at this
    omega
  have m1_eq_0' : App'[1] = 0 := by
    have := h_quota.quota_rule e' 1 App' h_App'
    simp only [e'] at this
    norm_num at this
    rcases this with m1_eq_0' | m1_eq_1'
    · assumption
    · have h_sum' : App'.sum = 8 := rule.house_size_feasibility e' App' h_App'
      have : App'[1] ≤ App'[0] := h_concord.concordant e' 1 0 (by decide) App' h_App'
      have : App'[1] ≤ App'[2] := h_concord.concordant e' 1 2 (by decide) App' h_App'
      linarith [Vector.sum_four App']
  -- show that it's not population monotone --
  have : App[1] > App'[1] ∧ App[3] < App'[3] := by omega
  have := h_mono.population_monotone e e' 1 3 (by decide) (by decide) App h_App App' h_App'
  contradiction

end Apportionment
