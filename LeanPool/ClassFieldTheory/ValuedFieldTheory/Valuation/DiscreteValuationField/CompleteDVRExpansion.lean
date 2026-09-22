/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Topology.Models
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
/-!
# Coefficients for a complete DVR expansion

This file formalizes the recursive coefficient construction in the recursive coefficient proof.
  Given a section of the residue map and a uniformizer `π`, every element
of the valuation ring has uniquely determined successive representative
coefficients and remainders satisfying

`u = a 0 + a 1 * π + ... + a (n - 1) * π ^ (n - 1) + π ^ n * b n`.
-/

noncomputable section

namespace LubinTate
namespace Valuations

universe u v

open ValuationTheory.DiscreteValuationField

/-- A normalized system of representatives for the residue field of a local
ring.  This common structure is used both for the original valuation ring and
for the valuation ring in its completion. -/
structure residueRepresentativeSystemOf
    (O : Type u) [CommRing O] [IsLocalRing O] where
  /-- The chosen representative of each residue class. -/
  repr : IsLocalRing.ResidueField O → O
  /-- Reducing a chosen representative recovers its residue class. -/
  residue_repr : ∀ a : IsLocalRing.ResidueField O,
    IsLocalRing.residue O (repr a) = a
  /-- The zero residue class is represented by zero. -/
  repr_zero : repr 0 = 0

namespace residueRepresentativeSystemOf

variable (O : Type u) [CommRing O] [IsLocalRing O]

/-- A normalized representative system exists by surjectivity of the residue
map. -/
noncomputable def ofChoice : residueRepresentativeSystemOf O := by
  classical
  refine
    { repr := fun a =>
        if ha : a = 0 then 0 else Classical.choose (IsLocalRing.residue_surjective a)
      residue_repr := ?_
      repr_zero := ?_ }
  · intro a
    by_cases ha : a = 0
    · simp [ha]
    · simp [ha, Classical.choose_spec (IsLocalRing.residue_surjective a)]
  · simp

end residueRepresentativeSystemOf

/-- A system of representatives for the residue field of a complete DVF
valuation ring, encoded as a section of the residue map and normalized at
zero. -/
abbrev residueRepresentativeSystem
    {K : Type u} [Field K]
    (F : CompleteDVF.{u, v} K) :=
  residueRepresentativeSystemOf F.valuationSubring

namespace residueRepresentativeSystem

variable {K : Type u} [Field K]
variable (F : CompleteDVF.{u, v} K)

/-- A representative system exists by surjectivity of the residue map. -/
noncomputable def ofChoice : residueRepresentativeSystem F := by
  exact residueRepresentativeSystemOf.ofChoice F.valuationSubring

end residueRepresentativeSystem

variable {K : Type u} [Field K]
variable (F : CompleteDVF.{u, v} K)

/-- One step of the digit expansion: subtract the chosen residue
representative, then divide by the uniformizer. -/
theorem exists_remainder_step
    (R : residueRepresentativeSystem F)
    (π : F.valuationSubring) (hπ : F.valuation.IsUniformizer (π : K))
    (r : F.valuationSubring) :
    ∃ b : F.valuationSubring,
      r = R.repr (F.residueMap r) + π * b := by
  have hres :
      F.residueMap (r - R.repr (F.residueMap r)) = 0 := by
    simp [map_sub, R.residue_repr]
  have hmem :
      r - R.repr (F.residueMap r) ∈ F.maximalIdeal :=
    (F.residue_eq_zero_iff _).1 hres
  have hspan :
      r - R.repr (F.residueMap r) ∈
        Ideal.span ({π} : Set F.valuationSubring) := by
    simpa [F.maximalIdeal_eq_span_uniformizer hπ] using hmem
  rcases (Ideal.mem_span_singleton.mp hspan) with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  rw [sub_eq_iff_eq_add] at hb
  simpa [add_comm] using hb

/-- The recursively defined remainders in the expansion of `u`. -/
noncomputable def remainder
    (R : residueRepresentativeSystem F)
    (π : F.valuationSubring) (hπ : F.valuation.IsUniformizer (π : K))
    (u : F.valuationSubring) :
    ℕ → F.valuationSubring
  | 0 => u
  | n + 1 =>
      Classical.choose
        (exists_remainder_step F R π hπ
          (remainder R π hπ u n))

/-- The recursively defined representative coefficients in the expansion of
`u`. -/
noncomputable def coeff
    (R : residueRepresentativeSystem F)
    (π : F.valuationSubring) (hπ : F.valuation.IsUniformizer (π : K))
    (u : F.valuationSubring) (n : ℕ) :
    F.valuationSubring :=
  R.repr (F.residueMap (remainder F R π hπ u n))

/-- The defining recursion for the remainders and coefficients. -/
theorem remainder_step
    (R : residueRepresentativeSystem F)
    (π : F.valuationSubring) (hπ : F.valuation.IsUniformizer (π : K))
    (u : F.valuationSubring) (n : ℕ) :
    remainder F R π hπ u n =
      coeff F R π hπ u n +
        π * remainder F R π hπ u (n + 1) := by
  exact
    Classical.choose_spec
      (exists_remainder_step F R π hπ
        (remainder F R π hπ u n))

/-- Adding a multiple of the uniformizer does not change the residue class. -/
theorem residueMap_add_uniformizer_mul
    (π : F.valuationSubring) (hπ : F.valuation.IsUniformizer (π : K))
    (a b : F.valuationSubring) :
    F.residueMap (a + π * b) = F.residueMap a := by
  have hπ_res : F.residueMap π = 0 :=
    (F.residue_eq_zero_iff π).2 (F.uniformizer_mem_maximalIdeal hπ)
  rw [map_add, map_mul, hπ_res, zero_mul, add_zero]

/-- Recursive uniqueness of the coefficient and remainder sequences in the
valuation-ring part of the complete-DVR expansion. -/
theorem coeff_remainder_unique
    (R : residueRepresentativeSystem F)
    (π : F.valuationSubring) (hπ : F.valuation.IsUniformizer (π : K))
    (u : F.valuationSubring)
    (c b : ℕ → F.valuationSubring)
    (hb0 : b 0 = u)
    (hstep : ∀ n : ℕ, b n = c n + π * b (n + 1))
    (hcoeff_repr : ∀ n : ℕ, ∃ a : F.residueField, c n = R.repr a) :
    ∀ n : ℕ,
      b n = remainder F R π hπ u n ∧
        c n = coeff F R π hπ u n := by
  classical
  have hπ_ne : π ≠ 0 := by
    intro hzero
    exact hπ.ne_zero (by simpa using congrArg (fun x : F.valuationSubring => (x : K)) hzero)
  have coeff_eq_of_remainder_eq :
      ∀ n : ℕ,
        b n = remainder F R π hπ u n →
          c n = coeff F R π hπ u n := by
    intro n hb
    rcases hcoeff_repr n with ⟨a, ha⟩
    have hres_eq : F.residueMap (b n) = F.residueMap (c n) := by
      rw [hstep n]
      exact residueMap_add_uniformizer_mul F π hπ
        (c n) (b (n + 1))
    calc
      c n = R.repr a := ha
      _ = R.repr (F.residueMap (c n)) := by rw [ha, R.residue_repr]
      _ = R.repr (F.residueMap (b n)) := by rw [hres_eq]
      _ = coeff F R π hπ u n := by
          simp [coeff, hb]
  have next_remainder_eq_of :
      ∀ n : ℕ,
        b n = remainder F R π hπ u n →
          c n = coeff F R π hπ u n →
            b (n + 1) = remainder F R π hπ u (n + 1) := by
    intro n hb hc
    have hmul : π * b (n + 1) =
        π * remainder F R π hπ u (n + 1) := by
      apply add_left_cancel (a := coeff F R π hπ u n)
      calc
        coeff F R π hπ u n + π * b (n + 1)
            = c n + π * b (n + 1) := by rw [hc]
        _ = b n := (hstep n).symm
        _ = remainder F R π hπ u n := hb
        _ = coeff F R π hπ u n +
              π * remainder F R π hπ u (n + 1) :=
            remainder_step F R π hπ u n
    exact mul_left_cancel₀ hπ_ne hmul
  intro n
  induction n with
  | zero =>
      have hb : b 0 = remainder F R π hπ u 0 := by
        simp [remainder, hb0]
      exact ⟨hb, coeff_eq_of_remainder_eq 0 hb⟩
  | succ n ih =>
      have hb_succ : b (n + 1) = remainder F R π hπ u (n + 1) :=
        next_remainder_eq_of n ih.1 ih.2
      exact ⟨hb_succ, coeff_eq_of_remainder_eq (n + 1) hb_succ⟩

/-- Laurent-unit decomposition in a complete DVF: every nonzero field element
is a power of the chosen uniformizer times a valuation-ring unit. -/
theorem exists_laurent_unit
    (π : F.valuationSubring) (hπ : F.valuation.IsUniformizer (π : K))
    {x : K} (hx : x ≠ 0) :
    ∃ m : ℤ, ∃ u : F.valuationSubring,
      IsUnit u ∧ x = (π : K) ^ m * (u : K) := by
  classical
  rcases F.valuation.valuationSubring.mem_or_inv_mem x with hxmem | hxinvmem
  · let r : F.valuationSubring := ⟨x, hxmem⟩
    have hr : r ≠ 0 := by
      intro hr0
      exact hx (by simpa [r] using congrArg (fun y : F.valuationSubring => (y : K)) hr0)
    rcases Valuation.exists_pow_Uniformizer (v := F.valuation) hr
        (Valuation.Uniformizer.mk π hπ) with ⟨n, u, hu⟩
    let u0 : F.valuationSubring := u.val
    have hu0 : IsUnit u0 := by
      simp [u0]
    have hcoe_pow :
        ((π ^ n : F.valuationSubring) : K) = (π : K) ^ n := by
      exact map_pow F.valuation.integer.subtype π n
    refine ⟨(n : ℤ), u0, hu0, ?_⟩
    calc
      x = ((π ^ n : F.valuationSubring) : K) * (u0 : K) := by
        change x = ((π ^ n : F.valuationSubring) : K) * (u0 : K) at hu
        exact hu
      _ = (π : K) ^ (n : ℤ) * (u0 : K) := by
        rw [hcoe_pow, zpow_natCast]
  · let r : F.valuationSubring := ⟨x⁻¹, hxinvmem⟩
    have hr : r ≠ 0 := by
      intro hr0
      have hxinv0 : x⁻¹ = 0 := by
        simpa [r] using congrArg (fun y : F.valuationSubring => (y : K)) hr0
      exact inv_ne_zero hx hxinv0
    rcases Valuation.exists_pow_Uniformizer (v := F.valuation) hr
        (Valuation.Uniformizer.mk π hπ) with ⟨n, u, hu⟩
    let u0 : F.valuationSubring := (u⁻¹).val
    have hu0 : IsUnit u0 := by
      simp [u0]
    have hcoe_pow :
        ((π ^ n : F.valuationSubring) : K) = (π : K) ^ n := by
      exact map_pow F.valuation.integer.subtype π n
    have huK : x⁻¹ = (π : K) ^ n * ((u.val : F.valuationSubring) : K) := by
      calc
        x⁻¹ = ((π ^ n : F.valuationSubring) : K) *
            ((u.val : F.valuationSubring) : K) := by
          change x⁻¹ = ((π ^ n : F.valuationSubring) : K) *
            ((u.val : F.valuationSubring) : K) at hu
          exact hu
        _ = (π : K) ^ n * ((u.val : F.valuationSubring) : K) := by
          rw [hcoe_pow]
    have huinv : (((u.val : F.valuationSubring) : K))⁻¹ = (u0 : K) := by
      have hmulO :
          (u.val : F.valuationSubring) * ((u⁻¹).val : F.valuationSubring) = 1 :=
        Units.mul_inv u
      have hmulK : ((u.val : F.valuationSubring) : K) * (u0 : K) = 1 := by
        change
          (((u.val : F.valuationSubring) * ((u⁻¹).val : F.valuationSubring) :
              F.valuationSubring) : K) = (1 : K)
        rw [hmulO]
        rfl
      exact inv_eq_of_mul_eq_one_right hmulK
    refine ⟨-((n : ℤ)), u0, hu0, ?_⟩
    calc
      x = (x⁻¹)⁻¹ := by rw [inv_inv]
      _ = ((π : K) ^ n * ((u.val : F.valuationSubring) : K))⁻¹ := by rw [huK]
      _ = (((u.val : F.valuationSubring) : K))⁻¹ * ((π : K) ^ n)⁻¹ := by
        rw [mul_inv_rev]
      _ = ((π : K) ^ n)⁻¹ * (((u.val : F.valuationSubring) : K))⁻¹ := by
        rw [mul_comm]
      _ = (π : K) ^ (-((n : ℤ))) * (u0 : K) := by
        rw [huinv]
        rw [zpow_neg, zpow_natCast]

/-- The uniformizer exponent in a Laurent-unit decomposition is unique. -/
theorem laurent_exponent_unique
    (π : F.valuationSubring) (hπ : F.valuation.IsUniformizer (π : K))
    {m n : ℤ} {u w : F.valuationSubring}
    (hu : IsUnit u) (hw : IsUnit w)
    (h : (π : K) ^ m * (u : K) = (π : K) ^ n * (w : K)) :
    m = n := by
  have huval : F.valuation (u : K) = 1 := by
    change F.valuation ((algebraMap F.valuationSubring K) u) = 1
    exact
      (Valuation.Integers.isUnit_iff_valuation_eq_one
        (Valuation.integer.integers F.valuation) (x := u)).mp hu
  have hwval : F.valuation (w : K) = 1 := by
    change F.valuation ((algebraMap F.valuationSubring K) w) = 1
    exact
      (Valuation.Integers.isUnit_iff_valuation_eq_one
        (Valuation.integer.integers F.valuation) (x := w)).mp hw
  have hval :
      F.valuation ((π : K) ^ m * (u : K)) =
        F.valuation ((π : K) ^ n * (w : K)) :=
    congrArg F.valuation h
  rw [map_mul, map_mul, map_zpow₀, map_zpow₀, huval, hwval, mul_one, mul_one] at hval
  exact zpow_right_injective₀ hπ.val_pos (ne_of_lt hπ.val_lt_one) hval

/-- The Laurent-unit part of the complete-DVR expansion is unique: if two unit
decompositions with powers of the same uniformizer represent the same field
element, then both the exponent and the unit agree. -/
theorem laurent_unit_unique
    (π : F.valuationSubring) (hπ : F.valuation.IsUniformizer (π : K))
    {m n : ℤ} {u w : F.valuationSubring}
    (hu : IsUnit u) (hw : IsUnit w)
    (h : (π : K) ^ m * (u : K) = (π : K) ^ n * (w : K)) :
    m = n ∧ u = w := by
  have hm : m = n := laurent_exponent_unique F π hπ hu hw h
  subst n
  have hπ_ne : (π : K) ≠ 0 := hπ.ne_zero
  have hpow_ne : (π : K) ^ m ≠ 0 := zpow_ne_zero m hπ_ne
  have hu_eq : (u : K) = (w : K) := mul_left_cancel₀ hpow_ne h
  exact ⟨rfl, Subtype.ext hu_eq⟩

/-- Finite partial sums of the `π`-adic representative expansion. -/
noncomputable def partialSum
    (R : residueRepresentativeSystem F)
    (π : F.valuationSubring) (hπ : F.valuation.IsUniformizer (π : K))
    (u : F.valuationSubring) :
    ℕ → F.valuationSubring
  | 0 => 0
  | n + 1 =>
      partialSum R π hπ u n +
        coeff F R π hπ u n * π ^ n

/-- Finite-stage expansion with a remainder term. -/
theorem partialSum_add_remainder
    (R : residueRepresentativeSystem F)
    (π : F.valuationSubring) (hπ : F.valuation.IsUniformizer (π : K))
    (u : F.valuationSubring) (n : ℕ) :
    u =
      partialSum F R π hπ u n +
        π ^ n * remainder F R π hπ u n := by
  induction n with
  | zero =>
      simp [partialSum, remainder]
  | succ n ih =>
      calc
        u =
            partialSum F R π hπ u n +
              π ^ n * remainder F R π hπ u n := ih
        _ =
            partialSum F R π hπ u n +
              π ^ n *
                (coeff F R π hπ u n +
                  π * remainder F R π hπ u (n + 1)) := by
          rw [remainder_step F R π hπ u n]
        _ =
            partialSum F R π hπ u (n + 1) +
              π ^ (n + 1) * remainder F R π hπ u (n + 1) := by
          change
            partialSum F R π hπ u n +
                π ^ n *
                  (coeff F R π hπ u n +
                    π * remainder F R π hπ u (n + 1)) =
              (partialSum F R π hπ u n +
                  coeff F R π hπ u n * π ^ n) +
                π ^ (n + 1) * remainder F R π hπ u (n + 1)
          rw [pow_succ]
          ring

/-- The finite expansion gives the correct residue modulo `π ^ n`. -/
theorem partialSum_congr
    (R : residueRepresentativeSystem F)
    (π : F.valuationSubring) (hπ : F.valuation.IsUniformizer (π : K))
    (u : F.valuationSubring) (n : ℕ) :
    u - partialSum F R π hπ u n ∈ F.maximalIdeal ^ n := by
  let ps := partialSum F R π hπ u n
  let rem := remainder F R π hπ u n
  have hsum :
      u = ps + π ^ n * rem := by
    simpa [ps, rem] using
      partialSum_add_remainder F R π hπ u n
  have hdiff :
      u - ps = π ^ n * rem := by
    nth_rewrite 1 [hsum]
    ring
  have hpow :
      π ^ n * rem ∈
        Ideal.span ({π ^ n} : Set F.valuationSubring) := by
    rw [Ideal.mem_span_singleton]
    exact ⟨rem, by rw [mul_comm]⟩
  have hspan_eq := F.maximalIdeal_pow_eq_span_uniformizer_pow hπ n
  simpa [ps, rem, hdiff, hspan_eq] using hpow

/-- Convergence of the finite partial sums in the maximal-ideal adic
topology, represented on a type-level topological copy of the valuation
ring. -/
def PartialSumsConvergeAdically
    (R : residueRepresentativeSystem F)
    (π : F.valuationSubring) (hπ : F.valuation.IsUniformizer (π : K))
    (u : F.valuationSubring) : Prop :=
  Filter.Tendsto
    (fun n =>
      WithTopology.toTopology F.maximalIdeal.adicTopology
        (partialSum F R π hπ u n))
    Filter.atTop
    (nhds
      (WithTopology.toTopology F.maximalIdeal.adicTopology u))

/-- The finite partial sums converge to `u` in the type-level model of the
maximal-ideal adic topology. -/
theorem partialSum_tendsto_adic
    (R : residueRepresentativeSystem F)
    (π : F.valuationSubring) (hπ : F.valuation.IsUniformizer (π : K))
    (u : F.valuationSubring) :
    PartialSumsConvergeAdically F R π hπ u := by
  classical
  unfold PartialSumsConvergeAdically
  apply WithTopology.tendsto_nhds_iff.mpr
  let : TopologicalSpace F.valuationSubring := F.maximalIdeal.adicTopology
  rw [Filter.tendsto_def]
  intro s hs
  rw [Filter.mem_atTop_sets]
  rcases (Ideal.hasBasis_nhds_adic F.maximalIdeal u).mem_iff.mp hs with
    ⟨m, _hm, hms⟩
  refine ⟨m, ?_⟩
  intro n hn
  apply hms
  let ps := partialSum F R π hπ u n
  refine ⟨ps - u, ?_, ?_⟩
  · have hcongr : u - ps ∈ F.maximalIdeal ^ n := by
      simpa [ps] using partialSum_congr F R π hπ u n
    have hneg : ps - u ∈ F.maximalIdeal ^ n := by
      simpa [ps, sub_eq_add_neg] using
        (F.maximalIdeal ^ n).neg_mem hcongr
    exact Ideal.pow_le_pow_right hn hneg
  · simp [ps, sub_eq_add_neg]

/-- The residue of each coefficient is the residue of the corresponding
remainder. -/
theorem residue_coeff
    (R : residueRepresentativeSystem F)
    (π : F.valuationSubring) (hπ : F.valuation.IsUniformizer (π : K))
    (u : F.valuationSubring) (n : ℕ) :
      F.residueMap (coeff F R π hπ u n) =
      F.residueMap (remainder F R π hπ u n) := by
  simp [coeff, R.residue_repr]

/-- The first digit of a unit is nonzero. -/
theorem coeff_zero_ne_zero_of_isUnit
    (R : residueRepresentativeSystem F)
    (π : F.valuationSubring) (hπ : F.valuation.IsUniformizer (π : K))
    {u : F.valuationSubring} (hu : IsUnit u) :
    coeff F R π hπ u 0 ≠ 0 := by
  intro hzero
  have hres_coeff :
      F.residueMap (coeff F R π hπ u 0) = 0 := by
    simp [hzero]
  have hres_u : F.residueMap u = 0 := by
    have hcoeff :=
      residue_coeff F R π hπ u 0
    rw [hres_coeff] at hcoeff
    simpa [remainder] using hcoeff.symm
  have hne : F.residueMap u ≠ 0 :=
    (F.residue_ne_zero_iff_isUnit u).2 hu
  exact hne hres_u

/-- The complete-DVR expansion, existence-side Laurent expansion data for a nonzero field
element: after extracting the uniformizer power, the unit part has a
convergent representative expansion with nonzero first digit. -/
theorem exists_laurent_expansion_data
    (R : residueRepresentativeSystem F)
    (π : F.valuationSubring) (hπ : F.valuation.IsUniformizer (π : K))
    {x : K} (hx : x ≠ 0) :
    ∃ m : ℤ, ∃ u : F.valuationSubring,
      IsUnit u ∧
        x = (π : K) ^ m * (u : K) ∧
        coeff F R π hπ u 0 ≠ 0 ∧
        PartialSumsConvergeAdically F R π hπ u ∧
        ∀ n : ℕ,
          x =
            (π : K) ^ m *
              (((partialSum F R π hπ u n +
                π ^ n * remainder F R π hπ u n) :
                  F.valuationSubring) : K) := by
  rcases exists_laurent_unit F π hπ hx with ⟨m, u, hu, hx_eq⟩
  refine
    ⟨m, u, hu, hx_eq, coeff_zero_ne_zero_of_isUnit F R π hπ hu,
      partialSum_tendsto_adic F R π hπ u, ?_⟩
  intro n
  have hstage : (u : K) =
      (((partialSum F R π hπ u n +
        π ^ n * remainder F R π hπ u n) :
          F.valuationSubring) : K) := by
    simpa using
      congrArg (fun y : F.valuationSubring => (y : K))
        (partialSum_add_remainder F R π hπ u n)
  rw [hx_eq, hstage]

/-- The complete-DVR expansion, the canonical Laurent-series representation predicate.
The element `x` is represented as
`π^m * (a₀ + a₁π + a₂π² + ⋯)`, where the coefficients are the canonical
representatives attached to the unit part `u`. -/
def isLaurentExpansion
    (R : residueRepresentativeSystem F)
    (π : F.valuationSubring) (hπ : F.valuation.IsUniformizer (π : K))
    (x : K) (m : ℤ) (u : F.valuationSubring) : Prop :=
  IsUnit u ∧
    x = (π : K) ^ m * (u : K) ∧
      coeff F R π hπ u 0 ≠ 0 ∧
        PartialSumsConvergeAdically F R π hπ u ∧
        ∀ n : ℕ,
          x =
            (π : K) ^ m *
              (((partialSum F R π hπ u n +
                π ^ n * remainder F R π hπ u n) :
                  F.valuationSubring) : K)

/-- The complete-DVR expansion, public form: every nonzero element of a complete
discretely valued field has a unique convergent Laurent expansion with respect
to the chosen uniformizer and residue representative system. -/
theorem exists_unique_laurent_expansion
    (R : residueRepresentativeSystem F)
    (π : F.valuationSubring) (hπ : F.valuation.IsUniformizer (π : K))
    {x : K} (hx : x ≠ 0) :
    ∃! p : ℤ × F.valuationSubring,
      isLaurentExpansion F R π hπ x p.1 p.2 := by
  rcases exists_laurent_expansion_data F R π hπ hx with
    ⟨m, u, hu, hx_eq, hcoeff0, htendsto, hstage⟩
  refine ⟨(m, u), ?_, ?_⟩
  · exact ⟨hu, hx_eq, hcoeff0, htendsto, hstage⟩
  · intro p hp
    rcases p with ⟨n, w⟩
    rcases hp with ⟨hw, hx_eq_w, _hcoeff0_w, _htendsto_w, _hstage_w⟩
    have hsame :
        (π : K) ^ m * (u : K) = (π : K) ^ n * (w : K) := by
      rw [← hx_eq, ← hx_eq_w]
    rcases laurent_unit_unique F π hπ hu hw hsame with
      ⟨hm, huw⟩
    exact Prod.ext hm.symm huw.symm

end Valuations
end LubinTate

end
