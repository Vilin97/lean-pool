/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.Diophantine.LocalCounts

/-!
# Exact first-coordinate product formula

This file formalizes the exact finite-product identity preceding the asymptotic estimate in
published Section 7.  A first coordinate is coprime to the squarefree product modulus exactly
when it is nonzero in every prime factor.  The carrier below records that local condition
directly; no real-valued comparison with `exp (-2 * L)` is asserted here.
-/

@[expose] public section

namespace BGS.Markoff

open Finset

/-- Punctured Markoff points whose first coordinate is nonzero.  This is definitionally the
complement of the zero-coordinate locus counted in `LocalCounts`. -/
def puncturedMarkoffFirstCoordinateNonzero (R : Type*) [CommRing R] :
    Set (PuncturedMarkoffSurface R) :=
  (puncturedMarkoffFirstCoordinateZero R)ᶜ

@[simp] theorem mem_puncturedMarkoffFirstCoordinateNonzero_iff
    {R : Type*} [CommRing R] (x : PuncturedMarkoffSurface R) :
    x ∈ puncturedMarkoffFirstCoordinateNonzero R ↔ x.1.1.x1 ≠ 0 := by
  simp [puncturedMarkoffFirstCoordinateNonzero, puncturedMarkoffFirstCoordinateZero]

/-- Exact local numerator in published equation (97). -/
theorem puncturedMarkoffFirstCoordinateNonzero_zmod_card_eq_of_mod_four_eq_one
    (p : ℕ) [Fact p.Prime] (hpModFour : p % 4 = 1) :
    Nat.card ↑(puncturedMarkoffFirstCoordinateNonzero (ZMod p)) = p ^ 2 + p + 2 := by
  change (puncturedMarkoffFirstCoordinateZero (ZMod p))ᶜ.ncard = p ^ 2 + p + 2
  rw [Set.ncard_compl, ← Nat.card_coe_set_eq,
    puncturedMarkoffFirstCoordinateZero_zmod_card_eq_of_mod_four_eq_one p hpModFour,
    puncturedMarkoffSurface_zmod_card_eq_of_mod_four_eq_one p hpModFour]
  have hpTwo : 2 ≤ p := (Fact.out : p.Prime).two_le
  omega

/-- Primewise-punctured points whose first coordinate is nonzero at every factor. -/
def primewisePuncturedFirstCoordinateNonzero {ι : Type*} (a : ι → ℕ) :
    Set (PrimewisePuncturedMarkoffSurface a) :=
  {x | ∀ i, x i ∈ puncturedMarkoffFirstCoordinateNonzero (ZMod (a i))}

/-- The primewise nonzero-coordinate carrier is the product of its local subtypes. -/
def primewisePuncturedFirstCoordinateNonzeroEquivPi {ι : Type*} (a : ι → ℕ) :
    ↑(primewisePuncturedFirstCoordinateNonzero a) ≃
      ∀ i, ↑(puncturedMarkoffFirstCoordinateNonzero (ZMod (a i))) where
  toFun x i := ⟨x.1 i, x.2 i⟩
  invFun x := ⟨fun i => (x i).1, fun i => (x i).2⟩
  left_inv x := by apply Subtype.ext; funext i; rfl
  right_inv x := by funext i; apply Subtype.ext; rfl

/-- Exact product numerator for points whose first coordinate is nonzero at every prime. -/
theorem primewisePuncturedFirstCoordinateNonzero_card_eq_of_mod_four_eq_one
    {ι : Type*} [Fintype ι] (a : ι → ℕ) [∀ i, Fact (a i).Prime]
    (hmod : ∀ i, a i % 4 = 1) :
    Nat.card ↑(primewisePuncturedFirstCoordinateNonzero a) =
      ∏ i, (a i ^ 2 + a i + 2) := by
  rw [Nat.card_congr (primewisePuncturedFirstCoordinateNonzeroEquivPi a), Nat.card_pi]
  apply Finset.prod_congr rfl
  intro i _
  exact puncturedMarkoffFirstCoordinateNonzero_zmod_card_eq_of_mod_four_eq_one
    (a i) (hmod i)

/-- First-coordinate nonvanishing pulled back to the single-residue-ring CRT presentation. -/
def crtPrimewisePuncturedFirstCoordinateNonzero {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (coprime : Pairwise (Function.onFun Nat.Coprime a)) :
    Set (CRTPrimewisePuncturedMarkoffSurface a coprime) :=
  {x | ∀ i, primewisePuncturedCRTEquiv a coprime x i ∈
    puncturedMarkoffFirstCoordinateNonzero (ZMod (a i))}

/-- CRT restricts to the first-coordinate-nonzero carriers. -/
noncomputable def crtPrimewisePuncturedFirstCoordinateNonzeroEquiv
    {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (coprime : Pairwise (Function.onFun Nat.Coprime a)) :
    ↑(crtPrimewisePuncturedFirstCoordinateNonzero a coprime) ≃
      ↑(primewisePuncturedFirstCoordinateNonzero a) :=
  (primewisePuncturedCRTEquiv a coprime).subtypeEquiv fun _ => Iff.rfl

/-- The CRT presentation has the same exact product numerator. -/
theorem crtPrimewisePuncturedFirstCoordinateNonzero_card_eq_of_mod_four_eq_one
    {ι : Type*} [Fintype ι] (a : ι → ℕ) [∀ i, Fact (a i).Prime]
    (coprime : Pairwise (Function.onFun Nat.Coprime a)) (hmod : ∀ i, a i % 4 = 1) :
    Nat.card ↑(crtPrimewisePuncturedFirstCoordinateNonzero a coprime) =
      ∏ i, (a i ^ 2 + a i + 2) := by
  rw [Nat.card_congr (crtPrimewisePuncturedFirstCoordinateNonzeroEquiv a coprime)]
  exact primewisePuncturedFirstCoordinateNonzero_card_eq_of_mod_four_eq_one a hmod

/-- Exact rational proportion in product-numerator form.  This deliberately stops before the
paper's real-valued asymptotic comparison. -/
theorem primewisePuncturedFirstCoordinateNonzero_proportion_eq_product
    {ι : Type*} [Fintype ι] (a : ι → ℕ) [∀ i, Fact (a i).Prime]
    (hmod : ∀ i, a i % 4 = 1) :
    (Nat.card ↑(primewisePuncturedFirstCoordinateNonzero a) : ℚ) /
        Nat.card (PrimewisePuncturedMarkoffSurface a) =
      ∏ i, ((a i ^ 2 + a i + 2 : ℕ) : ℚ) / (a i ^ 2 + 3 * a i : ℕ) := by
  rw [primewisePuncturedFirstCoordinateNonzero_card_eq_of_mod_four_eq_one a hmod,
    primewisePuncturedMarkoffSurface_card_eq_of_mod_four_eq_one a hmod]
  push_cast
  exact (Finset.prod_div_distrib _ _).symm

/-- A local numerator factor is exactly one minus the zero-coordinate proportion. -/
theorem firstCoordinateNonzero_proportion_factor_eq_one_sub
    (p : ℕ) [Fact p.Prime] (hpModFour : p % 4 = 1) :
    ((p ^ 2 + p + 2 : ℕ) : ℚ) / (p ^ 2 + 3 * p : ℕ) =
      1 - ((2 * p - 2 : ℕ) : ℚ) / (p ^ 2 + 3 * p : ℕ) := by
  have hpTwo : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hsub : 2 ≤ 2 * p := by omega
  have hdenNat : 0 < p ^ 2 + 3 * p := by omega
  have hden : ((p ^ 2 + 3 * p : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hdenNat.ne'
  push_cast [Nat.cast_sub hsub]
  field_simp [hden]
  ring

/-- Exact rational form of published equation (97), with one local zero-coordinate factor
removed at each prime. -/
theorem primewisePuncturedFirstCoordinateNonzero_proportion_eq_product_one_sub
    {ι : Type*} [Fintype ι] (a : ι → ℕ) [∀ i, Fact (a i).Prime]
    (hmod : ∀ i, a i % 4 = 1) :
    (Nat.card ↑(primewisePuncturedFirstCoordinateNonzero a) : ℚ) /
        Nat.card (PrimewisePuncturedMarkoffSurface a) =
      ∏ i, (1 - ((2 * a i - 2 : ℕ) : ℚ) / (a i ^ 2 + 3 * a i : ℕ)) := by
  rw [primewisePuncturedFirstCoordinateNonzero_proportion_eq_product a hmod]
  apply Finset.prod_congr rfl
  intro i _
  exact firstCoordinateNonzero_proportion_factor_eq_one_sub (a i) (hmod i)

/-- The same exact rational proportion on the single-residue-ring CRT carrier. -/
theorem crtPrimewisePuncturedFirstCoordinateNonzero_proportion_eq_product_one_sub
    {ι : Type*} [Fintype ι] (a : ι → ℕ) [∀ i, Fact (a i).Prime]
    (coprime : Pairwise (Function.onFun Nat.Coprime a)) (hmod : ∀ i, a i % 4 = 1) :
    (Nat.card ↑(crtPrimewisePuncturedFirstCoordinateNonzero a coprime) : ℚ) /
        Nat.card (CRTPrimewisePuncturedMarkoffSurface a coprime) =
      ∏ i, (1 - ((2 * a i - 2 : ℕ) : ℚ) / (a i ^ 2 + 3 * a i : ℕ)) := by
  rw [crtPrimewisePuncturedFirstCoordinateNonzero_card_eq_of_mod_four_eq_one a coprime hmod,
    crtPrimewisePuncturedMarkoffSurface_card_eq_of_mod_four_eq_one a coprime hmod]
  rw [← primewisePuncturedFirstCoordinateNonzero_card_eq_of_mod_four_eq_one a hmod,
    ← primewisePuncturedMarkoffSurface_card_eq_of_mod_four_eq_one a hmod]
  exact primewisePuncturedFirstCoordinateNonzero_proportion_eq_product_one_sub a hmod

end BGS.Markoff
