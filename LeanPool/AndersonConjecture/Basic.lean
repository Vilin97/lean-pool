/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Quasi-Complete Local Rings

Definitions of quasi-completeness and weak quasi-completeness for
local rings, following Anderson (2014). A local ring (R, M) is
quasi-complete if every descending chain of ideals eventually
stabilizes modulo powers of M. The weak variant restricts to
chains with zero intersection. We also define analytical
irreducibility (the M-adic completion is a domain).
-/

open scoped Pointwise

variable (R : Type*) [CommRing R] [IsLocalRing R]

/-- A local ring `R` is quasi-complete if for any antitone sequence of
ideals `A : ℕ → Ideal R` and each `k : ℕ`, there exists `s` such that
`A s ≤ (⨅ n, A n) ⊔ (IsLocalRing.maximalIdeal R) ^ k`.

This is Definition 1.1 of Anderson (2014). -/
def IsQuasiComplete : Prop :=
  ∀ (A : ℕ → Ideal R), Antitone A →
    ∀ (k : ℕ), ∃ s,
      A s ≤ (⨅ n, A n) ⊔ (IsLocalRing.maximalIdeal R) ^ k

/-- A local ring `R` is weakly quasi-complete if for any antitone sequence
of ideals `A : ℕ → Ideal R` with `⨅ n, A n = ⊥` and each `k : ℕ`,
there exists `s` such that `A s ≤ (IsLocalRing.maximalIdeal R) ^ k`.

Equivalently, this is `IsQuasiComplete` restricted to sequences whose
intersection is `⊥`. -/
def IsWeaklyQuasiComplete : Prop :=
  ∀ (A : ℕ → Ideal R), Antitone A → (⨅ n, A n) = ⊥ →
    ∀ (k : ℕ), ∃ s, A s ≤ (IsLocalRing.maximalIdeal R) ^ k

/-- A local ring `R` is **analytically irreducible** if its
maximal-ideal-adic completion is a domain. (This notion is primarily of
interest for Noetherian local rings.) -/
def IsAnalyticallyIrreducible : Prop :=
  IsDomain (AdicCompletion (IsLocalRing.maximalIdeal R) R)

/-- Quasi-completeness implies weak quasi-completeness. -/
theorem IsQuasiComplete.isWeaklyQuasiComplete
    (h : IsQuasiComplete R) : IsWeaklyQuasiComplete R := by
  intro A hA hInt k
  obtain ⟨s, hs⟩ := h A hA k
  exact ⟨s, by rwa [hInt, bot_sup_eq] at hs⟩

/-- If `R` is quasi-complete, then every quotient `R ⧸ I` is weakly
quasi-complete.
This is one direction of Anderson Theorem 5, Item 3. -/
theorem IsQuasiComplete.quotient_isWeaklyQuasiComplete
    (h : IsQuasiComplete R) (I : Ideal R) (hI : I ≠ ⊤) :
    letI : Nontrivial (R ⧸ I) :=
      Ideal.Quotient.nontrivial_iff.mpr hI
    letI : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective'
        (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    IsWeaklyQuasiComplete (R ⧸ I) := by
  letI : Nontrivial (R ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr hI
  letI : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective'
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  set mk := Ideal.Quotient.mk I
  haveI : IsLocalHom mk :=
    IsLocalHom.of_surjective mk Ideal.Quotient.mk_surjective
  have hmap_M : Ideal.map mk (IsLocalRing.maximalIdeal R) ≤
      IsLocalRing.maximalIdeal (R ⧸ I) := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective mk
        Ideal.Quotient.mk_surjective).mp hx
    rw [IsLocalRing.mem_maximalIdeal] at hr ⊢
    exact fun hu => hr (isUnit_of_map_unit mk r hu)
  intro B hB hBint k
  set A : ℕ → Ideal R := fun n => Ideal.comap mk (B n)
  have hA_anti : Antitone A :=
    fun _ _ hmn => Ideal.comap_mono (hB hmn)
  obtain ⟨s, hs⟩ := h A hA_anti k
  refine ⟨s, ?_⟩
  rw [← Ideal.map_comap_of_surjective mk
    Ideal.Quotient.mk_surjective (B s)]
  apply le_trans (Ideal.map_mono hs)
  rw [Ideal.map_sup]
  have hinf_le : Ideal.map mk (⨅ n, A n) ≤ ⨅ n, B n := by
    apply le_iInf
    intro n
    exact le_trans (Ideal.map_mono (iInf_le A n))
      (Ideal.map_comap_of_surjective mk
        Ideal.Quotient.mk_surjective (B n)).le
  have hpow_le :
      Ideal.map mk (IsLocalRing.maximalIdeal R ^ k) ≤
        (IsLocalRing.maximalIdeal (R ⧸ I)) ^ k := by
    rw [Ideal.map_pow mk (IsLocalRing.maximalIdeal R) k]
    exact Ideal.pow_right_mono hmap_M k
  calc Ideal.map mk (⨅ n, A n) ⊔
        Ideal.map mk (IsLocalRing.maximalIdeal R ^ k)
      _ ≤ (⨅ n, B n) ⊔
        (IsLocalRing.maximalIdeal (R ⧸ I)) ^ k :=
          sup_le_sup hinf_le hpow_le
      _ = ⊥ ⊔ (IsLocalRing.maximalIdeal (R ⧸ I)) ^ k := by
          rw [hBint]
      _ = (IsLocalRing.maximalIdeal (R ⧸ I)) ^ k :=
          bot_sup_eq _
