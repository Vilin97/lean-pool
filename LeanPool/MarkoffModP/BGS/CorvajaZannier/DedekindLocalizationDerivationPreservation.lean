/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Tactic

/-!
# Derivations preserving localizations

An ambient derivation that maps a domain into itself also maps every prime
localization into itself.  The statement deliberately does not require an
algebra structure from the derivation's constant ring to the localized ring;
that structure need not exist in the Frobenius-constant application.
-/

@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section

/-- An ambient derivation which preserves a domain also preserves each of its
localizations at a prime.  This is the quotient-rule bridge from a global
different-annihilator certificate to the local DVR Wronskian bounds. -/
theorem ambientDerivation_preserves_localizationAtPrime_of_preserves
    {C R U : Type*} [CommRing C] [CommRing R] [IsDomain R] [Field U]
    [Algebra C U] [Algebra R U] [IsFractionRing R U]
    (q : Ideal R) [q.IsPrime]
    [Algebra (Localization.AtPrime q) U]
    [IsScalarTower R (Localization.AtPrime q) U]
    (E : Derivation C U U)
    (hE : ∀ r : R, ∃ r' : R,
      E (algebraMap R U r) = algebraMap R U r') :
    ∀ z : Localization.AtPrime q, ∃ z' : Localization.AtPrime q,
      E (algebraMap (Localization.AtPrime q) U z) =
        algebraMap (Localization.AtPrime q) U z' := by
  intro z
  obtain ⟨⟨a, d, hd⟩, hzd⟩ := IsLocalization.surj q.primeCompl z
  obtain ⟨a', ha'⟩ := hE a
  obtain ⟨d', hd'⟩ := hE d
  let dSub : q.primeCompl := ⟨d, hd⟩
  let invD : Localization.AtPrime q :=
    IsLocalization.mk' (Localization.AtPrime q) 1 dSub
  let z' : Localization.AtPrime q :=
    (algebraMap R (Localization.AtPrime q) a' -
      z * algebraMap R (Localization.AtPrime q) d') * invD
  have hd0 : d ≠ 0 := by
    intro hdZero
    exact hd (hdZero ▸ q.zero_mem)
  have hdU : algebraMap R U d ≠ 0 := by
    simpa using (IsFractionRing.injective R U).ne hd0
  have hzdU :
      algebraMap (Localization.AtPrime q) U z * algebraMap R U d =
        algebraMap R U a := by
    calc
      algebraMap (Localization.AtPrime q) U z * algebraMap R U d =
          algebraMap (Localization.AtPrime q) U z *
            algebraMap (Localization.AtPrime q) U
              (algebraMap R (Localization.AtPrime q) d) := by
              rw [IsScalarTower.algebraMap_apply R
                (Localization.AtPrime q) U d]
      _ = algebraMap (Localization.AtPrime q) U
            (z * algebraMap R (Localization.AtPrime q) d) := by
              rw [map_mul]
      _ = algebraMap (Localization.AtPrime q) U
          (algebraMap R (Localization.AtPrime q) a) := by rw [hzd]
      _ = algebraMap R U a :=
        (IsScalarTower.algebraMap_apply R (Localization.AtPrime q) U a).symm
  have hder := congrArg (fun x : U => E x) hzdU
  rw [E.leibniz, ha', hd'] at hder
  have hder' :
      E (algebraMap (Localization.AtPrime q) U z) * algebraMap R U d +
        algebraMap (Localization.AtPrime q) U z * algebraMap R U d' =
          algebraMap R U a' := by
    simp only [Algebra.smul_def, Algebra.algebraMap_self_apply] at hder
    linear_combination hder
  have hinv :
      algebraMap (Localization.AtPrime q) U invD * algebraMap R U d = 1 := by
    have hspec := IsLocalization.mk'_spec
      (Localization.AtPrime q) (1 : R) dSub
    calc
      algebraMap (Localization.AtPrime q) U invD * algebraMap R U d =
          algebraMap (Localization.AtPrime q) U invD *
            algebraMap (Localization.AtPrime q) U
              (algebraMap R (Localization.AtPrime q) d) := by
                rw [IsScalarTower.algebraMap_apply R
                  (Localization.AtPrime q) U d]
      _ = algebraMap (Localization.AtPrime q) U
          (invD * algebraMap R (Localization.AtPrime q) d) := by rw [map_mul]
      _ = algebraMap (Localization.AtPrime q) U
          (algebraMap R (Localization.AtPrime q) 1) := by
            rw [show invD * algebraMap R (Localization.AtPrime q) d =
              algebraMap R (Localization.AtPrime q) 1 by
                simp [invD, dSub] using hspec]
      _ = 1 := by simp
  refine ⟨z', ?_⟩
  apply mul_right_cancel₀ hdU
  calc
    E (algebraMap (Localization.AtPrime q) U z) * algebraMap R U d =
        algebraMap R U a' -
          algebraMap (Localization.AtPrime q) U z * algebraMap R U d' :=
      eq_sub_of_add_eq hder'
    _ = algebraMap (Localization.AtPrime q) U z' * algebraMap R U d := by
      simp only [z', map_mul, map_sub]
      rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime q) U a',
        ← IsScalarTower.algebraMap_apply R (Localization.AtPrime q) U d']
      rw [mul_assoc, hinv, mul_one]

end

end BGS.CorvajaZannier
