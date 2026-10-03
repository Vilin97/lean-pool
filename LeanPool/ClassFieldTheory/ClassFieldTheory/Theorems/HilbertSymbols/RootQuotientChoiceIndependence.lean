/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
/-!
# Independence of the chosen Kummer root

When the base field contains the `n`-th roots of unity, the quotient
`σ(u) / u` depends only on `u ^ n`. In particular, the Artin root quotient
used to normalize a local Hilbert symbol does not depend on the root chosen.
-/

@[expose] public section

namespace ClassFieldTheory

/-- Two roots with the same `n`-th power have the same Galois root quotient
when the base field contains a primitive `n`-th root of unity. This also
applies when `σ` is a local Artin automorphism. -/
theorem rootQuotient_eq_of_pow_eq_pow
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (u v : Lˣ) (huv : u ^ (n : ℕ) = v ^ (n : ℕ))
    (σ : L ≃ₐ[K] L) :
    σ • u / u = σ • v / v := by
  have hpow : (u / v) ^ (n : ℕ) = 1 := by
    rw [div_pow, huv]
    exact div_self' (v ^ (n : ℕ))
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Kˣ,
      u / v = Units.map (algebraMap K L).toMonoidHom ζ := by
    let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
    let η : rootsOfUnity (n : ℕ) L := ⟨u / v, hpow⟩
    let e : rootsOfUnity (n : ℕ) K ≃* rootsOfUnity (n : ℕ) L :=
      rootsOfUnityEquivOfPrimitiveRoots (algebraMap K L).injective hmu
    refine ⟨(e.symm η : rootsOfUnity (n : ℕ) K).1, ?_⟩
    apply Units.ext
    exact (rootsOfUnityEquivOfPrimitiveRoots_symm_apply
      (algebraMap K L).injective hmu η).symm
  have hfixed : σ • (u / v) = u / v := by
    rw [hζ]
    apply Units.ext
    change σ (algebraMap K L (ζ : K)) = algebraMap K L (ζ : K)
    exact σ.commutes (ζ : K)
  have hquot : (σ • u / u) / (σ • v / v) = 1 := by
    have hchange : (σ • u / u) / (σ • v / v) =
        (σ • (u / v)) / (u / v) := by
      rw [smul_div' σ u v]
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      calc
        (σ • u) * u⁻¹ * (v * (σ • v)⁻¹) =
            (σ • u) * v * (u⁻¹ * (σ • v)⁻¹) :=
          mul_mul_mul_comm _ _ _ _
        _ = (σ • u) * v * ((σ • v)⁻¹ * u⁻¹) :=
          congrArg (fun t : Lˣ => (σ • u) * v * t)
            (mul_comm u⁻¹ (σ • v)⁻¹)
        _ = (σ • u) * (σ • v)⁻¹ * (v * u⁻¹) :=
          mul_mul_mul_comm _ _ _ _
    rw [hchange, hfixed]
    exact div_self' (u / v)
  exact div_eq_one.mp hquot

end ClassFieldTheory
