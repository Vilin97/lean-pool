/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import LeanPool.ZetaZeros.Defs
public import LeanPool.ZetaZeros.Meta.Attr

/-!
# The vocabulary of the Hilbert space inequality

The objects of the source's key proposition, which speaks only of a finite conjugation-invariant
multiset of complex numbers and a test function — no zeta function appears.

A multiset is presented by its finite support `Z` together with a multiplicity function `m`, so
every sum is written over a finite set with explicit weights. That is what removes the source's
bookkeeping over conjugate pairs: because `gz` is conjugation-invariant and `hz` anti-invariant, a
sum over the whole non-real part equals twice a sum over representatives, with no choice of
representatives to make.
-/

@[expose] public section

namespace ZetaZeros

/-- The Fourier transform of a compactly supported real function, at a complex argument. -/
@[zz_tag "def_f_z"]
noncomputable def fz (eta : ℝ → ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  (eta u : ℂ) * Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (u : ℂ) * z)

/-- The even part of the twisted pair, `gz = (fz z + fz (conj z)) / 2`. -/
@[zz_tag "def_g_z"]
noncomputable def gz (eta : ℝ → ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  (fz eta z u + fz eta ((starRingEnd ℂ) z) u) / 2

/-- The odd part of the twisted pair, `hz = (fz z - fz (conj z)) / (2i)`. -/
@[zz_tag "def_h_z"]
noncomputable def hz (eta : ℝ → ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  (fz eta z u - fz eta ((starRingEnd ℂ) z) u) / (2 * Complex.I)

/-- A function `ℝ → ℂ` is symmetric when conjugation acts as reflection: `conj (Φ u) = Φ (-u)`.
The property is preserved by Gram–Schmidt and is what makes the Bessel coefficients real. -/
@[zz_tag "def_symmetric"]
def IsSymmetric (Φ : ℝ → ℂ) : Prop := ∀ u : ℝ, (starRingEnd ℂ) (Φ u) = Φ (-u)

/-- The two-variable kernel `F (u, v) = ∑ z, m z * fz z u * fz z v`, the multiset sum written with
explicit multiplicities. -/
@[zz_tag "def_F"]
noncomputable def bigF (eta : ℝ → ℝ) (Z : Finset ℂ) (m : ℂ → ℕ) (u v : ℝ) : ℂ :=
  ∑ z ∈ Z, (m z : ℂ) * fz eta z u * fz eta z v

/-- The simple real part of the support: real points of multiplicity one. -/
@[zz_tag "def_R2"]
noncomputable def multipleRealPart (Z : Finset ℂ) (m : ℂ → ℕ) : Finset ℂ :=
  Z.filter fun x => x.im = 0 ∧ 2 ≤ m x

/-- The non-real part of the support. -/
@[zz_tag "def_S"]
noncomputable def nonRealPart (Z : Finset ℂ) : Finset ℂ :=
  Z.filter fun z => z.im ≠ 0

/-- The even part is conjugation-invariant. -/
@[zz_tag "lem_g_conj"]
theorem gz_conj (eta : ℝ → ℝ) (z : ℂ) : gz eta ((starRingEnd ℂ) z) = gz eta z := by
  funext u
  simp only [gz, Complex.conj_conj]
  ring

/-- The odd part is conjugation-anti-invariant. -/
@[zz_tag "lem_h_conj"]
theorem hz_conj (eta : ℝ → ℝ) (z : ℂ) :
    hz eta ((starRingEnd ℂ) z) = fun u => -hz eta z u := by
  funext u
  simp only [hz, Complex.conj_conj]
  ring

/-- The twisted function splits into its even and odd parts: `fz = gz + i * hz`. -/
@[zz_tag "lem_f_decomp"]
theorem fz_eq_gz_add_I_mul_hz (eta : ℝ → ℝ) (z : ℂ) (u : ℝ) :
    fz eta z u = gz eta z u + Complex.I * hz eta z u := by
  simp only [gz, hz]
  field_simp
  ring

end ZetaZeros
