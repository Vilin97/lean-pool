/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import LeanPool.ZetaZeros.Hilbert.Defs

/-!
# Symmetry of the twisted functions

Conjugation acts on the twisted functions as reflection in the origin. This is the property that
survives Gram–Schmidt and makes every Bessel coefficient real, which is what lets the source treat
them with real inequalities rather than complex ones.

Everything here follows from one computation, `conj_fz`: conjugating `fz eta z` reflects the
argument and conjugates the twist.
-/

@[expose] public section

namespace ZetaZeros

variable {lam : ℝ} {eta : ℝ → ℝ}

/-- Conjugation reflects the argument and conjugates the twist. The single computation the three
symmetry lemmas below rest on. -/
theorem conj_fz (he : ∀ x, eta (-x) = eta x) (z : ℂ) (u : ℝ) :
    (starRingEnd ℂ) (fz eta z u) = fz eta ((starRingEnd ℂ) z) (-u) := by
  simp only [fz, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg, map_mul,
    Complex.conj_I, Complex.conj_ofReal, map_ofNat, he u, Complex.ofReal_neg]
  ring_nf

/-- At a real point the twisted function is symmetric. -/
@[zz_tag "lem_f_symmetric"]
theorem isSymmetric_fz (h : IsAdmissible lam eta) {x : ℂ} (hx : x.im = 0) :
    IsSymmetric (fz eta x) := by
  intro u
  rw [conj_fz h.even x u]
  congr 1
  exact Complex.ext (by simp) (by simp [hx])

/-- The even part is symmetric. -/
@[zz_tag "lem_g_symmetric"]
theorem isSymmetric_gz (h : IsAdmissible lam eta) (z : ℂ) : IsSymmetric (gz eta z) := by
  intro u
  simp only [gz, map_div₀, map_add, map_ofNat]
  rw [conj_fz h.even z u, conj_fz h.even ((starRingEnd ℂ) z) u, Complex.conj_conj]
  ring

/-- The odd part is symmetric. -/
@[zz_tag "lem_h_symmetric"]
theorem isSymmetric_hz (h : IsAdmissible lam eta) (z : ℂ) : IsSymmetric (hz eta z) := by
  intro u
  simp only [hz, map_div₀, map_sub, map_mul, map_ofNat, Complex.conj_I]
  rw [conj_fz h.even z u, conj_fz h.even ((starRingEnd ℂ) z) u, Complex.conj_conj]
  field_simp
  ring

end ZetaZeros
