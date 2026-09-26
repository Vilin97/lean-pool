/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Projection


/-!
# The square-zero linear trace calculation

This file isolates the finite-dimensional block calculation used in the local
trace argument.  Composition is written in Lean's order:
`F.comp G` sends `v` to `F (G v)`.  Thus the commutator hypothesis below is

`A.comp B - B.comp A = C.comp Z`.

If `ker C = range C`, then `C` identifies `V / range C` with `range C`.
Choosing a linear section of the quotient map gives the usual two-by-two
block decomposition.  The off-diagonal block of the displayed commutator is
a sum of two rectangular commutators, so its trace is zero.
-/

@[expose] public section

noncomputable section

namespace Stafford38.Characteristic.SquareZeroLinearTrace

open Function

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- An endomorphism commuting with `C` preserves `range C`. -/
lemma mapsTo_range_of_comp_comm (C F : V →ₗ[k] V)
    (hF : F.comp C = C.comp F) : Set.MapsTo F (LinearMap.range C) (LinearMap.range C) := by
  rintro _ ⟨v, rfl⟩
  refine ⟨F v, ?_⟩
  exact LinearMap.congr_fun hF.symm v

/-- The endomorphism induced by `F` on `V / range C`. -/
def quotientEnd (C F : V →ₗ[k] V) (hF : F.comp C = C.comp F) :
    (V ⧸ LinearMap.range C) →ₗ[k] (V ⧸ LinearMap.range C) :=
  (LinearMap.range C).mapQ (LinearMap.range C) F
    (mapsTo_range_of_comp_comm C F hF)

/-- The restriction of a commuting endomorphism to `range C`. -/
def rangeEnd (C F : V →ₗ[k] V) (hF : F.comp C = C.comp F) :
    LinearMap.range C →ₗ[k] LinearMap.range C :=
  F.restrict (mapsTo_range_of_comp_comm C F hF)

/-- Exactness makes the map induced by `C` from the quotient to its range an equivalence. -/
def quotientToRangeEquiv (C : V →ₗ[k] V) (hExact : LinearMap.ker C = LinearMap.range C) :
    (V ⧸ LinearMap.range C) ≃ₗ[k] LinearMap.range C := by
  let cbar : (V ⧸ LinearMap.range C) →ₗ[k] LinearMap.range C :=
    (LinearMap.range C).liftQ C.rangeRestrict (by
      intro x hx
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      exact LinearMap.mem_ker.mp (hExact ▸ hx))
  refine LinearEquiv.ofBijective cbar ⟨?_, ?_⟩
  · intro q₁ q₂ hq
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range C) q₁
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range C) q₂
    apply (Submodule.Quotient.eq (LinearMap.range C)).mpr
    rw [← hExact, LinearMap.mem_ker]
    rw [map_sub, sub_eq_zero]
    simpa [cbar] using Subtype.ext_iff.mp hq
  · intro y
    obtain ⟨x, hx⟩ := y.property
    refine ⟨Submodule.Quotient.mk x, ?_⟩
    exact Subtype.ext hx

@[simp]
lemma quotientToRangeEquiv_apply_mk (C : V →ₗ[k] V)
    (hExact : LinearMap.ker C = LinearMap.range C) (v : V) :
    quotientToRangeEquiv C hExact (Submodule.Quotient.mk v) = C.rangeRestrict v := rfl

private lemma trace_commutator_sum_eq_zero
    {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (P Q X Y : W →ₗ[k] W) :
    LinearMap.trace k W
      (P.comp Y - Y.comp P + (X.comp Q - Q.comp X)) = 0 := by
  simp only [map_add, map_sub]
  rw [LinearMap.trace_comp_comm' P Y, LinearMap.trace_comp_comm' X Q]
  abel

/-- The upper-right block of a commuting endomorphism relative to a section of
the quotient by `range C`. -/
def offDiagonal (C F : V →ₗ[k] V) (hF : F.comp C = C.comp F)
    (s : (V ⧸ LinearMap.range C) →ₗ[k] V)
    (hs : (LinearMap.range C).mkQ.comp s = LinearMap.id) :
    (V ⧸ LinearMap.range C) →ₗ[k] LinearMap.range C :=
  (F.comp s - s.comp (quotientEnd C F hF)).codRestrict (LinearMap.range C) (by
    intro x
    have hz :
        (LinearMap.range C).mkQ
          ((F.comp s - s.comp (quotientEnd C F hF)) x) = 0 := by
      change (LinearMap.range C).mkQ
        (F (s x) - s (quotientEnd C F hF x)) = 0
      rw [map_sub]
      have hsx : (LinearMap.range C).mkQ (s x) = x := by
        exact LinearMap.congr_fun hs x
      have hsFx :
          (LinearMap.range C).mkQ (s (quotientEnd C F hF x)) = quotientEnd C F hF x := by
        exact LinearMap.congr_fun hs (quotientEnd C F hF x)
      have hFq :
          (LinearMap.range C).mkQ (F (s x)) = quotientEnd C F hF x := by
        calc
          (LinearMap.range C).mkQ (F (s x)) =
              quotientEnd C F hF ((LinearMap.range C).mkQ (s x)) := rfl
          _ = quotientEnd C F hF x := congrArg (quotientEnd C F hF) hsx
      rw [hFq, hsFx, sub_self]
    have hxker :
        (F.comp s - s.comp (quotientEnd C F hF)) x ∈
          LinearMap.ker (LinearMap.range C).mkQ := LinearMap.mem_ker.mpr hz
    simpa only [Submodule.ker_mkQ] using hxker)

/-- The exact square-zero trace lemma.  Exactness itself implies `C² = 0`,
so neither a separate square-zero hypothesis nor a characteristic assumption
is needed for this linear calculation. -/
theorem quotientEnd_trace_eq_zero
    [FiniteDimensional k V]
    (C A B Z : V →ₗ[k] V)
    (hExact : LinearMap.ker C = LinearMap.range C)
    (hAC : A.comp C = C.comp A)
    (hBC : B.comp C = C.comp B)
    (hZC : Z.comp C = C.comp Z)
    (hcomm : A.comp B - B.comp A = C.comp Z) :
    LinearMap.trace k (V ⧸ LinearMap.range C) (quotientEnd C Z hZC) = 0 := by
  let q : V →ₗ[k] (V ⧸ LinearMap.range C) := (LinearMap.range C).mkQ
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective (LinearMap.range C)))
  let e := quotientToRangeEquiv C hExact
  let Aq := quotientEnd C A hAC
  let Bq := quotientEnd C B hBC
  let Zq := quotientEnd C Z hZC
  let Ak := rangeEnd C A hAC
  let Bk := rangeEnd C B hBC
  let Au := offDiagonal C A hAC s hs
  let Bu := offDiagonal C B hBC s hs
  have hs_apply (x : V ⧸ LinearMap.range C) : q (s x) = x := by
    exact LinearMap.congr_fun hs x
  have hquot_comm : Aq.comp Bq = Bq.comp Aq := by
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range C) x
    apply (Submodule.Quotient.eq (LinearMap.range C)).mpr
    change A (B v) - B (A v) ∈ LinearMap.range C
    refine ⟨Z v, ?_⟩
    exact (LinearMap.congr_fun hcomm v).symm
  have heA : e.toLinearMap.comp Aq = Ak.comp e.toLinearMap := by
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range C) x
    apply Subtype.ext
    exact LinearMap.congr_fun hAC.symm v
  have heB : e.toLinearMap.comp Bq = Bk.comp e.toLinearMap := by
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range C) x
    apply Subtype.ext
    exact LinearMap.congr_fun hBC.symm v
  have hblock :
      e.toLinearMap.comp Zq =
        Ak.comp Bu + Au.comp Bq - Bk.comp Au - Bu.comp Aq := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hABx : Aq (Bq x) = Bq (Aq x) := LinearMap.congr_fun hquot_comm x
    have hleft : e (Zq x) = C.rangeRestrict (Z (s x)) := by
      calc
        e (Zq x) = e (Zq (q (s x))) := by rw [hs_apply x]
        _ = C.rangeRestrict (Z (s x)) := rfl
    change (e (Zq x) : V) = _
    rw [hleft]
    dsimp [Ak, Bk, Au, Bu, rangeEnd, offDiagonal]
    change C (Z (s x)) =
      A (B (s x) - s (Bq x)) +
          (A (s (Bq x)) - s (Aq (Bq x))) -
        B (A (s x) - s (Aq x)) -
      (B (s (Aq x)) - s (Bq (Aq x)))
    have hh := LinearMap.congr_fun hcomm (s x)
    simp only [LinearMap.sub_apply, LinearMap.comp_apply] at hh
    rw [← hh]
    simp only [  map_sub]
    rw [hABx]
    abel
  let X : (V ⧸ LinearMap.range C) →ₗ[k] (V ⧸ LinearMap.range C) :=
    e.symm.toLinearMap.comp Au
  let Y : (V ⧸ LinearMap.range C) →ₗ[k] (V ⧸ LinearMap.range C) :=
    e.symm.toLinearMap.comp Bu
  have hZblock : Zq = Aq.comp Y - Y.comp Aq + (X.comp Bq - Bq.comp X) := by
    apply LinearMap.ext
    intro x
    apply e.injective
    have hb := LinearMap.congr_fun hblock x
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply] at hb ⊢
    have hY (u : V ⧸ LinearMap.range C) : e (Y u) = Bu u := by
      exact e.apply_symm_apply (Bu u)
    have hX (u : V ⧸ LinearMap.range C) : e (X u) = Au u := by
      exact e.apply_symm_apply (Au u)
    have hAY : e (Aq (Y x)) = Ak (Bu x) := by
      calc
        e (Aq (Y x)) = Ak (e (Y x)) := LinearMap.congr_fun heA (Y x)
        _ = Ak (Bu x) := congrArg Ak (hY x)
    have hBX : e (Bq (X x)) = Bk (Au x) := by
      calc
        e (Bq (X x)) = Bk (e (X x)) := LinearMap.congr_fun heB (X x)
        _ = Bk (Au x) := congrArg Bk (hX x)
    rw [map_add, map_sub, map_sub, hAY, hY, hX, hBX]
    exact hb.trans (by abel)
  change LinearMap.trace k (V ⧸ LinearMap.range C) Zq = 0
  rw [hZblock]
  exact trace_commutator_sum_eq_zero Aq Bq X Y


end Stafford38.Characteristic.SquareZeroLinearTrace
