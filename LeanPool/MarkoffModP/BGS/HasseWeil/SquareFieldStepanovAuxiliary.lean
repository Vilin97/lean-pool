/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.OnePointStepanovDegreeTwoAuxiliary
import LeanPool.MarkoffModP.BGS.HasseWeil.PlaneStepanovAuxiliary
import LeanPool.MarkoffModP.BGS.HasseWeil.SquareFieldStepanovRestriction
import Mathlib.Tactic

/-!
# A sharp one-point Stepanov auxiliary over a square constant field

The function field is defined over the full square field `S`, so an
`S`-rational normalization point is a place of degree one.  The integer
`s = #K`, for a quadratic subfield `K`, is used only as the half-Frobenius
scale.  This keeps both the Riemann-space dimension count and the final pole
height sharp.
-/

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped Polynomial

noncomputable section


variable (K S : Type*) [Field K] [Fintype K]
  [Field S] [Fintype S] [DecidableEq S] [Algebra K S]
  [DecidableEq (RatFunc S)]
variable (L : Type*) [Field L] [Algebra (RatFunc S) L]
  [FiniteDimensional (RatFunc S) L]
  [Algebra.IsSeparable (RatFunc S) L]

local instance squareFieldAuxiliaryConstantAlgebra : Algebra S L :=
  RingHom.toAlgebra ((algebraMap (RatFunc S) L).comp
    (algebraMap S (RatFunc S)))

local instance squareFieldAuxiliaryConstantTower :
    IsScalarTower S (RatFunc S) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Riemann's inequality at a degree-one place, together with the standard
large-square-field condition, produces the semilinear Stepanov auxiliary.
-/
theorem exists_squareField_onePointStepanovAuxiliary_of_degree_one
    (P : FiniteExtensionPlace S L) (g : ℕ)
    (hconstants : algebraicClosure S L = ⊥)
    (hdegree : finiteExtensionPlaceDegree S L P = 1)
    (hriemann : ∀ N,
      N + 1 ≤ Module.finrank S
        (finiteExtensionOnePointRiemannSpace S L P N) + g)
    (hlarge : (g + 1) * (g + 2) ≤ Fintype.card K) :
    let s := Fintype.card K
    let ell := stepanovEll s
    let m := stepanovM g s
    ∃ (u : Option (Fin (ell - g)) → L)
      (du : Option (Fin (ell - g)) → ℕ)
      (v : Option (Fin (m - g)) → L)
      (dv : Option (Fin (m - g)) → ℕ)
      (c : (Option (Fin (ell - g)) × Option (Fin (m - g))) →₀ S),
      onePointSectionFamilySpec S L P ell u du ∧
      onePointSectionFamilySpec S L P m v dv ∧
      c ≠ 0 ∧
      onePointStepanovSecondRestrictionMap S L u v s c = 0 ∧
      squareFieldStepanovFirstRestriction K S L u v c ≠ 0 := by
  let s := Fintype.card K
  let ell := stepanovEll s
  let m := stepanovM g s
  have hlarge' : (g + 1) * (g + 2) ≤ s := hlarge
  have hs : 0 < s := Fintype.card_pos
  have hglt : g < s := by nlinarith
  have hgell : g ≤ ell := by
    simp only [ell, stepanovEll]
    omega
  have hgm : g ≤ m := by
    simp only [m, stepanovM]
    omega
  have helllt : ell < s := stepanovEll_lt hlarge'
  have hstrict : ∀ N, g ≤ N →
      N - g ≤
        (strictFiltrationLevels
          (fun r => finiteExtensionOnePointRiemannSpace S L P r) N).card := by
    intro N hgN
    apply le_card_onePointStrictLevels_of_finrank_lower
      S L P N (N - g) hconstants
    have hN := hriemann N
    rw [hdegree]
    omega
  obtain ⟨u, du, huMem, huNe, huOrder, hduInjective,
      hduLe, huLI⟩ :=
    exists_onePointSectionsWithConstant_of_le_card_strictLevels
      S L P ell (ell - g) (hstrict ell hgell)
  obtain ⟨v, dv, hvMem, hvNe, hvOrder, hdvInjective,
      hdvLe, hvLI⟩ :=
    exists_onePointSectionsWithConstant_of_le_card_strictLevels
      S L P m (m - g) (hstrict m hgm)
  have hgridLI : LinearIndependent S
      (fun ij : Option (Fin (ell - g)) × Option (Fin (m - g)) =>
        u ij.1 * (v ij.2) ^ s) := by
    exact onePointStepanovGrid_linearIndependent S L P u v du dv s
      huNe hvNe huOrder hvOrder hduInjective hdvInjective
      (fun i => (hduLe i).trans_lt helllt)
  have hupper : Module.finrank S
      (finiteExtensionOnePointRiemannSpace S L P (s * ell + m)) ≤
        s * ell + m + 1 := by
    have h := finiteExtensionOnePointRiemannSpace_finrank_upper
      S L P hconstants (s * ell + m)
    rw [hdegree] at h
    simpa using h
  have hellCard : ell - g + 1 = ell + 1 - g := by omega
  have hmCard : m - g + 1 = m + 1 - g := by omega
  have hnumeric : s * ell + m + 1 <
      Fintype.card (Option (Fin (ell - g))) *
        Fintype.card (Option (Fin (m - g))) := by
    have hdim := stepanov_dimension_inequality hlarge'
    simpa only [Fintype.card_option, Fintype.card_fin, hellCard, hmCard,
      Nat.mul_comm s ell] using hdim
  obtain ⟨c, hc, hsecond, hfirst⟩ :=
    exists_squareFieldStepanovAuxiliary_of_target_finrank_upper
      K S L P u v ell m (s * ell + m + 1)
        huMem hvMem hgridLI hupper hnumeric
  refine ⟨u, du, v, dv, c, ?_, ?_, hc, hsecond, hfirst⟩
  · exact ⟨huMem, huNe, huOrder, hduInjective, hduLe, huLI⟩
  · exact ⟨hvMem, hvNe, hvOrder, hdvInjective, hdvLe, hvLI⟩

end

end BGS.HasseWeil
