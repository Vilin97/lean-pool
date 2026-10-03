/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.Degree
public import LeanPool.BooleanMultiplication.N4.TwoForm
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# Algebraic quadratic lower-bound core

The classical quadratic lower bound is developed here without importing it as
an assumption.  The key certificate is a two-bit linear coloring of the
rank-at-most-two Hankel graph.  Every nonzero word in the explicit rank-two
table has nonzero color, so a family with pairwise rank-two differences has at
most four members.  This replaces a search over quadratic circuits by a small
linear-algebra certificate.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- The two-bit certificate `(c₀+c₂+c₅, c₁+c₃+c₆)`. -/
def rankTwoColor : TargetCoeff →ₗ[F₂] (Fin 2 → F₂) where
  toFun c := ![c 0 + c 2 + c 5, c 1 + c 3 + c 6]
  map_add' c d := by
    ext i
    fin_cases i <;> simp
    all_goals ring
  map_smul' a c := by
    ext i
    fin_cases i <;> simp
    all_goals ring

/-- The color kernel contains no nonzero rank-at-most-two Hankel word. -/
theorem rankTwoColor_eq_zero_iff {c : TargetCoeff}
    (hc : HankelRankLETwo c) : rankTwoColor c = 0 ↔ c = 0 := by
  constructor
  · intro hcolor
    rcases (rankTwo_target_classification c).mp hc with ⟨i, rfl⟩
    fin_cases i <;> simp [rankTwoColor, rankTwoWord] at hcolor ⊢ <;>
      norm_num at hcolor ⊢ <;>
      simp [N3Certificate.two_eq_zero_f2, N3Certificate.three_eq_one_f2] at hcolor
  · rintro rfl
    simp

/-- A family of distinct target words whose pairwise differences have Hankel
rank at most two has cardinality at most four. -/
theorem rankTwo_clique_card_le_four {ι : Type*} [Fintype ι]
    (c : ι → TargetCoeff) (hinj : Function.Injective c)
    (hpair : ∀ i j, HankelRankLETwo (c i + c j)) :
    Fintype.card ι ≤ 4 := by
  have hcolorInj : Function.Injective (fun i => rankTwoColor (c i)) := by
    intro i j hij
    have hzero : rankTwoColor (c i + c j) = 0 := by
      rw [map_add]
      change rankTwoColor (c i) = rankTwoColor (c j) at hij
      rw [hij]
      ext k
      exact CharTwo.add_self_eq_zero _
    have hsum : c i + c j = 0 :=
      (rankTwoColor_eq_zero_iff (hpair i j)).mp hzero
    have hcij : c i = c j := by
      funext k
      have hk := congrFun hsum k
      simp only [Pi.add_apply, Pi.zero_apply] at hk
      rw [← CharTwo.sub_eq_add] at hk
      exact sub_eq_zero.mp hk
    exact hinj hcij
  have hcard := Fintype.card_le_of_injective
    (f := fun i => rankTwoColor (c i)) hcolorInj
  norm_num at hcard ⊢
  exact hcard

/-- A target Hankel matrix is an outer product. -/
def IsOuterTarget (c : TargetCoeff) : Prop :=
  ∃ a b : Fin 4 → F₂,
    ∀ i j : Fin 4, c ⟨i.val + j.val, by omega⟩ = a i * b j

theorem decomposableTarget_outer {c : TargetCoeff}
    (hc : IsDecomposableTarget c) : IsOuterTarget c := by
  rcases hc with ⟨u, v, hAA, _hBB, hcross⟩
  have hApart : ∀ i j : Fin 4,
      aPart u i * aPart v j + aPart u j * aPart v i = 0 := by
    intro i j
    simpa [aPart, vectorWedge] using hAA i j
  rcases dependent_of_vectorWedge_zero (aPart u) (aPart v) hApart with hu | hv | huv
  · refine ⟨aPart v, bPart u, ?_⟩
    intro i j
    rw [hcross i j]
    have hui : u (aCoord i) = 0 := congrFun hu i
    simp [crossPart, vectorWedge, aPart, bPart, hui]
    ring
  · refine ⟨aPart u, bPart v, ?_⟩
    intro i j
    rw [hcross i j]
    have hvi : v (aCoord i) = 0 := congrFun hv i
    simp [crossPart, vectorWedge, aPart, bPart, hvi]
  · refine ⟨aPart u, fun j => bPart v j + bPart u j, ?_⟩
    intro i j
    rw [hcross i j]
    have hui : u (aCoord i) = v (aCoord i) := congrFun huv i
    simp only [crossPart, vectorWedge, aPart, bPart, hui]
    ring

/-- A sum of two outer-product target matrices has Hankel rank at most two. -/
theorem outer_sum_rankTwo {c d : TargetCoeff}
    (hc : IsOuterTarget c) (hd : IsOuterTarget d) :
    HankelRankLETwo (c + d) := by
  rcases hc with ⟨a, b, hc⟩
  rcases hd with ⟨x, y, hd⟩
  intro dropRow dropCol
  simp only [hankelMinorThree, detThree, hankelMatrix, Pi.add_apply]
  simp_rw [hc, hd]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, N3Certificate.six_eq_zero_f2]

theorem sum_decomposable_rankTwo {c d : TargetCoeff}
    (hc : IsDecomposableTarget c) (hd : IsDecomposableTarget d) :
    HankelRankLETwo (c + d) :=
  outer_sum_rankTwo (decomposableTarget_outer hc) (decomposableTarget_outer hd)

/-! ## Sums of two arbitrary decomposable forms -/

/-- Four-dimensional vectors over the two-element field. -/
abbrev Vec4 := Fin 4 → F₂
/-- Two-index coordinate arrays in four dimensions. -/
abbrev Two4 := Fin 4 → Fin 4 → F₂

/-- The exterior product of two four-dimensional vectors. -/
def vecWedge4 (u v : Vec4) : Two4 :=
  fun i j => u i * v j + u j * v i

/-- The exterior product of three four-dimensional vectors. -/
def tripleWedge (u v x : Vec4) : Fin 4 → Fin 4 → Fin 4 → F₂ :=
  fun i j k =>
    x i * (u j * v k + u k * v j) +
    x j * (u i * v k + u k * v i) +
    x k * (u i * v j + u j * v i)

/-- The exterior product of the three vectors vanishes. -/
def TripleWedgeZero (u v x : Vec4) : Prop := tripleWedge u v x = 0

instance (u v x : Vec4) : Decidable (TripleWedgeZero u v x) :=
  inferInstanceAs (Decidable (tripleWedge u v x = 0))

/-- If `u ∧ v` is nonzero and `x ∧ u ∧ v = 0`, then `x` lies in the plane
spanned by `u,v`.  The proof chooses a nonzero `2 × 2` minor and solves the
resulting two equations, so it works symbolically rather than by enumeration. -/
theorem tripleWedgeZero_mem_span (u v x : Vec4)
    (huv : vecWedge4 u v ≠ 0) (hx : TripleWedgeZero u v x) :
    ∃ a b : F₂, x = a • u + b • v := by
  have hex : ∃ i j, vecWedge4 u v i j ≠ 0 := by
    by_contra hn
    push Not at hn
    apply huv
    funext i j
    exact hn i j
  rcases hex with ⟨i, j, hij⟩
  have hij1 : vecWedge4 u v i j = 1 :=
    (f2_eq_zero_or_one (vecWedge4 u v i j)).resolve_left hij
  refine ⟨x i * v j + x j * v i, u i * x j + u j * x i, ?_⟩
  funext k
  have hk := congrFun (congrFun (congrFun hx i) j) k
  change x i * (u j * v k + u k * v j) +
      x j * (u i * v k + u k * v i) +
      x k * (u i * v j + u j * v i) = 0 at hk
  have hij1' : u i * v j + u j * v i = 1 := by
    simpa [vecWedge4] using hij1
  rw [hij1', mul_one] at hk
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hs :
      (x i * (u j * v k + u k * v j) +
        x j * (u i * v k + u k * v i)) - x k = 0 := by
    simpa only [CharTwo.sub_eq_add] using hk
  have hk' : x k = x i * (u j * v k + u k * v j) +
      x j * (u i * v k + u k * v i) := (sub_eq_zero.mp hs).symm
  rw [hk']
  ring

theorem vecWedgeTwo_repeat (x y : Vec4) :
    (fun i j k =>
      x i * vecWedge4 x y j k + x j * vecWedge4 x y i k +
        x k * vecWedge4 x y i j) = 0 := by
  funext i j k
  simp [vecWedge4]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2]

/-- The mixed input matrix is a single outer product. -/
def IsOuterCross (u v : LinearForm) : Prop :=
  ∃ a b : Fin 4 → F₂, ∀ i j, crossPart u v i j = a i * b j

theorem outerCross_of_A_dependent {u v : LinearForm}
    (h : vecWedge4 (aPart u) (aPart v) = 0) : IsOuterCross u v := by
  have hp : ∀ i j, aPart u i * aPart v j + aPart u j * aPart v i = 0 := by
    intro i j
    simpa [vecWedge4] using congrFun (congrFun h i) j
  rcases dependent_of_vectorWedge_zero (aPart u) (aPart v) hp with hu | hv | huv
  · refine ⟨aPart v, bPart u, ?_⟩
    intro i j
    have hui : u (aCoord i) = 0 := congrFun hu i
    simp [crossPart, vectorWedge, aPart, bPart, hui]
    ring
  · refine ⟨aPart u, bPart v, ?_⟩
    intro i j
    have hvi : v (aCoord i) = 0 := congrFun hv i
    simp [crossPart, vectorWedge, aPart, bPart, hvi]
  · refine ⟨aPart u, fun j => bPart v j + bPart u j, ?_⟩
    intro i j
    have hui : u (aCoord i) = v (aCoord i) := congrFun huv i
    simp only [crossPart, vectorWedge, aPart, bPart, hui]
    ring

/-- The target Hankel matrix is a sum of two outer products. -/
def IsTwoOuterTarget (c : TargetCoeff) : Prop :=
  ∃ a b x y : Fin 4 → F₂,
    ∀ i j, c ⟨i.val + j.val, by omega⟩ = a i * b j + x i * y j

theorem twoOuter_rankTwo {c : TargetCoeff} (hc : IsTwoOuterTarget c) :
    HankelRankLETwo c := by
  rcases hc with ⟨a, b, x, y, hc⟩
  intro dropRow dropCol
  simp only [hankelMinorThree, detThree, hankelMatrix]
  simp_rw [hc]
  ring_nf
  simp [N3Certificate.two_eq_zero_f2, N3Certificate.six_eq_zero_f2]

/-- If a target two-form is the sum of two arbitrary decomposable two-forms,
then its Hankel rank is at most two. -/
theorem target_sum_two_decomposable_rankTwo {c : TargetCoeff}
    {u v x y : LinearForm}
    (h : targetTwo c = vectorWedge u v + vectorWedge x y) :
    HankelRankLETwo c := by
  have hAA : vecWedge4 (aPart u) (aPart v) =
      vecWedge4 (aPart x) (aPart y) := by
    funext i j
    have hij := congrFun (congrFun h (aCoord i)) (aCoord j)
    rw [targetTwo_sameA] at hij
    simp only [Pi.add_apply] at hij
    rw [← CharTwo.sub_eq_add] at hij
    have heq := sub_eq_zero.mp hij.symm
    simpa [vecWedge4, vectorWedge, aPart] using heq
  by_cases hz : vecWedge4 (aPart u) (aPart v) = 0
  · have hz' : vecWedge4 (aPart x) (aPart y) = 0 := hAA ▸ hz
    rcases outerCross_of_A_dependent hz with ⟨a, b, hab⟩
    rcases outerCross_of_A_dependent hz' with ⟨p, q, hpq⟩
    apply twoOuter_rankTwo
    exact ⟨a, b, p, q, by
      intro i j
      have hij := congrFun (congrFun h (aCoord i)) (bCoord j)
      rw [targetTwo_cross] at hij
      calc
        c ⟨i.val + j.val, by omega⟩ =
            crossPart u v i j + crossPart x y i j := by
              simpa [crossPart, vectorWedge] using hij
        _ = a i * b j + p i * q j := by rw [hab i j, hpq i j]⟩
  · have hxTriple : TripleWedgeZero (aPart u) (aPart v) (aPart x) := by
      funext i j k
      have hr := congrFun (congrFun (congrFun
        (vecWedgeTwo_repeat (aPart x) (aPart y)) i) j) k
      change aPart x i * vecWedge4 (aPart u) (aPart v) j k +
          aPart x j * vecWedge4 (aPart u) (aPart v) i k +
          aPart x k * vecWedge4 (aPart u) (aPart v) i j = 0
      rw [hAA]
      simpa using hr
    have hyTriple : TripleWedgeZero (aPart u) (aPart v) (aPart y) := by
      funext i j k
      have hr := congrFun (congrFun (congrFun
        (vecWedgeTwo_repeat (aPart y) (aPart x)) i) j) k
      change aPart y i * vecWedge4 (aPart u) (aPart v) j k +
          aPart y j * vecWedge4 (aPart u) (aPart v) i k +
          aPart y k * vecWedge4 (aPart u) (aPart v) i j = 0
      rw [hAA]
      simpa [vecWedge4, add_comm, mul_comm] using hr
    rcases tripleWedgeZero_mem_span (aPart u) (aPart v) (aPart x) hz hxTriple with
      ⟨α, β, hxspan⟩
    rcases tripleWedgeZero_mem_span (aPart u) (aPart v) (aPart y) hz hyTriple with
      ⟨γ, δ, hyspan⟩
    apply twoOuter_rankTwo
    refine ⟨aPart u,
      fun j => bPart v j + α * bPart y j + γ * bPart x j,
      aPart v,
      fun j => bPart u j + β * bPart y j + δ * bPart x j, ?_⟩
    intro i j
    have hij := congrFun (congrFun h (aCoord i)) (bCoord j)
    rw [targetTwo_cross] at hij
    have hxi : x (aCoord i) = α * u (aCoord i) + β * v (aCoord i) := by
      simpa [aPart] using congrFun hxspan i
    have hyi : y (aCoord i) = γ * u (aCoord i) + δ * v (aCoord i) := by
      simpa [aPart] using congrFun hyspan i
    simp only [Pi.add_apply, vectorWedge] at hij
    rw [hxi, hyi] at hij
    change c ⟨i.val + j.val, by omega⟩ =
      u (aCoord i) *
          (v (bCoord j) + α * y (bCoord j) + γ * x (bCoord j)) +
        v (aCoord i) *
          (u (bCoord j) + β * y (bCoord j) + δ * x (bCoord j))
    rw [hij]
    ring

/-! ## Eight decomposable forms cannot cover the target space -/

/-- The coefficient vectors for evaluations at zero, one, and infinity. -/
@[expose] def rationalPlaceCoeff : Fin 3 → TargetCoeff :=
  ![rZeroCoeff, rOneCoeff, rInfinityCoeff]

theorem rationalPlaceCoeff_injective : Function.Injective rationalPlaceCoeff := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp [rationalPlaceCoeff, rZeroCoeff, rOneCoeff, rInfinityCoeff] at h ⊢

theorem targetTwo_decomposableTarget {c : TargetCoeff}
    (h : IsDecomposableTwo (targetTwo c)) : IsDecomposableTarget c := by
  rcases h with ⟨u, v, huv⟩
  refine ⟨u, v, ?_, ?_, ?_⟩
  · intro i j
    rw [← huv, targetTwo_sameA]
  · intro i j
    rw [← huv, targetTwo_sameB]
  · intro i j
    calc
      c ⟨i.val + j.val, by omega⟩ = targetTwo c (aCoord i) (bCoord j) :=
        (targetTwo_cross c i j).symm
      _ = crossPart u v i j := by rw [huv]; rfl

theorem target_decomposable_family_card_le_three {ι : Type*} [Fintype ι]
    (c : ι → TargetCoeff) (hinj : Function.Injective c)
    (hne : ∀ i, c i ≠ 0)
    (hdec : ∀ i, IsDecomposableTwo (targetTwo (c i))) :
    Fintype.card ι ≤ 3 := by
  have hplace : ∀ i, ∃ θ : Fin 3, c i = rationalPlaceCoeff θ := by
    intro i
    rcases decomposableTarget_classification
        (targetTwo_decomposableTarget (hdec i)) (hne i) with h | h | h
    · exact ⟨0, by simpa [rationalPlaceCoeff] using h⟩
    · exact ⟨1, by simpa [rationalPlaceCoeff] using h⟩
    · exact ⟨2, by simpa [rationalPlaceCoeff] using h⟩
  let placeIndex : ι → Fin 3 := fun i => Classical.choose (hplace i)
  have hplaceIndex (i : ι) : c i = rationalPlaceCoeff (placeIndex i) :=
    Classical.choose_spec (hplace i)
  have hindexInj : Function.Injective placeIndex := by
    intro i j hij
    apply hinj
    rw [hplaceIndex i, hplaceIndex j, hij]
  simpa using Fintype.card_le_of_injective placeIndex hindexInj

theorem add_mem_of_codim_one {V : Type*} [AddCommGroup V] [Module F₂ V]
    [FiniteDimensional F₂ V] {T Q : Submodule F₂ V}
    (hTQ : T ≤ Q) (hT : Module.finrank F₂ T = 7)
    (hQ : Module.finrank F₂ Q = 8)
    {x y : V} (hxQ : x ∈ Q) (hyQ : y ∈ Q)
    (hxT : x ∉ T) (hyT : y ∉ T) : x + y ∈ T := by
  let S : Submodule F₂ Q := T.comap Q.subtype
  have hS : Module.finrank F₂ S = 7 := by
    have he := (Submodule.comapSubtypeEquivOfLe hTQ).finrank_eq
    simpa [S, hT] using he
  have hquot : Module.finrank F₂ (Q ⧸ S) = 1 := by
    have hledger := S.finrank_quotient_add_finrank
    rw [hS, hQ] at hledger
    omega
  let xQ : Q := ⟨x, hxQ⟩
  let yQ : Q := ⟨y, hyQ⟩
  let xbar : Q ⧸ S := Submodule.Quotient.mk xQ
  let ybar : Q ⧸ S := Submodule.Quotient.mk yQ
  have hxbar : xbar ≠ 0 := by
    intro hz
    have hm : xQ ∈ S := (Submodule.Quotient.mk_eq_zero S).mp hz
    exact hxT hm
  have hybar : ybar ≠ 0 := by
    intro hz
    have hm : yQ ∈ S := (Submodule.Quotient.mk_eq_zero S).mp hz
    exact hyT hm
  obtain ⟨a, ha⟩ :=
    (finrank_eq_one_iff_of_nonzero' xbar hxbar).mp hquot ybar
  have ha0 : a ≠ 0 := by
    intro haz
    apply hybar
    rw [← ha, haz, zero_smul]
  have ha1 : a = 1 := (f2_eq_zero_or_one a).resolve_left ha0
  have hxy : xbar = ybar := by simpa [ha1] using ha
  have hmQ : S.mkQ (xQ + yQ) = 0 := by
    rw [map_add]
    change xbar + ybar = 0
    rw [hxy]
    have h11 : (1 + 1 : F₂) = 0 := by
      change (2 : F₂) = 0
      exact N3Certificate.two_eq_zero_f2
    calc
      ybar + ybar = (1 + 1 : F₂) • ybar := by rw [add_smul, one_smul]
      _ = 0 := by rw [h11, zero_smul]
  have hm : xQ + yQ ∈ S :=
    (Submodule.Quotient.mk_eq_zero S).mp (by
      simpa [Submodule.mkQ_apply] using hmQ)
  exact hm

/-- The span of the three rational-place target two-forms. -/
@[expose] def rationalPlaceTwoSpace : Submodule F₂ TwoForm :=
  Submodule.span F₂ (Set.range (fun θ : Fin 3 => targetTwo (rationalPlaceCoeff θ)))

theorem rationalPlaceTwoSpace_finrank_le_three :
    Module.finrank F₂ rationalPlaceTwoSpace ≤ 3 := by
  exact (finrank_span_le_card
    (Set.range (fun θ : Fin 3 => targetTwo (rationalPlaceCoeff θ)))).trans (by
      rw [Set.toFinset_card]
      simpa using Fintype.card_range_le
        (fun θ : Fin 3 => targetTwo (rationalPlaceCoeff θ)))

theorem decomposable_mem_rationalPlaceTwoSpace {q : TwoForm}
    (hq : q ∈ targetTwoSpace) (hdec : IsDecomposableTwo q) :
    q ∈ rationalPlaceTwoSpace := by
  change q ∈ LinearMap.range targetTwoLinear at hq
  rcases hq with ⟨c, hc⟩
  change targetTwo c = q at hc
  subst q
  by_cases hzero : c = 0
  · subst c
    rw [show targetTwo (0 : TargetCoeff) = 0 from targetTwoLinear.map_zero]
    exact Submodule.zero_mem rationalPlaceTwoSpace
  · rcases decomposableTarget_classification
        (targetTwo_decomposableTarget hdec) hzero with h | h | h
    · exact Submodule.subset_span ⟨0, by simpa [rationalPlaceCoeff] using (congrArg targetTwo
      h).symm⟩
    · exact Submodule.subset_span ⟨1, by simpa [rationalPlaceCoeff] using (congrArg targetTwo
      h).symm⟩
    · exact Submodule.subset_span ⟨2, by simpa [rationalPlaceCoeff] using (congrArg targetTwo
      h).symm⟩

/-- The span of eight candidate two-form generators. -/
@[expose]
def decomposableTwoSpan (q : Fin 8 → TwoForm) : Submodule F₂ TwoForm :=
  Submodule.span F₂ (Set.range q)

/-- Eight decomposable alternating forms cannot span the seven-dimensional
Hankel target.  The proof splits by whether their span has dimension seven or
eight.  In codimension one, at most three forms lie in the target and at most
four lie outside it; the latter bound is the two-bit Hankel coloring. -/
theorem no_eight_decomposable_span (q : Fin 8 → TwoForm)
    (hdec : ∀ i, IsDecomposableTwo (q i)) :
    ¬ targetTwoSpace ≤ decomposableTwoSpan q := by
  classical
  intro hTQ
  have hQle : Module.finrank F₂ (decomposableTwoSpan q) ≤ 8 := by
    exact (finrank_span_le_card (Set.range q)).trans (by
      rw [Set.toFinset_card]
      simpa using Fintype.card_range_le q)
  have hQge : 7 ≤ Module.finrank F₂ (decomposableTwoSpan q) := by
    have hm := Submodule.finrank_mono hTQ
    simpa [targetTwoSpace_finrank] using hm
  have hcases : Module.finrank F₂ (decomposableTwoSpan q) = 7 ∨
      Module.finrank F₂ (decomposableTwoSpan q) = 8 := by omega
  rcases hcases with hQ7 | hQ8
  · have hEq : targetTwoSpace = decomposableTwoSpan q :=
      Submodule.eq_of_le_of_finrank_eq hTQ (by
        rw [targetTwoSpace_finrank, hQ7])
    have hQR : decomposableTwoSpan q ≤ rationalPlaceTwoSpace := by
      rw [decomposableTwoSpan, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      apply decomposable_mem_rationalPlaceTwoSpace
      · rw [hEq]
        exact Submodule.subset_span ⟨i, rfl⟩
      · exact hdec i
    have hdim := (Submodule.finrank_mono hQR).trans
      rationalPlaceTwoSpace_finrank_le_three
    omega
  · have hLI : LinearIndependent F₂ q := by
      rw [linearIndependent_iff_card_eq_finrank_span]
      change Fintype.card (Fin 8) =
        Module.finrank F₂ (decomposableTwoSpan q)
      simpa using hQ8.symm
    let Inside := {i : Fin 8 // q i ∈ targetTwoSpace}
    have hcoeffExists (i : Inside) : ∃ c : TargetCoeff, targetTwo c = q i := by
      have hi := i.property
      change q i ∈ LinearMap.range targetTwoLinear at hi
      rcases hi with ⟨c, hc⟩
      exact ⟨c, hc⟩
    let insideCoeff : Inside → TargetCoeff := fun i => Classical.choose (hcoeffExists i)
    have hinsideCoeff (i : Inside) : targetTwo (insideCoeff i) = q i :=
      Classical.choose_spec (hcoeffExists i)
    have hinsideInj : Function.Injective insideCoeff := by
      intro i j hij
      apply Subtype.ext
      apply hLI.injective
      rw [← hinsideCoeff i, ← hinsideCoeff j, hij]
    have hinsideNe (i : Inside) : insideCoeff i ≠ 0 := by
      intro hz
      have hq0 : q i = 0 := by
        rw [← hinsideCoeff i, hz]
        exact targetTwoLinear.map_zero
      exact (LinearIndependent.ne_zero i.val hLI) hq0
    have hinsideDec (i : Inside) :
        IsDecomposableTwo (targetTwo (insideCoeff i)) := by
      rw [hinsideCoeff i]
      exact hdec i
    have hInsideCard : Fintype.card Inside ≤ 3 :=
      target_decomposable_family_card_le_three insideCoeff hinsideInj
        hinsideNe hinsideDec
    let Outside := {i : Fin 8 // q i ∉ targetTwoSpace}
    have hOutsideCardEq : Fintype.card Outside = 8 - Fintype.card Inside := by
      simp [Inside, Outside]
    have hOutsidePos : 0 < Fintype.card Outside := by omega
    let : Nonempty Outside := Fintype.card_pos_iff.mp hOutsidePos
    let base : Outside := Classical.choice inferInstance
    have hqMem (i : Fin 8) : q i ∈ decomposableTwoSpan q :=
      Submodule.subset_span ⟨i, rfl⟩
    have hpairMem (i j : Outside) : q i + q j ∈ targetTwoSpace :=
      add_mem_of_codim_one hTQ targetTwoSpace_finrank hQ8
        (hqMem i) (hqMem j) i.property j.property
    have houtCoeffExists (i : Outside) :
        ∃ c : TargetCoeff, targetTwo c = q i + q base := by
      have hi := hpairMem i base
      change q i + q base ∈ LinearMap.range targetTwoLinear at hi
      rcases hi with ⟨c, hc⟩
      exact ⟨c, hc⟩
    let outsideCoeff : Outside → TargetCoeff :=
      fun i => Classical.choose (houtCoeffExists i)
    have houtsideCoeff (i : Outside) :
        targetTwo (outsideCoeff i) = q i + q base :=
      Classical.choose_spec (houtCoeffExists i)
    have houtsideInj : Function.Injective outsideCoeff := by
      intro i j hij
      apply Subtype.ext
      apply hLI.injective
      apply add_right_cancel (b := q base)
      rw [← houtsideCoeff i, ← houtsideCoeff j, hij]
    have houtsidePair (i j : Outside) :
        HankelRankLETwo (outsideCoeff i + outsideCoeff j) := by
      rcases hdec i with ⟨u, v, huv⟩
      rcases hdec j with ⟨x, y, hxy⟩
      apply target_sum_two_decomposable_rankTwo
        (u := u) (v := v) (x := x) (y := y)
      calc
        targetTwo (outsideCoeff i + outsideCoeff j) =
            targetTwo (outsideCoeff i) + targetTwo (outsideCoeff j) :=
          targetTwoLinear.map_add _ _
        _ = (q i + q base) + (q j + q base) := by
          rw [houtsideCoeff i, houtsideCoeff j]
        _ = q i + q j := by
          funext a b
          simp only [Pi.add_apply]
          ring_nf
          simp [N3Certificate.two_eq_zero_f2]
        _ = vectorWedge u v + vectorWedge x y := by rw [huv, hxy]
    have hOutsideCard : Fintype.card Outside ≤ 4 :=
      rankTwo_clique_card_le_four outsideCoeff houtsideInj houtsidePair
    omega

end

end N4
end UnrestrictedBooleanMul
