/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.Cancellation
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Nonpositive
import LeanPool.ConwayRefinement.ConwayRefinement.Data.Multiset.SelectionComplexity
import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.NaturalPowerFactorization

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Multiplicativity of the Cantor–Bendixson value

For nonpositive Hahn series over a characteristic-zero domain, the value defined by the
Cantor--Bendixson rank at zero is multiplicative for natural ordinal multiplication. The
exponent group is a nontrivial ordered uniform additive group that is Cauchy complete.

The finite-multiset induction selects a factor with least principal factor, then greatest
value. Replacing one copy by its residual truncation and doubling the remaining factors
strictly decreases the distinct-factor complexity. Conditional cancellation therefore applies
without a remaining hypothesis on smaller products. Values zero and one are handled separately.

This proof uses Cantor–Bendixson ranks and the finite convolution theorem, not the real-exponent
order-value valuation. Completeness of the exponent group is retained.
-/

public noncomputable section
open Set Filter Topology
universe u v
namespace HahnSeries
variable {G : Type u} {R : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [OrderTopology G] [CommRing R]

private abbrev Factor := {b : ↥(nonpositiveSubring G R) //
  1 < (b : HahnSeries G R).cantorBendixsonValue}

private def factorOrdinal (b : Factor (G := G) (R := R)) : Ordinal.AdditivePrincipalAboveOne.{u} :=
  ⟨(b.1 : HahnSeries G R).cantorBendixsonValue, by
    have hb : 0 ∈ closure (b.1 : HahnSeries G R).support := by
      by_contra h
      have hpos := b.2
      rw [cantorBendixsonValue_of_notMem _ h] at hpos
      exact not_lt_of_ge (zero_le : (0 : Ordinal.{u}) ≤ 1) hpos
    rw [cantorBendixsonValue_of_mem _ hb]
    exact Ordinal.isAdditivelyPrincipal_omega0_opow _, b.2⟩

private def selection : Multiset.SelectionWeights.{u, max u v} (Factor (G := G) (R := R)) :=
  ⟨fun b ↦ (factorOrdinal b).principalFactor, fun b ↦ (b.1 : HahnSeries G R).cantorBendixsonValue⟩

private def eval (w : Multiset (Factor (G := G) (R := R))) :
    ↥(nonpositiveSubring G R) := (w.map (·.1)).prod

private def valueProd (w : Multiset (Factor (G := G) (R := R))) : NatOrdinal.{u} :=
  (w.map fun x ↦ NatOrdinal.of (x.1 : HahnSeries G R).cantorBendixsonValue).prod

private theorem eval_add (w w' : Multiset (Factor (G := G) (R := R))) :
    eval (w + w') = eval w * eval w' := by
  simp only [eval, Multiset.map_add, Multiset.prod_add]

private theorem eval_singleton (x : Factor (G := G) (R := R)) :
    eval {x} = x.1 := by
  simp only [eval, Multiset.map_singleton, Multiset.prod_singleton]

private theorem valueProd_singleton (x : Factor (G := G) (R := R)) :
    valueProd {x} = NatOrdinal.of (x.1 : HahnSeries G R).cantorBendixsonValue := by
  simp only [valueProd, Multiset.map_singleton, Multiset.prod_singleton]

private theorem eval_replicate (n : ℕ) (x : Factor (G := G) (R := R)) :
    eval (Multiset.replicate n x) = x.1 ^ n := by
  simp only [eval, Multiset.map_replicate, Multiset.prod_replicate]

private theorem valueProd_add (w w' : Multiset (Factor (G := G) (R := R))) :
    valueProd (w + w') = valueProd w * valueProd w' := by
  simp only [valueProd, Multiset.map_add, Multiset.prod_add]

private theorem valueProd_replicate (n : ℕ) (x : Factor (G := G) (R := R)) :
    valueProd (Multiset.replicate n x) =
      NatOrdinal.of (x.1 : HahnSeries G R).cantorBendixsonValue ^ n := by
  simp only [valueProd, Multiset.map_replicate, Multiset.prod_replicate]

private theorem one_le_valueProd (w : Multiset (Factor (G := G) (R := R))) :
    1 ≤ valueProd w := by
  induction w using Multiset.induction with
  | empty => simp [valueProd]
  | cons a s ih =>
    rw [valueProd, Multiset.map_cons, Multiset.prod_cons, ← valueProd]
    simpa only [NatOrdinal.of_one, one_mul] using mul_le_mul'
      (NatOrdinal.of.le_iff_le.mpr a.2.le) ih

private theorem one_lt_valueProd {w : Multiset (Factor (G := G) (R := R))} (hw : w ≠ 0) :
    1 < valueProd w := by
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hw
  obtain ⟨s, rfl⟩ := Multiset.exists_cons_of_mem ha
  rw [valueProd, Multiset.map_cons, Multiset.prod_cons, ← valueProd]
  calc (1 : NatOrdinal.{u}) < NatOrdinal.of (a.1 : HahnSeries G R).cantorBendixsonValue :=
        a.2
    _ = NatOrdinal.of (a.1 : HahnSeries G R).cantorBendixsonValue * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul' le_rfl (one_le_valueProd s)

private theorem eval_zero : eval (0 : Multiset (Factor (G := G) (R := R))) = 1 := by
  simp only [eval, Multiset.map_zero, Multiset.prod_zero]

private theorem valueProd_zero : valueProd (0 : Multiset (Factor (G := G) (R := R))) = 1 := by
  simp only [valueProd, Multiset.map_zero, Multiset.prod_zero]

private def translated (b : ↥(nonpositiveSubring G R)) (γ : G) :
    ↥(nonpositiveSubring G R) :=
  ⟨translate (-γ) (truncLE γ (b : HahnSeries G R)), support_translated_truncLE _ _⟩

local notation "V" => (fun b : ↥(nonpositiveSubring G R) ↦
  NatOrdinal.of (cantorBendixsonValue (b : HahnSeries G R)))

variable [IsUniformAddGroup G] [Nontrivial G] [CompleteSpace G]
  [NoZeroDivisors R] [CharZero R]

omit [IsUniformAddGroup G] [Nontrivial G] [CompleteSpace G] [NoZeroDivisors R] in
private theorem value_one : V 1 = 1 := by
  apply congrArg NatOrdinal.of
  exact cantorBendixsonValue_of_finite_of_coeff_ne_zero (1 : HahnSeries G R)
    (by rw [support_one]; exact finite_singleton _) (by simp)

private theorem value_eval (w : Multiset (Factor (G := G) (R := R))) :
    V (eval w) = valueProd w := by
  let s := selection (G := G) (R := R)
  suffices h : ∀ p : Multiset Ordinal.{u} × ℕ,
      ∀ (w : Multiset (Factor (G := G) (R := R))) (hw : w ≠ 0),
        s.complexity w hw = p → V (eval w) = valueProd w by
    rcases eq_or_ne w 0 with rfl | hw
    · rw [eval_zero, valueProd_zero, value_one]
    · exact h _ w hw rfl
  refine fun p ↦ Multiset.SelectionWeights.wellFounded_complexityLT.induction
    (C := fun q ↦ ∀ (w : Multiset (Factor (G := G) (R := R))) (hw : w ≠ 0),
      s.complexity w hw = q → V (eval w) = valueProd w) p ?_
  clear p
  intro p ih w hw hp
  classical
  have IH : ∀ w' : Multiset (Factor (G := G) (R := R)),
      (∀ hw' : w' ≠ 0, Multiset.SelectionWeights.ComplexityLT
        (s.complexity w' hw') (s.complexity w hw)) →
      V (eval w') = valueProd w' := by
    intro w' hlt
    rcases eq_or_ne w' 0 with rfl | hw'
    · rw [eval_zero, valueProd_zero, value_one]
    · exact ih (s.complexity w' hw') (hp ▸ hlt hw') w' hw' rfl
  set x := s.selected w hw with hx
  set r := s.unselected w hw with hrdef
  obtain ⟨m, hm⟩ : ∃ m, s.selectedExponent w hw = m + 1 :=
    ⟨s.selectedExponent w hw - 1, by have := s.one_le_selectedExponent w hw; omega⟩
  have hdecomp : w = Multiset.replicate (m + 1) x + r := by
    rw [hrdef, hx, ← hm, s.replicate_selectedExponent_add_unselected]
  have heval : eval w = x.1 ^ (m + 1) * eval r := by
    conv_lhs => rw [hdecomp]
    rw [eval_add, eval_replicate]
  have hvp : valueProd w = V x.1 ^ (m + 1) * valueProd r := by
    conv_lhs => rw [hdecomp]
    rw [valueProd_add, valueProd_replicate]
  have hr : V (eval r) = valueProd r :=
    IH r fun hr0 ↦ s.complexityLT_unselected hw hr0
  have hIHred : ∀ t : Multiset (Factor (G := G) (R := R)),
      (∀ u ∈ t, V u.1 < V x.1) →
      (∀ u ∈ t, (factorOrdinal x).principalFactor ≤ (factorOrdinal u).principalFactor) →
      V (eval t * x.1 ^ m * (eval r * eval r)) =
        valueProd t * V x.1 ^ m * (valueProd r * valueProd r) := by
    intro t ht htp
    have hred := IH (s.reduced w hw t) fun hne ↦
      s.complexityLT_reduced w hw t ht htp hne
    rw [s.reduced_eq, hm, Nat.add_sub_cancel] at hred
    simpa only [eval_add, eval_replicate, valueProd_add, valueProd_replicate] using hred
  have hkey : ∀ᶠ γ in 𝓝[<] (0 : G),
      V (translated x.1 γ) = NatOrdinal.of (factorOrdinal x).residualFactor →
      V (translated x.1 γ * x.1 ^ m * (eval r * eval r)) =
        V x.1 ^ m * V (translated x.1 γ) * valueProd r * valueProd r := by
    have hcut := ((x.1 : HahnSeries G R).eventually_value_translated_truncLE_lt
      (ne_of_gt (zero_lt_one.trans x.2))).filter_mono
        (nhdsWithin_le_nhds (s := Iio (0 : G)))
    filter_upwards [hcut, self_mem_nhdsWithin] with γ hγ hneg he
    have hsmall : V (translated x.1 γ) < V x.1 := hγ (ne_of_lt hneg)
    by_cases hg1 : 1 < V (translated x.1 γ)
    · let z : Factor (G := G) (R := R) := ⟨translated x.1 γ, hg1⟩
      have hpri : (factorOrdinal x).principalFactor ≤ (factorOrdinal z).principalFactor :=
        (factorOrdinal x).principalFactor_le_principalFactor_of_eq_residualFactor
          (factorOrdinal z) (NatOrdinal.of.injective he)
      have h := hIHred {z}
        (fun u hu ↦ by rw [Multiset.mem_singleton.mp hu]; exact hsmall)
        (fun u hu ↦ by rw [Multiset.mem_singleton.mp hu]; exact hpri)
      rw [eval_singleton, valueProd_singleton] at h
      change V (translated x.1 γ * x.1 ^ m * (eval r * eval r)) = _ at h
      dsimp only at h
      rw [h]
      ring
    · have hone : V (translated x.1 γ) = 1 := by
        have hne : V (translated x.1 γ) ≠ 0 := by
          dsimp only
          rw [he]
          exact (factorOrdinal x).residualFactor_isAdditivelyPrincipal.ne_zero
        exact le_antisymm (not_lt.mp hg1) (Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr hne))
      have h := hIHred 0 (by simp) (by simp)
      rw [eval_zero, valueProd_zero, one_mul, one_mul] at h
      have hmul : V (translated x.1 γ * (x.1 ^ m * (eval r * eval r))) =
          V (x.1 ^ m * (eval r * eval r)) :=
        congrArg NatOrdinal.of (cantorBendixsonValue_mul_of_left_eq_one _ _
          (translated x.1 γ).property (x.1 ^ m * (eval r * eval r)).property
          (NatOrdinal.of.injective hone))
      dsimp only at hmul h hone
      rw [mul_assoc, hmul, h, hone]
      ring
  rcases eq_or_ne r 0 with hr0 | hr0
  · rw [heval, hvp, hr0, eval_zero, valueProd_zero, mul_one, mul_one]
    apply cantorBendixsonValue_pow_eq_of_eventually (x.1 : HahnSeries G R) x.1.property
      (factorOrdinal x) rfl m
    filter_upwards [hkey] with γ hγ he
    have h := hγ he
    change V (translated x.1 γ) = _ at he
    dsimp only at he
    rw [he] at h
    simpa only [hr0, eval_zero, valueProd_zero, mul_one, Subring.coe_mul,
      Subring.coe_pow, translated, factorOrdinal] using h
  · have hc1 : 1 < V (eval r) := hr ▸ one_lt_valueProd hr0
    let c : Factor (G := G) (R := R) := ⟨eval r, hc1⟩
    have hp' : (factorOrdinal x).principalFactor ≤ (factorOrdinal c).principalFactor := by
      apply (factorOrdinal x).principalFactor_le_of_naturalProd (factorOrdinal c)
        (r.map factorOrdinal)
      · intro y hy
        obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hy
        exact (s.isSelected_selected w hw).min_priority z (s.mem_unselected.mp hz).1
      · simpa only [Multiset.map_map, Function.comp_def, valueProd, factorOrdinal] using hr
    have hev : ∀ᶠ γ in 𝓝[<] (0 : G),
        V (translated x.1 γ) = NatOrdinal.of (factorOrdinal x).residualFactor →
        V (translated x.1 γ * (x.1 ^ m * c.1 ^ 2)) =
          V x.1 ^ m * NatOrdinal.of (factorOrdinal x).residualFactor * V c.1 * V c.1 := by
      filter_upwards [hkey] with γ hγ he
      have h := hγ he
      rw [he] at h
      dsimp only at hr
      simpa only [c, sq, mul_assoc, hr] using h
    have h := cantorBendixsonValue_pow_mul_eq_of_eventually
      (x.1 : HahnSeries G R) (c.1 : HahnSeries G R) x.1.property c.1.property
      (factorOrdinal x) (factorOrdinal c) rfl rfl hp' m hev
    rw [heval, hvp]
    exact h.trans (congrArg (V x.1 ^ (m + 1) * ·) hr)

/-- The Cantor–Bendixson value is multiplicative on nonpositive Hahn series over a
characteristic-zero domain with an ordered exponent group that is Cauchy complete. -/
@[blueprint "thm:cantor-bendixson-value-multiplicative"
  (phase := "Cantor–Bendixson ranks of supports")
  (title := "Multiplicativity of the Cantor--Bendixson value")
  (statement := /--
    Let $R$ be a characteristic-zero domain and let $G$ be a nontrivial
    ordered abelian group equipped with a compatible additive uniformity and
    its order topology.  Assume that $G$ is Cauchy complete.  For all
    $b,c\in R((G^{\le0}))$,
    \[
      V_{\mathrm{CB}}(bc)
        =V_{\mathrm{CB}}(b)\odot V_{\mathrm{CB}}(c),
    \]
    where $\odot$ is Hessenberg's natural product.
  -/)
  (proof := /--
    If either value is $0$, the product upper bound forces the product value
    to be $0$.  A factor of value $1$ is a nonzero scalar at exponent $0$
    plus a remainder of value $0$, so it preserves the other value.  For
    values greater than $1$, argue by well-founded induction on the finite
    multiset of factors.  Choose a factor for which the final multiplicatively
    principal factor is least, and among ties choose one of greatest value.
    At a cutoff where its
    translated truncation has the residual value, that truncation has smaller
    value, so the induction hypothesis computes every required local product.
    If no other factors remain, apply
    \ref{lem:cantor-bendixson-pure-power-cancellation}; otherwise combine the
    remaining factors and apply
    \ref{lem:cantor-bendixson-power-factor-cancellation}.  In both cases the
    result is the natural product of the factor values, and the two-factor
    statement follows.
  -/)
  (highlight)]
theorem cantorBendixsonValue_mul (b c : HahnSeries G R)
    (hb : b.support ⊆ Iic 0) (hc : c.support ⊆ Iic 0) :
    NatOrdinal.of (b * c).cantorBendixsonValue =
      NatOrdinal.of b.cantorBendixsonValue * NatOrdinal.of c.cantorBendixsonValue := by
  rcases eq_or_ne b.cantorBendixsonValue 0 with hb0 | hb0
  · rw [cantorBendixsonValue_mul_eq_zero_of_left b c hb hc hb0, hb0,
      NatOrdinal.of_zero, zero_mul]
  rcases eq_or_ne c.cantorBendixsonValue 0 with hc0 | hc0
  · rw [mul_comm b c, cantorBendixsonValue_mul_eq_zero_of_left c b hc hb hc0, hc0,
      NatOrdinal.of_zero, mul_zero]
  rcases eq_or_lt_of_le (Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr hb0)) with hb1 | hb1
  · rw [cantorBendixsonValue_mul_of_left_eq_one b c hb hc hb1.symm, ← hb1,
      NatOrdinal.of_one, one_mul]
  rcases eq_or_lt_of_le (Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr hc0)) with hc1 | hc1
  · rw [mul_comm b c, cantorBendixsonValue_mul_of_left_eq_one c b hc hb hc1.symm, ← hc1,
      NatOrdinal.of_one, mul_one]
  have h := value_eval ({⟨⟨b, hb⟩, hb1⟩, ⟨⟨c, hc⟩, hc1⟩} :
    Multiset (Factor (G := G) (R := R)))
  simpa [eval, valueProd] using h

end HahnSeries
