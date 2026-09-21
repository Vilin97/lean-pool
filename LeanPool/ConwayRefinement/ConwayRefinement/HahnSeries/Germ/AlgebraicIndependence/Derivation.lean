/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.SuccessorLeibniz
import LeanPool.ConwayRefinement.ConwayRefinement.Order.Filter.Germ.LinearMap
import Mathlib.Tactic.Abel
import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# A derivation on the associated graded ring of the Cantor–Bendixson degree

The translated-truncation maps from degree `α + 1` to degree `α` assemble additively into a map
from the associated graded
ring to germs of functions with values in that ring. On zero and limit grades it vanishes; on
components of successor degree it is injective and lowers the degree by one. The homogeneous
product identities give the Leibniz rule for arbitrary elements of the direct sum.

Coefficients act here only through the additive structure. A coefficient-linear structure and
a polynomial presentation are separate constructions. The exponent group carries an ordered
uniform structure that is Cauchy complete and may lie in any universe.
-/

public noncomputable section
open Set Filter Topology
open scoped NatOrdinal
universe u v
namespace HahnSeries.Nonpositive
variable {G : Type u} {R : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [CommRing R] [NoZeroDivisors R] [CharZero R]

local notation "ν" => (cantorBendixsonDegreeValuation (G := G) (R := R))

private def successorDerivation (α : NatOrdinal.{u}) :
    (ν).Component (α + 1) →+ Filter.Germ (𝓝[<] (0 : G)) (ν).AssociatedGraded :=
  (Filter.Germ.mapLinear (DirectSum.of (ν).Component α).toIntLinearMap).toAddMonoidHom.comp
    (cantorBendixsonLayerDeriv α)

private theorem successorDerivation_componentMk (α : NatOrdinal.{u})
    (b : (ν).filtrationLE (α + 1)) :
    successorDerivation α ((ν).componentMk (α + 1) b) =
      ((fun γ ↦ DirectSum.of (ν).Component α
        (cantorBendixsonDerivAt α (b : Nonpositive G R) γ)) :
          Filter.Germ (𝓝[<] (0 : G)) (ν).AssociatedGraded) := by
  rw [successorDerivation, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    cantorBendixsonLayerDeriv_componentMk, Filter.Germ.mapLinear_coe]
  rfl

private theorem remove_one_add_one {α : NatOrdinal.{u}} (h : 0 < α.constantCoeff) :
    α.removeNat 1 + 1 = α := by
  simpa only [Nat.cast_one] using NatOrdinal.removeNat_add_natCast h

open Classical in
/-- The truncation map included in the graded ring, zero on zero and limit grades. -/
def cantorBendixsonHomogeneousDerivation (α : NatOrdinal.{u}) :
    (ν).Component α →+ Filter.Germ (𝓝[<] (0 : G)) (ν).AssociatedGraded :=
  if h : 0 < α.constantCoeff then
    (successorDerivation (α.removeNat 1)).comp
      (AddEquiv.cast (M := (ν).Component) (remove_one_add_one h).symm).toAddMonoidHom
  else 0

/-- The homogeneous map vanishes when the finite Cantor coefficient is zero. -/
theorem cantorBendixsonHomogeneousDerivation_limit (α : NatOrdinal.{u})
    (hα : α.constantCoeff = 0) :
    cantorBendixsonHomogeneousDerivation (G := G) (R := R) α = 0 := by
  rw [cantorBendixsonHomogeneousDerivation, dif_neg (by simp [hα])]

private theorem successorDerivation_cast {α β : NatOrdinal.{u}}
    (h : α = β) (e : β + 1 = α + 1) :
    (successorDerivation (G := G) (R := R) α).comp
      (AddEquiv.cast (M := (ν).Component) e).toAddMonoidHom = successorDerivation β := by
  subst β
  rfl

private theorem cantorBendixsonHomogeneousDerivation_succ (α : NatOrdinal.{u}) :
    cantorBendixsonHomogeneousDerivation (G := G) (R := R) (α + 1) =
      successorDerivation α := by
  have hc : 0 < (α + 1).constantCoeff := by
    have he := NatOrdinal.constantCoeff_add_natCast α 1
    simp only [Nat.cast_one] at he
    rw [he]
    exact Nat.zero_lt_succ _
  rw [cantorBendixsonHomogeneousDerivation, dif_pos hc]
  have he : (α + 1).removeNat 1 = α := by
    apply add_right_cancel (b := (1 : NatOrdinal))
    simpa only [Nat.cast_one] using NatOrdinal.removeNat_add_natCast hc
  exact successorDerivation_cast he _

/-- The additive extension of the homogeneous truncation maps to the associated graded ring. -/
def cantorBendixsonGradedDerivation :
    (ν).AssociatedGraded →+ Filter.Germ (𝓝[<] (0 : G)) (ν).AssociatedGraded :=
  DirectSum.toAddMonoid (cantorBendixsonHomogeneousDerivation (G := G) (R := R))

/-- On a homogeneous inclusion, the graded derivation is the homogeneous truncation map. -/
theorem cantorBendixsonGradedDerivation_of (α : NatOrdinal.{u}) (a : (ν).Component α) :
    cantorBendixsonGradedDerivation (DirectSum.of (ν).Component α a) =
      cantorBendixsonHomogeneousDerivation α a := by
  rw [cantorBendixsonGradedDerivation, DirectSum.toAddMonoid_of]

/-- A successor representative is sent to its translated truncation classes near zero. -/
@[blueprint "lem:cantor-bendixson-derivation-successor-formula"
  (phase := "Algebraic independence in graded rings")
  (title := "The successor formula for the Cantor--Bendixson derivation")
  (statement := /--
    Let $\nu$ be the Cantor--Bendixson degree on
    $R((G^{\leq0}))$, and let $\partial_{\mathrm{CB}}$ be the additive map
    from $\operatorname{gr}_\nu$ to functions
    $G\to\operatorname{gr}_\nu$ modulo equality on a left neighbourhood of
    $0$.  If $\nu(b)\leq\alpha+1$, then
    \[
      \partial_{\mathrm{CB}}\bigl(\operatorname{in}_{\alpha+1}(b)\bigr)
      =
      \left[\gamma\longmapsto
        \operatorname{in}_{\alpha}\bigl(b^{\mid\gamma}\bigr)\right]_{\gamma\to0^-},
    \]
    where $b^{\mid\gamma}$ is the translated truncation of $b$ at $\gamma$.
  -/)
  (proof := /--
    By \ref{thm:cantor-bendixson-value-multiplicative}, the
    Cantor--Bendixson degree defines the multiplicative filtration and
    associated graded ring used here.  On the component of degree
    $\alpha+1$, the map
    $\partial_{\mathrm{CB}}$ is defined by taking the degree-$\alpha$ class
    of each translated truncation.  Including those classes in the associated
    graded ring gives the displayed equality.
  -/)]
theorem cantorBendixsonGradedDerivation_homogeneousMk_succ {δ : NatOrdinal.{u}}
    (α : NatOrdinal.{u}) (hδ : δ = α + 1) (b : (ν).filtrationLE δ) :
    cantorBendixsonGradedDerivation ((ν).homogeneousMk δ b) =
      ((fun γ ↦ DirectSum.of (ν).Component α
        (cantorBendixsonDerivAt α (b : Nonpositive G R) γ)) :
          Filter.Germ (𝓝[<] (0 : G)) (ν).AssociatedGraded) := by
  subst δ
  rw [(ν).homogeneousMk_apply, cantorBendixsonGradedDerivation_of,
    cantorBendixsonHomogeneousDerivation_succ, successorDerivation_componentMk]

/-- Zero and limit homogeneous representatives have zero derivative. -/
theorem cantorBendixsonGradedDerivation_homogeneousMk_limit (α : NatOrdinal.{u})
    (hα : α.constantCoeff = 0) (b : (ν).filtrationLE α) :
    cantorBendixsonGradedDerivation ((ν).homogeneousMk α b) = 0 := by
  rw [(ν).homogeneousMk_apply, cantorBendixsonGradedDerivation_of,
    cantorBendixsonHomogeneousDerivation_limit _ hα, AddMonoidHom.zero_apply]

/-- The Leibniz rule holds on every pair of homogeneous representatives. -/
theorem cantorBendixsonGradedDerivation_mul_homogeneous (α β : NatOrdinal.{u})
    (b : (ν).filtrationLE α) (c : (ν).filtrationLE β) :
    cantorBendixsonGradedDerivation ((ν).homogeneousMk α b * (ν).homogeneousMk β c) =
      cantorBendixsonGradedDerivation ((ν).homogeneousMk α b) *
        ((ν).homogeneousMk β c : Filter.Germ (𝓝[<] (0 : G)) (ν).AssociatedGraded) +
      ((ν).homogeneousMk α b : Filter.Germ (𝓝[<] (0 : G)) (ν).AssociatedGraded) *
        cantorBendixsonGradedDerivation ((ν).homogeneousMk β c) := by
  let LeibnizAt : (ν).AssociatedGraded → (ν).AssociatedGraded → Prop := fun x y ↦
    cantorBendixsonGradedDerivation (x * y) =
      cantorBendixsonGradedDerivation x *
          (y : Filter.Germ (𝓝[<] (0 : G)) (ν).AssociatedGraded) +
        (x : Filter.Germ (𝓝[<] (0 : G)) (ν).AssociatedGraded) *
          cantorBendixsonGradedDerivation y
  change LeibnizAt ((ν).homogeneousMk α b) ((ν).homogeneousMk β c)
  have succ_succ (α β : NatOrdinal.{u})
      (b : (ν).filtrationLE (α + 1)) (c : (ν).filtrationLE (β + 1)) :
      LeibnizAt ((ν).homogeneousMk (α + 1) b) ((ν).homogeneousMk (β + 1) c) := by
    dsimp only [LeibnizAt]
    rw [(ν).homogeneousMk_mul,
      cantorBendixsonGradedDerivation_homogeneousMk_succ (α + β + 1) (by ac_rfl),
      cantorBendixsonGradedDerivation_homogeneousMk_succ α rfl,
      cantorBendixsonGradedDerivation_homogeneousMk_succ β rfl]
    simp only [(ν).coe_mulFiltrationLE]
    exact Filter.EventuallyEq.germ_eq (eventually_homogeneousDerivAt_mul_succ α β b c)
  have succ_limit (α β : NatOrdinal.{u}) (hβ : β.constantCoeff = 0)
      (b : (ν).filtrationLE (α + 1)) (c : (ν).filtrationLE β) :
      LeibnizAt ((ν).homogeneousMk (α + 1) b) ((ν).homogeneousMk β c) := by
    dsimp only [LeibnizAt]
    rw [(ν).homogeneousMk_mul,
      cantorBendixsonGradedDerivation_homogeneousMk_succ (α + β) (by ac_rfl),
      cantorBendixsonGradedDerivation_homogeneousMk_succ α rfl,
      cantorBendixsonGradedDerivation_homogeneousMk_limit β hβ, mul_zero, add_zero]
    simp only [(ν).coe_mulFiltrationLE]
    exact Filter.EventuallyEq.germ_eq (eventually_homogeneousDerivAt_mul_limit α β hβ b c)
  have succ (α β : NatOrdinal.{u})
      (b : (ν).filtrationLE (α + 1)) (c : (ν).filtrationLE β) :
      LeibnizAt ((ν).homogeneousMk (α + 1) b) ((ν).homogeneousMk β c) := by
    by_cases hβ : β.constantCoeff = 0
    · exact succ_limit α β hβ b c
    · obtain ⟨β', rfl⟩ : ∃ β', β = β' + 1 :=
        ⟨β.removeNat 1, (remove_one_add_one (Nat.pos_of_ne_zero hβ)).symm⟩
      exact succ_succ α β' b c
  dsimp only [LeibnizAt]
  by_cases hα : α.constantCoeff = 0
  · by_cases hβ : β.constantCoeff = 0
    · have hs : (α + β).constantCoeff = 0 := by
        rw [NatOrdinal.constantCoeff_add, hα, hβ, zero_add]
      rw [(ν).homogeneousMk_mul, cantorBendixsonGradedDerivation_homogeneousMk_limit _ hs,
        cantorBendixsonGradedDerivation_homogeneousMk_limit _ hα,
        cantorBendixsonGradedDerivation_homogeneousMk_limit _ hβ,
        zero_mul, mul_zero, add_zero]
    · obtain ⟨β', rfl⟩ : ∃ β', β = β' + 1 :=
        ⟨β.removeNat 1, (remove_one_add_one (Nat.pos_of_ne_zero hβ)).symm⟩
      have h := succ β' α c b
      rw [mul_comm ((ν).homogeneousMk α b) ((ν).homogeneousMk (β' + 1) c), h]
      rw [add_comm]
      congr 1 <;> exact mul_comm _ _
  · obtain ⟨α', rfl⟩ : ∃ α', α = α' + 1 :=
      ⟨α.removeNat 1, (remove_one_add_one (Nat.pos_of_ne_zero hα)).symm⟩
    exact succ α' β b c

private theorem const_add (x y : (ν).AssociatedGraded) :
    ((x + y : (ν).AssociatedGraded) : Filter.Germ (𝓝[<] (0 : G)) (ν).AssociatedGraded) =
      (x : Filter.Germ (𝓝[<] (0 : G)) (ν).AssociatedGraded) +
        (y : Filter.Germ (𝓝[<] (0 : G)) (ν).AssociatedGraded) := rfl

private theorem const_zero :
    ((0 : (ν).AssociatedGraded) : Filter.Germ (𝓝[<] (0 : G)) (ν).AssociatedGraded) = 0 := rfl

/-- The graded truncation map satisfies the Leibniz rule, using constant function germs. -/
@[blueprint "lem:cantor-bendixson-derivation-leibniz"
  (phase := "Algebraic independence in graded rings")
  (title := "The Leibniz rule for the Cantor--Bendixson derivation")
  (statement := /--
    For all $x,y\in\operatorname{gr}_\nu$,
    \[
      \partial_{\mathrm{CB}}(xy)
      =\partial_{\mathrm{CB}}(x)y+x\partial_{\mathrm{CB}}(y),
    \]
    where elements of $\operatorname{gr}_\nu$ on the right are regarded as
    constant functions near $0$.
  -/)
  (proof := /--
    Decompose $x$ and $y$ into homogeneous components.  On successor
    components, \ref{lem:cantor-bendixson-derivation-successor-formula}
    turns the identity into the translated-truncation product formula.  The
    derivative vanishes on components whose constant Cantor coefficient is
    zero.  Additivity then gives the formula for arbitrary $x$ and $y$.
  -/)]
theorem cantorBendixsonGradedDerivation_mul (x y : (ν).AssociatedGraded) :
    cantorBendixsonGradedDerivation (x * y) =
      cantorBendixsonGradedDerivation x *
          (y : Filter.Germ (𝓝[<] (0 : G)) (ν).AssociatedGraded) +
        (x : Filter.Germ (𝓝[<] (0 : G)) (ν).AssociatedGraded) *
          cantorBendixsonGradedDerivation y := by
  induction x using DirectSum.induction_on with
  | zero => simp [const_zero]
  | of α a =>
    induction y using DirectSum.induction_on with
    | zero => simp [const_zero]
    | of β b =>
      induction a using MaxAddDegree.componentInductionOn with
      | H a =>
        induction b using MaxAddDegree.componentInductionOn with
        | H b =>
          simpa only [(ν).homogeneousMk_apply] using
            cantorBendixsonGradedDerivation_mul_homogeneous α β a b
    | add y z hy hz =>
      rw [mul_add, map_add, hy, hz, map_add, const_add, mul_add, mul_add]
      abel
  | add x z hx hz =>
    rw [add_mul, map_add, hx, hz, map_add, const_add, add_mul, add_mul]
    abel

/-- Restriction of the graded derivation to each successor homogeneous component is injective. -/
theorem cantorBendixsonGradedDerivation_injective_on_successor (α : NatOrdinal.{u}) :
    Function.Injective (fun a : (ν).Component (α + 1) ↦
      cantorBendixsonGradedDerivation (DirectSum.of (ν).Component (α + 1) a)) := by
  intro a b hab
  simp only [cantorBendixsonGradedDerivation_of,
    cantorBendixsonHomogeneousDerivation_succ] at hab
  apply cantorBendixsonLayerDeriv_injective α
  apply Filter.Germ.mapLinear_injective (DirectSum.of (ν).Component α).toIntLinearMap
    (DirectSum.of_injective α)
  exact hab

end HahnSeries.Nonpositive
