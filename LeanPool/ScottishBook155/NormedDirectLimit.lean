/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
import Mathlib.Algebra.Colimit.Module
import Mathlib.Analysis.Normed.Group.Seminorm
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Normed direct limits of isometric systems

Mathlib supplies the algebraic direct limit of modules.  For a directed system
whose transition maps are linear isometries, this file equips that algebraic
direct limit with the unique norm making every canonical map isometric.
-/

namespace ScottishBook155

universe u

namespace NormedDirectLimit

variable {ι : Type u} [LinearOrder ι] [Nonempty ι]
variable (G : ι → Type u)
variable [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace ℝ (G i)]
variable (f : ∀ i j : ι, i ≤ j → G i →ₗᵢ[ℝ] G j)
variable [DirectedSystem G (f · · ·)]


/-- The linear map underlying an isometric transition in the direct system. -/
abbrev linearMap (i j : ι) (h : i ≤ j) : G i →ₗ[ℝ] G j :=
  (f i j h).toLinearMap

local instance linearDirectedSystem : DirectedSystem G (linearMap G f · · ·) where
  map_self {_i} x := DirectedSystem.map_self (f := (f · · ·)) x
  map_map {_k _j _i} hij hjk x :=
    DirectedSystem.map_map (f := (f · · ·)) hij hjk x

/-- The underlying algebraic direct limit. -/
abbrev Carrier := Module.DirectLimit G (linearMap G f)

omit [Nonempty ι] in
/-- Equal representatives in an isometric direct system have equal norms. -/
theorem norm_eq_of_of_eq {i j : ι} {x : G i} {y : G j}
    (h : Module.DirectLimit.of ℝ ι G (linearMap G f) i x =
      Module.DirectLimit.of ℝ ι G (linearMap G f) j y) :
    ‖x‖ = ‖y‖ := by
  let k := max i j
  have hik : i ≤ k := le_max_left _ _
  have hjk : j ≤ k := le_max_right _ _
  have hk : Module.DirectLimit.of ℝ ι G (linearMap G f) k
        (linearMap G f i k hik x) =
      Module.DirectLimit.of ℝ ι G (linearMap G f) k
        (linearMap G f j k hjk y) := by
    rw [Module.DirectLimit.of_f, Module.DirectLimit.of_f]
    exact h
  obtain ⟨l, hkl, heq⟩ := Module.DirectLimit.exists_eq_of_of_eq hk
  have heqk : f i k hik x = f j k hjk y :=
    (f k l hkl).injective heq
  calc
    ‖x‖ = ‖f i k hik x‖ := (f i k hik).norm_map x |>.symm
    _ = ‖f j k hjk y‖ := congrArg norm heqk
    _ = ‖y‖ := (f j k hjk).norm_map y

/-- A chosen component containing a representative of a direct-limit element. -/
noncomputable def reprIndex (z : Carrier G f) : ι :=
  Classical.choose (Module.DirectLimit.exists_of z)

/-- A chosen representative in `reprIndex`. -/
noncomputable def reprValue (z : Carrier G f) : G (reprIndex G f z) :=
  Classical.choose (Classical.choose_spec (Module.DirectLimit.exists_of z))

omit [DirectedSystem G fun x1 x2 x3 => ⇑(f x1 x2 x3)] in
theorem repr_spec (z : Carrier G f) :
    Module.DirectLimit.of ℝ ι G (linearMap G f) (reprIndex G f z) (reprValue G f z) = z :=
  Classical.choose_spec (Classical.choose_spec (Module.DirectLimit.exists_of z))

/-- The norm of a direct-limit element, computed from any representative. -/
noncomputable def limitNorm (z : Carrier G f) : ℝ :=
  ‖reprValue G f z‖

theorem limitNorm_of (i : ι) (x : G i) :
    limitNorm G f (Module.DirectLimit.of ℝ ι G (linearMap G f) i x) = ‖x‖ := by
  change ‖reprValue G f (Module.DirectLimit.of ℝ ι G (linearMap G f) i x)‖ = ‖x‖
  exact norm_eq_of_of_eq G f (repr_spec G f _)

/-- The additive norm induced on the algebraic direct limit. -/
noncomputable def addGroupNorm : AddGroupNorm (Carrier G f) where
  toFun := limitNorm G f
  map_zero' := by
    let i := Classical.choice ‹Nonempty ι›
    rw [← map_zero (Module.DirectLimit.of ℝ ι G (linearMap G f) i), limitNorm_of]
    exact norm_zero
  add_le' z w := by
    obtain ⟨i, x, y, rfl, rfl⟩ := Module.DirectLimit.exists_of₂ z w
    rw [← map_add, limitNorm_of, limitNorm_of, limitNorm_of]
    exact norm_add_le x y
  neg' z := by
    refine Module.DirectLimit.induction_on z ?_
    intro i x
    rw [← map_neg, limitNorm_of, limitNorm_of, norm_neg]
  eq_zero_of_map_eq_zero' z hz := by
    refine Module.DirectLimit.induction_on z ?_ hz
    intro i x hx
    rw [limitNorm_of] at hx
    rw [norm_eq_zero] at hx
    simp [hx]

noncomputable instance normedAddCommGroup : NormedAddCommGroup (Carrier G f) :=
  (addGroupNorm G f).toNormedAddCommGroup

noncomputable instance normedSpace : NormedSpace ℝ (Carrier G f) where
  norm_smul_le c z := by
    refine Module.DirectLimit.induction_on z ?_
    intro i x
    rw [← map_smul (Module.DirectLimit.of ℝ ι G (linearMap G f) i)]
    change limitNorm G f (Module.DirectLimit.of ℝ ι G (linearMap G f) i (c • x)) ≤
      ‖c‖ * limitNorm G f (Module.DirectLimit.of ℝ ι G (linearMap G f) i x)
    rw [limitNorm_of, limitNorm_of, norm_smul]

/-- Every canonical component map is a linear isometry. -/
noncomputable def of (i : ι) : G i →ₗᵢ[ℝ] Carrier G f where
  toLinearMap := Module.DirectLimit.of ℝ ι G (linearMap G f) i
  norm_map' := limitNorm_of G f i

/-- Transition maps have the same image in the algebraic normed direct
limit. -/
theorem of_f {i j : ι} (hij : i ≤ j) (x : G i) :
    of G f j (f i j hij x) = of G f i x :=
  Module.DirectLimit.of_f

/-- The completed normed direct limit. -/
abbrev CompletedCarrier := UniformSpace.Completion (Carrier G f)

/-- The canonical isometric embedding of a component into the completed
direct limit. -/
noncomputable def completedOf (i : ι) : G i →ₗᵢ[ℝ] CompletedCarrier G f :=
  UniformSpace.Completion.toComplₗᵢ.comp (of G f i)

@[simp]
theorem completedOf_apply (i : ι) (x : G i) :
    completedOf G f i x = (of G f i x : CompletedCarrier G f) :=
  rfl

/-- Transition maps have the same image in the completed direct limit. -/
theorem completedOf_f {i j : ι} (hij : i ≤ j) (x : G i) :
    completedOf G f j (f i j hij x) = completedOf G f i x := by
  exact congrArg ((↑) : Carrier G f → CompletedCarrier G f)
    (Module.DirectLimit.of_f (R := ℝ) (G := G) (f := linearMap G f)
      (hij := hij) (x := x))

section Lift

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
variable (g : ∀ i, G i →L[ℝ] H)
variable (hg : ∀ i j (hij : i ≤ j) x, g j (f i j hij x) = g i x)

/-- The coherent linear map on the algebraic normed direct limit. -/
noncomputable def algebraicLiftLinear : Carrier G f →ₗ[ℝ] H :=
  Module.DirectLimit.lift ℝ ι G (linearMap G f) (fun i => (g i).toLinearMap) hg

omit [CompleteSpace H] in
theorem algebraicLiftLinear_of (i : ι) (x : G i) :
    algebraicLiftLinear G f g hg (of G f i x) = g i x := by
  exact Module.DirectLimit.lift_of (R := ℝ) (ι := ι) (G := G) (f := linearMap G f)
    (fun i => (g i).toLinearMap) hg x

omit [CompleteSpace H] in
/-- A uniform componentwise bound descends to the algebraic direct limit. -/
theorem algebraicLiftLinear_norm_le (C : ℝ)
    (hC : ∀ i x, ‖g i x‖ ≤ C * ‖x‖) (z : Carrier G f) :
    ‖algebraicLiftLinear G f g hg z‖ ≤ C * ‖z‖ := by
  refine Module.DirectLimit.induction_on z ?_
  intro i x
  change ‖algebraicLiftLinear G f g hg (of G f i x)‖ ≤ C * ‖of G f i x‖
  rw [algebraicLiftLinear_of,
    show ‖of G f i x‖ = ‖x‖ from limitNorm_of G f i x]
  exact hC i x

/-- The bounded coherent map on the algebraic direct limit. -/
noncomputable def algebraicLift (C : ℝ)
    (hC : ∀ i x, ‖g i x‖ ≤ C * ‖x‖) : Carrier G f →L[ℝ] H :=
  (algebraicLiftLinear G f g hg).mkContinuous C
    (algebraicLiftLinear_norm_le G f g hg C hC)

/-- A bounded coherent family extends uniquely over the completed direct
limit. -/
noncomputable def completedLift (C : ℝ)
    (hC : ∀ i x, ‖g i x‖ ≤ C * ‖x‖) : CompletedCarrier G f →L[ℝ] H :=
  (algebraicLift G f g hg C hC).extend
    (UniformSpace.Completion.toComplL : Carrier G f →L[ℝ] CompletedCarrier G f)

theorem completedLift_completedOf (C : ℝ)
    (hC : ∀ i x, ‖g i x‖ ≤ C * ‖x‖) (i : ι) (x : G i) :
    completedLift G f g hg C hC (completedOf G f i x) = g i x := by
  change (algebraicLift G f g hg C hC).extend
      (UniformSpace.Completion.toComplL : Carrier G f →L[ℝ] CompletedCarrier G f)
      ((↑(of G f i x) : CompletedCarrier G f)) = g i x
  change (algebraicLift G f g hg C hC).extend
      (UniformSpace.Completion.toComplL : Carrier G f →L[ℝ] CompletedCarrier G f)
      ((UniformSpace.Completion.toComplL : Carrier G f →L[ℝ] CompletedCarrier G f)
        (of G f i x)) = g i x
  rw [ContinuousLinearMap.extend_eq _ UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe _)]
  exact algebraicLiftLinear_of G f g hg i x

/-- A coherent componentwise contraction remains contractive after passage to
the completed direct limit. -/
theorem completedLift_norm_le_one
    (hC : ∀ i x, ‖g i x‖ ≤ ‖x‖) (z : CompletedCarrier G f) :
    ‖completedLift G f g hg 1 (by
      intro i x
      simpa using hC i x) z‖ ≤ ‖z‖ := by
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih z =>
      change ‖(algebraicLift G f g hg 1 _).extend
          (UniformSpace.Completion.toComplL : Carrier G f →L[ℝ] CompletedCarrier G f)
          (↑z)‖ ≤ ‖(↑z : CompletedCarrier G f)‖
      change ‖(algebraicLift G f g hg 1 _).extend
          (UniformSpace.Completion.toComplL : Carrier G f →L[ℝ] CompletedCarrier G f)
          ((UniformSpace.Completion.toComplL :
            Carrier G f →L[ℝ] CompletedCarrier G f) z)‖ ≤
        ‖(↑z : CompletedCarrier G f)‖
      rw [ContinuousLinearMap.extend_eq _ UniformSpace.Completion.denseRange_coe
        (UniformSpace.Completion.isUniformInducing_coe _),
        UniformSpace.Completion.norm_coe]
      change ‖algebraicLiftLinear G f g hg z‖ ≤ ‖z‖
      simpa using algebraicLiftLinear_norm_le G f g hg 1 (by
        intro i x
        simpa using hC i x) z

end Lift

end NormedDirectLimit

end ScottishBook155
