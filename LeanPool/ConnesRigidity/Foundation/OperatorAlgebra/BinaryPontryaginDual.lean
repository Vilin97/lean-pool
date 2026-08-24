/-
Copyright (c) 2026 Utensil Song, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song, OpenAI
-/
/-

Derived in part from Apache-2.0 `openai/ten-proofs`, `ConnesRigidity.lean` at
94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6, lines 10717-11155.
Modifications: extracted the binary character-coordinate layer and changed
carrier names and namespace for Zhou §§3-4. See the upstream PORT_MAP.md.
-/
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.Instances.ZMod

/-!
The binary pontryagin dual component of the Connes rigidity formalization.
-/

namespace Connes
namespace BinaryPontryaginDual

noncomputable section

/--
The `F` construction used in the Connes rigidity formalization.
-/
abbrev F := ZMod 2

/- Pointwise topology on a binary linear dual. Paper: §3.
-/
/--
The `pointwiseDualTopology` construction used in the Connes rigidity formalization.
-/
@[reducible] def pointwiseDualTopology (M : Type*) [AddCommGroup M] [Module F M] :
    TopologicalSpace (M →ₗ[F] F) :=
  TopologicalSpace.induced (fun ℓ : M →ₗ[F] F => (fun m => ℓ m)) inferInstance

/--
The `instPointwiseDualTopology` construction used in the Connes rigidity formalization.
-/
local instance instPointwiseDualTopology {M : Type*} [AddCommGroup M] [Module F M] :
    TopologicalSpace (M →ₗ[F] F) := pointwiseDualTopology M

/-- The two-valued character group is identified with the binary roots. Paper: §3.
-/
def binaryRootsEquiv : Multiplicative F ≃* rootsOfUnity 2 Circle :=
  MulEquiv.ofBijective
    (AddChar.toMonoidHomEquiv (ZMod.rootsOfUnityAddChar 2))
    (by simpa only [AddChar.coe_toMonoidHomEquiv,
          EquivLike.bijective_comp] using (bijective_rootsOfUnityAddChar (n := 2)))

@[simp] theorem binaryRootsEquiv_apply (a : F) :
    binaryRootsEquiv (Multiplicative.ofAdd a) =
      ZMod.rootsOfUnityAddChar 2 a := rfl

@[simp] theorem binaryRootsEquiv_val (a : Multiplicative F) :
    ((binaryRootsEquiv a).val : Circle) =
      ZMod.toCircle (Multiplicative.toAdd a) := rfl

/-- Binary characters have order dividing two. Paper: §3. -/
theorem character_sq (M : Type*) [AddCommGroup M] [Module F M]
    [TopologicalSpace M]
    (χ : PontryaginDual (Multiplicative M))
    (x : Multiplicative M) : χ x ^ (2 : ℕ) = 1 := by
  have hx : x ^ (2 : ℕ) = (1 : Multiplicative M) := by
    apply Multiplicative.toAdd.injective
    change (2 : ℕ) • Multiplicative.toAdd x = 0
    rw [← Nat.cast_smul_eq_nsmul F]
    have htwo : (↑(2 : ℕ) : F) = 0 := by decide
    rw [htwo, zero_smul]
  rw [← map_pow, hx, map_one]

/- Extract the binary additive character represented by a Pontryagin character. Paper: §3.
-/
/--
The `characterIntoRoots` construction used in the Connes rigidity formalization.
-/
def characterIntoRoots {M : Type*} [AddCommGroup M] [Module F M]
    [TopologicalSpace M]
    (χ : PontryaginDual (Multiplicative M)) :
    Multiplicative M →* rootsOfUnity 2 Circle where
  toFun x := ⟨toUnits (χ x), by
    rw [mem_rootsOfUnity']
    change χ x ^ (2 : ℕ) = 1
    exact character_sq M χ x⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    exact map_one χ
  map_mul' x y := by
    apply Subtype.ext
    apply Units.ext
    exact map_mul χ x y

/-- The additive binary character underlying a Pontryagin character. Paper: §3.
-/
def characterAdd {M : Type*} [AddCommGroup M] [Module F M]
    [TopologicalSpace M]
    (χ : PontryaginDual (Multiplicative M)) : M →+ F :=
  { toFun x := Multiplicative.toAdd
      (binaryRootsEquiv.symm
        (characterIntoRoots χ (Multiplicative.ofAdd x)))
    map_zero' := by
      change Multiplicative.toAdd
        (binaryRootsEquiv.symm (characterIntoRoots χ 1)) = 0
      rw [map_one, map_one]
      rfl
    map_add' x y := by
      change Multiplicative.toAdd
          (binaryRootsEquiv.symm
            (characterIntoRoots χ
              (Multiplicative.ofAdd x * Multiplicative.ofAdd y))) = _
      rw [map_mul, map_mul]
      rfl }

/-- The linear form underlying a Pontryagin character. Paper: §3.
-/
def characterLinear {M : Type*} [AddCommGroup M] [Module F M]
    [TopologicalSpace M]
    (χ : PontryaginDual (Multiplicative M)) : M →ₗ[F] F :=
  (characterAdd χ).toZModLinearMap 2

@[simp] theorem characterLinear_circle {M : Type*} [AddCommGroup M] [Module F M]
    [TopologicalSpace M]
    (χ : PontryaginDual (Multiplicative M)) (x : M) :
    ZMod.toCircle (characterLinear χ x) =
      χ (Multiplicative.ofAdd x) := by
  have h := binaryRootsEquiv.apply_symm_apply
    (characterIntoRoots χ (Multiplicative.ofAdd x))
  change ZMod.toCircle (Multiplicative.toAdd
    (binaryRootsEquiv.symm
      (characterIntoRoots χ (Multiplicative.ofAdd x)))) =
    χ (Multiplicative.ofAdd x)
  calc
    _ = ((characterIntoRoots χ
      (Multiplicative.ofAdd x)).val : Circle) := by
      simpa only [binaryRootsEquiv_val] using
        congrArg (fun z : rootsOfUnity 2 Circle => (z.val : Circle)) h
    _ = _ := rfl

/-- The extracted linear character is continuous in the pointwise dual topology. Paper: §3. -/
theorem continuous_characterLinear {M : Type*} [AddCommGroup M] [Module F M]
    [TopologicalSpace M]
    (χ : PontryaginDual (Multiplicative M)) :
    Continuous (characterLinear χ) := by
  rw [continuous_def]
  intro s _
  classical
  have hopen (a : F) :
      IsOpen {x : M | characterLinear χ x = a} := by
    have hcircle : Continuous (fun x : M =>
        χ (Multiplicative.ofAdd x)) := χ.continuous
    have hpre : IsOpen {x : M |
        χ (Multiplicative.ofAdd x) ≠ ZMod.toCircle (a + 1)} :=
      isOpen_ne.preimage hcircle
    convert hpre using 1
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [← characterLinear_circle χ x]
    rw [ZMod.injective_toCircle.ne_iff]
    exact (show ∀ a b : F, b = a ↔ b ≠ a + 1 from by decide)
      a (characterLinear χ x)
  have hs : (characterLinear χ : M → F) ⁻¹' s =
      ⋃ a ∈ s, {x : M | characterLinear χ x = a} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq,
      exists_prop, exists_eq_right']
  rw [hs]
  apply isOpen_iUnion
  intro a
  exact isOpen_iUnion fun _ => by simpa only using hopen a

/- Continuous binary bidual functionals are evaluations. Paper: §3. -/
theorem continuous_binaryDual_eq_evaluation
    (M : Type*) [AddCommGroup M] [Module F M]
    (φ : (M →ₗ[F] F) →ₗ[F] F)
    (hφ : @Continuous (M →ₗ[F] F) F
      (pointwiseDualTopology M) inferInstance φ) :
    ∃ m : M, ∀ ℓ : M →ₗ[F] F, φ ℓ = ℓ m := by
  let pointwiseTopology : TopologicalSpace (M →ₗ[F] F) := pointwiseDualTopology M
  have hzeroOpen : IsOpen ({0} : Set F) := isOpen_discrete _
  have hkerOpen : IsOpen {ℓ : M →ₗ[F] F | φ ℓ = 0} :=
    hzeroOpen.preimage hφ
  have hkerOpen' :
      @IsOpen (M →ₗ[F] F) (pointwiseDualTopology M)
        {ℓ : M →ₗ[F] F | φ ℓ = 0} := hkerOpen
  obtain ⟨U, hU, hpre⟩ := isOpen_induced_iff.mp hkerOpen'
  have hzeroU : (0 : M → F) ∈ U := by
    have h : (0 : M →ₗ[F] F) ∈ {ℓ : M →ₗ[F] F | φ ℓ = 0} := by
      simp only [Set.mem_ofPred_eq, map_zero]
    rw [← hpre] at h
    exact h
  obtain ⟨I, u, hu, hsubset⟩ := (isOpen_pi_iff.mp hU) 0 hzeroU
  have hkernels :
      (⨅ i : {i // i ∈ I}, (Module.Dual.eval F M i.1).ker) ≤ φ.ker := by
    intro ℓ hℓ
    have hv : ∀ i ∈ I, ℓ i = 0 := by
      intro i hi
      have hi' :=
        (Submodule.mem_iInf
          (fun i : {i // i ∈ I} => (Module.Dual.eval F M i.1).ker)).mp hℓ
          (⟨i, hi⟩ : {i // i ∈ I})
      exact LinearMap.mem_ker.mp hi'
    have hcylinder : (fun m => ℓ m) ∈ (I : Set M).pi u := by
      intro i hi
      change ℓ i ∈ u i
      rw [hv i (Finset.mem_coe.mp hi)]
      exact (hu i (Finset.mem_coe.mp hi)).2
    apply LinearMap.mem_ker.mpr
    have hmem : ℓ ∈ {f : M →ₗ[F] F | φ f = 0} := by
      rw [← hpre]
      exact hsubset hcylinder
    exact hmem
  have hspan :
      φ ∈ Submodule.span F (Set.range fun i : {i // i ∈ I} =>
        Module.Dual.eval F M i.1) :=
    mem_span_of_iInf_ker_le_ker hkernels
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hspan
  refine ⟨∑ i, c i • i.1, ?_⟩
  intro ℓ
  rw [← hc]
  simp only [Finset.univ_eq_attach, LinearMap.coe_sum, LinearMap.coe_smul,
    Finset.sum_apply, Pi.smul_apply, Module.Dual.eval_apply, smul_eq_mul,
    map_sum, map_smul]

/- Evaluation identifies the continuous binary bidual with the original module. Paper: §3.
-/
/--
The `continuousBinaryBidual` construction used in the Connes rigidity formalization.
-/
def continuousBinaryBidual (M : Type*) [AddCommGroup M] [Module F M] :
    Submodule F ((M →ₗ[F] F) →ₗ[F] F) :=
  let _ : TopologicalSpace (M →ₗ[F] F) := pointwiseDualTopology M
  { carrier := {φ | Continuous (φ : (M →ₗ[F] F) → F)}
    zero_mem' := continuous_const
    add_mem' := fun hf hg ↦ hf.add hg
    smul_mem' := fun c _ hφ ↦ hφ.const_smul c }

/--
The `continuousBinaryBidualEvaluation` construction used in the Connes rigidity formalization.
-/
def continuousBinaryBidualEvaluation (M : Type*) [AddCommGroup M] [Module F M] :
    M →ₗ[F] continuousBinaryBidual M :=
  let _ : TopologicalSpace (M →ₗ[F] F) := pointwiseDualTopology M
  { toFun m :=
      ⟨Module.Dual.eval F M m,
        (continuous_apply m).comp continuous_induced_dom⟩
    map_add' m n := by
      apply Subtype.ext
      exact map_add (Module.Dual.eval F M) m n
    map_smul' c m := by
      apply Subtype.ext
      exact map_smul (Module.Dual.eval F M) c m }

@[simp] theorem continuousBinaryBidualEvaluation_apply
    (M : Type*) [AddCommGroup M] [Module F M]
    (m : M) (ℓ : M →ₗ[F] F) :
    (continuousBinaryBidualEvaluation M m :
      (M →ₗ[F] F) →ₗ[F] F) ℓ = ℓ m := rfl

/-- The binary Pontryagin dual of a linear dual is its evaluation module. Paper: §3.
-/
def pointwiseEvaluationCharacter
    (M : Type*) [AddCommGroup M] [Module F M]
    (m : M) :
    PontryaginDual (Multiplicative (M →ₗ[F] F)) := by
  let _ : TopologicalSpace (M →ₗ[F] F) := pointwiseDualTopology M
  exact {
    toMonoidHom :=
      (AddChar.toMonoidHomEquiv (ZMod.toCircle : AddChar F Circle)).comp
        (Module.Dual.eval F M m).toAddMonoidHom.toMultiplicative
    continuous_toFun := by
      change Continuous
        (fun ℓ : M →ₗ[F] F ↦ ZMod.toCircle (ℓ m))
      exact continuous_of_discreteTopology.comp
        ((continuous_apply m).comp continuous_induced_dom) }

@[simp] theorem pointwiseEvaluationCharacter_apply
    (M : Type*) [AddCommGroup M] [Module F M]
    (m : M) (ℓ : M →ₗ[F] F) :
    pointwiseEvaluationCharacter M m (Multiplicative.ofAdd ℓ) =
      ZMod.toCircle (ℓ m) := rfl

/--
The `pointwiseEvaluationHom` construction used in the Connes rigidity formalization.
-/
def pointwiseEvaluationHom (M : Type*) [AddCommGroup M] [Module F M] :
    M →+ Additive (PontryaginDual (Multiplicative (M →ₗ[F] F))) where
  toFun m := Additive.ofMul (pointwiseEvaluationCharacter M m)
  map_zero' := by
    apply Additive.toMul.injective
    apply PontryaginDual.ext
    intro ℓ
    change ZMod.toCircle ((Multiplicative.toAdd ℓ) 0) = 1
    simp only [map_zero, AddChar.map_zero_eq_one]
  map_add' m n := by
    apply Additive.toMul.injective
    apply PontryaginDual.ext
    intro ℓ
    change ZMod.toCircle ((Multiplicative.toAdd ℓ) (m + n)) =
      ZMod.toCircle ((Multiplicative.toAdd ℓ) m) *
        ZMod.toCircle ((Multiplicative.toAdd ℓ) n)
    rw [map_add, AddChar.map_add_eq_mul]

@[simp] theorem pointwiseEvaluationHom_apply
    (M : Type*) [AddCommGroup M] [Module F M]
    (m : M) (ℓ : M →ₗ[F] F) :
    Additive.toMul (pointwiseEvaluationHom M m)
      (Multiplicative.ofAdd ℓ) = ZMod.toCircle (ℓ m) := by
  change pointwiseEvaluationCharacter M m (Multiplicative.ofAdd ℓ) = _
  exact pointwiseEvaluationCharacter_apply M m ℓ

/-- The Pontryagin dual isomorphism used by the Zhou Fourier model. Paper: §3.
-/
def pointwisePontryaginDualEquiv
    (M : Type*) [AddCommGroup M] [Module F M] :
    Additive (PontryaginDual (Multiplicative (M →ₗ[F] F))) ≃+ M := by
  refine (AddEquiv.ofBijective (pointwiseEvaluationHom M) ⟨?_, ?_⟩).symm
  · intro m n h
    apply Module.eval_apply_injective F
    apply LinearMap.ext
    intro ℓ
    change ℓ m = ℓ n
    apply ZMod.injective_toCircle
    simpa only [pointwiseEvaluationHom_apply] using
      DFunLike.congr_fun (congrArg Additive.toMul h)
        (Multiplicative.ofAdd ℓ)
  · intro χ
    obtain ⟨m, hm⟩ := continuous_binaryDual_eq_evaluation M
      (characterLinear (Additive.toMul χ))
      (continuous_characterLinear (Additive.toMul χ))
    refine ⟨m, ?_⟩
    apply Additive.toMul.injective
    apply PontryaginDual.ext
    intro ℓ
    change ZMod.toCircle ((Multiplicative.toAdd ℓ) m) =
      Additive.toMul χ ℓ
    rw [← hm (Multiplicative.toAdd ℓ)]
    exact characterLinear_circle (Additive.toMul χ) (Multiplicative.toAdd ℓ)

@[simp] theorem pointwisePontryaginDualEquiv_symm_apply
    (M : Type*) [AddCommGroup M] [Module F M] (m : M) :
    (pointwisePontryaginDualEquiv M).symm m = pointwiseEvaluationHom M m := rfl

@[simp] theorem pointwisePontryaginDualEquiv_apply_character
    (M : Type*) [AddCommGroup M] [Module F M]
    (χ : Additive (PontryaginDual (Multiplicative (M →ₗ[F] F))))
    (ℓ : M →ₗ[F] F) :
    ZMod.toCircle (ℓ (pointwisePontryaginDualEquiv M χ)) =
      Additive.toMul χ (Multiplicative.ofAdd ℓ) := by
  have h := (pointwisePontryaginDualEquiv M).symm_apply_apply χ
  have hpoint := DFunLike.congr_fun (congrArg Additive.toMul h)
    (Multiplicative.ofAdd ℓ)
  rw [pointwisePontryaginDualEquiv_symm_apply] at hpoint
  simpa only [pointwiseEvaluationHom_apply] using hpoint

end

end BinaryPontryaginDual
end Connes
