/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Exactness
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Finiteness.Subalgebra
public import Mathlib.Topology.UniformSpace.AbstractCompletion
public import Mathlib.Topology.UniformSpace.Completion
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Bridge between UniformSpace.Completion and AdicCompletion

For a commutative ring `R` with an ideal `I` such that the topology on `R`
is the `I`-adic topology (`IsAdic I`), we construct a ring isomorphism:

  `UniformSpace.Completion R ≃+* AdicCompletion I R`

## Strategy

`AdicCompletion I R` is a subtype of `∀ n, R ⧸ (I^n • ⊤)`. We put the
discrete uniformity on each quotient and the product uniformity on the Pi
type. `AdicCompletion` inherits the subtype uniformity. Then:

1. The product of discrete spaces is T₂ and complete.
2. `AdicCompletion` is a closed subtype → T₂ and complete.
3. `AdicCompletion.of I R` is uniform inducing with dense range.
4. Package as `AbstractCompletion`, use `compareEquiv`.
5. Multiplicativity by density + T₂.
-/

@[expose] public section

universe u

open scoped Topology Uniformity

open Filter Set Function

namespace AdicCompletionBridge

variable {R : Type u} [CommRing R] (I : Ideal R)

/-! ### The key submodule identity -/

/-- For a ring `R` as a module over itself: `I^n • ⊤ = I^n`. -/
theorem ideal_smul_top_eq_self (n : ℕ) :
    (I ^ n • (⊤ : Submodule R R) : Submodule R R) = ↑(I ^ n) := by
  ext x
  constructor
  · intro hx
    exact Submodule.smul_induction_on hx (fun a ha r _ => Ideal.mul_mem_right r _ ha)
      fun _ _ h1 h2 => (I ^ n).add_mem h1 h2
  · intro hx
    have : x * 1 ∈ (I ^ n • (⊤ : Submodule R R) : Submodule R R) :=
      Submodule.smul_mem_smul hx Submodule.mem_top
    rwa [mul_one] at this

/-! ### Discrete topology on quotients -/

/-- Discrete topology on `R ⧸ (I^n • ⊤)`. -/
noncomputable instance quotientDiscreteTopology (n : ℕ) :
    TopologicalSpace (R ⧸ (I ^ n • (⊤ : Submodule R R))) := ⊥

/-- Discrete uniform space on `R ⧸ (I^n • ⊤)`. -/
noncomputable instance quotientDiscreteUniformSpace (n : ℕ) :
    UniformSpace (R ⧸ (I ^ n • (⊤ : Submodule R R))) := ⊥

/-- The topology on `R ⧸ (I^n • ⊤)` is discrete. -/
instance quotientDiscrete (n : ℕ) :
    DiscreteTopology (R ⧸ (I ^ n • (⊤ : Submodule R R))) := ⟨rfl⟩

/-- The uniformity on `R ⧸ (I^n • ⊤)` is discrete. -/
instance quotientDiscreteUnif (n : ℕ) :
    DiscreteUniformity (R ⧸ (I ^ n • (⊤ : Submodule R R))) := ⟨rfl⟩

/-! ### Helper: coordinate entourages -/

/-- `{(f,g) | f n = g n}` is a Pi-uniformity entourage (discrete factors). -/
private theorem pi_coord_mem_uniformity (n : ℕ) :
    {p : (∀ k, R ⧸ (I ^ k • (⊤ : Submodule R R))) ×
         (∀ k, R ⧸ (I ^ k • (⊤ : Submodule R R))) |
      p.1 n = p.2 n} ∈
      𝓤 (∀ k, R ⧸ (I ^ k • (⊤ : Submodule R R))) := by
  rw [Pi.uniformity]
  refine Filter.mem_iInf_of_mem n (Filter.mem_comap.mpr ?_)
  exact ⟨{p | p.1 = p.2}, Filter.mem_principal_self _, fun ⟨_, _⟩ h => h⟩

/-- `{(x,y) | eval n x = eval n y}` is in the subtype uniformity of AdicCompletion. -/
private theorem eval_entourage_mem (n : ℕ) :
    {p : AdicCompletion I R × AdicCompletion I R |
      AdicCompletion.eval I R n p.1 =
        AdicCompletion.eval I R n p.2} ∈
      @uniformity (AdicCompletion I R) instUniformSpaceSubtype :=
  Filter.mem_comap.mpr ⟨{p | p.1 n = p.2 n}, pi_coord_mem_uniformity I n,
    fun ⟨_, _⟩ h => h⟩

/-! ### Topology and uniformity on AdicCompletion via subtype of product -/

section Instances

variable [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]

/-- The uniform structure on `AdicCompletion I R`: the subtype uniformity
from the product `∀ n, R ⧸ (I^n • ⊤)` with discrete factors. -/
noncomputable instance adicCompletionUniformSpace :
    UniformSpace (AdicCompletion I R) :=
  instUniformSpaceSubtype

/-- `AdicCompletion I R` is T₀ because elements agreeing at all levels are equal. -/
instance adicCompletionT0 : @T0Space (AdicCompletion I R)
    (adicCompletionUniformSpace I).toTopologicalSpace := by
  constructor
  intro ⟨f, hf⟩ ⟨g, hg⟩ hinsep
  ext n
  have hpi : @Inseparable _ Pi.topologicalSpace
      (⟨f, hf⟩ : AdicCompletion I R).val (⟨g, hg⟩ : AdicCompletion I R).val :=
    Inseparable.map hinsep continuous_subtype_val
  exact (inseparable_pi.mp hpi n).eq

/-- The set underlying `AdicCompletion I R` inside the product type. -/
private def adicCompletionSet :
    Set (∀ k, R ⧸ (I ^ k • (⊤ : Submodule R R))) :=
  {f | ∀ {m n : ℕ} (hmn : m ≤ n),
    (AdicCompletion.transitionMap I R hmn) (f n) = f m}

omit [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R] in
private theorem adicCompletionSet_isClosed : IsClosed (adicCompletionSet I) := by
  rw [show adicCompletionSet I =
      ⋂ (p : ℕ × ℕ) (_ : p.1 ≤ p.2),
        {g | (AdicCompletion.transitionMap I R ‹p.1 ≤ p.2›) (g p.2) = g p.1} from by
    ext g; simp only [adicCompletionSet, Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨fun h p hp => h hp, fun h m n hmn => h ⟨m, n⟩ hmn⟩]
  exact isClosed_iInter fun ⟨m, n⟩ => isClosed_iInter fun hmn =>
    isClosed_eq (continuous_of_discreteTopology.comp (continuous_apply n))
      (continuous_apply m)

/-- `AdicCompletion I R` is complete: it's a closed subtype of the complete
product `∀ n, R ⧸ (I^n • ⊤)` (product of discrete = complete). -/
instance adicCompletionComplete : @CompleteSpace (AdicCompletion I R)
    (adicCompletionUniformSpace I) :=
  (adicCompletionSet_isClosed I).completeSpace_coe

end Instances

section Bridge

variable [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]

omit [IsTopologicalRing R] in
/-- `AdicCompletion.of I R` is uniform inducing for the I-adic uniformity
on `R` and the subtype uniformity on `AdicCompletion I R`. -/
theorem of_isUniformInducing (hadic : IsAdic I) :
    @IsUniformInducing R (AdicCompletion I R) _ (adicCompletionUniformSpace I)
      (AdicCompletion.of I R) := by
  constructor
  have hbasis_nhds : (𝓝 (0 : R)).HasBasis (fun (_ : ℕ) => True)
      (fun n => ((I ^ n : Ideal R) : Set R)) := by
    have h : @nhds R _ 0 = @nhds R I.adicTopology 0 := by rw [hadic]
    rw [h]; convert Ideal.hasBasis_nhds_adic I (0 : R) using 1
    funext n; simp [zero_add, Set.image_id']
  have hbasis_unif := hbasis_nhds.uniformity_of_nhds_zero
  have hbasis_comap : (Filter.comap (fun x =>
      ((AdicCompletion.of I R) x.1, (AdicCompletion.of I R) x.2))
      (𝓤 (AdicCompletion I R))).HasBasis (fun (_ : ℕ) => True)
      (fun n => {x : R × R | x.2 - x.1 ∈ (I ^ n : Ideal R)}) := by
    constructor; intro U; constructor
    · intro hU
      obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp hU
      obtain ⟨W, hW, hWV⟩ := Filter.mem_comap.mp hV
      rw [Pi.uniformity, Filter.mem_iInf] at hW
      obtain ⟨S, hSfin, V_fn, hV_mem, hW_eq⟩ := hW
      refine ⟨hSfin.toFinset.sup id, trivial, ?_⟩
      intro ⟨a, b⟩ (hab : b - a ∈ (I ^ hSfin.toFinset.sup id : Ideal R))
      apply hVU; apply hWV; rw [hW_eq]
      apply Set.mem_iInter.mpr; intro ⟨i, hi⟩
      obtain ⟨D_i, hD_i, hD_V⟩ := Filter.mem_comap.mp (hV_mem ⟨i, hi⟩)
      apply hD_V
      have hle : i ≤ hSfin.toFinset.sup id :=
        Finset.le_sup (f := id) (hSfin.mem_toFinset.mpr hi)
      have hsub : b - a ∈ (I ^ i : Ideal R) := Ideal.pow_le_pow_right hle hab
      have heval_eq : (AdicCompletion.of I R a).val i =
          (AdicCompletion.of I R b).val i := by
        change AdicCompletion.eval I R i (AdicCompletion.of I R a) =
          AdicCompletion.eval I R i (AdicCompletion.of I R b)
        rw [AdicCompletion.eval_of, AdicCompletion.eval_of, ← sub_eq_zero, ← map_sub]
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        rw [ideal_smul_top_eq_self]
        exact (I ^ i).neg_mem_iff.mp (by rwa [neg_sub])
      change ((AdicCompletion.of I R a).val i, (AdicCompletion.of I R b).val i) ∈ D_i
      rw [heval_eq]; exact refl_mem_uniformity hD_i
    · rintro ⟨n, -, hn⟩
      refine Filter.mem_comap.mpr ⟨{p | AdicCompletion.eval I R n p.1 =
        AdicCompletion.eval I R n p.2}, eval_entourage_mem I n, ?_⟩
      intro ⟨a, b⟩ hab
      apply hn; change b - a ∈ (I ^ n : Ideal R)
      simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hab
      rw [AdicCompletion.eval_of, AdicCompletion.eval_of] at hab
      have hmem := (Submodule.Quotient.eq (I ^ n • ⊤)).mp hab
      rw [ideal_smul_top_eq_self] at hmem
      exact (I ^ n).neg_mem_iff.mp (by rwa [neg_sub])
  exact hbasis_unif.eq_of_same_basis hbasis_comap |>.symm

omit [IsUniformAddGroup R] [IsTopologicalRing R] in
/-- `AdicCompletion.of I R` has dense range in the subtype topology. -/
theorem of_denseRange (_hadic : IsAdic I) :
    @DenseRange (AdicCompletion I R) (adicCompletionUniformSpace I).toTopologicalSpace
      R (AdicCompletion.of I R) := by
  intro x
  choose r hr using fun n => Submodule.Quotient.mk_surjective (I ^ n • ⊤) (x.val n)
  have htendsto : Filter.Tendsto (fun n => AdicCompletion.of I R (r n))
      Filter.atTop (@nhds _ (adicCompletionUniformSpace I).toTopologicalSpace x) := by
    rw [Filter.Tendsto, Filter.map_le_iff_le_comap, Filter.le_def]
    intro U hU
    rw [Filter.mem_comap] at hU
    obtain ⟨V, hV, hVU⟩ := hU
    rw [@nhds_eq_comap_uniformity _ (adicCompletionUniformSpace I)] at hV
    obtain ⟨E, hE, hEV⟩ := Filter.mem_comap.mp hV
    obtain ⟨W, hW, hWE⟩ := Filter.mem_comap.mp hE
    rw [Pi.uniformity] at hW
    obtain ⟨S, hSfin, V_fn, hV_fn, hW_eq⟩ := (Filter.mem_iInf).mp hW
    refine Filter.mem_atTop_sets.mpr ⟨hSfin.toFinset.sup id, fun m hm => hVU ?_⟩
    apply hEV; apply hWE; rw [hW_eq]; apply Set.mem_iInter.mpr
    intro ⟨i, hi⟩
    obtain ⟨D_i, hD_i, hD_V⟩ := Filter.mem_comap.mp (hV_fn ⟨i, hi⟩)
    apply hD_V
    change (x.val i, (AdicCompletion.of I R (r m)).val i) ∈ D_i
    have hle : i ≤ hSfin.toFinset.sup id :=
      Finset.le_sup (f := id) (hSfin.mem_toFinset.mpr hi)
    have hle_m : i ≤ m := le_trans hle hm
    have heval : (AdicCompletion.of I R (r m)).val i = x.val i := by
      change AdicCompletion.eval I R i (AdicCompletion.of I R (r m)) = x.val i
      rw [show AdicCompletion.eval I R i (AdicCompletion.of I R (r m)) =
        (AdicCompletion.transitionMap I R hle_m)
          (AdicCompletion.eval I R m (AdicCompletion.of I R (r m))) from
          ((AdicCompletion.of I R (r m)).property hle_m).symm,
        AdicCompletion.eval_of]
      change (AdicCompletion.transitionMap I R hle_m) (Submodule.Quotient.mk (r m)) = x.val i
      rw [hr m, x.property hle_m]
    rw [heval]; exact refl_mem_uniformity hD_i
  exact mem_closure_of_tendsto htendsto
    (Filter.Eventually.of_forall fun n => Set.mem_range.mpr ⟨r n, rfl⟩)

/-- `AdicCompletion I R` with subtype uniformity as an `AbstractCompletion`. -/
noncomputable def adicAbstractCompletion (hadic : IsAdic I) : AbstractCompletion R where
  space := AdicCompletion I R
  coe := AdicCompletion.of I R
  uniformStruct := adicCompletionUniformSpace I
  complete := adicCompletionComplete I
  separation := adicCompletionT0 I
  isUniformInducing := of_isUniformInducing I hadic
  dense := of_denseRange I hadic

/-- Forward comparison: `Completion R → AdicCompletion I R`. -/
noncomputable def adicCompletionEquiv (hadic : IsAdic I) :
    UniformSpace.Completion R → AdicCompletion I R :=
  (UniformSpace.Completion.cPkg (α := R)).compare (adicAbstractCompletion I hadic)

/-- Backward comparison: `AdicCompletion I R → Completion R`. -/
noncomputable def adicCompletionEquivInv (hadic : IsAdic I) :
    AdicCompletion I R → UniformSpace.Completion R :=
  (adicAbstractCompletion I hadic).compare (UniformSpace.Completion.cPkg (α := R))

/-- The ring isomorphism `Completion R ≃+* AdicCompletion I R`. -/
noncomputable def adicCompletionRingEquiv (hadic : IsAdic I) :
    UniformSpace.Completion R ≃+* AdicCompletion I R := by
  let e := adicCompletionEquiv I hadic
  let e_inv := adicCompletionEquivInv I hadic
  haveI : T2Space (AdicCompletion I R) := inferInstance
  haveI : CompleteSpace (AdicCompletion I R) := adicCompletionComplete I
  haveI : ContinuousMul (AdicCompletion I R) := ⟨by
    apply Continuous.subtype_mk; apply continuous_pi; intro n
    change Continuous fun p : AdicCompletion I R × AdicCompletion I R =>
      p.1.val n * p.2.val n
    exact ((continuous_apply n).comp (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_apply n).comp (continuous_subtype_val.comp continuous_snd))⟩
  haveI : ContinuousAdd (AdicCompletion I R) := ⟨by
    apply Continuous.subtype_mk; apply continuous_pi; intro n
    change Continuous fun p : AdicCompletion I R × AdicCompletion I R =>
      p.1.val n + p.2.val n
    exact ((continuous_apply n).comp (continuous_subtype_val.comp continuous_fst)).add
      ((continuous_apply n).comp (continuous_subtype_val.comp continuous_snd))⟩
  have he_cont : Continuous e := @UniformSpace.Completion.continuous_extension
    R _ (AdicCompletion I R) (adicCompletionUniformSpace I)
    (f := AdicCompletion.of I R) (adicCompletionComplete I)
  have he_coe : ∀ a : R, e (↑a) = AdicCompletion.of I R a := fun a =>
    AbstractCompletion.compare_coe
      UniformSpace.Completion.cPkg (adicAbstractCompletion I hadic) a
  exact {
    toFun := e
    invFun := e_inv
    left_inv := fun x => congr_fun (AbstractCompletion.inverse_compare
      (adicAbstractCompletion I hadic) UniformSpace.Completion.cPkg) x
    right_inv := fun x => congr_fun (AbstractCompletion.inverse_compare
      UniformSpace.Completion.cPkg (adicAbstractCompletion I hadic)) x
    map_mul' := fun x y => by
      refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
      · exact isClosed_eq (he_cont.comp continuous_mul)
          ((he_cont.comp continuous_fst).mul (he_cont.comp continuous_snd))
      · intro a b
        rw [← UniformSpace.Completion.coe_mul, he_coe, he_coe, he_coe]
        exact map_mul (algebraMap R (AdicCompletion I R)) a b
    map_add' := fun x y => by
      refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
      · exact isClosed_eq (he_cont.comp continuous_add)
          ((he_cont.comp continuous_fst).add (he_cont.comp continuous_snd))
      · intro a b
        rw [show (↑a : UniformSpace.Completion R) + ↑b = ↑(a + b) from
          (map_add UniformSpace.Completion.coeRingHom a b).symm,
          he_coe, he_coe, he_coe, map_add (AdicCompletion.of I R)]
  }

end Bridge

/-! ### Ring equivalence for abstract completions -/

/-- A complete T₂ commutative ring S with a dense uniform-inducing ring hom
from R is ring-isomorphic to `Completion R`. The forward map is `extensionHom g`
(a ring hom by construction); the inverse is the AbstractCompletion comparison.
Bijectivity follows from the comparison being a two-sided inverse. -/
noncomputable def completionRingEquiv
    {R : Type*} [CommRing R] [UniformSpace R] [IsTopologicalRing R]
    [IsUniformAddGroup R]
    {S : Type*} [CommRing S] [UniformSpace S] [IsTopologicalRing S]
    [IsUniformAddGroup S] [T2Space S] [CompleteSpace S]
    (g : R →+* S) (hg_cont : Continuous g) (hg_ui : IsUniformInducing g)
    (hg_dense : DenseRange g) : UniformSpace.Completion R ≃+* S := by
  let f := UniformSpace.Completion.extensionHom g hg_cont
  let pkg : AbstractCompletion R :=
    ⟨S, g, inferInstance, inferInstance, inferInstance, hg_ui, hg_dense⟩
  letI := (@UniformSpace.Completion.cPkg R _).uniformStruct
  haveI := (@UniformSpace.Completion.cPkg R _).complete
  haveI := (@UniformSpace.Completion.cPkg R _).separation
  let f_inv : S → UniformSpace.Completion R :=
    pkg.compare UniformSpace.Completion.cPkg
  have hf_inv_coe : ∀ a : R, f_inv (g a) = (↑a : UniformSpace.Completion R) :=
    AbstractCompletion.compare_coe pkg UniformSpace.Completion.cPkg
  have hf_coe : ∀ a : R, f (↑a) = g a :=
    UniformSpace.Completion.extensionHom_coe _ _
  have hf_cont : Continuous f := UniformSpace.Completion.continuous_extension
  have hf_inv_cont : Continuous f_inv :=
    (AbstractCompletion.uniformContinuous_compare pkg
      UniformSpace.Completion.cPkg).continuous
  exact {
    f with
    invFun := f_inv
    left_inv := fun x => by
      change f_inv (f x) = x
      refine UniformSpace.Completion.induction_on x ?_ ?_
      · exact isClosed_eq (hf_inv_cont.comp hf_cont) continuous_id
      · intro a; rw [hf_coe, hf_inv_coe]
    right_inv := congr_fun (hg_dense.equalizer (hf_cont.comp hf_inv_cont)
      continuous_id (funext fun a => by
        simp [Function.comp, hf_inv_coe, hf_coe]))
  }

/-- **Coe property of `completionRingEquiv`**: on the dense image of `R`, the
forward map equals `g`. Matches `UniformSpace.Completion.extensionHom_coe`. -/
theorem completionRingEquiv_coe
    {R : Type*} [CommRing R] [UniformSpace R] [IsTopologicalRing R]
    [IsUniformAddGroup R]
    {S : Type*} [CommRing S] [UniformSpace S] [IsTopologicalRing S]
    [IsUniformAddGroup S] [T2Space S] [CompleteSpace S]
    (g : R →+* S) (hg_cont : Continuous g) (hg_ui : IsUniformInducing g)
    (hg_dense : DenseRange g) (a : R) :
    completionRingEquiv g hg_cont hg_ui hg_dense (↑a) = g a :=
  UniformSpace.Completion.extensionHom_coe g hg_cont a

/-- **Coe property of `adicCompletionRingEquiv`**: on the dense image of `R`,
the forward map equals `AdicCompletion.of I R`. Matches
`AbstractCompletion.compare_coe`. -/
theorem adicCompletionRingEquiv_coe {R' : Type*} [CommRing R'] [UniformSpace R']
    [IsTopologicalRing R'] [IsUniformAddGroup R'] (I' : Ideal R') (hadic : IsAdic I')
    (a : R') :
    adicCompletionRingEquiv I' hadic (↑a) = AdicCompletion.of I' R' a :=
  AbstractCompletion.compare_coe UniformSpace.Completion.cPkg
    (adicAbstractCompletion I' hadic) a

/-! ### Kernel identity for evalₐ -/

/-- In the adic completion of a Noetherian ring, the kernel of the evaluation
at level `n` equals the ideal generated by the image of `I^n`. -/
theorem ker_evalₐ_eq {R : Type*} [CommRing R] (I : Ideal R)
    [IsNoetherianRing R] (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ I n) =
    Ideal.map (algebraMap R (AdicCompletion I R)) (I ^ n) := by
  apply le_antisymm
  · intro x hx; rw [RingHom.mem_ker] at hx
    have hxn : x.val n = 0 := by
      unfold AdicCompletion.evalₐ at hx
      simp only [AlgHom.comp_apply] at hx
      exact (Ideal.quotientEquivAlgOfEq R (ideal_smul_top_eq_self I n)).injective
        (hx.trans (map_zero _).symm)
    have hmkQ : AdicCompletion.map I (I ^ n • ⊤ : Submodule R R).mkQ x = 0 := by
      apply AdicCompletion.ext; intro m
      change (I ^ n • ⊤ : Submodule R R).mkQ.reduceModIdeal (I ^ m) (x.val m) = 0
      rcases le_or_gt m n with hmn | hmn
      · rw [show x.val m = AdicCompletion.transitionMap I R hmn (x.val n) from
          (x.property hmn).symm, hxn, map_zero, map_zero]
      · obtain ⟨r, hr_eq⟩ := Submodule.Quotient.mk_surjective _ (x.val m)
        have hr_mem : r ∈ (I ^ n • ⊤ : Submodule R R) := by
          rw [← Submodule.Quotient.mk_eq_zero]
          have hT : AdicCompletion.transitionMap I R (le_of_lt hmn) (x.val m) = 0 := by
            rw [x.property (le_of_lt hmn)]; exact hxn
          rw [← hr_eq] at hT
          simpa [AdicCompletion.transitionMap_ideal_mk] using hT
        have h1 : (I ^ n • ⊤ : Submodule R R).mkQ r = 0 :=
          (Submodule.Quotient.mk_eq_zero _).mpr hr_mem
        rw [show x.val m = Submodule.Quotient.mk r from hr_eq.symm]
        change Submodule.Quotient.mk ((I ^ n • ⊤ : Submodule R R).mkQ r) = 0
        rw [h1]; rfl
    obtain ⟨z, rfl⟩ : x ∈ Set.range
        (AdicCompletion.map I (I ^ n • ⊤ : Submodule R R).subtype) := by
      rwa [← AdicCompletion.map_exact (I := I) Subtype.val_injective
        (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _)]
    obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I _ z
    refine TensorProduct.inductionOn t ?_ ?_
    · intro c a
      rw [AdicCompletion.ofTensorProduct_tmul, map_smul, AdicCompletion.map_of]
      have ha_mem : (a : R) ∈ (I ^ n : Ideal R) := by
        simpa only [ideal_smul_top_eq_self] using a.2
      exact Ideal.mul_mem_left _ c (Ideal.mem_map_of_mem _ ha_mem)
    · intro _ _ h1 h2; simp only [map_add]; exact Ideal.add_mem _ h1 h2
  · rw [Ideal.map_le_iff_le_comap]; intro a ha
    simp only [Ideal.mem_comap, RingHom.mem_ker]
    change (AdicCompletion.evalₐ I n) (AdicCompletion.of I R a) = 0
    rw [AdicCompletion.evalₐ_of]; exact Ideal.Quotient.eq_zero_iff_mem.mpr ha

/-- **[T-KS1-A]** The `I`-adic completion of a surjection is a surjection (Stacks 10.96.1(2),
tag 0315 — **noeth-free**, no finiteness on `M`/`N`). Linchpin of the noeth-free
`ker_evalₐ_eq_of_fg` (Stacks 05GG): the genuine content is that the kernel tower
`K/(K ∩ IᵏM)` (`K = ker f`) has surjective transitions (quotients of a fixed `K`), so the
inverse limit of the levelwise-surjective `f mod Iᵏ` is surjective — NO non-f.g.-syzygy obstruction.
Mathlib upstreamable. -/
theorem map_surjective_of_surjective {R : Type*} [CommRing R] (I : Ideal R)
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Function.Surjective (AdicCompletion.map I f) := by
  classical
  intro y
  obtain ⟨b, rfl⟩ := AdicCompletion.mk_surjective I N y
  have hmaptop : Submodule.map f ⊤ = ⊤ := by
    rw [Submodule.map_top, LinearMap.range_eq_top]; exact hf
  have hmap : ∀ j : ℕ,
      Submodule.map f (I ^ j • ⊤ : Submodule R M) = (I ^ j • ⊤ : Submodule R N) := by
    intro j; rw [Submodule.map_smul'', hmaptop]
  have hδ : ∀ j : ℕ, ∃ d : M, d ∈ (I ^ j • ⊤ : Submodule R M) ∧ f d = b (j + 1) - b j := by
    intro j
    have hb : (b (j + 1) - b j) ∈ (I ^ j • ⊤ : Submodule R N) :=
      SModEq.sub_mem.mp (b.2 (Nat.le_succ j)).symm
    rw [← hmap j, Submodule.mem_map] at hb
    exact hb
  obtain ⟨a₀, ha₀f⟩ := hf (b 0)
  set δ : ℕ → M := fun j => (hδ j).choose with hδdef
  have hδmem : ∀ j, δ j ∈ (I ^ j • ⊤ : Submodule R M) := fun j => (hδ j).choose_spec.1
  have hδf : ∀ j, f (δ j) = b (j + 1) - b j := fun j => (hδ j).choose_spec.2
  set a : ℕ → M := fun k => a₀ + ∑ j ∈ Finset.range k, δ j with hadef
  have haf : ∀ k, f (a k) = b k := by
    intro k
    simp only [hadef, map_add, map_sum, ha₀f, hδf]
    rw [Finset.sum_range_sub (fun j => (b : ℕ → N) j)]
    abel
  have hCauchy : AdicCompletion.IsAdicCauchy I M a := by
    intro m n hmn
    rw [SModEq.sub_mem]
    have hsub : a m - a n = - ∑ j ∈ Finset.Ico m n, δ j := by
      simp only [hadef]
      rw [← Finset.sum_range_add_sum_Ico δ hmn]; abel
    rw [hsub]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun j hj => ?_)
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Finset.mem_Ico.mp hj).1) (hδmem j)
  let c : AdicCompletion.AdicCauchySequence I M := ⟨a, hCauchy⟩
  refine ⟨AdicCompletion.mk I M c, ?_⟩
  rw [AdicCompletion.map_mk]
  congr 1
  ext k
  simp only [AdicCompletion.AdicCauchySequence.map_apply_coe]
  exact haf k

/-- **Step 1 of the noeth-free Stacks 05GG kernel identity** (`ker_evalₐ_eq_of_fg`).
The kernel of the level-`n` adic-completion evaluation map is contained in the range of the
completed inclusion of the submodule `Iⁿ • ⊤` of `R`. **No finiteness hypothesis on `I`.**
Proof (Cauchy-shift): for `x = mk c ∈ ker`, `c n ∈ Iⁿ•⊤`, hence `c k ∈ Iⁿ•⊤` for all `k ≥ n`,
so the shifted sequence `d k = c (k + n)` is `IsAdicCauchy` in `↥(Iⁿ•⊤)` and
`map subtype (mk d) = mk c = x`. -/
theorem ker_evalₐ_le_range_map_subtype {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ)
    {x : AdicCompletion I R} (hx : x ∈ RingHom.ker (AdicCompletion.evalₐ I n)) :
    x ∈ LinearMap.range
      (AdicCompletion.map I (Submodule.subtype (I ^ n • ⊤ : Submodule R R))) := by
  classical
  obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective I R x
  set p : Submodule R R := I ^ n • ⊤ with hp
  -- `c.val n ∈ Iⁿ•⊤` from `mk c ∈ ker(evalₐ n)`.
  have hcn : c.val n ∈ p := by
    have h0 : AdicCompletion.evalₐ I n (AdicCompletion.mk I R c) = 0 := RingHom.mem_ker.mp hx
    rw [AdicCompletion.evalₐ_mk] at h0
    simpa [hp] using Ideal.Quotient.eq_zero_iff_mem.mp h0
  -- hence `c.val k ∈ Iⁿ•⊤` for all `k ≥ n` (Cauchy).
  have hck : ∀ k, n ≤ k → c.val k ∈ p := by
    intro k hk
    have h1 : c.val k - c.val n ∈ p := SModEq.sub_mem.mp (c.2 hk).symm
    have he : c.val k = (c.val k - c.val n) + c.val n := by abel
    rw [he]; exact Submodule.add_mem _ h1 hcn
  -- the shifted sequence `d k = c.val (k+n)`, Cauchy in the submodule `Iⁿ•⊤`.
  let d : ℕ → ↥p := fun k => ⟨c.val (k + n), hck (k + n) (Nat.le_add_left n k)⟩
  have hd : AdicCompletion.IsAdicCauchy I ↥p d := by
    intro m m' hmm
    rw [SModEq.sub_mem, Submodule.mem_smul_top_iff]
    have hsmul : (I ^ m • p : Submodule R R) = I ^ (m + n) • ⊤ := by
      rw [hp, ← mul_smul, ← pow_add]
    have hco : ((d m - d m' : ↥p) : R) = c.val (m + n) - c.val (m' + n) := rfl
    rw [hco, hsmul]
    exact SModEq.sub_mem.mp (c.2 (by omega : m + n ≤ m' + n))
  -- `map subtype (mk d) = mk c` by shift-invariance.
  let shifted : AdicCompletion.AdicCauchySequence I ↥p := ⟨d, hd⟩
  refine ⟨AdicCompletion.mk I ↥p shifted, ?_⟩
  rw [AdicCompletion.map_mk]
  refine AdicCompletion.ext fun k => ?_
  rw [AdicCompletion.mk_apply_coe, AdicCompletion.mk_apply_coe]
  simp only [AdicCompletion.AdicCauchySequence.map_apply_coe, Submodule.coe_subtype]
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  exact SModEq.sub_mem.mp (c.2 (Nat.le_add_right k n)).symm

/-- **Step 2 of the noeth-free Stacks 05GG kernel identity** (`ker_evalₐ_eq_of_fg`).
For a **finitely generated** ideal `I` (so `Iⁿ • ⊤` is f.g.), the range of the completed inclusion
of `Iⁿ • ⊤` lands in `(Iⁿ)·Â = Ideal.map (algebraMap R Â) (Iⁿ)`.
Proof: pick a finite generating family of `Iⁿ`, corestrict the surjection `Rʳ ↠ Iⁿ•⊤`, apply
`map_surjective_of_surjective`, and expand `map I φ = ∑ wᵢ • map I (proj i)` as an `R`-combination
of elements of the image of `algebraMap`. -/
theorem range_map_subtype_le_map_pow_of_fg {R : Type*} [CommRing R] (I : Ideal R) (hI : I.FG)
    (n : ℕ) (z : AdicCompletion I R)
    (hz : z ∈ LinearMap.range
      (AdicCompletion.map I (Submodule.subtype (I ^ n • ⊤ : Submodule R R)))) :
    z ∈ Ideal.map (algebraMap R (AdicCompletion I R)) (I ^ n) := by
  classical
  have hpfg : (I ^ n • ⊤ : Submodule R R).FG := by
    have he : (I ^ n • ⊤ : Submodule R R) = (I ^ n : Ideal R) := by simp
    rw [he]; exact Submodule.FG.pow hI n
  obtain ⟨r, w, hw⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hpfg
  have hwmem : ∀ i, w i ∈ (I ^ n : Ideal R) := fun i => by
    have hmem : w i ∈ (I ^ n • ⊤ : Submodule R R) := hw ▸ Submodule.subset_span ⟨i, rfl⟩
    simpa using hmem
  set φ : (Fin r → R) →ₗ[R] R := ∑ i, w i • LinearMap.proj i with hφdef
  have hφrange : ∀ c, φ c ∈ (I ^ n • ⊤ : Submodule R R) := by
    intro c
    rw [← hw, hφdef]
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, smul_eq_mul]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [mul_comm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hφsingle : ∀ i, φ (Pi.single i 1) = w i := by
    intro i
    simp only [hφdef, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ i]
    simp
  have hσsurj : Function.Surjective (LinearMap.codRestrict _ φ hφrange) := by
    rintro ⟨y, hy⟩
    rw [← hw] at hy
    have hsub : Submodule.span R (Set.range w) ≤ LinearMap.range φ := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨Pi.single i 1, hφsingle i⟩
    obtain ⟨c, hc⟩ := hsub hy
    exact ⟨c, Subtype.ext (by rw [LinearMap.codRestrict_apply]; exact hc)⟩
  have hdecomp : ∀ η : AdicCompletion I (Fin r → R),
      AdicCompletion.map I φ η
        = ∑ i, w i • AdicCompletion.map I (LinearMap.proj i) η := by
    intro η
    obtain ⟨e, rfl⟩ := AdicCompletion.mk_surjective I _ η
    simp only [AdicCompletion.map_mk, ← map_smul, ← map_sum]
    congr 1
    apply Subtype.ext
    funext m
    simp only [AdicCompletion.AdicCauchySequence.map_apply_coe, hφdef, LinearMap.coe_sum,
      Finset.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
    rw [show (∑ x, (AdicCompletion.AdicCauchySequence.map I (LinearMap.proj x)) (w x • e)) m
          = ∑ x, ((AdicCompletion.AdicCauchySequence.map I (LinearMap.proj x)) (w x • e)) m
        from ?_]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [AdicCompletion.AdicCauchySequence.map_apply_coe, LinearMap.proj_apply,
        AdicCompletion.AdicCauchySequence.smul_apply, Pi.smul_apply, smul_eq_mul]
    · exact map_sum (AddMonoidHom.mk' (fun g : AdicCompletion.AdicCauchySequence I R => g m)
          (fun a b => AdicCompletion.AdicCauchySequence.add_apply m a b))
        (fun x => (AdicCompletion.AdicCauchySequence.map I (LinearMap.proj x)) (w x • e))
        Finset.univ
  obtain ⟨xt, rfl⟩ := hz
  obtain ⟨η, rfl⟩ :=
    map_surjective_of_surjective I (LinearMap.codRestrict _ φ hφrange) hσsurj xt
  rw [AdicCompletion.map_comp_apply, LinearMap.subtype_comp_codRestrict, hdecomp η]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hwmem i))

/-- **Noeth-free, finitely-generated version of `ker_evalₐ_eq`**
(Wedhorn Prop 5.37(2), wedhorn.txt:1903 / Bourbaki [BouAC] III §2.12).

For a **finitely generated** ideal `I`,
`ker(AdicCompletion.evalₐ I n) = (Iⁿ)·Â`.

`ker_evalₐ_eq` (above) proves the hard inclusion via `AdicCompletion.map_exact`, which Mathlib
states with `[IsNoetherianRing R]`. But the identity holds noeth-free for f.g. `I` (Prop 5.37),
and this is the faithful form the project's `presheafValue_isAdic` needs — `locIdeal` is f.g.
noeth-free (`locIdeal_fg = P.fg.map _`), so threading `[IsNoetherianRing (locSubring)]` through the
whole `presheafValue` adic-structure chain is a tool-choice artifact, not a mathematical necessity
(and that hypothesis is ℂ_p-false: the ring of definition of ℂ_p is not noetherian).

* **Easy inclusion `(Iⁿ)·Â ≤ ker`** — proven below, noeth-free.
* **Hard inclusion `ker ≤ (Iⁿ)·Â`** — `sorry`. This is the only step in `ker_evalₐ_eq`'s proof that
  uses more than `Module.Finite (Iⁿ•⊤)` (which `hI` supplies via `Ideal.FG.pow`): the single
  `AdicCompletion.map_exact` call establishing `ker(map mkQ) = range(map subtype)` for the SES
  `0 → Iⁿ → R → R/Iⁿ → 0`.

  **Discharge route (Stacks 10.96.3, tag 05GG — verbatim noeth-free,
  via `map_surjective_of_surjective`).**
  Stacks: `IⁿM^∧ = Ker(M^∧ → M/IⁿM) = (IⁿM)^∧`. For `M = R`: `ker(evalₐ I n) = Iⁿ·Â`.
  The earlier "solution-set Sₘ with surjective transitions" route was WRONG (those transitions are
  NOT surjective; ℤ_p counterexample in `b2_log.jsonl`). The correct inverse system is the kernel
  tower, handled noeth-free by `map_surjective_of_surjective`. Two steps:
  * **Step 1** `ker(evalₐ n) ≤ range(map I (subtype (Iⁿ•⊤)))`: for `x = mk c ∈ ker`, `c_n ∈ Iⁿ•⊤`,
    so `c_m ∈ Iⁿ•⊤` for all `m ≥ n` (Cauchy). The **shifted** sequence `d_m := c_{m+n} ∈ Iⁿ•⊤` is
    `IsAdicCauchy` *in the submodule* `Iⁿ•⊤` because `d_m − d_{m'} ∈ I^{m+n}•⊤ = Iᵐ•(Iⁿ•⊤)`
    (ideal-smul composes — NO Artin-Rees). Then `xLift := mk_{Iⁿ•⊤} d` satisfies
    `map I subtype xLift = x`.
  * **Step 2** `range(map I subtype) ≤ Iⁿ·Â`: `map_surjective_of_surjective` on the corestriction
    `Rʳ ↠ Iⁿ•⊤` (gens of `Iⁿ`) writes `xLift = map I ψ' η`, so `x = map I (subtype∘ψ') η = map I
      ψ η`,
    and `map I ψ` is `R`-linear in `ψ = Σ gᵢ•projᵢ`, so `x = Σ gᵢ•(…) ∈ Iⁿ·Â`. -/
theorem ker_evalₐ_eq_of_fg {R : Type*} [CommRing R] (I : Ideal R) (hI : I.FG) (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ I n) =
    Ideal.map (algebraMap R (AdicCompletion I R)) (I ^ n) := by
  apply le_antisymm
  · -- HARD inclusion, Stacks 05GG (noeth-free). `p := Iⁿ•⊤` as a submodule of `R`.
    intro x hx
    exact range_map_subtype_le_map_pow_of_fg I hI n x
      (ker_evalₐ_le_range_map_subtype I n hx)
  · rw [Ideal.map_le_iff_le_comap]; intro a ha
    simp only [Ideal.mem_comap, RingHom.mem_ker]
    change (AdicCompletion.evalₐ I n) (AdicCompletion.of I R a) = 0
    rw [AdicCompletion.evalₐ_of]; exact Ideal.Quotient.eq_zero_iff_mem.mpr ha

end AdicCompletionBridge
