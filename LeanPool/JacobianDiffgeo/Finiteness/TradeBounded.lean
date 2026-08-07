/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Finiteness.Chain
import LeanPool.JacobianDiffgeo.DolbeaultComparison.Leray

/-!
# The norm-bounded trade (`finiteness-and-chi`, gated file 1/3)

Unit: finiteness-and-chi (`docs/design/finiteness-and-chi.md` §4.4, §4.5, proof plan §5, §6.3
step 5). This is the first of the three files that were blocked on the cech `Colimit`/`Window`/
`Skyscraper` gate and dolbeault's `Leray.lean` gate — both are now open.

* `isCompactOperator_resZ_UV`/`isCompactOperator_tradeCompact` (§4.4, still owed from
  `Chain.lean`/`CompactRestrict.lean`): the finite-`Pi` assembly of Montel compactness into the
  cocycle-level `U → V` restriction and the `tradeCompact` Schwartz leg.
* `toGermZ1`/`boundZ1`: the Banach ↔ Čech germ bridges at a fixed level (D5).
* `tradePi_surjective` (Forster 14.6(a) upgraded to the Banach layer): the trade projection is
  onto — the Schwartz surjectivity input.
* `classMap`/`classMap_tradeDiff_eq_zero`/`classMap_surjective`: the Čech class map and its two
  Schwartz-consumer properties.
-/

open scoped ContDiff Manifold BoundedContinuousFunction
open Set Filter Topology TopologicalSpace Metric RS.Cech

namespace RS.Finiteness

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### §4.4: the compact-operator assembly (owed from `Chain.lean`/`CompactRestrict.lean`) -/

section CompactAssembly

variable [T1Space X] [T2Space X] [CompactSpace X]

/-- A finite `Pi` of compact operators (all sharing the same domain) is a compact operator. -/
theorem isCompactOperator_pi {ι : Type*} [Finite ι] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℂ (F i)]
    (f : ∀ i, E →L[ℂ] F i) (hf : ∀ i, IsCompactOperator (f i)) :
    IsCompactOperator (ContinuousLinearMap.pi f) := by
  choose K hKcompact hKmem using hf
  refine ⟨Set.pi Set.univ K, isCompact_univ_pi hKcompact, ?_⟩
  have heq : (ContinuousLinearMap.pi f) ⁻¹' (Set.pi Set.univ K) = ⋂ i, (f i) ⁻¹' (K i) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_iInter,
      ContinuousLinearMap.pi_apply]
  rw [heq]
  exact Filter.iInter_mem.2 hKmem

variable (T : ShrinkChain X)

omit [T1Space X] [T2Space X] [CompactSpace X] in
theorem resZ_apply_coe {P P' : Fin T.n → Opens X} (h : ∀ i, P' i ≤ P i) (x : NZ1 T P) :
    (resZ T P P' h x : NC1 T P') = resNC1 T P P' h (x : NC1 T P) := rfl

omit [IsManifold 𝓘(ℂ, ℂ) ω X] [T1Space X] [T2Space X] [CompactSpace X] in
/-- Closure of a same-index-pair meet: `closure (P₁ i ⊓ P₁ j) ⊆ closure (P₁ i) ∩ closure (P₁ j)`,
specialized to the `V ⊓ V ⊆ closure ⊆ U ⊓ U` shape needed for the Montel input. -/
private theorem closure_inf_pair_subset {P₁ P₂ : Fin T.n → Opens X}
    (h : ∀ i, closure (P₁ i : Set X) ⊆ (P₂ i : Set X)) (i j : Fin T.n) :
    closure ((P₁ i ⊓ P₁ j : Opens X) : Set X) ⊆ ((P₂ i ⊓ P₂ j : Opens X) : Set X) := by
  simp only [Opens.coe_inf]
  exact closure_inter_subset.trans (Set.inter_subset_inter (h i) (h j))

omit [T1Space X] [T2Space X] [CompactSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
private theorem inf_pair_subset_chart_source (i j : Fin T.n) :
    ((T.U i ⊓ T.U j : Opens X) : Set X) ⊆ (chartAt ℂ (T.c i)).source := by
  rw [Opens.coe_inf]
  exact (Set.inter_subset_left.trans (T.U_subset_Ustar i)).trans (T.Ustar_subset_source i)

omit [T1Space X] [T2Space X] in
theorem isCompactOperator_resNC1_U_V : IsCompactOperator (resNC1 T T.U T.V T.V_le_U) := by
  change IsCompactOperator (ContinuousLinearMap.pi (fun p : Fin T.n × Fin T.n =>
    (restrictCLM (inf_le_inf (T.V_le_U p.1) (T.V_le_U p.2))).comp (ContinuousLinearMap.proj p)))
  apply isCompactOperator_pi
  intro p
  exact (isCompactOperator_restrictCLM (X := X) (S := T.U p.1 ⊓ T.U p.2)
    (S' := T.V p.1 ⊓ T.V p.2) (x₀ := T.c p.1) (inf_pair_subset_chart_source T p.1 p.2)
    (closure_inf_pair_subset T T.closure_V_subset p.1 p.2)).comp_clm
    (ContinuousLinearMap.proj p : NC1 T T.U →L[ℂ] BddHoloOn (T.U p.1 ⊓ T.U p.2))

omit [T1Space X] [T2Space X] in
/-- **§4.4**: the finite-`Pi` Montel assembly of the cocycle-level `U → V` restriction. -/
theorem isCompactOperator_resZ_UV : IsCompactOperator (resZ T T.U T.V T.V_le_U) := by
  have hval : IsCompactOperator (fun x : NZ1 T T.U => (resZ T T.U T.V T.V_le_U x : NC1 T T.V)) := by
    have heq : (fun x : NZ1 T T.U => (resZ T T.U T.V T.V_le_U x : NC1 T T.V)) =
        (resNC1 T T.U T.V T.V_le_U) ∘ (fun x : NZ1 T T.U => (x : NC1 T T.U)) := by
      funext x
      exact resZ_apply_coe T T.V_le_U x
    rw [heq]
    exact (isCompactOperator_resNC1_U_V T).comp_clm (NZ1 T T.U).subtypeL
  exact isCompactOperator_of_isCompactOperator_val (ContinuousLinearMap.isClosed_ker (d1NC T T.V))
    (resZ T T.U T.V T.V_le_U) hval

omit [T1Space X] [T2Space X] in
/-- **§4.4**: the Montel-compact leg of the Schwartz cospan. -/
theorem isCompactOperator_tradeCompact : IsCompactOperator (tradeCompact T) := by
  have heq : (tradeCompact T : tradeSpace T → NZ1 T T.V) =
      (resZ T T.U T.V T.V_le_U) ∘
        ((ContinuousLinearMap.fst ℂ (NZ1 T T.U) (NZ1 T T.V × NC0 T T.W)).comp
          (tradeSpace T).subtypeL) := rfl
  rw [heq]
  exact (isCompactOperator_resZ_UV T).comp_clm _

end CompactAssembly

/-! ### Compat: `evalAt` arithmetic missing from `Meromorphic/OrderEval.lean` -/

section EvalAtCompat

variable [T1Space X]

omit [T1Space X] in
theorem MeroGermOn.evalAt_neg {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U)
    {φ : RS.MeroGermOn X U} (h : 0 ≤ φ.ord x) : (-φ).evalAt x = -(φ.evalAt x) := by
  rw [← neg_one_smul ℂ φ, RS.MeroGermOn.evalAt_smul hU hx h, neg_one_mul]

omit [T1Space X] in
theorem MeroGermOn.evalAt_sub {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U)
    {φ ψ : RS.MeroGermOn X U} (h1 : 0 ≤ φ.ord x) (h2 : 0 ≤ ψ.ord x) :
    (φ - ψ).evalAt x = φ.evalAt x - ψ.evalAt x := by
  rw [sub_eq_add_neg, RS.MeroGermOn.evalAt_add hU hx h1 (by rw [RS.MeroGermOn.ord_neg]; exact h2),
    MeroGermOn.evalAt_neg hU hx h2, sub_eq_add_neg]

omit [T1Space X] in
theorem MeroGermOn.evalAt_zero {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U) :
    (0 : RS.MeroGermOn X U).evalAt x = 0 := by
  rw [← RS.MeroGermOn.mk_zero]
  exact RS.MeroGermOn.evalAt_mk_of_contMDiffAt hU hx contMDiffAt_const

omit [IsManifold 𝓘(ℂ, ℂ) ω X] [T1Space X] in
/-- `LinSysOn 0`-membership gives `0 ≤ ord` unconditionally (D=0's own zero divisor). -/
theorem LinSysOn.ord_nonneg {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U)
    (φ : RS.LinSysOn (0 : RS.Divisor X) U) : 0 ≤ (φ : RS.MeroGermOn X U).ord x := by
  have h := (RS.mem_linSysOn_iff_of_isOpen hU).1 φ.2 x hx
  have h0 : ((0 : RS.Divisor X) x : ℤ) = 0 := by
    simp [Function.locallyFinsuppWithin.coe_zero]
  rwa [h0, neg_zero] at h

omit [T1Space X] in
/-- The "repr\_cocycle" pattern (dolbeault §6.2): a `Z1`-cocycle relation, evaluated pointwise. -/
theorem Z1.rel_res_evalAt {𝒰 : FinCover (⊤ : Opens X)} {f : C1 (0 : RS.Divisor X) 𝒰}
    (hf : f ∈ Z1 (0 : RS.Divisor X) 𝒰) (a b c : Fin 𝒰.n) {z : X}
    (hbc : z ∈ (𝒰.U b ⊓ 𝒰.U c : Opens X)) (hac : z ∈ (𝒰.U a ⊓ 𝒰.U c : Opens X))
    (hab : z ∈ (𝒰.U a ⊓ 𝒰.U b : Opens X)) :
    (f (b, c) : RS.MeroGermOn X (𝒰.U b ⊓ 𝒰.U c : Set X)).evalAt z
      - (f (a, c) : RS.MeroGermOn X (𝒰.U a ⊓ 𝒰.U c : Set X)).evalAt z
      + (f (a, b) : RS.MeroGermOn X (𝒰.U a ⊓ 𝒰.U b : Set X)).evalAt z = 0 := by
  have hopen : IsOpen ((𝒰.U a ⊓ 𝒰.U b ⊓ 𝒰.U c : Opens X) : Set X) := (𝒰.U a ⊓ 𝒰.U b ⊓ 𝒰.U c).2
  have hzabc : z ∈ (𝒰.U a ⊓ 𝒰.U b ⊓ 𝒰.U c : Opens X) := ⟨hab, hbc.2⟩
  have hbc' : (𝒰.U a ⊓ 𝒰.U b ⊓ 𝒰.U c : Opens X) ≤ 𝒰.U b ⊓ 𝒰.U c :=
    le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hac' : (𝒰.U a ⊓ 𝒰.U b ⊓ 𝒰.U c : Opens X) ≤ 𝒰.U a ⊓ 𝒰.U c :=
    le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hab' : (𝒰.U a ⊓ 𝒰.U b ⊓ 𝒰.U c : Opens X) ≤ 𝒰.U a ⊓ 𝒰.U b := inf_le_left
  have hzero : d1 (0 : RS.Divisor X) 𝒰 f (a, b, c) = 0 := (mem_Z1_iff _ _ _).1 hf (a, b, c)
  rw [d1_apply] at hzero
  have hcoe : RS.MeroGermOn.restrict hbc' (f (b, c) : RS.MeroGermOn X (𝒰.U b ⊓ 𝒰.U c : Set X))
      - RS.MeroGermOn.restrict hac' (f (a, c) : RS.MeroGermOn X (𝒰.U a ⊓ 𝒰.U c : Set X))
      + RS.MeroGermOn.restrict hab' (f (a, b) : RS.MeroGermOn X (𝒰.U a ⊓ 𝒰.U b : Set X)) = 0 := by
    have hcast := congrArg Subtype.val hzero
    exact hcast
  have hnn_A : 0 ≤ (RS.MeroGermOn.restrict hbc' (f (b, c) :
      RS.MeroGermOn X (𝒰.U b ⊓ 𝒰.U c : Set X))).ord z := by
    rw [RS.MeroGermOn.ord_restrict hbc' hopen (𝒰.U b ⊓ 𝒰.U c).2 hzabc]
    exact LinSysOn.ord_nonneg (𝒰.U b ⊓ 𝒰.U c).2 hbc (f (b, c))
  have hnn_B : 0 ≤ (RS.MeroGermOn.restrict hac' (f (a, c) :
      RS.MeroGermOn X (𝒰.U a ⊓ 𝒰.U c : Set X))).ord z := by
    rw [RS.MeroGermOn.ord_restrict hac' hopen (𝒰.U a ⊓ 𝒰.U c).2 hzabc]
    exact LinSysOn.ord_nonneg (𝒰.U a ⊓ 𝒰.U c).2 hac (f (a, c))
  have hnn_C : 0 ≤ (RS.MeroGermOn.restrict hab' (f (a, b) :
      RS.MeroGermOn X (𝒰.U a ⊓ 𝒰.U b : Set X))).ord z := by
    rw [RS.MeroGermOn.ord_restrict hab' hopen (𝒰.U a ⊓ 𝒰.U b).2 hzabc]
    exact LinSysOn.ord_nonneg (𝒰.U a ⊓ 𝒰.U b).2 hab (f (a, b))
  have hnn_AB : 0 ≤ (RS.MeroGermOn.restrict hbc' (f (b, c) :
        RS.MeroGermOn X (𝒰.U b ⊓ 𝒰.U c : Set X))
      - RS.MeroGermOn.restrict hac'
          (f (a, c) : RS.MeroGermOn X (𝒰.U a ⊓ 𝒰.U c : Set X))).ord z := by
    rw [sub_eq_add_neg]
    refine le_trans (le_min hnn_A ?_)
      (RS.MeroGermOn.ord_add hopen hzabc _ (-RS.MeroGermOn.restrict hac'
        (f (a, c) : RS.MeroGermOn X (𝒰.U a ⊓ 𝒰.U c : Set X))))
    rw [RS.MeroGermOn.ord_neg]
    exact hnn_B
  have heval : (RS.MeroGermOn.restrict hbc' (f (b, c) : RS.MeroGermOn X (𝒰.U b ⊓ 𝒰.U c : Set X))
        - RS.MeroGermOn.restrict hac' (f (a, c) : RS.MeroGermOn X (𝒰.U a ⊓ 𝒰.U c : Set X))).evalAt z
      + (RS.MeroGermOn.restrict hab' (f (a, b) :
          RS.MeroGermOn X (𝒰.U a ⊓ 𝒰.U b : Set X))).evalAt z = 0 := by
    rw [← MeroGermOn.evalAt_add hopen hzabc hnn_AB hnn_C, hcoe, MeroGermOn.evalAt_zero hopen hzabc]
  rw [MeroGermOn.evalAt_sub hopen hzabc hnn_A hnn_B] at heval
  rwa [RS.MeroGermOn.evalAt_restrict hbc' hopen (𝒰.U b ⊓ 𝒰.U c).2 hzabc,
    RS.MeroGermOn.evalAt_restrict hac' hopen (𝒰.U a ⊓ 𝒰.U c).2 hzabc,
    RS.MeroGermOn.evalAt_restrict hab' hopen (𝒰.U a ⊓ 𝒰.U b).2 hzabc] at heval

end EvalAtCompat

/-! ### §5: the germ ↔ Banach bridges at a cover level (D5) -/

section GermBridge

variable [T1Space X]

/-- Germification into the `LinSysOn 0` submodule (D5, bundled linear form of `toGerm`). -/
noncomputable def toGermSub (S : Opens X) :
    BddHoloOn S →ₗ[ℂ] RS.LinSysOn (0 : RS.Divisor X) (S : Set X) :=
  LinearMap.codRestrict _ (toGerm S) (fun f => toGerm_mem_linSysOn f)

omit [T1Space X] in
theorem toGermSub_apply_coe (S : Opens X) (f : BddHoloOn S) :
    (toGermSub S f : RS.MeroGermOn X (S : Set X)) = toGerm S f := rfl

omit [T1Space X] in
theorem toGermSub_restrictCLM_comm {S' S : Opens X} (h : S' ≤ S) (f : BddHoloOn S) :
    toGermSub S' (restrictCLM h f) = LinSysOn.restrictL (0 : RS.Divisor X) h (toGermSub S f) := by
  apply Subtype.ext
  rw [toGermSub_apply_coe, restrictL_apply_coe, toGermSub_apply_coe, toGerm_restrict_comm]

variable (T : ShrinkChain X)

/-- The `FinCover (⊤ : Opens X)` induced by a `ShrinkChain`-indexed family `P` (generic form of
`T.coverU`/`T.coverV`/`T.coverW`; kept separate from those concrete defs so that this section's
lemmas typecheck for a bare `P : Fin T.n → Opens X` without needing `𝒰.n` to be *syntactically*
`T.n` — a genuine dependent-type obstruction for a free `𝒰 : FinCover (⊤ : Opens X)` variable).
`T.coverU`/`T.coverV`/`T.coverW` are `rfl`-equal to `coverOfP T.U T.covers_U` etc. (same fields,
`Prop`-irrelevant `covers` witness), so this is used transparently at call sites. -/
@[reducible] noncomputable def coverOfP (P : Fin T.n → Opens X) (hcov : ∀ x, ∃ i, x ∈ P i) :
    FinCover (⊤ : Opens X) where
  n := T.n
  U := P
  le_base _ := le_top
  covers x _ := hcov x

/-- Germification of a `P`-indexed `1`-cochain of `BddHoloOn`s (§5 step 3). -/
noncomputable def toGermC1 (P : Fin T.n → Opens X) :
    NC1 T P →ₗ[ℂ] ∀ p : Fin T.n × Fin T.n, RS.LinSysOn (0 : RS.Divisor X)
        ((P p.1 ⊓ P p.2 : Opens X) : Set X) :=
  LinearMap.pi fun p => (toGermSub (P p.1 ⊓ P p.2)).comp (LinearMap.proj p)

omit [T1Space X] in
theorem toGermC1_apply (P : Fin T.n → Opens X) (f : NC1 T P) (p : Fin T.n × Fin T.n) :
    toGermC1 T P f p = toGermSub (P p.1 ⊓ P p.2) (f p) := rfl

omit [T1Space X] in
theorem toGermC1_mem_Z1 (P : Fin T.n → Opens X) (hcov : ∀ x, ∃ i, x ∈ P i)
    {f : NC1 T P} (hf : f ∈ NZ1 T P) :
    toGermC1 T P f ∈ Z1 (0 : RS.Divisor X) (coverOfP T P hcov) := by
  refine (mem_Z1_iff (0 : RS.Divisor X) (coverOfP T P hcov) (toGermC1 T P f)).2 ?_
  rintro ⟨a, b, c⟩
  apply Subtype.ext
  have hz : d1NC T P f (a, b, c) = 0 := (mem_NZ1_iff T P f).1 hf (a, b, c)
  rw [d1NC_apply] at hz
  rw [d1_apply]
  simp only [ZeroMemClass.coe_zero, Submodule.coe_add, Submodule.coe_sub,
    restrictL_apply_coe, toGermC1_apply, toGermSub_apply_coe]
  have hz' := congrArg (toGerm (P a ⊓ P b ⊓ P c)) hz
  simp only [map_sub, map_add, map_zero, toGerm_restrict_comm] at hz'
  exact hz'

/-- Germification of bounded cocycles into `Z1 0 (coverOfP T P hcov)`, bundled linear
(§5 step 3). -/
noncomputable def toGermZ1 (P : Fin T.n → Opens X) (hcov : ∀ x, ∃ i, x ∈ P i) :
    NZ1 T P →ₗ[ℂ] Z1 (0 : RS.Divisor X) (coverOfP T P hcov) :=
  LinearMap.codRestrict _ ((toGermC1 T P).comp (NZ1 T P).subtype)
    (fun ξ => toGermC1_mem_Z1 T P hcov ξ.2)

omit [T1Space X] in
theorem toGermZ1_apply_coe (P : Fin T.n → Opens X) (hcov : ∀ x, ∃ i, x ∈ P i) (ξ : NZ1 T P) :
    (toGermZ1 T P hcov ξ : C1 (0 : RS.Divisor X) (coverOfP T P hcov)) = toGermC1 T P (ξ : NC1 T P)
        :=
  rfl

variable [T2Space X] [CompactSpace X]

/-- De-germification of a good-cover cocycle down onto a `⋐`-nested level (§5 step 5). -/
noncomputable def boundZ1 {P : Fin T.n → Opens X}
    (h : ∀ i, closure (P i : Set X) ⊆ (T.Ustar i : Set X))
    (F : Z1 (0 : RS.Divisor X) T.coverStar) : NC1 T P :=
  fun p => restrictGerm (closure_inf_pair_subset T h p.1 p.2)
    ((F : C1 (0 : RS.Divisor X) T.coverStar) (p.1, p.2))

/-- The `(i, j)`-component of a good-cover cocycle, as a `LinSysOn`-membership term (a named
helper: writing the `LinSysOn`-then-`MeroGermOn` coercion inline as a single doubly-nested type
ascription hits a hard `isDefEq` rejection — `T.coverStar.U i ⊓ T.coverStar.U j` vs
`T.Ustar i ⊓ T.Ustar j` — that a two-step named unfolding avoids entirely; see the build log for
the diagnosis). -/
noncomputable def starPairMem (F : Z1 (0 : RS.Divisor X) T.coverStar) (i j : Fin T.n) :
    RS.LinSysOn (0 : RS.Divisor X) ((T.Ustar i ⊓ T.Ustar j : Opens X) : Set X) :=
  (F : C1 (0 : RS.Divisor X) T.coverStar) (i, j)

/-- The `(i, j)` component of a `coverStar`-level cocycle, as a germ. -/
noncomputable def starPairGerm (F : Z1 (0 : RS.Divisor X) T.coverStar) (i j : Fin T.n) :
    RS.MeroGermOn X ((T.Ustar i ⊓ T.Ustar j : Opens X) : Set X) :=
  starPairMem T F i j

omit [T1Space X] [T2Space X] in
theorem boundZ1_apply_eq_evalAt {P : Fin T.n → Opens X}
    (h : ∀ i, closure (P i : Set X) ⊆ (T.Ustar i : Set X)) (F : Z1 (0 : RS.Divisor X) T.coverStar)
    (i j : Fin T.n) (z : ↥((P i ⊓ P j : Opens X) : Set X)) :
    (boundZ1 T h F (i, j) : ↥((P i ⊓ P j : Opens X) : Set X) →ᵇ ℂ) z =
      (starPairGerm T F i j).evalAt (z : X) := by
  rw [boundZ1, restrictGerm_apply]
  rfl

omit [T1Space X] [T2Space X] in
/-- **§5 step 5's `NZ1`-membership**: the de-germified cochain is a genuine bounded cocycle
(the "repr\_cocycle" pattern: evaluate `F`'s germ cocycle relation pointwise). -/
theorem boundZ1_mem_NZ1 {P : Fin T.n → Opens X}
    (h : ∀ i, closure (P i : Set X) ⊆ (T.Ustar i : Set X)) (F : Z1 (0 : RS.Divisor X) T.coverStar) :
    boundZ1 T h F ∈ NZ1 T P := by
  rw [mem_NZ1_iff]
  rintro ⟨a, b, c⟩
  rw [d1NC_apply]
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro z
  simp only [Submodule.coe_add, Submodule.coe_sub, ZeroMemClass.coe_zero,
    BoundedContinuousFunction.coe_add, BoundedContinuousFunction.coe_sub, Pi.add_apply,
    Pi.sub_apply, BoundedContinuousFunction.coe_zero, Pi.zero_apply, restrictCLM_apply_coe]
  rw [boundZ1_apply_eq_evalAt, boundZ1_apply_eq_evalAt, boundZ1_apply_eq_evalAt]
  have hzP : (z : X) ∈ (P a ⊓ P b ⊓ P c : Opens X) := z.2
  have hza : (z : X) ∈ P a := hzP.1.1
  have hzb : (z : X) ∈ P b := hzP.1.2
  have hzc : (z : X) ∈ P c := hzP.2
  have hzUa : (z : X) ∈ T.Ustar a := (subset_closure.trans (h a)) hza
  have hzUb : (z : X) ∈ T.Ustar b := (subset_closure.trans (h b)) hzb
  have hzUc : (z : X) ∈ T.Ustar c := (subset_closure.trans (h c)) hzc
  exact Z1.rel_res_evalAt F.2 a b c ⟨hzUb, hzUc⟩ ⟨hzUa, hzUc⟩ ⟨hzUa, hzUb⟩

/-- De-germification of a `0`-cochain down onto the `W`-level (§5 step 5, second half). -/
noncomputable def boundZ1C0 (g : C0 (0 : RS.Divisor X) T.coverV) : NC0 T T.W :=
  fun i => restrictGerm (T.closure_W_subset i) ((g : C0 (0 : RS.Divisor X) T.coverV) i)

/-- The `i`-component of a `T.coverV`-level `0`-cochain, as a `LinSysOn`-membership term (same
two-step naming device as `starPairMem`/`starPairGerm`). -/
noncomputable def vMem (g : C0 (0 : RS.Divisor X) T.coverV) (i : Fin T.n) :
    RS.LinSysOn (0 : RS.Divisor X) (T.V i : Set X) :=
  (g : C0 (0 : RS.Divisor X) T.coverV) i

/-- The `i`-th component of a `coverV`-level cochain, as a germ. -/
noncomputable def vGerm (g : C0 (0 : RS.Divisor X) T.coverV) (i : Fin T.n) :
    RS.MeroGermOn X (T.V i : Set X) :=
  vMem T g i

omit [T1Space X] [T2Space X] in
theorem boundZ1C0_apply_eq_evalAt (g : C0 (0 : RS.Divisor X) T.coverV) (i : Fin T.n)
    (z : ↥((T.W i : Set X))) :
    (boundZ1C0 T g i : ↥(T.W i : Set X) →ᵇ ℂ) z = (vGerm T g i).evalAt (z : X) := by
  rw [boundZ1C0, restrictGerm_apply]
  rfl

omit [T2Space X] [CompactSpace X] [T1Space X] in
/-- **The trade equation, evaluated pointwise** (the "repr\_cocycle" pattern applied to
`exists_trade`'s conclusion): reads off a scalar identity relating the good-cover cocycle `F`,
the traded cocycle `f`, and the coboundary witness `g` at a point. Reused for both
`tradePi_surjective` (§5 steps 5–6, at level `V`) and `classMap_surjective` (§5 step 9, at
level `W`). -/
theorem trade_evalAt {𝒱 : FinCover (⊤ : Opens X)} {τ : Fin 𝒱.n → Fin T.n}
    (hτ : IsRefIdx T.coverStar 𝒱 τ) (F : Z1 (0 : RS.Divisor X) T.coverStar)
    (f : C1 (0 : RS.Divisor X) 𝒱) (g : C0 (0 : RS.Divisor X) 𝒱)
    (hFg : (resZ1 (0 : RS.Divisor X) τ hτ F : C1 (0 : RS.Divisor X) 𝒱) = f + d0 (0 : RS.Divisor X)
        𝒱 g)
    (α β : Fin 𝒱.n) {z : X} (hz : z ∈ (𝒱.U α ⊓ 𝒱.U β : Opens X)) :
    (starPairGerm T F (τ α) (τ β)).evalAt z =
      (f (α, β) : RS.MeroGermOn X (𝒱.U α ⊓ 𝒱.U β : Set X)).evalAt z
        + ((g β : RS.MeroGermOn X (𝒱.U β : Set X)).evalAt z
          - (g α : RS.MeroGermOn X (𝒱.U α : Set X)).evalAt z) := by
  have hLopen : IsOpen ((𝒱.U α ⊓ 𝒱.U β : Opens X) : Set X) := (𝒱.U α ⊓ 𝒱.U β).2
  have hza : (z : X) ∈ 𝒱.U α := hz.1
  have hzb : (z : X) ∈ 𝒱.U β := hz.2
  have hpt : (resZ1 (0 : RS.Divisor X) τ hτ F : C1 (0 : RS.Divisor X) 𝒱) (α, β) =
      f (α, β) + d0 (0 : RS.Divisor X) 𝒱 g (α, β) := congrFun hFg (α, β)
  rw [resZ1_apply_coe, resC1_apply, d0_apply] at hpt
  have hcoe := congrArg Subtype.val hpt
  simp only [Submodule.coe_add, Submodule.coe_sub, restrictL_apply_coe] at hcoe
  have hnn_f : 0 ≤ (f (α, β) : RS.MeroGermOn X (𝒱.U α ⊓ 𝒱.U β : Set X)).ord z :=
    LinSysOn.ord_nonneg hLopen hz (f (α, β))
  have hnn_gb : 0 ≤ (g β : RS.MeroGermOn X (𝒱.U β : Set X)).ord z :=
    LinSysOn.ord_nonneg (𝒱.U β).2 hzb (g β)
  have hnn_ga : 0 ≤ (g α : RS.MeroGermOn X (𝒱.U α : Set X)).ord z :=
    LinSysOn.ord_nonneg (𝒱.U α).2 hza (g α)
  have hnn_gb' : 0 ≤ (RS.MeroGermOn.restrict (inf_le_right : 𝒱.U α ⊓ 𝒱.U β ≤ 𝒱.U β)
      (g β : RS.MeroGermOn X (𝒱.U β : Set X))).ord z := by
    rw [RS.MeroGermOn.ord_restrict inf_le_right hLopen (𝒱.U β).2 hz]; exact hnn_gb
  have hnn_ga' : 0 ≤ (RS.MeroGermOn.restrict (inf_le_left : 𝒱.U α ⊓ 𝒱.U β ≤ 𝒱.U α)
      (g α : RS.MeroGermOn X (𝒱.U α : Set X))).ord z := by
    rw [RS.MeroGermOn.ord_restrict inf_le_left hLopen (𝒱.U α).2 hz]; exact hnn_ga
  have hnn_sub : 0 ≤ (RS.MeroGermOn.restrict (inf_le_right : 𝒱.U α ⊓ 𝒱.U β ≤ 𝒱.U β) (g β :
        RS.MeroGermOn X (𝒱.U β : Set X))
      - RS.MeroGermOn.restrict (inf_le_left : 𝒱.U α ⊓ 𝒱.U β ≤ 𝒱.U α) (g α :
        RS.MeroGermOn X (𝒱.U α : Set X))).ord z := by
    rw [sub_eq_add_neg]
    refine le_trans (le_min hnn_gb' ?_) (RS.MeroGermOn.ord_add hLopen hz _ _)
    rw [RS.MeroGermOn.ord_neg]
    exact hnn_ga'
  have hcongr := congrArg (fun ψ : RS.MeroGermOn X ((𝒱.U α ⊓ 𝒱.U β : Opens X) : Set X) =>
    ψ.evalAt z) hcoe
  rw [MeroGermOn.evalAt_add hLopen hz hnn_f hnn_sub,
    MeroGermOn.evalAt_sub hLopen hz hnn_gb' hnn_ga',
    RS.MeroGermOn.evalAt_restrict inf_le_right hLopen (𝒱.U β).2 hz,
    RS.MeroGermOn.evalAt_restrict inf_le_left hLopen (𝒱.U α).2 hz] at hcongr
  rw [RS.MeroGermOn.evalAt_restrict (inf_le_inf (hτ α) (hτ β)) hLopen
    (T.Ustar (τ α) ⊓ T.Ustar (τ β)).2 hz] at hcongr
  exact hcongr

end GermBridge

/-! ### §5 steps 4–6: `tradePi_surjective` (the qualitative trade, Banach layer) -/

variable [T1Space X] [T2Space X] [CompactSpace X] (T : ShrinkChain X)

/-- The germified `V`-level cocycle `c` viewed at `T.coverV` directly (same two-step naming
device as `starPairMem`/`starPairGerm`, needed since `coverOfP T T.V T.covers_V` and `T.coverV`
are `rfl`-equal but the coercion chain `Z1 → C1 → (ascribe)` cannot be nested inline). -/
noncomputable def cC1 (ξ : NZ1 T T.V) : C1 (0 : RS.Divisor X) T.coverV :=
  (toGermZ1 T T.V T.covers_V ξ : C1 (0 : RS.Divisor X) (coverOfP T T.V T.covers_V))

/-- Membership witness for the `(α, β)` component of a norm-bounded cocycle. -/
noncomputable def cCompMem (ξ : NZ1 T T.V) (α β : Fin T.n) :
    RS.LinSysOn (0 : RS.Divisor X) ((T.V α ⊓ T.V β : Opens X) : Set X) :=
  cC1 T ξ (α, β)

/-- The `(α, β)` component of a norm-bounded cocycle, as a `LinSysOn` element. -/
noncomputable def cComp (ξ : NZ1 T T.V) (α β : Fin T.n) :
    RS.MeroGermOn X ((T.V α ⊓ T.V β : Opens X) : Set X) :=
  cCompMem T ξ α β

omit [T2Space X] [CompactSpace X] [T1Space X] in
theorem cComp_eq (ξ : NZ1 T T.V) (α β : Fin T.n) :
    cComp T ξ α β = toGerm (T.V α ⊓ T.V β) ((ξ : NC1 T T.V) (α, β)) := by
  rw [cComp, cCompMem, cC1, toGermZ1_apply_coe, toGermC1_apply, toGermSub_apply_coe]

omit [T1Space X] in
/-- **§5's centerpiece**: the trade projection `π : L →L Z¹(𝔙)` is onto (Forster 14.6(a) upgraded
to the Banach layer). -/
theorem tradePi_surjective (T : ShrinkChain X) : Function.Surjective (tradePi T) := by
  intro ξ
  obtain ⟨F, g, hFg⟩ := exists_trade (𝒰 := T.coverStar) (𝒱 := T.coverV) (D := (0 : RS.Divisor X))
    (h𝒰 := T.good_star) (hτ := T.ref_star_V) (τ := id) (f := toGermZ1 T T.V T.covers_V ξ)
  have hζmem : boundZ1 T T.closure_U_subset F ∈ NZ1 T T.U := boundZ1_mem_NZ1 T T.closure_U_subset F
  set ζ : NZ1 T T.U := ⟨boundZ1 T T.closure_U_subset F, hζmem⟩ with hζ_def
  set η : NC0 T T.W := boundZ1C0 T g with hη_def
  have hmem : (ζ, ξ, η) ∈ tradeSpace T := by
    rw [mem_tradeSpace_iff_eq]
    rintro ⟨α, β⟩
    apply Subtype.ext
    apply BoundedContinuousFunction.ext
    intro z
    simp only [Submodule.coe_add, Submodule.coe_sub, BoundedContinuousFunction.coe_add,
      BoundedContinuousFunction.coe_sub, Pi.add_apply, Pi.sub_apply, restrictCLM_apply_coe]
    have hzeq : (ζ.1 : NC1 T T.U) (α, β) = boundZ1 T T.closure_U_subset F (α, β) := rfl
    rw [hzeq, boundZ1_apply_eq_evalAt]
    have hηβ : η β = boundZ1C0 T g β := rfl
    have hηα : η α = boundZ1C0 T g α := rfl
    rw [hηβ, hηα, boundZ1C0_apply_eq_evalAt, boundZ1C0_apply_eq_evalAt]
    have hξeval : ((ξ : NC1 T T.V) (α, β) : ↥((T.V α ⊓ T.V β : Set X)) →ᵇ ℂ)
        (Set.inclusion (inf_le_inf (T.W_le_V α) (T.W_le_V β)) z) =
        (toGerm (T.V α ⊓ T.V β) ((ξ : NC1 T T.V) (α, β))).evalAt
          ((Set.inclusion (inf_le_inf (T.W_le_V α) (T.W_le_V β)) z : X)) :=
      (evalAt_toGerm ((ξ : NC1 T T.V) (α, β))
        (Set.inclusion (inf_le_inf (T.W_le_V α) (T.W_le_V β)) z).2).symm
    rw [hξeval]
    rw [← cComp_eq]
    exact trade_evalAt T T.ref_star_V F (cC1 T ξ) g hFg α β
      ⟨(Set.inclusion (inf_le_inf (T.W_le_V α) (T.W_le_V β)) z).2.1,
        (Set.inclusion (inf_le_inf (T.W_le_V α) (T.W_le_V β)) z).2.2⟩
  exact ⟨⟨(ζ, ξ, η), hmem⟩, rfl⟩

/-! ### §5 steps 8–9: `classMap` and the two Schwartz-consumer properties -/

omit [T1Space X] [T2Space X] [CompactSpace X] in
/-- Composition law for the Banach-level restriction (mirrors `resZ1_comp`/`resC1_comp`). -/
theorem resZ_resZ {P P' P'' : Fin T.n → Opens X} (h1 : ∀ i, P' i ≤ P i) (h2 : ∀ i, P'' i ≤ P' i)
    (h3 : ∀ i, P'' i ≤ P i) (x : NZ1 T P) :
    resZ T P' P'' h2 (resZ T P P' h1 x) = resZ T P P'' h3 x := by
  apply Subtype.ext
  funext p
  rw [resZ_apply_coe, resZ_apply_coe, resZ_apply_coe, resNC1_apply, resNC1_apply, resNC1_apply,
    restrictCLM_restrictCLM]

/-- Germification of a `P`-indexed `0`-cochain (needed for `classMap`'s coboundary witness). -/
noncomputable def toGermC0 (P : Fin T.n → Opens X) :
    NC0 T P →ₗ[ℂ] ∀ i : Fin T.n, RS.LinSysOn (0 : RS.Divisor X) ((P i : Opens X) : Set X) :=
  LinearMap.pi fun i => (toGermSub (P i)).comp (LinearMap.proj i)

omit [T2Space X] [CompactSpace X] [T1Space X] in
theorem toGermC0_apply (P : Fin T.n → Opens X) (h : NC0 T P) (i : Fin T.n) :
    toGermC0 T P h i = toGermSub (P i) (h i) := rfl

omit [T2Space X] [CompactSpace X] [T1Space X] in
/-- Naturality: germifying a `0`-cochain then taking its cover-level coboundary agrees with
germifying the Banach-level coboundary (§5 step 8's "`toGermZ1 ∘ δ_W = d0 ∘ toGermC0`"). -/
theorem toGermC1_deltaCLM_eq_d0 (η : NC0 T T.W) (p : Fin T.n × Fin T.n) :
    toGermC1 T T.W (deltaCLM T T.W η) p =
      d0 (0 : RS.Divisor X) T.coverW (toGermC0 T T.W η) p := by
  rw [toGermC1_apply, deltaCLM_apply, map_sub, toGermSub_restrictCLM_comm,
    toGermSub_restrictCLM_comm, d0_apply, toGermC0_apply, toGermC0_apply]

/-- The `toGermZ1`-image of a `T.W`-level bounded cocycle, viewed at `T.coverW` directly (same
two-step naming device as `cC1`). -/
noncomputable def toGermZ1W (ψ : NZ1 T T.W) : Z1 (0 : RS.Divisor X) T.coverW :=
  (toGermZ1 T T.W T.covers_W ψ : Z1 (0 : RS.Divisor X) (coverOfP T T.W T.covers_W))

omit [T2Space X] [CompactSpace X] [T1Space X] in
theorem toGermZ1W_apply_coe (ψ : NZ1 T T.W) :
    (toGermZ1W T ψ : C1 (0 : RS.Divisor X) T.coverW) = toGermC1 T T.W (ψ : NC1 T T.W) := rfl

/-- **The Čech class map** (§5 step 8): bound `V`-level cocycles down to `W`, germify, take the
Mittag-Leffler class. -/
noncomputable def classMap : NZ1 T T.V →ₗ[ℂ] H1Cover (0 : RS.Divisor X) T.coverW :=
  (H1Cover.mk (0 : RS.Divisor X) T.coverW).comp
    ({ toFun := fun ψ => toGermZ1W T ψ
       map_add' := fun ψ ψ' => by
         apply Subtype.ext
         rw [toGermZ1W_apply_coe]
         simp only [Submodule.coe_add]
         rw [map_add, toGermZ1W_apply_coe, toGermZ1W_apply_coe]
       map_smul' := fun c ψ => by
         apply Subtype.ext
         rw [toGermZ1W_apply_coe]
         simp only [Submodule.coe_smul, RingHom.id_apply]
         rw [map_smul, toGermZ1W_apply_coe]
         } ∘ₗ (resZ T T.V T.W T.W_le_V))

omit [T2Space X] [CompactSpace X] [T1Space X] in
theorem classMap_apply (ψ : NZ1 T T.V) :
    classMap T ψ = H1Cover.mk (0 : RS.Divisor X) T.coverW
        (toGermZ1W T (resZ T T.V T.W T.W_le_V ψ)) :=
  rfl

omit [T2Space X] [CompactSpace X] [T1Space X] in
/-- The trade defect, restricted to `W`, is minus the coboundary of `x`'s `W`-component.

Split out of `classMap_tradeDiff_eq_zero`: the two halves together exceed the default heartbeat
budget, and as separate declarations each elaborates well inside it. -/
private theorem resZ_tradeDiff_eq_neg_deltaCLM (x : tradeSpace T) :
    (resZ T T.V T.W T.W_le_V (tradePi T x - tradeCompact T x) : NC1 T T.W) =
      -(deltaCLM T T.W x.1.2.2) := by
  have hxmem := (mem_tradeSpace_iff_eq T x.1).1 x.2
  rw [map_sub]
  funext p
  obtain ⟨α, β⟩ := p
  simp only [Submodule.coe_sub, Pi.sub_apply, Pi.neg_apply]
  rw [tradePi_apply]
  have hcomp : resZ T T.V T.W T.W_le_V (tradeCompact T x) = resZ T T.U T.W T.W_le_U x.1.1 := by
    rw [tradeCompact_apply, resZ_resZ]
  rw [hcomp, resZ_apply_coe, resZ_apply_coe, resNC1_apply, resNC1_apply, deltaCLM_apply]
  have e1 := hxmem (α, β)
  rw [e1]
  abel

omit [T2Space X] [CompactSpace X] [T1Space X] in
/-- **Schwartz-consumer property 1** (§5 step 8): the trade defect dies in `H¹(𝔚)`. -/
theorem classMap_tradeDiff_eq_zero (x : tradeSpace T) :
    classMap T (tradePi T x - tradeCompact T x) = 0 := by
  have hkey := resZ_tradeDiff_eq_neg_deltaCLM T x
  simp only [classMap_apply, H1Cover.mk_eq_zero_iff]
  refine ⟨-(toGermC0 T T.W x.1.2.2), ?_⟩
  rw [toGermZ1W_apply_coe, hkey]
  have hd0neg : d0 (0 : RS.Divisor X) T.coverW (-(toGermC0 T T.W x.1.2.2)) =
      -(d0 (0 : RS.Divisor X) T.coverW (toGermC0 T T.W x.1.2.2)) := map_neg _ _
  have htgneg : toGermC1 T T.W (-(deltaCLM T T.W x.1.2.2)) =
      -(toGermC1 T T.W (deltaCLM T T.W x.1.2.2)) := map_neg _ _
  rw [hd0neg, htgneg]
  congr 1
  funext p
  exact (toGermC1_deltaCLM_eq_d0 T x.1.2.2 p).symm

omit [T1Space X] [T2Space X] in
/-- Restriction commutes with `boundZ1` (Banach-level restriction of a de-germified good-cover
cocycle equals de-germifying with the transitively-composed closure hypothesis). -/
theorem resZ_boundZ1 {P P' : Fin T.n → Opens X}
    (h : ∀ i, closure (P i : Set X) ⊆ (T.Ustar i : Set X)) (h' : ∀ i, P' i ≤ P i)
    (h2 : ∀ i, closure (P' i : Set X) ⊆ (T.Ustar i : Set X))
        (F : Z1 (0 : RS.Divisor X) T.coverStar) :
    resZ T P P' h' ⟨boundZ1 T h F, boundZ1_mem_NZ1 T h F⟩ =
      (⟨boundZ1 T h2 F, boundZ1_mem_NZ1 T h2 F⟩ : NZ1 T P') := by
  apply Subtype.ext
  funext p
  obtain ⟨i, j⟩ := p
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro z
  rw [resZ_apply_coe, resNC1_apply]
  change (boundZ1 T h F (i, j) : ↥((P i ⊓ P j : Opens X) : Set X) →ᵇ ℂ)
      (Set.inclusion (inf_le_inf (h' i) (h' j)) z) =
    (boundZ1 T h2 F (i, j) : ↥((P' i ⊓ P' j : Opens X) : Set X) →ᵇ ℂ) z
  rw [boundZ1_apply_eq_evalAt, boundZ1_apply_eq_evalAt]

/-- The `(i, j)`-component of a `T.coverW`-level `Z1` element, as a `LinSysOn`-membership term
(same two-step naming device as `starPairMem`/`starPairGerm`). -/
noncomputable def wPairMem (c : Z1 (0 : RS.Divisor X) T.coverW) (i j : Fin T.n) :
    RS.LinSysOn (0 : RS.Divisor X) ((T.W i ⊓ T.W j : Opens X) : Set X) :=
  (c : C1 (0 : RS.Divisor X) T.coverW) (i, j)

/-- The `(i, j)` component of a `coverW`-level cocycle, as a germ. -/
noncomputable def wPairGerm (c : Z1 (0 : RS.Divisor X) T.coverW) (i j : Fin T.n) :
    RS.MeroGermOn X ((T.W i ⊓ T.W j : Opens X) : Set X) :=
  wPairMem T c i j

omit [T2Space X] [T1Space X] in
/-- The germ roundtrip: germifying the `T.W`-level de-germified `F` recovers `F`'s own germ
restriction down to `T.coverW` (`resZ1 0 id T.ref_star_W F`). -/
theorem toGermZ1W_boundZ1 (h : ∀ i, closure (T.W i : Set X) ⊆ (T.Ustar i : Set X))
    (F : Z1 (0 : RS.Divisor X) T.coverStar) :
    (toGermZ1W T ⟨boundZ1 T h F, boundZ1_mem_NZ1 T h F⟩ : C1 (0 : RS.Divisor X) T.coverW) =
      (resZ1 (𝒰 := T.coverStar) (𝒱 := T.coverW) (0 : RS.Divisor X) id T.ref_star_W F : C1 (0 :
          RS.Divisor X) T.coverW) := by
  rw [toGermZ1W_apply_coe]
  funext p
  obtain ⟨i, j⟩ := p
  change toGermSub (T.W i ⊓ T.W j) (boundZ1 T h F (i, j)) = _
  apply Subtype.ext
  rw [toGermSub_apply_coe]
  change toGerm (T.W i ⊓ T.W j) (boundZ1 T h F (i, j)) =
    wPairGerm T (resZ1 (𝒰 := T.coverStar) (𝒱 := T.coverW) (0 : RS.Divisor X) id T.ref_star_W F) i j
  rw [wPairGerm, wPairMem, boundZ1, toGerm_restrictGerm, resZ1_apply_coe, resC1_apply,
    restrictL_apply_coe]
  rfl

omit [T1Space X] in
/-- **§5's second centerpiece**: `classMap` is surjective (§5 step 9). -/
theorem classMap_surjective : Function.Surjective (classMap T) := by
  intro c'
  obtain ⟨c, hc⟩ := H1Cover.mk_surjective (0 : RS.Divisor X) T.coverW c'
  obtain ⟨F, g, hFg⟩ := exists_trade (𝒰 := T.coverStar) (𝒱 := T.coverW) (D := (0 : RS.Divisor X))
    (h𝒰 := T.good_star) (hτ := T.ref_star_W) (τ := id) (f := c)
  have hWUstar : ∀ i, closure (T.W i : Set X) ⊆ (T.Ustar i : Set X) :=
    fun i => (T.closure_W_subset i).trans ((T.V_subset_U i).trans (T.U_subset_Ustar i))
  have hVUstar : ∀ i, closure (T.V i : Set X) ⊆ (T.Ustar i : Set X) :=
    fun i => (T.closure_V_subset i).trans (T.U_subset_Ustar i)
  set ξF : NZ1 T T.V := ⟨boundZ1 T hVUstar F, boundZ1_mem_NZ1 T hVUstar F⟩ with hξF_def
  refine ⟨ξF, ?_⟩
  rw [classMap_apply, ← hc]
  have hresZ : resZ T T.V T.W T.W_le_V ξF = ⟨boundZ1 T hWUstar F, boundZ1_mem_NZ1 T hWUstar F⟩ :=
    resZ_boundZ1 T hVUstar T.W_le_V hWUstar F
  rw [hξF_def, hresZ]
  have hrt := toGermZ1W_boundZ1 T hWUstar F
  have hd0mem : d0 (0 : RS.Divisor X) T.coverW g ∈ Z1 (0 : RS.Divisor X) T.coverW :=
    B1_le_Z1 (0 : RS.Divisor X) T.coverW ⟨g, rfl⟩
  have hsplit : (toGermZ1W T ⟨boundZ1 T hWUstar F, boundZ1_mem_NZ1 T hWUstar F⟩ :
      Z1 (0 : RS.Divisor X) T.coverW) = c + (⟨d0 (0 : RS.Divisor X) T.coverW g, hd0mem⟩ :
        Z1 (0 : RS.Divisor X) T.coverW) := by
    apply Subtype.ext
    rw [hrt]
    simp only [Submodule.coe_add]
    exact hFg
  rw [hsplit, map_add]
  have hmk0 : H1Cover.mk (0 : RS.Divisor X) T.coverW
      (⟨d0 (0 : RS.Divisor X) T.coverW g, hd0mem⟩ : Z1 (0 : RS.Divisor X) T.coverW) = 0 := by
    rw [H1Cover.mk_eq_zero_iff]
    exact ⟨g, rfl⟩
  rw [hmk0, add_zero]

end RS.Finiteness
