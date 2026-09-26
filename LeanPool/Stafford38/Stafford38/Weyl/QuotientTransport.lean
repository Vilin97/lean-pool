/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Quotient.EulerSurjectivity
public import LeanPool.Stafford38.Stafford38.Weyl.EulerRemainder
public import LeanPool.Stafford38.Stafford38.Weyl.IteratedEquivalence


/-!
# Transport of the canonical right quotient

The recursive Ore tower and the presented Weyl algebra are related by an
algebra equivalence.  This file transports the *literal* two-generator right
ideal and its right quotient across that equivalence.  The final theorem is
the presented-Weyl form of the already proved `PairStage` surjectivity.
-/

@[expose] public section

namespace Stafford38.WeylQuotientTransport

open Stafford38.EulerSurjectivity
open Stafford38.OreIteratedPairStage
open Stafford38.OrePairStage
open Stafford38.WeylEulerRemainder
open Stafford38.WeylEulerResidue
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBWMonicBridge
open Stafford38.WeylUniversal

noncomputable section

universe u

variable {k : Type u} [Field k]

/-! ## Right-module transport -/

instance rightModuleEquiv_invPair {A B : Type*} [Ring A] [Ring B]
    [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B) :
    RingHomInvPair
      ((AlgEquiv.op e).toRingEquiv : Aᵐᵒᵖ →+* Bᵐᵒᵖ)
      ((AlgEquiv.op e).toRingEquiv.symm : Bᵐᵒᵖ →+* Aᵐᵒᵖ) :=
  RingHomInvPair.of_ringEquiv (AlgEquiv.op e).toRingEquiv

instance rightModuleEquiv_invPair_symm {A B : Type*} [Ring A] [Ring B]
    [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B) :
    RingHomInvPair
      ((AlgEquiv.op e).toRingEquiv.symm : Bᵐᵒᵖ →+* Aᵐᵒᵖ)
      ((AlgEquiv.op e).toRingEquiv : Aᵐᵒᵖ →+* Bᵐᵒᵖ) :=
  RingHomInvPair.of_ringEquiv (AlgEquiv.op e).toRingEquiv.symm

/-- The algebra equivalence, regarded as a semilinear equivalence of regular
right modules.  The scalar ring is transported on opposites. -/
def rightModuleEquiv {A B : Type*} [Ring A] [Ring B] [Algebra k A]
    [Algebra k B] (e : A ≃ₐ[k] B) :
    @LinearEquiv Aᵐᵒᵖ Bᵐᵒᵖ _ _ (AlgEquiv.op e).toRingEquiv
      (AlgEquiv.op e).toRingEquiv.symm _ _ A B _ _ _ _ :=
  { e.toAddEquiv with
    map_smul' := by
      intro c a
      change e (a * c.unop) = e a * e c.unop
      exact map_mul e a c.unop }

/-- The inverse regular-right-module equivalence, with the inverse opposite
scalar map made explicit for quotient composition. -/
def rightModuleEquivSymm {A B : Type*} [Ring A] [Ring B] [Algebra k A]
    [Algebra k B] (e : A ≃ₐ[k] B) :
    @LinearEquiv Bᵐᵒᵖ Aᵐᵒᵖ _ _ (AlgEquiv.op e).toRingEquiv.symm
      (AlgEquiv.op e).toRingEquiv _ _ B A _ _ _ _ :=
  { e.symm.toAddEquiv with
    map_smul' := by
      intro c b
      change e.symm (b * c.unop) = e.symm b * e.symm c.unop
      exact map_mul e.symm b c.unop }

/-- Image transport of a literal right ideal along an algebra equivalence. -/
def transportedRightIdeal {A B : Type*} [Ring A] [Ring B] [Algebra k A]
    [Algebra k B] (e : A ≃ₐ[k] B) (I : RightIdeal A) : RightIdeal B :=
  { carrier := e '' I
    zero_mem' := by
      exact ⟨0, I.zero_mem, by simp⟩
    add_mem' := by
      rintro y z ⟨y', hy', rfl⟩ ⟨z', hz', rfl⟩
      refine ⟨y' + z', I.add_mem hy' hz', ?_⟩
      simp
    smul_mem' := by
      rintro b y ⟨a, ha, rfl⟩
      let c : Aᵐᵒᵖ := (AlgEquiv.op e).symm b
      refine ⟨c • a, I.smul_mem c ha, ?_⟩
      have h := (rightModuleEquiv e).map_smulₛₗ c a
      calc
        e (c • a) = (AlgEquiv.op e).toRingEquiv c • e a := h
        _ = b • e a := by
          rw [show (AlgEquiv.op e).toRingEquiv c = b by
            exact (AlgEquiv.op e).apply_symm_apply b] }

/-! ## The two generators and quotient -/

/-- The literal canonical right ideal in the presented Weyl algebra. -/
def presentedCanonicalRightIdeal (n N : ℕ) (d : PresentedWeyl k (n + 1)) :
    RightIdeal (PresentedWeyl k (n + 1)) :=
  canonicalRightIdeal (presentedCoordinate k n) d N

/-- Its literal right quotient. -/
abbrev PresentedCanonicalRightQuotient (n N : ℕ)
    (d : PresentedWeyl k (n + 1)) :=
  RightQuotient (presentedCanonicalRightIdeal (k := k) n N d)

theorem transported_canonicalRightIdeal
    {A B : Type*} [Ring A] [Ring B] [Algebra k A] [Algebra k B]
    (e : A ≃ₐ[k] B) (x d : A) (N : ℕ) :
    transportedRightIdeal e (canonicalRightIdeal x d N) =
      canonicalRightIdeal (e x) (e d) N := by
  apply le_antisymm
  · intro y hy
    change y ∈ e '' canonicalRightIdeal x d N at hy
    rcases hy with ⟨z, hz, rfl⟩
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz
      · subst z
        exact firstGenerator_mem (e x) (e d) N
      · subst z
        simpa [map_mul, map_pow] using
          (secondGenerator_mem (e x) (e d) N)
    · simp
    · intro a b ha hb hha hhb
      simpa using (canonicalRightIdeal (e x) (e d) N).add_mem hha hhb
    · intro c a ha hha
      change (rightModuleEquiv e) (c • a) ∈
        canonicalRightIdeal (e x) (e d) N
      rw [(rightModuleEquiv e).map_smulₛₗ c a]
      exact (canonicalRightIdeal (e x) (e d) N).smul_mem _ hha
  · intro y hy
    change y ∈ e '' canonicalRightIdeal x d N
    refine ⟨e.symm y, ?_, by simp⟩
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz
      · subst z
        simpa using (firstGenerator_mem x d N)
      · subst z
        simpa [map_mul, map_pow] using (secondGenerator_mem x d N)
    · simp
    · intro a b ha hb hha hhb
      simpa using (canonicalRightIdeal x d N).add_mem hha hhb
    · intro c a ha hha
      change (rightModuleEquivSymm e) (c • a) ∈
        canonicalRightIdeal x d N
      rw [(rightModuleEquivSymm e).map_smulₛₗ c a]
      exact (canonicalRightIdeal x d N).smul_mem _ hha

theorem presented_canonicalRightIdeal_map
    (n N : ℕ) (d : PresentedWeyl k (n + 1)) :
    transportedRightIdeal (presentedIteratedEquiv k (n + 1))
        (presentedCanonicalRightIdeal (k := k) n N d) =
      canonicalRightIdeal (pairCoordinate (B := IteratedPairStage k n))
        (presentedToIterated k (n + 1) d) N := by
  have h := transported_canonicalRightIdeal
      (e := presentedIteratedEquiv k (n + 1))
      (x := presentedCoordinate k n) (d := d) (N := N)
  change transportedRightIdeal (presentedIteratedEquiv k (n + 1))
      (canonicalRightIdeal (presentedCoordinate k n) d N) = _
  have hx : presentedIteratedEquiv k (n + 1) (presentedCoordinate k n) =
      pairCoordinate (B := IteratedPairStage k n) := by
    change presentedToIterated k (n + 1) (presentedCoordinate k n) =
      pairCoordinate (B := IteratedPairStage k n)
    simpa only [stageCoordinate] using (presentedToIterated_coordinate k n)
  rw [hx] at h
  exact h

/-- The quotient map induced by the transported ideal. -/
def transportedRightQuotientMap {A B : Type*} [Ring A] [Ring B]
    [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B) (I : RightIdeal A) :
    @LinearMap Aᵐᵒᵖ Bᵐᵒᵖ _ _ (AlgEquiv.op e).toRingEquiv
      (RightQuotient I) (RightQuotient (transportedRightIdeal e I)) _ _ _ _ :=
  Submodule.mapQ I (transportedRightIdeal e I) (rightModuleEquiv e) (by
    intro a ha
    exact ⟨a, ha, by rfl⟩)

@[simp]
theorem transportedRightQuotientMap_qmk
    {A B : Type*} [Ring A] [Ring B] [Algebra k A] [Algebra k B]
    (e : A ≃ₐ[k] B) (I : RightIdeal A) (a : A) :
  transportedRightQuotientMap e I (qmk I a) =
      qmk (transportedRightIdeal e I) (e a) := by
  rfl

/-- The quotient equivalence induced by the transported ideal. -/
def transportedRightQuotientEquiv {A B : Type*} [Ring A] [Ring B]
    [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B) (I : RightIdeal A) :
    @LinearEquiv Aᵐᵒᵖ Bᵐᵒᵖ _ _ (AlgEquiv.op e).toRingEquiv
      (AlgEquiv.op e).toRingEquiv.symm _ _
      (RightQuotient I) (RightQuotient (transportedRightIdeal e I)) _ _ _ _ := by
  apply LinearEquiv.ofLinearMap (transportedRightQuotientMap e I)
    (Submodule.mapQ (transportedRightIdeal e I) I
      (rightModuleEquivSymm e) (by
        intro b hb
        change b ∈ e '' I at hb
        rcases hb with ⟨a, ha, rfl⟩
        simpa [rightModuleEquivSymm] using ha))
  · apply LinearMap.ext
    intro q
    refine Submodule.Quotient.induction_on
      (transportedRightIdeal e I) q ?_
    intro b
    change transportedRightQuotientMap e I
        (qmk I (e.symm b)) = qmk (transportedRightIdeal e I) b
    rw [transportedRightQuotientMap_qmk]
    simp
  · apply LinearMap.ext
    intro q
    refine Submodule.Quotient.induction_on I q ?_
    intro a
    simp only [LinearMap.coe_comp, Function.comp_apply]
    change qmk I (e.symm (e a)) = qmk I a
    simp

@[simp]
theorem transportedRightQuotientEquiv_qmk
    {A B : Type*} [Ring A] [Ring B] [Algebra k A] [Algebra k B]
    (e : A ≃ₐ[k] B) (I : RightIdeal A) (a : A) :
    transportedRightQuotientEquiv e I (qmk I a) =
      qmk (transportedRightIdeal e I) (e a) := rfl

theorem transportedRightQuotientEquiv_rightMul
    {A B : Type*} [Ring A] [Ring B] [Algebra k A] [Algebra k B]
    (e : A ≃ₐ[k] B) (I : RightIdeal A) (a : A) (q : RightQuotient I) :
    transportedRightQuotientEquiv e I (rightMul I a q) =
      rightMul (transportedRightIdeal e I) (e a)
        (transportedRightQuotientEquiv e I q) := by
  refine Submodule.Quotient.induction_on I q ?_
  intro b
  change transportedRightQuotientEquiv e I
      (MulOpposite.op a • Submodule.Quotient.mk b) = _
  rw [LinearEquiv.map_smulₛₗ]
  rfl

/-! ## Presented-Weyl surjectivity -/

theorem presentedCanonicalRightQuotient_rightMul_coordinate_surjective
    [Algebra ℚ k] (n N : ℕ) {d : PresentedWeyl k (n + 1)}
    (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d) :
    Function.Surjective
      (rightMul (presentedCanonicalRightIdeal (k := k) n N d)
        (presentedCoordinate k n)) := by
  let e := presentedIteratedEquiv k (n + 1)
  let I := presentedCanonicalRightIdeal (k := k) n N d
  let f := transportedRightQuotientEquiv e I
  have hmap : transportedRightIdeal e I =
      canonicalRightIdeal (pairCoordinate (B := IteratedPairStage k n))
        (presentedToIterated k (n + 1) d) N := by
    exact presented_canonicalRightIdeal_map (k := k) n N d
  have hsurj := presentedCanonicalQuotient_rightMul_coordinate_surjective
    k n N hd
  have hsurj' : Function.Surjective
      (rightMul (transportedRightIdeal e I)
        (e (presentedCoordinate k n))) := by
    rw [hmap]
    have hx : e (presentedCoordinate k n) =
        pairCoordinate (B := IteratedPairStage k n) := by
      change presentedToIterated k (n + 1) (presentedCoordinate k n) =
        pairCoordinate (B := IteratedPairStage k n)
      simpa only [stageCoordinate] using (presentedToIterated_coordinate k n)
    rw [hx]
    exact hsurj
  intro q
  obtain ⟨r, hr⟩ := hsurj' (f q)
  refine ⟨f.symm r, ?_⟩
  apply f.injective
  rw [transportedRightQuotientEquiv_rightMul]
  rw [f.apply_symm_apply]
  exact hr


end
end Stafford38.WeylQuotientTransport
