/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.Algebra
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.RestrictedGaussAdic
import LeanPool.UniformSheafyTateDomains.AdicSpaces.Presheaf
import LeanPool.UniformSheafyTateDomains.AdicSpaces.RelativePieceKeystone

/-!
# The small perturbation lemma ([WP] §6.3, lem:small-perturbation)

Source ([WP] lines 949–966): "Let `(E,E⁺)` be a complete Tate Huber pair and choose a
closed ring of definition `E₀ ⊆ E⁺`.  Let `α=(f_1,…,f_m;g)` be a rational datum whose
entries lie in `E₀`. … Suppose that for some `ℓ ≥ 0` there are `a_0,…,a_m ∈ E₀` with
`ϖ^ℓ = ∑ a_j d_j`.  Let `d_j' ∈ E₀` satisfy `d_j' − d_j ∈ ϖ^{ℓ+1}E₀`.  Then `α'` is a
rational datum, `α` and `α'` define the same rational subset of `Spa(E,E⁺)`, and their
completed rational localizations are canonically isomorphic."

Formalization scope (documented specialization): stated for a complete NORMED
ultrametric Tate ring with a norm-scaling pseudouniformizer (the FJP `(t, htu, ht1,
ht0, hscale)` bundle) — `E₀` is the unit ball; this covers every use in this project.
The setup is bundled in `PerturbSetup`.  Because covering data arrive with arbitrary
pairs of definition, this file also states pod-independence of `presheafValue`
(search first: `CompletionModelIndependence.lean` / `PresheafIdentification.lean`).
-/

@[expose] public section

namespace WeightedParity

open ValuationSpectrum

variable {E : Type*} [NormedCommRing E] [IsUltrametricDist E] [NormOneClass E]
  [CompleteSpace E] [ValuationSpectrum.PlusSubring E]

/-! ### Pod-independence of the localization topology (spawned sub-ticket W12a)

`CompletionModelIndependence` proves the whole-space case (`T = {1}`, `s = 1`);
here the general-datum case: every element of a `P'`-basic neighborhood is a
`ℤ`-combination of terms `φ(a')·τ` with `a'` in a power of `I'` and `τ` a
`T/s`-monomial; `A`-level absorption (both pods present `𝓝_A 0`) replaces the
`I'`-power element by an `I`-power element, and the `τ`-multiplier is absorbed by
the `P`-side ideal. -/

section PodIndependence

open Filter Topology

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The multiplicative monoid of `T/s`-monomials. -/
private noncomputable def tsMonoid (T : Finset A) (s : A) :
    Submonoid (Localization.Away s) :=
  Submonoid.closure (Set.range fun t : T => divByS (t : A) s)

private theorem tsMonoid_le_locSubring (P : PairOfDefinition A) (T : Finset A)
    (s : A) {τ : Localization.Away s} (hτ : τ ∈ tsMonoid T s) :
    τ ∈ locSubring P T s := by
  induction hτ using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨t, rfl⟩ := hx
    exact divByS_mem_locSubring P T s t.2
  | one => exact one_mem _
  | mul x y _ _ hx hy => exact mul_mem hx hy

/-- Normal-form generators: `φ(a)·τ` with `a ∈ A₀` and `τ` a `T/s`-monomial. -/
private def normalSet (P : PairOfDefinition A) (T : Finset A) (s : A) :
    Set (Localization.Away s) :=
  {x | ∃ a ∈ P.A₀, ∃ τ ∈ tsMonoid T s,
    x = algebraMap A (Localization.Away s) a * τ}

private theorem normalSet_mul_self (P : PairOfDefinition A) (T : Finset A) (s : A)
    {x y : Localization.Away s} (hx : x ∈ normalSet P T s)
    (hy : y ∈ normalSet P T s) : x * y ∈ normalSet P T s := by
  obtain ⟨a, ha, τ, hτ, rfl⟩ := hx
  obtain ⟨b, hb, σ, hσ, rfl⟩ := hy
  exact ⟨a * b, mul_mem ha hb, τ * σ, mul_mem hτ hσ, by rw [map_mul]; ring⟩

private theorem mul_mem_closure_normalSet (P : PairOfDefinition A) (T : Finset A)
    (s : A) {x y : Localization.Away s}
    (hx : x ∈ AddSubgroup.closure (normalSet P T s))
    (hy : y ∈ AddSubgroup.closure (normalSet P T s)) :
    x * y ∈ AddSubgroup.closure (normalSet P T s) := by
  induction hx using AddSubgroup.closure_induction with
  | mem a ha =>
    induction hy using AddSubgroup.closure_induction with
    | mem b hb => exact AddSubgroup.subset_closure (normalSet_mul_self P T s ha hb)
    | zero => rw [mul_zero]; exact zero_mem _
    | add b c _ _ ihb ihc => rw [mul_add]; exact add_mem ihb ihc
    | neg b _ ihb => rw [mul_neg]; exact neg_mem ihb
  | zero => rw [zero_mul]; exact zero_mem _
  | add a b _ _ iha ihb => rw [add_mul]; exact add_mem iha ihb
  | neg a _ iha => rw [neg_mul]; exact neg_mem iha

private theorem locSubring_subset_closure_normalSet (P : PairOfDefinition A)
    (T : Finset A) (s : A) {r : Localization.Away s} (hr : r ∈ locSubring P T s) :
    r ∈ AddSubgroup.closure (normalSet P T s) := by
  induction hr using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, ha, rfl⟩ | ⟨t, rfl⟩
    · exact AddSubgroup.subset_closure ⟨a, ha, 1, one_mem _, (mul_one _).symm⟩
    · exact AddSubgroup.subset_closure ⟨1, one_mem _,
        divByS (t : A) s, Submonoid.subset_closure ⟨t, rfl⟩, by rw [map_one, one_mul]⟩
  | zero => exact zero_mem _
  | one => exact AddSubgroup.subset_closure ⟨1, one_mem _, 1, one_mem _, by
      rw [map_one, one_mul]⟩
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx
  | mul x y _ _ hx hy => exact mul_mem_closure_normalSet P T s hx hy

/-- `A`-level absorption between two pods: both `Iⁿ`-image families present
`𝓝_A 0`. -/
private theorem pod_absorb (P P' : PairOfDefinition A) (n : ℕ) :
    ∃ m : ℕ, (Subtype.val '' ((P'.I ^ m : Ideal P'.A₀) : Set P'.A₀) : Set A) ⊆
      Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀) := by
  have hmem : (Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀)) ∈ 𝓝 (0 : A) :=
    P.hasBasis_nhds_zero.mem_of_mem (i := n) trivial
  obtain ⟨m, -, hm⟩ := P'.hasBasis_nhds_zero.mem_iff.mp hmem
  exact ⟨m, hm⟩

/-- A single normal-form multiple of an absorbed `I`-power image lies in the
`P`-side basic neighborhood. -/
private theorem term_mem_locNhd (P : PairOfDefinition A) (T : Finset A) (s : A)
    (n : ℕ) (c : P.A₀) (hc : c ∈ P.I ^ n) {τ : Localization.Away s}
    (hτ : τ ∈ tsMonoid T s) :
    algebraMap A (Localization.Away s) (c : A) * τ ∈ locNhd P T s n := by
  refine AddSubgroup.mem_map.mpr ⟨algebraMapD P T s c * ⟨τ, tsMonoid_le_locSubring P T s hτ⟩, ?_, rfl⟩
  have h1 : algebraMapD P T s c ∈ (locIdeal P T s) ^ n := by
    rw [locIdeal, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hc
  exact Ideal.mul_mem_right _ _ h1

/-- The `P'`-basic neighborhoods are absorbed by the `P`-basic ones. -/
private theorem locNhd_absorb (P P' : PairOfDefinition A) (T : Finset A) (s : A)
    (n : ℕ) : ∃ m : ℕ, (locNhd P' T s m : Set (Localization.Away s)) ⊆
      locNhd P T s n := by
  classical
  obtain ⟨m, hm⟩ := pod_absorb P P' n
  refine ⟨m, ?_⟩
  rintro x hx
  obtain ⟨d, hd, rfl⟩ := AddSubgroup.mem_map.mp hx
  rw [Submodule.mem_toAddSubgroup, locIdeal, ← Ideal.map_pow,
    ← Ideal.span_eq (P'.I ^ m), Ideal.map_span] at hd
  have key : ∀ (d : locSubring P' T s)
      (_ : d ∈ Ideal.span (⇑(algebraMapD P' T s) ''
        ((P'.I ^ m : Ideal P'.A₀) : Set P'.A₀))),
      ∀ r ∈ AddSubgroup.closure (normalSet P' T s),
        r * (d : Localization.Away s) ∈ locNhd P T s n := by
    intro d hd
    induction hd using Submodule.span_induction with
    | mem d hdmem =>
      obtain ⟨c', hc', rfl⟩ := hdmem
      intro r hr
      induction hr using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, ha, τ, hτ, rfl⟩ := hy
        have hprod : (⟨a, ha⟩ * c' : P'.A₀) ∈ P'.I ^ m :=
          Ideal.mul_mem_left _ _ hc'
        obtain ⟨c₀, hc₀, hval⟩ := hm ⟨⟨a, ha⟩ * c', hprod, rfl⟩
        have hcast : (algebraMap A (Localization.Away s) a * τ) *
            ((algebraMapD P' T s c' : locSubring P' T s) : Localization.Away s) =
            algebraMap A (Localization.Away s) ((c₀ : P.A₀) : A) * τ := by
          have h1 : ((algebraMapD P' T s c' : locSubring P' T s) :
              Localization.Away s) =
              algebraMap A (Localization.Away s) (c' : A) := rfl
          rw [h1, hval]
          show algebraMap A (Localization.Away s) a * τ *
              algebraMap A (Localization.Away s) (c' : A) =
            algebraMap A (Localization.Away s) (a * (c' : A)) * τ
          rw [map_mul]
          ring
        rw [hcast]
        exact term_mem_locNhd P T s n c₀ hc₀ hτ
      | zero =>
        rw [zero_mul]
        exact zero_mem _
      | add y z _ _ ihy ihz =>
        rw [add_mul]
        exact add_mem ihy ihz
      | neg y _ ihy =>
        rw [neg_mul]
        exact neg_mem ihy
    | zero =>
      intro r hr
      rw [show ((0 : locSubring P' T s) : Localization.Away s) = 0 from rfl,
        mul_zero]
      exact zero_mem _
    | add d e _ _ ihd ihe =>
      intro r hr
      rw [show ((d + e : locSubring P' T s) : Localization.Away s) =
        (d : Localization.Away s) + e from rfl, mul_add]
      exact add_mem (ihd r hr) (ihe r hr)
    | smul u d _ ihd =>
      intro r hr
      rw [show ((u • d : locSubring P' T s) : Localization.Away s) =
        (u : Localization.Away s) * d from rfl, ← mul_assoc]
      exact ihd (r * (u : Localization.Away s))
        (mul_mem_closure_normalSet P' T s hr
          (locSubring_subset_closure_normalSet P' T s u.2))
  have h1 : (1 : Localization.Away s) ∈ AddSubgroup.closure (normalSet P' T s) :=
    AddSubgroup.subset_closure ⟨1, one_mem _, 1, one_mem _, by rw [map_one, one_mul]⟩
  have hfin := key d hd 1 h1
  rwa [one_mul] at hfin

/-- **Pod-independence of the localization topology** for a general rational datum
(Wedhorn §6.1 pushed through the §8.1 construction; generalizes
`locTopology_globalLocData_eq`). -/
theorem locTopology_pod_eq (P P' : PairOfDefinition A) (T : Finset A) (s : A)
    (h : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : A) s ∈ locSubring P T s)
    (h' : ∃ N : ℕ, ∀ b : P'.A₀, b ∈ P'.I ^ N →
      divByS (↑b : A) s ∈ locSubring P' T s) :
    locTopology P T s h = locTopology P' T s h' := by
  have h₁ := (locBasis P T s h).toRingFilterBasis.isTopologicalRing
  have h₂ := (locBasis P' T s h').toRingFilterBasis.isTopologicalRing
  refine IsTopologicalAddGroup.ext
    (@IsTopologicalRing.to_topologicalAddGroup _ _ (locTopology P T s h) h₁)
    (@IsTopologicalRing.to_topologicalAddGroup _ _ (locTopology P' T s h') h₂) ?_
  refine Filter.HasBasis.ext ((locBasis P T s h).hasBasis_nhds_zero)
    ((locBasis P' T s h').hasBasis_nhds_zero) ?_ ?_
  · intro n _
    obtain ⟨m, hm⟩ := locNhd_absorb P P' T s n
    exact ⟨m, trivial, hm⟩
  · intro n _
    obtain ⟨m, hm⟩ := locNhd_absorb P' P T s n
    exact ⟨m, trivial, hm⟩

end PodIndependence

section PodCongr

private theorem podCongr_cross_continuous (P P' : PairOfDefinition E) (T : Finset E)
    (s : E)
    (h : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : E) s ∈ locSubring P T s)
    (h' : ∃ N : ℕ, ∀ b : P'.A₀, b ∈ P'.I ^ N →
      divByS (↑b : E) s ∈ locSubring P' T s) :
    @Continuous _ _ (⟨P, T, s, h⟩ : RationalLocData E).topology _
      (⇑((⟨P', T, s, h'⟩ : RationalLocData E).coeRingHom)) := by
  have heq : (⟨P, T, s, h⟩ : RationalLocData E).topology =
      (⟨P', T, s, h'⟩ : RationalLocData E).topology :=
    locTopology_pod_eq P P' T s h h'
  rw [show (⟨P, T, s, h⟩ : RationalLocData E).topology = _ from heq]
  exact @UniformSpace.Completion.continuous_coe _
    (⟨P', T, s, h'⟩ : RationalLocData E).uniformSpace

private noncomputable def podCongrHomAux (P P' : PairOfDefinition E) (T : Finset E)
    (s : E)
    (h : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : E) s ∈ locSubring P T s)
    (h' : ∃ N : ℕ, ∀ b : P'.A₀, b ∈ P'.I ^ N →
      divByS (↑b : E) s ∈ locSubring P' T s) :
    presheafValue (⟨P, T, s, h⟩ : RationalLocData E) →+*
      presheafValue (⟨P', T, s, h'⟩ : RationalLocData E) := by
  letI : UniformSpace (Localization.Away s) :=
    (⟨P, T, s, h⟩ : RationalLocData E).uniformSpace
  letI : IsTopologicalRing (Localization.Away s) :=
    (⟨P, T, s, h⟩ : RationalLocData E).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away s) :=
    (⟨P, T, s, h⟩ : RationalLocData E).isUniformAddGroup
  exact UniformSpace.Completion.extensionHom
    ((⟨P', T, s, h'⟩ : RationalLocData E).coeRingHom)
    (podCongr_cross_continuous P P' T s h h')

private theorem podCongrHomAux_coe (P P' : PairOfDefinition E) (T : Finset E)
    (s : E)
    (h : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : E) s ∈ locSubring P T s)
    (h' : ∃ N : ℕ, ∀ b : P'.A₀, b ∈ P'.I ^ N →
      divByS (↑b : E) s ∈ locSubring P' T s)
    (l : Localization.Away s) :
    podCongrHomAux P P' T s h h'
        ((⟨P, T, s, h⟩ : RationalLocData E).coeRingHom l) =
      (⟨P', T, s, h'⟩ : RationalLocData E).coeRingHom l := by
  letI : UniformSpace (Localization.Away s) :=
    (⟨P, T, s, h⟩ : RationalLocData E).uniformSpace
  letI : IsTopologicalRing (Localization.Away s) :=
    (⟨P, T, s, h⟩ : RationalLocData E).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away s) :=
    (⟨P, T, s, h⟩ : RationalLocData E).isUniformAddGroup
  exact UniformSpace.Completion.extensionHom_coe _ _ l

private theorem podCongrHomAux_continuous (P P' : PairOfDefinition E) (T : Finset E)
    (s : E)
    (h : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : E) s ∈ locSubring P T s)
    (h' : ∃ N : ℕ, ∀ b : P'.A₀, b ∈ P'.I ^ N →
      divByS (↑b : E) s ∈ locSubring P' T s) :
    Continuous (podCongrHomAux P P' T s h h') := by
  letI : UniformSpace (Localization.Away s) :=
    (⟨P, T, s, h⟩ : RationalLocData E).uniformSpace
  exact UniformSpace.Completion.continuous_extension

private theorem podCongrHomAux_roundtrip (P P' : PairOfDefinition E) (T : Finset E)
    (s : E)
    (h : ∃ N : ℕ, ∀ b : P.A₀, b ∈ P.I ^ N →
      divByS (↑b : E) s ∈ locSubring P T s)
    (h' : ∃ N : ℕ, ∀ b : P'.A₀, b ∈ P'.I ^ N →
      divByS (↑b : E) s ∈ locSubring P' T s)
    (x : presheafValue (⟨P, T, s, h⟩ : RationalLocData E)) :
    podCongrHomAux P' P T s h' h (podCongrHomAux P P' T s h h' x) = x := by
  letI : UniformSpace (Localization.Away s) :=
    (⟨P, T, s, h⟩ : RationalLocData E).uniformSpace
  have hdense : DenseRange (⇑((⟨P, T, s, h⟩ : RationalLocData E).coeRingHom)) :=
    @UniformSpace.Completion.denseRange_coe _
      (⟨P, T, s, h⟩ : RationalLocData E).uniformSpace
  have hfun : ⇑(podCongrHomAux P' P T s h' h) ∘ ⇑(podCongrHomAux P P' T s h h') =
      (id : presheafValue (⟨P, T, s, h⟩ : RationalLocData E) → _) := by
    refine hdense.equalizer ?_ continuous_id ?_
    · exact (podCongrHomAux_continuous P' P T s h' h).comp
        (podCongrHomAux_continuous P P' T s h h')
    · funext l
      show podCongrHomAux P' P T s h' h (podCongrHomAux P P' T s h h'
        ((⟨P, T, s, h⟩ : RationalLocData E).coeRingHom l)) =
        (⟨P, T, s, h⟩ : RationalLocData E).coeRingHom l
      rw [podCongrHomAux_coe P P' T s h h' l]
      exact podCongrHomAux_coe P' P T s h' h l
  exact congr_fun hfun x

end PodCongr

/-- Pod-independence of the completed rational localization for Tate rings: two data
with the same `(T, s)` have canonically isomorphic presheaf values.  (Any two rings of
definition of a Tate ring are commensurable; search first —
`CompletionModelIndependence` provides the global case.) -/
noncomputable def podCongrEquiv (D D' : RationalLocData E) (hT : D.T = D'.T)
    (hs : D.s = D'.s) : presheafValue D ≃+* presheafValue D' := by
  obtain ⟨P, T, s, h⟩ := D
  obtain ⟨P', T', s', h'⟩ := D'
  dsimp only at hT hs
  subst hT
  subst hs
  exact
    { toFun := podCongrHomAux P P' T s h h'
      invFun := podCongrHomAux P' P T s h' h
      left_inv := podCongrHomAux_roundtrip P P' T s h h'
      right_inv := podCongrHomAux_roundtrip P' P T s h' h
      map_mul' := map_mul _
      map_add' := map_add _ }

theorem podCongrEquiv_continuous (D D' : RationalLocData E) (hT : D.T = D'.T)
    (hs : D.s = D'.s) : Continuous (podCongrEquiv D D' hT hs) := by
  obtain ⟨P, T, s, h⟩ := D
  obtain ⟨P', T', s', h'⟩ := D'
  dsimp only at hT hs
  subst hT
  subst hs
  exact podCongrHomAux_continuous P P' T s h h'

theorem podCongrEquiv_symm_continuous (D D' : RationalLocData E) (hT : D.T = D'.T)
    (hs : D.s = D'.s) : Continuous (podCongrEquiv D D' hT hs).symm := by
  obtain ⟨P, T, s, h⟩ := D
  obtain ⟨P', T', s', h'⟩ := D'
  dsimp only at hT hs
  subst hT
  subst hs
  exact podCongrHomAux_continuous P' P T s h' h

theorem podCongrEquiv_canonicalMap (D D' : RationalLocData E) (hT : D.T = D'.T)
    (hs : D.s = D'.s) (x : E) :
    podCongrEquiv D D' hT hs (D.canonicalMap x) = D'.canonicalMap x := by
  obtain ⟨P, T, s, h⟩ := D
  obtain ⟨P', T', s', h'⟩ := D'
  dsimp only at hT hs
  subst hT
  subst hs
  exact podCongrHomAux_coe P P' T s h h'
    (algebraMap E (Localization.Away s) x)

/-- The bundled data of a small perturbation of a rational datum
([WP] lem:small-perturbation): a norm-scaling pseudouniformizer `t`, a rational datum
`D` with unit-ball entries and the redundant `s ∈ T` coordinate, an integral Bezout
relation `∑_{x ∈ T} a_x·x = t^ℓ` with unit-ball coefficients, and a perturbation
`pert` moving each entry by at most `‖t‖^{ℓ+1}`. -/
structure PerturbSetup (E : Type*) [NormedCommRing E] [IsUltrametricDist E]
    [NormOneClass E] [ValuationSpectrum.PlusSubring E] : Type _ where
  /-- The pseudouniformizer. -/
  t : E
  htu : IsUnit t
  ht1 : ‖t‖ < 1
  ht0 : 0 < ‖t‖
  hscale : ∀ x : E, ‖t * x‖ = ‖t‖ * ‖x‖
  /-- The rational datum being perturbed. -/
  D : RationalLocData E
  hsT : D.s ∈ D.T
  hT1 : ∀ x ∈ D.T, ‖x‖ ≤ 1
  /-- The Bezout level ([WP] eq:integral-bezout). -/
  ℓ : ℕ
  /-- The Bezout coefficients. -/
  a : E → E
  ha1 : ∀ x, ‖a x‖ ≤ 1
  hbez : ∑ x ∈ D.T, a x * x = t ^ ℓ
  /-- The perturbation of the entries. -/
  pert : E → E
  hpert1 : ∀ x ∈ D.T, ‖pert x‖ ≤ 1
  hpert : ∀ x ∈ D.T, ‖pert x - x‖ ≤ ‖t‖ ^ (ℓ + 1)
  /-- The chosen ring of definition (the unit ball) lies in `E⁺` ([WP] line 949:
  "choose a closed ring of definition `E₀ ⊆ E⁺`" — restored 2026-07-29; the first
  skeleton dropped this source hypothesis, without which the `Spa`-point estimates
  of `rationalOpen_datum` are unavailable). -/
  hplus : ∀ x : E, ‖x‖ ≤ 1 → x ∈ ((E⁺ : Subring E) : Set E)

namespace PerturbSetup

variable [DecidableEq E]

/-- The primed integral Bezout relation ([WP] lem:small-perturbation, proof):
`∑ a_x·pert x = t^ℓ·(1 + t·h)` with `‖h‖ ≤ 1`. -/
theorem exists_perturbed_bezout (S : PerturbSetup E) :
    ∃ h : E, ‖h‖ ≤ 1 ∧
      ∑ x ∈ S.D.T, S.a x * S.pert x = S.t ^ S.ℓ * (1 + S.t * h) := by
  classical
  have hsplit : ∑ x ∈ S.D.T, S.a x * S.pert x =
      S.t ^ S.ℓ + ∑ x ∈ S.D.T, S.a x * (S.pert x - x) := by
    rw [← S.hbez, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    ring
  have hr : ‖∑ x ∈ S.D.T, S.a x * (S.pert x - x)‖ ≤ ‖S.t‖ ^ (S.ℓ + 1) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (pow_nonneg S.ht0.le _) fun x hx => ?_
    calc ‖S.a x * (S.pert x - x)‖ ≤ ‖S.a x‖ * ‖S.pert x - x‖ := norm_mul_le _ _
      _ ≤ 1 * ‖S.t‖ ^ (S.ℓ + 1) := by
          exact mul_le_mul (S.ha1 x) (S.hpert x hx) (norm_nonneg _) zero_le_one
      _ = ‖S.t‖ ^ (S.ℓ + 1) := one_mul _
  obtain ⟨h, hh1, hEq⟩ := FiniteJet.GraphKoszul.exists_norm_le_one_eq_pow_mul
    S.htu S.ht0 S.hscale (S.ℓ + 1) _ hr
  refine ⟨h, hh1, ?_⟩
  rw [hsplit, hEq, pow_succ]
  ring

/-- The perturbed entries still generate the unit ideal (the primed Bezout
combination is a unit: `t^ℓ·(1 + t·h)` with `1 + t·h` a geometric-series unit). -/
theorem span_pertImage_eq_top (S : PerturbSetup E) :
    Ideal.span ((S.D.T.image S.pert : Finset E) : Set E) = ⊤ := by
  classical
  obtain ⟨h, hh1, hsum⟩ := exists_perturbed_bezout S
  have hmem : (S.t ^ S.ℓ * (1 + S.t * h)) ∈
      Ideal.span ((S.D.T.image S.pert : Finset E) : Set E) := by
    rw [← hsum]
    refine Ideal.sum_mem _ fun x hx => ?_
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem S.pert hx)))
  have hu : IsUnit (S.t ^ S.ℓ * (1 + S.t * h)) := by
    refine IsUnit.mul (S.htu.pow S.ℓ) ?_
    have hnorm : ‖-(S.t * h)‖ < 1 := by
      rw [norm_neg]
      calc ‖S.t * h‖ = ‖S.t‖ * ‖h‖ := S.hscale h
        _ ≤ ‖S.t‖ * 1 := mul_le_mul_of_nonneg_left hh1 S.ht0.le
        _ = ‖S.t‖ := mul_one _
        _ < 1 := S.ht1
    have hunit : IsUnit (1 - -(S.t * h)) := (Units.oneSub _ hnorm).isUnit
    rwa [sub_neg_eq_add] at hunit
  exact Ideal.eq_top_of_isUnit_mem _ hmem hu

/-- The perturbed rational datum `α'` ([WP] lem:small-perturbation), with the
unit-ball pair of definition. -/
noncomputable def datum (S : PerturbSetup E) : RationalLocData E :=
  genPieceDatum (FiniteJet.unitBallPod S.t S.htu S.ht1 S.ht0 S.hscale)
    (S.D.T.image S.pert) (S.pert S.D.s) (span_pertImage_eq_top S)

theorem datum_T (S : PerturbSetup E) : S.datum.T = S.D.T.image S.pert := rfl

theorem datum_s (S : PerturbSetup E) : S.datum.s = S.pert S.D.s := rfl

/-- The perturbed datum is rational ([WP]: "`α'` is a rational datum" — the primed
integral Bezout relation `∑ a_j d_j' = ϖ^ℓ(1 + ϖH)` with `1 + ϖH` a unit of `E₀`). -/
theorem datum_isRational (S : PerturbSetup E) : S.datum.IsRational :=
  RationalLocData.isRational_of_span_eq_top (by
    rw [datum_T]
    exact span_pertImage_eq_top S)

private theorem gv_mul_lt_of_lt_one {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {a b : Γ₀} (ha : a < 1) (hb : b ≠ 0) : a * b < b := by
  by_contra hcon
  push_neg at hcon
  have h1 := mul_le_mul_left hcon b⁻¹
  rw [mul_inv_cancel₀ hb, mul_assoc, mul_inv_cancel₀ hb, mul_one] at h1
  exact absurd ha (not_lt.mpr h1)

/-- The scaling pseudouniformizer is topologically nilpotent. -/
theorem t_isTopologicallyNilpotent (S : PerturbSetup E) :
    IsTopologicallyNilpotent S.t := by
  show Filter.Tendsto (S.t ^ ·) Filter.atTop (nhds 0)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hn : ∀ n : ℕ, ‖S.t ^ n‖ = ‖S.t‖ ^ n := fun n => by
    have h := FiniteJet.norm_pow_mul_of_scale S.hscale n 1
    rwa [mul_one, norm_one, mul_one] at h
  exact (Filter.tendsto_congr hn).mpr
    (tendsto_pow_atTop_nhds_zero_of_lt_one S.ht0.le S.ht1)

/-- Perturbation does not change the rational subset ([WP]: "`α` and `α'` define the
same rational subset of `Spa(E,E⁺)`" — at every point of the subset
`|ϖ|^ℓ ≤ |g(x)|`, and the perturbations have value `≤ |ϖ|^{ℓ+1} < |g(x)|`). -/
theorem rationalOpen_datum (S : PerturbSetup E) :
    rationalOpen S.datum.T S.datum.s = rationalOpen S.D.T S.D.s := by
  classical
  rw [datum_T, datum_s]
  ext v
  constructor
  · rintro ⟨hspa, hT', hs0'⟩
    letI : ValuativeRel E := v.toValuativeRel
    set w := ValuativeRel.valuation E with hw
    have hvle : ∀ g h : E, v.vle g h ↔ w g ≤ w h := fun g h =>
      Valuation.Compatible.vle_iff_le (v := w) g h
    have hble : ∀ f : E, ‖f‖ ≤ 1 → w f ≤ 1 := fun f hf => by
      have h1 := (hvle f 1).mp (hspa.2 f (S.hplus f hf))
      rwa [map_one] at h1
    have hwt1 : w S.t < 1 := by
      refine lt_of_not_ge fun hge => ?_
      refine not_vle_one_of_mem_spa_of_topologicallyNilpotent hspa
        (t_isTopologicallyNilpotent S) ?_
      rw [hvle, map_one]
      exact hge
    have hwT' : ∀ x ∈ S.D.T, w (S.pert x) ≤ w (S.pert S.D.s) := fun x hx =>
      (hvle _ _).mp (hT' (S.pert x) (Finset.mem_image_of_mem S.pert hx))
    have hws0' : w (S.pert S.D.s) ≠ 0 := by
      intro h0
      refine hs0' ?_
      rw [hvle, map_zero, h0]
    -- the primed Bezout gives w(t)^ℓ ≤ w(pert s)
    obtain ⟨h, hh1, hsum⟩ := exists_perturbed_bezout S
    have hone : w (1 + S.t * h) = 1 := by
      have hlt : w (S.t * h) < w 1 := by
        rw [map_one, map_mul]
        calc w S.t * w h ≤ w S.t * 1 := mul_le_mul_right (hble h hh1) _
          _ = w S.t := mul_one _
          _ < 1 := hwt1
      rw [Valuation.map_add_eq_of_lt_left _ hlt, map_one]
    have hpow : w S.t ^ S.ℓ ≤ w (S.pert S.D.s) := by
      have hle : w (∑ x ∈ S.D.T, S.a x * S.pert x) ≤ w (S.pert S.D.s) := by
        refine Valuation.map_sum_le _ fun x hx => ?_
        rw [map_mul]
        calc w (S.a x) * w (S.pert x) ≤ 1 * w (S.pert S.D.s) :=
              mul_le_mul' (hble _ (S.ha1 x)) (hwT' x hx)
          _ = w (S.pert S.D.s) := one_mul _
      rw [hsum, map_mul, hone, mul_one, map_pow] at hle
      exact hle
    have hsmall : ∀ x ∈ S.D.T, w (S.pert x - x) < w (S.pert S.D.s) := by
      intro x hx
      obtain ⟨y, hy1, hyEq⟩ := FiniteJet.GraphKoszul.exists_norm_le_one_eq_pow_mul
        S.htu S.ht0 S.hscale (S.ℓ + 1) _ (S.hpert x hx)
      rw [hyEq, map_mul, map_pow, pow_succ]
      calc w S.t ^ S.ℓ * w S.t * w y ≤ w S.t ^ S.ℓ * w S.t * 1 :=
            mul_le_mul_right (hble y hy1) _
        _ = w S.t * w S.t ^ S.ℓ := by rw [mul_one, mul_comm]
        _ ≤ w S.t * w (S.pert S.D.s) := mul_le_mul_right hpow _
        _ < w (S.pert S.D.s) := gv_mul_lt_of_lt_one hwt1 hws0'
    have hs_eq : w S.D.s = w (S.pert S.D.s) := by
      have h1 : w (S.D.s - S.pert S.D.s) < w (S.pert S.D.s) := by
        have := hsmall S.D.s S.hsT
        rwa [← Valuation.map_neg, neg_sub] at this
      have h2 := Valuation.map_add_eq_of_lt_left w (y := S.D.s - S.pert S.D.s) h1
      rwa [add_sub_cancel] at h2
    refine ⟨hspa, fun x hx => ?_, fun hvle0 => ?_⟩
    · rw [hvle]
      have hx' : w x ≤ w (S.pert S.D.s) := by
        have h1 : w (x - S.pert x) < w (S.pert S.D.s) := by
          have := hsmall x hx
          rwa [← Valuation.map_neg, neg_sub] at this
        calc w x = w (S.pert x + (x - S.pert x)) := by rw [add_sub_cancel]
          _ ≤ max (w (S.pert x)) (w (x - S.pert x)) := Valuation.map_add _ _ _
          _ ≤ w (S.pert S.D.s) := max_le (hwT' x hx) h1.le
      rw [← hs_eq] at hx'
      exact hx'
    · rw [hvle, map_zero] at hvle0
      exact hws0' (by rw [← hs_eq]; exact le_antisymm hvle0 zero_le)
  · rintro ⟨hspa, hT, hs0⟩
    letI : ValuativeRel E := v.toValuativeRel
    set w := ValuativeRel.valuation E with hw
    have hvle : ∀ g h : E, v.vle g h ↔ w g ≤ w h := fun g h =>
      Valuation.Compatible.vle_iff_le (v := w) g h
    have hble : ∀ f : E, ‖f‖ ≤ 1 → w f ≤ 1 := fun f hf => by
      have h1 := (hvle f 1).mp (hspa.2 f (S.hplus f hf))
      rwa [map_one] at h1
    have hwt1 : w S.t < 1 := by
      refine lt_of_not_ge fun hge => ?_
      refine not_vle_one_of_mem_spa_of_topologicallyNilpotent hspa
        (t_isTopologicallyNilpotent S) ?_
      rw [hvle, map_one]
      exact hge
    have hwT : ∀ x ∈ S.D.T, w x ≤ w S.D.s := fun x hx =>
      (hvle _ _).mp (hT x hx)
    have hws0 : w S.D.s ≠ 0 := by
      intro h0
      refine hs0 ?_
      rw [hvle, map_zero, h0]
    have hpow : w S.t ^ S.ℓ ≤ w S.D.s := by
      have hle : w (∑ x ∈ S.D.T, S.a x * x) ≤ w S.D.s := by
        refine Valuation.map_sum_le _ fun x hx => ?_
        rw [map_mul]
        calc w (S.a x) * w x ≤ 1 * w S.D.s :=
              mul_le_mul' (hble _ (S.ha1 x)) (hwT x hx)
          _ = w S.D.s := one_mul _
      rw [S.hbez, map_pow] at hle
      exact hle
    have hsmall : ∀ x ∈ S.D.T, w (S.pert x - x) < w S.D.s := by
      intro x hx
      obtain ⟨y, hy1, hyEq⟩ := FiniteJet.GraphKoszul.exists_norm_le_one_eq_pow_mul
        S.htu S.ht0 S.hscale (S.ℓ + 1) _ (S.hpert x hx)
      rw [hyEq, map_mul, map_pow, pow_succ]
      calc w S.t ^ S.ℓ * w S.t * w y ≤ w S.t ^ S.ℓ * w S.t * 1 :=
            mul_le_mul_right (hble y hy1) _
        _ = w S.t * w S.t ^ S.ℓ := by rw [mul_one, mul_comm]
        _ ≤ w S.t * w S.D.s := mul_le_mul_right hpow _
        _ < w S.D.s := gv_mul_lt_of_lt_one hwt1 hws0
    have hs_eq : w (S.pert S.D.s) = w S.D.s := by
      have h2 := Valuation.map_add_eq_of_lt_left w
        (y := S.pert S.D.s - S.D.s) (x := S.D.s) (hsmall S.D.s S.hsT)
      rwa [add_sub_cancel] at h2
    refine ⟨hspa, fun t' ht' => ?_, fun hvle0 => ?_⟩
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht'
      rw [hvle]
      have hx' : w (S.pert x) ≤ w S.D.s := by
        calc w (S.pert x) = w (x + (S.pert x - x)) := by rw [add_sub_cancel]
          _ ≤ max (w x) (w (S.pert x - x)) := Valuation.map_add _ _ _
          _ ≤ w S.D.s := max_le (hwT x hx) (hsmall x hx).le
      rw [hs_eq]
      exact hx'
    · rw [hvle, map_zero] at hvle0
      exact hws0 (by rw [← hs_eq]; exact le_antisymm hvle0 zero_le)

variable [IsRingOfIntegralElements (E⁺ : Subring E)]

/-- The faithful loc-lift package holds in the `PerturbSetup` context (the Huber/Tate
structure comes from the scaling pseudouniformizer; `E⁺` is a ring of integral
elements per the Huber-pair convention of [WP] §6.3). -/
theorem hasLocLiftPowerBounded (S : PerturbSetup E) :
    haveI : IsHuberRing E :=
      FiniteJet.isHuberRing_of_scale S.t S.htu S.ht1 S.ht0 S.hscale
    HasLocLiftPowerBounded E := by
  haveI : IsHuberRing E :=
    FiniteJet.isHuberRing_of_scale S.t S.htu S.ht1 S.ht0 S.hscale
  haveI : IsTateRing E :=
    FiniteJet.isTateRing_of_scale S.t S.htu S.ht1 S.ht0 S.hscale
  haveI : @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E) := by
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    infer_instance
  exact hasLocLiftPowerBounded_faithful

/-- **The canonical isomorphism of completed localizations** ([WP]
lem:small-perturbation: "their completed rational localizations are canonically
isomorphic" — `g'/g` is a 1-unit with power-bounded inverse; both universal-property
maps exist and are mutually inverse). -/
noncomputable def equiv (S : PerturbSetup E) :
    presheafValue S.D ≃+* presheafValue S.datum := by
  haveI : IsHuberRing E :=
    FiniteJet.isHuberRing_of_scale S.t S.htu S.ht1 S.ht0 S.hscale
  haveI : HasLocLiftPowerBounded E := S.hasLocLiftPowerBounded
  exact
    { toFun := restrictionMapHom S.D S.datum (rationalOpen_datum S).le
      invFun := restrictionMapHom S.datum S.D (rationalOpen_datum S).ge
      left_inv := fun x => by
        have h := congr_fun (restrictionMap_comp S.D S.datum S.D
          (rationalOpen_datum S).le (rationalOpen_datum S).ge) x
        have hid : restrictionMap S.D S.D
            (((rationalOpen_datum S).ge).trans (rationalOpen_datum S).le) = id :=
          restrictionMap_id S.D
        rw [hid] at h
        exact h
      right_inv := fun x => by
        have h := congr_fun (restrictionMap_comp S.datum S.D S.datum
          (rationalOpen_datum S).ge (rationalOpen_datum S).le) x
        have hid : restrictionMap S.datum S.datum
            (((rationalOpen_datum S).le).trans (rationalOpen_datum S).ge) = id :=
          restrictionMap_id S.datum
        rw [hid] at h
        exact h
      map_mul' := map_mul _
      map_add' := map_add _ }

theorem equiv_continuous (S : PerturbSetup E) : Continuous S.equiv := by
  haveI : IsHuberRing E :=
    FiniteJet.isHuberRing_of_scale S.t S.htu S.ht1 S.ht0 S.hscale
  haveI : HasLocLiftPowerBounded E := S.hasLocLiftPowerBounded
  show Continuous (restrictionMapHom S.D S.datum (rationalOpen_datum S).le)
  letI : UniformSpace (Localization.Away S.D.s) := S.D.uniformSpace
  letI : IsTopologicalRing (Localization.Away S.D.s) := S.D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away S.D.s) := S.D.isUniformAddGroup
  exact UniformSpace.Completion.continuous_extension

theorem equiv_symm_continuous (S : PerturbSetup E) : Continuous S.equiv.symm := by
  haveI : IsHuberRing E :=
    FiniteJet.isHuberRing_of_scale S.t S.htu S.ht1 S.ht0 S.hscale
  haveI : HasLocLiftPowerBounded E := S.hasLocLiftPowerBounded
  show Continuous (restrictionMapHom S.datum S.D (rationalOpen_datum S).ge)
  letI : UniformSpace (Localization.Away S.datum.s) := S.datum.uniformSpace
  letI : IsTopologicalRing (Localization.Away S.datum.s) := S.datum.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away S.datum.s) := S.datum.isUniformAddGroup
  exact UniformSpace.Completion.continuous_extension

/-- The perturbation isomorphism commutes with the canonical maps from `E`
("Both composites restrict to the identity on `E`"). -/
theorem equiv_canonicalMap (S : PerturbSetup E) (x : E) :
    S.equiv (S.D.canonicalMap x) = S.datum.canonicalMap x := by
  haveI : IsHuberRing E :=
    FiniteJet.isHuberRing_of_scale S.t S.htu S.ht1 S.ht0 S.hscale
  haveI : HasLocLiftPowerBounded E := S.hasLocLiftPowerBounded
  show restrictionMapHom S.D S.datum (rationalOpen_datum S).le
    (S.D.canonicalMap x) = S.datum.canonicalMap x
  letI : UniformSpace (Localization.Away S.D.s) := S.D.uniformSpace
  letI : IsTopologicalRing (Localization.Away S.D.s) := S.D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away S.D.s) := S.D.isUniformAddGroup
  have h := UniformSpace.Completion.extensionHom_coe
    (restrictionMapAlg S.D S.datum (rationalOpen_datum S).le)
    (restrictionMapAlg_continuous S.D S.datum (rationalOpen_datum S).le)
    (algebraMap E (Localization.Away S.D.s) x)
  have h2 : restrictionMapAlg S.D S.datum (rationalOpen_datum S).le
      (algebraMap E (Localization.Away S.D.s) x) = S.datum.canonicalMap x := by
    show IsLocalization.Away.lift S.D.s
      (HasLocLiftPowerBounded.isUnit_canonicalMap_s S.D S.datum
        (rationalOpen_datum S).le)
      (algebraMap E (Localization.Away S.D.s) x) = S.datum.canonicalMap x
    rw [IsLocalization.Away.lift_eq]
  exact h.trans h2

end PerturbSetup

/-- Existence of an integral Bezout relation for a rational datum in a normed Tate
ring, without any normalization of the entries (the coefficients absorb the
scaling; [WP] cor:finite-head-presentation, first step). -/
theorem exists_integral_bezout' (t : E) (htu : IsUnit t) (ht1 : ‖t‖ < 1)
    (ht0 : 0 < ‖t‖) (hscale : ∀ x : E, ‖t * x‖ = ‖t‖ * ‖x‖)
    (D : RationalLocData E) (hD : D.IsRational) :
    ∃ (ℓ : ℕ) (a : E → E), (∀ x, ‖a x‖ ≤ 1) ∧ ∑ x ∈ D.T, a x * x = t ^ ℓ := by
  classical
  haveI : IsTateRing E := FiniteJet.isTateRing_of_scale t htu ht1 ht0 hscale
  have h1 : (1 : E) ∈ Ideal.span (D.T : Set E) := by
    rw [hD.span_eq_top]
    trivial
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp h1
  set M := ∑ x ∈ D.T, ‖c x‖ with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun x _ => norm_nonneg _
  have hMx : ∀ x ∈ D.T, ‖c x‖ ≤ M := fun x hx =>
    Finset.single_le_sum (fun y _ => norm_nonneg (c y)) hx
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℕ, ‖t‖ ^ ℓ * M ≤ 1 := by
    rcases eq_or_lt_of_le hM0 with h0 | hMpos
    · exact ⟨0, by rw [← h0, mul_zero]; exact zero_le_one⟩
    · obtain ⟨ℓ, hℓ⟩ := exists_pow_lt_of_lt_one (div_pos one_pos hMpos) ht1
      exact ⟨ℓ, ((lt_div_iff₀ hMpos).mp hℓ).le⟩
  refine ⟨ℓ, fun x => if x ∈ D.T then t ^ ℓ * c x else 0, fun x => ?_, ?_⟩
  · show ‖if x ∈ D.T then t ^ ℓ * c x else 0‖ ≤ 1
    by_cases hx : x ∈ D.T
    · rw [if_pos hx, FiniteJet.norm_pow_mul_of_scale hscale]
      calc ‖t‖ ^ ℓ * ‖c x‖ ≤ ‖t‖ ^ ℓ * M :=
            mul_le_mul_of_nonneg_left (hMx x hx) (pow_nonneg ht0.le ℓ)
        _ ≤ 1 := hℓ
    · rw [if_neg hx, norm_zero]
      exact zero_le_one
  · rw [Finset.sum_congr rfl fun x hx => by
      show (if x ∈ D.T then t ^ ℓ * c x else 0) * x = t ^ ℓ * (c x * x)
      rw [if_pos hx, mul_assoc], ← Finset.mul_sum]
    rw [show ∑ x ∈ D.T, c x * x = 1 from hc, mul_one]

/-- Existence of an integral Bezout relation for a rational datum in a normed Tate
ring ([WP] cor:finite-head-presentation, first step: "Choose an integral Bezout
relation `ϖ^ℓ = ∑ a_j d_j, a_j ∈ 𝒜₀`"). -/
theorem exists_integral_bezout (t : E) (htu : IsUnit t) (ht1 : ‖t‖ < 1)
    (ht0 : 0 < ‖t‖) (hscale : ∀ x : E, ‖t * x‖ = ‖t‖ * ‖x‖)
    (D : RationalLocData E) (hD : D.IsRational) (hT1 : ∀ x ∈ D.T, ‖x‖ ≤ 1) :
    ∃ (ℓ : ℕ) (a : E → E), (∀ x, ‖a x‖ ≤ 1) ∧ ∑ x ∈ D.T, a x * x = t ^ ℓ := by
  classical
  haveI : IsTateRing E := FiniteJet.isTateRing_of_scale t htu ht1 ht0 hscale
  have h1 : (1 : E) ∈ Ideal.span (D.T : Set E) := by
    rw [hD.span_eq_top]
    trivial
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp h1
  set M := ∑ x ∈ D.T, ‖c x‖ with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun x _ => norm_nonneg _
  have hMx : ∀ x ∈ D.T, ‖c x‖ ≤ M := fun x hx =>
    Finset.single_le_sum (fun y _ => norm_nonneg (c y)) hx
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℕ, ‖t‖ ^ ℓ * M ≤ 1 := by
    rcases eq_or_lt_of_le hM0 with h0 | hMpos
    · exact ⟨0, by rw [← h0, mul_zero]; exact zero_le_one⟩
    · obtain ⟨ℓ, hℓ⟩ := exists_pow_lt_of_lt_one (div_pos one_pos hMpos) ht1
      exact ⟨ℓ, ((lt_div_iff₀ hMpos).mp hℓ).le⟩
  refine ⟨ℓ, fun x => if x ∈ D.T then t ^ ℓ * c x else 0, fun x => ?_, ?_⟩
  · show ‖if x ∈ D.T then t ^ ℓ * c x else 0‖ ≤ 1
    by_cases hx : x ∈ D.T
    · rw [if_pos hx, FiniteJet.norm_pow_mul_of_scale hscale]
      calc ‖t‖ ^ ℓ * ‖c x‖ ≤ ‖t‖ ^ ℓ * M :=
            mul_le_mul_of_nonneg_left (hMx x hx) (pow_nonneg ht0.le ℓ)
        _ ≤ 1 := hℓ
    · rw [if_neg hx, norm_zero]
      exact zero_le_one
  · rw [Finset.sum_congr rfl fun x hx => by
      show (if x ∈ D.T then t ^ ℓ * c x else 0) * x = t ^ ℓ * (c x * x)
      rw [if_pos hx, mul_assoc], ← Finset.mul_sum]
    rw [show ∑ x ∈ D.T, c x * x = 1 from hc, mul_one]

/-! ### Datum changes that preserve the rational subset
([WP] cor:finite-head-presentation, step 1) -/

/-- Adjoining `s` to `T` does not change the rational subset. -/
theorem rationalOpen_insert_self (T : Finset E) (s : E) [DecidableEq E] :
    rationalOpen (insert s T) s = rationalOpen T s := by
  ext v
  letI : ValuativeRel E := v.toValuativeRel
  set w := ValuativeRel.valuation E with hw
  have hvle : ∀ g h : E, v.vle g h ↔ w g ≤ w h := fun g h =>
    Valuation.Compatible.vle_iff_le (v := w) g h
  constructor
  · rintro ⟨hspa, hT, hs0⟩
    exact ⟨hspa, fun t ht => hT t (Finset.mem_insert_of_mem ht), hs0⟩
  · rintro ⟨hspa, hT, hs0⟩
    refine ⟨hspa, fun t ht => ?_, hs0⟩
    rcases Finset.mem_insert.mp ht with rfl | ht'
    · exact (hvle t t).mpr (le_refl _)
    · exact hT t ht'

private theorem gv_le_of_mul_le_mul_left {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] {a b c : Γ₀} (hc : c ≠ 0)
    (h : c * a ≤ c * b) : a ≤ b := by
  have h1 := mul_le_mul_left h c⁻¹
  rwa [mul_right_comm, mul_inv_cancel₀ hc, one_mul, mul_right_comm,
    mul_inv_cancel₀ hc, one_mul] at h1

/-- Scaling both `T` and `s` by a unit does not change the rational subset
([WP] cor:finite-head-presentation: replace `(T, s)` by `(ϖ^k T, ϖ^k s)`). -/
theorem rationalOpen_unitSMul (c : E) (hc : IsUnit c) (T : Finset E) (s : E)
    [DecidableEq E] :
    rationalOpen (T.image (c * ·)) (c * s) = rationalOpen T s := by
  ext v
  letI : ValuativeRel E := v.toValuativeRel
  set w := ValuativeRel.valuation E with hw
  have hvle : ∀ g h : E, v.vle g h ↔ w g ≤ w h := fun g h =>
    Valuation.Compatible.vle_iff_le (v := w) g h
  have hc0 : w c ≠ 0 := (hc.map w).ne_zero
  constructor
  · rintro ⟨hspa, hT, hs0⟩
    refine ⟨hspa, fun t ht => ?_, fun hcon => ?_⟩
    · have h1 := hT (c * t) (Finset.mem_image_of_mem _ ht)
      rw [hvle, map_mul, map_mul] at h1
      exact (hvle t s).mpr (gv_le_of_mul_le_mul_left hc0 h1)
    · refine hs0 ?_
      rw [hvle, map_zero] at hcon ⊢
      rw [map_mul]
      rw [le_zero_iff] at hcon ⊢
      rw [hcon, mul_zero]
  · rintro ⟨hspa, hT, hs0⟩
    refine ⟨hspa, fun t' ht' => ?_, fun hcon => ?_⟩
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ht'
      have h1 := (hvle t s).mp (hT t ht)
      rw [hvle, map_mul, map_mul, mul_comm (w c) (w t), mul_comm (w c) (w s)]
      exact mul_le_mul_left h1 (w c)
    · refine hs0 ?_
      rw [hvle, map_zero, le_zero_iff, map_mul] at hcon
      rcases mul_eq_zero.mp hcon with h0 | h0
      · exact absurd h0 hc0
      · rw [hvle, map_zero, le_zero_iff]
        exact h0

/-! ### The restriction equivalence at equal rational subsets -/

/-- Any two rational data cutting the same rational subset have canonically
isomorphic completed localizations (the [WP] lem:small-perturbation mechanism,
decoupled from the perturbation: restriction maps both ways). -/
noncomputable def restrictionEquiv [IsHuberRing E] [HasLocLiftPowerBounded E]
    (D D' : RationalLocData E)
    (h : rationalOpen D'.T D'.s = rationalOpen D.T D.s) :
    presheafValue D ≃+* presheafValue D' :=
  { toFun := restrictionMapHom D D' h.le
    invFun := restrictionMapHom D' D h.ge
    left_inv := fun x => by
      have hcomp := congr_fun (restrictionMap_comp D D' D h.le h.ge) x
      have hid : restrictionMap D D (h.ge.trans h.le) = id := restrictionMap_id D
      rw [hid] at hcomp
      exact hcomp
    right_inv := fun x => by
      have hcomp := congr_fun (restrictionMap_comp D' D D' h.ge h.le) x
      have hid : restrictionMap D' D' (h.le.trans h.ge) = id := restrictionMap_id D'
      rw [hid] at hcomp
      exact hcomp
    map_mul' := map_mul _
    map_add' := map_add _ }

theorem restrictionEquiv_continuous [IsHuberRing E] [HasLocLiftPowerBounded E]
    (D D' : RationalLocData E)
    (h : rationalOpen D'.T D'.s = rationalOpen D.T D.s) :
    Continuous (restrictionEquiv D D' h) := by
  show Continuous (restrictionMapHom D D' h.le)
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  exact UniformSpace.Completion.continuous_extension

theorem restrictionEquiv_symm_continuous [IsHuberRing E] [HasLocLiftPowerBounded E]
    (D D' : RationalLocData E)
    (h : rationalOpen D'.T D'.s = rationalOpen D.T D.s) :
    Continuous (restrictionEquiv D D' h).symm := by
  show Continuous (restrictionMapHom D' D h.ge)
  letI : UniformSpace (Localization.Away D'.s) := D'.uniformSpace
  letI : IsTopologicalRing (Localization.Away D'.s) := D'.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D'.s) := D'.isUniformAddGroup
  exact UniformSpace.Completion.continuous_extension

theorem restrictionEquiv_canonicalMap [IsHuberRing E] [HasLocLiftPowerBounded E]
    (D D' : RationalLocData E)
    (h : rationalOpen D'.T D'.s = rationalOpen D.T D.s) (x : E) :
    restrictionEquiv D D' h (D.canonicalMap x) = D'.canonicalMap x := by
  show restrictionMapHom D D' h.le (D.canonicalMap x) = D'.canonicalMap x
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  have h1 := UniformSpace.Completion.extensionHom_coe
    (restrictionMapAlg D D' h.le)
    (restrictionMapAlg_continuous D D' h.le)
    (algebraMap E (Localization.Away D.s) x)
  have h2 : restrictionMapAlg D D' h.le
      (algebraMap E (Localization.Away D.s) x) = D'.canonicalMap x := by
    show IsLocalization.Away.lift D.s
      (HasLocLiftPowerBounded.isUnit_canonicalMap_s D D' h.le)
      (algebraMap E (Localization.Away D.s) x) = D'.canonicalMap x
    rw [IsLocalization.Away.lift_eq]
  exact h1.trans h2

end WeightedParity
