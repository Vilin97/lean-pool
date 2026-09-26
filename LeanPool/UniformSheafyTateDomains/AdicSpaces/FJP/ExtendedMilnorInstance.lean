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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.ExtendedCornerPackage
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.MilnorSquareInstance

/-!
# The `⟨V⟩`-extended square as a `MilnorSquareData` (T627, campaign B)

Instantiates the abstract strict-Milnor-descent criterion at the extended
finite-jet square `PA F n = PB F n ×_{PD F n} PC F n` (T626's `extPinch`),
following the `jetSquare` template (T620) with the generic datum layer (T624),
the generic naturality/composition lemmas (T623), and the value-level Milnor
row of the abstract pinch (T625's `valueRow_*`).

Output: `isSheafy_extJetA n : IsSheafy (PA F n)` — the sheafiness of the
Gauss-normed Tate extension of the pinching algebra, for every `n`
([Reviewer] §5.1; the normed half of the B-headline).
-/

@[expose] public section

@[expose] public section

noncomputable section

namespace FiniteJet

open ValuationSpectrum TopologicalRing GraphKoszul StrictLoc

variable (F : Type*) [Field F] (n : ℕ)

/-! ### Pods and the power-bounded transport -/

/-- Pair of definition for `PA F n` (unit ball at the constant-series scale). -/
noncomputable def podPA : PairOfDefinition (PA F n) :=
  unitBallPod (polyToP (MvPolynomial.C (tA F)))
    (isUnit_tP _ (isUnit_tA F))
    (by rw [norm_tP _ (norm_tA_mul F)]; exact norm_tA_lt_one F)
    (by rw [norm_tP _ (norm_tA_mul F)]; exact norm_tA_pos F)
    (fun x => by rw [norm_tP _ (norm_tA_mul F)]
                 exact norm_tP_mul _ (norm_tA_mul F) x)

/-- Pair of definition for `PB F n`. -/
noncomputable def podPB : PairOfDefinition (PB F n) :=
  unitBallPod (polyToP (MvPolynomial.C (tB F)))
    (isUnit_tP _ (isUnit_tB F))
    (by rw [norm_tP _ (norm_tB_mul F), norm_tB]; exact norm_t_lt_one F)
    (by rw [norm_tP _ (norm_tB_mul F), norm_tB]; exact norm_t_pos F)
    (fun x => by rw [norm_tP _ (norm_tB_mul F)]
                 exact norm_tP_mul _ (norm_tB_mul F) x)

/-- Pair of definition for `PC F n`. -/
noncomputable def podPC : PairOfDefinition (PC F n) :=
  unitBallPod (polyToP (MvPolynomial.C (tC F)))
    (isUnit_tP _ (isUnit_tC F))
    (by rw [norm_tP _ (norm_tC_mul F), norm_tC]; exact norm_t_lt_one F)
    (by rw [norm_tP _ (norm_tC_mul F), norm_tC]; exact norm_t_pos F)
    (fun x => by rw [norm_tP _ (norm_tC_mul F)]
                 exact norm_tP_mul _ (norm_tC_mul F) x)

/-- Pair of definition for `PD F n`. -/
noncomputable def podPD : PairOfDefinition (PD F n) :=
  unitBallPod (polyToP (MvPolynomial.C (tD F)))
    (isUnit_tP _ (isUnit_tD F))
    (by rw [norm_tP _ (norm_tD_mul F), norm_tD]; exact norm_t_lt_one F)
    (by rw [norm_tP _ (norm_tD_mul F), norm_tD]; exact norm_t_pos F)
    (fun x => by rw [norm_tP _ (norm_tD_mul F)]
                 exact norm_tP_mul _ (norm_tD_mul F) x)

section Transport

variable {A' B' : Type*}
  [NormedCommRing A'] [IsUltrametricDist A']
  [NormedCommRing B'] [IsUltrametricDist B']

omit [IsUltrametricDist A'] in
/-- Norm-bounded sets are Huber-bounded in a seminormed ring
(submultiplicativity shrinks the ball). -/
theorem isBounded_of_norm_le {S : Set A'} {M : ℝ} (hM : 0 ≤ M)
    (hS : ∀ x ∈ S, ‖x‖ ≤ M) : TopologicalRing.IsBounded S := by
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨Metric.ball 0 (ε / (M + 1)), Metric.ball_mem_nhds 0 (by positivity), ?_⟩
  rintro _ ⟨s, hs, v, hv, rfl⟩
  rw [Metric.mem_ball, dist_zero_right] at hv
  refine hball ?_
  rw [Metric.mem_ball, dist_zero_right]
  calc ‖s * v‖ ≤ ‖s‖ * ‖v‖ := norm_mul_le _ _
    _ ≤ M * ‖v‖ := mul_le_mul_of_nonneg_right (hS s hs) (norm_nonneg v)
    _ ≤ (M + 1) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg v)
    _ < (M + 1) * (ε / (M + 1)) := by
        have hM1 : (0 : ℝ) < M + 1 := by linarith
        exact mul_lt_mul_of_pos_left hv hM1
    _ = ε := by
        have hM1 : (M + 1 : ℝ) ≠ 0 := by linarith
        field_simp

omit [IsUltrametricDist A'] in
/-- In a normed ring with a multiplicative scale, Huber-bounded sets are
norm-bounded (`t`-power division). -/
theorem exists_norm_le_of_isBounded (t : A') (ht1 : ‖t‖ < 1) (ht0 : 0 < ‖t‖)
    (hscale : ∀ x : A', ‖t * x‖ = ‖t‖ * ‖x‖)
    {S : Set A'} (hS : TopologicalRing.IsBounded S) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ S, ‖x‖ ≤ M := by
  obtain ⟨V, hV, hVS⟩ := hS (Metric.ball 0 1) (Metric.ball_mem_nhds 0 one_pos)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ ht1
  have hpow : ∀ (y : A') (j : ℕ), ‖y * t ^ j‖ = ‖t‖ ^ j * ‖y‖ := by
    intro y j
    induction j with
    | zero => simp
    | succ i ih =>
      calc ‖y * t ^ (i + 1)‖ = ‖t * (y * t ^ i)‖ := by
            rw [show y * t ^ (i + 1) = t * (y * t ^ i) from by ring]
        _ = ‖t‖ * ‖y * t ^ i‖ := hscale _
        _ = ‖t‖ * (‖t‖ ^ i * ‖y‖) := by rw [ih]
        _ = ‖t‖ ^ (i + 1) * ‖y‖ := by ring
  refine ⟨(‖t‖ ^ (k + 1))⁻¹, by positivity, fun x hx => ?_⟩
  have htk : t ^ (k + 1) ∈ V := by
    refine hball ?_
    rw [Metric.mem_ball, dist_zero_right]
    calc ‖t ^ (k + 1)‖ ≤ ‖t‖ ^ (k + 1) := norm_pow_le' t (Nat.succ_pos k)
      _ = ‖t‖ ^ k * ‖t‖ := pow_succ _ _
      _ < δ * 1 := by
          refine mul_lt_mul'' hk ht1 (by positivity) (norm_nonneg t)
      _ = δ := mul_one δ
  have hmem : x * t ^ (k + 1) ∈ Metric.ball (0 : A') 1 :=
    hVS (Set.mul_mem_mul hx htk)
  rw [Metric.mem_ball, dist_zero_right, hpow x (k + 1)] at hmem
  rw [← one_div, le_div_iff₀ (by positivity), mul_comm]
  exact hmem.le

omit [IsUltrametricDist A'] [IsUltrametricDist B'] in
/-- **Power-bounded transport along a 1-Lipschitz hom** out of a scaled corner:
the generic `A⁺ ≤ (B⁺).comap φ` input for the pushed-datum comap iffs. -/
theorem powerBounded_le_comap (t : A') (ht1 : ‖t‖ < 1) (ht0 : 0 < ‖t‖)
    (hscale : ∀ x : A', ‖t * x‖ = ‖t‖ * ‖x‖)
    (φ : A' →+* B') (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) {x : A'}
    (hx : TopologicalRing.IsPowerBounded x) :
    TopologicalRing.IsPowerBounded (φ x) := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_le_of_isBounded t ht1 ht0 hscale hx
  refine (isBounded_of_norm_le hM0 (fun y hy => ?_) : TopologicalRing.IsBounded
    (Set.range (φ x ^ · : ℕ → B')))
  obtain ⟨m, rfl⟩ := hy
  calc ‖φ x ^ m‖ = ‖φ (x ^ m)‖ := by rw [map_pow]
    _ ≤ ‖x ^ m‖ := hφ _
    _ ≤ M := hM _ ⟨m, rfl⟩

end Transport

/-- The plus-transport `(PA F n)⁺ ≤ ((PB F n)⁺).comap (extJB F n)`. -/
theorem plusLe_extJB :
    ((PA F n)⁺ : Subring (PA F n)) ≤ ((PB F n)⁺ : Subring (PB F n)).comap (extJB F n) :=
  fun _ hx => powerBounded_le_comap (polyToP (MvPolynomial.C (tA F)))
    (by rw [norm_tP _ (norm_tA_mul F)]; exact norm_tA_lt_one F)
    (by rw [norm_tP _ (norm_tA_mul F)]; exact norm_tA_pos F)
    (fun x => by rw [norm_tP _ (norm_tA_mul F)]
                 exact norm_tP_mul _ (norm_tA_mul F) x)
    (extJB F n) ((extPinch F n).norm_φB_le) hx

/-- The plus-transport `(PA F n)⁺ ≤ ((PC F n)⁺).comap (extIotaC F n)`. -/
theorem plusLe_extIotaC :
    ((PA F n)⁺ : Subring (PA F n)) ≤
      ((PC F n)⁺ : Subring (PC F n)).comap (extIotaC F n) :=
  fun _ hx => powerBounded_le_comap (polyToP (MvPolynomial.C (tA F)))
    (by rw [norm_tP _ (norm_tA_mul F)]; exact norm_tA_lt_one F)
    (by rw [norm_tP _ (norm_tA_mul F)]; exact norm_tA_pos F)
    (fun x => by rw [norm_tP _ (norm_tA_mul F)]
                 exact norm_tP_mul _ (norm_tA_mul F) x)
    (extIotaC F n) (fun p => le_of_eq ((extPinch F n).norm_φC p)) hx

/-- The plus-transport along the composite leg to `PD F n`. -/
theorem plusLe_extD :
    ((PA F n)⁺ : Subring (PA F n)) ≤
      ((PD F n)⁺ : Subring (PD F n)).comap ((extRhoC F n).comp (extIotaC F n)) :=
  fun _ hx => powerBounded_le_comap (polyToP (MvPolynomial.C (tA F)))
    (by rw [norm_tP _ (norm_tA_mul F)]; exact norm_tA_lt_one F)
    (by rw [norm_tP _ (norm_tA_mul F)]; exact norm_tA_pos F)
    (fun x => by rw [norm_tP _ (norm_tA_mul F)]
                 exact norm_tP_mul _ (norm_tA_mul F) x)
    ((extRhoC F n).comp (extIotaC F n))
    (fun p => le_trans ((extPinch F n).norm_ψC_le _)
      (le_of_eq ((extPinch F n).norm_φC p))) hx

/-! ### The pushes (rationality-gated, T620 pattern) -/

open Classical in
/-- The total `B`-push of the extended square. -/
noncomputable def extPushB : RationalLocData (PA F n) → RationalLocData (PB F n) :=
  fun D => if h : D.IsRational then pushDatumOfHom (extJB F n) (podPB F n) D h
    else trivialPlusDatum (PB F n) (podPB F n) 1

open Classical in
/-- The total `C`-push. -/
noncomputable def extPushC : RationalLocData (PA F n) → RationalLocData (PC F n) :=
  fun D => if h : D.IsRational then pushDatumOfHom (extIotaC F n) (podPC F n) D h
    else trivialPlusDatum (PC F n) (podPC F n) 1

open Classical in
/-- The total `D`-push. -/
noncomputable def extPushD : RationalLocData (PA F n) → RationalLocData (PD F n) :=
  fun D => if h : D.IsRational then
    pushDatumOfHom ((extRhoC F n).comp (extIotaC F n)) (podPD F n) D h
    else trivialPlusDatum (PD F n) (podPD F n) 1

theorem extPushB_eq {D : RationalLocData (PA F n)} (hD : D.IsRational) :
    extPushB F n D = pushDatumOfHom (extJB F n) (podPB F n) D hD := by
  simp [extPushB, dif_pos hD]

theorem extPushC_eq {D : RationalLocData (PA F n)} (hD : D.IsRational) :
    extPushC F n D = pushDatumOfHom (extIotaC F n) (podPC F n) D hD := by
  simp [extPushC, dif_pos hD]

theorem extPushD_eq {D : RationalLocData (PA F n)} (hD : D.IsRational) :
    extPushD F n D =
      pushDatumOfHom ((extRhoC F n).comp (extIotaC F n)) (podPD F n) D hD := by
  simp [extPushD, dif_pos hD]

/-! ### Subst-helpers for the row and compat fields -/

private theorem extRowInjectiveAux (U : RationalLocData (PA F n)) (hU : U.IsRational)
    {DB : RationalLocData (PB F n)} {DC : RationalLocData (PC F n)}
    (hDB : DB = pushDatumOfHom (extJB F n) (podPB F n) U hU)
    (hDC : DC = pushDatumOfHom (extIotaC F n) (podPC F n) U hU)
    (hsB : DB.s = extJB F n U.s) (hTB : ∀ t ∈ U.T, extJB F n t ∈ DB.T)
    (hsC : DC.s = extIotaC F n U.s) (hTC : ∀ t ∈ U.T, extIotaC F n t ∈ DC.T)
    (hφB : Continuous (extJB F n)) (hφC : Continuous (extIotaC F n))
    (x y : presheafValue U)
    (hB : presheafValueMapOfHom (extJB F n) hφB U DB hsB hTB x =
      presheafValueMapOfHom (extJB F n) hφB U DB hsB hTB y)
    (hC : presheafValueMapOfHom (extIotaC F n) hφC U DC hsC hTC x =
      presheafValueMapOfHom (extIotaC F n) hφC U DC hsC hTC y) :
    x = y := by
  subst hDB; subst hDC
  exact (extPinch F n).valueRow_injective (podPB F n) (podPC F n) U (cornerEnum U) hU
    (extNoethPack F n (cornerEnum U).m)
    ((extPinch F n).isClosed_IA (cornerEnum U).m U.s (cornerEnum U).f
      (extNoethPack F n (cornerEnum U).m) ((cornerEnum U).span_eq_top U hU))
    ((extPinch F n).isClosed_pushB U (cornerEnum U)
      (extNoethPack F n (cornerEnum U).m).hPB
      (extNoethPack F n (cornerEnum U).m).hPBball)
    ((extPinch F n).isClosed_pushC U (cornerEnum U)
      (extNoethPack F n (cornerEnum U).m).hPC
      (extNoethPack F n (cornerEnum U).m).hPCball)
    hφB hφC hsB hTB hsC hTC x y hB hC

private theorem extRowGlueAux (U : RationalLocData (PA F n)) (hU : U.IsRational)
    {DB : RationalLocData (PB F n)} {DC : RationalLocData (PC F n)}
    {DD : RationalLocData (PD F n)}
    (hDB : DB = pushDatumOfHom (extJB F n) (podPB F n) U hU)
    (hDC : DC = pushDatumOfHom (extIotaC F n) (podPC F n) U hU)
    (hDD : DD = pushDatumOfHom ((extRhoC F n).comp (extIotaC F n)) (podPD F n) U hU)
    (hsB : DB.s = extJB F n U.s) (hTB : ∀ t ∈ U.T, extJB F n t ∈ DB.T)
    (hsC : DC.s = extIotaC F n U.s) (hTC : ∀ t ∈ U.T, extIotaC F n t ∈ DC.T)
    (hsBD : DD.s = extRhoB F n DB.s) (hTBD : ∀ t ∈ DB.T, extRhoB F n t ∈ DD.T)
    (hsCD : DD.s = extRhoC F n DC.s) (hTCD : ∀ t ∈ DC.T, extRhoC F n t ∈ DD.T)
    (hφB : Continuous (extJB F n)) (hφC : Continuous (extIotaC F n))
    (hψB : Continuous (extRhoB F n)) (hψC : Continuous (extRhoC F n))
    (b : presheafValue DB) (c : presheafValue DC)
    (h : presheafValueMapOfHom (extRhoB F n) hψB DB DD hsBD hTBD b =
      presheafValueMapOfHom (extRhoC F n) hψC DC DD hsCD hTCD c) :
    ∃ x : presheafValue U,
      presheafValueMapOfHom (extJB F n) hφB U DB hsB hTB x = b ∧
      presheafValueMapOfHom (extIotaC F n) hφC U DC hsC hTC x = c := by
  subst hDB; subst hDC; subst hDD
  exact (extPinch F n).valueRow_glue (podPB F n) (podPC F n) (podPD F n) U
    (cornerEnum U) hU (extNoethPack F n (cornerEnum U).m)
    ((extPinch F n).isClosed_IA (cornerEnum U).m U.s (cornerEnum U).f
      (extNoethPack F n (cornerEnum U).m) ((cornerEnum U).span_eq_top U hU))
    ((extPinch F n).isClosed_pushB U (cornerEnum U)
      (extNoethPack F n (cornerEnum U).m).hPB
      (extNoethPack F n (cornerEnum U).m).hPBball)
    ((extPinch F n).isClosed_pushC U (cornerEnum U)
      (extNoethPack F n (cornerEnum U).m).hPC
      (extNoethPack F n (cornerEnum U).m).hPCball)
    ((extPinch F n).isClosed_pushD U (cornerEnum U)
      (extNoethPack F n (cornerEnum U).m).hPD
      (extNoethPack F n (cornerEnum U).m).hPDball)
    hφB hφC hψB hψC hsB hTB hsC hTC hsBD hTBD hsCD hTCD b c h

private theorem extRowEmbeddingAux (U : RationalLocData (PA F n)) (hU : U.IsRational)
    {DB : RationalLocData (PB F n)} {DC : RationalLocData (PC F n)}
    (hDB : DB = pushDatumOfHom (extJB F n) (podPB F n) U hU)
    (hDC : DC = pushDatumOfHom (extIotaC F n) (podPC F n) U hU)
    (hsB : DB.s = extJB F n U.s) (hTB : ∀ t ∈ U.T, extJB F n t ∈ DB.T)
    (hsC : DC.s = extIotaC F n U.s) (hTC : ∀ t ∈ U.T, extIotaC F n t ∈ DC.T)
    (hφB : Continuous (extJB F n)) (hφC : Continuous (extIotaC F n)) :
    Topology.IsEmbedding (fun x : presheafValue U =>
      (presheafValueMapOfHom (extJB F n) hφB U DB hsB hTB x,
       presheafValueMapOfHom (extIotaC F n) hφC U DC hsC hTC x)) := by
  subst hDB; subst hDC
  exact (extPinch F n).valueRow_embedding (podPB F n) (podPC F n) U (cornerEnum U) hU
    (extNoethPack F n (cornerEnum U).m)
    ((extPinch F n).isClosed_IA (cornerEnum U).m U.s (cornerEnum U).f
      (extNoethPack F n (cornerEnum U).m) ((cornerEnum U).span_eq_top U hU))
    ((extPinch F n).isClosed_pushB U (cornerEnum U)
      (extNoethPack F n (cornerEnum U).m).hPB
      (extNoethPack F n (cornerEnum U).m).hPBball)
    ((extPinch F n).isClosed_pushC U (cornerEnum U)
      (extNoethPack F n (cornerEnum U).m).hPC
      (extNoethPack F n (cornerEnum U).m).hPCball)
    hφB hφC hsB hTB hsC hTC

private theorem extPushedCompatBAux (U₁ U₂ : RationalLocData (PA F n))
    (hU₁ : U₁.IsRational) (hU₂ : U₂.IsRational)
    {DB₁ DB₂ : RationalLocData (PB F n)}
    (hDB₁ : DB₁ = pushDatumOfHom (extJB F n) (podPB F n) U₁ hU₁)
    (hDB₂ : DB₂ = pushDatumOfHom (extJB F n) (podPB F n) U₂ hU₂)
    (hφ : Continuous (extJB F n))
    (hs₁ : DB₁.s = extJB F n U₁.s) (hT₁ : ∀ t ∈ U₁.T, extJB F n t ∈ DB₁.T)
    (hs₂ : DB₂.s = extJB F n U₂.s) (hT₂ : ∀ t ∈ U₂.T, extJB F n t ∈ DB₂.T)
    (x₁ : presheafValue U₁) (x₂ : presheafValue U₂)
    (hmatch : ∀ (D₃ : RationalLocData (PA F n))
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen U₁.T U₁.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen U₂.T U₂.s),
      restrictionMap U₁ D₃ h₃₁ x₁ = restrictionMap U₂ D₃ h₃₂ x₂)
    (E₃ : RationalLocData (PB F n))
    (hE₁ : rationalOpen E₃.T E₃.s ⊆ rationalOpen DB₁.T DB₁.s)
    (hE₂ : rationalOpen E₃.T E₃.s ⊆ rationalOpen DB₂.T DB₂.s) :
    restrictionMap DB₁ E₃ hE₁
        (presheafValueMapOfHom (extJB F n) hφ U₁ DB₁ hs₁ hT₁ x₁) =
      restrictionMap DB₂ E₃ hE₂
        (presheafValueMapOfHom (extJB F n) hφ U₂ DB₂ hs₂ hT₂ x₂) := by
  subst hDB₁; subst hDB₂
  have hsub₁ : rationalOpen (interDatumOfRational U₁ U₂ hU₁ hU₂).T (interDatumOfRational U₁ U₂ hU₁ hU₂).s ⊆ rationalOpen U₁.T U₁.s := by
    rw [rationalOpen_interDatumOfRational]
    exact Set.inter_subset_left
  have hsub₂ : rationalOpen (interDatumOfRational U₁ U₂ hU₁ hU₂).T (interDatumOfRational U₁ U₂ hU₁ hU₂).s ⊆ rationalOpen U₂.T U₂.s := by
    rw [rationalOpen_interDatumOfRational]
    exact Set.inter_subset_right
  have hpush₁ : rationalOpen (pushDatumOfHom (extJB F n) (podPB F n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)).T
      (pushDatumOfHom (extJB F n) (podPB F n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)).s ⊆
      rationalOpen (pushDatumOfHom (extJB F n) (podPB F n) U₁ hU₁).T
        (pushDatumOfHom (extJB F n) (podPB F n) U₁ hU₁).s := by
    rw [pushDatumOfHom_interOpen hφ
      (plusLe_extJB F n) (podPB F n) U₁ U₂ hU₁ hU₂]
    exact Set.inter_subset_left
  have hpush₂ : rationalOpen (pushDatumOfHom (extJB F n) (podPB F n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)).T
      (pushDatumOfHom (extJB F n) (podPB F n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)).s ⊆
      rationalOpen (pushDatumOfHom (extJB F n) (podPB F n) U₂ hU₂).T
        (pushDatumOfHom (extJB F n) (podPB F n) U₂ hU₂).s := by
    rw [pushDatumOfHom_interOpen hφ
      (plusLe_extJB F n) (podPB F n) U₁ U₂ hU₁ hU₂]
    exact Set.inter_subset_right
  have h₃I : rationalOpen E₃.T E₃.s ⊆
      rationalOpen (pushDatumOfHom (extJB F n) (podPB F n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)).T
        (pushDatumOfHom (extJB F n) (podPB F n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)).s := by
    rw [pushDatumOfHom_interOpen hφ
      (plusLe_extJB F n) (podPB F n) U₁ U₂ hU₁ hU₂]
    exact Set.subset_inter hE₁ hE₂
  have hpushed := congrArg
    (presheafValueMapOfHom (extJB F n) hφ (interDatumOfRational U₁ U₂ hU₁ hU₂)
      (pushDatumOfHom (extJB F n) (podPB F n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)) rfl
      (fun t ht => Finset.mem_image_of_mem _ ht))
    (hmatch (interDatumOfRational U₁ U₂ hU₁ hU₂) hsub₁ hsub₂)
  rw [presheafValueMapOfHom_restriction (extJB F n) hφ U₁ (interDatumOfRational U₁ U₂ hU₁ hU₂)
      (pushDatumOfHom (extJB F n) (podPB F n) U₁ hU₁)
      (pushDatumOfHom (extJB F n) (podPB F n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)) hs₁ hT₁ rfl
      (fun t ht => Finset.mem_image_of_mem _ ht) hsub₁ hpush₁ x₁,
    presheafValueMapOfHom_restriction (extJB F n) hφ U₂ (interDatumOfRational U₁ U₂ hU₁ hU₂)
      (pushDatumOfHom (extJB F n) (podPB F n) U₂ hU₂)
      (pushDatumOfHom (extJB F n) (podPB F n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)) hs₂ hT₂ rfl
      (fun t ht => Finset.mem_image_of_mem _ ht) hsub₂ hpush₂ x₂] at hpushed
  have hfac₁ := congrFun (restrictionMap_comp
    (pushDatumOfHom (extJB F n) (podPB F n) U₁ hU₁)
    (pushDatumOfHom (extJB F n) (podPB F n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)) E₃ hpush₁ h₃I)
    (presheafValueMapOfHom (extJB F n) hφ U₁
      (pushDatumOfHom (extJB F n) (podPB F n) U₁ hU₁) hs₁ hT₁ x₁)
  have hfac₂ := congrFun (restrictionMap_comp
    (pushDatumOfHom (extJB F n) (podPB F n) U₂ hU₂)
    (pushDatumOfHom (extJB F n) (podPB F n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)) E₃ hpush₂ h₃I)
    (presheafValueMapOfHom (extJB F n) hφ U₂
      (pushDatumOfHom (extJB F n) (podPB F n) U₂ hU₂) hs₂ hT₂ x₂)
  simp only [Function.comp_apply] at hfac₁ hfac₂
  rw [← hfac₁, ← hfac₂, hpushed]

private theorem extPushedCompatCAux (U₁ U₂ : RationalLocData (PA F n))
    (hU₁ : U₁.IsRational) (hU₂ : U₂.IsRational)
    {DC₁ DC₂ : RationalLocData (PC F n)}
    (hDC₁ : DC₁ = pushDatumOfHom (extIotaC F n) (podPC F n) U₁ hU₁)
    (hDC₂ : DC₂ = pushDatumOfHom (extIotaC F n) (podPC F n) U₂ hU₂)
    (hφ : Continuous (extIotaC F n))
    (hs₁ : DC₁.s = extIotaC F n U₁.s) (hT₁ : ∀ t ∈ U₁.T, extIotaC F n t ∈ DC₁.T)
    (hs₂ : DC₂.s = extIotaC F n U₂.s) (hT₂ : ∀ t ∈ U₂.T, extIotaC F n t ∈ DC₂.T)
    (x₁ : presheafValue U₁) (x₂ : presheafValue U₂)
    (hmatch : ∀ (D₃ : RationalLocData (PA F n))
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen U₁.T U₁.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen U₂.T U₂.s),
      restrictionMap U₁ D₃ h₃₁ x₁ = restrictionMap U₂ D₃ h₃₂ x₂)
    (E₃ : RationalLocData (PC F n))
    (hE₁ : rationalOpen E₃.T E₃.s ⊆ rationalOpen DC₁.T DC₁.s)
    (hE₂ : rationalOpen E₃.T E₃.s ⊆ rationalOpen DC₂.T DC₂.s) :
    restrictionMap DC₁ E₃ hE₁
        (presheafValueMapOfHom (extIotaC F n) hφ U₁ DC₁ hs₁ hT₁ x₁) =
      restrictionMap DC₂ E₃ hE₂
        (presheafValueMapOfHom (extIotaC F n) hφ U₂ DC₂ hs₂ hT₂ x₂) := by
  subst hDC₁; subst hDC₂
  have hsub₁ : rationalOpen (interDatumOfRational U₁ U₂ hU₁ hU₂).T (interDatumOfRational U₁ U₂ hU₁ hU₂).s ⊆ rationalOpen U₁.T U₁.s := by
    rw [rationalOpen_interDatumOfRational]
    exact Set.inter_subset_left
  have hsub₂ : rationalOpen (interDatumOfRational U₁ U₂ hU₁ hU₂).T (interDatumOfRational U₁ U₂ hU₁ hU₂).s ⊆ rationalOpen U₂.T U₂.s := by
    rw [rationalOpen_interDatumOfRational]
    exact Set.inter_subset_right
  have hpush₁ : rationalOpen (pushDatumOfHom (extIotaC F n) (podPC F n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)).T
      (pushDatumOfHom (extIotaC F n) (podPC F n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)).s ⊆
      rationalOpen (pushDatumOfHom (extIotaC F n) (podPC F n) U₁ hU₁).T
        (pushDatumOfHom (extIotaC F n) (podPC F n) U₁ hU₁).s := by
    rw [pushDatumOfHom_interOpen hφ
      (plusLe_extIotaC F n) (podPC F n) U₁ U₂ hU₁ hU₂]
    exact Set.inter_subset_left
  have hpush₂ : rationalOpen (pushDatumOfHom (extIotaC F n) (podPC F n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)).T
      (pushDatumOfHom (extIotaC F n) (podPC F n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)).s ⊆
      rationalOpen (pushDatumOfHom (extIotaC F n) (podPC F n) U₂ hU₂).T
        (pushDatumOfHom (extIotaC F n) (podPC F n) U₂ hU₂).s := by
    rw [pushDatumOfHom_interOpen hφ
      (plusLe_extIotaC F n) (podPC F n) U₁ U₂ hU₁ hU₂]
    exact Set.inter_subset_right
  have h₃I : rationalOpen E₃.T E₃.s ⊆
      rationalOpen (pushDatumOfHom (extIotaC F n) (podPC F n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)).T
        (pushDatumOfHom (extIotaC F n) (podPC F n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)).s := by
    rw [pushDatumOfHom_interOpen hφ
      (plusLe_extIotaC F n) (podPC F n) U₁ U₂ hU₁ hU₂]
    exact Set.subset_inter hE₁ hE₂
  have hpushed := congrArg
    (presheafValueMapOfHom (extIotaC F n) hφ (interDatumOfRational U₁ U₂ hU₁ hU₂)
      (pushDatumOfHom (extIotaC F n) (podPC F n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)) rfl
      (fun t ht => Finset.mem_image_of_mem _ ht))
    (hmatch (interDatumOfRational U₁ U₂ hU₁ hU₂) hsub₁ hsub₂)
  rw [presheafValueMapOfHom_restriction (extIotaC F n) hφ U₁ (interDatumOfRational U₁ U₂ hU₁ hU₂)
      (pushDatumOfHom (extIotaC F n) (podPC F n) U₁ hU₁)
      (pushDatumOfHom (extIotaC F n) (podPC F n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)) hs₁ hT₁ rfl
      (fun t ht => Finset.mem_image_of_mem _ ht) hsub₁ hpush₁ x₁,
    presheafValueMapOfHom_restriction (extIotaC F n) hφ U₂ (interDatumOfRational U₁ U₂ hU₁ hU₂)
      (pushDatumOfHom (extIotaC F n) (podPC F n) U₂ hU₂)
      (pushDatumOfHom (extIotaC F n) (podPC F n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)) hs₂ hT₂ rfl
      (fun t ht => Finset.mem_image_of_mem _ ht) hsub₂ hpush₂ x₂] at hpushed
  have hfac₁ := congrFun (restrictionMap_comp
    (pushDatumOfHom (extIotaC F n) (podPC F n) U₁ hU₁)
    (pushDatumOfHom (extIotaC F n) (podPC F n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)) E₃ hpush₁ h₃I)
    (presheafValueMapOfHom (extIotaC F n) hφ U₁
      (pushDatumOfHom (extIotaC F n) (podPC F n) U₁ hU₁) hs₁ hT₁ x₁)
  have hfac₂ := congrFun (restrictionMap_comp
    (pushDatumOfHom (extIotaC F n) (podPC F n) U₂ hU₂)
    (pushDatumOfHom (extIotaC F n) (podPC F n) (interDatumOfRational U₁ U₂ hU₁ hU₂) (interDatumOfRational_isRational hU₁ hU₂)) E₃ hpush₂ h₃I)
    (presheafValueMapOfHom (extIotaC F n) hφ U₂
      (pushDatumOfHom (extIotaC F n) (podPC F n) U₂ hU₂) hs₂ hT₂ x₂)
  simp only [Function.comp_apply] at hfac₁ hfac₂
  rw [← hfac₁, ← hfac₂, hpushed]

/-! ### The extended square as a `MilnorSquareData` -/

/-- **The `⟨V⟩`-extended finite-jet square as a strict Milnor square-with-rows**
(T627): the T620 template at the extended corners, with the generic datum layer
and the abstract pinch's value-level row. -/
noncomputable def extJetSquare :
    MilnorSquareData (extJB F n) (extIotaC F n) ((extRhoC F n).comp (extIotaC F n))
      ((extPinch F n).φB_continuous) ((extPinch F n).φC_continuous)
      (by exact ((extPinch F n).ψC_continuous).comp ((extPinch F n).φC_continuous)) where
  pushB := extPushB F n
  pushC := extPushC F n
  pushD := extPushD F n
  pushB_s := by
    intro U hU
    rw [extPushB_eq F n hU]
    rfl
  pushC_s := by
    intro U hU
    rw [extPushC_eq F n hU]
    rfl
  pushD_s := by
    intro U hU
    rw [extPushD_eq F n hU]
    rfl
  pushB_T := by
    classical
    intro U hU t ht
    rw [extPushB_eq F n hU]
    exact Finset.mem_image_of_mem _ ht
  pushC_T := by
    classical
    intro U hU t ht
    rw [extPushC_eq F n hU]
    exact Finset.mem_image_of_mem _ ht
  pushD_T := by
    classical
    intro U hU t ht
    rw [extPushD_eq F n hU]
    exact Finset.mem_image_of_mem _ ht
  pushB_isRational := by
    intro U hU
    rw [extPushB_eq F n hU]
    exact pushDatumOfHom_isRational _ _ hU
  pushC_isRational := by
    intro U hU
    rw [extPushC_eq F n hU]
    exact pushDatumOfHom_isRational _ _ hU
  pushD_isRational := by
    intro U hU
    rw [extPushD_eq F n hU]
    exact pushDatumOfHom_isRational _ _ hU
  legB := extRhoB F n
  legC := extRhoC F n
  hlegB := (extPinch F n).ψB_continuous
  hlegC := (extPinch F n).ψC_continuous
  legB_s := by
    intro U hU
    rw [extPushB_eq F n hU, extPushD_eq F n hU]
    exact (ext_square_commutes F n U.s).symm
  legC_s := by
    intro U hU
    rw [extPushC_eq F n hU, extPushD_eq F n hU]
    rfl
  legB_T := by
    classical
    intro U hU t ht
    rw [extPushB_eq F n hU] at ht
    rw [extPushD_eq F n hU]
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    rw [ext_square_commutes F n u]
    exact Finset.mem_image_of_mem _ hu
  legC_T := by
    classical
    intro U hU t ht
    rw [extPushC_eq F n hU] at ht
    rw [extPushD_eq F n hU]
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_image_of_mem _ hu
  row_injective := by
    intro U hU x y hB hC
    exact extRowInjectiveAux F n U hU (extPushB_eq F n hU) (extPushC_eq F n hU)
      _ _ _ _ _ _ x y hB hC
  row_glue := by
    intro U hU b c h
    exact extRowGlueAux F n U hU (extPushB_eq F n hU) (extPushC_eq F n hU)
      (extPushD_eq F n hU) _ _ _ _ _ _ _ _ _ _ _ _ b c h
  row_embedding := by
    intro U hU
    exact extRowEmbeddingAux F n U hU (extPushB_eq F n hU) (extPushC_eq F n hU)
      _ _ _ _ _ _
  pushB_mono := by
    intro U U' hU hU' hsub v hv
    rw [extPushB_eq F n hU'] at hv
    rw [extPushB_eq F n hU]
    have hvspa := rationalOpen_subset_spa hv
    exact (mem_rationalOpen_pushDatumOfHom_iff ((extPinch F n).φB_continuous)
      (plusLe_extJB F n) (podPB F n) U hU v hvspa).mpr
      (hsub ((mem_rationalOpen_pushDatumOfHom_iff ((extPinch F n).φB_continuous)
        (plusLe_extJB F n) (podPB F n) U' hU' v hvspa).mp hv))
  pushC_mono := by
    intro U U' hU hU' hsub v hv
    rw [extPushC_eq F n hU'] at hv
    rw [extPushC_eq F n hU]
    have hvspa := rationalOpen_subset_spa hv
    exact (mem_rationalOpen_pushDatumOfHom_iff ((extPinch F n).φC_continuous)
      (plusLe_extIotaC F n) (podPC F n) U hU v hvspa).mpr
      (hsub ((mem_rationalOpen_pushDatumOfHom_iff ((extPinch F n).φC_continuous)
        (plusLe_extIotaC F n) (podPC F n) U' hU' v hvspa).mp hv))
  push_natural_B := by
    intro U U' hU hU' h x
    exact presheafValueMapOfHom_restriction (extJB F n) ((extPinch F n).φB_continuous)
      U U' (extPushB F n U) (extPushB F n U') _ _ _ _ h _ x
  push_natural_C := by
    intro U U' hU hU' h x
    exact presheafValueMapOfHom_restriction (extIotaC F n) ((extPinch F n).φC_continuous)
      U U' (extPushC F n U) (extPushC F n U') _ _ _ _ h _ x
  pushB_cover := by
    intro U S hU hS hcov w hw
    rw [extPushB_eq F n hU] at hw
    have hwspa := rationalOpen_subset_spa hw
    obtain ⟨W, hWS, hWmem⟩ := hcov (ValuationSpectrum.comap (extJB F n) w)
      ((mem_rationalOpen_pushDatumOfHom_iff ((extPinch F n).φB_continuous)
        (plusLe_extJB F n) (podPB F n) U hU w hwspa).mp hw)
    refine ⟨W, hWS, ?_⟩
    rw [extPushB_eq F n (hS W hWS)]
    exact (mem_rationalOpen_pushDatumOfHom_iff ((extPinch F n).φB_continuous)
      (plusLe_extJB F n) (podPB F n) W (hS W hWS) w hwspa).mpr hWmem
  pushC_cover := by
    intro U S hU hS hcov w hw
    rw [extPushC_eq F n hU] at hw
    have hwspa := rationalOpen_subset_spa hw
    obtain ⟨W, hWS, hWmem⟩ := hcov (ValuationSpectrum.comap (extIotaC F n) w)
      ((mem_rationalOpen_pushDatumOfHom_iff ((extPinch F n).φC_continuous)
        (plusLe_extIotaC F n) (podPC F n) U hU w hwspa).mp hw)
    refine ⟨W, hWS, ?_⟩
    rw [extPushC_eq F n (hS W hWS)]
    exact (mem_rationalOpen_pushDatumOfHom_iff ((extPinch F n).φC_continuous)
      (plusLe_extIotaC F n) (podPC F n) W (hS W hWS) w hwspa).mpr hWmem
  pushD_cover := by
    intro U S hU hS hcov w hw
    rw [extPushD_eq F n hU] at hw
    have hwspa := rationalOpen_subset_spa hw
    obtain ⟨W, hWS, hWmem⟩ := hcov
      (ValuationSpectrum.comap ((extRhoC F n).comp (extIotaC F n)) w)
      ((mem_rationalOpen_pushDatumOfHom_iff
        (by exact ((extPinch F n).ψC_continuous).comp ((extPinch F n).φC_continuous))
        (plusLe_extD F n) (podPD F n) U hU w hwspa).mp hw)
    refine ⟨W, hWS, ?_⟩
    rw [extPushD_eq F n (hS W hWS)]
    exact (mem_rationalOpen_pushDatumOfHom_iff
      (by exact ((extPinch F n).ψC_continuous).comp ((extPinch F n).φC_continuous))
      (plusLe_extD F n) (podPD F n) W (hS W hWS) w hwspa).mpr hWmem
  pushD_mono := by
    intro U U' hU hU' hsub v hv
    rw [extPushD_eq F n hU'] at hv
    rw [extPushD_eq F n hU]
    have hvspa := rationalOpen_subset_spa hv
    exact (mem_rationalOpen_pushDatumOfHom_iff
      (by exact ((extPinch F n).ψC_continuous).comp ((extPinch F n).φC_continuous))
      (plusLe_extD F n) (podPD F n) U hU v hvspa).mpr
      (hsub ((mem_rationalOpen_pushDatumOfHom_iff
        (by exact ((extPinch F n).ψC_continuous).comp ((extPinch F n).φC_continuous))
        (plusLe_extD F n) (podPD F n) U' hU' v hvspa).mp hv))
  leg_natural_B := by
    intro U U' hU hU' h b
    exact presheafValueMapOfHom_restriction (extRhoB F n) ((extPinch F n).ψB_continuous)
      (extPushB F n U) (extPushB F n U') (extPushD F n U) (extPushD F n U')
      _ _ _ _ _ _ b
  leg_natural_C := by
    intro U U' hU hU' h c
    exact presheafValueMapOfHom_restriction (extRhoC F n) ((extPinch F n).ψC_continuous)
      (extPushC F n U) (extPushC F n U') (extPushD F n U) (extPushD F n U')
      _ _ _ _ _ _ c
  row_comm := by
    intro U hU x
    have hsχ : (extPushD F n U).s = ((extRhoC F n).comp (extIotaC F n)) U.s := by
      rw [extPushD_eq F n hU]; rfl
    have hTχ : ∀ t ∈ U.T,
        ((extRhoC F n).comp (extIotaC F n)) t ∈ (extPushD F n U).T := by
      classical
      intro t ht
      rw [extPushD_eq F n hU]
      exact Finset.mem_image_of_mem _ ht
    refine (presheafValueMapOfHom_comp (extJB F n) ((extPinch F n).φB_continuous)
      (extRhoB F n) ((extPinch F n).ψB_continuous)
      ((extRhoC F n).comp (extIotaC F n))
      (by exact ((extPinch F n).ψC_continuous).comp ((extPinch F n).φC_continuous))
      (RingHom.ext fun a => ext_square_commutes F n a)
      U (extPushB F n U) (extPushD F n U) _ _ _ _ hsχ hTχ x).trans
      (presheafValueMapOfHom_comp (extIotaC F n) ((extPinch F n).φC_continuous)
        (extRhoC F n) ((extPinch F n).ψC_continuous)
        ((extRhoC F n).comp (extIotaC F n))
        (by exact ((extPinch F n).ψC_continuous).comp ((extPinch F n).φC_continuous))
        rfl U (extPushC F n U) (extPushD F n U) _ _ _ _ hsχ hTχ x).symm
  pushedCompat_B := by
    intro U₁ U₂ hU₁ hU₂ x₁ x₂ hmatch E₃ hE₁ hE₂
    exact extPushedCompatBAux F n U₁ U₂ hU₁ hU₂ (extPushB_eq F n hU₁)
      (extPushB_eq F n hU₂) _ _ _ _ _ x₁ x₂ hmatch E₃ hE₁ hE₂
  pushedCompat_C := by
    intro U₁ U₂ hU₁ hU₂ x₁ x₂ hmatch E₃ hE₁ hE₂
    exact extPushedCompatCAux F n U₁ U₂ hU₁ hU₂ (extPushC_eq F n hU₁)
      (extPushC_eq F n hU₂) _ _ _ _ _ x₁ x₂ hmatch E₃ hE₁ hE₂

/-! ### Vertex sheafiness and the headline -/

/-- Strong noetherianity of the extended `B`-corner (Fubini + the base facts). -/
theorem isStronglyNoetherian_PB : IsStronglyNoetherian (PB F n) := by
  refine ⟨fun k => ?_⟩
  obtain ⟨e, -⟩ := exists_flattenPP (JetB F) n k
  have h1 : IsNoetherianRing (P (PB F n) k) := by
    have := isNoetherianRing_PB F (n + k)
    exact isNoetherianRing_of_surjective (PB F (n + k)) _
      e.symm.toRingHom e.symm.surjective
  exact isNoetherianRing_of_surjective (P (PB F n) k) _
    (UnitDiscExample.restrictedGaussEquiv (PB F n) k).toRingHom
    (RingEquiv.surjective _)

theorem isStronglyNoetherian_PC : IsStronglyNoetherian (PC F n) := by
  refine ⟨fun k => ?_⟩
  obtain ⟨e, -⟩ := exists_flattenPP (JetC F) n k
  have h1 : IsNoetherianRing (P (PC F n) k) := by
    have := isNoetherianRing_PC F (n + k)
    exact isNoetherianRing_of_surjective (PC F (n + k)) _
      e.symm.toRingHom e.symm.surjective
  exact isNoetherianRing_of_surjective (P (PC F n) k) _
    (UnitDiscExample.restrictedGaussEquiv (PC F n) k).toRingHom
    (RingEquiv.surjective _)

theorem isStronglyNoetherian_PD : IsStronglyNoetherian (PD F n) := by
  refine ⟨fun k => ?_⟩
  obtain ⟨e, -⟩ := exists_flattenPP (JetD F) n k
  have h1 : IsNoetherianRing (P (PD F n) k) := by
    have := isNoetherianRing_PD F (n + k)
    exact isNoetherianRing_of_surjective (PD F (n + k)) _
      e.symm.toRingHom e.symm.surjective
  exact isNoetherianRing_of_surjective (P (PD F n) k) _
    (UnitDiscExample.restrictedGaussEquiv (PD F n) k).toRingHom
    (RingEquiv.surjective _)

/-- Sheafiness of the extended `B`-corner (Wedhorn 8.28(b), clean form). -/
theorem isSheafy_PB : IsSheafy (PB F n) := by
  have := isStronglyNoetherian_PB F n
  exact ValuationSpectrum.isSheafy_of_stronglyNoetherian_828b

theorem isSheafy_PC : IsSheafy (PC F n) := by
  have := isStronglyNoetherian_PC F n
  exact ValuationSpectrum.isSheafy_of_stronglyNoetherian_828b

theorem isSheafy_PD : IsSheafy (PD F n) := by
  have := isStronglyNoetherian_PD F n
  exact ValuationSpectrum.isSheafy_of_stronglyNoetherian_828b

/-- **Sheafiness of the `⟨V⟩`-extended pinching algebra** ([Reviewer] §5.1, the
normed half of the B-headline): the Gauss-normed Tate extension `PA F n` is
sheafy, by abstract strict Milnor descent at the extended square. -/
theorem isSheafy_extJetA : IsSheafy (PA F n) := by
  classical
  let _iB : DecidableEq (RationalLocData (PB F n)) := Classical.decEq _
  let _iC : DecidableEq (RationalLocData (PC F n)) := Classical.decEq _
  let _iD : DecidableEq (RationalLocData (PD F n)) := Classical.decEq _
  exact isSheafy_of_milnorSquare (extJB F n) (extIotaC F n)
    ((extRhoC F n).comp (extIotaC F n))
    ((extPinch F n).φB_continuous) ((extPinch F n).φC_continuous)
    (by rw [RingHom.coe_comp]
        exact ((extPinch F n).ψC_continuous).comp ((extPinch F n).φC_continuous))
    (extJetSquare F n) (isSheafy_PB F n) (isSheafy_PC F n) (isSheafy_PD F n)

end FiniteJet
