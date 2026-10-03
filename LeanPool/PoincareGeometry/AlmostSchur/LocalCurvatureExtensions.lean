/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.CurvatureVendor.Tensor

/-! # Global representatives of local tangent-section germs

A cutoff inside one chart makes both the section and its totalized chart
coefficients globally regular. The global coefficient hypotheses needed by the
vendored right-slot tensoriality theorem are proved here, not assumed.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Set Filter
open scoped Manifold ContDiff Topology
namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
local notation "TM" => (TangentSpace I : M → Type _)

/-- A finite-regularity section germ has a global representative with globally
regular coefficients in the chart at the base point. -/
theorem exists_contMDiff_section_germ_with_coefficients
    (n : ℕ) [ContMDiffVectorBundle n E TM I]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {W : Π y, TM y} {x : M}
    (hW : ContMDiffAt I (I.prod 𝓘(ℝ, E)) n (T% W) x) :
    ∃ W' : Π y, TM y,
      ContMDiff I (I.prod 𝓘(ℝ, E)) n (T% W') ∧
      W' =ᶠ[𝓝 x] W ∧ ∀ i, ContMDiff I 𝓘(ℝ, ℝ) n
        (fun y ↦ (trivializationAt E TM x).localFrameCoeff I b i y (W' y)) := by
  letI : IsManifold I (n : ℕ∞ω) M :=
    IsManifold.of_le (n := ∞) (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have he := (contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hW
  obtain ⟨U, hUA, hUo, hxU⟩ := mem_nhds_iff.mp he
  let e := trivializationAt E TM x
  let V := U ∩ e.baseSet
  have hVo : IsOpen V := hUo.inter e.open_baseSet
  have hxV : x ∈ V := ⟨hxU, mem_baseSet_trivializationAt E TM x⟩
  obtain ⟨φ, _, hφV⟩ : ∃ φ : SmoothBumpFunction I x, True ∧ tsupport φ ⊆ V :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) (c := x)).mem_iff.mp (hVo.mem_nhds hxV)
  have hφ : ContMDiff I 𝓘(ℝ, ℝ) n (φ : M → ℝ) :=
    φ.contMDiff.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have hWV : ContMDiffOn I (I.prod 𝓘(ℝ, E)) n (T% W) V :=
    fun y hy ↦ (hUA hy.1).contMDiffWithinAt
  let W' : Π y, TM y := fun y ↦ φ y • W y
  have hW' : ContMDiff I (I.prod 𝓘(ℝ, E)) n (T% W') :=
    ContMDiffOn.smul_section_of_tsupport hφ.contMDiffOn hVo hφV hWV
  refine ⟨W', hW', ?_, ?_⟩
  · filter_upwards [φ.eventuallyEq_one] with y hy
    simp only [W', hy, Pi.one_apply, one_smul]
    rfl
  · intro i
    have hbase : ContMDiffOn I 𝓘(ℝ, ℝ) n
        (fun y ↦ e.localFrameCoeff I b i y (W' y)) e.baseSet :=
      contMDiffOn_localFrameCoeff (I := I) (e := e) (b := b)
        e.open_baseSet (subset_refl _) hW'.contMDiffOn i
    have hout : ContMDiffOn I 𝓘(ℝ, ℝ) n
        (fun y ↦ e.localFrameCoeff I b i y (W' y)) (tsupport φ)ᶜ := by
      apply (contMDiffOn_const (c := (0 : ℝ))).congr
      intro y hy
      have hzero : φ y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp [W', hzero]
    apply contMDiff_of_contMDiffOn_union_of_isOpen hbase hout _ e.open_baseSet
      (isClosed_tsupport φ).isOpen_compl
    ext y
    simp only [mem_union, mem_compl_iff, mem_univ, iff_true]
    by_cases hy : y ∈ e.baseSet
    · exact Or.inl hy
    · exact Or.inr (fun hs ↦ hy (hφV hs).2)

end AlmostSchur
