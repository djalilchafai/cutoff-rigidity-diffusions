module

public import CutoffRigidity.Riemann.DiffInstance2
public import CutoffRigidity.Riemann.EigenFinite
public import CutoffRigidity.Riemann.DiffGapHilbert
public import CutoffRigidity.Riemann.DiffGapManifold

/-! # Attainment of the spectral gap from compactness of the energy balls (workstream HPOS)
Proof (HPOS-G): Poincare on test functions from the definition of `mSpectralGap`, abstract
minimiser from `DirFriedrichs.exists_eigen_of_compact` (`DiffGapHilbert`), smoothness by
`diff_eigen_smooth`, identification of the pointwise equation by `integral_mul_generator_comm` and
`eq_zero_of_integral_test` (`DiffGapManifold`). -/

@[expose] public section

open Bundle MeasureTheory Filter Set ProbabilityTheory
open scoped Manifold ContDiff ENNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Gap

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsProbabilityMeasure μ]
  (hμ : IsWeightedVolume F μ V) {ρ : ℝ} (hρ : 0 < ρ) (hCD : CD F ρ V)
  (hgap : mSpectralGap F μ = ρ)

theorem L2_inner_eq' (u w : M →₂[μ] ℝ) :
    inner ℝ u w = ∫ x, (u : M → ℝ) x * (w : M → ℝ) x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [mul_comm]

theorem norm_oneL2 : ‖oneL2 μ‖ = 1 := by
  have h : ‖oneL2 μ‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_oneL2]
    rw [integral_congr_ae (coeFn_oneL2 μ)]
    simp
  have h0 := norm_nonneg (oneL2 μ)
  nlinarith

/-- The variance of a test function is the squared norm of its `L²` projection onto `1^⊥`. -/
theorem norm_sq_proj_testToL2 (a : testSub F M) :
    ‖testToL2 F μ a - inner ℝ (testToL2 F μ a) (oneL2 μ) • oneL2 μ‖ ^ 2 =
      variance (a : M → ℝ) μ := by
  have hm : MemLp (a : M → ℝ) 2 μ := testSub_memLp F a μ
  set c : ℝ := ∫ x, (a : M → ℝ) x ∂μ with hc
  have hci : inner ℝ (testToL2 F μ a) (oneL2 μ) = c := by
    rw [inner_oneL2]
    exact integral_congr_ae (coeFn_testToL2 F μ a)
  rw [hci]
  set u := testToL2 F μ a - c • oneL2 μ with hu
  have hae : (u : M → ℝ) =ᵐ[μ] fun x => (a : M → ℝ) x - c := by
    filter_upwards [Lp.coeFn_sub (testToL2 F μ a) (c • oneL2 μ),
      Lp.coeFn_smul c (oneL2 μ), coeFn_oneL2 μ, coeFn_testToL2 F μ a] with x h1 h2 h3 h4
    rw [hu, h1]
    simp only [Pi.sub_apply, h2, Pi.smul_apply, h3, smul_eq_mul, h4]
    ring
  have h1 : ‖u‖ ^ 2 = ∫ x, ((u : M → ℝ) x) ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2_inner_eq']
    exact integral_congr_ae (Eventually.of_forall fun x => by simp [sq])
  rw [h1, variance_eq_integral hm.aemeasurable]
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  simp [hx, hc]

include hV hμ hρ hgap in
/-- Poincare inequality on `D` with constant `ρ`. -/
theorem poincare_D (f : (diffFormData F hV hμ).D) :
    ρ * ‖(f : M →₂[μ] ℝ) - inner ℝ (f : M →₂[μ] ℝ) (oneL2 μ) • oneL2 μ‖ ^ 2 ≤
      (diffFormData F hV hμ).en f f := by
  obtain ⟨_, a, rfl⟩ := f
  show ρ * ‖testToL2 F μ a - inner ℝ (testToL2 F μ a) (oneL2 μ) • oneL2 μ‖ ^ 2 ≤ _
  rw [norm_sq_proj_testToL2 F, en_diffFormData]
  have hcar : ∫ x, carre F (a : M → ℝ) (a : M → ℝ) x ∂μ =
      ∫ x, ‖mgrad F (a : M → ℝ) x‖ ^ 2 ∂μ :=
    integral_congr_ae (Eventually.of_forall fun x => by
      simp only [carre, real_inner_self_eq_norm_sq])
  rw [hcar]
  have hvar : 0 ≤ variance (a : M → ℝ) μ := variance_nonneg _ _
  have hint : 0 ≤ ∫ x, ‖mgrad F (a : M → ℝ) x‖ ^ 2 ∂μ := integral_nonneg fun x => by positivity
  rcases hvar.eq_or_lt with h0 | hpos
  · rw [← h0]; simpa using hint
  · have hmem : (∫ x, ‖mgrad F (a : M → ℝ) x‖ ^ 2 ∂μ) / variance (a : M → ℝ) μ ∈
        {r : ℝ | ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f ∧ HasCompactSupport f ∧
          0 < variance f μ ∧ r = (∫ x, ‖mgrad F f x‖ ^ 2 ∂μ) / variance f μ} :=
      ⟨a, a.2.1, a.2.2, hpos, rfl⟩
    have hbdd : BddBelow {r : ℝ | ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f ∧
        HasCompactSupport f ∧ 0 < variance f μ ∧
        r = (∫ x, ‖mgrad F f x‖ ^ 2 ∂μ) / variance f μ} := by
      refine ⟨0, ?_⟩
      rintro r ⟨f, -, -, hf, rfl⟩
      exact div_nonneg (integral_nonneg fun x => by positivity) hf.le
    have := csInf_le hbdd hmem
    have hg : mSpectralGap F μ = sInf {r : ℝ | ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f ∧
        HasCompactSupport f ∧ 0 < variance f μ ∧
        r = (∫ x, ‖mgrad F f x‖ ^ 2 ∂μ) / variance f μ} := rfl
    rw [← hg, hgap, le_div_iff₀ hpos] at this
    exact this

include hV hμ hρ hgap in
/-- Sharpness of the Poincare inequality on `D`. -/
theorem poincare_D_sharp {δ : ℝ} (hδ : 0 < δ) :
    ∃ f : (diffFormData F hV hμ).D,
      0 < ‖(f : M →₂[μ] ℝ) - inner ℝ (f : M →₂[μ] ℝ) (oneL2 μ) • oneL2 μ‖ ∧
      (diffFormData F hV hμ).en f f ≤ (ρ + δ) *
        ‖(f : M →₂[μ] ℝ) - inner ℝ (f : M →₂[μ] ℝ) (oneL2 μ) • oneL2 μ‖ ^ 2 := by
  set S : Set ℝ := {r : ℝ | ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f ∧
        HasCompactSupport f ∧ 0 < variance f μ ∧
        r = (∫ x, ‖mgrad F f x‖ ^ 2 ∂μ) / variance f μ} with hS
  have hg : sInf S = ρ := hgap
  have hne : S.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Real.sInf_empty] at hg
    exact hρ.ne hg
  obtain ⟨r, ⟨f, hf1, hf2, hf3, rfl⟩, hr⟩ := exists_lt_of_csInf_lt hne (show sInf S < ρ + δ by
    linarith)
  let a : testSub F M := ⟨f, hf1, hf2⟩
  refine ⟨⟨testToL2 F μ a, a, rfl⟩, ?_, ?_⟩
  · show 0 < ‖testToL2 F μ a - inner ℝ (testToL2 F μ a) (oneL2 μ) • oneL2 μ‖
    have h := norm_sq_proj_testToL2 F (μ := μ) a
    have : 0 < ‖testToL2 F μ a - inner ℝ (testToL2 F μ a) (oneL2 μ) • oneL2 μ‖ ^ 2 := by
      rw [h]; exact hf3
    exact lt_of_le_of_ne (norm_nonneg _) (fun h0 => by rw [← h0] at this; simp at this)
  · show (diffFormData F hV hμ).en ⟨testToL2 F μ a, a, rfl⟩ ⟨testToL2 F μ a, a, rfl⟩ ≤ (ρ + δ) *
      ‖testToL2 F μ a - inner ℝ (testToL2 F μ a) (oneL2 μ) • oneL2 μ‖ ^ 2
    rw [norm_sq_proj_testToL2 F, en_diffFormData]
    have hcar : ∫ x, carre F (a : M → ℝ) (a : M → ℝ) x ∂μ =
        ∫ x, ‖mgrad F (a : M → ℝ) x‖ ^ 2 ∂μ :=
      integral_congr_ae (Eventually.of_forall fun x => by
        simp only [carre, real_inner_self_eq_norm_sq])
    rw [hcar]
    rw [div_lt_iff₀ hf3] at hr
    exact hr.le

include hV hμ hρ hCD hgap in
/-- Gap attainment from compactness of the energy balls of `Q` in `L²(μ)`. -/
theorem gap_attained_of_compact
    (hcomp : ∀ C : ℝ, TotallyBounded {u : M →₂[μ] ℝ | u ∈ (diffT F hV hμ).Q ∧
      (diffT F hV hμ).E u u + ‖u‖ ^ 2 ≤ C}) :
    0 < mFirstEigenDim F μ V := by
  have hopen := isOpenPosMeasure_of_isWeightedVolume F hV hμ
  obtain ⟨v, hvQ, hv1, hv0, hEL⟩ := (diffT F hV hμ).exists_eigen_of_compact (oneL2 μ)
    (one_mem_Q F hV hμ (diffT F hV hμ)).1 (norm_oneL2 (μ := μ))
    (one_mem_Q F hV hμ (diffT F hV hμ)).2 hρ (poincare_D F hV hμ hρ hgap)
    (fun δ hδ => poincare_D_sharp F hV hμ hρ hgap hδ) hcomp
  obtain ⟨vb, hvb, hvae⟩ := diff_eigen_smooth F hV hμ (c := ρ) hvQ hEL
  rw [mFirstEigenDim_pos_iff F hV hμ hρ hCD hgap]
  refine ⟨vb, ⟨hvb, (Lp.memLp v).ae_eq hvae, ?_⟩, ?_⟩
  · -- pointwise equation
    have hg : Continuous (fun x => mgenerator F V vb x + ρ * vb x) :=
      (continuous_iff_continuousAt.mpr (continuousAt_mgenerator F hV hvb)).add
        (continuous_const.mul hvb.continuous)
    have key : ∀ b : M → ℝ, MSmooth F b → HasCompactSupport b →
        ∫ x, b x * (mgenerator F V vb x + ρ * vb x) ∂μ = 0 := by
      intro b hb hbc
      let bt : testSub F M := ⟨b, hb, hbc⟩
      have h1 : (diffT F hV hμ).E v (testToL2 F μ bt) =
          inner ℝ v (-(testToL2 F μ (testGen F hV bt))) := by
        have := (diffT F hV hμ).E_coe_right v hvQ ⟨testToL2 F μ bt, bt, rfl⟩
        rw [this]
        show inner ℝ v (diffA F hV hμ ⟨testToL2 F μ bt, bt, rfl⟩) = _
        rw [diffA_toL2]
      have h2 := hEL (testToL2 F μ bt) ((diffT F hV hμ).coe_mem ⟨testToL2 F μ bt, bt, rfl⟩)
      rw [h1] at h2
      rw [L2_inner_eq', L2_inner_eq'] at h2
      have h3 : ∫ x, (v : M → ℝ) x * (-(testToL2 F μ (testGen F hV bt)) : M →₂[μ] ℝ) x ∂μ =
          -∫ x, vb x * mgenerator F V b x ∂μ := by
        rw [← integral_neg]
        refine integral_congr_ae ?_
        filter_upwards [hvae, Lp.coeFn_neg (testToL2 F μ (testGen F hV bt)),
          coeFn_testToL2 F μ (testGen F hV bt)] with x hx h4 h5
        rw [h4, Pi.neg_apply, h5, hx]
        simp [testGen_apply]
        exact Or.inl rfl
      have h4 : ∫ x, (v : M → ℝ) x * (testToL2 F μ bt : M → ℝ) x ∂μ =
          ∫ x, vb x * b x ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [hvae, coeFn_testToL2 F μ bt] with x hx h5
        rw [hx, h5]
      rw [h3, h4] at h2
      have h5 := integral_mul_generator_comm F hV hμ hvb hb hbc
      have hi1 : Integrable (fun x => b x * mgenerator F V vb x) μ := by
        have hc : Continuous (fun x => b x * mgenerator F V vb x) :=
          hb.continuous.mul (continuous_iff_continuousAt.mpr (continuousAt_mgenerator F hV hvb))
        exact hc.integrable_of_hasCompactSupport
          (HasCompactSupport.intro hbc fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, zero_mul])
      have hi2 : Integrable (fun x => b x * (ρ * vb x)) μ := by
        have hc : Continuous (fun x => b x * (ρ * vb x)) :=
          hb.continuous.mul (continuous_const.mul hvb.continuous)
        exact hc.integrable_of_hasCompactSupport
          (HasCompactSupport.intro hbc fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, zero_mul])
      simp only [mul_add]
      rw [integral_add hi1 hi2]
      have h6 : ∫ x, b x * (ρ * vb x) ∂μ = ρ * ∫ x, vb x * b x ∂μ := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Eventually.of_forall fun x => by ring)
      rw [h6, ← h5]
      linarith
    intro x
    have := eq_zero_of_integral_test F hg key x
    linarith
  · by_contra hall
    push Not at hall
    have h0 : (v : M → ℝ) =ᵐ[μ] 0 := by
      filter_upwards [hvae] with x hx
      rw [hx]; exact hall x
    have : v = 0 := Lp.eq_zero_iff_ae_eq_zero.2 h0
    rw [this, norm_zero] at hv1
    exact zero_ne_one hv1

end Gap

end CutoffRigidity.Riemann.Diff
