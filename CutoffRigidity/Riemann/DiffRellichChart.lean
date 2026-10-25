module

public import CutoffRigidity.Riemann.DiffInstance2
public import CutoffRigidity.Riemann.DiffRellichChart2

/-! # Local Rellich in one chart (workstream HPOS) (workstream HPOS) -/

@[expose] public section

open Bundle MeasureTheory Filter Set
open scoped Manifold ContDiff ENNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Chart

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

/-- Pointwise product rule bound: `Γ(θ f, θ f) ≤ 2 θ² Γ(f,f) + 2 f² Γ(θ,θ)`. -/
theorem carre_mul_le {θ f : M → ℝ} (hθ : MSmooth F θ) (hf : MSmooth F f) (x : M) :
    carre F (fun y => θ y * f y) (fun y => θ y * f y) x ≤
      2 * θ x ^ 2 * carre F f f x + 2 * f x ^ 2 * carre F θ θ x := by
  have h : mgrad F (fun y => θ y * f y) x = θ x • mgrad F f x + f x • mgrad F θ x :=
    mgrad_mul F hθ hf x
  rw [carre_self_eq, carre_self_eq, carre_self_eq, h]
  have h1 := norm_add_le (θ x • mgrad F f x) (f x • mgrad F θ x)
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs] at h1
  have h2 : ‖θ x • mgrad F f x + f x • mgrad F θ x‖ ^ 2 ≤
      (|θ x| * ‖mgrad F f x‖ + |f x| * ‖mgrad F θ x‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : (|θ x| * ‖mgrad F f x‖ + |f x| * ‖mgrad F θ x‖) ^ 2 ≤
      2 * (|θ x| * ‖mgrad F f x‖) ^ 2 + 2 * (|f x| * ‖mgrad F θ x‖) ^ 2 := by
    nlinarith [sq_nonneg (|θ x| * ‖mgrad F f x‖ - |f x| * ‖mgrad F θ x‖)]
  refine h2.trans (h3.trans (le_of_eq ?_))
  rw [mul_pow, mul_pow, sq_abs, sq_abs]
  ring

include hV hμ in
/-- Local Rellich in a chart: multiplying the energy ball of test functions by a cutoff supported in a
chart domain gives a totally bounded subset of `L²(μ)`. -/
theorem chart_local_totallyBounded (x₀ : M) (θ : testSub F M)
    (hθ : tsupport (θ : M → ℝ) ⊆ (chartAt F x₀).source) (C : ℝ) :
    TotallyBounded {u : M →₂[μ] ℝ | ∃ f g : testSub F M, (∀ x, (g : M → ℝ) x = (θ : M → ℝ) x * (f : M → ℝ) x) ∧
      ∫ x, carre F (f : M → ℝ) (f : M → ℝ) x ∂μ + ∫ x, (f : M → ℝ) x ^ 2 ∂μ ≤ C ∧ u = testToL2 F μ g} := by
  classical
  set K₀ := tsupport (θ : M → ℝ) with hK₀def
  have hK₀ : IsCompact K₀ := θ.2.2
  have hKc : IsCompact ((chartAt F x₀) '' K₀) :=
    hK₀.image_of_continuousOn ((chartAt F x₀).continuousOn.mono hθ)
  have hKT : (chartAt F x₀) '' K₀ ⊆ (chartAt F x₀).target := by
    rintro _ ⟨y, hy, rfl⟩; exact (chartAt F x₀).map_source (hθ hy)
  obtain ⟨ρmin, ρmax, κmin, hρmin, hρmax, hκmin, hbd⟩ := exists_chart_bounds F hV x₀ hKc hKT
  have hb1 : ∀ z ∈ (chartAt F x₀) '' K₀, ρmin ≤ chartRho F V x₀ z ∧ chartRho F V x₀ z ≤ ρmax :=
    fun z hz => ⟨(hbd z hz).1, (hbd z hz).2.1⟩
  have hb2 : ∀ z ∈ (chartAt F x₀) '' K₀, κmin ≤ chartKappa F V x₀ z := fun z hz => (hbd z hz).2.2
  -- bounds on the cutoff
  obtain ⟨Θ, hΘ⟩ := (testSub_continuous F θ).bounded_above_of_compact_support θ.2.2
  have hΓθ : Continuous (fun x => carre F (θ : M → ℝ) (θ : M → ℝ) x) := continuous_carre F θ.2.1 θ.2.1
  obtain ⟨Λ₀, hΛ₀⟩ := hΓθ.bounded_above_of_compact_support (hasCompactSupport_carre F _ θ.2.2)
  set Λ := max Λ₀ 0 with hΛ
  have hΛ0 : 0 ≤ Λ := le_max_right _ _
  have hΓθΛ : ∀ x, carre F (θ : M → ℝ) (θ : M → ℝ) x ≤ Λ := fun x =>
    ((le_abs_self _).trans (by simpa using hΛ₀ x)).trans (le_max_left _ _)
  have hΘx : ∀ x, (θ : M → ℝ) x ^ 2 ≤ Θ ^ 2 := fun x => by
    have := hΘ x
    rw [Real.norm_eq_abs] at this
    exact sq_le_sq' (by linarith [abs_nonneg ((θ : M → ℝ) x), neg_abs_le ((θ : M → ℝ) x)]) (by linarith [le_abs_self ((θ : M → ℝ) x)])
  -- product with the cutoff
  let mul : testSub F M → testSub F M := fun f =>
    ⟨fun x => (θ : M → ℝ) x * (f : M → ℝ) x, (θ.2.1.mul f.2.1 : MSmooth F fun x => (θ : M → ℝ) x * (f : M → ℝ) x),
      f.2.2.mul_left⟩
  have hmul_supp : ∀ f, tsupport (mul f : M → ℝ) ⊆ K₀ := fun f =>
    closure_mono (fun x hx => by
      by_contra h
      exact hx (by simp [mul, Function.notMem_support.1 h]))
  have hgood : ∀ f : testSub F M,
      ∫ x, carre F (f : M → ℝ) (f : M → ℝ) x ∂μ + ∫ x, (f : M → ℝ) x ^ 2 ∂μ ≤ C →
      ∫ x, (mul f : M → ℝ) x ^ 2 ∂μ ≤ Θ ^ 2 * C ∧
      ∫ x, carre F (mul f : M → ℝ) (mul f : M → ℝ) x ∂μ ≤ 2 * Θ ^ 2 * C + 2 * Λ * C := by
    intro f hf
    have hIa : 0 ≤ ∫ x, (f : M → ℝ) x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    have hIb : 0 ≤ ∫ x, carre F (f : M → ℝ) (f : M → ℝ) x ∂μ :=
      integral_nonneg fun x => carre_nonneg F _ x
    have hf2 : Integrable (fun x => (f : M → ℝ) x ^ 2) μ := (testSub_memLp F f μ).integrable_sq
    have hΓf := integrable_carre_test F hV (μ := μ) f f
    have hg2 : Integrable (fun x => (mul f : M → ℝ) x ^ 2) μ := (testSub_memLp F (mul f) μ).integrable_sq
    have hΓg := integrable_carre_test F hV (μ := μ) (mul f) (mul f)
    constructor
    · calc ∫ x, (mul f : M → ℝ) x ^ 2 ∂μ ≤ ∫ x, Θ ^ 2 * (f : M → ℝ) x ^ 2 ∂μ := by
            refine integral_mono hg2 (hf2.const_mul _) fun x => ?_
            show ((θ : M → ℝ) x * (f : M → ℝ) x) ^ 2 ≤ _
            rw [mul_pow]
            exact mul_le_mul_of_nonneg_right (hΘx x) (sq_nonneg _)
        _ = Θ ^ 2 * ∫ x, (f : M → ℝ) x ^ 2 ∂μ := integral_const_mul _ _
        _ ≤ Θ ^ 2 * C := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    · calc ∫ x, carre F (mul f : M → ℝ) (mul f : M → ℝ) x ∂μ
          ≤ ∫ x, (2 * Θ ^ 2 * carre F (f : M → ℝ) (f : M → ℝ) x + 2 * Λ * (f : M → ℝ) x ^ 2) ∂μ := by
            refine integral_mono hΓg ((hΓf.const_mul _).add (hf2.const_mul _)) fun x => ?_
            have h1 := carre_mul_le F θ.2.1 f.2.1 x
            have h2 : 2 * (θ : M → ℝ) x ^ 2 * carre F (f : M → ℝ) (f : M → ℝ) x ≤
                2 * Θ ^ 2 * carre F (f : M → ℝ) (f : M → ℝ) x :=
              mul_le_mul_of_nonneg_right (by linarith [hΘx x]) (carre_nonneg F _ x)
            have h3 : 2 * (f : M → ℝ) x ^ 2 * carre F (θ : M → ℝ) (θ : M → ℝ) x ≤
                2 * Λ * (f : M → ℝ) x ^ 2 := by
              nlinarith [mul_le_mul_of_nonneg_left (hΓθΛ x) (sq_nonneg ((f : M → ℝ) x))]
            exact h1.trans (by linarith)
        _ = 2 * Θ ^ 2 * ∫ x, carre F (f : M → ℝ) (f : M → ℝ) x ∂μ +
              2 * Λ * ∫ x, (f : M → ℝ) x ^ 2 ∂μ := by
            rw [integral_add (hΓf.const_mul _) (hf2.const_mul _), integral_const_mul, integral_const_mul]
        _ ≤ _ := by nlinarith [sq_nonneg Θ]
  let ι := {f : testSub F M //
    ∫ x, carre F (f : M → ℝ) (f : M → ℝ) x ∂μ + ∫ x, (f : M → ℝ) x ^ 2 ∂μ ≤ C}
  let gi : ι → F → ℝ := fun i => chartRestr F x₀ (mul i.1 : M → ℝ)
  have hcd : ∀ i, ContDiff ℝ ∞ (gi i) := fun i =>
    contDiff_chartRestr F (mul i.1).2.1 (hmul_supp i.1) hK₀ hθ
  have hcs : ∀ i, HasCompactSupport (gi i) := fun i =>
    hasCompactSupport_chartRestr F (hmul_supp i.1) hK₀ hθ
  have hsq := fun i : ι => chart_sq_bounds F hV hμ (mul i.1).2.1 (hmul_supp i.1) hK₀ hθ hb1
  have hgr := fun i : ι => chart_grad_bound F hV hμ (mul i.1) (hmul_supp i.1) hK₀ hθ hκmin hb2
  have hcrit := rellich_criterion_F F gi hKc (Θ ^ 2 * C / ρmin)
    (κmin⁻¹ * (2 * Θ ^ 2 * C + 2 * Λ * C))
    (fun i => (hcd i).continuous.memLp_of_hasCompactSupport (hcs i))
    (fun i x hx => chartRestr_eq_zero' F (hmul_supp i.1) hx)
    (fun i => by
      have h1 : ρmin * ∫ x, gi i x ^ 2 ≤ ∫ x, (mul i.1 : M → ℝ) x ^ 2 ∂μ := (hsq i).1
      have h2 := (hgood i.1 i.2).1
      rw [le_div_iff₀ hρmin]
      linarith)
    (fun i h => by
      refine (c1_translation_F F ((hcd i).of_le (by simp)) (hcs i) h).trans ?_
      have h1 := (hgr i).trans (mul_le_mul_of_nonneg_left (hgood i.1 i.2).2 (inv_nonneg.2 hκmin.le))
      rw [mul_comm (κmin⁻¹ * _)]
      exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _))
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨s, hs⟩ := hcrit (ε ^ 2 / (2 * ρmax)) (by positivity)
  refine ⟨↑(s.image fun j : ι => testToL2 F μ (mul j.1)), Finset.finite_toSet _, ?_⟩
  rintro u ⟨f, g, hg, hE, rfl⟩
  have hgm : g = mul f := Subtype.ext (funext hg)
  subst hgm
  obtain ⟨j, hjs, hj⟩ := hs ⟨f, hE⟩
  simp only [Set.mem_iUnion, Finset.coe_image, Set.mem_image, Finset.mem_coe]
  refine ⟨testToL2 F μ (mul j.1), ⟨j, hjs, rfl⟩, ?_⟩
  rw [Metric.mem_ball, dist_eq_norm, ← map_sub]
  set d : testSub F M := mul f - mul j.1 with hd
  have hdsupp : tsupport (d : M → ℝ) ⊆ K₀ := by
    refine closure_minimal ?_ hK₀.isClosed
    refine (Function.support_sub _ _).trans (union_subset ?_ ?_)
    · exact subset_tsupport _ |>.trans (hmul_supp f)
    · exact subset_tsupport _ |>.trans (hmul_supp j.1)
  have hdb := (chart_sq_bounds F hV hμ d.2.1 hdsupp hK₀ hθ hb1).2
  have hdr : chartRestr F x₀ (d : M → ℝ) = fun z => gi ⟨f, hE⟩ z - gi j z :=
    chartRestr_sub F x₀ _ _
  rw [hdr] at hdb
  have hnorm : ‖testToL2 F μ d‖ ^ 2 = ∫ x, (d : M → ℝ) x ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, inner_testToL2]
    simp [pow_two]
  have h3 : ‖testToL2 F μ d‖ ^ 2 < ε ^ 2 := by
    rw [hnorm]
    calc _ ≤ _ := hdb
      _ < ρmax * (ε ^ 2 / (2 * ρmax)) := mul_lt_mul_of_pos_left hj hρmax
      _ = ε ^ 2 / 2 := by field_simp
      _ < ε ^ 2 := by linarith [pow_pos hε 2]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le h3

end Chart

end CutoffRigidity.Riemann.Diff
