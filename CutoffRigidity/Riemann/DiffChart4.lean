module

public import CutoffRigidity.Riemann.DiffChart3
public import CutoffRigidity.Riemann.WeightedIBPEuclid

/-! # Weak gradient identity and chart transfer of the weak equation (workstream DIR) -/

@[expose] public section

open Bundle MeasureTheory Filter Set
open scoped Manifold ContDiff ENNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section IBP

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M] (x₀ : M)

/-- Integration by parts in the chart: for a smooth `a` on `M` and `ψ ∈ C_c^∞(F)` supported in the
chart target, `∫ ã ∂_wψ = - ∫ ⟪∇ã, w⟫ ψ`. -/
theorem integral_ibp_chart {a : M → ℝ} (ha : MSmooth F a) {ψ : F → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (hψT : tsupport ψ ⊆ (chartAt F x₀).target) (w : F) :
    ∫ z, (a ∘ (chartAt F x₀).symm) z * fderiv ℝ ψ z w =
      -∫ z, inner ℝ (chartGrad F x₀ a z) w * ψ z := by
  set φ := chartAt F x₀ with hφ
  set at' : F → ℝ := a ∘ φ.symm with hat
  have hCD := contDiffOn_chartCoord F x₀ ha
  set h : F → ℝ := fun z => at' z * ψ z with hh
  -- ψ and its derivative vanish off the target
  have hψz : ∀ z, z ∉ φ.target → ψ =ᶠ[𝓝 z] fun _ => (0 : ℝ) := fun z hz =>
    notMem_tsupport_iff_eventuallyEq.1 (fun h => hz (hψT h))
  have hhCD : ContDiff ℝ 1 h := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ φ.target
    · have h1 : ContDiffAt ℝ 1 at' z :=
        ((hCD.contDiffAt (φ.open_target.mem_nhds hz)).of_le (by simp))
      exact h1.mul (hψ.contDiffAt.of_le (by simp))
    · have : h =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
        filter_upwards [hψz z hz] with y hy
        simp [hh, hy]
      exact (contDiffAt_const).congr_of_eventuallyEq this
  have hhc : HasCompactSupport h := hψc.mul_left
  have hI := CutoffRigidity.integral_fderiv_apply_eq_zero hhCD hhc w
  have hpt : ∀ z, fderiv ℝ h z w = inner ℝ (chartGrad F x₀ a z) w * ψ z + at' z * fderiv ℝ ψ z w := by
    intro z
    by_cases hz : z ∈ φ.target
    · have h1 := differentiableAt_chartCoord F x₀ ha hz
      have h2 : DifferentiableAt ℝ ψ z := hψ.differentiable (by simp) z
      have : fderiv ℝ h z = at' z • fderiv ℝ ψ z + ψ z • fderiv ℝ at' z := by
        simp only [hh]
        exact fderiv_mul h1 h2
      rw [this]
      simp only [add_apply, smul_apply, smul_eq_mul,
        chartGrad, gradient, InnerProductSpace.toDual_symm_apply]
      ring
    · have hev := hψz z hz
      have h0 : h =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
        filter_upwards [hev] with y hy
        simp [hh, hy]
      rw [h0.fderiv_eq, hev.fderiv_eq, hev.self_of_nhds]
      simp
  simp only [hpt] at hI
  have hKc : IsCompact (tsupport ψ) := hψc
  have hψcont : Continuous ψ := hψ.continuous
  have hdψ : Continuous (fun z => fderiv ℝ ψ z w) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hint1 : Integrable (fun z => inner ℝ (chartGrad F x₀ a z) w * ψ z) volume := by
    have hc : ContinuousOn (fun z => inner ℝ (chartGrad F x₀ a z) w * ψ z) (tsupport ψ) :=
      (((continuousOn_chartGrad F x₀ ha).inner continuousOn_const).mul hψcont.continuousOn).mono hψT
    refine (integrableOn_iff_integrable_of_support_subset (s := tsupport ψ) ?_).1
      (hc.integrableOn_compact hKc)
    intro z hz
    by_contra hnz
    apply hz
    have := image_eq_zero_of_notMem_tsupport hnz
    simp [this]
  have hint2 : Integrable (fun z => at' z * fderiv ℝ ψ z w) volume := by
    have hc : ContinuousOn (fun z => at' z * fderiv ℝ ψ z w) (tsupport ψ) :=
      (hCD.continuousOn.mono hψT).mul hdψ.continuousOn
    refine (integrableOn_iff_integrable_of_support_subset (s := tsupport ψ) ?_).1
      (hc.integrableOn_compact hKc)
    intro z hz
    by_contra hnz
    apply hz
    have hev := notMem_tsupport_iff_eventuallyEq.1 hnz
    have : fderiv ℝ ψ z = 0 := by rw [hev.fderiv_eq]; simp
    simp [this]
  rw [integral_add hint1 hint2] at hI
  linarith

end IBP

section Coe

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V) (x₀ : M)

theorem coeFn_testPullLp (a : testSub F M) :
    (testPullLp F hV hμ x₀ a : F → ℝ) =ᵐ[chartNu F V x₀] fun z => (a : M → ℝ) ((chartAt F x₀).symm z) :=
  MemLp.coeFn_toLp (memLp_chartPull F hV hμ x₀ a.2.1.continuous.measurable (testSub_memLp F a μ))

theorem coeFn_lpPullLp (u : M →₂[μ] ℝ) :
    (lpPullLp F hV hμ x₀ u : F → ℝ) =ᵐ[chartNu F V x₀] fun z => (u : M → ℝ) ((chartAt F x₀).symm z) :=
  MemLp.coeFn_toLp (memLp_chartPull F hV hμ x₀ (Lp.stronglyMeasurable u).measurable (Lp.memLp u))

theorem coeFn_gradLp (a : testSub F M) :
    (gradLp F hV hμ x₀ a : F → F) =ᵐ[chartNu F V x₀] chartGrad F x₀ (a : M → ℝ) :=
  MemLp.coeFn_toLp (memLp_chartGrad F hV hμ x₀ a)

end Coe

section WeakGrad

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V) (x₀ : M)

/-- `ν`-integrals are `κ dz`-integrals over the target. -/
theorem integral_chartNu_eq (f : F → ℝ) (hV' : AEMeasurable (fun z => ENNReal.ofReal (chartKappa F V x₀ z))
      (volume.restrict (chartAt F x₀).target)) :
    ∫ z, f z ∂(chartNu F V x₀) = ∫ z in (chartAt F x₀).target, chartKappa F V x₀ z * f z := by
  unfold chartNu
  rw [integral_withDensity_eq_integral_toReal_smul₀ hV'
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun (chartAt F x₀).open_target.measurableSet fun z hz => ?_
  simp [ENNReal.toReal_ofReal (chartKappa_pos F V x₀ hz).le]

/-- The test fields used to pass the weak gradient identity to the limit are in `L²(ν)`. -/
theorem memLp_chartNu_test_scalar (hV : MSmooth F V) (hμ : IsWeightedVolume F μ V) (x₀ : M)
    {ψ : F → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψT : tsupport ψ ⊆ (chartAt F x₀).target) (w : F) :
    MemLp (fun z => fderiv ℝ ψ z w / chartKappa F V x₀ z) 2 (chartNu F V x₀) := by
  refine memLp_chartNu_of_continuousOn F hV hμ x₀ hψc hψT ?_ ?_
  · intro z hz
    have hd : Continuous (fun z => fderiv ℝ ψ z w) :=
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    exact hd.continuousWithinAt.div ((continuousOn_chartKappa F hV x₀) z hz)
      (chartKappa_pos F V x₀ hz).ne'
  · intro z hz hzK
    have hev := notMem_tsupport_iff_eventuallyEq.1 hzK
    have : fderiv ℝ ψ z = 0 := by rw [hev.fderiv_eq]; simp
    simp [this]

theorem memLp_chartNu_test_vector (hV : MSmooth F V) (hμ : IsWeightedVolume F μ V) (x₀ : M)
    {ψ : F → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψT : tsupport ψ ⊆ (chartAt F x₀).target) (w : F) :
    MemLp (fun z => (ψ z / chartKappa F V x₀ z) • w) 2 (chartNu F V x₀) := by
  refine memLp_chartNu_of_continuousOn F hV hμ x₀ hψc hψT ?_ ?_
  · intro z hz
    exact (hψ.continuous.continuousWithinAt.div ((continuousOn_chartKappa F hV x₀) z hz)
      (chartKappa_pos F V x₀ hz).ne').smul continuousWithinAt_const
  · intro z hz hzK
    have : ψ z = 0 := image_eq_zero_of_notMem_tsupport hzK
    simp [this]

end WeakGrad

section WeakGradLimit

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V) (x₀ : M)

/-- **Weak gradient identity** for the limit objects: for `ψ ∈ C_c^∞` supported in the chart
target, `∫ ũ ∂_wψ = - ∫ ⟪Ĝ, w⟫ ψ`. -/
theorem weak_gradient_identity_of_limit {u : M →₂[μ] ℝ} (a : ℕ → testSub F M)
    (Ĝ : Lp F 2 (chartNu F V x₀))
    (hG : Tendsto (fun n => gradLp F hV hμ x₀ (a n)) atTop (𝓝 Ĝ))
    (hs : Tendsto (fun n => testPullLp F hV hμ x₀ (a n)) atTop (𝓝 (lpPullLp F hV hμ x₀ u)))
    {ψ : F → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψT : tsupport ψ ⊆ (chartAt F x₀).target) (w : F) :
    ∫ z, (u : M → ℝ) ((chartAt F x₀).symm z) * fderiv ℝ ψ z w =
      -∫ z, inner ℝ (Ĝ z) w * ψ z := by
  set φ := chartAt F x₀ with hφ
  have hTm : MeasurableSet φ.target := φ.open_target.measurableSet
  have hκm := aemeasurable_chartKappa F hV x₀
  have hψ0 : ∀ z, z ∉ φ.target → ψ z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport (fun h => hz (hψT h))
  have hdψ0 : ∀ z, z ∉ φ.target → fderiv ℝ ψ z = 0 := fun z hz => by
    have hev := notMem_tsupport_iff_eventuallyEq.1 (fun h => hz (hψT h))
    rw [hev.fderiv_eq]; simp
  set θ₂ : F → ℝ := fun z => fderiv ℝ ψ z w / chartKappa F V x₀ z with hθ₂
  set θ₁ : F → F := fun z => (ψ z / chartKappa F V x₀ z) • w with hθ₁
  have hθ₂m := memLp_chartNu_test_scalar F hV hμ x₀ hψ hψc hψT w
  have hθ₁m := memLp_chartNu_test_vector F hV hμ x₀ hψ hψc hψT w
  have hA := tendsto_integral_inner_of_tendsto θ₂ hθ₂m _ _ hs
  have hB := tendsto_integral_inner_of_tendsto θ₁ hθ₁m _ _ hG
  -- identification of the sequence terms
  have hAn : ∀ n, ∫ z, inner ℝ (θ₂ z) (testPullLp F hV hμ x₀ (a n) z) ∂(chartNu F V x₀) =
      ∫ z, (a n : M → ℝ) (φ.symm z) * fderiv ℝ ψ z w := by
    intro n
    have hae : ∀ᵐ z ∂(chartNu F V x₀), testPullLp F hV hμ x₀ (a n) z = (a n : M → ℝ) (φ.symm z) :=
      coeFn_testPullLp F hV hμ x₀ (a n)
    rw [integral_congr_ae (g := fun z => inner ℝ (θ₂ z) ((a n : M → ℝ) (φ.symm z)))
      (by filter_upwards [hae] with z hz; rw [hz])]
    rw [integral_chartNu_eq F x₀ _ hκm]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := φ.target)
      (f := fun z => (a n : M → ℝ) (φ.symm z) * fderiv ℝ ψ z w)
      (fun z hz => by simp [hdψ0 z hz])]
    refine setIntegral_congr_fun hTm fun z hz => ?_
    have := (chartKappa_pos F V x₀ hz).ne'
    simp only [hθ₂, RCLike.inner_apply, conj_trivial]
    field_simp
  have hBn : ∀ n, ∫ z, inner ℝ (θ₁ z) (gradLp F hV hμ x₀ (a n) z) ∂(chartNu F V x₀) =
      ∫ z, inner ℝ (chartGrad F x₀ (a n : M → ℝ) z) w * ψ z := by
    intro n
    have hae : ∀ᵐ z ∂(chartNu F V x₀), gradLp F hV hμ x₀ (a n) z = chartGrad F x₀ (a n : M → ℝ) z :=
      coeFn_gradLp F hV hμ x₀ (a n)
    rw [integral_congr_ae (g := fun z => inner ℝ (θ₁ z) (chartGrad F x₀ (a n : M → ℝ) z))
      (by filter_upwards [hae] with z hz; rw [hz])]
    rw [integral_chartNu_eq F x₀ _ hκm]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := φ.target)
      (f := fun z => inner ℝ (chartGrad F x₀ (a n : M → ℝ) z) w * ψ z)
      (fun z hz => by simp [hψ0 z hz])]
    refine setIntegral_congr_fun hTm fun z hz => ?_
    have := (chartKappa_pos F V x₀ hz).ne'
    simp only [hθ₁, inner_smul_left, conj_trivial]
    rw [real_inner_comm]
    field_simp
  -- the identity for each `n`
  have hIBP : ∀ n, ∫ z, inner ℝ (θ₂ z) (testPullLp F hV hμ x₀ (a n) z) ∂(chartNu F V x₀) =
      -∫ z, inner ℝ (θ₁ z) (gradLp F hV hμ x₀ (a n) z) ∂(chartNu F V x₀) := by
    intro n
    rw [hAn n, hBn n]
    exact integral_ibp_chart F x₀ (a n).2.1 hψ hψc hψT w
  have hlim : ∫ z, inner ℝ (θ₂ z) (lpPullLp F hV hμ x₀ u z) ∂(chartNu F V x₀) =
      -∫ z, inner ℝ (θ₁ z) (Ĝ z) ∂(chartNu F V x₀) := by
    refine tendsto_nhds_unique (hA.congr (fun n => rfl)) ?_
    have := hB.neg
    exact this.congr fun n => (hIBP n).symm
  -- translate the limit objects back to Lebesgue integrals
  have hU : ∀ᵐ z ∂(chartNu F V x₀), lpPullLp F hV hμ x₀ u z = (u : M → ℝ) (φ.symm z) :=
    coeFn_lpPullLp F hV hμ x₀ u
  have e1 : ∫ z, inner ℝ (θ₂ z) (lpPullLp F hV hμ x₀ u z) ∂(chartNu F V x₀) =
      ∫ z, (u : M → ℝ) (φ.symm z) * fderiv ℝ ψ z w := by
    rw [integral_congr_ae (g := fun z => inner ℝ (θ₂ z) ((u : M → ℝ) (φ.symm z)))
      (by filter_upwards [hU] with z hz; rw [hz])]
    rw [integral_chartNu_eq F x₀ _ hκm]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := φ.target)
      (f := fun z => (u : M → ℝ) (φ.symm z) * fderiv ℝ ψ z w)
      (fun z hz => by simp [hdψ0 z hz])]
    refine setIntegral_congr_fun hTm fun z hz => ?_
    have := (chartKappa_pos F V x₀ hz).ne'
    simp only [hθ₂, RCLike.inner_apply, conj_trivial]
    field_simp
  have e2 : ∫ z, inner ℝ (θ₁ z) (Ĝ z) ∂(chartNu F V x₀) = ∫ z, inner ℝ (Ĝ z) w * ψ z := by
    rw [integral_chartNu_eq F x₀ _ hκm]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := φ.target)
      (f := fun z => inner ℝ (Ĝ z) w * ψ z)
      (fun z hz => by simp [hψ0 z hz])]
    refine setIntegral_congr_fun hTm fun z hz => ?_
    have := (chartKappa_pos F V x₀ hz).ne'
    simp only [hθ₁, inner_smul_left, conj_trivial]
    rw [real_inner_comm]
    field_simp
  rw [← e1, hlim, e2]

end WeakGradLimit

end CutoffRigidity.Riemann.Diff
