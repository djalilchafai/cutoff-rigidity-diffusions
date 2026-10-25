module

public import CutoffRigidity.Riemann.DiffBEMain2

/-! # Bakry-Emery, pointwise bound: from `A(0) ≤ ...` to the integrated gradient bound
(workstream BE, part D3) -/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set Topology
open scoped Manifold ContDiff ENNReal NNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Main3

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

theorem norm_mgrad_eq (g : M → ℝ) (x : M) : ‖mgrad F g x‖ = Real.sqrt (carre F g g x) := by
  rw [carre_self_eq, Real.sqrt_sq (norm_nonneg _)]

theorem continuous_norm_mgrad (hReg : WeightedRegular F V) {g : M → ℝ} (hg : MSmooth F g) :
    Continuous fun x => ‖mgrad F g x‖ := by
  simp_rw [norm_mgrad_eq F]
  exact (hReg.1 g g hg hg).continuous.sqrt

theorem bdd_norm_mgrad (hReg : WeightedRegular F V) (f : testSub F M) :
    ∃ C, ∀ x, |‖mgrad F (f : M → ℝ) x‖| ≤ C := by
  have hc : HasCompactSupport (fun x => ‖mgrad F (f : M → ℝ) x‖) := by
    simp_rw [norm_mgrad_eq F]
    exact (hasCompactSupport_carre F (f : M → ℝ) f.2.2).comp_left Real.sqrt_zero
  obtain ⟨C, hC⟩ := (continuous_norm_mgrad F hReg f.2.1).bounded_above_of_compact_support hc
  exact ⟨C, fun x => by simpa using hC x⟩

/-- `x ↦ ∫ ψ dKk t x` is continuous for bounded continuous `ψ` (`t ≠ 0`). -/
theorem continuous_semi_bdd {t : ℝ≥0} (ht : t ≠ 0) {ψ : M → ℝ} (hψ : Continuous ψ)
    (hb : ∃ C, ∀ x, |ψ x| ≤ C) : Continuous (semi (Kk F hV hμ) t ψ) := by
  set u : M →₂[μ] ℝ := (memLp_of_bdd (μ := μ) hψ hb).toLp ψ
  have hu' : (u : M → ℝ) =ᵐ[μ] ψ := MemLp.coeFn_toLp _
  have : semi (Kk F hV hμ) t ψ = Tc F hV hμ t u :=
    funext fun x => int_Kk_eq_Tc F hV hμ ht x u hu'
  rw [this]
  exact Tc_continuous F hV hμ ht u

theorem continuous_semi_test {t : ℝ≥0} (ht : t ≠ 0) (f : testSub F M) :
    MSmooth F (semi (Kk F hV hμ) t (f : M → ℝ)) := by
  have : semi (Kk F hV hμ) t (f : M → ℝ) = Tc F hV hμ t (testToL2 F μ f) :=
    funext fun x => semi_Kk_eq_Tc F hV hμ ht f x
  rw [this]
  exact Tc_smooth F hV hμ ht _

theorem integrable_bdd_kernel {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α] {P : Measure α} [IsFiniteMeasure P] {ψ : α → ℝ} (hψ : Continuous ψ)
    (hb : ∃ C, ∀ x, |ψ x| ≤ C) : Integrable ψ P := by
  obtain ⟨C, hC⟩ := hb
  exact Integrable.of_bound hψ.aestronglyMeasurable C (Eventually.of_forall fun x => by simpa using hC x)

variable (hIBP : WeightedIBP F μ V) (hReg : WeightedRegular F V) (hC : WeightedCutoffs F M)

include hIBP hReg hC hV in
/-- The integrated gradient bound. -/
theorem integrated_grad {ρ : ℝ} (hρ : 0 ≤ ρ) (hB : WeightedBochnerIneq F V ρ)
    (f ζ : testSub F M) (hζ : ∀ x, 0 ≤ (ζ : M → ℝ) x) {t : ℝ≥0} (ht : t ≠ 0) :
    ∫ x, (ζ : M → ℝ) x * ‖mgrad F (semi (Kk F hV hμ) t (f : M → ℝ)) x‖ ∂μ ≤
      Real.exp (-ρ * t) * ∫ x, (ζ : M → ℝ) x * (∫ y, ‖mgrad F (f : M → ℝ) y‖ ∂Kk F hV hμ t x) ∂μ := by
  haveI := Kk_markov F hV hμ t
  set Kt := semi (Kk F hV hμ) t (f : M → ℝ) with hKt
  have hKts : MSmooth F Kt := continuous_semi_test F hV hμ ht f
  have hζc : Continuous (ζ : M → ℝ) := testSub_continuous F ζ
  have hζk : HasCompactSupport (ζ : M → ℝ) := ζ.2.2
  set I := ∫ x, (ζ : M → ℝ) x ∂μ with hI
  have hI0 : 0 ≤ I := integral_nonneg hζ
  have hfg : Continuous fun y => ‖mgrad F (f : M → ℝ) y‖ := continuous_norm_mgrad F hReg f.2.1
  obtain ⟨Cf, hCf⟩ := bdd_norm_mgrad F hReg f
  set G : M → ℝ := semi (Kk F hV hμ) t (fun y => ‖mgrad F (f : M → ℝ) y‖) with hG
  have hGc : Continuous G := continuous_semi_bdd F hV hμ ht hfg ⟨Cf, hCf⟩
  have hdiff : ∀ ε : ℝ, 0 < ε → ∫ x, (ζ : M → ℝ) x * ‖mgrad F Kt x‖ ∂μ ≤
      Real.exp (-ρ * t) * ∫ x, (ζ : M → ℝ) x * G x ∂μ + Real.sqrt ε * I := by
    intro ε hε
    have hcomp := Afun_comparison F hV hμ hIBP hReg hC hρ hB f ζ hζ hε
      (t := (t : ℝ)) (by positivity)
    simp only [Real.toNNReal_coe, sub_self, Real.toNNReal_zero, sub_zero, semi_Kk_zero,
      Afun] at hcomp
    set ψ : M → ℝ := fun x => Real.sqrt (carre F (f : M → ℝ) (f : M → ℝ) x + ε) with hψ
    have hΓf : Continuous (carre F (f : M → ℝ) (f : M → ℝ)) := (hReg.1 _ _ f.2.1 f.2.1).continuous
    have hψc : Continuous ψ := (hΓf.add continuous_const).sqrt
    have hψle : ∀ y, ψ y ≤ ‖mgrad F (f : M → ℝ) y‖ + Real.sqrt ε := by
      intro y
      rw [norm_mgrad_eq F]
      exact sqrt_add_le_add_sqrt' (carre_nonneg F _ y) hε.le
    have hψ0 : ∀ y, 0 ≤ ψ y := fun y => Real.sqrt_nonneg _
    have hψb : ∃ C, ∀ x, |ψ x| ≤ C :=
      ⟨Cf + Real.sqrt ε, fun y => by
        rw [abs_of_nonneg (hψ0 y)]
        have := hCf y
        rw [abs_of_nonneg (norm_nonneg _)] at this
        linarith [hψle y]⟩
    have dual := duality_Kk F hV hμ ht ζ hψc hψb
    have hsc := continuous_semi_bdd F hV hμ ht hψc hψb
    have hsemi : ∀ x, semi (Kk F hV hμ) t ψ x ≤ G x + Real.sqrt ε := by
      intro x
      have i1 : Integrable ψ (Kk F hV hμ t x) := integrable_bdd_kernel hψc hψb
      have i2 : Integrable (fun y => ‖mgrad F (f : M → ℝ) y‖) (Kk F hV hμ t x) :=
        integrable_bdd_kernel hfg ⟨Cf, hCf⟩
      have i3 : Integrable (fun y => ‖mgrad F (f : M → ℝ) y‖ + Real.sqrt ε) (Kk F hV hμ t x) :=
        i2.add (integrable_const _)
      have := integral_mono i1 i3 hψle
      rw [integral_add i2 (integrable_const _)] at this
      simpa [semi, hG] using this
    have hi1 : Integrable (fun x => (ζ : M → ℝ) x * semi (Kk F hV hμ) t ψ x) μ :=
      (hζc.mul hsc).integrable_of_hasCompactSupport hζk.mul_right
    have hi2 : Integrable (fun x => (ζ : M → ℝ) x * (G x + Real.sqrt ε)) μ :=
      (hζc.mul (hGc.add continuous_const)).integrable_of_hasCompactSupport hζk.mul_right
    have hiG : Integrable (fun x => (ζ : M → ℝ) x * G x) μ :=
      (hζc.mul hGc).integrable_of_hasCompactSupport hζk.mul_right
    have hZ : ∫ x, (ζ : M → ℝ) x * semi (Kk F hV hμ) t ψ x ∂μ ≤
        ∫ x, (ζ : M → ℝ) x * G x ∂μ + Real.sqrt ε * I := by
      have := integral_mono hi1 hi2 (fun x => mul_le_mul_of_nonneg_left (hsemi x) (hζ x))
      have e : ∫ x, (ζ : M → ℝ) x * (G x + Real.sqrt ε) ∂μ =
          ∫ x, (ζ : M → ℝ) x * G x ∂μ + Real.sqrt ε * I := by
        simp_rw [mul_add]
        rw [integral_add hiG (hζc.integrable_of_hasCompactSupport hζk |>.mul_const _), integral_mul_const]
        rw [hI]; ring
      linarith
    have hΓK : Continuous (carre F Kt Kt) := (hReg.1 _ _ hKts hKts).continuous
    have hXY : ∫ x, (ζ : M → ℝ) x * ‖mgrad F Kt x‖ ∂μ ≤
        ∫ x, (ζ : M → ℝ) x * Real.sqrt (carre F Kt Kt x + ε) ∂μ := by
      refine integral_mono ?_ ?_ (fun x => ?_)
      · exact (hζc.mul (continuous_norm_mgrad F hReg hKts)).integrable_of_hasCompactSupport
          hζk.mul_right
      · exact (hζc.mul (hΓK.add continuous_const).sqrt).integrable_of_hasCompactSupport
          hζk.mul_right
      · refine mul_le_mul_of_nonneg_left ?_ (hζ x)
        rw [norm_mgrad_eq F]
        exact Real.sqrt_le_sqrt (by linarith)
    have he := Real.exp_pos (-ρ * t)
    have := mul_le_mul_of_nonneg_left hZ he.le
    rw [← dual] at this
    nlinarith
  show _ ≤ Real.exp (-ρ * t) * ∫ x, (ζ : M → ℝ) x * G x ∂μ
  by_contra hcon
  push Not at hcon
  set δ := ∫ x, (ζ : M → ℝ) x * ‖mgrad F Kt x‖ ∂μ -
    Real.exp (-ρ * t) * ∫ x, (ζ : M → ℝ) x * G x ∂μ with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hpos : 0 < 2 * (1 + I) := by positivity
  have h1 := hdiff ((δ / (2 * (1 + I))) ^ 2) (by positivity)
  rw [Real.sqrt_sq (by positivity)] at h1
  have h2 : δ / (2 * (1 + I)) * I ≤ δ / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hpos (by norm_num)]
    nlinarith
  linarith

end Main3

end CutoffRigidity.Riemann.Diff
