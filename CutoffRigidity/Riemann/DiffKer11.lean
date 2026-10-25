module

public import CutoffRigidity.Riemann.DiffKer10
public import CutoffRigidity.Riemann.DiffLaplace

/-! # `resolvent_repr`: the pointwise Laplace representation of the resolvent (KER) -/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set Topology
open scoped Manifold ContDiff ENNReal Topology NNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Repr

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

theorem continuous_semi_space (s : ℝ) (g : testSub F M) :
    Continuous fun x => semi (Kk F hV hμ) s.toNNReal (g : M → ℝ) x := by
  by_cases hs : s.toNNReal = 0
  · rw [hs]
    simp only [semi_Kk_zero]
    exact g.2.1.continuous
  · have : (fun x => semi (Kk F hV hμ) s.toNNReal (g : M → ℝ) x) =
        Tc F hV hμ s.toNNReal (testToL2 F μ g) :=
      funext fun x => semi_Kk_eq_Tc F hV hμ hs g x
    rw [this]
    exact Tc_continuous F hV hμ hs _

/-- **Pointwise Laplace representation of the resolvent.** -/
theorem resolvent_repr {lam : ℝ} (hlam : 0 < lam) (g : M → ℝ) (hg : MSmooth F g)
    (hc : HasCompactSupport g) :
    ∃ ū : M → ℝ, MSmooth F ū ∧
      (((diffFR F hV hμ).resolvent lam (testToL2 F μ ⟨g, hg, hc⟩) : M →₂[μ] ℝ) : M → ℝ) =ᵐ[μ] ū ∧
      ∀ x, ū x = ∫ s in Set.Ioi (0 : ℝ), Real.exp (-lam * s) *
        semi (Kk F hV hμ) s.toNNReal g x := by
  classical
  set f₀ : testSub F M := ⟨g, hg, hc⟩ with hf₀
  set S := diffFR F hV hμ with hS
  obtain ⟨B, hB⟩ := hg.continuous.bounded_above_of_compact_support hc
  set G : M → ℝ → ℝ := fun x s => semi (Kk F hV hμ) s.toNNReal g x with hG
  have hGb : ∀ x s, |G x s| ≤ B := fun x s =>
    abs_semi_le F hV hμ x g (fun z => by simpa using hB z)
  have hGcs : ∀ x, Continuous fun s => G x s := fun x => continuous_semi_time F hV hμ f₀ x
  have hGcx : ∀ s, Continuous fun x => G x s := fun s => continuous_semi_space F hV hμ s f₀
  have hexp : IntegrableOn (fun s : ℝ => Real.exp (-lam * s)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hlam
  have hexpc : Continuous fun s : ℝ => Real.exp (-lam * s) := by fun_prop
  set U : M → ℝ := fun x => ∫ s in Ioi (0:ℝ), Real.exp (-lam * s) * G x s with hU
  have hbd : IntegrableOn (fun s : ℝ => B * Real.exp (-lam * s)) (Ioi 0) := hexp.const_mul B
  have hUb : ∀ x, ‖U x‖ ≤ ∫ s in Ioi (0:ℝ), B * Real.exp (-lam * s) := fun x => by
    refine norm_integral_le_of_norm_le hbd ?_
    refine Filter.Eventually.of_forall fun s => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have := hGb x s
    nlinarith [Real.exp_pos (-lam * s)]
  have hUc : Continuous U := by
    refine continuous_of_dominated (bound := fun s => B * Real.exp (-lam * s))
      (fun x => ((hexpc.mul (hGcs x)).aestronglyMeasurable)) (fun x => ?_) hbd ?_
    · refine Filter.Eventually.of_forall fun s => ?_
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have := hGb x s
      nlinarith [Real.exp_pos (-lam * s)]
    · exact Filter.Eventually.of_forall fun s => continuous_const.mul (hGcx s)
  have hUmem : MemLp U 2 μ :=
    MemLp.of_bound hUc.aestronglyMeasurable (∫ s in Ioi (0:ℝ), B * Real.exp (-lam * s))
      (Filter.Eventually.of_forall hUb)
  set UL := hUmem.toLp U with hUL
  have hULae : (UL : M → ℝ) =ᵐ[μ] U := MemLp.coeFn_toLp hUmem
  -- joint measurability
  have hGmeas : Measurable (fun z : M × ℝ => G z.1 z.2) := by
    have := measurable_uncurry_of_continuous_of_measurable (α := M) (ι := ℝ)
      (u := fun (s : ℝ) (x : M) => G x s) hGcs (fun s => (hGcx s).measurable)
    exact this.comp measurable_swap
  have hinner : ∀ φ : M →₂[μ] ℝ, inner ℝ UL φ = ∫ s in Ioi (0:ℝ), Real.exp (-lam * s) *
      inner ℝ (S.semigroup s.toNNReal (testToL2 F μ f₀)) φ := by
    intro φ
    have hφi : Integrable (φ : M → ℝ) μ := (Lp.memLp φ).integrable one_le_two
    have hprod : Integrable (fun z : M × ℝ => (φ : M → ℝ) z.1 * (Real.exp (-lam * z.2) * G z.1 z.2))
        (μ.prod (volume.restrict (Ioi 0))) := by
      have h1 : Integrable (fun z : M × ℝ => ‖(φ : M → ℝ) z.1‖ * (B * Real.exp (-lam * z.2)))
          (μ.prod (volume.restrict (Ioi 0))) :=
        hφi.norm.mul_prod hbd
      refine h1.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
      · exact ((Lp.stronglyMeasurable φ).measurable.comp measurable_fst |>.mul
          ((hexpc.measurable.comp measurable_snd).mul hGmeas)).aestronglyMeasurable
      · rw [norm_mul]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        have := hGb z.1 z.2
        nlinarith [Real.exp_pos (-lam * z.2)]
    rw [MeasureTheory.L2.inner_def]
    have e1 : ∫ x, inner ℝ (UL x) (φ x) ∂μ = ∫ x, (φ : M → ℝ) x * U x ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hULae] with x hx
      rw [hx]; simp only [RCLike.inner_apply, conj_trivial]
    rw [e1]
    have e2 : ∀ x, (φ : M → ℝ) x * U x = ∫ s in Ioi (0:ℝ),
        (φ : M → ℝ) x * (Real.exp (-lam * s) * G x s) := fun x => by
      rw [integral_const_mul]
    simp_rw [e2]
    rw [integral_integral_swap hprod]
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have hs' : s.toNNReal ≠ 0 := by
      intro h0; rw [Real.toNNReal_eq_zero] at h0; exact absurd hs (not_lt.2 h0)
    have e3 : ∫ x, (φ : M → ℝ) x * (Real.exp (-lam * s) * G x s) ∂μ =
        Real.exp (-lam * s) * inner ℝ (S.semigroup s.toNNReal (testToL2 F μ f₀)) φ := by
      rw [MeasureTheory.L2.inner_def, ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [Tc_ae F hV hμ hs' (testToL2 F μ f₀)] with x hx
      simp only [RCLike.inner_apply, conj_trivial]
      have : G x s = Tc F hV hμ s.toNNReal (testToL2 F μ f₀) x :=
        semi_Kk_eq_Tc F hV hμ hs' f₀ x
      rw [this, hx]; ring
    exact e3
  have hRg : S.resolvent lam (testToL2 F μ f₀) = UL := by
    refine ext_inner_right ℝ fun φ => ?_
    rw [S.inner_resolvent_eq_laplace hlam, hinner φ]
  obtain ⟨ū, hūs, hūae⟩ := diff_resolvent_smooth' F hV hμ hlam (testToL2 F μ f₀) g hg
    (coeFn_testToL2 F μ f₀)
  have hūU : ū = U := by
    refine continuous_eq_of_ae F hV hμ hūs.continuous hUc ?_
    have hRgae : (((diffFR F hV hμ).resolvent lam (testToL2 F μ f₀) : M →₂[μ] ℝ) : M → ℝ) =ᵐ[μ] U := by
      rw [hRg]; exact hULae
    exact hūae.symm.trans hRgae
  refine ⟨ū, hūs, hūae, fun x => ?_⟩
  rw [hūU]

end Repr

end CutoffRigidity.Riemann.Diff
