module

public import CutoffRigidity.Riemann.DiffKer7

/-! # Pointwise continuity at `t = 0` and the pointwise Dynkin identity for `Kk` (KER, A6) -/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set Topology
open scoped Manifold ContDiff ENNReal Topology NNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

/-- An `L²`-convergent sequence has an a.e. convergent subsequence. -/
theorem exists_ae_tendsto_of_tendsto_Lp {M : Type} [MeasurableSpace M] {μ : Measure M}
    (u : ℕ → (M →₂[μ] ℝ)) (v : M →₂[μ] ℝ) (h : Tendsto u atTop (𝓝 v)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ z ∂μ, Tendsto (fun k => (u (ns k) : M → ℝ) z) atTop (𝓝 ((v : M → ℝ) z)) := by
  have hmeas : TendstoInMeasure μ (fun n => ((u n : Lp ℝ 2 μ) : M → ℝ)) atTop (v : M → ℝ) := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) ?_
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 h
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  exact ⟨ns, hns, hae⟩



/-- The time sequence `1/(k+1)`. -/
noncomputable def rk (k : ℕ) : ℝ≥0 := (1 / ((k : ℝ) + 1)).toNNReal

theorem rk_ne_zero (k : ℕ) : rk k ≠ 0 := by
  intro h
  have h1 := Real.toNNReal_eq_zero.1 h
  have : (0:ℝ) < 1 / ((k:ℝ) + 1) := by positivity
  linarith

theorem tendsto_rk : Tendsto rk atTop (𝓝 0) := by
  have h := (continuous_real_toNNReal.tendsto 0).comp
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have e : (0:ℝ).toNNReal = 0 := by simp
  rw [e] at h
  exact h

section Dyn

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

theorem abs_semi_le {t : ℝ≥0} (x : M) (g : M → ℝ) {B : ℝ} (hB : ∀ z, |g z| ≤ B) :
    |semi (Kk F hV hμ) t g x| ≤ B := by
  haveI := Kk_markov F hV hμ t
  haveI : IsProbabilityMeasure (Kk F hV hμ t x) := inferInstance
  unfold semi
  have := norm_integral_le_of_norm_le_const (μ := Kk F hV hμ t x) (f := g) (C := B)
    (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hB z)
  simpa using this

theorem abs_Tc_sub_le {s : ℝ≥0} (hs : s ≠ 0) (f : testSub F M) {B : ℝ}
    (hB : ∀ z, |mgenerator F V (f : M → ℝ) z| ≤ B) (y : M) :
    |Tc F hV hμ s (testToL2 F μ f) y - (f : M → ℝ) y| ≤ B * s := by
  set S := diffFR F hV hμ
  set fL := testToL2 F μ f
  have hlip : ∀ (z : M) (r r' : ℝ≥0), r ≠ 0 → r ≤ r' →
      |Tc F hV hμ r' fL z - Tc F hV hμ r fL z| ≤ B * ((r' : ℝ) - r) := by
    intro z r r' hr hrr'
    have hr0 : (0:ℝ) < r := by positivity
    have := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := fun q : ℝ => Tc F hV hμ q.toNNReal fL z) (s := Ioi (0:ℝ)) (C := B)
      (fun q hq => (hasDerivAt_Tc F hV hμ hq f z).differentiableAt)
      (fun q hq => by
        rw [(hasDerivAt_Tc F hV hμ hq f z).deriv]
        have hq' : q.toNNReal ≠ 0 := by
          intro h0; rw [Real.toNNReal_eq_zero] at h0; exact absurd hq (not_lt.2 h0)
        rw [← semi_Kk_eq_Tc F hV hμ hq' (testGen F hV f) z]
        exact (abs_semi_le F hV hμ z _ (fun w => by
          have := hB w; simpa [testGen_apply] using this)))
      (convex_Ioi 0) (show (r:ℝ) ∈ Ioi 0 from hr0)
      (show (r':ℝ) ∈ Ioi 0 from lt_of_lt_of_le hr0 (by exact_mod_cast hrr'))
    simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast hrr' : (r:ℝ) ≤ r'))]
      using this
  have hconv : Tendsto (fun k : ℕ => S.semigroup (rk k) fL) atTop (𝓝 fL) := by
    have h1 := (S.continuous_semigroup_apply fL).tendsto 0
    rw [S.semigroup_zero] at h1
    simp only [one_apply_eq_self] at h1
    exact h1.comp tendsto_rk
  obtain ⟨ns, hns, hae⟩ := exists_ae_tendsto_of_tendsto_Lp _ _ hconv
  have hall : ∀ᵐ z ∂μ, ∀ k, (S.semigroup (rk (ns k)) fL : M → ℝ) z =
      Tc F hV hμ (rk (ns k)) fL z :=
    ae_all_iff.2 fun k => (Tc_ae F hV hμ (rk_ne_zero _) fL)
  have hfae : ∀ᵐ z ∂μ, (fL : M → ℝ) z = (f : M → ℝ) z := coeFn_testToL2 F μ f
  have hB0 : 0 ≤ B := by
    obtain ⟨z⟩ : Nonempty M := ⟨y⟩
    exact le_trans (abs_nonneg _) (hB z)
  have hgood : ∀ᵐ z ∂μ, 0 ≤ B * s - |Tc F hV hμ s fL z - (f : M → ℝ) z| := by
    filter_upwards [hae, hall, hfae] with z h1 h2 h3
    simp only [h2] at h1
    rw [h3] at h1
    have hlim : Tendsto (fun k => |Tc F hV hμ s fL z - Tc F hV hμ (rk (ns k)) fL z|)
        atTop (𝓝 (|Tc F hV hμ s fL z - (f : M → ℝ) z|)) :=
      ((tendsto_const_nhds.sub h1).abs)
    have hrk : Tendsto (fun k => rk (ns k)) atTop (𝓝 0) := tendsto_rk.comp hns.tendsto_atTop
    have hev : ∀ᶠ k in atTop, rk (ns k) ≤ s := by
      have : (0:ℝ≥0) < s := pos_iff_ne_zero.2 hs
      exact (hrk.eventually (ge_mem_nhds this))
    have hbound : ∀ᶠ k in atTop, |Tc F hV hμ s fL z - Tc F hV hμ (rk (ns k)) fL z| ≤
        B * s := by
      filter_upwards [hev] with k hk
      have h := hlip z (rk (ns k)) s (rk_ne_zero _) hk
      refine h.trans ?_
      nlinarith [(NNReal.coe_nonneg (rk (ns k)))]
    have := le_of_tendsto hlim hbound
    linarith
  have hcont : Continuous fun z => B * s - |Tc F hV hμ s fL z - (f : M → ℝ) z| :=
    continuous_const.sub (((Tc_continuous F hV hμ hs fL).sub f.2.1.continuous).abs)
  have := continuous_nonneg_of_ae F hV hμ hcont hgood y
  linarith

end Dyn

end CutoffRigidity.Riemann.Diff
