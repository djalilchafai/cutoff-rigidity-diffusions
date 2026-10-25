module

public import CutoffRigidity.Riemann.DiffKer6

/-! # Pointwise time derivative of `t ↦ (T_t f)(x)` (KER, A6) -/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set Topology
open scoped Manifold ContDiff ENNReal Topology NNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Deriv

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

theorem hasDerivAt_Tc {s : ℝ} (hs : 0 < s) (f : testSub F M) (x : M) :
    HasDerivAt (fun r : ℝ => Tc F hV hμ r.toNNReal (testToL2 F μ f) x)
      (Tc F hV hμ s.toNNReal (testToL2 F μ (testGen F hV f)) x) s := by
  set S := diffFR F hV hμ with hS
  set fL := testToL2 F μ f with hfL
  set LfL := testToL2 F μ (testGen F hV f) with hLfL
  set h := fL - LfL with hh
  have hRh : S.R h = fL := testFun_eq_R F hV hμ f
  have hc : (0:ℝ) < s - s / 2 := by linarith
  have hc' : s - s / 2 = s / 2 := by ring
  have hd := S.hasDerivAt_semigroup hc h
  rw [hRh] at hd
  have hd2 := hd.comp_sub_const s (s / 2)
  have ha : (s / 2).toNNReal ≠ 0 := by
    intro h0; rw [Real.toNNReal_eq_zero] at h0; linarith
  have hev := (evalCLM F hV hμ (s / 2).toNNReal x).hasFDerivAt.comp_hasDerivAt s hd2
  have hsum : (s / 2).toNNReal + (s / 2).toNNReal = s.toNNReal := by
    rw [← Real.toNNReal_add (by linarith) (by linarith)]; congr 1; ring
  have hval : (evalCLM F hV hμ (s / 2).toNNReal x) (-(S.semigroup (s - s / 2).toNNReal) (h - fL)) =
      Tc F hV hμ s.toNNReal LfL x := by
    have e1 : h - fL = -LfL := by rw [hh]; abel
    rw [e1, hc']
    simp only [map_neg, neg_neg]
    rw [evalCLM_apply F hV hμ ha, ← Tc_comp F hV hμ ha ha, hsum]
  have hfun : (fun r : ℝ => Tc F hV hμ r.toNNReal fL x) =ᶠ[𝓝 s]
      ((evalCLM F hV hμ (s / 2).toNNReal x) ∘ fun r => (S.semigroup (r - s / 2).toNNReal) fL) := by
    filter_upwards [Ioi_mem_nhds (show s / 2 < s by linarith)] with r hr
    have hr' : s / 2 < r := hr
    have hb : (r - s / 2).toNNReal ≠ 0 := by
      intro h0; rw [Real.toNNReal_eq_zero] at h0; linarith
    simp only [Function.comp_apply]
    rw [evalCLM_apply F hV hμ ha, ← Tc_comp F hV hμ ha hb,
      ← Real.toNNReal_add (by linarith) (by linarith)]
    congr 2; ring
  exact (hev.congr_deriv hval).congr_of_eventuallyEq hfun

end Deriv

end CutoffRigidity.Riemann.Diff
