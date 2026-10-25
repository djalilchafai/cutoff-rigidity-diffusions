module

public import CutoffRigidity.Riemann.DiffBEMain1
public import CutoffRigidity.Riemann.DiffBEGreen
public import CutoffRigidity.Riemann.DiffBESemi

/-! # Bakry-Emery, pointwise bound: the integrated differential inequality (workstream BE, part D2)

`∫ ζ (K_t f-gradient) ≤ e^{-ρ t} ...` at the level of `A(0) - c ≤ e^{-ρ t}(A(t) - c)`.
-/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set Topology
open scoped Manifold ContDiff ENNReal NNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Main2

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

/-- `Kk F hV hμ` is a `KerCanonical` kernel. -/
theorem kerCanonical_Kk : KerCanonical F V μ (Kk F hV hμ) := by
  refine ⟨Kk_markov F hV hμ, isDiffusionSemigroup_Kk F hV hμ, Kk_bind F hV hμ,
    fun c u hu hL2 hc t x => Kk_eigen F hV hμ hu hL2 hc t x, fun g hg hc t => ?_⟩
  obtain ⟨B1, hB1⟩ := (hg.continuous.bounded_above_of_compact_support hc)
  obtain ⟨B2, -, hB2⟩ := exists_abs_mgenerator_le F hV hg hc
  have hgen : ∀ s, semi (Kk F hV hμ) s (mgenerator F V g) =
      mgenerator F V (semi (Kk F hV hμ) s g) ∧ MSmooth F (semi (Kk F hV hμ) s g) := by
    intro s
    by_cases hs : s = 0
    · subst hs
      rw [semi_Kk_zero, semi_Kk_zero]; exact ⟨rfl, hg⟩
    · have e1 : semi (Kk F hV hμ) s g = Tc F hV hμ s (testToL2 F μ ⟨g, hg, hc⟩) :=
        funext fun x => semi_Kk_eq_Tc F hV hμ hs ⟨g, hg, hc⟩ x
      have e2 : semi (Kk F hV hμ) s (mgenerator F V g) =
          Tc F hV hμ s (testToL2 F μ (testGen F hV ⟨g, hg, hc⟩)) :=
        funext fun x => semi_Kk_eq_Tc F hV hμ hs (testGen F hV ⟨g, hg, hc⟩) x
      rw [e1, e2]
      exact ⟨(funext fun x => (Tc_generator F hV hμ hs ⟨g, hg, hc⟩ x).symm), Tc_smooth F hV hμ hs _⟩
  refine ⟨(hgen t).2, (hgen t).1.symm, max B1 B2, fun s x => ⟨?_, ?_⟩⟩
  · exact (abs_semi_le F hV hμ x g (fun z => by simpa using hB1 z)).trans (le_max_left _ _)
  · rw [← (hgen s).1]
    exact (abs_semi_le F hV hμ x _ hB2).trans (le_max_right _ _)

theorem sqrt_le_one_add {a : ℝ} (ha : 0 ≤ a) : Real.sqrt a ≤ 1 + a := by
  nlinarith [Real.sq_sqrt ha, Real.sqrt_nonneg a, sq_nonneg (Real.sqrt a - 1)]

variable (hIBP : WeightedIBP F μ V) (hReg : WeightedRegular F V) (hC : WeightedCutoffs F M)

include hIBP hReg hC in
theorem integrable_mul_sqrt {Φ w : M → ℝ} (hΦ : MSmooth F Φ) (hb : ∃ C, ∀ x, |Φ x| ≤ C)
    (hw : InS F V μ w) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x => Φ x * Real.sqrt (carre F w w x + ε)) μ := by
  obtain ⟨C, hC'⟩ := hb
  have hG := integrable_carre_of_InS F hIBP hReg hC hw
  have hGc : Continuous (carre F w w) := (hReg.1 w w hw.1 hw.1).continuous
  refine Integrable.mono' ((hG.add (integrable_const (1 + ε))).const_mul C) ?_ ?_
  · exact (hΦ.continuous.mul (by fun_prop)).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    have h0 := carre_nonneg F w x
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have := sqrt_le_one_add (by linarith : 0 ≤ carre F w w x + ε)
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC' x)
    calc |Φ x| * Real.sqrt (carre F w w x + ε) ≤ C * (1 + (carre F w w x + ε)) :=
          mul_le_mul (hC' x) this (Real.sqrt_nonneg _) hC0
      _ = C * (carre F w w x + (1 + ε)) := by ring

include hIBP hReg hC hV in
/-- The differential inequality `A' ≥ ρ (A - c)` on `(0,t)`. -/
theorem deriv_Afun_ge {ρ : ℝ} (hρ : 0 ≤ ρ) (hB : WeightedBochnerIneq F V ρ)
    (f ζ : testSub F M) (hζ : ∀ x, 0 ≤ (ζ : M → ℝ) x) {ε : ℝ} (hε : 0 < ε) {t s : ℝ}
    (hs : 0 < s) (hst : s < t) :
    ρ * (Afun F (Kk F hV hμ) μ t (f : M → ℝ) (ζ : M → ℝ) ε s - Real.sqrt ε * ∫ x, (ζ : M → ℝ) x ∂μ) ≤
      deriv (Afun F (Kk F hV hμ) μ t (f : M → ℝ) (ζ : M → ℝ) ε) s := by
  have hK := kerCanonical_Kk F hV hμ
  rw [(hasDerivAt_Afun F hK hV hIBP hReg hC f ζ hε hs hst).deriv]
  obtain ⟨hΦ, -, hΦb⟩ := inS_semi F hK hReg ζ s.toNNReal
  obtain ⟨hw, hLw, -⟩ := inS_semi F hK hReg f (t - s).toNNReal
  obtain ⟨C, hCb⟩ := hΦb
  have hΦ0 : ∀ x, 0 ≤ semi (Kk F hV hμ) s.toNNReal (ζ : M → ℝ) x := fun x =>
    semi_nonneg F hK hζ _ x
  have hg := green_sqrt F hIBP hReg hC hρ hB hε hΦ0 ⟨C, fun x => (le_abs_self _).trans (hCb x)⟩ hΦ hw hLw
  have hint := integrable_mul_sqrt F hIBP hReg hC hΦ.1 ⟨C, hCb⟩ hw hε
  have hΦint : Integrable (semi (Kk F hV hμ) s.toNNReal (ζ : M → ℝ)) μ :=
    hΦ.2.1.integrable one_le_two
  have hζm : Measurable (ζ : M → ℝ) := (testSub_continuous F ζ).measurable
  have hinv := integral_semi F hK hζm (testSub_bounded F ζ) s.toNNReal
  have e : ∫ x, semi (Kk F hV hμ) s.toNNReal (ζ : M → ℝ) x *
        (Real.sqrt (carre F (semi (Kk F hV hμ) (t - s).toNNReal (f : M → ℝ))
          (semi (Kk F hV hμ) (t - s).toNNReal (f : M → ℝ)) x + ε) - Real.sqrt ε) ∂μ =
      Afun F (Kk F hV hμ) μ t (f : M → ℝ) (ζ : M → ℝ) ε s - Real.sqrt ε * ∫ x, (ζ : M → ℝ) x ∂μ := by
    unfold Afun
    simp_rw [mul_sub]
    rw [integral_sub hint (hΦint.mul_const _), integral_mul_const, hinv]
    ring
  rw [e] at hg
  exact hg.2.2

include hIBP hReg hC hV in
/-- Integrated form: `A(0) - c ≤ e^{-ρ t} (A(t) - c)`. -/
theorem Afun_comparison {ρ : ℝ} (hρ : 0 ≤ ρ) (hB : WeightedBochnerIneq F V ρ)
    (f ζ : testSub F M) (hζ : ∀ x, 0 ≤ (ζ : M → ℝ) x) {ε : ℝ} (hε : 0 < ε) {t : ℝ}
    (ht : 0 < t) :
    Afun F (Kk F hV hμ) μ t (f : M → ℝ) (ζ : M → ℝ) ε 0 - Real.sqrt ε * ∫ x, (ζ : M → ℝ) x ∂μ ≤
      Real.exp (-ρ * t) * (Afun F (Kk F hV hμ) μ t (f : M → ℝ) (ζ : M → ℝ) ε t -
        Real.sqrt ε * ∫ x, (ζ : M → ℝ) x ∂μ) := by
  have hK := kerCanonical_Kk F hV hμ
  set A := Afun F (Kk F hV hμ) μ t (f : M → ℝ) (ζ : M → ℝ) ε with hA
  set c := Real.sqrt ε * ∫ x, (ζ : M → ℝ) x ∂μ with hc
  set B : ℝ → ℝ := fun s => Real.exp (-ρ * s) * (A s - c) with hBdef
  have hcont : ContinuousOn A (Icc 0 t) :=
    continuousOn_Afun F hK hV hIBP hReg hC f ζ hε ht.le
  have hBc : ContinuousOn B (Icc 0 t) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
      (hcont.sub continuousOn_const)
  have hder : ∀ s ∈ Ioo 0 t, HasDerivAt B (Real.exp (-ρ * s) * (-ρ) * (A s - c) +
      Real.exp (-ρ * s) * deriv A s) s := by
    intro s hs
    have h1 : HasDerivAt A _ s := hasDerivAt_Afun F hK hV hIBP hReg hC f ζ hε hs.1 hs.2
    have h2 : HasDerivAt (fun s => Real.exp (-ρ * s)) (Real.exp (-ρ * s) * (-ρ)) s := by
      have := ((hasDerivAt_id s).const_mul (-ρ)).exp
      simpa using this
    have := h2.mul (h1.sub_const c)
    rw [h1.deriv]
    exact this
  have hmono : MonotoneOn B (Icc 0 t) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 t) hBc ?_ ?_
    · rw [interior_Icc]
      exact fun s hs => (hder s hs).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro s hs
      rw [(hder s hs).deriv]
      have := deriv_Afun_ge F hV hμ hIBP hReg hC hρ hB f ζ hζ hε hs.1 hs.2
      have he := Real.exp_pos (-ρ * s)
      nlinarith [mul_le_mul_of_nonneg_left this he.le]
  have := hmono ⟨le_refl 0, ht.le⟩ ⟨ht.le, le_refl t⟩ ht.le
  simpa [hBdef] using this

end Main2

end CutoffRigidity.Riemann.Diff
