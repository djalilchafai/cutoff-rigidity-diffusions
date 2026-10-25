module

public import CutoffRigidity.Riemann.DiffForm2

/-! # Beurling-Deny for the form of `-𝓛` on `L²(μ)` (workstream DIR)

A smooth normal contraction `τ` acts on `L²(μ)` (`liftLp`), preserves the test functions and does
not increase the energy; combined with the generic variational argument of `DiffMarkov` this gives
positivity preservation of the Friedrichs resolvent (`resolvent_posPreserving`).
-/

@[expose] public section

open Bundle MeasureTheory Filter Set
open scoped Manifold ContDiff ENNReal Topology NNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

/-- A smooth nondecreasing `1`-Lipschitz function `τ` with `τ 0 = 0`, `τ s = s` for `s ≥ 0` and
`τ s > s` for `s < 0`.  (Then `τ s - s` is a nonnegative smooth approximation of the negative part
which is strictly positive on `(-∞, 0)`.) -/
theorem exists_posContraction : ∃ τ : ℝ → ℝ, ContDiff ℝ ∞ τ ∧ τ 0 = 0 ∧
    (∀ s, |deriv τ s| ≤ 1) ∧ (∀ s, 0 ≤ s → τ s = s) ∧ (∀ s, s ≤ τ s) ∧
    ∀ s, s < 0 → s < τ s := by
  obtain ⟨B, hB1, hB⟩ := exists_deriv_smoothTransition_bound
  have hBpos : 0 < B := by linarith
  set τ : ℝ → ℝ := fun s => s + (1 - Real.smoothTransition (1 + s)) / B with hτ
  have hsm : ContDiff ℝ ∞ τ := by
    refine contDiff_id.add ?_
    exact (contDiff_const.sub (Real.smoothTransition.contDiff.comp
      (contDiff_const.add contDiff_id))).div_const B
  have hder : ∀ s, deriv τ s = 1 - deriv Real.smoothTransition (1 + s) / B := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => 1 + s) 1 s := (hasDerivAt_id s).const_add 1
    have h2 := ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp) _).hasDerivAt.comp
      s h1
    have h3 : HasDerivAt (fun s : ℝ => s + (1 - Real.smoothTransition (1 + s)) / B)
        (1 + (-(deriv Real.smoothTransition (1 + s) * 1)) / B) s :=
      (hasDerivAt_id s).add ((h2.const_sub 1).div_const B)
    simp only [hτ]
    rw [h3.deriv]
    ring
  have hd0 : ∀ s, 0 ≤ deriv Real.smoothTransition s := fun s => Real.smoothTransition.monotone.deriv_nonneg
  have hdB : ∀ s, deriv Real.smoothTransition s ≤ B := fun s => (le_abs_self _).trans (hB s)
  refine ⟨τ, hsm, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hτ, Real.smoothTransition.one]
  · intro s
    rw [hder s]
    have h1 : deriv Real.smoothTransition (1 + s) / B ≤ 1 := by
      rw [div_le_one hBpos]; exact hdB _
    have h2 : 0 ≤ deriv Real.smoothTransition (1 + s) / B := div_nonneg (hd0 _) hBpos.le
    rw [abs_of_nonneg (by linarith)]
    linarith
  · intro s hs
    simp [hτ, Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 1 + s)]
  · intro s
    have := Real.smoothTransition.le_one (1 + s)
    simp only [hτ]
    have : 0 ≤ (1 - Real.smoothTransition (1 + s)) / B := div_nonneg (by linarith) hBpos.le
    linarith
  · intro s hs
    have := Real.smoothTransition.lt_one_of_lt_one (x := 1 + s) (by linarith)
    simp only [hτ]
    have : 0 < (1 - Real.smoothTransition (1 + s)) / B := div_pos (by linarith) hBpos
    linarith

section Lift

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]

theorem lipschitzWith_of_deriv_le {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ) (h1 : ∀ s, |deriv τ s| ≤ 1) :
    LipschitzWith 1 τ := by
  apply lipschitzWith_of_nnnorm_deriv_le (hτ.differentiable (by simp))
  intro s
  have := h1 s
  rw [← NNReal.coe_le_coe]
  simpa using this

/-- The action of a smooth normal contraction on `L²(μ)`. -/
noncomputable def liftLp {μ : Measure M} {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ) (h0 : τ 0 = 0)
    (h1 : ∀ s, |deriv τ s| ≤ 1) : (M →₂[μ] ℝ) → (M →₂[μ] ℝ) :=
  (lipschitzWith_of_deriv_le hτ h1).compLp h0

theorem liftLp_norm_sub_le {μ : Measure M} {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ) (h0 : τ 0 = 0)
    (h1 : ∀ s, |deriv τ s| ≤ 1) (u v : M →₂[μ] ℝ) :
    ‖liftLp hτ h0 h1 u - liftLp hτ h0 h1 v‖ ≤ 1 * ‖u - v‖ := by
  have := (lipschitzWith_of_deriv_le hτ h1).norm_compLp_sub_le h0 u v
  unfold liftLp
  simpa using this

theorem liftLp_norm_le {μ : Measure M} {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ) (h0 : τ 0 = 0)
    (h1 : ∀ s, |deriv τ s| ≤ 1) (u : M →₂[μ] ℝ) : ‖liftLp hτ h0 h1 u‖ ≤ ‖u‖ := by
  have := (lipschitzWith_of_deriv_le hτ h1).norm_compLp_le h0 u
  unfold liftLp
  simpa using this

theorem coeFn_liftLp {μ : Measure M} {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ) (h0 : τ 0 = 0)
    (h1 : ∀ s, |deriv τ s| ≤ 1) (u : M →₂[μ] ℝ) :
    (liftLp hτ h0 h1 u : M → ℝ) =ᵐ[μ] fun x => τ (u x) :=
  (lipschitzWith_of_deriv_le hτ h1).coeFn_compLp h0 u


end Lift

section Concrete

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

include hV in
theorem integrable_carre (a b : testSub F M) :
    Integrable (fun x => carre F (a : M → ℝ) (b : M → ℝ) x) μ := by
  have hs : MSmooth F (carre F (a : M → ℝ) (b : M → ℝ)) := (weightedRegular V hV).1 _ _ a.2.1 b.2.1
  exact hs.continuous.integrable_of_hasCompactSupport (hasCompactSupport_carre F _ a.2.2)

/-- The test function `τ ∘ a`. -/
def compTest {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ) (h0 : τ 0 = 0) (a : testSub F M) : testSub F M :=
  ⟨τ ∘ (a : M → ℝ), ⟨hτ.contMDiff.comp a.2.1, a.2.2.comp_left h0⟩⟩

theorem liftLp_testToL2 {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ) (h0 : τ 0 = 0)
    (h1 : ∀ s, |deriv τ s| ≤ 1) (a : testSub F M) :
    liftLp (μ := μ) hτ h0 h1 (testToL2 F μ a) = testToL2 F μ (compTest F hτ h0 a) := by
  apply Lp.ext
  filter_upwards [coeFn_liftLp hτ h0 h1 (testToL2 F μ a), coeFn_testToL2 F μ a,
    coeFn_testToL2 F μ (compTest F hτ h0 a)] with x h1 h2 h3
  rw [h1, h3, h2]
  rfl

theorem liftLp_mem_D {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ) (h0 : τ 0 = 0)
    (h1 : ∀ s, |deriv τ s| ≤ 1) (f : (diffFormData F hV hμ).D) :
    ∃ g : (diffFormData F hV hμ).D, (g : M →₂[μ] ℝ) = liftLp hτ h0 h1 (f : M →₂[μ] ℝ) := by
  obtain ⟨_, a, rfl⟩ := f
  exact ⟨⟨testToL2 F μ (compTest F hτ h0 a), _, rfl⟩, (liftLp_testToL2 F hτ h0 h1 a).symm⟩

theorem liftLp_en_le {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ) (h0 : τ 0 = 0)
    (h1 : ∀ s, |deriv τ s| ≤ 1) (f g : (diffFormData F hV hμ).D)
    (hg : (g : M →₂[μ] ℝ) = liftLp hτ h0 h1 (f : M →₂[μ] ℝ)) :
    (diffFormData F hV hμ).en g g ≤ (diffFormData F hV hμ).en f f := by
  obtain ⟨_, a, rfl⟩ := f
  have hg' : g = ⟨testToL2 F μ (compTest F hτ h0 a), _, rfl⟩ :=
    Subtype.ext (by rw [hg]; exact liftLp_testToL2 F hτ h0 h1 a)
  have e1 := en_diffFormData F hV hμ (compTest F hτ h0 a) (compTest F hτ h0 a)
  have e2 := en_diffFormData F hV hμ a a
  have e3 : ∫ x, carre F (compTest F hτ h0 a : M → ℝ) (compTest F hτ h0 a : M → ℝ) x ∂μ ≤
      ∫ x, carre F (a : M → ℝ) (a : M → ℝ) x ∂μ := by
    refine integral_mono (integrable_carre F hV (μ := μ) (compTest F hτ h0 a) (compTest F hτ h0 a))
      (integrable_carre F hV (μ := μ) a a) (fun x => ?_)
    have := (normalContraction_stable F τ hτ h0 h1 (a : M → ℝ) a.2).2 x
    exact this
  rw [hg']
  exact e1.le.trans (e3.trans e2.ge)

variable (T : DirFriedrichs (diffFormData F hV hμ))

/-- **Beurling-Deny: positivity of the resolvent.** If `R` is the resolvent of the Friedrichs form
of `-𝓛` and `g ≥ 0` a.e., then `R g ≥ 0` a.e. -/
theorem resolvent_posPreserving {lam : ℝ} (hlam : 0 < lam) {R : (M →₂[μ] ℝ) →L[ℝ] (M →₂[μ] ℝ)}
    (hR : DirResolvent T lam R) (g : M →₂[μ] ℝ) (hg : 0 ≤ᵐ[μ] g) : 0 ≤ᵐ[μ] R g := by
  obtain ⟨τ, hτ, h0, h1, hτpos, hτle, hτlt⟩ := exists_posContraction
  have h00 : τ 0 = 0 := h0
  set Tm := liftLp (μ := μ) hτ h00 h1 with hTm
  have key : Tm (R g) = R g := by
    refine T.fixed_of_comparison Tm 1 (fun u v => liftLp_norm_sub_le hτ h00 h1 u v)
      (liftLp_mem_D F hV hμ hτ h00 h1) (fun f g hg => liftLp_en_le F hV hμ hτ h00 h1 f g hg)
      (hR.mem g) hlam g (hR.weak g) ?_ (liftLp_norm_le hτ h00 h1 _)
    rw [MeasureTheory.L2.inner_def]
    refine integral_nonneg_of_ae ?_
    filter_upwards [hg, Lp.coeFn_sub (Tm (R g)) (R g), coeFn_liftLp hτ h00 h1 (R g)] with x hx h2 h3
    rw [h2, Pi.sub_apply, h3]
    have := hτle ((R g) x)
    simp only [Pi.zero_apply] at hx ⊢
    simp only [real_inner_eq_re_inner, RCLike.re_to_real]
    simp only [RCLike.inner_apply, conj_trivial]
    exact mul_nonneg (sub_nonneg.2 this) hx
  filter_upwards [coeFn_liftLp hτ h00 h1 (R g)] with x hx
  have h2 : (Tm (R g)) x = (R g) x := by rw [key]
  rw [hx] at h2
  by_contra hneg
  push Not at hneg
  have := hτlt _ hneg
  simp only [Pi.zero_apply] at hneg
  linarith

end Concrete

end CutoffRigidity.Riemann.Diff
