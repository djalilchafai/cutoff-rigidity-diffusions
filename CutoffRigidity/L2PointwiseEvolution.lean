module
public import CutoffRigidity.L2TimeIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Pointwise fundamental theorem from genuine L² evolution

Full support and dominated spatial continuity upgrade the actual Hilbert
fundamental theorem to continuous representatives at every spatial point.
-/
public section
namespace CutoffRigidity
open MeasureTheory Filter Set
open scoped Topology

theorem pointwise_integral_eq_sub_of_L2_deriv
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [FirstCountableTopology X]
    (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    (U D : ℝ → X →₂[μ] ℝ) (F G : ℝ → X → ℝ)
    {a b : ℝ} (hab : a ≤ b)
    (hderiv : ∀ s ∈ uIcc a b, HasDerivAt U (D s) s)
    (hInt : IntervalIntegrable D volume a b)
    (hF : ∀ s, Continuous (F s)) (hG : ∀ s, Continuous (G s))
    (hGm : StronglyMeasurable (Function.uncurry G))
    (hU : ∀ s, U s =ᵐ[μ] F s) (hD : ∀ s, D s =ᵐ[μ] G s)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ s x, ‖G s x‖ ≤ M) (x : X) :
    (∫ s in a..b, G s x) = F b x - F a x := by
  have hI := coeFn_integral_L2_of_bounded (volume.restrict (Ioc a b)) μ D
    (hInt.1) G hGm M hM hb hD
  have he (y : X) : (∫ s in a..b, G s y) = ∫ s in Ioc a b, G s y :=
    intervalIntegral.integral_of_le hab
  have hQ : (∫ s in a..b, D s) = ∫ s in Ioc a b, D s :=
    intervalIntegral.integral_of_le hab
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hInt
  have hAE : (fun y => ∫ s in Ioc a b, G s y) =ᵐ[μ] fun y => F b y - F a y := by
    have hs := Lp.coeFn_sub (U b) (U a)
    filter_upwards [hI, hU a, hU b, hs] with y hi ha hb hs
    have hclass : (∫ s in Ioc a b, D s) = U b - U a := hQ.symm.trans hFTC
    rw [hclass, hs, Pi.sub_apply, ha, hb] at hi
    exact hi.symm
  have hcont : Continuous (fun y => ∫ s in Ioc a b, G s y) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    apply tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => M)
    · exact Eventually.of_forall fun z =>
        (hGm.comp_measurable measurable_prodMk_right).aestronglyMeasurable
    · exact Eventually.of_forall fun z => Eventually.of_forall fun s => hb s z
    · exact integrable_const M
    · exact Eventually.of_forall fun s => (hG s).tendsto y
  rw [he]
  exact congrFun (Measure.eq_of_ae_eq hAE hcont ((hF b).sub (hF a))) x

/-- A genuine strong Hilbert derivative with continuous bounded spatial
representatives is the pointwise classical time derivative at interior times. -/
theorem hasDerivAt_of_L2_deriv_continuous_representatives
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [FirstCountableTopology X]
    (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    (U D : ℝ → X →₂[μ] ℝ) (F G : ℝ → X → ℝ)
    {a b t : ℝ} (ht : t ∈ Ioo a b)
    (hderiv : ∀ s ∈ Ioo a b, HasDerivAt U (D s) s)
    (hDc : Continuous D)
    (hF : ∀ s, Continuous (F s)) (hG : ∀ s, Continuous (G s))
    (hGt : ∀ x, Continuous (fun s => G s x))
    (hGm : StronglyMeasurable (Function.uncurry G))
    (hU : ∀ s, U s =ᵐ[μ] F s) (hD : ∀ s, D s =ᵐ[μ] G s)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ s x, ‖G s x‖ ≤ M) (x : X) :
    HasDerivAt (fun s => F s x) (G t x) t := by
  have hc := hGt x
  have hd := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable t t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add (F t x)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
  have he : (∫ s in t..r, G s x) = F r x - F t x := by
    rcases le_total t r with htr | hrt
    · exact pointwise_integral_eq_sub_of_L2_deriv μ U D F G htr
        (fun s hs => hderiv s (by
          rw [uIcc_of_le htr] at hs
          exact ⟨ht.1.trans_le hs.1, hs.2.trans_lt hr.2⟩))
        (hDc.intervalIntegrable t r) hF hG hGm hU hD M hM hb x
    · have hh := pointwise_integral_eq_sub_of_L2_deriv μ U D F G hrt
        (fun s hs => hderiv s (by
          rw [uIcc_of_le hrt] at hs
          exact ⟨hr.1.trans_le hs.1, hs.2.trans_lt ht.2⟩))
        (hDc.intervalIntegrable r t) hF hG hGm hU hD M hM hb x
      rw [intervalIntegral.integral_symm, hh]
      abel
  rw [he]
  abel

/-- Bounded jointly continuous representatives give true strong L²
continuity, without continuity of the chosen measurable representatives. -/
theorem continuous_L2_of_bounded_representatives
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (D : ℝ → X →₂[μ] ℝ) (G : ℝ → X → ℝ)
    (hGc : ∀ s, Continuous (G s)) (hGt : ∀ x, Continuous (fun s => G s x))
    (hD : ∀ s, D s =ᵐ[μ] G s)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ s x, ‖G s x‖ ≤ M) : Continuous D := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have he (s : ℝ) : ‖D s - D t‖ ^ 2 = ∫ x, ‖G s x - G t x‖ ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (D s) (D t), hD s, hD t] with x hs hds hdt
    rw [hs, Pi.sub_apply, hds, hdt, real_inner_self_eq_norm_sq]
  have hlim : Tendsto (fun s => ∫ x, ‖G s x - G t x‖ ^ 2 ∂μ) (𝓝 t) (𝓝 0) := by
    have hh := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝 t)
      (F := fun s x => ‖G s x - G t x‖ ^ 2) (f := fun _ => (0 : ℝ)) (fun _ => (2 * M) ^ 2)
      (Eventually.of_forall fun s => ((hGc s).sub (hGc t)).norm.pow 2 |>.aestronglyMeasurable)
      (Eventually.of_forall fun s => Eventually.of_forall fun x => ?_)
      (integrable_const _) (Eventually.of_forall fun x => ?_)
    · simpa using hh
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (by linarith [hb s x, hb t x])) 2
    · simpa using (((hGt x).tendsto t).sub (tendsto_const_nhds (x := G t x))).norm.pow 2
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hlim
  simpa only [Function.comp_def, ← he, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hh

end CutoffRigidity
