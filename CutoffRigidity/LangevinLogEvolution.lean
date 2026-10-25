module
public import CutoffRigidity.LangevinDeBruijn
public import CutoffRigidity.WeakLaplacianLogChain
public import CutoffRigidity.LangevinBoundedGradientEstimate

/-! # Actual strong L² logarithmic time evolution

Actual compact-test Dynkin differentiation, probability bounds, and
squared dominated convergence justify the logarithmic time derivative.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

theorem tendsto_toL2_filter_of_dominated_sq_evolution
    {X J : Type*} [MeasurableSpace X] {μ : Measure X} {l : Filter J} [l.IsCountablyGenerated]
    {f : X → ℝ} {F : J → X → ℝ} (hf : MemLp f 2 μ) (hF : ∀ j, MemLp (F j) 2 μ)
    (bound : X → ℝ) (hb : Integrable bound μ)
    (hbound : ∀ᶠ j in l, ∀ᵐ x ∂μ, ‖F j x - f x‖ ^ 2 ≤ bound x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun j => F j x) l (𝓝 (f x))) :
    Tendsto (fun j => (hF j).toLp (F j)) l (𝓝 (hf.toLp f)) := by
  have hInt : Tendsto (fun j => ∫ x, ‖F j x - f x‖ ^ 2 ∂μ) l (𝓝 0) := by
    have hh := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := l)
      (F := fun j x => ‖F j x - f x‖ ^ 2) (f := fun _ => (0 : ℝ)) bound
      (Eventually.of_forall (fun j => ((hF j).aestronglyMeasurable.sub hf.aestronglyMeasurable).norm.pow 2))
      ?_ hb ?_
    · simpa using hh
    · filter_upwards [hbound] with j hj
      filter_upwards [hj] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hx
    · filter_upwards [hlim] with x hx
      simpa using ((hx.sub (tendsto_const_nhds (x := f x))).norm.pow 2)
  have hnorm (j : J) : ‖(hF j).toLp (F j) - hf.toLp f‖ ^ 2 = ∫ x, ‖F j x - f x‖ ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hF j).toLp (F j)) (hf.toLp f), (hF j).coeFn_toLp, hf.coeFn_toLp]
      with x hs hj hx
    rw [hs, Pi.sub_apply, hj, hx, real_inner_self_eq_norm_sq]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hInt
  simpa only [Function.comp_def, ← hnorm, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hh


set_option maxHeartbeats 600000 in
/-- Pointwise time derivatives with a true uniform bound give a strong
L² derivative on any probability space by squared dominated convergence. -/
theorem hasDerivAt_toL2_of_uniform_pointwise_derivative
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (F D : ℝ → X → ℝ) (hF : ∀ r, MemLp (F r) 2 μ)
    (hD : ∀ r, 0 < r → MemLp (D r) 2 μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hDeriv : ∀ r, 0 < r → ∀ x, HasDerivAt (fun s => F s x) (D r x) r)
    (hBound : ∀ r, 0 < r → ∀ x, ‖D r x‖ ≤ C)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun r => (hF r).toLp (F r)) ((hD t ht).toLp (D t)) t := by
  let Q (r : ℝ) (x : X) := (r - t)⁻¹ * (F r x - F t x)
  have hQ (r : ℝ) : MemLp (Q r) 2 μ := by
    simpa only [Q, Pi.sub_apply] using ((hF r).sub (hF t)).const_mul (r - t)⁻¹
  have hQB : ∀ᶠ r in 𝓝[≠] t, ∀ x, ‖Q r x‖ ≤ C := by
    filter_upwards [(eventually_gt_nhds ht).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with r hr hne
    have hrt : r - t ≠ 0 := sub_ne_zero.mpr hne
    intro x
    have hh := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun s hs => (hDeriv s hs x).differentiableAt)
      (fun s hs => by rw [(hDeriv s hs x).deriv]; exact hBound s hs x)
      (convex_Ioi (0 : ℝ)) ht hr
    change ‖(r - t)⁻¹ * (F r x - F t x)‖ ≤ C
    rw [norm_mul, Real.norm_eq_abs, abs_inv]
    calc
      |r - t|⁻¹ * ‖F r x - F t x‖ ≤ |r - t|⁻¹ * (C * ‖r - t‖) :=
        mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (abs_nonneg _))
      _ = C := by rw [Real.norm_eq_abs]; field_simp
  have hlim := tendsto_toL2_filter_of_dominated_sq_evolution
    (l := 𝓝[≠] t) (hD t ht) hQ (fun _ => (2 * C) ^ 2) (integrable_const _) ?_ ?_
  · apply hasDerivAt_iff_tendsto_slope.mpr
    apply hlim.congr'
    apply Eventually.of_forall
    intro r
    apply Lp.ext
    filter_upwards [(hQ r).coeFn_toLp,
      Lp.coeFn_smul (r - t)⁻¹ ((hF r).toLp (F r) - (hF t).toLp (F t)),
      Lp.coeFn_sub ((hF r).toLp (F r)) ((hF t).toLp (F t)),
      (hF r).coeFn_toLp, (hF t).coeFn_toLp] with x hqx hsm hsub hrx htx
    rw [slope_def_module, hsm, Pi.smul_apply, smul_eq_mul, hsub, Pi.sub_apply, hrx, htx, hqx]
  · filter_upwards [hQB] with r hr
    apply Eventually.of_forall
    intro x
    have hh := (norm_sub_le (Q r x) (D t x)).trans (add_le_add (hr x) (hBound t ht x))
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) hC)).mpr (by linarith)
  · apply Eventually.of_forall
    intro x
    apply (hDeriv t ht x).tendsto_slope.congr'
    exact Eventually.of_forall (fun r => slope_def_module (fun s => F s x) t r)


variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

@[expose] noncomputable def langevinPositiveProfile (V g : E → ℝ)
    (B : NNReal → Ω → E) (P : Measure Ω) (c r : ℝ) (x : E) : ℝ :=
  c + ∫ y, g y ∂langevinKernel V B P r.toNNReal x

@[expose] noncomputable def langevinProfileGenerator (V g : E → ℝ)
    (B : NNReal → Ω → E) (P : Measure Ω) (r : ℝ) (x : E) : ℝ :=
  ∫ y, langevinDifferentialOperator V g y ∂langevinKernel V B P r.toNNReal x

section Profile
variable {d : ℕ}
variable {B : NNReal → Ω → (EuclideanSpace ℝ (Fin d))} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : (EuclideanSpace ℝ (Fin d)) → ℝ} (hV : ContDiff ℝ 2 V) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z : (EuclideanSpace ℝ (Fin d)), κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x)

include hB hV hg hgc hκ hHess hpos in
/-- Actual Markov integration preserves the initial positive lower bound. -/
theorem langevinPositiveProfile_lower (r : ℝ) (x : (EuclideanSpace ℝ (Fin d))) :
    m ≤ langevinPositiveProfile V g B P c r x := by
  let := langevinKernel_isMarkovKernel hB hV κ hκ hHess r.toNNReal
  obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg.continuous
  have hgI : Integrable g (langevinKernel V B P r.toNNReal x) :=
    (integrable_const M).mono' hg.continuous.aestronglyMeasurable (Eventually.of_forall hM)
  have hh := integral_mono (integrable_const m) ((integrable_const c).add hgI) hpos
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_const c) hgI] at hh
  simpa only [langevinPositiveProfile, integral_const, measureReal_def, measure_univ,
    ENNReal.toReal_one, one_smul] using hh

include hB hV hg hgc hκ hHess hm hpos in
/-- Logarithmic actual transition profiles are genuinely in L² under any
probability law, without an invariance assumption. -/
theorem langevinLogProfile_memLp (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (r : ℝ) :
    MemLp (fun x => Real.log (langevinPositiveProfile V g B P c r x)) 2 μ := by
  obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg.continuous
  have hqM : Measurable (langevinPositiveProfile V g B P c r) :=
    measurable_const.add hg.continuous.measurable.stronglyMeasurable.integral_kernel.measurable
  have hlower := langevinPositiveProfile_lower hB hV hg hgc κ hκ hHess c m hpos r
  have hupper (x : (EuclideanSpace ℝ (Fin d))) : langevinPositiveProfile V g B P c r x ≤ |c| + M := by
    have hh := langevinKernel_integral_compact_test_norm_le hB hV κ hκ hHess hM r.toNNReal x
    exact le_trans (by exact le_abs_self _) (by
      change |c + ∫ y, g y ∂langevinKernel V B P r.toNNReal x| ≤ _
      exact (abs_add_le _ _).trans (add_le_add (le_refl _) (by simpa only [Real.norm_eq_abs] using hh)))
  apply MemLp.of_bound (hqM.log.aestronglyMeasurable) (2 + |Real.log m| + |Real.log (|c| + M)|)
  apply Eventually.of_forall
  intro x
  have hh := norm_one_add_log_le_of_bounds hm (hlower x) (hupper x)
  have he := norm_sub_le (1 + Real.log (langevinPositiveProfile V g B P c r x)) (1 : ℝ)
  have heq : 1 + Real.log (langevinPositiveProfile V g B P c r x) - 1 =
      Real.log (langevinPositiveProfile V g B P c r x) := by ring
  rw [heq, norm_one] at he
  linarith

include hB hV hg hgc hκ hHess hm hpos in
theorem langevinLogProfileDerivative_memLp (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (r : ℝ) :
    MemLp (fun x => langevinProfileGenerator V g B P r x /
      langevinPositiveProfile V g B P c r x) 2 μ := by
  obtain ⟨N, hN0, hN⟩ := compact_continuous_norm_bound
    (continuous_langevinDifferentialOperator hV hg) (hasCompactSupport_langevinDifferentialOperator V hgc)
  have hqM : Measurable (langevinPositiveProfile V g B P c r) :=
    measurable_const.add hg.continuous.measurable.stronglyMeasurable.integral_kernel.measurable
  have hDM : Measurable (langevinProfileGenerator V g B P r) :=
    (continuous_langevinDifferentialOperator hV hg).measurable.stronglyMeasurable.integral_kernel.measurable
  apply MemLp.of_bound (hDM.div hqM).aestronglyMeasurable (N / m)
  apply Eventually.of_forall
  intro x
  have hlower := langevinPositiveProfile_lower hB hV hg hgc κ hκ hHess c m hpos r x
  have hN' := langevinKernel_integral_compact_test_norm_le hB hV κ hκ hHess hN r.toNNReal x
  change ‖langevinProfileGenerator V g B P r x / langevinPositiveProfile V g B P c r x‖ ≤ _
  simp only [norm_div, Real.norm_eq_abs, abs_of_pos (hm.trans_le hlower)]
  exact (div_le_div_of_nonneg_right hN' (hm.trans_le hlower).le).trans
    (div_le_div_of_nonneg_left hN0 hm hlower)

@[expose] noncomputable def langevinLogProfileLp (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (r : ℝ) : (EuclideanSpace ℝ (Fin d)) →₂[μ] ℝ :=
  (langevinLogProfile_memLp hB hV hg hgc κ hκ hHess c m hm hpos μ r).toLp
    (fun x => Real.log (langevinPositiveProfile V g B P c r x))

@[expose] noncomputable def langevinLogProfileDerivativeLp (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (r : ℝ) : (EuclideanSpace ℝ (Fin d)) →₂[μ] ℝ :=
  (langevinLogProfileDerivative_memLp hB hV hg hgc κ hκ hHess c m hm hpos μ r).toLp
    (fun x => langevinProfileGenerator V g B P r x / langevinPositiveProfile V g B P c r x)

include hB hV hg hgc hκ hHess hm hpos in
/-- The actual strong L² logarithmic backward derivative. No logarithmic
time derivative, generator-domain assertion, or regularity estimate is
supplied as a premise. -/
theorem hasDerivAt_langevinLogProfileLp (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (langevinLogProfileLp hB hV hg hgc κ hκ hHess c m hm hpos μ)
      (langevinLogProfileDerivativeLp hB hV hg hgc κ hκ hHess c m hm hpos μ t) t := by
  let q := langevinPositiveProfile V g B P c
  let D := langevinProfileGenerator V g B P
  obtain ⟨N, hN0, hN⟩ := compact_continuous_norm_bound
    (continuous_langevinDifferentialOperator hV hg) (hasCompactSupport_langevinDifferentialOperator V hgc)
  have hlower (r : ℝ) (x : (EuclideanSpace ℝ (Fin d))) : m ≤ q r x :=
    langevinPositiveProfile_lower hB hV hg hgc κ hκ hHess c m hpos r x
  have hDeriv (r : ℝ) (hr : 0 < r) (x : (EuclideanSpace ℝ (Fin d))) :
      HasDerivAt (fun s => Real.log (q s x)) (D r x / q r x) r := by
    have hh := (hasDerivAt_langevinKernel_integral_compact hB hV hg hgc κ hκ hHess x hr).const_add c
    exact hh.log (hm.trans_le (hlower r x)).ne'
  have hbound (r : ℝ) (_hr : 0 < r) (x : (EuclideanSpace ℝ (Fin d))) : ‖D r x / q r x‖ ≤ N / m := by
    have hN' := langevinKernel_integral_compact_test_norm_le hB hV κ hκ hHess hN r.toNNReal x
    simp only [norm_div, Real.norm_eq_abs, abs_of_pos (hm.trans_le (hlower r x))]
    exact (div_le_div_of_nonneg_right hN' (hm.trans_le (hlower r x)).le).trans
      (div_le_div_of_nonneg_left hN0 hm (hlower r x))
  exact hasDerivAt_toL2_of_uniform_pointwise_derivative μ
    (fun r x => Real.log (q r x)) (fun r x => D r x / q r x)
    (fun r => langevinLogProfile_memLp hB hV hg hgc κ hκ hHess c m hm hpos μ r)
    (fun r _hr => langevinLogProfileDerivative_memLp hB hV hg hgc κ hκ hHess c m hm hpos μ r)
    (N / m) (div_nonneg hN0 hm.le) hDeriv hbound ht

end Profile
end CutoffRigidity
