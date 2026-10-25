module

public import CutoffRigidity.LangevinWeakDriftGenerator
public import CutoffRigidity.LangevinDynkin

/-! # Actual strong L² time evolution of compact Langevin tests

The probability measure used for L² need not be invariant. Actual pointwise
semigroup generator limits and the derived global quotient bound give
strong L² convergence by squared dominated convergence.
-/

public section

namespace CutoffRigidity

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

private theorem tendsto_toL2_filter_of_dominated_sq
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

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- A compact continuous actual transition test is in L² under any actual
initial probability law, with no stochastic invariance hypothesis. -/
theorem langevinKernel_compact_test_memLp
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ≥0) :
    MemLp (fun x => ∫ y, g y ∂langevinKernel V B P t x) 2 μ := by
  obtain ⟨M, _, hM⟩ := compact_continuous_norm_bound hg hgc
  have hm : StronglyMeasurable (fun x => ∫ y, g y ∂langevinKernel V B P t x) :=
    hg.measurable.stronglyMeasurable.integral_kernel
  apply MemLp.of_bound hm.aestronglyMeasurable M
  apply Eventually.of_forall
  intro x
  let := langevinKernel_isMarkovKernel hB hV κ hκ hHess t
  simpa using (norm_integral_le_of_norm_le_const (μ := langevinKernel V B P t x) (Eventually.of_forall hM))

/-- The actual L² transition curve, formed from its proved genuine L²
representatives. No L² contraction or Markov operator is assumed. -/
@[expose] noncomputable def langevinCompactTestLp
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ≥0) : E →₂[μ] ℝ :=
  (langevinKernel_compact_test_memLp hB hV κ hκ hHess hg hgc μ t).toLp
    (fun x => ∫ y, g y ∂langevinKernel V B P t x)

/-- Actual representative equality for the canonical stochastic L² curve. -/
theorem langevinCompactTestLp_coeFn
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ≥0) :
    (langevinCompactTestLp hB hV κ hκ hHess hg hgc μ t : E → ℝ) =ᵐ[μ]
      fun x => ∫ y, g y ∂langevinKernel V B P t x :=
  (langevinKernel_compact_test_memLp hB hV κ hκ hHess hg hgc μ t).coeFn_toLp

/-- The actual stochastic L² curve is strongly continuous under every
probability law used for the Hilbert space; invariance is unnecessary. -/
theorem continuous_langevinCompactTestLp
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (μ : Measure E) [IsProbabilityMeasure μ] :
    Continuous (langevinCompactTestLp hB hV κ hκ hHess hg hgc μ) := by
  obtain ⟨M, hM0, hM⟩ := compact_continuous_norm_bound hg hgc
  apply continuous_iff_continuousAt.mpr
  intro t
  apply tendsto_toL2_filter_of_dominated_sq
    (langevinKernel_compact_test_memLp hB hV κ hκ hHess hg hgc μ t)
    (fun s => langevinKernel_compact_test_memLp hB hV κ hκ hHess hg hgc μ s)
    (fun _ => (2 * M) ^ 2) (integrable_const _) ?_ ?_
  · apply Eventually.of_forall
    intro s
    apply Eventually.of_forall
    intro x
    have hs := langevinKernel_integral_compact_test_norm_le hB hV κ hκ hHess hM s x
    have ht := langevinKernel_integral_compact_test_norm_le hB hV κ hκ hHess hM t x
    have hb := (norm_sub_le _ _).trans (add_le_add hs ht)
    have hb' : ‖(∫ y, g y ∂langevinKernel V B P s x) - ∫ y, g y ∂langevinKernel V B P t x‖ ≤ 2 * M := by
      linarith
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hb'
  · apply Eventually.of_forall
    intro x
    exact (continuous_langevinKernel_integral_of_bounded_continuous hB hV hg ⟨M, hM⟩ κ hκ hHess x).tendsto t

/-- Actual strong L² convergence of the right-time generator quotient.
The limit is the genuine K_t(Lg), not a formal differential placeholder. -/
theorem langevinCompactTestLp_right_generator_tendsto
    {B : ℝ≥0 → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ≥0) :
    Tendsto (fun h : ℝ => h⁻¹ •
      (langevinCompactTestLp hB hV κ hκ hHess hg.continuous hgc μ (t + h.toNNReal) -
        langevinCompactTestLp hB hV κ hκ hHess hg.continuous hgc μ t))
      (𝓝[>] 0) (𝓝 (langevinCompactTestLp hB hV κ hκ hHess
        (continuous_langevinDifferentialOperator hV hg)
        (hasCompactSupport_langevinDifferentialOperator V hgc) μ t)) := by
  let q := fun s x => ∫ y, g y ∂langevinKernel V B P s x
  let F := fun x => ∫ y, langevinDifferentialOperator V g y ∂langevinKernel V B P t x
  have hq (s : ℝ≥0) : MemLp (q s) 2 μ :=
    langevinKernel_compact_test_memLp hB hV κ hκ hHess hg.continuous hgc μ s
  have hF : MemLp F 2 μ := langevinKernel_compact_test_memLp hB hV κ hκ hHess
    (continuous_langevinDifferentialOperator hV hg) (hasCompactSupport_langevinDifferentialOperator V hgc) μ t
  let Q := fun (h : ℝ) (x : E) => (q (t + h.toNNReal) x - q t x) / h
  have hQ (h : ℝ) : MemLp (Q h) 2 μ := by
    simpa only [Q, div_eq_mul_inv, mul_comm, Pi.sub_apply] using (((hq (t + h.toNNReal)).sub (hq t)).const_mul h⁻¹)
  obtain ⟨M, hM0, hM⟩ := exists_uniform_langevinKernel_generator_quotient_bound hB hV hg hgc κ hκ hHess
  obtain ⟨N, hN0, hN⟩ := compact_continuous_norm_bound
    (continuous_langevinDifferentialOperator hV hg) (hasCompactSupport_langevinDifferentialOperator V hgc)
  have hFn (x : E) : ‖F x‖ ≤ N := langevinKernel_integral_compact_test_norm_le hB hV κ hκ hHess hN t x
  have hQbound : ∀ᶠ h : ℝ in 𝓝[>] 0, ∀ x, ‖Q h x‖ ≤ M := by
    filter_upwards [hM] with h hh
    intro x
    dsimp only [Q, q]
    rw [langevinKernel_time_quotient_eq_integral hB hV hg.continuous hgc κ hκ hHess]
    let := langevinKernel_isMarkovKernel hB hV κ hκ hHess t
    have hb := norm_integral_le_of_norm_le_const (μ := langevinKernel V B P t x)
      (f := fun y => ((∫ z, g z ∂langevinKernel V B P h.toNNReal y) - g y) / h) (C := M)
      (Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs] using hh y))
    simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using hb
  have hlim := tendsto_toL2_filter_of_dominated_sq (l := 𝓝[>] (0 : ℝ)) hF hQ
    (fun _ => (M + N) ^ 2) (integrable_const _) ?_ ?_
  · apply hlim.congr'
    apply Eventually.of_forall
    intro h
    apply Lp.ext
    filter_upwards [(hQ h).coeFn_toLp,
      Lp.coeFn_smul h⁻¹ (langevinCompactTestLp hB hV κ hκ hHess hg.continuous hgc μ (t + h.toNNReal) -
        langevinCompactTestLp hB hV κ hκ hHess hg.continuous hgc μ t),
      Lp.coeFn_sub (langevinCompactTestLp hB hV κ hκ hHess hg.continuous hgc μ (t + h.toNNReal))
        (langevinCompactTestLp hB hV κ hκ hHess hg.continuous hgc μ t),
      (hq (t + h.toNNReal)).coeFn_toLp, (hq t).coeFn_toLp] with x hQx hsm hsub hplus hbase
    rw [hsm, Pi.smul_apply, smul_eq_mul, hsub, Pi.sub_apply]
    symm
    rw [hQx]
    change h⁻¹ * ((hq (t + h.toNNReal)).toLp (q (t + h.toNNReal)) x - (hq t).toLp (q t) x) = Q h x
    rw [hplus, hbase]
    dsimp only [Q]
    ring
  · filter_upwards [hQbound] with h hh
    apply Eventually.of_forall
    intro x
    have hb := (norm_sub_le (Q h x) (F x)).trans (add_le_add (hh x) (hFn x))
    exact (sq_le_sq₀ (norm_nonneg _) (add_nonneg hM0 hN0)).mpr hb
  · apply Eventually.of_forall
    intro x
    exact langevinKernel_time_generator_tendsto hB hV hg hgc κ hκ hHess t x

section StrongEvolution

variable {d : ℕ}
variable {B : ℝ≥0 → Ω → (EuclideanSpace ℝ (Fin d))} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : (EuclideanSpace ℝ (Fin d)) → ℝ} (hV : ContDiff ℝ 2 V) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hHess : ∀ x z, κ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]

/-- The canonical stochastic L² curve starts at the actual compact test class. -/
theorem langevinCompactTestLp_zero :
    langevinCompactTestLp hB hV κ hκ hHess hg.continuous hgc μ 0 =
      (hg.continuous.memLp_of_hasCompactSupport hgc).toLp g := by
  apply Lp.ext
  filter_upwards [langevinCompactTestLp_coeFn hB hV κ hκ hHess hg.continuous hgc μ 0,
    (hg.continuous.memLp_of_hasCompactSupport hgc : MemLp g 2 μ).coeFn_toLp] with x hx hxg
  rw [hx, hxg, langevinKernel_zero hB hV κ hκ hHess, Kernel.id_apply, integral_dirac]

/-- Strong right derivative, without any invariant-law premise. -/
theorem hasDerivWithinAt_langevinCompactTestLp_right {s : ℝ} (hs : 0 ≤ s) :
    HasDerivWithinAt
      (fun r : ℝ => langevinCompactTestLp hB hV κ hκ hHess hg.continuous hgc μ r.toNNReal)
      (langevinCompactTestLp hB hV κ hκ hHess
        (continuous_langevinDifferentialOperator hV hg)
        (hasCompactSupport_langevinDifferentialOperator V hgc) μ s.toNNReal) (Ioi s) s := by
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp : s ∉ Ioi s)]
  have hshift : Tendsto (fun r : ℝ => r - s) (𝓝[>] s) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun r : ℝ => r - s) := continuous_id.sub continuous_const
      simpa only [sub_self] using (hc.tendsto s).mono_left
        (show 𝓝[>] s ≤ 𝓝 s from nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact sub_pos.mpr hr
  have hh := (langevinCompactTestLp_right_generator_tendsto hB hV hg hgc κ hκ hHess μ s.toNNReal).comp hshift
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hsum : s.toNNReal + (r - s).toNNReal = r.toNNReal := by
    apply NNReal.eq
    simp only [NNReal.coe_add, Real.coe_toNNReal _ hs, Real.coe_toNNReal _ (sub_nonneg.mpr hr.le),
      Real.coe_toNNReal _ (hs.trans hr.le)]
    ring
  dsimp only [Function.comp_apply]
  rw [hsum, slope_def_module]

/-- Actual Hilbert-valued Duhamel identity, deduced from the derived strong
right derivative and continuity. -/
theorem langevinCompactTestLp_duhamel {T : ℝ} (hT : 0 ≤ T) :
    langevinCompactTestLp hB hV κ hκ hHess hg.continuous hgc μ T.toNNReal =
      langevinCompactTestLp hB hV κ hκ hHess hg.continuous hgc μ 0 +
      ∫ s in 0..T, langevinCompactTestLp hB hV κ hκ hHess
        (continuous_langevinDifferentialOperator hV hg)
        (hasCompactSupport_langevinDifferentialOperator V hgc) μ s.toNNReal := by
  have hc := (continuous_langevinCompactTestLp hB hV κ hκ hHess hg.continuous hgc μ).comp continuous_real_toNNReal
  have hi := (continuous_langevinCompactTestLp hB hV κ hκ hHess
    (continuous_langevinDifferentialOperator hV hg)
    (hasCompactSupport_langevinDifferentialOperator V hgc) μ).comp continuous_real_toNNReal
  have hh := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT hc.continuousOn
    (fun s hs => hasDerivWithinAt_langevinCompactTestLp_right hB hV hg hgc κ hκ hHess μ hs.1.le)
    (hi.intervalIntegrable 0 T)
  simpa only [Function.comp_apply, Real.toNNReal_zero, add_comm] using (eq_add_of_sub_eq hh.symm)

/-- The genuine transition curve solves the strong L² backward equation
at every positive time under any initial probability measure. -/
theorem hasDerivAt_langevinCompactTestLp {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun r : ℝ => langevinCompactTestLp hB hV κ hκ hHess hg.continuous hgc μ r.toNNReal)
      (langevinCompactTestLp hB hV κ hκ hHess
        (continuous_langevinDifferentialOperator hV hg)
        (hasCompactSupport_langevinDifferentialOperator V hgc) μ t.toNNReal) t := by
  let I := fun s : ℝ => langevinCompactTestLp hB hV κ hκ hHess
    (continuous_langevinDifferentialOperator hV hg)
    (hasCompactSupport_langevinDifferentialOperator V hgc) μ s.toNNReal
  have hi : Continuous I := (continuous_langevinCompactTestLp hB hV κ hκ hHess
    (continuous_langevinDifferentialOperator hV hg)
    (hasCompactSupport_langevinDifferentialOperator V hgc) μ).comp continuous_real_toNNReal
  have hh := (intervalIntegral.integral_hasDerivAt_right (hi.intervalIntegrable 0 t)
    hi.aestronglyMeasurable.stronglyMeasurableAtFilter hi.continuousAt).const_add
      (langevinCompactTestLp hB hV κ hκ hHess hg.continuous hgc μ 0)
  apply hh.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with r hr
  exact langevinCompactTestLp_duhamel hB hV hg hgc κ hκ hHess μ hr.le

end StrongEvolution

end CutoffRigidity
