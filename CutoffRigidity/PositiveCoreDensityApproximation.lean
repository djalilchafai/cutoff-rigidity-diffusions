module
public import CutoffRigidity.CompactC2MeasureApproximation
public import CutoffRigidity.LangevinEntropyContraction

/-! # Actual positive compact C² approximation of bounded positive densities

Continuous compact approximation is applied to the actual square root.
Squaring preserves positivity of the compact perturbation; true mass
normalization and bounded-interval KL continuity preserve relative entropy.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped Topology ENNReal NNReal

/-- KL's integrand is Lipschitz on every positive compact interval. -/
theorem klFun_lipschitzOn_positive_interval {a b : ℝ} (ha : 0 < a) :
    LipschitzOnWith (Real.toNNReal (|Real.log a| + |Real.log b|)) klFun (Icc a b) := by
  apply (convex_Icc a b).lipschitzOnWith_of_nnnorm_deriv_le
    (fun x hx => (hasDerivAt_klFun (ha.trans_le hx.1).ne').differentiableAt)
  intro x hx
  change ‖deriv klFun x‖ ≤ (Real.toNNReal (|Real.log a| + |Real.log b|) : ℝ)
  rw [deriv_klFun, Real.norm_eq_abs, Real.coe_toNNReal _ (add_nonneg (abs_nonneg _) (abs_nonneg _))]
  have hl := Real.log_le_log ha hx.1
  have hu := Real.log_le_log (ha.trans_le hx.1) hx.2
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (Real.log a), abs_nonneg (Real.log b)]
  · linarith [le_abs_self (Real.log b), abs_nonneg (Real.log a)]

set_option maxHeartbeats 700000 in
/-- Actual L¹ approximation remains true after normalization by the
actual masses, with no approximate-normalization premise. -/
theorem normalized_density_L1_tendsto
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ℝ) (u : ℕ → X → ℝ) (hf : Integrable f μ) (hu : ∀ n, Integrable (u n) μ)
    (hfpos : ∀ x, 0 ≤ f x) (hmass : ∫ x, f x ∂μ = 1)
    (_hupos : ∀ n x, 0 ≤ u n x) (hmasspos : ∀ n, 0 < ∫ x, u n x ∂μ)
    (hL1 : Tendsto (fun n => ∫ x, ‖u n x - f x‖ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ‖u n x / (∫ y, u n y ∂μ) - f x‖ ∂μ) atTop (𝓝 0) := by
  let mass := fun n => ∫ x, u n x ∂μ
  have hmasslim : Tendsto mass atTop (𝓝 1) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) _ hL1
    intro n
    rw [← hmass, ← integral_sub (hu n) hf]
    exact norm_integral_le_integral_norm _
  have hinv : Tendsto (fun n => (mass n)⁻¹) atTop (𝓝 (1 : ℝ)) := by simpa using hmasslim.inv₀ (by norm_num)
  have hbnd (n : ℕ) :
      (∫ x, ‖u n x / mass n - f x‖ ∂μ) ≤
        (mass n)⁻¹ * (∫ x, ‖u n x - f x‖ ∂μ) + |(mass n)⁻¹ - 1| := by
    have hp (x : X) : ‖u n x / mass n - f x‖ ≤
        (mass n)⁻¹ * ‖u n x - f x‖ + |(mass n)⁻¹ - 1| * f x := by
      have he : u n x / mass n - f x =
          (mass n)⁻¹ * (u n x - f x) + ((mass n)⁻¹ - 1) * f x := by ring
      rw [he]
      apply (norm_add_le _ _).trans
      simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (show 0 < mass n from hmasspos n)), abs_of_nonneg (hfpos x)]
      exact le_rfl
    have hi := integral_mono (((hu n).div_const _).sub hf).norm
      ((((hu n).sub hf).norm.const_mul _).add (hf.const_mul _)) hp
    simp only [Pi.add_apply, Pi.sub_apply] at hi
    have hAdd : (∫ x, (mass n)⁻¹ * ‖u n x - f x‖ + |(mass n)⁻¹ - 1| * f x ∂μ) =
        (∫ x, (mass n)⁻¹ * ‖u n x - f x‖ ∂μ) + ∫ x, |(mass n)⁻¹ - 1| * f x ∂μ :=
      integral_add (((hu n).sub hf).norm.const_mul _) (hf.const_mul _)
    rw [hAdd, integral_const_mul, integral_const_mul, hmass, mul_one] at hi
    exact hi
  apply squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _)) hbnd
  have hi := (hinv.mul hL1).add ((hinv.sub_const 1).abs)
  simpa only [mul_zero, sub_self, abs_zero, add_zero] using hi

/-- True probability normalization of a nonnegative real density. -/
theorem isProbabilityMeasure_withDensity_ofReal_integral_one
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {f : X → ℝ} (hf : Integrable f μ) (hn : ∀ x, 0 ≤ f x) (hMass : ∫ x, f x ∂μ = 1) :
    IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall hn), hMass]
  norm_num

/-- Genuine KL of a bounded normalized positive density is its actual
finite KL-integrand integral, using the actual Radon--Nikodym identity. -/
theorem klDiv_bounded_positive_density_eq_integral
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {f : X → ℝ} (hf : Measurable f) (M : ℝ) (hn : ∀ x, 0 ≤ f x)
    (hBound : ∀ x, f x ≤ M) (hMass : ∫ x, f x ∂μ = 1) :
    klDiv (μ.withDensity (fun x => ENNReal.ofReal (f x))) μ =
      ENNReal.ofReal (∫ x, klFun (f x) ∂μ) := by
  have hfLp : MemLp f 2 μ := MemLp.of_bound hf.aestronglyMeasurable M
    (Eventually.of_forall (fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hn x)]; exact hBound x))
  have hprob := isProbabilityMeasure_withDensity_ofReal_integral_one (hfLp.integrable (by norm_num)) hn hMass
  let := hprob
  have hfin := klDiv_withDensity_ne_top_of_memLp_two hf hfLp hn hprob
  rw [← ENNReal.ofReal_toReal hfin, toReal_klDiv_eq_integral_klFun (withDensity_absolutelyContinuous _ _)]
  congr 1
  apply integral_congr_ae
  filter_upwards [Measure.rnDeriv_withDensity μ hf.ennreal_ofReal] with x hx
  rw [hx, ENNReal.toReal_ofReal (hn x)]

set_option maxHeartbeats 650000 in
/-- On one fixed positive bounded interval, actual L¹ density convergence
implies convergence of genuine KL, with normalization proved separately. -/
theorem klDiv_tendsto_of_positive_bounded_L1
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ℝ) (u : ℕ → X → ℝ) (hf : Measurable f) (hu : ∀ n, Measurable (u n))
    (a b : ℝ) (ha : 0 < a) (hfB : ∀ x, f x ∈ Icc a b) (huB : ∀ n x, u n x ∈ Icc a b)
    (hfMass : ∫ x, f x ∂μ = 1) (huMass : ∀ n, ∫ x, u n x ∂μ = 1)
    (hL1 : Tendsto (fun n => ∫ x, ‖u n x - f x‖ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => klDiv (μ.withDensity (fun x => ENNReal.ofReal (u n x))) μ)
      atTop (𝓝 (klDiv (μ.withDensity (fun x => ENNReal.ofReal (f x))) μ) ) := by
  have hLip := klFun_lipschitzOn_positive_interval (b := b) ha
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn continuous_klFun.continuousOn
  have hfI : Integrable f μ := (integrable_const b).mono' hf.aestronglyMeasurable
    (Eventually.of_forall (fun x => by rw [Real.norm_eq_abs, abs_of_pos (ha.trans_le (hfB x).1)]; exact (hfB x).2))
  have huI (n : ℕ) : Integrable (u n) μ := (integrable_const b).mono' (hu n).aestronglyMeasurable
    (Eventually.of_forall (fun x => by rw [Real.norm_eq_abs, abs_of_pos (ha.trans_le (huB n x).1)]; exact (huB n x).2))
  have hfKL : Integrable (fun x => klFun (f x)) μ := (integrable_const C).mono'
    (measurable_klFun.comp hf).aestronglyMeasurable (Eventually.of_forall (fun x => hC _ (hfB x)))
  have huKL (n : ℕ) : Integrable (fun x => klFun (u n x)) μ := (integrable_const C).mono'
    (measurable_klFun.comp (hu n)).aestronglyMeasurable (Eventually.of_forall (fun x => hC _ (huB n x)))
  have hIntegral : Tendsto (fun n => ∫ x, klFun (u n x) ∂μ) atTop (𝓝 (∫ x, klFun (f x) ∂μ)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) _
      (show Tendsto (fun n => (Real.toNNReal (|Real.log a| + |Real.log b|) : ℝ) *
        ∫ x, ‖u n x - f x‖ ∂μ) atTop (𝓝 0) by simpa using hL1.const_mul _)
    intro n
    rw [← integral_sub (huKL n) hfKL]
    apply (norm_integral_le_integral_norm _).trans
    have hh := integral_mono ((huKL n).sub hfKL).norm (((huI n).sub hfI).norm.const_mul _)
      (fun x => hLip.norm_sub_le (huB n x) (hfB x))
    simpa only [integral_const_mul, Pi.sub_apply] using hh
  have hFinal := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hIntegral
  simpa only [Function.comp_def, klDiv_bounded_positive_density_eq_integral hf b
      (fun x => (ha.trans_le (hfB x).1).le) (fun x => (hfB x).2) hfMass,
    klDiv_bounded_positive_density_eq_integral (hu _) b
      (fun x => (ha.trans_le (huB _ x).1).le) (fun x => (huB _ x).2) (huMass _)] using hFinal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 750000 in
/-- Genuine positive compact C² perturbations approximate a bounded
positive measurable density in actual L¹, before mass normalization. -/
theorem exists_positive_compact_c2_unnormalized_L1_approx
    (μ : Measure E) [IsProbabilityMeasure μ] {f : E → ℝ} (hf : Measurable f)
    (m M : ℝ) (hm : 0 < m) (hlo : ∀ x, m ≤ f x) (hhi : ∀ x, f x ≤ M) :
    ∃ ψ : ℕ → E → ℝ,
      (∀ n, ContDiff ℝ 2 (ψ n)) ∧ (∀ n, HasCompactSupport (ψ n)) ∧
      (∀ n x, ‖ψ n x‖ ≤ Real.sqrt M + 1) ∧
      Tendsto (fun n => ∫ x, ‖(m + ψ n x ^ 2) - f x‖ ∂μ) atTop (𝓝 0) := by
  let φ := fun x => Real.sqrt (f x - m)
  have hM : 0 < M := hm.trans_le ((hlo 0).trans (hhi 0))
  have hφ : Measurable φ := (hf.sub_const m).sqrt
  have hφB (x : E) : ‖φ x‖ ≤ Real.sqrt M := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (by linarith [hhi x])
  obtain ⟨ψ, hψ, hψc, hψB, hψlim⟩ := exists_bounded_compact_c2_L1_approx μ hφ
    (Real.sqrt M) (Real.sqrt_nonneg _) hφB
  refine ⟨ψ, hψ, hψc, hψB, ?_⟩
  have hfI : Integrable f μ := (integrable_const M).mono' hf.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_pos (hm.trans_le (hlo x))]; exact hhi x)
  have hφI : Integrable φ μ := (integrable_const (Real.sqrt M)).mono' hφ.aestronglyMeasurable
    (Eventually.of_forall hφB)
  have hψI (n : ℕ) : Integrable (ψ n) μ := (integrable_const (Real.sqrt M + 1)).mono'
    (hψ n).continuous.aestronglyMeasurable (Eventually.of_forall (hψB n))
  have hsqc (n : ℕ) : HasCompactSupport (fun x => ψ n x ^ 2) := by
    simpa only [Function.comp_def] using (hψc n).comp_left (g := fun a : ℝ => a ^ 2) (by simp)
  have hsqCont (n : ℕ) : Continuous (fun x => ψ n x ^ 2) := by
    simpa only [Pi.pow_def] using (hψ n).continuous.pow 2
  have huI (n : ℕ) : Integrable (fun x => m + ψ n x ^ 2) μ :=
    (integrable_const m).add ((hsqCont n).integrable_of_hasCompactSupport (hsqc n))
  have hpoint (n : ℕ) (x : E) : ‖(m + ψ n x ^ 2) - f x‖ ≤
      (2 * Real.sqrt M + 1) * ‖φ x - ψ n x‖ := by
    have he : (φ x) ^ 2 = f x - m := Real.sq_sqrt (sub_nonneg.mpr (hlo x))
    have hsum : |ψ n x + φ x| ≤ 2 * Real.sqrt M + 1 := by
      have h1 : |ψ n x| ≤ Real.sqrt M + 1 := by simpa only [Real.norm_eq_abs] using hψB n x
      have h2 : |φ x| ≤ Real.sqrt M := by simpa only [Real.norm_eq_abs] using hφB x
      exact (abs_add_le _ _).trans (by linarith)
    have hid : (m + ψ n x ^ 2) - f x = (ψ n x - φ x) * (ψ n x + φ x) := by nlinarith only [he]
    rw [Real.norm_eq_abs, hid, abs_mul, Real.norm_eq_abs, abs_sub_comm]
    exact (mul_le_mul_of_nonneg_left hsum (abs_nonneg _)).trans_eq (mul_comm _ _)
  have hbound (n : ℕ) : (∫ x, ‖(m + ψ n x ^ 2) - f x‖ ∂μ) ≤
      (2 * Real.sqrt M + 1) * ∫ x, ‖φ x - ψ n x‖ ∂μ := by
    have hh := integral_mono ((huI n).sub hfI).norm ((hφI.sub (hψI n)).norm.const_mul _) (hpoint n)
    simpa only [integral_const_mul, Pi.sub_apply] using hh
  exact squeeze_zero (fun n => integral_nonneg (fun x => norm_nonneg _)) hbound
    (by simpa only [mul_zero] using hψlim.const_mul (2 * Real.sqrt M + 1))


set_option maxHeartbeats 900000 in
/-- Actual positive normalized constant-plus-compact C² densities converge
in L¹ and genuine KL to every bounded positive measurable probability
density. The masses, positive floors and all convergence are constructed. -/
theorem exists_positive_compact_c2_density_L1_KL_approx
    (μ : Measure E) [IsProbabilityMeasure μ] {f : E → ℝ} (hf : Measurable f)
    (m M : ℝ) (hm : 0 < m) (hlo : ∀ x, m ≤ f x) (hhi : ∀ x, f x ≤ M)
    (hMass : ∫ x, f x ∂μ = 1) :
    ∃ (c : ℕ → ℝ) (g : ℕ → E → ℝ),
      (∀ n, ContDiff ℝ 2 (g n)) ∧ (∀ n, HasCompactSupport (g n)) ∧
      (∀ n, 0 < c n) ∧ (∀ n x, c n ≤ c n + g n x) ∧
      (∀ n, ∫ x, c n + g n x ∂μ = 1) ∧
      Tendsto (fun n => ∫ x, ‖c n + g n x - f x‖ ∂μ) atTop (𝓝 0) ∧
      Tendsto (fun n => klDiv (μ.withDensity (fun x => ENNReal.ofReal (c n + g n x))) μ)
        atTop (𝓝 (klDiv (μ.withDensity (fun x => ENNReal.ofReal (f x))) μ)) := by
  obtain ⟨ψ, hψ, hψc, hψB, hψlim⟩ :=
    exists_positive_compact_c2_unnormalized_L1_approx μ hf m M hm hlo hhi
  let u := fun n x => m + ψ n x ^ 2
  let A := m + (Real.sqrt M + 1) ^ 2
  have hApos : 0 < A := add_pos_of_pos_of_nonneg hm (sq_nonneg _)
  have huMeas (n : ℕ) : Measurable (u n) := measurable_const.add ((hψ n).continuous.measurable.pow_const 2)
  have huLower (n : ℕ) (x : E) : m ≤ u n x := le_add_of_nonneg_right (sq_nonneg _)
  have huUpper (n : ℕ) (x : E) : u n x ≤ A := by
    change m + ψ n x ^ 2 ≤ m + (Real.sqrt M + 1) ^ 2
    have hsq : ψ n x ^ 2 ≤ (Real.sqrt M + 1) ^ 2 := by
      simpa only [Real.norm_eq_abs, sq_abs] using
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (hψB n x)
    exact add_le_add le_rfl hsq
  have huI (n : ℕ) : Integrable (u n) μ := (integrable_const A).mono' (huMeas n).aestronglyMeasurable
    (Eventually.of_forall (fun x => by rw [Real.norm_eq_abs, abs_of_pos (hm.trans_le (huLower n x))]; exact huUpper n x))
  have hfI : Integrable f μ := (integrable_const M).mono' hf.aestronglyMeasurable
    (Eventually.of_forall (fun x => by rw [Real.norm_eq_abs, abs_of_pos (hm.trans_le (hlo x))]; exact hhi x))
  let mass := fun n => ∫ x, u n x ∂μ
  have hmassLower (n : ℕ) : m ≤ mass n := by
    have hh := integral_mono (integrable_const m) (huI n) (huLower n)
    simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using hh
  have hmassUpper (n : ℕ) : mass n ≤ A := by
    have hh := integral_mono (huI n) (integrable_const A) (huUpper n)
    simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using hh
  have hmassPos (n : ℕ) : 0 < mass n := hm.trans_le (hmassLower n)
  let c := fun n => m / mass n
  let g := fun n x => ψ n x ^ 2 / mass n
  let q := fun n x => c n + g n x
  have hqEq (n : ℕ) : q n = fun x => u n x / mass n := by
    funext x
    dsimp only [q, c, g, u]
    ring
  have hg (n : ℕ) : ContDiff ℝ 2 (g n) := ((hψ n).pow 2).div_const _
  have hgc (n : ℕ) : HasCompactSupport (g n) := by
    simpa only [Function.comp_def] using (hψc n).comp_left (g := fun a : ℝ => a ^ 2 / mass n) (by simp)
  have hcPos (n : ℕ) : 0 < c n := div_pos hm (hmassPos n)
  have hqFloor (n : ℕ) (x : E) : c n ≤ q n x :=
    le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (hmassPos n).le)
  have hqMass (n : ℕ) : ∫ x, q n x ∂μ = 1 := by
    rw [hqEq, integral_div]
    exact div_self (hmassPos n).ne'
  have hqL1 : Tendsto (fun n => ∫ x, ‖q n x - f x‖ ∂μ) atTop (𝓝 0) := by
    have hh := normalized_density_L1_tendsto μ f u hfI huI
      (fun x => (hm.trans_le (hlo x)).le) hMass
      (fun n x => (hm.trans_le (huLower n x)).le) hmassPos hψlim
    simpa only [hqEq] using hh
  let a := min m (m / A)
  let b := max M (A / m)
  have ha : 0 < a := lt_min hm (div_pos hm hApos)
  have hfInterval (x : E) : f x ∈ Icc a b :=
    ⟨(min_le_left _ _).trans (hlo x), (hhi x).trans (le_max_left _ _)⟩
  have hqInterval (n : ℕ) (x : E) : q n x ∈ Icc a b := by
    rw [hqEq]
    constructor
    · apply (min_le_right _ _).trans
      exact (div_le_div_of_nonneg_left hm.le (hmassPos n) (hmassUpper n)).trans
        (div_le_div_of_nonneg_right (huLower n x) (hmassPos n).le)
    · apply le_trans _ (le_max_right _ _)
      exact (div_le_div_of_nonneg_right (huUpper n x) (hmassPos n).le).trans
        (div_le_div_of_nonneg_left (hApos.le) hm (hmassLower n))
  refine ⟨c, g, hg, hgc, hcPos, hqFloor, hqMass, hqL1, ?_⟩
  exact klDiv_tendsto_of_positive_bounded_L1 μ f q hf
    (fun n => measurable_const.add (hg n).continuous.measurable) a b ha hfInterval hqInterval hMass hqMass hqL1

end CutoffRigidity
