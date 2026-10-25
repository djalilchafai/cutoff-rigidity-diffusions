module
public import CutoffRigidity.LangevinPowerHarnack
public import CutoffRigidity.QuadraticDistanceWeight
public import CutoffRigidity.GibbsRNFromL2Tests
public import CutoffRigidity.LangevinEntropyFinite
public import CutoffRigidity.InvariantKernelL2

/-! # Actual L² transition RN densities from power-two Harnack

The true Gaussian-distance weight is integrated against the actual Gibbs
law. Signed compact tests are handled by genuine positive square-root
regularization, and the actual dense-test/Riesz theorem identifies the RN
density. No density regularity or evaluation bound is assumed.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

@[expose] noncomputable def harnackEvaluationConstant (μ : Measure E) (ρ T : ℝ) (x : E) : ℝ :=
  (Real.sqrt (quadraticDistanceWeightIntegral μ (ρ / (Real.exp (2 * ρ * T) - 1)) x))⁻¹

set_option maxHeartbeats 800000 in
/-- Integration of the actual power-two Harnack inequality against its
true exponential distance weight. -/
theorem langevinPositiveProfile_sq_mul_weight_le_integral
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x)
    (T : ℝ) (hT : 0 < T) (x : E) :
    (langevinPositiveProfile V g B P c T x) ^ 2 *
      quadraticDistanceWeightIntegral (gibbsMeasure volume V) (ρ / (Real.exp (2 * ρ * T) - 1)) x ≤
      ∫ z, (c + g z) ^ 2 ∂gibbsMeasure volume V := by
  let := hp
  let μ := gibbsMeasure volume V
  let K := langevinKernel V B P T.toNNReal
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess T.toNNReal
  let a := ρ / (Real.exp (2 * ρ * T) - 1)
  have ha : 0 < a := div_pos hρ (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity)))
  let f := fun z => c + g z
  have hfLp : MemLp f 2 μ := (memLp_const c).add (hg.continuous.memLp_of_hasCompactSupport hgc)
  have hInv : K ∘ₘ μ = μ := langevinKernel_gibbs_invariant hB hV hp ρ hρ hHess T.toNNReal
  have hKI : Integrable (fun y => ∫ z, f z ^ 2 ∂K y) μ := invariantKernel_integral_sq_integrable K hInv hfLp
  have hWI := (quadraticDistanceWeight_integrable μ ha.le x).const_mul
    ((langevinPositiveProfile V g B P c T x) ^ 2)
  have hPoint (y : E) : (langevinPositiveProfile V g B P c T x) ^ 2 * Real.exp (-a * ‖x-y‖ ^ 2) ≤
      ∫ z, f z ^ 2 ∂K y := by
    have hh := langevinKernel_power_two_harnack_compact_perturbation hB hV hp hg hgc ρ hρ hHess c m hm hpos T hT x y
    have he : Real.exp (ρ * ‖x-y‖ ^ 2 / (Real.exp (2 * ρ * T) - 1)) * Real.exp (-a * ‖x-y‖ ^ 2) = 1 := by
      rw [← Real.exp_add]
      have hz : ρ * ‖x-y‖ ^ 2 / (Real.exp (2 * ρ * T) - 1) + -a * ‖x-y‖ ^ 2 = 0 := by dsimp only [a]; ring
      rw [hz, Real.exp_zero]
    calc
      _ ≤ ((∫ z, f z ^ 2 ∂K y) * Real.exp (ρ * ‖x-y‖ ^ 2 / (Real.exp (2 * ρ * T) - 1))) *
          Real.exp (-a * ‖x-y‖ ^ 2) := mul_le_mul_of_nonneg_right hh (Real.exp_nonneg _)
      _ = _ := by rw [mul_assoc, he, mul_one]
  have hi := integral_mono hWI hKI hPoint
  rw [integral_const_mul, integral_invariantKernel K hInv hfLp.integrable_sq] at hi
  exact hi

set_option maxHeartbeats 1000000 in
/-- Signed compact C² tests satisfy the actual weighted L² evaluation
bound. The positive square-root regularization is constructed explicitly. -/
theorem langevinKernel_compact_test_sq_mul_weight_le
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (T : ℝ) (hT : 0 < T) (x : E) :
    ‖∫ z, g z ∂langevinKernel V B P T.toNNReal x‖ ^ 2 *
      quadraticDistanceWeightIntegral (gibbsMeasure volume V) (ρ / (Real.exp (2 * ρ * T) - 1)) x ≤
      ∫ z, g z ^ 2 ∂gibbsMeasure volume V := by
  let := hp
  let μ := gibbsMeasure volume V
  let K := langevinKernel V B P T.toNNReal
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess T.toNNReal
  let J := quadraticDistanceWeightIntegral μ (ρ / (Real.exp (2 * ρ * T) - 1)) x
  have hJ : 0 < J := quadraticDistanceWeightIntegral_pos μ
    (div_pos hρ (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity)))).le x
  apply le_of_forall_pos_le_add
  intro ε hε
  let c := Real.sqrt ε
  let f := fun z => Real.sqrt (g z ^ 2 + ε)
  let h := fun z => f z - c
  have hc : 0 < c := Real.sqrt_pos.mpr hε
  have hfC : ContDiff ℝ 2 f := ((hg.pow 2).add contDiff_const).sqrt (fun z => by positivity)
  have hhC : ContDiff ℝ 2 h := hfC.sub contDiff_const
  have hhc : HasCompactSupport h := by
    simpa only [h, f, c, Function.comp_def] using hgc.comp_left
      (g := fun a : ℝ => Real.sqrt (a ^ 2 + ε) - Real.sqrt ε) (by simp)
  have hfEq (z : E) : c + h z = f z := by dsimp only [h]; ring
  have hFloor (z : E) : c ≤ c + h z := by
    rw [hfEq]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg _))
  have hroot := langevinPositiveProfile_sq_mul_weight_le_integral hB hV hp hhC hhc ρ hρ hHess c c hc hFloor T hT x
  have hgI : Integrable g (K x) := hg.continuous.integrable_of_hasCompactSupport hgc
  have hhI : Integrable h (K x) := hhC.continuous.integrable_of_hasCompactSupport hhc
  have hfI : Integrable f (K x) := by
    have he : f = fun z => c + h z := by funext z; exact (hfEq z).symm
    rw [he]
    exact (integrable_const c).add hhI
  have hNorm : ‖∫ z, g z ∂K x‖ ≤ langevinPositiveProfile V h B P c T x := by
    have hPoint (z : E) : ‖g z‖ ≤ f z := by
      rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (le_add_of_nonneg_right hε.le)
    calc
      _ ≤ ∫ z, ‖g z‖ ∂K x := norm_integral_le_integral_norm _
      _ ≤ ∫ z, f z ∂K x := integral_mono hgI.norm hfI hPoint
      _ = _ := by
        have he : f = fun z => c + h z := by funext z; exact (hfEq z).symm
        rw [he, integral_add (integrable_const c) hhI]
        simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
        rfl
  have hPPos : 0 ≤ langevinPositiveProfile V h B P c T x :=
    (hc.trans_le (langevinPositiveProfile_lower hB hV hhC hhc ρ hρ.le hHess c c hFloor T x)).le
  have hSq := (sq_le_sq₀ (norm_nonneg _) hPPos).mpr hNorm
  have he (z : E) : (c + h z) ^ 2 = g z ^ 2 + ε := by
    rw [hfEq]
    exact Real.sq_sqrt (add_nonneg (sq_nonneg _) hε.le)
  have hg2I : Integrable (fun z => g z ^ 2) μ := (hg.continuous.memLp_of_hasCompactSupport hgc : MemLp g 2 μ).integrable_sq
  rw [integral_congr_ae (Eventually.of_forall he), integral_add hg2I (integrable_const ε), integral_const] at hroot
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hroot
  exact (mul_le_mul_of_nonneg_right hSq hJ.le).trans hroot


/-- The actual evaluation constant is nonnegative. -/
theorem harnackEvaluationConstant_nonneg (μ : Measure E) (ρ T : ℝ) (x : E) :
    0 ≤ harnackEvaluationConstant μ ρ T x := inv_nonneg.mpr (Real.sqrt_nonneg _)

set_option maxHeartbeats 750000 in
/-- The actual compact-test integral is a bounded L² evaluation functional,
with the true positive Harnack-weight constant. -/
theorem langevinKernel_compact_c2_L2_evaluation_bound
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (T : ℝ) (hT : 0 < T) (x : E) :
    ‖∫ z, g z ∂langevinKernel V B P T.toNNReal x‖ ≤
      harnackEvaluationConstant (gibbsMeasure volume V) ρ T x *
        ‖(hg.continuous.memLp_of_hasCompactSupport hgc : MemLp g 2 (gibbsMeasure volume V)).toLp g‖ := by
  let := hp
  let μ := gibbsMeasure volume V
  let J := quadraticDistanceWeightIntegral μ (ρ / (Real.exp (2 * ρ * T) - 1)) x
  have hJ : 0 < J := quadraticDistanceWeightIntegral_pos μ
    (div_pos hρ (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity)))).le x
  let gLp := (hg.continuous.memLp_of_hasCompactSupport hgc : MemLp g 2 μ).toLp g
  have hn : ‖gLp‖ ^ 2 = ∫ z, g z ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hg.continuous.memLp_of_hasCompactSupport hgc : MemLp g 2 μ).coeFn_toLp] with z hz
    change inner ℝ (gLp z) (gLp z) = _
    rw [hz, Real.inner_apply]
    ring
  have hSq := langevinKernel_compact_test_sq_mul_weight_le hB hV hp hg hgc ρ hρ hHess T hT x
  rw [← hn] at hSq
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (harnackEvaluationConstant_nonneg μ ρ T x) (norm_nonneg _))).mp
  calc
    _ ≤ ‖gLp‖ ^ 2 / J := (le_div_iff₀ hJ).mpr hSq
    _ = _ := by
      change ‖gLp‖ ^ 2 / J = ((Real.sqrt J)⁻¹ * ‖gLp‖) ^ 2
      rw [mul_pow, inv_pow, Real.sq_sqrt hJ.le]
      ring

/-- The source Harnack evaluation envelope is locally bounded by actual
compact lower bounds for its true quadratic-distance weight. -/
theorem exists_bound_harnackEvaluationConstant_on_compact
    (μ : Measure E) [IsProbabilityMeasure μ] {ρ T : ℝ} (hρ : 0 < ρ) (hT : 0 < T)
    (K : Set E) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, harnackEvaluationConstant μ ρ T x ≤ C := by
  have ha : 0 ≤ ρ / (Real.exp (2 * ρ * T) - 1) :=
    (div_pos hρ (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity)))).le
  obtain ⟨m, hm, hBound⟩ := exists_pos_le_quadraticDistanceWeightIntegral_on_compact μ ha K hK
  refine ⟨(Real.sqrt m)⁻¹, inv_nonneg.mpr (Real.sqrt_nonneg _), ?_⟩
  intro x hx
  exact inv_anti₀ (Real.sqrt_pos.mpr hm) (Real.sqrt_le_sqrt (hBound x hx))

/-- Every actual positive-time transition law has an actual L² RN density
relative to Gibbs, with its true pointwise Harnack evaluation envelope.
The RN density is not assumed or selected as a regular representative. -/
theorem langevinKernel_rnDeriv_memLp_two
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (T : ℝ) (hT : 0 < T) (x : E) :
    ∃ hRN : MemLp (fun y => ((langevinKernel V B P T.toNNReal x).rnDeriv (gibbsMeasure volume V) y).toReal)
        2 (gibbsMeasure volume V),
      ‖hRN.toLp _‖ ≤ harnackEvaluationConstant (gibbsMeasure volume V) ρ T x := by
  let := hp
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess T.toNNReal
  apply memLp_rnDeriv_of_compact_c2_L2_bound hV.continuous hp (langevinKernel V B P T.toNNReal x)
    (langevinKernel_absolutelyContinuous_gibbs hB hV hp ρ hρ hHess x T hT)
    (harnackEvaluationConstant (gibbsMeasure volume V) ρ T x)
    (harnackEvaluationConstant_nonneg _ _ _ _)
  intro g hg hgc
  exact langevinKernel_compact_c2_L2_evaluation_bound hB hV hp hg hgc ρ hρ hHess T hT x

end CutoffRigidity
