module
public import CutoffRigidity.LangevinRpowHarnack
public import CutoffRigidity.GibbsRNLpDuality
public import CutoffRigidity.LangevinChiSquareBound

/-! # Actual Lʳ transition RN densities from power-α Harnack

The true power-α Harnack inequality is integrated against the Gibbs law
with its exact Gaussian-distance weight, signed compact tests are handled
by the positive square-root regularization, and Lᵅ/Lʳ duality on truncated
powers of the density gives ‖dμ_T/dμ‖_{Lʳ} ≤ exp(ρ M/(2(α-1)(e^{2ρT}-1)))
for r = α/(α-1), with M the actual second moment of μ around the start.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 800000 in
/-- Integration of the actual power-α Harnack inequality against its true
exponential distance weight. -/
theorem langevinPositiveProfile_rpow_mul_weight_le_integral
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x) (α : ℝ) (hα : 1 < α)
    (T : ℝ) (hT : 0 < T) (x : E) :
    (langevinPositiveProfile V g B P c T x) ^ α *
      quadraticDistanceWeightIntegral (gibbsMeasure volume V)
        (α * ρ / (2 * (α - 1) * (Real.exp (2 * ρ * T) - 1))) x ≤
      ∫ z, (c + g z) ^ α ∂gibbsMeasure volume V := by
  let := hp
  let μ := gibbsMeasure volume V
  let K := langevinKernel V B P T.toNNReal
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess T.toNNReal
  let b := α * ρ / (2 * (α - 1) * (Real.exp (2 * ρ * T) - 1))
  have hα1 : 0 < α - 1 := by linarith
  have hden : 0 < Real.exp (2 * ρ * T) - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))
  have hb : 0 < b := div_pos (mul_pos (by linarith) hρ) (by positivity)
  obtain ⟨M, hM0, hM⟩ := compact_continuous_norm_bound hg.continuous hgc
  let φ := fun z => (c + g z) ^ α
  have hφpos (z : E) : 0 < c + g z := hm.trans_le (hpos z)
  have hφC : Continuous φ := (continuous_const.add hg.continuous).rpow_const
    (fun z => Or.inl (hφpos z).ne')
  have hφB (z : E) : ‖φ z‖ ≤ m ^ α + (|c| + M) ^ α := by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hφpos z).le _)]
    apply rpow_le_add_of_mem_Icc hm (hpos z)
    exact (le_abs_self _).trans ((abs_add_le _ _).trans (add_le_add le_rfl
      (by simpa only [Real.norm_eq_abs] using hM z)))
  have hφI : Integrable φ μ :=
    (integrable_const _).mono' hφC.aestronglyMeasurable (Eventually.of_forall hφB)
  have hInv : K ∘ₘ μ = μ := langevinKernel_gibbs_invariant hB hV hp ρ hρ hHess T.toNNReal
  have hKI : Integrable (fun y => ∫ z, φ z ∂K y) μ := by
    have hh : Integrable φ (K ∘ₘ μ) := by rw [hInv]; exact hφI
    rw [Measure.comp_eq_comp_const_apply] at hh
    simpa only [Kernel.const_apply] using hh.integral_comp
  have hWI := (quadraticDistanceWeight_integrable μ hb.le x).const_mul
    ((langevinPositiveProfile V g B P c T x) ^ α)
  have hPoint (y : E) : (langevinPositiveProfile V g B P c T x) ^ α * Real.exp (-b * ‖x-y‖ ^ 2) ≤
      ∫ z, φ z ∂K y := by
    have hh := langevinKernel_rpow_harnack_compact_perturbation hB hV hp hg hgc ρ hρ hHess c m hm hpos
      α hα T hT x y
    have he : Real.exp (α * ρ * ‖x - y‖ ^ 2 / (2 * (α - 1) * (Real.exp (2 * ρ * T) - 1))) *
        Real.exp (-b * ‖x-y‖ ^ 2) = 1 := by
      rw [← Real.exp_add]
      have hz : α * ρ * ‖x - y‖ ^ 2 / (2 * (α - 1) * (Real.exp (2 * ρ * T) - 1)) + -b * ‖x-y‖ ^ 2 = 0 := by
        dsimp only [b]; ring
      rw [hz, Real.exp_zero]
    calc
      _ ≤ ((∫ z, φ z ∂K y) * Real.exp (α * ρ * ‖x - y‖ ^ 2 /
            (2 * (α - 1) * (Real.exp (2 * ρ * T) - 1)))) * Real.exp (-b * ‖x-y‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hh (Real.exp_nonneg _)
      _ = _ := by rw [mul_assoc, he, mul_one]
  have hi := integral_mono hWI hKI hPoint
  rw [integral_const_mul, integral_invariantKernel K hInv hφI] at hi
  exact hi

set_option maxHeartbeats 1000000 in
/-- Signed compact C² tests satisfy the actual weighted Lᵅ evaluation
bound, for 1 < α ≤ 2. The positive square-root regularization and the
subadditivity of s ↦ s^(α/2) are used explicitly. -/
theorem langevinKernel_compact_test_rpow_mul_weight_le
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (α : ℝ) (hα : 1 < α) (hα2 : α ≤ 2)
    (T : ℝ) (hT : 0 < T) (x : E) :
    |∫ z, g z ∂langevinKernel V B P T.toNNReal x| ^ α *
      quadraticDistanceWeightIntegral (gibbsMeasure volume V)
        (α * ρ / (2 * (α - 1) * (Real.exp (2 * ρ * T) - 1))) x ≤
      ∫ z, |g z| ^ α ∂gibbsMeasure volume V := by
  let := hp
  let μ := gibbsMeasure volume V
  let K := langevinKernel V B P T.toNNReal
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess T.toNNReal
  have hα0 : 0 < α := zero_lt_one.trans hα
  have hα1 : 0 < α - 1 := by linarith
  let J := quadraticDistanceWeightIntegral μ (α * ρ / (2 * (α - 1) * (Real.exp (2 * ρ * T) - 1))) x
  have hJ : 0 < J := quadraticDistanceWeightIntegral_pos μ
    (div_pos (mul_pos hα0 hρ) (mul_pos (by linarith)
      (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))))).le x
  obtain ⟨M, hM0, hM⟩ := compact_continuous_norm_bound hg.continuous hgc
  have hgαI : Integrable (fun z => |g z| ^ α) μ :=
    (integrable_const (M ^ α)).mono' ((hg.continuous.abs.rpow_const
      (fun _ => Or.inr hα0.le))).aestronglyMeasurable (Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
        exact Real.rpow_le_rpow (abs_nonneg _) (by simpa only [Real.norm_eq_abs] using hM z) hα0.le)
  have hMain (ε : ℝ) (hε : 0 < ε) :
      |∫ z, g z ∂K x| ^ α * J ≤ (∫ z, |g z| ^ α ∂μ) + ε ^ (α / 2) := by
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
    have hroot := langevinPositiveProfile_rpow_mul_weight_le_integral hB hV hp hhC hhc ρ hρ hHess c c hc
      hFloor α hα T hT x
    have hgI : Integrable g (K x) := hg.continuous.integrable_of_hasCompactSupport hgc
    have hhI : Integrable h (K x) := hhC.continuous.integrable_of_hasCompactSupport hhc
    have hfI : Integrable f (K x) := by
      have he : f = fun z => c + h z := by funext z; exact (hfEq z).symm
      rw [he]
      exact (integrable_const c).add hhI
    have hNorm : |∫ z, g z ∂K x| ≤ langevinPositiveProfile V h B P c T x := by
      have hPoint (z : E) : ‖g z‖ ≤ f z := by
        rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt (le_add_of_nonneg_right hε.le)
      rw [← Real.norm_eq_abs]
      calc
        _ ≤ ∫ z, ‖g z‖ ∂K x := norm_integral_le_integral_norm _
        _ ≤ ∫ z, f z ∂K x := integral_mono hgI.norm hfI hPoint
        _ = _ := by
          have he : f = fun z => c + h z := by funext z; exact (hfEq z).symm
          rw [he, integral_add (integrable_const c) hhI]
          simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
          rfl
    have hPow := Real.rpow_le_rpow (abs_nonneg _) hNorm hα0.le
    have hpt (z : E) : (c + h z) ^ α ≤ |g z| ^ α + ε ^ (α / 2) := by
      rw [hfEq]
      dsimp only [f]
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
      have hsq : g z ^ 2 = |g z| ^ (2 : ℝ) := by rw [Real.rpow_two, sq_abs]
      have hadd := Real.rpow_add_le_add_rpow (sq_nonneg (g z)) hε.le (by positivity : (0:ℝ) ≤ α / 2)
        (by linarith : α / 2 ≤ 1)
      have hg2 : (g z ^ 2) ^ (α / 2) = |g z| ^ α := by
        rw [hsq, ← Real.rpow_mul (abs_nonneg _)]
        congr 1
        ring
      rw [hg2] at hadd
      rw [show (1 / 2 : ℝ) * α = α / 2 by ring]
      exact hadd
    have hcI : Integrable (fun z => (c + h z) ^ α) μ := by
      refine (hgαI.add (integrable_const (ε ^ (α / 2)))).mono'
        ((continuous_const.add hhC.continuous).rpow_const
          (fun _ => Or.inr hα0.le)).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (hc.le.trans (hFloor z)) _)]
      exact hpt z
    have hInt : (∫ z, (c + h z) ^ α ∂μ) ≤ (∫ z, |g z| ^ α ∂μ) + ε ^ (α / 2) := by
      calc
        _ ≤ ∫ z, (|g z| ^ α + ε ^ (α / 2)) ∂μ :=
          integral_mono hcI (hgαI.add (integrable_const _)) hpt
        _ = _ := by
          rw [integral_add hgαI (integrable_const _), integral_const]
          simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    exact ((mul_le_mul_of_nonneg_right hPow hJ.le).trans hroot).trans hInt
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hε : 0 < δ ^ (2 / α) := Real.rpow_pos_of_pos hδ _
  have he : (δ ^ (2 / α)) ^ (α / 2) = δ := by
    rw [← Real.rpow_mul hδ.le, show 2 / α * (α / 2) = 1 by field_simp, Real.rpow_one]
  have hh := hMain _ hε
  rwa [he] at hh

set_option maxHeartbeats 1000000 in
/-- Every actual positive-time transition law has an Lʳ RN density with
respect to Gibbs, r = α/(α-1) ≥ 2, with the true integrated Harnack bound.
No density regularity, hypercontractivity, or Lʳ estimate is assumed. -/
theorem langevinKernel_rnDeriv_eLpNorm_le
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (α : ℝ) (hα : 1 < α) (hα2 : α ≤ 2)
    (T : ℝ) (hT : 0 < T) (x : E) :
    eLpNorm (fun y => ((langevinKernel V B P T.toNNReal x).rnDeriv (gibbsMeasure volume V) y).toReal)
      (ENNReal.ofReal (α / (α - 1))) (gibbsMeasure volume V) ≤
      ENNReal.ofReal (Real.exp (ρ / (2 * (α - 1) * (Real.exp (2 * ρ * T) - 1)) *
        ∫ y, ‖x - y‖ ^ 2 ∂gibbsMeasure volume V)) := by
  let := hp
  let μ := gibbsMeasure volume V
  let ν := langevinKernel V B P T.toNNReal x
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess T.toNNReal
  have hα0 : 0 < α := zero_lt_one.trans hα
  have hα1 : 0 < α - 1 := by linarith
  have hden : 0 < Real.exp (2 * ρ * T) - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))
  let b := α * ρ / (2 * (α - 1) * (Real.exp (2 * ρ * T) - 1))
  have hb : 0 < b := div_pos (mul_pos hα0 hρ) (by positivity)
  let J := quadraticDistanceWeightIntegral μ b x
  let Mx := ∫ y, ‖x - y‖ ^ 2 ∂μ
  have hJ : 0 < J := quadraticDistanceWeightIntegral_pos μ hb.le x
  obtain ⟨hRN, -⟩ := langevinKernel_rnDeriv_memLp_two hB hV hp ρ hρ hHess T hT x
  have hAC : ν ≪ μ := langevinKernel_absolutelyContinuous_gibbs hB hV hp ρ hρ hHess x T hT
  have hBound (f : E → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
      |∫ z, f z ∂ν| ≤ J⁻¹ ^ (1 / α) * (eLpNorm f (ENNReal.ofReal α) μ).toReal := by
    have hfLp : MemLp f (ENNReal.ofReal α) μ := hf.continuous.memLp_of_hasCompactSupport hfc
    rw [hfLp.eLpNorm_eq_integral_rpow_norm (by simp [hα0]) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hα0.le, ENNReal.toReal_ofReal
        (Real.rpow_nonneg (integral_nonneg fun z => by positivity) _)]
    simp_rw [Real.norm_eq_abs]
    have hw := langevinKernel_compact_test_rpow_mul_weight_le hB hV hp hf hfc ρ hρ hHess α hα hα2 T hT x
    change |∫ z, f z ∂ν| ^ α * J ≤ _ at hw
    have hI0 : 0 ≤ ∫ z, |f z| ^ α ∂μ := integral_nonneg fun z => by positivity
    have h1 : |∫ z, f z ∂ν| ^ α ≤ J⁻¹ * ∫ z, |f z| ^ α ∂μ := by
      rw [inv_mul_eq_div]; exact (le_div_iff₀ hJ).mpr hw
    have h2 := Real.rpow_le_rpow (by positivity) h1 (by positivity : (0:ℝ) ≤ α⁻¹)
    rw [← Real.rpow_mul (abs_nonneg _), mul_inv_cancel₀ hα0.ne', Real.rpow_one,
      Real.mul_rpow (inv_nonneg.mpr hJ.le) hI0] at h2
    simpa only [one_div] using h2
  have hmain := eLpNorm_rnDeriv_le_of_compact_test_bound hp ν hAC hRN hα hα2 _
    (Real.rpow_nonneg (inv_nonneg.mpr hJ.le) _) hBound
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  have hLower : Real.exp (-b * Mx) ≤ J :=
    exp_neg_second_moment_le_quadraticDistanceWeightIntegral μ hb.le
      (gibbs_memLp_two_id_of_hessian_bound hV ρ hρ hHess) x
  have hInv : J⁻¹ ≤ Real.exp (b * Mx) := by
    have hh := inv_anti₀ (Real.exp_pos (-b * Mx)) hLower
    rwa [show -b * Mx = -(b * Mx) by ring, Real.exp_neg, inv_inv] at hh
  calc
    J⁻¹ ^ (1 / α) ≤ Real.exp (b * Mx) ^ (1 / α) :=
      Real.rpow_le_rpow (inv_nonneg.mpr hJ.le) hInv (by positivity)
    _ = _ := by
      rw [← Real.exp_mul]
      congr 1
      dsimp only [b, Mx]
      field_simp
      rfl

end CutoffRigidity
