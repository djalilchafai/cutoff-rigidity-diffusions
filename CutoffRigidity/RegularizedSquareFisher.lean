module
public import CutoffRigidity.LogSobolevSquareCore

/-! # Actual Fisher control for positive normalized square regularization -/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal Topology
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Positive normalization supplies actual probability laws whose genuine
canonical Fisher information is bounded by the original square-root energy. -/
theorem relativeFisherInformation_regularized_compact_square_le
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (ε : ℝ) (hε : 0 < ε) :
    let μ := gibbsMeasure volume V
    let a := ∫ x, f x ^ 2 ∂μ
    let r := fun x => ε / (a + ε) + f x ^ 2 / (a + ε)
    ∃ hν : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (r x))),
      letI := hν
      relativeFisherInformation hV hp (μ.withDensity (fun x => ENNReal.ofReal (r x))) ≤
        ENNReal.ofReal ((4 / (a + ε)) * ∫ x, ‖gradient f x‖ ^ 2 ∂μ) := by
  let := hp
  let μ := gibbsMeasure volume V
  let a := ∫ x, f x ^ 2 ∂μ
  let D := a + ε
  let c := ε / D
  let g := fun x => f x ^ 2 / D
  let r := fun x => c + g x
  have ha : 0 ≤ a := integral_nonneg (fun x => sq_nonneg _)
  have hD : 0 < D := by dsimp only [D]; linarith
  have hc : 0 < c := div_pos hε hD
  have hg : ContDiff ℝ 2 g := (hf.pow 2).div_const D
  have hgc : HasCompactSupport g := by
    have hs := hfc.comp_left (g := fun s : ℝ => s ^ 2 / D) (by simp)
    exact hs
  have hr : ContDiff ℝ 1 r := contDiff_const.add (hg.of_le (by norm_num))
  have hrpos (x : E) : c ≤ r x := by
    dsimp only [r, g]
    exact le_add_of_nonneg_right (div_nonneg (sq_nonneg _) hD.le)
  have hNorm : ∫ x, r x ∂μ = 1 := by
    have hi : Integrable (fun x => f x ^ 2) μ :=
      (hf.continuous.memLp_of_hasCompactSupport hfc : MemLp f 2 μ).integrable_sq
    rw [integral_add (integrable_const c) (hi.div_const D), integral_div]
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    rw [integral_div]
    change ε / D + a / D = 1
    rw [← add_div]
    dsimp only [D]
    rw [add_comm ε a]
    exact div_self hD.ne'
  have hν : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (r x))) := by
    constructor
    have hrI : Integrable r μ := (integrable_const c).add (hg.continuous.integrable_of_hasCompactSupport hgc)
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal hrI (Eventually.of_forall (fun x => (hc.trans_le (hrpos x)).le)), hNorm]
    norm_num
  refine ⟨hν, ?_⟩
  let := hν
  have hgradLp : MemLp (gradient r) 2 μ := by
    have hcgrad : HasCompactSupport (gradient g) :=
      (hgc.fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ E).symm) (by simp)
    have heq : gradient r = gradient g := by
      funext x
      change (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fun y => c + g y) x) = _
      rw [fderiv_const_add]
      rfl
    rw [heq]
    exact (continuous_gradient_of_c1 (hg.of_le (by norm_num))).memLp_of_hasCompactSupport hcgrad
  have hScore := integrable_weighted_gradient_of_memLp hr hc hrpos hgradLp
  have hFI := relativeFisherInformation_withDensity_c1 hV hp ρ hρ hHess hr
    (fun x => hc.trans_le (hrpos x)) hν hScore
  have hE : Integrable (fun x => ‖gradient f x‖ ^ 2) μ :=
    ((continuous_gradient_of_c1 (hf.of_le (by norm_num))).memLp_of_hasCompactSupport
      ((hfc.fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ E).symm) (by simp))).norm.integrable_sq
  have hpoint (x : E) : ‖gradient r x‖ ^ 2 / r x ≤ (4 / D) * ‖gradient f x‖ ^ 2 := by
    have heq : r x = (f x ^ 2 + ε) / D := by dsimp only [r, c, g]; ring
    have hγ : gradient r x = (2 * f x / D) • gradient f x :=
      gradient_constant_add_div_square (hf.differentiable (by norm_num)) c D x
    have hs : ‖gradient r x‖ ^ 2 / r x =
        ((4 / D) * ‖gradient f x‖ ^ 2) * (f x ^ 2 / (f x ^ 2 + ε)) := by
      rw [hγ, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, heq]
      field_simp
      ring
    rw [hs]
    have hratio : f x ^ 2 / (f x ^ 2 + ε) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by linarith)
    exact mul_le_of_le_one_right (mul_nonneg (div_nonneg (by norm_num) hD.le) (sq_nonneg _)) hratio
  have hScoreBound := integral_mono hScore (hE.const_mul (4 / D)) hpoint
  rw [integral_const_mul] at hScoreBound
  rw [hFI]
  exact ENNReal.ofReal_le_ofReal hScoreBound

end CutoffRigidity
