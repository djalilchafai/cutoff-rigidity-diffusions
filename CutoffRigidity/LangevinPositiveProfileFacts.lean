module
public import CutoffRigidity.LangevinPointwiseEntropyInterpolation
public import CutoffRigidity.LangevinL1Duality
public import CutoffRigidity.LangevinDeBruijn

/-! # Genuine normalization and entropy pairing of positive profiles -/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem langevinPositiveProfile_eq_kernel_integral
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (hg : Continuous g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (c r : ℝ) (x : E) :
    langevinPositiveProfile V g B P c r x = ∫ y, (c + g y) ∂langevinKernel V B P r.toNNReal x := by
  let := langevinKernel_isMarkovKernel hB hV ρ hρ hHess r.toNNReal
  obtain ⟨M,hM⟩ := hgc.exists_bound_of_continuous hg
  have hi : Integrable g (langevinKernel V B P r.toNNReal x) :=
    (integrable_const M).mono' hg.aestronglyMeasurable (Eventually.of_forall hM)
  rw [integral_add (integrable_const c) hi]
  simp [langevinPositiveProfile]

theorem integral_langevinPositiveProfile
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (c r : ℝ) :
    (∫ x, langevinPositiveProfile V g B P c r x ∂gibbsMeasure volume V) =
      ∫ x, (c + g x) ∂gibbsMeasure volume V := by
  let := hp
  simp_rw [langevinPositiveProfile_eq_kernel_integral hB hV hg hgc ρ hρ.le hHess c r]
  exact integral_invariantKernel (langevinKernel V B P r.toNNReal)
    (langevinKernel_gibbs_invariant hB hV hp ρ hρ hHess r.toNNReal)
    ((integrable_const c).add (hg.integrable_of_hasCompactSupport hgc))

theorem langevinPositiveProfile_probability
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V g : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (c m : ℝ) (hm : 0 < m) (hpos : ∀ x, m ≤ c + g x)
    (hNorm : ∫ x, (c + g x) ∂gibbsMeasure volume V = 1) (r : ℝ) :
    IsProbabilityMeasure ((gibbsMeasure volume V).withDensity
      (fun x => ENNReal.ofReal (langevinPositiveProfile V g B P c r x))) := by
  let := hp
  have hq : Continuous (langevinPositiveProfile V g B P c r) := continuous_const.add
    (contDiff_one_langevinKernel_integral hB hV ρ hρ.le hHess (hg.of_le (by norm_num)) hgc r.toNNReal).continuous
  obtain ⟨M,hM⟩ := hgc.exists_bound_of_continuous hg.continuous
  have hqb (x : E) : ‖langevinPositiveProfile V g B P c r x‖ ≤ |c| + M := by
    exact (norm_add_le _ _).trans (add_le_add (by simp)
      (langevinKernel_integral_compact_test_norm_le hB hV ρ hρ.le hHess hM r.toNNReal x))
  have hi : Integrable (langevinPositiveProfile V g B P c r) (gibbsMeasure volume V) :=
    (integrable_const (|c|+M)).mono' hq.aestronglyMeasurable (Eventually.of_forall hqb)
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall fun x => (hm.trans_le
        (langevinPositiveProfile_lower hB hV hg hgc ρ hρ.le hHess c m hpos r x)).le),
    integral_langevinPositiveProfile hB hV hp hg.continuous hgc ρ hρ hHess c r, hNorm]
  norm_num

end CutoffRigidity
