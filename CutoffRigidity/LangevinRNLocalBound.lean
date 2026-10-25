module
public import CutoffRigidity.L2RNDensityIntegration
public import CutoffRigidity.RNDensityLocalDomination
public import CutoffRigidity.LangevinEntropyFinite
public import CutoffRigidity.LangevinL1Density

/-! # Actual local transition-density domination from earlier L² densities

The actual RN evolution and time split are tested using genuine L²
Cauchy--Schwarz. A compact uniform earlier evaluation norm gives an actual
local measure bound, without choosing pointwise transition-density versions.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem langevinKernel_add_apply_eq_comp
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (s t : NNReal) (x : E) :
    langevinKernel V B P (s+t) x = langevinKernel V B P t ∘ₘ langevinKernel V B P s x := by
  rw [← langevinKernel_comp hB hV ρ hρ hHess s t]
  rfl

theorem langevinKernel_rnDeriv_time_split_le
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (t : NNReal) (ht : 0 < t)
    (hRN : ∀ x : E, MemLp (fun y => ((langevinKernel V B P t x).rnDeriv (gibbsMeasure volume V) y).toReal)
      2 (gibbsMeasure volume V)) (x : E) :
    ∀ᵐ y ∂gibbsMeasure volume V,
      ((langevinKernel V B P (t+t) x).rnDeriv (gibbsMeasure volume V) y).toReal ≤
        ‖(hRN y).toLp _‖ * ‖(hRN x).toLp _‖ := by
  let := hp
  let μ := gibbsMeasure volume V
  let K := langevinKernel V B P t
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t
  have hAC (z : E) : K z ≪ μ := by
    have hh := langevinKernel_absolutelyContinuous_gibbs hB hV hp ρ hρ hHess z t ht
    simpa only [@Real.toNNReal_coe t] using hh
  have he := langevinKernel_rnDeriv_toReal hB hV hp ρ hρ hHess (K x) (hAC x) t
  have hsplit : langevinKernel V B P (t+t) x = K ∘ₘ K x :=
    langevinKernel_add_apply_eq_comp hB hV ρ hρ.le hHess t t x
  rw [← hsplit] at he
  filter_upwards [he] with y hy
  rw [hy]
  apply (le_abs_self _).trans
  simpa only [← Real.norm_eq_abs] using norm_integral_le_L2_rnDeriv (K y) μ (hAC y) (hRN y)
    (Measure.measurable_rnDeriv (K x) μ).ennreal_toReal (hRN x)

theorem langevinKernel_local_domination_of_earlier_L2
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (t : NNReal) (ht : 0 < t)
    (hRN : ∀ x : E, MemLp (fun y => ((langevinKernel V B P t x).rnDeriv (gibbsMeasure volume V) y).toReal)
      2 (gibbsMeasure volume V))
    (hLocal : ∀ K : Set E, IsCompact K → ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ‖(hRN y).toLp _‖ ≤ C)
    (x : E) (K : Set E) (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ (langevinKernel V B P (t+t) x).restrict K ≤ ENNReal.ofReal M • gibbsMeasure volume V := by
  let := hp
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess (t+t)
  obtain ⟨C,hC0,hC⟩ := hLocal K hK
  refine ⟨C * ‖(hRN x).toLp _‖,mul_nonneg hC0 (norm_nonneg _),?_⟩
  have hAC : langevinKernel V B P (t+t) x ≪ gibbsMeasure volume V := by
    have hh := langevinKernel_absolutelyContinuous_gibbs hB hV hp ρ hρ hHess x ((t+t : NNReal) : ℝ)
      (show (0 : ℝ) < (t+t : NNReal) by exact_mod_cast add_pos ht ht)
    simpa only [@Real.toNNReal_coe (t+t)] using hh
  apply measure_restrict_le_of_rnDeriv_toReal_bound _ _ hAC K hK.measurableSet
    (C * ‖(hRN x).toLp _‖) (mul_nonneg hC0 (norm_nonneg _))
  filter_upwards [langevinKernel_rnDeriv_time_split_le hB hV hp ρ hρ hHess t ht hRN x] with y hy hyK
  exact hy.trans (mul_le_mul_of_nonneg_right (hC y hyK) (norm_nonneg _))

end CutoffRigidity
