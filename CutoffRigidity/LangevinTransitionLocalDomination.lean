module
public import CutoffRigidity.LangevinRNL2
public import CutoffRigidity.LangevinRNLocalBound
public import CutoffRigidity.GibbsCompactApproximation

/-! # Genuine local measure bounds for every positive-time transition

The actual power-Harnack L² density bound has a true compact norm envelope.
A genuine time split and Cauchy--Schwarz give local domination of the actual
transition measure by Gibbs, without selecting smooth RN representatives.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 650000 in
theorem langevinKernel_restrict_le_gibbs
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (T : NNReal) (hT : 0 < T) (x : E) (K : Set E) (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ (langevinKernel V B P T x).restrict K ≤ ENNReal.ofReal M • gibbsMeasure volume V := by
  let := hp
  let μ := gibbsMeasure volume V
  let t : NNReal := T / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hRNExists (y : E) : ∃ hRN : MemLp
      (fun z => ((langevinKernel V B P t y).rnDeriv μ z).toReal) 2 μ,
      ‖hRN.toLp _‖ ≤ harnackEvaluationConstant μ ρ t y := by
    have hh := langevinKernel_rnDeriv_memLp_two hB hV hp ρ hρ hHess t htR y
    simpa only [@Real.toNNReal_coe t] using hh
  choose hRN hNorm using hRNExists
  have hLocal (L : Set E) (hL : IsCompact L) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ L, ‖(hRN y).toLp _‖ ≤ C := by
    obtain ⟨C,hC0,hC⟩ := exists_bound_harnackEvaluationConstant_on_compact μ hρ htR L hL
    exact ⟨C,hC0,fun y hy => (hNorm y).trans (hC y hy)⟩
  have hh := langevinKernel_local_domination_of_earlier_L2 hB hV hp ρ hρ hHess t ht hRN hLocal x K hK
  have he : t + t = T := by dsimp [t]; ring
  simpa only [he] using hh

/-- The same genuine transition domination relative to actual Lebesgue
volume, as needed for local weak Sobolev approximation. -/
theorem langevinKernel_restrict_le_volume
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (T : NNReal) (hT : 0 < T) (x : E) (K : Set E) (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ (langevinKernel V B P T x).restrict K ≤ ENNReal.ofReal M • volume := by
  obtain ⟨M,hM,hBound⟩ := langevinKernel_restrict_le_gibbs hB hV hp ρ hρ hHess T hT x K hK
  let D := Real.exp (‖gradient V 0‖ ^ 2 / ρ - V 0)
  refine ⟨M*D,mul_nonneg hM (Real.exp_pos _).le,hBound.trans ?_⟩
  apply Measure.le_iff.mpr
  intro A hA
  have hAμ := (Measure.le_iff.mp (gibbsMeasure_le_smul_volume hV ρ hρ hHess)) A hA
  simp only [Measure.smul_apply,smul_eq_mul] at hAμ ⊢
  rw [ENNReal.ofReal_mul hM,mul_assoc]
  exact mul_le_mul' le_rfl hAμ

end CutoffRigidity
