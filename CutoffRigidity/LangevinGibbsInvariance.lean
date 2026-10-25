module

public import CutoffRigidity.LangevinOperatorDomain
public import CutoffRigidity.NonnegativeOperatorEvolution
public import CutoffRigidity.GibbsHeatMarkov
public import CutoffRigidity.SmoothTestMeasureExt
public import CutoffRigidity.LangevinForwardEquation

/-! # Genuine Gibbs invariance of the constructed Brownian Langevin kernel

Actual compact-test transition curves solve the strong L² equation in the
true self-adjoint operator graph. Nonnegative-graph uniqueness identifies
them with the canonical form heat. Its integral preservation and equality
of finite measures on actual compact C² tests prove stochastic invariance.
Infinitesimal stationarity is not used as a substitute for this bridge.
-/

public section

namespace CutoffRigidity

open MeasureTheory ProbabilityTheory Set Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Actual stochastic compact tests equal the canonical form heat in L²,
with no supplied invariance, regularity, or operator-identification premise. -/
theorem langevinCompactTestLp_eq_gibbsHeatSemigroup
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (t : NNReal) :
    langevinCompactTestLp hB hV ρ hρ.le hHess hf.continuous hfc (gibbsMeasure volume V) t =
      gibbsHeatSemigroup hV hp ρ hρ hHess t
        ((hf.continuous.memLp_of_hasCompactSupport hfc).toLp f) := by
  have := hp
  let μ := gibbsMeasure volume V
  let U := langevinCompactTestLp hB hV ρ hρ.le hHess hf.continuous hfc μ
  let H := langevinCompactTestLp hB hV ρ hρ.le hHess
    (continuous_langevinDifferentialOperator hV hf) (hasCompactSupport_langevinDifferentialOperator V hfc) μ
  have hgraph (s : NNReal) : (U s,-H s) ∈ (gibbsPositiveGenerator hV hp).graph :=
    langevinCompactTestLp_mem_operatorGraph hB hV hp ρ hρ hHess hf hfc s
  have hd (s : ℝ) (hs : 0 < s) : HasDerivAt (fun r : ℝ => U r.toNNReal) (-(-H s.toNNReal)) s := by
    simpa only [neg_neg] using hasDerivAt_langevinCompactTestLp hB hV hf hfc ρ hρ.le hHess μ hs
  have hh := gibbsHeatSemigroup_unique_strong_solution hV hp ρ hρ hHess (U 0) (-H 0) (hgraph 0)
    (fun r : ℝ => U r.toNNReal) (fun r : ℝ => -H r.toNNReal) t.property
    (((continuous_langevinCompactTestLp hB hV ρ hρ.le hHess hf.continuous hfc μ).comp
      continuous_real_toNNReal).continuousOn)
    (fun s hs => hd s hs.1) (fun s _ => hgraph s.toNNReal)
    (by simp only [Real.toNNReal_zero])
  have hz := langevinCompactTestLp_zero hB hV hf hfc ρ hρ.le hHess μ
  change U 0 = _ at hz
  rw [hz] at hh
  change U t = gibbsHeatSemigroup hV hp ρ hρ hHess t _
  calc
    U t = U (t : ℝ).toNNReal := congrArg U (@Real.toNNReal_coe t).symm
    _ = _ := hh
    _ = _ := congrArg (fun a : NNReal => gibbsHeatSemigroup hV hp ρ hρ hHess a
      ((hf.continuous.memLp_of_hasCompactSupport hfc).toLp f)) (@Real.toNNReal_coe t)

/-- The actual nonlinear stochastic kernel preserves Gibbs integrals of
all genuine compact C² tests. -/
theorem integral_langevinKernel_gibbs_compact
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (t : NNReal) :
    (∫ x, (∫ y, f y ∂langevinKernel V B P t x) ∂gibbsMeasure volume V) =
      ∫ x, f x ∂gibbsMeasure volume V := by
  have := hp
  let μ := gibbsMeasure volume V
  let fLp : E →₂[μ] ℝ := (hf.continuous.memLp_of_hasCompactSupport hfc).toLp f
  calc
    _ = ∫ x, langevinCompactTestLp hB hV ρ hρ.le hHess hf.continuous hfc μ t x ∂μ :=
      integral_congr_ae (langevinCompactTestLp_coeFn hB hV ρ hρ.le hHess hf.continuous hfc μ t).symm
    _ = ∫ x, gibbsHeatSemigroup hV hp ρ hρ hHess t fLp x ∂μ := by
      rw [langevinCompactTestLp_eq_gibbsHeatSemigroup hB hV hp ρ hρ hHess hf hfc t]
    _ = ∫ x, fLp x ∂μ := integral_gibbsHeatSemigroup hV hp ρ hρ hHess t fLp
    _ = _ := integral_congr_ae (hf.continuous.memLp_of_hasCompactSupport hfc : MemLp f 2 μ).coeFn_toLp

/-- Genuine Gibbs invariance for the actual constructed Brownian kernel,
derived from the source assumptions and actual semigroup identification. -/
theorem langevinKernel_gibbs_invariant
    {B : NNReal → Ω → E} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (t : NNReal) : (langevinKernel V B P t) ∘ₘ (gibbsMeasure volume V) = gibbsMeasure volume V := by
  have := hp
  let := langevinKernel_isMarkovKernel hB hV ρ hρ.le hHess t
  apply measure_eq_of_compact_c2_integrals
  intro f hf hfc
  rw [integral_langevinKernel_comp_measure hB hV hf.continuous hfc ρ hρ.le hHess]
  exact integral_langevinKernel_gibbs_compact hB hV hp ρ hρ hHess hf hfc t

end CutoffRigidity
