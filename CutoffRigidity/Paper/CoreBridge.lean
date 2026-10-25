module

public import CutoffRigidity.Statements
public import CutoffRigidity.LangevinKernel
public import CutoffRigidity.LangevinBrownian
public import CutoffRigidity.RelativeLpDistance
public import CutoffRigidity.ConvexInteraction

/-! # Bridges from the statement surface to the library: core objects

The compact Mathlib-only definitions of `CutCur` (the Gibbs measure, the
generator, standard Brownian motion, strong solutions of the Langevin equation,
the coupling Wasserstein distance, total variation and the relative `Lᵖ`
distance) are identified with the library constructions. Strong solutions are
pathwise unique for a convex `C²` potential, so their laws at fixed times are
the library Langevin kernel; the library process is such a strong solution.
-/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

variable {d : ℕ}

/-! ### The Gibbs measure and the generator -/

theorem gibbs_eq_gibbsMeasure (V : CutCur.Rd d → ℝ) : CutCur.gibbs V = gibbsMeasure volume V :=
  rfl

/-- Second derivatives along a fixed direction, for a twice differentiable function. -/
theorem fderiv_fderiv_apply_eq {f : CutCur.Rd d → ℝ} (hf : ContDiff ℝ 2 f) (x v : CutCur.Rd d) :
    fderiv ℝ (fderiv ℝ f) x v v = fderiv ℝ (fun y => fderiv ℝ f y v) x v := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  rw [fderiv_clm_apply hdf (differentiableAt_const _)]
  simp

theorem laplacian_eq_euclideanLaplacian {f : CutCur.Rd d → ℝ} (hf : ContDiff ℝ 2 f)
    (x : CutCur.Rd d) : CutCur.laplacian f x = euclideanLaplacian f x := by
  unfold CutCur.laplacian euclideanLaplacian
  exact Finset.sum_congr rfl fun i _ => fderiv_fderiv_apply_eq hf x _

/-- The elementary generator is the library differential operator on `C²` functions. -/
theorem generator_eq_langevinDifferentialOperator (V : CutCur.Rd d → ℝ) {f : CutCur.Rd d → ℝ}
    (hf : ContDiff ℝ 2 f) : CutCur.generator V f = langevinDifferentialOperator V f := by
  funext x
  rw [CutCur.generator, langevinDifferentialOperator, laplacian_eq_euclideanLaplacian hf]

theorem isEigenfunction_iff {V f : CutCur.Rd d → ℝ} {r : ℝ} :
    CutCur.IsEigenfunction V r f ↔ ContDiff ℝ 2 f ∧ MemLp f 2 (gibbsMeasure volume V) ∧
      ∀ x, langevinDifferentialOperator V f x = -r * f x := by
  constructor
  · rintro ⟨hf, hL, he⟩
    exact ⟨hf, hL, by rwa [← generator_eq_langevinDifferentialOperator V hf]⟩
  · rintro ⟨hf, hL, he⟩
    exact ⟨hf, hL, by rwa [generator_eq_langevinDifferentialOperator V hf]⟩

/-! ### Brownian motion -/

theorem isStdBrownian_iff {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → CutCur.Rd d}
    {P : Measure Ω} : CutCur.IsStdBrownian B P ↔ IsEuclideanBrownian B P :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-! ### Distances -/

section Distances

variable {E : Type*} [MetricSpace E] [MeasurableSpace E]

/-- The squared coupling distance is the library squared transport cost. -/
theorem wasserstein2_sq (μ ν : Measure E) :
    CutCur.wasserstein2 μ ν ^ 2 = squaredWasserstein μ ν := by
  rw [CutCur.wasserstein2, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num
  rw [iInf_subtype']
  rfl

theorem wasserstein2_eq_rpow (μ ν : Measure E) :
    CutCur.wasserstein2 μ ν = squaredWasserstein μ ν ^ (1 / 2 : ℝ) := by
  rw [← wasserstein2_sq, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

end Distances

theorem tvDist_eq_totalVariationDistance {α : Type*} [MeasurableSpace α] (μ ν : Measure α) :
    CutCur.tvDist μ ν = totalVariationDistance μ ν := by
  rw [CutCur.tvDist, totalVariationDistance, iSup]
  congr 1
  ext r
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨A.1, A.2, rfl⟩
  · rintro ⟨A, hA, rfl⟩
    exact ⟨⟨A, hA⟩, rfl⟩

theorem relLp_eq_relativeLpDistance {α : Type*} [MeasurableSpace α] (ν μ : Measure α)
    (p : ℝ≥0∞) : CutCur.relLp ν μ p = relativeLpDistance ν μ p :=
  rfl

/-! ### Strong solutions of the Langevin equation -/

section Solutions

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Pathwise uniqueness: for a convex `C²` potential, every strong solution agrees
almost surely with the library's Brownian-driven Langevin process at each time. -/
theorem IsLangevinSolution.ae_eq_langevinProcess
    {B : ℝ≥0 → Ω → CutCur.Rd d} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : CutCur.Rd d → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : CutCur.Rd d, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {x₀ : CutCur.Rd d} {X : ℝ≥0 → Ω → CutCur.Rd d} (hX : CutCur.IsLangevinSolution V B P x₀ X)
    (t : ℝ≥0) : X t =ᵐ[P] langevinProcess V B x₀ t := by
  filter_upwards [hX, brownianDrivingPath_continuous_ae hB,
    brownianDrivingPath_initial_zero_ae hB] with ω hω hw hw0
  obtain ⟨hcont, heq⟩ := hω
  have hpath : ∀ T ≥ (0 : ℝ), IsLangevinPathOn V (brownianDrivingPath B ω) x₀
      (fun s : ℝ => X s.toNNReal ω) T := by
    intro T _
    refine ⟨(hcont.comp continuous_real_toNNReal).continuousOn, ?_⟩
    intro s hs
    rw [hw0, sub_zero]
    change X s.toNNReal ω = x₀ + Real.sqrt 2 • B s.toNNReal ω - _
    rw [heq s.toNNReal, Real.coe_toNNReal s hs.1]
    abel
  have h := langevinSolution_eqOn_of_global_solution hV rate hrate hHess hw hpath
    (show (0 : ℝ) ≤ t from t.property)
  change X t ω = langevinSolution V (brownianDrivingPath B ω) x₀ t
  rw [h]
  simp

/-- The law of a strong solution at time `t` is the library Langevin kernel. -/
theorem IsLangevinSolution.map_eq_langevinKernel
    {B : ℝ≥0 → Ω → CutCur.Rd d} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : CutCur.Rd d → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : CutCur.Rd d, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {x₀ : CutCur.Rd d} {X : ℝ≥0 → Ω → CutCur.Rd d} (hX : CutCur.IsLangevinSolution V B P x₀ X)
    (t : ℝ≥0) : P.map (X t) = langevinKernel V B P t x₀ := by
  rw [langevinKernel_apply_eq_process_law hB hV rate hrate hHess,
    Measure.map_congr (IsLangevinSolution.ae_eq_langevinProcess hB hV rate hrate hHess hX t)]

/-- The library process is a strong solution (existence). -/
theorem isLangevinSolution_langevinProcess
    {B : ℝ≥0 → Ω → CutCur.Rd d} {P : Measure Ω} (hB : IsEuclideanBrownian B P)
    {V : CutCur.Rd d → ℝ} (hV : ContDiff ℝ 2 V) (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : CutCur.Rd d, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : CutCur.Rd d) : CutCur.IsLangevinSolution V B P x₀ (langevinProcess V B x₀) := by
  filter_upwards [langevinProcess_continuous_paths_ae hB hV rate hrate hHess x₀,
    langevinProcess_integral_equation_ae hB hV rate hrate hHess x₀] with ω h1 h2
  refine ⟨h1, fun t => ?_⟩
  rw [h2 t]
  abel

/-- Non-vacuity of the standing assumptions: for a convex `C²` potential with a
probability Gibbs measure and a standard Brownian motion, the library process
solves the Langevin equation from every initial condition. -/
theorem isLangevin_langevinProcess
    {B : ℝ≥0 → Ω → CutCur.Rd d} {P : Measure Ω} (hB : CutCur.IsStdBrownian B P)
    {V : CutCur.Rd d → ℝ} (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (CutCur.gibbs V))
    (hconv : ∀ x z : CutCur.Rd d, 0 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    CutCur.IsLangevin V B P (fun x₀ => langevinProcess V B x₀) :=
  ⟨hV, hp, hB, fun x₀ => isLangevinSolution_langevinProcess (isStdBrownian_iff.mp hB) hV 0 le_rfl
    (fun x z => by simpa using hconv x z) x₀⟩

/-- Under the standing assumptions and a convexity bound, the laws of the solution are
the library Langevin kernel. -/
theorem IsLangevin.map_eq_langevinKernel
    {V : CutCur.Rd d → ℝ} {B : ℝ≥0 → Ω → CutCur.Rd d} {P : Measure Ω}
    {X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d} (hL : CutCur.IsLangevin V B P X)
    (rate : ℝ) (hrate : 0 ≤ rate)
    (hHess : ∀ x z : CutCur.Rd d, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x₀ : CutCur.Rd d) (t : ℝ≥0) : P.map (X x₀ t) = langevinKernel V B P t x₀ :=
  IsLangevinSolution.map_eq_langevinKernel (isStdBrownian_iff.mp hL.2.2.1) hL.1 rate hrate hHess
    (hL.2.2.2 x₀) t

end Solutions

end CutoffRigidity.Paper
