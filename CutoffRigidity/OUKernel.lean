module

public import CutoffRigidity.GaussianTransport
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# The normalized Ornstein--Uhlenbeck Mehler kernel

This constructs the actual Gaussian transition law used in the paper's
projected OU calculation. Identification with a projected Langevin SDE
remains a separate obligation.
-/

public section

namespace CutoffRigidity

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "E" => EuclideanSpace ℝ ι

/-- Mean decay in the normalized OU law. -/
noncomputable def ouDecay (rate time : ℝ) : ℝ := Real.exp (-rate * time)

/-- Standard deviation of its Gaussian noise. -/
noncomputable def ouNoise (rate time : ℝ) : ℝ :=
  Real.sqrt (1 - Real.exp (-2 * rate * time))

/-- The normalized Mehler law at a deterministic initial point. -/
@[expose] noncomputable def ouLaw (rate time : ℝ) (x : E) : Measure E :=
  affineGaussian (ouDecay rate time • x) (ouNoise rate time)

instance (rate time : ℝ) (x : E) : IsProbabilityMeasure (ouLaw rate time x) := by
  unfold ouLaw
  infer_instance

/-- The genuine measurable Markov kernel obtained by adding independent Gaussian noise. -/
noncomputable def ouKernel (rate time : ℝ) : Kernel E E :=
  ((Kernel.id : Kernel E E).prod (Kernel.const E (stdGaussian E))).map
    (fun z => ouDecay rate time • z.1 + ouNoise rate time • z.2)

omit [DecidableEq ι] in
/-- Evaluation of the kernel is the Mehler Gaussian law. -/
theorem ouKernel_apply (rate time : ℝ) (x : E) :
    ouKernel rate time x = ouLaw rate time x := by
  rw [ouKernel, Kernel.map_apply _ (by fun_prop), Kernel.prod_apply,
    Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (by fun_prop) measurable_prodMk_left]
  rfl

instance (rate time : ℝ) : IsMarkovKernel (ouKernel (ι := ι) rate time) := by
  constructor
  intro x
  rw [ouKernel_apply]
  infer_instance

omit [DecidableEq ι] in
@[simp] theorem ouLaw_zero (rate : ℝ) (x : E) :
    ouLaw rate 0 x = Measure.dirac x := by
  simp [ouLaw, ouDecay, ouNoise, affineGaussian]

theorem ouNoise_nonneg (rate time : ℝ) : 0 ≤ ouNoise rate time :=
  Real.sqrt_nonneg _

omit [DecidableEq ι] in
/-- The time-zero transition kernel is the identity kernel. -/
@[simp] theorem ouKernel_zero (rate : ℝ) : ouKernel (ι := ι) rate 0 = Kernel.id := by
  apply Kernel.ext
  intro x
  rw [ouKernel_apply, ouLaw_zero, Kernel.id_apply]

/-- The covariance parameter of the normalized Mehler law is nonnegative. -/
theorem ouNoise_sq {rate time : ℝ} (hr : 0 ≤ rate) (ht : 0 ≤ time) :
    ouNoise rate time ^ 2 = 1 - Real.exp (-2 * rate * time) := by
  apply Real.sq_sqrt
  have he : Real.exp (-2 * rate * time) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  linarith

/-- The normalized Mehler law stated using Mathlib's actual multivariate Gaussian. -/
theorem ouLaw_eq_multivariateGaussian {rate time : ℝ} (hr : 0 ≤ rate) (ht : 0 ≤ time)
    (x : E) :
    ouLaw rate time x = multivariateGaussian (Real.exp (-rate * time) • x)
      ((1 - Real.exp (-2 * rate * time)) • (1 : Matrix ι ι ℝ)) := by
  rw [ouLaw, affineGaussian_eq_multivariateGaussian _ _ (ouNoise_nonneg rate time), ouNoise_sq hr ht]
  rfl

/-- The law's mean is the exponentially decayed initial point. -/
theorem integral_id_ouLaw (rate time : ℝ) (x : E) :
    ∫ y, y ∂ouLaw rate time x = Real.exp (-rate * time) • x := by
  rw [ouLaw, integral_id_affineGaussian _ _ (ouNoise_nonneg rate time)]
  rfl

/-- Every coordinate has the variance given by Mehler's formula. -/
theorem variance_eval_ouLaw {rate time : ℝ} (hr : 0 ≤ rate) (ht : 0 ≤ time)
    (x : E) (i : ι) :
    variance (fun y => y i) (ouLaw rate time x) = 1 - Real.exp (-2 * rate * time) := by
  rw [ouLaw, variance_eval_affineGaussian _ _ (ouNoise_nonneg rate time), ouNoise_sq hr ht]

/-- Exact equilibrium transport profile of the actual Mehler probability law. -/
theorem squaredWasserstein_ouLaw (rate time : ℝ)
    (x : E) :
    squaredWasserstein (ouLaw rate time x) (stdGaussian E) =
      ENNReal.ofReal (Real.exp (-2 * rate * time) * ‖x‖ ^ 2 +
        Fintype.card ι * (1 - Real.sqrt (1 - Real.exp (-2 * rate * time))) ^ 2) := by
  rw [ouLaw, squaredWasserstein_affineGaussian _ _ (ouNoise_nonneg rate time)]
  congr 1
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hexp : ouDecay rate time ^ 2 = Real.exp (-2 * rate * time) := by
    unfold ouDecay
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp]
  unfold ouNoise
  ring

omit [DecidableEq ι] in
/-- Characteristic function of an affine Gaussian, with arbitrary real scale. -/
theorem charFun_affineGaussian (m : E) (s : ℝ) (u : E) :
    charFun (affineGaussian m s) u =
      Complex.exp ((inner ℝ m u : ℂ) * Complex.I - (s : ℂ) ^ 2 * (‖u‖ : ℂ) ^ 2 / 2) := by
  have heq : affineGaussian m s = ((stdGaussian E).map (s • ·)).map (m + ·) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [heq, charFun_map_const_add, charFun_map_smul, charFun_stdGaussian, ← Complex.exp_add]
  congr 1
  rw [norm_smul, Real.norm_eq_abs]
  push_cast
  have habs : ((|s| : ℝ) : ℂ) ^ 2 = (s : ℂ) ^ 2 := by exact_mod_cast sq_abs s
  rw [mul_pow, habs]
  ring

omit [DecidableEq ι] in
/-- Independent affine Gaussian noises add their means and variances. -/
theorem affineGaussian_conv (m n : E) (s t : ℝ) :
    affineGaussian m s ∗ affineGaussian n t =
      affineGaussian (m + n) (Real.sqrt (s ^ 2 + t ^ 2)) := by
  apply Measure.ext_of_charFun
  funext u
  rw [charFun_conv, charFun_affineGaussian, charFun_affineGaussian,
    charFun_affineGaussian, ← Complex.exp_add]
  congr 1
  have hsq : ((Real.sqrt (s ^ 2 + t ^ 2) : ℝ) : ℂ) ^ 2 = (s : ℂ) ^ 2 + (t : ℂ) ^ 2 := by
    norm_cast
    exact Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  rw [hsq, inner_add_left]
  push_cast
  ring

omit [DecidableEq ι] in
/-- Scaling an affine Gaussian scales both its mean and its standard noise. -/
theorem affineGaussian_map_smul (m : E) (s a : ℝ) :
    (affineGaussian m s).map (a • ·) = affineGaussian (a • m) (a * s) := by
  rw [affineGaussian, Measure.map_map (by fun_prop) (by fun_prop), affineGaussian]
  congr 1
  ext x
  simp [smul_add, smul_smul]

/-- Decay factors multiply when times add. -/
theorem ouDecay_add (rate time step : ℝ) :
    ouDecay rate (time + step) = ouDecay rate step * ouDecay rate time := by
  unfold ouDecay
  rw [← Real.exp_add]
  congr 1
  ring

/-- The square of the mean-decay factor is the variance-decay factor. -/
theorem ouDecay_sq (rate time : ℝ) :
    ouDecay rate time ^ 2 = Real.exp (-2 * rate * time) := by
  unfold ouDecay
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- Independent noise accumulated over two intervals has the Mehler variance
for their combined duration. -/
theorem ouNoise_add_variance {rate time step : ℝ}
    (hr : 0 ≤ rate) (ht : 0 ≤ time) (hu : 0 ≤ step) :
    (ouDecay rate step * ouNoise rate time) ^ 2 + ouNoise rate step ^ 2 =
      1 - Real.exp (-2 * rate * (time + step)) := by
  rw [mul_pow, ouNoise_sq hr ht, ouNoise_sq hr hu, ouDecay_sq]
  have hexp : Real.exp (-2 * rate * (time + step)) =
      Real.exp (-2 * rate * step) * Real.exp (-2 * rate * time) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

omit [DecidableEq ι] in
/-- The independent-noise composition law for the actual Mehler measures.
Convolution expresses adding the fresh Gaussian noise independently. -/
theorem ouLaw_compose {rate time step : ℝ}
    (hr : 0 ≤ rate) (ht : 0 ≤ time) (hu : 0 ≤ step) (x : E) :
    ((ouLaw rate time x).map (ouDecay rate step • ·)) ∗
        affineGaussian (0 : E) (ouNoise rate step) = ouLaw rate (time + step) x := by
  rw [ouLaw, affineGaussian_map_smul, affineGaussian_conv, ouLaw]
  congr 1
  · rw [add_zero, smul_smul, ← ouDecay_add]
  · rw [ouNoise_add_variance hr ht hu]
    rfl

omit [DecidableEq ι] in
/-- The standard Gaussian is invariant under one Mehler update with independent noise. -/
theorem ouLaw_invariant {rate time : ℝ} (hr : 0 ≤ rate) (ht : 0 ≤ time) :
    ((stdGaussian E).map (ouDecay rate time • ·)) ∗
        affineGaussian (0 : E) (ouNoise rate time) = stdGaussian E := by
  conv_lhs => rw [← affineGaussian_zero_one]
  rw [affineGaussian_map_smul, smul_zero, mul_one, affineGaussian_conv, zero_add]
  have hvar : ouDecay rate time ^ 2 + ouNoise rate time ^ 2 = 1 := by
    rw [ouDecay_sq, ouNoise_sq hr ht]
    ring
  rw [hvar, Real.sqrt_one, affineGaussian_zero_one]

omit [DecidableEq ι] in
/-- Applying the Mehler kernel to an arbitrary input law is convolution of the
decayed input with the independent Gaussian noise. -/
theorem ouKernel_comp_measure (rate time : ℝ) (μ : Measure E) [SFinite μ] :
    ouKernel rate time ∘ₘ μ =
      (μ.map (ouDecay rate time • ·)) ∗ affineGaussian (0 : E) (ouNoise rate time) := by
  have hmap : Measurable (fun z : E × E =>
      ouDecay rate time • z.1 + ouNoise rate time • z.2) := by fun_prop
  rw [ouKernel, ← Measure.map_comp _ _ hmap,
    ← Measure.compProd_eq_comp_prod, Measure.compProd_const]
  rw [affineGaussian, Measure.conv, Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  ext z
  simp

omit [DecidableEq ι] in
/-- The actual Mehler kernels satisfy the semigroup composition identity. -/
theorem ouKernel_comp {rate time step : ℝ}
    (hr : 0 ≤ rate) (ht : 0 ≤ time) (hu : 0 ≤ step) :
    ouKernel (ι := ι) rate step ∘ₖ ouKernel rate time = ouKernel rate (time + step) := by
  apply Kernel.ext
  intro x
  change ouKernel rate step ∘ₘ (ouKernel rate time x) = ouKernel rate (time + step) x
  rw [ouKernel_comp_measure, ouKernel_apply, ouKernel_apply]
  exact ouLaw_compose hr ht hu x

omit [DecidableEq ι] in
/-- The standard Gaussian is an invariant probability measure of the actual kernel. -/
theorem ouKernel_invariant {rate time : ℝ} (hr : 0 ≤ rate) (ht : 0 ≤ time) :
    ouKernel rate time ∘ₘ stdGaussian E = stdGaussian E := by
  rw [ouKernel_comp_measure]
  exact ouLaw_invariant hr ht

end CutoffRigidity
