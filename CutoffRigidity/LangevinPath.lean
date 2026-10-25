module

public import CutoffRigidity.CurvatureMonotonicity
public import CutoffRigidity.SynchronousContraction
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Langevin paths driven by the same additive noise

The definition below is the actual integral equation for additive-noise
Langevin dynamics on a finite time interval. Brownian construction and
measurable dependence of the solution on its driving path are not asserted.
The deterministic cancellation of the common noise and the resulting
curvature contraction are proved from that equation.
-/

public section

open Set MeasureTheory
open scoped Topology

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Actual integral equation, with the noise increment measured from time zero. -/
@[expose] def IsLangevinPathOn (V : E → ℝ) (w : ℝ → E) (x₀ : E)
    (X : ℝ → E) (T : ℝ) : Prop :=
  ContinuousOn X (Icc 0 T) ∧ ∀ t ∈ Icc 0 T,
    X t = x₀ + (w t - w 0) - ∫ s in 0..t, gradient V (X s)

theorem IsLangevinPathOn.initial {V : E → ℝ} {w X : ℝ → E} {x₀ : E} {T : ℝ}
    (hX : IsLangevinPathOn V w x₀ X T) (hT : 0 ≤ T) : X 0 = x₀ := by
  simpa using hX.2 0 ⟨le_rfl, hT⟩

theorem IsLangevinPathOn.mono {V : E → ℝ} {w X : ℝ → E} {x₀ : E} {T t : ℝ}
    (hX : IsLangevinPathOn V w x₀ X T) (ht : t ≤ T) :
    IsLangevinPathOn V w x₀ X t := by
  have hsubset : Icc 0 t ⊆ Icc 0 T := fun _ hs => ⟨hs.1, hs.2.trans ht⟩
  exact ⟨hX.1.mono hsubset, fun s hs => hX.2 s (hsubset hs)⟩

theorem langevin_same_noise_difference {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    {w X Y : ℝ → E} {x₀ y₀ : E} {T t : ℝ}
    (hX : IsLangevinPathOn V w x₀ X T) (hY : IsLangevinPathOn V w y₀ Y T)
    (ht : t ∈ Icc 0 T) :
    X t - Y t = (x₀ - y₀) - ∫ s in 0..t, (gradient V (X s) - gradient V (Y s)) := by
  have hg := (differentiable_gradient_of_contDiff_two hV).continuous
  have hiX := (hg.comp_continuousOn hX.1).mono
    (show Icc 0 t ⊆ Icc 0 T from fun s hs => ⟨hs.1, hs.2.trans ht.2⟩)
  have hiY := (hg.comp_continuousOn hY.1).mono
    (show Icc 0 t ⊆ Icc 0 T from fun s hs => ⟨hs.1, hs.2.trans ht.2⟩)
  have hsub : (∫ s in 0..t, (gradient V (X s) - gradient V (Y s))) =
      (∫ s in 0..t, gradient V (X s)) - ∫ s in 0..t, gradient V (Y s) :=
    intervalIntegral.integral_sub
      (hiX.intervalIntegrable_of_Icc ht.1) (hiY.intervalIntegrable_of_Icc ht.1)
  rw [hsub, hX.2 t ht, hY.2 t ht]
  abel

theorem langevin_same_noise_difference_hasDerivAt {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    {w X Y : ℝ → E} {x₀ y₀ : E} {T t : ℝ}
    (hX : IsLangevinPathOn V w x₀ X T) (hY : IsLangevinPathOn V w y₀ Y T)
    (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun s => X s - Y s) (-gradient V (X t) + gradient V (Y t)) t := by
  have hg := (differentiable_gradient_of_contDiff_two hV).continuous
  have hc : ContinuousOn (fun s => gradient V (X s) - gradient V (Y s)) (Icc 0 T) :=
    (hg.comp_continuousOn hX.1).sub (hg.comp_continuousOn hY.1)
  have hct : ContinuousAt (fun s => gradient V (X s) - gradient V (Y s)) t :=
    hc.continuousAt (Icc_mem_nhds ht.1 ht.2)
  have hi : IntervalIntegrable (fun s => gradient V (X s) - gradient V (Y s)) volume 0 t := (hc.mono
    (show Icc 0 t ⊆ Icc 0 T from fun s hs => ⟨hs.1, hs.2.trans ht.2.le⟩)).intervalIntegrable_of_Icc ht.1.le
  have hm : StronglyMeasurableAtFilter
      (fun s => gradient V (X s) - gradient V (Y s)) (𝓝 t) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
      (hc.mono Ioo_subset_Icc_self) t ht
  have hd := (intervalIntegral.integral_hasDerivAt_right hi hm hct).const_sub (x₀ - y₀)
  have heq : (fun s => X s - Y s) =ᶠ[𝓝 t]
      (fun s => (x₀ - y₀) - ∫ u in 0..s, (gradient V (X u) - gradient V (Y u))) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact langevin_same_noise_difference hV hX hY hs
  convert hd.congr_of_eventuallyEq heq using 1
  abel

/-- Curvature contracts any two actual integral-equation solutions driven by
the same noise, without a differentiability assumption on the noise itself. -/
theorem langevin_same_noise_contraction {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (rate : ℝ) (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {w X Y : ℝ → E} {x₀ y₀ : E} {T : ℝ}
    (hX : IsLangevinPathOn V w x₀ X T) (hY : IsLangevinPathOn V w y₀ Y T)
    (hT : 0 ≤ T) :
    ‖X T - Y T‖ ≤ Real.exp (-rate * T) * ‖x₀ - y₀‖ := by
  have h := synchronous_difference_norm_contraction V X Y hT (hX.1.sub hY.1)
    (fun _ hs => langevin_same_noise_difference_hasDerivAt hV hX hY hs)
    (gradient_strongly_monotone_of_hessian_bound hV rate hHess)
  rwa [hX.initial hT, hY.initial hT] at h

/-- Pathwise uniqueness for the integral equation under the paper's curvature
bound; existence and measurable dependence are separate requirements. -/
theorem langevin_path_unique {V : E → ℝ} (hV : ContDiff ℝ 2 V)
    (rate : ℝ) (hHess : ∀ x z : E, rate * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    {w X Y : ℝ → E} {x₀ : E} {T : ℝ}
    (hX : IsLangevinPathOn V w x₀ X T) (hY : IsLangevinPathOn V w x₀ Y T) :
    EqOn X Y (Icc 0 T) := by
  intro t ht
  have h := langevin_same_noise_contraction hV rate hHess
    (hX.mono ht.2) (hY.mono ht.2) ht.1
  have hn : ‖X t - Y t‖ = 0 := le_antisymm (by simpa using h) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

end CutoffRigidity
