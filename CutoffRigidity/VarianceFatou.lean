module
public import CutoffRigidity.PoincareIntegrableDomain

/-! # Genuine variance bounds pass through centered Fatou limits

Both the second-moment domain and the variance bound are derived. Only
actual convergence of the means and almost-everywhere values is used.
-/
public section
namespace CutoffRigidity
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
variable {X : Type*} [MeasurableSpace X]

theorem memLp_two_and_variance_le_of_ae_tendsto
    (ν : Measure X) [IsProbabilityMeasure ν]
    {fn : ℕ → X → ℝ} {f : X → ℝ} {A : ℝ}
    (hfn : ∀ n, MemLp (fn n) 2 ν) (hf : AEStronglyMeasurable f ν)
    (hmean : Tendsto (fun n => ∫ x, fn n x ∂ν) atTop (𝓝 (∫ x, f x ∂ν)))
    (hlim : ∀ᵐ x ∂ν, Tendsto (fun n => fn n x) atTop (𝓝 (f x)))
    (hbound : ∀ n, variance (fn n) ν ≤ A) :
    MemLp f 2 ν ∧ variance f ν ≤ A := by
  let centered := fun n : ℕ => fun x : X => fn n x-∫ y, fn n y ∂ν
  have hcenter (n : ℕ) : MemLp (centered n) 2 ν := (hfn n).sub (memLp_const _)
  have hcenterBound (n : ℕ) : (∫ x, ‖centered n x‖^2 ∂ν) ≤ A := by
    have hh := hbound n
    rw [variance_eq_integral (hfn n).aemeasurable] at hh
    simpa only [centered,Real.norm_eq_abs,sq_abs] using hh
  obtain ⟨hmem,hbound⟩ := memLp_two_and_second_moment_le_of_ae_tendsto hcenter
    (hf.sub aestronglyMeasurable_const)
    (by filter_upwards [hlim] with x hx; exact hx.sub hmean) hcenterBound
  have hfLp : MemLp f 2 ν := by
    have hh := hmem.add (memLp_const (∫ y, f y ∂ν))
    simpa only [Pi.add_apply,sub_add_cancel] using hh
  refine ⟨hfLp,?_⟩
  rw [variance_eq_integral hf.aemeasurable]
  simpa only [Pi.sub_apply,Real.norm_eq_abs,sq_abs] using hbound

end CutoffRigidity
