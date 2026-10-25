module

public import CutoffRigidity.SmoothFisherInformation
public import CutoffRigidity.Paper.CoreBridge

/-! # The score of the heat kernel (manuscript, Section 4.1)

`∇ log (dμ_t/dμ) = ∇ log p_t + ∇V`, for a positive differentiable density `p` with respect to Lebesgue
measure and `μ = e^{-V} dx`.
-/

public section

namespace CutoffRigidity.Paper

open MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- If `ν = p dx` with `p > 0` continuous and differentiable, then `ν ≪ μ = e^{-V}dx`, a differentiable version of
`log dν/dμ` is `log p + V` and its gradient is `∇ log p + ∇V`. -/
theorem heat_kernel_score {V p : CutCur.Rd d → ℝ} (hVc : Continuous V) (hVd : Differentiable ℝ V)
    (hpc : Continuous p) (hpd : Differentiable ℝ p) (hp : ∀ x, 0 < p x) :
    let ν : MeasureTheory.Measure (CutCur.Rd d) := volume.withDensity fun x => ENNReal.ofReal (p x)
    ∃ u : CutCur.Rd d → ℝ, Differentiable ℝ u ∧ ν ≪ CutCur.gibbs V ∧
      (∀ᵐ x ∂CutCur.gibbs V, u x = Real.log (ν.rnDeriv (CutCur.gibbs V) x).toReal) ∧
      ∀ x, gradient u x = gradient (fun y => Real.log (p y)) x + gradient V x := by
  intro ν
  have hlogp : Continuous fun y => Real.log (p y) := hpc.log (fun y => (hp y).ne')
  have hu : Continuous fun x => Real.log (p x) + V x := hlogp.add hVc
  have hm1 : Measurable fun x : CutCur.Rd d => ENNReal.ofReal (Real.exp (-V x)) :=
    hVc.neg.rexp.measurable.ennreal_ofReal
  have hm2 : Measurable fun x : CutCur.Rd d => ENNReal.ofReal (Real.exp (Real.log (p x) + V x)) :=
    hu.rexp.measurable.ennreal_ofReal
  have hν : ν = (CutCur.gibbs V).withDensity
      (fun x => ENNReal.ofReal (Real.exp (Real.log (p x) + V x))) := by
    show _ = (volume.withDensity fun x => ENNReal.ofReal (Real.exp (-V x))).withDensity _
    rw [← withDensity_mul _ hm1 hm2]
    change volume.withDensity (fun x => ENNReal.ofReal (p x)) = _
    congr 1
    funext x
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    congr 1
    rw [show -V x + (Real.log (p x) + V x) = Real.log (p x) by ring, Real.exp_log (hp x)]
  refine ⟨fun x => Real.log (p x) + V x,
    (hpd.log (fun y => (hp y).ne')).add hVd, ?_, ?_, ?_⟩
  · rw [hν]; exact withDensity_absolutelyContinuous _ _
  · have : SigmaFinite (CutCur.gibbs V) := by unfold CutCur.gibbs; infer_instance
    have hu' := llr_exponentialDensityMeasure (μ := CutCur.gibbs V)
      (u := fun x => Real.log (p x) + V x) hu.measurable
    filter_upwards [hu'] with x hx
    rw [hν]
    exact hx.symm
  · intro x
    have h1 : DifferentiableAt ℝ (fun y => Real.log (p y)) x := (hpd x).log (hp x).ne'
    have h2 : fderiv ℝ (fun y => Real.log (p y) + V y) x =
        fderiv ℝ (fun y => Real.log (p y)) x + fderiv ℝ V x := fderiv_add h1 (hVd x)
    apply ext_inner_right ℝ
    intro z
    rw [inner_gradient_left, h2, inner_add_left, inner_gradient_left, inner_gradient_left]
    rfl

end CutoffRigidity.Paper
