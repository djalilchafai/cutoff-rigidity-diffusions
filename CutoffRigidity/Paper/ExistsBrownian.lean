module

public import CutoffRigidity.Statements
public import CutoffRigidity.LangevinBrownian
import BrownianMotion.Gaussian.BrownianMotion

/-! # Existence of a standard Brownian motion and non-vacuity of `IsLangevin`

`exists_stdBrownian` builds, on a probability space, a standard Brownian motion on `ℝ^d`
(independent real Brownian coordinates, in the sense of Mathlib's `IsBrownianReal`, including
almost-sure path continuity). The real Brownian motion comes from the vendored library of
R. Degenne, S. Ledvinka, E. Marion and P. Pfaffelhuber (see `vendor/README.md`), through
`isBrownianReal_brownian`; the library is imported privately, so none of its declarations is visible
downstream. `exists_langevin` shows that the standing hypothesis `IsLangevin` of the Challenge is
satisfiable for every `C²` potential with nonnegative Hessian and probability Gibbs measure.
-/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

private lemma isBrownianReal_comp_measurePreserving {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {X : ℝ≥0 → Ω' → ℝ} {Q : Measure Ω'} {P : Measure Ω} {f : Ω → Ω'}
    (hf : MeasurePreserving f P Q) (hX : IsBrownianReal X Q) :
    IsBrownianReal (fun t w => X t (f w)) P where
  hasLaw I := (hX.hasLaw I).comp hf.hasLaw
  cont := hf.quasiMeasurePreserving.ae hX.cont

/-- A standard Brownian motion on `ℝ^d` exists on some probability space. -/
theorem exists_stdBrownian (d : ℕ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (B : ℝ≥0 → Ω → CutCur.Rd d),
      IsProbabilityMeasure P ∧ CutCur.IsStdBrownian B P := by
  refine ⟨Fin d → (ℝ≥0 → ℝ), inferInstance, Measure.pi fun _ => gaussianLimit,
    fun t w => WithLp.toLp 2 (fun i => brownian t (w i)), inferInstance, ?_, ?_⟩
  · intro i
    exact isBrownianReal_comp_measurePreserving
      (f := fun w : Fin d → (ℝ≥0 → ℝ) => w i)
      (measurePreserving_eval _ i) isBrownianReal_brownian
  · exact iIndepFun_pi (μ := fun _ : Fin d => gaussianLimit)
      (X := fun _ => fun ω : ℝ≥0 → ℝ => fun t : ℝ≥0 => brownian t ω)
      (fun _ => (Measurable.of_eval fun t => measurable_brownian t).aemeasurable)

/-- The standing hypothesis `IsLangevin` is satisfiable: for a `C²` potential with nonnegative
Hessian (equivalently convex) and probability Gibbs measure, there are a probability space, a
standard Brownian motion `B` and a family `X` of solutions of the Langevin SDE from every starting
point. -/
theorem exists_langevin (d : ℕ) (V : CutCur.Rd d → ℝ) (hV : ContDiff ℝ 2 V)
    (hHess : ∀ x z : CutCur.Rd d, 0 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hgibbs : IsProbabilityMeasure (CutCur.gibbs V)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (B : ℝ≥0 → Ω → CutCur.Rd d) (P : Measure Ω)
      (X : CutCur.Rd d → ℝ≥0 → Ω → CutCur.Rd d),
      IsProbabilityMeasure P ∧ CutCur.IsLangevin V B P X := by
  obtain ⟨Ω, hΩ, P, B, hP, hB⟩ := exists_stdBrownian d
  have hB' : IsEuclideanBrownian B P := ⟨hB.1, hB.2⟩
  have hH : ∀ x z : CutCur.Rd d, (0 : ℝ) * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z := by
    intro x z; simpa using hHess x z
  refine ⟨Ω, hΩ, B, P, fun x₀ => langevinProcess V B x₀, hP, hV, hgibbs, hB, fun x₀ => ?_⟩
  filter_upwards [langevinProcess_continuous_paths_ae hB' hV 0 le_rfl hH x₀,
    langevinProcess_integral_equation_ae hB' hV 0 le_rfl hH x₀] with w hc he
  refine ⟨hc, fun t => ?_⟩
  rw [he t]
  abel

end CutoffRigidity.Paper
