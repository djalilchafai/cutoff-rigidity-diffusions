module

public import CutoffRigidity.Riemann.TransportW2

/-! # Transport, step 2: the upper bound from invariance and `W₂`-contraction

Abstract kernel lemma: if `μ` is invariant for a Markov kernel `P` and `P` contracts `W₂²` by a
factor `q`, then `W₂²(P x₀, μ) ≤ q ∫ d(x₀,·)² dμ`, and the same for suprema over a set.  The
two hypotheses (`hinv`, `hcontr`) are exactly the two analytic inputs that the Challenge's
`IsDiffusionSemigroup` does not give for free (see `riemann-status/transport.md`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace CutoffRigidity.Riemann

variable {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]

/-- `W₂²`-contraction of a kernel by the factor `q` on probability measures. -/
def W2Contraction (P : Kernel M M) (q : ℝ≥0∞) : Prop :=
  ∀ ν ν' : Measure M, IsProbabilityMeasure ν → IsProbabilityMeasure ν' →
    cost2 (ν.bind P) (ν'.bind P) ≤ q * cost2 ν ν'

theorem upper_pointwise (μ : Measure M) [IsProbabilityMeasure μ] (P : Kernel M M)
    [IsMarkovKernel P] {q : ℝ≥0∞} (hinv : μ.bind P = μ) (hc : W2Contraction P q) (x₀ : M) :
    CutCur.wasserstein2 (P x₀) μ ^ 2 ≤ q * ∫⁻ y, edist x₀ y ^ 2 ∂μ := by
  rw [wasserstein2_sq_eq_cost2]
  have h := hc (Measure.dirac x₀) μ inferInstance inferInstance
  rw [Measure.dirac_bind P.measurable, hinv] at h
  exact h.trans (mul_le_mul_right (cost2_dirac_left_le x₀ μ) q)

theorem upper_iSup (μ : Measure M) [IsProbabilityMeasure μ] (P : Kernel M M)
    [IsMarkovKernel P] {q : ℝ≥0∞} (hinv : μ.bind P = μ) (hc : W2Contraction P q) (S : Set M) :
    ⨆ x₀ ∈ S, CutCur.wasserstein2 (P x₀) μ ^ 2 ≤ q * ⨆ x₀ ∈ S, ∫⁻ y, edist x₀ y ^ 2 ∂μ := by
  refine iSup₂_le fun x₀ hx₀ => ?_
  refine (upper_pointwise μ P hinv hc x₀).trans ?_
  gcongr
  exact le_iSup₂ (f := fun x₀ (_ : x₀ ∈ S) => ∫⁻ y, edist x₀ y ^ 2 ∂μ) x₀ hx₀

end CutoffRigidity.Riemann
