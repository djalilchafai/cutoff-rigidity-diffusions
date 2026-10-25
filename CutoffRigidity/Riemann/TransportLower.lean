module

public import CutoffRigidity.Riemann.TransportGauss

/-! # Transport, step 4: the lower bound through the isometric splitting

Generic form (no manifold structure): `Φ : M → ℝ^k × N` satisfies the distance identity of the
Challenge's splitting and `μ.map Φ = γ ⊗ μ'`; `Pt` is a Markov kernel whose Euclidean projection
has the exact Mehler law (hypothesis `MehlerLaw`, to be discharged from the diffusion hypothesis,
see `riemann-status/transport.md`).  Then the projection `√ρ·p` is `√ρ`-Lipschitz and pushes the
equilibrium to the standard Gaussian, which gives the pointwise lower bound
`ρ e^{-2ρt}|p x₀|² + k(1-√(1-e^{-2ρt}))² ≤ ρ W₂²(P_t x₀, μ)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace CutoffRigidity.Riemann

/-- The abstract output of the splitting theorem used by the transport argument. -/
structure SplitData (M N : Type*) [PseudoEMetricSpace M] [MeasurableSpace M]
    [PseudoEMetricSpace N] [MeasurableSpace N] (k : ℕ) (ρ : ℝ) (μ : Measure M) where
  Φ : M → EuclideanSpace ℝ (Fin k) × N
  μ' : Measure N
  prob' : IsProbabilityMeasure μ'
  aemeasurable : AEMeasurable Φ μ
  surj : Function.Surjective Φ
  dist_sq : ∀ x y, edist x y ^ 2 = edist (Φ x).1 (Φ y).1 ^ 2 + edist (Φ x).2 (Φ y).2 ^ 2
  map_eq : μ.map Φ = (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
    (ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ))).prod μ'

variable {M N : Type*} [PseudoEMetricSpace M] [MeasurableSpace M] [OpensMeasurableSpace M]
  [PseudoEMetricSpace N] [MeasurableSpace N] {k : ℕ} {ρ : ℝ} {μ : Measure M}

namespace SplitData

variable (D : SplitData M N k ρ μ)

/-- The Euclidean coordinate. -/
def proj (x : M) : EuclideanSpace ℝ (Fin k) := (D.Φ x).1

omit [OpensMeasurableSpace M] in
theorem edist_proj_le (x y : M) : edist (D.proj x) (D.proj y) ≤ edist x y := by
  have h := D.dist_sq x y
  have h2 : edist (D.proj x) (D.proj y) ^ 2 ≤ edist x y ^ 2 := by
    rw [h]; exact le_self_add
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 h2

omit [OpensMeasurableSpace M] in
theorem lipschitz_proj : LipschitzWith 1 D.proj :=
  LipschitzWith.of_edist_le fun x y => by simpa using D.edist_proj_le x y

theorem measurable_proj : Measurable D.proj := D.lipschitz_proj.continuous.measurable

omit [OpensMeasurableSpace M] in
/-- The projection of `μ` is the Gaussian `N(0, ρ⁻¹ I)`. -/
theorem map_proj_eq :
    μ.map D.proj = multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
      (ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ)) := by
  have := D.prob'
  have h : D.proj = Prod.fst ∘ D.Φ := rfl
  rw [h, ← AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable D.aemeasurable,
    D.map_eq]
  simp

/-- The Mehler (Ornstein–Uhlenbeck) law of the Euclidean coordinate at time `t` from `x₀`. -/
noncomputable def mehler (ρ t : ℝ) (z : EuclideanSpace ℝ (Fin k)) : Measure (EuclideanSpace ℝ (Fin k)) :=
  multivariateGaussian (Real.exp (-ρ * t) • z)
    ((ρ⁻¹ * (1 - Real.exp (-2 * ρ * t))) • (1 : Matrix (Fin k) (Fin k) ℝ))

/-- **Lower bound for one law**: if the Euclidean coordinate of `ν` is the Mehler law from `x₀`
then `ρ e^{-2ρt}|p x₀|² + k (1-√(1-e^{-2ρt}))² ≤ ρ W₂²(ν, μ)`. -/
theorem lower_of_mehler (hρ : 0 < ρ) {t : ℝ} (ht : 0 ≤ t) (x₀ : M) (ν : Measure M)
    (hν : ν.map D.proj = mehler ρ t (D.proj x₀)) :
    ENNReal.ofReal (ρ * (Real.exp (-2 * ρ * t) * ‖D.proj x₀‖ ^ 2) +
        k * (1 - Real.sqrt (1 - Real.exp (-2 * ρ * t))) ^ 2) ≤
      ENNReal.ofReal ρ * CutCur.wasserstein2 ν μ ^ 2 := by
  have hT : Measurable (fun x : M => Real.sqrt ρ • D.proj x) :=
    (measurable_const_smul _).comp D.measurable_proj
  have hsm : Measurable (fun z : EuclideanSpace ℝ (Fin k) => Real.sqrt ρ • z) :=
    measurable_const_smul _
  obtain ⟨K, hK⟩ : ∃ K : ℝ≥0, (K : ℝ) = Real.sqrt ρ := ⟨⟨_, Real.sqrt_nonneg ρ⟩, rfl⟩
  have hK0 : K ≠ 0 := by
    intro h
    rw [h] at hK
    simp at hK
    exact absurd hK.symm (Real.sqrt_pos.2 hρ).ne'
  have hKe : ‖Real.sqrt ρ‖₊ = K := NNReal.eq (by
    rw [coe_nnnorm, ← hK, NNReal.norm_eq])
  have hc := cost2_map_le ν μ hT (L := K) hK0
    (by
      intro x y
      have h1 := D.edist_proj_le x y
      rw [edist_smul₀, hKe, ENNReal.smul_def, smul_eq_mul]
      gcongr)
  have hfac : (K : ℝ≥0∞) ^ 2 = ENNReal.ofReal ρ := by
    rw [← ENNReal.coe_pow, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_pow, hK, Real.sq_sqrt hρ.le]
  rw [hfac, ← wasserstein2_sq_eq_cost2 ν μ] at hc
  have e1 : ν.map (fun x : M => Real.sqrt ρ • D.proj x) =
      (mehler ρ t (D.proj x₀)).map (fun z => Real.sqrt ρ • z) := by
    rw [← hν, Measure.map_map hsm D.measurable_proj]; rfl
  have e2 : μ.map (fun x : M => Real.sqrt ρ • D.proj x) =
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
        (ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ))).map (fun z => Real.sqrt ρ • z) := by
    rw [← D.map_proj_eq, Measure.map_map hsm D.measurable_proj]; rfl
  rw [e1, e2, mehler, cost2_mehler_rescaled hρ ht] at hc
  exact hc

end SplitData

end CutoffRigidity.Riemann
