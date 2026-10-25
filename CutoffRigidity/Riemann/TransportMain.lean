module

public import CutoffRigidity.Riemann.TransportAlgebra
public import CutoffRigidity.Riemann.TransportUpper

/-! # Transport, step 6: the two-sided `W₂` estimate from the splitting and three analytic inputs

`riemannian_wasserstein_estimate_of_transport` is the conclusion of the Challenge's
`riemannian_wasserstein_estimate`, proved from

* the splitting data (`SplitData`, `EigenSplitting`),
* the three analytic properties of the diffusion semigroup `TransportInputs`
  (invariance of `μ`, Mehler law of the Euclidean coordinate, `W₂²`-contraction),

which are NOT consequences of the bare `IsDiffusionSemigroup` hypothesis without a uniqueness
theorem (see `riemann-status/transport.md`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Bundle
open scoped ENNReal NNReal Manifold ContDiff RealInnerProductSpace

namespace CutoffRigidity.Riemann

open CutCur

section

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M]

/-- The consequences of the splitting for first eigenfunctions (Lemma `lem_rig`) together with the
existence of an orthonormal eigenbasis and `k₁ ≥ 1` (attainment of the spectral gap). -/
structure EigenSplitting {N : Type*} [PseudoEMetricSpace N] [MeasurableSpace N]
    (μ : Measure M) (V : M → ℝ) (ρ : ℝ) (D : SplitData M N (mFirstEigenDim F μ V) ρ μ) : Prop where
  rep : ∀ f, IsMEigenfunction F μ V ρ f → ∃ a : EuclideanSpace ℝ (Fin (mFirstEigenDim F μ V)),
    (∀ x, f x = inner ℝ a (D.proj x)) ∧ ‖a‖ ^ 2 = ρ * ∫ x, f x ^ 2 ∂μ
  orth : ∀ f g (a b : EuclideanSpace ℝ (Fin (mFirstEigenDim F μ V))),
    IsMEigenfunction F μ V ρ f → IsMEigenfunction F μ V ρ g →
    (∀ x, f x = inner ℝ a (D.proj x)) → (∀ x, g x = inner ℝ b (D.proj x)) →
    ∫ x, f x * g x ∂μ = 0 → inner ℝ a b = 0
  basis : ∃ T : Fin (mFirstEigenDim F μ V) → M → ℝ, (∀ i, IsMEigenfunction F μ V ρ (T i)) ∧
    ∀ i j, ∫ y, T i y * T j y ∂μ = if i = j then 1 else 0
  pos : 0 < mFirstEigenDim F μ V

variable {N : Type*} [PseudoEMetricSpace N] [MeasurableSpace N] [OpensMeasurableSpace M]
  {V : M → ℝ} {μ : Measure M} {ρ : ℝ}

/-- `Λ ≤ ρ |p|²` and, with an eigenbasis, equality. -/
theorem mLambda_eq_of_splitting (hρ : 0 < ρ) (hgap : mSpectralGap F μ = ρ)
    (D : SplitData M N (mFirstEigenDim F μ V) ρ μ) (E : EigenSplitting F μ V ρ D) (x : M) :
    mLambda F μ V x = ENNReal.ofReal (ρ * ‖D.proj x‖ ^ 2) := by
  have key : ∀ T : Fin (mFirstEigenDim F μ V) → M → ℝ, (∀ i, IsMEigenfunction F μ V ρ (T i)) →
      (∀ i j, ∫ y, T i y * T j y ∂μ = if i = j then 1 else 0) →
      ∑ i, T i x ^ 2 = ρ * ‖D.proj x‖ ^ 2 := by
    intro T hT hTo
    choose a ha1 ha2 using fun i => E.rep (T i) (hT i)
    have hij : ∀ i j, inner ℝ (a i) (a j) = if i = j then ρ else 0 := by
      intro i j
      by_cases h : i = j
      · subst h
        have h1 := hTo i i
        simp only [if_true] at h1
        rw [real_inner_self_eq_norm_sq, ha2, if_pos rfl]
        simp_rw [pow_two]
        rw [h1, mul_one]
      · rw [if_neg h]
        refine E.orth (T i) (T j) (a i) (a j) (hT i) (hT j) (ha1 i) (ha1 j) ?_
        rw [hTo, if_neg h]
    have := sum_sq_inner_of_orthogonal hρ a hij (D.proj x)
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by rw [ha1 i x]
  apply le_antisymm
  · unfold mLambda
    rw [hgap]
    refine iSup_le fun T => iSup_le fun hT => ?_
    rw [key T hT.1 hT.2]
  · obtain ⟨T, hT1, hT2⟩ := E.basis
    refine le_trans ?_ (le_iSup₂ (f := fun (T : Fin (mFirstEigenDim F μ V) → M → ℝ)
      (_ : (∀ i, IsMEigenfunction F μ V (mSpectralGap F μ) (T i)) ∧
        ∀ i j, ∫ y, T i y * T j y ∂μ = if i = j then 1 else 0) =>
          ENNReal.ofReal (∑ i, T i x ^ 2)) T ⟨fun i => hgap ▸ hT1 i, hT2⟩)
    rw [key T hT1 hT2]

end

section Inputs

variable {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M] [OpensMeasurableSpace M]
  {N : Type*} [PseudoEMetricSpace N] [MeasurableSpace N] {k : ℕ} {ρ : ℝ} {μ : Measure M}

/-- The three analytic properties of the diffusion semigroup `Pt` used by the transport argument. -/
structure TransportInputs (μ : Measure M) (ρ : ℝ) (D : SplitData M N k ρ μ)
    (Pt : ℝ≥0 → Kernel M M) : Prop where
  invariant : ∀ t, μ.bind (Pt t) = μ
  contraction : ∀ t : ℝ≥0, W2Contraction (Pt t) (ENNReal.ofReal (Real.exp (-2 * ρ * t)))
  mehler : ∀ (t : ℝ≥0) (x₀ : M), (Pt t x₀).map D.proj = SplitData.mehler ρ t (D.proj x₀)

/-- Pointwise lower bound `W₂²(P_t x₀, μ) ≥ (e^{-2ρt}/ρ) ρ|p x₀|² + k (1-√(1-e^{-2ρt}))²/ρ`. -/
theorem pointwise_lower (hρ : 0 < ρ) (D : SplitData M N k ρ μ) (Pt : ℝ≥0 → Kernel M M)
    (I : TransportInputs μ ρ D Pt) (t : ℝ≥0) (x₀ : M) :
    ENNReal.ofReal (Real.exp (-2 * ρ * t) / ρ) * ENNReal.ofReal (ρ * ‖D.proj x₀‖ ^ 2) +
      ENNReal.ofReal (k * (1 - Real.sqrt (1 - Real.exp (-2 * ρ * t))) ^ 2 / ρ) ≤
    CutCur.wasserstein2 (Pt t x₀) μ ^ 2 := by
  have h := D.lower_of_mehler hρ t.coe_nonneg x₀ (Pt t x₀) (I.mehler t x₀)
  have hq : 0 ≤ Real.exp (-2 * ρ * t) := (Real.exp_pos _).le
  have h2 : ENNReal.ofReal ρ⁻¹ * ENNReal.ofReal (ρ * (Real.exp (-2 * ρ * t) * ‖D.proj x₀‖ ^ 2) +
        k * (1 - Real.sqrt (1 - Real.exp (-2 * ρ * t))) ^ 2) ≤
      CutCur.wasserstein2 (Pt t x₀) μ ^ 2 := by
    calc _ ≤ ENNReal.ofReal ρ⁻¹ * (ENNReal.ofReal ρ * CutCur.wasserstein2 (Pt t x₀) μ ^ 2) :=
          mul_le_mul_right h _
      _ = _ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hρ.le), inv_mul_cancel₀ hρ.ne',
            ENNReal.ofReal_one, one_mul]
  refine le_trans (le_of_eq ?_) h2
  rw [← ENNReal.ofReal_mul (div_nonneg hq hρ.le), ← ENNReal.ofReal_add (by positivity)
    (by positivity), ← ENNReal.ofReal_mul (inv_nonneg.2 hρ.le)]
  congr 1
  field_simp

end Inputs

section Final

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  {N : Type*} [PseudoEMetricSpace N] [MeasurableSpace N]
  {V : M → ℝ} {μ : Measure M} {ρ : ℝ}

/-- **The two-sided Wasserstein estimate** (conclusion of the Challenge's
`riemannian_wasserstein_estimate`) from the splitting data and the three analytic properties
of the semigroup. -/
theorem riemannian_wasserstein_estimate_of_transport [IsProbabilityMeasure μ] (hρ : 0 < ρ)
    (hgap : mSpectralGap F μ = ρ) (D : SplitData M N (mFirstEigenDim F μ V) ρ μ)
    (E : EigenSplitting F μ V ρ D) {Pt : ℝ≥0 → Kernel M M}
    (hP : IsDiffusionSemigroup F V Pt) (I : TransportInputs μ ρ D Pt) (t : ℝ≥0) :
    let q := Real.exp (-2 * ρ * t)
    let lower := fun Λ : ℝ≥0∞ => ENNReal.ofReal (q / ρ) * Λ +
      ENNReal.ofReal (mFirstEigenDim F μ V * (1 - Real.sqrt (1 - q)) ^ 2 / ρ)
    let W := fun x₀ => wasserstein2 (Pt t x₀) μ ^ 2
    (∀ S : Set M, S.Nonempty →
      lower (⨆ x₀ ∈ S, mLambda F μ V x₀) ≤ ⨆ x₀ ∈ S, W x₀ ∧
      ⨆ x₀ ∈ S, W x₀ ≤ ENNReal.ofReal q * ⨆ x₀ ∈ S, ∫⁻ x, edist x₀ x ^ 2 ∂μ) ∧
    ∀ (m : M) (R : ℝ), 0 ≤ R → mLambda F μ V m = 0 →
      lower (ENNReal.ofReal (ρ * R ^ 2)) ≤ ⨆ x₀ ∈ {x | edist m x ≤ ENNReal.ofReal R}, W x₀ := by
  intro q lower W
  have hΛ := mLambda_eq_of_splitting F hρ hgap D E
  have hpt := pointwise_lower hρ D Pt I t
  have hMarkov : IsMarkovKernel (Pt t) := hP.1 t
  refine ⟨fun S hS => ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨x₁, hx₁⟩ := hS
    have : Nonempty S := ⟨⟨x₁, hx₁⟩⟩
    simp_rw [hΛ]
    rw [iSup_subtype']
    simp only [lower]
    rw [ENNReal.mul_iSup, ENNReal.iSup_add]
    refine iSup_le fun x => (hpt x.1).trans ?_
    exact le_iSup₂ (f := fun x₀ (_ : x₀ ∈ S) => W x₀) x.1 x.2
  · exact upper_iSup μ (Pt t) (I.invariant t) (I.contraction t) S
  · intro m R hR hm
    rw [hΛ] at hm
    have hp0 : D.proj m = 0 := by
      have h0 : ρ * ‖D.proj m‖ ^ 2 ≤ 0 := by
        have := (ENNReal.ofReal_eq_zero.1 hm)
        exact this
      have : ‖D.proj m‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖D.proj m‖]
      exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
    let i0 : Fin (mFirstEigenDim F μ V) := ⟨0, E.pos⟩
    let z : EuclideanSpace ℝ (Fin (mFirstEigenDim F μ V)) := R • EuclideanSpace.single i0 (1 : ℝ)
    obtain ⟨x₁, hx₁⟩ := D.surj (z, (D.Φ m).2)
    have hpz : D.proj x₁ = z := by
      have := congrArg Prod.fst hx₁
      simpa [SplitData.proj] using this
    have hnz : ‖z‖ = R := by
      simp [z, norm_smul, abs_of_nonneg hR]
    have hd : edist m x₁ ≤ ENNReal.ofReal R := by
      have h := D.dist_sq m x₁
      have h2 : (D.Φ x₁).2 = (D.Φ m).2 := by
        have := congrArg Prod.snd hx₁
        simpa using this
      have h3 : edist (D.Φ m).1 (D.Φ x₁).1 = ENNReal.ofReal R := by
        have h0' : (D.Φ m).1 = 0 := hp0
        have h1' : (D.Φ x₁).1 = z := hpz
        rw [h1', h0', edist_dist, dist_zero_left, hnz]
      rw [h2, edist_self, h3] at h
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at h
      exact ((ENNReal.pow_le_pow_left_iff two_ne_zero).1 h.le)
    refine le_trans ?_ (le_iSup₂ (f := fun x₀ (_ : x₀ ∈ {x | edist m x ≤ ENNReal.ofReal R}) => W x₀)
      x₁ hd)
    refine le_trans (le_of_eq ?_) (hpt x₁)
    simp only [lower, q, hpz, hnz]

end Final

end CutoffRigidity.Riemann
