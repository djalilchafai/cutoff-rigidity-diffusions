module

public import CutoffRigidity.Riemann.DiffMoments

/-! # The Challenge estimate from a canonical diffusion (Tier C, assembly)

`riemannian_wasserstein_estimate_of_canonical` has verbatim the conclusion of the Challenge's
`riemannian_wasserstein_estimate`.  Its hypotheses are those of the Challenge, except that the
four analytic hypotheses `hinv`, `hcontr`, `hmehler` (and `hP`) are replaced by a
`CanonicalDiffusion` `Kk` and the identification `Pt = Kk`:

* the lower bound uses only two moments of the eigenmap under `Kk t x₀` (`eigen_moments`) and the
  Cauchy-Schwarz coupling bound (`SplitData.lower_of_moments`): no Mehler law;
* the upper bound uses only the Dirac contraction `W₂²(Kk t x, μ) ≤ e^{-2ρt} ∫ d²(x,·) dμ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Bundle
open scoped ENNReal NNReal Manifold ContDiff RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace CutoffRigidity.Paper

section Riemannian

open CutCur CutoffRigidity.Riemann CutoffRigidity.Riemann.Diff

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M]

theorem riemannian_wasserstein_estimate_of_canonical {V : M → ℝ}
    (hV : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ V)
    {μ : Measure M} [IsProbabilityMeasure μ] (hμ : IsWeightedVolume F μ V) {ρ : ℝ} (hρ : 0 < ρ)
    (hCD : CD F ρ V) (hgap : mSpectralGap F μ = ρ) (hpos : 0 < mFirstEigenDim F μ V)
    {Pt : ℝ≥0 → Kernel M M} (Kk : ℝ≥0 → Kernel M M) (hK : CanonicalDiffusion F V μ ρ Kk)
    (hPK : ∀ t x, Pt t x = Kk t x) (t : ℝ≥0) :
    let q := Real.exp (-2 * ρ * t)
    let lower := fun Λ : ℝ≥0∞ => ENNReal.ofReal (q / ρ) * Λ +
      ENNReal.ofReal (mFirstEigenDim F μ V * (1 - Real.sqrt (1 - q)) ^ 2 / ρ)
    let W := fun x₀ => wasserstein2 (Pt t x₀) μ ^ 2
    (∀ S : Set M, S.Nonempty →
      lower (⨆ x₀ ∈ S, mLambda F μ V x₀) ≤ ⨆ x₀ ∈ S, W x₀ ∧
      ⨆ x₀ ∈ S, W x₀ ≤ ENNReal.ofReal q * ⨆ x₀ ∈ S, ∫⁻ x, edist x₀ x ^ 2 ∂μ) ∧
    ∀ (m : M) (R : ℝ), 0 ≤ R → mLambda F μ V m = 0 →
      lower (ENNReal.ofReal (ρ * R ^ 2)) ≤ ⨆ x₀ ∈ {x | edist m x ≤ ENNReal.ofReal R}, W x₀ := by
  have hPt : Kk = Pt := funext fun s => (Kernel.ext (hPK s)).symm
  subst hPt
  obtain ⟨F', _, _, _, N, _, _, _, _, _, _, _, _, _, _, V', μ', Φ, hprops, hdist, hmap, hrep,
    horth⟩ := riemannian_gaussian_splitting F hV hμ hρ hCD hgap
  have hΦc : Continuous Φ := Φ.contMDiff.continuous
  have hΦm : Measurable (fun x => Φ x) :=
    (hΦc.fst.measurable).prodMk (hΦc.snd.measurable)
  have hμ'p : IsProbabilityMeasure μ' := hprops.2.1
  let D : SplitData M N (mFirstEigenDim F μ V) ρ μ :=
    { Φ := fun x => Φ x
      μ' := μ'
      prob' := hμ'p
      aemeasurable := hΦm.aemeasurable
      surj := Φ.surjective
      dist_sq := hdist
      map_eq := hmap }
  obtain ⟨T0, hT0, hT0o⟩ := exists_orthonormal_eigenbasis F hV hμ hρ hCD hgap
  have E : EigenSplitting F μ V ρ D :=
    { rep := hrep
      orth := horth
      basis := ⟨T0, hT0, hT0o⟩
      pos := hpos }
  intro q lower W
  have hΛ := mLambda_eq_of_splitting F hρ hgap D E
  have hMarkov : ∀ s, IsMarkovKernel (Kk s) := hK.markov
  -- pointwise lower bound from the two moments
  have hpt : ∀ x : M, ENNReal.ofReal (Real.exp (-2 * ρ * t) / ρ) *
        ENNReal.ofReal (ρ * ‖D.proj x‖ ^ 2) +
      ENNReal.ofReal (mFirstEigenDim F μ V * (1 - Real.sqrt (1 - Real.exp (-2 * ρ * t))) ^ 2 / ρ)
      ≤ wasserstein2 (Kk t x) μ ^ 2 := by
    intro x₀
    haveI : IsProbabilityMeasure (Kk t x₀) := (hMarkov t).isProbabilityMeasure x₀
    obtain ⟨h1, h2i, h2⟩ := eigen_moments F hV hμ hρ hCD hgap hK D E t x₀
    have h := D.lower_of_moments hρ t.coe_nonneg x₀ (Kk t x₀) h1 h2i h2
    have hq : 0 ≤ Real.exp (-2 * ρ * t) := (Real.exp_pos _).le
    have h2 : ENNReal.ofReal ρ⁻¹ * ENNReal.ofReal (ρ * (Real.exp (-2 * ρ * t) * ‖D.proj x₀‖ ^ 2) +
          (mFirstEigenDim F μ V) * (1 - Real.sqrt (1 - Real.exp (-2 * ρ * t))) ^ 2) ≤
        wasserstein2 (Kk t x₀) μ ^ 2 := by
      calc _ ≤ ENNReal.ofReal ρ⁻¹ * (ENNReal.ofReal ρ * wasserstein2 (Kk t x₀) μ ^ 2) :=
            mul_le_mul_right h _
        _ = _ := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hρ.le), inv_mul_cancel₀ hρ.ne',
              ENNReal.ofReal_one, one_mul]
    refine le_trans (le_of_eq ?_) h2
    rw [← ENNReal.ofReal_mul (div_nonneg hq hρ.le), ← ENNReal.ofReal_add (by positivity)
      (by positivity), ← ENNReal.ofReal_mul (inv_nonneg.2 hρ.le)]
    congr 1
    field_simp
  refine ⟨fun S hS => ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨x₁, hx₁⟩ := hS
    have : Nonempty S := ⟨⟨x₁, hx₁⟩⟩
    simp_rw [hΛ]
    rw [iSup_subtype']
    simp only [lower]
    rw [ENNReal.mul_iSup, ENNReal.iSup_add]
    refine iSup_le fun x => (hpt x.1).trans ?_
    exact le_iSup₂ (f := fun x₀ (_ : x₀ ∈ S) => W x₀) x.1 x.2
  · exact upper_iSup_dirac (Kk t) (fun x => hK.contraction t x) S
  · intro m R hR hm
    rw [hΛ] at hm
    have hp0 : D.proj m = 0 := by
      have h0 : ρ * ‖D.proj m‖ ^ 2 ≤ 0 := by
        have := (ENNReal.ofReal_eq_zero.1 hm)
        exact this
      have : ‖D.proj m‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖D.proj m‖]
      exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
    let i0 : Fin (mFirstEigenDim F μ V) := ⟨0, E.pos⟩
    let z : EuclideanSpace ℝ (Fin (mFirstEigenDim F μ V)) :=
      R • EuclideanSpace.single i0 (1 : ℝ)
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
    refine le_trans ?_ (le_iSup₂ (f := fun x₀ (_ : x₀ ∈ {x | edist m x ≤ ENNReal.ofReal R}) =>
      W x₀) x₁ hd)
    refine le_trans (le_of_eq ?_) (hpt x₁)
    simp only [lower, q, hpz, hnz]

end Riemannian

end CutoffRigidity.Paper
