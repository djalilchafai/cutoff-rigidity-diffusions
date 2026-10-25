module

public import CutoffRigidity.Riemann.AssembleMain
public import CutoffRigidity.Riemann.EigenFinite
public import CutoffRigidity.Riemann.TransportMain
public import CutoffRigidity.Riemann.WassMehler

/-! # Assembly of the Riemannian Wasserstein estimate (Challenge `riemannian_wasserstein_estimate`) -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Bundle
open scoped ENNReal NNReal ContDiff Manifold RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann

open CutCur

section Linear

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M]
  {N : Type*} [PseudoEMetricSpace N] [MeasurableSpace N]
  {V : M → ℝ} {μ : Measure M} {ρ : ℝ}

/-- Every linear functional of the Euclidean coordinate is a first eigenfunction. -/
theorem eigen_of_inner (hρ : 0 < ρ) (D : SplitData M N (mFirstEigenDim F μ V) ρ μ)
    (E : EigenSplitting F μ V ρ D) (z : EuclideanSpace ℝ (Fin (mFirstEigenDim F μ V))) :
    IsMEigenfunction F μ V ρ (fun x => ⟪z, D.proj x⟫) := by
  classical
  obtain ⟨T, hT, hTo⟩ := E.basis
  choose a ha1 ha2 using fun i => E.rep (T i) (hT i)
  have hij : ∀ i j, ⟪a i, a j⟫ = if i = j then ρ else 0 := by
    intro i j
    by_cases h : i = j
    · subst h
      have h1 := hTo i i
      simp only [ite_true] at h1
      rw [real_inner_self_eq_norm_sq, ha2, if_pos rfl]
      simp_rw [pow_two]
      rw [h1, mul_one]
    · rw [if_neg h]
      refine E.orth (T i) (T j) (a i) (a j) (hT i) (hT j) (ha1 i) (ha1 j) ?_
      rw [hTo, if_neg h]
  set s : ℝ := (Real.sqrt ρ)⁻¹ with hs
  have hs2 : s ^ 2 * ρ = 1 := by
    rw [hs, inv_pow, Real.sq_sqrt hρ.le]; field_simp
  have hon : Orthonormal ℝ (fun i => s • a i) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [inner_smul_left, inner_smul_right, hij]
    by_cases h : i = j
    · simp [h]; nlinarith [hs2]
    · simp [h]
  have : Nonempty (Fin (mFirstEigenDim F μ V)) := ⟨⟨0, E.pos⟩⟩
  let b := basisOfOrthonormalOfCardEqFinrank hon (by simp)
  have hb : ∀ i, b i = s • a i := fun i => by simp [b]
  have hz : z = ∑ i, (b.repr z i * s) • a i := by
    conv_lhs => rw [← b.sum_repr z]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb, smul_smul]
  have hf : (fun x => ⟪z, D.proj x⟫) = ∑ i, (b.repr z i * s) • T i := by
    funext x
    conv_lhs => rw [hz]
    rw [sum_inner, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left, ← ha1 i x]
    simp
  rw [hf]
  exact (eigenSub F μ V ρ).sum_mem fun i _ => (eigenSub F μ V ρ).smul_mem _ (hT i)

theorem proj_surjective {k : ℕ} (D : SplitData M N k ρ μ) (x₀ : M) :
    Function.Surjective D.proj := by
  intro z
  obtain ⟨x, hx⟩ := D.surj (z, (D.Φ x₀).2)
  exact ⟨x, congrArg Prod.fst hx⟩

end Linear

end CutoffRigidity.Riemann

namespace CutoffRigidity.Paper

section Riemannian

open CutCur CutoffRigidity.Riemann

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M]

theorem riemannian_wasserstein_estimate_amended {V : M → ℝ} (hV : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ V)
    {μ : Measure M} [IsProbabilityMeasure μ] (hμ : IsWeightedVolume F μ V) {ρ : ℝ} (hρ : 0 < ρ)
    (hCD : CD F ρ V) (hgap : mSpectralGap F μ = ρ) (hpos : 0 < mFirstEigenDim F μ V)
    {Pt : ℝ≥0 → Kernel M M} (hP : IsDiffusionSemigroup F V Pt)
    (hinv : ∀ t, μ.bind (Pt t) = μ)
    (hcontr : ∀ (t : ℝ≥0) (ν ν' : Measure M), IsProbabilityMeasure ν → IsProbabilityMeasure ν' →
      wasserstein2 (ν.bind (Pt t)) (ν'.bind (Pt t)) ≤
        ENNReal.ofReal (Real.exp (-ρ * t)) * wasserstein2 ν ν')
    (hmehler : ∀ f, IsMEigenfunction F μ V ρ f → ∀ (t : ℝ≥0) (x₀ : M),
      (Pt t x₀).map f = gaussianReal (Real.exp (-ρ * t) * f x₀)
        (((1 - Real.exp (-2 * ρ * t)) * ∫ x, f x ^ 2 ∂μ).toNNReal))
    (t : ℝ≥0) :
    let q := Real.exp (-2 * ρ * t)
    let lower := fun Λ : ℝ≥0∞ => ENNReal.ofReal (q / ρ) * Λ +
      ENNReal.ofReal (mFirstEigenDim F μ V * (1 - Real.sqrt (1 - q)) ^ 2 / ρ)
    let W := fun x₀ => wasserstein2 (Pt t x₀) μ ^ 2
    (∀ S : Set M, S.Nonempty →
      lower (⨆ x₀ ∈ S, mLambda F μ V x₀) ≤ ⨆ x₀ ∈ S, W x₀ ∧
      ⨆ x₀ ∈ S, W x₀ ≤ ENNReal.ofReal q * ⨆ x₀ ∈ S, ∫⁻ x, edist x₀ x ^ 2 ∂μ) ∧
    ∀ (m : M) (R : ℝ), 0 ≤ R → mLambda F μ V m = 0 →
      lower (ENNReal.ofReal (ρ * R ^ 2)) ≤ ⨆ x₀ ∈ {x | edist m x ≤ ENNReal.ofReal R}, W x₀ := by
  obtain ⟨F', _, _, _, N, _, _, _, _, _, _, _, _, _, _, V', μ', Φ, hprops, hdist, hmap, hrep, horth⟩ :=
    riemannian_gaussian_splitting_base F hV hμ hρ hCD hgap
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
  have hproj := proj_surjective D (Classical.choice (inferInstance : Nonempty M))
  have hmeh : ∀ (t : ℝ≥0) (x₀ : M), (Pt t x₀).map D.proj = SplitData.mehler ρ t (D.proj x₀) := by
    intro t x₀
    haveI : IsProbabilityMeasure (Pt t x₀) := (hP.1 t).isProbabilityMeasure x₀
    refine map_proj_eq_mehler hρ D (Pt t x₀) t x₀ fun z => ?_
    have hf := eigen_of_inner F hρ D E z
    have h1 := hmehler _ hf t x₀
    obtain ⟨a, ha1, ha2⟩ := hrep _ hf
    have haz : a = z := by
      have h0 : ∀ w, ⟪a - z, w⟫ = 0 := by
        intro w
        obtain ⟨x, rfl⟩ := hproj w
        rw [inner_sub_left, sub_eq_zero]
        exact (ha1 x).symm
      exact sub_eq_zero.1 (inner_self_eq_zero.1 (h0 _))
    subst haz
    have : ∫ x, ⟪a, D.proj x⟫ ^ 2 ∂μ = ‖a‖ ^ 2 / ρ := by
      rw [ha2]; field_simp
    rw [this] at h1
    exact h1
  have I : TransportInputs μ ρ D Pt :=
    { invariant := hinv
      contraction := fun t ν ν' hν hν' => by
        have h := hcontr t ν ν' hν hν'
        rw [← wasserstein2_sq_eq_cost2, ← wasserstein2_sq_eq_cost2]
        calc _ ≤ (ENNReal.ofReal (Real.exp (-ρ * t)) * wasserstein2 ν ν') ^ 2 :=
              pow_le_pow_left' h 2
          _ = _ := by
              rw [mul_pow, ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
              congr 3
              push_cast; ring
      mehler := hmeh }
  exact riemannian_wasserstein_estimate_of_transport F hρ hgap D E hP I t

end Riemannian

end CutoffRigidity.Paper
