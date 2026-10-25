module

public import CutoffRigidity.Riemann.DiffAPI
public import CutoffRigidity.Riemann.DiffLowerMoments
public import CutoffRigidity.Riemann.WassAssemble
public import CutoffRigidity.Riemann.SplitEigenFrame
public import CutoffRigidity.Riemann.EigenLinear

/-! # The two moments of the eigenmap under a canonical diffusion (Tier C, lemma C3)

For a `CanonicalDiffusion` `Kk` and the splitting data, the Euclidean coordinate `p` of the
eigenmap satisfies, for every `x₀` and `t`,
* `∫ ⟪a, p⟫ dKk t x₀ = e^{-ρt} ⟪a, p x₀⟫`,
* `∫ ‖p‖² dKk t x₀ = e^{-2ρt} ‖p x₀‖² + (k/ρ)(1 - e^{-2ρt})`.

The first is the eigen identity for the eigenfunctions `⟪a, p⟫`; the second is the eigen identity
for `T_i² - 1` (eigenvalue `2ρ`, by `𝓛(f²) = 2f𝓛f + 2Γf` and `Γ T_i = ρ`), summed over the
`L²`-orthonormal eigenbasis; the value `Γ T_i = ρ` is recovered from the invariance of `μ`.
-/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set
open scoped Manifold ContDiff ENNReal NNReal Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace CutCur

section Leibniz

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

theorem mlaplacian_sq {f : M → ℝ} (hf : MSmooth F f) (x : M) :
    mlaplacian F (fun y => f y ^ 2) x = 2 * f x * mlaplacian F f x + 2 * carre F f f x := by
  have e : mgrad F (fun y => f y ^ 2) = fun y => (fun z => 2 * f z) y • mgrad F f y := by
    funext y
    have := mgrad_mul F hf hf y
    have e2 : (fun y => f y ^ 2) = f * f := by funext z; simp [pow_two]
    rw [e2, this, ← add_smul]; congr 1; ring
  have hcov := (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M).isCovariantDerivativeOn
    (s := Set.univ)
  have hg : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) (fun z => 2 * f z) x :=
    (mdiffAt_of_smooth F hf x).const_smul (2:ℝ)
  have hl := hcov.leibniz (σ := mgrad F f) (g := fun z => 2 * f z) (x := x)
    (mgrad_mdiffAt F hf x) hg
  unfold mlaplacian
  rw [e]
  have e3 : (fun y => (fun z => 2 * f z) y • mgrad F f y) = (fun z => 2 * f z) • mgrad F f := rfl
  rw [e3, hl]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply]
  have hd : ∀ v : TangentSpace 𝓘(ℝ, F) x, mvfderiv 𝓘(ℝ, F) (fun z => 2 * f z) x v =
      2 * inner ℝ (mgrad F f x) v := by
    intro v
    have e2 : (fun z => 2 * f z) = (fun _ : M => (2:ℝ)) * f := by funext z; simp
    rw [e2, mvfderiv_mul mdifferentiableAt_const (mdiffAt_of_smooth F hf x), mvfderiv_const]
    simp only [add_apply, smul_apply, smul_eq_mul, zero_apply, mul_zero, add_zero]
    rw [mgrad]
    simp
  simp only [inner_add_left, real_inner_smul_left, Finset.sum_add_distrib, ← Finset.mul_sum, hd]
  congr 1
  have h := (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x)).sum_inner_mul_inner
    (mgrad F f x) (mgrad F f x)
  rw [carre, ← h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm (mgrad F f x)]
  ring

/-- Leibniz rule for the generator on a square: `𝓛(f²) = 2f𝓛f + 2Γ(f)`. -/
theorem mgenerator_sq {V f : M → ℝ} (hf : MSmooth F f) (x : M) :
    mgenerator F V (fun y => f y ^ 2) x = 2 * f x * mgenerator F V f x + 2 * carre F f f x := by
  have e : mgrad F (fun y => f y ^ 2) x = (2 * f x) • mgrad F f x := by
    have := mgrad_mul F hf hf x
    have e2 : (fun y => f y ^ 2) = f * f := by funext z; simp [pow_two]
    rw [e2, this, ← add_smul]; congr 1; ring
  unfold mgenerator
  rw [mlaplacian_sq F hf, e, real_inner_smul_right]
  ring

theorem mlaplacian_const (c : ℝ) (x : M) : mlaplacian F (fun _ : M => c) x = 0 := by
  have e : mgrad F (fun _ : M => c) = 0 := funext (mgrad_const F c)
  unfold mlaplacian
  rw [e, CovariantDerivative.zero]
  simp

theorem mgenerator_const (V : M → ℝ) (c : ℝ) (x : M) : mgenerator F V (fun _ : M => c) x = 0 := by
  unfold mgenerator
  rw [mlaplacian_const, mgrad_const]; simp

end Leibniz

end CutCur

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Moments

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M]
  {V : M → ℝ} {μ : Measure M} {ρ : ℝ} {Kk : ℝ≥0 → Kernel M M}

theorem integral_bind_eq (κ : Kernel M M) [IsMarkovKernel κ] [IsProbabilityMeasure μ] {g : M → ℝ}
    (hg : Integrable g (μ.bind κ)) :
    ∫ y, g y ∂(μ.bind κ) = ∫ x, ∫ y, g y ∂κ x ∂μ := by
  have h := Measure.comp_eq_comp_const_apply (κ := κ) (μ := μ)
  have h2 : (κ ∘ₖ Kernel.const Unit μ) () = μ.bind κ := h.symm
  have := Kernel.integral_comp (η := κ) (κ := Kernel.const Unit μ) (a := ()) (f := g)
    (by rw [h2]; exact hg)
  rw [h2] at this
  simpa using this

/-- The second moment of an eigenfunction with constant carré du champ under the canonical
diffusion: `Kₜ(T²)(x) = e^{-2ρt} T(x)² + (c/ρ)(1 - e^{-2ρt})` where `Γ T = c`. -/
theorem sq_moment_of_eigen [IsFiniteMeasure μ] (hK : CanonicalDiffusion F V μ ρ Kk) (hρ : 0 < ρ)
    {T : M → ℝ} (hT : IsMEigenfunction F μ V ρ T) {c : ℝ}
    (hΓ : ∀ x, carre F T T x = c) (hT2 : MemLp (fun y => T y ^ 2) 2 μ) (t : ℝ≥0) (x : M) :
    Integrable (fun y => T y ^ 2) (Kk t x) ∧
      ∫ y, T y ^ 2 ∂Kk t x =
        Real.exp (-2 * ρ * t) * T x ^ 2 + c / ρ * (1 - Real.exp (-2 * ρ * t)) := by
  have : IsProbabilityMeasure (Kk t x) := (hK.markov t).isProbabilityMeasure x
  have hsq : MSmooth F (fun y => T y ^ 2) := hT.1.pow 2
  have hcst : MSmooth F (fun _ : M => -(c / ρ)) := contMDiff_const
  set u : M → ℝ := fun y => T y ^ 2 + -(c / ρ) with hu
  have hus : MSmooth F u := hsq.add hcst
  have hum : MemLp u 2 μ := hT2.add (memLp_const _)
  have hgen : ∀ y, mgenerator F V u y = -(2 * ρ) * u y := by
    intro y
    have h1 := mgenerator_add F (V := V) hsq hcst y
    rw [show u = fun y => (fun y => T y ^ 2) y + (fun _ : M => -(c / ρ)) y from rfl, h1,
      mgenerator_sq F hT.1, mgenerator_const, hT.2.2 y, hΓ y]
    simp only [hu]
    field_simp
    ring
  obtain ⟨hi, hI⟩ := hK.eigen (2 * ρ) u hus hum hgen t x
  have hi' : Integrable (fun y => T y ^ 2) (Kk t x) := by
    have := hi.add (integrable_const (c / ρ))
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp [hu]
  refine ⟨hi', ?_⟩
  have e : (fun y => T y ^ 2) = fun y => u y + c / ρ := by funext y; simp [hu]
  rw [e, integral_add hi (integrable_const _), hI]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, hu]
  have : Real.exp (-(2 * ρ) * t) = Real.exp (-2 * ρ * t) := by congr 1; ring
  rw [this]
  ring

/-- The carré du champ of a unit-norm eigenfunction with constant `Γ` is `ρ`, by invariance of `μ`. -/
theorem carre_eq_of_invariant [IsProbabilityMeasure μ] (hK : CanonicalDiffusion F V μ ρ Kk)
    (hρ : 0 < ρ) {T : M → ℝ} (hT : IsMEigenfunction F μ V ρ T) {c : ℝ}
    (hΓ : ∀ x, carre F T T x = c) (hT2 : MemLp (fun y => T y ^ 2) 2 μ)
    (hnorm : ∫ y, T y ^ 2 ∂μ = 1) : c = ρ := by
  have hmom := fun x => (sq_moment_of_eigen F hK hρ hT hΓ hT2 1 x)
  have hTi : Integrable (fun y => T y ^ 2) μ := hT2.integrable (by norm_num)
  have hinv := hK.invariant 1
  haveI : IsMarkovKernel (Kk 1) := hK.markov 1
  have hint : Integrable (fun y => T y ^ 2) (μ.bind (Kk 1)) := by rw [hinv]; exact hTi
  have h1 := integral_bind_eq (κ := Kk 1) (μ := μ) hint
  rw [hinv] at h1
  set e := Real.exp (-2 * ρ * ((1 : ℝ≥0) : ℝ)) with he
  have hφ : ∀ x, ∫ y, T y ^ 2 ∂Kk 1 x = e * T x ^ 2 + c / ρ * (1 - e) := fun x => (hmom x).2
  simp_rw [hφ] at h1
  rw [integral_add (hTi.const_mul e) (integrable_const _), integral_const_mul, hnorm] at h1
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h1
  have he1 : e < 1 := by
    rw [he, Real.exp_lt_one_iff]
    simp
    positivity
  have h2 : (1 - e) * (1 - c / ρ) = 0 := by linarith
  rcases mul_eq_zero.1 h2 with h | h
  · linarith
  · field_simp at h
    linarith

end Moments

end CutoffRigidity.Riemann.Diff

namespace CutoffRigidity.Riemann.Diff

open CutCur CutoffRigidity.Riemann

theorem memLp_sq_of_four {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : MemLp f 4 μ) : MemLp (fun x => f x ^ 2) 2 μ := by
  have h := hf.norm_rpow_div 2
  have h42 : (4 : ℝ≥0∞) / 2 = 2 := by
    rw [show (4:ℝ≥0∞) = 2 * 2 by norm_num]
    exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
  rw [h42] at h
  convert h using 1
  funext x
  simp [Real.norm_eq_abs, sq_abs]

section Split

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M]
  {N : Type*} [PseudoEMetricSpace N] [MeasurableSpace N]
  {V : M → ℝ} {μ : Measure M} {ρ : ℝ} {Kk : ℝ≥0 → Kernel M M}

/-- `Γ(f)` is constant for a first eigenfunction (parallel gradient). -/
theorem carre_const_of_eigen (hV : MSmooth F V) [IsProbabilityMeasure μ]
    (hμ : IsWeightedVolume F μ V) (hρ : 0 < ρ) (hCD : CD F ρ V) (hgap : mSpectralGap F μ = ρ)
    {f : M → ℝ} (hf : IsMEigenfunction F μ V ρ f) (x y : M) :
    carre F f f x = carre F f f y := by
  have hX1 : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F).tangent 1 (T% (mgrad F f)) :=
    (WReg.contMDiff_mgrad hf.1).of_le (by simp)
  exact CutoffRigidity.inner_parallel_eq_of_preconnected hX1 hX1
    (fun x => manifold_eigenfunction_parallel_gradient F hV hμ hρ hCD hgap hf x)
    (fun x => manifold_eigenfunction_parallel_gradient F hV hμ hρ hCD hgap hf x) x y

/-- The square of a linear functional of the Euclidean coordinate is in `L²(μ)`. -/
theorem memLp_sq_inner [IsProbabilityMeasure μ] (hρ : 0 < ρ) {k : ℕ} (D : SplitData M N k ρ μ)
    (a : EuclideanSpace ℝ (Fin k)) : MemLp (fun y => ⟪a, D.proj y⟫ ^ 2) 2 μ := by
  have hS : (ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (inv_nonneg.mpr hρ.le)
  have hmap := D.map_proj_eq
  have hpm : AEMeasurable D.proj μ := D.measurable_proj.aemeasurable
  have hm4 : MemLp id 4 (μ.map D.proj) := by
    rw [hmap]; exact IsGaussian.memLp_id _ 4 (by simp)
  have hl : MemLp (fun x : EuclideanSpace ℝ (Fin k) => ⟪a, x⟫) 4 (μ.map D.proj) :=
    (innerSL ℝ a).comp_memLp' hm4
  have hl' : MemLp (fun y => ⟪a, D.proj y⟫) 4 μ :=
    (memLp_map_measure_iff (by fun_prop) hpm).1 hl
  exact memLp_sq_of_four hl'

/-- **Moments of the eigenmap under a canonical diffusion** (Tier C, lemma C3). -/
theorem eigen_moments (hV : MSmooth F V) [IsProbabilityMeasure μ]
    (hμ : IsWeightedVolume F μ V) (hρ : 0 < ρ) (hCD : CD F ρ V) (hgap : mSpectralGap F μ = ρ)
    (hK : CanonicalDiffusion F V μ ρ Kk)
    (D : SplitData M N (mFirstEigenDim F μ V) ρ μ) (E : EigenSplitting F μ V ρ D)
    (t : ℝ≥0) (x₀ : M) :
    (∀ a : EuclideanSpace ℝ (Fin (mFirstEigenDim F μ V)),
      ∫ y, ⟪a, D.proj y⟫ ∂Kk t x₀ = Real.exp (-ρ * t) * ⟪a, D.proj x₀⟫) ∧
    Integrable (fun y => ‖D.proj y‖ ^ 2) (Kk t x₀) ∧
    ∫ y, ‖D.proj y‖ ^ 2 ∂Kk t x₀ =
      Real.exp (-2 * ρ * t) * ‖D.proj x₀‖ ^ 2 +
        (mFirstEigenDim F μ V : ℝ) / ρ * (1 - Real.exp (-2 * ρ * t)) := by
  classical
  have : IsProbabilityMeasure (Kk t x₀) := (hK.markov t).isProbabilityMeasure x₀
  refine ⟨fun a => ?_, ?_⟩
  · have hf := eigen_of_inner F hρ D E a
    exact (hK.eigen ρ _ hf.1 hf.2.1 hf.2.2 t x₀).2
  -- second moment
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
  have hsum : ∀ y, ∑ i, T i y ^ 2 = ρ * ‖D.proj y‖ ^ 2 := by
    intro y
    rw [← sum_sq_inner_of_orthogonal hρ a hij (D.proj y)]
    exact Finset.sum_congr rfl fun i _ => by rw [ha1 i y]
  have hT2 : ∀ i, MemLp (fun y => T i y ^ 2) 2 μ := fun i => by
    have := memLp_sq_inner hρ D (a i)
    convert this using 2 with y
    rw [ha1 i y]
  have hconst : ∀ i x y, carre F (T i) (T i) x = carre F (T i) (T i) y := fun i =>
    carre_const_of_eigen F hV hμ hρ hCD hgap (hT i)
  have hcρ : ∀ i x, carre F (T i) (T i) x = ρ := fun i x => by
    obtain ⟨x1⟩ := (inferInstance : Nonempty M)
    refine (hconst i x x1).trans ?_
    refine carre_eq_of_invariant F hK hρ (hT i) (c := carre F (T i) (T i) x1)
      (fun y => hconst i y x1) (hT2 i) ?_
    have := hTo i i
    simpa [pow_two] using this
  have hmom := fun i => sq_moment_of_eigen F hK hρ (hT i) (hcρ i) (hT2 i) t x₀
  have hint : Integrable (fun y => ‖D.proj y‖ ^ 2) (Kk t x₀) := by
    have : Integrable (fun y => ∑ i, T i y ^ 2) (Kk t x₀) :=
      integrable_finsetSum _ fun i _ => (hmom i).1
    have h2 := this.const_mul ρ⁻¹
    refine h2.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [hsum]
    field_simp
  refine ⟨hint, ?_⟩
  have e : (fun y => ‖D.proj y‖ ^ 2) = fun y => ρ⁻¹ * ∑ i, T i y ^ 2 := by
    funext y; rw [hsum]; field_simp
  rw [e, integral_const_mul, integral_finsetSum _ fun i _ => (hmom i).1]
  simp only [fun i => (hmom i).2]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hs0 : ∑ i, T i x₀ ^ 2 = ρ * ‖D.proj x₀‖ ^ 2 := hsum x₀
  rw [hs0]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

end Split

end CutoffRigidity.Riemann.Diff
