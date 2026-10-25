module

public import CutoffRigidity.Paper.ConvexInteraction
public import CutoffRigidity.Paper.SpectralBridge
public import CutoffRigidity.AffineEigenfunctionOrthogonality

/-! # First eigenspace of the Ornstein–Uhlenbeck process (manuscript L278)

For `V = ρ|x|²/2 + const`: `λ₁ = ρ`, `k₁ = d`, and `fᵢ(x) = √ρ xᵢ` is an orthonormal basis of `E₁`.
-/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory
open scoped ContDiff

theorem gradient_ou (ρ c : ℝ) {d : ℕ} (x : CutCur.Rd d) :
    gradient (fun y : CutCur.Rd d => ρ / 2 * ‖y‖ ^ 2 + c) x = ρ • x := by
  have h : HasGradientAt (fun y : CutCur.Rd d => ρ / 2 * ‖y‖ ^ 2 + c) (ρ • x) x := by
    have h1 : HasStrictFDerivAt (fun y : CutCur.Rd d => ‖y‖ ^ 2)
        (2 • (innerSL ℝ x)) x := by
      simpa using (hasStrictFDerivAt_norm_sq x)
    have h2 := (h1.const_mul (ρ / 2)).add_const c
    refine h2.hasFDerivAt.congr_fderiv ?_
    ext v
    simp [innerSL_apply_apply]
    ring
  exact h.gradient

theorem coord_eq (ρ : ℝ) {d : ℕ} (i : Fin d) :
    (fun x : CutCur.Rd d => Real.sqrt ρ * x i) =
      fun x => inner ℝ (Real.sqrt ρ • EuclideanSpace.single i (1 : ℝ)) x + 0 := by
  funext x
  simp [real_inner_smul_left, EuclideanSpace.inner_single_left]

/-- **First eigenspace of the Ornstein–Uhlenbeck process** (introduction, after (1.4)): for
`V(x) = ρ|x|²/2 + c` (the constant `c` normalizing `e^{-V}` to a probability measure) in
dimension `d ≥ 1`, `λ₁ = ρ`, `k₁ = d`, and the functions `fᵢ(x) = √ρ xᵢ`, `i = 1,…,d`, are
eigenfunctions forming an orthonormal family in `L²(μ)` (hence an orthonormal basis of `E₁`). -/
theorem ou_first_eigenspace {d : ℕ} (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ) {c : ℝ}
    (hp : IsProbabilityMeasure (CutCur.gibbs fun x : CutCur.Rd d => ρ / 2 * ‖x‖ ^ 2 + c)) :
    let V := fun x : CutCur.Rd d => ρ / 2 * ‖x‖ ^ 2 + c
    CutCur.spectralGap V = ρ ∧ CutCur.firstEigenDim V = d ∧
      (∀ i : Fin d, CutCur.IsEigenfunction V ρ (fun x => Real.sqrt ρ * x i)) ∧
      ∀ i j : Fin d, ∫ x, (Real.sqrt ρ * x i) * (Real.sqrt ρ * x j) ∂CutCur.gibbs V =
        if i = j then 1 else 0 := by
  intro V
  have hVc : ContDiff ℝ 2 V := by
    have : ContDiff ℝ 2 (fun x : CutCur.Rd d => ‖x‖ ^ 2) := contDiff_norm_sq ℝ
    exact (this.const_smul (ρ / 2)).add contDiff_const
  have hCI := convex_interaction hd hρ (W := fun _ => c) contDiff_const
    (convexOn_const c convex_univ) (fun _ _ => rfl) hp
  obtain ⟨⟨hgap, -⟩, -, hrig⟩ := hCI
  have hp' : IsProbabilityMeasure (gibbsMeasure volume V) := hp
  have hdrift : ∀ i : Fin d, ∀ x, inner ℝ (Real.sqrt ρ • EuclideanSpace.single i (1 : ℝ))
      (gradient V x) = ρ * (inner ℝ (Real.sqrt ρ • EuclideanSpace.single i (1 : ℝ)) x + 0) := by
    intro i x
    have hg : gradient V x = ρ • x := gradient_ou ρ c x
    rw [hg, real_inner_smul_right, add_zero]
  have heig : ∀ i : Fin d, ∀ x, langevinDifferentialOperator V
      (fun y => inner ℝ (Real.sqrt ρ • EuclideanSpace.single i (1 : ℝ)) y + 0) x =
      -ρ * (inner ℝ (Real.sqrt ρ • EuclideanSpace.single i (1 : ℝ)) x + 0) := fun i =>
    (affine_eigenfunction_iff_drift V _ 0 ρ).mpr (hdrift i)
  have hmem : ∀ i : Fin d, MemLp (fun x : CutCur.Rd d => Real.sqrt ρ * x i) 2
      (gibbsMeasure volume V) := by
    intro i
    rw [coord_eq ρ i]
    exact affine_eigenfunction_memLp_all V (hVc.differentiable (by norm_num)) _ 0 ρ hρ (heig i) hp'
  have hef : ∀ i : Fin d, CutCur.IsEigenfunction V ρ (fun x => Real.sqrt ρ * x i) := by
    intro i
    refine isEigenfunction_iff.mpr ⟨?_, hmem i, ?_⟩
    · exact contDiff_const.mul (EuclideanSpace.proj i : CutCur.Rd d →L[ℝ] ℝ).contDiff
    · intro x
      have := heig i x
      have e := congrFun (coord_eq ρ i) x
      simp only at e
      rw [← e, ← coord_eq ρ i] at this
      exact this
  have horth : ∀ i j : Fin d, ∫ x, (Real.sqrt ρ * x i) * (Real.sqrt ρ * x j) ∂CutCur.gibbs V =
      if i = j then 1 else 0 := by
    intro i j
    have h := affine_eigenfunction_cross_moment V (hVc.differentiable (by norm_num))
      (Real.sqrt ρ • EuclideanSpace.single i (1 : ℝ)) (Real.sqrt ρ • EuclideanSpace.single j (1 : ℝ))
      0 0 ρ hρ (heig i) (heig j) hp'
    have hs : (Real.sqrt ρ) ^ 2 = ρ := Real.sq_sqrt hρ.le
    have e1 := congrFun (coord_eq ρ i)
    have e2 := congrFun (coord_eq ρ j)
    have : (fun x : CutCur.Rd d => (Real.sqrt ρ * x i) * (Real.sqrt ρ * x j)) =
        fun x => (inner ℝ (Real.sqrt ρ • EuclideanSpace.single i (1 : ℝ)) x + 0) *
          (inner ℝ (Real.sqrt ρ • EuclideanSpace.single j (1 : ℝ)) x + 0) := by
      funext x; rw [← e1 x, ← e2 x]
    rw [this]
    change ∫ x, _ ∂gibbsMeasure volume V = _
    rw [h, real_inner_smul_left, inner_smul_right]
    by_cases hij : i = j
    · subst hij
      simp
      field_simp
      nlinarith [hs]
    · simp [hij, EuclideanSpace.inner_single_left]
  refine ⟨hgap, ?_, hef, horth⟩
  apply le_antisymm
  · exact firstEigenDim_le hVc hp' hrig
  · -- the d coordinate functions are orthonormal in L² and lie in E₁
    have : FiniteDimensional ℝ (CutCur.firstEigenspace V) := by
      rw [firstEigenspace_eq_gibbsFirstEigenspace hVc hp' hrig]
      exact firstEigenspace_finiteDimensional hVc hp' ρ hρ
        (fun x z => hgap ▸ hrig.2 x z) ((spectralGap_eq_gibbsSpectralGap hVc hp' hrig).symm.trans hgap)
    have hE : ∀ i : Fin d, (hmem i).toLp _ ∈ CutCur.firstEigenspace V := by
      intro i
      have h1 : CutCur.IsEigenfunction V (CutCur.spectralGap V) (fun x => Real.sqrt ρ * x i) := by
        rw [hgap]; exact hef i
      exact Submodule.subset_span ⟨_, h1, (hmem i).coeFn_toLp.symm⟩
    let u : Fin d → (CutCur.firstEigenspace V) := fun i => ⟨(hmem i).toLp _, hE i⟩
    have hon : Orthonormal ℝ u := by
      rw [orthonormal_iff_ite]
      intro i j
      change inner ℝ ((hmem i).toLp _) ((hmem j).toLp _) = _
      rw [← integral_mul_eq_inner (hmem i) (hmem j)]
      exact horth i j
    have := hon.linearIndependent.fintype_card_le_finrank
    simpa [CutCur.firstEigenDim] using this

end CutoffRigidity.Paper
