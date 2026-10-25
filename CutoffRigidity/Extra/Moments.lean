module

public import CutoffRigidity.Paper.GaussianFactorization
public import CutoffRigidity.SecondMoment
public import CutoffRigidity.GibbsMoments

/-! # Moment bounds used in the proofs of Corollaries 1.3 and 1.4

The coordinate variance bound `Var_μ(x_i) ≤ 1/λ₁`, the second moment bound
`∫|x-m|² dμ ≤ d/λ₁`, the identity `∫|x-x₀|² dμ = |x₀-m|² + ∫|x-m|² dμ`, the bound
`(c² + 1/λ₁) d` on `W₂(δ_{x₀}, μ)²` on the ball `B(m, c√d)`, and the equality
`sup_{|x-m| ≤ R} Λ(x) = λ₁ R²` (manuscript, proofs of Theorem 1.1 and Corollary 1.3).
-/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

variable {d : ℕ}

/-- The coordinates of a probability measure with a Poincaré inequality have variance
at most `1 / rate`. -/
theorem coordinate_sq_dev_le_of_smoothPoincare
    (μ : Measure (CutCur.Rd d)) [IsProbabilityMeasure μ]
    (rate : ℝ) (hLp : MemLp (fun x : CutCur.Rd d => x) 2 μ) (hP : HasSmoothPoincare μ rate)
    (i : Fin d) :
    ∫ x, (x i - (∫ y, y ∂μ) i) ^ 2 ∂μ ≤ 1 / rate := by
  have hcoord : MemLp (fun x : CutCur.Rd d => x i) 2 μ :=
    hLp.of_le_mul (c := 1) (by fun_prop) (Filter.Eventually.of_forall (fun x => by
      simpa only [one_mul] using PiLp.norm_apply_le x i))
  have hmean : (∫ x : CutCur.Rd d, x i ∂μ) = (∫ y, y ∂μ) i := by
    have h := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm
      (hLp.integrable (by norm_num))
    simpa using h
  set c : ℝ := (∫ y, y ∂μ) i with hc
  have hgrad (x : CutCur.Rd d) :
      gradient (fun y : CutCur.Rd d => y i - c) x = EuclideanSpace.single i 1 := by
    have h := gradient_inner_add_const (EuclideanSpace.single i 1) (-c) x
    simpa only [EuclideanSpace.inner_single_left, map_one, one_mul, ← sub_eq_add_neg] using h
  have hi : Integrable (fun x : CutCur.Rd d =>
      ‖gradient (fun y : CutCur.Rd d => y i - c) x‖ ^ 2) μ := by
    simp only [hgrad, PiLp.norm_single, norm_one, one_pow]
    exact integrable_const 1
  have hsm : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun x : CutCur.Rd d => x i - c) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff).sub contDiff_const
  have hmem : MemLp (fun x : CutCur.Rd d => x i - c) 2 μ := hcoord.sub (memLp_const c)
  have hzero : (∫ x, (x i - c) ∂μ) = 0 := by
    rw [integral_sub (hcoord.integrable (by norm_num)) (integrable_const c), hmean]
    simp
  have h := hP (fun x => x i - c) hsm hmem hi hzero
  simpa only [hgrad, PiLp.norm_single, norm_one, one_pow, integral_const, measureReal_def,
    measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] using h

/-- The decomposition of the second moment about an arbitrary point, around the mean. -/
theorem shifted_second_moment (μ : Measure (CutCur.Rd d)) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun x : CutCur.Rd d => x) 2 μ) (x₀ : CutCur.Rd d) :
    ∫ x, ‖x - x₀‖ ^ 2 ∂μ = ‖x₀ - ∫ y, y ∂μ‖ ^ 2 + ∫ x, ‖x - ∫ y, y ∂μ‖ ^ 2 ∂μ := by
  set m : CutCur.Rd d := ∫ y, y ∂μ with hm
  have hi : Integrable (fun x : CutCur.Rd d => x) μ := hμ.integrable (by norm_num)
  have hs : Integrable (fun x : CutCur.Rd d => ‖x - m‖ ^ 2) μ :=
    (hμ.sub (memLp_const m)).norm.integrable_sq
  have hc : Integrable (fun x : CutCur.Rd d => (2 : ℝ) * inner ℝ (x - m) (x₀ - m)) μ :=
    ((hi.sub (integrable_const m)).inner_const (x₀ - m)).const_mul 2
  have hexp : (fun x : CutCur.Rd d => ‖x - x₀‖ ^ 2) =
      fun x => (‖x - m‖ ^ 2 - 2 * inner ℝ (x - m) (x₀ - m)) + ‖x₀ - m‖ ^ 2 := by
    funext x
    have : x - x₀ = (x - m) - (x₀ - m) := by abel
    rw [this, norm_sub_sq_real]
  have hadd := integral_add (hs.sub hc) (integrable_const (‖x₀ - m‖ ^ 2) (μ := μ))
  simp only [Pi.sub_apply] at hadd
  rw [hexp, hadd, integral_sub hs hc, integral_const_mul]
  have hinner : ∫ x, inner ℝ (x - m) (x₀ - m) ∂μ = 0 := by
    have h1 : ∫ x, (x - m) ∂μ = 0 := by
      rw [integral_sub hi (integrable_const m)]
      simp [hm]
    calc
      _ = ∫ x, inner ℝ (x₀ - m) (x - m) ∂μ := by
        simp_rw [real_inner_comm (x₀ - m)]
      _ = inner ℝ (x₀ - m) (∫ x, (x - m) ∂μ) := integral_inner (f := fun x => x - m) (hi.sub (integrable_const m)) (x₀ - m)
      _ = 0 := by rw [h1]; simp
  rw [hinner]
  simp [add_comm]

/-- The moment bounds of the proofs of Theorem 1.1 and Corollaries 1.3, 1.4. -/
theorem langevin_moment_bounds {V : CutCur.Rd d → ℝ} (hV2 : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (CutCur.gibbs V)) (hV : CutCur.RigidCurvature V) :
    let m := ∫ x, x ∂CutCur.gibbs V
    (∀ i : Fin d, variance (fun x : CutCur.Rd d => x i) (CutCur.gibbs V) ≤
        1 / CutCur.spectralGap V) ∧
      ∫ x, ‖x - m‖ ^ 2 ∂CutCur.gibbs V ≤ d / CutCur.spectralGap V ∧
      (∀ x₀, ∫ x, ‖x - x₀‖ ^ 2 ∂CutCur.gibbs V =
        ‖x₀ - m‖ ^ 2 + ∫ x, ‖x - m‖ ^ 2 ∂CutCur.gibbs V) ∧
      (∀ x₀, CutCur.wasserstein2 (Measure.dirac x₀) (CutCur.gibbs V) ^ 2 =
        ENNReal.ofReal (∫ x, ‖x - x₀‖ ^ 2 ∂CutCur.gibbs V)) ∧
      ∀ c : ℝ, 0 ≤ c → ∀ x₀ ∈ CutCur.meanBall V c,
        CutCur.wasserstein2 (Measure.dirac x₀) (CutCur.gibbs V) ^ 2 ≤
          ENNReal.ofReal ((c ^ 2 + 1 / CutCur.spectralGap V) * d) := by
  intro m
  have hm' : m = ∫ x, x ∂gibbsMeasure volume V := rfl
  clear_value m
  simp only [gibbs_eq_gibbsMeasure]
  subst hm'
  set m : CutCur.Rd d := ∫ x, x ∂gibbsMeasure volume V with hm
  have hp' : IsProbabilityMeasure (gibbsMeasure volume V) := hp
  have hd : 0 < d := pos_dim_of_rigidCurvature hp hV
  have hρ := hV.1
  set ρ := CutCur.spectralGap V with hρdef
  have hG : gibbsSpectralGap hV2 hp' = ρ := (spectralGap_eq_gibbsSpectralGap hV2 hp' hV).symm
  have hP : HasSmoothPoincare (gibbsMeasure volume V) ρ := by
    have := hasSmoothPoincare_gibbsSpectralGap hV2 hp' hd ρ hρ hV.2
    rwa [hG] at this
  have hLp : MemLp (fun x : CutCur.Rd d => x) 2 (gibbsMeasure volume V) :=
    gibbs_memLp_two_id_of_hessian_bound hV2 ρ hρ hV.2
  have hcoord : ∀ i : Fin d, ∫ x, (x i - m i) ^ 2 ∂gibbsMeasure volume V ≤ 1 / ρ :=
    fun i => coordinate_sq_dev_le_of_smoothPoincare (gibbsMeasure volume V) ρ hLp hP i
  have hvar : ∀ i : Fin d, variance (fun x : CutCur.Rd d => x i) (gibbsMeasure volume V) =
      ∫ x, (x i - m i) ^ 2 ∂gibbsMeasure volume V := by
    intro i
    have hmean : (∫ x : CutCur.Rd d, x i ∂gibbsMeasure volume V) = m i := by
      have h := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm
        (hLp.integrable (by norm_num))
      simpa using h
    rw [variance_eq_integral (by fun_prop)]
    simp only [hmean]
  have hsum : ∫ x, ‖x - m‖ ^ 2 ∂gibbsMeasure volume V ≤ d / ρ := by
    have hcoordL (i : Fin d) : MemLp (fun x : CutCur.Rd d => x i - m i) 2
        (gibbsMeasure volume V) := by
      have : MemLp (fun x : CutCur.Rd d => x i) 2 (gibbsMeasure volume V) :=
        hLp.of_le_mul (c := 1) (by fun_prop) (Filter.Eventually.of_forall (fun x => by
          simpa only [one_mul] using PiLp.norm_apply_le x i))
      exact this.sub (memLp_const _)
    have hnorm : (fun x : CutCur.Rd d => ‖x - m‖ ^ 2) =
        fun x => ∑ i : Fin d, (x i - m i) ^ 2 := by
      funext x
      rw [EuclideanSpace.real_norm_sq_eq]
      rfl
    rw [hnorm, integral_finsetSum _ (fun i _ => (hcoordL i).integrable_sq)]
    calc
      _ ≤ ∑ _ : Fin d, 1 / ρ := Finset.sum_le_sum (fun i _ => hcoord i)
      _ = d / ρ := by simp [div_eq_mul_inv]
  have hshift : ∀ x₀, ∫ x, ‖x - x₀‖ ^ 2 ∂gibbsMeasure volume V =
      ‖x₀ - m‖ ^ 2 + ∫ x, ‖x - m‖ ^ 2 ∂gibbsMeasure volume V :=
    fun x₀ => shifted_second_moment (gibbsMeasure volume V) hLp x₀
  have hW : ∀ x₀, CutCur.wasserstein2 (Measure.dirac x₀) (gibbsMeasure volume V) ^ 2 =
      ENNReal.ofReal (∫ x, ‖x - x₀‖ ^ 2 ∂gibbsMeasure volume V) := by
    intro x₀
    rw [wasserstein2_sq]
    exact squaredWasserstein_dirac_eq_ofReal (gibbsMeasure volume V) hLp x₀
  refine ⟨fun i => (hvar i).le.trans (hcoord i), hsum, hshift, hW, ?_⟩
  intro c hc x₀ hx₀
  rw [hW, hshift]
  apply ENNReal.ofReal_le_ofReal
  have hx : ‖x₀ - m‖ ≤ c * Real.sqrt d := by
    have hx₀' : x₀ ∈ Metric.closedBall m (c * Real.sqrt d) := hx₀
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx₀'
  have h1 : ‖x₀ - m‖ ^ 2 ≤ c ^ 2 * d := by
    calc ‖x₀ - m‖ ^ 2 ≤ (c * Real.sqrt d) ^ 2 := by gcongr
      _ = c ^ 2 * d := by rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  have h2 : (c ^ 2 + 1 / ρ) * d = c ^ 2 * d + d / ρ := by ring
  rw [h2]
  linarith

/-! ### The supremum of `Λ` over a ball -/

/-- Every first eigenfunction is affine, `f(x) = ⟨A, x⟩ - ⟨A, m⟩` with `m` the mean
(Theorem 3.1 together with `∫ f dμ = 0`). -/
theorem eigenfunction_eq_affine_mean {V : CutCur.Rd d → ℝ} (hV2 : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (CutCur.gibbs V)) (hV : CutCur.RigidCurvature V)
    {f : CutCur.Rd d → ℝ} (hf : CutCur.IsEigenfunction V (CutCur.spectralGap V) f) :
    ∃ A : CutCur.Rd d, ∀ x, f x = inner ℝ A x - inner ℝ A (∫ y, y ∂CutCur.gibbs V) := by
  have hp' : IsProbabilityMeasure (gibbsMeasure volume V) := hp
  simp only [gibbs_eq_gibbsMeasure]
  have hρ := hV.1
  set ρ := CutCur.spectralGap V with hρdef
  obtain ⟨e, m', U, -, -, -, hfac⟩ :=
    euclidean_gaussian_factorization hV2 hp hρ hV.2 rfl
  obtain ⟨a, -, hfx, -⟩ := hfac f hf
  let A : CutCur.Rd d := ∑ i, a i • e i
  let b : ℝ := -∑ i, a i * m' i
  have hfA : ∀ x, f x = inner ℝ A x + b := by
    intro x
    rw [hfx x]
    simp only [A, b, sum_inner, real_inner_smul_left, mul_sub, Finset.sum_sub_distrib]
    ring
  have hfeq : f = fun y => inner ℝ A y + b := funext hfA
  have heigen : ∀ x, langevinDifferentialOperator V (fun y => inner ℝ A y + b) x =
      -ρ * (inner ℝ A x + b) := by
    intro x
    have h := (isEigenfunction_iff.mp hf).2.2 x
    rw [hfeq] at h
    exact h
  have hmean : inner ℝ A (∫ y, y ∂gibbsMeasure volume V) + b = 0 := by
    have hLp : MemLp (fun x : CutCur.Rd d => x) 2 (gibbsMeasure volume V) :=
      gibbs_memLp_two_id_of_hessian_bound hV2 ρ hρ hV.2
    by_cases hA : A = 0
    · have hb : b = 0 := by
        have h0 : ∀ x, langevinDifferentialOperator V
            (fun y => inner ℝ (0 : CutCur.Rd d) y + b) x =
            -ρ * (inner ℝ (0 : CutCur.Rd d) x + b) := by
          rw [hA] at heigen
          exact heigen
        exact affine_eigenfunction_constant_zero V b ρ hρ h0
      simp [hA, hb]
    · have h0 := affine_eigenfunction_mean_zero V (hV2.differentiable (by norm_num)) A hA b ρ hρ
        heigen hp'
      have hint : ∫ x : CutCur.Rd d, (inner ℝ A x + b) ∂gibbsMeasure volume V =
          inner ℝ A (∫ y, y ∂gibbsMeasure volume V) + b := by
        rw [integral_add ((hLp.integrable (by norm_num)).const_inner A) (integrable_const b),
          integral_inner (hLp.integrable (by norm_num)) A]
        simp
      rw [← hint]
      exact h0
  refine ⟨A, fun x => ?_⟩
  rw [hfA x]
  linarith

/-- The pointwise bound and the exact supremum of `Λ` on balls around the mean. -/
theorem sup_eigenLambda_ball {V : CutCur.Rd d → ℝ} (hV2 : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (CutCur.gibbs V)) (hV : CutCur.RigidCurvature V) :
    let m := ∫ x, x ∂CutCur.gibbs V
    (∀ x₀, CutCur.eigenLambda V x₀ ≤
        ENNReal.ofReal (CutCur.spectralGap V * ‖x₀ - m‖ ^ 2)) ∧
      (∀ R : ℝ, 0 ≤ R → ⨆ x₀ ∈ Metric.closedBall m R, CutCur.eigenLambda V x₀ =
        ENNReal.ofReal (CutCur.spectralGap V * R ^ 2)) ∧
      ∀ c : ℝ, 0 ≤ c → ⨆ x₀ ∈ CutCur.meanBall V c, CutCur.eigenLambda V x₀ =
        ENNReal.ofReal (CutCur.spectralGap V * c ^ 2 * d) := by
  intro m
  have hm' : m = ∫ x, x ∂gibbsMeasure volume V := rfl
  clear_value m
  have hp' : IsProbabilityMeasure (gibbsMeasure volume V) := hp
  have hρ := hV.1
  set ρ := CutCur.spectralGap V with hρdef
  obtain ⟨f, hf⟩ := exists_isEigenbasis hV2 hp' hV
  have hAex : ∀ i, ∃ A : CutCur.Rd d, ∀ x, f i x = inner ℝ A x - inner ℝ A m := by
    intro i
    have := eigenfunction_eq_affine_mean hV2 hp hV (hf.1 i)
    rw [hm']
    simpa only [gibbs_eq_gibbsMeasure] using this
  choose A hA using hAex
  set b : Fin (CutCur.firstEigenDim V) → ℝ := fun i => -inner ℝ (A i) m with hb
  have hfA : ∀ i x, f i x = inner ℝ (A i) x + b i := by
    intro i x
    rw [hA i x, hb]
    ring
  have heigen : ∀ i x, langevinDifferentialOperator V (fun y => inner ℝ (A i) y + b i) x =
      -ρ * (inner ℝ (A i) x + b i) := by
    intro i x
    have h := (isEigenfunction_iff.mp (hf.1 i)).2.2 x
    have hfeq : f i = fun y => inner ℝ (A i) y + b i := funext (hfA i)
    rw [hfeq] at h
    exact h
  have horth : ∀ i j, ∫ x, (inner ℝ (A i) x + b i) * (inner ℝ (A j) x + b j)
      ∂gibbsMeasure volume V = if i = j then 1 else 0 := by
    intro i j
    have h := hf.2 i j
    simp_rw [hfA] at h
    exact h
  have hu := affine_eigenfunction_normalized_rows_orthonormal V
    (hV2.differentiable (by norm_num)) A b ρ hρ heigen hp' horth
  set u := normalizedAffineRows A ρ with hudef
  have hsq : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have hfu : ∀ i x₀, f i x₀ = Real.sqrt ρ * inner ℝ (u i) (x₀ - m) := by
    intro i x₀
    rw [hA i x₀, ← inner_sub_right, hudef, normalizedAffineRows, real_inner_smul_left,
      ← mul_assoc, mul_inv_cancel₀ hsq.ne', one_mul]
  have hΛ : ∀ x₀, CutCur.eigenLambda V x₀ =
      ENNReal.ofReal (ρ * ∑ i, inner ℝ (u i) (x₀ - m) ^ 2) := by
    intro x₀
    rw [eigenLambda_eq_sum hV2 hp' hV f hf x₀]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfu i x₀, mul_pow, Real.sq_sqrt hρ.le]
  have hle : ∀ x₀, CutCur.eigenLambda V x₀ ≤ ENNReal.ofReal (ρ * ‖x₀ - m‖ ^ 2) := by
    intro x₀
    rw [hΛ x₀]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hρ.le
    have h := hu.sum_inner_products_le (x₀ - m) (s := Finset.univ)
    simpa only [Real.norm_eq_abs, sq_abs] using h
  have hpos : 0 < CutCur.firstEigenDim V := one_le_firstEigenDim hV2 hp' hV
  have hball : ∀ R : ℝ, 0 ≤ R → ⨆ x₀ ∈ Metric.closedBall m R, CutCur.eigenLambda V x₀ =
      ENNReal.ofReal (ρ * R ^ 2) := by
    intro R hR
    apply le_antisymm
    · refine iSup₂_le fun x₀ hx₀ => (hle x₀).trans (ENNReal.ofReal_le_ofReal ?_)
      have hx : ‖x₀ - m‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hx₀
      have : ‖x₀ - m‖ ^ 2 ≤ R ^ 2 := by gcongr
      exact mul_le_mul_of_nonneg_left this hρ.le
    · let i₀ : Fin (CutCur.firstEigenDim V) := ⟨0, hpos⟩
      let x₀ : CutCur.Rd d := m + R • u i₀
      have hx₀ : x₀ ∈ Metric.closedBall m R := by
        simp [x₀, Metric.mem_closedBall, dist_eq_norm, norm_smul, hu.norm_eq_one,
          abs_of_nonneg hR]
      refine le_iSup₂_of_le x₀ hx₀ ?_
      rw [hΛ x₀]
      apply le_of_eq
      congr 2
      have hy : x₀ - m = R • u i₀ := by simp [x₀]
      simp only [hy, real_inner_smul_right, orthonormal_iff_ite.mp hu _ i₀, mul_ite, mul_one,
        mul_zero]
      simp [ite_pow, Finset.sum_ite_eq']
  refine ⟨hle, hball, fun c hc => ?_⟩
  have hR : 0 ≤ c * Real.sqrt d := mul_nonneg hc (Real.sqrt_nonneg _)
  have h := hball (c * Real.sqrt d) hR
  have hmb : CutCur.meanBall V c = Metric.closedBall m (c * Real.sqrt d) := by
    rw [hm']; rfl
  rw [hmb, h, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  congr 1
  ring

end CutoffRigidity.Paper
