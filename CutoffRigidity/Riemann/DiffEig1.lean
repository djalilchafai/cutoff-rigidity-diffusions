module

public import CutoffRigidity.Riemann.DiffInstance2
public import CutoffRigidity.Riemann.WeightedRigidity
public import CutoffRigidity.Riemann.WeightedRegular

/-! # Weak equation versus pointwise equation (workstream KER-EIG)

* `E_testFun_eq`: for `u ∈ Q` and a test function `f`, `E(u, f) = -∫ u 𝓛f dμ`.
* `green_test`: weighted Green identity `∫ ū 𝓛f dμ = ∫ f 𝓛ū dμ` for smooth `ū` and `f ∈ C_c^∞`.
* `fundamental_lemma`: a continuous `h` with `∫ h f dμ = 0` for all test functions vanishes.
* `pointwise_of_weak`: a smooth weak solution of `lam u + A u = g` is a pointwise solution.
-/

@[expose] public section

open Bundle MeasureTheory Filter Set
open scoped Manifold ContDiff ENNReal Topology NNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Eig1

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

theorem inner_testToL2_right (u : M →₂[μ] ℝ) (h : testSub F M) :
    inner ℝ u (testToL2 F μ h) = ∫ x, (u : M → ℝ) x * (h : M → ℝ) x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_testToL2 F μ h] with x h1
  rw [h1]
  simp [mul_comm]

/-- **`E(u, f) = -∫ u 𝓛f dμ`** for `u ∈ Q` and a test function `f`. -/
theorem E_testFun_eq {u : M →₂[μ] ℝ} (hu : u ∈ (diffT F hV hμ).Q) (f : testSub F M) :
    (diffT F hV hμ).E u (testToL2 F μ f) =
      -∫ x, (u : M → ℝ) x * mgenerator F V (f : M → ℝ) x ∂μ := by
  obtain ⟨s, hs, hsc⟩ := ((diffT F hV hμ).mem_Q u).1 hu
  set g : (diffFormData F hV hμ).D := ⟨testToL2 F μ f, f, rfl⟩ with hg
  have h1 := (diffT F hV hμ).E_lim s (fun _ => g) u (g : M →₂[μ] ℝ) hs hsc tendsto_const_nhds
    (DirFormData.EnCauchy.const g)
  have hAg : (diffFormData F hV hμ).A g = -(testToL2 F μ (testGen F hV f)) :=
    diffA_toL2 F hV hμ f
  have h2 : ∀ n, (diffFormData F hV hμ).en (s n) g =
      inner ℝ (s n : M →₂[μ] ℝ) (-(testToL2 F μ (testGen F hV f))) := by
    intro n
    show inner ℝ ((diffFormData F hV hμ).A (s n)) (g : M →₂[μ] ℝ) = _
    rw [(diffFormData F hV hμ).symm (s n) g, hAg]
  simp only [h2] at h1
  have h3 : Tendsto (fun n => inner ℝ (s n : M →₂[μ] ℝ) (-(testToL2 F μ (testGen F hV f))))
      atTop (𝓝 (inner ℝ u (-(testToL2 F μ (testGen F hV f))))) :=
    hs.inner tendsto_const_nhds
  have h4 := tendsto_nhds_unique h1 h3
  show (diffT F hV hμ).E u (g : M →₂[μ] ℝ) = _
  rw [h4, inner_neg_right, inner_testToL2_right]
  rfl

include hV hμ in
/-- **Weighted Green identity**: `∫ ū 𝓛f dμ = ∫ f 𝓛ū dμ` for smooth `ū` and `f ∈ C_c^∞`. -/
theorem green_test {ū : M → ℝ} (hū : MSmooth F ū) (f : testSub F M) :
    ∫ x, ū x * mgenerator F V (f : M → ℝ) x ∂μ =
      ∫ x, (f : M → ℝ) x * mgenerator F V ū x ∂μ := by
  have hIBP := weightedIBP_of_isWeightedVolume F hV hμ
  obtain ⟨χ, hχ, hlim⟩ := weightedCutoffs_of_complete F (M := M)
  have hf : MSmooth F (f : M → ℝ) := f.2.1
  have hfc : HasCompactSupport (f : M → ℝ) := f.2.2
  have hLf : MSmooth F (mgenerator F V (f : M → ℝ)) := msmooth_mgenerator F hV hf
  have hLfc : HasCompactSupport (mgenerator F V (f : M → ℝ)) :=
    hasCompactSupport_mgenerator F V hf hfc
  have hχ1 : ∀ n x, ‖mgrad F (χ n) x‖ ≤ 1 := fun n x => by
    refine ((hχ n).2.2 x).2.2.trans ?_
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have key1 : ∫ x, carre F (f : M → ℝ) ū x ∂μ = -∫ x, (f : M → ℝ) x * mgenerator F V ū x ∂μ :=
    hIBP f ū hf hū hfc
  -- integrability facts
  have hI_uLf : Integrable (fun x => ū x * mgenerator F V (f : M → ℝ) x) μ :=
    (hū.continuous.mul hLf.continuous).integrable_of_hasCompactSupport hLfc.mul_left
  have hI_G : Integrable (fun x => carre F (f : M → ℝ) ū x) μ := CutCur.integrable_carre F hf hū hfc μ
  have hGc : HasCompactSupport (fun x => carre F (f : M → ℝ) ū x) := hasCompactSupport_carre F ū hfc
  have hnorm_cont : Continuous (fun x => ‖mgrad F (f : M → ℝ) x‖) := by
    have : (fun x => ‖mgrad F (f : M → ℝ) x‖) = fun x => Real.sqrt (carre F (f : M → ℝ) f x) := by
      funext x; rw [carre_self_eq, Real.sqrt_sq (norm_nonneg _)]
    rw [this]; exact (continuous_carre F hf hf).sqrt
  have hnorm_cs : HasCompactSupport (fun x => ‖mgrad F (f : M → ℝ) x‖) := by
    refine hfc.mono' ?_
    intro x hx
    by_contra h
    exact hx (by simp [mgrad_eq_zero_of_notMem_tsupport F h])
  have hI_bd : Integrable (fun x => |ū x| * ‖mgrad F (f : M → ℝ) x‖) μ :=
    ((hū.continuous.abs.mul hnorm_cont)).integrable_of_hasCompactSupport hnorm_cs.mul_left
  have hn : ∀ n, -∫ x, (χ n x * ū x) * mgenerator F V (f : M → ℝ) x ∂μ =
      (∫ x, χ n x * carre F (f : M → ℝ) ū x ∂μ) +
        ∫ x, ū x * carre F (f : M → ℝ) (χ n) x ∂μ := by
    intro n
    have hsm : MSmooth F (χ n * ū) := (hχ n).1.mul hū
    have h0 := hIBP (χ n * ū) f hsm hf ((hχ n).2.1.mul_right)
    have hpt : ∀ x, carre F (χ n * ū) (f : M → ℝ) x =
        χ n x * carre F (f : M → ℝ) ū x + ū x * carre F (f : M → ℝ) (χ n) x := by
      intro x
      rw [carre_mul_left F (hχ n).1 hū x, carre_comm F ū f x, carre_comm F (χ n) f x]
    have h1 : Integrable (fun x => χ n x * carre F (f : M → ℝ) ū x) μ :=
      ((hχ n).1.continuous.mul (continuous_carre F hf hū)).integrable_of_hasCompactSupport
        hGc.mul_left
    have h2 : Integrable (fun x => ū x * carre F (f : M → ℝ) (χ n) x) μ :=
      (hū.continuous.mul (continuous_carre F hf (hχ n).1)).integrable_of_hasCompactSupport
        (hasCompactSupport_carre F (χ n) hfc).mul_left
    have h3 : ∫ x, carre F (χ n * ū) (f : M → ℝ) x ∂μ =
        (∫ x, χ n x * carre F (f : M → ℝ) ū x ∂μ) +
          ∫ x, ū x * carre F (f : M → ℝ) (χ n) x ∂μ := by
      rw [← integral_add h1 h2]
      exact integral_congr_ae (Eventually.of_forall hpt)
    rw [← h3, h0]
    simp only [Pi.mul_apply]
  -- limits
  have hA : Tendsto (fun n => ∫ x, (χ n x * ū x) * mgenerator F V (f : M → ℝ) x ∂μ) atTop
      (𝓝 (∫ x, ū x * mgenerator F V (f : M → ℝ) x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖ū x * mgenerator F V (f : M → ℝ) x‖)
      (fun n => ((hχ n).1.continuous.mul hū.continuous |>.mul hLf.continuous).aestronglyMeasurable)
      hI_uLf.norm (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · rw [mul_assoc, norm_mul, Real.norm_eq_abs (χ n x), abs_of_nonneg ((hχ n).2.2 x).1]
      exact mul_le_of_le_one_left (norm_nonneg _) ((hχ n).2.2 x).2.1
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hlim x] with n hn
      rw [hn, one_mul]
  have hB : Tendsto (fun n => ∫ x, χ n x * carre F (f : M → ℝ) ū x ∂μ) atTop
      (𝓝 (∫ x, carre F (f : M → ℝ) ū x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖carre F (f : M → ℝ) ū x‖)
      (fun n => ((hχ n).1.continuous.mul (continuous_carre F hf hū)).aestronglyMeasurable)
      hI_G.norm (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · rw [norm_mul, Real.norm_eq_abs (χ n x), abs_of_nonneg ((hχ n).2.2 x).1]
      exact mul_le_of_le_one_left (norm_nonneg _) ((hχ n).2.2 x).2.1
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hlim x] with n hn
      rw [hn, one_mul]
  have hC : Tendsto (fun n => ∫ x, ū x * carre F (f : M → ℝ) (χ n) x ∂μ) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := μ) (fun x => |ū x| * ‖mgrad F (f : M → ℝ) x‖)
      (F := fun n x => ū x * carre F (f : M → ℝ) (χ n) x) (f := fun _ => 0)
      (fun n => (hū.continuous.mul (continuous_carre F hf (hχ n).1)).aestronglyMeasurable)
      hI_bd (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · simpa using this
    · rw [norm_mul, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [Real.norm_eq_abs]
      exact (abs_carre_le F _ _ x).trans (mul_le_of_le_one_right (norm_nonneg _) (hχ1 n x))
    · have hb : Tendsto (fun n : ℕ => |ū x| * ‖mgrad F (f : M → ℝ) x‖ * (1 / ((n : ℝ) + 1))) atTop
          (𝓝 0) := by
        simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
          (|ū x| * ‖mgrad F (f : M → ℝ) x‖)
      refine squeeze_zero_norm (fun n => ?_) hb
      rw [norm_mul, Real.norm_eq_abs]
      calc |ū x| * ‖carre F (f : M → ℝ) (χ n) x‖
          ≤ |ū x| * (‖mgrad F (f : M → ℝ) x‖ * (1 / ((n : ℝ) + 1))) := by
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            rw [Real.norm_eq_abs]
            refine (abs_carre_le F _ _ x).trans ?_
            exact mul_le_mul_of_nonneg_left ((hχ n).2.2 x).2.2 (norm_nonneg _)
        _ = _ := by ring
  have hsum := (hB.add hC)
  simp only [add_zero] at hsum
  have hlimeq : Tendsto (fun n => -∫ x, (χ n x * ū x) * mgenerator F V (f : M → ℝ) x ∂μ) atTop
      (𝓝 (∫ x, carre F (f : M → ℝ) ū x ∂μ)) := by
    refine hsum.congr' (Eventually.of_forall fun n => ?_)
    exact (hn n).symm
  have := tendsto_nhds_unique hlimeq hA.neg
  linarith

theorem not_pos_of_integral_test [μ.IsOpenPosMeasure] {h : M → ℝ} (hh : Continuous h)
    (hz : ∀ f : testSub F M, ∫ x, h x * (f : M → ℝ) x ∂μ = 0) (x : M) : ¬ 0 < h x := by
  intro hx
  have hnhds : {y | 0 < h y} ∈ 𝓝 x := (isOpen_lt continuous_const hh).mem_nhds hx
  obtain ⟨ψ, -, hψ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, F)) x).mem_iff.1 hnhds
  have hψs : MSmooth F (ψ : M → ℝ) := ψ.contMDiff
  have hψc : HasCompactSupport (ψ : M → ℝ) := ψ.hasCompactSupport
  have hpos : 0 < ∫ y, h y * (ψ : M → ℝ) y ∂μ := by
    refine (hh.mul hψs.continuous).integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x)
      hψc.mul_left (fun y => ?_) ?_
    · by_cases hy : y ∈ tsupport (ψ : M → ℝ)
      · exact mul_nonneg (le_of_lt (hψ hy)) ψ.nonneg
      · have h0 := image_eq_zero_of_notMem_tsupport hy
        show 0 ≤ h y * (ψ : M → ℝ) y
        rw [h0, mul_zero]
    · rw [ψ.eq_one, mul_one]; exact hx.ne'
  have := hz ⟨ψ, hψs, hψc⟩
  exact hpos.ne' this

/-- **Fundamental lemma**: a continuous `h` with `∫ h f dμ = 0` for all `f ∈ C_c^∞` vanishes. -/
theorem fundamental_lemma [μ.IsOpenPosMeasure] {h : M → ℝ} (hh : Continuous h)
    (hz : ∀ f : testSub F M, ∫ x, h x * (f : M → ℝ) x ∂μ = 0) (x : M) : h x = 0 := by
  have h1 := not_pos_of_integral_test F hh hz x
  have h2 := not_pos_of_integral_test F (μ := μ) hh.neg (fun f => by
    simp only [Pi.neg_apply, neg_mul]
    rw [integral_neg, hz f, neg_zero]) x
  simp only [Pi.neg_apply, Left.neg_pos_iff] at h2
  exact le_antisymm (not_lt.1 h1) (not_lt.1 h2)

include hV hμ in
/-- **The pointwise PDE from the weak equation**: if `u = ū` is in the form domain, `ū, g'` are
smooth, and `E(u,φ) + lam ⟪u,φ⟫ = ⟪g,φ⟫` for all `φ ∈ Q`, then `lam ū - 𝓛ū = g'` everywhere. -/
theorem pointwise_of_weak {lam : ℝ} {uL gL : M →₂[μ] ℝ} {ū g' : M → ℝ} (hū : MSmooth F ū)
    (hg' : MSmooth F g') (huū : (uL : M → ℝ) =ᵐ[μ] ū) (hgg' : (gL : M → ℝ) =ᵐ[μ] g')
    (hu : uL ∈ (diffT F hV hμ).Q)
    (hweak : ∀ φ ∈ (diffT F hV hμ).Q,
      (diffT F hV hμ).E uL φ + lam * inner ℝ uL φ = inner ℝ gL φ) :
    ∀ x, lam * ū x - mgenerator F V ū x = g' x := by
  haveI := isOpenPosMeasure_of_isWeightedVolume F hV hμ
  set k : M → ℝ := fun x => lam * ū x - mgenerator F V ū x - g' x with hk
  have hkc : Continuous k :=
    ((continuous_const.mul hū.continuous).sub
      (msmooth_mgenerator F hV hū).continuous).sub hg'.continuous
  have hz : ∀ f : testSub F M, ∫ x, k x * (f : M → ℝ) x ∂μ = 0 := by
    intro f
    have hfc : HasCompactSupport (f : M → ℝ) := f.2.2
    have hfs : Continuous (f : M → ℝ) := f.2.1.continuous
    have hw := hweak (testToL2 F μ f) ((((diffFR F hV hμ).toDirFriedrichs.coe_mem
      (⟨testToL2 F μ f, f, rfl⟩ : (diffFormData F hV hμ).D))))
    rw [E_testFun_eq F hV hμ hu f, inner_testToL2_right, inner_testToL2_right] at hw
    have hg := green_test F hV hμ hū f
    have i1 : Integrable (fun x => ū x * (f : M → ℝ) x) μ :=
      (hū.continuous.mul hfs).integrable_of_hasCompactSupport hfc.mul_left
    have i2 : Integrable (fun x => g' x * (f : M → ℝ) x) μ :=
      (hg'.continuous.mul hfs).integrable_of_hasCompactSupport hfc.mul_left
    have i3 : Integrable (fun x => mgenerator F V ū x * (f : M → ℝ) x) μ :=
      ((msmooth_mgenerator F hV hū).continuous.mul hfs).integrable_of_hasCompactSupport
        hfc.mul_left
    have e1 : ∫ x, (uL : M → ℝ) x * mgenerator F V (f : M → ℝ) x ∂μ =
        ∫ x, ū x * mgenerator F V (f : M → ℝ) x ∂μ :=
      integral_congr_ae (huū.mono fun x hx => by simp only [hx])
    have e2 : ∫ x, (uL : M → ℝ) x * (f : M → ℝ) x ∂μ = ∫ x, ū x * (f : M → ℝ) x ∂μ :=
      integral_congr_ae (huū.mono fun x hx => by simp only [hx])
    have e3 : ∫ x, (gL : M → ℝ) x * (f : M → ℝ) x ∂μ = ∫ x, g' x * (f : M → ℝ) x ∂μ :=
      integral_congr_ae (hgg'.mono fun x hx => by simp only [hx])
    rw [e2, e3] at hw
    have hexp : ∫ x, k x * (f : M → ℝ) x ∂μ = lam * ∫ x, ū x * (f : M → ℝ) x ∂μ -
        ∫ x, mgenerator F V ū x * (f : M → ℝ) x ∂μ - ∫ x, g' x * (f : M → ℝ) x ∂μ := by
      have : ∫ x, k x * (f : M → ℝ) x ∂μ = ∫ x, (lam * (ū x * (f : M → ℝ) x) -
          mgenerator F V ū x * (f : M → ℝ) x - g' x * (f : M → ℝ) x) ∂μ :=
        integral_congr_ae (Eventually.of_forall fun x => by simp only [hk]; ring)
      have j0 : Integrable (fun x => lam * (ū x * (f : M → ℝ) x)) μ := i1.const_mul lam
      have j1 : Integrable (fun x => lam * (ū x * (f : M → ℝ) x) -
          mgenerator F V ū x * (f : M → ℝ) x) μ := j0.sub i3
      rw [this, integral_sub j1 i2, integral_sub j0 i3, integral_const_mul]
    have e4 : ∫ x, mgenerator F V ū x * (f : M → ℝ) x ∂μ =
        ∫ x, ū x * mgenerator F V (f : M → ℝ) x ∂μ := by
      rw [hg]; exact integral_congr_ae (Eventually.of_forall fun x => by ring)
    rw [hexp, e4]
    rw [e1] at hw
    linarith
  intro x
  have := fundamental_lemma F hkc hz x
  simp only [hk] at this
  linarith

end Eig1

end CutoffRigidity.Riemann.Diff
