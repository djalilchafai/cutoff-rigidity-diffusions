module

public import CutoffRigidity.Riemann.DiffBEClass

/-! # Integrated Bochner inequality on `𝒮` (workstream BE, part A4) -/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set
open scoped Manifold ContDiff ENNReal NNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Hess

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  {V : M → ℝ} {μ : Measure M} [IsFiniteMeasure μ]


theorem carre_comm' (f g : M → ℝ) (x : M) : carre F f g x = carre F g f x := by
  simp only [carre]; exact real_inner_comm _ _

/-- Young-type bound: `4 a b ≤ α a² + (4/α) b²`. -/
theorem young4 {α a b : ℝ} (hα : 0 < α) : 4 * a * b ≤ α * a ^ 2 + 4 / α * b ^ 2 := by
  rw [← sub_nonneg]
  have : α * a ^ 2 + 4 / α * b ^ 2 - 4 * a * b = (α * a - 2 * b) ^ 2 / α := by
    field_simp; ring
  rw [this]; positivity


theorem hess_real {ρ α ε c ℓ a s H G LG γ1 γ2 γ3 : ℝ} (hρ : 0 ≤ ρ) (hα : 0 < α) (hc : 0 ≤ c)
    (hε : 0 ≤ ε) (ha2 : a ^ 2 = H) (hs2 : s ^ 2 = G) (ha : 0 ≤ a) (hs : 0 ≤ s)
    (hb : H + ρ * G ≤ LG / 2 - γ3) (h1 : |γ1| ≤ 2 * ε * a * s) (h2 : |γ2| ≤ ε * s) :
    2 * (c ^ 2 * (H + ρ * G)) ≤
      ((c * c * LG + (c * γ1 + c * γ1)) -
        2 * ((c * c * γ3 + ℓ * (c * γ2 + c * γ2)) + c * c * ℓ * ℓ)) +
      (α * (c ^ 2 * ℓ ^ 2) + α * (c ^ 2 * H) + 8 / α * ε ^ 2 * G + 2 * (c ^ 2 * ℓ ^ 2)) := by
  have hb' := mul_le_mul_of_nonneg_left hb (sq_nonneg c)
  have e1 : -(c * γ1) ≤ 2 * c * ε * a * s := by
    have := neg_abs_le γ1
    have h := mul_le_mul_of_nonneg_left (neg_le_of_abs_le h1) hc
    nlinarith
  have e2 : c * ℓ * γ2 ≤ c * |ℓ| * (ε * s) := by
    have h3 : ℓ * γ2 ≤ |ℓ| * (ε * s) := by
      calc ℓ * γ2 ≤ |ℓ * γ2| := le_abs_self _
        _ = |ℓ| * |γ2| := abs_mul _ _
        _ ≤ |ℓ| * (ε * s) := by gcongr
    nlinarith [mul_le_mul_of_nonneg_left h3 hc]
  have y1 := young4 (α := α) (a := c * a) (b := ε * s) hα
  have y2 := young4 (α := α) (a := c * |ℓ|) (b := ε * s) hα
  have hl2 : |ℓ| ^ 2 = ℓ ^ 2 := sq_abs ℓ
  have q1 : 4 / α * (ε * s) ^ 2 = 4 / α * ε ^ 2 * G := by rw [mul_pow, hs2]; ring
  have q2 : 8 / α * ε ^ 2 * G = 4 / α * ε ^ 2 * G + 4 / α * ε ^ 2 * G := by ring
  have r1 : α * (c * a) ^ 2 = α * (c ^ 2 * H) := by rw [mul_pow, ha2]
  have r2 : α * (c * |ℓ|) ^ 2 = α * (c ^ 2 * ℓ ^ 2) := by rw [mul_pow, hl2]
  rw [q1] at y1 y2
  nlinarith

/-- Cutoff step of the integrated Bochner inequality. -/
theorem hess_step {ρ α ε : ℝ} (hρ : 0 ≤ ρ) (hα : 0 < α)
    (hIBP : WeightedIBP F μ V) (hReg : WeightedRegular F V) (hB : WeightedBochnerIneq F V ρ)
    {w χ : M → ℝ} (hw : MSmooth F w) (hχ : MSmooth F χ) (hχc : HasCompactSupport χ)
    (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (hε0 : 0 ≤ ε) (hε : ∀ x, ‖mgrad F χ x‖ ≤ ε)
    (hG : Integrable (fun x => carre F w w x) μ)
    (hL2 : Integrable (fun x => mgenerator F V w x ^ 2) μ) :
    (2 - α) * ∫ x, χ x ^ 2 * (mHessNormSq F w x + ρ * carre F w w x) ∂μ ≤
      (2 + α) * ∫ x, mgenerator F V w x ^ 2 ∂μ + 8 / α * ε ^ 2 * ∫ x, carre F w w x ∂μ := by
  have hGs : MSmooth F (carre F w w) := hReg.1 w w hw hw
  have hLs : MSmooth F (mgenerator F V w) := hReg.2.1 w hw
  have hLGs : MSmooth F (mgenerator F V (carre F w w)) := hReg.2.1 _ hGs
  have hHc : Continuous (mHessNormSq F w) := hReg.2.2 w hw
  have hχχ : MSmooth F (χ * χ) := hχ.mul hχ
  have hχχc : HasCompactSupport (χ * χ) := hχc.mul_right
  have hu2 : MSmooth F ((χ * χ) * mgenerator F V w) := hχχ.mul hLs
  have hu2c : HasCompactSupport ((χ * χ) * mgenerator F V w) := hχχc.mul_right
  have hib1 := hIBP (χ * χ) (carre F w w) hχχ hGs hχχc
  have hib2 := hIBP ((χ * χ) * mgenerator F V w) w hu2 hw hu2c
  have hcs : ∀ g : M → ℝ, Continuous g → Integrable (fun x => χ x ^ 2 * g x) μ := fun g hg =>
    integrable_cutoff_sq_mul hχ.continuous hχc hg
  have hcsq : ∀ g : M → ℝ, Continuous g → (∀ x, χ x = 0 → g x = 0) →
      Integrable g μ := fun g hg h0 =>
    integrable_of_cont_cs hg (hcs_of_zero hχc h0)
  have hKc : Continuous (fun x => mHessNormSq F w x + ρ * carre F w w x) :=
    hHc.add (continuous_const.mul hGs.continuous)
  have hIK := hcs _ hKc
  have hIH := hcs _ hHc
  have hIl := hcs (fun x => mgenerator F V w x ^ 2) (hLs.continuous.pow 2)
  have hIA : Integrable (fun x => (χ * χ) x * mgenerator F V (carre F w w) x) μ :=
    hcsq _ (hχχ.continuous.mul hLGs.continuous) (fun x hx => by simp [hx])
  have hIB : Integrable (fun x => carre F (χ * χ) (carre F w w) x) μ :=
    integrable_of_cont_cs (hReg.1 _ _ hχχ hGs).continuous (hasCompactSupport_carre F _ hχχc)
  have hIC : Integrable (fun x => carre F ((χ * χ) * mgenerator F V w) w x) μ :=
    integrable_of_cont_cs (hReg.1 _ _ hu2 hw).continuous (hasCompactSupport_carre F _ hu2c)
  have hID : Integrable (fun x => ((χ * χ) * mgenerator F V w) x * mgenerator F V w x) μ :=
    hcsq _ (hu2.continuous.mul hLs.continuous) (fun x hx => by simp [hx])
  have hIG := hG
  -- the pointwise inequality
  have hpt : ∀ x, 2 * (χ x ^ 2 * (mHessNormSq F w x + ρ * carre F w w x)) ≤
      ((χ * χ) x * mgenerator F V (carre F w w) x + carre F (χ * χ) (carre F w w) x) -
        2 * (carre F ((χ * χ) * mgenerator F V w) w x +
          ((χ * χ) * mgenerator F V w) x * mgenerator F V w x) +
      (α * (χ x ^ 2 * mgenerator F V w x ^ 2) + α * (χ x ^ 2 * mHessNormSq F w x) +
        8 / α * ε ^ 2 * carre F w w x + 2 * (χ x ^ 2 * mgenerator F V w x ^ 2)) := by
    intro x
    obtain ⟨h0, h1⟩ := hχ01 x
    have hb := hB w hw x
    rw [carre2, carre_comm' F w (mgenerator F V w) x] at hb
    have ha2 : Real.sqrt (mHessNormSq F w x) ^ 2 = mHessNormSq F w x :=
      Real.sq_sqrt (mHessNormSq_nonneg F w x)
    have hs2 : Real.sqrt (carre F w w x) ^ 2 = carre F w w x :=
      Real.sq_sqrt (carre_nonneg F w x)
    have hgs : ‖mgrad F w x‖ = Real.sqrt (carre F w w x) := by
      rw [carre_self_eq, Real.sqrt_sq (norm_nonneg _)]
    have hγ1 : |carre F χ (carre F w w) x| ≤
        2 * ε * Real.sqrt (mHessNormSq F w x) * Real.sqrt (carre F w w x) := by
      refine (abs_carre_carre_le F hw χ x).trans ?_
      have := hε x
      have has : 0 ≤ Real.sqrt (mHessNormSq F w x) * Real.sqrt (carre F w w x) := by positivity
      calc 2 * ‖mgrad F χ x‖ * Real.sqrt (mHessNormSq F w x) * Real.sqrt (carre F w w x)
          = (2 * ‖mgrad F χ x‖) * (Real.sqrt (mHessNormSq F w x) * Real.sqrt (carre F w w x)) := by
            ring
        _ ≤ (2 * ε) * (Real.sqrt (mHessNormSq F w x) * Real.sqrt (carre F w w x)) := by gcongr
        _ = _ := by ring
    have hγ2 : |carre F χ w x| ≤ ε * Real.sqrt (carre F w w x) := by
      refine (abs_carre_le F χ w x).trans ?_
      rw [hgs]; gcongr; exact hε x
    have key := hess_real (ρ := ρ) (α := α) (ε := ε) (c := χ x) (ℓ := mgenerator F V w x)
      hρ hα h0 hε0 ha2 hs2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hb hγ1 hγ2
    simp only [Pi.mul_apply]
    rw [carre_mul_left F hχχ hLs, carre_mul_left F hχ hχ, carre_mul_left F hχ hχ]
    simp only [Pi.mul_apply]
    linarith
  have hl1 : Integrable (fun x => α * (χ x ^ 2 * mgenerator F V w x ^ 2)) μ := hIl.const_mul α
  have hh1 : Integrable (fun x => α * (χ x ^ 2 * mHessNormSq F w x)) μ := hIH.const_mul α
  have hg1 : Integrable (fun x => 8 / α * ε ^ 2 * carre F w w x) μ := hIG.const_mul _
  have hl2 : Integrable (fun x => 2 * (χ x ^ 2 * mgenerator F V w x ^ 2)) μ := hIl.const_mul 2
  have hs1 : Integrable (fun x => α * (χ x ^ 2 * mgenerator F V w x ^ 2) +
      α * (χ x ^ 2 * mHessNormSq F w x)) μ := hl1.add hh1
  have hs2 : Integrable (fun x => α * (χ x ^ 2 * mgenerator F V w x ^ 2) +
      α * (χ x ^ 2 * mHessNormSq F w x) + 8 / α * ε ^ 2 * carre F w w x) μ := hs1.add hg1
  have hF3 : Integrable (fun x => α * (χ x ^ 2 * mgenerator F V w x ^ 2) +
      α * (χ x ^ 2 * mHessNormSq F w x) + 8 / α * ε ^ 2 * carre F w w x +
      2 * (χ x ^ 2 * mgenerator F V w x ^ 2)) μ := hs2.add hl2
  have hAB : Integrable (fun x => (χ * χ) x * mgenerator F V (carre F w w) x +
      carre F (χ * χ) (carre F w w) x) μ := hIA.add hIB
  have hCD : Integrable (fun x => carre F ((χ * χ) * mgenerator F V w) w x +
      ((χ * χ) * mgenerator F V w) x * mgenerator F V w x) μ := hIC.add hID
  have hCD2 : Integrable (fun x => 2 * (carre F ((χ * χ) * mgenerator F V w) w x +
      ((χ * χ) * mgenerator F V w) x * mgenerator F V w x)) μ := hCD.const_mul 2
  have hABC : Integrable (fun x => ((χ * χ) x * mgenerator F V (carre F w w) x +
      carre F (χ * χ) (carre F w w) x) - 2 * (carre F ((χ * χ) * mgenerator F V w) w x +
      ((χ * χ) * mgenerator F V w) x * mgenerator F V w x)) μ := hAB.sub hCD2
  have hR : Integrable (fun x => ((χ * χ) x * mgenerator F V (carre F w w) x +
      carre F (χ * χ) (carre F w w) x) - 2 * (carre F ((χ * χ) * mgenerator F V w) w x +
      ((χ * χ) * mgenerator F V w) x * mgenerator F V w x) +
      (α * (χ x ^ 2 * mgenerator F V w x ^ 2) +
      α * (χ x ^ 2 * mHessNormSq F w x) + 8 / α * ε ^ 2 * carre F w w x +
      2 * (χ x ^ 2 * mgenerator F V w x ^ 2))) μ := hABC.add hF3
  have h1 := integral_mono (hIK.const_mul 2) hR hpt
  rw [integral_const_mul, integral_add hABC hF3,
    integral_sub hAB hCD2, integral_add hIA hIB, integral_const_mul,
    integral_add hIC hID, integral_add hs2 hl2, integral_add hs1 hg1,
    integral_add hl1 hh1, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, hib1, hib2] at h1
  have hlt : ∫ x, χ x ^ 2 * mgenerator F V w x ^ 2 ∂μ ≤ ∫ x, mgenerator F V w x ^ 2 ∂μ := by
    refine integral_mono hIl hL2 fun x => ?_
    obtain ⟨h0, h1⟩ := hχ01 x
    have : χ x ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (mgenerator F V w x)]
  have hHK : ∫ x, χ x ^ 2 * mHessNormSq F w x ∂μ ≤
      ∫ x, χ x ^ 2 * (mHessNormSq F w x + ρ * carre F w w x) ∂μ := by
    refine integral_mono hIH hIK fun x => ?_
    have := mul_nonneg (sq_nonneg (χ x)) (mul_nonneg hρ (carre_nonneg F w x))
    nlinarith
  have hD : ∫ x, ((χ * χ) * mgenerator F V w) x * mgenerator F V w x ∂μ =
      ∫ x, χ x ^ 2 * mgenerator F V w x ^ 2 ∂μ := by
    congr 1; funext x; simp only [Pi.mul_apply]; ring
  rw [hD] at h1
  nlinarith [mul_le_mul_of_nonneg_left hlt hα.le, mul_le_mul_of_nonneg_left hHK hα.le]

variable (hIBP : WeightedIBP F μ V) (hReg : WeightedRegular F V) (hC : WeightedCutoffs F M)

include hIBP hReg hC in
/-- (A4) Integrated Bochner on `𝒮`: `‖Hess w‖² ∈ L¹` and `∫(‖Hess w‖² + ρ Γw) ≤ ∫ (𝓛w)²`. -/
theorem hess_integrable_of_InS {ρ : ℝ} (hρ : 0 ≤ ρ) (hB : WeightedBochnerIneq F V ρ)
    {w : M → ℝ} (hw : InS F V μ w) :
    Integrable (fun x => mHessNormSq F w x) μ ∧
      ∫ x, (mHessNormSq F w x + ρ * carre F w w x) ∂μ ≤ ∫ x, mgenerator F V w x ^ 2 ∂μ := by
  obtain ⟨hws, hw2, hL2m⟩ := id hw
  have hG : Integrable (fun x => carre F w w x) μ := integrable_carre_of_InS F hIBP hReg hC hw
  have hL2 : Integrable (fun x => mgenerator F V w x ^ 2) μ := hL2m.integrable_sq
  obtain ⟨χ, hχ, hlim⟩ := hC
  have hGs : MSmooth F (carre F w w) := hReg.1 w w hws hws
  have hHc : Continuous (mHessNormSq F w) := hReg.2.2 w hws
  have hKc : Continuous (fun x => mHessNormSq F w x + ρ * carre F w w x) :=
    hHc.add (continuous_const.mul hGs.continuous)
  have hKnn : ∀ x, 0 ≤ mHessNormSq F w x + ρ * carre F w w x := fun x =>
    add_nonneg (mHessNormSq_nonneg F w x) (mul_nonneg hρ (carre_nonneg F w x))
  set T := ∫ x, mgenerator F V w x ^ 2 ∂μ with hT
  set J := ∫ x, carre F w w x ∂μ with hJ
  have hT0 : 0 ≤ T := integral_nonneg fun x => sq_nonneg _
  have hJ0 : 0 ≤ J := integral_nonneg fun x => carre_nonneg F w x
  have hmeas : ∀ n, Measurable (fun x => χ n x ^ 2 * (mHessNormSq F w x +
      ρ * carre F w w x)) := fun n =>
    (((hχ n).1.continuous.pow 2).mul hKc).measurable
  have hev : ∀ x, ∀ᶠ n in atTop, χ n x ^ 2 * (mHessNormSq F w x + ρ * carre F w w x) =
      mHessNormSq F w x + ρ * carre F w w x := by
    intro x
    filter_upwards [hlim x] with n hn
    simp [hn]
  have hfat : ∀ α : ℝ, 0 < α → α ≤ 1 → ∫⁻ x, ENNReal.ofReal (mHessNormSq F w x +
      ρ * carre F w w x) ∂μ ≤ ENNReal.ofReal (((2 + α) * T) / (2 - α)) := by
    intro α hα hα1
    have h2a : 0 < 2 - α := by linarith
    refine lintegral_ofReal_le_of_approx (h := fun n x => χ n x ^ 2 * (mHessNormSq F w x +
      ρ * carre F w w x)) hmeas hev
      (b := fun n => ENNReal.ofReal (((2 + α) * T + 8 / α * (1 / ((n : ℝ) + 1)) ^ 2 * J) /
        (2 - α))) ?_ ?_
    · intro n
      rw [← ofReal_integral_eq_lintegral_ofReal
        (integrable_cutoff_sq_mul (hχ n).1.continuous (hχ n).2.1 hKc)
        (Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (hKnn x))]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [le_div_iff₀ h2a, mul_comm]
      exact hess_step F hρ hα hIBP hReg hB hws (hχ n).1 (hχ n).2.1
        (fun x => ⟨((hχ n).2.2 x).1, ((hχ n).2.2 x).2.1⟩) (by positivity)
        (fun x => ((hχ n).2.2 x).2.2) hG hL2
    · have h0 : Tendsto (fun n : ℕ => ((2 + α) * T + 8 / α * (1 / ((n : ℝ) + 1)) ^ 2 * J) /
          (2 - α)) atTop (𝓝 (((2 + α) * T) / (2 - α))) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
        have h3 := (((this.const_mul (8 / α)).mul_const J).const_add ((2 + α) * T)).div_const
          (2 - α)
        simpa using h3
      exact ENNReal.tendsto_ofReal h0
  have hKint : Integrable (fun x => mHessNormSq F w x + ρ * carre F w w x) μ := by
    refine ⟨hKc.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hKnn)]
    exact lt_of_le_of_lt (hfat 1 one_pos le_rfl) ENNReal.ofReal_lt_top
  have hHint : Integrable (fun x => mHessNormSq F w x) μ := by
    refine hKint.mono' hHc.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mHessNormSq_nonneg F w x)]
    have := mul_nonneg hρ (carre_nonneg F w x)
    linarith
  refine ⟨hHint, ?_⟩
  set K := ∫ x, (mHessNormSq F w x + ρ * carre F w w x) ∂μ with hK
  have hK0 : 0 ≤ K := integral_nonneg hKnn
  have hα : ∀ α : ℝ, 0 < α → α ≤ 1 → (2 - α) * K ≤ (2 + α) * T := by
    intro α hα hα1
    have h2a : 0 < 2 - α := by linarith
    have := hfat α hα hα1
    rw [← ofReal_integral_eq_lintegral_ofReal hKint (Eventually.of_forall hKnn)] at this
    have h4 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp this
    rw [le_div_iff₀ h2a] at h4
    linarith
  refine le_of_forall_pos_le_add fun e he => ?_
  set α := min 1 (e / (T + K + 1)) with hαdef
  have hαpos : 0 < α := lt_min one_pos (by positivity)
  have hα1 : α ≤ 1 := min_le_left _ _
  have hα2 : α ≤ e / (T + K + 1) := min_le_right _ _
  have h5 : α * (T + K + 1) ≤ e := by
    rwa [le_div_iff₀ (by positivity), ] at hα2
  have := hα α hαpos hα1
  nlinarith

end Hess

end CutoffRigidity.Riemann.Diff
