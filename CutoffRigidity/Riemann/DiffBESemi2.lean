module

public import CutoffRigidity.Riemann.DiffBEClass

/-! # Energy estimates on bounded functions (workstream BE, part C)

For smooth `v` bounded with bounded generator: `∫ Γ v ≤ ‖v‖∞ ‖𝓛v‖∞ μ(M)`; Cauchy-Schwarz type
`L¹` bound for `Γ(a,b)`; estimates for `Γ(w') - Γ(w)` and the `L¹` derivative of `Γ(w_h)`.
-/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set
open scoped Manifold ContDiff ENNReal NNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Energy

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} {μ : Measure M} [IsFiniteMeasure μ]

theorem mgrad_comb {a b : M → ℝ} (α β : ℝ) (ha : MSmooth F a) (hb : MSmooth F b) (x : M) :
    mgrad F (fun y => α * a y + β * b y) x = α • mgrad F a x + β • mgrad F b x := by
  have h1 : MSmooth F (fun y => α * a y) := contMDiff_const.mul ha
  have h2 : MSmooth F (fun y => β * b y) := contMDiff_const.mul hb
  rw [mgrad_add' F h1 h2, mgrad_const_mul F α ha, mgrad_const_mul F β hb]

theorem mgenerator_comb {a b : M → ℝ} (α β : ℝ) (ha : MSmooth F a) (hb : MSmooth F b) (x : M) :
    mgenerator F V (fun y => α * a y + β * b y) x = α * mgenerator F V a x + β * mgenerator F V b x := by
  have h1 : MSmooth F (fun y => α * a y) := contMDiff_const.mul ha
  have h2 : MSmooth F (fun y => β * b y) := contMDiff_const.mul hb
  rw [mgenerator_add F h1 h2, mgenerator_const_mul F α ha, mgenerator_const_mul F β hb]

theorem msmooth_comb {a b : M → ℝ} (α β : ℝ) (ha : MSmooth F a) (hb : MSmooth F b) :
    MSmooth F (fun y => α * a y + β * b y) := by
  have h1 : MSmooth F (fun y => α * a y) := contMDiff_const.mul ha
  have h2 : MSmooth F (fun y => β * b y) := contMDiff_const.mul hb
  exact h1.add h2

theorem abs_carre_le (a b : M → ℝ) {lam : ℝ} (hl : 0 < lam) (x : M) :
    |carre F a b x| ≤ (lam * carre F a a x + carre F b b x / lam) / 2 := by
  have h1 : |carre F a b x| ≤ ‖mgrad F a x‖ * ‖mgrad F b x‖ := abs_real_inner_le_norm _ _
  rw [carre_self_eq, carre_self_eq]
  refine h1.trans ?_
  set p := ‖mgrad F a x‖
  set q := ‖mgrad F b x‖
  have : 2 * (p * q) ≤ lam * p ^ 2 + q ^ 2 / lam := by
    have h := sq_nonneg (lam * p - q)
    have : q ^ 2 / lam = q ^ 2 * lam⁻¹ := div_eq_mul_inv _ _
    rw [this]
    have hi : lam * lam⁻¹ = 1 := mul_inv_cancel₀ hl.ne'
    have hi0 : 0 < lam⁻¹ := inv_pos.2 hl
    nlinarith [mul_nonneg hi0.le h]
  linarith

variable (hIBP : WeightedIBP F μ V) (hReg : WeightedRegular F V) (hC : WeightedCutoffs F M)

include hIBP hReg hC in
theorem energy_bound {v : M → ℝ} (hv : MSmooth F v) {A B : ℝ} (hA : ∀ x, |v x| ≤ A)
    (hB : ∀ x, |mgenerator F V v x| ≤ B) :
    Integrable (fun x => carre F v v x) μ ∧
      ∫ x, carre F v v x ∂μ ≤ A * B * μ.real univ := by
  have hS : InS F V μ v := InS.of_bounded F hReg hv ⟨A, hA⟩ ⟨B, hB⟩
  have hint := integrable_carre_of_InS F hIBP hReg hC hS
  obtain ⟨-, h2⟩ := integral_carre_cross F hIBP hReg hC hv hS.2.1 hint hS
  refine ⟨hint, ?_⟩
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => v x * mgenerator F V v x)
    (C := A * B) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hA x) (hB x) (abs_nonneg _) ((abs_nonneg _).trans (hA x)))
  rw [h2]
  rw [Real.norm_eq_abs] at this
  exact (neg_le_abs _).trans this

theorem integral_abs_carre_le {a b : M → ℝ} (ha : MSmooth F a) (hb : MSmooth F b)
    (hGa : Integrable (fun x => carre F a a x) μ) (hGb : Integrable (fun x => carre F b b x) μ)
    {lam : ℝ} (hl : 0 < lam) :
    Integrable (fun x => carre F a b x) μ ∧
      ∫ x, |carre F a b x| ∂μ ≤ (lam * ∫ x, carre F a a x ∂μ + (∫ x, carre F b b x ∂μ) / lam) / 2 := by
  have hbd : Integrable (fun x => (lam * carre F a a x + carre F b b x / lam) / 2) μ :=
    ((hGa.const_mul lam).add (hGb.div_const lam)).div_const 2
  have hi : Integrable (fun x => carre F a b x) μ :=
    Integrable.mono' hbd (continuous_carre F ha hb).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact abs_carre_le F a b hl x)
  refine ⟨hi, ?_⟩
  calc ∫ x, |carre F a b x| ∂μ ≤ ∫ x, (lam * carre F a a x + carre F b b x / lam) / 2 ∂μ :=
        integral_mono hi.abs hbd fun x => abs_carre_le F a b hl x
    _ = _ := by
        rw [integral_div, integral_add (hGa.const_mul lam) (hGb.div_const lam), integral_const_mul,
          integral_div]

theorem mgenerator_sub'' {f g : M → ℝ} (hf : MSmooth F f) (hg : MSmooth F g) (x : M) :
    mgenerator F V (fun y => f y - g y) x = mgenerator F V f x - mgenerator F V g x := by
  have e : (fun y => f y - g y) = fun y => f y + (-1) * g y := by
    funext y; ring
  have hg' : MSmooth F (fun y => -1 * g y) := contMDiff_const.mul hg
  rw [e, mgenerator_add F hf hg' x, mgenerator_const_mul F (-1) hg x]; ring

theorem msmooth_dq {w1 w0 : M → ℝ} (h : ℝ) (h1 : MSmooth F w1) (h0 : MSmooth F w0) :
    MSmooth F (fun y => h⁻¹ * (w1 y - w0 y)) := by
  have : MSmooth F (fun y => w1 y - w0 y) := h1.sub h0
  exact contMDiff_const.mul this

theorem mgrad_dq {w1 w0 : M → ℝ} (h : ℝ) (h1 : MSmooth F w1) (h0 : MSmooth F w0) (x : M) :
    mgrad F (fun y => h⁻¹ * (w1 y - w0 y)) x = h⁻¹ • (mgrad F w1 x - mgrad F w0 x) := by
  rw [mgrad_const_mul F h⁻¹ (h1.sub h0), mgrad_sub' F h1 h0]

theorem mgenerator_dq {w1 w0 : M → ℝ} (h : ℝ) (h1 : MSmooth F w1) (h0 : MSmooth F w0) (x : M) :
    mgenerator F V (fun y => h⁻¹ * (w1 y - w0 y)) x =
      h⁻¹ * (mgenerator F V w1 x - mgenerator F V w0 x) := by
  rw [mgenerator_const_mul F h⁻¹ (h1.sub h0), mgenerator_sub'' F h1 h0]

theorem mgrad_dq_sub {w1 w0 D : M → ℝ} (h : ℝ) (h1 : MSmooth F w1) (h0 : MSmooth F w0)
    (hD : MSmooth F D) (x : M) :
    mgrad F (fun y => h⁻¹ * (w1 y - w0 y) - D y) x =
      h⁻¹ • (mgrad F w1 x - mgrad F w0 x) - mgrad F D x := by
  rw [mgrad_sub' F (msmooth_dq F h h1 h0) hD, mgrad_dq F h h1 h0]

theorem mgenerator_dq_sub {w1 w0 D : M → ℝ} (h : ℝ) (h1 : MSmooth F w1) (h0 : MSmooth F w0)
    (hD : MSmooth F D) (x : M) :
    mgenerator F V (fun y => h⁻¹ * (w1 y - w0 y) - D y) x =
      h⁻¹ * (mgenerator F V w1 x - mgenerator F V w0 x) - mgenerator F V D x := by
  rw [mgenerator_sub'' F (msmooth_dq F h h1 h0) hD, mgenerator_dq F h h1 h0]

theorem carre_sub_eq {w' w : M → ℝ} (h' : MSmooth F w') (h : MSmooth F w) (x : M) :
    carre F w' w' x - carre F w w x =
      carre F (fun y => w' y - w y) (fun y => w' y + w y) x := by
  simp only [carre, mgrad_sub' F h' h, mgrad_add' F h' h, inner_sub_left, inner_add_right]
  rw [real_inner_comm (mgrad F w x) (mgrad F w' x)]; ring

/-- the pointwise identity for the `L¹` derivative of `Γ(w_h)`. -/
theorem carre_deriv_identity {w1 w0 D : M → ℝ} {h : ℝ} (hh : h ≠ 0) (h1 : MSmooth F w1)
    (h0 : MSmooth F w0) (hD : MSmooth F D) (x : M) :
    (carre F w1 w1 x - carre F w0 w0 x) / h - 2 * carre F D w0 x =
      2 * carre F (fun y => h⁻¹ * (w1 y - w0 y) - D y) w0 x +
        h * carre F (fun y => h⁻¹ * (w1 y - w0 y)) (fun y => h⁻¹ * (w1 y - w0 y)) x := by
  simp only [carre, mgrad_dq_sub F h h1 h0 hD, mgrad_dq F h h1 h0, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm (mgrad F w0 x) (mgrad F w1 x)]
  field_simp
  ring

include hIBP hReg hC in
/-- `L¹` Lipschitz estimate for `w ↦ Γ(w)` on bounded functions with bounded generator. -/
theorem integral_abs_carre_sub_le {w w' : M → ℝ} (hw : MSmooth F w) (hw' : MSmooth F w')
    {A B a b δ : ℝ} (hδ : 0 < δ)
    (hA : ∀ x, |w x| ≤ A) (hA' : ∀ x, |w' x| ≤ A)
    (hB : ∀ x, |mgenerator F V w x| ≤ B) (hB' : ∀ x, |mgenerator F V w' x| ≤ B)
    (ha : ∀ x, |w' x - w x| ≤ a * δ) (hb : ∀ x, |mgenerator F V w' x - mgenerator F V w x| ≤ b * δ) :
    ∫ x, |carre F w' w' x - carre F w w x| ∂μ ≤ ((a * b + 4 * A * B) * μ.real univ * δ) / 2 := by
  have hD : MSmooth F (fun y => w' y - w y) := hw'.sub hw
  have hS : MSmooth F (fun y => w' y + w y) := hw'.add hw
  obtain ⟨iD, eD⟩ := energy_bound F hIBP hReg hC (V := V) (μ := μ) hD (A := a * δ) (B := b * δ) ha
    (fun x => by rw [mgenerator_sub'' F hw' hw]; exact hb x)
  obtain ⟨iS, eS⟩ := energy_bound F hIBP hReg hC (V := V) (μ := μ) hS (A := 2 * A) (B := 2 * B)
    (fun x => (abs_add_le _ _).trans (by linarith [hA x, hA' x]))
    (fun x => by
      rw [mgenerator_add F hw' hw]
      exact (abs_add_le _ _).trans (by linarith [hB x, hB' x]))
  obtain ⟨-, e⟩ := integral_abs_carre_le F hD hS iD iS (inv_pos.2 hδ)
  have hm : 0 ≤ μ.real univ := measureReal_nonneg
  have hcongr : ∫ x, |carre F w' w' x - carre F w w x| ∂μ =
      ∫ x, |carre F (fun y => w' y - w y) (fun y => w' y + w y) x| ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [carre_sub_eq F hw' hw])
  rw [hcongr]
  refine e.trans ?_
  have h1 : δ⁻¹ * ∫ x, carre F (fun y => w' y - w y) (fun y => w' y - w y) x ∂μ ≤
      δ⁻¹ * (a * δ * (b * δ) * μ.real univ) :=
    mul_le_mul_of_nonneg_left eD (inv_pos.2 hδ).le
  have h2 : (∫ x, carre F (fun y => w' y + w y) (fun y => w' y + w y) x ∂μ) / δ⁻¹ ≤
      (2 * A * (2 * B) * μ.real univ) / δ⁻¹ :=
    div_le_div_of_nonneg_right eS (inv_pos.2 hδ).le
  have h3 : δ⁻¹ * (a * δ * (b * δ) * μ.real univ) = a * b * μ.real univ * δ := by
    field_simp
  have h4 : (2 * A * (2 * B) * μ.real univ) / δ⁻¹ = 4 * A * B * μ.real univ * δ := by
    field_simp; ring
  rw [h3] at h1; rw [h4] at h2
  nlinarith

include hIBP hReg hC in
/-- `L¹` derivative estimate for `h ↦ Γ(w_h)`. -/
theorem integral_abs_carre_deriv_le {w1 w0 D : M → ℝ} {h : ℝ} (hh : h ≠ 0) (h1 : MSmooth F w1)
    (h0 : MSmooth F w0) (hD : MSmooth F D) {aR bR A' B' E0 : ℝ}
    (hR : ∀ x, |h⁻¹ * (w1 x - w0 x) - D x| ≤ aR)
    (hLR : ∀ x, |mgenerator F V (fun y => h⁻¹ * (w1 y - w0 y) - D y) x| ≤ bR)
    (hδ : ∀ x, |h⁻¹ * (w1 x - w0 x)| ≤ A')
    (hLδ : ∀ x, |mgenerator F V (fun y => h⁻¹ * (w1 y - w0 y)) x| ≤ B')
    (hG0 : Integrable (fun x => carre F w0 w0 x) μ) (hE0 : ∫ x, carre F w0 w0 x ∂μ ≤ E0) :
    ∫ x, |(carre F w1 w1 x - carre F w0 w0 x) / h - 2 * carre F D w0 x| ∂μ ≤
      aR * bR * μ.real univ / |h| + |h| * (E0 + A' * B' * μ.real univ) := by
  have hRs : MSmooth F (fun y => h⁻¹ * (w1 y - w0 y) - D y) := (msmooth_dq F h h1 h0).sub hD
  have hδs : MSmooth F (fun y => h⁻¹ * (w1 y - w0 y)) := msmooth_dq F h h1 h0
  obtain ⟨iR, eR⟩ := energy_bound F hIBP hReg hC (V := V) (μ := μ) hRs hR hLR
  obtain ⟨iδ, eδ⟩ := energy_bound F hIBP hReg hC (V := V) (μ := μ) hδs hδ hLδ
  have hl : 0 < |h|⁻¹ := inv_pos.2 (abs_pos.2 hh)
  obtain ⟨iRc, eRc⟩ := integral_abs_carre_le F hRs h0 iR hG0 hl
  have hm : 0 ≤ μ.real univ := measureReal_nonneg
  have hpt : ∀ x, |(carre F w1 w1 x - carre F w0 w0 x) / h - 2 * carre F D w0 x| ≤
      2 * |carre F (fun y => h⁻¹ * (w1 y - w0 y) - D y) w0 x| +
        |h| * carre F (fun y => h⁻¹ * (w1 y - w0 y)) (fun y => h⁻¹ * (w1 y - w0 y)) x := by
    intro x
    rw [carre_deriv_identity F hh h1 h0 hD x]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (carre_nonneg F _ x)]
    norm_num
  have hI1 : Integrable (fun x => 2 * |carre F (fun y => h⁻¹ * (w1 y - w0 y) - D y) w0 x|) μ :=
    iRc.abs.const_mul 2
  have hI2 : Integrable (fun x => |h| * carre F (fun y => h⁻¹ * (w1 y - w0 y))
      (fun y => h⁻¹ * (w1 y - w0 y)) x) μ := iδ.const_mul _
  have hmeas : AEStronglyMeasurable (fun x => (carre F w1 w1 x - carre F w0 w0 x) / h
      - 2 * carre F D w0 x) μ := by
    have c1 := continuous_carre F h1 h1
    have c0 := continuous_carre F h0 h0
    have cD := continuous_carre F hD h0
    exact (((c1.sub c0).div_const h).sub (continuous_const.mul cD)).aestronglyMeasurable
  have hint : Integrable (fun x => |(carre F w1 w1 x - carre F w0 w0 x) / h
      - 2 * carre F D w0 x|) μ :=
    Integrable.mono' (hI1.add hI2) hmeas.norm
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_abs]; exact hpt x)
  calc _ ≤ ∫ x, (2 * |carre F (fun y => h⁻¹ * (w1 y - w0 y) - D y) w0 x| +
        |h| * carre F (fun y => h⁻¹ * (w1 y - w0 y)) (fun y => h⁻¹ * (w1 y - w0 y)) x) ∂μ :=
        integral_mono hint (hI1.add hI2) hpt
    _ = 2 * ∫ x, |carre F (fun y => h⁻¹ * (w1 y - w0 y) - D y) w0 x| ∂μ +
        |h| * ∫ x, carre F (fun y => h⁻¹ * (w1 y - w0 y)) (fun y => h⁻¹ * (w1 y - w0 y)) x ∂μ := by
        rw [integral_add hI1 hI2, integral_const_mul, integral_const_mul]
    _ ≤ _ := by
        have e1 : |h|⁻¹ * (∫ x, carre F (fun y => h⁻¹ * (w1 y - w0 y) - D y)
            (fun y => h⁻¹ * (w1 y - w0 y) - D y) x ∂μ) ≤ |h|⁻¹ * (aR * bR * μ.real univ) :=
          mul_le_mul_of_nonneg_left eR hl.le
        have e2 : (∫ x, carre F w0 w0 x ∂μ) / |h|⁻¹ ≤ E0 / |h|⁻¹ :=
          div_le_div_of_nonneg_right hE0 hl.le
        have e3 : |h| * ∫ x, carre F (fun y => h⁻¹ * (w1 y - w0 y))
            (fun y => h⁻¹ * (w1 y - w0 y)) x ∂μ ≤ |h| * (A' * B' * μ.real univ) :=
          mul_le_mul_of_nonneg_left eδ (abs_nonneg _)
        have e4 : E0 / |h|⁻¹ = E0 * |h| := by rw [div_inv_eq_mul]
        have e5 : |h|⁻¹ * (aR * bR * μ.real univ) = aR * bR * μ.real univ / |h| := by
          rw [inv_mul_eq_div]
        rw [e4] at e2; rw [e5] at e1
        nlinarith

end Energy

end CutoffRigidity.Riemann.Diff
