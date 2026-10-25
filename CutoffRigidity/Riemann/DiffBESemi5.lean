module

public import CutoffRigidity.Riemann.DiffBESemi4

/-! # `L¹` estimates for `Γ(K_τ f)` and `√(Γ(K_τ f) + ε)`; Lipschitz continuity of `A`
(workstream BE, part C)
-/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set
open scoped Manifold ContDiff ENNReal NNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

theorem abs_sqrt_sub_le {ε : ℝ} (hε : 0 < ε) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.sqrt (a + ε) - Real.sqrt (b + ε)| ≤ |a - b| / (2 * Real.sqrt ε) := by
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have h1 : Real.sqrt ε ≤ Real.sqrt (a + ε) := Real.sqrt_le_sqrt (by linarith)
  have h2 : Real.sqrt ε ≤ Real.sqrt (b + ε) := Real.sqrt_le_sqrt (by linarith)
  have e : (Real.sqrt (a + ε) - Real.sqrt (b + ε)) * (Real.sqrt (a + ε) + Real.sqrt (b + ε)) = a - b := by
    have := Real.sq_sqrt (show 0 ≤ a + ε by linarith)
    have := Real.sq_sqrt (show 0 ≤ b + ε by linarith)
    nlinarith
  rw [le_div_iff₀ (by positivity)]
  have : |a - b| = |Real.sqrt (a + ε) - Real.sqrt (b + ε)| * (Real.sqrt (a + ε) + Real.sqrt (b + ε)) := by
    rw [← e, abs_mul, abs_of_pos (by linarith : 0 < Real.sqrt (a + ε) + Real.sqrt (b + ε))]
  rw [this]
  exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)

theorem sqrt_le_self_add (y : ℝ) (hy : 0 ≤ y) : Real.sqrt y ≤ y + 1 := by
  rw [Real.sqrt_le_iff]
  constructor
  · linarith
  · nlinarith

/-- abstract product estimate. -/
theorem abs_integral_mul_sub_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {P' P u' u : α → ℝ} (hP' : AEStronglyMeasurable P' μ) (hP : AEStronglyMeasurable P μ)
    {a b Cu : ℝ} (ha0 : 0 ≤ a) (ha : ∀ x, |P' x - P x| ≤ a) (hb : ∀ x, |P x| ≤ b)
    (hb' : ∀ x, |P' x| ≤ b)
    (hu' : Integrable u' μ) (hu : Integrable u μ) (hu'0 : ∀ x, 0 ≤ u' x)
    (hCu : ∫ x, u' x ∂μ ≤ Cu) :
    |∫ x, P' x * u' x ∂μ - ∫ x, P x * u x ∂μ| ≤ a * Cu + b * ∫ x, |u' x - u x| ∂μ := by
  have i1 : Integrable (fun x => P' x * u' x) μ := hu'.bdd_mul hP' (Filter.Eventually.of_forall hb')
  have i2 : Integrable (fun x => P x * u x) μ := hu.bdd_mul hP (Filter.Eventually.of_forall hb)
  have i3 : Integrable (fun x => (P' x - P x) * u' x) μ :=
    hu'.bdd_mul (hP'.sub hP) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact ha x)
  have i4 : Integrable (fun x => P x * (u' x - u x)) μ :=
    (hu'.sub hu).bdd_mul hP (Filter.Eventually.of_forall hb) |>.congr
      (Filter.Eventually.of_forall fun x => by simp)
  have e : ∫ x, P' x * u' x ∂μ - ∫ x, P x * u x ∂μ =
      ∫ x, (P' x - P x) * u' x ∂μ + ∫ x, P x * (u' x - u x) ∂μ := by
    rw [← integral_add i3 i4, ← integral_sub i1 i2]
    congr 1; funext x; ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · have : ‖∫ x, (P' x - P x) * u' x ∂μ‖ ≤ ∫ x, ‖(P' x - P x) * u' x‖ ∂μ := norm_integral_le_integral_norm _
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    calc ∫ x, ‖(P' x - P x) * u' x‖ ∂μ ≤ ∫ x, a * u' x ∂μ :=
          integral_mono i3.norm (hu'.const_mul a) fun x => by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hu'0 x)]
            exact mul_le_mul_of_nonneg_right (ha x) (hu'0 x)
      _ = a * ∫ x, u' x ∂μ := integral_const_mul _ _
      _ ≤ a * Cu := by
          exact mul_le_mul_of_nonneg_left hCu ha0
  · have : ‖∫ x, P x * (u' x - u x) ∂μ‖ ≤ ∫ x, ‖P x * (u' x - u x)‖ ∂μ := norm_integral_le_integral_norm _
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    calc ∫ x, ‖P x * (u' x - u x)‖ ∂μ ≤ ∫ x, b * |u' x - u x| ∂μ :=
          integral_mono i4.norm ((hu'.sub hu).abs.const_mul b) fun x => by
            rw [Real.norm_eq_abs, abs_mul]
            exact mul_le_mul_of_nonneg_right (hb x) (abs_nonneg _)
      _ = _ := integral_const_mul _ _

section Path5

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} {μ : Measure M} [IsFiniteMeasure μ] {Kk : ℝ≥0 → Kernel M M}
  (hIBP : WeightedIBP F μ V) (hReg : WeightedRegular F V) (hC : WeightedCutoffs F M)

include hIBP hReg hC in
theorem G_integrable (hK : KerCanonical F V μ Kk) {f : M → ℝ} (hf : MSmooth F f)
    (hfc : HasCompactSupport f) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ τ : ℝ,
      Integrable (fun x => carre F (semi Kk τ.toNNReal f) (semi Kk τ.toNNReal f) x) μ ∧
      ∫ x, carre F (semi Kk τ.toNNReal f) (semi Kk τ.toNNReal f) x ∂μ ≤ Cf * Cf * μ.real univ := by
  obtain ⟨C, hC0, hCb⟩ := bdd_semi F hK hf hfc
  exact ⟨C, hC0, fun τ => energy_bound F hIBP hReg hC (smooth_semi F hK hf hfc _)
    (fun x => (hCb _ x).1) (fun x => (hCb _ x).2)⟩

include hIBP hReg hC in
theorem G_lip (hK : KerCanonical F V μ Kk) (hV : MSmooth F V) {f : M → ℝ} (hf : MSmooth F f)
    (hfc : HasCompactSupport f) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ τ τ' : ℝ,
      ∫ x, |carre F (semi Kk τ'.toNNReal f) (semi Kk τ'.toNNReal f) x -
        carre F (semi Kk τ.toNNReal f) (semi Kk τ.toNNReal f) x| ∂μ ≤ c * |τ' - τ| := by
  obtain ⟨C, hC0, hCb⟩ := bdd_semi F hK hf hfc
  have hLf := msmooth_mgenerator F hV hf
  have hLfc := hasCompactSupport_mgenerator F V hf hfc
  obtain ⟨C1, hC10, hC1⟩ := semi_lip F hK hV hf hfc
  obtain ⟨C2, hC20, hC2⟩ := semi_lip F hK hV hLf hLfc
  have hm : 0 ≤ μ.real univ := measureReal_nonneg
  refine ⟨(C1 * C2 + 4 * C * C) * μ.real univ / 2, by positivity, fun τ τ' => ?_⟩
  by_cases hd : τ' = τ
  · subst hd; simp
  have hδ : 0 < |τ' - τ| := abs_pos.2 (sub_ne_zero.2 hd)
  have := integral_abs_carre_sub_le F hIBP hReg hC (V := V) (μ := μ)
    (smooth_semi F hK hf hfc τ.toNNReal) (smooth_semi F hK hf hfc τ'.toNNReal)
    (A := C) (B := C) (a := C1) (b := C2) hδ
    (fun x => (hCb _ x).1) (fun x => (hCb _ x).1) (fun x => (hCb _ x).2) (fun x => (hCb _ x).2)
    (fun x => hC1 x τ' τ)
    (fun x => by
      rw [gen_semi F hK hf hfc, gen_semi F hK hf hfc]; exact hC2 x τ' τ)
  refine this.trans (le_of_eq ?_)
  ring

include hIBP hReg hC in
theorem u_integrable (hK : KerCanonical F V μ Kk) {f : M → ℝ} (hf : MSmooth F f)
    (hfc : HasCompactSupport f) {ε : ℝ} (hε : 0 < ε) :
    ∃ Cu : ℝ, ∀ τ : ℝ,
      Integrable (fun x => Real.sqrt (carre F (semi Kk τ.toNNReal f) (semi Kk τ.toNNReal f) x + ε)) μ ∧
      ∫ x, Real.sqrt (carre F (semi Kk τ.toNNReal f) (semi Kk τ.toNNReal f) x + ε) ∂μ ≤ Cu := by
  obtain ⟨Cf, hCf0, hG⟩ := G_integrable F hIBP hReg hC hK hf hfc
  refine ⟨Cf * Cf * μ.real univ + (ε + 1) * μ.real univ, fun τ => ?_⟩
  obtain ⟨hi, hb⟩ := hG τ
  have hw := smooth_semi F hK hf hfc τ.toNNReal
  have hbd : Integrable (fun x => carre F (semi Kk τ.toNNReal f) (semi Kk τ.toNNReal f) x + (ε + 1)) μ :=
    hi.add (integrable_const _)
  have hle : ∀ x, Real.sqrt (carre F (semi Kk τ.toNNReal f) (semi Kk τ.toNNReal f) x + ε) ≤
      carre F (semi Kk τ.toNNReal f) (semi Kk τ.toNNReal f) x + (ε + 1) := fun x => by
    have := sqrt_le_self_add (carre F (semi Kk τ.toNNReal f) (semi Kk τ.toNNReal f) x + ε)
      (by linarith [carre_nonneg F (semi Kk τ.toNNReal f) x])
    linarith
  have hmeas : AEStronglyMeasurable (fun x => Real.sqrt (carre F (semi Kk τ.toNNReal f)
      (semi Kk τ.toNNReal f) x + ε)) μ :=
    ((continuous_carre F hw hw).add_const ε).sqrt.aestronglyMeasurable
  have hint : Integrable (fun x => Real.sqrt (carre F (semi Kk τ.toNNReal f)
      (semi Kk τ.toNNReal f) x + ε)) μ :=
    Integrable.mono' hbd hmeas (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]; exact hle x)
  refine ⟨hint, ?_⟩
  calc _ ≤ ∫ x, (carre F (semi Kk τ.toNNReal f) (semi Kk τ.toNNReal f) x + (ε + 1)) ∂μ :=
        integral_mono hint hbd hle
    _ ≤ _ := by
        rw [integral_add hi (integrable_const _)]
        simp only [integral_const, smul_eq_mul]
        have e : μ.real univ * (ε + 1) = (ε + 1) * μ.real univ := mul_comm _ _
        linarith

include hIBP hReg hC in
theorem u_lip (hK : KerCanonical F V μ Kk) (hV : MSmooth F V) {f : M → ℝ} (hf : MSmooth F f)
    (hfc : HasCompactSupport f) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ τ τ' : ℝ,
      ∫ x, |Real.sqrt (carre F (semi Kk τ'.toNNReal f) (semi Kk τ'.toNNReal f) x + ε) -
        Real.sqrt (carre F (semi Kk τ.toNNReal f) (semi Kk τ.toNNReal f) x + ε)| ∂μ ≤
        c * |τ' - τ| := by
  obtain ⟨c, hc0, hc⟩ := G_lip F hIBP hReg hC hK hV hf hfc
  obtain ⟨Cf, hCf0, hG⟩ := G_integrable F hIBP hReg hC hK hf hfc
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  refine ⟨c / (2 * Real.sqrt ε), by positivity, fun τ τ' => ?_⟩
  have hw := smooth_semi F hK hf hfc τ.toNNReal
  have hw' := smooth_semi F hK hf hfc τ'.toNNReal
  have iu := u_integrable F hIBP hReg hC hK hf hfc hε
  obtain ⟨Cu, hCu⟩ := iu
  have hi' := (hCu τ').1
  have hi := (hCu τ).1
  have hGi := (hG τ).1
  have hGi' := (hG τ').1
  calc _ ≤ ∫ x, |carre F (semi Kk τ'.toNNReal f) (semi Kk τ'.toNNReal f) x -
        carre F (semi Kk τ.toNNReal f) (semi Kk τ.toNNReal f) x| / (2 * Real.sqrt ε) ∂μ :=
        integral_mono (hi'.sub hi).abs ((hGi'.sub hGi).abs.div_const _) fun x =>
          abs_sqrt_sub_le hε (carre_nonneg F _ x) (carre_nonneg F _ x)
    _ = (∫ x, |carre F (semi Kk τ'.toNNReal f) (semi Kk τ'.toNNReal f) x -
        carre F (semi Kk τ.toNNReal f) (semi Kk τ.toNNReal f) x| ∂μ) / (2 * Real.sqrt ε) :=
        integral_div _ _
    _ ≤ (c * |τ' - τ|) / (2 * Real.sqrt ε) :=
        div_le_div_of_nonneg_right (hc τ τ') (by positivity)
    _ = _ := by ring

include hIBP hReg hC in
/-- `A` is globally Lipschitz. -/
theorem Afun_lip (hK : KerCanonical F V μ Kk) (hV : MSmooth F V) {f ζ : M → ℝ} (hf : MSmooth F f)
    (hfc : HasCompactSupport f) (hζ : MSmooth F ζ) (hζc : HasCompactSupport ζ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (t s s' : ℝ),
      |∫ x, semi Kk s'.toNNReal ζ x *
          Real.sqrt (carre F (semi Kk (t - s').toNNReal f) (semi Kk (t - s').toNNReal f) x + ε) ∂μ -
        ∫ x, semi Kk s.toNNReal ζ x *
          Real.sqrt (carre F (semi Kk (t - s).toNNReal f) (semi Kk (t - s).toNNReal f) x + ε) ∂μ|
        ≤ K * |s' - s| := by
  obtain ⟨Cu, hCu⟩ := u_integrable F hIBP hReg hC hK hf hfc hε
  obtain ⟨c, hc0, hc⟩ := u_lip F hIBP hReg hC hK hV hf hfc hε
  obtain ⟨Cz, hCz0, hCz⟩ := semi_lip F hK hV hζ hζc
  obtain ⟨Cb, hCb0, hCb⟩ := bdd_semi F hK hζ hζc
  have hCu0 : 0 ≤ Cu := by
    refine le_trans (integral_nonneg fun x => Real.sqrt_nonneg _) (hCu 0).2
  refine ⟨Cz * Cu + Cb * c, by positivity, fun t s s' => ?_⟩
  have hP' := (smooth_semi F hK hζ hζc s'.toNNReal).continuous.aestronglyMeasurable (μ := μ)
  have hP := (smooth_semi F hK hζ hζc s.toNNReal).continuous.aestronglyMeasurable (μ := μ)
  have key := abs_integral_mul_sub_le (μ := μ) hP' hP (a := Cz * |s' - s|) (b := Cb) (Cu := Cu)
    (u' := fun x => Real.sqrt (carre F (semi Kk (t - s').toNNReal f) (semi Kk (t - s').toNNReal f) x + ε))
    (u := fun x => Real.sqrt (carre F (semi Kk (t - s).toNNReal f) (semi Kk (t - s).toNNReal f) x + ε))
    (by positivity) (fun x => hCz x s' s) (fun x => (hCb _ x).1) (fun x => (hCb _ x).1)
    (hCu (t - s')).1 (hCu (t - s)).1 (fun x => Real.sqrt_nonneg _) (hCu (t - s')).2
  have hl := hc (t - s) (t - s')
  have : |t - s' - (t - s)| = |s' - s| := by rw [← abs_neg]; congr 1; ring
  rw [this] at hl
  refine key.trans ?_
  nlinarith [mul_nonneg hCb0 hc0, abs_nonneg (s' - s), mul_le_mul_of_nonneg_left hl hCb0]

include hIBP hReg hC in
theorem q_integrable (hK : KerCanonical F V μ Kk) (hV : MSmooth F V) {f : M → ℝ} (hf : MSmooth F f)
    (hfc : HasCompactSupport f) (τ : ℝ) :
    Integrable (fun x => carre F (fun y => -1 * mgenerator F V (semi Kk τ.toNNReal f) y)
      (semi Kk τ.toNNReal f) x) μ := by
  have hLf := msmooth_mgenerator F hV hf
  have hLfc := hasCompactSupport_mgenerator F V hf hfc
  obtain ⟨CL, hCL0, hCL⟩ := bdd_semi F hK hLf hLfc
  obtain ⟨Cf', hCf'0, hCf'⟩ := bdd_semi F hK hf hfc
  obtain ⟨Cf, hCf0, hG⟩ := G_integrable F hIBP hReg hC hK hf hfc
  have hw0 := smooth_semi F hK hf hfc τ.toNNReal
  have hLw0 : MSmooth F (mgenerator F V (semi Kk τ.toNNReal f)) := msmooth_mgenerator F hV hw0
  have hD : MSmooth F (fun y => -1 * mgenerator F V (semi Kk τ.toNNReal f) y) :=
    contMDiff_const.mul hLw0
  obtain ⟨hGD, -⟩ := energy_bound F hIBP hReg hC (V := V) (μ := μ) hD (A := Cf') (B := CL)
    (fun x => by rw [abs_mul]; simpa using (hCf' _ x).2)
    (fun x => by
      rw [mgenerator_const_mul F (-1) hLw0, gen_semi F hK hf hfc, abs_mul]
      simpa using (hCL _ x).2)
  exact (integral_abs_carre_le F hD hw0 hGD (hG τ).1 one_pos).1

include hIBP hReg hC in
theorem G_deriv_bound (hK : KerCanonical F V μ Kk) (hV : MSmooth F V) {f : M → ℝ}
    (hf : MSmooth F f) (hfc : HasCompactSupport f) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (τ0 τ1 h : ℝ), 0 < τ0 → 0 < τ1 → h ≠ 0 → τ1 - τ0 = -h →
      ∫ x, |(carre F (semi Kk τ1.toNNReal f) (semi Kk τ1.toNNReal f) x -
          carre F (semi Kk τ0.toNNReal f) (semi Kk τ0.toNNReal f) x) / h -
        2 * carre F (fun y => -1 * mgenerator F V (semi Kk τ0.toNNReal f) y)
          (semi Kk τ0.toNNReal f) x| ∂μ ≤ K * |h| := by
  obtain ⟨CR, hCR0, hR⟩ := remainder_bounds F hK hV hf hfc
  obtain ⟨Cf, hCf0, hG⟩ := G_integrable F hIBP hReg hC hK hf hfc
  have hm : 0 ≤ μ.real univ := measureReal_nonneg
  refine ⟨CR * CR * μ.real univ + (Cf * Cf * μ.real univ + CR * CR * μ.real univ), by positivity,
    fun τ0 τ1 h h0 h1 hh hτ => ?_⟩
  have hw0 := smooth_semi F hK hf hfc τ0.toNNReal
  have hw1 := smooth_semi F hK hf hfc τ1.toNNReal
  have hLw0 : MSmooth F (mgenerator F V (semi Kk τ0.toNNReal f)) := msmooth_mgenerator F hV hw0
  have hD : MSmooth F (fun y => -1 * mgenerator F V (semi Kk τ0.toNNReal f) y) :=
    contMDiff_const.mul hLw0
  obtain ⟨b1, b2, b3, b4⟩ := hR τ0 τ1 h h0 h1 hh hτ
  have key := integral_abs_carre_deriv_le F hIBP hReg hC (V := V) (μ := μ) hh hw1 hw0 hD
    (aR := CR * |h|) (bR := CR * |h|) (A' := CR) (B' := CR) (E0 := Cf * Cf * μ.real univ)
    b1 b2 b3 b4 (hG τ0).1 (hG τ0).2
  refine key.trans (le_of_eq ?_)
  have hpos : |h| ≠ 0 := (abs_pos.2 hh).ne'
  field_simp

end Path5

end CutoffRigidity.Riemann.Diff
