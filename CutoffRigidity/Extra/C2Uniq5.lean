module

public import CutoffRigidity.Extra.C2Uniq4
public import CutoffRigidity.Riemann.DiffDynkinBounded

/-! # `C²` uniqueness, stage 4b: calculus of the resolvent `U_λ` and the generator of a product -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutCur

open MeasureTheory ProbabilityTheory Filter Topology Set
open Bundle
open scoped ENNReal NNReal ContDiff Manifold

namespace C2U

variable {d : ℕ}

/-- Generator of a product (flat space). -/
theorem generator_mul (V : Rd d → ℝ) {χ f : Rd d → ℝ} (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f)
    (y : Rd d) :
    generator V (fun z => χ z * f z) y =
      χ y * generator V f y + f y * generator V χ y + 2 * inner ℝ (gradient χ y) (gradient f y) := by
  have hχ' : ContMDiff 𝓘(ℝ, Rd d) 𝓘(ℝ, ℝ) ∞ χ := contMDiff_iff_contDiff.2 hχ
  have hf' : ContMDiff 𝓘(ℝ, Rd d) 𝓘(ℝ, ℝ) ∞ f := contMDiff_iff_contDiff.2 hf
  have h := CutoffRigidity.Riemann.Diff.mgenerator_mul (Rd d) (V := V) hχ' hf' y
  have hm : ContDiff ℝ ∞ (fun z => χ z * f z) := hχ.mul hf
  rw [CutoffRigidity.Riemann.Witness.mgenerator_rd (hm.of_le (by norm_cast)),
    CutoffRigidity.Riemann.Witness.mgenerator_rd (hf.of_le (by norm_cast)),
    CutoffRigidity.Riemann.Witness.mgenerator_rd (hχ.of_le (by norm_cast)),
    CutoffRigidity.Riemann.Witness.carre_rd] at h
  rw [generator_eq_langevinOp (hm.of_le (by norm_cast)), generator_eq_langevinOp (hf.of_le (by norm_cast)),
    generator_eq_langevinOp (hχ.of_le (by norm_cast))]
  exact h


section U

variable {V : Rd d → ℝ} {P : ℝ≥0 → Kernel (Rd d) (Rd d)}

theorem integral_exp_mul_const (lam c : ℝ) (hlam : 0 < lam) :
    ∫ s in Ioi (0 : ℝ), Real.exp (-lam * s) * c = c / lam := by
  rw [integral_mul_const, integral_exp_mul_Ioi (a := -lam) (by linarith)]
  simp only [mul_zero, Real.exp_zero]
  field_simp

theorem integrableOn_exp_mul_const (lam c : ℝ) (hlam : 0 < lam) :
    IntegrableOn (fun s : ℝ => Real.exp (-lam * s) * c) (Ioi (0 : ℝ)) :=
  (integrableOn_exp_mul_Ioi (a := -lam) (by linarith) 0).mul_const c

theorem integrable_cs' {h : Rd d → ℝ} (hh : Continuous h) (hhc : HasCompactSupport h)
    (μ : Measure (Rd d)) [IsFiniteMeasure μ] : Integrable h μ :=
  hh.integrable_of_hasCompactSupport hhc

theorem resU_add (hP : IsEuclideanDiffusion V P) (hV : ContDiff ℝ 1 V) {h1 h2 : Rd d → ℝ}
    (c1 : Continuous h1) (s1 : HasCompactSupport h1) (c2 : Continuous h2) (s2 : HasCompactSupport h2)
    {lam : ℝ} (hlam : 0 < lam) (x : Rd d) :
    resU P lam (fun y => h1 y + h2 y) x = resU P lam h1 x + resU P lam h2 x := by
  unfold resU
  rw [← integral_add (resU_integrableOn hP hV c1 s1 hlam x) (resU_integrableOn hP hV c2 s2 hlam x)]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  haveI : IsProbabilityMeasure (P s.toNNReal x) := (hP.1 _).isProbabilityMeasure x
  simp only
  rw [integral_add (integrable_cs' c1 s1 _) (integrable_cs' c2 s2 _), mul_add]

theorem resU_smul (c : ℝ) (h : Rd d → ℝ) (lam : ℝ) (x : Rd d) :
    resU P lam (fun y => c * h y) x = c * resU P lam h x := by
  unfold resU
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only
  rw [integral_const_mul]; ring

theorem resU_ge (hP : IsEuclideanDiffusion V P) (hV : ContDiff ℝ 1 V) {h : Rd d → ℝ}
    (hc : Continuous h) (hs : HasCompactSupport h) {a : ℝ} (ha : ∀ y, a ≤ h y) {lam : ℝ}
    (hlam : 0 < lam) (x : Rd d) : a / lam ≤ resU P lam h x := by
  rw [← integral_exp_mul_const lam a hlam]
  refine setIntegral_mono_on (integrableOn_exp_mul_const lam a hlam)
    (resU_integrableOn hP hV hc hs hlam x) measurableSet_Ioi fun s _ => ?_
  haveI : IsProbabilityMeasure (P s.toNNReal x) := (hP.1 _).isProbabilityMeasure x
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have := integral_mono (integrable_const a) (integrable_cs' hc hs (P s.toNNReal x)) (fun y => ha y)
  simpa using this

theorem resU_le (hP : IsEuclideanDiffusion V P) (hV : ContDiff ℝ 1 V) {h : Rd d → ℝ}
    (hc : Continuous h) (hs : HasCompactSupport h) {b : ℝ} (hb : ∀ y, h y ≤ b) {lam : ℝ}
    (hlam : 0 < lam) (x : Rd d) : resU P lam h x ≤ b / lam := by
  rw [← integral_exp_mul_const lam b hlam]
  refine setIntegral_mono_on (resU_integrableOn hP hV hc hs hlam x)
    (integrableOn_exp_mul_const lam b hlam) measurableSet_Ioi fun s _ => ?_
  haveI : IsProbabilityMeasure (P s.toNNReal x) := (hP.1 _).isProbabilityMeasure x
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have := integral_mono (integrable_cs' hc hs (P s.toNNReal x)) (integrable_const b) (fun y => hb y)
  simpa using this


end U

section Deriv

variable {V W g : Rd d → ℝ} {P : ℝ≥0 → Kernel (Rd d) (Rd d)} {w : ℝ≥0 → Rd d → ℝ} {K G C : ℝ}
  {χ : Rd d → ℝ}

theorem IsBackward.continuous_w (hb : IsBackward W g w K G C) (τ : ℝ≥0) : Continuous (w τ) :=
  (hb.smooth τ).continuous

theorem IsBackward.continuous_gen (hb : IsBackward W g w K G C) (hW1 : ContDiff ℝ 1 W) (τ : ℝ≥0) :
    Continuous (generator W (w τ)) :=
  continuous_generator hW1 ((hb.smooth τ).of_le (by norm_cast))

/-- The tau-derivative of `U_λ(χ w_τ)` is `U_λ(χ 𝓛_W w_τ)`. -/
theorem hasDerivAt_resU_w (hP : IsEuclideanDiffusion V P) (hV : ContDiff ℝ 1 V)
    (hW1 : ContDiff ℝ 1 W) (hb : IsBackward W g w K G C) (hχ : Continuous χ)
    (hχc : HasCompactSupport χ) (hχ01 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) {lam : ℝ} (hlam : 0 < lam)
    (x : Rd d) {s₀ : ℝ} (hs₀ : 0 < s₀) :
    HasDerivAt (fun s : ℝ => resU P lam (fun y => χ y * w s.toNNReal y) x)
      (resU P lam (fun y => χ y * generator W (w s₀.toNNReal) y) x) s₀ := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hb.gen_bound 0 0)
  -- the inner derivative
  have hinner : ∀ (t : ℝ) (s : ℝ), 0 < s →
      HasDerivAt (fun r : ℝ => ∫ y, χ y * w r.toNNReal y ∂P t.toNNReal x)
        (∫ y, χ y * generator W (w s.toNNReal) y ∂P t.toNNReal x) s := by
    intro t s hs
    haveI : IsProbabilityMeasure (P t.toNNReal x) := (hP.1 _).isProbabilityMeasure x
    have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P t.toNNReal x)
      (F := fun (r : ℝ) (y : Rd d) => χ y * w r.toNNReal y)
      (F' := fun (r : ℝ) (y : Rd d) => χ y * generator W (w r.toNNReal) y)
      (x₀ := s) (bound := fun _ => C) (Ioi_mem_nhds hs)
      (Eventually.of_forall fun r => (hχ.mul (hb.continuous_w _)).aestronglyMeasurable)
      (integrable_cs' (hχ.mul (hb.continuous_w _)) (hχc.mul_right) _)
      ((hχ.mul (hb.continuous_gen hW1 _)).aestronglyMeasurable)
      (Eventually.of_forall fun y r hr => by
        rw [Real.norm_eq_abs, abs_mul]
        have h1 : |χ y| ≤ 1 := by rw [abs_of_nonneg (hχ01 y).1]; exact (hχ01 y).2
        calc |χ y| * |generator W (w r.toNNReal) y| ≤ 1 * C :=
              mul_le_mul h1 (hb.gen_bound _ _) (abs_nonneg _) zero_le_one
          _ = C := one_mul C)
      (integrable_const C)
      (Eventually.of_forall fun y r hr => (hb.deriv r hr y).const_mul (χ y))
    exact this.2
  -- the outer derivative
  have hmeas : ∀ (τ : ℝ), AEStronglyMeasurable
      (fun t : ℝ => Real.exp (-lam * t) * ∫ y, χ y * w τ.toNNReal y ∂P t.toNNReal x)
      (volume.restrict (Ioi (0 : ℝ))) := fun τ =>
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (continuous_semi_cs_real hP hV (hχ.mul (hb.continuous_w _)) (hχc.mul_right) x)).aestronglyMeasurable
  have hmeas' : ∀ (τ : ℝ), AEStronglyMeasurable
      (fun t : ℝ => Real.exp (-lam * t) * ∫ y, χ y * generator W (w τ.toNNReal) y ∂P t.toNNReal x)
      (volume.restrict (Ioi (0 : ℝ))) := fun τ =>
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (continuous_semi_cs_real hP hV (hχ.mul (hb.continuous_gen hW1 _)) (hχc.mul_right) x)).aestronglyMeasurable
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (r : ℝ) (t : ℝ) =>
      Real.exp (-lam * t) * ∫ y, χ y * w r.toNNReal y ∂P t.toNNReal x)
    (F' := fun (r : ℝ) (t : ℝ) =>
      Real.exp (-lam * t) * ∫ y, χ y * generator W (w r.toNNReal) y ∂P t.toNNReal x)
    (x₀ := s₀) (bound := fun t => C * Real.exp (-lam * t)) (Ioi_mem_nhds hs₀)
    (Eventually.of_forall fun r => hmeas r)
    (resU_integrableOn hP hV (hχ.mul (hb.continuous_w _)) (hχc.mul_right) hlam x)
    (hmeas' s₀)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t _ r _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      exact abs_integral_le_of_bound hP (C := C) (fun y => by
        rw [abs_mul]
        have h1 : |χ y| ≤ 1 := by rw [abs_of_nonneg (hχ01 y).1]; exact (hχ01 y).2
        calc |χ y| * |generator W (w r.toNNReal) y| ≤ 1 * C :=
              mul_le_mul h1 (hb.gen_bound _ _) (abs_nonneg _) zero_le_one
          _ = C := one_mul C) _ x))
    ((integrableOn_exp_mul_Ioi (a := -lam) (by linarith) 0).const_mul C)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t _ r hr =>
      (hinner t r hr).const_mul _))
  exact this.2


theorem continuous_resU_w (hP : IsEuclideanDiffusion V P) (hV : ContDiff ℝ 1 V)
    (hb : IsBackward W g w K G C) (hχ : Continuous χ)
    (hχc : HasCompactSupport χ) (hχ01 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) {lam : ℝ} (hlam : 0 < lam)
    (x : Rd d) :
    Continuous (fun s : ℝ => resU P lam (fun y => χ y * w s.toNNReal y) x) := by
  have hbd : ∀ (s : ℝ) (y : Rd d), |χ y * w s.toNNReal y| ≤ K := by
    intro s y
    rw [abs_mul, abs_of_nonneg (hχ01 y).1, abs_of_nonneg (hb.nonneg _ _)]
    calc χ y * w s.toNNReal y ≤ 1 * K :=
          mul_le_mul (hχ01 y).2 (hb.le _ _) (hb.nonneg _ _) zero_le_one
      _ = K := one_mul K
  have hinner : ∀ t : ℝ, Continuous (fun s : ℝ => ∫ y, χ y * w s.toNNReal y ∂P t.toNNReal x) := by
    intro t
    haveI : IsProbabilityMeasure (P t.toNNReal x) := (hP.1 _).isProbabilityMeasure x
    refine continuous_of_dominated (bound := fun _ => K)
      (fun s => (hχ.mul (hb.continuous_w _)).aestronglyMeasurable) (fun s => ?_) (integrable_const K)
      (Eventually.of_forall fun y => continuous_const.mul (hb.cont y))
    exact Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hbd s y
  unfold resU
  refine continuous_of_dominated (bound := fun t => K * Real.exp (-lam * t))
    (fun s => ?_) (fun s => ?_) ((integrableOn_exp_mul_Ioi (a := -lam) (by linarith) 0).const_mul K)
    (Eventually.of_forall fun t => continuous_const.mul (hinner t))
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (continuous_semi_cs_real hP hV (hχ.mul (hb.continuous_w _)) (hχc.mul_right) x)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t _ => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_integral_le_of_bound hP (hbd s) _ x) (Real.exp_pos _).le


/-- Pointwise algebra: `𝓛_V(χ f) - χ 𝓛_W f` in terms of the commutator and cutoff terms. -/
theorem generator_mul_sub (V W : Rd d → ℝ) {χ f : Rd d → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hf : ContDiff ℝ ∞ f) (y : Rd d) :
    generator V (fun z => χ z * f z) y - χ y * generator W f y =
      χ y * inner ℝ (gradient W y - gradient V y) (gradient f y) + f y * laplacian χ y +
        2 * inner ℝ (gradient χ y) (gradient f y) - f y * inner ℝ (gradient V y) (gradient χ y) := by
  rw [generator_mul V hχ hf]
  unfold generator
  rw [inner_sub_left]
  ring

/-- The pointwise lower bound for the error term. -/
theorem error_lower {V W : Rd d → ℝ} {χ f : Rd d → ℝ} {K G A R δ : ℝ}
    (hf0 : ∀ y, 0 ≤ f y) (hfK : ∀ y, f y ≤ K) (hfG : ∀ y, ‖gradient f y‖ ≤ G)
    (hχ01 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (hgrad : ∀ y, ‖gradient χ y‖ ≤ A / R) (hlap : ∀ y, |laplacian χ y| ≤ A / R ^ 2)
    (hVχ : ∀ y, inner ℝ (gradient V y) (gradient χ y) ≤ A / R)
    (hδ : ∀ y, χ y ≠ 0 → ‖gradient V y - gradient W y‖ ≤ δ) (hδ0 : 0 ≤ δ)
    (hA1 : 0 ≤ A / R) (hA2 : 0 ≤ A / R ^ 2)
    (y : Rd d) :
    -(δ * G + K * (A / R ^ 2) + 2 * (A / R) * G + K * (A / R)) ≤
      χ y * inner ℝ (gradient W y - gradient V y) (gradient f y) + f y * laplacian χ y +
        2 * inner ℝ (gradient χ y) (gradient f y) - f y * inner ℝ (gradient V y) (gradient χ y) := by
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hfG y)
  have hK0 : 0 ≤ K := (hf0 y).trans (hfK y)
  -- term 1
  have t1 : -(δ * G) ≤ χ y * inner ℝ (gradient W y - gradient V y) (gradient f y) := by
    by_cases h : χ y = 0
    · rw [h]; simp; positivity
    · have h1 := hδ y h
      have h2 := abs_real_inner_le_norm (gradient W y - gradient V y) (gradient f y)
      rw [norm_sub_rev] at h2
      have h3 : ‖gradient V y - gradient W y‖ * ‖gradient f y‖ ≤ δ * G :=
        mul_le_mul h1 (hfG y) (norm_nonneg _) hδ0
      have h4 : |inner ℝ (gradient W y - gradient V y) (gradient f y)| ≤ δ * G := h2.trans h3
      have h5 : |χ y * inner ℝ (gradient W y - gradient V y) (gradient f y)| ≤ δ * G := by
        rw [abs_mul, abs_of_nonneg (hχ01 y).1]
        calc χ y * |inner ℝ (gradient W y - gradient V y) (gradient f y)|
            ≤ 1 * (δ * G) := mul_le_mul (hχ01 y).2 h4 (abs_nonneg _) zero_le_one
          _ = δ * G := one_mul _
      exact (neg_le_of_abs_le h5)
  -- term 2
  have t2 : -(K * (A / R ^ 2)) ≤ f y * laplacian χ y := by
    have h1 : |f y * laplacian χ y| ≤ K * (A / R ^ 2) := by
      rw [abs_mul, abs_of_nonneg (hf0 y)]
      exact mul_le_mul (hfK y) (hlap y) (abs_nonneg _) hK0
    exact neg_le_of_abs_le h1
  -- term 3
  have t3 : -(2 * (A / R) * G) ≤ 2 * inner ℝ (gradient χ y) (gradient f y) := by
    have h1 := abs_real_inner_le_norm (gradient χ y) (gradient f y)
    have h2 : ‖gradient χ y‖ * ‖gradient f y‖ ≤ (A / R) * G :=
      mul_le_mul (hgrad y) (hfG y) (norm_nonneg _) hA1
    have h3 := neg_le_of_abs_le (h1.trans h2)
    nlinarith
  -- term 4
  have t4 : -(K * (A / R)) ≤ -(f y * inner ℝ (gradient V y) (gradient χ y)) := by
    have h1 : f y * inner ℝ (gradient V y) (gradient χ y) ≤ f y * (A / R) :=
      mul_le_mul_of_nonneg_left (hVχ y) (hf0 y)
    have h2 : f y * (A / R) ≤ K * (A / R) := mul_le_mul_of_nonneg_right (hfK y) hA1
    linarith
  linarith


/-- **Core inequality** (one-sided comparison of the resolvent of `P` with the backward family
of the smooth approximant). -/
theorem core_upper
    (hP : IsEuclideanDiffusion V P) (hV : ContDiff ℝ 2 V) (hW : ContDiff ℝ ∞ W)
    (hb : IsBackward W g w K G C)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχ01 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    {A R δ : ℝ} (hgrad : ∀ y, ‖gradient χ y‖ ≤ A / R) (hlap : ∀ y, |laplacian χ y| ≤ A / R ^ 2)
    (hVχ : ∀ y, inner ℝ (gradient V y) (gradient χ y) ≤ A / R)
    (hδ : ∀ y, χ y ≠ 0 → ‖gradient V y - gradient W y‖ ≤ δ) (hδ0 : 0 ≤ δ)
    (hA1 : 0 ≤ A / R) (hA2 : 0 ≤ A / R ^ 2)
    {lam : ℝ} (hlam : 0 < lam) (x : Rd d) :
    χ x * (∫ s in Ioi (0 : ℝ), Real.exp (-lam * s) * w s.toNNReal x) ≤
      resU P lam (fun y => χ y * g y) x +
        (δ * G + K * (A / R ^ 2) + 2 * (A / R) * G + K * (A / R)) / lam ^ 2 := by
  have hV1 : ContDiff ℝ 1 V := hV.of_le (by norm_cast)
  have hW1 : ContDiff ℝ 1 W := hW.of_le (by norm_cast)
  have hχ0 : Continuous χ := hχ.continuous
  set Err : ℝ := δ * G + K * (A / R ^ 2) + 2 * (A / R) * G + K * (A / R) with hErr
  set f : ℝ → Rd d → ℝ := fun s y => χ y * w s.toNNReal y with hf
  have hfs : ∀ s, ContDiff ℝ ∞ (f s) := fun s => hχ.mul (hb.smooth _)
  have hfc : ∀ s, HasCompactSupport (f s) := fun s => hχc.mul_right
  have hfcont : ∀ s, Continuous (f s) := fun s => (hfs s).continuous
  have hLcont : ∀ s : ℝ, Continuous (fun y => χ y * generator W (w s.toNNReal) y) := fun s =>
    hχ0.mul (hb.continuous_gen hW1 _)
  have hLcs : ∀ s : ℝ, HasCompactSupport (fun y => χ y * generator W (w s.toNNReal) y) := fun s =>
    hχc.mul_right
  have hGen : ∀ s : ℝ, Continuous (generator V (f s)) := fun s =>
    continuous_generator hV1 ((hfs s).of_le (by norm_cast))
  have hGencs : ∀ s : ℝ, HasCompactSupport (generator V (f s)) := fun s => hasCompactSupport_generator (hfc s)
  set F : ℝ → ℝ := fun s => resU P lam (f s) x with hF
  set Hh : ℝ → ℝ := fun s => resU P lam (fun y => χ y * generator W (w s.toNNReal) y) x with hHh
  set Eh : ℝ → ℝ := fun s =>
    resU P lam (fun y => generator V (f s) y - χ y * generator W (w s.toNNReal) y) x with hEh
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hb.grad 0 0)
  have hK0 : 0 ≤ K := (hb.nonneg 0 0).trans (hb.le 0 0)
  -- lower bound for Eh
  have hE_lower : ∀ s : ℝ, -Err / lam ≤ Eh s := by
    intro s
    have := resU_ge hP hV1 (h := fun y => generator V (f s) y - χ y * generator W (w s.toNNReal) y)
      ((hGen s).sub (hLcont s)) ((hGencs s).sub (hLcs s)) (a := -Err) (fun y => by
        have h1 := generator_mul_sub V W hχ (hb.smooth s.toNNReal) y
        have h2 := error_lower (V := V) (W := W) (χ := χ) (f := w s.toNNReal) (K := K) (G := G)
          (A := A) (R := R) (δ := δ) (hb.nonneg _) (hb.le _) (hb.grad _) hχ01 hgrad hlap hVχ hδ hδ0 hA1 hA2 y
        simp only [hf]
        linarith) hlam x
    exact this
  -- the resolvent identity
  have hid : ∀ s : ℝ, lam * F s - Hh s - Eh s = χ x * w s.toNNReal x := by
    intro s
    have h1 := resU_dynkin hP hV1 hlam (hfs s) (hfc s) x
    have e1 : resU P lam (fun y => lam * f s y - generator V (f s) y) x =
        lam * F s - resU P lam (generator V (f s)) x := by
      have := resU_add hP hV1 (h1 := fun y => lam * f s y) (h2 := fun y => -1 * generator V (f s) y)
        ((continuous_const.mul (hfcont s))) ((hfc s).mul_left (f := fun _ => lam))
        (continuous_const.mul (hGen s)) ((hGencs s).mul_left (f := fun _ => -1)) hlam x
      have h3 := resU_smul (P := P) lam (f s) lam x
      have h4 := resU_smul (P := P) (-1) (generator V (f s)) lam x
      have e : (fun y => lam * f s y - generator V (f s) y) =
          fun y => lam * f s y + -1 * generator V (f s) y := by funext y; ring
      rw [e, this, h3, h4]; ring
    have e2 : resU P lam (generator V (f s)) x = Hh s + Eh s := by
      have := resU_add hP hV1 (h1 := fun y => χ y * generator W (w s.toNNReal) y)
        (h2 := fun y => generator V (f s) y - χ y * generator W (w s.toNNReal) y)
        (hLcont s) (hLcs s) ((hGen s).sub (hLcont s)) ((hGencs s).sub (hLcs s)) hlam x
      have e : (fun y => χ y * generator W (w s.toNNReal) y +
          (generator V (f s) y - χ y * generator W (w s.toNNReal) y)) = generator V (f s) := by
        funext y; ring
      rw [e] at this
      exact this
    rw [e1, e2] at h1
    simp only [hf] at h1
    linarith
  have hderivF : ∀ s : ℝ, 0 < s → HasDerivAt F (Hh s) s := fun s hs =>
    hasDerivAt_resU_w hP hV1 hW1 hb hχ0 hχc hχ01 hlam x hs
  have hcontF : Continuous F := continuous_resU_w hP hV1 hb hχ0 hχc hχ01 hlam x
  set φ : ℝ → ℝ := fun σ => Real.exp (-lam * σ) * (χ x * w σ.toNNReal x) with hφ
  have hecont : Continuous (fun σ : ℝ => Real.exp (-lam * σ)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hφc : Continuous φ := hecont.mul (continuous_const.mul (hb.cont x))
  set Θ : ℝ → ℝ := fun s => Real.exp (-lam * s) * F s + (∫ σ in (0 : ℝ)..s, φ σ) +
    (Err / lam ^ 2) * Real.exp (-lam * s) with hΘ
  have hΘc : Continuous Θ :=
    ((hecont.mul hcontF).add (by
      have := (hφc.integral_hasStrictDerivAt 0)
      exact continuous_iff_continuousAt.2 fun s => (this s).hasDerivAt.continuousAt)).add
      (continuous_const.mul hecont)
  have hexp : ∀ s : ℝ, HasDerivAt (fun s : ℝ => Real.exp (-lam * s))
      (Real.exp (-lam * s) * (-lam)) s := by
    intro s
    simpa using ((hasDerivAt_id s).const_mul (-lam)).exp
  have hΘd : ∀ s : ℝ, 0 < s → HasDerivAt Θ
      (Real.exp (-lam * s) * (Hh s - lam * F s + χ x * w s.toNNReal x - Err / lam)) s := by
    intro s hs
    have h1 := (hexp s).mul (hderivF s hs)
    have h2 := (hφc.integral_hasStrictDerivAt 0 s).hasDerivAt
    have h3 := (hexp s).const_mul (Err / lam ^ 2)
    have := (h1.add h2).add h3
    convert this using 1
    simp only [hφ]
    field_simp
    ring
  have hΘnp : ∀ s ∈ interior (Ici (0 : ℝ)), deriv Θ s ≤ 0 := by
    intro s hs
    rw [interior_Ici] at hs
    have hs' : (0 : ℝ) < s := hs
    rw [(hΘd s hs').deriv]
    have h1 := hid s
    have h2 := hE_lower s
    have h3 : Hh s - lam * F s + χ x * w s.toNNReal x - Err / lam ≤ 0 := by
      have : -Err / lam = -(Err / lam) := by ring
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le h3
  have hanti : AntitoneOn Θ (Ici 0) :=
    antitoneOn_of_deriv_nonpos (convex_Ici 0) hΘc.continuousOn
      (fun s hs => by
        rw [interior_Ici] at hs
        exact (hΘd s hs).differentiableAt.differentiableWithinAt) hΘnp
  have hF0 : F 0 = resU P lam (fun y => χ y * g y) x := by
    simp only [hF, hf, Real.toNNReal_zero, hb.zero]
  have hErr0 : 0 ≤ Err := by
    have : 0 ≤ A / R := hA1
    positivity
  have hFbd : ∀ s : ℝ, -(K / lam) ≤ F s := by
    intro s
    have := resU_ge hP hV1 (h := f s) (hfcont s) (hfc s) (a := -K) (fun y => by
      simp only [hf]
      have h1 : 0 ≤ χ y * w s.toNNReal y := mul_nonneg (hχ01 y).1 (hb.nonneg _ _)
      linarith) hlam x
    simpa [neg_div] using this
  have hmain : ∀ S : ℝ, 0 ≤ S → (∫ σ in (0 : ℝ)..S, φ σ) ≤
      F 0 + Err / lam ^ 2 + (K / lam) * Real.exp (-lam * S) := by
    intro S hS
    have h1 : Θ S ≤ Θ 0 := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hS) hS
    have h0 : Θ 0 = F 0 + Err / lam ^ 2 := by simp [hΘ]
    have h2 : -(K / lam) * Real.exp (-lam * S) ≤ Real.exp (-lam * S) * F S := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hFbd S) (Real.exp_pos _).le
    have h3 : 0 ≤ (Err / lam ^ 2) * Real.exp (-lam * S) := by positivity
    rw [h0] at h1
    simp only [hΘ] at h1
    nlinarith
  have hφint : IntegrableOn φ (Ioi 0) := by
    refine ((integrableOn_exp_mul_Ioi (a := -lam) (by linarith) 0).const_mul K).mono'
      hφc.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun σ _ => ?_)
    rw [Real.norm_eq_abs, hφ, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm, abs_mul,
      abs_of_nonneg (hχ01 x).1, abs_of_nonneg (hb.nonneg _ _)]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    calc χ x * w σ.toNNReal x ≤ 1 * K := mul_le_mul (hχ01 x).2 (hb.le _ _) (hb.nonneg _ _) zero_le_one
      _ = K := one_mul K
  have hlim1 : Tendsto (fun S : ℝ => ∫ σ in (0 : ℝ)..S, φ σ) atTop (𝓝 (∫ σ in Ioi (0 : ℝ), φ σ)) :=
    intervalIntegral_tendsto_integral_Ioi 0 hφint tendsto_id
  have hexp0 : Tendsto (fun S : ℝ => Real.exp (-lam * S)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hlam) : Tendsto (fun s : ℝ => -lam * s) atTop atBot)
  have hlim2 : Tendsto (fun S : ℝ => F 0 + Err / lam ^ 2 + (K / lam) * Real.exp (-lam * S)) atTop
      (𝓝 (F 0 + Err / lam ^ 2 + (K / lam) * 0)) :=
    tendsto_const_nhds.add (hexp0.const_mul _)
  have hle := le_of_tendsto_of_tendsto hlim1 hlim2
    ((eventually_ge_atTop (0 : ℝ)).mono fun S hS => hmain S hS)
  have hint_eq : ∫ σ in Ioi (0 : ℝ), φ σ =
      χ x * ∫ s in Ioi (0 : ℝ), Real.exp (-lam * s) * w s.toNNReal x := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun σ => ?_)
    simp only [hφ]; ring
  rw [← hint_eq]
  simpa [hF0] using hle

end Deriv

end C2U

end CutCur
