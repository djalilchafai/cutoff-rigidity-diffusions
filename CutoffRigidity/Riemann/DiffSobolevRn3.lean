module

public import CutoffRigidity.Riemann.DiffSobolevRn1
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.Real.Pi.Bounds

/-! # Sobolev inequality for `C_c^∞` functions via the Fourier transform

For `f ∈ C_c^∞(E)`, `sobSmooth b m f = ∫ (1 + 4π²‖ξ‖²)^m ‖𝓕 f ξ‖² dξ` and, when `m` is large
enough, `sup |D^i f|² ≤ C * sobSmooth b m f`.
-/

@[expose] public section

open MeasureTheory SchwartzMap
open scoped ContDiff FourierTransform
open LineDeriv

set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Diff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι]

/-- A smooth compactly supported real function, as a complex Schwartz function. -/
noncomputable def gS {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : 𝓢(E, ℂ) :=
  (hc.comp_left (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hf)

@[simp] lemma gS_apply {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (x : E) :
    gS hf hc x = (f x : ℂ) := rfl

lemma pd_contDiff {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (v : E) : ContDiff ℝ ∞ (pd v f) :=
  (hf.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

lemma pd_hasCompactSupport {f : E → ℝ} (hc : HasCompactSupport f) (v : E) :
    HasCompactSupport (pd v f) :=
  (hc.fderiv ℝ).comp_left (g := fun T : E →L[ℝ] ℝ => T v) (by simp)

lemma fourier_gS_pd {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (v : E) (ξ : E) :
    𝓕 (gS (pd_contDiff hf v) (pd_hasCompactSupport hc v)) ξ =
      (2 * Real.pi * Complex.I * (inner ℝ ξ v : ℝ)) * 𝓕 (gS hf hc) ξ := by
  have h : gS (pd_contDiff hf v) (pd_hasCompactSupport hc v) = ∂_{v} (gS hf hc) := by
    ext x
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    have hd : DifferentiableAt ℝ f x := (hf.differentiable (by simp)) x
    have : (gS hf hc : E → ℂ) = Complex.ofRealCLM ∘ f := rfl
    rw [this, fderiv_comp x Complex.ofRealCLM.differentiableAt hd]
    simp [pd]
  rw [h, SchwartzMap.fourier_lineDerivOp_eq]
  have : (inner ℝ · v : E → ℝ).HasTemperateGrowth := ((innerSL ℝ).flip v).hasTemperateGrowth
  simp [SchwartzMap.smulLeftCLM_apply_apply this]
  ring


/-- The Sobolev weight `1 + 4π²‖ξ‖²`. -/
noncomputable def wt (ξ : E) : ℝ := 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2

lemma one_le_wt (ξ : E) : 1 ≤ wt ξ := by
  unfold wt; nlinarith [sq_nonneg ‖ξ‖, Real.pi_pos, sq_nonneg Real.pi]

lemma wt_pos (ξ : E) : 0 < wt ξ := lt_of_lt_of_le one_pos (one_le_wt ξ)

lemma integrable_wt_pow_mul_norm_sq (φ : 𝓢(E, ℂ)) (m : ℕ) :
    Integrable (fun ξ : E => wt ξ ^ m * ‖φ ξ‖ ^ 2) := by
  have hT : (fun ξ : E => (((wt ξ) ^ m : ℝ) : ℂ)).HasTemperateGrowth := by
    unfold wt; fun_prop
  set ψ : 𝓢(E, ℂ) := smulLeftCLM ℂ (fun ξ : E => (((wt ξ) ^ m : ℝ) : ℂ)) φ with hψ
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ ξ, ‖φ ξ‖ ≤ M :=
    ⟨‖φ.toBoundedContinuousFunction‖, fun ξ => φ.toBoundedContinuousFunction.norm_coe_le_norm ξ⟩
  refine ((ψ.integrable.norm).mul_const M).mono' ?_ (Filter.Eventually.of_forall fun ξ => ?_)
  · have : Continuous fun ξ : E => wt ξ ^ m * ‖φ ξ‖ ^ 2 := by
      unfold wt; have := φ.continuous; fun_prop
    exact this.aestronglyMeasurable
  · have h1 : ‖ψ ξ‖ = wt ξ ^ m * ‖φ ξ‖ := by
      rw [hψ, smulLeftCLM_apply_apply hT, norm_smul]
      simp [abs_of_pos (wt_pos ξ)]
    rw [Real.norm_of_nonneg (by have := wt_pos ξ; positivity), h1, sq, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left (hM ξ) (by have := wt_pos ξ; positivity)

lemma norm_sq_mul_helper (r : ℝ) (z : ℂ) :
    ‖(2 * Real.pi * Complex.I * (r : ℂ)) * z‖ ^ 2 = 4 * Real.pi ^ 2 * r ^ 2 * ‖z‖ ^ 2 := by
  have : ‖(2 * Real.pi * Complex.I * (r : ℂ))‖ = 2 * Real.pi * |r| := by
    simp [Complex.norm_I, abs_of_pos Real.pi_pos]
  rw [norm_mul, mul_pow, this, mul_pow, mul_pow, sq_abs]; ring

/-- Geometric sum `∑_{k ≤ m} t^k`. -/
noncomputable def geo (m : ℕ) (t : ℝ) : ℝ := ∑ k ∈ Finset.range (m + 1), t ^ k

lemma geo_zero (t : ℝ) : geo 0 t = 1 := by simp [geo]

lemma geo_succ (m : ℕ) (t : ℝ) : geo (m + 1) t = 1 + t * geo m t := by
  unfold geo
  rw [Finset.sum_range_succ' _ (m + 1), Finset.mul_sum]
  simp [pow_succ, mul_comm, add_comm]

lemma geo_nonneg (m : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ geo m t :=
  Finset.sum_nonneg fun k _ => pow_nonneg ht k

lemma geo_le (m : ℕ) {t : ℝ} (ht : 0 ≤ t) : geo m t ≤ (1 + t) ^ m := by
  induction m with
  | zero => simp [geo_zero]
  | succ m ih =>
    rw [geo_succ, pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left ih ht, one_le_pow₀ (by linarith : (1:ℝ) ≤ 1 + t) (n := m)]

lemma pow_le_geo (m : ℕ) {t : ℝ} (ht : 0 ≤ t) : (1 + t) ^ m ≤ 2 ^ m * geo m t := by
  induction m with
  | zero => simp [geo_zero]
  | succ m ih =>
    have h1 : geo m t ≤ geo (m + 1) t := by
      have : geo (m + 1) t = geo m t + t ^ (m + 1) := Finset.sum_range_succ _ (m + 1)
      linarith [pow_nonneg ht (m + 1)]
    have h2 : t * geo m t = geo (m + 1) t - 1 := by rw [geo_succ]; ring
    have h3 : (1 + t) * geo m t ≤ 2 * geo (m + 1) t := by
      nlinarith [geo_nonneg m ht, geo_nonneg (m+1) ht]
    calc (1 + t) ^ (m + 1) = (1 + t) * (1 + t) ^ m := by ring
      _ ≤ (1 + t) * (2 ^ m * geo m t) := mul_le_mul_of_nonneg_left ih (by linarith)
      _ = 2 ^ m * ((1 + t) * geo m t) := by ring
      _ ≤ 2 ^ m * (2 * geo (m + 1) t) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 2 ^ (m + 1) * geo (m + 1) t := by ring

lemma wt_eq (ξ : E) : wt ξ = 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := rfl

lemma t_nonneg (ξ : E) : 0 ≤ 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by positivity

lemma integrable_geo_mul_norm_sq (φ : 𝓢(E, ℂ)) (m : ℕ) :
    Integrable (fun ξ : E => geo m (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) * ‖φ ξ‖ ^ 2) := by
  refine (integrable_wt_pow_mul_norm_sq φ m).mono' ?_ (Filter.Eventually.of_forall fun ξ => ?_)
  · have : Continuous fun ξ : E => geo m (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) * ‖φ ξ‖ ^ 2 := by
      unfold geo; have := φ.continuous; fun_prop
    exact this.aestronglyMeasurable
  · rw [Real.norm_of_nonneg (mul_nonneg (geo_nonneg m (t_nonneg ξ)) (by positivity))]
    exact mul_le_mul_of_nonneg_right (geo_le m (t_nonneg ξ)) (by positivity)

lemma sobSmooth_zero_eq {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ∫ x, f x ^ 2 = ∫ ξ, ‖𝓕 (gS hf hc) ξ‖ ^ 2 := by
  have := SchwartzMap.integral_norm_sq_fourier (gS hf hc)
  simp only [gS_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs] at this
  exact this.symm

theorem sobSmooth_eq_fourier (b : OrthonormalBasis ι ℝ E) (m : ℕ) :
    ∀ {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f),
      sobSmooth b m f = ∫ ξ, geo m (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) * ‖𝓕 (gS hf hc) ξ‖ ^ 2 := by
  induction m with
  | zero => intro f hf hc; simpa [sobSmooth, geo_zero] using sobSmooth_zero_eq hf hc
  | succ m ih =>
    intro f hf hc
    simp only [sobSmooth]
    have h1 : ∀ i, sobSmooth b m (pd (b i) f) = ∫ ξ, geo m (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) *
        (4 * Real.pi ^ 2 * (inner ℝ ξ (b i)) ^ 2 * ‖𝓕 (gS hf hc) ξ‖ ^ 2) := by
      intro i
      rw [ih (pd_contDiff hf (b i)) (pd_hasCompactSupport hc (b i))]
      congr 1; ext ξ
      rw [fourier_gS_pd hf hc (b i) ξ, norm_sq_mul_helper]
    have hint : ∀ i, Integrable (fun ξ : E => geo m (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) *
        (4 * Real.pi ^ 2 * (inner ℝ ξ (b i)) ^ 2 * ‖𝓕 (gS hf hc) ξ‖ ^ 2)) := by
      intro i
      refine (integrable_geo_mul_norm_sq
        (𝓕 (gS (pd_contDiff hf (b i)) (pd_hasCompactSupport hc (b i)))) m).congr ?_
      refine Filter.Eventually.of_forall fun ξ => ?_
      show geo m (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) * ‖𝓕 (gS (pd_contDiff hf (b i)) (pd_hasCompactSupport hc (b i))) ξ‖ ^ 2 = _
      rw [fourier_gS_pd hf hc (b i) ξ, norm_sq_mul_helper]
    have h0 : Integrable (fun ξ : E => ‖𝓕 (gS hf hc) ξ‖ ^ 2) := by
      simpa [geo_zero] using integrable_geo_mul_norm_sq (𝓕 (gS hf hc)) 0
    simp_rw [h1]
    rw [sobSmooth_zero_eq hf hc, ← integral_finsetSum _ (fun i _ => hint i),
      ← integral_add h0 (integrable_finsetSum _ (fun i _ => hint i))]
    congr 1; ext ξ
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    have h2 : ∑ i, (inner ℝ ξ (b i)) ^ 2 = ‖ξ‖ ^ 2 := by
      have := b.sum_sq_norm_inner_right ξ
      simpa [real_inner_comm] using this
    have h3 : ∑ i, 4 * Real.pi ^ 2 * (inner ℝ ξ (b i)) ^ 2 = 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by
      rw [← Finset.mul_sum, h2]
    rw [h3, geo_succ]; ring


lemma norm_fourier_le_integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (h : E → F) (w : E) : ‖𝓕 h w‖ ≤ ∫ v, ‖h v‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

lemma norm_fourierInv_le_integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (h : E → F) (w : E) : ‖𝓕⁻ h w‖ ≤ ∫ v, ‖h v‖ := by
  rw [Real.fourierInv_eq_fourier_neg]; exact norm_fourier_le_integral h _

theorem norm_iteratedFDeriv_le_integral {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (x : E) (i : ℕ) :
    ‖iteratedFDeriv ℝ i f x‖ ≤ ∫ ξ, (2 * Real.pi) ^ i * (‖ξ‖ ^ i * ‖𝓕 (gS hf hc) ξ‖) := by
  set G : 𝓢(E, ℂ) := gS hf hc with hG
  have hGf : (G : E → ℂ) = Complex.ofRealLI ∘ f := rfl
  have h1 : ‖iteratedFDeriv ℝ i (G : E → ℂ) x‖ = ‖iteratedFDeriv ℝ i f x‖ := by
    rw [hGf]
    exact Complex.ofRealLI.norm_iteratedFDeriv_comp_left (hf.contDiffAt) (by exact_mod_cast le_top)
  rw [← h1]
  set D := iteratedFDeriv ℝ i (G : E → ℂ) with hD
  have hDc : Continuous D := (G.smooth ⊤).continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hint : ∀ n : ℕ, Integrable (iteratedFDeriv ℝ n (G : E → ℂ)) := by
    intro n
    refine ((G.smooth ⊤).continuous_iteratedFDeriv (by exact_mod_cast le_top)).integrable_of_hasCompactSupport ?_
    exact (hc.comp_left (g := Complex.ofRealLI) (by simp)).iteratedFDeriv n
  have hDi : Integrable D := hint i
  have hF : 𝓕 D = fun w => VectorFourier.fourierPowSMulRight (-innerSL ℝ) (𝓕 (G : E → ℂ)) w i :=
    Real.fourier_iteratedFDeriv (N := ⊤) (G.smooth ⊤)
      (fun n _ => hint n) (by exact_mod_cast le_top)
  have hFi : Integrable (𝓕 D) := by
    rw [hF]
    exact VectorFourier.integrable_fourierPowSMulRight _ ((𝓕 G).integrable_pow_mul volume i)
      (𝓕 G).continuous.aestronglyMeasurable
  have h2 : 𝓕⁻ (𝓕 D) x = D x := hDi.fourierInv_fourier_eq hFi hDc.continuousAt
  rw [← h2]
  refine (norm_fourierInv_le_integral _ x).trans ?_
  refine integral_mono hFi.norm ?_ (fun ξ => ?_)
  · exact ((𝓕 G).integrable_pow_mul volume i).const_mul _
  · rw [hF]
    refine (VectorFourier.norm_fourierPowSMulRight_le _ _ _ _).trans ?_
    have : ‖-innerSL ℝ (E := E)‖ ≤ 1 := (norm_neg (innerSL ℝ (E := E))).le.trans (norm_innerSL_le _)
    have h3 : (2 * Real.pi * ‖-innerSL ℝ (E := E)‖) ^ i ≤ (2 * Real.pi) ^ i := by
      calc _ ≤ (2 * Real.pi * 1) ^ i := by gcongr
        _ = _ := by rw [mul_one]
    calc _ ≤ (2 * Real.pi) ^ i * ‖ξ‖ ^ i * ‖(𝓕 (G : E → ℂ)) ξ‖ := by gcongr
      _ = _ := by rw [mul_assoc]; rfl


lemma cs_aux {u q p : E → ℝ} (hu0 : ∀ ξ, 0 ≤ u ξ) (hq0 : ∀ ξ, 0 ≤ q ξ) (hp0 : ∀ ξ, 0 ≤ p ξ)
    (hu : Integrable u) (hq : Integrable q) (hp : Integrable p)
    (hle : ∀ ξ, u ξ ^ 2 ≤ q ξ * p ξ) : (∫ ξ, u ξ) ^ 2 ≤ (∫ ξ, q ξ) * ∫ ξ, p ξ := by
  have hQ : 0 ≤ ∫ ξ, q ξ := integral_nonneg hq0
  have hP : 0 ≤ ∫ ξ, p ξ := integral_nonneg hp0
  have hU : 0 ≤ ∫ ξ, u ξ := integral_nonneg hu0
  have key : ∀ t : ℝ, 0 ≤ (∫ ξ, q ξ) * (t * t) + (-2 * ∫ ξ, u ξ) * t + ∫ ξ, p ξ := by
    intro t
    rcases le_or_gt t 0 with ht | ht
    · nlinarith [mul_nonneg hQ (mul_self_nonneg t), mul_nonneg hU (neg_nonneg.2 ht)]
    · have h1 : ∫ ξ, 2 * t * u ξ ≤ ∫ ξ, (t ^ 2 * q ξ + p ξ) := by
        refine integral_mono (hu.const_mul _) ((hq.const_mul _).add hp) (fun ξ => ?_)
        have := hle ξ
        have := hu0 ξ; have := hq0 ξ; have := hp0 ξ
        have h : (2 * t * u ξ) ^ 2 ≤ (t ^ 2 * q ξ + p ξ) ^ 2 := by
          nlinarith [sq_nonneg (t ^ 2 * q ξ - p ξ),
            mul_le_mul_of_nonneg_left (hle ξ) (sq_nonneg t)]
        exact (pow_le_pow_iff_left₀ (by have := hu0 ξ; positivity)
          (by have := hq0 ξ; have := hp0 ξ; positivity) two_ne_zero).1 h
      rw [integral_const_mul, integral_add (hq.const_mul _) hp, integral_const_mul] at h1
      nlinarith
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

theorem sobolev_sup_sq_le (b : OrthonormalBasis ι ℝ E) {j m : ℕ}
    (hm : Module.finrank ℝ E + 2 * j < 2 * m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : E → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → ∀ x, ∀ i ≤ j,
      ‖iteratedFDeriv ℝ i f x‖ ^ 2 ≤ C * sobSmooth b m f := by
  have hjm : j ≤ m := by omega
  set k := m - j with hk
  have hkr : (Module.finrank ℝ E : ℝ) < 2 * (k : ℝ) := by
    have : Module.finrank ℝ E < 2 * k := by omega
    exact_mod_cast this
  have hqi := integrable_rpow_neg_one_add_norm_sq (E := E) (μ := volume) (r := 2 * (k : ℝ)) hkr
  set q : E → ℝ := fun ξ => (2 : ℝ) ^ m * ((1 + ‖ξ‖ ^ 2) ^ k)⁻¹ with hqdef
  have hqeq : ∀ ξ : E, q ξ = (2 : ℝ) ^ m * ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-(2 * (k : ℝ)) / 2) := by
    intro ξ
    rw [hqdef]; simp only
    rw [show -(2 * (k : ℝ)) / 2 = -(k : ℝ) by ring, Real.rpow_neg (by positivity),
      Real.rpow_natCast]
  have hqint : Integrable q := by
    have := hqi.const_mul ((2 : ℝ) ^ m)
    refine this.congr (Filter.Eventually.of_forall fun ξ => ?_)
    exact (hqeq ξ).symm
  have hq0 : ∀ ξ, 0 ≤ q ξ := fun ξ => by simp only [hqdef]; positivity
  refine ⟨∫ ξ, q ξ, integral_nonneg hq0, ?_⟩
  intro f hf hc x i hi
  set F : 𝓢(E, ℂ) := 𝓕 (gS hf hc) with hFdef
  set u : E → ℝ := fun ξ => (2 * Real.pi) ^ i * (‖ξ‖ ^ i * ‖F ξ‖) with hudef
  set p : E → ℝ := fun ξ => geo m (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) * ‖F ξ‖ ^ 2 with hpdef
  have hu0 : ∀ ξ, 0 ≤ u ξ := fun ξ => by simp only [hudef]; positivity
  have hp0 : ∀ ξ, 0 ≤ p ξ := fun ξ => by
    simp only [hpdef]; exact mul_nonneg (geo_nonneg m (t_nonneg ξ)) (by positivity)
  have hui : Integrable u := (F.integrable_pow_mul volume i).const_mul _
  have hpi : Integrable p := integrable_geo_mul_norm_sq F m
  have hle : ∀ ξ, u ξ ^ 2 ≤ q ξ * p ξ := by
    intro ξ
    set r : ℝ := ‖ξ‖ ^ 2 with hr
    have hr0 : 0 ≤ r := by positivity
    have ht : 0 ≤ 4 * Real.pi ^ 2 * r := by positivity
    have hrt : r ≤ 4 * Real.pi ^ 2 * r := by
      have : (1 : ℝ) ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
      nlinarith [mul_le_mul_of_nonneg_right this hr0]
    have h1 : u ξ ^ 2 = (4 * Real.pi ^ 2 * r) ^ i * ‖F ξ‖ ^ 2 := by
      have e : (2 * Real.pi) ^ i * (‖ξ‖ ^ i * ‖F ξ‖) = (2 * Real.pi * ‖ξ‖) ^ i * ‖F ξ‖ := by
        rw [mul_pow]; ring
      have e2 : (2 * Real.pi * ‖ξ‖) ^ 2 = 4 * Real.pi ^ 2 * r := by rw [hr]; ring
      simp only [hudef]
      rw [e, mul_pow, ← pow_mul, mul_comm i 2, pow_mul, e2]
    have h2 : (4 * Real.pi ^ 2 * r) ^ i * (1 + r) ^ k ≤ 2 ^ m * geo m (4 * Real.pi ^ 2 * r) := by
      calc (4 * Real.pi ^ 2 * r) ^ i * (1 + r) ^ k
          ≤ (1 + 4 * Real.pi ^ 2 * r) ^ i * (1 + 4 * Real.pi ^ 2 * r) ^ k := by
            (gcongr; all_goals linarith)
        _ = (1 + 4 * Real.pi ^ 2 * r) ^ (i + k) := by rw [pow_add]
        _ ≤ (1 + 4 * Real.pi ^ 2 * r) ^ m :=
            pow_le_pow_right₀ (by linarith) (by omega)
        _ ≤ _ := pow_le_geo m ht
    have h3 : 0 < (1 + r) ^ k := by positivity
    rw [h1]
    simp only [hqdef, hpdef]
    rw [← hr]
    have : (4 * Real.pi ^ 2 * r) ^ i ≤ 2 ^ m * ((1 + r) ^ k)⁻¹ * geo m (4 * Real.pi ^ 2 * r) := by
      generalize geo m (4 * Real.pi ^ 2 * r) = g at h2 ⊢
      generalize (4 * Real.pi ^ 2 * r) ^ i = a at h2 ⊢
      have e : 2 ^ m * ((1 + r) ^ k)⁻¹ * g = (2 ^ m * g) / (1 + r) ^ k := by
        rw [div_eq_mul_inv]; ring
      rw [e, le_div_iff₀ h3]
      exact h2
    calc _ ≤ (2 ^ m * ((1 + r) ^ k)⁻¹ * geo m (4 * Real.pi ^ 2 * r)) * ‖F ξ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = _ := by ring
  have hcs := cs_aux hu0 hq0 hp0 hui hqint hpi hle
  have hU : ‖iteratedFDeriv ℝ i f x‖ ≤ ∫ ξ, u ξ := norm_iteratedFDeriv_le_integral hf hc x i
  have hP : sobSmooth b m f = ∫ ξ, p ξ := sobSmooth_eq_fourier b m hf hc
  rw [hP]
  exact le_trans (pow_le_pow_left₀ (norm_nonneg _) hU 2) hcs

end CutoffRigidity.Riemann.Diff
