module

public import CutoffRigidity.Riemann.DiffAPI
public import CutoffRigidity.Riemann.EigenLinear
public import CutoffRigidity.Riemann.WeightedCutoffs

/-! # Tier B1: Dynkin's identity for bounded smooth functions

`IsDiffusionSemigroup` only gives Dynkin's identity on `C_c^∞`.  Given `OneSidedCutoffs`
(smooth compactly supported `χₙ ↑ 1` with `|∇χₙ| ≤ C`, `𝓛χₙ ≥ -C`) we prove it for smooth
functions with bounded value, gradient and generator (`DynkinBounded`), by the mass trick.
-/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set
open scoped Manifold ContDiff ENNReal NNReal Topology

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur CutoffRigidity.Riemann

section Calculus

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

theorem sum_inner_smulRight {T : Type*} [NormedAddCommGroup T] [InnerProductSpace ℝ T]
    [FiniteDimensional ℝ T] (L : T →L[ℝ] ℝ) (v : T) :
    L v = ∑ i, inner ℝ ((L.smulRight v : T →L[ℝ] T) (stdOrthonormalBasis ℝ T i))
      (stdOrthonormalBasis ℝ T i) := by
  set b := stdOrthonormalBasis ℝ T
  conv_lhs => rw [← b.sum_repr' v]
  simp [map_sum, ContinuousLinearMap.smulRight_apply, real_inner_smul_right, real_inner_comm,
    mul_comm]

theorem carre_comm_dyn (f g : M → ℝ) (x : M) : carre F f g x = carre F g f x := real_inner_comm _ _

theorem mlaplacian_mul {χ f : M → ℝ} (hχ : MSmooth F χ) (hf : MSmooth F f) (x : M) :
    mlaplacian F (fun y => χ y * f y) x =
      χ x * mlaplacian F f x + f x * mlaplacian F χ x + 2 * carre F χ f x := by
  have e : mgrad F (fun y => χ y * f y) = χ • mgrad F f + f • mgrad F χ := by
    funext y; exact mgrad_mul F hχ hf y
  have hcov := (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M).isCovariantDerivativeOn
    (s := Set.univ)
  have h1 := MDifferentiableAt.smul_section (hχ x |>.mdifferentiableAt (by simp)) (mgrad_mdiffAt F hf x)
  have h2 := MDifferentiableAt.smul_section (hf x |>.mdifferentiableAt (by simp)) (mgrad_mdiffAt F hχ x)
  have key := hcov.add h1 h2 (x := x)
  have l1 := hcov.leibniz (mgrad_mdiffAt F hf x) (hχ x |>.mdifferentiableAt (by simp)) (x := x)
  have l2 := hcov.leibniz (mgrad_mdiffAt F hχ x) (hf x |>.mdifferentiableAt (by simp)) (x := x)
  have hsum : ∀ (g k : M → ℝ), ∑ i, inner ℝ (((mvfderiv 𝓘(ℝ, F) g x).smulRight (mgrad F k x) :
        TangentSpace 𝓘(ℝ, F) x →L[ℝ] TangentSpace 𝓘(ℝ, F) x)
        (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i))
        (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i) = carre F k g x := by
    intro g k
    rw [carre_eq_mvfderiv F k g x]; exact (sum_inner_smulRight _ _).symm
  unfold mlaplacian
  rw [e, key, l1, l2]
  simp only [add_apply, smul_apply, inner_add_left,
    real_inner_smul_left, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hsum, hsum]
  rw [carre_comm_dyn]
  ring

theorem mgenerator_mul {V χ f : M → ℝ} (hχ : MSmooth F χ) (hf : MSmooth F f) (x : M) :
    mgenerator F V (fun y => χ y * f y) x =
      χ x * mgenerator F V f x + f x * mgenerator F V χ x + 2 * carre F χ f x := by
  unfold mgenerator
  have e : mgrad F (fun y => χ y * f y) x = χ x • mgrad F f x + f x • mgrad F χ x :=
    mgrad_mul F hχ hf x
  rw [mlaplacian_mul F hχ hf x, e, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  ring

theorem mlaplacian_const (c : ℝ) (x : M) : mlaplacian F (fun _ : M => c) x = 0 := by
  have e : mgrad F (fun _ : M => c) = 0 := funext (mgrad_const F c)
  unfold mlaplacian
  rw [e, CovariantDerivative.zero]
  simp

theorem mgenerator_const {V : M → ℝ} (c : ℝ) (x : M) :
    mgenerator F V (fun _ : M => c) x = 0 := by
  unfold mgenerator
  rw [mlaplacian_const, mgrad_const]; simp

theorem mgrad_add_const {f : M → ℝ} (hf : MSmooth F f) (c : ℝ) (x : M) :
    mgrad F (fun y => f y + c) x = mgrad F f x := by
  rw [mgrad_add' F hf contMDiff_const, mgrad_const]; simp

theorem mgenerator_add_const {V f : M → ℝ} (hf : MSmooth F f) (c : ℝ) (x : M) :
    mgenerator F V (fun y => f y + c) x = mgenerator F V f x := by
  rw [mgenerator_add F hf contMDiff_const, mgenerator_const]; simp

/-- If `χ ≡ 1` near `x`, then `∇χ(x) = 0` and `𝓛χ(x) = 0`. -/
theorem mgrad_mgenerator_eq_zero_of_eventually_one {V χ : M → ℝ} (hχ : MSmooth F χ) {x : M}
    (h : ∀ᶠ y in 𝓝 x, χ y = 1) : mgrad F χ x = 0 ∧ mgenerator F V χ x = 0 := by
  have hs : MSmooth F (fun y => χ y + (-1 : ℝ)) := hχ.add contMDiff_const
  have hx : x ∉ tsupport (fun y => χ y + (-1 : ℝ)) := by
    rw [notMem_tsupport_iff_eventuallyEq]
    filter_upwards [h] with y hy
    simp [hy]
  refine ⟨?_, ?_⟩
  · have := mgrad_eq_zero_of_notMem_tsupport F hx
    rwa [mgrad_add_const F hχ] at this
  · have := mgenerator_eq_zero_of_notMem_tsupport F V hs hx
    rwa [mgenerator_add_const F hχ] at this

section Defs

variable [MeasurableSpace M]

/-- Smooth functions with bounded value, gradient and generator. -/
def BddSmooth (V : M → ℝ) (f : M → ℝ) : Prop :=
  MSmooth F f ∧ ∃ C : ℝ, ∀ x, |f x| ≤ C ∧ ‖mgrad F f x‖ ≤ C ∧ |mgenerator F V f x| ≤ C

/-- Dynkin's identity for bounded smooth functions with bounded gradient and generator. -/
def DynkinBounded (V : M → ℝ) (Pt : ℝ≥0 → Kernel M M) : Prop :=
  ∀ f : M → ℝ, BddSmooth F V f → ∀ (x : M) (t : ℝ≥0),
    ∫ y, f y ∂Pt t x = f x + ∫ s in (0 : ℝ)..(t : ℝ), ∫ y, mgenerator F V f y ∂Pt s.toNNReal x

/-- One-sided cutoffs: smooth compactly supported `[0,1]`-valued `χₙ`, eventually `≡ 1` near
every point, with `‖∇χₙ‖ ≤ C` and `𝓛χₙ ≥ -C`. -/
def OneSidedCutoffs (V : M → ℝ) : Prop :=
  ∃ (C : ℝ) (χ : ℕ → M → ℝ), (∀ n, MSmooth F (χ n) ∧ HasCompactSupport (χ n) ∧
      ∀ x, 0 ≤ χ n x ∧ χ n x ≤ 1 ∧ ‖mgrad F (χ n) x‖ ≤ C ∧ -C ≤ mgenerator F V (χ n) x) ∧
    ∀ x, ∃ U ∈ 𝓝 x, ∀ᶠ n in atTop, ∀ y ∈ U, χ n y = 1

theorem BddSmooth.affine {V f : M → ℝ} (hf : BddSmooth F V f) (a b : ℝ) :
    BddSmooth F V (fun y => a * f y + b) := by
  obtain ⟨hs, C, hC⟩ := hf
  have hms : MSmooth F (fun y => a * f y) := contMDiff_const.mul hs
  refine ⟨hms.add contMDiff_const, |a| * C + |b|, fun x => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hC x
  have hC0 : 0 ≤ C := (abs_nonneg _).trans h1
  have hg : mgrad F (fun y => a * f y + b) x = a • mgrad F f x := by
    rw [mgrad_add_const F hms, mgrad_const_mul F a hs]
  have hL : mgenerator F V (fun y => a * f y + b) x = a * mgenerator F V f x := by
    rw [mgenerator_add_const F hms, mgenerator_const_mul F a hs]
  refine ⟨?_, ?_, ?_⟩
  · calc |a * f x + b| ≤ |a * f x| + |b| := abs_add_le _ _
      _ ≤ |a| * C + |b| := by rw [abs_mul]; gcongr
  · rw [hg, norm_smul, Real.norm_eq_abs]
    calc |a| * ‖mgrad F f x‖ ≤ |a| * C := by gcongr
      _ ≤ |a| * C + |b| := by linarith [abs_nonneg b]
  · rw [hL, abs_mul]
    calc |a| * |mgenerator F V f x| ≤ |a| * C := by gcongr
      _ ≤ |a| * C + |b| := by linarith [abs_nonneg b]

theorem BddSmooth.generator_affine {V f : M → ℝ} (hf : BddSmooth F V f) (a b : ℝ) (x : M) :
    mgenerator F V (fun y => a * f y + b) x = a * mgenerator F V f x := by
  have hms : MSmooth F (fun y => a * f y) := contMDiff_const.mul hf.1
  rw [mgenerator_add_const F hms, mgenerator_const_mul F a hf.1]

end Defs

/-! ### Smooth surrogates of `u⁻` and `|∇χ|` -/

/-- Smooth majorant of `u⁻ = max 0 (-u)`: `θ_ε(u) = (√(u²+ε²) - u)/2`. -/
noncomputable def thetaFn (ε u : ℝ) : ℝ := (Real.sqrt (u ^ 2 + ε ^ 2) - u) / 2

theorem thetaFn_contDiff {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (thetaFn ε) := by
  unfold thetaFn
  have h : ContDiff ℝ ∞ (fun u : ℝ => Real.sqrt (u ^ 2 + ε ^ 2)) :=
    ContDiff.sqrt (by fun_prop) (fun u => by positivity)
  exact (h.sub contDiff_id).div_const 2

theorem thetaFn_nonneg (ε u : ℝ) : 0 ≤ thetaFn ε u := by
  unfold thetaFn
  have : u ≤ Real.sqrt (u ^ 2 + ε ^ 2) :=
    (le_abs_self u).trans (Real.abs_le_sqrt (by nlinarith [sq_nonneg ε]))
  linarith

theorem neg_le_thetaFn (ε u : ℝ) : -u ≤ thetaFn ε u := by
  unfold thetaFn
  have : -u ≤ Real.sqrt (u ^ 2 + ε ^ 2) :=
    (neg_le_abs u).trans (Real.abs_le_sqrt (by nlinarith [sq_nonneg ε]))
  linarith

theorem thetaFn_zero (ε : ℝ) (hε : 0 ≤ ε) : thetaFn ε 0 = ε / 2 := by
  unfold thetaFn
  rw [zero_pow two_ne_zero, zero_add, Real.sqrt_sq hε]; ring

theorem thetaFn_le {ε u C : ℝ} (hε : 0 ≤ ε) (hu : -C ≤ u) : thetaFn ε u ≤ |C| + ε := by
  unfold thetaFn
  have h1 : Real.sqrt (u ^ 2 + ε ^ 2) ≤ |u| + ε := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [abs_nonneg u, sq_abs u]
  rcases le_total 0 u with h | h
  · rw [abs_of_nonneg h] at h1; linarith [abs_nonneg C]
  · rw [abs_of_nonpos h] at h1
    have : -u ≤ |C| := by linarith [le_abs_self C]
    linarith

theorem mgenerator_mul_ge {V χ f : M → ℝ} (hχ : MSmooth F χ) (hf : MSmooth F f)
    {Cf ε : ℝ} (hf0 : ∀ y, 0 ≤ f y) (hfC : ∀ y, f y ≤ Cf)
    (hgC : ∀ y, ‖mgrad F f y‖ ≤ Cf) (y : M) :
    χ y * mgenerator F V f y - Cf * thetaFn ε (mgenerator F V χ y)
      - 2 * Cf * Real.sqrt (carre F χ χ y + ε ^ 2) ≤ mgenerator F V (fun z => χ z * f z) y := by
  rw [mgenerator_mul F hχ hf]
  have h1 : f y * mgenerator F V χ y ≥ -(Cf * thetaFn ε (mgenerator F V χ y)) := by
    have a := neg_le_thetaFn ε (mgenerator F V χ y)
    have b := thetaFn_nonneg ε (mgenerator F V χ y)
    nlinarith [mul_le_mul_of_nonneg_right (hfC y) b, mul_le_mul_of_nonneg_left a (hf0 y)]
  have h2 : |carre F χ f y| ≤ ‖mgrad F χ y‖ * Cf :=
    (abs_carre_le F χ f y).trans (by gcongr; exact hgC y)
  have h3 : ‖mgrad F χ y‖ ≤ Real.sqrt (carre F χ χ y + ε ^ 2) := by
    calc ‖mgrad F χ y‖ = Real.sqrt (‖mgrad F χ y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (carre F χ χ y) := by rw [carre_self_eq]
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ε])
  have hCf : 0 ≤ Cf := (norm_nonneg _).trans (hgC y)
  have h4 : ‖mgrad F χ y‖ * Cf ≤ Real.sqrt (carre F χ χ y + ε ^ 2) * Cf := by gcongr
  have := neg_abs_le (carre F χ f y)
  nlinarith

theorem msmooth_sqrt_add {h : M → ℝ} (hh : MSmooth F h) (h0 : ∀ y, 0 ≤ h y) {ε : ℝ} (hε : ε ≠ 0) :
    MSmooth F (fun y => Real.sqrt (h y + ε ^ 2)) := by
  intro y
  have hpos : h y + ε ^ 2 ≠ 0 := by have := h0 y; positivity
  have hg : ContDiffAt ℝ ∞ (fun v : ℝ => Real.sqrt (v + ε ^ 2)) (h y) :=
    ContDiffAt.sqrt (by fun_prop) hpos
  exact hg.comp_contMDiffAt (hh y)

theorem msmooth_thetaFn {h : M → ℝ} (hh : MSmooth F h) {ε : ℝ} (hε : 0 < ε) :
    MSmooth F (fun y => thetaFn ε (h y)) :=
  (thetaFn_contDiff hε).comp_contMDiff hh

theorem intervalIntegrable_of_measurable_bdd {G : ℝ → ℝ} (hG : Measurable G) {K : ℝ}
    (hb : ∀ s, |G s| ≤ K) (a b : ℝ) : IntervalIntegrable G volume a b := by
  rw [intervalIntegrable_iff]
  exact Measure.integrableOn_of_bounded (by simp) hG.aestronglyMeasurable
    (Filter.Eventually.of_forall fun s => by simpa using hb s)

theorem tendsto_interval_of_bdd {G : ℕ → ℝ → ℝ} {G0 : ℝ → ℝ} (hm : ∀ n, Measurable (G n))
    {K : ℝ} (hb : ∀ n s, |G n s| ≤ K) (hl : ∀ s, Tendsto (fun n => G n s) atTop (𝓝 (G0 s)))
    (a b : ℝ) :
    Tendsto (fun n => ∫ s in a..b, G n s) atTop (𝓝 (∫ s in a..b, G0 s)) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => K)
    (Filter.Eventually.of_forall fun n => (hm n).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun s _ => by
      simpa using hb n s)
    intervalIntegrable_const (Filter.Eventually.of_forall fun s _ => hl s)

theorem tendsto_integral_of_bdd [MeasurableSpace M] {P : Measure M} [IsFiniteMeasure P] {h : ℕ → M → ℝ} {h0 : M → ℝ}
    (hm : ∀ n, AEStronglyMeasurable (h n) P) {K : ℝ} (hb : ∀ n y, |h n y| ≤ K)
    (hl : ∀ y, Tendsto (fun n => h n y) atTop (𝓝 (h0 y))) :
    Tendsto (fun n => ∫ y, h n y ∂P) atTop (𝓝 (∫ y, h0 y ∂P)) :=
  tendsto_integral_of_dominated_convergence (fun _ => K) hm (integrable_const _)
    (fun n => Filter.Eventually.of_forall fun y => by simpa using hb n y)
    (Filter.Eventually.of_forall hl)

theorem abs_integral_le_of_prob [MeasurableSpace M] {P : Measure M} [IsProbabilityMeasure P]
    {h : M → ℝ} {K : ℝ} (hb : ∀ y, |h y| ≤ K) : |∫ y, h y ∂P| ≤ K := by
  have := norm_integral_le_of_norm_le_const (μ := P) (f := h) (C := K)
    (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hb y)
  simpa [Real.norm_eq_abs] using this

theorem integrable_of_bdd_cont [MeasurableSpace M] [OpensMeasurableSpace M] {P : Measure M}
    [IsFiniteMeasure P] {h : M → ℝ} {K : ℝ} (hc : Continuous h) (hb : ∀ y, |h y| ≤ K) :
    Integrable h P :=
  Integrable.mono' (integrable_const K) hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hb y)

section Dyn

variable [MeasurableSpace M] [BorelSpace M] {V : M → ℝ} {Pt : ℝ≥0 → Kernel M M}

/-- Measurability in time of `s ↦ ∫ h dPₛ(x,·)` for bounded smooth `h` (via cutoffs and the
continuity of the Dynkin functions `s ↦ ∫ χₙ h dPₛ(x,·)`). -/
theorem measurable_semi_time_of_cutoffs (hP : IsDiffusionSemigroup F V Pt) (hV : MSmooth F V)
    (χ : ℕ → M → ℝ) (hχ : ∀ n, MSmooth F (χ n) ∧ HasCompactSupport (χ n))
    (hχ01 : ∀ n y, 0 ≤ χ n y ∧ χ n y ≤ 1)
    (hlim : ∀ y, ∀ᶠ n in atTop, χ n y = 1) {h : M → ℝ} (hh : MSmooth F h)
    (C : ℝ) (hb : ∀ y, |h y| ≤ C) (x : M) :
    Measurable fun s : ℝ => ∫ y, h y ∂Pt s.toNNReal x := by
  refine measurable_of_tendsto_metrizable (f := fun n s => ∫ y, χ n y * h y ∂Pt s.toNNReal x)
    (fun n => ?_) (tendsto_pi_nhds.2 fun s => ?_)
  · exact ((continuous_dynkin F hP ((hχ n).1.mul hh) ((hχ n).2.mul_right) hV x).comp
      continuous_real_toNNReal).measurable
  · have : IsProbabilityMeasure (Pt s.toNNReal x) := (hP.1 _).isProbabilityMeasure x
    refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun n => ?_) ?_ ?_ ?_
    · exact (((hχ n).1.continuous.mul hh.continuous)).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      refine Filter.Eventually.of_forall fun y => ?_
      rw [Real.norm_eq_abs, abs_mul]
      have := hχ01 n y
      have h1 : |χ n y| ≤ 1 := by rw [abs_of_nonneg this.1]; exact this.2
      calc |χ n y| * |h y| ≤ 1 * C := mul_le_mul h1 (hb y) (abs_nonneg _) zero_le_one
        _ = C := one_mul C
    · refine Filter.Eventually.of_forall fun y => ?_
      exact tendsto_const_nhds.congr' (by
        filter_upwards [hlim y] with n hn
        rw [hn, one_mul])

/-- Step 1 of the mass trick: the inequality `≥` in Dynkin's identity for `f ≥ 0` in `BddSmooth`,
from the one-sided cutoffs. -/
theorem dynkin_ge_of_nonneg (hP : IsDiffusionSemigroup F V Pt) (hV : MSmooth F V)
    (hc : OneSidedCutoffs F V) {f : M → ℝ} (hf : BddSmooth F V f) (hf0 : ∀ y, 0 ≤ f y)
    (x : M) (t : ℝ≥0) :
    f x + ∫ s in (0 : ℝ)..(t : ℝ), ∫ y, mgenerator F V f y ∂Pt s.toNNReal x ≤
      ∫ y, f y ∂Pt t x := by
  obtain ⟨C, χ, hχ, hlim⟩ := hc
  obtain ⟨hfs, Cf₀, hCf₀⟩ := hf
  set Cf : ℝ := |Cf₀| with hCfdef
  have hCf0 : 0 ≤ Cf := abs_nonneg _
  have hfC : ∀ y, f y ≤ Cf := fun y => ((le_abs_self _).trans (hCf₀ y).1).trans (le_abs_self _)
  have hgC : ∀ y, ‖mgrad F f y‖ ≤ Cf := fun y => (hCf₀ y).2.1.trans (le_abs_self _)
  have hLC : ∀ y, |mgenerator F V f y| ≤ Cf := fun y => (hCf₀ y).2.2.trans (le_abs_self _)
  have hlim' : ∀ y, ∀ᶠ n in atTop, χ n y = 1 := fun y => by
    obtain ⟨U, hU, h⟩ := hlim y
    filter_upwards [h] with n hn using hn y (mem_of_mem_nhds hU)
  have hloc : ∀ y, ∀ᶠ n in atTop, mgrad F (χ n) y = 0 ∧ mgenerator F V (χ n) y = 0 := fun y => by
    obtain ⟨U, hU, h⟩ := hlim y
    filter_upwards [h] with n hn
    exact mgrad_mgenerator_eq_zero_of_eventually_one F (hχ n).1
      (Filter.mem_of_superset hU hn)
  have hχ01 : ∀ n y, 0 ≤ χ n y ∧ χ n y ≤ 1 := fun n y =>
    ⟨((hχ n).2.2 y).1, ((hχ n).2.2 y).2.1⟩
  have hLfs : MSmooth F (mgenerator F V f) := msmooth_mgenerator F hV hfs
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hε
  have hεpos : ∀ n, 0 < ε n := fun n => by simp only [hε]; positivity
  have hεle : ∀ n, ε n ≤ 1 := fun n => by
    simp only [hε]
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hεt : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  -- the functions
  set g : ℕ → M → ℝ := fun n y => χ n y * f y with hg
  set K : ℕ → M → ℝ := fun n y => χ n y * mgenerator F V f y with hK
  set ψ : ℕ → M → ℝ := fun n y => Cf * thetaFn (ε n) (mgenerator F V (χ n) y) +
    2 * Cf * Real.sqrt (carre F (χ n) (χ n) y + ε n ^ 2) with hψ
  have hgs : ∀ n, MSmooth F (g n) := fun n => (hχ n).1.mul hfs
  have hKs : ∀ n, MSmooth F (K n) := fun n => (hχ n).1.mul hLfs
  have hψs : ∀ n, MSmooth F (ψ n) := fun n => by
    have h1 := msmooth_thetaFn F (msmooth_mgenerator F hV (hχ n).1) (hεpos n)
    have h2 := msmooth_sqrt_add F ((weightedRegular V hV).1 _ _ (hχ n).1 (hχ n).1)
      (carre_nonneg F (χ n)) (hεpos n).ne'
    exact (contMDiff_const.mul h1).add (contMDiff_const.mul h2)
  have hKb : ∀ n y, |K n y| ≤ Cf := fun n y => by
    simp only [hK, abs_mul]
    calc |χ n y| * |mgenerator F V f y| ≤ 1 * Cf := by
          refine mul_le_mul ?_ (hLC y) (abs_nonneg _) zero_le_one
          rw [abs_of_nonneg (hχ01 n y).1]; exact (hχ01 n y).2
      _ = Cf := one_mul _
  set Kψ : ℝ := 3 * Cf * (|C| + 1) with hKψ
  have hψ0 : ∀ n y, 0 ≤ ψ n y := fun n y => by
    simp only [hψ]
    have := thetaFn_nonneg (ε n) (mgenerator F V (χ n) y)
    positivity
  have hψb : ∀ n y, |ψ n y| ≤ Kψ := fun n y => by
    rw [abs_of_nonneg (hψ0 n y)]
    have h1 : thetaFn (ε n) (mgenerator F V (χ n) y) ≤ |C| + 1 :=
      (thetaFn_le (hεpos n).le ((hχ n).2.2 y).2.2.2).trans (by linarith [hεle n])
    have h2 : Real.sqrt (carre F (χ n) (χ n) y + ε n ^ 2) ≤ |C| + 1 := by
      rw [Real.sqrt_le_left (by positivity), carre_self_eq]
      have h3 : ‖mgrad F (χ n) y‖ ≤ |C| := ((hχ n).2.2 y).2.2.1.trans (le_abs_self _)
      have h4 := hεle n
      have h5 := hεpos n
      nlinarith [norm_nonneg (mgrad F (χ n) y), abs_nonneg C]
    simp only [hψ, hKψ]
    nlinarith [thetaFn_nonneg (ε n) (mgenerator F V (χ n) y), Real.sqrt_nonneg
      (carre F (χ n) (χ n) y + ε n ^ 2)]
  have hmeasK : ∀ n, Measurable fun s : ℝ => ∫ y, K n y ∂Pt s.toNNReal x := fun n =>
    measurable_semi_time_of_cutoffs F hP hV χ (fun n => ⟨(hχ n).1, (hχ n).2.1⟩) hχ01 hlim'
      (hKs n) Cf (hKb n) x
  have hmeasψ : ∀ n, Measurable fun s : ℝ => ∫ y, ψ n y ∂Pt s.toNNReal x := fun n =>
    measurable_semi_time_of_cutoffs F hP hV χ (fun n => ⟨(hχ n).1, (hχ n).2.1⟩) hχ01 hlim'
      (hψs n) Kψ (hψb n) x
  have hmeasL : Measurable fun s : ℝ => ∫ y, mgenerator F V f y ∂Pt s.toNNReal x :=
    measurable_semi_time_of_cutoffs F hP hV χ (fun n => ⟨(hχ n).1, (hχ n).2.1⟩) hχ01 hlim'
      hLfs Cf hLC x
  have hprob : ∀ s : ℝ, IsProbabilityMeasure (Pt s.toNNReal x) := fun s =>
    (hP.1 _).isProbabilityMeasure x
  have hbK : ∀ n (s : ℝ), |∫ y, K n y ∂Pt s.toNNReal x| ≤ Cf := fun n s => by
    haveI := hprob s; exact abs_integral_le_of_prob (hKb n)
  have hbψ : ∀ n (s : ℝ), |∫ y, ψ n y ∂Pt s.toNNReal x| ≤ Kψ := fun n s => by
    haveI := hprob s; exact abs_integral_le_of_prob (hψb n)
  -- pointwise inequality for the generator
  have hpt : ∀ n y, K n y - ψ n y ≤ mgenerator F V (g n) y := fun n y => by
    have := mgenerator_mul_ge (V := V) F (hχ n).1 hfs (ε := ε n) hf0 hfC hgC y
    simp only [hK, hψ, hg]
    linarith
  have hgenint : ∀ n (s : ℝ), Integrable (mgenerator F V (g n)) (Pt s.toNNReal x) := fun n s => by
    haveI := hprob s
    exact ((msmooth_mgenerator F hV (hgs n)).continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_mgenerator F V (hgs n) ((hχ n).2.1.mul_right))
  have hsub : ∀ n (s : ℝ), (∫ y, K n y ∂Pt s.toNNReal x) - ∫ y, ψ n y ∂Pt s.toNNReal x ≤
      ∫ y, mgenerator F V (g n) y ∂Pt s.toNNReal x := fun n s => by
    haveI := hprob s
    rw [← integral_sub (integrable_of_bdd_cont (hKs n).continuous (hKb n))
      (integrable_of_bdd_cont (hψs n).continuous (hψb n))]
    exact integral_mono ((integrable_of_bdd_cont (hKs n).continuous (hKb n)).sub
      (integrable_of_bdd_cont (hψs n).continuous (hψb n))) (hgenint n s) (fun y => hpt n y)
  have hmain : ∀ n, g n x + ((∫ s in (0 : ℝ)..(t : ℝ), ∫ y, K n y ∂Pt s.toNNReal x) -
      ∫ s in (0 : ℝ)..(t : ℝ), ∫ y, ψ n y ∂Pt s.toNNReal x) ≤ ∫ y, f y ∂Pt t x := fun n => by
    have hdyn := hP.2.2 (g n) (hgs n) ((hχ n).2.1.mul_right) x t
    have hJc : Continuous fun s : ℝ => ∫ y, mgenerator F V (g n) y ∂Pt s.toNNReal x :=
      continuous_dynkin_integrand F hP (hgs n) ((hχ n).2.1.mul_right) hV x
    have hiK := intervalIntegrable_of_measurable_bdd (hmeasK n) (hbK n) (0 : ℝ) (t : ℝ)
    have hiψ := intervalIntegrable_of_measurable_bdd (hmeasψ n) (hbψ n) (0 : ℝ) (t : ℝ)
    rw [← intervalIntegral.integral_sub hiK hiψ]
    have h1 : (∫ s in (0 : ℝ)..(t : ℝ), ((∫ y, K n y ∂Pt s.toNNReal x) -
        ∫ y, ψ n y ∂Pt s.toNNReal x)) ≤
        ∫ s in (0 : ℝ)..(t : ℝ), ∫ y, mgenerator F V (g n) y ∂Pt s.toNNReal x :=
      intervalIntegral.integral_mono_on t.coe_nonneg (hiK.sub hiψ)
        (hJc.intervalIntegrable _ _) (fun s _ => hsub n s)
    have h2 : ∫ y, g n y ∂Pt t x ≤ ∫ y, f y ∂Pt t x := by
      haveI := (hP.1 t).isProbabilityMeasure x
      refine integral_mono ((hgs n).continuous.integrable_of_hasCompactSupport
        ((hχ n).2.1.mul_right)) (integrable_of_bdd_cont hfs.continuous (fun y => (hCf₀ y).1))
        (fun y => ?_)
      simp only [hg]
      exact mul_le_of_le_one_left (hf0 y) (hχ01 n y).2
    linarith
  -- limits
  have hgx : Tendsto (fun n => g n x) atTop (𝓝 (f x)) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [hlim' x] with n hn
      simp only [hg, hn, one_mul])
  have hKlim : ∀ s : ℝ, Tendsto (fun n => ∫ y, K n y ∂Pt s.toNNReal x) atTop
      (𝓝 (∫ y, mgenerator F V f y ∂Pt s.toNNReal x)) := fun s => by
    haveI := hprob s
    refine tendsto_integral_of_bdd (fun n => (hKs n).continuous.aestronglyMeasurable) hKb
      (fun y => ?_)
    exact tendsto_const_nhds.congr' (by
      filter_upwards [hlim' y] with n hn
      simp only [hK, hn, one_mul])
  have hψlim : ∀ s : ℝ, Tendsto (fun n => ∫ y, ψ n y ∂Pt s.toNNReal x) atTop
      (𝓝 (∫ y, (0 : ℝ) ∂Pt s.toNNReal x)) := fun s => by
    haveI := hprob s
    refine tendsto_integral_of_bdd (fun n => (hψs n).continuous.aestronglyMeasurable) hψb
      (fun y => ?_)
    have h0 : Tendsto (fun n => Cf * (ε n / 2) + 2 * Cf * ε n) atTop (𝓝 0) := by
      have := ((hεt.div_const 2).const_mul Cf).add (hεt.const_mul (2 * Cf))
      simpa using this
    refine h0.congr' ?_
    filter_upwards [hloc y] with n hn
    have hs : Real.sqrt (carre F (χ n) (χ n) y + ε n ^ 2) = ε n := by
      rw [carre_self_eq, hn.1]
      simp [Real.sqrt_sq (hεpos n).le]
    simp only [hψ, hn.2, hs, thetaFn_zero _ (hεpos n).le]
  have hKint := tendsto_interval_of_bdd hmeasK hbK hKlim (0 : ℝ) (t : ℝ)
  have hψint := tendsto_interval_of_bdd hmeasψ hbψ hψlim (0 : ℝ) (t : ℝ)
  have hall := hgx.add (hKint.sub hψint)
  have := le_of_tendsto' hall hmain
  simpa using this

theorem dynkin_ge_affine (hP : IsDiffusionSemigroup F V Pt) (hV : MSmooth F V)
    (hc : OneSidedCutoffs F V) {f : M → ℝ} (hf : BddSmooth F V f) (a C₀ : ℝ)
    (_hC₀ : ∀ y, |f y| ≤ C₀) (ha : ∀ y, 0 ≤ a * f y + C₀) (x : M) (t : ℝ≥0) :
    (a * f x + C₀) + a * ∫ s in (0 : ℝ)..(t : ℝ), ∫ y, mgenerator F V f y ∂Pt s.toNNReal x ≤
      a * ∫ y, f y ∂Pt t x + C₀ := by
  have h := dynkin_ge_of_nonneg F hP hV hc (hf.affine F a C₀) ha x t
  have hgen : ∀ s : ℝ, (∫ y, mgenerator F V (fun z => a * f z + C₀) y ∂Pt s.toNNReal x) =
      a * ∫ y, mgenerator F V f y ∂Pt s.toNNReal x := fun s => by
    simp only [hf.generator_affine F a C₀, integral_const_mul]
  simp only [hgen, intervalIntegral.integral_const_mul] at h
  obtain ⟨C, hC⟩ := hf.2
  haveI := (hP.1 t).isProbabilityMeasure x
  have hint : Integrable f (Pt t x) :=
    integrable_of_bdd_cont hf.1.continuous (fun y => (hC y).1)
  have : ∫ y, (a * f y + C₀) ∂Pt t x = a * ∫ y, f y ∂Pt t x + C₀ := by
    rw [integral_add (hint.const_mul a) (integrable_const _), integral_const_mul]
    simp
  rw [this] at h
  exact h

/-- **B1.** Dynkin's identity for `BddSmooth` functions, from `IsDiffusionSemigroup` and
`OneSidedCutoffs` (the mass trick: apply the one-sided inequality to `f + C₀` and `C₀ - f`). -/
theorem dynkinBounded_of_oneSidedCutoffs (hP : IsDiffusionSemigroup F V Pt) (hV : MSmooth F V)
    (hc : OneSidedCutoffs F V) : DynkinBounded F V Pt := by
  intro f hf x t
  obtain ⟨C, hC⟩ := hf.2
  set C₀ := |C|
  have hb : ∀ y, |f y| ≤ C₀ := fun y => (hC y).1.trans (le_abs_self _)
  have h1 := dynkin_ge_affine F hP hV hc hf 1 C₀ hb
    (fun y => by have := neg_abs_le (f y); have := hb y; linarith [neg_le_abs (f y)]) x t
  have h2 := dynkin_ge_affine F hP hV hc hf (-1) C₀ hb
    (fun y => by have := hb y; linarith [le_abs_self (f y)]) x t
  apply le_antisymm
  · linarith
  · linarith

end Dyn

end Calculus

end CutoffRigidity.Riemann.Diff
