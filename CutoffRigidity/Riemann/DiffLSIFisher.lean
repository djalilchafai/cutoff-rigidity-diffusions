module

public import CutoffRigidity.Riemann.DiffLSIBruijn

/-! # LSI from strong Bakry-Emery: analytic helpers and the Fisher information bound
(workstream BE, part E2).  Pure measure-theoretic lemmas (Cauchy-Schwarz, entropy versus variance,
the `delta -> 0` limit) followed by the semigroup estimates `I(t) <= 4 e^{-2 rho t} int Gamma f`
and `int Gamma (K_T g) <= e^{-2 rho T} int Gamma g`. -/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set
open scoped Manifold ContDiff ENNReal NNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur


theorem cs_int {α : Type*} [MeasurableSpace α] {ν : Measure α} {p q : α → ℝ}
    (hp : MemLp p 2 ν) (hq : MemLp q 2 ν) :
    (∫ x, p x * q x ∂ν) ^ 2 ≤ (∫ x, p x ^ 2 ∂ν) * (∫ x, q x ^ 2 ∂ν) := by
  have hp2 := hp.integrable_sq
  have hq2 := hq.integrable_sq
  have hpq : Integrable (fun x => p x * q x) ν := hp.integrable_mul hq
  have key : ∀ t : ℝ, 0 ≤ (∫ x, q x ^ 2 ∂ν) * (t * t) + (-2 * ∫ x, p x * q x ∂ν) * t + ∫ x, p x ^ 2 ∂ν := by
    intro t
    have h0 : 0 ≤ ∫ x, (p x - t * q x) ^ 2 ∂ν := integral_nonneg fun x => sq_nonneg _
    have e1 : ∫ x, (p x - t * q x) ^ 2 ∂ν =
        ∫ x, (p x ^ 2 - 2 * t * (p x * q x)) ∂ν + ∫ x, t ^ 2 * q x ^ 2 ∂ν := by
      have := integral_add (μ := ν) (f := fun x => p x ^ 2 - 2 * t * (p x * q x))
        (g := fun x => t ^ 2 * q x ^ 2) (hp2.sub (hpq.const_mul _)) (hq2.const_mul _)
      exact (integral_congr_ae (Eventually.of_forall fun x => by ring)).trans this
    rw [e1, integral_sub hp2 (hpq.const_mul _), integral_const_mul, integral_const_mul] at h0
    nlinarith [h0]
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith [this]

theorem bdd_mul_log {B : ℝ} : ∃ K : ℝ, ∀ y ∈ Icc (0:ℝ) B, |y * Real.log y| ≤ K := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := fun y : ℝ => y * Real.log y)
    (Real.continuous_mul_log.continuousOn)
  exact ⟨K, fun y hy => by simpa using hK y hy⟩

theorem entropy_le_var {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {w : α → ℝ} (hw0 : ∀ x, 0 ≤ w x) (hwm : Measurable w) {B : ℝ} (hB : ∀ x, w x ≤ B)
    {δ : ℝ} (hδ : 0 < δ) :
    ∫ x, (w x + δ) * Real.log (w x + δ) ∂μ ≤
      (∫ x, w x ∂μ + δ) * Real.log (∫ x, w x ∂μ + δ) + (∫ x, (w x - ∫ y, w y ∂μ) ^ 2 ∂μ) / (∫ x, w x ∂μ + δ) := by
  set a := ∫ x, w x ∂μ with ha
  have hwi : Integrable w μ := Integrable.of_bound hwm.aestronglyMeasurable B
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hw0 x)]; exact hB x)
  have ha0 : 0 ≤ a := integral_nonneg hw0
  have hm : 0 < a + δ := by linarith
  set m := a + δ with hmdef
  have hlogm : ∀ x, (w x + δ) * Real.log (w x + δ) ≤
      (w x + δ) * Real.log m + ((w x - a) ^ 2 / m + (w x - a)) := by
    intro x
    have hh : 0 < w x + δ := by linarith [hw0 x]
    have h1 : Real.log ((w x + δ) / m) ≤ (w x + δ) / m - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div hh.ne' hm.ne'] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 hh.le
    have e : (w x + δ) * ((w x + δ) / m - 1) = (w x - a) ^ 2 / m + (w x - a) := by
      field_simp; rw [hmdef]; ring
    nlinarith [h2, e]
  obtain ⟨K, hK⟩ := bdd_mul_log (B := B + δ)
  have i1 : Integrable (fun x => (w x + δ) * Real.log (w x + δ)) μ := by
    refine Integrable.of_bound ((Real.continuous_mul_log.measurable.comp (hwm.add_const δ)).aestronglyMeasurable) K
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    exact hK _ ⟨by linarith [hw0 x], by linarith [hB x]⟩
  have iw : Integrable (fun x => w x + δ) μ := hwi.add (integrable_const δ)
  have i2 : Integrable (fun x => (w x + δ) * Real.log m) μ := iw.mul_const _
  have iv : Integrable (fun x => (w x - a) ^ 2) μ := by
    refine Integrable.of_bound ((hwm.sub_const a).pow_const 2).aestronglyMeasurable ((B + a) ^ 2)
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have : |w x - a| ≤ B + a := by
      rw [abs_le]; constructor <;> linarith [hw0 x, hB x]
    calc (w x - a) ^ 2 = |w x - a| ^ 2 := (sq_abs _).symm
      _ ≤ (B + a) ^ 2 := by gcongr
  have i3 : Integrable (fun x => (w x - a) ^ 2 / m + (w x - a)) μ :=
    (iv.div_const m).add (hwi.sub (integrable_const a))
  have h : ∫ x, (w x + δ) * Real.log (w x + δ) ∂μ ≤
      ∫ x, ((w x + δ) * Real.log m + ((w x - a) ^ 2 / m + (w x - a))) ∂μ :=
    integral_mono i1 (i2.add i3) hlogm
  have e1 : ∫ x, (w x - a) ∂μ = 0 := by
    rw [integral_sub hwi (integrable_const a)]; simp [ha]
  have e2 : ∫ x, ((w x - a) ^ 2 / m + (w x - a)) ∂μ = (∫ x, (w x - a) ^ 2 ∂μ) / m := by
    have := integral_add (μ := μ) (f := fun x => (w x - a) ^ 2 / m) (g := fun x => w x - a)
      (iv.div_const m) (hwi.sub (integrable_const a))
    rw [this, integral_div, e1, add_zero]
  have e3 : ∫ x, (w x + δ) * Real.log m ∂μ = m * Real.log m := by
    rw [integral_mul_const, integral_add hwi (integrable_const δ)]; simp [ha, hmdef]
  rw [integral_add i2 i3, e2, e3] at h
  exact h

theorem ent_delta_limit {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {g : α → ℝ} (hg0 : ∀ x, 0 ≤ g x) (hgm : Measurable g) {R : ℝ} (hR : ∀ x, g x ≤ R) {B : ℝ}
    (hB : ∀ δ : ℝ, 0 < δ → ∫ x, (g x + δ) * Real.log (g x + δ) ∂μ -
      (∫ x, g x ∂μ + δ) * Real.log (∫ x, g x ∂μ + δ) ≤ B) :
    ∫ x, g x * Real.log (g x) ∂μ - (∫ x, g x ∂μ) * Real.log (∫ x, g x ∂μ) ≤ B := by
  obtain ⟨K, hK⟩ := bdd_mul_log (B := R + 1)
  have hφ : Continuous fun y : ℝ => y * Real.log y := Real.continuous_mul_log
  have h1 : Tendsto (fun δ : ℝ => ∫ x, (g x + δ) * Real.log (g x + δ) ∂μ) (𝓝[>] 0)
      (𝓝 (∫ x, g x * Real.log (g x) ∂μ)) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝[>] (0:ℝ))
      (F := fun δ x => (g x + δ) * Real.log (g x + δ)) (f := fun x => g x * Real.log (g x))
      (bound := fun _ => K) ?_ ?_ ?_ ?_
    · exact this
    · exact Eventually.of_forall fun δ =>
        (hφ.measurable.comp (hgm.add_const δ)).aestronglyMeasurable
    · have : ∀ᶠ δ in 𝓝[>] (0:ℝ), δ ∈ Ioo (0:ℝ) 1 := Ioo_mem_nhdsGT one_pos
      filter_upwards [this] with δ hδ
      refine Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs]
      exact hK _ ⟨by linarith [hg0 x, hδ.1], by linarith [hR x, hδ.2]⟩
    · exact integrable_const K
    · refine Eventually.of_forall fun x => ?_
      have : Tendsto (fun δ : ℝ => g x + δ) (𝓝[>] 0) (𝓝 (g x)) := by
        have : Tendsto (fun δ : ℝ => g x + δ) (𝓝 0) (𝓝 (g x + 0)) :=
          (continuous_const.add continuous_id).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      exact (hφ.tendsto _).comp this
  have h2 : Tendsto (fun δ : ℝ => (∫ x, g x ∂μ + δ) * Real.log (∫ x, g x ∂μ + δ)) (𝓝[>] 0)
      (𝓝 ((∫ x, g x ∂μ) * Real.log (∫ x, g x ∂μ))) := by
    have : Tendsto (fun δ : ℝ => ∫ x, g x ∂μ + δ) (𝓝[>] 0) (𝓝 (∫ x, g x ∂μ)) := by
      have : Tendsto (fun δ : ℝ => ∫ x, g x ∂μ + δ) (𝓝 0) (𝓝 (∫ x, g x ∂μ + 0)) :=
        (continuous_const.add continuous_id).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    exact (hφ.tendsto _).comp this
  refine le_of_tendsto (h1.sub h2) ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact hB δ hδ


section Fisher

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} {μ : Measure M} [IsFiniteMeasure μ] {Kk : ℝ≥0 → Kernel M M}

/-- The square `f²` of a test function, as a test function. -/
noncomputable def sqf (f : testSub F M) : testSub F M :=
  ⟨fun x => (f : M → ℝ) x ^ 2,
    ⟨by
      have e : (fun x => (f : M → ℝ) x ^ 2) = fun x => (f : M → ℝ) x * (f : M → ℝ) x :=
        funext fun x => sq _
      rw [e]; exact f.2.1.mul f.2.1,
      f.2.2.comp_left (g := fun y : ℝ => y ^ 2) (by simp)⟩⟩

theorem sqf_apply (f : testSub F M) (x : M) : (sqf F f : M → ℝ) x = (f : M → ℝ) x ^ 2 := rfl

theorem norm_mgrad_sqf (f : testSub F M) (x : M) :
    ‖mgrad F (sqf F f : M → ℝ) x‖ = 2 * |(f : M → ℝ) x| * ‖mgrad F (f : M → ℝ) x‖ := by
  have h := mgrad_comp_real F (θ := fun y : ℝ => y ^ 2) (by fun_prop) f.2.1 x
  have e : (sqf F f : M → ℝ) = (fun y : ℝ => y ^ 2) ∘ (f : M → ℝ) := rfl
  rw [e, h, norm_smul]
  have : deriv (fun y : ℝ => y ^ 2) ((f : M → ℝ) x) = 2 * (f : M → ℝ) x := by simp
  rw [this, Real.norm_eq_abs, abs_mul, abs_two]

/-- Probability-kernel bound: `|K_t h| ≤ C` if `|h| ≤ C`. -/
theorem semi_abs_le_lsi (hK : KerCanonical F V μ Kk) {h : M → ℝ} {C : ℝ} (hC : ∀ x, |h x| ≤ C)
    (t : ℝ≥0) (x : M) : |semi Kk t h x| ≤ C := by
  haveI := hK.markov t
  have := norm_integral_le_of_norm_le_const (μ := Kk t x) (f := h) (C := C)
    (Eventually.of_forall fun y => by simpa using hC y)
  simpa [semi] using this

theorem semi_measurable {h : M → ℝ} (hh : Measurable h) (t : ℝ≥0) : Measurable (semi Kk t h) :=
  (hh.stronglyMeasurable.integral_kernel (κ := Kk t)).measurable

theorem semi_nonneg' {h : M → ℝ} (hh : ∀ x, 0 ≤ h x) (t : ℝ≥0) (x : M) : 0 ≤ semi Kk t h x :=
  integral_nonneg hh

/-- `Γ f` is continuous, nonnegative, and bounded for a test function. -/
theorem carre_bdd (hReg : WeightedRegular F V) (f : testSub F M) :
    Continuous (fun x => carre F (f : M → ℝ) (f : M → ℝ) x) ∧
    ∃ C, ∀ x, |carre F (f : M → ℝ) (f : M → ℝ) x| ≤ C := by
  have hc := (hReg.1 _ _ f.2.1 f.2.1).continuous
  refine ⟨hc, ?_⟩
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support (hasCompactSupport_carre F (f : M → ℝ) f.2.2)
  exact ⟨C, fun x => by simpa using hC x⟩

/-- Pointwise Fisher information bound. -/
theorem fisher_pt (hK : KerCanonical F V μ Kk) (hReg : WeightedRegular F V) {ρ : ℝ}
    (hBE : ∀ (f : testSub F M) (t : ℝ≥0) (x : M), ‖mgrad F (semi Kk t (f : M → ℝ)) x‖ ≤
        Real.exp (-ρ * t) * ∫ y, ‖mgrad F (f : M → ℝ) y‖ ∂Kk t x)
    (f : testSub F M) {δ : ℝ} (hδ : 0 < δ) (t : ℝ≥0) (x : M) :
    carre F (semi Kk t (sqf F f : M → ℝ)) (semi Kk t (sqf F f : M → ℝ)) x /
        (semi Kk t (sqf F f : M → ℝ) x + δ) ≤
      4 * Real.exp (-2 * ρ * t) * semi Kk t (fun y => carre F (f : M → ℝ) (f : M → ℝ) y) x := by
  haveI := hK.markov t
  set ν := Kk t x with hν
  obtain ⟨hGc, C0, hC0⟩ := carre_bdd F hReg f
  obtain ⟨Cf, hCf⟩ := testSub_bounded F f
  set p : M → ℝ := fun y => Real.sqrt (carre F (f : M → ℝ) (f : M → ℝ) y) with hp
  set q : M → ℝ := fun y => |(f : M → ℝ) y| with hq
  have hpq : ∀ y, ‖mgrad F (f : M → ℝ) y‖ = p y := fun y => by
    rw [hp]; simp only; rw [carre_self_eq, Real.sqrt_sq (norm_nonneg _)]
  have hp2 : ∀ y, p y ^ 2 = carre F (f : M → ℝ) (f : M → ℝ) y := fun y =>
    Real.sq_sqrt (carre_nonneg F _ y)
  have hpm : MemLp p 2 ν := MemLp.of_bound (hGc.sqrt.aestronglyMeasurable) (Real.sqrt C0)
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt ((le_abs_self _).trans (hC0 y)))
  have hqm : MemLp q 2 ν := MemLp.of_bound
    ((testSub_continuous F f).abs.aestronglyMeasurable) Cf
    (Eventually.of_forall fun y => by simpa [hq] using hCf y)
  have hcs := cs_int hpm hqm
  have hgs : ‖mgrad F (semi Kk t (sqf F f : M → ℝ)) x‖ ≤
      Real.exp (-ρ * t) * (2 * ∫ y, p y * q y ∂ν) := by
    refine (hBE (sqf F f) t x).trans ?_
    gcongr
    have : ∀ y, ‖mgrad F (sqf F f : M → ℝ) y‖ = 2 * (p y * q y) := fun y => by
      rw [norm_mgrad_sqf, hpq]; simp only [hq]; ring
    simp_rw [this]
    rw [integral_const_mul]
  set s := semi Kk t (sqf F f : M → ℝ) x with hs
  have hs0 : 0 ≤ s := integral_nonneg fun y => by simp [sqf_apply]; positivity
  have hsq : s = ∫ y, q y ^ 2 ∂ν := by
    simp only [hs, semi, hq, sqf_apply, sq_abs, hν]
  have hGp : semi Kk t (fun y => carre F (f : M → ℝ) (f : M → ℝ) y) x = ∫ y, p y ^ 2 ∂ν := by
    simp only [semi, hp2, hν]
  have hA0 : 0 ≤ ∫ y, p y ^ 2 ∂ν := integral_nonneg fun y => sq_nonneg _
  have hex : 0 < Real.exp (-ρ * t) := Real.exp_pos _
  have hexx : Real.exp (-2 * ρ * t) = Real.exp (-ρ * t) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [carre_self_eq, hGp, div_le_iff₀ (by linarith), hexx]
  have h1 : ‖mgrad F (semi Kk t (sqf F f : M → ℝ)) x‖ ^ 2 ≤
      (Real.exp (-ρ * t) * (2 * ∫ y, p y * q y ∂ν)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hgs 2
  have h2 : (Real.exp (-ρ * t) * (2 * ∫ y, p y * q y ∂ν)) ^ 2 ≤
      4 * Real.exp (-ρ * t) ^ 2 * (∫ y, p y ^ 2 ∂ν) * s := by
    rw [hsq]
    have : (Real.exp (-ρ * t) * (2 * ∫ y, p y * q y ∂ν)) ^ 2 =
        4 * Real.exp (-ρ * t) ^ 2 * (∫ y, p y * q y ∂ν) ^ 2 := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_left hcs (by positivity : 0 ≤ 4 * Real.exp (-ρ * t) ^ 2)
    nlinarith [this]
  have h3 : 0 ≤ 4 * Real.exp (-ρ * t) ^ 2 * (∫ y, p y ^ 2 ∂ν) := by positivity
  nlinarith [h1, h2, h3, mul_nonneg h3 hδ.le]

/-- Integrated Fisher information bound `I(t) ≤ 4 e^{-2ρt} ∫ Γ f`. -/
theorem fisher_int (hK : KerCanonical F V μ Kk) (hReg : WeightedRegular F V) {ρ : ℝ}
    (hBE : ∀ (f : testSub F M) (t : ℝ≥0) (x : M), ‖mgrad F (semi Kk t (f : M → ℝ)) x‖ ≤
        Real.exp (-ρ * t) * ∫ y, ‖mgrad F (f : M → ℝ) y‖ ∂Kk t x)
    (f : testSub F M) {δ : ℝ} (hδ : 0 < δ) (t : ℝ≥0) :
    ∫ x, carre F (semi Kk t (sqf F f : M → ℝ)) (semi Kk t (sqf F f : M → ℝ)) x /
        (semi Kk t (sqf F f : M → ℝ) x + δ) ∂μ ≤
      4 * Real.exp (-2 * ρ * t) * ∫ x, carre F (f : M → ℝ) (f : M → ℝ) x ∂μ := by
  obtain ⟨hGc, C0, hC0⟩ := carre_bdd F hReg f
  have hmK : Measurable (semi Kk t (fun y => carre F (f : M → ℝ) (f : M → ℝ) y)) :=
    semi_measurable hGc.measurable t
  have hbK := semi_abs_le_lsi F hK hC0 t
  have hint : Integrable (fun x => 4 * Real.exp (-2 * ρ * t) *
      semi Kk t (fun y => carre F (f : M → ℝ) (f : M → ℝ) y) x) μ :=
    (Integrable.of_bound hmK.aestronglyMeasurable C0
      (Eventually.of_forall fun x => by simpa using hbK x)).const_mul _
  calc _ ≤ ∫ x, 4 * Real.exp (-2 * ρ * t) *
        semi Kk t (fun y => carre F (f : M → ℝ) (f : M → ℝ) y) x ∂μ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x => ?_) hint
          (Eventually.of_forall fun x => fisher_pt F hK hReg hBE f hδ t x)
        refine div_nonneg (carre_nonneg F _ x) ?_
        have := semi_nonneg' (Kk := Kk) (h := (sqf F f : M → ℝ)) (fun y => by
          simp only [sqf_apply]; positivity) t x
        linarith
    _ = _ := by
        rw [integral_const_mul, integral_semi F hK hGc.measurable ⟨C0, hC0⟩ t]

/-- `‖∇ K_T g‖² ≤ e^{-2ρT} K_T (Γ g)` pointwise. -/
theorem grad_decay_pt (hK : KerCanonical F V μ Kk) (hReg : WeightedRegular F V) {ρ : ℝ}
    (hBE : ∀ (f : testSub F M) (t : ℝ≥0) (x : M), ‖mgrad F (semi Kk t (f : M → ℝ)) x‖ ≤
        Real.exp (-ρ * t) * ∫ y, ‖mgrad F (f : M → ℝ) y‖ ∂Kk t x)
    (g : testSub F M) (T : ℝ≥0) (x : M) :
    carre F (semi Kk T (g : M → ℝ)) (semi Kk T (g : M → ℝ)) x ≤
      Real.exp (-2 * ρ * T) * semi Kk T (fun y => carre F (g : M → ℝ) (g : M → ℝ) y) x := by
  haveI := hK.markov T
  set ν := Kk T x with hν
  obtain ⟨hGc, C0, hC0⟩ := carre_bdd F hReg g
  set a : M → ℝ := fun y => Real.sqrt (carre F (g : M → ℝ) (g : M → ℝ) y) with ha
  have hpq : ∀ y, ‖mgrad F (g : M → ℝ) y‖ = a y := fun y => by
    rw [ha]; simp only; rw [carre_self_eq, Real.sqrt_sq (norm_nonneg _)]
  have ha2 : ∀ y, a y ^ 2 = carre F (g : M → ℝ) (g : M → ℝ) y := fun y =>
    Real.sq_sqrt (carre_nonneg F _ y)
  have ham : MemLp a 2 ν := MemLp.of_bound (hGc.sqrt.aestronglyMeasurable) (Real.sqrt C0)
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt ((le_abs_self _).trans (hC0 y)))
  have h1m : MemLp (fun _ : M => (1 : ℝ)) 2 ν := memLp_const 1
  have hcs := cs_int ham h1m
  simp only [mul_one, one_pow, integral_const, probReal_univ, smul_eq_mul] at hcs
  have hgs := hBE g T x
  simp_rw [hpq] at hgs
  have hex : 0 < Real.exp (-ρ * T) := Real.exp_pos _
  have hexx : Real.exp (-2 * ρ * T) = Real.exp (-ρ * T) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hGp : semi Kk T (fun y => carre F (g : M → ℝ) (g : M → ℝ) y) x = ∫ y, a y ^ 2 ∂ν := by
    simp only [semi, ha2, hν]
  rw [carre_self_eq, hGp, hexx]
  have h1 := pow_le_pow_left₀ (norm_nonneg _) hgs 2
  rw [mul_pow] at h1
  nlinarith [mul_le_mul_of_nonneg_left hcs (sq_nonneg (Real.exp (-ρ * T)))]

/-- `∫ Γ(K_T g) ≤ e^{-2ρT} ∫ Γ g`. -/
theorem grad_decay_int (hK : KerCanonical F V μ Kk) (hReg : WeightedRegular F V) {ρ : ℝ}
    (hBE : ∀ (f : testSub F M) (t : ℝ≥0) (x : M), ‖mgrad F (semi Kk t (f : M → ℝ)) x‖ ≤
        Real.exp (-ρ * t) * ∫ y, ‖mgrad F (f : M → ℝ) y‖ ∂Kk t x)
    (g : testSub F M) (T : ℝ≥0) :
    ∫ x, carre F (semi Kk T (g : M → ℝ)) (semi Kk T (g : M → ℝ)) x ∂μ ≤
      Real.exp (-2 * ρ * T) * ∫ x, carre F (g : M → ℝ) (g : M → ℝ) x ∂μ := by
  obtain ⟨hGc, C0, hC0⟩ := carre_bdd F hReg g
  have hmK : Measurable (semi Kk T (fun y => carre F (g : M → ℝ) (g : M → ℝ) y)) :=
    semi_measurable hGc.measurable T
  have hbK := semi_abs_le_lsi F hK hC0 T
  have hint : Integrable (fun x => Real.exp (-2 * ρ * T) *
      semi Kk T (fun y => carre F (g : M → ℝ) (g : M → ℝ) y) x) μ :=
    (Integrable.of_bound hmK.aestronglyMeasurable C0
      (Eventually.of_forall fun x => by simpa using hbK x)).const_mul _
  calc _ ≤ ∫ x, Real.exp (-2 * ρ * T) *
        semi Kk T (fun y => carre F (g : M → ℝ) (g : M → ℝ) y) x ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => carre_nonneg F _ x) hint
          (Eventually.of_forall fun x => grad_decay_pt F hK hReg hBE g T x)
    _ = _ := by
        rw [integral_const_mul, integral_semi F hK hGc.measurable ⟨C0, hC0⟩ T]

end Fisher

end CutoffRigidity.Riemann.Diff
