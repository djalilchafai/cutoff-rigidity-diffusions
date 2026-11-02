module

public import Mathlib

/-! # Gaussian isoperimetric profile (stage 1 of the Bobkov inequality)

`gφ` standard normal density, `gΦ` its cdf, `gQ = gΦ⁻¹`, `gI = gφ ∘ gQ` on `(0,1)` (and `0` elsewhere).
Facts: `gI' = -gQ`, `gI'' = -1/gI` on `(0,1)`.  Also the Stein lemma `∫ y k dγ = ∫ k' dγ`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal

namespace CutoffRigidity.GaussIso

/-- Standard normal density. -/
noncomputable def gφ (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

/-- Standard normal cdf. -/
noncomputable def gΦ (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

lemma gφ_eq (x : ℝ) : gφ x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) := by
  simp [gφ, gaussianPDFReal_def]

lemma gφ_pos (x : ℝ) : 0 < gφ x := gaussianPDFReal_pos 0 1 x one_ne_zero

lemma continuous_gφ : Continuous gφ := by
  have : gφ = fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) := funext gφ_eq
  rw [this]; fun_prop

lemma hasDerivAt_gφ (x : ℝ) : HasDerivAt gφ (-x * gφ x) x := by
  have : gφ = fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) := funext gφ_eq
  rw [this]
  have h1 : HasDerivAt (fun x : ℝ => -(x ^ 2) / 2) (-x) x := by
    have := ((hasDerivAt_pow 2 x).neg).div_const 2
    convert this using 1; simp; ring
  have h2 := (h1.exp).const_mul ((Real.sqrt (2 * Real.pi))⁻¹)
  convert h2 using 1
  ring

lemma integrable_gφ : Integrable gφ := integrable_gaussianPDFReal 0 1

lemma gφ_le (x : ℝ) : gφ x ≤ gφ 0 := by
  rw [gφ_eq, gφ_eq]
  have : Real.exp (-(x ^ 2) / 2) ≤ Real.exp (-(0 ^ 2) / 2) :=
    Real.exp_le_exp.2 (by nlinarith [sq_nonneg x])
  have hp : 0 < (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  exact mul_le_mul_of_nonneg_left this hp.le

lemma gΦ_eq_integral (x : ℝ) : gΦ x = ∫ t in Iic x, gφ t := by
  have h : cdf (gaussianReal 0 1) x = (gaussianReal 0 1).real (Iic x) := cdf_eq_real (gaussianReal 0 1) x
  rw [gΦ, h, Measure.real, gaussianReal_apply_eq_integral 0 one_ne_zero (Iic x)]
  rw [ENNReal.toReal_ofReal]
  · rfl
  · exact setIntegral_nonneg measurableSet_Iic fun t _ => (gφ_pos t).le

lemma hasDerivAt_gΦ (x : ℝ) : HasDerivAt gΦ (gφ x) x := by
  have hint : ∀ a b : ℝ, IntervalIntegrable gφ volume a b := fun a b =>
    continuous_gφ.intervalIntegrable a b
  have key : ∀ y, gΦ y = gΦ 0 + ∫ t in (0 : ℝ)..y, gφ t := by
    intro y
    rw [gΦ_eq_integral, gΦ_eq_integral, ← intervalIntegral.integral_Iic_sub_Iic
      integrable_gφ.integrableOn integrable_gφ.integrableOn]
    ring
  have : gΦ = fun y => gΦ 0 + ∫ t in (0 : ℝ)..y, gφ t := funext key
  rw [this]
  exact (intervalIntegral.integral_hasDerivAt_right (hint 0 x)
    continuous_gφ.aestronglyMeasurable.stronglyMeasurableAtFilter
    continuous_gφ.continuousAt).const_add _

lemma continuous_gΦ : Continuous gΦ := continuous_iff_continuousAt.2 fun x => (hasDerivAt_gΦ x).continuousAt

lemma strictMono_gΦ : StrictMono gΦ :=
  strictMono_of_deriv_pos fun x => by rw [(hasDerivAt_gΦ x).deriv]; exact gφ_pos x

lemma tendsto_gΦ_atBot : Tendsto gΦ atBot (𝓝 0) := tendsto_cdf_atBot _
lemma tendsto_gΦ_atTop : Tendsto gΦ atTop (𝓝 1) := tendsto_cdf_atTop _

lemma gΦ_pos (x : ℝ) : 0 < gΦ x :=
  lt_of_le_of_lt (strictMono_gΦ.monotone.le_of_tendsto tendsto_gΦ_atBot (x - 1))
    (strictMono_gΦ (by linarith))

lemma gΦ_lt_one (x : ℝ) : gΦ x < 1 :=
  lt_of_lt_of_le (strictMono_gΦ (show x < x + 1 by linarith))
    (strictMono_gΦ.monotone.ge_of_tendsto tendsto_gΦ_atTop (x + 1))

lemma gΦ_surj {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) : ∃ x, gΦ x = u := by
  obtain ⟨a, ha⟩ := eventually_atBot.1 (tendsto_gΦ_atBot.eventually (gt_mem_nhds hu.1))
  obtain ⟨b, hb⟩ := eventually_atTop.1 (tendsto_gΦ_atTop.eventually (lt_mem_nhds hu.2))
  have h1 : gΦ (min a b) < u := ha _ (min_le_left _ _)
  have h2 : u < gΦ (max a b) := hb _ (le_max_right _ _)
  obtain ⟨x, -, hx⟩ := intermediate_value_Icc (min_le_max (a := a) (b := b))
    continuous_gΦ.continuousOn ⟨h1.le, h2.le⟩
  exact ⟨x, hx⟩

open Classical in
/-- The Gaussian quantile function `Φ⁻¹` (value `0` outside `(0,1)`). -/
noncomputable def gQ (u : ℝ) : ℝ :=
  if h : ∃ x, gΦ x = u then Classical.choose h else 0

lemma gΦ_gQ {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) : gΦ (gQ u) = u := by
  have h := gΦ_surj hu
  rw [gQ, dif_pos h]; exact Classical.choose_spec h

lemma gQ_gΦ (x : ℝ) : gQ (gΦ x) = x := by
  have h : ∃ y, gΦ y = gΦ x := ⟨x, rfl⟩
  rw [gQ, dif_pos h]
  exact strictMono_gΦ.injective (Classical.choose_spec h)

lemma gΦ_mem (x : ℝ) : gΦ x ∈ Ioo (0:ℝ) 1 := ⟨gΦ_pos x, gΦ_lt_one x⟩

lemma strictMonoOn_gQ : StrictMonoOn gQ (Ioo (0:ℝ) 1) := by
  intro u hu v hv huv
  by_contra h
  rw [not_lt] at h
  have := strictMono_gΦ.monotone h
  rw [gΦ_gQ hu, gΦ_gQ hv] at this
  linarith

lemma continuousAt_gQ {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) : ContinuousAt gQ u := by
  refine strictMonoOn_gQ.continuousAt_of_image_mem_nhds (Ioo_mem_nhds hu.1 hu.2) ?_
  have : gQ '' Ioo (0:ℝ) 1 = univ := by
    refine eq_univ_of_forall fun x => ⟨gΦ x, gΦ_mem x, gQ_gΦ x⟩
  rw [this]; exact univ_mem

lemma hasDerivAt_gQ {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) :
    HasDerivAt gQ (gφ (gQ u))⁻¹ u := by
  refine HasDerivAt.of_local_left_inverse (f := gΦ) (continuousAt_gQ hu) (hasDerivAt_gΦ (gQ u))
    (gφ_pos _).ne' ?_
  · filter_upwards [Ioo_mem_nhds hu.1 hu.2] with y hy using gΦ_gQ hy

/-- The isoperimetric profile `I = φ ∘ Φ⁻¹` on `(0,1)`, `0` elsewhere. -/
noncomputable def gI (u : ℝ) : ℝ := if u ∈ Ioo (0:ℝ) 1 then gφ (gQ u) else 0

lemma gI_of_mem {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) : gI u = gφ (gQ u) := if_pos hu

lemma gI_pos {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) : 0 < gI u := by
  rw [gI_of_mem hu]; exact gφ_pos _

lemma gI_nonneg (u : ℝ) : 0 ≤ gI u := by
  unfold gI; split_ifs
  · exact (gφ_pos _).le
  · exact le_rfl

lemma gI_le (u : ℝ) : gI u ≤ gφ 0 := by
  unfold gI; split_ifs
  · exact gφ_le _
  · exact (gφ_pos 0).le

/-- `I' = -Φ⁻¹`. -/
lemma hasDerivAt_gI {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) : HasDerivAt gI (-gQ u) u := by
  have h1 := (hasDerivAt_gφ (gQ u)).comp u (hasDerivAt_gQ hu)
  have h2 : (-gQ u * gφ (gQ u)) * (gφ (gQ u))⁻¹ = -gQ u := by
    field_simp [(gφ_pos (gQ u)).ne']
  rw [h2] at h1
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hu.1 hu.2] with y hy
  simp [gI_of_mem hy]

/-- `I'' = -1/I`, i.e. `I I'' = -1`. -/
lemma hasDerivAt_neg_gQ {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (fun y => -gQ y) (-(gI u)⁻¹) u := by
  have := (hasDerivAt_gQ hu).neg
  rwa [← gI_of_mem hu] at this

lemma gI_mul_second {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) : gI u * (-(gI u)⁻¹) = -1 := by
  have := (gI_pos hu).ne'
  field_simp

lemma tendsto_gφ_cocompact : Tendsto gφ (cocompact ℝ) (𝓝 0) := by
  have : gφ = fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(‖x‖ ^ 2) / 2) := by
    funext x; rw [gφ_eq]; simp
  rw [this]
  have h1 : Tendsto (fun x : ℝ => -(‖x‖ ^ 2) / 2) (cocompact ℝ) atBot := by
    have := tendsto_norm_cocompact_atTop (E := ℝ)
    have h2 : Tendsto (fun t : ℝ => -(t ^ 2) / 2) atTop atBot := by
      refine tendsto_atBot_mono' _ ?_ (tendsto_neg_atTop_atBot.comp (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop))
      filter_upwards [eventually_ge_atTop 2] with t ht
      simp only [Function.comp, id]; nlinarith
    exact h2.comp this
  simpa using (Real.tendsto_exp_atBot.comp h1).const_mul (Real.sqrt (2 * Real.pi))⁻¹

lemma tendsto_gQ_zero : Tendsto gQ (𝓝[>] 0) atBot := by
  refine tendsto_atBot.2 fun M => ?_
  have hM := gΦ_pos M
  have : Ioo (0:ℝ) (gΦ M) ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT hM
  filter_upwards [this] with u hu
  have hu' : u ∈ Ioo (0:ℝ) 1 := ⟨hu.1, hu.2.trans (gΦ_lt_one M)⟩
  have := strictMonoOn_gQ hu' (gΦ_mem M) hu.2
  rw [gQ_gΦ] at this
  exact this.le

lemma tendsto_gQ_one : Tendsto gQ (𝓝[<] 1) atTop := by
  refine tendsto_atTop.2 fun M => ?_
  have hM := gΦ_lt_one M
  have : Ioo (gΦ M) 1 ∈ 𝓝[<] (1:ℝ) := Ioo_mem_nhdsLT hM
  filter_upwards [this] with u hu
  have hu' : u ∈ Ioo (0:ℝ) 1 := ⟨(gΦ_pos M).trans hu.1, hu.2⟩
  have := strictMonoOn_gQ (gΦ_mem M) hu' hu.1
  rw [gQ_gΦ] at this
  exact this.le

lemma tendsto_gI_zero : Tendsto gI (𝓝[Icc (0:ℝ) 1] 0) (𝓝 0) := by
  have h0 : gI 0 = 0 := by simp [gI]
  have hIoo : Tendsto gI (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun u => gφ (gQ u)) (𝓝[>] 0) (𝓝 0) :=
      tendsto_gφ_cocompact.comp (tendsto_gQ_zero.mono_right atBot_le_cocompact)
    refine h1.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with u hu
    exact (gI_of_mem hu).symm
  rw [nhdsWithin_Icc_eq_nhdsGE (by norm_num : (0:ℝ) < 1), ← Ioi_insert, nhdsWithin_insert]
  exact (by simpa [h0] using tendsto_pure_nhds gI 0 : Tendsto gI (pure 0) (𝓝 0)).sup hIoo

lemma tendsto_gI_one : Tendsto gI (𝓝[Icc (0:ℝ) 1] 1) (𝓝 0) := by
  have h0 : gI 1 = 0 := by simp [gI]
  have hIoo : Tendsto gI (𝓝[<] 1) (𝓝 0) := by
    have h1 : Tendsto (fun u => gφ (gQ u)) (𝓝[<] 1) (𝓝 0) :=
      tendsto_gφ_cocompact.comp (tendsto_gQ_one.mono_right atTop_le_cocompact)
    refine h1.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with u hu
    exact (gI_of_mem hu).symm
  rw [nhdsWithin_Icc_eq_nhdsLE (by norm_num : (0:ℝ) < 1), ← Iio_insert, nhdsWithin_insert]
  exact (by simpa [h0] using tendsto_pure_nhds gI 1 : Tendsto gI (pure 1) (𝓝 0)).sup hIoo

lemma continuousOn_gI : ContinuousOn gI (Icc (0:ℝ) 1) := by
  intro u hu
  rcases hu.1.eq_or_lt with h | h
  · subst h
    have h0 : gI 0 = 0 := by simp [gI]
    show Tendsto _ _ _
    rw [h0]; exact tendsto_gI_zero
  rcases hu.2.eq_or_lt with h' | h'
  · subst h'
    have h0 : gI 1 = 0 := by simp [gI]
    show Tendsto _ _ _
    rw [h0]; exact tendsto_gI_one
  exact (hasDerivAt_gI ⟨h, h'⟩).continuousAt.continuousWithinAt

/-- The standard Gaussian law on `ℝ`. -/
noncomputable abbrev γ1 : Measure ℝ := gaussianReal 0 1

instance : IsProbabilityMeasure γ1 := inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))

lemma integral_γ1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) :
    ∫ x, f x ∂γ1 = ∫ x, gφ x • f x :=
  integral_gaussianReal_eq_integral_smul one_ne_zero

lemma integrable_mul_gφ : Integrable (fun x : ℝ => x * gφ x) := by
  have h := integrable_mul_exp_neg_mul_sq (show (0:ℝ) < 1 / 2 by norm_num)
  have h2 := h.const_mul (Real.sqrt (2 * Real.pi))⁻¹
  refine h2.congr (Eventually.of_forall fun x => ?_)
  simp only [gφ_eq]
  ring_nf

/-- **Stein's lemma** for the standard Gaussian (bounded `k` with bounded continuous derivative). -/
lemma stein {k k' : ℝ → ℝ} (hk : ∀ x, HasDerivAt k (k' x) x) (hkb : ∃ C, ∀ x, |k x| ≤ C)
    (hk'b : ∃ C, ∀ x, |k' x| ≤ C) (hk'c : Continuous k') :
    ∫ y, y * k y ∂γ1 = ∫ y, k' y ∂γ1 := by
  obtain ⟨C, hC⟩ := hkb
  obtain ⟨C', hC'⟩ := hk'b
  have hkc : Continuous k := continuous_iff_continuousAt.2 fun x => (hk x).continuousAt
  have h1 : Integrable (fun x => k x * (-x * gφ x)) := by
    have := (integrable_mul_gφ.neg).bdd_mul (c := C) hkc.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa using hC x)
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp
  have h2 : Integrable (fun x => k' x * gφ x) :=
    integrable_gφ.bdd_mul (c := C') hk'c.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa using hC' x)
  have h3 : Integrable (fun x => k x * gφ x) :=
    integrable_gφ.bdd_mul (c := C) hkc.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa using hC x)
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := k) (v := gφ) (u' := k')
    (v' := fun x => -x * gφ x) (fun x _ => hk x) (fun x _ => hasDerivAt_gφ x) h1 h2 h3
  rw [integral_γ1, integral_γ1]
  simp only [smul_eq_mul]
  have e1 : ∫ x, gφ x * (x * k x) = -∫ x, k x * (-x * gφ x) := by
    rw [← integral_neg]; congr 1; funext x; ring
  have e2 : ∫ x, gφ x * k' x = ∫ x, k' x * gφ x := by congr 1; funext x; ring
  rw [e1, e2, key]; ring

end CutoffRigidity.GaussIso
