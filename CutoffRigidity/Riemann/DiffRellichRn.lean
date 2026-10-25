module

public import CutoffRigidity.EuclideanL2Translations
public import CutoffRigidity.EuclideanMollifiedCompactness
public import CutoffRigidity.L2CompactnessTools
public import CutoffRigidity.EuclideanL2MollificationGeneral

/-! # Rellich-Kolmogorov criterion in a finite-dimensional inner product space (workstream HPOS)

STUB (statements only; being proved by a sub-agent).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

section Rn

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

theorem continuous_gradient_F {f : F → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (gradient f) := by
  let R : (F →L[ℝ] ℝ) →L[ℝ] F :=
    (InnerProductSpace.toDual ℝ F).symm.toContinuousLinearEquiv.toContinuousLinearMap
  exact R.continuous.comp ((hf.fderiv_right (m := 0) (by norm_num)).continuous)

theorem c1_translation_sq_le_line_energy_F {f : F → ℝ} (hf : ContDiff ℝ 1 f) (x h : F) :
    (f (x + h) - f x) ^ 2 ≤ ‖h‖ ^ 2 *
      ∫ t, ‖gradient f (x + t • h)‖ ^ 2 ∂CutoffRigidity.unitIntervalLebesgue := by
  have hG : Continuous (gradient f) := continuous_gradient_F F hf
  have hFTC : (∫ t, inner ℝ (gradient f (x + t • h)) h ∂CutoffRigidity.unitIntervalLebesgue)
      = f (x + h) - f x := by
    have hc : Continuous (fun t : ℝ => inner ℝ (gradient f (x + t • h)) h) := by fun_prop
    have hd (t : ℝ) : HasDerivAt (fun s : ℝ => f (x + s • h))
        (inner ℝ (gradient f (x + t • h)) h) t := by
      have hl : HasDerivAt (fun s : ℝ => x + s • h) h t := by
        simpa using ((hasDerivAt_id t).smul_const h).const_add x
      have hh := ((hf.differentiable (by norm_num)) (x + t • h)).hasFDerivAt.comp_hasDerivAt t hl
      simpa only [Function.comp_def, inner_gradient_left] using hh
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t (_ : t ∈ Set.uIcc (0 : ℝ) 1) => hd t) (hc.intervalIntegrable 0 1)
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← integral_Icc_eq_integral_Ioc] at hi
    simpa only [CutoffRigidity.unitIntervalLebesgue, one_smul, zero_smul, add_zero] using hi
  let g (t : ℝ) := inner ℝ (gradient f (x + t • h)) h
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hg2 : Integrable (fun t => g t ^ 2) CutoffRigidity.unitIntervalLebesgue :=
    (hg.pow 2).integrableOn_Icc
  have hgLp : MemLp g 2 CutoffRigidity.unitIntervalLebesgue :=
    (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mpr hg2
  have hj := ProbabilityTheory.variance_nonneg g CutoffRigidity.unitIntervalLebesgue
  rw [ProbabilityTheory.variance_eq_sub hgLp] at hj
  change (∫ t, g t ∂CutoffRigidity.unitIntervalLebesgue) = f (x + h) - f x at hFTC
  have hnorm : Integrable (fun t : ℝ => ‖gradient f (x + t • h)‖ ^ 2)
      CutoffRigidity.unitIntervalLebesgue :=
    (show Continuous (fun t : ℝ => ‖gradient f (x + t • h)‖ ^ 2) by fun_prop).integrableOn_Icc
  have hpoint (t : ℝ) : g t ^ 2 ≤ ‖h‖ ^ 2 * ‖gradient f (x + t • h)‖ ^ 2 := by
    have hh := abs_real_inner_le_norm (gradient f (x + t • h)) h
    have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hh
    simpa only [sq_abs, mul_pow, mul_comm] using hs
  have hi := integral_mono hg2 (hnorm.const_mul (‖h‖ ^ 2)) hpoint
  rw [integral_const_mul] at hi
  simp only [Pi.pow_apply] at hj
  rw [hFTC] at hj
  linarith

/-- L² translation estimate for `C¹` compactly supported functions on `F`. -/
theorem c1_translation_F {f : F → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (h : F) :
    ∫ x, (f (x + h) - f x) ^ 2 ≤ ‖h‖ ^ 2 * ∫ x, ‖gradient f x‖ ^ 2 := by
  have hG : Continuous (gradient f) := continuous_gradient_F F hf
  have hgc : HasCompactSupport (gradient f) :=
    (hfc.fderiv ℝ).comp_left (g := (InnerProductSpace.toDual ℝ F).symm) (by simp)
  have hE : Integrable (fun x => ‖gradient f x‖ ^ 2) volume :=
    (hG.memLp_of_hasCompactSupport hgc).norm.integrable_sq
  have hfLp : MemLp f 2 volume := hf.continuous.memLp_of_hasCompactSupport hfc
  have hD : Integrable (fun x => (f (x + h) - f x) ^ 2) volume := by
    have : MemLp (fun x => f (x + h) - f x) 2 volume := by
      simpa only [Function.comp_def, Pi.sub_def] using
        (hfLp.comp_measurePreserving (measurePreserving_add_right volume h)).sub hfLp
    exact this.integrable_sq
  let G (x : F) (t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (‖gradient f (x + t • h)‖ ^ 2)
  have hFm : Measurable (Function.uncurry G) := by
    have hc : Continuous (fun p : F × ℝ => ‖gradient f (p.1 + p.2 • h)‖ ^ 2) := by fun_prop
    exact hc.measurable.ennreal_ofReal
  have hpoint (x : F) : ENNReal.ofReal ((f (x + h) - f x) ^ 2) ≤
      ENNReal.ofReal (‖h‖ ^ 2) * ∫⁻ t, G x t ∂CutoffRigidity.unitIntervalLebesgue := by
    have ht : Integrable (fun t : ℝ => ‖gradient f (x + t • h)‖ ^ 2)
        CutoffRigidity.unitIntervalLebesgue :=
      (show Continuous (fun t : ℝ => ‖gradient f (x + t • h)‖ ^ 2) by fun_prop).integrableOn_Icc
    have hh := ENNReal.ofReal_le_ofReal (c1_translation_sq_le_line_energy_F F hf x h)
    rw [ENNReal.ofReal_mul (sq_nonneg _), ofReal_integral_eq_lintegral_ofReal ht
      (Filter.Eventually.of_forall fun t => sq_nonneg _)] at hh
    exact hh
  have hi := lintegral_mono (μ := (volume : Measure F)) hpoint
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_lintegral_swap hFm.aemeasurable] at hi
  have hHaar (t : ℝ) : (∫⁻ x, G x t) = ∫⁻ x, ENNReal.ofReal (‖gradient f x‖ ^ 2) :=
    lintegral_add_right_eq_self (fun x => ENNReal.ofReal (‖gradient f x‖ ^ 2)) (t • h)
  simp_rw [hHaar] at hi
  simp only [lintegral_const, measure_univ, mul_one] at hi
  rw [← ofReal_integral_eq_lintegral_ofReal hD (Filter.Eventually.of_forall fun x => sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hE (Filter.Eventually.of_forall fun x => sq_nonneg _),
    ← ENNReal.ofReal_mul (sq_nonneg _)] at hi
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (sq_nonneg _) (integral_nonneg fun x => sq_nonneg _))).mp hi

end Rn

section Euclid

open CutoffRigidity

variable {d : ℕ}

theorem L2_dist_sq_eq {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [InnerProductSpace ℝ E] {μ : Measure E} {f g : E → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ x, (f x - g x) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g), hf.coeFn_toLp, hg.coeFn_toLp]
    with x hsub hf' hg'
  rw [hsub, Pi.sub_apply, hf', hg', Real.inner_apply, pow_two]

/-- Euclidean version, for measurable inputs. -/
theorem rellich_criterion_E_meas {ι : Type*} (g : ι → EuclideanSpace ℝ (Fin d) → ℝ)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) (A C : ℝ)
    (hmeas : ∀ i, Measurable (g i))
    (hmem : ∀ i, MemLp (g i) 2 volume) (hsupp : ∀ i x, x ∉ K → g i x = 0)
    (hA : ∀ i, ∫ x, g i x ^ 2 ≤ A)
    (htrans : ∀ i (h : EuclideanSpace ℝ (Fin d)), ∫ x, (g i (x + h) - g i x) ^ 2 ≤ C * ‖h‖ ^ 2) :
    ∀ ε : ℝ, 0 < ε → ∃ s : Finset ι, ∀ i, ∃ j ∈ s, ∫ x, (g i x - g j x) ^ 2 < ε := by
  set c := Real.sqrt (max C 0) with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  set M := Real.sqrt (max A 0) with hM
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  have hnorm (i : ι) : ‖(hmem i).toLp (g i)‖ ≤ M := by
    apply Real.le_sqrt_of_sq_le
    have h2 : ‖(hmem i).toLp (g i)‖ ^ 2 = ∫ x, g i x ^ 2 := by
      have := L2_dist_sq_eq (hmem i) (hmem i)
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(hmem i).coeFn_toLp] with x hx
      rw [hx, Real.inner_apply, pow_two]
    rw [h2]; exact (hA i).trans (le_max_left _ _)
  have htr' (i : ι) (h : EuclideanSpace ℝ (Fin d)) :
      ∫ x, (g i (x + h) - g i x) ^ 2 ≤ c ^ 2 * ‖h‖ ^ 2 := by
    rw [hc, Real.sq_sqrt (le_max_right _ _)]
    exact (htrans i h).trans (by gcongr; exact le_max_left _ _)
  let u (i : ι) : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) := (hmem i).toLp (g i)
  have htb : TotallyBounded (Set.range u) := by
    apply totallyBounded_of_uniform_precompact_approximation
    intro ε hε
    let η := ε / (2 * (c + 1))
    have hη : 0 < η := by positivity
    let φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) := euclideanMollifierBump η hη
    have hsupp' := hsupp
    let m (i : ι) : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
      (bumpMollification_memLp_of_commonSupport φ (hmem i) hK (hsupp i)).toLp
        (bumpMollification φ (g i))
    have hcompact : IsCompact (closure (Set.range m)) :=
      isCompact_closure_bumpMollification_L2_family φ g hmem hK hsupp M hM0 hnorm
    refine ⟨closure (Set.range m), hcompact.totallyBounded, ?_⟩
    rintro x ⟨i, rfl⟩
    refine ⟨m i, subset_closure ⟨i, rfl⟩, ?_⟩
    have hmoll : ‖m i - u i‖ ≤ η * c :=
      bumpMollification_L2_dist_le_of_translation_bound φ (hmeas i) (hmem i) c hc0 (htr' i)
    rw [dist_eq_norm, norm_sub_rev]
    refine lt_of_le_of_lt hmoll ?_
    have : η * c < ε := by
      have he : η * (2 * (c + 1)) = ε := by dsimp only [η]; field_simp
      nlinarith [hη]
    exact this
  intro ε hε
  obtain ⟨t, hts, htf, hcov⟩ :=
    Metric.finite_approx_of_totallyBounded htb (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
  obtain ⟨s, -, hsf, hst⟩ := Set.exists_subset_image_finite_and (f := u) (s := Set.univ)
    (p := fun t' => t' = t) |>.mp ⟨t, by simpa using hts, htf, rfl⟩
  refine ⟨hsf.toFinset, fun i => ?_⟩
  have hi : u i ∈ ⋃ y ∈ t, Metric.ball y (Real.sqrt ε) := hcov ⟨i, rfl⟩
  simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at hi
  obtain ⟨y, hy, hd⟩ := hi
  rw [← hst] at hy
  obtain ⟨j, hj, rfl⟩ := hy
  refine ⟨j, by simpa using hj, ?_⟩
  rw [← L2_dist_sq_eq (hmem i) (hmem j)]
  rw [dist_eq_norm] at hd
  have h0 := norm_nonneg (u i - u j)
  calc ‖(hmem i).toLp (g i) - (hmem j).toLp (g j)‖ ^ 2 < (Real.sqrt ε) ^ 2 :=
        pow_lt_pow_left₀ hd h0 (by norm_num)
    _ = ε := Real.sq_sqrt hε.le

/-- Euclidean version (no measurability assumption). -/
theorem rellich_criterion_E {ι : Type*} (g : ι → EuclideanSpace ℝ (Fin d) → ℝ)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) (A C : ℝ)
    (hmem : ∀ i, MemLp (g i) 2 volume) (hsupp : ∀ i x, x ∉ K → g i x = 0)
    (hA : ∀ i, ∫ x, g i x ^ 2 ≤ A)
    (htrans : ∀ i (h : EuclideanSpace ℝ (Fin d)), ∫ x, (g i (x + h) - g i x) ^ 2 ≤ C * ‖h‖ ^ 2) :
    ∀ ε : ℝ, 0 < ε → ∃ s : Finset ι, ∀ i, ∃ j ∈ s, ∫ x, (g i x - g j x) ^ 2 < ε := by
  let g' (i : ι) : EuclideanSpace ℝ (Fin d) → ℝ := K.indicator (hmem i).aestronglyMeasurable.mk
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hm (i : ι) : Measurable (g' i) :=
    (hmem i).aestronglyMeasurable.stronglyMeasurable_mk.measurable.indicator hKm
  have heq (i : ι) : g' i =ᵐ[volume] g i := by
    filter_upwards [(hmem i).aestronglyMeasurable.ae_eq_mk] with x hx
    by_cases hxK : x ∈ K
    · simp only [g', Set.indicator_of_mem hxK, ← hx]
    · simp only [g', Set.indicator_of_notMem hxK, hsupp i x hxK]
  have heqh (i : ι) (h : EuclideanSpace ℝ (Fin d)) :
      (fun x => g' i (x + h)) =ᵐ[volume] fun x => g i (x + h) :=
    (measurePreserving_add_right volume h).quasiMeasurePreserving.ae_eq_comp (heq i)
  have hs : ∀ i x, x ∉ K → g' i x = 0 := fun i x hx => by
    simp only [g', Set.indicator_of_notMem hx]
  have h1 := rellich_criterion_E_meas g' hK A C hm (fun i => (hmem i).ae_eq (heq i).symm) hs
    (fun i => by
      rw [integral_congr_ae (g := fun x => g i x ^ 2) (by filter_upwards [heq i] with x hx; simp [hx])]
      exact hA i)
    (fun i h => by
      rw [integral_congr_ae (g := fun x => (g i (x + h) - g i x) ^ 2)
        (by filter_upwards [heq i, heqh i h] with x hx hxh; simp [hx, hxh])]
      exact htrans i h)
  intro ε hε
  obtain ⟨s, hs'⟩ := h1 ε hε
  refine ⟨s, fun i => ?_⟩
  obtain ⟨j, hj, hij⟩ := hs' i
  refine ⟨j, hj, ?_⟩
  rwa [integral_congr_ae (g := fun x => (g' i x - g' j x) ^ 2)
    (by filter_upwards [heq i, heq j] with x hx hy; simp [hx, hy])] 

end Euclid

section Transport

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- Rellich-Kolmogorov: a family of `L²(F)` functions with common compact support, uniformly bounded
in `L²` and with uniform `L²` translation modulus `∫ (g(x+h)-g(x))² ≤ C ‖h‖²` is totally bounded in
`L²`: for every `ε > 0` there is a finite subfamily that is `ε`-dense in the squared `L²` distance. -/
theorem rellich_criterion_F {ι : Type*} (g : ι → F → ℝ) {K : Set F} (hK : IsCompact K) (A C : ℝ)
    (hmem : ∀ i, MemLp (g i) 2 volume) (hsupp : ∀ i x, x ∉ K → g i x = 0)
    (hA : ∀ i, ∫ x, g i x ^ 2 ≤ A)
    (htrans : ∀ i (h : F), ∫ x, (g i (x + h) - g i x) ^ 2 ≤ C * ‖h‖ ^ 2) :
    ∀ ε : ℝ, 0 < ε → ∃ s : Finset ι, ∀ i, ∃ j ∈ s, ∫ x, (g i x - g j x) ^ 2 < ε := by
  let e := (stdOrthonormalBasis ℝ F).repr
  have hmp : MeasurePreserving e.symm volume volume := e.symm.measurePreserving
  have hme : MeasurableEmbedding e.symm := e.symm.toHomeomorph.measurableEmbedding
  have hint (f : F → ℝ) : ∫ x, f (e.symm x) = ∫ x, f x := hmp.integral_comp hme f
  let g' (i : ι) : EuclideanSpace ℝ (Fin (Module.finrank ℝ F)) → ℝ := fun x => g i (e.symm x)
  have hK' : IsCompact (e '' K) := hK.image e.continuous
  have h1 := rellich_criterion_E g' hK' A C
    (fun i => (hmem i).comp_measurePreserving hmp)
    (fun i x hx => hsupp i _ (fun hxK => hx ⟨_, hxK, by simp⟩))
    (fun i => by simpa only [g', hint (fun y => g i y ^ 2)] using hA i)
    (fun i h => by
      have := htrans i (e.symm h)
      have e1 : ∫ x, (g' i (x + h) - g' i x) ^ 2 =
          ∫ x, (g i (x + e.symm h) - g i x) ^ 2 := by
        rw [← hint (fun x => (g i (x + e.symm h) - g i x) ^ 2)]
        simp [g']
      rw [e1]
      simpa using this)
  intro ε hε
  obtain ⟨s, hs⟩ := h1 ε hε
  refine ⟨s, fun i => ?_⟩
  obtain ⟨j, hj, hij⟩ := hs i
  refine ⟨j, hj, ?_⟩
  rwa [show ∫ x, (g' i x - g' j x) ^ 2 = ∫ x, (g i x - g j x) ^ 2 from
    hint (fun x => (g i x - g j x) ^ 2)] at hij

end Transport

end CutoffRigidity.Riemann.Diff
