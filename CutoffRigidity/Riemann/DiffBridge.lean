module

public import CutoffRigidity.Riemann.DiffPerronAPI
public import CutoffRigidity.Riemann.DiffusionRegular
public import CutoffRigidity.Riemann.DiffIdentify
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Bridge `Pt = Kk`, part 1: Laplace uniqueness and the resolvent calculus

* `laplace_unique`: a bounded continuous `φ : ℝ → ℝ` with `∫₀^∞ e^{-(m+2)s} φ(s) ds = 0` for all
  `m : ℕ` vanishes on `[0,∞)` (Weierstrass in the variable `y = e^{-s}`).
* `resolventU` calculus for `IsDiffusionSemigroup`: integrability, linearity, monotonicity,
  and the resolvent form of Dynkin's identity `U_λ((λ - 𝓛) f) = f`.
-/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set
open scoped Manifold ContDiff ENNReal NNReal Topology Polynomial

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur CutoffRigidity.Riemann

section Laplace

theorem integrableOn_exp_mul_bdd {φ : ℝ → ℝ} (hc : Continuous φ) {B : ℝ} (hb : ∀ s, |φ s| ≤ B)
    {c : ℝ} (hc0 : 0 < c) :
    IntegrableOn (fun s => Real.exp (-c * s) * φ s) (Ioi (0 : ℝ)) := by
  have hi : IntegrableOn (fun s : ℝ => B * Real.exp (-c * s)) (Ioi (0 : ℝ)) :=
    (integrableOn_exp_mul_Ioi (a := -c) (by linarith) 0).const_mul B
  refine hi.mono' ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    hc).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s _ => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
  exact mul_le_mul_of_nonneg_right (hb s) (Real.exp_pos _).le

/-- The auxiliary function `y ↦ y φ(-log y)` (zero for `y ≤ 0`) is continuous. -/
theorem continuous_aux_laplace {φ : ℝ → ℝ} (hc : Continuous φ) {B : ℝ} (hb : ∀ s, |φ s| ≤ B) :
    Continuous (fun y : ℝ => if 0 < y then y * φ (-Real.log y) else 0) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hb 0)
  set u : ℝ → ℝ := fun y => if 0 < y then y * φ (-Real.log y) else 0 with hu
  rw [continuous_iff_continuousAt]
  intro y
  rcases lt_trichotomy y 0 with hy | hy | hy
  · have : u =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hy] with z hz
      simp [hu, not_lt.2 (le_of_lt hz)]
    exact continuousAt_const.congr this.symm
  · subst hy
    have h0 : u 0 = 0 := by simp [hu]
    have hbd : ∀ z, |u z| ≤ B * |z| := by
      intro z
      by_cases hz : 0 < z
      · simp only [hu, hz, ite_true, abs_mul, abs_of_pos hz]
        nlinarith [mul_nonneg (sub_nonneg.2 (hb (-Real.log z))) hz.le]
      · simp only [hu, hz, ite_false, abs_zero]
        positivity
    rw [ContinuousAt, h0]
    have h1 : Tendsto (fun z : ℝ => B * |z|) (𝓝 0) (𝓝 0) := by
      have := ((continuous_abs.tendsto (0 : ℝ)).const_mul B)
      simpa using this
    exact squeeze_zero_norm (fun z => by simpa [Real.norm_eq_abs] using hbd z) h1
  · have : u =ᶠ[𝓝 y] fun z => z * φ (-Real.log z) := by
      filter_upwards [Ioi_mem_nhds hy] with z hz
      have hz' : 0 < z := hz
      simp [hu, hz']
    refine ContinuousAt.congr ?_ this.symm
    exact continuousAt_id.mul (hc.continuousAt.comp
      ((Real.continuousAt_log hy.ne').neg))

/-- **Laplace uniqueness** for bounded continuous functions (checked on `λ = m + 2`). -/
theorem laplace_unique {φ : ℝ → ℝ} (hc : Continuous φ) {B : ℝ} (hb : ∀ s, |φ s| ≤ B)
    (h : ∀ m : ℕ, ∫ s in Ioi (0 : ℝ), Real.exp (-((m : ℝ) + 2) * s) * φ s = 0) :
    ∀ s, 0 ≤ s → φ s = 0 := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hb 0)
  set u : ℝ → ℝ := fun y => if 0 < y then y * φ (-Real.log y) else 0 with hu
  have huc : Continuous u := continuous_aux_laplace hc hb
  have hue : ∀ s : ℝ, u (Real.exp (-s)) = Real.exp (-s) * φ s := by
    intro s
    simp [hu, Real.exp_pos, Real.log_exp]
  have hint3 : IntegrableOn (fun s => Real.exp (-3 * s) * φ s ^ 2) (Ioi (0 : ℝ)) := by
    have hc2 : Continuous (fun s => φ s ^ 2) := hc.pow 2
    have := integrableOn_exp_mul_bdd (c := 3) hc2 (B := B ^ 2) (fun s => by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hb s) 2 |>.trans_eq' (by rw [sq_abs])) (by norm_num)
    exact this
  -- the target integral is zero
  set T : ℝ := ∫ s in Ioi (0 : ℝ), Real.exp (-3 * s) * φ s ^ 2 with hT
  have hpoly : ∀ ε : ℝ, 0 < ε → |T| ≤ ε * B / 2 := by
    intro ε hε
    obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap 0 1
      ⟨fun y => u (y : ℝ), huc.comp continuous_subtype_val⟩ ε hε
    have hpu : ∀ y : ℝ, y ∈ Icc (0 : ℝ) 1 → |p.eval y - u y| < ε := by
      intro y hy
      have := ContinuousMap.norm_coe_le_norm (p.toContinuousMapOn (Icc (0 : ℝ) 1) -
        ⟨fun y => u (y : ℝ), huc.comp continuous_subtype_val⟩) ⟨y, hy⟩
      simp only [ContinuousMap.sub_apply, Polynomial.toContinuousMapOn_apply, Real.norm_eq_abs] at this
      exact lt_of_le_of_lt this hp
    -- integral of the polynomial part vanishes
    have hint : ∀ m : ℕ, IntegrableOn (fun s => Real.exp (-((m : ℝ) + 2) * s) * φ s) (Ioi (0 : ℝ)) :=
      fun m => integrableOn_exp_mul_bdd hc hb (by positivity)
    have hzero : ∫ s in Ioi (0 : ℝ), Real.exp (-2 * s) * (p.eval (Real.exp (-s)) * φ s) = 0 := by
      have e : ∀ s : ℝ, Real.exp (-2 * s) * (p.eval (Real.exp (-s)) * φ s) =
          ∑ m ∈ Finset.range (p.natDegree + 1),
            p.coeff m * (Real.exp (-((m : ℝ) + 2) * s) * φ s) := by
        intro s
        rw [Polynomial.eval_eq_sum_range, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        have : Real.exp (-((m : ℝ) + 2) * s) = Real.exp (-2 * s) * Real.exp (-s) ^ m := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
        rw [this]; ring
      simp_rw [e]
      rw [integral_finsetSum _ (fun m _ => (hint m).const_mul _)]
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [integral_const_mul, h m, mul_zero]
    -- comparison
    have hdiff : T = ∫ s in Ioi (0 : ℝ), Real.exp (-2 * s) *
        ((u (Real.exp (-s)) - p.eval (Real.exp (-s))) * φ s) := by
      have hTe : T = ∫ s in Ioi (0 : ℝ), (Real.exp (-2 * s) *
          (u (Real.exp (-s)) * φ s)) := by
        rw [hT]; refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
        simp only [hue]
        have : Real.exp (-3 * s) = Real.exp (-2 * s) * Real.exp (-s) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [this]; ring
      have hi1 : IntegrableOn (fun s => Real.exp (-2 * s) * (u (Real.exp (-s)) * φ s))
          (Ioi (0 : ℝ)) := by
        have := hint3
        refine this.congr_fun (fun s _ => ?_) measurableSet_Ioi
        simp only [hue]
        have e3 : Real.exp (-3 * s) = Real.exp (-2 * s) * Real.exp (-s) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [e3]; ring
      have hi2 : IntegrableOn (fun s => Real.exp (-2 * s) * (p.eval (Real.exp (-s)) * φ s))
          (Ioi (0 : ℝ)) := by
        have e : ∀ s : ℝ, Real.exp (-2 * s) * (p.eval (Real.exp (-s)) * φ s) =
            ∑ m ∈ Finset.range (p.natDegree + 1),
              p.coeff m * (Real.exp (-((m : ℝ) + 2) * s) * φ s) := by
          intro s
          rw [Polynomial.eval_eq_sum_range, Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          have : Real.exp (-((m : ℝ) + 2) * s) = Real.exp (-2 * s) * Real.exp (-s) ^ m := by
            rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
          rw [this]; ring
        simp_rw [e]
        exact integrable_finsetSum _ (fun m _ => (hint m).const_mul _)
      rw [hTe]
      have := integral_sub hi1 hi2
      rw [hzero, sub_zero] at this
      rw [← this]
      refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      simp only; ring
    rw [hdiff]
    have hi : IntegrableOn (fun s : ℝ => ε * B * Real.exp (-2 * s)) (Ioi (0 : ℝ)) :=
      (integrableOn_exp_mul_Ioi (a := -2) (by norm_num) 0).const_mul (ε * B)
    have hle := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (0 : ℝ)))
      (f := fun s => Real.exp (-2 * s) * ((u (Real.exp (-s)) - p.eval (Real.exp (-s))) * φ s))
      (g := fun s => ε * B * Real.exp (-2 * s)) hi
      ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs => by
        have hs' : (0 : ℝ) < s := hs
        have hy : Real.exp (-s) ∈ Icc (0 : ℝ) 1 :=
          ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (by linarith)⟩
        have h1 := hpu _ hy
        rw [abs_sub_comm] at h1
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_mul]
        have := mul_le_mul h1.le (hb s) (abs_nonneg _) hε.le
        calc Real.exp (-2 * s) * (|u (Real.exp (-s)) - p.eval (Real.exp (-s))| * |φ s|)
            ≤ Real.exp (-2 * s) * (ε * B) :=
              mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
          _ = ε * B * Real.exp (-2 * s) := by ring))
    rw [integral_const_mul, integral_exp_mul_Ioi (a := -2) (by norm_num)] at hle
    rw [Real.norm_eq_abs] at hle
    refine hle.trans (le_of_eq ?_)
    simp; ring
  have hT0 : T = 0 := by
    have hnn : 0 ≤ T := setIntegral_nonneg measurableSet_Ioi fun s _ =>
      mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
    by_contra hne
    have hpos : 0 < T := lt_of_le_of_ne hnn (Ne.symm hne)
    have := hpoly (T / (B + 1)) (by positivity)
    rw [abs_of_nonneg hnn] at this
    have h1 : T / (B + 1) * B / 2 < T := by
      rw [div_mul_eq_mul_div, div_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  -- pointwise vanishing
  have hae := (integral_eq_zero_iff_of_nonneg_ae (μ := volume.restrict (Ioi (0 : ℝ)))
    (Filter.Eventually.of_forall fun s => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
    hint3).1 hT0
  have hpos0 : ∀ s : ℝ, 0 < s → φ s = 0 := by
    intro s hs
    by_contra hne
    have hopen : IsOpen {t : ℝ | 0 < t ∧ φ t ≠ 0} :=
      (isOpen_lt continuous_const continuous_id).inter (isOpen_ne_fun hc continuous_const)
    have hmem : s ∈ {t : ℝ | 0 < t ∧ φ t ≠ 0} := ⟨hs, hne⟩
    have hmeas : 0 < volume {t : ℝ | 0 < t ∧ φ t ≠ 0} := hopen.measure_pos volume ⟨s, hmem⟩
    have hz : volume {t : ℝ | 0 < t ∧ φ t ≠ 0} = 0 := by
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioi] at hae
      have := ae_iff.1 hae
      refine measure_mono_null (fun t ht => ?_) this
      simp only [Pi.zero_apply, mem_setOf_eq, not_imp]
      refine ⟨ht.1, ?_⟩
      simp [(Real.exp_pos _).ne', ht.2]
    exact hmeas.ne' hz
  intro s hs
  rcases hs.eq_or_lt with rfl | hs
  · have : Tendsto φ (𝓝[Ioi 0] 0) (𝓝 (φ 0)) := hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto φ (𝓝[Ioi 0] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [self_mem_nhdsWithin] with t ht
        exact (hpos0 t ht).symm)
    exact tendsto_nhds_unique this h2
  · exact hpos0 s hs

end Laplace


section Calculus

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M] {V : M → ℝ} {Pt : ℝ≥0 → Kernel M M}

theorem semi_abs_le_bridge (hP : IsDiffusionSemigroup F V Pt) {g : M → ℝ} {C : ℝ}
    (hb : ∀ y, |g y| ≤ C) (t : ℝ≥0) (x : M) : |semi Pt t g x| ≤ C := by
  haveI : IsProbabilityMeasure (Pt t x) := (hP.1 t).isProbabilityMeasure x
  exact abs_integral_le_of_prob hb

theorem exists_abs_le_of_cs {g : M → ℝ} (hg : MSmooth F g) (hgc : HasCompactSupport g) :
    ∃ C : ℝ, ∀ y, |g y| ≤ C := by
  obtain ⟨C, hC⟩ := hg.continuous.bounded_above_of_compact_support hgc
  exact ⟨C, fun y => by simpa [Real.norm_eq_abs] using hC y⟩

theorem integrable_cs {g : M → ℝ} (hg : MSmooth F g) (hgc : HasCompactSupport g) (P : Measure M)
    [IsFiniteMeasure P] : Integrable g P :=
  hg.continuous.integrable_of_hasCompactSupport hgc

theorem continuous_semi_time_of_diffusion (hP : IsDiffusionSemigroup F V Pt) (hV : MSmooth F V) {g : M → ℝ}
    (hg : MSmooth F g) (hgc : HasCompactSupport g) (x : M) :
    Continuous (fun s : ℝ => semi Pt s.toNNReal g x) :=
  (continuous_dynkin F hP hg hgc hV x).comp continuous_real_toNNReal

theorem resolventU_integrableOn (hP : IsDiffusionSemigroup F V Pt) (hV : MSmooth F V)
    {g : M → ℝ} (hg : MSmooth F g) (hgc : HasCompactSupport g) {lam : ℝ} (hlam : 0 < lam)
    (x : M) :
    IntegrableOn (fun s : ℝ => Real.exp (-lam * s) * semi Pt s.toNNReal g x) (Ioi (0 : ℝ)) := by
  obtain ⟨C, hC⟩ := exists_abs_le_of_cs F hg hgc
  exact integrableOn_exp_mul_bdd (continuous_semi_time_of_diffusion F hP hV hg hgc x)
    (fun s => semi_abs_le_bridge F hP hC _ x) hlam

theorem semi_sub (hP : IsDiffusionSemigroup F V Pt) {g h : M → ℝ} (hg : MSmooth F g)
    (hgc : HasCompactSupport g) (hh : MSmooth F h) (hhc : HasCompactSupport h) (t : ℝ≥0) (x : M) :
    semi Pt t (fun y => g y - h y) x = semi Pt t g x - semi Pt t h x := by
  haveI : IsProbabilityMeasure (Pt t x) := (hP.1 t).isProbabilityMeasure x
  exact integral_sub (integrable_cs F hg hgc _) (integrable_cs F hh hhc _)

theorem semi_mono (hP : IsDiffusionSemigroup F V Pt) {g h : M → ℝ} (hg : MSmooth F g)
    (hgc : HasCompactSupport g) (hh : MSmooth F h) (hhc : HasCompactSupport h)
    (hgh : ∀ y, g y ≤ h y) (t : ℝ≥0) (x : M) : semi Pt t g x ≤ semi Pt t h x := by
  haveI : IsProbabilityMeasure (Pt t x) := (hP.1 t).isProbabilityMeasure x
  exact integral_mono (integrable_cs F hg hgc _) (integrable_cs F hh hhc _) hgh

theorem semi_nonneg_bridge (hP : IsDiffusionSemigroup F V Pt) {g : M → ℝ} (hg0 : ∀ y, 0 ≤ g y)
    (t : ℝ≥0) (x : M) : 0 ≤ semi Pt t g x := integral_nonneg hg0

theorem resolventU_mono (hP : IsDiffusionSemigroup F V Pt) (hV : MSmooth F V) {g h : M → ℝ}
    (hg : MSmooth F g) (hgc : HasCompactSupport g) (hh : MSmooth F h) (hhc : HasCompactSupport h)
    (hgh : ∀ y, g y ≤ h y) {lam : ℝ} (hlam : 0 < lam) (x : M) :
    resolventU Pt lam g x ≤ resolventU Pt lam h x := by
  unfold resolventU
  refine setIntegral_mono_on (resolventU_integrableOn F hP hV hg hgc hlam x)
    (resolventU_integrableOn F hP hV hh hhc hlam x) measurableSet_Ioi fun s _ => ?_
  exact mul_le_mul_of_nonneg_left (semi_mono F hP hg hgc hh hhc hgh _ x) (Real.exp_pos _).le

theorem resolventU_nonneg (hP : IsDiffusionSemigroup F V Pt) {g : M → ℝ} (hg0 : ∀ y, 0 ≤ g y)
    (lam : ℝ) (x : M) : 0 ≤ resolventU Pt lam g x :=
  setIntegral_nonneg measurableSet_Ioi fun s _ =>
    mul_nonneg (Real.exp_pos _).le (semi_nonneg_bridge F hP hg0 _ x)

theorem resolventU_sub (hP : IsDiffusionSemigroup F V Pt) (hV : MSmooth F V) {g h : M → ℝ}
    (hg : MSmooth F g) (hgc : HasCompactSupport g) (hh : MSmooth F h) (hhc : HasCompactSupport h)
    {lam : ℝ} (hlam : 0 < lam) (x : M) :
    resolventU Pt lam (fun y => g y - h y) x = resolventU Pt lam g x - resolventU Pt lam h x := by
  unfold resolventU
  rw [← integral_sub (resolventU_integrableOn F hP hV hg hgc hlam x)
    (resolventU_integrableOn F hP hV hh hhc hlam x)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [semi_sub F hP hg hgc hh hhc, mul_sub]

/-- **Resolvent form of Dynkin's identity**: `U_λ((λ - 𝓛) f) = f` pointwise, `f ∈ C_c^∞`. -/
theorem resolventU_dynkin (hP : IsDiffusionSemigroup F V Pt) (hV : MSmooth F V) {lam : ℝ}
    (hlam : 0 < lam) {f : M → ℝ} (hf : MSmooth F f) (hfc : HasCompactSupport f) (x : M) :
    resolventU Pt lam (fun y => lam * f y - mgenerator F V f y) x = f x := by
  have hLf : MSmooth F (mgenerator F V f) := msmooth_mgenerator F hV hf
  have hLfc : HasCompactSupport (mgenerator F V f) := hasCompactSupport_mgenerator F V hf hfc
  set φ : ℝ → ℝ := fun s => semi Pt s.toNNReal f x with hφ
  set ψ : ℝ → ℝ := fun s => semi Pt s.toNNReal (mgenerator F V f) x with hψ
  have hφc : Continuous φ := continuous_semi_time_of_diffusion F hP hV hf hfc x
  obtain ⟨C, hC⟩ := exists_abs_le_of_cs F hf hfc
  have hφb : ∀ s, |φ s| ≤ C := fun s => semi_abs_le_bridge F hP hC _ x
  have hmix : ∀ s : ℝ, semi Pt s.toNNReal (fun y => lam * f y - mgenerator F V f y) x =
      lam * φ s - ψ s := by
    intro s
    haveI : IsProbabilityMeasure (Pt s.toNNReal x) := (hP.1 _).isProbabilityMeasure x
    simp only [semi, hφ, hψ]
    rw [integral_sub ((integrable_cs F hf hfc _).const_mul lam) (integrable_cs F hLf hLfc _),
      integral_const_mul]
  set G : ℝ → ℝ := fun s => -(Real.exp (-lam * s) * φ s) with hG
  have hGc : Continuous G := (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    hφc)).neg
  have hder : ∀ s ∈ Ioi (0 : ℝ), HasDerivAt G
      (Real.exp (-lam * s) * (lam * φ s - ψ s)) s := by
    intro s hs
    have hs' : (0 : ℝ) < s := hs
    have hφd : HasDerivAt φ (ψ s) s := hasDerivAt_dynkin F hP hf hfc hV x hs'
    have he : HasDerivAt (fun s : ℝ => Real.exp (-lam * s)) (Real.exp (-lam * s) * (-lam)) s := by
      simpa using ((hasDerivAt_id s).const_mul (-lam)).exp
    have := (he.mul hφd).neg
    convert this using 1
    ring
  have hint : IntegrableOn (fun s : ℝ => Real.exp (-lam * s) * (lam * φ s - ψ s)) (Ioi (0 : ℝ)) := by
    have h1 := resolventU_integrableOn F hP hV hf hfc hlam x
    have h2 := resolventU_integrableOn F hP hV hLf hLfc hlam x
    have h3 : IntegrableOn (fun s : ℝ => lam * (Real.exp (-lam * s) * φ s) -
        Real.exp (-lam * s) * ψ s) (Ioi (0 : ℝ)) := (h1.const_mul lam).sub h2
    refine h3.congr_fun (fun s _ => ?_) measurableSet_Ioi
    ring
  have hlim : Tendsto G atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => C * Real.exp (-lam * s)) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hlam) : Tendsto (fun s : ℝ => -lam * s) atTop atBot))
      simpa using this.const_mul C
    refine squeeze_zero_norm (fun s => ?_) h1
    simp only [hG, norm_neg, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hφb s) (Real.exp_pos _).le
  have key := integral_Ioi_of_hasDerivAt_of_tendsto hGc.continuousWithinAt hder hint hlim
  have hφ0 : φ 0 = f x := by
    have := hP.2.2 f hf hfc x 0
    simpa [hφ, semi] using this
  have hG0 : G 0 = -f x := by simp [hG, hφ0]
  unfold resolventU
  simp_rw [hmix]
  rw [key, hG0]; ring

/-- Comparison from the Perron property: `U^K_λ g ≤ U^P_λ g` for every diffusion semigroup `P`. -/
theorem resolventU_le_of_minimal {Kk : ℝ≥0 → Kernel M M} (hP : IsDiffusionSemigroup F V Pt)
    (hV : MSmooth F V) (hmin : MinimalResolvent F V Kk) {lam : ℝ} (hlam : 0 < lam) {g : M → ℝ}
    (hg : MSmooth F g) (hgc : HasCompactSupport g) (hg0 : ∀ y, 0 ≤ g y) (x : M) :
    resolventU Kk lam g x ≤ resolventU Pt lam g x := by
  refine le_of_forall_pos_le_add fun η hη => ?_
  obtain ⟨f, hf, hfc, hsub, hfx⟩ := hmin lam hlam g hg hgc hg0 x η hη
  have hLf : MSmooth F (mgenerator F V f) := msmooth_mgenerator F hV hf
  have hLfc : HasCompactSupport (mgenerator F V f) := hasCompactSupport_mgenerator F V hf hfc
  have hD : MSmooth F (fun y => lam * f y - mgenerator F V f y) :=
    (contMDiff_const.mul hf).sub hLf
  have hDc : HasCompactSupport (fun y => lam * f y - mgenerator F V f y) :=
    (hfc.mul_left (f := fun _ => lam)).sub hLfc
  have h1 := resolventU_dynkin F hP hV hlam hf hfc x
  have h2 := resolventU_mono F hP hV hD hDc hg hgc hsub hlam x
  linarith

end Calculus

end CutoffRigidity.Riemann.Diff
