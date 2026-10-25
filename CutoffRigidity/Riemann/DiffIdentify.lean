module

public import CutoffRigidity.Riemann.DiffDynkinBounded
public import CutoffRigidity.Riemann.WeightedProper
public import Mathlib.Geometry.Manifold.SmoothApprox

/-! # Tier B2: identification `Pt = Kk`

Let `Pt` satisfy `IsDiffusionSemigroup` and `DynkinBounded`, and `Kk` be a `CanonicalDiffusion`.
Then `Pt t x = Kk t x` for every `t` and `x`: the function `s ↦ ∫ (Kk (t-s) g) dPt s (x,·)` has
increments `O((b-a)²)`, hence is constant.
-/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set
open scoped Manifold ContDiff ENNReal NNReal Topology

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur CutoffRigidity.Riemann

section Generic

/-- A function on `ℝ≥0` with quadratic increments is constant. -/
theorem eq_of_quadratic_increments (G : ℝ≥0 → ℝ) (t : ℝ≥0) (K : ℝ)
    (h : ∀ a b : ℝ≥0, a ≤ b → b ≤ t → |G b - G a| ≤ K * ((b : ℝ) - a) ^ 2) :
    G t = G 0 := by
  have key : ∀ n : ℕ, 0 < n → |G t - G 0| ≤ K * (t : ℝ) ^ 2 / n := by
    intro n hn
    set a : ℕ → ℝ≥0 := fun i => t * i / n with ha
    have hmono : ∀ i, a i ≤ a (i + 1) := fun i => by
      simp only [ha]
      gcongr
      simp
    have hle : ∀ i, i ≤ n → a i ≤ t := fun i hi => by
      simp only [ha]
      calc t * i / n ≤ t * n / n := by gcongr
        _ = t := by field_simp
    have hdiff : ∀ i, ((a (i + 1) : ℝ≥0) : ℝ) - a i = t / n := fun i => by
      simp only [ha]
      push_cast
      field_simp
      ring
    have ht : G (a n) - G (a 0) = ∑ i ∈ Finset.range n, (G (a (i + 1)) - G (a i)) :=
      (Finset.sum_range_sub (fun i => G (a i)) n).symm
    have han : a n = t := by simp only [ha]; field_simp
    have ha0 : a 0 = 0 := by simp [ha]
    rw [han, ha0] at ht
    rw [ht]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ Finset.range n, |G (a (i + 1)) - G (a i)|
        ≤ ∑ i ∈ Finset.range n, K * ((t : ℝ) / n) ^ 2 := by
          refine Finset.sum_le_sum fun i hi => ?_
          have := h (a i) (a (i + 1)) (hmono i) (hle _ (Finset.mem_range.1 hi))
          rwa [hdiff] at this
      _ = K * (t : ℝ) ^ 2 / n := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          have : (n : ℝ) ≠ 0 := by positivity
          field_simp
  by_contra hne
  have hpos : 0 < |G t - G 0| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := exists_nat_gt (K * (t : ℝ) ^ 2 / |G t - G 0|)
  have hn0 : 0 < n + 1 := Nat.succ_pos n
  have := key (n + 1) hn0
  have hnr : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hn0
  rw [le_div_iff₀ hnr] at this
  rw [div_lt_iff₀ hpos] at hn
  push_cast at this hnr
  nlinarith

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]

/-- Two probability measures that agree on smooth compactly supported functions are equal. -/
theorem measure_eq_of_integral_smooth [SigmaCompactSpace M] (hcut : WeightedCutoffs F M)
    {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ g : M → ℝ, MSmooth F g → HasCompactSupport g → ∫ y, g y ∂μ = ∫ y, g y ∂ν) :
    μ = ν := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  obtain ⟨χ, hχ, hlim⟩ := hcut
  have hχ01 : ∀ n y, 0 ≤ χ n y ∧ χ n y ≤ 1 := fun n y => ⟨((hχ n).2.2 y).1, ((hχ n).2.2 y).2.1⟩
  have hfb : ∀ y, |f y| ≤ ‖f‖ := fun y => by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm y
  have hlimit : ∀ (P : Measure M) [IsProbabilityMeasure P],
      Tendsto (fun n => ∫ y, χ n y * f y ∂P) atTop (𝓝 (∫ y, f y ∂P)) := by
    intro P _
    refine tendsto_integral_of_bdd (fun n => ((hχ n).1.continuous.mul f.continuous).aestronglyMeasurable)
      (K := ‖f‖) (fun n y => ?_) (fun y => ?_)
    · rw [abs_mul, abs_of_nonneg (hχ01 n y).1]
      calc χ n y * |f y| ≤ 1 * ‖f‖ := mul_le_mul (hχ01 n y).2 (hfb y) (abs_nonneg _) zero_le_one
        _ = ‖f‖ := one_mul _
    · exact tendsto_const_nhds.congr' (by
        filter_upwards [hlim y] with n hn
        rw [hn, one_mul])
  have key : ∀ ε : ℝ, 0 < ε → |∫ y, f y ∂μ - ∫ y, f y ∂ν| ≤ 2 * ε := by
    intro ε hε
    obtain ⟨g, hg, -⟩ := f.continuous.exists_contMDiff_approx 𝓘(ℝ, F) (⊤ : ℕ∞)
      (ε := fun _ => ε) continuous_const (fun _ => hε)
    have hgs : MSmooth F g := g.contMDiff
    have hbound : ∀ (P : Measure M) [IsProbabilityMeasure P] (n : ℕ),
        |∫ y, χ n y * f y ∂P - ∫ y, χ n y * g y ∂P| ≤ ε := by
      intro P _ n
      have hi1 : Integrable (fun y => χ n y * f y) P :=
        integrable_of_bdd_cont ((hχ n).1.continuous.mul f.continuous) (K := ‖f‖) (fun y => by
          rw [abs_mul, abs_of_nonneg (hχ01 n y).1]
          calc χ n y * |f y| ≤ 1 * ‖f‖ :=
                mul_le_mul (hχ01 n y).2 (hfb y) (abs_nonneg _) zero_le_one
            _ = ‖f‖ := one_mul _)
      have hi2 : Integrable (fun y => χ n y * g y) P :=
        (((hχ n).1.mul hgs).continuous).integrable_of_hasCompactSupport ((hχ n).2.1.mul_right)
      rw [← integral_sub hi1 hi2]
      have := norm_integral_le_of_norm_le_const (μ := P)
        (f := fun y => χ n y * f y - χ n y * g y) (C := ε)
        (Filter.Eventually.of_forall fun y => by
          rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hχ01 n y).1]
          have h3 := hg y
          rw [Real.dist_eq, abs_sub_comm] at h3
          calc χ n y * |f y - g y| ≤ 1 * ε :=
                mul_le_mul (hχ01 n y).2 h3.le (abs_nonneg _) zero_le_one
            _ = ε := one_mul _)
      simpa [Real.norm_eq_abs] using this
    have hL : ∀ n, |(∫ y, χ n y * f y ∂μ) - ∫ y, χ n y * f y ∂ν| ≤ 2 * ε := fun n => by
      have e : ∫ y, χ n y * g y ∂μ = ∫ y, χ n y * g y ∂ν :=
        h _ ((hχ n).1.mul hgs) ((hχ n).2.1.mul_right)
      have h1 := hbound μ n
      have h2 := hbound ν n
      rw [e] at h1
      calc _ = |((∫ y, χ n y * f y ∂μ) - ∫ y, χ n y * g y ∂ν) -
            ((∫ y, χ n y * f y ∂ν) - ∫ y, χ n y * g y ∂ν)| := by ring_nf
        _ ≤ _ := (abs_sub _ _).trans (by linarith)
    exact le_of_tendsto' ((hlimit μ).sub (hlimit ν)).abs hL
  have : ∫ y, f y ∂μ - ∫ y, f y ∂ν = 0 := by
    by_contra hne
    have hpos : 0 < |∫ y, f y ∂μ - ∫ y, f y ∂ν| := abs_pos.2 hne
    have := key (|∫ y, f y ∂μ - ∫ y, f y ∂ν| / 4) (by positivity)
    linarith
  linarith

section TimeLemmas

variable {V : M → ℝ} {Pt : ℝ≥0 → Kernel M M}

theorem measurable_time_of_weightedCutoffs (hcut : WeightedCutoffs F M)
    (hP : IsDiffusionSemigroup F V Pt) (hV : MSmooth F V) {h : M → ℝ} (hh : MSmooth F h)
    {C : ℝ} (hb : ∀ y, |h y| ≤ C) (x : M) :
    Measurable fun s : ℝ => ∫ y, h y ∂Pt s.toNNReal x := by
  obtain ⟨χ, hχ, hlim⟩ := hcut
  exact measurable_semi_time_of_cutoffs F hP hV χ (fun n => ⟨(hχ n).1, (hχ n).2.1⟩)
    (fun n y => ⟨((hχ n).2.2 y).1, ((hχ n).2.2 y).2.1⟩) (fun y => by
      filter_upwards [hlim y] with n hn using hn) hh C hb x

/-- Dynkin increments for `BddSmooth` functions. -/
theorem dynkin_increment (hcut : WeightedCutoffs F M) (hP : IsDiffusionSemigroup F V Pt)
    (hV : MSmooth F V) (hD : DynkinBounded F V Pt) {ψ : M → ℝ} (hψ : BddSmooth F V ψ)
    (x : M) (a b : ℝ≥0) :
    ∫ y, ψ y ∂Pt b x - ∫ y, ψ y ∂Pt a x =
      ∫ r in (a : ℝ)..(b : ℝ), ∫ y, mgenerator F V ψ y ∂Pt r.toNNReal x := by
  obtain ⟨C, hC⟩ := hψ.2
  have hm := measurable_time_of_weightedCutoffs F hcut hP hV (msmooth_mgenerator F hV hψ.1)
    (fun y => (hC y).2.2) x
  haveI : ∀ s : ℝ, IsProbabilityMeasure (Pt s.toNNReal x) := fun s =>
    (hP.1 _).isProbabilityMeasure x
  have hb : ∀ s : ℝ, |∫ y, mgenerator F V ψ y ∂Pt s.toNNReal x| ≤ C := fun s =>
    abs_integral_le_of_prob (fun y => (hC y).2.2)
  have hi := intervalIntegrable_of_measurable_bdd hm hb
  rw [hD ψ hψ x b, hD ψ hψ x a]
  have := intervalIntegral.integral_interval_sub_left (hi 0 (b : ℝ)) (hi 0 (a : ℝ))
  linarith

theorem dynkin_increment_bound (hcut : WeightedCutoffs F M) (hP : IsDiffusionSemigroup F V Pt)
    (hV : MSmooth F V) (hD : DynkinBounded F V Pt) {ψ : M → ℝ} (hψ : BddSmooth F V ψ)
    (x : M) {B : ℝ} (hB : ∀ y, |mgenerator F V ψ y| ≤ B) {a b : ℝ≥0} (hab : a ≤ b) :
    |∫ y, ψ y ∂Pt b x - ∫ y, ψ y ∂Pt a x| ≤ B * ((b : ℝ) - a) := by
  rw [dynkin_increment F hcut hP hV hD hψ x a b]
  haveI : ∀ s : ℝ, IsProbabilityMeasure (Pt s.toNNReal x) := fun s =>
    (hP.1 _).isProbabilityMeasure x
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (a : ℝ)) (b := (b : ℝ))
    (f := fun r : ℝ => ∫ y, mgenerator F V ψ y ∂Pt r.toNNReal x) (C := B)
    (fun r _ => by simpa [Real.norm_eq_abs] using abs_integral_le_of_prob (fun y => hB y))
  have h2 : |(b : ℝ) - a| = (b : ℝ) - a := abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast hab))
  simpa [Real.norm_eq_abs, h2] using this

/-- Second-order Taylor bound in time for a diffusion semigroup acting on `g ∈ C_c^∞`. -/
theorem semi_time_taylor {Kk : ℝ≥0 → Kernel M M} (hK : IsDiffusionSemigroup F V Kk)
    (hV : MSmooth F V) {g : M → ℝ} (hg : MSmooth F g) (hgc : HasCompactSupport g) {C₃ : ℝ}
    (hC₃0 : 0 ≤ C₃) (hC₃ : ∀ z, |mgenerator F V (mgenerator F V g) z| ≤ C₃) (y : M)
    {p q : ℝ≥0} (hpq : p ≤ q) :
    |semi Kk q g y - semi Kk p g y - ((q : ℝ) - p) * semi Kk q (mgenerator F V g) y| ≤
      C₃ * ((q : ℝ) - p) ^ 2 := by
  have hLg : MSmooth F (mgenerator F V g) := msmooth_mgenerator F hV hg
  have hLgc : HasCompactSupport (mgenerator F V g) := hasCompactSupport_mgenerator F V hg hgc
  set Ψ : ℝ → ℝ := fun s => ∫ z, mgenerator F V g z ∂Kk s.toNNReal y with hΨ
  have hΨc : Continuous Ψ := continuous_dynkin_integrand F hK hg hgc hV y
  have hpq' : (p : ℝ) ≤ q := by exact_mod_cast hpq
  have hdiff : semi Kk q g y - semi Kk p g y = ∫ s in (p : ℝ)..(q : ℝ), Ψ s := by
    have h1 := hK.2.2 g hg hgc y q
    have h2 := hK.2.2 g hg hgc y p
    have := intervalIntegral.integral_interval_sub_left
      (hΨc.intervalIntegrable (μ := volume) 0 (q : ℝ))
      (hΨc.intervalIntegrable (μ := volume) 0 (p : ℝ))
    simp only [semi]
    rw [h1, h2]
    linarith
  have hlip : LipschitzWith ⟨C₃, hC₃0⟩ (fun t : ℝ≥0 => ∫ z, mgenerator F V g z ∂Kk t y) :=
    dynkin_lipschitz F hK hLg hLgc hC₃0 hC₃ y
  have hq : Ψ (q : ℝ) = semi Kk q (mgenerator F V g) y := by simp [hΨ, semi]
  have hpt : ∀ r ∈ Set.uIoc (p : ℝ) (q : ℝ), |Ψ r - Ψ (q : ℝ)| ≤ C₃ * ((q : ℝ) - p) := by
    intro r hr
    rw [Set.uIoc_of_le hpq'] at hr
    have hr0 : 0 ≤ r := (NNReal.coe_nonneg p).trans hr.1.le
    have hd := hlip.dist_le_mul r.toNNReal q
    rw [NNReal.dist_eq, Real.coe_toNNReal r hr0, Real.dist_eq] at hd
    simp only [hΨ, Real.toNNReal_coe]
    have hd' : |∫ z, mgenerator F V g z ∂Kk r.toNNReal y - ∫ z, mgenerator F V g z ∂Kk q y| ≤
        C₃ * |r - q| := hd
    refine hd'.trans (mul_le_mul_of_nonneg_left ?_ hC₃0)
    rw [abs_sub_comm, abs_of_nonneg (by linarith [hr.2])]
    linarith [hr.1]
  have hint : (∫ s in (p : ℝ)..(q : ℝ), Ψ s) - ((q : ℝ) - p) * Ψ (q : ℝ) =
      ∫ s in (p : ℝ)..(q : ℝ), (Ψ s - Ψ (q : ℝ)) := by
    rw [intervalIntegral.integral_sub (hΨc.intervalIntegrable (μ := volume) _ _)
      intervalIntegrable_const]
    simp
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (p : ℝ)) (b := (q : ℝ))
    (f := fun s => Ψ s - Ψ (q : ℝ)) (C := C₃ * ((q : ℝ) - p))
    (fun r hr => by simpa [Real.norm_eq_abs] using hpt r hr)
  rw [hdiff, ← hq]
  have h2 : |(q : ℝ) - p| = (q : ℝ) - p := abs_of_nonneg (sub_nonneg.2 hpq')
  rw [hint]
  simpa [Real.norm_eq_abs, h2, pow_two, mul_assoc] using hb

theorem BddSmooth.integrable {ψ : M → ℝ} (hψ : BddSmooth F V ψ) (P : Measure M)
    [IsFiniteMeasure P] : Integrable ψ P := by
  obtain ⟨C, hC⟩ := hψ.2
  exact integrable_of_bdd_cont hψ.1.continuous (fun y => (hC y).1)

/-- The quadratic increment estimate for `s ↦ ∫ (Kk (t-s) g) dPt s (x,·)`. -/
theorem quad_increment (hcut : WeightedCutoffs F M) (hP : IsDiffusionSemigroup F V Pt)
    (hV : MSmooth F V) (hD : DynkinBounded F V Pt) {μ : Measure M} {ρ : ℝ}
    {Kk : ℝ≥0 → Kernel M M} (hK : CanonicalDiffusion F V μ ρ Kk) {g : M → ℝ} (hg : MSmooth F g)
    (hgc : HasCompactSupport g) :
    ∃ K : ℝ, ∀ (x : M) (t a b : ℝ≥0), a ≤ b → b ≤ t →
      |(∫ y, semi Kk (t - b) g y ∂Pt b x) - ∫ y, semi Kk (t - a) g y ∂Pt a x| ≤
        K * ((b : ℝ) - a) ^ 2 := by
  have hLg : MSmooth F (mgenerator F V g) := msmooth_mgenerator F hV hg
  have hLgc : HasCompactSupport (mgenerator F V g) := hasCompactSupport_mgenerator F V hg hgc
  obtain ⟨C₃, hC₃0, hC₃⟩ := exists_abs_mgenerator_le F hV hLg hLgc
  obtain ⟨-, -, C₁, hC₁⟩ := hK.smoothing g hg hgc 0
  obtain ⟨-, -, C₂, hC₂⟩ := hK.smoothing _ hLg hLgc 0
  refine ⟨C₂ + C₃, fun x t a b hab hbt => ?_⟩
  have hub : ∀ r, BddSmooth F V (semi Kk r g) := fun r =>
    ⟨(hK.smoothing g hg hgc r).1, C₁, fun y => hC₁ r y⟩
  have hψb : ∀ r, BddSmooth F V (semi Kk r (mgenerator F V g)) := fun r =>
    ⟨(hK.smoothing _ hLg hLgc r).1, C₂, fun y => hC₂ r y⟩
  have hgen : ∀ r, mgenerator F V (semi Kk r g) = semi Kk r (mgenerator F V g) := fun r =>
    (hK.smoothing g hg hgc r).2.1
  set p : ℝ≥0 := t - b with hp
  set q : ℝ≥0 := t - a with hq
  have hpq : p ≤ q := tsub_le_tsub_left hab t
  have hδ : (q : ℝ) - p = (b : ℝ) - a := by
    rw [hp, hq, NNReal.coe_sub hbt, NNReal.coe_sub (hab.trans hbt)]; ring
  set δ : ℝ := (b : ℝ) - a with hδdef
  have hδ0 : 0 ≤ δ := by rw [← hδ]; exact sub_nonneg.2 (by exact_mod_cast hpq)
  haveI : IsProbabilityMeasure (Pt b x) := (hP.1 b).isProbabilityMeasure x
  haveI : ∀ s : ℝ, IsProbabilityMeasure (Pt s.toNNReal x) := fun s =>
    (hP.1 _).isProbabilityMeasure x
  set A : ℝ := ∫ y, semi Kk q (mgenerator F V g) y ∂Pt b x with hA
  -- first bracket
  have h1 : |(∫ y, semi Kk p g y ∂Pt b x) - (∫ y, semi Kk q g y ∂Pt b x) + δ * A| ≤
      C₃ * δ ^ 2 := by
    have hi1 := BddSmooth.integrable F (hub p) (Pt b x)
    have hi2 := BddSmooth.integrable F (hub q) (Pt b x)
    have hi3 := BddSmooth.integrable F (hψb q) (Pt b x)
    have e : (∫ y, semi Kk p g y ∂Pt b x) - (∫ y, semi Kk q g y ∂Pt b x) + δ * A =
        ∫ y, (semi Kk p g y - semi Kk q g y + δ * semi Kk q (mgenerator F V g) y) ∂Pt b x := by
      have hi12 : Integrable (fun y => semi Kk p g y - semi Kk q g y) (Pt b x) := hi1.sub hi2
      have hi4 : Integrable (fun y => δ * semi Kk q (mgenerator F V g) y) (Pt b x) :=
        hi3.const_mul δ
      rw [integral_add hi12 hi4, integral_sub hi1 hi2, integral_const_mul]
    rw [e]
    have := norm_integral_le_of_norm_le_const (μ := Pt b x)
      (f := fun y => semi Kk p g y - semi Kk q g y + δ * semi Kk q (mgenerator F V g) y)
      (C := C₃ * δ ^ 2) (Filter.Eventually.of_forall fun y => by
        have h := semi_time_taylor F hK.dynkin hV hg hgc hC₃0 hC₃ y hpq
        rw [hδ] at h
        rw [Real.norm_eq_abs, ← abs_neg]
        convert h using 2
        ring)
    simpa [Real.norm_eq_abs] using this
  -- second bracket
  have h2 : |((∫ y, semi Kk q g y ∂Pt b x) - ∫ y, semi Kk q g y ∂Pt a x) - δ * A| ≤
      C₂ * δ ^ 2 := by
    set G : ℝ → ℝ := fun r => ∫ y, semi Kk q (mgenerator F V g) y ∂Pt r.toNNReal x with hG
    have hGm : Measurable G := measurable_time_of_weightedCutoffs F hcut hP hV (hψb q).1
      (fun y => (hC₂ q y).1) x
    have hGb : ∀ r, |G r| ≤ C₂ := fun r => abs_integral_le_of_prob (fun y => (hC₂ q y).1)
    have hinc := dynkin_increment F hcut hP hV hD (hub q) x a b
    simp only [hgen q] at hinc
    have hGb' : G (b : ℝ) = A := by simp [hG, hA]
    have hint : (∫ r in (a : ℝ)..(b : ℝ), G r) - δ * G (b : ℝ) =
        ∫ r in (a : ℝ)..(b : ℝ), (G r - G (b : ℝ)) := by
      rw [intervalIntegral.integral_sub (intervalIntegrable_of_measurable_bdd hGm hGb _ _)
        intervalIntegrable_const]
      simp [hδdef]
    have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
    have hpt : ∀ r ∈ Set.uIoc (a : ℝ) (b : ℝ), ‖G r - G (b : ℝ)‖ ≤ C₂ * δ := by
      intro r hr
      rw [Set.uIoc_of_le hab'] at hr
      have hr0 : 0 ≤ r := (NNReal.coe_nonneg a).trans hr.1.le
      have hle : r.toNNReal ≤ b := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal r hr0]; exact hr.2
      have := dynkin_increment_bound F hcut hP hV hD (hψb q) x (B := C₂)
        (fun y => (hC₂ q y).2.2) hle
      rw [Real.coe_toNNReal r hr0] at this
      have hb2 : G (b : ℝ) - G r = ∫ y, semi Kk q (mgenerator F V g) y ∂Pt b x -
          ∫ y, semi Kk q (mgenerator F V g) y ∂Pt r.toNNReal x := by simp [hG]
      rw [Real.norm_eq_abs, abs_sub_comm, hb2]
      refine this.trans (mul_le_mul_of_nonneg_left ?_ ?_)
      · simp only [hδdef]; linarith [hr.1]
      · exact (abs_nonneg _).trans (hC₂ q x).1
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (a : ℝ)) (b := (b : ℝ))
      (f := fun r => G r - G (b : ℝ)) (C := C₂ * δ) hpt
    have hinc' : (∫ y, semi Kk q g y ∂Pt b x) - ∫ y, semi Kk q g y ∂Pt a x =
        ∫ r in (a : ℝ)..(b : ℝ), G r := hinc
    rw [hinc', ← hGb', hint]
    have habs : |(b : ℝ) - a| = δ := abs_of_nonneg hδ0
    rw [← Real.norm_eq_abs]
    refine hb.trans (le_of_eq ?_)
    rw [habs]; ring
  have : (∫ y, semi Kk p g y ∂Pt b x) - ∫ y, semi Kk q g y ∂Pt a x =
      ((∫ y, semi Kk p g y ∂Pt b x) - (∫ y, semi Kk q g y ∂Pt b x) + δ * A) +
      (((∫ y, semi Kk q g y ∂Pt b x) - ∫ y, semi Kk q g y ∂Pt a x) - δ * A) := by ring
  rw [this]
  refine (abs_add_le _ _).trans ?_
  nlinarith

end TimeLemmas

/-- **B2 (identification).** A family of kernels with `IsDiffusionSemigroup` and `DynkinBounded`
equals the canonical diffusion `Kk`, pointwise for all `t` and `x`. -/
theorem identification [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
    {V : M → ℝ} {Pt : ℝ≥0 → Kernel M M} {μ : Measure M} {ρ : ℝ} {Kk : ℝ≥0 → Kernel M M}
    (hP : IsDiffusionSemigroup F V Pt) (hV : MSmooth F V) (hD : DynkinBounded F V Pt)
    (hK : CanonicalDiffusion F V μ ρ Kk) :
    ∀ (t : ℝ≥0) (x : M), Pt t x = Kk t x := by
  haveI : SigmaCompactSpace M := sigmaCompactSpace_of_complete_riemannian (F := F) (M := M)
  have hcut : WeightedCutoffs F M := weightedCutoffs_of_complete F
  intro t x
  haveI := (hP.1 t).isProbabilityMeasure x
  haveI := (hK.markov t).isProbabilityMeasure x
  refine measure_eq_of_integral_smooth F hcut (fun g hg hgc => ?_)
  obtain ⟨K, hKq⟩ := quad_increment F hcut hP hV hD hK hg hgc
  have hconst := eq_of_quadratic_increments (fun a : ℝ≥0 => ∫ y, semi Kk (t - a) g y ∂Pt a x) t K
    (fun a b hab hbt => hKq x t a b hab hbt)
  have h0 : ∀ y, semi Kk 0 g y = g y := fun y => by
    have := hK.dynkin.2.2 g hg hgc y 0
    simpa [semi] using this
  have hu : BddSmooth F V (semi Kk t g) := by
    obtain ⟨-, -, C₁, hC₁⟩ := hK.smoothing g hg hgc 0
    exact ⟨(hK.smoothing g hg hgc t).1, C₁, fun y => hC₁ t y⟩
  have h1 := hD _ hu x 0
  simp only [tsub_self, h0] at hconst
  simp only [tsub_zero] at hconst
  simp only [NNReal.coe_zero, intervalIntegral.integral_same, add_zero] at h1
  rw [h1] at hconst
  simpa [semi] using hconst


end Generic

end CutoffRigidity.Riemann.Diff
