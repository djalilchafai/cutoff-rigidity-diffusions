module
public import CutoffRigidity.GibbsRNFromL2Tests

/-! # Genuine Lʳ RN densities from Lᵅ bounds on compact tests

If an absolutely continuous probability law with an L² density satisfies
|∫ f dν| ≤ C ‖f‖_{Lᵅ(μ)} on compact C² tests, with 1 < α ≤ 2, then the bound
extends by actual L² density of compact tests to every L² input. Testing it
against the truncated powers min(h,n)^(r-1) and monotone convergence gives
‖dν/dμ‖_{Lʳ(μ)} ≤ C for the conjugate exponent r = α/(α-1).
-/
public section
namespace CutoffRigidity
open MeasureTheory Filter
open scoped Topology ENNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

set_option maxHeartbeats 800000 in
/-- The compact-test Lᵖ bound extends to every L² input. -/
theorem abs_integral_mul_rnDeriv_le_of_compact_test_bound
    {V : E → ℝ} (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ν : Measure E) [IsProbabilityMeasure ν] (hAC : ν ≪ gibbsMeasure volume V)
    (hRN : MemLp (fun x => (ν.rnDeriv (gibbsMeasure volume V) x).toReal) 2 (gibbsMeasure volume V))
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ f : E → ℝ, ContDiff ℝ 2 f → HasCompactSupport f →
      |∫ x, f x ∂ν| ≤ C * (eLpNorm f p (gibbsMeasure volume V)).toReal)
    {G : E → ℝ} (hG : MemLp G 2 (gibbsMeasure volume V)) :
    |∫ x, G x * (ν.rnDeriv (gibbsMeasure volume V) x).toReal ∂gibbsMeasure volume V| ≤
      C * (eLpNorm G p (gibbsMeasure volume V)).toReal := by
  let := hp
  let μ := gibbsMeasure volume V
  let h := fun x => (ν.rnDeriv μ x).toReal
  let w := hG.toLp G
  let hL := hRN.toLp h
  have hpair {F : E → ℝ} (hF : MemLp F 2 μ) : (∫ x, F x * h x ∂μ) = inner ℝ (hF.toLp F) hL := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hF.coeFn_toLp, hRN.coeFn_toLp] with x hx hy
    rw [Real.inner_apply, hx, hy, mul_comm]
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hη : 0 < δ / (C + ‖hL‖ + 1) := div_pos hδ (by positivity)
  obtain ⟨u, hu, hdist⟩ := (compactGibbsGeneratorDomain_dense V hp).exists_dist_lt w hη
  let f := compactGibbsRepresentative V ⟨u, hu⟩
  obtain ⟨hf, hfc, hfu⟩ := compactGibbsRepresentative_spec V ⟨u, hu⟩
  have hfLp : MemLp f 2 μ := hf.continuous.memLp_of_hasCompactSupport hfc
  have hfw : hfLp.toLp f = u := Lp.ext (hfLp.coeFn_toLp.trans hfu)
  have hν : (∫ x, f x ∂ν) = ∫ x, f x * h x ∂μ := by
    rw [integral_eq_integral_toReal_rnDeriv_mul ν μ hAC hf.continuous.measurable]
    exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  have hdiff : (∫ x, G x * h x ∂μ) = (∫ x, f x * h x ∂μ) + inner ℝ (w - u) hL := by
    rw [hpair hG, hpair hfLp, hfw, inner_sub_left]
    ring
  have hCS : |inner ℝ (w - u) hL| ≤ ‖w - u‖ * ‖hL‖ := abs_real_inner_le_norm _ _
  have hwu : ‖w - u‖ < δ / (C + ‖hL‖ + 1) := by rwa [← dist_eq_norm]
  -- the Lᵖ norm of the test is close to that of the input
  have hGp : MemLp G p μ := hG.mono_exponent hp2
  have hdLp : MemLp (fun x => f x - G x) 2 μ := hfLp.sub hG
  have hTri : eLpNorm f p μ ≤ eLpNorm G p μ + eLpNorm (fun x => f x - G x) 2 μ := by
    have he : f = G + fun x => f x - G x := by funext x; simp
    calc
      eLpNorm f p μ = eLpNorm (G + fun x => f x - G x) p μ := by rw [← he]
      _ ≤ eLpNorm G p μ + eLpNorm (fun x => f x - G x) p μ := eLpNorm_add_le hp1
      _ ≤ _ := add_le_add le_rfl (eLpNorm_le_eLpNorm_of_exponent_le hp2)
  have hnorm : (eLpNorm (fun x => f x - G x) 2 μ).toReal = ‖w - u‖ := by
    rw [norm_sub_rev, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_ae
    filter_upwards [Lp.coeFn_sub u w, hfu, hG.coeFn_toLp] with x hs hfx hGx
    rw [hs, Pi.sub_apply, ← hfx, hGx]
  have hTriR : (eLpNorm f p μ).toReal ≤ (eLpNorm G p μ).toReal + ‖w - u‖ := by
    rw [← hnorm, ← ENNReal.toReal_add hGp.eLpNorm_ne_top hdLp.eLpNorm_ne_top]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hGp.eLpNorm_ne_top, hdLp.eLpNorm_ne_top⟩) hTri
  have hb := hBound f hf hfc
  rw [hν] at hb
  rw [hdiff]
  have hwu0 : 0 ≤ ‖w - u‖ := norm_nonneg _
  have hsmall : ‖w - u‖ * (C + ‖hL‖) ≤ δ := by
    have h1 : ‖w - u‖ * (C + ‖hL‖ + 1) ≤ δ := by
      have := (lt_div_iff₀ (by positivity : (0:ℝ) < C + ‖hL‖ + 1)).mp hwu
      linarith
    nlinarith
  calc
    |(∫ x, f x * h x ∂μ) + inner ℝ (w - u) hL| ≤ |∫ x, f x * h x ∂μ| + |inner ℝ (w - u) hL| :=
      abs_add_le _ _
    _ ≤ C * ((eLpNorm G p μ).toReal + ‖w - u‖) + ‖w - u‖ * ‖hL‖ :=
      add_le_add (hb.trans (mul_le_mul_of_nonneg_left hTriR hC)) hCS
    _ ≤ _ := by nlinarith

set_option maxHeartbeats 1200000 in
/-- Genuine Lʳ integrability of the RN density, by duality with Lᵅ,
α = r/(r-1), on truncated powers of the density itself. -/
theorem eLpNorm_rnDeriv_le_of_compact_test_bound
    {V : E → ℝ} (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ν : Measure E) [IsProbabilityMeasure ν] (hAC : ν ≪ gibbsMeasure volume V)
    (hRN : MemLp (fun x => (ν.rnDeriv (gibbsMeasure volume V) x).toReal) 2 (gibbsMeasure volume V))
    {α : ℝ} (hα : 1 < α) (hα2 : α ≤ 2) (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ f : E → ℝ, ContDiff ℝ 2 f → HasCompactSupport f →
      |∫ x, f x ∂ν| ≤ C * (eLpNorm f (ENNReal.ofReal α) (gibbsMeasure volume V)).toReal) :
    eLpNorm (fun x => (ν.rnDeriv (gibbsMeasure volume V) x).toReal)
      (ENNReal.ofReal (α / (α - 1))) (gibbsMeasure volume V) ≤ ENNReal.ofReal C := by
  let := hp
  let μ := gibbsMeasure volume V
  let h := fun x => (ν.rnDeriv μ x).toReal
  let r := α / (α - 1)
  have hα0 : 0 < α := zero_lt_one.trans hα
  have hα1 : 0 < α - 1 := by linarith
  have hr : 0 < r := div_pos hα0 hα1
  have hr1 : 0 < r - 1 := by
    have : r - 1 = 1 / (α - 1) := by dsimp only [r]; field_simp; ring
    rw [this]; positivity
  have hrα : (r - 1) * α = r := by dsimp only [r]; field_simp; ring
  have hexp : (1 - 1 / α) * r = 1 := by dsimp only [r]; field_simp
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal α := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hα.le
  have hp2 : ENNReal.ofReal α ≤ 2 := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]; exact ENNReal.ofReal_le_ofReal hα2
  have hhM : Measurable h := (Measure.measurable_rnDeriv ν μ).ennreal_toReal
  have hh0 (x : E) : 0 ≤ h x := ENNReal.toReal_nonneg
  have hhI : Integrable h μ := hRN.integrable (by norm_num)
  let hn := fun (n : ℕ) (x : E) => min (h x) n
  have hnM (n : ℕ) : Measurable (hn n) := hhM.min measurable_const
  have hn0 (n : ℕ) (x : E) : 0 ≤ hn n x := le_min (hh0 x) (Nat.cast_nonneg n)
  have hnle (n : ℕ) (x : E) : hn n x ≤ n := min_le_right _ _
  -- the truncated moment bound
  have hTrunc (n : ℕ) : ∫ x, hn n x ^ r ∂μ ≤ C ^ r := by
    let Gn := fun x => hn n x ^ (r - 1)
    have hGM : Measurable Gn := (hnM n).pow_const _
    have hGb (x : E) : ‖Gn x‖ ≤ (n : ℝ) ^ (r - 1) := by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (hn0 n x) _)]
      exact Real.rpow_le_rpow (hn0 n x) (hnle n x) hr1.le
    have hGLp : MemLp Gn 2 μ := MemLp.of_bound hGM.aestronglyMeasurable _ (Eventually.of_forall hGb)
    have hIr : Integrable (fun x => hn n x ^ r) μ :=
      (integrable_const ((n : ℝ) ^ r)).mono' ((hnM n).pow_const _).aestronglyMeasurable
        (Eventually.of_forall fun x => by
          rw [Real.norm_of_nonneg (Real.rpow_nonneg (hn0 n x) _)]
          exact Real.rpow_le_rpow (hn0 n x) (hnle n x) hr.le)
    have hGh : Integrable (fun x => Gn x * h x) μ :=
      hhI.bdd_mul hGM.aestronglyMeasurable (Eventually.of_forall hGb)
    let I := ∫ x, hn n x ^ r ∂μ
    have hI0 : 0 ≤ I := integral_nonneg fun x => Real.rpow_nonneg (hn0 n x) _
    have hlow : I ≤ ∫ x, Gn x * h x ∂μ := by
      apply integral_mono hIr hGh
      intro x
      have he : hn n x ^ r = Gn x * hn n x := by
        rcases (hn0 n x).eq_or_lt with h0 | hpos
        · rw [← h0, Real.zero_rpow hr.ne']
          simp
        · dsimp only [Gn]
          rw [← Real.rpow_add_one hpos.ne']
          ring_nf
      show hn n x ^ r ≤ Gn x * h x
      rw [he]
      exact mul_le_mul_of_nonneg_left (min_le_left _ _) (Real.rpow_nonneg (hn0 n x) _)
    have hNorm : (eLpNorm Gn (ENNReal.ofReal α) μ).toReal = I ^ (1 / α) := by
      rw [(hGLp.mono_exponent hp2).eLpNorm_eq_integral_rpow_norm
        (by simp [hα0]) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hα0.le,
        ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun x => by positivity) _), one_div]
      congr 1
      apply integral_congr_ae (Eventually.of_forall fun x => ?_)
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (hn0 n x) _), ← Real.rpow_mul (hn0 n x), hrα]
    have hdual := abs_integral_mul_rnDeriv_le_of_compact_test_bound hp ν hAC hRN hp1 hp2 C hC hBound hGLp
    rw [hNorm] at hdual
    have hkey : I ≤ C * I ^ (1 / α) := hlow.trans ((le_abs_self _).trans hdual)
    change I ≤ C ^ r
    rcases hI0.eq_or_lt with h0 | hIpos
    · rw [← h0]; exact Real.rpow_nonneg hC _
    · have hsplit : I = I ^ (1 / α) * I ^ (1 - 1 / α) := by
        rw [← Real.rpow_add hIpos]; norm_num
      have hroot : I ^ (1 - 1 / α) ≤ C := by
        have hpos' := Real.rpow_pos_of_pos hIpos (1 / α)
        have : I ^ (1 / α) * I ^ (1 - 1 / α) ≤ I ^ (1 / α) * C := by
          rw [← hsplit, mul_comm]; exact hkey
        exact le_of_mul_le_mul_left this hpos'
      have hh := Real.rpow_le_rpow (Real.rpow_nonneg hI0 _) hroot hr.le
      rwa [← Real.rpow_mul hI0, hexp, Real.rpow_one] at hh
  -- monotone convergence
  have hLint : ∫⁻ x, ENNReal.ofReal (h x ^ r) ∂μ ≤ ENNReal.ofReal (C ^ r) := by
    have hsup (x : E) : ENNReal.ofReal (h x ^ r) = ⨆ n : ℕ, ENNReal.ofReal (hn n x ^ r) := by
      apply le_antisymm
      · apply le_iSup_of_le (⌈h x⌉₊)
        rw [show hn ⌈h x⌉₊ x = h x from min_eq_left (Nat.le_ceil _)]
      · exact iSup_le fun n => ENNReal.ofReal_le_ofReal
          (Real.rpow_le_rpow (hn0 n x) (min_le_left _ _) hr.le)
    simp_rw [hsup]
    rw [lintegral_iSup (fun n => ((hnM n).pow_const r).ennreal_ofReal)]
    · apply iSup_le
      intro n
      rw [← ofReal_integral_eq_lintegral_ofReal _ (Eventually.of_forall fun x =>
        Real.rpow_nonneg (hn0 n x) r)]
      · exact ENNReal.ofReal_le_ofReal (hTrunc n)
      · exact (integrable_const ((n : ℝ) ^ r)).mono' ((hnM n).pow_const _).aestronglyMeasurable
          (Eventually.of_forall fun x => by
            rw [Real.norm_of_nonneg (Real.rpow_nonneg (hn0 n x) _)]
            exact Real.rpow_le_rpow (hn0 n x) (hnle n x) hr.le)
    · intro a b hab x
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (hn0 a x)
        (min_le_min_left _ (by exact_mod_cast hab)) hr.le)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hr) ENNReal.ofReal_ne_top
    hhM.aestronglyMeasurable, ENNReal.toReal_ofReal hr.le]
  have he (x : E) : ‖h x‖ₑ ^ r = ENNReal.ofReal (h x ^ r) := by
    rw [Real.enorm_of_nonneg (hh0 x), ENNReal.ofReal_rpow_of_nonneg (hh0 x) hr.le]
  simp_rw [he]
  calc
    _ ≤ ENNReal.ofReal (C ^ r) ^ (1 / r) := ENNReal.rpow_le_rpow hLint (by positivity)
    _ = _ := by
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hC _) (by positivity), one_div,
        Real.rpow_rpow_inv hC hr.ne']

end CutoffRigidity
