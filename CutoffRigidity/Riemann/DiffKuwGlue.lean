module

public import CutoffRigidity.Riemann.DiffKuwFinal
public import CutoffRigidity.Riemann.DiffKuwBE
public import CutoffRigidity.Riemann.DiffKuwApprox
public import CutoffRigidity.Riemann.DiffHopfLax
public import CutoffRigidity.Riemann.DiffKuwada

/-! # KUW-B glue: the dual-pair inequality and the contraction `W₂(K_t x, μ)²`

`dualPair`: for bounded Lipschitz `f(y) + g(z) ≤ d(y,z)²`,
`∫ f dK_t(a) + ∫ g dK_t(b) ≤ e^{-2ρt} d(a,b)²` (Kuwada's interpolation along a near-minimizing
`C¹` curve with the Hopf-Lax semigroup), and `contraction_of_BE`.
-/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set Topology
open scoped Manifold ContDiff ENNReal NNReal Topology BoundedContinuousFunction

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Glue

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M]

include F

theorem hcpt_dd (x : M) (R : ℝ) : IsCompact {y : M | dd x y ≤ R} := by
  by_cases hR : 0 ≤ R
  · convert isCompact_edist_le F x hR using 1
    ext y
    simp only [mem_ofPred_eq, dd]
    exact (ENNReal.le_ofReal_iff_toReal_le (edist_ne_top_of_connected F x y) hR).symm
  · convert isCompact_empty using 1
    ext y
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
    exact lt_of_lt_of_le (not_le.1 hR) (dd_nonneg _ _)

/-- Near-minimizing `C¹` curves. -/
theorem exists_curve (a b : M) {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 1 γ ∧ γ 0 = b ∧ γ 1 = a ∧
      (∫ τ in (0:ℝ)..1, ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ τ 1‖) ≤ dd a b + ε := by
  have hD : 0 ≤ dd a b + ε := by linarith [dd_nonneg a b]
  have hr : Manifold.riemannianEDist 𝓘(ℝ, F) b a < ENNReal.ofReal (dd a b + ε) := by
    rw [← IsRiemannianManifold.out (I := 𝓘(ℝ, F)),
      edist_eq_ofReal_dd (edist_ne_top_of_connected F), dd_comm]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [dd_nonneg a b])).2 (by linarith)
  obtain ⟨γ, h0, h1, hC, hlen, -⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt (I := 𝓘(ℝ, F)) hr zero_lt_one
  refine ⟨γ, hC, h0, h1, ?_⟩
  have hv := continuous_speed F hC
  rw [intervalIntegral.integral_of_le zero_le_one,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => norm_nonneg _)
      hv.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal hD (le_of_lt (lt_of_le_of_lt ?_ hlen))
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  simp_rw [ofReal_norm]
  exact lintegral_mono_set Ioc_subset_Icc_self

variable {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsProbabilityMeasure μ]
  (hμ : IsWeightedVolume F μ V)

/-- **Dual-pair inequality** (Kuwada). -/
theorem dualPair {ρ : ℝ} (hBE : BETestFun F V μ ρ (Kk F hV hμ)) (t : ℝ≥0)
    (f g : M →ᵇ ℝ) (L J : ℝ≥0) (hf : LipschitzWith L f) (hg : LipschitzWith J g)
    (hfg : ∀ x y, f x + g y ≤ (edist x y).toReal ^ 2) (a b : M) :
    ∫ y, f y ∂(Kk F hV hμ t a) + ∫ y, g y ∂(Kk F hV hμ t b) ≤
      Real.exp (-2 * ρ * t) * (edist a b).toReal ^ 2 := by
  by_cases ht : t = 0
  · subst ht
    rw [Kk_zero, Kernel.id_apply, Kernel.id_apply, integral_dirac' _ _ f.continuous.stronglyMeasurable,
      integral_dirac' _ _ g.continuous.stronglyMeasurable]
    simpa using hfg a b
  have hfin := edist_ne_top_of_connected (F := F) (M := M)
  have hcpt := hcpt_dd F (M := M)
  have hA : SharpApprox F M := sharpApprox F
  set P := Kk F hV hμ with hP
  haveI hPm : ∀ s, IsMarkovKernel (P s) := Kk_markov F hV hμ
  set h : M → ℝ := fun z => -g z with hh_def
  have hh : LipschitzWith J h := by
    intro x y
    simpa [h, edist_dist, dist_neg_neg] using hg x y
  set B : ℝ := ‖g‖ with hBdef
  have hb : ∀ z, |h z| ≤ B := fun z => by
    simpa [h, Real.norm_eq_abs] using g.norm_coe_le_norm z
  have hQc : ∀ r, 0 < r → Continuous (hlQ h r) := fun r hr => continuous_hlQ hfin hcpt hh hb hr
  have hQb : ∀ r, 0 < r → ∀ y, |hlQ h r y| ≤ B := fun r hr y => abs_hlQ_le hb hr y
  have hhc : Continuous h := g.continuous.neg
  -- the data of the interpolation lemma
  set W : ℝ → M → ℝ := fun r y => semi P t (hlQ h r) y with hW
  set W0 : M → ℝ := semi P t h with hW0
  set Sg : ℝ → M → ℝ := fun r y => ∫ z, lipAt (hlQ h r) z ^ 2 ∂(P t y) with hSg
  set c : ℝ := Real.exp (-ρ * t) with hc
  have hc2 : c ^ 2 = Real.exp (-2 * ρ * t) := by
    rw [hc, sq, ← Real.exp_add]; congr 1; ring
  have h1 : ∀ r, 0 < r → MSmooth F (W r) := fun r hr =>
    semi_smooth_of_lip F hV hμ (hQc r hr) (hQb r hr) ht
  have h2 : ∀ r₀, 0 < r₀ → ∃ C : ℝ, ∀ r s y, r₀ ≤ r → r ≤ 1 → r₀ ≤ s → s ≤ 1 →
      |W r y - W s y| ≤ C * |r - s| := by
    intro r₀ hr₀
    refine ⟨4 * (J : ℝ) ^ 2 * (1 / r₀), fun r s y hr₀r hr1 hr₀s hs1 => ?_⟩
    have := semi_sub_le F hV hμ (hQc r (hr₀.trans_le hr₀r)) (hQc s (hr₀.trans_le hr₀s))
      (hQb r (hr₀.trans_le hr₀r)) (hQb s (hr₀.trans_le hr₀s)) t
      (δ := 4 * (J : ℝ) ^ 2 * (1 / r₀) * |r - s|)
      (fun z => by
        have := abs_hlQ_sub_le hfin hcpt hh hb hr₀ hr₀s hr₀r hr1 z
        simpa using this) y
    exact this
  -- the dual-pair argument for a fixed curve
  have key : ∀ ε : ℝ, 0 < ε →
      ∫ y, f y ∂(P t a) + ∫ y, g y ∂(P t b) ≤ Real.exp (-2 * ρ * t) * (dd a b + ε) ^ 2 := by
    intro ε hε
    obtain ⟨γ, hγ, hγ0, hγ1, hℓ⟩ := exists_curve F a b hε
    have hK : IsCompact (γ '' Set.Icc (0:ℝ) 1) := isCompact_Icc.image hγ.continuous
    obtain ⟨CG, hCG0, hCG⟩ := grad_semi_sub_le F hV hμ ht hK
    have h3 : ∀ r₀, 0 < r₀ → ∃ C : ℝ, ∀ r s, r₀ ≤ r → r ≤ 1 → r₀ ≤ s → s ≤ 1 →
        ∀ τ ∈ Set.Icc (0:ℝ) 1,
          ‖mgrad F (W r) (γ τ) - mgrad F (W s) (γ τ)‖ ≤ C * |r - s| := by
      intro r₀ hr₀
      refine ⟨CG * (4 * (J : ℝ) ^ 2 * (1 / r₀)), fun r s hr₀r hr1 hr₀s hs1 τ hτ => ?_⟩
      have := hCG (hlQ h r) (hlQ h s) B B (hQc r (hr₀.trans_le hr₀r)) (hQc s (hr₀.trans_le hr₀s))
        (hQb r (hr₀.trans_le hr₀r)) (hQb s (hr₀.trans_le hr₀s))
        (4 * (J : ℝ) ^ 2 * (1 / r₀) * |r - s|) (by positivity)
        (fun z => by
          have := abs_hlQ_sub_le hfin hcpt hh hb hr₀ hr₀s hr₀r hr1 z
          simpa using this) (γ τ) ⟨τ, hτ, rfl⟩
      calc _ ≤ CG * (4 * (J : ℝ) ^ 2 * (1 / r₀) * |r - s|) := this
        _ = _ := by ring
    have h4 : ∀ r, 0 < r → ∀ y, ‖mgrad F (W r) y‖ ^ 2 ≤ c ^ 2 * Sg r y := by
      intro r hr y
      obtain ⟨C, hC⟩ := lipschitzWith_hlQ hfin hcpt hh hb hr
      rw [hc2]
      exact beLip F hV hμ hBE hA hC (hQb r hr) ht y
    have h5 : ∀ r, 0 < r → ∀ y, 0 ≤ Sg r y ∧ ∀ s, r < s →
        (W s y - W r y) / (s - r) ≤ -(1 / 2) * (r / s) * Sg r y := by
      intro r hr y
      refine ⟨integral_nonneg fun z => sq_nonneg _, fun s hrs => ?_⟩
      have hs : 0 < s := hr.trans hrs
      obtain ⟨C, hC⟩ := lipschitzWith_hlQ hfin hcpt hh hb hr
      have hint : Integrable (fun z => lipAt (hlQ h r) z ^ 2) (P t y) :=
        integrable_lipAt_sq F hV hμ hC t y
      have hi1 := integrable_Kk_of_bdd F hV hμ (hQc s hs) (hQb s hs) t y
      have hi2 := integrable_Kk_of_bdd F hV hμ (hQc r hr) (hQb r hr) t y
      have hpt : ∀ z, hlQ h s z - hlQ h r z ≤
          (-(1 / 2) * (r / s) * (s - r)) * lipAt (hlQ h r) z ^ 2 := by
        intro z
        obtain ⟨E, hE0, hEl, hEs⟩ := hlQ_hj hfin hcpt hh hb hr z
        refine (hEs s hrs).trans ?_
        have h0 := lipAt_nonneg (hlQ h r) z
        have hsq : r ^ 2 * lipAt (hlQ h r) z ^ 2 ≤ E ^ 2 := by
          have : r * lipAt (hlQ h r) z ≤ E := by
            rwa [le_div_iff₀ hr, mul_comm] at hEl
          nlinarith [mul_nonneg hr.le h0]
        have hsr : 0 < s - r := by linarith
        rw [div_le_iff₀ (by positivity)]
        have : (-(1 / 2) * (r / s) * (s - r) * lipAt (hlQ h r) z ^ 2) * (2 * r * s)
            = -(r ^ 2 * lipAt (hlQ h r) z ^ 2 * (s - r)) := by
          field_simp
        rw [this]
        nlinarith [mul_le_mul_of_nonneg_right hsq hsr.le]
      have hmono : ∫ z, (hlQ h s z - hlQ h r z) ∂(P t y) ≤
          ∫ z, ((-(1 / 2) * (r / s) * (s - r)) * lipAt (hlQ h r) z ^ 2) ∂(P t y) :=
        integral_mono (hi1.sub hi2) (hint.const_mul _) hpt
      rw [integral_sub hi1 hi2, integral_const_mul] at hmono
      have hsr : 0 < s - r := by linarith
      rw [div_le_iff₀ hsr]
      have e : W s y - W r y = ∫ z, hlQ h s z ∂(P t y) - ∫ z, hlQ h r z ∂(P t y) := rfl
      rw [e]
      simp only [hSg]
      nlinarith [hmono]
    have h6 : Continuous W0 ∧ ∃ C : ℝ, ∀ r, 0 < r → r ≤ 1 → ∀ y, |W r y - W0 y| ≤ C * r := by
      refine ⟨(semi_smooth_of_lip F hV hμ hhc hb ht).continuous, (J : ℝ) ^ 2 / 2, ?_⟩
      intro r hr hr1 y
      have := semi_sub_le F hV hμ (hQc r hr) hhc (hQb r hr) hb t
        (δ := r * (J : ℝ) ^ 2 / 2)
        (fun z => by
          have h1 := hlQ_le_self hb hr z
          have h2 := self_sub_le hfin hcpt hh hb hr z
          rw [abs_le]; constructor <;> nlinarith) y
      calc _ ≤ r * (J : ℝ) ^ 2 / 2 := this
        _ = _ := by ring
    have main := curve_interpolation F hγ h1 h2 h3 h4 h5 h6
    rw [hγ0, hγ1] at main
    have hℓ0 : 0 ≤ ∫ τ in (0:ℝ)..1, ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ τ 1‖ :=
      intervalIntegral.integral_nonneg zero_le_one fun τ _ => norm_nonneg _
    have hsq : (∫ τ in (0:ℝ)..1, ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ τ 1‖) ^ 2 ≤ (dd a b + ε) ^ 2 :=
      pow_le_pow_left₀ hℓ0 hℓ 2
    -- endpoints
    have hfQ : ∫ y, f y ∂(P t a) ≤ W (1 / 2) a := by
      have hi := integrable_Kk_of_bdd F hV hμ (hQc (1 / 2) (by norm_num)) (hQb (1 / 2) (by norm_num)) t a
      have hif := integrable_Kk_of_bdd F hV hμ f.continuous (B := ‖f‖)
        (fun x => by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm x) t a
      refine integral_mono hif hi fun y => ?_
      refine le_ciInf fun z => ?_
      have := hfg y z
      have e : dd y z ^ 2 / (2 * (1 / 2 : ℝ)) = (edist y z).toReal ^ 2 := by
        simp [dd]
      simp only [h]
      rw [e]; linarith
    have hW0 : W0 b = -∫ y, g y ∂(P t b) := by
      simp only [hW0, semi, h]
      exact integral_neg _
    have hcnn : 0 ≤ c ^ 2 := sq_nonneg c
    calc ∫ y, f y ∂(P t a) + ∫ y, g y ∂(P t b) ≤ W (1 / 2) a - W0 b := by rw [hW0]; linarith
      _ ≤ c ^ 2 * _ := main
      _ ≤ c ^ 2 * (dd a b + ε) ^ 2 := mul_le_mul_of_nonneg_left hsq hcnn
      _ = _ := by rw [hc2]
  have hlim : Tendsto (fun ε : ℝ => Real.exp (-2 * ρ * t) * (dd a b + ε) ^ 2) (𝓝[>] 0)
      (𝓝 (Real.exp (-2 * ρ * t) * (dd a b + 0) ^ 2)) :=
    (((continuous_const.add continuous_id).pow 2).const_mul _).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have := ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => key ε hε)
  simpa [dd] using this

/-- **The contraction** `W₂(K_t(x,·), μ)² ≤ e^{-2ρt} ∫ d(x,y)² dμ` from the pointwise
Bakry-Emery bound. -/
theorem contraction_of_BE {ρ : ℝ} (hBE : BETestFun F V μ ρ (Kk F hV hμ)) (t : ℝ≥0) (x : M) :
    CutCur.wasserstein2 (Kk F hV hμ t x) μ ^ 2 ≤
      ENNReal.ofReal (Real.exp (-2 * ρ * t)) * ∫⁻ y, edist x y ^ 2 ∂μ :=
  contraction_of_dualPair F (Kk F hV hμ) (Kk_markov F hV hμ) (Kk_bind F hV hμ)
    (fun t f g L J hf hg hfg a b => dualPair F hV hμ hBE t f g L J hf hg hfg a b) t x

end Glue

end CutoffRigidity.Riemann.Diff
