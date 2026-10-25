module

public import CutoffRigidity.Paper.CarrierDefs
public import CutoffRigidity.Extra.EuclideanDiffusion
public import CutoffRigidity.Extra.OUFisher
public import CutoffRigidity.Extra.OUMeanStart
public import CutoffRigidity.Extra.OUInfty
public import CutoffRigidity.Extra.Dynamics
public import CutoffRigidity.Extra.FisherDecayGeneral
public import CutoffRigidity.Extra.Normalization
public import CutoffRigidity.Extra.Temperature
public import CutoffRigidity.Extra.TemperatureSDE
public import CutoffRigidity.ConvexInteractionCurvature

/-! # Brownian-free (kernel) versions of the law-of-the-process statements

`ou_fisher_information_K`, `ou_mean_start_cutoff_K`, `ou_lp_infty_fails_K`,
`langevin_entropy_decay_K`, `langevin_fisher_decay_K`, `langevin_fisher_dini_K`,
`normalization_cutoff_K`, `temperature_cutoff_K`: the Challenge statements with the Brownian
carrier `(Ω, B, P, X)` replaced by transition kernels `Pt` (`IsEuclideanLangevin`, resp.
`IsSigmaLangevin` for the `σ`-diffusions). Proofs go through the transfer lemmas of
`EuclideanDiffusion`.
-/

public section

set_option backward.isDefEq.respectTransparency false

namespace CutCur

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

/-- Time change: the `σ`-diffusion `Y_t`, speeded up as `Y_{u/σ²}`, is the Euclidean Langevin
diffusion for `V/σ²`. -/
theorem isEuclideanLangevin_of_sigma {d : ℕ} {V : Rd d → ℝ} {σ : ℝ} (hσ : 0 < σ)
    {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)} (h : IsSigmaLangevin V σ Pt) :
    IsEuclideanLangevin (fun x => V x / σ ^ 2)
      (fun u => Pt (((σ ^ 2)⁻¹).toNNReal * u)) := by
  obtain ⟨hV, hp, hmk, hsg, hdyn⟩ := h
  have hs2 : 0 < σ ^ 2 := by positivity
  have hcc : (0 : ℝ) ≤ (σ ^ 2)⁻¹ := by positivity
  have hcc' : (((σ ^ 2)⁻¹).toNNReal : ℝ) = (σ ^ 2)⁻¹ := Real.coe_toNNReal _ hcc
  refine ⟨hV.div_const _, hp, fun t => hmk _, fun s t => ?_, ?_⟩
  · simp only
    rw [mul_add]
    exact hsg _ _
  · intro f hf hfc x t
    have hd := hdyn f hf hfc x (((σ ^ 2)⁻¹).toNNReal * t)
    have hVd : Differentiable ℝ V := hV.differentiable (by simp)
    simp only
    rw [hd]
    congr 1
    set G : ℝ → ℝ := fun s => ∫ y, (σ ^ 2 * laplacian f y - inner ℝ (gradient V y) (gradient f y))
      ∂Pt s.toNNReal x with hG
    have hF : ∀ r ∈ Set.uIcc (0 : ℝ) (t : ℝ),
        ∫ y, generator (fun x => V x / σ ^ 2) f y ∂Pt (((σ ^ 2)⁻¹).toNNReal * r.toNNReal) x =
          (σ ^ 2)⁻¹ * G ((σ ^ 2)⁻¹ * r) := by
      intro r hr
      have hr0 : 0 ≤ r := by
        rcases Set.mem_uIcc.1 hr with h | h
        · exact h.1
        · linarith [h.1, t.2]
      have e1 : ((σ ^ 2)⁻¹ * r).toNNReal = ((σ ^ 2)⁻¹).toNNReal * r.toNNReal :=
        Real.toNNReal_mul hcc
      simp only [hG, e1]
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [generator, CutoffRigidity.Paper.gradient_div_const hVd, inner_smul_left, conj_trivial]
      field_simp
    rw [intervalIntegral.integral_congr hF, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (fun s => G s) (inv_ne_zero hs2.ne')]
    simp only [mul_zero, NNReal.coe_mul, hcc', inv_inv, smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hs2.ne', one_mul]

end CutCur

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff Asymptotics

/-! ### Generic helpers -/

theorem hasCutoff_congr_eventually_iff {p q : ℕ → ℝ → ℝ≥0∞} {t : ℕ → ℝ} {b a : ℝ≥0∞}
    (h : ∀ᶠ n in atTop, p n = q n) :
    CutCur.HasCutoff p t b a ↔ CutCur.HasCutoff q t b a :=
  ⟨CutCur.hasCutoff_congr_eventually h,
    CutCur.hasCutoff_congr_eventually (h.mono fun _ hn => hn.symm)⟩

/-- Carriers, dimension by dimension, for a family of smooth convex Euclidean Langevin potentials. -/
theorem exists_carriers_of_K {V : ∀ n, CutCur.Rd n → ℝ}
    {Pt : ∀ n, ℝ≥0 → Kernel (CutCur.Rd n) (CutCur.Rd n)}
    (hL : ∀ n, 0 < n → CutCur.IsEuclideanLangevin (V n) (Pt n))
    (hH : ∀ n, 0 < n → ∀ x z : CutCur.Rd n, 0 ≤ fderiv ℝ (fderiv ℝ (V n)) x z z) :
    ∃ (Ω : ℕ → Type) (_ : ∀ n, MeasurableSpace (Ω n)) (B : ∀ n, ℝ≥0 → Ω n → CutCur.Rd n)
      (P : ∀ n, Measure (Ω n)) (X : ∀ n, CutCur.Rd n → ℝ≥0 → Ω n → CutCur.Rd n),
      (∀ n, 0 < n → CutCur.IsLangevin (V n) (B n) (P n) (X n)) ∧
        ∀ n, 0 < n → ∀ (t : ℝ≥0) (x₀ : CutCur.Rd n), (P n).map (X n x₀ t) = Pt n t x₀ := by
  classical
  have hn : ∀ n : ℕ, ∃ (Ω : Type) (_ : MeasurableSpace Ω) (B : ℝ≥0 → Ω → CutCur.Rd n)
      (P : Measure Ω) (X : CutCur.Rd n → ℝ≥0 → Ω → CutCur.Rd n), 0 < n →
      (CutCur.IsLangevin (V n) B P X ∧
        ∀ (t : ℝ≥0) (x₀ : CutCur.Rd n), P.map (X x₀ t) = Pt n t x₀) := by
    intro n
    by_cases hn : 0 < n
    · obtain ⟨Ω, hΩ, B, P, X, -, h1, h2⟩ :=
        CutCur.exists_isLangevin_of_isEuclideanLangevin (hL n hn) (hH n hn)
      exact ⟨Ω, hΩ, B, P, X, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨Unit, inferInstance, fun _ _ => 0, 0, fun _ _ _ => 0, fun h' => absurd h' hn⟩
  choose Ω hΩ B P X hX using hn
  exact ⟨Ω, hΩ, B, P, X, fun n hn => (hX n hn).1, fun n hn => (hX n hn).2⟩

/-- Convexity of the quadratic potential. -/
theorem ou_hess_nonneg {d : ℕ} {ρ c : ℝ} (hρ : 0 < ρ) (x z : CutCur.Rd d) :
    0 ≤ fderiv ℝ (fderiv ℝ (fun x : CutCur.Rd d => ρ / 2 * ‖x‖ ^ 2 + c)) x z z := by
  have h := CutoffRigidity.hessian_quadratic_add_convex_lower (E := CutCur.Rd d)
    (W := fun _ => c) contDiff_const (convexOn_const c convex_univ) ρ x z
  exact le_trans (by positivity) h

theorem hess_nonneg_of_rate {d : ℕ} {V : CutCur.Rd d → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (x z : CutCur.Rd d) : 0 ≤ fderiv ℝ (fderiv ℝ V) x z z :=
  le_trans (by positivity) (hHess x z)

/-! ### Ornstein-Uhlenbeck -/

/-- **Fisher information and the heat kernel (OU case, manuscript Section 4.1), kernel form.** -/
theorem ou_fisher_information_K {d : ℕ} {ρ c : ℝ} (hρ : 0 < ρ)
    {Pt : ℝ≥0 → Kernel (CutCur.Rd d) (CutCur.Rd d)}
    (hL : CutCur.IsEuclideanLangevin (fun x : CutCur.Rd d => ρ / 2 * ‖x‖ ^ 2 + c) Pt)
    (x₀ : CutCur.Rd d) {t : ℝ} (ht : 0 < t) :
    let V := fun x : CutCur.Rd d => ρ / 2 * ‖x‖ ^ 2 + c
    let μt := Pt t.toNNReal x₀
    μt = multivariateGaussian (Real.exp (-ρ * t) • x₀)
        (((1 - Real.exp (-2 * ρ * t)) / ρ) • (1 : Matrix (Fin d) (Fin d) ℝ)) ∧
      (∃ u : CutCur.Rd d → ℝ, ContDiff ℝ ∞ u ∧
        μt = (CutCur.gibbs V).withDensity (fun x => ENNReal.ofReal (Real.exp (u x))) ∧
        (∀ᵐ x ∂CutCur.gibbs V, u x = Real.log (μt.rnDeriv (CutCur.gibbs V) x).toReal) ∧
        ∀ x, gradient u x = (ρ - ρ / (1 - Real.exp (-2 * ρ * t))) • x +
          (ρ * Real.exp (-ρ * t) / (1 - Real.exp (-2 * ρ * t))) • x₀) ∧
      CutCur.fisherInfo V μt = ENNReal.ofReal
        (ρ * d * Real.exp (-4 * ρ * t) / (1 - Real.exp (-2 * ρ * t)) +
          ρ ^ 2 * Real.exp (-2 * ρ * t) * ‖x₀‖ ^ 2) := by
  intro V μt
  obtain ⟨Ω, _, B, P, X, -, hLang, key⟩ :=
    CutCur.exists_isLangevin_of_isEuclideanLangevin hL (ou_hess_nonneg hρ)
  have h := ou_fisher_information_carrier (ρ := ρ) (c := c) hρ hLang x₀ ht
  simp only [key] at h
  exact h

/-- **OU started from the mean (after Corollary 1.3), kernel form.** -/
theorem ou_mean_start_cutoff_K {ρ : ℝ} (hρ : 0 < ρ)
    {c : ℕ → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (CutCur.Rd n) (CutCur.Rd n)} (hL : ∀ n, 0 < n →
      CutCur.IsEuclideanLangevin (fun x : CutCur.Rd n => ρ / 2 * ‖x‖ ^ 2 + c n) (Pt n)) :
    let V := fun n (x : CutCur.Rd n) => ρ / 2 * ‖x‖ ^ 2 + c n
    let prof := fun n => CutCur.worstK (Pt n) {∫ x, x ∂CutCur.gibbs (V n)}
      (CutCur.wasserstein2 · (CutCur.gibbs (V n)))
    CutCur.HasCutoff prof (fun n => Real.log n / (4 * CutCur.spectralGap (V n))) ⊤ 0 ∧
      ¬ CutCur.HasCutoff prof (fun n => CutCur.criticalTime n (CutCur.spectralGap (V n))) ⊤ 0 := by
  intro V prof
  obtain ⟨Ω, _, B, P, X, hLang, key⟩ :=
    exists_carriers_of_K (V := fun n (x : CutCur.Rd n) => ρ / 2 * ‖x‖ ^ 2 + c n) hL
      (fun n _ => ou_hess_nonneg hρ)
  have h := ou_mean_start_cutoff_carrier hρ hLang
  have hev := CutCur.eventually_worst_eq_worstK key
    (fun n => {∫ x, x ∂CutCur.gibbs (V n)}) (fun n => (CutCur.wasserstein2 · (CutCur.gibbs (V n))))
  exact ⟨(hasCutoff_congr_eventually_iff hev).1 h.1,
    fun hc => h.2 ((hasCutoff_congr_eventually_iff hev).2 hc)⟩

/-- **`p = ∞` fails for the Ornstein-Uhlenbeck process (after (1.25)), kernel form.** -/
theorem ou_lp_infty_fails_K {ρ : ℝ} (hρ : 0 < ρ)
    {c' : ℕ → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (CutCur.Rd n) (CutCur.Rd n)} (hL : ∀ n, 0 < n →
      CutCur.IsEuclideanLangevin (fun x : CutCur.Rd n => ρ / 2 * ‖x‖ ^ 2 + c' n) (Pt n))
    {c : ℝ} (hc : 0 < c) :
    let V := fun n (x : CutCur.Rd n) => ρ / 2 * ‖x‖ ^ 2 + c' n
    let prof := fun n => CutCur.worstK (Pt n) (CutCur.meanBall (V n) c)
      (CutCur.relLp · (CutCur.gibbs (V n)) ⊤)
    (∀ t : ℕ → ℝ, Tendsto (fun n => prof n (t n)) atTop (𝓝 ⊤)) ∧
      ¬ CutCur.HasCutoff prof (fun n => CutCur.criticalTime n (CutCur.spectralGap (V n))) ⊤ 0 := by
  intro V prof
  obtain ⟨Ω, _, B, P, X, hLang, key⟩ :=
    exists_carriers_of_K (V := fun n (x : CutCur.Rd n) => ρ / 2 * ‖x‖ ^ 2 + c' n) hL
      (fun n _ => ou_hess_nonneg hρ)
  have h := ou_lp_infty_fails_carrier hρ hLang hc
  have hev := CutCur.eventually_worst_eq_worstK key
    (fun n => CutCur.meanBall (V n) c) (fun n => (CutCur.relLp · (CutCur.gibbs (V n)) ⊤))
  refine ⟨fun t => ?_, fun hcut => h.2 ((hasCutoff_congr_eventually_iff hev).2 hcut)⟩
  refine (h.1 t).congr' ?_
  filter_upwards [hev] with n hn
  exact congrFun hn (t n)

/-! ### Langevin decay -/

/-- **Entropy decay and regularization, kernel form.** -/
theorem langevin_entropy_decay_K {d : ℕ} {V : CutCur.Rd d → ℝ}
    {Pt : ℝ≥0 → Kernel (CutCur.Rd d) (CutCur.Rd d)} (hL : CutCur.IsEuclideanLangevin V Pt)
    (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure (CutCur.Rd d)) [IsProbabilityMeasure ν] :
    let H := fun t : ℝ≥0 => InformationTheory.klDiv (ν.bind (Pt t)) (CutCur.gibbs V)
    let I := fun t : ℝ≥0 => CutCur.fisherInfo V (ν.bind (Pt t))
    let W := CutCur.wasserstein2 ν (CutCur.gibbs V) ^ 2
    (∀ s t : ℝ≥0, s ≤ t → H t ≤ ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - s))) * H s) ∧
      (∀ t : ℝ≥0, 0 < t →
        H t ≤ ENNReal.ofReal (ρ * Real.exp (-2 * ρ * t) / (1 - Real.exp (-2 * ρ * t))) * W ∧
        ENNReal.ofReal (ρ * Real.exp (-2 * ρ * t) / (1 - Real.exp (-2 * ρ * t))) * W ≤
          ENNReal.ofReal (1 / (2 * (t : ℝ))) * W) ∧
      (∀ t : ℝ≥0, 1 ≤ t →
        2 * H t ≤ ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - 1))) * W ∧
        ENNReal.ofReal (CutCur.tvDist (ν.bind (Pt t)) (CutCur.gibbs V) ^ 2) ≤
          ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - 1)) / 4) * W) ∧
      (∀ s t : ℝ≥0, s ≤ t → I t ≤ I s) ∧
      (∀ s t : ℝ≥0, 0 < t → I (s + t) ≤ H s / ENNReal.ofReal t) ∧
      (∀ t₀ t₁ : ℝ≥0, 1 ≤ t₀ → t₀ < t₁ →
        I t₁ ≤ ENNReal.ofReal (Real.exp (-2 * ρ * ((t₀ : ℝ) - 1)) / (2 * ((t₁ : ℝ) - t₀))) * W) := by
  intro H I W
  obtain ⟨Ω, _, B, P, X, -, hLang, key⟩ :=
    CutCur.exists_isLangevin_of_isEuclideanLangevin hL (hess_nonneg_of_rate hρ hHess)
  have hb : ∀ t : ℝ≥0, (fun x => P.map (X x t)) = ⇑(Pt t) := fun t => funext fun x => key t x
  have h := langevin_entropy_decay_carrier hLang hd hρ hHess ν
  simp only [hb] at h
  exact h

/-- **Fisher information decay, kernel form.** -/
theorem langevin_fisher_decay_K {d : ℕ} {V : CutCur.Rd d → ℝ}
    {Pt : ℝ≥0 → Kernel (CutCur.Rd d) (CutCur.Rd d)} (hL : CutCur.IsEuclideanLangevin V Pt)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure (CutCur.Rd d)) [IsProbabilityMeasure ν] :
    ∀ s t : ℝ≥0, s ≤ t →
      CutCur.fisherInfo V (ν.bind (Pt t)) ≤
        ENNReal.ofReal (Real.exp (-2 * ρ * ((t : ℝ) - s))) *
          CutCur.fisherInfo V (ν.bind (Pt s)) := by
  obtain ⟨Ω, _, B, P, X, -, hLang, key⟩ :=
    CutCur.exists_isLangevin_of_isEuclideanLangevin hL (hess_nonneg_of_rate hρ hHess)
  have hb : ∀ t : ℝ≥0, (fun x => P.map (X x t)) = ⇑(Pt t) := fun t => funext fun x => key t x
  have h := langevin_fisher_decay_carrier hLang hρ hHess ν
  simp only [hb] at h
  exact h

/-- **Upper Dini form of `∂ₜ I ≤ -2ρ I`, kernel form.** -/
theorem langevin_fisher_dini_K {d : ℕ} {V : CutCur.Rd d → ℝ}
    {Pt : ℝ≥0 → Kernel (CutCur.Rd d) (CutCur.Rd d)} (hL : CutCur.IsEuclideanLangevin V Pt)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (ν : Measure (CutCur.Rd d)) [IsProbabilityMeasure ν] (t : ℝ≥0)
    (ht : CutCur.fisherInfo V (ν.bind (Pt t)) ≠ ⊤) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ),
      ((CutCur.fisherInfo V (ν.bind (Pt (t + h.toNNReal)))).toReal -
          (CutCur.fisherInfo V (ν.bind (Pt t))).toReal) / h ≤
        -2 * ρ * (CutCur.fisherInfo V (ν.bind (Pt t))).toReal + ε := by
  obtain ⟨Ω, _, B, P, X, -, hLang, key⟩ :=
    CutCur.exists_isLangevin_of_isEuclideanLangevin hL (hess_nonneg_of_rate hρ hHess)
  have hb : ∀ t : ℝ≥0, (fun x => P.map (X x t)) = ⇑(Pt t) := fun t => funext fun x => key t x
  have ht' : CutCur.fisherInfo V (ν.bind fun x => P.map (X x t)) ≠ ⊤ := by
    rw [hb]; exact ht
  have h := langevin_fisher_dini_carrier hLang hρ hHess ν t ht' ε hε
  simp only [hb] at h
  exact h

/-! ### Normalization (generic kernels) -/

theorem worstK_timeChange {d : ℕ} (Pt : ℝ≥0 → Kernel (CutCur.Rd d) (CutCur.Rd d))
    (S : Set (CutCur.Rd d)) (δ : Measure (CutCur.Rd d) → ℝ≥0∞) {α : ℝ} (hα : 0 < α) (s : ℝ) :
    CutCur.worstK (fun u => Pt (α.toNNReal * u)) S δ s = CutCur.worstK Pt S δ (α * s) := by
  unfold CutCur.worstK
  rw [Real.toNNReal_mul hα.le]

theorem mixingTimeK_timeChange {d : ℕ} (Pt : ℝ≥0 → Kernel (CutCur.Rd d) (CutCur.Rd d))
    (μ : Measure (CutCur.Rd d)) (S : Set (CutCur.Rd d)) (η : ℝ) {α : ℝ} (hα : 0 < α) :
    CutCur.mixingTimeK (fun u => Pt (α.toNNReal * u)) μ S η =
      CutCur.mixingTimeK Pt μ S η / ENNReal.ofReal α := by
  have hne : α.toNNReal ≠ 0 := by simpa using hα
  have hcoe : ENNReal.ofReal α = (α.toNNReal : ℝ≥0∞) := rfl
  rw [hcoe]
  have hne' : (α.toNNReal : ℝ≥0∞) ≠ 0 := by exact_mod_cast hne
  rw [ENNReal.eq_div_iff hne' ENNReal.coe_ne_top]
  unfold CutCur.mixingTimeK
  simp only [ENNReal.mul_iInf_of_ne hne' ENNReal.coe_ne_top]
  have h2 := (Equiv.mulLeft₀ α.toNNReal hne).iInf_comp
    (g := fun u : ℝ≥0 => ⨅ (_ : CutCur.worstK Pt S
      (fun ν => ENNReal.ofReal (CutCur.tvDist ν μ)) u ≤ ENNReal.ofReal η), (u : ℝ≥0∞))
  rw [← h2]
  refine iInf_congr fun t => ?_
  have hw : CutCur.worstK (fun u => Pt (α.toNNReal * u)) S
      (fun ν => ENNReal.ofReal (CutCur.tvDist ν μ)) t =
      CutCur.worstK Pt S (fun ν => ENNReal.ofReal (CutCur.tvDist ν μ))
        ((α.toNNReal * t : ℝ≥0) : ℝ) := by
    rw [worstK_timeChange Pt S _ hα]
    congr 1
    rw [NNReal.coe_mul, Real.coe_toNNReal _ hα.le]
  simp only [Equiv.mulLeft₀_apply]
  rw [hw]
  refine iInf_congr fun h => ?_
  simp

/-- **Normalization (manuscript, Section "Normalization"), kernel form**: generic in the
transition kernels `Pt n`; the time-changed semigroup is `Pt n (α n · u)`. -/
theorem normalization_cutoff_K {Pt : ∀ n, ℝ≥0 → Kernel (CutCur.Rd n) (CutCur.Rd n)}
    {S : ∀ n, Set (CutCur.Rd n)} {α : ℕ → ℝ} (hα : ∀ n, 0 < α n) :
    let Ptα := fun n (u : ℝ≥0) => Pt n ((α n).toNNReal * u)
    (∀ (δ : ∀ n, Measure (CutCur.Rd n) → ℝ≥0∞) (t : ℕ → ℝ) (b a : ℝ≥0∞),
      CutCur.HasCutoff (fun n => CutCur.worstK (Pt n) (S n) (δ n)) t b a ↔
        CutCur.HasCutoff (fun n => CutCur.worstK (Ptα n) (S n) (δ n))
          (fun n => t n / α n) b a) ∧
    (∀ (μ : ∀ n, Measure (CutCur.Rd n)) (η : ℝ) (n : ℕ),
      CutCur.mixingTimeK (Ptα n) (μ n) (S n) η =
        CutCur.mixingTimeK (Pt n) (μ n) (S n) η / ENNReal.ofReal (α n)) ∧
    (∀ (μ : ∀ n, Measure (CutCur.Rd n)) (η : ℝ) (κ : ℕ → ℝ),
      Tendsto (fun n => α n * κ n * (CutCur.mixingTimeK (Ptα n) (μ n) (S n) η).toReal)
          atTop atTop ↔
        Tendsto (fun n => κ n * (CutCur.mixingTimeK (Pt n) (μ n) (S n) η).toReal)
          atTop atTop) := by
  intro Ptα
  refine ⟨fun δ t b a => ?_, fun μ η n => mixingTimeK_timeChange _ _ _ _ (hα n), fun μ η κ => ?_⟩
  · have h := hasCutoff_timeChange (profile := fun n => CutCur.worstK (Pt n) (S n) (δ n))
      (t := t) hα (b := b) (a := a)
    rw [h]
    have : ∀ n, CutCur.worstK (Ptα n) (S n) (δ n) =
        fun s => CutCur.worstK (Pt n) (S n) (δ n) (α n * s) := fun n =>
      funext fun s => worstK_timeChange _ _ _ (hα n) s
    simp only [this]
  · have : ∀ n, α n * κ n * (CutCur.mixingTimeK (Ptα n) (μ n) (S n) η).toReal =
        κ n * (CutCur.mixingTimeK (Pt n) (μ n) (S n) η).toReal := by
      intro n
      rw [mixingTimeK_timeChange _ _ _ _ (hα n), ENNReal.toReal_div,
        ENNReal.toReal_ofReal (hα n).le]
      have := (hα n).ne'
      field_simp
    simp only [this]

/-! ### Temperature -/

/-- **Temperature, cutoff (Section "Temperature"), kernel form**: the critical time is free of
`σ`. The `σ`-diffusions are given by their transition kernels (`IsSigmaLangevin`). -/
theorem temperature_cutoff_K {V : ∀ n, CutCur.Rd n → ℝ} {σ : ℝ} (hσ : 0 < σ) {ρ : ℕ → ℝ}
    {Pt : ∀ n, ℝ≥0 → Kernel (CutCur.Rd n) (CutCur.Rd n)}
    (hY : ∀ n, 0 < n → CutCur.IsSigmaLangevin (V n) σ (Pt n))
    (hρ : ∀ n, 0 < n → 0 < ρ n)
    (hHess : ∀ n, 0 < n → ∀ x z : CutCur.Rd n,
      ρ n * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (V n)) x z z)
    (hgap : ∀ n, 0 < n → ρ n = σ ^ 2 * CutCur.spectralGap (fun x => V n x / σ ^ 2))
    (hliminf : 0 < liminf (fun n => ENNReal.ofReal (ρ n)) atTop)
    {c : ℝ} (hc : 0 < c) :
    let t := fun n => CutCur.criticalTime n (ρ n)
    let S := fun n => CutCur.meanBall (fun x => V n x / σ ^ 2) c
    CutCur.HasCutoff (fun n => CutCur.worstK (Pt n) (S n)
      (CutCur.wasserstein2 · (CutCur.gibbs fun x => V n x / σ ^ 2))) t ⊤ 0 ∧
    ((ρ =o[atTop] (fun n : ℕ => Real.log n)) →
      CutCur.HasCutoff (fun n => CutCur.worstK (Pt n) (S n)
        (CutCur.fisherInfo fun x => V n x / σ ^ 2)) t ⊤ 0 ∧
      CutCur.HasCutoff (fun n => CutCur.worstK (Pt n) (S n)
        (InformationTheory.klDiv · (CutCur.gibbs fun x => V n x / σ ^ 2))) t ⊤ 0 ∧
      CutCur.HasCutoff (fun n => CutCur.worstK (Pt n) (S n)
        (fun ν => .ofReal (CutCur.tvDist ν (CutCur.gibbs fun x => V n x / σ ^ 2)))) t 1 0) := by
  classical
  intro t S
  set W : ∀ n, CutCur.Rd n → ℝ := fun n x => V n x / σ ^ 2 with hW
  set Q : ∀ n, ℝ≥0 → Kernel (CutCur.Rd n) (CutCur.Rd n) :=
    fun n u => Pt n (((σ ^ 2)⁻¹).toNNReal * u) with hQ
  have hs2 : 0 < σ ^ 2 := by positivity
  have hgap' : ∀ n, 0 < n → CutCur.spectralGap (W n) = ρ n / σ ^ 2 := fun n hn => by
    rw [hgap n hn]; field_simp; rfl
  have hK : CutCur.IsRigidSequenceK W Q := by
    refine ⟨fun n hn => ⟨CutCur.isEuclideanLangevin_of_sigma hσ (hY n hn), ?_, ?_⟩, ?_⟩
    · rw [hgap' n hn]; exact div_pos (hρ n hn) hs2
    · rw [hgap' n hn]
      intro x z
      have hV2 : ContDiff ℝ 2 (V n) := (hY n hn).1.of_le (by norm_cast)
      have h1 := hessian_div_const hV2 (σ ^ 2) x z
      simp only [hW]
      rw [h1, div_mul_eq_mul_div, ← inv_mul_eq_div]
      exact mul_le_mul_of_nonneg_left (hHess n hn x z) (inv_nonneg.mpr hs2.le)
    · have h1 : (fun n => ENNReal.ofReal (CutCur.spectralGap (W n))) =ᶠ[atTop]
          fun n => ENNReal.ofReal ((σ ^ 2)⁻¹) * ENNReal.ofReal (ρ n) := by
        filter_upwards [eventually_gt_atTop 0] with n hn
        rw [hW]; simp only
        rw [hgap' n hn, ← ENNReal.ofReal_mul (by positivity), div_eq_inv_mul]
      rw [liminf_congr h1, ENNReal.liminf_const_mul_of_ne_zero_of_ne_top
        (by simpa using hσ.ne') ENNReal.ofReal_ne_top]
      exact ENNReal.mul_pos (by simpa using hσ.ne') hliminf.ne'
  obtain ⟨Ω, _, B, P, X, hP, hrig, key⟩ := CutCur.exists_isRigidSequence_of_K hK
  have hα : ∀ n, 0 < (fun _ : ℕ => (σ ^ 2)⁻¹) n := fun n => by positivity
  have hnorm := fun δ t' b a => (normalization_cutoff_K (Pt := Pt)
    (S := fun n => CutCur.meanBall (W n) c) hα).1 δ t' b a
  have ht : (fun n => CutCur.criticalTime n (ρ n) / (σ ^ 2)⁻¹) =
      fun n => CutCur.criticalTime n (CutCur.spectralGap (W n)) := by
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [CutCur.criticalTime]
    · rw [hgap' n hn]
      have := (hρ n hn).ne'
      unfold CutCur.criticalTime
      field_simp
  -- transfer the carrier-level cutoff to the kernels `Q`
  have hcongr : ∀ δ : ∀ n, Measure (CutCur.Rd n) → ℝ≥0∞, ∀ (t' : ℕ → ℝ) (b a : ℝ≥0∞),
      CutCur.HasCutoff (fun n => CutCur.worst (P n) (X n) (CutCur.meanBall (W n) c) (δ n)) t' b a →
      CutCur.HasCutoff (fun n => CutCur.worstK (Q n) (CutCur.meanBall (W n) c) (δ n)) t' b a :=
    fun δ t' b a h => (hasCutoff_congr_eventually_iff
      (CutCur.eventually_worst_eq_worstK key (fun n => CutCur.meanBall (W n) c) δ)).1 h
  have hfin : ∀ δ : ∀ n, Measure (CutCur.Rd n) → ℝ≥0∞, ∀ (b a : ℝ≥0∞),
      CutCur.HasCutoff (fun n => CutCur.worstK (Q n) (CutCur.meanBall (W n) c) (δ n))
        (fun n => CutCur.criticalTime n (CutCur.spectralGap (W n))) b a →
      CutCur.HasCutoff (fun n => CutCur.worstK (Pt n) (CutCur.meanBall (W n) c) (δ n)) t b a := by
    intro δ b a h
    rw [hnorm δ t b a, ht]
    exact h
  refine ⟨?_, fun hsmall => ?_⟩
  · exact hfin (fun n ν => CutCur.wasserstein2 ν (CutCur.gibbs (W n))) ⊤ 0
      (hcongr _ _ _ _ (Paper.wasserstein_cutoff_carrier hrig hc))
  · have hsmall' : (fun n => CutCur.spectralGap (W n)) =o[atTop] (fun n : ℕ => Real.log n) := by
      have h1 : (fun n => CutCur.spectralGap (W n)) =ᶠ[atTop] fun n => (σ ^ 2)⁻¹ * ρ n := by
        filter_upwards [eventually_gt_atTop 0] with n hn
        rw [hgap' n hn, div_eq_inv_mul]
      exact (hsmall.const_mul_left _).congr' h1.symm (EventuallyEq.refl _ _)
    have hZi := Paper.information_cutoff_carrier hrig hsmall' hc
    exact ⟨hfin (fun n => CutCur.fisherInfo (W n)) ⊤ 0 (hcongr _ _ _ _ hZi.1),
      hfin (fun n ν => InformationTheory.klDiv ν (CutCur.gibbs (W n))) ⊤ 0
        (hcongr _ _ _ _ hZi.2.1),
      hfin (fun n ν => .ofReal (CutCur.tvDist ν (CutCur.gibbs (W n)))) 1 0
        (hcongr _ _ _ _ hZi.2.2)⟩

-- Names of the Challenge theorems (kernel statements; the Brownian versions are `*_carrier`).
alias ou_fisher_information := ou_fisher_information_K
alias ou_mean_start_cutoff := ou_mean_start_cutoff_K
alias ou_lp_infty_fails := ou_lp_infty_fails_K
alias langevin_entropy_decay := langevin_entropy_decay_K
alias langevin_fisher_decay := langevin_fisher_decay_K
alias langevin_fisher_dini := langevin_fisher_dini_K
alias normalization_cutoff := normalization_cutoff_K
alias temperature_cutoff := temperature_cutoff_K

end CutoffRigidity.Paper
