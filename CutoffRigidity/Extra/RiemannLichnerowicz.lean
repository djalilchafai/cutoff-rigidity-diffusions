module

public import CutoffRigidity.Riemann.DiffLSI
public import CutoffRigidity.Riemann.DiffKuwGlue
public import CutoffRigidity.Riemann.DiffGapManifold

/-! # Lichnerowicz / Bakry-Emery on a weighted Riemannian manifold (manuscript lines ~619-663)

`CD(rho, infinity)` with `rho > 0` on a connected complete weighted Riemannian manifold with
probability measure `mu = e^{-V} vol` implies the Poincare inequality `rho Var f <= int Gamma f`
and hence `lambda_1 >= rho`, WITHOUT assuming the value of the spectral gap beforehand.

Proof (this file): for a test function `f` and `g_s = K_s f`, `d/ds int g_s^2 dmu = -2 int Gamma(g_s)`
and `int Gamma(g_s) <= e^{-2 rho s} int Gamma f`, so `Var f <= Var g_T + (1/rho) int Gamma f`;
ergodicity `Var g_T -> 0` follows from the Bakry-Emery gradient bound
`|g_T x - g_T y| <= e^{-rho T} Lip(f) d(x,y)` and `|g_T| <= sup |f|` by dominated convergence.
-/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set Topology
open scoped Manifold ContDiff ENNReal NNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section RLich

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M]

include F

/-- Mean value inequality on `M`: a smooth function with `‖∇U‖ ≤ ℓ` is `ℓ`-Lipschitz for the
Riemannian distance. -/
theorem abs_sub_le_of_mgrad_le {U : M → ℝ} (hU : MSmooth F U) {ℓ : ℝ}
    (hg : ∀ x, ‖mgrad F U x‖ ≤ ℓ) (a b : M) : |U a - U b| ≤ ℓ * dd a b := by
  have hℓ : 0 ≤ ℓ := (norm_nonneg _).trans (hg a)
  have key : ∀ a b : M, U a - U b ≤ ℓ * dd a b := by
    intro a b
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨γ, hγ, hγ0, hγ1, hlen⟩ := exists_curve F a b (ε := ε / (ℓ + 1)) (by positivity)
    have hv := continuous_speed F hγ
    set S : ℝ → ℝ := fun s => ∫ τ in (0:ℝ)..s, ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ τ 1‖ with hS
    have hSd : ∀ s, HasDerivAt S ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ s 1‖ s := fun s =>
      (hv.integral_hasStrictDerivAt 0 s).hasDerivAt
    set φ : ℝ → ℝ := fun s => U (γ s) - ℓ * S s with hφ
    have hφd : ∀ s, HasDerivAt φ (mvfderiv 𝓘(ℝ, F) U (γ s) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ s 1) -
        ℓ * ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ s 1‖) s := fun s =>
      (hasDerivAt_comp_curve F hγ hU s).sub ((hSd s).const_mul ℓ)
    have hanti : Antitone φ := by
      refine antitone_of_deriv_nonpos (fun s => (hφd s).differentiableAt) fun s => ?_
      rw [(hφd s).deriv, sub_nonpos]
      have h1 := abs_mvfderiv_le_norm_mgrad F U (γ s) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ s 1)
      have h2 := mul_le_mul_of_nonneg_right (hg (γ s))
        (norm_nonneg (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ s 1))
      nlinarith [le_abs_self (mvfderiv 𝓘(ℝ, F) U (γ s) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ s 1))]
    have h01 := hanti (zero_le_one : (0:ℝ) ≤ 1)
    simp only [hφ, hγ0, hγ1, hS, intervalIntegral.integral_same, mul_zero, sub_zero] at h01
    have : ℓ * (∫ τ in (0:ℝ)..1, ‖mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) γ τ 1‖) ≤ ℓ * (dd a b + ε / (ℓ + 1)) :=
      mul_le_mul_of_nonneg_left hlen hℓ
    have h2 : ℓ * (ε / (ℓ + 1)) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
    nlinarith
  rw [abs_le]
  exact ⟨by have := key b a; rw [dd_comm b a] at this; linarith, key a b⟩

theorem continuous_dd_conn (x : M) : Continuous (fun y : M => dd x y) :=
  (ENNReal.continuousOn_toReal).comp_continuous (continuous_const.edist continuous_id)
    (fun y => edist_ne_top_of_connected F x y)

variable {μ : Measure M} [IsProbabilityMeasure μ]

theorem cont_minsq {B c : ℝ} (x : M) :
    Continuous (fun y : M => (min (2 * B) (c * dd x y)) ^ 2) :=
  (continuous_const.min (continuous_const.mul (continuous_dd_conn F x))).pow 2

theorem bdd_minsq {B c : ℝ} (hB : 0 ≤ B) (hc : 0 ≤ c) (x y : M) :
    |(min (2 * B) (c * dd x y)) ^ 2| ≤ 4 * B ^ 2 := by
  have h0 : 0 ≤ min (2 * B) (c * dd x y) := le_min (by linarith) (mul_nonneg hc (dd_nonneg _ _))
  have h1 : min (2 * B) (c * dd x y) ≤ 2 * B := min_le_left _ _
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith

theorem continuous_inner_minsq {B c : ℝ} (hB : 0 ≤ B) (hc : 0 ≤ c) :
    Continuous (fun x : M => ∫ y, (min (2 * B) (c * dd x y)) ^ 2 ∂μ) := by
  refine continuous_of_dominated (bound := fun _ => 4 * B ^ 2) (fun x => ?_)
    (fun x => Eventually.of_forall fun y => ?_) (integrable_const _)
    (Eventually.of_forall fun y => ?_)
  · exact (cont_minsq F x).aestronglyMeasurable
  · simpa [Real.norm_eq_abs] using bdd_minsq F hB hc x y
  · have : Continuous (fun x : M => dd x y) := by
      simpa [dd_comm] using continuous_dd_conn F y
    exact (continuous_const.min (continuous_const.mul this)).pow 2

/-- Variance bound from a Lipschitz-type estimate. -/
theorem variance_le_of_lip {h : M → ℝ} (hc : Continuous h) {B c : ℝ} (hc0 : 0 ≤ c)
    (hB : ∀ x, |h x| ≤ B) (hl : ∀ x y, |h x - h y| ≤ c * dd x y) :
    variance h μ ≤ ∫ x, ∫ y, (min (2 * B) (c * dd x y)) ^ 2 ∂μ ∂μ := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (Classical.arbitrary M))
  have hmem : MemLp h 2 μ := MemLp.of_bound hc.aestronglyMeasurable B
    (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hB x)
  have hint : Integrable h μ := hmem.integrable (by norm_num)
  rw [variance_eq_integral hc.aestronglyMeasurable.aemeasurable]
  have hcontΨ := continuous_inner_minsq F (μ := μ) hB0 hc0
  have hΨbd : ∀ x, |∫ y, (min (2 * B) (c * dd x y)) ^ 2 ∂μ| ≤ 4 * B ^ 2 := fun x => by
    have := norm_integral_le_of_norm_le_const (μ := μ) (C := 4 * B ^ 2)
      (f := fun y => (min (2 * B) (c * dd x y)) ^ 2)
      (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using bdd_minsq F hB0 hc0 x y)
    simpa [Real.norm_eq_abs] using this
  have hΨint : Integrable (fun x => ∫ y, (min (2 * B) (c * dd x y)) ^ 2 ∂μ) μ :=
    Integrable.of_bound hcontΨ.aestronglyMeasurable (4 * B ^ 2)
      (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hΨbd x)
  have hm : |∫ y, h y ∂μ| ≤ B := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (C := B) (f := h)
      (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hB y)
    simpa [Real.norm_eq_abs] using this
  have hsqint : Integrable (fun x => (h x - ∫ y, h y ∂μ) ^ 2) μ :=
    Integrable.of_bound ((hc.sub continuous_const).pow 2).aestronglyMeasurable ((2 * B) ^ 2)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have h1 := hB x
        have h2 := abs_le.1 h1
        have h3 := abs_le.1 hm
        have : |h x - ∫ y, h y ∂μ| ≤ 2 * B := abs_le.2 ⟨by linarith, by linarith⟩
        calc _ = |h x - ∫ y, h y ∂μ| ^ 2 := (sq_abs _).symm
          _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) this 2)
  refine integral_mono hsqint hΨint fun x => ?_
  have hxm : h x - ∫ y, h y ∂μ = ∫ y, (h x - h y) ∂μ := by
    rw [integral_sub (integrable_const _) hint]; simp
  have hdiffmem : MemLp (fun y => h x - h y) 2 μ :=
    MemLp.of_bound (continuous_const.sub hc).aestronglyMeasurable (2 * B)
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]
        have h1 := abs_le.1 (hB x)
        have h2 := abs_le.1 (hB y)
        exact abs_le.2 ⟨by linarith, by linarith⟩)
  have hj := sq_integral_le_integral_sq hdiffmem
  rw [hxm]
  refine hj.trans (integral_mono hdiffmem.integrable_sq
    (Integrable.of_bound (cont_minsq F x).aestronglyMeasurable (4 * B ^ 2)
      (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using bdd_minsq F hB0 hc0 x y))
    fun y => ?_)
  have h1 : |h x - h y| ≤ 2 * B := by
    have h1 := abs_le.1 (hB x)
    have h2 := abs_le.1 (hB y)
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have h2 : |h x - h y| ≤ min (2 * B) (c * dd x y) := le_min h1 (hl x y)
  calc (h x - h y) ^ 2 = |h x - h y| ^ 2 := (sq_abs _).symm
    _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) h2 2

theorem tendsto_double_minsq {B : ℝ} (hB : 0 ≤ B) {c : ℕ → ℝ} (hc0 : ∀ n, 0 ≤ c n)
    (hc : Tendsto c atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ∫ y, (min (2 * B) (c n * dd x y)) ^ 2 ∂μ ∂μ) atTop (𝓝 0) := by
  have hpt : ∀ x y : M, Tendsto (fun n => (min (2 * B) (c n * dd x y)) ^ 2) atTop (𝓝 0) := by
    intro x y
    refine squeeze_zero (fun n => sq_nonneg _) (fun n => ?_)
      (show Tendsto (fun n => (c n * dd x y) ^ 2) atTop (𝓝 0) by
        simpa using (hc.mul_const (dd x y)).pow 2)
    have h0 : 0 ≤ min (2 * B) (c n * dd x y) :=
      le_min (by linarith) (mul_nonneg (hc0 n) (dd_nonneg _ _))
    exact pow_le_pow_left₀ h0 (min_le_right _ _) 2
  have hinner : ∀ x : M, Tendsto (fun n => ∫ y, (min (2 * B) (c n * dd x y)) ^ 2 ∂μ) atTop (𝓝 0) := by
    intro x
    have := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun n y => (min (2 * B) (c n * dd x y)) ^ 2) (f := fun _ => (0:ℝ))
      (fun _ => 4 * B ^ 2) (fun n => (cont_minsq F x).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using bdd_minsq F hB (hc0 n) x y)
      (Eventually.of_forall fun y => hpt x y)
    simpa using this
  have := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n x => ∫ y, (min (2 * B) (c n * dd x y)) ^ 2 ∂μ) (f := fun _ => (0:ℝ))
    (fun _ => 4 * B ^ 2)
    (fun n => (continuous_inner_minsq F (μ := μ) hB (hc0 n)).aestronglyMeasurable)
    (integrable_const _)
    (fun n => Eventually.of_forall fun x => by
      have := norm_integral_le_of_norm_le_const (μ := μ) (C := 4 * B ^ 2)
        (f := fun y => (min (2 * B) (c n * dd x y)) ^ 2)
        (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using bdd_minsq F hB (hc0 n) x y)
      simpa [Real.norm_eq_abs] using this)
    (Eventually.of_forall fun x => hinner x)
  simpa using this

/-- If `h_n` are uniformly bounded and `c_n`-Lipschitz with `c_n → 0`, their variances tend to `0`. -/
theorem tendsto_variance_zero {h : ℕ → M → ℝ} (hc : ∀ n, Continuous (h n)) {B : ℝ}
    {c : ℕ → ℝ} (hc0 : ∀ n, 0 ≤ c n) (hct : Tendsto c atTop (𝓝 0))
    (hB : ∀ n x, |h n x| ≤ B) (hl : ∀ n x y, |h n x - h n y| ≤ c n * dd x y) :
    Tendsto (fun n => variance (h n) μ) atTop (𝓝 0) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 (Classical.arbitrary M))
  exact squeeze_zero (fun n => variance_nonneg _ _)
    (fun n => variance_le_of_lip F (hc n) (hc0 n) (hB n) (hl n))
    (tendsto_double_minsq F hB0 hc0 hct)

section Semigroup

variable {V : M → ℝ} {μ : Measure M} [IsProbabilityMeasure μ] {Kk : ℝ≥0 → Kernel M M}
  (hK : KerCanonical F V μ Kk) (hV : MSmooth F V)
  (hIBP : WeightedIBP F μ V) (hReg : WeightedRegular F V) (hC : WeightedCutoffs F M)

/-- `Φ(s) = ∫ (K_s g)² dμ`. -/
noncomputable def sqFun (Kk : ℝ≥0 → Kernel M M) (μ : Measure M) (g : M → ℝ) (s : ℝ) : ℝ :=
  ∫ x, (semi Kk s.toNNReal g x) ^ 2 ∂μ

include hK in
theorem sqFun_bounds (g : testSub F M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℝ) x, |semi Kk s.toNNReal (g : M → ℝ) x| ≤ C ∧
      |mgenerator F V (semi Kk s.toNNReal (g : M → ℝ)) x| ≤ C := by
  obtain ⟨_, _, C, hC⟩ := hK.smoothing (g : M → ℝ) g.2.1 g.2.2 0
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 (Classical.arbitrary M)).1
  exact ⟨C, hC0, fun s x => hC _ x⟩

include hK in
theorem sqFun_continuous (g : testSub F M) : Continuous (sqFun Kk μ (g : M → ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := sqFun_bounds F hK g
  unfold sqFun
  refine continuous_of_dominated (bound := fun _ => C ^ 2) (fun s => ?_)
    (fun s => Eventually.of_forall fun x => ?_) (integrable_const _)
    (Eventually.of_forall fun x => ?_)
  · exact ((hK.smoothing (g : M → ℝ) g.2.1 g.2.2 s.toNNReal).1.continuous.pow 2).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc _ = |semi Kk s.toNNReal (g : M → ℝ) x| ^ 2 := (sq_abs _).symm
      _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hC s x).1 2
  · exact (semi_continuous_time F hK g x).pow 2

include hK hV hIBP hReg hC in
/-- `d/ds ∫ (K_s g)² = -2 ∫ Γ(K_s g)` for `s > 0`. -/
theorem sqFun_hasDerivAt (g : testSub F M) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (sqFun Kk μ (g : M → ℝ))
      (-2 * ∫ x, carre F (semi Kk t.toNNReal (g : M → ℝ)) (semi Kk t.toNNReal (g : M → ℝ)) x ∂μ) t := by
  obtain ⟨C, hC0, hCb⟩ := sqFun_bounds F hK g
  have hsm : ∀ s : ℝ, MSmooth F (semi Kk s.toNNReal (g : M → ℝ)) := fun s =>
    (hK.smoothing (g : M → ℝ) g.2.1 g.2.2 _).1
  have hgen : ∀ s : ℝ, mgenerator F V (semi Kk s.toNNReal (g : M → ℝ)) =
      semi Kk s.toNNReal (mgenerator F V (g : M → ℝ)) := fun s =>
    (hK.smoothing (g : M → ℝ) g.2.1 g.2.2 _).2.1
  have hLc : ∀ s : ℝ, Continuous (mgenerator F V (semi Kk s.toNNReal (g : M → ℝ))) := fun s =>
    (hReg.2.1 _ (hsm s)).continuous
  have hF_meas : ∀ s : ℝ, AEStronglyMeasurable (fun x => (semi Kk s.toNNReal (g : M → ℝ) x) ^ 2) μ :=
    fun s => ((hsm s).continuous.pow 2).aestronglyMeasurable
  have hdiff : ∀ x : M, ∀ s : ℝ, 0 < s → HasDerivAt (fun s : ℝ => (semi Kk s.toNNReal (g : M → ℝ) x) ^ 2)
      (2 * semi Kk s.toNNReal (g : M → ℝ) x *
        mgenerator F V (semi Kk s.toNNReal (g : M → ℝ)) x) s := fun x s hs => by
    have d := hasDerivAt_dynkin F hK.dynkin g.2.1 g.2.2 hV x hs
    have := d.pow 2
    refine this.congr_deriv ?_
    rw [hgen s]
    simp only [semi]
    push_cast
    ring
  have hI := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (s : ℝ) (x : M) => (semi Kk s.toNNReal (g : M → ℝ) x) ^ 2)
    (F' := fun (s : ℝ) (x : M) => 2 * semi Kk s.toNNReal (g : M → ℝ) x *
      mgenerator F V (semi Kk s.toNNReal (g : M → ℝ)) x) (μ := μ) (x₀ := t)
    (s := Ioo (t / 2) (2 * t)) (Ioo_mem_nhds (by linarith) (by linarith))
    (bound := fun _ => 2 * C * C)
    (Eventually.of_forall hF_meas)
    (Integrable.of_bound (hF_meas t) (C ^ 2) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      calc _ = |semi Kk t.toNNReal (g : M → ℝ) x| ^ 2 := (sq_abs _).symm
        _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hCb t x).1 2))
    (((continuous_const.mul (hsm t).continuous).mul (hLc t)).aestronglyMeasurable)
    (ae_of_all _ fun x s _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_two]
      have := mul_le_mul (hCb s x).1 (hCb s x).2 (abs_nonneg _) hC0
      nlinarith)
    (integrable_const _)
    (ae_of_all _ fun x s hs => hdiff x s (by linarith [hs.1]))
  refine hI.2.congr_deriv ?_
  set P : M → ℝ := semi Kk t.toNNReal (g : M → ℝ) with hP
  have hPs : MSmooth F P := hsm t
  have hInS : InS F V μ P := (inS_semi F hK hReg g t.toNNReal).1
  have hGP : Integrable (fun x => carre F P P x) μ := integrable_carre_of_InS F hIBP hReg hC hInS
  obtain ⟨_, hcross⟩ := integral_carre_cross F hIBP hReg hC hPs hInS.2.1 hGP hInS
  have : ∫ x, 2 * P x * mgenerator F V P x ∂μ = 2 * ∫ x, P x * mgenerator F V P x ∂μ := by
    rw [← integral_const_mul]; congr 1; ext x; ring
  simp only [← hgen] at *
  rw [show (fun x => 2 * semi Kk t.toNNReal (g : M → ℝ) x *
      mgenerator F V (semi Kk t.toNNReal (g : M → ℝ)) x) =
      fun x => 2 * P x * mgenerator F V P x from rfl, this]
  have : ∫ x, P x * mgenerator F V P x ∂μ = -∫ x, carre F P P x ∂μ := by
    rw [hcross]; ring
  rw [this]; ring

include hK hV hIBP hReg hC in
/-- Monotonicity step: `∫ g² ≤ ∫ (K_T g)² + (1/ρ) ∫ Γ g`. -/
theorem sqFun_zero_le {ρ : ℝ} (hρ : 0 < ρ)
    (hBE : ∀ (f : testSub F M) (t : ℝ≥0) (x : M), ‖mgrad F (semi Kk t (f : M → ℝ)) x‖ ≤
        Real.exp (-ρ * t) * ∫ y, ‖mgrad F (f : M → ℝ) y‖ ∂Kk t x)
    (g : testSub F M) (T : ℝ≥0) :
    sqFun Kk μ (g : M → ℝ) 0 ≤ sqFun Kk μ (g : M → ℝ) T +
      (∫ x, carre F (g : M → ℝ) (g : M → ℝ) x ∂μ) / ρ := by
  set C := ∫ x, carre F (g : M → ℝ) (g : M → ℝ) x ∂μ with hCdef
  have hC0 : 0 ≤ C := integral_nonneg fun x => carre_nonneg F _ x
  set c := C / ρ with hc
  have hc0 : 0 ≤ c := by positivity
  set ψ : ℝ → ℝ := fun s => sqFun Kk μ (g : M → ℝ) s + c * (1 - Real.exp (-2 * ρ * s)) with hψ
  have hcont : ContinuousOn ψ (Ici 0) :=
    ((sqFun_continuous F hK g).add (continuous_const.mul (continuous_const.sub (by fun_prop)))).continuousOn
  have hderiv : ∀ s ∈ interior (Ici (0:ℝ)), HasDerivAt ψ
      (-2 * (∫ x, carre F (semi Kk s.toNNReal (g : M → ℝ)) (semi Kk s.toNNReal (g : M → ℝ)) x ∂μ) +
        c * (0 - Real.exp (-2 * ρ * s) * (-2 * ρ))) s := by
    intro s hs
    rw [interior_Ici] at hs
    have hE := sqFun_hasDerivAt F hK hV hIBP hReg hC g hs
    have hd : HasDerivAt (fun s : ℝ => Real.exp (-2 * ρ * s)) (Real.exp (-2 * ρ * s) * (-2 * ρ)) s := by
      simpa using ((hasDerivAt_id s).const_mul (-2 * ρ)).exp
    exact hE.add (((hasDerivAt_const s (1:ℝ)).sub hd).const_mul c)
  have hmono : MonotoneOn ψ (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont
      (fun s hs => (hderiv s hs).differentiableAt.differentiableWithinAt) ?_
    intro s hs
    rw [(hderiv s hs).deriv]
    have hs' : 0 < s := by rwa [interior_Ici] at hs
    have h1 := grad_decay_int F hK hReg hBE g s.toNNReal
    rw [Real.coe_toNNReal _ hs'.le] at h1
    have : c * (0 - Real.exp (-2 * ρ * s) * (-2 * ρ)) = 2 * Real.exp (-2 * ρ * s) * C := by
      rw [hc]; field_simp; ring
    rw [this]
    linarith
  have h := hmono (show (0:ℝ) ∈ Ici 0 from le_refl _) (show (T:ℝ) ∈ Ici (0:ℝ) from T.2) T.2
  simp only [hψ, mul_zero, Real.exp_zero, sub_self, add_zero] at h
  have hT : sqFun Kk μ (g : M → ℝ) (T : ℝ) = sqFun Kk μ (g : M → ℝ) ((T : ℝ≥0) : ℝ) := rfl
  have : c * (1 - Real.exp (-2 * ρ * T)) ≤ c := by
    have := Real.exp_pos (-2 * ρ * T)
    nlinarith
  linarith

include hK hV hIBP hReg hC in
/-- **Poincaré inequality from the strong Bakry-Émery bound**, with no assumption on the gap. -/
theorem poincare_of_strong_BE {ρ : ℝ} (hρ : 0 < ρ)
    (hBE : ∀ (f : testSub F M) (t : ℝ≥0) (x : M), ‖mgrad F (semi Kk t (f : M → ℝ)) x‖ ≤
        Real.exp (-ρ * t) * ∫ y, ‖mgrad F (f : M → ℝ) y‖ ∂Kk t x) :
    ∀ f : M → ℝ, MSmooth F f → HasCompactSupport f →
      ρ * variance f μ ≤ ∫ x, carre F f f x ∂μ := by
  intro f hf hfc
  set g : testSub F M := ⟨f, hf, hfc⟩ with hg
  have hgf : (g : M → ℝ) = f := rfl
  obtain ⟨Bf, hBf⟩ := testSub_bounded F g
  obtain ⟨Lf, hLf⟩ := bdd_norm_mgrad F hReg g
  have hLf0 : 0 ≤ Lf := (abs_nonneg _).trans (hLf (Classical.arbitrary M))
  have hBf0 : 0 ≤ Bf := (abs_nonneg _).trans (hBf (Classical.arbitrary M))
  set G := ∫ x, carre F f f x ∂μ with hG
  have hfm : Measurable f := hf.continuous.measurable
  have hmean : ∀ n : ℕ, ∫ x, semi Kk (n : ℝ≥0) f x ∂μ = ∫ x, f x ∂μ := fun n =>
    integral_semi F hK hfm ⟨Bf, hBf⟩ n
  have hmemf : MemLp f 2 μ := MemLp.of_bound hf.continuous.aestronglyMeasurable Bf
    (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hBf x)
  set h : ℕ → M → ℝ := fun n => semi Kk (n : ℝ≥0) f with hh
  have hhs : ∀ n, MSmooth F (h n) := fun n => (hK.smoothing f hf hfc _).1
  have hhB : ∀ n x, |h n x| ≤ Bf := fun n x => semi_abs_le_lsi F hK hBf _ x
  have hhmem : ∀ n, MemLp (h n) 2 μ := fun n => MemLp.of_bound (hhs n).continuous.aestronglyMeasurable Bf
    (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hhB n x)
  have hhgrad : ∀ n x, ‖mgrad F (h n) x‖ ≤ Real.exp (-ρ * n) * Lf := fun n x => by
    refine (hBE g n x).trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
    haveI := hK.markov n
    haveI := (hK.markov n).isProbabilityMeasure x
    have := norm_integral_le_of_norm_le_const (μ := Kk n x) (C := Lf)
      (f := fun y => ‖mgrad F (g : M → ℝ) y‖)
      (Eventually.of_forall fun y => by simpa using hLf y)
    simpa using (le_abs_self _).trans (by simpa using this)
  have hlip : ∀ n x y, |h n x - h n y| ≤ Real.exp (-ρ * n) * Lf * dd x y := fun n x y =>
    abs_sub_le_of_mgrad_le F (hhs n) (hhgrad n) x y
  have hct : Tendsto (fun n : ℕ => Real.exp (-ρ * n) * Lf) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ρ * (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hρ
    have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
    simpa [Function.comp, neg_mul] using h2.mul_const Lf
  have hvar0 := tendsto_variance_zero F (μ := μ) (h := h) (fun n => (hhs n).continuous)
    (fun n => (mul_nonneg (Real.exp_pos _).le hLf0)) hct hhB hlip
  -- the inequality for each n
  have hbound : ∀ n : ℕ, ρ * variance f μ ≤ ρ * variance (h n) μ + G := fun n => by
    have h1 := sqFun_zero_le F hK hV hIBP hReg hC hρ hBE g n
    have e0 : sqFun Kk μ (g : M → ℝ) 0 = ∫ x, f x ^ 2 ∂μ := by
      unfold sqFun
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [Real.toNNReal_zero, semi_zero_of_canonical F hK g x]
      rfl
    have eT : sqFun Kk μ (g : M → ℝ) (n : ℝ≥0) = ∫ x, (h n x) ^ 2 ∂μ := by
      unfold sqFun
      simp [hh]
      rfl
    rw [e0, eT] at h1
    have v1 : variance f μ = (∫ x, f x ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 := by
      rw [variance_eq_sub hmemf]; simp
    have v2 : variance (h n) μ = (∫ x, (h n x) ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 := by
      rw [variance_eq_sub (hhmem n)]
      simp only [Pi.pow_apply, hh]
      rw [hmean n]
    have h2 : variance f μ ≤ variance (h n) μ + G / ρ := by rw [v1, v2]; linarith
    calc ρ * variance f μ ≤ ρ * (variance (h n) μ + G / ρ) := mul_le_mul_of_nonneg_left h2 hρ.le
      _ = ρ * variance (h n) μ + G := by field_simp
  have hlim : Tendsto (fun n : ℕ => ρ * variance (h n) μ + G) atTop (𝓝 (ρ * 0 + G)) :=
    (hvar0.const_mul ρ).add_const G
  rw [mul_zero, zero_add] at hlim
  exact ge_of_tendsto hlim (Eventually.of_forall hbound)

end Semigroup

section Final

variable {V : M → ℝ} {μ : Measure M} [IsProbabilityMeasure μ]

/-- A manifold modelled on a space of positive dimension has two distinct points. -/
theorem nontrivial_of_finrank_pos (hF : 0 < Module.finrank ℝ F) : Nontrivial M := by
  haveI : Nontrivial F := Module.finrank_pos_iff.1 hF
  haveI : PerfectSpace F := perfectSpace_of_module ℝ F
  obtain ⟨x₀⟩ : Nonempty M := inferInstance
  have hopen : IsOpen (chartAt F x₀).target := (chartAt F x₀).open_target
  have hp : chartAt F x₀ x₀ ∈ (chartAt F x₀).target := (chartAt F x₀).map_source (mem_chart_source F x₀)
  have hnb : Filter.NeBot (𝓝[≠] (chartAt F x₀ x₀)) := PerfectSpace.not_isolated _
  obtain ⟨q, hqne, hq⟩ := hnb.nonempty_of_mem (inter_mem_nhdsWithin {chartAt F x₀ x₀}ᶜ
    (hopen.mem_nhds hp))
  refine ⟨⟨(chartAt F x₀).symm q, x₀, fun h => ?_⟩⟩
  have := congrArg (chartAt F x₀) h
  rw [(chartAt F x₀).right_inv hq] at this
  exact hqne (by simpa using this)

/-- There is a smooth compactly supported function of positive variance. -/
theorem exists_pos_variance (hV : MSmooth F V) (hμ : IsWeightedVolume F μ V) (hF : 0 < Module.finrank ℝ F) :
    ∃ f : M → ℝ, MSmooth F f ∧ HasCompactSupport f ∧ 0 < variance f μ := by
  haveI := nontrivial_of_finrank_pos F (M := M) hF
  haveI := isOpenPosMeasure_of_isWeightedVolume F hV hμ
  obtain ⟨x₀, x₁, hne⟩ := exists_pair_ne M
  have hU : ({x₁}ᶜ : Set M) ∈ 𝓝 x₀ := isOpen_compl_singleton.mem_nhds hne
  obtain ⟨ζ, hζs, hζc, -, hζx, hζU⟩ := exists_bump_in F hU
  have hx₁ : ζ x₁ = 0 := by
    by_contra h; exact hζU x₁ h rfl
  refine ⟨ζ, hζs, hζc, ?_⟩
  have hmem : MemLp ζ 2 μ := by
    obtain ⟨C, hC⟩ := hζs.continuous.bounded_above_of_compact_support hζc
    exact MemLp.of_bound hζs.continuous.aestronglyMeasurable C (Eventually.of_forall hC)
  refine lt_of_le_of_ne (variance_nonneg _ _) fun h0 => ?_
  have := ae_eq_integral_of_variance_eq_zero hmem h0.symm
  have hc : Continuous ζ := hζs.continuous
  have heq := (hc.ae_eq_iff_eq μ continuous_const).1 this
  have h0 := congrFun heq x₀
  have h1 := congrFun heq x₁
  rw [hζx] at h0; rw [hx₁] at h1
  linarith

/-- **Poincaré inequality from `CD(ρ,∞)`** on test functions (Lichnerowicz / Bakry-Émery). -/
theorem poincare_of_CD (hV : MSmooth F V) (hμ : IsWeightedVolume F μ V) {ρ : ℝ} (hρ : 0 < ρ) (hCD : CD F ρ V) :
    ∀ f : M → ℝ, MSmooth F f → HasCompactSupport f →
      ρ * variance f μ ≤ ∫ x, carre F f f x ∂μ :=
  poincare_of_strong_BE F (kerCanonical_Kk F hV hμ) hV (CutCur.weightedIBP_of_isWeightedVolume F hV hμ)
    (CutCur.weightedRegular V hV) (CutCur.weightedCutoffs_of_complete F) hρ
    (beStrong_of_CD F hV hμ hρ hCD)

/-- **Lichnerowicz / Bakry-Émery**: `CD(ρ,∞)`, `ρ > 0` implies `λ₁ ≥ ρ`. -/
theorem mSpectralGap_ge_of_CD' (hV : MSmooth F V) (hμ : IsWeightedVolume F μ V) (hF : 0 < Module.finrank ℝ F) {ρ : ℝ} (hρ : 0 < ρ)
    (hCD : CD F ρ V) : ρ ≤ mSpectralGap F μ := by
  have hP := poincare_of_CD F hV hμ hρ hCD
  obtain ⟨f₀, hf₀, hf₀c, hf₀v⟩ := exists_pos_variance F hV hμ hF
  refine le_csInf ⟨_, f₀, hf₀, hf₀c, hf₀v, rfl⟩ ?_
  rintro r ⟨f, hf, hfc, hfv, rfl⟩
  rw [le_div_iff₀ hfv]
  have := hP f hf hfc
  have hcar : ∫ x, carre F f f x ∂μ = ∫ x, ‖mgrad F f x‖ ^ 2 ∂μ :=
    integral_congr_ae (Eventually.of_forall fun x => carre_self_eq F f x)
  rw [hcar] at this
  exact this

end Final

end RLich

end CutoffRigidity.Riemann.Diff

namespace CutoffRigidity.Paper

section Riemannian

open CutCur CutoffRigidity.Riemann CutoffRigidity.Riemann.Diff

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M]

/-- **Lichnerowicz / Bakry-Émery spectral gap bound** (manuscript lines 619-627): `CD(ρ,∞)` with
`ρ > 0` gives `λ₁ ≥ ρ`.  AMENDMENT: `0 < finrank ℝ F` is necessary (on a point manifold the Rayleigh
set is empty, `sInf ∅ = 0`, and every other hypothesis holds). -/
theorem mSpectralGap_ge_of_CD (hF : 0 < Module.finrank ℝ F) {V : M → ℝ}
    (hV : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ V)
    {μ : Measure M} [IsProbabilityMeasure μ] (hμ : IsWeightedVolume F μ V) {ρ : ℝ} (hρ : 0 < ρ)
    (hCD : CD F ρ V) : ρ ≤ mSpectralGap F μ :=
  mSpectralGap_ge_of_CD' F (V := V) hV hμ hF hρ hCD

end Riemannian

end CutoffRigidity.Paper

