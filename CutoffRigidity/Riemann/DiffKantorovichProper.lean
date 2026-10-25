module

public import CutoffRigidity.Riemann.DiffKantorovichProper2
public import CutoffRigidity.Riemann.WeightedProper

/-! # Kantorovich budget duality on a proper metric space (non-compact)

`WS-KUW-A` of `riemann-status/DIFFUSION_PLAN.md`.  If `μ, ν` are probability measures on a proper
metric space `X` and every pair of bounded Lipschitz functions with `f x + g y ≤ dist x y ^ 2`
satisfies `∫ f dμ + ∫ g dν ≤ K`, then `cost2 μ ν ≤ ofReal K`, i.e. `W₂(μ,ν)² ≤ K`.  No moment
assumption on `μ, ν` is needed.

Proof: truncate the cost to `cR R = (min d R)²` (bounded, Lipschitz), restrict to the compact balls
`closedBall x₀ r` sending the outside mass to the base point (error `R² · tail → 0`), use the
compact strong duality (`exists_trunc_coupling`), then let `r → ∞` (Prokhorov, Portmanteau) and
`R → ∞` (monotone convergence).
-/

@[expose] public section

open MeasureTheory Filter Set Metric
open Bundle
open scoped Topology ENNReal NNReal BoundedContinuousFunction Manifold ContDiff

namespace CutoffRigidity.Riemann

section Main

variable {X : Type*} [MetricSpace X] [ProperSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

/-- Tails of a finite measure on a proper space, along balls of arbitrarily large radius. -/
theorem exists_tail_closedBall (μ : Measure X) [IsFiniteMeasure μ] (x₀ : X) {ε : ℝ} (hε : 0 < ε)
    (r₀ : ℝ) : ∃ r ≥ r₀, μ.real (closedBall x₀ r)ᶜ ≤ ε := by
  have ht : IsTightMeasureSet {μ} := isTightMeasureSet_singleton
  obtain ⟨K, hK, hμ⟩ := (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp ht)
    (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  obtain ⟨r₁, hr₁⟩ := hK.isBounded.subset_closedBall x₀
  refine ⟨max r₁ r₀, le_max_right _ _, ?_⟩
  have hsub : (closedBall x₀ (max r₁ r₀))ᶜ ⊆ Kᶜ := by
    intro y hy hyK
    exact hy (closedBall_subset_closedBall (le_max_left _ _) (hr₁ hyK))
  have := (measure_mono hsub).trans (hμ μ rfl)
  exact ENNReal.toReal_le_of_le_ofReal hε.le this

/-- Tail control for the truncated cost at level `R = m + 1`, with radius at least `m`. -/
theorem exists_radius (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (x₀ : X) (m : ℕ) : ∃ r : ℝ, (m : ℝ) ≤ r ∧
      ((m : ℝ) + 1) ^ 2 * (μ.real (closedBall x₀ r)ᶜ + ν.real (closedBall x₀ r)ᶜ) ≤
        1 / ((m : ℝ) + 1) := by
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hε : 0 < 1 / (2 * ((m : ℝ) + 1) ^ 3) := by positivity
  obtain ⟨r₁, hr₁, h₁⟩ := exists_tail_closedBall μ x₀ hε (m : ℝ)
  obtain ⟨r₂, hr₂, h₂⟩ := exists_tail_closedBall ν x₀ hε r₁
  refine ⟨r₂, hr₁.trans hr₂, ?_⟩
  have h₁' : μ.real (closedBall x₀ r₂)ᶜ ≤ 1 / (2 * ((m : ℝ) + 1) ^ 3) := by
    refine le_trans ?_ h₁
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
    exact compl_subset_compl.mpr (closedBall_subset_closedBall hr₂)
  have : ((m : ℝ) + 1) ^ 2 * (1 / (2 * ((m : ℝ) + 1) ^ 3) + 1 / (2 * ((m : ℝ) + 1) ^ 3)) =
      1 / ((m : ℝ) + 1) := by field_simp; ring
  rw [← this]
  exact mul_le_mul_of_nonneg_left (add_le_add h₁' h₂) (by positivity)

theorem cR_mono {R R' : ℝ} (hR : 0 ≤ R) (h : R ≤ R') (x y : X) : cR R x y ≤ cR R' x y := by
  unfold cR
  exact pow_le_pow_left₀ (le_min dist_nonneg hR) (min_le_min_left _ h) 2

/-- Truncating at radius `r m → ∞` converges weakly. -/
theorem tendsto_of_map_truncTo (x₀ : X) (r : ℕ → ℝ) (hr : ∀ m : ℕ, (m : ℝ) ≤ r m)
    (ρn : ℕ → ProbabilityMeasure X) (ρ : ProbabilityMeasure X)
    (h : ∀ m, (ρn m : Measure X) = (ρ : Measure X).map (truncTo (closedBall x₀ (r m)) x₀)) :
    Tendsto ρn atTop (𝓝 ρ) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  have hmeas : ∀ m, Measurable (truncTo (closedBall x₀ (r m)) x₀) := fun m =>
    measurable_truncTo isClosed_closedBall.measurableSet x₀
  have he : ∀ m, ∫ x, f x ∂(ρn m : Measure X) =
      ∫ x, f (truncTo (closedBall x₀ (r m)) x₀ x) ∂(ρ : Measure X) := fun m => by
    rw [h m]
    exact integral_map (hmeas m).aemeasurable f.continuous.aestronglyMeasurable
  simp_rw [he]
  refine tendsto_integral_of_dominated_convergence (fun _ => ‖f‖) (fun m => ?_)
    (integrable_const _) (fun m => Eventually.of_forall fun x => f.norm_coe_le_norm _) ?_
  · exact (f.continuous.measurable.comp (hmeas m)).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    have hev : ∀ᶠ m : ℕ in atTop, x ∈ closedBall x₀ (r m) := by
      have : ∀ᶠ m : ℕ in atTop, dist x x₀ ≤ (m : ℝ) :=
        tendsto_natCast_atTop_atTop.eventually_ge_atTop _
      filter_upwards [this] with m hm
      exact mem_closedBall.mpr ((hm).trans (hr m))
    exact tendsto_const_nhds.congr' (hev.mono fun m hm => by beta_reduce; rw [truncTo_of_mem hm])

set_option maxHeartbeats 1600000 in
/-- **Kantorovich budget duality on a proper metric space.** -/
theorem cost2_le_of_lipschitz_dual_budget (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (K : ℝ)
    (hDual : ∀ (f g : X →ᵇ ℝ) (L J : ℝ≥0), LipschitzWith L f → LipschitzWith J g →
      (∀ x y, f x + g y ≤ dist x y ^ 2) → ∫ x, f x ∂μ + ∫ y, g y ∂ν ≤ K) :
    cost2 μ ν ≤ ENNReal.ofReal K := by
  obtain ⟨x₀⟩ : Nonempty X := μ.nonempty_of_neZero
  choose r hr1 hr2 using exists_radius μ ν x₀
  have hr0 : ∀ m : ℕ, 0 ≤ r m := fun m => (Nat.cast_nonneg m).trans (hr1 m)
  have hcouple := fun m : ℕ => exists_trunc_coupling ((m : ℝ) + 1) (by positivity)
    (closedBall x₀ (r m)) (isCompact_closedBall _ _) x₀ (mem_closedBall_self (hr0 m)) μ ν K hDual
  choose pc hpp hp1 hp2 hpc using hcouple
  let πn : ℕ → ProbabilityMeasure (X × X) := fun m => ⟨pc m, hpp m⟩
  let μP : ProbabilityMeasure X := ⟨μ, inferInstance⟩
  let νP : ProbabilityMeasure X := ⟨ν, inferInstance⟩
  have hF : Tendsto (fun m => (πn m).map Prod.fst) atTop (𝓝 μP) :=
    tendsto_of_map_truncTo x₀ r hr1 _ μP fun m => hp1 m
  have hS : Tendsto (fun m => (πn m).map Prod.snd) atTop (𝓝 νP) :=
    tendsto_of_map_truncTo x₀ r hr1 _ νP fun m => hp2 m
  obtain ⟨q, φ, hφ, hq1, hq2, hlim⟩ := exists_weak_limit_coupling πn μP νP hF hS
  have hq1' : (q : Measure (X × X)).map Prod.fst = μ := congrArg (fun p : ProbabilityMeasure X => (p : Measure X)) hq1
  have hq2' : (q : Measure (X × X)).map Prod.snd = ν := congrArg (fun p : ProbabilityMeasure X => (p : Measure X)) hq2
  refine (cost2_le_cost (q : Measure (X × X)) ⟨hq1', hq2'⟩).trans ?_
  -- truncated costs
  have hbound : ∀ m₀ : ℕ, ∫⁻ z, ENNReal.ofReal (cR ((m₀ : ℝ) + 1) z.1 z.2) ∂(q : Measure (X × X)) ≤
      ENNReal.ofReal K := by
    intro m₀
    have hl := lintegral_le_liminf_of_tendsto hlim (h := fun z : X × X => cR ((m₀ : ℝ) + 1) z.1 z.2)
      (continuous_cR _) (fun z => cR_nonneg _ _ _)
    refine hl.trans ?_
    have hbn : ∀ᶠ n in atTop, ∫⁻ z, ENNReal.ofReal (cR ((m₀ : ℝ) + 1) z.1 z.2)
        ∂(πn (φ n) : Measure (X × X)) ≤ ENNReal.ofReal (K + 1 / ((φ n : ℝ) + 1)) := by
      filter_upwards [eventually_ge_atTop m₀] with n hn
      have hm0 : m₀ ≤ φ n := hn.trans (hφ.id_le n)
      have h1 : ∫⁻ z, ENNReal.ofReal (cR ((m₀ : ℝ) + 1) z.1 z.2) ∂(πn (φ n) : Measure (X × X)) ≤
          ∫⁻ z, ENNReal.ofReal (cR ((φ n : ℝ) + 1) z.1 z.2) ∂(pc (φ n)) :=
        lintegral_mono fun z => ENNReal.ofReal_le_ofReal
          (cR_mono (by positivity) (by have : (m₀ : ℝ) ≤ φ n := by exact_mod_cast hm0
                                       linarith) _ _)
      refine h1.trans ((hpc (φ n)).trans (ENNReal.ofReal_le_ofReal ?_))
      have := hr2 (φ n)
      linarith
    have htend : Tendsto (fun n => ENNReal.ofReal (K + 1 / ((φ n : ℝ) + 1))) atTop
        (𝓝 (ENNReal.ofReal K)) := by
      have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h1 := (h0.comp hφ.tendsto_atTop)
      have h2 : Tendsto (fun n => K + 1 / ((φ n : ℝ) + 1)) atTop (𝓝 (K + 0)) :=
        tendsto_const_nhds.add h1
      rw [add_zero] at h2
      exact (ENNReal.continuous_ofReal.tendsto K).comp h2
    calc _ ≤ _ := liminf_le_liminf hbn
      _ = ENNReal.ofReal K := htend.liminf_eq
  have hmeas : ∀ m : ℕ, Measurable fun z : X × X => ENNReal.ofReal (cR ((m : ℝ) + 1) z.1 z.2) :=
    fun m => ENNReal.measurable_ofReal.comp (continuous_cR _).measurable
  have hmono : Monotone fun (m : ℕ) (z : X × X) => ENNReal.ofReal (cR ((m : ℝ) + 1) z.1 z.2) := by
    intro m m' hmm z
    refine ENNReal.ofReal_le_ofReal (cR_mono (by positivity) ?_ _ _)
    have : (m : ℝ) ≤ m' := by exact_mod_cast hmm
    linarith
  have hsup : ∀ z : X × X, ⨆ m : ℕ, ENNReal.ofReal (cR ((m : ℝ) + 1) z.1 z.2) =
      edist z.1 z.2 ^ 2 := by
    intro z
    rw [edist_dist, ← ENNReal.ofReal_pow dist_nonneg]
    refine le_antisymm (iSup_le fun m => ENNReal.ofReal_le_ofReal
      (cR_le_sq _ (by positivity) _ _)) ?_
    refine le_trans (le_of_eq ?_) (le_iSup _ ⌈dist z.1 z.2⌉₊)
    congr 1
    have h1 : dist z.1 z.2 ≤ (⌈dist z.1 z.2⌉₊ : ℝ) + 1 := (Nat.le_ceil _).trans (by linarith)
    simp [cR, min_eq_left h1]
  calc ∫⁻ z, edist z.1 z.2 ^ 2 ∂(q : Measure (X × X))
      = ∫⁻ z, ⨆ m : ℕ, ENNReal.ofReal (cR ((m : ℝ) + 1) z.1 z.2) ∂(q : Measure (X × X)) := by
        simp_rw [hsup]
    _ = ⨆ m : ℕ, ∫⁻ z, ENNReal.ofReal (cR ((m : ℝ) + 1) z.1 z.2) ∂(q : Measure (X × X)) :=
        lintegral_iSup hmeas hmono
    _ ≤ ENNReal.ofReal K := iSup_le hbound

end Main

section Manifold

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M]

include F

set_option linter.unusedSectionVars false in
/-- **Kantorovich budget duality on a complete connected Riemannian manifold**, stated with
`edist` and the Challenge's `wasserstein2`. -/
theorem wasserstein2_sq_le_of_dual_budget_manifold (μ ν : Measure M) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (K : ℝ)
    (hDual : ∀ (f g : M →ᵇ ℝ) (L J : ℝ≥0), LipschitzWith L f → LipschitzWith J g →
      (∀ x y, f x + g y ≤ (edist x y).toReal ^ 2) → ∫ x, f x ∂μ + ∫ y, g y ∂ν ≤ K) :
    CutCur.wasserstein2 μ ν ^ 2 ≤ ENNReal.ofReal K := by
  letI : MetricSpace M := CutCur.riemannianMetricSpace F
  haveI : ProperSpace M := CutCur.properSpace_of_complete_riemannian (F := F) (M := M)
  rw [wasserstein2_sq_eq_cost2]
  exact cost2_le_of_lipschitz_dual_budget μ ν K fun f g L J hf hg hfg =>
    hDual f g L J hf hg fun x y => by simpa [dist_edist] using hfg x y

end Manifold

end CutoffRigidity.Riemann
