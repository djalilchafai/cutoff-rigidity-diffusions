module

public import CutoffRigidity.Riemann.DiffSobolevRn7
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.InnerProductSpace.Dual

/-! # Bounded difference quotients give a weak derivative
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff

set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Diff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem tendsto_dq_neg {v : E} {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : E) :
    Filter.Tendsto (fun n : ℕ => dq v (-(1 / ((n : ℝ) + 1))) φ x) Filter.atTop
      (nhds (pd v φ x)) := by
  have hd := hφ.differentiable (by simp)
  have hg : HasDerivAt (fun t : ℝ => φ (x + t • v)) (pd v φ x) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
    have := (hd (x + (0:ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0:ℝ) h1
    exact this.congr_deriv (by simp [pd])
  have hs := hasDerivAt_iff_tendsto_slope_zero.1 hg
  have ht : Filter.Tendsto (fun n : ℕ => -(1 / ((n : ℝ) + 1))) Filter.atTop (nhdsWithin 0 {0}ᶜ) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Filter.Eventually.of_forall (fun n => ?_)⟩
    · have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
      simpa using this
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, neg_eq_zero]
      positivity
  refine (hs.comp ht).congr (fun n => ?_)
  simp [dq, Function.comp, div_eq_inv_mul]

theorem tendsto_integral_mul_dq {v : E} {f φ : E → ℝ} (hf : LocallyIntegrable f volume)
    (hφ : IsTest Set.univ φ) :
    Filter.Tendsto (fun n : ℕ => ∫ x, f x * dq v (-(1 / ((n : ℝ) + 1))) φ x) Filter.atTop
      (nhds (∫ x, f x * pd v φ x)) := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφ.2.1 hφ.1 (n := ∞) (by simp)
  set S := Metric.cthickening ‖v‖ (tsupport φ) with hSdef
  have hS : IsCompact S := hφ.2.1.isCompact.cthickening
  have hfS : IntegrableOn f S volume := hf.integrableOn_isCompact hS
  have hbd : Integrable (fun x => S.indicator (fun x => ((C : ℝ) * ‖v‖) * |f x|) x) volume := by
    rw [integrable_indicator_iff hS.measurableSet]
    exact (hfS.abs.const_mul _)
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun x => f x * dq v (-(1 / ((n : ℝ) + 1))) φ x) volume := by
    intro n
    refine hf.aestronglyMeasurable.mul ?_
    exact (isTest_dq hφ v _).1.continuous.aestronglyMeasurable
  refine tendsto_integral_of_dominated_convergence _ hmeas hbd (fun n => ?_) ?_
  · refine Filter.Eventually.of_forall (fun x => ?_)
    set h : ℝ := 1 / ((n : ℝ) + 1) with hh
    have hh0 : 0 < h := by positivity
    have hh1 : h ≤ 1 := by
      rw [hh, div_le_one (by positivity)]; have := n.cast_nonneg (α := ℝ); linarith
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, norm_mul, Real.norm_eq_abs]
      have : |dq v (-h) φ x| ≤ C * ‖v‖ := by
        unfold dq
        rw [abs_div, abs_neg, abs_of_pos hh0, div_le_iff₀ hh0]
        have := hC.dist_le_mul (x + (-h) • v) x
        rw [Real.dist_eq, dist_eq_norm] at this
        simp only [add_sub_cancel_left, norm_smul, norm_neg, Real.norm_eq_abs,
          abs_of_pos hh0] at this
        nlinarith [this]
      calc |f x| * |dq v (-h) φ x| ≤ |f x| * (C * ‖v‖) :=
            mul_le_mul_of_nonneg_left this (abs_nonneg _)
        _ = _ := by ring
    · rw [Set.indicator_of_notMem hx]
      have h1 : φ x = 0 := by
        by_contra hne
        exact hx (Metric.self_subset_cthickening _ (subset_tsupport _ hne))
      have h2 : φ (x + (-h) • v) = 0 := by
        by_contra hne
        apply hx
        apply Metric.mem_cthickening_of_dist_le x (x + (-h) • v) ‖v‖
        · exact subset_tsupport _ hne
        · rw [dist_eq_norm]
          simp only [sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hh0]
          exact mul_le_of_le_one_left (norm_nonneg _) hh1
      have : dq v (-h) φ x = 0 := by unfold dq; rw [h1, h2]; simp
      simp [this]
  · refine Filter.Eventually.of_forall (fun x => ?_)
    exact (tendsto_dq_neg hφ.1 x).const_mul (f x)

theorem Lp_inner_eq_integral (y z : Lp ℝ 2 (volume : Measure E)) :
    inner ℝ y z = ∫ x, y x * z x := by
  rw [L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [mul_comm]

theorem Lp_norm_sq_eq (y : Lp ℝ 2 (volume : Measure E)) : ‖y‖ ^ 2 = ∫ x, y x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, Lp_inner_eq_integral]
  congr 1; funext x; ring

theorem Lp_norm_eq_l2 (y : Lp ℝ 2 (volume : Measure E)) : ‖y‖ = l2 (fun x => y x) := by
  unfold l2
  have := Lp_norm_sq_eq y
  rw [← this, Real.sqrt_sq (norm_nonneg _)]

theorem norm_toLp_eq_l2 {g : E → ℝ} (hg : MemLp g 2 volume) : ‖hg.toLp g‖ = l2 g := by
  rw [Lp_norm_eq_l2]
  unfold l2
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp] with x hx
  simp [hx]

theorem inner_toLp_eq {g k : E → ℝ} (hg : MemLp g 2 volume) (hk : MemLp k 2 volume) :
    inner ℝ (hg.toLp g) (hk.toLp k) = ∫ x, g x * k x := by
  rw [Lp_inner_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp, hk.coeFn_toLp] with x h1 h2
  simp [h1, h2]

theorem exists_hasWDeriv_of_bdd_dq {v : E} {f : E → ℝ} (hf : MemLp f 2 volume) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ n : ℕ, l2 (dq v (1 / ((n : ℝ) + 1)) f) ≤ M) :
    ∃ w, MemLp w 2 volume ∧ HasWDeriv Set.univ v f w ∧ l2 w ≤ M := by
  have hdq : ∀ n : ℕ, MemLp (dq v (1 / ((n : ℝ) + 1)) f) 2 volume := fun n => memLp_dq hf
  let g : ℕ → (Lp ℝ 2 (volume : Measure E)) := fun n => (hdq n).toLp _
  have hgn : ∀ n, ‖g n‖ ≤ M := fun n => by
    simp only [g]; rw [norm_toLp_eq_l2]; exact hb n
  let u : ℕ → WeakDual ℝ (Lp ℝ 2 (volume : Measure E)) := fun n => StrongDual.toWeakDual (InnerProductSpace.toDual ℝ (Lp ℝ 2 (volume : Measure E)) (g n))
  have hu : ∀ n, u n ∈ (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ (Lp ℝ 2 (volume : Measure E))) M) := by
    intro n
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    show ‖InnerProductSpace.toDual ℝ (Lp ℝ 2 (volume : Measure E)) (g n)‖ ≤ M
    rw [LinearIsometryEquiv.norm_map]; exact hgn n
  have hB := WeakDual.isCompact_closedBall (𝕜 := ℝ) (E := (Lp ℝ 2 (volume : Measure E))) 0 M
  obtain ⟨φw, hφw, hcl⟩ := hB.exists_mapClusterPt (f := Filter.atTop) (u := u)
    (Filter.le_principal_iff.2 (Filter.mem_map.2 (Filter.Eventually.of_forall hu)))
  set Φ : StrongDual ℝ (Lp ℝ 2 (volume : Measure E)) := WeakDual.toStrongDual φw with hΦ
  have hΦn : ‖Φ‖ ≤ M := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hφw
  have hclu : ∀ y : (Lp ℝ 2 (volume : Measure E)), MapClusterPt (φw y) Filter.atTop (fun n => (u n) y) := fun y =>
    MapClusterPt.continuousAt_comp (f := fun F : WeakDual ℝ (Lp ℝ 2 (volume : Measure E)) => F y)
      (WeakDual.eval_continuous y).continuousAt hcl
  set w0 : (Lp ℝ 2 (volume : Measure E)) := (InnerProductSpace.toDual ℝ (Lp ℝ 2 (volume : Measure E))).symm Φ with hw0
  have hw0y : ∀ y : (Lp ℝ 2 (volume : Measure E)), inner ℝ w0 y = Φ y := fun y => by
    rw [hw0, InnerProductSpace.toDual_symm_apply]
  have hnorm : ‖w0‖ ≤ M := by
    rw [hw0, LinearIsometryEquiv.norm_map]; exact hΦn
  have hmem : MemLp (fun x => w0 x) 2 volume := Lp.memLp w0
  refine ⟨fun x => w0 x, hmem, ⟨hf.locallyIntegrable (by norm_num) |>.locallyIntegrableOn _,
    hmem.locallyIntegrable (by norm_num) |>.locallyIntegrableOn _, fun φ hφ => ?_⟩, ?_⟩
  · have hφm : MemLp φ 2 volume := hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1
    set y : (Lp ℝ 2 (volume : Measure E)) := hφm.toLp φ with hy
    -- the sequence of pairings
    have hseq : ∀ n : ℕ, (u n) y = -∫ x, f x * dq v (-(1 / ((n : ℝ) + 1))) φ x := by
      intro n
      have hh : (1 / ((n : ℝ) + 1)) ≠ 0 := by positivity
      show inner ℝ (g n) y = _
      simp only [g, hy]
      rw [inner_toLp_eq]
      have := integral_mul_dq_neg (v := v) hh hf hφm
      linarith
    have hlim := (tendsto_integral_mul_dq (v := v) (hf.locallyIntegrable (by norm_num)) hφ).neg
    have hlim' : Filter.Tendsto (fun n : ℕ => (u n) y) Filter.atTop
        (nhds (-∫ x, f x * pd v φ x)) := by
      refine hlim.congr (fun n => ?_)
      rw [hseq n]
    have hcl2 : MapClusterPt (φw y) Filter.atTop (fun n => (u n) y) := hclu y
    have heq : φw y = -∫ x, f x * pd v φ x := by
      have h3 : ClusterPt (φw y) (nhds (-∫ x, f x * pd v φ x)) := hcl2.clusterPt.mono hlim'
      exact eq_of_nhds_neBot h3
    have hΦy : Φ y = φw y := rfl
    have hinner : inner ℝ w0 y = ∫ x, w0 x * φ x := by
      rw [hy]
      have := inner_toLp_eq (Lp.memLp w0) hφm
      rw [Lp_inner_eq_integral]
      refine integral_congr_ae ?_
      filter_upwards [hφm.coeFn_toLp] with x hx
      rw [hy] at *; simp [hx]
    have := hw0y y
    rw [hinner, hΦy, heq] at this
    linarith
  · rw [← Lp_norm_eq_l2]; exact hnorm

end CutoffRigidity.Riemann.Diff
