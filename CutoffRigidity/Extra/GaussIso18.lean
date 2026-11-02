module

public import CutoffRigidity.Extra.GaussIso17

/-! # Isoperimetry for sets (stage 7e): the finite-increment inequality (FS) from Bobkov's inequality -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ContDiff

set_option linter.unusedSectionVars false

namespace CutoffRigidity.GaussIso

variable {d : ℕ}

/-- `n_A(t) = μ{x | dist(x,A) ≤ t}`. -/
noncomputable def nA (ρ : ℝ) (A : Set (EuclideanSpace ℝ (Fin d))) (t : ℝ) : ℝ :=
  (gaussρ d ρ).real {x | infDist x A ≤ t}

lemma measurableSet_infDist_le (A : Set (EuclideanSpace ℝ (Fin d))) (t : ℝ) :
    MeasurableSet {x : EuclideanSpace ℝ (Fin d) | infDist x A ≤ t} :=
  (isClosed_le (continuous_infDist_pt A) continuous_const).measurableSet

lemma nA_mono {ρ : ℝ} (A : Set (EuclideanSpace ℝ (Fin d))) : Monotone (nA ρ A) := by
  intro s t hst
  unfold nA
  exact measureReal_mono (fun x hx => le_trans hx hst)

lemma nA_le_one {ρ : ℝ} (A : Set (EuclideanSpace ℝ (Fin d))) (t : ℝ) : nA ρ A t ≤ 1 := by
  unfold nA
  exact measureReal_le_one

lemma nA_rightContinuous {ρ : ℝ} (A : Set (EuclideanSpace ℝ (Fin d))) (r : ℝ) :
    ContinuousWithinAt (nA ρ A) (Ici r) r := by
  let ν : Measure ℝ := (gaussρ d ρ).map (fun x => infDist x A)
  have : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff (continuous_infDist_pt A).aemeasurable).2 inferInstance
  have h : nA ρ A = fun t => cdf ν t := by
    funext t
    rw [cdf_eq_real, nA]
    show _ = ν.real (Iic t)
    rw [Measure.real, Measure.real, Measure.map_apply (continuous_infDist_pt A).measurable measurableSet_Iic]
    rfl
  rw [h]
  exact (cdf ν).right_continuous r


lemma Gfun_le {ρ : ℝ} (hρ : 0 < ρ) (ψ : ℝ → ℝ) (t : ℝ) :
    Gfun ρ ψ t ≤ gI (ψ t) + (Real.sqrt ρ)⁻¹ * |deriv ψ t| := by
  unfold Gfun
  apply Real.sqrt_le_iff.2
  have hc : 0 ≤ (Real.sqrt ρ)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  refine ⟨by have := gI_nonneg (ψ t); positivity, ?_⟩
  have h2 : ((Real.sqrt ρ)⁻¹) ^ 2 = ρ⁻¹ := by rw [inv_pow, Real.sq_sqrt hρ.le]
  have : ρ⁻¹ * deriv ψ t ^ 2 = ((Real.sqrt ρ)⁻¹ * |deriv ψ t|) ^ 2 := by
    rw [mul_pow, h2, sq_abs]
  rw [this]
  nlinarith [gI_nonneg (ψ t), mul_nonneg hc (abs_nonneg (deriv ψ t)),
    mul_nonneg (gI_nonneg (ψ t)) (mul_nonneg hc (abs_nonneg (deriv ψ t)))]

/-- The finite-increment inequality (FS) for the distance profile of a set. -/
theorem fs_sets {ρ : ℝ} (hρ : 0 < ρ) {A : Set (EuclideanSpace ℝ (Fin d))} (hA : A.Nonempty)
    {r s η : ℝ} (hs : 0 < s) (hη : 0 < η) :
    ∃ N, nA ρ A r ≤ N ∧ N ≤ nA ρ A (r + s) ∧
      gI N ≤ (gφ 0 + (Real.sqrt ρ)⁻¹ * (1 + η) / s) * (nA ρ A (r + s) - nA ρ A r) := by
  obtain ⟨ψ, hψ, h01, hψ1, hψ0, hψd⟩ := exists_ramp (r := r) hs hη
  set μ := gaussρ d ρ with hμ
  have he : LipschitzWith 1 (fun x : EuclideanSpace ℝ (Fin d) => infDist x A) := lipschitz_infDist_pt A
  have hec : Continuous (fun x : EuclideanSpace ℝ (Fin d) => infDist x A) := continuous_infDist_pt A
  have hψc : Continuous ψ := hψ.continuous
  have hB := bobkov_ramp (d := d) hρ he hψ h01 ⟨(1 + η) / s, hψd⟩
  refine ⟨∫ x, ψ (infDist x A) ∂μ, ?_, ?_, hB.trans ?_⟩
  · -- n r ≤ N
    unfold nA
    have : (gaussρ d ρ).real {x | infDist x A ≤ r} =
        ∫ x, Set.indicator {x | infDist x A ≤ r} (fun _ => (1:ℝ)) x ∂gaussρ d ρ := by
      rw [integral_indicator_const (1:ℝ) (measurableSet_infDist_le A r)]; simp
    rw [this]
    refine integral_mono ?_ ?_ fun x => ?_
    · exact (integrable_const (1:ℝ)).indicator (measurableSet_infDist_le A r)
    · exact Integrable.mono' (integrable_const 1) (hψc.comp hec).aestronglyMeasurable
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (h01 _).1]; exact (h01 _).2)
    · by_cases hx : infDist x A ≤ r
      · rw [indicator_of_mem (show x ∈ {x | infDist x A ≤ r} from hx), hψ1 _ hx]
      · rw [indicator_of_notMem (show x ∉ {x | infDist x A ≤ r} from hx)]
        exact (h01 _).1
  · -- N ≤ n (r+s)
    unfold nA
    have : (gaussρ d ρ).real {x | infDist x A ≤ r + s} =
        ∫ x, Set.indicator {x | infDist x A ≤ r + s} (fun _ => (1:ℝ)) x ∂gaussρ d ρ := by
      rw [integral_indicator_const (1:ℝ) (measurableSet_infDist_le A (r + s))]; simp
    rw [this]
    refine integral_mono ?_ ?_ fun x => ?_
    · exact Integrable.mono' (integrable_const 1) (hψc.comp hec).aestronglyMeasurable
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (h01 _).1]; exact (h01 _).2)
    · exact (integrable_const (1:ℝ)).indicator (measurableSet_infDist_le A (r + s))
    · by_cases hx : infDist x A ≤ r + s
      · rw [indicator_of_mem (show x ∈ {x | infDist x A ≤ r + s} from hx)]; exact (h01 _).2
      · rw [indicator_of_notMem (show x ∉ {x | infDist x A ≤ r + s} from hx), hψ0 _ (by
          rw [not_le] at hx; linarith)]
  · -- RHS bound
    set Bd : ℝ := gφ 0 + (Real.sqrt ρ)⁻¹ * (1 + η) / s with hBd
    set D : Set (EuclideanSpace ℝ (Fin d)) := {x | infDist x A ≤ r + s} \ {x | infDist x A ≤ r} with hD
    have hDm : MeasurableSet D := (measurableSet_infDist_le A _).diff (measurableSet_infDist_le A _)
    have hGnn : ∀ t, 0 ≤ Gfun ρ ψ t := fun t => Real.sqrt_nonneg _
    have hderiv0 : ∀ t, (t ≤ r ∨ r + s ≤ t) → deriv ψ t = 0 := by
      intro t ht
      rcases ht with ht | ht
      · refine IsLocalMax.deriv_eq_zero (IsMaxOn.isLocalMax (s := univ) ?_ univ_mem)
        intro u _
        simp only [mem_setOf_eq]
        rw [hψ1 t ht]; exact (h01 u).2
      · refine IsLocalMin.deriv_eq_zero (IsMinOn.isLocalMin (s := univ) ?_ univ_mem)
        intro u _
        simp only [mem_setOf_eq]
        rw [hψ0 t ht]; exact (h01 u).1
    have hGsupp : ∀ t, (t ≤ r ∨ r + s ≤ t) → Gfun ρ ψ t = 0 := by
      intro t ht
      have h1 : gI (ψ t) = 0 := by
        rcases ht with ht | ht
        · rw [hψ1 t ht]; simp [gI]
        · rw [hψ0 t ht]; simp [gI]
      unfold Gfun
      rw [h1, hderiv0 t ht]; simp
    have hGbd : ∀ t, Gfun ρ ψ t ≤ Bd := by
      intro t
      refine (Gfun_le hρ ψ t).trans ?_
      refine add_le_add (gI_le _) ?_
      have := hψd t
      calc (Real.sqrt ρ)⁻¹ * |deriv ψ t| ≤ (Real.sqrt ρ)⁻¹ * ((1 + η) / s) :=
            mul_le_mul_of_nonneg_left this (inv_nonneg.2 (Real.sqrt_nonneg _))
        _ = (Real.sqrt ρ)⁻¹ * (1 + η) / s := by ring
    have hBdnn : 0 ≤ Bd := by
      have := gφ_pos 0
      have : 0 ≤ (Real.sqrt ρ)⁻¹ * (1 + η) / s := by positivity
      linarith
    have hpt : ∀ x, Gfun ρ ψ (infDist x A) ≤ Set.indicator D (fun _ => Bd) x := by
      intro x
      by_cases hx : x ∈ D
      · rw [indicator_of_mem hx]; exact hGbd _
      · rw [indicator_of_notMem hx]
        have : infDist x A ≤ r ∨ r + s ≤ infDist x A := by
          by_contra hcon
          rw [not_or, not_le, not_le] at hcon
          exact hx ⟨(le_of_lt hcon.2), not_le.2 hcon.1⟩
        exact (hGsupp _ this).le
    calc ∫ x, Gfun ρ ψ (infDist x A) ∂μ ≤ ∫ x, Set.indicator D (fun _ => Bd) x ∂μ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun x => hGnn _) ?_
            (Eventually.of_forall hpt)
          exact (integrable_const Bd).indicator hDm
      _ = Bd * μ.real D := by
          rw [integral_indicator hDm, setIntegral_const]; simp [mul_comm]
      _ = Bd * (nA ρ A (r + s) - nA ρ A r) := by
          congr 1
          have hsub : {x : EuclideanSpace ℝ (Fin d) | infDist x A ≤ r} ⊆ {x | infDist x A ≤ r + s} :=
            fun x hx => (show infDist x A ≤ r from hx).trans (by linarith)
          rw [hD, measureReal_sdiff hsub (measurableSet_infDist_le A r)]
          rfl

end CutoffRigidity.GaussIso
