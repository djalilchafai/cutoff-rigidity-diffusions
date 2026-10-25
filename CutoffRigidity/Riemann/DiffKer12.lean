module

public import CutoffRigidity.Riemann.DiffKer11
public import CutoffRigidity.Riemann.DiffRegPot

/-! # Local bounds `sup_K |T_t u| + sup_K |𝓛 T_t u| ≤ C(K,t) ‖u‖` (KER, A5ii) -/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set Topology
open scoped Manifold ContDiff ENNReal Topology NNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Loc

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

/-- The operator `G_t = (1 - 𝓛) T_t` (`T_t = R G_t`). -/
noncomputable def Gop (t : ℝ≥0) : (M →₂[μ] ℝ) →L[ℝ] (M →₂[μ] ℝ) :=
  (diffFR F hV hμ).R * Cx.rcfc (psiFun t 2) (diffFR F hV hμ).R

theorem semigroup_eq_R_Gop {t : ℝ≥0} (ht : t ≠ 0) :
    (diffFR F hV hμ).semigroup t = (diffFR F hV hμ).R * Gop F hV hμ t := by
  have := cfcSemigroup_eq_pow_mul (diffFR F hV hμ).R_unitOp ht 2
  unfold Gop FormData.semigroup
  rw [this, pow_two, mul_assoc]

theorem Gop_smooth {t : ℝ≥0} (ht : t ≠ 0) (u : M →₂[μ] ℝ) :
    ∃ ū : M → ℝ, MSmooth F ū ∧ ((Gop F hV hμ t u : M →₂[μ] ℝ) : M → ℝ) =ᵐ[μ] ū := by
  refine smooth_rep_of_pow F hV hμ _ (fun k => ?_)
  have h := cfcSemigroup_eq_pow_mul (diffFR F hV hμ).R_unitOp ht (k + 1)
  refine ⟨Cx.rcfc (psiFun t (k + 1)) (diffFR F hV hμ).R u, ?_⟩
  rw [(diffFR F hV hμ).resolvent_one]
  apply (diffFR F hV hμ).R_injective
  have h1 := congrArg (fun T => T u) (semigroup_eq_R_Gop F hV hμ ht)
  have h2 := congrArg (fun T => T u) h
  simp only [FormData.semigroup, ContinuousLinearMap.mul_apply] at h1 h2 ⊢
  rw [← h1]
  rw [h2, pow_succ']; rfl

/-- **Local bound** for `T_t u` and `𝓛 T_t u` (representatives `Tc`): `C(K,t)` independent of `u`. -/
theorem Tc_local_bound {t : ℝ≥0} (ht : t ≠ 0) {K : Set M} (hK : IsCompact K) :
    ∃ C : ℝ, ∀ u : M →₂[μ] ℝ, ∀ x ∈ K,
      |Tc F hV hμ t u x| ≤ C * ‖u‖ ∧ |mgenerator F V (Tc F hV hμ t u) x| ≤ C * ‖u‖ := by
  obtain ⟨C1, hC1⟩ := Tc_bound F hV hμ ht hK
  obtain ⟨C2, hC2⟩ := local_bound_of_smooth_rep F hV hμ (Gop F hV hμ t)
    (fun u => Gop_smooth F hV hμ ht u) hK
  refine ⟨|C1| + |C2|, fun u x hx => ⟨?_, ?_⟩⟩
  · have := hC1 u x hx
    have hn : 0 ≤ ‖u‖ := norm_nonneg _
    have h2 : C1 * ‖u‖ ≤ |C1| * ‖u‖ := mul_le_mul_of_nonneg_right (le_abs_self _) hn
    nlinarith [abs_nonneg C2, mul_nonneg (abs_nonneg C2) hn]
  · obtain ⟨g', hg's, hg'e⟩ := Gop_smooth F hV hμ ht u
    have hres := diff_dirResolvent F hV hμ (one_pos : (0:ℝ) < 1)
    rw [(diffFR F hV hμ).resolvent_one] at hres
    have hR : ((diffFR F hV hμ).R (Gop F hV hμ t u)) = (diffFR F hV hμ).semigroup t u := by
      have := semigroup_eq_R_Gop F hV hμ ht
      rw [this]; rfl
    have hpw := pointwise_of_weak F hV hμ (lam := 1) (uL := (diffFR F hV hμ).R (Gop F hV hμ t u))
      (gL := Gop F hV hμ t u) (ū := Tc F hV hμ t u) (g' := g') (Tc_smooth F hV hμ ht u) hg's
      (by rw [hR]; exact Tc_ae F hV hμ ht u) hg'e (hres.mem _) (fun φ hφ => hres.weak _ φ hφ) x
    have e : mgenerator F V (Tc F hV hμ t u) x = Tc F hV hμ t u x - g' x := by linarith
    rw [e]
    have b1 := hC1 u x hx
    have b2 := hC2 u g' hg's.continuous hg'e x hx
    calc |Tc F hV hμ t u x - g' x| ≤ |Tc F hV hμ t u x| + |g' x| := abs_sub _ _
      _ ≤ |C1| * ‖u‖ + |C2| * ‖u‖ :=
          add_le_add (b1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)))
            (b2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)))
      _ = (|C1| + |C2|) * ‖u‖ := by ring

end Loc

end CutoffRigidity.Riemann.Diff
