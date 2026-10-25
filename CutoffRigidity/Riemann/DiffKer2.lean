module

public import CutoffRigidity.Riemann.DiffKer1

/-! # The continuous representative `Tc t u` of `T_t u` and the Riesz density `p_t(x,·)` (KER, A6)
-/

@[expose] public section

open Bundle MeasureTheory Filter Set Topology
open scoped Manifold ContDiff ENNReal Topology NNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Rep

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

/-- The smooth representative of `T_t u` (junk `0` for `t = 0`). -/
noncomputable def Tc (t : ℝ≥0) (u : M →₂[μ] ℝ) : M → ℝ :=
  open Classical in
  if ht : t ≠ 0 then Classical.choose (smooth_rep_semigroup F hV hμ ht u) else 0

theorem Tc_smooth {t : ℝ≥0} (ht : t ≠ 0) (u : M →₂[μ] ℝ) : MSmooth F (Tc F hV hμ t u) := by
  unfold Tc; rw [dif_pos ht]
  exact (Classical.choose_spec (smooth_rep_semigroup F hV hμ ht u)).1

theorem Tc_ae {t : ℝ≥0} (ht : t ≠ 0) (u : M →₂[μ] ℝ) :
    (((diffFR F hV hμ).semigroup t u : M →₂[μ] ℝ) : M → ℝ) =ᵐ[μ] Tc F hV hμ t u := by
  unfold Tc; rw [dif_pos ht]
  exact (Classical.choose_spec (smooth_rep_semigroup F hV hμ ht u)).2

theorem Tc_continuous {t : ℝ≥0} (ht : t ≠ 0) (u : M →₂[μ] ℝ) : Continuous (Tc F hV hμ t u) :=
  (Tc_smooth F hV hμ ht u).continuous

theorem Tc_eq_of_ae {t : ℝ≥0} (ht : t ≠ 0) (u : M →₂[μ] ℝ) {f : M → ℝ} (hf : Continuous f)
    (h : (((diffFR F hV hμ).semigroup t u : M →₂[μ] ℝ) : M → ℝ) =ᵐ[μ] f) :
    Tc F hV hμ t u = f :=
  continuous_eq_of_ae F hV hμ (Tc_continuous F hV hμ ht u) hf ((Tc_ae F hV hμ ht u).symm.trans h)

theorem Tc_add (t : ℝ≥0) (u v : M →₂[μ] ℝ) :
    Tc F hV hμ t (u + v) = Tc F hV hμ t u + Tc F hV hμ t v := by
  by_cases ht : t = 0
  · simp [Tc, ht]
  · refine Tc_eq_of_ae F hV hμ ht _ ((Tc_continuous F hV hμ ht u).add (Tc_continuous F hV hμ ht v)) ?_
    rw [map_add]
    filter_upwards [Lp.coeFn_add ((diffFR F hV hμ).semigroup t u) ((diffFR F hV hμ).semigroup t v),
      Tc_ae F hV hμ ht u, Tc_ae F hV hμ ht v] with z h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3]; rfl

theorem Tc_smul (t : ℝ≥0) (c : ℝ) (u : M →₂[μ] ℝ) :
    Tc F hV hμ t (c • u) = c • Tc F hV hμ t u := by
  by_cases ht : t = 0
  · simp [Tc, ht]
  · refine Tc_eq_of_ae F hV hμ ht _ ((Tc_continuous F hV hμ ht u).const_smul c) ?_
    rw [map_smul]
    filter_upwards [Lp.coeFn_smul c ((diffFR F hV hμ).semigroup t u),
      Tc_ae F hV hμ ht u] with z h1 h2
    rw [h1, Pi.smul_apply, h2]; rfl

theorem Tc_sub (t : ℝ≥0) (u v : M →₂[μ] ℝ) :
    Tc F hV hμ t (u - v) = Tc F hV hμ t u - Tc F hV hμ t v := by
  have : u - v = u + (-1 : ℝ) • v := by simp [sub_eq_add_neg]
  rw [this, Tc_add, Tc_smul]
  ext z; simp [sub_eq_add_neg]

theorem Tc_nonneg {t : ℝ≥0} (ht : t ≠ 0) (u : M →₂[μ] ℝ) (hu : 0 ≤ᵐ[μ] u) :
    ∀ x, 0 ≤ Tc F hV hμ t u x := by
  have h1 := diff_semigroup_nonneg F hV hμ t u hu
  exact continuous_nonneg_of_ae F hV hμ (Tc_continuous F hV hμ ht u)
    (h1.mp ((Tc_ae F hV hμ ht u).mono fun z hz hz0 => by simpa [← hz] using hz0)
      |> fun h => by
        filter_upwards [h1, Tc_ae F hV hμ ht u] with z a b
        simpa [← b] using a)

theorem Tc_one {t : ℝ≥0} (ht : t ≠ 0) : Tc F hV hμ t (oneL2 μ) = fun _ => 1 := by
  refine Tc_eq_of_ae F hV hμ ht _ continuous_const ?_
  rw [diff_semigroup_one]
  exact coeFn_oneL2 μ

theorem Tc_comp {s t : ℝ≥0} (hs : s ≠ 0) (ht : t ≠ 0) (u : M →₂[μ] ℝ) :
    Tc F hV hμ (s + t) u = Tc F hV hμ s ((diffFR F hV hμ).semigroup t u) := by
  have hst : s + t ≠ 0 := fun h => hs (by simpa using (add_eq_zero.1 h).1)
  refine Tc_eq_of_ae F hV hμ hst u (Tc_continuous F hV hμ hs _) ?_
  rw [(diffFR F hV hμ).semigroup_add, ContinuousLinearMap.mul_apply]
  exact Tc_ae F hV hμ hs _

theorem Tc_bound {t : ℝ≥0} (ht : t ≠ 0) {K : Set M} (hK : IsCompact K) :
    ∃ C : ℝ, ∀ (u : M →₂[μ] ℝ), ∀ x ∈ K, |Tc F hV hμ t u x| ≤ C * ‖u‖ := by
  obtain ⟨C, hC⟩ := local_bound_of_smooth_rep F hV hμ ((diffFR F hV hμ).semigroup t)
    (fun u => ⟨_, Tc_smooth F hV hμ ht u, Tc_ae F hV hμ ht u⟩) hK
  exact ⟨C, fun u x hx => hC u _ (Tc_continuous F hV hμ ht u) (Tc_ae F hV hμ ht u) x hx⟩

end Rep

end CutoffRigidity.Riemann.Diff
