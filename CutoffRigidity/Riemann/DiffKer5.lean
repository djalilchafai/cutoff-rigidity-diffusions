module

public import CutoffRigidity.Riemann.DiffKer4

/-! # The kernel `Kk`: Markov, semigroup law, invariance (KER, A6) -/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set Topology
open scoped Manifold ContDiff ENNReal Topology NNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Kernel

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

theorem indL_coeFn {A : Set M} (hA : MeasurableSet A) :
    (indL μ hA : M → ℝ) =ᵐ[μ] A.indicator fun _ => (1 : ℝ) :=
  indicatorConstLp_coeFn

theorem indL_nonneg {A : Set M} (hA : MeasurableSet A) : 0 ≤ᵐ[μ] (indL μ hA : M → ℝ) := by
  filter_upwards [indL_coeFn hA] with y hy
  rw [hy]; exact Set.indicator_nonneg (fun _ _ => zero_le_one) y

theorem indL_univ : indL μ (MeasurableSet.univ : MeasurableSet (Set.univ : Set M)) = oneL2 μ := by
  apply Lp.ext
  filter_upwards [indL_coeFn (μ := μ) (MeasurableSet.univ : MeasurableSet (Set.univ : Set M)),
    coeFn_oneL2 μ] with y h1 h2
  rw [h1, h2]; simp

/-- The nonzero-time kernel. -/
noncomputable def kerPos (t : ℝ≥0) (ht : t ≠ 0) : Kernel M M where
  toFun x := kmeas F hV hμ t x
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    have : (fun x => kmeas F hV hμ t x A) = fun x => ENNReal.ofReal (Tc F hV hμ t (indL μ hA) x) :=
      funext fun x => kmeas_apply F hV hμ ht x hA
    rw [this]
    exact ENNReal.measurable_ofReal.comp (Tc_continuous F hV hμ ht _).measurable

/-- **The kernel** `Kk t x = p_t(x,·) μ` for `t > 0`, `Kk 0 x = δ_x`. -/
noncomputable def Kk (t : ℝ≥0) : Kernel M M :=
  open Classical in
  if ht : t = 0 then Kernel.id else kerPos F hV hμ t ht

theorem Kk_zero : Kk F hV hμ 0 = Kernel.id := by simp [Kk]

theorem Kk_apply_of_ne {t : ℝ≥0} (ht : t ≠ 0) (x : M) : Kk F hV hμ t x = kmeas F hV hμ t x := by
  simp [Kk, ht, kerPos]

theorem Kk_apply_set {t : ℝ≥0} (ht : t ≠ 0) (x : M) {A : Set M} (hA : MeasurableSet A) :
    Kk F hV hμ t x A = ENNReal.ofReal (Tc F hV hμ t (indL μ hA) x) := by
  rw [Kk_apply_of_ne F hV hμ ht, kmeas_apply F hV hμ ht]

theorem Kk_ac {t : ℝ≥0} (ht : t ≠ 0) (x : M) : Kk F hV hμ t x ≪ μ := by
  rw [Kk_apply_of_ne F hV hμ ht]; exact withDensity_absolutelyContinuous _ _

theorem Kk_markov (t : ℝ≥0) : IsMarkovKernel (Kk F hV hμ t) := by
  by_cases ht : t = 0
  · subst ht; rw [Kk_zero]; infer_instance
  · refine ⟨fun x => ⟨?_⟩⟩
    rw [Kk_apply_set F hV hμ ht x MeasurableSet.univ, indL_univ, Tc_one F hV hμ ht]
    simp

theorem Kk_comp (s t : ℝ≥0) : Kk F hV hμ (s + t) = Kk F hV hμ t ∘ₖ Kk F hV hμ s := by
  by_cases hs : s = 0
  · subst hs; rw [zero_add, Kk_zero, Kernel.comp_id]
  by_cases ht : t = 0
  · subst ht; rw [add_zero, Kk_zero, Kernel.id_comp]
  have hst : s + t ≠ 0 := fun h => hs (by simpa using (add_eq_zero.1 h).1)
  haveI := Kk_markov F hV hμ s
  ext x A hA
  rw [Kernel.comp_apply' _ _ _ hA, Kk_apply_set F hV hμ hst x hA, Kk_apply_of_ne F hV hμ hs x]
  set g := Tc F hV hμ t (indL μ hA) with hg
  have hgc : Continuous g := Tc_continuous F hV hμ ht _
  have hKt : ∀ y, Kk F hV hμ t y A = ENNReal.ofReal (g y) := fun y => Kk_apply_set F hV hμ ht y hA
  simp only [hKt]
  set p := pk F hV hμ s x with hp
  have hpm : Measurable fun y => ENNReal.ofReal (p y) :=
    ENNReal.measurable_ofReal.comp (Lp.stronglyMeasurable p).measurable
  have hgm : Measurable fun y => ENNReal.ofReal (g y) :=
    ENNReal.measurable_ofReal.comp hgc.measurable
  rw [kmeas, lintegral_withDensity_eq_lintegral_mul _ hpm hgm]
  have hg0 : ∀ y, 0 ≤ g y := Tc_nonneg F hV hμ ht _ (indL_nonneg hA)
  have hmul : ∀ᵐ y ∂μ, ENNReal.ofReal (p y) * ENNReal.ofReal (g y) = ENNReal.ofReal (p y * g y) := by
    filter_upwards [pk_nonneg F hV hμ hs x] with y hy
    rw [ENNReal.ofReal_mul hy]
  have hTae := Tc_ae F hV hμ ht (indL μ hA)
  have hint : Integrable (fun y => p y * g y) μ := by
    have := (Lp.memLp p).integrable_mul (Lp.memLp ((diffFR F hV hμ).semigroup t (indL μ hA)))
    exact this.congr (by filter_upwards [hTae] with y hy; simp [hy, hg])
  rw [lintegral_congr_ae (hmul.mono fun y hy => by simpa [Pi.mul_apply] using hy)]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (by
    filter_upwards [pk_nonneg F hV hμ hs x] with y hy
    exact mul_nonneg hy (hg0 y))]
  congr 1
  rw [Tc_comp F hV hμ hs ht, ← inner_pk F hV hμ hs x, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hTae] with y hy
  simp only [RCLike.inner_apply, conj_trivial]
  rw [hy]; ring

theorem Kk_bind (t : ℝ≥0) : μ.bind (Kk F hV hμ t) = μ := by
  by_cases ht : t = 0
  · subst ht; rw [Kk_zero]; ext A hA; rw [Measure.bind_apply hA (Kernel.aemeasurable _)]; simp [Kernel.id_apply, hA]
  · ext A hA
    rw [Measure.bind_apply hA (Kernel.aemeasurable _)]
    simp_rw [Kk_apply_set F hV hμ ht _ hA]
    set u := Tc F hV hμ t (indL μ hA)
    have hu0 : ∀ y, 0 ≤ u y := Tc_nonneg F hV hμ ht _ (indL_nonneg hA)
    have hint : Integrable u μ := by
      have := (Lp.memLp ((diffFR F hV hμ).semigroup t (indL μ hA))).integrable one_le_two
      exact this.congr (Tc_ae F hV hμ ht _)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hu0)]
    have h1 : ∫ y, u y ∂μ = ∫ y, ((diffFR F hV hμ).semigroup t (indL μ hA) : M → ℝ) y ∂μ :=
      (integral_congr_ae (Tc_ae F hV hμ ht _)).symm
    rw [h1, diff_semigroup_integral F hV hμ t (indL μ hA)]
    rw [integral_congr_ae (indL_coeFn hA)]
    rw [integral_indicator_const _ hA]
    simp [Measure.real, ENNReal.ofReal_toReal (measure_ne_top μ A)]

end Kernel

end CutoffRigidity.Riemann.Diff
