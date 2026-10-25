module

public import CutoffRigidity.Riemann.DiffKer9

/-! # `exists_kernel`: the Tier-A kernel (KER, A6 + A7)

`KerCanonical` is `CanonicalDiffusion` WITHOUT the Bakry-Emery gradient bound (field `contraction`
and the gradient bound in `smoothing`); see `KerCanonical.toCanonical`.
-/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set Topology
open scoped Manifold ContDiff ENNReal Topology NNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Final

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]

/-- Everything of `CanonicalDiffusion` except `contraction` and the gradient bound in `smoothing`.
(`smoothing`: smoothness of `semi Kk t g`, commutation `𝓛 (Kk_t g) = Kk_t (𝓛 g)`, and bounds on
`|semi Kk s g|` and `|𝓛 (semi Kk s g)|` uniform in `s`.) -/
structure KerCanonical (V : M → ℝ) (μ : Measure M) (Kk : ℝ≥0 → Kernel M M) : Prop where
  markov : ∀ t, IsMarkovKernel (Kk t)
  dynkin : IsDiffusionSemigroup F V Kk
  invariant : ∀ t, μ.bind (Kk t) = μ
  eigen : ∀ (c : ℝ) (u : M → ℝ), MSmooth F u → MemLp u 2 μ →
      (∀ x, mgenerator F V u x = -c * u x) →
      ∀ (t : ℝ≥0) (x : M), Integrable u (Kk t x) ∧ ∫ y, u y ∂Kk t x = Real.exp (-c * t) * u x
  smoothing : ∀ g, MSmooth F g → HasCompactSupport g → ∀ t, MSmooth F (semi Kk t g) ∧
      mgenerator F V (semi Kk t g) = semi Kk t (mgenerator F V g) ∧
      ∃ C : ℝ, ∀ (s : ℝ≥0) x, |semi Kk s g x| ≤ C ∧ |mgenerator F V (semi Kk s g) x| ≤ C

/-- Adding the Bakry-Emery inputs gives `CanonicalDiffusion`. -/
theorem KerCanonical.toCanonical {V : M → ℝ} {μ : Measure M} {ρ : ℝ} {Kk : ℝ≥0 → Kernel M M}
    (h : KerCanonical F V μ Kk)
    (hgrad : ∀ g, MSmooth F g → HasCompactSupport g → ∃ C : ℝ, ∀ (s : ℝ≥0) x,
      ‖mgrad F (semi Kk s g) x‖ ≤ C)
    (hcontr : ∀ (t : ℝ≥0) (x : M), CutCur.wasserstein2 (Kk t x) μ ^ 2 ≤
      ENNReal.ofReal (Real.exp (-2 * ρ * t)) * ∫⁻ y, edist x y ^ 2 ∂μ) :
    CanonicalDiffusion F V μ ρ Kk where
  markov := h.markov
  dynkin := h.dynkin
  invariant := h.invariant
  eigen := h.eigen
  smoothing := fun g hg hc t => by
    obtain ⟨h1, h2, C1, hC1⟩ := h.smoothing g hg hc t
    obtain ⟨C2, hC2⟩ := hgrad g hg hc
    refine ⟨h1, h2, max C1 C2, fun s x => ⟨?_, ?_, ?_⟩⟩
    · exact (hC1 s x).1.trans (le_max_left _ _)
    · exact (hC2 s x).trans (le_max_right _ _)
    · exact (hC1 s x).2.trans (le_max_left _ _)
  contraction := hcontr

variable {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

theorem Kk_eigen {c : ℝ} {u : M → ℝ} (hu : MSmooth F u) (hL2 : MemLp u 2 μ)
    (hc : ∀ x, mgenerator F V u x = -c * u x) (t : ℝ≥0) (x : M) :
    Integrable u (Kk F hV hμ t x) ∧ ∫ y, u y ∂Kk F hV hμ t x = Real.exp (-c * t) * u x := by
  by_cases ht : t = 0
  · subst ht
    rw [Kk_zero, Kernel.id_apply]
    refine ⟨?_, by simp⟩
    exact integrable_dirac enorm_lt_top
  · obtain ⟨uL, huL, hsg⟩ := eigen_semigroup F hV hμ hu hL2 hc
    have hTc : Tc F hV hμ t uL = fun y => Real.exp (-c * t) * u y := by
      refine Tc_eq_of_ae F hV hμ ht uL (continuous_const.mul hu.continuous) ?_
      rw [hsg t]
      filter_upwards [Lp.coeFn_smul (Real.exp (-c * t)) uL, huL] with y h1 h2
      rw [h1, Pi.smul_apply, h2]; rfl
    obtain ⟨hi, hint⟩ := kmeas_integral F hV hμ ht x uL
    have hae : (uL : M → ℝ) =ᵐ[kmeas F hV hμ t x] u :=
      (withDensity_absolutelyContinuous μ _).ae_le huL
    rw [Kk_apply_of_ne F hV hμ ht]
    refine ⟨(hi.congr hae), ?_⟩
    rw [← integral_congr_ae hae, hint, hTc]

include hV hμ in
theorem exists_kernel : ∃ Kk : ℝ≥0 → Kernel M M, KerCanonical F V μ Kk := by
  refine ⟨Kk F hV hμ, Kk_markov F hV hμ, isDiffusionSemigroup_Kk F hV hμ, Kk_bind F hV hμ,
    fun c u hu hL2 hc t x => Kk_eigen F hV hμ hu hL2 hc t x, fun g hg hc t => ?_⟩
  obtain ⟨B1, hB1⟩ := (hg.continuous.bounded_above_of_compact_support hc)
  obtain ⟨B2, -, hB2⟩ := exists_abs_mgenerator_le F hV hg hc
  have hgen : ∀ s, semi (Kk F hV hμ) s (mgenerator F V g) =
      mgenerator F V (semi (Kk F hV hμ) s g) ∧ MSmooth F (semi (Kk F hV hμ) s g) := by
    intro s
    by_cases hs : s = 0
    · subst hs
      rw [semi_Kk_zero, semi_Kk_zero]; exact ⟨rfl, hg⟩
    · have e1 : semi (Kk F hV hμ) s g = Tc F hV hμ s (testToL2 F μ ⟨g, hg, hc⟩) :=
        funext fun x => semi_Kk_eq_Tc F hV hμ hs ⟨g, hg, hc⟩ x
      have e2 : semi (Kk F hV hμ) s (mgenerator F V g) =
          Tc F hV hμ s (testToL2 F μ (testGen F hV ⟨g, hg, hc⟩)) :=
        funext fun x => semi_Kk_eq_Tc F hV hμ hs (testGen F hV ⟨g, hg, hc⟩) x
      rw [e1, e2]
      exact ⟨(funext fun x => (Tc_generator F hV hμ hs ⟨g, hg, hc⟩ x).symm), Tc_smooth F hV hμ hs _⟩
  refine ⟨(hgen t).2, (hgen t).1.symm, max B1 B2, fun s x => ⟨?_, ?_⟩⟩
  · exact (abs_semi_le F hV hμ x g (fun z => by simpa using hB1 z)).trans (le_max_left _ _)
  · rw [← (hgen s).1]
    exact (abs_semi_le F hV hμ x _ hB2).trans (le_max_right _ _)

end Final

end CutoffRigidity.Riemann.Diff
