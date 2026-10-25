module

public import CutoffRigidity.Riemann.DiffPenal1
public import CutoffRigidity.Riemann.DiffPerron1
public import CutoffRigidity.Riemann.DiffPerron2
public import CutoffRigidity.Riemann.DiffPerronBarrier

/-! # Assembly of P1-P3: the penalized Perron subsolution (input of P4)

For `lam > 0`, `ζ` smooth proper, smooth compactly supported `g ≥ 0` supported in `{ζ < a}`
and `ε > 0` there is `K₀` such that for every `K ≥ max K₀ 0` the penalized resolvent
`v = v_{a,K}` (killing rate `κ = K θ₀(ζ - a)`, `θ₀ = Real.smoothTransition`) has a smooth
representative `v'` with `0 ≤ v' ≤ ‖g‖_∞/lam`, `𝓛 v' = (lam + κ) v' - g`, `v' ≤ ε/2` on
`{ζ ≥ a + 2}`, and there is a smooth compactly supported `f` with `(lam - 𝓛) f ≤ g` and
`v' - 2 ε ≤ f`.  None of the conclusions is assumed.
-/

@[expose] public section

open Bundle MeasureTheory Filter Set
open scoped Manifold ContDiff ENNReal Topology NNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur

section Main

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

/-- The killing rate `K θ₀(ζ - a)` is a smooth potential with values in `[0, K]`. -/
theorem potOK_penal {ζ : M → ℝ} (hζ : MSmooth F ζ) (a : ℝ) {K : ℝ} (hK : 0 ≤ K) :
    PotOK F (fun x => K * Real.smoothTransition (ζ x - a)) K := by
  refine ⟨contMDiff_const.mul (Real.smoothTransition.contDiff.contMDiff.comp (hζ.sub contMDiff_const)),
    fun x => ⟨mul_nonneg hK (Real.smoothTransition.nonneg _), ?_⟩⟩
  calc K * Real.smoothTransition (ζ x - a) ≤ K * 1 :=
        mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one _) hK
    _ = K := mul_one K

include hV hμ in
/-- **Penalized Perron subsolution** (P1 + P2 + P3). -/
theorem penalized_perron {ζ : M → ℝ} (hζ : MSmooth F ζ) (hζc : ∀ c, IsCompact {x | ζ x ≤ c})
    {lam : ℝ} (hlam : 0 < lam) {g : M → ℝ} (hg : MSmooth F g) (hgc : HasCompactSupport g)
    (hg0 : ∀ x, 0 ≤ g x) {a : ℝ} (hga : ∀ x, g x ≠ 0 → ζ x < a) {ε : ℝ} (hε : 0 < ε) :
    ∃ K₀ : ℝ, ∀ K : ℝ, K₀ ≤ K → 0 ≤ K →
      ∃ (v : M →₂[μ] ℝ) (v' : M → ℝ),
        IsPenal hV hμ lam (fun x => K * Real.smoothTransition (ζ x - a))
          (testToL2 F μ ⟨g, hg, hgc⟩) v ∧
        MSmooth F v' ∧ (v : M → ℝ) =ᵐ[μ] v' ∧
        (∀ x, 0 ≤ v' x ∧ v' x ≤ (max (Classical.choose (testSub_bounded F ⟨g, hg, hgc⟩)) 0) / lam) ∧
        (∀ x, mgenerator F V v' x =
          (lam + K * Real.smoothTransition (ζ x - a)) * v' x - g x) ∧
        (∀ x, a + 2 ≤ ζ x → v' x ≤ ε / 2) ∧
        ∃ f : M → ℝ, f ∈ testSub F M ∧ (∀ y, lam * f y - mgenerator F V f y ≤ g y) ∧
          (∀ y, v' y - 2 * ε ≤ f y) := by
  set C0 := Classical.choose (testSub_bounded F ⟨g, hg, hgc⟩) with hC0
  have hC0b : ∀ x, |g x| ≤ C0 := Classical.choose_spec (testSub_bounded F ⟨g, hg, hgc⟩)
  set Cg := max C0 0 with hCg
  obtain ⟨K₀, hK₀⟩ := barrier_decay F hV hμ hζ hζc hlam Cg a (half_pos hε)
  refine ⟨K₀, fun K hKK hK0 => ?_⟩
  have hκ := potOK_penal F hζ a hK0
  obtain ⟨v, hv⟩ := penalized_exists (hV := hV) (hμ := hμ) hlam hκ (testToL2 F μ ⟨g, hg, hgc⟩)
  have hgL : ((testToL2 F μ ⟨g, hg, hgc⟩ : M →₂[μ] ℝ) : M → ℝ) =ᵐ[μ] g :=
    coeFn_testToL2 F μ ⟨g, hg, hgc⟩
  obtain ⟨v', hv's, hvv', hveq⟩ := penalized_smooth hV hμ hκ hg hgL hv
  have hgCg : ∀ x, 0 ≤ g x ∧ g x ≤ Cg := fun x =>
    ⟨hg0 x, (le_abs_self _).trans ((hC0b x).trans (le_max_left _ _))⟩
  -- a.e. bounds for `v`
  have h0 : 0 ≤ᵐ[μ] (v : M → ℝ) :=
    penalized_nonneg hlam hκ hv (by filter_upwards [hgL] with x hx; rw [hx]; exact hg0 x)
  have h1 : (v : M → ℝ) ≤ᵐ[μ] fun _ => Cg / lam :=
    penalized_le_const hlam hκ (le_max_right _ _) (c := Cg)
      (by filter_upwards [hgL] with x hx; rw [hx]; exact (hgCg x).2) hv
  have hb0 : ∀ x, 0 ≤ v' x := by
    exact fun x => continuous_le_of_ae_le hV hμ continuous_const hv's.continuous
      (by filter_upwards [h0, hvv'] with y h2 h3; rw [← h3]; exact h2) x
  have hb1 : ∀ x, v' x ≤ Cg / lam := fun x =>
    continuous_le_of_ae_le hV hμ hv's.continuous continuous_const
      (by filter_upwards [h1, hvv'] with y h2 h3; rw [← h3]; exact h2) x
  have hdecay := hK₀ K hKK g v' hv's hgCg hga (fun x => ⟨hb0 x, hb1 x⟩) hveq
  have hκ0 : ∀ x, 0 ≤ K * Real.smoothTransition (ζ x - a) := fun x => (hκ.nonneg x)
  obtain ⟨f, hf, hsub, hge⟩ := subsolution_of_penalized F hlam hv's hb0 hg0 hκ0 hveq hε
    (hζc (a + 2)) (K₀ := {x | ζ x ≤ a + 2}) (fun x hx => by
      by_contra hxc
      have hlt : a + 2 ≤ ζ x := by
        simp only [Set.mem_setOf_eq, not_le] at hxc; exact hxc.le
      have := hdecay x hlt
      linarith)
  exact ⟨v, v', hv, hv's, hvv', fun x => ⟨hb0 x, hb1 x⟩, hveq, hdecay, f, hf, hsub, hge⟩

end Main

end CutoffRigidity.Riemann.Diff
