module

public import CutoffRigidity.Riemann.DiffPenalMain
public import CutoffRigidity.Riemann.DiffPerronAPI
public import CutoffRigidity.Riemann.DiffPerron3
public import CutoffRigidity.Riemann.DiffRegPot

/-! # P4: the Perron property of the resolvent (`MinimalResolvent`)

The plan (`riemann-status/CO_PLAN.md`, 2.2 step 7) identifies the double limit `K → ∞`, `a → ∞` of
the penalized resolvents `v_{a,K}` through two monotone limits.  Here we use a direct variational
argument which gives the same conclusion without any limit: if `u = R_lam g` and `v = v_{a,K}`,
then for every test function `φ ∈ D` supported in `{ζ < a}` (so that the killing term vanishes on it)

  `lam ‖u - v‖² ≤ E(u - φ) + lam ‖u - φ‖²`   (`variational_dist`),

uniformly in `K ≥ 0` and in all `a` beyond the support of `φ`.  Since `D` is dense in `Q` for the
energy norm (`approx_energy`) this makes `‖u - v_{a,K}‖_{L²}` small for `a ≥ a₀(δ)` uniformly in
`K`; the interior sup estimate on the fixed open set `{ζ < ζ x + 1}` converts this into pointwise
smallness at `x`, and `penalized_perron` provides the compactly supported subsolution.
-/

@[expose] public section

open Bundle MeasureTheory Filter Set ProbabilityTheory
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

include hV hμ in
/-- **`L²` closeness of the penalized resolvent, uniform in the killing strength.** -/
theorem penalized_l2_close {ζ : M → ℝ} (hζ : MSmooth F ζ) {lam : ℝ} (hlam : 0 < lam)
    (gL : M →₂[μ] ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ a0 : ℝ, ∀ a : ℝ, a0 ≤ a → ∀ K : ℝ, 0 ≤ K → ∀ v : M →₂[μ] ℝ,
      IsPenal hV hμ lam (fun x => K * Real.smoothTransition (ζ x - a)) gL v →
      ‖(diffFR F hV hμ).resolvent lam gL - v‖ ≤ δ := by
  classical
  have hdr := diff_dirResolvent F hV hμ hlam
  set T := diffT F hV hμ with hT
  set ε1 : ℝ := min 1 (lam * δ ^ 2 / (1 + lam)) with hε1def
  have hε1 : 0 < ε1 := lt_min one_pos (by positivity)
  have hε1le : ε1 ≤ 1 := min_le_left _ _
  have hε1le2 : ε1 * (1 + lam) ≤ lam * δ ^ 2 := by
    have : ε1 ≤ lam * δ ^ 2 / (1 + lam) := min_le_right _ _
    rwa [le_div_iff₀ (by positivity)] at this
  obtain ⟨φ, hφE, hφN⟩ := approx_energy T (hdr.mem gL) hε1
  obtain ⟨b, hb⟩ := LinearMap.mem_range.1 φ.2
  obtain ⟨c, hc⟩ : BddAbove (ζ '' tsupport (b : M → ℝ)) :=
    (b.2.2.isCompact.image hζ.continuous).isBounded.bddAbove
  refine ⟨c + 1, fun a ha K hK v hv => ?_⟩
  have hbζ : ∀ x, (b : M → ℝ) x ≠ 0 → Real.smoothTransition (ζ x - a) = 0 := by
    intro x hx
    have : ζ x ≤ c := hc ⟨x, subset_tsupport _ hx, rfl⟩
    exact Real.smoothTransition.zero_of_nonpos (by linarith)
  set P : (M →₂[μ] ℝ) → ℝ := fun ψ =>
    ∫ x, K * Real.smoothTransition (ζ x - a) * (v : M → ℝ) x * (ψ : M → ℝ) x ∂μ with hP
  have hPφ : P (φ : M →₂[μ] ℝ) = 0 := by
    have hae : ((φ : M →₂[μ] ℝ) : M → ℝ) =ᵐ[μ] (b : M → ℝ) := by
      have := coeFn_testToL2 F μ b
      rw [hb] at this
      exact this
    have h1 : P (φ : M →₂[μ] ℝ) =
        ∫ x, K * Real.smoothTransition (ζ x - a) * (v : M → ℝ) x * (b : M → ℝ) x ∂μ :=
      integral_congr_ae (by filter_upwards [hae] with x hx; rw [hx])
    rw [h1]
    have h2 : (fun x => K * Real.smoothTransition (ζ x - a) * (v : M → ℝ) x * (b : M → ℝ) x) =
        fun _ => (0 : ℝ) := by
      funext x
      by_cases hbx : (b : M → ℝ) x = 0
      · simp [hbx]
      · simp [hbζ x hbx]
    rw [h2]; simp
  have hPv : 0 ≤ P v := by
    refine integral_nonneg fun x => ?_
    show 0 ≤ K * Real.smoothTransition (ζ x - a) * (v : M → ℝ) x * (v : M → ℝ) x
    rw [mul_assoc]
    exact mul_nonneg (mul_nonneg hK (Real.smoothTransition.nonneg _)) (mul_self_nonneg _)
  have hwv : ∀ ψ ∈ T.Q, T.E v ψ + lam * inner ℝ v ψ + P ψ = inner ℝ gL ψ := hv.weak
  have key := variational_dist T hlam (hdr.mem gL) hv.mem (T.coe_mem φ) P (hdr.weak gL) hwv
    hPφ hPv
  have hn2 : ‖(diffFR F hV hμ).resolvent lam gL - (φ : M →₂[μ] ℝ)‖ ^ 2 ≤ ε1 ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hφN 2
  have hsq : lam * ‖(diffFR F hV hμ).resolvent lam gL - v‖ ^ 2 ≤ lam * δ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hn2 hlam.le, mul_nonneg hε1.le (sub_nonneg.2 hε1le)]
  by_contra hcon
  push Not at hcon
  have := mul_self_lt_mul_self hδ.le hcon
  nlinarith

/-- The pointwise Laplace representation of the resolvent of a kernel family (field
`resolvent_repr` of the canonical kernel). -/
def ResolventRepr (Kk : ℝ≥0 → Kernel M M) : Prop :=
  ∀ lam : ℝ, 0 < lam → ∀ (g : M → ℝ) (hg : MSmooth F g) (hc : HasCompactSupport g),
    ∃ ū : M → ℝ, MSmooth F ū ∧
      (((diffFR F hV hμ).resolvent lam (testToL2 F μ ⟨g, hg, hc⟩) : M →₂[μ] ℝ) : M → ℝ)
        =ᵐ[μ] ū ∧
      ∀ x, ū x = resolventU Kk lam g x

include hV hμ in
/-- **Perron property of the resolvent** of any kernel family with the Laplace representation. -/
theorem minimalResolvent_of_repr {Kk : ℝ≥0 → Kernel M M} (hrepr : ResolventRepr F hV hμ Kk) :
    MinimalResolvent F V Kk := by
  classical
  intro lam hlam g hg hgc hg0 x η hη
  obtain ⟨ζ, hζ, hζ0, hζc⟩ := exists_smooth_proper (F := F) (M := M)
  obtain ⟨ū, hū, hūae, hūx⟩ := hrepr lam hlam g hg hgc
  set gL : M →₂[μ] ℝ := testToL2 F μ ⟨g, hg, hgc⟩ with hgL
  set uL : M →₂[μ] ℝ := (diffFR F hV hμ).resolvent lam gL with huL
  have hgLae : (gL : M → ℝ) =ᵐ[μ] g := coeFn_testToL2 F μ ⟨g, hg, hgc⟩
  -- smooth representative with its pointwise equation
  obtain ⟨u2, hu2s, hu2ae, hu2eq⟩ := penalized_smooth hV hμ (potOK_zero (F := F) (M := M)) hg
    hgLae (isPenal_resolvent hlam gL)
  have hūu2 : ∀ y, ū y = u2 y := fun y =>
    le_antisymm
      (continuous_le_of_ae_le hV hμ hū.continuous hu2s.continuous
        (hūae.symm.trans hu2ae).le y)
      (continuous_le_of_ae_le hV hμ hu2s.continuous hū.continuous
        (hūae.symm.trans hu2ae).symm.le y)
  -- interior sup estimate on a fixed neighbourhood of `x`
  set W0 : Set M := {y | ζ y < ζ x + 1} with hW0
  have hW0o : IsOpen W0 := isOpen_lt hζ.continuous continuous_const
  have hxW0 : x ∈ W0 := by show ζ x < ζ x + 1; linarith
  obtain ⟨C, hC0, hC⟩ := interior_sup_estimate_manifold F hV hμ hW0o isCompact_singleton
    (singleton_subset_iff.2 hxW0) lam
  set δ : ℝ := η / (2 * (C + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hCδ : C * δ ≤ η / 2 := by
    rw [hδ, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  obtain ⟨a0, ha0⟩ := penalized_l2_close F hV hμ hζ hlam gL hδpos
  -- support of `g`
  obtain ⟨cg, hcg⟩ : BddAbove (ζ '' tsupport g) :=
    (hgc.isCompact.image hζ.continuous).isBounded.bddAbove
  set a : ℝ := max (max a0 (ζ x + 1)) (cg + 1) with ha
  have hga : ∀ y, g y ≠ 0 → ζ y < a := by
    intro y hy
    have : ζ y ≤ cg := hcg ⟨y, subset_tsupport _ hy, rfl⟩
    have : cg + 1 ≤ a := le_max_right _ _
    linarith
  have haa0 : a0 ≤ a := le_trans (le_max_left _ _) (le_max_left _ _)
  have hax : ζ x + 1 ≤ a := le_trans (le_max_right _ _) (le_max_left _ _)
  obtain ⟨K₀, hK₀⟩ := penalized_perron F hV hμ hζ hζc hlam hg hgc hg0 hga
    (ε := η / 4) (by positivity)
  obtain ⟨v, v', hv, hv's, hvv', -, hveq, -, f, hf, hsub, hge⟩ :=
    hK₀ (max K₀ 0) (le_max_left _ _) (le_max_right _ _)
  have hclose : ‖uL - v‖ ≤ δ := ha0 a haa0 (max K₀ 0) (le_max_right _ _) v hv
  -- pointwise estimate
  have hws : MSmooth F (fun y => u2 y - v' y) := hu2s.sub hv's
  have hgenw : ∀ y ∈ W0, mgenerator F V (fun y => u2 y - v' y) y = lam * (u2 y - v' y) := by
    intro y hy
    have e : (fun y => u2 y - v' y) = fun y => u2 y + (-1 : ℝ) * v' y := by
      funext z; ring
    have hm : MSmooth F (fun y => (-1 : ℝ) * v' y) := (contMDiff_const (c := (-1 : ℝ))).mul hv's
    rw [e, mgenerator_add F hu2s hm, mgenerator_const_mul F (-1) hv's, hu2eq y, hveq y]
    have h0 : Real.smoothTransition (ζ y - a) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by have : ζ y < ζ x + 1 := hy; linarith)
    rw [h0]; ring
  have hwae : (((uL - v : M →₂[μ] ℝ)) : M → ℝ) =ᵐ[μ] fun y => u2 y - v' y := by
    filter_upwards [Lp.coeFn_sub uL v, hu2ae, hvv'] with y h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  have hmem : MemLp (fun y => u2 y - v' y) 2 μ := MemLp.ae_eq hwae (Lp.memLp _)
  have hint2 : ∫ y, (u2 y - v' y) ^ 2 ∂μ = ‖uL - v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hwae] with y h1
    rw [h1]
    simp [pow_two]
  have hintg : Integrable (fun y => (u2 y - v' y) ^ 2) μ :=
    (memLp_two_iff_integrable_sq hws.continuous.aestronglyMeasurable).1 hmem
  have hset : ∫ y in W0, (u2 y - v' y) ^ 2 ∂μ ≤ δ ^ 2 := by
    calc ∫ y in W0, (u2 y - v' y) ^ 2 ∂μ ≤ ∫ y, (u2 y - v' y) ^ 2 ∂μ :=
          setIntegral_le_integral hintg (Eventually.of_forall fun y => sq_nonneg _)
      _ = ‖uL - v‖ ^ 2 := hint2
      _ ≤ δ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hclose 2
  have hrt : (∫ y in W0, (u2 y - v' y) ^ 2 ∂μ) ^ (1 / 2 : ℝ) ≤ δ := by
    calc (∫ y in W0, (u2 y - v' y) ^ 2 ∂μ) ^ (1 / 2 : ℝ) ≤ (δ ^ 2) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (setIntegral_nonneg hW0o.measurableSet fun y _ => sq_nonneg _)
            hset (by norm_num)
      _ = δ := by
          rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hδpos.le]
  have hpt := hC (fun y => u2 y - v' y) hws hgenw (hmem.restrict W0) x (mem_singleton x)
  have hpt2 : |u2 x - v' x| ≤ η / 2 :=
    hpt.trans ((mul_le_mul_of_nonneg_left hrt hC0).trans hCδ)
  refine ⟨f, hf.1, hf.2, hsub, ?_⟩
  have h1 := hge x
  have h2 := hūx x
  rw [hūu2 x] at h2
  have h3 := (abs_le.1 hpt2).2
  have h4 := (abs_le.1 hpt2).1
  linarith

end Main

end CutoffRigidity.Riemann.Diff
