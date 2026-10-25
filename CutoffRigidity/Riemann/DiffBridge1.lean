module

public import CutoffRigidity.Riemann.DiffBridge

/-! # Bridge `Pt = Kk`, part 2: the mass trick and the identification

For `Pt`, `Kk` with `IsDiffusionSemigroup` and `MinimalResolvent F V Kk` (Perron property of the
resolvent of `Kk`), we show `U^P_λ g (x) = U^K_λ g (x)` (comparison from the Perron property, then
the mass trick with Gaffney cutoffs), then `Pₜ g (x) = Kₜ g (x)` by Laplace uniqueness, and finally
`Pt t x = Kk t x`.
-/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set
open scoped Manifold ContDiff ENNReal NNReal Topology

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutoffRigidity.Riemann.Diff

open CutCur CutoffRigidity.Riemann

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M] {V : M → ℝ} {Pt : ℝ≥0 → Kernel M M}

/-- Dominated convergence for the resolvent: uniformly bounded `C_c^∞` functions converging
pointwise to a constant `c` have resolvents converging to `c / λ`. -/
theorem tendsto_resolventU_const (hP : IsDiffusionSemigroup F V Pt) (hV : MSmooth F V) {lam : ℝ}
    (hlam : 0 < lam) {h : ℕ → M → ℝ} (hs : ∀ n, MSmooth F (h n))
    (hc : ∀ n, HasCompactSupport (h n)) {C : ℝ} (hb : ∀ n y, |h n y| ≤ C) {c : ℝ}
    (hl : ∀ y, Tendsto (fun n => h n y) atTop (𝓝 c)) (x : M) :
    Tendsto (fun n => resolventU Pt lam (h n) x) atTop (𝓝 (c / lam)) := by
  have hc0 : (∫ s in Ioi (0 : ℝ), Real.exp (-lam * s) * c) = c / lam := by
    rw [integral_mul_const, integral_exp_mul_Ioi (a := -lam) (by linarith)]
    simp only [mul_zero, Real.exp_zero]
    field_simp
  rw [← hc0]
  unfold resolventU
  refine tendsto_integral_of_dominated_convergence (fun s => C * Real.exp (-lam * s))
    (fun n => ?_) ?_ (fun n => ?_) ?_
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (continuous_semi_time_of_diffusion F hP hV (hs n) (hc n) x)).aestronglyMeasurable
  · exact (integrableOn_exp_mul_Ioi (a := -lam) (by linarith) 0).const_mul C
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s _ => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
    exact mul_le_mul_of_nonneg_right (semi_abs_le_bridge F hP (hb n) _ x) (Real.exp_pos _).le
  · refine Filter.Eventually.of_forall fun s => ?_
    haveI : IsProbabilityMeasure (Pt s.toNNReal x) := (hP.1 _).isProbabilityMeasure x
    have h1 : Tendsto (fun n => semi Pt s.toNNReal (h n) x) atTop (𝓝 c) := by
      have := tendsto_integral_of_bdd (P := Pt s.toNNReal x) (h := fun n => h n) (h0 := fun _ => c)
        (fun n => (hs n).continuous.aestronglyMeasurable) hb hl
      simpa [semi] using this
    exact h1.const_mul _

section Mass

variable [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]

/-- **Mass trick**: `U^P_λ g = U^K_λ g` for all `g ∈ C_c^∞`, `g ≥ 0`. -/
theorem resolventU_eq_of_minimal {Kk : ℝ≥0 → Kernel M M} (hP : IsDiffusionSemigroup F V Pt)
    (hK : IsDiffusionSemigroup F V Kk) (hV : MSmooth F V) (hmin : MinimalResolvent F V Kk)
    (hcut : WeightedCutoffs F M) {lam : ℝ} (hlam : 0 < lam) {g : M → ℝ} (hg : MSmooth F g)
    (hgc : HasCompactSupport g) (hg0 : ∀ y, 0 ≤ g y) (x : M) :
    resolventU Pt lam g x = resolventU Kk lam g x := by
  obtain ⟨χ, hχ, hlim⟩ := hcut
  obtain ⟨C, hC⟩ := exists_abs_le_of_cs F hg hgc
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC x)
  have hχs : ∀ n, MSmooth F (χ n) := fun n => (hχ n).1
  have hχc : ∀ n, HasCompactSupport (χ n) := fun n => (hχ n).2.1
  have hχ01 : ∀ n y, 0 ≤ χ n y ∧ χ n y ≤ 1 := fun n y => ⟨((hχ n).2.2 y).1, ((hχ n).2.2 y).2.1⟩
  -- the three families
  set A : ℕ → M → ℝ := fun n y => C * χ n y with hA
  set B : ℕ → M → ℝ := fun n y => g y * χ n y with hB
  set D : ℕ → M → ℝ := fun n y => g y - g y * χ n y with hD
  have hAs : ∀ n, MSmooth F (A n) := fun n => contMDiff_const.mul (hχs n)
  have hAc : ∀ n, HasCompactSupport (A n) := fun n => (hχc n).mul_left (f := fun _ => C)
  have hBs : ∀ n, MSmooth F (B n) := fun n => hg.mul (hχs n)
  have hBc : ∀ n, HasCompactSupport (B n) := fun n => (hχc n).mul_left (f := g)
  have hDs : ∀ n, MSmooth F (D n) := fun n => hg.sub (hBs n)
  have hDc : ∀ n, HasCompactSupport (D n) := fun n => hgc.sub (hBc n)
  -- nonnegativity of the difference
  have hd : ∀ {h : M → ℝ}, MSmooth F h → HasCompactSupport h → (∀ y, 0 ≤ h y) →
      resolventU Kk lam h x ≤ resolventU Pt lam h x := fun hs hc h0 =>
    resolventU_le_of_minimal F hP hV hmin hlam hs hc h0 x
  have hAB : ∀ n, MSmooth F (fun y => A n y - B n y) := fun n => (hAs n).sub (hBs n)
  have hABc : ∀ n, HasCompactSupport (fun y => A n y - B n y) := fun n => (hAc n).sub (hBc n)
  have hAB0 : ∀ n y, 0 ≤ A n y - B n y := fun n y => by
    simp only [hA, hB]
    have := (abs_le.1 (hC y)).2
    nlinarith [(hχ01 n y).1]
  have hD0 : ∀ n y, 0 ≤ D n y := fun n y => by
    simp only [hD]
    nlinarith [hg0 y, (hχ01 n y).2]
  -- inequality for each n
  have key : ∀ n, resolventU Pt lam g x - resolventU Kk lam g x ≤
      (resolventU Pt lam (A n) x - resolventU Kk lam (A n) x) + resolventU Pt lam (D n) x := by
    intro n
    have e1 := resolventU_sub F hP hV hg hgc (hBs n) (hBc n) hlam x
    have e2 := resolventU_sub F hK hV hg hgc (hBs n) (hBc n) hlam x
    have e3 := resolventU_sub F hP hV (hAs n) (hAc n) (hBs n) (hBc n) hlam x
    have e4 := resolventU_sub F hK hV (hAs n) (hAc n) (hBs n) (hBc n) hlam x
    have i1 := hd (hAB n) (hABc n) (hAB0 n)
    have i2 := resolventU_nonneg F hK (hD0 n) lam x
    simp only [hD] at i2
    simp only [hD]
    rw [e3, e4] at i1
    linarith
  -- limits
  have hbA : ∀ n y, |A n y| ≤ C := fun n y => by
    simp only [hA]
    rw [abs_mul, abs_of_nonneg hC0, abs_of_nonneg (hχ01 n y).1]
    nlinarith [(hχ01 n y).2]
  have hbD : ∀ n y, |D n y| ≤ C := fun n y => by
    rw [abs_of_nonneg (hD0 n y)]
    simp only [hD]
    nlinarith [(abs_le.1 (hC y)).2, (hχ01 n y).1, hg0 y]
  have hlA : ∀ y, Tendsto (fun n => A n y) atTop (𝓝 C) := fun y =>
    tendsto_const_nhds.congr' (by
      filter_upwards [hlim y] with n hn
      simp [hA, hn])
  have hlD : ∀ y, Tendsto (fun n => D n y) atTop (𝓝 0) := fun y =>
    tendsto_const_nhds.congr' (by
      filter_upwards [hlim y] with n hn
      simp [hD, hn])
  have tP := tendsto_resolventU_const F hP hV hlam hAs hAc hbA hlA x
  have tK := tendsto_resolventU_const F hK hV hlam hAs hAc hbA hlA x
  have tD := tendsto_resolventU_const F hP hV hlam hDs hDc hbD hlD x
  have tot := (tP.sub tK).add tD
  have hle : resolventU Pt lam g x - resolventU Kk lam g x ≤ C / lam - C / lam + 0 / lam :=
    ge_of_tendsto' tot key
  have hge := hd hg hgc hg0
  simp at hle
  linarith

end Mass

section Final

variable [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]

/-- **Bridge** (`riemann-status/CO_PLAN.md` 2.3): a diffusion semigroup `Pt` agrees with any
diffusion semigroup `Kk` whose resolvent has the Perron property. -/
theorem bridge_of_minimal {Kk : ℝ≥0 → Kernel M M} (hP : IsDiffusionSemigroup F V Pt)
    (hK : IsDiffusionSemigroup F V Kk) (hV : MSmooth F V) (hmin : MinimalResolvent F V Kk) :
    ∀ (t : ℝ≥0) (x : M), Pt t x = Kk t x := by
  haveI : SigmaCompactSpace M := sigmaCompactSpace_of_complete_riemannian (F := F) (M := M)
  have hcut : WeightedCutoffs F M := weightedCutoffs_of_complete F
  intro t x
  haveI := (hP.1 t).isProbabilityMeasure x
  haveI := (hK.1 t).isProbabilityMeasure x
  refine measure_eq_of_integral_smooth F hcut (fun g hg hgc => ?_)
  -- reduce to nonnegative `g`
  have hnn : ∀ g : M → ℝ, MSmooth F g → HasCompactSupport g → (∀ y, 0 ≤ g y) →
      semi Pt t g x = semi Kk t g x := by
    intro g hg hgc hg0
    set φ : ℝ → ℝ := fun s => semi Pt s.toNNReal g x - semi Kk s.toNNReal g x with hφ
    have hφc : Continuous φ := (continuous_semi_time_of_diffusion F hP hV hg hgc x).sub
      (continuous_semi_time_of_diffusion F hK hV hg hgc x)
    obtain ⟨C, hC⟩ := exists_abs_le_of_cs F hg hgc
    have hφb : ∀ s, |φ s| ≤ C + C := fun s =>
      (abs_sub _ _).trans (add_le_add (semi_abs_le_bridge F hP hC _ x) (semi_abs_le_bridge F hK hC _ x))
    have hz : ∀ m : ℕ, ∫ s in Ioi (0 : ℝ), Real.exp (-((m : ℝ) + 2) * s) * φ s = 0 := by
      intro m
      have hl : (0 : ℝ) < (m : ℝ) + 2 := by positivity
      have h1 := resolventU_eq_of_minimal F hP hK hV hmin hcut hl hg hgc hg0 x
      unfold resolventU at h1
      have : ∫ s in Ioi (0 : ℝ), Real.exp (-((m : ℝ) + 2) * s) * φ s =
          (∫ s in Ioi (0 : ℝ), Real.exp (-((m : ℝ) + 2) * s) * semi Pt s.toNNReal g x) -
          ∫ s in Ioi (0 : ℝ), Real.exp (-((m : ℝ) + 2) * s) * semi Kk s.toNNReal g x := by
        rw [← integral_sub (resolventU_integrableOn F hP hV hg hgc hl x)
          (resolventU_integrableOn F hK hV hg hgc hl x)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
        simp only [hφ, mul_sub]
      rw [this, h1, sub_self]
    have := laplace_unique hφc hφb hz (t : ℝ) t.2
    simpa [hφ, sub_eq_zero] using this
  -- general `g`: write `g = (g + C ψ) - C ψ` with a bump `ψ = 1` on `supp g`
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace F M
  obtain ⟨C, hC⟩ := exists_abs_le_of_cs F hg hgc
  obtain ⟨K', hK', hKK'⟩ := exists_compact_superset hgc
  obtain ⟨ψ, h1, h0, h01⟩ := exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, F)
    (n := ⊤) (isClosed_tsupport g) hKK'
  have hψ : MSmooth F (ψ : M → ℝ) := ψ.contMDiff
  have hψc : HasCompactSupport (ψ : M → ℝ) :=
    HasCompactSupport.intro hK' fun x hx => h0 x hx
  have hψ1 : ∀ y, y ∈ tsupport g → ψ y = 1 := fun y hy =>
    (eventually_nhdsSet_iff_forall.1 h1 y hy).self_of_nhds
  have hpos : ∀ y, 0 ≤ g y + C * ψ y := fun y => by
    by_cases hy : y ∈ tsupport g
    · rw [hψ1 y hy]; linarith [(abs_le.1 (hC y)).1]
    · rw [image_eq_zero_of_notMem_tsupport hy]
      simpa using mul_nonneg ((abs_nonneg _).trans (hC y)) (h01 y).1
  have hCψs : MSmooth F (fun y => C * ψ y) := contMDiff_const.mul hψ
  have hCψc : HasCompactSupport (fun y => C * ψ y) := hψc.mul_left (f := fun _ => C)
  have hgs : MSmooth F (fun y => g y + C * ψ y) := hg.add hCψs
  have hgsc : HasCompactSupport (fun y => g y + C * ψ y) := hgc.add hCψc
  have e1 := hnn _ hgs hgsc hpos
  have e2 := hnn (fun y => C * ψ y) hCψs hCψc (fun y => mul_nonneg
    ((abs_nonneg _).trans (hC y) |>.trans' le_rfl) (h01 y).1)
  have hi : ∀ (P : Measure M) [IsFiniteMeasure P], Integrable g P := fun P _ =>
    integrable_cs F hg hgc P
  have hi2 : ∀ (P : Measure M) [IsFiniteMeasure P], Integrable (fun y => C * ψ y) P :=
    fun P _ => integrable_cs F hCψs hCψc P
  simp only [semi] at e1 e2
  rw [integral_add (hi _) (hi2 _), integral_add (hi _) (hi2 _)] at e1
  linarith

end Final

end CutoffRigidity.Riemann.Diff
