module

public import CutoffRigidity.Riemann.WeightedRegular
public import CutoffRigidity.Riemann.WeightedPointwise

/-! # Diffusion semigroups: elementary regularity of `t ↦ Pₜ f (x)`

For `Pt` with `IsDiffusionSemigroup F V Pt` and a smooth compactly supported `f`, the Dynkin
identity of the Challenge integrates `s ↦ ∫ 𝓛f dPₛ(x,·)` with a Bochner interval integral,
which has the junk value `0` for a non-integrable integrand.  We show that this never happens:
`s ↦ Pₛ f (x)` is Lipschitz (hence continuous), so the integrand is continuous and the Dynkin
identity holds with a genuine integral; `t ↦ Pₜ f (x)` is `C¹` with derivative `Pₜ(𝓛f)(x)`.
-/

@[expose] public section

open Bundle MeasureTheory ProbabilityTheory Filter Set
open scoped Manifold ContDiff ENNReal NNReal Topology

namespace CutoffRigidity.Riemann

open CutCur

section

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

/-- `𝓛f` vanishes outside the support of `f` (locality of the Levi-Civita connection). -/
theorem mgenerator_eq_zero_of_notMem_tsupport (V : M → ℝ) {f : M → ℝ} (hf : MSmooth F f) {x : M}
    (hx : x ∉ tsupport f) : mgenerator F V f x = 0 := by
  have hg0 : mgrad F f x = 0 := mgrad_eq_zero_of_notMem_tsupport F hx
  have hev : ∀ᶠ y in 𝓝 x, mgrad F f y = 0 := by
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
    exact mgrad_eq_zero_of_notMem_tsupport F hy
  have hcov := (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M).isCovariantDerivativeOn (s := Set.univ)
  have key := hcov.congr_of_eventuallyEq (σ' := 0) (mgrad_mdiffAt F hf x)
    (mdifferentiableAt_zeroSection ..) Filter.univ_mem (by simpa using hev)
  have e : mlaplacian F f x = 0 := by
    unfold mlaplacian
    rw [key, CovariantDerivative.zero]
    simp
  simp [mgenerator, e, hg0]

theorem hasCompactSupport_mgenerator (V : M → ℝ) {f : M → ℝ} (hf : MSmooth F f)
    (hfc : HasCompactSupport f) : HasCompactSupport (mgenerator F V f) := by
  refine hfc.mono' ?_
  intro x hx
  by_contra h
  exact hx (mgenerator_eq_zero_of_notMem_tsupport F V hf h)

theorem msmooth_mgenerator {V : M → ℝ} (hV : MSmooth F V) {f : M → ℝ} (hf : MSmooth F f) :
    MSmooth F (mgenerator F V f) :=
  (weightedRegular V hV).2.1 f hf

/-- A smooth compactly supported function has a smooth compactly supported generator. -/
theorem exists_abs_mgenerator_le {V : M → ℝ} (hV : MSmooth F V) {f : M → ℝ} (hf : MSmooth F f)
    (hfc : HasCompactSupport f) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |mgenerator F V f z| ≤ C := by
  obtain ⟨C, hC⟩ := (msmooth_mgenerator F hV hf).continuous.bounded_above_of_compact_support
    (hasCompactSupport_mgenerator F V hf hfc)
  exact ⟨max C 0, le_max_right _ _, fun z => (hC z).trans (le_max_left _ _)⟩

section Dynkin

variable [MeasurableSpace M] [BorelSpace M] {V : M → ℝ} {Pt : ℝ≥0 → Kernel M M}

theorem dynkin_bound (hP : IsDiffusionSemigroup F V Pt) {f : M → ℝ} (hf : MSmooth F f)
    (hfc : HasCompactSupport f) {C : ℝ} (hC : ∀ z, |mgenerator F V f z| ≤ C) (u : ℝ≥0) (y : M) :
    |∫ z, f z ∂Pt u y - f y| ≤ C * u := by
  have h := hP.2.2 f hf hfc y u
  have hb : ‖∫ s in (0 : ℝ)..(u : ℝ), ∫ z, mgenerator F V f z ∂Pt s.toNNReal y‖ ≤
      C * |(u : ℝ) - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s _
    have : IsProbabilityMeasure (Pt s.toNNReal y) := (hP.1 _).isProbabilityMeasure y
    calc ‖∫ z, mgenerator F V f z ∂Pt s.toNNReal y‖
        ≤ C * (Pt s.toNNReal y).real univ :=
          norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hC)
      _ = C := by simp
  rw [h]
  simpa using hb

theorem dynkin_lipschitz_step (hP : IsDiffusionSemigroup F V Pt) {f : M → ℝ} (hf : MSmooth F f)
    (hfc : HasCompactSupport f) {C : ℝ} (hC : ∀ z, |mgenerator F V f z| ≤ C) (x : M)
    (t u : ℝ≥0) :
    |∫ z, f z ∂Pt (t + u) x - ∫ z, f z ∂Pt t x| ≤ C * u := by
  have hint : ∀ ν : Measure M, IsFiniteMeasure ν → Integrable f ν := fun ν _ =>
    hf.continuous.integrable_of_hasCompactSupport hfc
  have hcomp : Pt (t + u) = Pt u ∘ₖ Pt t := hP.2.1 t u
  have hI : Integrable f ((Pt u ∘ₖ Pt t) x) := by
    haveI : IsMarkovKernel (Pt u ∘ₖ Pt t) := by
      haveI := hP.1 u; haveI := hP.1 t; infer_instance
    exact hint _ inferInstance
  have h1 : ∫ z, f z ∂Pt (t + u) x = ∫ y, ∫ z, f z ∂Pt u y ∂Pt t x := by
    rw [hcomp]; exact ProbabilityTheory.Kernel.integral_comp hI
  have hg : Integrable (fun y => ∫ z, f z ∂Pt u y) (Pt t x) := hI.integral_comp
  haveI : IsProbabilityMeasure (Pt t x) := (hP.1 t).isProbabilityMeasure x
  have hf' : Integrable f (Pt t x) := hint _ inferInstance
  rw [h1, ← integral_sub hg hf']
  have := norm_integral_le_of_norm_le_const (μ := Pt t x)
    (f := fun y => ∫ z, f z ∂Pt u y - f y) (C := C * u)
    (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using dynkin_bound F hP hf hfc hC u y)
  simpa using this

theorem dynkin_lipschitz (hP : IsDiffusionSemigroup F V Pt) {f : M → ℝ} (hf : MSmooth F f)
    (hfc : HasCompactSupport f) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ z, |mgenerator F V f z| ≤ C)
    (x : M) :
    LipschitzWith ⟨C, hC0⟩ (fun t : ℝ≥0 => ∫ z, f z ∂Pt t x) := by
  have key : ∀ s t : ℝ≥0, s ≤ t → dist (∫ z, f z ∂Pt s x) (∫ z, f z ∂Pt t x) ≤ C * dist s t := by
    intro s t hst
    obtain ⟨u, rfl⟩ : ∃ u, t = s + u := ⟨t - s, by simp [add_tsub_cancel_of_le hst]⟩
    rw [Real.dist_eq, abs_sub_comm]
    have := dynkin_lipschitz_step F hP hf hfc hC x s u
    have hd : dist s (s + u) = u := by
      rw [NNReal.dist_eq]; simp [abs_of_nonneg]
    rw [hd]; exact this
  refine LipschitzWith.of_dist_le_mul fun s t => ?_
  rcases le_total s t with h | h
  · exact key s t h
  · rw [dist_comm, dist_comm s t]; exact key t s h

theorem continuous_dynkin (hP : IsDiffusionSemigroup F V Pt) {f : M → ℝ} (hf : MSmooth F f)
    (hfc : HasCompactSupport f) (hV : MSmooth F V) (x : M) :
    Continuous (fun t : ℝ≥0 => ∫ z, f z ∂Pt t x) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_mgenerator_le F hV hf hfc
  exact (dynkin_lipschitz F hP hf hfc hC0 hC x).continuous

/-- The Dynkin integrand `s ↦ Pₛ(𝓛f)(x)` is continuous on `ℝ`: no junk value occurs. -/
theorem continuous_dynkin_integrand (hP : IsDiffusionSemigroup F V Pt) {f : M → ℝ}
    (hf : MSmooth F f) (hfc : HasCompactSupport f) (hV : MSmooth F V) (x : M) :
    Continuous (fun s : ℝ => ∫ z, mgenerator F V f z ∂Pt s.toNNReal x) :=
  (continuous_dynkin F hP (msmooth_mgenerator F hV hf) (hasCompactSupport_mgenerator F V hf hfc)
    hV x).comp continuous_real_toNNReal

theorem dynkin_intervalIntegrable (hP : IsDiffusionSemigroup F V Pt) {f : M → ℝ}
    (hf : MSmooth F f) (hfc : HasCompactSupport f) (hV : MSmooth F V) (x : M) (a b : ℝ) :
    IntervalIntegrable (fun s : ℝ => ∫ z, mgenerator F V f z ∂Pt s.toNNReal x) volume a b :=
  (continuous_dynkin_integrand F hP hf hfc hV x).intervalIntegrable a b

/-- `t ↦ Pₜ f (x)` is `C¹` on `(0,∞)` with derivative `Pₜ(𝓛f)(x)`. -/
theorem hasDerivAt_dynkin (hP : IsDiffusionSemigroup F V Pt) {f : M → ℝ}
    (hf : MSmooth F f) (hfc : HasCompactSupport f) (hV : MSmooth F V) (x : M) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ∫ z, f z ∂Pt s.toNNReal x)
      (∫ z, mgenerator F V f z ∂Pt t.toNNReal x) t := by
  have hc := continuous_dynkin_integrand F hP hf hfc hV x
  have h1 := (hc.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add (f x)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ht] with s hs
  have := hP.2.2 f hf hfc x s.toNNReal
  rw [this, Real.coe_toNNReal _ (le_of_lt hs)]

end Dynkin

end

end CutoffRigidity.Riemann

