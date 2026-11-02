module

public import CutoffRigidity.Extra.C2Uniq2
public import CutoffRigidity.Extra.EuclideanDiffusion
public import CutoffRigidity.Extra.Temperature
public import CutoffRigidity.Riemann.DiffBEMain

/-! # `C²` uniqueness, stage 3: the backward family of the smooth approximant

For `W = Wm V n` (smooth, strongly convex, finite Gibbs measure) and a smooth compactly supported
`0 ≤ g ≤ K`, the canonical kernel `Kk` of the library gives the backward family
`w τ = K_τ g` with the properties collected in `IsBackward`; the gradient bound `G` is uniform in `n`
(Bakry-Emery).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CutCur

open MeasureTheory ProbabilityTheory Filter Topology Set
open Bundle
open scoped ENNReal NNReal ContDiff Manifold

namespace C2U

variable {d : ℕ}

/-- A backward family for `W` started at `g`: smooth in space, between `0` and `K`, gradient bounded
by `G`, differentiable in time with `∂_τ w = 𝓛_W w`, continuous in time, `w 0 = g`. -/
structure IsBackward (W g : Rd d → ℝ) (w : ℝ≥0 → Rd d → ℝ) (K G C : ℝ) : Prop where
  smooth : ∀ τ, ContDiff ℝ ∞ (w τ)
  nonneg : ∀ τ y, 0 ≤ w τ y
  le : ∀ τ y, w τ y ≤ K
  grad : ∀ τ y, ‖gradient (w τ) y‖ ≤ G
  deriv : ∀ s : ℝ, 0 < s → ∀ y,
    HasDerivAt (fun r : ℝ => w r.toNNReal y) (generator W (w s.toNNReal) y) s
  cont : ∀ y, Continuous (fun r : ℝ => w r.toNNReal y)
  zero : ∀ y, w 0 y = g y
  gen_bound : ∀ τ y, |generator W (w τ) y| ≤ C

theorem continuous_norm_gradient {g : Rd d → ℝ} (hg : ContDiff ℝ 1 g) :
    Continuous fun y => ‖gradient g y‖ :=
  (CutoffRigidity.Riemann.Witness.contDiff_gradient_rd (n := 0) hg (by norm_num)).continuous.norm

theorem hasCompactSupport_norm_gradient {g : Rd d → ℝ} (hgc : HasCompactSupport g) :
    HasCompactSupport fun y => ‖gradient g y‖ :=
  (hasCompactSupport_gradient hgc).comp_left (g := fun v : Rd d => ‖v‖) (by simp)

theorem exists_gradient_bound {g : Rd d → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ y, ‖gradient g y‖ ≤ G := by
  obtain ⟨C, hC⟩ := (continuous_norm_gradient (hg.of_le (by norm_cast))).bounded_above_of_compact_support
    (hasCompactSupport_norm_gradient hgc)
  exact ⟨max C 0, le_max_right _ _, fun y => by
    have := hC y
    rw [norm_norm] at this
    exact this.trans (le_max_left _ _)⟩

theorem norm_mgrad_rd (f : Rd d → ℝ) (x : Rd d) :
    ‖mgrad (Rd d) f x‖ = ‖gradient f x‖ := by
  have h := CutCur.carre_self_eq (Rd d) f x
  rw [CutoffRigidity.Riemann.Witness.carre_rd, real_inner_self_eq_norm_sq] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h.symm

open CutoffRigidity.Riemann in
theorem exists_backward {V : Rd d → ℝ} (hV : ContDiff ℝ 2 V) (hc : ConvexOn ℝ univ V)
    {g : Rd d → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (hg0 : ∀ y, 0 ≤ g y)
    {K : ℝ} (hK : ∀ y, g y ≤ K) {G : ℝ} (hG : ∀ y, ‖gradient g y‖ ≤ G) (n : ℕ) :
    ∃ (w : ℝ≥0 → Rd d → ℝ) (C : ℝ), IsBackward (Wm V n) g w K G C := by
  set W := Wm V n with hWdef
  have hW : ContDiff ℝ ∞ W := Wm_contDiff hV n
  have hW1 : ContDiff ℝ 1 W := hW.of_le (by norm_cast)
  have hW2 : ContDiff ℝ 2 W := hW.of_le (by norm_cast)
  have hW' : ContMDiff 𝓘(ℝ, Rd d) 𝓘(ℝ, ℝ) ∞ W := contMDiff_iff_contDiff.2 hW
  haveI : IsFiniteMeasure (gibbs W) := isFiniteMeasure_gibbs_Wm hV hc n
  have hμ := CutoffRigidity.Riemann.Witness.isWeightedVolume_gibbs W
  set Kk := Diff.Kk (Rd d) hW' hμ with hKk
  have hkc := Diff.kerCanonical_Kk (Rd d) hW' hμ
  have hP : IsEuclideanDiffusion W Kk := isEuclideanDiffusion_iff.2 hkc.dynkin
  have hρ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hCD : CD (Rd d) (1 / ((n : ℝ) + 1)) W :=
    (CutoffRigidity.Paper.cd_euclid_iff hW _).2 (Wm_hess hV hc n)
  have hBE := Diff.beStrong_of_CD (Rd d) hW' hμ hρ hCD
  have hg' : ContMDiff 𝓘(ℝ, Rd d) 𝓘(ℝ, ℝ) ∞ g := contMDiff_iff_contDiff.2 hg
  have hsm := hkc.smoothing g hg' hgc
  have hprob : ∀ (t : ℝ≥0) (y : Rd d), IsProbabilityMeasure (Kk t y) := fun t y =>
    (hkc.markov t).isProbabilityMeasure y
  have hint : ∀ (t : ℝ≥0) (y : Rd d), Integrable g (Kk t y) := fun t y => by
    haveI := hprob t y
    exact hg.continuous.integrable_of_hasCompactSupport hgc
  -- generator commutation in Euclidean form
  have hcomm : ∀ (τ : ℝ≥0) (y : Rd d),
      generator W (fun x => ∫ z, g z ∂Kk τ x) y = ∫ z, generator W g z ∂Kk τ y := by
    intro τ y
    have h1 := congrFun (hsm τ).2.1 y
    have e1 : mgenerator (Rd d) W (Diff.semi Kk τ g) y = generator W (fun x => ∫ z, g z ∂Kk τ x) y := by
      rw [CutoffRigidity.Riemann.Witness.mgenerator_rd (contMDiff_iff_contDiff.1 (hsm τ).1 |>.of_le (by norm_cast))]
      exact (generator_eq_langevinOp (contMDiff_iff_contDiff.1 (hsm τ).1 |>.of_le (by norm_cast))
        (V := W) y).symm
    have e2 : Diff.semi Kk τ (mgenerator (Rd d) W g) y = ∫ z, generator W g z ∂Kk τ y := by
      simp only [Diff.semi]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      rw [CutoffRigidity.Riemann.Witness.mgenerator_rd (hg.of_le (by norm_cast))]
      exact (generator_eq_langevinOp (hg.of_le (by norm_cast)) (V := W) z).symm
    rw [← e1, ← e2]; exact h1
  obtain ⟨C, hC⟩ := (hsm 0).2.2
  refine ⟨fun τ y => ∫ z, g z ∂Kk τ y, C, ?_⟩
  refine ⟨fun τ => contMDiff_iff_contDiff.1 (hsm τ).1, fun τ y => integral_nonneg hg0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro τ y
    haveI := hprob τ y
    have := integral_mono (hint τ y) (integrable_const K) (fun z => hK z)
    simpa using this
  · intro τ y
    have h1 := hBE ⟨g, hg', hgc⟩ τ y
    simp only [norm_mgrad_rd] at h1
    haveI := hprob τ y
    have hgi : Integrable (fun z => ‖gradient g z‖) (Kk τ y) :=
      (continuous_norm_gradient (hg.of_le (by norm_cast))).integrable_of_hasCompactSupport
        (hasCompactSupport_norm_gradient hgc)
    have hb : ∫ z, ‖gradient g z‖ ∂Kk τ y ≤ G := by
      have := integral_mono hgi (integrable_const G) (fun z => hG z)
      simpa using this
    have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
    have hexp : Real.exp (-(1 / ((n : ℝ) + 1)) * τ) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : (0 : ℝ) ≤ τ := τ.2
      nlinarith
    have hI0 : 0 ≤ ∫ z, ‖gradient g z‖ ∂Kk τ y := integral_nonneg fun z => norm_nonneg _
    calc _ ≤ Real.exp (-(1 / ((n : ℝ) + 1)) * τ) * ∫ z, ‖gradient g z‖ ∂Kk τ y := by
          exact h1
      _ ≤ 1 * G := mul_le_mul hexp hb hI0 zero_le_one
      _ = G := one_mul G
  · intro s hs y
    have h1 := hasDerivAt_semi hP hW1 hg hgc y hs
    have := hcomm s.toNNReal y
    rw [this]
    exact h1
  · intro y
    exact (continuous_semi_smooth hP hW1 hg hgc y).comp continuous_real_toNNReal
  · intro y
    simp [hKk, Diff.Kk_zero, Kernel.id_apply, integral_dirac]
  · intro τ y
    have := (hC τ y).2
    rw [CutoffRigidity.Riemann.Witness.mgenerator_rd
      (contMDiff_iff_contDiff.1 (hsm τ).1 |>.of_le (by norm_cast)),
      ← generator_eq_langevinOp (contMDiff_iff_contDiff.1 (hsm τ).1 |>.of_le (by norm_cast))] at this
    exact this


theorem gradient_const_sub (c : ℝ) (f : Rd d → ℝ) (x : Rd d) :
    gradient (fun y => c - f y) x = - gradient f x := by
  unfold gradient
  rw [fderiv_const_sub, map_neg]

theorem laplacian_const_sub (c : ℝ) (f : Rd d → ℝ) (x : Rd d) :
    laplacian (fun y => c - f y) x = - laplacian f x := by
  unfold laplacian
  have : fderiv ℝ (fun y => c - f y) = fun y => - fderiv ℝ f y := by
    funext y; exact fderiv_const_sub (𝕜 := ℝ) (f := f) (x := y) c
  rw [this, fderiv_fun_neg]
  simp [Finset.sum_neg_distrib]

theorem generator_const_sub (V : Rd d → ℝ) (c : ℝ) (f : Rd d → ℝ) (x : Rd d) :
    generator V (fun y => c - f y) x = - generator V f x := by
  unfold generator
  rw [laplacian_const_sub, gradient_const_sub]
  simp; ring

theorem IsBackward.const_sub {W g : Rd d → ℝ} {w : ℝ≥0 → Rd d → ℝ} {K G C : ℝ}
    (h : IsBackward W g w K G C) {c : ℝ} (hc : K ≤ c) :
    IsBackward W (fun y => c - g y) (fun τ y => c - w τ y) c G C where
  smooth τ := contDiff_const.sub (h.smooth τ)
  nonneg τ y := sub_nonneg.2 ((h.le τ y).trans hc)
  le τ y := by linarith [h.nonneg τ y]
  grad τ y := by
    rw [gradient_const_sub, norm_neg]; exact h.grad τ y
  deriv s hs y := by
    have := (h.deriv s hs y).const_sub c
    rw [generator_const_sub]; exact this
  cont y := continuous_const.sub (h.cont y)
  zero y := by simp [h.zero y]
  gen_bound τ y := by
    rw [generator_const_sub, abs_neg]; exact h.gen_bound τ y

end C2U

end CutCur
