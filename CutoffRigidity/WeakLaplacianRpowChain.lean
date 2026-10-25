module
public import CutoffRigidity.WeakLaplacianLogChain

/-! # The actual weak real-power chain at C¹ regularity

For a positive C¹ weak-generator function f and a real exponent α, the
compact C¹ test α f^(α-1) ψ is justified by the same genuine H¹
mollification used for the logarithm. This yields the classical identity
L(f^α) = α f^(α-1) Lf + α(α-1) f^(α-2) |∇f|² in the full generator graph.
-/
public section
namespace CutoffRigidity
open MeasureTheory
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem gradient_rpow_of_c1 {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (hpos : ∀ x, 0 < f x) (α : ℝ) (x : E) :
    gradient (fun y => f y ^ α) x = (α * f x ^ (α - 1)) • gradient f x := by
  have he := ((hf.differentiable one_ne_zero x).hasFDerivAt.rpow_const (p := α)
    (Or.inl (hpos x).ne')).fderiv
  simp only [gradient, he, map_smul]

theorem norm_gradient_rpow_of_c1 {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (hpos : ∀ x, 0 < f x) (α : ℝ) (x : E) :
    ‖gradient (fun y => f y ^ α) x‖ = |α| * f x ^ (α - 1) * ‖gradient f x‖ := by
  rw [gradient_rpow_of_c1 hf hpos, norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos (hpos x) _)]

/-- Real powers of a quantity confined to a positive interval are bounded
by the sum of the two endpoint powers, whatever the sign of the exponent. -/
theorem rpow_le_add_of_mem_Icc {m M y : ℝ} (hm : 0 < m) (hmy : m ≤ y) (hyM : y ≤ M) (q : ℝ) :
    y ^ q ≤ m ^ q + M ^ q := by
  have hm0 := Real.rpow_nonneg hm.le q
  have hM0 := Real.rpow_nonneg (hm.le.trans (hmy.trans hyM)) q
  rcases le_total 0 q with hq | hq
  · exact (Real.rpow_le_rpow (hm.le.trans hmy) hyM hq).trans (le_add_of_nonneg_left hm0)
  · exact (Real.rpow_le_rpow_of_nonpos hm hmy hq).trans (le_add_of_nonneg_right hM0)

set_option maxHeartbeats 600000 in
/-- True distributional real-power chain, using the compact C¹ test
α f^(α-1) ψ rather than a C² representative of f. -/
theorem weak_laplacian_rpow_chain {f F : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hpos : ∀ x, 0 < f x) (α : ℝ)
    (hFloc : ∀ K : Set E, IsCompact K → MemLp F 2 ((volume : Measure E).restrict K))
    (hLap : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      (∫ x, f x * euclideanLaplacian ψ x) = ∫ x, F x * ψ x)
    (ψ : E → ℝ) (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
    (∫ x, f x ^ α * euclideanLaplacian ψ x) =
      ∫ x, (α * f x ^ (α - 1) * F x +
        α * (α - 1) * f x ^ (α - 2) * ‖gradient f x‖ ^ 2) * ψ x := by
  let w : E → ℝ := fun x => α * f x ^ (α - 1)
  let A (x : E) := w x * inner ℝ (gradient f x) (gradient ψ x)
  let B (x : E) := α * (α - 1) * f x ^ (α - 2) * ‖gradient f x‖ ^ 2 * ψ x
  let C (x : E) := F x * (w x * ψ x)
  have hw : ContDiff ℝ 1 w := contDiff_const.mul (hf.rpow_const_of_ne (fun x => (hpos x).ne'))
  have hP2 : Continuous (fun x => f x ^ (α - 2)) :=
    hf.continuous.rpow_const (fun x => Or.inl (hpos x).ne')
  have hGf := continuous_gradient_of_c1 hf
  have hGψ := continuous_gradient_of_c1 (hψ.of_le (by norm_num))
  have hAcont : Continuous A := hw.continuous.mul (hGf.inner hGψ)
  have hAoff : ∀ x ∉ tsupport ψ, A x = 0 := by
    intro x hx
    have hgψ : gradient ψ x = 0 := gradient_eq_zero_off_closed_support (isClosed_tsupport ψ)
      (fun y hy => image_eq_zero_of_notMem_tsupport hy) hx
    simp only [A, hgψ, inner_zero_right, mul_zero]
  have hA : Integrable A volume := hAcont.integrable_of_hasCompactSupport
    (compactSupport_of_eq_zero_off_compact hψc hAoff)
  have hBcont : Continuous B :=
    ((continuous_const.mul hP2).mul (hGf.norm.pow 2)).mul hψ.continuous
  have hBc : HasCompactSupport B := by
    simpa only [B, Pi.mul_def] using
      hψc.mul_left (f := fun x => α * (α - 1) * f x ^ (α - 2) * ‖gradient f x‖ ^ 2)
  have hB : Integrable B volume := hBcont.integrable_of_hasCompactSupport hBc
  have hη : ContDiff ℝ 1 (fun x => w x * ψ x) := hw.mul (hψ.of_le (by norm_num))
  have hηc : HasCompactSupport (fun x => w x * ψ x) := by
    simpa only [Pi.mul_def] using hψc.mul_left (f := w)
  have hC : Integrable C volume := locallyL2_mul_compact_continuous_integrable hFloc hη.continuous hηc
  have hE := weak_laplacian_compact_c1_test hf hFloc hLap hη hηc
  have hgw (x : E) : gradient w x = (α * ((α - 1) * f x ^ (α - 1 - 1))) • gradient f x := by
    have he : gradient w x = α • gradient (fun y => f y ^ (α - 1)) x := by
      simp only [w, gradient]
      rw [fderiv_const_mul ((hf.rpow_const_of_ne (fun x => (hpos x).ne')).differentiable
        one_ne_zero x), map_smul]
    rw [he, gradient_rpow_of_c1 hf hpos, smul_smul]
  have hpoint (x : E) : inner ℝ (gradient f x) (gradient (fun y => w y * ψ y) x) = A x + B x := by
    rw [gradient_cutoff_mul (hw.differentiable one_ne_zero) (hψ.differentiable (by norm_num)),
      hgw, inner_add_right, inner_smul_right, inner_smul_right,
      inner_smul_right, real_inner_self_eq_norm_sq]
    dsimp only [A, B]
    have he : α - 1 - 1 = α - 2 := by ring
    rw [he]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), integral_add hA hB] at hE
  change (∫ x, A x) + (∫ x, B x) = -(∫ x, C x) at hE
  have hpowC : ContDiff ℝ 1 (fun x => f x ^ α) := hf.rpow_const_of_ne (fun x => (hpos x).ne')
  have hIBP := c1_integral_mul_laplacian_compact_test hpowC hψ hψc
  have hpowp (x : E) : inner ℝ (gradient (fun y => f y ^ α) x) (gradient ψ x) = A x := by
    rw [gradient_rpow_of_c1 hf hpos, real_inner_smul_left]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpowp)] at hIBP
  have hrhs (x : E) : (α * f x ^ (α - 1) * F x +
      α * (α - 1) * f x ^ (α - 2) * ‖gradient f x‖ ^ 2) * ψ x = C x + B x := by
    dsimp only [C, B, w]
    ring
  rw [hIBP, integral_congr_ae (Filter.Eventually.of_forall hrhs), integral_add hC hB]
  linarith only [hE]

/-- The drift cancels through the actual C¹ real-power gradient rule. -/
theorem weak_langevin_rpow_chain {V f h : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hpos : ∀ x, 0 < f x) (α : ℝ)
    (hFloc : ∀ K : Set E, IsCompact K →
      MemLp (fun x => h x + inner ℝ (gradient V x) (gradient f x)) 2
        ((volume : Measure E).restrict K))
    (hLap : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      (∫ x, f x * euclideanLaplacian ψ x) =
      ∫ x, (h x + inner ℝ (gradient V x) (gradient f x)) * ψ x)
    (ψ : E → ℝ) (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
    (∫ x, f x ^ α * euclideanLaplacian ψ x) =
      ∫ x, ψ x * ((α * f x ^ (α - 1) * h x +
        α * (α - 1) * f x ^ (α - 2) * ‖gradient f x‖ ^ 2) +
        inner ℝ (gradient V x) (gradient (fun y => f y ^ α) x)) := by
  have he := weak_laplacian_rpow_chain hf hpos α hFloc hLap ψ hψ hψc
  refine he.trans (integral_congr_ae (Filter.Eventually.of_forall ?_))
  intro x
  dsimp only
  rw [gradient_rpow_of_c1 hf hpos, inner_smul_right]
  ring

set_option maxHeartbeats 700000 in
/-- Uniformly positive bounded C¹ weak-generator functions have every
real power in the full self-adjoint generator domain. All L² memberships
are derived from the displayed actual pointwise bounds. -/
theorem bounded_c1_weak_langevin_rpow_mem_operatorGraph
    {V f h : E → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hf : ContDiff ℝ 1 f) (hh : Measurable h) (α : ℝ)
    (m M G H : ℝ) (hm : 0 < m) (hfloor : ∀ x, m ≤ f x)
    (hbound : ∀ x, f x ≤ M) (hgradBound : ∀ x, ‖gradient f x‖ ≤ G)
    (hhBound : ∀ x, |h x| ≤ H)
    (hweak : ∀ ψ : E → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      (∫ x, f x * euclideanLaplacian ψ x) =
      ∫ x, (h x + inner ℝ (gradient V x) (gradient f x)) * ψ x) :
    ∃ (hpow : MemLp (fun x => f x ^ α) 2 (gibbsMeasure volume V))
      (hR : MemLp (fun x => α * f x ^ (α - 1) * h x +
        α * (α - 1) * f x ^ (α - 2) * ‖gradient f x‖ ^ 2) 2 (gibbsMeasure volume V)),
      (hpow.toLp (fun x => f x ^ α),
        -hR.toLp (fun x => α * f x ^ (α - 1) * h x +
          α * (α - 1) * f x ^ (α - 2) * ‖gradient f x‖ ^ 2)) ∈
          (gibbsPositiveGenerator hV hp).graph := by
  let := hp
  have hpos (x : E) : 0 < f x := hm.trans_le (hfloor x)
  have hG : 0 ≤ G := (norm_nonneg _).trans (hgradBound 0)
  have hH : 0 ≤ H := (abs_nonneg _).trans (hhBound 0)
  have hpowC : ContDiff ℝ 1 (fun x => f x ^ α) := hf.rpow_const_of_ne (fun x => (hpos x).ne')
  have hP (q : ℝ) (x : E) : |f x ^ q| ≤ m ^ q + M ^ q := by
    rw [abs_of_pos (Real.rpow_pos_of_pos (hpos x) q)]
    exact rpow_le_add_of_mem_Icc hm (hfloor x) (hbound x) q
  have hM : 0 < M := (hpos 0).trans_le (hbound 0)
  have hPn (q : ℝ) : 0 ≤ |α| * (m ^ q + M ^ q) :=
    mul_nonneg (abs_nonneg _) (add_nonneg (Real.rpow_nonneg hm.le q) (Real.rpow_nonneg hM.le q))
  have hPn' (q : ℝ) : 0 ≤ |α * (α - 1)| * (m ^ q + M ^ q) :=
    mul_nonneg (abs_nonneg _) (add_nonneg (Real.rpow_nonneg hm.le q) (Real.rpow_nonneg hM.le q))
  have hPc (q : ℝ) : Continuous (fun x => f x ^ q) :=
    hf.continuous.rpow_const (fun x => Or.inl (hpos x).ne')
  have hpowLp : MemLp (fun x => f x ^ α) 2 (gibbsMeasure volume V) :=
    MemLp.of_bound hpowC.continuous.aestronglyMeasurable (m ^ α + M ^ α)
      (Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hP α x))
  have hpowGradLp : MemLp (gradient (fun x => f x ^ α)) 2 (gibbsMeasure volume V) := by
    apply MemLp.of_bound (continuous_gradient_of_c1 hpowC).aestronglyMeasurable
      (|α| * (m ^ (α - 1) + M ^ (α - 1)) * G)
    apply Filter.Eventually.of_forall
    intro x
    rw [norm_gradient_rpow_of_c1 hf hpos]
    have h1 := (le_abs_self _).trans (hP (α - 1) x)
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) (hgradBound x)
      (norm_nonneg _) (hPn (α - 1))
  let R : E → ℝ := fun x => α * f x ^ (α - 1) * h x +
    α * (α - 1) * f x ^ (α - 2) * ‖gradient f x‖ ^ 2
  have hRmeas : Measurable R :=
    (((hPc (α - 1)).measurable.const_mul α).mul hh).add
      (((hPc (α - 2)).measurable.const_mul (α * (α - 1))).mul
        ((continuous_gradient_of_c1 hf).norm.pow 2).measurable)
  have hRbound (x : E) : ‖R x‖ ≤ |α| * (m ^ (α - 1) + M ^ (α - 1)) * H +
      |α * (α - 1)| * (m ^ (α - 2) + M ^ (α - 2)) * G ^ 2 := by
    rw [Real.norm_eq_abs]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hP _ x) (abs_nonneg _)) (hhBound x)
        (abs_nonneg _) (hPn _)
    · rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ‖gradient f x‖)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hP _ x) (abs_nonneg _))
        (pow_le_pow_left₀ (norm_nonneg _) (hgradBound x) 2) (sq_nonneg _) (hPn' _)
  have hRLp : MemLp R 2 (gibbsMeasure volume V) :=
    MemLp.of_bound hRmeas.aestronglyMeasurable _ (Filter.Eventually.of_forall hRbound)
  have hhloc : ∀ K : Set E, IsCompact K → MemLp h 2 ((volume : Measure E).restrict K) := by
    intro K hK
    have : IsFiniteMeasure ((volume : Measure E).restrict K) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using (hK.measure_lt_top (μ := (volume : Measure E)))⟩
    exact MemLp.of_bound hh.aestronglyMeasurable H
      (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hhBound x))
  have hFloc : ∀ K : Set E, IsCompact K →
      MemLp (fun x => h x + inner ℝ (gradient V x) (gradient f x)) 2
        ((volume : Measure E).restrict K) := by
    intro K hK
    exact (hhloc K hK).add (continuous_memLp_two_restrict_compact
      ((continuous_gradient_of_c1 (hV.of_le (by norm_num))).inner (continuous_gradient_of_c1 hf)) hK)
  refine ⟨hpowLp, hRLp, ?_⟩
  apply c1_weak_langevin_mem_operatorGraph hV hp ρ hρ hHess hpowC hpowLp hpowGradLp hRLp
  intro ψ hψ hψc
  exact weak_langevin_rpow_chain hf hpos α hFloc hweak ψ hψ hψc

end CutoffRigidity
