module

public import CutoffRigidity.Paper.GapBridge
public import CutoffRigidity.Paper.FisherBridgeWeak
public import CutoffRigidity.AffineEigenfunctionOrthogonality
public import CutoffRigidity.ConvexInteraction

/-! # Upper bound for the variational spectral gap by an affine eigenfunction

If the affine function `⟨a, x⟩` is an eigenfunction of the Langevin generator with
eigenvalue `ρ`, then the optimal Poincaré constant over smooth compactly supported test
functions is at most `ρ`: the smooth cutoffs `χₙ ⟨a, ·⟩` have Rayleigh quotients tending
to `ρ`.
-/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem gradient_cutoff_mul_inner {χ : E → ℝ} (hχ : Differentiable ℝ χ) (a x : E) :
    gradient (fun y => χ y * inner ℝ a y) x = χ x • a + inner ℝ a x • gradient χ x := by
  have hs : DifferentiableAt ℝ (fun y : E => inner ℝ a y) x :=
    (innerSL ℝ a).differentiableAt
  have hd := fderiv_mul (hχ x) hs
  unfold gradient
  rw [show (fun y : E => χ y * inner ℝ a y) = χ * fun y => inner ℝ a y from rfl, hd, map_add, map_smul, map_smul]
  have h1 : fderiv ℝ (fun y : E => inner ℝ a y) x = innerSL ℝ a := (innerSL ℝ a).fderiv
  rw [h1]
  have h2 : (InnerProductSpace.toDual ℝ E).symm (innerSL ℝ a) = a :=
    (InnerProductSpace.toDual ℝ E).symm_apply_eq.mpr rfl
  rw [h2]

/-- The variational gap is at most the eigenvalue of an affine eigenfunction, and the set of
Rayleigh quotients is nonempty. -/
theorem spectralGap_le_of_affine_eigenfunction_aux {V : CutCur.Rd d → ℝ} (hV : Differentiable ℝ V)
    (a : E) (ha : a ≠ 0) (ρ : ℝ) (hρ : 0 < ρ)
    (heigen : ∀ x : E, langevinDifferentialOperator V (fun y => inner ℝ a y + 0) x =
      -ρ * (inner ℝ a x + 0))
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) :
    {r : ℝ | ∃ f : CutCur.Rd d → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
        0 < variance f (CutCur.gibbs V) ∧ r = (∫ x, ‖gradient f x‖ ^ 2 ∂CutCur.gibbs V) /
          variance f (CutCur.gibbs V)}.Nonempty ∧ CutCur.spectralGap V ≤ ρ := by
  set μ := gibbsMeasure volume V with hμ
  have hmem : MemLp (fun x : E => inner ℝ a x) 2 μ := by
    simpa using affine_eigenfunction_memLp V hV a ha 0 ρ hρ heigen hp
  have hmean : ∫ x, inner ℝ a x ∂μ = 0 := by
    simpa using affine_eigenfunction_mean_zero V hV a ha 0 ρ hρ heigen hp
  have hsec : ∫ x, inner ℝ a x ^ 2 ∂μ = ‖a‖ ^ 2 / ρ := by
    simpa using affine_eigenfunction_second_moment V hV a ha 0 ρ hρ heigen hp
  obtain ⟨C, hC0, χ, hχ, hχc, hχb, hχ1, hχg⟩ := exists_smooth_cutoff_exhaustion_infty (d := d)
  have hsmooth : ContDiff ℝ ∞ (fun y : E => inner ℝ a y) := (innerSL ℝ a).contDiff
  let f : ℕ → E → ℝ := fun n y => χ n y * inner ℝ a y
  have hfsmooth : ∀ n, ContDiff ℝ ∞ (f n) := fun n => (hχ n).mul hsmooth
  have hfc : ∀ n, HasCompactSupport (f n) := fun n => (hχc n).mul_right
  have hfg : ∀ n x, gradient (f n) x = χ n x • a + inner ℝ a x • gradient (χ n) x :=
    fun n x => gradient_cutoff_mul_inner ((hχ n).differentiable (by simp)) a x
  have hint1 : Integrable (fun x : E => inner ℝ a x) μ := hmem.integrable (by norm_num)
  have hint2 : Integrable (fun x : E => inner ℝ a x ^ 2) μ := hmem.integrable_sq
  have hfm : ∀ n, MemLp (f n) 2 μ := fun n => by
    refine hmem.of_le_mul (c := 1) ((hfsmooth n).continuous.aestronglyMeasurable) ?_
    refine Eventually.of_forall fun x => ?_
    simp only [f, norm_mul, one_mul, Real.norm_eq_abs]
    calc |χ n x| * |inner ℝ a x| ≤ 1 * |inner ℝ a x| :=
          mul_le_mul_of_nonneg_right (by rw [abs_of_nonneg (hχb n x).1]; exact (hχb n x).2)
            (abs_nonneg _)
      _ = ‖inner ℝ a x‖ := by rw [one_mul, Real.norm_eq_abs]
  -- the three convergences
  have hT1 : Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, inner ℝ a x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖inner ℝ a x‖)
      (fun n => (hfsmooth n).continuous.aestronglyMeasurable) hint1.norm
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · simp only [f, norm_mul, Real.norm_eq_abs]
      calc |χ n x| * |inner ℝ a x| ≤ 1 * |inner ℝ a x| :=
            mul_le_mul_of_nonneg_right (by rw [abs_of_nonneg (hχb n x).1]; exact (hχb n x).2)
              (abs_nonneg _)
        _ = ‖inner ℝ a x‖ := by rw [one_mul, Real.norm_eq_abs]
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hχ1 x] with n hn
      simp [f, hn]
  have hT2 : Tendsto (fun n => ∫ x, f n x ^ 2 ∂μ) atTop (𝓝 (∫ x, inner ℝ a x ^ 2 ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => inner ℝ a x ^ 2)
      (fun n => ((hfsmooth n).continuous.pow 2).aestronglyMeasurable) hint2
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · simp only [f, mul_pow, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      calc χ n x ^ 2 * inner ℝ a x ^ 2 ≤ 1 * inner ℝ a x ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
            nlinarith [(hχb n x).1, (hχb n x).2]
        _ = _ := one_mul _
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hχ1 x] with n hn
      simp [f, hn]
  have hgc : ∀ n, Continuous (gradient (f n)) := fun n =>
    continuous_gradient_of_c1 ((hfsmooth n).of_le (by simp))
  have hmeas : ∀ n, AEStronglyMeasurable (fun x => ‖gradient (f n) x‖ ^ 2) μ := fun n =>
    ((hgc n).norm.pow 2).aestronglyMeasurable
  have hbound_int : Integrable (fun x : E => 2 * ‖a‖ ^ 2 + 2 * C ^ 2 * inner ℝ a x ^ 2) μ :=
    (integrable_const _).add (hint2.const_mul _)
  have hT3 : Tendsto (fun n => ∫ x, ‖gradient (f n) x‖ ^ 2 ∂μ) atTop (𝓝 (∫ x, ‖a‖ ^ 2 ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x : E => 2 * ‖a‖ ^ 2 + 2 * C ^ 2 * inner ℝ a x ^ 2) hmeas hbound_int
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hfg]
      have h1 : ‖χ n x • a + inner ℝ a x • gradient (χ n) x‖ ≤ ‖a‖ + |inner ℝ a x| * C := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχb n x).1]
          exact mul_le_of_le_one_left (norm_nonneg _) (hχb n x).2
        · rw [norm_smul, Real.norm_eq_abs]
          refine mul_le_mul_of_nonneg_left ((hχg n x).trans ?_) (abs_nonneg _)
          exact div_le_self hC0 (by linarith [Nat.cast_nonneg (α := ℝ) n])
      have h2 : (‖a‖ + |inner ℝ a x| * C) ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * C ^ 2 * inner ℝ a x ^ 2 := by
        have : |inner ℝ a x| ^ 2 = inner ℝ a x ^ 2 := sq_abs _
        nlinarith [sq_nonneg (‖a‖ - |inner ℝ a x| * C)]
      exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
    · have hg0 : Tendsto (fun n : ℕ => gradient (χ n) x) atTop (𝓝 0) := by
        refine squeeze_zero_norm (fun n => hχg n x) ?_
        exact tendsto_const_nhds.div_atTop
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      have h3 : Tendsto (fun n : ℕ => a + inner ℝ a x • gradient (χ n) x) atTop (𝓝 a) := by
        simpa using (tendsto_const_nhds (x := a)).add
          ((tendsto_const_nhds (x := inner ℝ a x)).smul hg0)
      have hcl : Tendsto (fun n => gradient (f n) x) atTop (𝓝 a) := by
        refine h3.congr' ?_
        filter_upwards [hχ1 x] with n hn
        rw [hfg, hn, one_smul]
      exact ((continuous_norm.tendsto a).comp hcl).pow 2
  have hvar : ∀ n, variance (f n) μ = ∫ x, f n x ^ 2 ∂μ - (∫ x, f n x ∂μ) ^ 2 := fun n => by
    simpa using variance_eq_sub (hfm n)
  have hD : Tendsto (fun n => variance (f n) μ) atTop (𝓝 (‖a‖ ^ 2 / ρ)) := by
    have := hT2.sub (hT1.pow 2)
    rw [hmean, hsec] at this
    simpa [hvar] using this
  have hN : Tendsto (fun n => ∫ x, ‖gradient (f n) x‖ ^ 2 ∂μ) atTop (𝓝 (‖a‖ ^ 2)) := by
    simpa using hT3
  have hapos : 0 < ‖a‖ ^ 2 := by positivity
  have hratio := hN.div hD (by positivity)
  have hlim : ‖a‖ ^ 2 / (‖a‖ ^ 2 / ρ) = ρ := by field_simp
  rw [hlim] at hratio
  have hbdd : BddBelow {r : ℝ | ∃ f : CutCur.Rd d → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
        0 < variance f (CutCur.gibbs V) ∧ r = (∫ x, ‖gradient f x‖ ^ 2 ∂CutCur.gibbs V) /
          variance f (CutCur.gibbs V)} := by
    refine ⟨0, ?_⟩
    rintro r ⟨g, -, -, hg, rfl⟩
    exact div_nonneg (integral_nonneg fun x => by positivity) hg.le
  have hmemR : ∀ n, 0 < variance (f n) μ → (∫ x, ‖gradient (f n) x‖ ^ 2 ∂μ) / variance (f n) μ ∈
      {r : ℝ | ∃ f : CutCur.Rd d → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
        0 < variance f (CutCur.gibbs V) ∧ r = (∫ x, ‖gradient f x‖ ^ 2 ∂CutCur.gibbs V) /
          variance f (CutCur.gibbs V)} := fun n hn => ⟨f n, hfsmooth n, hfc n, hn, rfl⟩
  have hpos := (hD.eventually (lt_mem_nhds (by positivity : 0 < ‖a‖ ^ 2 / ρ))).exists
  refine ⟨⟨_, hmemR _ hpos.choose_spec⟩, ?_⟩
  apply le_of_forall_pos_lt_add
  intro ε hε
  have hev := (hD.eventually (lt_mem_nhds (by positivity : 0 < ‖a‖ ^ 2 / ρ))).and
    (hratio.eventually (gt_mem_nhds (by linarith : ρ < ρ + ε)))
  obtain ⟨n, hn1, hn2⟩ := hev.exists
  exact (csInf_le hbdd (hmemR n hn1)).trans_lt hn2

/-- Under a Hessian lower bound `ρ` with the library gap equal to `ρ`, an affine eigenfunction
with eigenvalue `ρ` shows that the variational gap is `ρ`. -/
theorem spectralGap_eq_of_affine_eigenfunction {V : CutCur.Rd d → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) (hd : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hgap : gibbsSpectralGap hV hp = ρ)
    (a : E) (ha : a ≠ 0)
    (heigen : ∀ x : E, langevinDifferentialOperator V (fun y => inner ℝ a y + 0) x =
      -ρ * (inner ℝ a x + 0)) : CutCur.spectralGap V = ρ := by
  obtain ⟨hne, hle⟩ := spectralGap_le_of_affine_eigenfunction_aux
    (hV.differentiable (by norm_num)) a ha ρ hρ heigen hp
  refine le_antisymm hle ?_
  rw [CutCur.spectralGap]
  refine le_csInf hne ?_
  rintro r ⟨g, hg, hgc, hvar, rfl⟩
  rw [le_div_iff₀ hvar, ← hgap]
  exact gibbsSpectralGap_mul_variance_le hV hp hd _ (hgap ▸ hρ) (hgap ▸ hHess) hg hgc

end CutoffRigidity.Paper
