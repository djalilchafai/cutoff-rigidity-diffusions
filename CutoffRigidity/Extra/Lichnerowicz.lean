module

public import CutoffRigidity.Paper.GapBridge
public import CutoffRigidity.Paper.GapUpper
public import CutoffRigidity.Paper.GaussianFactorization

/-! # Euclidean Lichnerowicz / Bakry–Émery bound `λ₁ ≥ ρ` (manuscript (1.x), eq:Lichne) -/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)


theorem gradient_cutoff_mul_inner_add {χ : E → ℝ} (hχ : Differentiable ℝ χ) (a : E) (b : ℝ) (x : E) :
    gradient (fun y => χ y * (inner ℝ a y + b)) x =
      χ x • a + (inner ℝ a x + b) • gradient χ x := by
  have hs : DifferentiableAt ℝ (fun y : E => inner ℝ a y + b) x :=
    (innerSL ℝ a).differentiableAt.add_const b
  have hd := fderiv_mul (hχ x) hs
  unfold gradient
  rw [show (fun y : E => χ y * (inner ℝ a y + b)) = χ * fun y => inner ℝ a y + b from rfl, hd,
    map_add, map_smul, map_smul]
  have h1 : fderiv ℝ (fun y : E => inner ℝ a y + b) x = innerSL ℝ a := by
    rw [fderiv_add_const]; exact (innerSL ℝ a).fderiv
  rw [h1]
  have h2 : (InnerProductSpace.toDual ℝ E).symm (innerSL ℝ a) = a :=
    (InnerProductSpace.toDual ℝ E).symm_apply_eq.mpr rfl
  rw [h2]

theorem spectralGap_le_of_affine_eigenfunction_aux_shift {V : CutCur.Rd d → ℝ} (hV : Differentiable ℝ V)
    (a : E) (ha : a ≠ 0) (b ρ : ℝ) (hρ : 0 < ρ)
    (heigen : ∀ x : E, langevinDifferentialOperator V (fun y => inner ℝ a y + b) x =
      -ρ * (inner ℝ a x + b))
    (hp : IsProbabilityMeasure (gibbsMeasure volume V)) :
    {r : ℝ | ∃ f : CutCur.Rd d → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
        0 < variance f (CutCur.gibbs V) ∧ r = (∫ x, ‖gradient f x‖ ^ 2 ∂CutCur.gibbs V) /
          variance f (CutCur.gibbs V)}.Nonempty ∧ CutCur.spectralGap V ≤ ρ := by
  set μ := gibbsMeasure volume V with hμ
  have hmem : MemLp (fun x : E => (inner ℝ a x + b)) 2 μ := by
    exact affine_eigenfunction_memLp V hV a ha b ρ hρ heigen hp
  have hmean : ∫ x, (inner ℝ a x + b) ∂μ = 0 := by
    exact affine_eigenfunction_mean_zero V hV a ha b ρ hρ heigen hp
  have hsec : ∫ x, (inner ℝ a x + b) ^ 2 ∂μ = ‖a‖ ^ 2 / ρ := by
    exact affine_eigenfunction_second_moment V hV a ha b ρ hρ heigen hp
  obtain ⟨C, hC0, χ, hχ, hχc, hχb, hχ1, hχg⟩ := exists_smooth_cutoff_exhaustion_infty (d := d)
  have hsmooth : ContDiff ℝ ∞ (fun y : E => (inner ℝ a y + b)) := (innerSL ℝ a).contDiff.add contDiff_const
  let f : ℕ → E → ℝ := fun n y => χ n y * (inner ℝ a y + b)
  have hfsmooth : ∀ n, ContDiff ℝ ∞ (f n) := fun n => (hχ n).mul hsmooth
  have hfc : ∀ n, HasCompactSupport (f n) := fun n => (hχc n).mul_right
  have hfg : ∀ n x, gradient (f n) x = χ n x • a + (inner ℝ a x + b) • gradient (χ n) x :=
    fun n x => gradient_cutoff_mul_inner_add ((hχ n).differentiable (by simp)) a b x
  have hint1 : Integrable (fun x : E => (inner ℝ a x + b)) μ := hmem.integrable (by norm_num)
  have hint2 : Integrable (fun x : E => (inner ℝ a x + b) ^ 2) μ := hmem.integrable_sq
  have hfm : ∀ n, MemLp (f n) 2 μ := fun n => by
    refine hmem.of_le_mul (c := 1) ((hfsmooth n).continuous.aestronglyMeasurable) ?_
    refine Eventually.of_forall fun x => ?_
    simp only [f, norm_mul, one_mul, Real.norm_eq_abs]
    calc |χ n x| * |(inner ℝ a x + b)| ≤ 1 * |(inner ℝ a x + b)| :=
          mul_le_mul_of_nonneg_right (by rw [abs_of_nonneg (hχb n x).1]; exact (hχb n x).2)
            (abs_nonneg _)
      _ = ‖(inner ℝ a x + b)‖ := by rw [one_mul, Real.norm_eq_abs]
  -- the three convergences
  have hT1 : Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, (inner ℝ a x + b) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖(inner ℝ a x + b)‖)
      (fun n => (hfsmooth n).continuous.aestronglyMeasurable) hint1.norm
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · simp only [f, norm_mul, Real.norm_eq_abs]
      calc |χ n x| * |(inner ℝ a x + b)| ≤ 1 * |(inner ℝ a x + b)| :=
            mul_le_mul_of_nonneg_right (by rw [abs_of_nonneg (hχb n x).1]; exact (hχb n x).2)
              (abs_nonneg _)
        _ = ‖(inner ℝ a x + b)‖ := by rw [one_mul, Real.norm_eq_abs]
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hχ1 x] with n hn
      simp [f, hn]
  have hT2 : Tendsto (fun n => ∫ x, f n x ^ 2 ∂μ) atTop (𝓝 (∫ x, (inner ℝ a x + b) ^ 2 ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => (inner ℝ a x + b) ^ 2)
      (fun n => ((hfsmooth n).continuous.pow 2).aestronglyMeasurable) hint2
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · simp only [f, mul_pow, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      calc χ n x ^ 2 * (inner ℝ a x + b) ^ 2 ≤ 1 * (inner ℝ a x + b) ^ 2 := by
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
  have hbound_int : Integrable (fun x : E => 2 * ‖a‖ ^ 2 + 2 * C ^ 2 * (inner ℝ a x + b) ^ 2) μ :=
    (integrable_const _).add (hint2.const_mul _)
  have hT3 : Tendsto (fun n => ∫ x, ‖gradient (f n) x‖ ^ 2 ∂μ) atTop (𝓝 (∫ x, ‖a‖ ^ 2 ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x : E => 2 * ‖a‖ ^ 2 + 2 * C ^ 2 * (inner ℝ a x + b) ^ 2) hmeas hbound_int
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hfg]
      have h1 : ‖χ n x • a + (inner ℝ a x + b) • gradient (χ n) x‖ ≤ ‖a‖ + |(inner ℝ a x + b)| * C := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχb n x).1]
          exact mul_le_of_le_one_left (norm_nonneg _) (hχb n x).2
        · rw [norm_smul, Real.norm_eq_abs]
          refine mul_le_mul_of_nonneg_left ((hχg n x).trans ?_) (abs_nonneg _)
          exact div_le_self hC0 (by linarith [Nat.cast_nonneg (α := ℝ) n])
      have h2 : (‖a‖ + |(inner ℝ a x + b)| * C) ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * C ^ 2 * (inner ℝ a x + b) ^ 2 := by
        have : |(inner ℝ a x + b)| ^ 2 = (inner ℝ a x + b) ^ 2 := sq_abs _
        nlinarith [sq_nonneg (‖a‖ - |(inner ℝ a x + b)| * C)]
      exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
    · have hg0 : Tendsto (fun n : ℕ => gradient (χ n) x) atTop (𝓝 0) := by
        refine squeeze_zero_norm (fun n => hχg n x) ?_
        exact tendsto_const_nhds.div_atTop
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      have h3 : Tendsto (fun n : ℕ => a + (inner ℝ a x + b) • gradient (χ n) x) atTop (𝓝 a) := by
        simpa using (tendsto_const_nhds (x := a)).add
          ((tendsto_const_nhds (x := (inner ℝ a x + b))).smul hg0)
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



theorem hessian_quad (u : E) (ρ m : ℝ) (x z : E) :
    fderiv ℝ (fderiv ℝ (fun y : E => ρ / 2 * (inner ℝ u y - m) ^ 2)) x z z = ρ * inner ℝ u z ^ 2 := by
  have hℓ : ∀ y : E, HasFDerivAt (fun y : E => inner ℝ u y - m) (innerSL ℝ u) y := fun y =>
    ((innerSL ℝ u).hasFDerivAt).sub_const m
  have h1 : fderiv ℝ (fun y : E => ρ / 2 * (inner ℝ u y - m) ^ 2) =
      fun y => (ρ * (inner ℝ u y - m)) • innerSL ℝ u := by
    funext y
    have := ((hℓ y).pow 2).const_mul (ρ / 2)
    rw [this.fderiv]
    ext w
    simp
    ring
  rw [h1]
  have h2 : HasFDerivAt (fun y : E => (ρ * (inner ℝ u y - m)) • innerSL ℝ u)
      ((ρ • innerSL ℝ u).smulRight (innerSL ℝ u)) x := by
    have := ((hℓ x).const_mul ρ).smul_const (innerSL ℝ u)
    exact this
  rw [h2.fderiv]
  simp [pow_two]
  ring

theorem hessian_inv (U : E → ℝ) (hU : ContDiff ℝ 2 U) (u : E)
    (hinv : ∀ x (t : ℝ), U (x + t • u) = U x) (x w : E) :
    fderiv ℝ (fderiv ℝ U) x u w = 0 := by
  have h1 : ∀ y, fderiv ℝ U y u = 0 := by
    intro y
    have hl : HasDerivAt (fun t : ℝ => y + t • u) u 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const u).const_add y
    have := (hU.differentiable (by norm_num) (y + (0:ℝ) • u)).hasFDerivAt.comp_hasDerivAt (0:ℝ) hl
    have h0 : (fun t : ℝ => U (y + t • u)) = fun _ => U y := funext fun t => hinv y t
    have h2 : HasDerivAt (fun t : ℝ => U (y + t • u)) 0 0 := by
      rw [h0]; exact hasDerivAt_const _ _
    simpa using this.unique h2
  have hdiff : Differentiable ℝ (fderiv ℝ U) :=
    hU.fderiv_right (m := 1) (by norm_num) |>.differentiable (by norm_num)
  have h3 : fderiv ℝ (fun y => fderiv ℝ U y u) x w = fderiv ℝ (fderiv ℝ U) x w u := by
    have := (hdiff x).hasFDerivAt.clm_apply (hasFDerivAt_const u x)
    simp [this.fderiv]
  have h4 : fderiv ℝ (fun y => fderiv ℝ U y u) x = 0 := by
    have : (fun y => fderiv ℝ U y u) = fun _ => (0:ℝ) := funext h1
    rw [this]; simp
  have hsym := (hU.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  rw [hsym.eq u w, ← h3, h4]; rfl

/-- The set of Rayleigh quotients defining `spectralGap` is nonempty when `0 < d` and `gibbs V`
has an everywhere positive density. -/
theorem rayleigh_nonempty (hd : 0 < d) (V : CutCur.Rd d → ℝ) (hVc : Continuous V)
    (hp : IsProbabilityMeasure (CutCur.gibbs V)) :
    {r : ℝ | ∃ f : CutCur.Rd d → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      0 < variance f (CutCur.gibbs V) ∧ r = (∫ x, ‖gradient f x‖ ^ 2 ∂CutCur.gibbs V) /
        variance f (CutCur.gibbs V)}.Nonempty := by
  set μ := CutCur.gibbs V with hμ
  let b : ContDiffBump (0 : CutCur.Rd d) := ⟨1, 2, one_pos, one_lt_two⟩
  have hfc : Continuous (b : CutCur.Rd d → ℝ) := b.continuous
  have hmem : MemLp (b : CutCur.Rd d → ℝ) 2 μ := hfc.memLp_of_hasCompactSupport b.hasCompactSupport
  refine ⟨_, b, b.contDiff, b.hasCompactSupport, ?_, rfl⟩
  rcases (variance_nonneg (b : CutCur.Rd d → ℝ) μ).lt_or_eq with h | h
  · exact h
  · exfalso
    have hae := ae_eq_integral_of_variance_eq_zero hmem h.symm
    have hac : volume ≪ μ := by
      refine withDensity_absolutelyContinuous' (by fun_prop) ?_
      exact Eventually.of_forall fun x => by simp [Real.exp_pos]
    have hae' := hac.ae_le hae
    have hconst : Continuous (fun _ : CutCur.Rd d => ∫ x, (b : CutCur.Rd d → ℝ) x ∂μ) :=
      continuous_const
    have heq := Continuous.ae_eq_iff_eq volume hfc hconst |>.mp hae'
    have h0 : (b : CutCur.Rd d → ℝ) 0 = 1 := b.one_of_mem_closedBall (by simp [Metric.mem_closedBall]; exact b.rIn_pos.le)
    obtain ⟨x, hx⟩ : ∃ x : CutCur.Rd d, ‖x‖ = 3 := by
      refine ⟨(3 : ℝ) • EuclideanSpace.single ⟨0, hd⟩ 1, ?_⟩
      simp [norm_smul]
    have h3 : (b : CutCur.Rd d → ℝ) x = 0 := b.zero_of_le_dist (by
      simp [dist_zero_right, hx]; norm_num)
    have e0 := congrFun heq 0
    have e1 := congrFun heq x
    rw [h0] at e0
    rw [h3] at e1
    have : (1 : ℝ) = 0 := e0.trans e1.symm
    exact one_ne_zero this

/-- **Lichnerowicz / Bakry–Émery** (eq:Lichne). -/
theorem spectral_gap_ge_curvature (hd : 0 < d) {V : CutCur.Rd d → ℝ} (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (CutCur.gibbs V)) {ρ : ℝ} (hρ : 0 < ρ)
    (hconv : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
    ρ ≤ CutCur.spectralGap V := by
  rw [CutCur.spectralGap]
  refine le_csInf (rayleigh_nonempty hd V hV.continuous hp) ?_
  rintro r ⟨g, hg, hgc, hvar, rfl⟩
  rw [le_div_iff₀ hvar]
  have hP := gibbsSpectralGap_mul_variance_le hV hp hd ρ hρ hconv hg hgc
  have hge := gibbsSpectralGap_ge_curvature hV hp hd ρ hρ hconv
  nlinarith [variance_nonneg g (CutCur.gibbs V)]

/-- **(R2) ⇒ (R1)** (rigidity). -/
theorem rigidity_of_gaussian_factor {V : CutCur.Rd d → ℝ} (hV2 : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (CutCur.gibbs V)) {ρ : ℝ} (hρ : 0 < ρ)
    (u : CutCur.Rd d) (hu : ‖u‖ = 1) (m : ℝ) (U : CutCur.Rd d → ℝ)
    (hsplit : ∀ x, V x = ρ / 2 * (inner ℝ u x - m) ^ 2 + U x)
    (hinv : ∀ x (t : ℝ), U (x + t • u) = U x)
    (hU : ∀ x z, inner ℝ u z = 0 → ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ U) x z z) :
    (∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) ∧
      CutCur.spectralGap V = ρ ∧
      CutCur.IsEigenfunction V ρ (fun x => inner ℝ u x - m) := by
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h
    · subst h0
      exact absurd (Subsingleton.elim u 0 ▸ hu) (by simp)
    · exact h
  set q : E → ℝ := fun y => ρ / 2 * (inner ℝ u y - m) ^ 2 with hq
  have hqc : ContDiff ℝ 2 q := by
    have hl : ContDiff ℝ 2 (fun y : E => inner ℝ u y - m) :=
      (innerSL ℝ u).contDiff.sub contDiff_const
    exact contDiff_const.mul (hl.pow 2)
  have hVq : V = fun x => q x + U x := funext hsplit
  have hU2 : ContDiff ℝ 2 U := by
    have : U = fun x => V x - q x := funext fun x => by rw [hsplit x]; simp [hq]
    rw [this]; exact hV2.sub hqc
  have hqd : Differentiable ℝ (fderiv ℝ q) :=
    hqc.fderiv_right (m := 1) (by norm_num) |>.differentiable (by norm_num)
  have hUd : Differentiable ℝ (fderiv ℝ U) :=
    hU2.fderiv_right (m := 1) (by norm_num) |>.differentiable (by norm_num)
  have hfV : fderiv ℝ V = fun x => fderiv ℝ q x + fderiv ℝ U x := by
    rw [hVq]; funext x
    exact fderiv_add (hqc.differentiable (by norm_num) x) (hU2.differentiable (by norm_num) x)
  have hHV : ∀ x z, fderiv ℝ (fderiv ℝ V) x z z =
      ρ * inner ℝ u z ^ 2 + fderiv ℝ (fderiv ℝ U) x z z := by
    intro x z
    rw [hfV, fderiv_fun_add (hqd x) (hUd x)]
    simp only [add_apply]
    rw [hessian_quad]
  have hHess : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z := by
    intro x z
    rw [hHV]
    set c := inner ℝ u z with hc
    set w := z - c • u with hw
    have huw : inner ℝ u w = 0 := by
      rw [hw, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hu]; simp [hc]
    have hz : z = c • u + w := by rw [hw]; abel
    have hsymm := (hU2.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
    have h1 := hessian_inv U hU2 u hinv x w
    have h2 : fderiv ℝ (fderiv ℝ U) x w u = 0 := by rw [hsymm.eq w u]; exact h1
    have h3 : fderiv ℝ (fderiv ℝ U) x u u = 0 := hessian_inv U hU2 u hinv x u
    have hexp : fderiv ℝ (fderiv ℝ U) x z z = fderiv ℝ (fderiv ℝ U) x w w := by
      conv_lhs => rw [hz]
      simp [map_add, map_smul, h1, h2, h3]
    have hn : ‖z‖ ^ 2 = c ^ 2 + ‖w‖ ^ 2 := by
      rw [hz, norm_add_sq_real]
      simp [norm_smul, hu, inner_smul_left, huw, hc]
    rw [hexp]
    have := hU x w huw
    nlinarith
  have hge := spectral_gap_ge_curvature hd hV2 hp hρ hHess
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hDV : ∀ x, fderiv ℝ V x u = ρ * (inner ℝ u x - m) := by
    intro x
    have hl : HasDerivAt (fun t : ℝ => x + t • u) u 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const u).const_add x
    have h1 := (hV2.differentiable (by norm_num) (x + (0:ℝ) • u)).hasFDerivAt.comp_hasDerivAt
      (0:ℝ) hl
    have hline : (fun t : ℝ => V (x + t • u)) =
        fun t => ρ / 2 * (inner ℝ u x + t - m) ^ 2 + U x := by
      funext t
      rw [hsplit, hinv]
      simp [inner_add_right, inner_smul_right, hu]
    have h2 : HasDerivAt (fun t : ℝ => ρ / 2 * (inner ℝ u x + t - m) ^ 2 + U x)
        (ρ * (inner ℝ u x - m)) 0 := by
      have := ((((hasDerivAt_id (0:ℝ)).const_add (inner ℝ u x)).sub_const m).pow 2).const_mul
        (ρ / 2) |>.add_const (U x)
      refine this.congr_deriv ?_
      simp [id]; ring
    have h3 := h1
    simp only [Function.comp_def, zero_smul, add_zero] at h3
    rw [hline] at h3
    exact h3.unique h2
  have heigen : ∀ x : E, langevinDifferentialOperator V (fun y => inner ℝ u y + -m) x =
      -ρ * (inner ℝ u x + -m) := by
    intro x
    have hlap : euclideanLaplacian (fun y : E => inner ℝ u y + -m) x = 0 := by
      have : fderiv ℝ (fun y : E => inner ℝ u y + -m) = fun _ => innerSL ℝ u := by
        funext y; rw [fderiv_add_const]; exact (innerSL ℝ u).fderiv
      unfold euclideanLaplacian
      rw [this]
      simp
    have hg : gradient (fun y : E => inner ℝ u y + -m) x = u := by
      have : fderiv ℝ (fun y : E => inner ℝ u y + -m) x = innerSL ℝ u := by
        rw [fderiv_add_const]; exact (innerSL ℝ u).fderiv
      unfold gradient
      rw [this]
      exact (InnerProductSpace.toDual ℝ E).symm_apply_eq.mpr rfl
    rw [langevinDifferentialOperator, hlap, hg, inner_gradient_left, hDV]
    ring
  obtain ⟨hne, hle⟩ := spectralGap_le_of_affine_eigenfunction_aux_shift
    (hV2.differentiable (by norm_num)) u hu0 (-m) ρ hρ heigen hp
  have hgap : CutCur.spectralGap V = ρ := le_antisymm hle hge
  refine ⟨hHess, hgap, ?_⟩
  have hmem := affine_eigenfunction_memLp V (hV2.differentiable (by norm_num)) u hu0 (-m) ρ hρ
    heigen hp
  refine isEigenfunction_iff.mpr ⟨?_, ?_, fun x => ?_⟩
  · exact ((innerSL ℝ u).contDiff.sub contDiff_const)
  · simpa [sub_eq_add_neg] using hmem
  · simpa [sub_eq_add_neg] using heigen x

end CutoffRigidity.Paper
