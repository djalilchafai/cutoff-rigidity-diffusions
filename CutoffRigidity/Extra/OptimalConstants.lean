module

public import CutoffRigidity.Statements
public import CutoffRigidity.Paper.GapBridge
public import CutoffRigidity.Paper.ConvexInteraction
public import CutoffRigidity.LipschitzLogSobolev
public import CutoffRigidity.LipschitzExponentialLogSobolev

/-! # Optimal constants (manuscript subsection "Optimal constants")

Conventions.  `Var_μ f ≤ C ∫ |∇f|² dμ` is the Poincaré inequality (PI) with constant `C`, and
`Ent_μ(f²) ≤ C ∫ |∇f|² dμ` the logarithmic Sobolev inequality (LSI) with constant `C`, where
`Ent_μ(g) = ∫ g log g dμ - (∫ g dμ) log (∫ g dμ)`.  For the Gaussian `𝒩(0, 1/ρ)` the optimal
constants are `1/ρ` (PI) and `2/ρ` (LSI), which is the convention of the manuscript
(`CD(ρ,∞)` gives LSI with constant `2/ρ` and PI with constant `1/ρ`).
Test functions are smooth bounded Lipschitz functions.
-/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal ContDiff Topology

variable {d : ℕ}

open CutCur (entropyOf IsTestFunction optimalPI optimalLSI)

/-! ### Elementary facts on test functions -/

theorem _root_.CutCur.IsTestFunction.of_compactSupport {f : CutCur.Rd d → ℝ} (hf : ContDiff ℝ ∞ f)
    (hcs : HasCompactSupport f) : IsTestFunction f := by
  refine ⟨hf, ?_, ?_⟩
  · obtain ⟨M, hM⟩ := hf.continuous.bounded_above_of_compact_support hcs
    exact ⟨M, fun x => by simpa [Real.norm_eq_abs] using hM x⟩
  · obtain ⟨L, hL⟩ := hf.lipschitzWith_of_hasCompactSupport hcs (by simp)
    exact ⟨L, hL⟩

theorem _root_.CutCur.IsTestFunction.affine {g : CutCur.Rd d → ℝ} (hg : IsTestFunction g) (c ε : ℝ) :
    IsTestFunction (fun x => c + ε * g x) := by
  obtain ⟨hs, ⟨M, hM⟩, ⟨L, hL⟩⟩ := hg
  refine ⟨contDiff_const.add (contDiff_const.mul hs), ⟨|c| + |ε| * M, fun x => ?_⟩,
    ⟨Real.toNNReal |ε| * L, LipschitzWith.of_dist_le_mul fun x y => ?_⟩⟩
  · calc |c + ε * g x| ≤ |c| + |ε * g x| := abs_add_le _ _
      _ ≤ |c| + |ε| * M := by
        rw [abs_mul]; gcongr; exact hM x
  · have := hL.dist_le_mul x y
    rw [Real.dist_eq] at this ⊢
    calc |c + ε * g x - (c + ε * g y)| = |ε| * |g x - g y| := by
          rw [← abs_mul]; congr 1; ring
      _ ≤ |ε| * (L * dist x y) := by gcongr
      _ = _ := by simp; ring

theorem gradient_affine {g : CutCur.Rd d → ℝ} (hg : DifferentiableAt ℝ g x) (c ε : ℝ) :
    gradient (fun x => c + ε * g x) x = ε • gradient g x := by
  apply ext_inner_right ℝ
  intro z
  rw [inner_gradient_left, real_inner_smul_left, inner_gradient_left]
  have hh := (hg.hasFDerivAt.const_mul ε).const_add c
  rw [hh.fderiv]
  simp

theorem _root_.CutCur.IsTestFunction.gradient_bound {g : CutCur.Rd d → ℝ} (hg : IsTestFunction g) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x, ‖gradient g x‖ ≤ L := by
  obtain ⟨hs, -, ⟨L, hL⟩⟩ := hg
  refine ⟨L, L.2, fun x => ?_⟩
  have := norm_fderiv_le_of_lipschitz ℝ (x₀ := x) hL
  simpa [gradient] using this

theorem _root_.CutCur.IsTestFunction.integrable_gradient_sq {g : CutCur.Rd d → ℝ} (hg : IsTestFunction g)
    (μ : Measure (CutCur.Rd d)) [IsProbabilityMeasure μ] :
    Integrable (fun x => ‖gradient g x‖ ^ 2) μ := by
  obtain ⟨L, hL0, hL⟩ := hg.gradient_bound
  have hc : Continuous (gradient g) := continuous_gradient_of_c1 (hg.1.of_le (by simp))
  refine Integrable.of_bound (C := L ^ 2) (hc.norm.pow 2).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hL x) 2

theorem _root_.CutCur.IsTestFunction.integrable_of_bounded {g : CutCur.Rd d → ℝ} (hg : IsTestFunction g)
    (μ : Measure (CutCur.Rd d)) [IsProbabilityMeasure μ] {F : ℝ → ℝ} (hF : Continuous F) :
    Integrable (fun x => F (g x)) μ := by
  obtain ⟨M, hM⟩ := hg.2.1
  have hcomp : Continuous fun x => F (g x) := hF.comp hg.1.continuous
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := -M) (b := M)).exists_bound_of_continuousOn hF.continuousOn
  exact Integrable.of_bound (C := K) hcomp.aestronglyMeasurable
    (Eventually.of_forall fun x => hK _ (abs_le.mp (hM x)))

/-! ### A pointwise lower bound for `(1+s)² log (1+s)²` -/

theorem phi_lower {s : ℝ} (hs : |s| ≤ 1 / 2) :
    2 * s + 3 * s ^ 2 - 10 * |s| ^ 3 ≤ (1 + s) ^ 2 * Real.log ((1 + s) ^ 2) := by
  have hs1 : |-s| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hs1 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  have hpos : 0 < 1 + s := by linarith [(abs_le.mp hs).1]
  have hlp : Real.log ((1 + s) ^ 2) = 2 * Real.log (1 + s) := by rw [Real.log_pow]; norm_num
  rw [show (1 - -s) = 1 + s by ring] at h
  have hb : |s| ^ 3 / (1 - |s|) ≤ 2 * |s| ^ 3 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [pow_nonneg (abs_nonneg s) 3]
  have hl : s - s ^ 2 / 2 - 2 * |s| ^ 3 ≤ Real.log (1 + s) := by
    have := (abs_le.mp (h.trans (by simpa [abs_neg] using hb))).1
    nlinarith [this]
  have hsq : (1 + s) ^ 2 ≤ 9 / 4 := by nlinarith [(abs_le.mp hs).1, (abs_le.mp hs).2]
  have hs4 : s ^ 4 ≤ |s| ^ 3 / 2 := by
    have : s ^ 4 = |s| ^ 3 * |s| := by
      rw [show s ^ 4 = |s| ^ 4 by rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]]; ring
    rw [this]; nlinarith [pow_nonneg (abs_nonneg s) 3]
  have habs3 : 0 ≤ |s| ^ 3 := pow_nonneg (abs_nonneg s) 3
  have key : (1 + s) ^ 2 * (2 * (s - s ^ 2 / 2 - 2 * |s| ^ 3)) ≤
      (1 + s) ^ 2 * (2 * Real.log (1 + s)) := by
    gcongr
  have e1 : (1 + s) ^ 2 * (2 * (s - s ^ 2 / 2 - 2 * |s| ^ 3)) =
      2 * s + 3 * s ^ 2 - s ^ 4 - 4 * (1 + s) ^ 2 * |s| ^ 3 := by ring
  have e2 : 4 * (1 + s) ^ 2 * |s| ^ 3 ≤ 9 * |s| ^ 3 := by nlinarith
  rw [hlp]
  linarith [key, e1, e2, hs4]

/-! ### Linearization: LSI with constant `C` implies PI with constant `C/2` -/

theorem pi_of_lsi {μ : Measure (CutCur.Rd d)} [IsProbabilityMeasure μ] {C : ℝ}
    (hC : ∀ f : CutCur.Rd d → ℝ, IsTestFunction f →
      entropyOf μ (fun x => f x ^ 2) ≤ C * ∫ x, ‖gradient f x‖ ^ 2 ∂μ)
    {g : CutCur.Rd d → ℝ} (hg : IsTestFunction g) :
    2 * variance g μ ≤ C * ∫ x, ‖gradient g x‖ ^ 2 ∂μ := by
  set m := ∫ x, g x ∂μ with hm
  set h : CutCur.Rd d → ℝ := fun x => g x - m with hh
  set a := variance g μ with ha
  set E := ∫ x, ‖gradient g x‖ ^ 2 ∂μ with hE
  obtain ⟨B, hB⟩ := hg.2.1
  have hgi : Integrable g μ := by simpa using hg.integrable_of_bounded μ (F := id) continuous_id
  have hgc : Continuous g := hg.1.continuous
  have hhc : Continuous h := hgc.sub continuous_const
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hMh : ∃ Mh : ℝ, 0 ≤ Mh ∧ ∀ x, |h x| ≤ Mh :=
    ⟨B + |m|, by positivity, fun x => (abs_sub _ _).trans (by linarith [hB x])⟩
  obtain ⟨Mh, hMh0, hMh⟩ := hMh
  -- integrals of powers of `h`
  have hint : ∀ F : ℝ → ℝ, Continuous F → Integrable (fun x => F (h x)) μ := by
    intro F hF
    obtain ⟨K, hK⟩ := (isCompact_Icc (a := -Mh) (b := Mh)).exists_bound_of_continuousOn hF.continuousOn
    exact Integrable.of_bound (C := K) (hF.comp hhc).aestronglyMeasurable
      (Eventually.of_forall fun x => hK _ (abs_le.mp (hMh x)))
  have h1 : Integrable h μ := by simpa using hint id continuous_id
  have h2 : Integrable (fun x => h x ^ 2) μ := hint (fun t => t ^ 2) (by fun_prop)
  have h3 : Integrable (fun x => |h x| ^ 3) μ := hint (fun t => |t| ^ 3) (by fun_prop)
  have hmean : ∫ x, h x ∂μ = 0 := by
    simp only [hh]; rw [integral_sub hgi (integrable_const _)]; simp [hm]
  have hvar : a = ∫ x, h x ^ 2 ∂μ := variance_eq_integral hgc.aemeasurable
  set T := ∫ x, |h x| ^ 3 ∂μ with hT
  have hT0 : 0 ≤ T := integral_nonneg fun x => by positivity
  have ha0 : 0 ≤ a := by rw [hvar]; exact integral_nonneg fun x => sq_nonneg _
  -- the key estimate for small `ε`
  have key : ∀ ε : ℝ, 0 < ε → ε * Mh ≤ 1 / 2 →
      2 * a ≤ C * E + ε * (10 * T + ε * a ^ 2) := by
    intro ε hε hεM
    set f : CutCur.Rd d → ℝ := fun x => (1 - ε * m) + ε * g x with hf
    have hfT : IsTestFunction f := hg.affine _ _
    have hfx : ∀ x, f x = 1 + ε * h x := fun x => by simp only [hf, hh]; ring
    have hs : ∀ x, |ε * h x| ≤ 1 / 2 := fun x => by
      rw [abs_mul, abs_of_pos hε]; nlinarith [hMh x]
    have hfc : Continuous f := hfT.1.continuous
    -- ∫ f² = 1 + ε² a
    have hsq : ∫ x, f x ^ 2 ∂μ = 1 + ε ^ 2 * a := by
      have : ∀ x, f x ^ 2 = 1 + 2 * ε * h x + ε ^ 2 * h x ^ 2 := fun x => by rw [hfx]; ring
      simp_rw [this]
      have hA : Integrable (fun x => 1 + 2 * ε * h x) μ :=
        (integrable_const (1 : ℝ)).add (h1.const_mul _)
      have hB' : Integrable (fun x => ε ^ 2 * h x ^ 2) μ := h2.const_mul _
      rw [integral_add (f := fun x => 1 + 2 * ε * h x) (g := fun x => ε ^ 2 * h x ^ 2) hA hB',
        integral_add (f := fun _ => (1 : ℝ)) (g := fun x => 2 * ε * h x) (integrable_const _)
          (h1.const_mul _), integral_const_mul, integral_const_mul, hmean, ← hvar]
      simp
    have hfi : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) μ :=
      hfT.integrable_of_bounded μ (F := fun t => t ^ 2 * Real.log (t ^ 2))
        (Real.continuous_mul_log.comp (continuous_pow 2))
    have hlow : 3 * ε ^ 2 * a - 10 * ε ^ 3 * T ≤ ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ := by
      have hmono : ∫ x, (2 * ε * h x + 3 * ε ^ 2 * h x ^ 2 - 10 * ε ^ 3 * |h x| ^ 3) ∂μ ≤
          ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ := by
        refine integral_mono (((h1.const_mul _).add (h2.const_mul _)).sub (h3.const_mul _)) hfi
          fun x => ?_
        have := phi_lower (hs x)
        have e : |ε * h x| ^ 3 = ε ^ 3 * |h x| ^ 3 := by rw [abs_mul, abs_of_pos hε, mul_pow]
        simp only [hfx x]
        calc 2 * ε * h x + 3 * ε ^ 2 * h x ^ 2 - 10 * ε ^ 3 * |h x| ^ 3
            = 2 * (ε * h x) + 3 * (ε * h x) ^ 2 - 10 * |ε * h x| ^ 3 := by rw [e]; ring
          _ ≤ _ := this
      refine le_trans (le_of_eq ?_) hmono
      have hA : Integrable (fun x => 2 * ε * h x + 3 * ε ^ 2 * h x ^ 2) μ :=
        (h1.const_mul _).add (h2.const_mul _)
      rw [integral_sub (f := fun x => 2 * ε * h x + 3 * ε ^ 2 * h x ^ 2)
        (g := fun x => 10 * ε ^ 3 * |h x| ^ 3) hA (h3.const_mul _),
        integral_add (f := fun x => 2 * ε * h x) (g := fun x => 3 * ε ^ 2 * h x ^ 2)
          (h1.const_mul _) (h2.const_mul _), integral_const_mul, integral_const_mul,
        integral_const_mul, hmean, ← hvar]
      ring
    have hent : 3 * ε ^ 2 * a - 10 * ε ^ 3 * T - (1 + ε ^ 2 * a) * (ε ^ 2 * a) ≤
        entropyOf μ (fun x => f x ^ 2) := by
      unfold entropyOf
      rw [hsq]
      have hpos : 0 < 1 + ε ^ 2 * a := by positivity
      have := Real.log_le_sub_one_of_pos hpos
      have h' : (1 + ε ^ 2 * a) * Real.log (1 + ε ^ 2 * a) ≤ (1 + ε ^ 2 * a) * (ε ^ 2 * a) := by
        calc _ ≤ (1 + ε ^ 2 * a) * ((1 + ε ^ 2 * a) - 1) := by gcongr
          _ = _ := by ring
      linarith
    have hgrad : ∫ x, ‖gradient f x‖ ^ 2 ∂μ = ε ^ 2 * E := by
      rw [hE, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      have hd : DifferentiableAt ℝ g x := (hg.1.differentiable (by simp)) x
      simp only [hf]
      rw [gradient_affine hd, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have hCf := hC f hfT
    rw [hgrad] at hCf
    have hε2 : 0 < ε ^ 2 := by positivity
    have : ε ^ 2 * (2 * a) ≤ ε ^ 2 * (C * E + ε * (10 * T + ε * a ^ 2)) := by
      nlinarith [hent, hCf]
    exact le_of_mul_le_mul_left this hε2
  by_contra hcon
  rw [not_le] at hcon
  set δ := 2 * a - C * E with hδ
  have hδ0 : 0 < δ := by linarith
  set K := 10 * T + a ^ 2 + 1 with hK
  have hK0 : 0 < K := by positivity
  set ε := min (1 / (2 * (Mh + 1))) (δ / (2 * K)) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
  have hε1 : ε ≤ 1 / (2 * (Mh + 1)) := min_le_left _ _
  have hε2 : ε ≤ δ / (2 * K) := min_le_right _ _
  have hεM : ε * Mh ≤ 1 / 2 := by
    calc ε * Mh ≤ 1 / (2 * (Mh + 1)) * Mh := by gcongr
      _ ≤ 1 / 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hεle1 : ε ≤ 1 := hε1.trans (by
    rw [div_le_one (by positivity)]; nlinarith)
  have := key ε hε0 hεM
  have hsmall : ε * (10 * T + ε * a ^ 2) ≤ δ / 2 := by
    calc ε * (10 * T + ε * a ^ 2) ≤ ε * K := by
          gcongr
          nlinarith [sq_nonneg a]
      _ ≤ δ / (2 * K) * K := by gcongr
      _ = δ / 2 := by field_simp
  linarith

theorem integral_comb {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {u v : α → ℝ} (hu : Integrable u μ) (hv : Integrable v μ) (a b : ℝ) :
    ∫ x, (a * u x + b * v x + 1 - a * v x) ∂μ =
      a * ∫ x, u x ∂μ + b * ∫ x, v x ∂μ + 1 - a * ∫ x, v x ∂μ := by
  have h1 : Integrable (fun x => a * u x) μ := hu.const_mul a
  have h2 : Integrable (fun x => b * v x) μ := hv.const_mul b
  have h3 : Integrable (fun x => a * v x) μ := hv.const_mul a
  have h4 : Integrable (fun x => a * u x + b * v x) μ := h1.add h2
  have h5 : Integrable (fun x => a * u x + b * v x + 1) μ := h4.add (integrable_const 1)
  have e1 := integral_sub h5 h3
  have e2 := integral_add h4 (integrable_const (1 : ℝ))
  have e3 := integral_add h1 h2
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, integral_const_mul] at e1 e2 e3
  rw [e1, e2, e3]

/-! ### Validity of the Bakry–Émery constants on test functions -/

section Validity

variable {V : CutCur.Rd d → ℝ}

/-- PI with constant `1/ρ` on test functions, from the curvature condition. -/
theorem pi_valid (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (CutCur.gibbs V))
    (hR : CutCur.RigidCurvature V) {f : CutCur.Rd d → ℝ} (hf : IsTestFunction f) :
    variance f (CutCur.gibbs V) ≤
      (CutCur.spectralGap V)⁻¹ * ∫ x, ‖gradient f x‖ ^ 2 ∂CutCur.gibbs V := by
  have hd := pos_dim_of_rigidCurvature hp hR
  have hρ := hR.1
  have hp' : IsProbabilityMeasure (gibbsMeasure volume V) := hp
  have hP := hasSmoothPoincare_gibbsSpectralGap hV hp' hd _ hρ hR.2
  rw [← spectralGap_eq_gibbsSpectralGap hV hp' hR] at hP
  have hP : HasSmoothPoincare (CutCur.gibbs V) (CutCur.spectralGap V) := hP
  set μ := CutCur.gibbs V
  set m := ∫ x, f x ∂μ
  obtain ⟨M, hM⟩ := hf.2.1
  have hfi : Integrable f μ := by simpa using hf.integrable_of_bounded μ (F := id) continuous_id
  have hgrad : gradient (fun x => f x - m) = gradient f := by
    funext x; simp only [gradient, fderiv_sub_const]
  have hLp : MemLp (fun x => f x - m) 2 μ :=
    (memLp_of_bounded (a := -(M + |m|)) (b := M + |m|) (Eventually.of_forall fun x => by
      rw [Set.mem_Icc, ← abs_le]; exact (abs_sub _ _).trans (by linarith [hM x]))
      (hf.1.continuous.sub continuous_const).aestronglyMeasurable 2)
  have h := hP (fun x => f x - m) (hf.1.sub contDiff_const) hLp
    (by rw [hgrad]; exact hf.integrable_gradient_sq μ)
    (by rw [integral_sub hfi (integrable_const m)]; simp [m])
  rw [hgrad] at h
  rw [variance_eq_integral hf.1.continuous.aemeasurable, div_eq_inv_mul] at *
  exact h

/-- LSI with constant `2/ρ` on test functions, from the curvature condition. -/
theorem lsi_valid {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → CutCur.Rd d} {P : Measure Ω}
    (hB : CutCur.IsStdBrownian B P) (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (CutCur.gibbs V))
    (hR : CutCur.RigidCurvature V) {f : CutCur.Rd d → ℝ} (hf : IsTestFunction f) :
    entropyOf (CutCur.gibbs V) (fun x => f x ^ 2) ≤
      2 * (CutCur.spectralGap V)⁻¹ * ∫ x, ‖gradient f x‖ ^ 2 ∂CutCur.gibbs V := by
  have hd := pos_dim_of_rigidCurvature hp hR
  have hρ := hR.1
  have hp' : IsProbabilityMeasure (gibbsMeasure volume V) := hp
  have hB' : IsEuclideanBrownian B P := isStdBrownian_iff.mp hB
  set μ := CutCur.gibbs V with hμ
  set ρ := CutCur.spectralGap V with hρdef
  set E := ∫ x, ‖gradient f x‖ ^ 2 ∂μ with hE
  set A := ∫ x, f x ^ 2 ∂μ with hA
  have hE0 : 0 ≤ E := integral_nonneg fun x => sq_nonneg _
  have hv : Integrable (fun x => f x ^ 2) μ := hf.integrable_of_bounded μ (F := fun t => t ^ 2) (by fun_prop)
  have hu : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) μ :=
    hf.integrable_of_bounded μ (F := fun t => t ^ 2 * Real.log (t ^ 2))
      (Real.continuous_mul_log.comp (continuous_pow 2))
  have hA0 : 0 ≤ A := integral_nonneg fun x => sq_nonneg _
  rcases hA0.eq_or_lt with hA00 | hApos
  · -- `f = 0` almost everywhere
    have hz : (fun x => f x ^ 2) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hv).mp hA00.symm
    have hu0 : ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ = 0 :=
      integral_eq_zero_of_ae (hz.mono fun x hx => by simp at hx ⊢; simp [hx])
    have : entropyOf μ (fun x => f x ^ 2) = 0 := by
      unfold entropyOf; rw [hu0, ← hA, ← hA00]; simp
    rw [this]; positivity
  · set c := (Real.sqrt A)⁻¹ with hc
    have hc2 : c ^ 2 = A⁻¹ := by rw [hc, inv_pow, Real.sq_sqrt hA0]
    have hgT : IsTestFunction (fun x => 0 + c * f x) := hf.affine 0 c
    obtain ⟨M, hM⟩ := hgT.2.1
    obtain ⟨L, hL⟩ := hgT.2.2
    have hnorm : ∫ x, (0 + c * f x) ^ 2 ∂μ = 1 := by
      have : ∀ x, (0 + c * f x) ^ 2 = c ^ 2 * f x ^ 2 := fun x => by ring
      simp_rw [this]
      rw [integral_const_mul, hc2, ← hA]; field_simp
    have hlsi0 := logSobolev_normalized_bounded_lipschitz (V := V) (f := fun x => 0 + c * f x) hB'
      hV hp' hd ρ hρ hR.2 hL M (fun x => by simpa [Real.norm_eq_abs] using hM x) hnorm
    have hlsi : ∫ x, InformationTheory.klFun ((0 + c * f x) ^ 2) ∂μ ≤
        2 / ρ * ∫ x, ‖gradient (fun x => 0 + c * f x) x‖ ^ 2 ∂μ := hlsi0
    have hgrad : ∫ x, ‖gradient (fun x => 0 + c * f x) x‖ ^ 2 ∂μ = A⁻¹ * E := by
      rw [hE, ← hc2, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      have hd' : DifferentiableAt ℝ f x := (hf.1.differentiable (by simp)) x
      show ‖gradient (fun x => 0 + c * f x) x‖ ^ 2 = c ^ 2 * ‖gradient f x‖ ^ 2
      rw [gradient_affine hd', norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have hkl : ∫ x, InformationTheory.klFun ((0 + c * f x) ^ 2) ∂μ =
        A⁻¹ * entropyOf μ (fun x => f x ^ 2) := by
      have hpt : ∀ x, InformationTheory.klFun ((0 + c * f x) ^ 2) =
          A⁻¹ * (f x ^ 2 * Real.log (f x ^ 2)) + (A⁻¹ * Real.log A⁻¹) * f x ^ 2 + 1 -
            A⁻¹ * f x ^ 2 := by
        intro x
        rw [InformationTheory.klFun_apply]
        have e : (0 + c * f x) ^ 2 = A⁻¹ * f x ^ 2 := by rw [← hc2]; ring
        rw [e]
        by_cases hx : f x = 0
        · simp [hx]
        · rw [Real.log_mul (inv_ne_zero hApos.ne') (pow_ne_zero 2 hx)]; ring
      rw [integral_congr_ae (Eventually.of_forall hpt),
        integral_comb (μ := μ) (u := fun x => f x ^ 2 * Real.log (f x ^ 2))
          (v := fun x => f x ^ 2) hu hv]
      unfold entropyOf
      rw [← hA, Real.log_inv]
      field_simp
      ring
    have hkl' := hlsi
    rw [hkl, hgrad] at hkl'
    have : entropyOf μ (fun x => f x ^ 2) ≤ 2 / ρ * E := by
      have hAi : 0 < A⁻¹ := inv_pos.mpr hApos
      rw [mul_left_comm] at hkl'
      exact (mul_le_mul_iff_right₀ hAi).mp hkl'
    calc _ ≤ 2 / ρ * E := this
      _ = _ := by rw [div_eq_mul_inv]

/-- Any valid Poincaré constant on test functions is at least `1/λ₁`. -/
theorem inv_spectralGap_le_of_pi (hρ : 0 < CutCur.spectralGap V) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ f : CutCur.Rd d → ℝ, IsTestFunction f →
      variance f (CutCur.gibbs V) ≤ C * ∫ x, ‖gradient f x‖ ^ 2 ∂CutCur.gibbs V) :
    (CutCur.spectralGap V)⁻¹ ≤ C := by
  set R := {r : ℝ | ∃ f : CutCur.Rd d → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    0 < variance f (CutCur.gibbs V) ∧ r = (∫ x, ‖gradient f x‖ ^ 2 ∂CutCur.gibbs V) /
      variance f (CutCur.gibbs V)} with hR
  have hne : R.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have : CutCur.spectralGap V = 0 := by
      show sInf R = 0
      rw [h, Real.sInf_empty]
    linarith
  obtain ⟨r₀, f₀, hf₀, hcs₀, hvar₀, hr₀⟩ := hne
  have hCpos : 0 < C := by
    rcases hC0.eq_or_lt with h | h
    · exfalso
      have := hC f₀ (CutCur.IsTestFunction.of_compactSupport hf₀ hcs₀)
      rw [← h, zero_mul] at this
      linarith
    · exact h
  have hle : 1 / C ≤ CutCur.spectralGap V := by
    show 1 / C ≤ sInf R
    refine le_csInf ⟨r₀, f₀, hf₀, hcs₀, hvar₀, hr₀⟩ ?_
    rintro r ⟨f, hf, hcs, hvar, rfl⟩
    have := hC f (CutCur.IsTestFunction.of_compactSupport hf hcs)
    rw [div_le_div_iff₀ hCpos hvar]
    linarith
  rw [div_le_iff₀ hCpos] at hle
  rw [inv_le_comm₀ hρ hCpos]
  rw [inv_eq_one_div, div_le_iff₀ hCpos]
  linarith

/-- Under rigidity, the optimal Poincaré constant is `1/λ₁`. -/
theorem optimalPI_eq (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (CutCur.gibbs V))
    (hR : CutCur.RigidCurvature V) : optimalPI V = (CutCur.spectralGap V)⁻¹ := by
  refine IsLeast.csInf_eq ⟨⟨inv_nonneg.mpr hR.1.le, fun f hf => pi_valid hV hp hR hf⟩, ?_⟩
  rintro C ⟨hC0, hC⟩
  exact inv_spectralGap_le_of_pi hR.1 hC0 hC

/-- Under rigidity and with a Brownian motion, the optimal LSI constant is `2/λ₁`. -/
theorem optimalLSI_eq {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → CutCur.Rd d}
    {P : Measure Ω} (hB : CutCur.IsStdBrownian B P) (hV : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (CutCur.gibbs V)) (hR : CutCur.RigidCurvature V) :
    optimalLSI V = 2 * (CutCur.spectralGap V)⁻¹ := by
  refine IsLeast.csInf_eq ⟨⟨by have := hR.1; positivity, fun f hf => lsi_valid hB hV hp hR hf⟩, ?_⟩
  rintro C ⟨hC0, hC⟩
  have h2 := inv_spectralGap_le_of_pi (V := V) hR.1 (C := C / 2) (by positivity) (fun f hf => by
    have := pi_of_lsi (μ := CutCur.gibbs V) hC hf
    linarith)
  linarith

end Validity

/-- **Optimal constants** (manuscript subsection "Optimal constants"): under rigidity
(`Hess V ≥ λ₁ I`, `λ₁ > 0`), the optimal Poincaré constant is `1/λ₁` and the optimal
logarithmic Sobolev constant is twice the optimal Poincaré constant. -/
theorem optimal_lsi_twice_pi_carrier {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {B : ℝ≥0 → Ω → CutCur.Rd d}
    {P : Measure Ω} (hB : CutCur.IsStdBrownian B P) {V : CutCur.Rd d → ℝ}
    (hV : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (CutCur.gibbs V))
    (hR : CutCur.RigidCurvature V) :
    optimalPI V = (CutCur.spectralGap V)⁻¹ ∧ optimalLSI V = 2 * optimalPI V := by
  rw [optimalPI_eq hV hp hR]
  exact ⟨rfl, optimalLSI_eq hB hV hp hR⟩

/-! ### Extremal functions for convex interactions -/

section Extremal

theorem gaussian_exp_moments (σ : ℝ≥0) (b : ℝ) :
    Integrable (fun s : ℝ => Real.exp (b * s)) (gaussianReal 0 σ) ∧
    Integrable (fun s : ℝ => s * Real.exp (b * s)) (gaussianReal 0 σ) ∧
    ∫ s, Real.exp (b * s) ∂gaussianReal 0 σ = Real.exp (σ * b ^ 2 / 2) ∧
    ∫ s, s * Real.exp (b * s) ∂gaussianReal 0 σ = σ * b * Real.exp (σ * b ^ 2 / 2) := by
  have hmem : b ∈ interior (integrableExpSet id (gaussianReal 0 σ)) := by
    simp [integrableExpSet_id_gaussianReal]
  have hmgf : mgf id (gaussianReal 0 σ) b = Real.exp (σ * b ^ 2 / 2) := by
    rw [mgf_id_gaussianReal]; simp
  refine ⟨integrable_exp_mul_gaussianReal b, ?_, ?_, ?_⟩
  · simpa using integrable_pow_mul_exp_of_mem_interior_integrableExpSet hmem 1
  · have := hmgf
    simpa [mgf] using this
  · have h1 := hasDerivAt_mgf hmem
    rw [mgf_id_gaussianReal] at h1
    simp only [zero_mul, zero_add] at h1
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (σ * t ^ 2 / 2))
        (Real.exp (σ * b ^ 2 / 2) * (σ * (2 * b) / 2)) b := by
      have := (((hasDerivAt_pow 2 b).const_mul (σ:ℝ)).div_const 2).exp
      simpa using this
    have h3 := h1.unique h2
    simp only [id] at h3
    rw [h3]; ring

theorem sum_eq_sqrt_mul_inner {d : ℕ} (hd : 0 < d) (x : CutCur.Rd d) :
    ∑ i, x i = Real.sqrt d * inner ℝ ((Real.sqrt d)⁻¹ • CutCur.diagonal d) x := by
  have hs : Real.sqrt d ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'
  rw [real_inner_smul_left]
  have : inner ℝ (CutCur.diagonal d) x = ∑ i, x i := inner_diagonalDirection x
  rw [this]; field_simp

theorem gradient_sum {d : ℕ} (x : CutCur.Rd d) :
    gradient (fun y : CutCur.Rd d => ∑ i, y i) x = CutCur.diagonal d := by
  have heq : (fun y : CutCur.Rd d => ∑ i, y i) = innerSL ℝ (CutCur.diagonal d) := by
    funext y; exact (inner_diagonalDirection y).symm
  rw [heq]
  apply ext_inner_right ℝ
  intro z
  rw [inner_gradient_left, ContinuousLinearMap.fderiv]
  simp

theorem norm_sq_diagonal {d : ℕ} : ‖CutCur.diagonal d‖ ^ 2 = (d : ℝ) := norm_sq_diagonalDirection d

/-- The law of `⟨u,x⟩` under the Gibbs measure of a convex interaction is `𝒩(0, 1/ρ)`. -/
theorem law_inner_eq_gaussian {d : ℕ} {ρ : ℝ} {μ : Measure (CutCur.Rd d)}
    [IsProbabilityMeasure μ] {u : CutCur.Rd d} {π : CutCur.Rd d → CutCur.Rd d}
    (hπ : Continuous π)
    (hprod : μ.map (fun x => (inner ℝ u x, π x)) =
      (gaussianReal 0 ρ⁻¹.toNNReal).prod (μ.map π)) :
    μ.map (fun x => inner ℝ u x) = gaussianReal 0 ρ⁻¹.toNNReal := by
  have hc : Continuous fun x : CutCur.Rd d => inner ℝ u x := by fun_prop
  have hm : Measurable fun x => (inner ℝ u x, π x) := (hc.prodMk hπ).measurable
  have : IsProbabilityMeasure (μ.map π) := (Measure.isProbabilityMeasure_map_iff hπ.aemeasurable).mpr ‹_›
  have h1 : μ.map (fun x => inner ℝ u x) = (μ.map (fun x => (inner ℝ u x, π x))).map Prod.fst := by
    rw [Measure.map_map measurable_fst hm]; rfl
  rw [h1, hprod, Measure.map_fst_prod]
  simp

set_option maxHeartbeats 1000000 in
/-- **Extremal functions** (manuscript subsection "Optimal constants"): in the convex-interaction
setting `V = ρ|x|²/2 + W`, the function `x ↦ x₁+⋯+x_d` is extremal for the Poincaré inequality
(equality with the optimal constant), and `x ↦ e^{α(x₁+⋯+x_d)}` is extremal for the logarithmic
Sobolev inequality (equality with the optimal constant), for every real `α`. -/
theorem optimal_constants_extremal_carrier {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → CutCur.Rd d}
    {P : Measure Ω} (hB : CutCur.IsStdBrownian B P) (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ)
    {W : CutCur.Rd d → ℝ} (hW : ContDiff ℝ 2 W) (hconv : ConvexOn ℝ univ W)
    (hinv : ∀ x (s : ℝ), W (x + s • CutCur.diagonal d) = W x)
    (hp : IsProbabilityMeasure (CutCur.gibbs fun x => ρ / 2 * ‖x‖ ^ 2 + W x)) :
    let V := fun x : CutCur.Rd d => ρ / 2 * ‖x‖ ^ 2 + W x
    let h := fun x : CutCur.Rd d => ∑ i, x i
    optimalPI V = ρ⁻¹ ∧ optimalLSI V = 2 * optimalPI V ∧
    (MemLp h 2 (CutCur.gibbs V) ∧ 0 < variance h (CutCur.gibbs V) ∧
      variance h (CutCur.gibbs V) =
        optimalPI V * ∫ x, ‖gradient h x‖ ^ 2 ∂CutCur.gibbs V) ∧
    ∀ α : ℝ,
      Integrable (fun x => Real.exp (α * h x) ^ 2) (CutCur.gibbs V) ∧
      Integrable (fun x => Real.exp (α * h x) ^ 2 * Real.log (Real.exp (α * h x) ^ 2))
        (CutCur.gibbs V) ∧
      Integrable (fun x => ‖gradient (fun y => Real.exp (α * h y)) x‖ ^ 2) (CutCur.gibbs V) ∧
      (α ≠ 0 → 0 < ∫ x, ‖gradient (fun y => Real.exp (α * h y)) x‖ ^ 2 ∂CutCur.gibbs V) ∧
      entropyOf (CutCur.gibbs V) (fun x => Real.exp (α * h x) ^ 2) =
        optimalLSI V * ∫ x, ‖gradient (fun y => Real.exp (α * h y)) x‖ ^ 2 ∂CutCur.gibbs V := by
  intro V h
  obtain ⟨⟨hgap, heig⟩, ⟨-, hprod⟩, hrig⟩ := convex_interaction hd hρ hW hconv hinv hp
  have hVc : ContDiff ℝ 2 V := (contDiff_const.mul (contDiff_norm_sq ℝ)).add hW
  have hPI : optimalPI V = ρ⁻¹ := by rw [optimalPI_eq hVc hp hrig, hgap]
  have hLSI : optimalLSI V = 2 * optimalPI V := by
    rw [optimalLSI_eq hB hVc hp hrig, hPI, hgap]
  set μ := CutCur.gibbs V with hμ
  set u : CutCur.Rd d := (Real.sqrt d)⁻¹ • CutCur.diagonal d with hu
  set π := fun x : CutCur.Rd d => x - inner ℝ u x • u with hπ
  have hπc : Continuous π := by fun_prop
  have hL := law_inner_eq_gaussian (μ := μ) (ρ := ρ) (u := u) (π := π) hπc hprod
  set σ : ℝ≥0 := ρ⁻¹.toNNReal with hσ
  have hσρ : (σ : ℝ) = ρ⁻¹ := by rw [hσ]; exact Real.coe_toNNReal _ (inv_nonneg.mpr hρ.le)
  set t : CutCur.Rd d → ℝ := fun x => inner ℝ u x with ht
  have htc : Continuous t := by fun_prop
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hht : ∀ x, h x = Real.sqrt d * t x := fun x => sum_eq_sqrt_mul_inner hd x
  have hsq : Real.sqrt d ^ 2 = d := Real.sq_sqrt (by positivity)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hint : ∀ {G : ℝ → ℝ}, Integrable G (gaussianReal 0 σ) →
      Integrable (fun x => G (t x)) μ := fun {G} hG => by
    have hG' : Integrable G (μ.map t) := by rw [hL]; exact hG
    exact (integrable_map_measure hG'.aestronglyMeasurable htc.aemeasurable).mp hG'
  have hintg : ∀ (G : ℝ → ℝ), Continuous G →
      ∫ x, G (t x) ∂μ = ∫ s, G s ∂gaussianReal 0 σ := fun G hG => by
    rw [← hL, integral_map htc.aemeasurable hG.aestronglyMeasurable]
  have hexp2 : ∀ y : ℝ, Real.exp y ^ 2 = Real.exp (2 * y) := fun y => by
    rw [← Real.exp_nat_mul]; norm_num
  have hvar : variance h μ = d * ρ⁻¹ := by
    have hh : h = (fun s => Real.sqrt d * s) ∘ t := funext hht
    have h1 := variance_map (μ := μ) (X := fun s : ℝ => Real.sqrt d * s) (Y := t)
      (by rw [hL]; fun_prop) htc.aemeasurable
    rw [hL] at h1
    have h2 := variance_const_mul (Real.sqrt d) id (gaussianReal 0 σ)
    have h3 := variance_id_gaussianReal (μ := 0) (v := σ)
    rw [hh, ← h1]
    show variance (fun y => Real.sqrt d * id y) (gaussianReal 0 σ) = _
    rw [h2, h3, hsq, hσρ]
  have hgradh : ∫ x, ‖gradient h x‖ ^ 2 ∂μ = d := by
    have : ∀ x, ‖gradient h x‖ ^ 2 = d := fun x => by
      rw [show gradient h x = CutCur.diagonal d from gradient_sum x, norm_sq_diagonal]
    simp_rw [this]; simp
  refine ⟨hPI, hLSI, ⟨heig.2.1, ?_, ?_⟩, fun α => ?_⟩
  · rw [hvar]; positivity
  · rw [hvar, hgradh, hPI]; ring
  · set a := α * Real.sqrt d with ha
    set b := 2 * a with hb
    obtain ⟨hI0, hI1, hZ0, hY0⟩ := gaussian_exp_moments σ b
    have e1 : ∀ x, Real.exp (α * h x) ^ 2 = Real.exp (b * t x) := fun x => by
      rw [hexp2, hht]; congr 1; simp only [hb, ha]; ring
    have e2 : ∀ x, Real.exp (α * h x) ^ 2 * Real.log (Real.exp (α * h x) ^ 2) =
        b * (t x * Real.exp (b * t x)) := fun x => by
      rw [e1, Real.log_exp]; ring
    have hdiff : ∀ x, DifferentiableAt ℝ h x := fun x => by
      have hhd : (fun y : CutCur.Rd d => ∑ i, y i) = ⇑(innerSL ℝ (CutCur.diagonal d)) :=
        funext fun y => (inner_diagonalDirection y).symm
      show DifferentiableAt ℝ (fun y : CutCur.Rd d => ∑ i, y i) x
      rw [hhd]; exact (innerSL ℝ _).differentiableAt
    have e3 : ∀ x, ‖gradient (fun y => Real.exp (α * h y)) x‖ ^ 2 =
        α ^ 2 * d * Real.exp (b * t x) := fun x => by
      rw [CutoffRigidity.gradient_exp_mul_at (hdiff x) α, gradient_sum x, norm_smul, mul_pow, Real.norm_eq_abs,
        sq_abs, norm_sq_diagonal, mul_pow, e1]
      ring
    have hZ : ∫ x, Real.exp (b * t x) ∂μ = Real.exp (σ * b ^ 2 / 2) :=
      (hintg (fun s => Real.exp (b * s)) (by fun_prop)).trans hZ0
    have hY : ∫ x, t x * Real.exp (b * t x) ∂μ = σ * b * Real.exp (σ * b ^ 2 / 2) :=
      (hintg (fun s => s * Real.exp (b * s)) (by fun_prop)).trans hY0
    have hE1 : ∫ x, Real.exp (α * h x) ^ 2 ∂μ = Real.exp (σ * b ^ 2 / 2) := by
      simp_rw [e1]; exact hZ
    have hE2 : ∫ x, Real.exp (α * h x) ^ 2 * Real.log (Real.exp (α * h x) ^ 2) ∂μ =
        b * (σ * b * Real.exp (σ * b ^ 2 / 2)) := by
      simp_rw [e2]; rw [integral_const_mul, hY]
    have hE3 : ∫ x, ‖gradient (fun y => Real.exp (α * h y)) x‖ ^ 2 ∂μ =
        α ^ 2 * d * Real.exp (σ * b ^ 2 / 2) := by
      simp_rw [e3]; rw [integral_const_mul, hZ]
    have hi0 : Integrable (fun x => Real.exp (b * t x)) μ :=
      hint (G := fun s => Real.exp (b * s)) hI0
    refine ⟨hi0.congr (Eventually.of_forall fun x => (e1 x).symm),
      ((hint (G := fun s => s * Real.exp (b * s)) hI1).const_mul b).congr (Eventually.of_forall fun x => (e2 x).symm),
      (hi0.const_mul (α ^ 2 * d)).congr (Eventually.of_forall fun x => (e3 x).symm),
      fun hα => ?_, ?_⟩
    · rw [hE3]; positivity
    · show (∫ x, Real.exp (α * h x) ^ 2 * Real.log (Real.exp (α * h x) ^ 2) ∂μ) -
        (∫ x, Real.exp (α * h x) ^ 2 ∂μ) * Real.log (∫ x, Real.exp (α * h x) ^ 2 ∂μ) = _
      rw [hE2, hE1, hE3, hLSI, hPI, Real.log_exp, hσρ]
      have hb2 : b ^ 2 = 4 * α ^ 2 * d := by
        calc b ^ 2 = 4 * α ^ 2 * Real.sqrt d ^ 2 := by rw [hb, ha]; ring
          _ = _ := by rw [hsq]
      have : b * (ρ⁻¹ * b * Real.exp (ρ⁻¹ * b ^ 2 / 2)) -
          Real.exp (ρ⁻¹ * b ^ 2 / 2) * (ρ⁻¹ * b ^ 2 / 2) =
          ρ⁻¹ * b ^ 2 * Real.exp (ρ⁻¹ * b ^ 2 / 2) / 2 := by ring
      rw [this, hb2]; ring

end Extremal

end CutoffRigidity.Paper
