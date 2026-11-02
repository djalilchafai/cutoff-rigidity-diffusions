module

public import CutoffRigidity.Extra.GaussIso1

/-! # Mehler averages: derivatives in `x` (stage 2a of the Bobkov inequality) -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace CutoffRigidity.GaussIso

/-- `mT h a b x = ∫ h (a x + b y) dγ(y)`: the Mehler average (`a = e^{-s}`, `b = √(1-e^{-2s})`). -/
noncomputable def mT (h : ℝ → ℝ) (a b x : ℝ) : ℝ := ∫ y, h (a * x + b * y) ∂γ1

/-- Bounded continuous functions. -/
structure BC (h : ℝ → ℝ) : Prop where
  cont : Continuous h
  bdd : ∃ C, ∀ x, |h x| ≤ C

lemma BC.integrable {h : ℝ → ℝ} (hh : BC h) (a b x : ℝ) :
    Integrable (fun y => h (a * x + b * y)) γ1 := by
  obtain ⟨C, hC⟩ := hh.bdd
  refine Integrable.mono' (integrable_const C) ?_ (Eventually.of_forall fun y => ?_)
  · exact (hh.cont.comp (by fun_prop)).aestronglyMeasurable
  · simpa using hC _

lemma mT_abs_le {h : ℝ → ℝ} {C : ℝ} (hC : ∀ x, |h x| ≤ C) (a b x : ℝ) : |mT h a b x| ≤ C := by
  unfold mT
  have := norm_integral_le_of_norm_le_const (μ := γ1) (f := fun y => h (a * x + b * y)) (C := C)
    (Eventually.of_forall fun y => by simpa using hC _)
  simpa using this

lemma BC.mT {h : ℝ → ℝ} (hh : BC h) (a b : ℝ) : BC (mT h a b) := by
  obtain ⟨C, hC⟩ := hh.bdd
  refine ⟨?_, ⟨C, mT_abs_le hC a b⟩⟩
  unfold CutoffRigidity.GaussIso.mT
  obtain ⟨C, hC⟩ := hh.bdd
  refine continuous_of_dominated (bound := fun _ => C) (fun x => ?_) (fun x => ?_) ?_ ?_
  · exact (hh.cont.comp (by fun_prop)).aestronglyMeasurable
  · exact Eventually.of_forall fun y => by simpa using hC _
  · exact integrable_const C
  · exact Eventually.of_forall fun y => hh.cont.comp (by fun_prop : Continuous fun x : ℝ => a * x + b * y)

/-- Differentiation of a Mehler average in `x`. -/
lemma hasDerivAt_mT {h h1 : ℝ → ℝ} (hd : ∀ x, HasDerivAt h (h1 x) x) (hh : BC h) (hh1 : BC h1)
    (a b x : ℝ) : HasDerivAt (mT h a b) (a * mT h1 a b x) x := by
  obtain ⟨C1, hC1⟩ := hh1.bdd
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := γ1) (𝕜 := ℝ)
    (F := fun x y => h (a * x + b * y)) (F' := fun x y => a * h1 (a * x + b * y)) (x₀ := x)
    (s := univ) (bound := fun _ => |a| * C1) Filter.univ_mem
    (Eventually.of_forall fun x => (hh.cont.comp (by fun_prop)).aestronglyMeasurable)
    (hh.integrable a b x)
    ((hh1.cont.comp (by fun_prop)).const_mul a |>.aestronglyMeasurable)
    (Eventually.of_forall fun y x _ => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hC1 _) (abs_nonneg a))
    (integrable_const _)
    (Eventually.of_forall fun y x _ => by
      have := (hd (a * x + b * y)).comp x
        (((hasDerivAt_id x).const_mul a).add_const (b * y))
      exact this.congr_deriv (by ring))
  unfold mT
  have := key.2
  rwa [integral_const_mul] at this

/-- `e^{-s}`. -/
noncomputable def rr (s : ℝ) : ℝ := Real.exp (-s)
/-- `√(1-e^{-2s})`. -/
noncomputable def sg (s : ℝ) : ℝ := Real.sqrt (1 - Real.exp (-2 * s))

lemma rr_pos (s : ℝ) : 0 < rr s := Real.exp_pos _
lemma rr_le_one {s : ℝ} (hs : 0 ≤ s) : rr s ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
lemma rr_sq (s : ℝ) : rr s ^ 2 = Real.exp (-2 * s) := by
  rw [rr, ← Real.exp_nat_mul]; congr 1; push_cast; ring

lemma sg_pos {s : ℝ} (hs : 0 < s) : 0 < sg s := by
  unfold sg
  apply Real.sqrt_pos.2
  have : Real.exp (-2 * s) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  linarith

lemma sg_nonneg (s : ℝ) : 0 ≤ sg s := Real.sqrt_nonneg _

lemma sg_sq {s : ℝ} (hs : 0 ≤ s) : sg s ^ 2 = 1 - rr s ^ 2 := by
  unfold sg
  rw [Real.sq_sqrt, rr_sq]
  have : Real.exp (-2 * s) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  linarith

lemma sg_mono {s t : ℝ} (hst : s ≤ t) : sg s ≤ sg t := by
  unfold sg
  apply Real.sqrt_le_sqrt
  have : Real.exp (-2 * t) ≤ Real.exp (-2 * s) := Real.exp_le_exp.2 (by linarith)
  linarith

lemma hasDerivAt_rr (s : ℝ) : HasDerivAt rr (-rr s) s := by
  have := (hasDerivAt_neg s).exp
  show HasDerivAt (fun s => Real.exp (-s)) (-Real.exp (-s)) s
  simpa using this

lemma hasDerivAt_sg {s : ℝ} (hs : 0 < s) : HasDerivAt sg (Real.exp (-2 * s) / sg s) s := by
  have h1 : HasDerivAt (fun s : ℝ => 1 - Real.exp (-2 * s)) (2 * Real.exp (-2 * s)) s := by
    have := (((hasDerivAt_id s).const_mul (-2:ℝ)).exp).const_sub 1
    refine this.congr_deriv ?_; simp; ring
  have hne : (1 - Real.exp (-2 * s)) ≠ 0 := by
    have : Real.exp (-2 * s) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  have := h1.sqrt hne
  have hsg : sg s ≠ 0 := (sg_pos hs).ne'
  have e : sg = fun y => Real.sqrt (1 - Real.exp (-2 * y)) := rfl
  rw [e]
  convert this using 1
  have hs' : Real.sqrt (1 - Real.exp (-2 * s)) ≠ 0 := hsg
  show Real.exp (-2 * s) / Real.sqrt (1 - Real.exp (-2 * s)) = _
  field_simp

/-- Heat equation for the Mehler average (`s > 0`). -/
lemma hasDerivAt_mT_time {h h1 h2 : ℝ → ℝ} (hd : ∀ x, HasDerivAt h (h1 x) x)
    (hd1 : ∀ x, HasDerivAt h1 (h2 x) x) (hh : BC h) (hh1 : BC h1) (hh2 : BC h2) (x : ℝ)
    {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun s => mT h (rr s) (sg s) x)
      (rr s ^ 2 * mT h2 (rr s) (sg s) x - x * (rr s * mT h1 (rr s) (sg s) x)) s := by
  obtain ⟨C1, hC1⟩ := hh1.bdd
  set M : ℝ := (sg (s / 2))⁻¹ with hM
  have hsg2 : 0 < sg (s / 2) := sg_pos (by linarith)
  have hball : ∀ t ∈ Metric.ball s (s / 2), 0 < t ∧ sg (s / 2) ≤ sg t := by
    intro t ht
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
    exact ⟨by linarith, sg_mono (by linarith)⟩
  have hint : Integrable (fun y : ℝ => C1 * (|x| + M * |y|)) γ1 := by
    have h1 : Integrable (fun y : ℝ => |y|) γ1 := (memLp_id_gaussianReal 1).integrable le_rfl |>.norm
    exact (((integrable_const |x|).add (h1.const_mul M)).const_mul C1)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := γ1) (𝕜 := ℝ)
    (F := fun t y => h (rr t * x + sg t * y))
    (F' := fun t y => h1 (rr t * x + sg t * y) * (-rr t * x + (Real.exp (-2 * t) / sg t) * y))
    (x₀ := s) (s := Metric.ball s (s / 2)) (bound := fun y => C1 * (|x| + M * |y|))
    (Metric.ball_mem_nhds _ (by linarith))
    (Eventually.of_forall fun t => (hh.cont.comp (by fun_prop)).aestronglyMeasurable)
    (hh.integrable _ _ x)
    (((hh1.cont.comp (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun y t ht => by
      obtain ⟨ht0, htm⟩ := hball t ht
      have hsgt := lt_of_lt_of_le hsg2 htm
      have hr : |-rr t * x| ≤ |x| := by
        rw [abs_mul, abs_neg, abs_of_pos (rr_pos t)]
        exact mul_le_of_le_one_left (abs_nonneg _) (rr_le_one ht0.le)
      have hq : |Real.exp (-2 * t) / sg t| ≤ M := by
        rw [abs_of_pos (div_pos (Real.exp_pos _) hsgt), hM]
        have : Real.exp (-2 * t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
        calc Real.exp (-2 * t) / sg t ≤ 1 / sg t := by gcongr
          _ ≤ 1 / sg (s / 2) := by gcongr
          _ = (sg (s / 2))⁻¹ := one_div _
      rw [Real.norm_eq_abs, abs_mul]
      calc |h1 (rr t * x + sg t * y)| * |-rr t * x + Real.exp (-2 * t) / sg t * y|
          ≤ C1 * (|x| + M * |y|) := by
            apply mul_le_mul (hC1 _) _ (abs_nonneg _) ((abs_nonneg _).trans (hC1 0))
            calc |-rr t * x + Real.exp (-2 * t) / sg t * y|
                ≤ |-rr t * x| + |Real.exp (-2 * t) / sg t * y| := abs_add_le _ _
              _ ≤ |x| + M * |y| := by
                rw [abs_mul (Real.exp (-2 * t) / sg t) y]
                exact add_le_add hr (mul_le_mul_of_nonneg_right hq (abs_nonneg _))
              )
    hint
    (Eventually.of_forall fun y t ht => by
      obtain ⟨ht0, -⟩ := hball t ht
      have h3 := ((hasDerivAt_rr t).mul_const x).add (((hasDerivAt_sg ht0)).mul_const y)
      have := (hd (rr t * x + sg t * y)).comp t h3
      exact this)
  have hsgs : sg s ≠ 0 := (sg_pos hs).ne'
  obtain ⟨C2, hC2⟩ := hh2.bdd
  have hk : ∀ y, HasDerivAt (fun y => h1 (rr s * x + sg s * y)) (sg s * h2 (rr s * x + sg s * y)) y := by
    intro y
    have := (hd1 (rr s * x + sg s * y)).comp y (((hasDerivAt_id y).const_mul (sg s)).const_add (rr s * x))
    exact this.congr_deriv (by simp [mul_comm])
  have hstein := stein (k := fun y => h1 (rr s * x + sg s * y))
    (k' := fun y => sg s * h2 (rr s * x + sg s * y)) hk
    ⟨C1, fun y => hC1 _⟩ ⟨|sg s| * C2, fun y => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC2 _) (abs_nonneg _)⟩
    ((hh2.cont.comp (by fun_prop)).const_mul _)
  have hI1 := hh1.integrable (rr s) (sg s) x
  have hI2 : Integrable (fun y : ℝ => y * h1 (rr s * x + sg s * y)) γ1 := by
    have := ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl).bdd_mul (c := C1)
      (hh1.cont.comp (by fun_prop : Continuous fun y : ℝ => rr s * x + sg s * y)).aestronglyMeasurable
      (Eventually.of_forall fun y => by simpa using hC1 _)
    exact this.congr (Eventually.of_forall fun y => by simp [mul_comm])
  have hval : ∫ y, h1 (rr s * x + sg s * y) * (-rr s * x + (Real.exp (-2 * s) / sg s) * y) ∂γ1 =
      rr s ^ 2 * mT h2 (rr s) (sg s) x - x * (rr s * mT h1 (rr s) (sg s) x) := by
    have e1 : ∀ y, h1 (rr s * x + sg s * y) * (-rr s * x + (Real.exp (-2 * s) / sg s) * y) =
        (-rr s * x) * h1 (rr s * x + sg s * y) + (Real.exp (-2 * s) / sg s) * (y * h1 (rr s * x + sg s * y)) := by
      intro y; ring
    simp_rw [e1]
    rw [integral_add (hI1.const_mul _) (hI2.const_mul _), integral_const_mul, integral_const_mul]
    rw [hstein]
    unfold mT
    rw [integral_const_mul, ← rr_sq]
    field_simp
    ring
  have := key.2
  rw [hval] at this
  exact this

end CutoffRigidity.GaussIso
