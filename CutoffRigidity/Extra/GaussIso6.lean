module

public import CutoffRigidity.Extra.GaussIso5

/-! # Smoothing of Mehler averages (stage 4a): derivatives of `x ↦ ∫ h(ax+by) dγ` for merely continuous `h`

The "primitive trick": with `Hh(z) = ∫₀^z h`, Stein's lemma gives `∫ q(y) h(ax+by) dγ = (1/b) ∫ (y q - q') Hh(ax+by) dγ`,
and the right-hand side is `C¹` in `x`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology

set_option linter.unusedSectionVars false

namespace CutoffRigidity.GaussIso

lemma integrable_γ1_iff (g : ℝ → ℝ) : Integrable g γ1 ↔ Integrable (fun x => gφ x * g x) := by
  have h : γ1 = volume.withDensity (gaussianPDF 0 1) := gaussianReal_of_var_ne_zero 0 one_ne_zero
  rw [h, integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
    (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp [toReal_gaussianPDF, gφ, smul_eq_mul]

lemma integrable_abs_pow_γ1 (n : ℕ) : Integrable (fun y : ℝ => |y| ^ n) γ1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have := (memLp_id_gaussianReal (μ := 0) (v := 1) (n : NNReal)).integrable_norm_pow
      (by simpa using hn.ne')
    simpa using this

lemma integrable_poly3 : Integrable (fun y : ℝ => (1 + |y|) ^ 3) γ1 := by
  have e : ∀ y : ℝ, (1 + |y|) ^ 3 = 1 + 3 * |y| + 3 * |y| ^ 2 + |y| ^ 3 := fun y => by ring
  simp_rw [e]
  have h1 := integrable_abs_pow_γ1 1
  have h2 := integrable_abs_pow_γ1 2
  have h3 := integrable_abs_pow_γ1 3
  simp only [pow_one] at h1
  exact (((integrable_const (1:ℝ)).add (h1.const_mul 3)).add (h2.const_mul 3)).add h3

/-- Integrability from a cubic growth bound. -/
lemma integrable_of_cubic {g : ℝ → ℝ} (hg : Continuous g) {C : ℝ} (hb : ∀ y, |g y| ≤ C * (1 + |y|) ^ 3) :
    Integrable g γ1 :=
  Integrable.mono' (integrable_poly3.const_mul C) hg.aestronglyMeasurable
    (Eventually.of_forall fun y => by simpa using hb y)

/-- **Stein's lemma with growth conditions.** -/
lemma stein' {k k' : ℝ → ℝ} (hk : ∀ x, HasDerivAt k (k' x) x) (hk'c : Continuous k')
    (i1 : Integrable (fun y => y * k y) γ1) (i2 : Integrable k' γ1) (i3 : Integrable k γ1) :
    ∫ y, y * k y ∂γ1 = ∫ y, k' y ∂γ1 := by
  have hkc : Continuous k := continuous_iff_continuousAt.2 fun x => (hk x).continuousAt
  have j1 : Integrable (fun x => k x * (-x * gφ x)) := by
    have := ((integrable_γ1_iff _).1 i1).neg
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp; ring
  have j2 : Integrable (fun x => k' x * gφ x) := by
    have := (integrable_γ1_iff _).1 i2
    exact this.congr (Eventually.of_forall fun x => by simp [mul_comm])
  have j3 : Integrable (fun x => k x * gφ x) := by
    have := (integrable_γ1_iff _).1 i3
    exact this.congr (Eventually.of_forall fun x => by simp [mul_comm])
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := k) (v := gφ) (u' := k')
    (v' := fun x => -x * gφ x) (fun x _ => hk x) (fun x _ => hasDerivAt_gφ x) j1 j2 j3
  rw [integral_γ1, integral_γ1]
  simp only [smul_eq_mul]
  have e1 : ∫ x, gφ x * (x * k x) = -∫ x, k x * (-x * gφ x) := by
    rw [← integral_neg]; congr 1; funext x; ring
  have e2 : ∫ x, gφ x * k' x = ∫ x, k' x * gφ x := by congr 1; funext x; ring
  rw [e1, e2, key]; ring

/-- Primitive of a continuous function. -/
noncomputable def prim (h : ℝ → ℝ) (z : ℝ) : ℝ := ∫ t in (0:ℝ)..z, h t

lemma hasDerivAt_prim {h : ℝ → ℝ} (hh : Continuous h) (z : ℝ) : HasDerivAt (prim h) (h z) z :=
  intervalIntegral.integral_hasDerivAt_right (hh.intervalIntegrable 0 z)
    hh.aestronglyMeasurable.stronglyMeasurableAtFilter hh.continuousAt

lemma abs_prim_le {h : ℝ → ℝ} {C : ℝ} (hC : ∀ x, |h x| ≤ C) (z : ℝ) : |prim h z| ≤ C * |z| := by
  unfold prim
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := z) (f := h) (C := C)
    (fun t _ => by simpa using hC t)
  simpa [Real.norm_eq_abs, mul_comm] using this

/-- Weighted Mehler average. -/
noncomputable def mTw (w h : ℝ → ℝ) (a b x : ℝ) : ℝ := ∫ y, w y * h (a * x + b * y) ∂γ1

lemma mTw_one (h : ℝ → ℝ) (a b x : ℝ) : mTw (fun _ => 1) h a b x = mT h a b x := by
  simp [mTw, mT]


lemma one_add_abs_pow_le {t : ℝ} (ht : 0 ≤ t) {j : ℕ} (hj : j ≤ 3) : (1 + t) ^ j ≤ (1 + t) ^ 3 :=
  pow_le_pow_right₀ (by linarith) hj

lemma abs_affine_le (a b x y : ℝ) : |a * x + b * y| ≤ (|a * x| + |b|) * (1 + |y|) := by
  calc |a * x + b * y| ≤ |a * x| + |b * y| := abs_add_le _ _
    _ ≤ (|a * x| + |b|) * (1 + |y|) := by
      rw [abs_mul b y]
      nlinarith [abs_nonneg (a * x), abs_nonneg b, abs_nonneg y, mul_nonneg (abs_nonneg (a * x)) (abs_nonneg y)]

/-- The pieces of the integration-by-parts identity are controlled by `(1+|y|)^3`. -/
lemma weighted_identity {h : ℝ → ℝ} (hh : BC h) {q q' : ℝ → ℝ}
    (hq : ∀ y, HasDerivAt q (q' y) y) (hq'c : Continuous q') {Cq Cq' : ℝ}
    (hqb : ∀ y, |q y| ≤ Cq * (1 + |y|)) (hq'b : ∀ y, |q' y| ≤ Cq')
    {a b : ℝ} (hb : b ≠ 0) (x : ℝ) :
    mTw q h a b x = b⁻¹ * ∫ y, (y * q y - q' y) * prim h (a * x + b * y) ∂γ1 := by
  obtain ⟨C, hC⟩ := hh.bdd
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hqc : Continuous q := continuous_iff_continuousAt.2 fun x => (hq x).continuousAt
  have hCq : 0 ≤ Cq := by
    have := (abs_nonneg _).trans (hqb 0); simpa using this
  have hCq' : 0 ≤ Cq' := (abs_nonneg _).trans (hq'b 0)
  set M : ℝ := C * (|a * x| + |b|) with hM
  have hM0 : 0 ≤ M := by positivity
  have hprim : ∀ y, |prim h (a * x + b * y)| ≤ M * (1 + |y|) := fun y =>
    (abs_prim_le hC _).trans (by
      rw [hM, mul_assoc]; exact mul_le_mul_of_nonneg_left (abs_affine_le a b x y) hC0)
  have hpc : Continuous fun y => prim h (a * x + b * y) :=
    (continuous_iff_continuousAt.2 fun z => (hasDerivAt_prim hh.cont z).continuousAt).comp (by fun_prop)
  have hk : ∀ y, HasDerivAt (fun y => q y * prim h (a * x + b * y))
      (q' y * prim h (a * x + b * y) + q y * (h (a * x + b * y) * b)) y := by
    intro y
    have h1 := (hasDerivAt_prim hh.cont (a * x + b * y)).comp y
      (((hasDerivAt_id y).const_mul b).const_add (a * x))
    have := (hq y).mul h1
    exact this.congr_deriv (by simp)
  have hy1 : ∀ y : ℝ, 1 ≤ 1 + |y| := fun y => by linarith [abs_nonneg y]
  have hp2 : ∀ y : ℝ, (1 + |y|) ^ 2 ≤ (1 + |y|) ^ 3 := fun y => one_add_abs_pow_le (abs_nonneg y) (by norm_num)
  have hp1 : ∀ y : ℝ, (1 + |y|) ≤ (1 + |y|) ^ 3 := fun y => by
    simpa using one_add_abs_pow_le (abs_nonneg y) (j := 1) (by norm_num)
  have hqp : ∀ y, |q y * prim h (a * x + b * y)| ≤ (Cq * M) * (1 + |y|) ^ 3 := by
    intro y
    rw [abs_mul]
    calc |q y| * |prim h (a * x + b * y)| ≤ (Cq * (1 + |y|)) * (M * (1 + |y|)) :=
          mul_le_mul (hqb y) (hprim y) (abs_nonneg _) (by positivity)
      _ = (Cq * M) * (1 + |y|) ^ 2 := by ring
      _ ≤ (Cq * M) * (1 + |y|) ^ 3 := mul_le_mul_of_nonneg_left (hp2 y) (by positivity)
  have i3 : Integrable (fun y => q y * prim h (a * x + b * y)) γ1 :=
    integrable_of_cubic (hqc.mul hpc) hqp
  have i1 : Integrable (fun y => y * (q y * prim h (a * x + b * y))) γ1 := by
    refine integrable_of_cubic (C := Cq * M) (continuous_id.mul (hqc.mul hpc)) fun y => ?_
    rw [abs_mul]
    calc |y| * |q y * prim h (a * x + b * y)| ≤ (1 + |y|) * ((Cq * M) * (1 + |y|) ^ 2) := by
          apply mul_le_mul (by linarith [abs_nonneg y]) _ (abs_nonneg _) (by positivity)
          rw [abs_mul]
          calc |q y| * |prim h (a * x + b * y)| ≤ (Cq * (1 + |y|)) * (M * (1 + |y|)) :=
                mul_le_mul (hqb y) (hprim y) (abs_nonneg _) (by positivity)
            _ = (Cq * M) * (1 + |y|) ^ 2 := by ring
      _ = (Cq * M) * (1 + |y|) ^ 3 := by ring
  have ia : Integrable (fun y => q' y * prim h (a * x + b * y)) γ1 := by
    refine integrable_of_cubic (C := Cq' * M) (hq'c.mul hpc) fun y => ?_
    rw [abs_mul]
    calc |q' y| * |prim h (a * x + b * y)| ≤ Cq' * (M * (1 + |y|)) :=
          mul_le_mul (hq'b y) (hprim y) (abs_nonneg _) hCq'
      _ = (Cq' * M) * (1 + |y|) := by ring
      _ ≤ (Cq' * M) * (1 + |y|) ^ 3 := mul_le_mul_of_nonneg_left (hp1 y) (by positivity)
  have ib : Integrable (fun y => q y * (h (a * x + b * y) * b)) γ1 := by
    refine integrable_of_cubic (C := Cq * C * |b|) (hqc.mul (hh.cont.comp (by fun_prop) |>.mul continuous_const)) fun y => ?_
    rw [abs_mul, abs_mul]
    calc |q y| * (|h (a * x + b * y)| * |b|) ≤ (Cq * (1 + |y|)) * (C * |b|) :=
          mul_le_mul (hqb y) (mul_le_mul_of_nonneg_right (hC _) (abs_nonneg _)) (by positivity) (by positivity)
      _ = (Cq * C * |b|) * (1 + |y|) := by ring
      _ ≤ (Cq * C * |b|) * (1 + |y|) ^ 3 := mul_le_mul_of_nonneg_left (hp1 y) (by positivity)
  have hk'c : Continuous fun y => q' y * prim h (a * x + b * y) + q y * (h (a * x + b * y) * b) :=
    (hq'c.mul hpc).add (hqc.mul ((hh.cont.comp (by fun_prop)).mul continuous_const))
  have hst := stein' (k := fun y => q y * prim h (a * x + b * y))
    (k' := fun y => q' y * prim h (a * x + b * y) + q y * (h (a * x + b * y) * b)) hk hk'c i1
    (ia.add ib) i3
  rw [integral_add ia ib] at hst
  have e : ∫ y, (y * q y - q' y) * prim h (a * x + b * y) ∂γ1 =
      (∫ y, y * (q y * prim h (a * x + b * y)) ∂γ1) - ∫ y, q' y * prim h (a * x + b * y) ∂γ1 := by
    rw [← integral_sub i1 ia]; congr 1; funext y; ring
  rw [e, hst]
  have e2 : ∫ y, q y * (h (a * x + b * y) * b) ∂γ1 = b * mTw q h a b x := by
    unfold mTw; rw [← integral_const_mul]; congr 1; funext y; ring
  rw [e2]
  field_simp
  ring


lemma hasDerivAt_weighted_prim {h : ℝ → ℝ} (hh : BC h) {p : ℝ → ℝ} (hp : Continuous p) {Cp : ℝ}
    (hpb : ∀ y, |p y| ≤ Cp * (1 + |y|) ^ 2) (a b x : ℝ) :
    HasDerivAt (fun x => ∫ y, p y * prim h (a * x + b * y) ∂γ1)
      (a * ∫ y, p y * h (a * x + b * y) ∂γ1) x := by
  obtain ⟨C, hC⟩ := hh.bdd
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hCp : 0 ≤ Cp := by have := (abs_nonneg _).trans (hpb 0); simpa using this
  have hpc : ∀ x, Continuous fun y => prim h (a * x + b * y) := fun x =>
    (continuous_iff_continuousAt.2 fun z => (hasDerivAt_prim hh.cont z).continuousAt).comp (by fun_prop)
  have hy1 : ∀ y : ℝ, 1 ≤ 1 + |y| := fun y => by linarith [abs_nonneg y]
  have hp2 : ∀ y : ℝ, (1 + |y|) ^ 2 ≤ (1 + |y|) ^ 3 := fun y => one_add_abs_pow_le (abs_nonneg y) (by norm_num)
  have hint : ∀ x, Integrable (fun y => p y * prim h (a * x + b * y)) γ1 := by
    intro x
    refine integrable_of_cubic (C := Cp * (C * (|a * x| + |b|))) (hp.mul (hpc x)) fun y => ?_
    rw [abs_mul]
    have hpr : |prim h (a * x + b * y)| ≤ C * ((|a * x| + |b|) * (1 + |y|)) :=
      (abs_prim_le hC _).trans (mul_le_mul_of_nonneg_left (abs_affine_le a b x y) hC0)
    calc |p y| * |prim h (a * x + b * y)| ≤ (Cp * (1 + |y|) ^ 2) * (C * ((|a * x| + |b|) * (1 + |y|))) :=
          mul_le_mul (hpb y) hpr (abs_nonneg _) (by positivity)
      _ = (Cp * (C * (|a * x| + |b|))) * (1 + |y|) ^ 3 := by ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := γ1) (𝕜 := ℝ)
    (F := fun x y => p y * prim h (a * x + b * y))
    (F' := fun x y => p y * (h (a * x + b * y) * a)) (x₀ := x)
    (s := univ) (bound := fun y => Cp * C * |a| * (1 + |y|) ^ 3) Filter.univ_mem
    (Eventually.of_forall fun x => (hp.mul (hpc x)).aestronglyMeasurable)
    (hint x)
    ((hp.mul ((hh.cont.comp (by fun_prop)).mul continuous_const)).aestronglyMeasurable)
    (Eventually.of_forall fun y x _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |p y| * (|h (a * x + b * y)| * |a|) ≤ (Cp * (1 + |y|) ^ 2) * (C * |a|) :=
            mul_le_mul (hpb y) (mul_le_mul_of_nonneg_right (hC _) (abs_nonneg _)) (by positivity) (by positivity)
        _ = (Cp * C * |a|) * (1 + |y|) ^ 2 := by ring
        _ ≤ (Cp * C * |a|) * (1 + |y|) ^ 3 := mul_le_mul_of_nonneg_left (hp2 y) (by positivity))
    (integrable_poly3.const_mul _)
    (Eventually.of_forall fun y x _ => by
      have h1 := (hasDerivAt_prim hh.cont (a * x + b * y)).comp x
        (((hasDerivAt_id x).const_mul a).add_const (b * y))
      have := h1.const_mul (p y)
      exact this.congr_deriv (by simp))
  have := key.2
  rw [← integral_const_mul]
  convert this using 2
  funext y; ring

/-- Derivative of the weighted Mehler average of a merely continuous function. -/
lemma hasDerivAt_mTw {h : ℝ → ℝ} (hh : BC h) {q q' : ℝ → ℝ}
    (hq : ∀ y, HasDerivAt q (q' y) y) (hq'c : Continuous q') {Cq Cq' : ℝ}
    (hqb : ∀ y, |q y| ≤ Cq * (1 + |y|)) (hq'b : ∀ y, |q' y| ≤ Cq')
    {a b : ℝ} (hb : b ≠ 0) (x : ℝ) :
    HasDerivAt (mTw q h a b) ((a / b) * mTw (fun y => y * q y - q' y) h a b x) x := by
  have hqc : Continuous q := continuous_iff_continuousAt.2 fun x => (hq x).continuousAt
  have hCq : 0 ≤ Cq := by
    have := (abs_nonneg _).trans (hqb 0); simpa using this
  have hCq' : 0 ≤ Cq' := (abs_nonneg _).trans (hq'b 0)
  have hpb : ∀ y, |y * q y - q' y| ≤ (Cq + Cq') * (1 + |y|) ^ 2 := by
    intro y
    calc |y * q y - q' y| ≤ |y * q y| + |q' y| := abs_sub _ _
      _ ≤ |y| * (Cq * (1 + |y|)) + Cq' := by
          rw [abs_mul]; exact add_le_add (mul_le_mul_of_nonneg_left (hqb y) (abs_nonneg _)) (hq'b y)
      _ ≤ (Cq + Cq') * (1 + |y|) ^ 2 := by
          nlinarith [abs_nonneg y, mul_nonneg hCq (abs_nonneg y), mul_nonneg hCq' (abs_nonneg y),
            mul_nonneg hCq' (sq_nonneg |y|), mul_nonneg hCq (sq_nonneg |y|)]
  have hpc : Continuous fun y => y * q y - q' y := (continuous_id.mul hqc).sub hq'c
  have e : mTw q h a b = fun x => b⁻¹ * ∫ y, (y * q y - q' y) * prim h (a * x + b * y) ∂γ1 :=
    funext fun x => weighted_identity hh hq hq'c hqb hq'b hb x
  rw [e]
  have := (hasDerivAt_weighted_prim hh hpc hpb a b x).const_mul b⁻¹
  refine this.congr_deriv ?_
  unfold mTw
  field_simp

/-- Weighted Mehler averages of bounded continuous functions are bounded continuous. -/
lemma BC.weighted {h : ℝ → ℝ} (hh : BC h) {w : ℝ → ℝ} (hw : Continuous w) {Cw : ℝ}
    (hwb : ∀ y, |w y| ≤ Cw * (1 + |y|) ^ 3) (a b : ℝ) : BC (CutoffRigidity.GaussIso.mTw w h a b) := by
  obtain ⟨C, hC⟩ := hh.bdd
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hCw : 0 ≤ Cw := by have := (abs_nonneg _).trans (hwb 0); simpa using this
  have hbd : ∀ x y, |w y * h (a * x + b * y)| ≤ Cw * C * (1 + |y|) ^ 3 := by
    intro x y
    rw [abs_mul]
    calc |w y| * |h (a * x + b * y)| ≤ (Cw * (1 + |y|) ^ 3) * C :=
          mul_le_mul (hwb y) (hC _) (abs_nonneg _) (by positivity)
      _ = Cw * C * (1 + |y|) ^ 3 := by ring
  refine ⟨?_, ⟨∫ y, Cw * C * (1 + |y|) ^ 3 ∂γ1, fun x => ?_⟩⟩
  · unfold CutoffRigidity.GaussIso.mTw
    refine continuous_of_dominated (bound := fun y => Cw * C * (1 + |y|) ^ 3) (fun x => ?_) (fun x => ?_)
      (integrable_poly3.const_mul _) ?_
    · exact (hw.mul (hh.cont.comp (by fun_prop))).aestronglyMeasurable
    · exact Eventually.of_forall fun y => by simpa using hbd x y
    · exact Eventually.of_forall fun y => continuous_const.mul (hh.cont.comp (by fun_prop))
  · unfold CutoffRigidity.GaussIso.mTw
    have := norm_integral_le_of_norm_le (μ := γ1) (f := fun y => w y * h (a * x + b * y))
      (g := fun y => Cw * C * (1 + |y|) ^ 3) (integrable_poly3.const_mul _)
      (Eventually.of_forall fun y => by simpa using hbd x y)
    simpa using this

end CutoffRigidity.GaussIso
