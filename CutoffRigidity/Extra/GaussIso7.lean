module

public import CutoffRigidity.Extra.GaussIso6

/-! # Mehler invariance and the `C¹` one-dimensional Bobkov inequality (stage 4b) -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal

set_option linter.unusedSectionVars false

namespace CutoffRigidity.GaussIso

lemma hasLaw_mul_fst (a : ℝ) :
    HasLaw (fun ω : ℝ × ℝ => a * ω.1) (gaussianReal 0 ⟨a ^ 2, sq_nonneg _⟩) (γ1.prod γ1) := by
  refine ⟨by fun_prop, ?_⟩
  have h1 : (γ1.prod γ1).map (fun ω : ℝ × ℝ => a * ω.1) = γ1.map (fun x => a * x) := by
    rw [show (fun ω : ℝ × ℝ => a * ω.1) = (fun x => a * x) ∘ Prod.fst from rfl,
      ← Measure.map_map (by fun_prop) measurable_fst, Measure.map_fst_prod]
    simp
  rw [h1]
  have := gaussianReal_map_const_mul (μ := 0) (v := 1) a
  rw [show γ1 = gaussianReal 0 1 from rfl, this]
  simp
  rfl

lemma hasLaw_mul_snd (a : ℝ) :
    HasLaw (fun ω : ℝ × ℝ => a * ω.2) (gaussianReal 0 ⟨a ^ 2, sq_nonneg _⟩) (γ1.prod γ1) := by
  refine ⟨by fun_prop, ?_⟩
  have h1 : (γ1.prod γ1).map (fun ω : ℝ × ℝ => a * ω.2) = γ1.map (fun x => a * x) := by
    rw [show (fun ω : ℝ × ℝ => a * ω.2) = (fun x => a * x) ∘ Prod.snd from rfl,
      ← Measure.map_map (by fun_prop) measurable_snd, Measure.map_snd_prod]
    simp
  rw [h1]
  have := gaussianReal_map_const_mul (μ := 0) (v := 1) a
  rw [show γ1 = gaussianReal 0 1 from rfl, this]
  simp
  rfl

lemma map_affine_prod {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) :
    (γ1.prod γ1).map (fun ω : ℝ × ℝ => a * ω.1 + b * ω.2) = γ1 := by
  have hind := indepFun_prod (μ := γ1) (ν := γ1) (X := fun x : ℝ => a * x) (Y := fun x : ℝ => b * x)
    (by fun_prop) (by fun_prop)
  have := gaussianReal_add_gaussianReal_of_indepFun hind (hasLaw_mul_fst a) (hasLaw_mul_snd b)
  have e : (⟨a ^ 2, sq_nonneg _⟩ + ⟨b ^ 2, sq_nonneg _⟩ : ℝ≥0) = 1 := by
    apply NNReal.coe_injective
    show a ^ 2 + b ^ 2 = 1
    exact hab
  rw [e, add_zero] at this
  exact this

/-- Invariance of the standard Gaussian under the Mehler average. -/
lemma mehler_invariant {h : ℝ → ℝ} (hh : BC h) {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) :
    ∫ x, mT h a b x ∂γ1 = ∫ y, h y ∂γ1 := by
  obtain ⟨C, hC⟩ := hh.bdd
  have hint : Integrable (fun p : ℝ × ℝ => h (a * p.1 + b * p.2)) (γ1.prod γ1) :=
    Integrable.mono' (integrable_const C) (hh.cont.comp (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun p => by simpa using hC _)
  have h1 : ∫ p, h (a * p.1 + b * p.2) ∂(γ1.prod γ1) = ∫ x, mT h a b x ∂γ1 := by
    rw [integral_prod _ hint]; rfl
  have h2 : ∫ p, h (a * p.1 + b * p.2) ∂(γ1.prod γ1) = ∫ y, h y ∂γ1 := by
    have := integral_map (μ := γ1.prod γ1) (φ := fun ω : ℝ × ℝ => a * ω.1 + b * ω.2) (f := h)
      (by fun_prop) hh.cont.aestronglyMeasurable
    rw [map_affine_prod hab] at this
    exact this.symm
  rw [← h1, h2]


lemma BC.const_mul {g : ℝ → ℝ} (hg : BC g) (c : ℝ) : BC (fun x => c * g x) := by
  obtain ⟨C, hC⟩ := hg.bdd
  exact ⟨hg.cont.const_mul c, |c| * C, fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _)⟩

/-- Initial data of class `C¹`: bounded, with bounded continuous derivative, values in `[ε,1-ε]`. -/
structure Good1 (ε : ℝ) (f f1 : ℝ → ℝ) : Prop where
  hε : 0 < ε
  d0 : ∀ x, HasDerivAt f (f1 x) x
  b0 : BC f
  b1 : BC f1
  rng : ∀ x, ε ≤ f x ∧ f x ≤ 1 - ε

lemma G0_zero_gen (f : ℝ → ℝ) (x : ℝ) : G0 f 0 x = f x := by
  unfold G0 mT
  have : sg 0 = 0 := by simp [sg]
  simp [this, rr]

lemma G1_zero_gen (f1 : ℝ → ℝ) (x : ℝ) : G1 f1 0 x = f1 x := by
  unfold G1 mT
  have : sg 0 = 0 := by simp [sg]
  simp [this, rr]

section good1
variable {ε : ℝ} {f f1 : ℝ → ℝ} (H : Good1 ε f f1)
include H

/-- Smoothed data at time `s > 0`: `P_s f` and its first three derivatives. -/
noncomputable def sm2 (f1 : ℝ → ℝ) (s x : ℝ) : ℝ :=
  rr s * ((rr s / sg s) * mTw (fun y => y * 1 - 0) f1 (rr s) (sg s) x)
noncomputable def sm3 (f1 : ℝ → ℝ) (s x : ℝ) : ℝ :=
  rr s * ((rr s / sg s) * ((rr s / sg s) * mTw (fun y => y * (y * 1 - 0) - 1) f1 (rr s) (sg s) x))

lemma Good1.smooth {s : ℝ} (hs : 0 < s) : Good ε (G0 f s) (G1 f1 s) (sm2 f1 s) (sm3 f1 s) := by
  have hb : sg s ≠ 0 := (sg_pos hs).ne'
  have hq1 : ∀ y : ℝ, HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 y := fun y => hasDerivAt_const y 1
  have hq2 : ∀ y : ℝ, HasDerivAt (fun y : ℝ => y * 1 - 0) 1 y := fun y => by
    simpa using (hasDerivAt_id y).sub_const 0
  have e1 : mTw (fun _ => (1:ℝ)) f1 (rr s) (sg s) = mT f1 (rr s) (sg s) :=
    funext fun x => mTw_one f1 _ _ x
  have D1 := fun x => hasDerivAt_mTw H.b1 hq1 continuous_const (Cq := 1) (Cq' := 0)
    (fun y => by simp) (fun y => by simp) hb (a := rr s) x
  have D2 := fun x => hasDerivAt_mTw H.b1 hq2 continuous_const (Cq := 1) (Cq' := 1)
    (fun y => by simp) (fun y => by simp) hb (a := rr s) x
  refine
  { hε := H.hε
    d0 := fun x => hasDerivAt_mT H.d0 H.b0 H.b1 _ _ x
    d1 := fun x => ?_
    d2 := fun x => ?_
    b0 := H.b0.mT _ _
    b1 := H.b1.mT _ _ |>.const_mul _
    b2 := ?_
    b3 := ?_
    rng := fun x => ?_ }
  · have := (D1 x)
    rw [e1] at this
    have := this.const_mul (rr s)
    exact this
  · have := (D2 x).const_mul ((rr s / sg s))
    have := this.const_mul (rr s)
    exact this
  · have hw : ∀ y : ℝ, |y * 1 - 0| ≤ 1 * (1 + |y|) ^ 3 := fun y => by
      simp only [mul_one, sub_zero, one_mul]
      have : 1 + |y| ≤ (1 + |y|) ^ 3 := by
        simpa using one_add_abs_pow_le (abs_nonneg y) (j := 1) (by norm_num)
      linarith [abs_nonneg y]
    exact ((H.b1.weighted (by fun_prop) hw (rr s) (sg s)).const_mul _).const_mul _
  · have hw : ∀ y : ℝ, |y * (y * 1 - 0) - 1| ≤ 1 * (1 + |y|) ^ 3 := fun y => by
      have h2 : (1 + |y|) ^ 2 ≤ (1 + |y|) ^ 3 := one_add_abs_pow_le (abs_nonneg y) (by norm_num)
      have h3 : |y * (y * 1 - 0) - 1| ≤ y ^ 2 + 1 := by
        calc |y * (y * 1 - 0) - 1| ≤ |y * (y * 1 - 0)| + |1| := abs_sub _ _
          _ = y ^ 2 + 1 := by simp [pow_two, abs_mul_abs_self]
      nlinarith [sq_abs y, abs_nonneg y]
    exact (((H.b1.weighted (by fun_prop) hw (rr s) (sg s)).const_mul _).const_mul _).const_mul _
  · have h1 : ∀ y : ℝ, ε ≤ f (rr s * x + sg s * y) := fun y => (H.rng _).1
    have h2 : ∀ y : ℝ, f (rr s * x + sg s * y) ≤ 1 - ε := fun y => (H.rng _).2
    constructor
    · have := integral_mono (μ := γ1) (integrable_const ε) (H.b0.integrable (rr s) (sg s) x) (fun y => h1 y)
      simpa [G0, mT] using this
    · have := integral_mono (μ := γ1) (H.b0.integrable (rr s) (sg s) x) (integrable_const (1 - ε)) (fun y => h2 y)
      simpa [G0, mT] using this


lemma Good1.G0_rng (s x : ℝ) : ε ≤ G0 f s x ∧ G0 f s x ≤ 1 - ε := by
  have h1 : ∀ y : ℝ, ε ≤ f (rr s * x + sg s * y) := fun y => (H.rng _).1
  have h2 : ∀ y : ℝ, f (rr s * x + sg s * y) ≤ 1 - ε := fun y => (H.rng _).2
  constructor
  · have := integral_mono (μ := γ1) (integrable_const ε) (H.b0.integrable (rr s) (sg s) x) (fun y => h1 y)
    simpa [G0, mT] using this
  · have := integral_mono (μ := γ1) (H.b0.integrable (rr s) (sg s) x) (integrable_const (1 - ε)) (fun y => h2 y)
    simpa [G0, mT] using this

lemma Good1.G0_mem (s x : ℝ) : G0 f s x ∈ Ioo (0:ℝ) 1 :=
  ⟨H.hε.trans_le (H.G0_rng s x).1, by linarith [(H.G0_rng s x).2, H.hε]⟩

lemma Good1.continuous_pF (s : ℝ) : Continuous (pF (G0 f s) (G1 f1 s)) := by
  have hg0 : Continuous (G0 f s) := (H.b0.mT (rr s) (sg s)).cont
  have hg1 : Continuous (G1 f1 s) := (H.b1.mT (rr s) (sg s)).cont.const_mul _
  have hc : Continuous fun x => gI (G0 f s x) :=
    continuous_iff_continuousAt.2 fun x => ContinuousAt.comp (f := G0 f s) (x := x)
      (hasDerivAt_gI (H.G0_mem s x)).continuousAt hg0.continuousAt
  unfold pF
  exact Real.continuous_sqrt.comp ((hc.pow 2).add (hg1.pow 2))

lemma Good1.bobkov_pos {s : ℝ} (hs : 0 < s) :
    gI (∫ y, f y ∂γ1) ≤ Psi f f1 s := by
  have h := (H.smooth hs).bobkov
  have hab : rr s ^ 2 + sg s ^ 2 = 1 := by rw [sg_sq hs.le]; ring
  have hinv : ∫ x, G0 f s x ∂γ1 = ∫ y, f y ∂γ1 := mehler_invariant H.b0 hab
  rw [show (fun x => G0 f s x) = G0 f s from rfl] at hinv
  rw [hinv] at h
  exact h

lemma Good1.tendsto_Psi_zero : Tendsto (Psi f f1) (𝓝[>] 0) (𝓝 (Psi f f1 0)) := by
  obtain ⟨C1, hC1⟩ := H.b1.bdd
  have hC1' : 0 ≤ C1 := (abs_nonneg _).trans (hC1 0)
  have hlim : ∀ x, Tendsto (fun s => pF (G0 f s) (G1 f1 s) x) (𝓝[>] 0)
      (𝓝 (pF (G0 f 0) (G1 f1 0) x)) := by
    intro x
    have hg0 : Continuous fun s => G0 f s x := continuous_mT_s H.b0 x
    have hg1 : Continuous fun s => G1 f1 s x := continuous_rr.mul (continuous_mT_s H.b1 x)
    have hc : Continuous fun s => gI (G0 f s x) :=
      continuous_iff_continuousAt.2 fun s => ContinuousAt.comp (f := fun s => G0 f s x) (x := s)
        (hasDerivAt_gI (H.G0_mem s x)).continuousAt hg0.continuousAt
    have : Continuous fun s => pF (G0 f s) (G1 f1 s) x := by
      show Continuous fun s => Real.sqrt (gI (G0 f s x) ^ 2 + G1 f1 s x ^ 2)
      exact Real.continuous_sqrt.comp ((hc.pow 2).add (hg1.pow 2))
    exact (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have := tendsto_integral_filter_of_dominated_convergence (μ := γ1) (l := 𝓝[>] (0:ℝ))
    (F := fun s x => pF (G0 f s) (G1 f1 s) x) (f := fun x => pF (G0 f 0) (G1 f1 0) x)
    (bound := fun _ => gφ 0 + C1)
    (Eventually.of_forall fun s => (H.continuous_pF s).aestronglyMeasurable)
    (by
      filter_upwards [self_mem_nhdsWithin] with s hs
      refine Eventually.of_forall fun x => ?_
      have hs' : (0:ℝ) ≤ s := le_of_lt hs
      have hpos : 0 < pF (G0 f s) (G1 f1 s) x := by
        unfold pF
        apply Real.sqrt_pos.2
        have := gI_pos (H.G0_mem s x); positivity
      rw [Real.norm_eq_abs, abs_of_pos hpos]
      have hg : |G1 f1 s x| ≤ C1 := abs_G1_le hC1 hs' x
      unfold pF
      calc Real.sqrt (gI (G0 f s x) ^ 2 + G1 f1 s x ^ 2) ≤ Real.sqrt ((gφ 0 + C1) ^ 2) := by
            apply Real.sqrt_le_sqrt
            have h1 : gI (G0 f s x) ≤ gφ 0 := gI_le _
            have h2 : G1 f1 s x ^ 2 ≤ C1 ^ 2 := by nlinarith [abs_nonneg (G1 f1 s x), sq_abs (G1 f1 s x)]
            nlinarith [gI_nonneg (G0 f s x), gφ_pos 0]
        _ = gφ 0 + C1 := Real.sqrt_sq (by have := gφ_pos 0; linarith))
    (integrable_const _)
    (Eventually.of_forall hlim)
  exact this

/-- **One-dimensional Bobkov inequality for `C¹` data** with values in `[ε,1-ε]`. -/
theorem Good1.bobkov :
    gI (∫ y, f y ∂γ1) ≤ ∫ x, Real.sqrt (gI (f x) ^ 2 + f1 x ^ 2) ∂γ1 := by
  have h0 : Psi f f1 0 = ∫ x, Real.sqrt (gI (f x) ^ 2 + f1 x ^ 2) ∂γ1 := by
    unfold Psi
    congr 1; funext x
    simp only [pF, G0_zero_gen, G1_zero_gen]
  rw [← h0]
  refine ge_of_tendsto H.tendsto_Psi_zero ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact H.bobkov_pos hs

end good1
end CutoffRigidity.GaussIso
