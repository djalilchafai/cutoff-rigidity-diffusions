module

public import CutoffRigidity.Extra.GaussIso3

/-! # The monotone functional `Ψ(s) = ∫ √(I(P_s f)² + (P_s f)'²) dγ` (stage 3b) -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology

set_option linter.unusedSectionVars false

namespace CutoffRigidity.GaussIso

/-- Initial data: `C³`-type function with bounded derivatives, values in `[ε,1-ε]`. -/
structure Good (ε : ℝ) (f f1 f2 f3 : ℝ → ℝ) : Prop where
  hε : 0 < ε
  d0 : ∀ x, HasDerivAt f (f1 x) x
  d1 : ∀ x, HasDerivAt f1 (f2 x) x
  d2 : ∀ x, HasDerivAt f2 (f3 x) x
  b0 : BC f
  b1 : BC f1
  b2 : BC f2
  b3 : BC f3
  rng : ∀ x, ε ≤ f x ∧ f x ≤ 1 - ε

noncomputable def G0 (f : ℝ → ℝ) (s x : ℝ) : ℝ := mT f (rr s) (sg s) x
noncomputable def G1 (f1 : ℝ → ℝ) (s x : ℝ) : ℝ := rr s * mT f1 (rr s) (sg s) x
noncomputable def G2 (f2 : ℝ → ℝ) (s x : ℝ) : ℝ := rr s ^ 2 * mT f2 (rr s) (sg s) x
noncomputable def G3 (f3 : ℝ → ℝ) (s x : ℝ) : ℝ := rr s ^ 3 * mT f3 (rr s) (sg s) x

lemma continuous_mT_ab {h : ℝ → ℝ} (hh : BC h) (x : ℝ) :
    Continuous (fun p : ℝ × ℝ => mT h p.1 p.2 x) := by
  obtain ⟨C, hC⟩ := hh.bdd
  unfold mT
  refine continuous_of_dominated (bound := fun _ => C) (fun p => ?_) (fun p => ?_) ?_ ?_
  · exact (hh.cont.comp (by fun_prop)).aestronglyMeasurable
  · exact Eventually.of_forall fun y => by simpa using hC _
  · exact integrable_const C
  · exact Eventually.of_forall fun y => hh.cont.comp (by fun_prop : Continuous fun p : ℝ × ℝ => p.1 * x + p.2 * y)

lemma continuous_rr : Continuous rr := by unfold rr; fun_prop
lemma continuous_sg : Continuous sg := by unfold sg; fun_prop

lemma continuous_mT_s {h : ℝ → ℝ} (hh : BC h) (x : ℝ) :
    Continuous (fun s => mT h (rr s) (sg s) x) :=
  (continuous_mT_ab hh x).comp (continuous_rr.prodMk continuous_sg)

lemma abs_SF_le (A q g1 g2 g3 x F K C1 C2 C3 : ℝ) (hF : F ^ 2 = A ^ 2 + g1 ^ 2) (hFp : 0 < F)
    (hq : |q| ≤ K) (h1 : |g1| ≤ C1) (h2 : |g2| ≤ C2) (h3 : |g3| ≤ C3) :
    |(A * (-q * (g2 - x * g1)) + g1 * (g3 - x * g2 - g1)) / F| ≤
      (K * (C1 + C2) + C3 + C2 + C1) * (1 + |x|) := by
  have hK : 0 ≤ K := (abs_nonneg _).trans hq
  have hC1 : 0 ≤ C1 := (abs_nonneg _).trans h1
  have hC2 : 0 ≤ C2 := (abs_nonneg _).trans h2
  have hC3 : 0 ≤ C3 := (abs_nonneg _).trans h3
  have hA : |A| ≤ F := by
    apply abs_le_of_sq_le_sq' _ hFp.le |> fun h => abs_le.2 h
    nlinarith [sq_nonneg g1]
  have hg : |g1| ≤ F := by
    apply abs_le.2; apply abs_le_of_sq_le_sq' _ hFp.le
    nlinarith [sq_nonneg A]
  have hu : |-q * (g2 - x * g1)| ≤ K * (C2 + |x| * C1) := by
    rw [abs_mul, abs_neg]
    have : |g2 - x * g1| ≤ C2 + |x| * C1 := by
      calc |g2 - x * g1| ≤ |g2| + |x * g1| := abs_sub _ _
        _ ≤ C2 + |x| * C1 := by rw [abs_mul]; exact add_le_add h2 (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
    exact mul_le_mul hq this (abs_nonneg _) hK
  have hv : |g3 - x * g2 - g1| ≤ C3 + |x| * C2 + C1 := by
    calc |g3 - x * g2 - g1| ≤ |g3 - x * g2| + |g1| := abs_sub _ _
      _ ≤ |g3| + |x * g2| + |g1| := by gcongr; exact abs_sub _ _
      _ ≤ C3 + |x| * C2 + C1 := by
        rw [abs_mul]; gcongr
  rw [abs_div, abs_of_pos hFp, div_le_iff₀ hFp]
  calc |A * (-q * (g2 - x * g1)) + g1 * (g3 - x * g2 - g1)|
      ≤ |A| * |-q * (g2 - x * g1)| + |g1| * |g3 - x * g2 - g1| := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_mul A (-q * (g2 - x * g1)), abs_mul g1 (g3 - x * g2 - g1)]
    _ ≤ F * (K * (C2 + |x| * C1)) + F * (C3 + |x| * C2 + C1) := by
        gcongr
    _ ≤ _ := by
        have hx := abs_nonneg x
        have key : K * (C2 + |x| * C1) + (C3 + |x| * C2 + C1) ≤
            (K * (C1 + C2) + C3 + C2 + C1) * (1 + |x|) := by
          nlinarith [mul_nonneg hK hC1, mul_nonneg hK hC2, mul_nonneg hx hC1, mul_nonneg hx hC2,
            mul_nonneg hx hC3, mul_nonneg (mul_nonneg hK hx) hC2]
        have := mul_le_mul_of_nonneg_left key hFp.le
        nlinarith [this]

lemma abs_G1_le {h : ℝ → ℝ} {C : ℝ} (hC : ∀ x, |h x| ≤ C) {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    |rr s * mT h (rr s) (sg s) x| ≤ C := by
  rw [abs_mul, abs_of_pos (rr_pos s)]
  exact (mul_le_of_le_one_left (abs_nonneg _) (rr_le_one hs)).trans (mT_abs_le hC _ _ x)

lemma abs_G2_le {h : ℝ → ℝ} {C : ℝ} (hC : ∀ x, |h x| ≤ C) {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    |rr s ^ 2 * mT h (rr s) (sg s) x| ≤ C := by
  rw [abs_mul, abs_of_pos (pow_pos (rr_pos s) 2)]
  exact (mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (rr_pos s).le (rr_le_one hs))).trans (mT_abs_le hC _ _ x)

lemma abs_G3_le {h : ℝ → ℝ} {C : ℝ} (hC : ∀ x, |h x| ≤ C) {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    |rr s ^ 3 * mT h (rr s) (sg s) x| ≤ C := by
  rw [abs_mul, abs_of_pos (pow_pos (rr_pos s) 3)]
  exact (mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (rr_pos s).le (rr_le_one hs))).trans (mT_abs_le hC _ _ x)

section good
variable {ε : ℝ} {f f1 f2 f3 : ℝ → ℝ} (H : Good ε f f1 f2 f3)
include H

lemma Good.prof (s : ℝ) : Prof ε (G0 f s) (G1 f1 s) (G2 f2 s) (G3 f3 s) where
  hε := H.hε
  d0 x := hasDerivAt_mT H.d0 H.b0 H.b1 _ _ x
  d1 x := by
    have := (hasDerivAt_mT H.d1 H.b1 H.b2 (rr s) (sg s) x).const_mul (rr s)
    exact this.congr_deriv (by unfold G2; ring)
  d2 x := by
    have := (hasDerivAt_mT H.d2 H.b2 H.b3 (rr s) (sg s) x).const_mul (rr s ^ 2)
    exact this.congr_deriv (by unfold G3; ring)
  b0 := H.b0.mT _ _
  b1 := by
    obtain ⟨C, hC⟩ := (H.b1.mT (rr s) (sg s)).bdd
    refine ⟨(H.b1.mT (rr s) (sg s)).cont.const_mul _, ⟨|rr s| * C, fun x => ?_⟩⟩
    unfold G1; rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _)
  b2 := by
    obtain ⟨C, hC⟩ := (H.b2.mT (rr s) (sg s)).bdd
    refine ⟨(H.b2.mT (rr s) (sg s)).cont.const_mul _, ⟨|rr s ^ 2| * C, fun x => ?_⟩⟩
    unfold G2; rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _)
  b3 := by
    obtain ⟨C, hC⟩ := (H.b3.mT (rr s) (sg s)).bdd
    refine ⟨(H.b3.mT (rr s) (sg s)).cont.const_mul _, ⟨|rr s ^ 3| * C, fun x => ?_⟩⟩
    unfold G3; rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _)
  rng x := by
    obtain ⟨h1, h2⟩ : _ := (⟨fun y => (H.rng _).1, fun y => (H.rng _).2⟩ :
      (∀ y : ℝ, ε ≤ f (rr s * x + sg s * y)) ∧ ∀ y : ℝ, f (rr s * x + sg s * y) ≤ 1 - ε)
    constructor
    · have := integral_mono (μ := γ1) (integrable_const ε) (H.b0.integrable (rr s) (sg s) x) (fun y => h1 y)
      simpa [G0, mT] using this
    · have := integral_mono (μ := γ1) (H.b0.integrable (rr s) (sg s) x) (integrable_const (1 - ε)) (fun y => h2 y)
      simpa [G0, mT] using this


lemma Good.hasDerivAt_G0 (x : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun s => G0 f s x) (G2 f2 s x - x * G1 f1 s x) s :=
  hasDerivAt_mT_time H.d0 H.d1 H.b0 H.b1 H.b2 x hs

lemma Good.hasDerivAt_G1 (x : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun s => G1 f1 s x) (G3 f3 s x - x * G2 f2 s x - G1 f1 s x) s := by
  have := (hasDerivAt_rr s).mul (hasDerivAt_mT_time H.d1 H.d2 H.b1 H.b2 H.b3 x hs)
  refine this.congr_deriv ?_
  unfold G3 G2 G1; ring

lemma Good.hasDerivAt_pF (x : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun s => pF (G0 f s) (G1 f1 s) x)
      (pSF (G0 f s) (G1 f1 s) (G2 f2 s) (G3 f3 s) x) s := by
  have P := H.prof s
  have hA : HasDerivAt (fun s => gI (G0 f s x))
      (-gQ (G0 f s x) * (G2 f2 s x - x * G1 f1 s x)) s :=
    HasDerivAt.comp (h₂ := gI) s (hasDerivAt_gI (P.mem x)) (H.hasDerivAt_G0 x hs)
  have hB := H.hasDerivAt_G1 x hs
  have hsum : HasDerivAt (fun s => gI (G0 f s x) ^ 2 + G1 f1 s x ^ 2)
      (2 * gI (G0 f s x) * (-gQ (G0 f s x) * (G2 f2 s x - x * G1 f1 s x)) +
        2 * G1 f1 s x * (G3 f3 s x - x * G2 f2 s x - G1 f1 s x)) s := by
    have := (hA.pow 2).add (hB.pow 2)
    refine this.congr_deriv ?_
    simp
  have hne : gI (G0 f s x) ^ 2 + G1 f1 s x ^ 2 ≠ 0 := by
    have := gI_pos (P.mem x); positivity
  have := hsum.sqrt hne
  refine this.congr_deriv ?_
  have hp := (P.pF_pos x).ne'
  unfold pSF
  have e : Real.sqrt (gI (G0 f s x) ^ 2 + G1 f1 s x ^ 2) = pF (G0 f s) (G1 f1 s) x := rfl
  rw [e]
  field_simp

/-- Uniform linear-growth bound for `∂ₛF`. -/
lemma Good.exists_bound_SF : ∃ D, ∀ s : ℝ, 0 ≤ s → ∀ x : ℝ,
    |pSF (G0 f s) (G1 f1 s) (G2 f2 s) (G3 f3 s) x| ≤ D * (1 + |x|) := by
  obtain ⟨K, hK⟩ := exists_gQ_bound H.hε
  obtain ⟨C1, hC1⟩ := H.b1.bdd
  obtain ⟨C2, hC2⟩ := H.b2.bdd
  obtain ⟨C3, hC3⟩ := H.b3.bdd
  refine ⟨K * (C1 + C2) + C3 + C2 + C1, fun s hs x => ?_⟩
  have P := H.prof s
  exact abs_SF_le (gI (G0 f s x)) (gQ (G0 f s x)) (G1 f1 s x) (G2 f2 s x) (G3 f3 s x) x
    (pF (G0 f s) (G1 f1 s) x) K C1 C2 C3 (P.pF_sq x) (P.pF_pos x)
    (hK _ ⟨(P.rng x).1, (P.rng x).2⟩) (abs_G1_le hC1 hs x) (abs_G2_le hC2 hs x) (abs_G3_le hC3 hs x)

end good
end CutoffRigidity.GaussIso
