module

public import CutoffRigidity.Extra.GaussIso2

/-! # Pointwise calculus for `F = √(I(g)² + g'²)` (stage 3a of the Bobkov inequality)

For a "profile" `g0` (with derivatives `g1,g2,g3`, values in `[ε,1-ε]`), compute `F'` and `F''` explicitly and
the algebraic identity `∂ₛF = F'' - x F' - (I g'' - I' g'^2)²/F³` (with `∂ₛ g = g'' - x g'`). -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology

set_option linter.unusedSectionVars false

namespace CutoffRigidity.GaussIso

/-- Bounded functions. -/
def Bd (φ : ℝ → ℝ) : Prop := ∃ C, ∀ x, |φ x| ≤ C

lemma Bd.const (c : ℝ) : Bd (fun _ => c) := ⟨|c|, fun _ => le_rfl⟩
lemma Bd.add {a b : ℝ → ℝ} (ha : Bd a) (hb : Bd b) : Bd (fun x => a x + b x) := by
  obtain ⟨C, hC⟩ := ha; obtain ⟨D, hD⟩ := hb
  exact ⟨C + D, fun x => (abs_add_le _ _).trans (add_le_add (hC x) (hD x))⟩
lemma Bd.neg {a : ℝ → ℝ} (ha : Bd a) : Bd (fun x => -a x) := by
  obtain ⟨C, hC⟩ := ha; exact ⟨C, fun x => by simpa using hC x⟩
lemma Bd.sub {a b : ℝ → ℝ} (ha : Bd a) (hb : Bd b) : Bd (fun x => a x - b x) := by
  simpa [sub_eq_add_neg] using ha.add hb.neg
lemma Bd.mul {a b : ℝ → ℝ} (ha : Bd a) (hb : Bd b) : Bd (fun x => a x * b x) := by
  obtain ⟨C, hC⟩ := ha; obtain ⟨D, hD⟩ := hb
  refine ⟨C * D, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hC x) (hD x) (abs_nonneg _) ((abs_nonneg _).trans (hC x))
lemma Bd.pow {a : ℝ → ℝ} (ha : Bd a) (n : ℕ) : Bd (fun x => a x ^ n) := by
  induction n with
  | zero => simpa using Bd.const 1
  | succ n ih => simpa [pow_succ] using ih.mul ha
lemma Bd.inv_of_lower {a : ℝ → ℝ} {m : ℝ} (hm : 0 < m) (h : ∀ x, m ≤ a x) : Bd (fun x => (a x)⁻¹) := by
  refine ⟨m⁻¹, fun x => ?_⟩
  have : 0 < a x := hm.trans_le (h x)
  rw [abs_of_pos (inv_pos.2 this)]
  exact inv_anti₀ hm (h x)
lemma BC.bd {h : ℝ → ℝ} (hh : BC h) : Bd h := hh.bdd

lemma exists_gI_lower {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 - ε) : ∃ m, 0 < m ∧ ∀ u ∈ Icc ε (1 - ε), m ≤ gI u := by
  have hc : ContinuousOn gI (Icc ε (1 - ε)) := continuousOn_gI.mono (fun u hu => ⟨hε.le.trans hu.1, hu.2.trans (by linarith)⟩)
  obtain ⟨u0, hu0, hmin⟩ := (isCompact_Icc).exists_isMinOn ⟨ε, le_rfl, hε'⟩ hc
  exact ⟨gI u0, gI_pos ⟨by linarith [hu0.1], by linarith [hu0.2]⟩, fun u hu => hmin hu⟩

lemma exists_gQ_bound {ε : ℝ} (hε : 0 < ε) : ∃ K, ∀ u ∈ Icc ε (1 - ε), |gQ u| ≤ K := by
  refine ⟨|gQ ε| + |gQ (1 - ε)|, fun u hu => ?_⟩
  have h0 : ε ∈ Ioo (0:ℝ) 1 := ⟨hε, by linarith [hu.1, hu.2]⟩
  have h1 : (1 - ε) ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hu.1, hu.2], by linarith⟩
  have hu' : u ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have a1 : gQ ε ≤ gQ u := by
    rcases hu.1.eq_or_lt with h | h
    · rw [h]
    · exact (strictMonoOn_gQ h0 hu' h).le
  have a2 : gQ u ≤ gQ (1 - ε) := by
    rcases hu.2.eq_or_lt with h | h
    · rw [h]
    · exact (strictMonoOn_gQ hu' h1 h).le
  rw [abs_le]
  constructor <;> nlinarith [neg_abs_le (gQ ε), le_abs_self (gQ (1 - ε)), abs_nonneg (gQ ε), abs_nonneg (gQ (1 - ε))]

lemma core_alg (A g1 g2 g3 q x Fv : ℝ) (hA : 0 < A) (hFp : 0 < Fv) (hF : Fv ^ 2 = A ^ 2 + g1 ^ 2) :
    (A * (-q * (g2 - x * g1)) + g1 * (g3 - x * g2 - g1)) / Fv =
      ((((-q * g1) ^ 2 + A * (-g1 ^ 2 / A - q * g2) + g2 ^ 2 + g1 * g3) * Fv
          - (A * (-q * g1) + g1 * g2) * ((A * (-q * g1) + g1 * g2) / Fv)) / Fv ^ 2)
      - x * ((A * (-q * g1) + g1 * g2) / Fv)
      - ((-q * g1) * g1 - A * g2) ^ 2 / Fv ^ 3 := by
  have hA' := hA.ne'
  have hF' := hFp.ne'
  field_simp
  linear_combination (-(q ^ 2 * g1 ^ 2 + g2 ^ 2)) * hF


/-- Profile data at a fixed time. -/
structure Prof (ε : ℝ) (g0 g1 g2 g3 : ℝ → ℝ) : Prop where
  hε : 0 < ε
  d0 : ∀ x, HasDerivAt g0 (g1 x) x
  d1 : ∀ x, HasDerivAt g1 (g2 x) x
  d2 : ∀ x, HasDerivAt g2 (g3 x) x
  b0 : BC g0
  b1 : BC g1
  b2 : BC g2
  b3 : BC g3
  rng : ∀ x, ε ≤ g0 x ∧ g0 x ≤ 1 - ε

section prof
variable {ε : ℝ} {g0 g1 g2 g3 : ℝ → ℝ} (P : Prof ε g0 g1 g2 g3)
include P

lemma Prof.mem (x : ℝ) : g0 x ∈ Ioo (0:ℝ) 1 :=
  ⟨P.hε.trans_le (P.rng x).1, by linarith [(P.rng x).2, P.hε]⟩

lemma Prof.hasDerivAt_A (x : ℝ) :
    HasDerivAt (fun x => gI (g0 x)) (-gQ (g0 x) * g1 x) x := by
  have := (hasDerivAt_gI (P.mem x)).comp x (P.d0 x)
  exact this

lemma Prof.hasDerivAt_Q (x : ℝ) :
    HasDerivAt (fun x => gQ (g0 x)) ((gI (g0 x))⁻¹ * g1 x) x := by
  have := (hasDerivAt_gQ (P.mem x)).comp x (P.d0 x)
  rw [← gI_of_mem (P.mem x)] at this
  exact this

lemma Prof.hasDerivAt_A' (x : ℝ) :
    HasDerivAt (fun x => -gQ (g0 x) * g1 x) (-(g1 x) ^ 2 / gI (g0 x) - gQ (g0 x) * g2 x) x := by
  have := ((P.hasDerivAt_Q x).neg).mul (P.d1 x)
  refine this.congr_deriv ?_
  have := (gI_pos (P.mem x)).ne'
  simp only [Pi.neg_apply]
  field_simp
  ring

lemma Prof.continuous_A : Continuous (fun x => gI (g0 x)) :=
  continuous_iff_continuousAt.2 fun x => (P.hasDerivAt_A x).continuousAt

lemma Prof.continuous_Q : Continuous (fun x => gQ (g0 x)) :=
  continuous_iff_continuousAt.2 fun x => (P.hasDerivAt_Q x).continuousAt

/-- `F = √(I(g)² + g'²)`. -/
noncomputable def pF (g0 g1 : ℝ → ℝ) (x : ℝ) : ℝ := Real.sqrt (gI (g0 x) ^ 2 + g1 x ^ 2)
/-- `N = I I' + g' g''` (so `F' = N/F`). -/
noncomputable def pN (g0 g1 g2 : ℝ → ℝ) (x : ℝ) : ℝ :=
  gI (g0 x) * (-gQ (g0 x) * g1 x) + g1 x * g2 x
/-- `N'`. -/
noncomputable def pN' (g0 g1 g2 g3 : ℝ → ℝ) (x : ℝ) : ℝ :=
  (-gQ (g0 x) * g1 x) ^ 2 + gI (g0 x) * (-(g1 x) ^ 2 / gI (g0 x) - gQ (g0 x) * g2 x) + g2 x ^ 2 + g1 x * g3 x
/-- `F'`. -/
noncomputable def pFx (g0 g1 g2 : ℝ → ℝ) (x : ℝ) : ℝ := pN g0 g1 g2 x / pF g0 g1 x
/-- `F''`. -/
noncomputable def pFxx (g0 g1 g2 g3 : ℝ → ℝ) (x : ℝ) : ℝ :=
  (pN' g0 g1 g2 g3 x * pF g0 g1 x - pN g0 g1 g2 x * pFx g0 g1 g2 x) / pF g0 g1 x ^ 2

lemma Prof.pF_ge (x : ℝ) : gI (g0 x) ≤ pF g0 g1 x := by
  unfold pF
  calc gI (g0 x) = Real.sqrt (gI (g0 x) ^ 2) := (Real.sqrt_sq (gI_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (g1 x)])

lemma Prof.pF_pos (x : ℝ) : 0 < pF g0 g1 x := (gI_pos (P.mem x)).trans_le (P.pF_ge x)

lemma Prof.pF_sq (x : ℝ) : pF g0 g1 x ^ 2 = gI (g0 x) ^ 2 + g1 x ^ 2 := by
  unfold pF; rw [Real.sq_sqrt]; positivity

lemma Prof.hasDerivAt_F (x : ℝ) : HasDerivAt (pF g0 g1) (pFx g0 g1 g2 x) x := by
  have hsum : HasDerivAt (fun x => gI (g0 x) ^ 2 + g1 x ^ 2)
      (2 * gI (g0 x) * (-gQ (g0 x) * g1 x) + 2 * g1 x * g2 x) x := by
    have := ((P.hasDerivAt_A x).pow 2).add ((P.d1 x).pow 2)
    refine this.congr_deriv ?_
    simp
  have hne : gI (g0 x) ^ 2 + g1 x ^ 2 ≠ 0 := by
    have := gI_pos (P.mem x); positivity
  have := hsum.sqrt hne
  refine this.congr_deriv ?_
  have hp := (P.pF_pos x).ne'
  unfold pFx pN
  have e : Real.sqrt (gI (g0 x) ^ 2 + g1 x ^ 2) = pF g0 g1 x := rfl
  rw [e]
  field_simp

lemma Prof.hasDerivAt_N (x : ℝ) : HasDerivAt (pN g0 g1 g2) (pN' g0 g1 g2 g3 x) x := by
  have := ((P.hasDerivAt_A x).mul (P.hasDerivAt_A' x)).add ((P.d1 x).mul (P.d2 x))
  refine this.congr_deriv ?_
  unfold pN'; ring

lemma Prof.hasDerivAt_Fx (x : ℝ) : HasDerivAt (pFx g0 g1 g2) (pFxx g0 g1 g2 g3 x) x := by
  have := (P.hasDerivAt_N x).div (P.hasDerivAt_F x) (P.pF_pos x).ne'
  exact this

/-- Lower bound `F ≥ m > 0`. -/
lemma Prof.exists_m : ∃ m, 0 < m ∧ ∀ x, m ≤ pF g0 g1 x := by
  obtain ⟨m, hm, h⟩ := exists_gI_lower P.hε (by
    have := (P.rng 0); linarith [this.1, this.2])
  exact ⟨m, hm, fun x => (h _ ⟨(P.rng x).1, (P.rng x).2⟩).trans (P.pF_ge x)⟩

lemma Prof.bd_A : Bd (fun x => gI (g0 x)) := ⟨gφ 0, fun x => by
  rw [abs_of_nonneg (gI_nonneg _)]; exact gI_le _⟩

lemma Prof.bd_Q : Bd (fun x => gQ (g0 x)) := by
  obtain ⟨K, hK⟩ := exists_gQ_bound P.hε
  exact ⟨K, fun x => hK _ ⟨(P.rng x).1, (P.rng x).2⟩⟩

lemma Prof.bd_F : Bd (pF g0 g1) := by
  obtain ⟨C, hC⟩ := P.b1.bdd
  refine ⟨gφ 0 + C, fun x => ?_⟩
  rw [abs_of_pos (P.pF_pos x)]
  unfold pF
  calc Real.sqrt (gI (g0 x) ^ 2 + g1 x ^ 2) ≤ Real.sqrt ((gφ 0 + C) ^ 2) := by
        apply Real.sqrt_le_sqrt
        have h1 : gI (g0 x) ≤ gφ 0 := gI_le _
        have h2 : g1 x ^ 2 ≤ C ^ 2 := by
          have := hC x; nlinarith [abs_nonneg (g1 x), sq_abs (g1 x)]
        have h3 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
        nlinarith [gI_nonneg (g0 x), gφ_pos 0]
    _ = gφ 0 + C := Real.sqrt_sq (by have := gφ_pos 0; have : 0 ≤ C := (abs_nonneg _).trans (hC 0); linarith)

lemma Prof.bd_N : Bd (pN g0 g1 g2) := by
  have := (P.bd_A.mul ((P.bd_Q.neg.mul P.b1.bd))).add (P.b1.bd.mul P.b2.bd)
  exact this

lemma Prof.bd_Finv : Bd (fun x => (pF g0 g1 x)⁻¹) := by
  obtain ⟨m, hm, h⟩ := P.exists_m
  exact Bd.inv_of_lower hm h

lemma Prof.bd_Fx : Bd (pFx g0 g1 g2) := by
  have := P.bd_N.mul P.bd_Finv
  have e : pFx g0 g1 g2 = fun x => pN g0 g1 g2 x * (pF g0 g1 x)⁻¹ := by
    funext x; simp [pFx, div_eq_mul_inv]
  rw [e]; exact this

lemma Prof.bd_N' : Bd (pN' g0 g1 g2 g3) := by
  have hA := P.bd_A
  have hQ := P.bd_Q
  have h1 := P.b1.bd
  have h2 := P.b2.bd
  have h3 := P.b3.bd
  have hAinv : Bd (fun x => (gI (g0 x))⁻¹) := by
    obtain ⟨m, hm, h⟩ := exists_gI_lower P.hε (by have := (P.rng 0); linarith [this.1, this.2])
    exact Bd.inv_of_lower hm (fun x => h _ ⟨(P.rng x).1, (P.rng x).2⟩)
  have e1 : Bd (fun x => (-gQ (g0 x) * g1 x) ^ 2) := ((hQ.neg).mul h1).pow 2
  have e2 : Bd (fun x => gI (g0 x) * (-(g1 x) ^ 2 / gI (g0 x) - gQ (g0 x) * g2 x)) := by
    refine hA.mul (Bd.sub ?_ (hQ.mul h2))
    have := ((h1.pow 2).neg).mul hAinv
    simpa [div_eq_mul_inv] using this
  have := ((e1.add e2).add (h2.pow 2)).add (h1.mul h3)
  exact this

lemma Prof.bd_Fxx : Bd (pFxx g0 g1 g2 g3) := by
  have := ((P.bd_N'.mul P.bd_F).sub (P.bd_N.mul P.bd_Fx)).mul (P.bd_Finv.pow 2)
  have e : pFxx g0 g1 g2 g3 = fun x => (pN' g0 g1 g2 g3 x * pF g0 g1 x - pN g0 g1 g2 x * pFx g0 g1 g2 x) * ((pF g0 g1 x)⁻¹) ^ 2 := by
    funext x; simp [pFxx, div_eq_mul_inv, inv_pow]
  rw [e]; exact this

lemma Prof.continuous_F : Continuous (pF g0 g1) := by
  unfold pF
  have := P.continuous_A
  have := P.b1.cont
  fun_prop

lemma Prof.continuous_Fx : Continuous (pFx g0 g1 g2) := by
  have hF := P.continuous_F
  have hFne : ∀ x, pF g0 g1 x ≠ 0 := fun x => (P.pF_pos x).ne'
  unfold pFx pN
  have := P.continuous_A; have := P.continuous_Q; have := P.b1.cont; have := P.b2.cont
  exact Continuous.div (by fun_prop) hF hFne

lemma Prof.continuous_Fxx : Continuous (pFxx g0 g1 g2 g3) := by
  have hF := P.continuous_F
  have hFne : ∀ x, pF g0 g1 x ≠ 0 := fun x => (P.pF_pos x).ne'
  have hFx := P.continuous_Fx
  have hAne : ∀ x, gI (g0 x) ≠ 0 := fun x => (gI_pos (P.mem x)).ne'
  have hA := P.continuous_A; have hQ := P.continuous_Q
  have h1 := P.b1.cont; have h2 := P.b2.cont; have h3 := P.b3.cont
  have hN' : Continuous (pN' g0 g1 g2 g3) := by
    unfold pN'
    have : Continuous (fun x => -(g1 x) ^ 2 / gI (g0 x)) := Continuous.div (by fun_prop) hA hAne
    have : Continuous (fun x => gI (g0 x) * (-(g1 x) ^ 2 / gI (g0 x) - gQ (g0 x) * g2 x)) := by fun_prop
    fun_prop
  have hN : Continuous (pN g0 g1 g2) := by unfold pN; fun_prop
  unfold pFxx
  exact Continuous.div (by fun_prop) (by fun_prop) (fun x => pow_ne_zero 2 (hFne x))

/-- Stein for `F`: `∫ x F' = ∫ F''` (so `∫ (F'' - x F') dγ = 0`). -/
lemma Prof.integral_L : ∫ x, (pFxx g0 g1 g2 g3 x - x * pFx g0 g1 g2 x) ∂γ1 = 0 := by
  have hs := stein (k := pFx g0 g1 g2) (k' := pFxx g0 g1 g2 g3) P.hasDerivAt_Fx P.bd_Fx P.bd_Fxx
    P.continuous_Fxx
  have i1 : Integrable (fun x => x * pFx g0 g1 g2 x) γ1 := by
    obtain ⟨C, hC⟩ := P.bd_Fx
    have := ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl).bdd_mul (c := C)
      P.continuous_Fx.aestronglyMeasurable (Eventually.of_forall fun x => by simpa using hC x)
    exact this.congr (Eventually.of_forall fun x => by simp [mul_comm])
  have i2 : Integrable (pFxx g0 g1 g2 g3) γ1 := by
    obtain ⟨C, hC⟩ := P.bd_Fxx
    exact Integrable.mono' (integrable_const C) P.continuous_Fxx.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa using hC x)
  rw [integral_sub i2 i1, hs]; ring

/-- `∂ₛF`, with `∂ₛ g = g'' - x g'` and `∂ₛ g' = g''' - x g'' - g'`. -/
noncomputable def pSF (g0 g1 g2 g3 : ℝ → ℝ) (x : ℝ) : ℝ :=
  (gI (g0 x) * (-gQ (g0 x) * (g2 x - x * g1 x)) + g1 x * (g3 x - x * g2 x - g1 x)) / pF g0 g1 x

/-- The nonnegative defect `(I g'' - I' g'^2)²/F³`. -/
noncomputable def pM (g0 g1 g2 : ℝ → ℝ) (x : ℝ) : ℝ :=
  ((-gQ (g0 x) * g1 x) * g1 x - gI (g0 x) * g2 x) ^ 2 / pF g0 g1 x ^ 3

end prof

section prof2
variable {ε : ℝ} {g0 g1 g2 g3 : ℝ → ℝ} (P : Prof ε g0 g1 g2 g3)
include P

lemma Prof.SF_eq (x : ℝ) :
    pSF g0 g1 g2 g3 x = pFxx g0 g1 g2 g3 x - x * pFx g0 g1 g2 x - pM g0 g1 g2 x := by
  have := core_alg (gI (g0 x)) (g1 x) (g2 x) (g3 x) (gQ (g0 x)) x (pF g0 g1 x)
    (gI_pos (P.mem x)) (P.pF_pos x) (P.pF_sq x)
  unfold pSF pFxx pFx pN pN' pM
  exact this

lemma Prof.pM_nonneg (x : ℝ) : 0 ≤ pM g0 g1 g2 x := by
  unfold pM
  have := P.pF_pos x
  positivity

lemma Prof.bd_M : Bd (pM g0 g1 g2) := by
  have hQ := P.bd_Q; have h1 := P.b1.bd; have h2 := P.b2.bd
  have := ((((hQ.neg).mul h1).mul h1).sub (P.bd_A.mul h2)).pow 2
  have := this.mul (P.bd_Finv.pow 3)
  have e : pM g0 g1 g2 = fun x => ((-gQ (g0 x) * g1 x * g1 x - gI (g0 x) * g2 x) ^ 2) * ((pF g0 g1 x)⁻¹) ^ 3 := by
    funext x; simp [pM, div_eq_mul_inv, inv_pow]
  rw [e]; exact this

lemma Prof.continuous_M : Continuous (pM g0 g1 g2) := by
  have hF := P.continuous_F
  have hFne : ∀ x, pF g0 g1 x ≠ 0 := fun x => (P.pF_pos x).ne'
  have hA := P.continuous_A; have hQ := P.continuous_Q
  have h1 := P.b1.cont; have h2 := P.b2.cont
  unfold pM
  exact Continuous.div (by fun_prop) (by fun_prop) (fun x => pow_ne_zero 3 (hFne x))

/-- `∫ ∂ₛF dγ = -∫ M dγ`. -/
lemma Prof.integral_SF : ∫ x, pSF g0 g1 g2 g3 x ∂γ1 = -∫ x, pM g0 g1 g2 x ∂γ1 := by
  have i2 : Integrable (pFxx g0 g1 g2 g3) γ1 := by
    obtain ⟨C, hC⟩ := P.bd_Fxx
    exact Integrable.mono' (integrable_const C) P.continuous_Fxx.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa using hC x)
  have i1 : Integrable (fun x => x * pFx g0 g1 g2 x) γ1 := by
    obtain ⟨C, hC⟩ := P.bd_Fx
    have := ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl).bdd_mul (c := C)
      P.continuous_Fx.aestronglyMeasurable (Eventually.of_forall fun x => by simpa using hC x)
    exact this.congr (Eventually.of_forall fun x => by simp [mul_comm])
  have iM : Integrable (pM g0 g1 g2) γ1 := by
    obtain ⟨C, hC⟩ := P.bd_M
    exact Integrable.mono' (integrable_const C) P.continuous_M.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa using hC x)
  have hL := P.integral_L
  have e : ∀ x, pSF g0 g1 g2 g3 x = (pFxx g0 g1 g2 g3 x - x * pFx g0 g1 g2 x) - pM g0 g1 g2 x :=
    fun x => P.SF_eq x
  simp_rw [e]
  have i3 : Integrable (fun x => pFxx g0 g1 g2 g3 x - x * pFx g0 g1 g2 x) γ1 := i2.sub i1
  rw [integral_sub i3 iM, hL]; ring

end prof2
end CutoffRigidity.GaussIso
