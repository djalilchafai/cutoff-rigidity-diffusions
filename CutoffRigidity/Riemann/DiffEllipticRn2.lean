module

public import CutoffRigidity.Riemann.DiffEllipticRn1

/-! # Difference quotient estimates for divergence form equations
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff

set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Diff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)

theorem AESupp.dq {f : E → ℝ} (hf : AESupp f) (e : E) (h : ℝ) : AESupp (dq e h f) := by
  obtain ⟨R, hR⟩ := hf
  refine ⟨R + |h| * ‖e‖, ?_⟩
  have h2 : ∀ᵐ x ∂(volume : Measure E), R < ‖x + h • e‖ → f (x + h • e) = 0 :=
    (measurePreserving_add_right volume (h • e)).quasiMeasurePreserving.ae hR
  filter_upwards [hR, h2] with x h1 h3 hx
  have hn : ‖x‖ - |h| * ‖e‖ ≤ ‖x + h • e‖ := by
    have := norm_sub_norm_le x (-(h • e))
    rw [sub_neg_eq_add, norm_neg, norm_smul, Real.norm_eq_abs] at this
    exact this
  have hx1 : R < ‖x‖ := by linarith [abs_nonneg h, norm_nonneg e, mul_nonneg (abs_nonneg h) (norm_nonneg e)]
  have hx2 : R < ‖x + h • e‖ := by linarith
  show (f (x + h • e) - f x) / h = 0
  rw [h3 hx2, h1 hx1]; simp

theorem abs_dq_le_of_fderiv_bound {a : E → ℝ} (ha : ContDiff ℝ ∞ a) {K : ℝ}
    (hK : ∀ x, ‖fderiv ℝ a x‖ ≤ K) (e : E) {h : ℝ} (hh : h ≠ 0) (x : E) :
    |dq e h a x| ≤ K * ‖e‖ := by
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := a) (s := Set.univ)
    (fun y _ => (ha.differentiable (by simp)) y) (fun y _ => hK y) convex_univ
    (Set.mem_univ x) (Set.mem_univ (x + h • e))
  rw [Real.norm_eq_abs] at this
  simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at this
  unfold dq
  rw [abs_div, div_le_iff₀ (abs_pos.2 hh)]
  linarith

theorem l2_le_of_abs_le {f g : E → ℝ} (hg : MemLp g 2 volume) (hf : MemLp f 2 volume) {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ x, |f x| ≤ c * |g x|) : l2 f ≤ c * l2 g := by
  have h1 : ∫ x, f x ^ 2 ≤ ∫ x, (c * g x) ^ 2 := by
    refine integral_mono hf.integrable_sq (hg.integrable_sq.const_mul (c ^ 2) |>.congr
      (Filter.Eventually.of_forall fun x => by simp only [mul_pow])) (fun x => ?_)
    have := h x
    have h2 : |f x| ^ 2 ≤ (c * |g x|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
    simpa [sq_abs, mul_pow] using h2
  have h3 : ∫ x, (c * g x) ^ 2 = c ^ 2 * ∫ x, g x ^ 2 := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  unfold l2
  calc Real.sqrt (∫ x, f x ^ 2) ≤ Real.sqrt (c ^ 2 * ∫ x, g x ^ 2) :=
        Real.sqrt_le_sqrt (h1.trans h3.le)
    _ = c * Real.sqrt (∫ x, g x ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc]

theorem abs_integral_mul_neg_dq_le {f f' g : E → ℝ} {e : E} {h : ℝ} (hh : h ≠ 0)
    (hf : MemLp f 2 volume) (hf' : MemLp f' 2 volume) (hH : HasWDeriv Set.univ e f f')
    (hg : MemLp g 2 volume) :
    |∫ x, f x * (-(dq e (-h) g x))| ≤ l2 f' * l2 g := by
  have e1 : ∫ x, f x * (-(dq e (-h) g x)) = ∫ x, dq e h f x * g x := by
    have := integral_mul_dq_neg (v := e) hh hf hg
    have e2 : ∫ x, f x * (-(dq e (-h) g x)) = -∫ x, f x * dq e (-h) g x := by
      rw [← integral_neg]; congr 1; funext x; ring
    rw [e2, this]; ring
  rw [e1]
  exact (abs_integral_mul_le_l2 (memLp_dq hf) hg).trans
    (mul_le_mul_of_nonneg_right (l2_dq_le_l2_deriv hh hf hf' hH) (l2_nonneg _))

theorem abs_integral_mul_neg_dq_le' {F g g' : E → ℝ} {e : E} {h : ℝ} (hh : h ≠ 0)
    (hF : MemLp F 2 volume) (hg : MemLp g 2 volume) (hg' : MemLp g' 2 volume)
    (hH : HasWDeriv Set.univ e g g') :
    |∫ x, F x * (-(dq e (-h) g x))| ≤ l2 F * l2 g' := by
  have hneg : MemLp (fun x => -(dq e (-h) g x)) 2 volume := (memLp_dq hg).neg
  refine (abs_integral_mul_le_l2 hF hneg).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (l2_nonneg _)
  rw [l2_neg]
  exact l2_dq_le_l2_deriv (neg_ne_zero.2 hh) hg hg' hH

theorem memLp_mul_of_bound {a f : E → ℝ} (ha : Continuous a) {K : ℝ} (hK : ∀ x, ‖a x‖ ≤ K)
    (hf : MemLp f 2 volume) : MemLp (fun x => a x * f x) 2 volume :=
  (integral_sq_mul_le ha hK hf).1

theorem continuous_dq {a : E → ℝ} (ha : Continuous a) (e : E) (h : ℝ) : Continuous (dq e h a) := by
  unfold dq
  exact ((ha.comp (continuous_id.add continuous_const)).sub ha).div_const h

theorem lhs_decomp {a u g : E → ℝ} {e : E} {h : ℝ} (hh : h ≠ 0) (ha : ContDiff ℝ ∞ a) {K : ℝ}
    (hbd : ∀ x, ‖a x‖ ≤ K) (hlip : ∀ x, ‖fderiv ℝ a x‖ ≤ K)
    (hu : MemLp u 2 volume) (hg : MemLp g 2 volume) :
    ∫ x, a x * u x * (-(dq e (-h) g x)) =
      (∫ x, a (x + h • e) * dq e h u x * g x) + ∫ x, dq e h a x * u x * g x := by
  have hau : MemLp (fun x => a x * u x) 2 volume := memLp_mul_of_bound ha.continuous hbd hu
  have e1 : ∫ x, a x * u x * (-(dq e (-h) g x)) = ∫ x, dq e h (fun x => a x * u x) x * g x := by
    have := integral_mul_dq_neg (v := e) hh hau hg
    have e2 : ∫ x, a x * u x * (-(dq e (-h) g x)) = -∫ x, a x * u x * dq e (-h) g x := by
      rw [← integral_neg]; congr 1; funext x; ring
    rw [e2, this]; ring
  have hshift : Continuous (fun x => a (x + h • e)) :=
    ha.continuous.comp (continuous_id.add continuous_const)
  have i1 : Integrable (fun x => a (x + h • e) * dq e h u x * g x) volume :=
    (memLp_mul_of_bound hshift (fun x => hbd _) (memLp_dq hu)).integrable_mul hg
  have hdqa : ∀ x, |dq e h a x| ≤ K * ‖e‖ := abs_dq_le_of_fderiv_bound ha hlip e hh
  have i2 : Integrable (fun x => dq e h a x * u x * g x) volume := by
    have := memLp_mul_of_bound (continuous_dq ha.continuous e h) (K := K * ‖e‖)
      (fun x => by simpa using hdqa x) hu
    exact this.integrable_mul hg
  rw [e1, ← integral_add i1 i2]
  congr 1; funext x
  rw [dq_mul hh a u x]
  ring

theorem AESupp.neg {f : E → ℝ} (hf : AESupp f) : AESupp (fun x => -f x) := by
  obtain ⟨R, hR⟩ := hf
  exact ⟨R, by filter_upwards [hR] with x hx h; simp [hx h]⟩

theorem Ell.fderiv_bound {A : ι → ι → E → ℝ} {θ K : ℝ} {N : ℕ} (hA : Ell A θ K (N + 1)) (i j : ι)
    (x : E) : ‖fderiv ℝ (A i j) x‖ ≤ K := by
  have := hA.bound i j 1 (by omega) x
  simpa using this

theorem Ell.sup_bound {A : ι → ι → E → ℝ} {θ K : ℝ} {N : ℕ} (hA : Ell A θ K N) (i j : ι)
    (x : E) : ‖A i j x‖ ≤ K := by
  have := hA.bound i j 0 (Nat.zero_le _) x
  simpa using this

/-- Energy estimate for the difference quotients of the gradient. -/
theorem dq_energy {A : ι → ι → E → ℝ} {θ K : ℝ} (hA : Ell A θ K 1) (hθ : 0 < θ)
    {w F : E → ℝ} {G : ι → E → ℝ} (hw : Sob b 1 w) (hs : AESupp w) (hF : MemLp F 2 volume)
    (hG : ∀ i, Sob b 1 (G i)) (heq : WeakEq b A w F G) (k : ι) {h : ℝ} (hh : h ≠ 0) :
    ∑ j, ∫ x, dq (b k) h (wd (b j) w) x ^ 2 ≤
      ((l2 F + ∑ i, l2 (wd (b k) (G i)) + K * ∑ _i : ι, ∑ j, l2 (wd (b j) w)) / θ) ^ 2 := by
  haveI : Nonempty ι := ⟨k⟩
  obtain ⟨hwm, hwd⟩ := Sob.one_wd b hw
  have hK0 : 0 ≤ K := by
    exact le_trans (norm_nonneg _) (hA.sup_bound k k 0)
  set e := b k with he
  have hGm : ∀ i, MemLp (G i) 2 volume := fun i => (Sob.one_wd b (hG i)).1
  have hW : ∀ j, MemLp (dq e h (wd (b j) w)) 2 volume := fun j => memLp_dq (hwd j).2
  set X := ∑ j, ∫ x, dq e h (wd (b j) w) x ^ 2 with hX
  have hX0 : 0 ≤ X := Finset.sum_nonneg (fun j _ => integral_nonneg (fun x => sq_nonneg _))
  set s := Real.sqrt X with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = X := Real.sq_sqrt hX0
  have hWs : ∀ i, l2 (dq e h (wd (b i) w)) ≤ s := fun i => by
    apply Real.sqrt_le_sqrt
    exact Finset.single_le_sum (f := fun j => ∫ x, dq e h (wd (b j) w) x ^ 2)
      (fun j _ => integral_nonneg (fun x => sq_nonneg _)) (Finset.mem_univ i)
  -- test function
  set φ : E → ℝ := fun x => -(dq e (-h) (dq e h w) x) with hφdef
  set φ' : ι → E → ℝ := fun i x => -(dq e (-h) (dq e h (wd (b i) w)) x) with hφ'def
  have hφm : MemLp φ 2 volume := (memLp_dq (memLp_dq hwm)).neg
  have hφs : AESupp φ := ((hs.dq e h).dq e (-h)).neg
  have hφ' : ∀ i, HasWDeriv Set.univ (b i) φ (φ' i) := by
    intro i
    have h1 := hasWDeriv_dq (e := e) (h := h) hh hwm (hwd i).2 (hwd i).1
    have h2 := hasWDeriv_dq (e := e) (h := -h) (neg_ne_zero.2 hh) (memLp_dq hwm)
      (memLp_dq (hwd i).2) h1
    exact h2.neg
  have hφ'm : ∀ i, MemLp (φ' i) 2 volume := fun i => (memLp_dq (memLp_dq (hwd i).2)).neg
  have E1 := WeakEq.extend b hA hw hF hGm heq hφm hφs hφ' hφ'm
  -- decomposition of the left side
  have hdec : ∀ i j, ∫ x, A i j x * wd (b j) w x * φ' i x =
      (∫ x, A i j (x + h • e) * dq e h (wd (b j) w) x * dq e h (wd (b i) w) x) +
        ∫ x, dq e h (A i j) x * wd (b j) w x * dq e h (wd (b i) w) x := fun i j =>
    lhs_decomp hh (hA.smooth i j) (hA.sup_bound i j) (hA.fderiv_bound i j) (hwd j).2 (hW i)
  have hshift : ∀ i j, Continuous (fun x => A i j (x + h • e)) := fun i j =>
    (hA.smooth i j).continuous.comp (continuous_id.add continuous_const)
  have hint : ∀ i j, Integrable
      (fun x => A i j (x + h • e) * dq e h (wd (b j) w) x * dq e h (wd (b i) w) x) volume :=
    fun i j => (memLp_mul_of_bound (hshift i j) (fun x => hA.sup_bound i j _) (hW j)).integrable_mul
      (hW i)
  have hint2 : ∀ i j, Integrable
      (fun x => dq e h (A i j) x * wd (b j) w x * dq e h (wd (b i) w) x) volume := by
    intro i j
    have hdqa : ∀ x, ‖dq e h (A i j) x‖ ≤ K := fun x => by
      have := abs_dq_le_of_fderiv_bound (hA.smooth i j) (hA.fderiv_bound i j) e hh x
      rw [he, b.norm_eq_one, mul_one] at this
      simpa using this
    exact (memLp_mul_of_bound (continuous_dq (hA.smooth i j).continuous e h) hdqa
      (hwd j).2).integrable_mul (hW i)
  -- ellipticity
  have hell : θ * X ≤ ∑ i, ∑ j, ∫ x, A i j (x + h • e) * dq e h (wd (b j) w) x *
      dq e h (wd (b i) w) x := by
    have e1 : ∫ x, ∑ i, ∑ j, A i j (x + h • e) * dq e h (wd (b j) w) x *
        dq e h (wd (b i) w) x = ∑ i, ∑ j, ∫ x, A i j (x + h • e) * dq e h (wd (b j) w) x *
        dq e h (wd (b i) w) x := by
      rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hint i j))]
      exact Finset.sum_congr rfl fun i _ => integral_finset_sum _ (fun j _ => hint i j)
    have e2 : ∫ x, θ * ∑ j, dq e h (wd (b j) w) x ^ 2 = θ * X := by
      rw [integral_const_mul, integral_finset_sum _ (fun j _ => (hW j).integrable_sq)]
    rw [← e1, ← e2]
    refine integral_mono ((integrable_finset_sum _ (fun j _ => (hW j).integrable_sq)).const_mul θ)
      (integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hint i j)))
      (fun x => ?_)
    exact hA.elliptic (x + h • e) (fun j => dq e h (wd (b j) w) x)
  -- bounds on the pieces
  have hT2 : ∀ i j, |∫ x, dq e h (A i j) x * wd (b j) w x * dq e h (wd (b i) w) x| ≤
      K * l2 (wd (b j) w) * s := by
    intro i j
    have hdqa : ∀ x, ‖dq e h (A i j) x‖ ≤ K := fun x => by
      have := abs_dq_le_of_fderiv_bound (hA.smooth i j) (hA.fderiv_bound i j) e hh x
      rw [he, b.norm_eq_one, mul_one] at this
      simpa using this
    have hf : MemLp (fun x => dq e h (A i j) x * wd (b j) w x) 2 volume :=
      memLp_mul_of_bound (continuous_dq (hA.smooth i j).continuous e h) hdqa (hwd j).2
    have h1 := abs_integral_mul_le_l2 hf (hW i)
    have h2 : l2 (fun x => dq e h (A i j) x * wd (b j) w x) ≤ K * l2 (wd (b j) w) :=
      l2_le_of_abs_le (hwd j).2 hf hK0 (fun x => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (by simpa using hdqa x) (abs_nonneg _))
    calc _ ≤ _ := h1
      _ ≤ (K * l2 (wd (b j) w)) * s :=
        mul_le_mul h2 (hWs i) (l2_nonneg _) (mul_nonneg hK0 (l2_nonneg _))
  have hFb : |∫ x, F x * φ x| ≤ l2 F * s := by
    have h1 := abs_integral_mul_neg_dq_le' (e := e) (h := h) hh hF (memLp_dq hwm)
      (memLp_dq (hwd k).2) (hasWDeriv_dq (v := e) (e := e) hh hwm (hwd k).2 (hwd k).1)
    exact h1.trans (mul_le_mul_of_nonneg_left (hWs k) (l2_nonneg _))
  have hGb : ∀ i, |∫ x, G i x * φ' i x| ≤ l2 (wd (b k) (G i)) * s := by
    intro i
    have h1 := abs_integral_mul_neg_dq_le (e := e) (h := h) hh (hGm i)
      ((Sob.one_wd b (hG i)).2 k).2 (((Sob.one_wd b (hG i)).2 k).1) (hW i)
    exact h1.trans (mul_le_mul_of_nonneg_left (hWs i) (l2_nonneg _))
  -- combine
  have hsplit : ∑ i, ∑ j, ((∫ x, A i j (x + h • e) * dq e h (wd (b j) w) x *
        dq e h (wd (b i) w) x) +
        ∫ x, dq e h (A i j) x * wd (b j) w x * dq e h (wd (b i) w) x) =
      (∑ i, ∑ j, ∫ x, A i j (x + h • e) * dq e h (wd (b j) w) x * dq e h (wd (b i) w) x) +
      ∑ i, ∑ j, ∫ x, dq e h (A i j) x * wd (b j) w x * dq e h (wd (b i) w) x := by
    simp only [Finset.sum_add_distrib]
  have E2 : ∑ i, ∑ j, ((∫ x, A i j (x + h • e) * dq e h (wd (b j) w) x *
        dq e h (wd (b i) w) x) +
        ∫ x, dq e h (A i j) x * wd (b j) w x * dq e h (wd (b i) w) x) =
      (∫ x, F x * φ x) + ∑ i, ∫ x, G i x * φ' i x := by
    rw [← E1]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => (hdec i j).symm
  have hT2sum : |∑ i, ∑ j, ∫ x, dq e h (A i j) x * wd (b j) w x * dq e h (wd (b i) w) x| ≤
      ∑ _i : ι, ∑ j, K * l2 (wd (b j) w) * s := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => hT2 i j))
  have hGsum : |∑ i, ∫ x, G i x * φ' i x| ≤ ∑ i, l2 (wd (b k) (G i)) * s :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => hGb i))
  set a := l2 F + ∑ i, l2 (wd (b k) (G i)) + K * ∑ _i : ι, ∑ j, l2 (wd (b j) w) with ha
  have hwsum : 0 ≤ ∑ _i : ι, ∑ j, l2 (wd (b j) w) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun j _ => l2_nonneg _))
  have hGnn : 0 ≤ ∑ i, l2 (wd (b k) (G i)) := Finset.sum_nonneg (fun i _ => l2_nonneg _)
  have ha0 : 0 ≤ a := add_nonneg (add_nonneg (l2_nonneg _) hGnn) (mul_nonneg hK0 hwsum)
  have hQ : ∑ _i : ι, ∑ j, K * l2 (wd (b j) w) * s = (K * ∑ _i : ι, ∑ j, l2 (wd (b j) w)) * s := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
  have hGs : ∑ i, l2 (wd (b k) (G i)) * s = (∑ i, l2 (wd (b k) (G i))) * s := by
    rw [Finset.sum_mul]
  have key : θ * X ≤ a * s := by
    have := abs_le.1 hFb
    have h3 := abs_le.1 hGsum
    have h4 := abs_le.1 hT2sum
    rw [hQ] at h4
    rw [hGs] at h3
    have hsum := hsplit.symm.trans E2
    have : a * s = l2 F * s + (∑ i, l2 (wd (b k) (G i))) * s + (K * ∑ _i : ι, ∑ j, l2 (wd (b j) w)) * s := by
      rw [ha]; ring
    linarith [hell, hsum, this]
  have hs_le : s ≤ a / θ := by
    rcases hs0.eq_or_lt with h0 | h0
    · rw [← h0]; positivity
    · rw [le_div_iff₀ hθ]
      have : θ * s ^ 2 ≤ a * s := by rw [hs2]; exact key
      nlinarith
  calc X = s ^ 2 := hs2.symm
    _ ≤ (a / θ) ^ 2 := pow_le_pow_left₀ hs0 hs_le 2

end CutoffRigidity.Riemann.Diff
