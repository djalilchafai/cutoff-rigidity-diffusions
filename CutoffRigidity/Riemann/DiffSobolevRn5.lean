module

public import CutoffRigidity.Riemann.DiffSobolevRn4
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! # The canonical weak derivative and the global Sobolev classes

`wd`, `Sob`, `sobSq`: invariance under a.e. equality, monotonicity in the order, algebra
(sums, multiples).
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff

set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Diff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)

theorem wd_spec {v : E} {u w : E → ℝ} (h : HasWDeriv Set.univ v u w) (hw : MemLp w 2 volume) :
    HasWDeriv Set.univ v u (wd v u) ∧ MemLp (wd v u) 2 volume ∧ wd v u =ᵐ[volume] w := by
  have hex : ∃ w, HasWDeriv Set.univ v u w ∧ MemLp w 2 volume := ⟨w, h, hw⟩
  have hs := hex.choose_spec
  have e : wd v u = hex.choose := by
    simp only [wd, hex, ↓reduceDIte]
  rw [e]
  exact ⟨hs.1, hs.2, hs.1.unique h⟩

theorem wd_congr {v : E} {u u' : E → ℝ} (hu : u =ᵐ[volume] u') : wd v u = wd v u' := by
  have hpred : (fun w => HasWDeriv Set.univ v u w ∧ MemLp w 2 volume) =
      (fun w => HasWDeriv Set.univ v u' w ∧ MemLp w 2 volume) := by
    funext w
    exact propext (and_congr_left' (hasWDeriv_congr_left hu))
  unfold wd
  rw [hpred]

theorem Sob.memLp {m : ℕ} {u : E → ℝ} (h : Sob b m u) : MemLp u 2 volume := by
  cases m with
  | zero => exact h
  | succ m => exact h.1

theorem Sob.congr_ae {m : ℕ} {u u' : E → ℝ} (h : Sob b m u) (hu : u =ᵐ[volume] u') :
    Sob b m u' := by
  induction m generalizing u u' with
  | zero => exact MemLp.ae_eq hu h
  | succ m ih =>
    refine ⟨MemLp.ae_eq hu h.1, fun i => ?_⟩
    obtain ⟨w, hw, hS⟩ := h.2 i
    exact ⟨w, hw.congr_ae hu Filter.EventuallyEq.rfl, hS⟩

theorem Sob.mono {m m' : ℕ} (hm : m ≤ m') {u : E → ℝ} (h : Sob b m' u) : Sob b m u := by
  induction m' generalizing m u with
  | zero =>
    have : m = 0 := by omega
    subst this; exact h
  | succ m' ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · exact h.memLp
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      refine ⟨h.1, fun i => ?_⟩
      obtain ⟨w, hw, hS⟩ := h.2 i
      exact ⟨w, hw, ih (by omega) hS⟩

theorem sobSq_congr_ae {m : ℕ} {u u' : E → ℝ} (hu : u =ᵐ[volume] u') :
    sobSq b m u = sobSq b m u' := by
  have hint : ∫ x, u x ^ 2 = ∫ x, u' x ^ 2 :=
    integral_congr_ae (by filter_upwards [hu] with x hx; rw [hx])
  cases m with
  | zero => exact hint
  | succ m =>
    show (∫ x, u x ^ 2) + ∑ i, sobSq b m (wd (b i) u) = (∫ x, u' x ^ 2) + ∑ i, sobSq b m (wd (b i) u')
    rw [hint]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by rw [wd_congr hu])

theorem Sob.succ_iff {m : ℕ} {u : E → ℝ} :
    Sob b (m + 1) u ↔ MemLp u 2 volume ∧ ∀ i, HasWDeriv Set.univ (b i) u (wd (b i) u) ∧
      Sob b m (wd (b i) u) := by
  constructor
  · intro h
    refine ⟨h.1, fun i => ?_⟩
    obtain ⟨w, hw, hS⟩ := h.2 i
    obtain ⟨h1, h2, h3⟩ := wd_spec hw hS.memLp
    exact ⟨h1, hS.congr_ae b h3.symm⟩
  · intro h
    exact ⟨h.1, fun i => ⟨_, (h.2 i).1, (h.2 i).2⟩⟩

theorem sobSq_succ_eq {m : ℕ} {u : E → ℝ} {w : ι → E → ℝ}
    (hw : ∀ i, HasWDeriv Set.univ (b i) u (w i) ∧ MemLp (w i) 2 volume) :
    sobSq b (m + 1) u = (∫ x, u x ^ 2) + ∑ i, sobSq b m (w i) := by
  show (∫ x, u x ^ 2) + ∑ i, sobSq b m (wd (b i) u) = _
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact sobSq_congr_ae b (wd_spec (hw i).1 (hw i).2).2.2

theorem sobSq_nonneg (m : ℕ) (u : E → ℝ) : 0 ≤ sobSq b m u := by
  induction m generalizing u with
  | zero => exact integral_nonneg (fun x => sq_nonneg _)
  | succ m ih =>
    exact add_nonneg (integral_nonneg (fun x => sq_nonneg _))
      (Finset.sum_nonneg (fun i _ => ih _))

theorem sobSq_le_succ (m : ℕ) (u : E → ℝ) : sobSq b m u ≤ sobSq b (m + 1) u := by
  induction m generalizing u with
  | zero =>
    show ∫ x, u x ^ 2 ≤ (∫ x, u x ^ 2) + ∑ i, sobSq b 0 (wd (b i) u)
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => sobSq_nonneg b 0 _))
  | succ m ih =>
    show (∫ x, u x ^ 2) + ∑ i, sobSq b m (wd (b i) u) ≤
      (∫ x, u x ^ 2) + ∑ i, sobSq b (m + 1) (wd (b i) u)
    exact add_le_add le_rfl (Finset.sum_le_sum (fun i _ => ih _))

theorem sobSq_mono {m m' : ℕ} (hm : m ≤ m') (u : E → ℝ) : sobSq b m u ≤ sobSq b m' u := by
  induction hm with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (sobSq_le_succ b _ u)

theorem integral_sq_le_sobSq (m : ℕ) (u : E → ℝ) : ∫ x, u x ^ 2 ≤ sobSq b m u :=
  sobSq_mono b (Nat.zero_le m) u

theorem integral_sq_add_le {f g : E → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ∫ x, (f x + g x) ^ 2 ≤ 2 * ((∫ x, f x ^ 2) + ∫ x, g x ^ 2) := by
  have h1 : Integrable (fun x => f x ^ 2) volume := hf.integrable_sq
  have h2 : Integrable (fun x => g x ^ 2) volume := hg.integrable_sq
  have h3 : Integrable (fun x => (f x + g x) ^ 2) volume := (hf.add hg).integrable_sq
  calc ∫ x, (f x + g x) ^ 2 ≤ ∫ x, 2 * (f x ^ 2 + g x ^ 2) :=
        integral_mono h3 ((h1.add h2).const_mul 2) (fun x => by
          simp only; nlinarith [sq_nonneg (f x - g x)])
    _ = _ := by rw [integral_const_mul, integral_add h1 h2]

theorem Sob.add {m : ℕ} {f g : E → ℝ} (hf : Sob b m f) (hg : Sob b m g) :
    Sob b m (f + g) ∧ sobSq b m (f + g) ≤ 2 * (sobSq b m f + sobSq b m g) := by
  induction m generalizing f g with
  | zero => exact ⟨MemLp.add hf hg, integral_sq_add_le hf hg⟩
  | succ m ih =>
    rw [Sob.succ_iff b] at hf hg
    have key : ∀ i, HasWDeriv Set.univ (b i) (f + g) (wd (b i) f + wd (b i) g) ∧
        Sob b m (wd (b i) f + wd (b i) g) ∧
        sobSq b m (wd (b i) f + wd (b i) g) ≤
          2 * (sobSq b m (wd (b i) f) + sobSq b m (wd (b i) g)) := fun i =>
      ⟨(hf.2 i).1.add (hg.2 i).1, (ih (hf.2 i).2 (hg.2 i).2).1, (ih (hf.2 i).2 (hg.2 i).2).2⟩
    have hmem : ∀ i, MemLp (wd (b i) f + wd (b i) g) 2 volume := fun i => (key i).2.1.memLp b
    refine ⟨(Sob.succ_iff b).2 ⟨hf.1.add hg.1, fun i => ?_⟩, ?_⟩
    · obtain ⟨h1, h2, h3⟩ := wd_spec (key i).1 (hmem i)
      exact ⟨h1, ((key i).2.1).congr_ae b h3.symm⟩
    · rw [sobSq_succ_eq b (fun i => ⟨(key i).1, hmem i⟩),
        sobSq_succ_eq b (fun i => ⟨(hf.2 i).1, (hf.2 i).2.memLp b⟩),
        sobSq_succ_eq b (fun i => ⟨(hg.2 i).1, (hg.2 i).2.memLp b⟩)]
      have h0 := integral_sq_add_le hf.1 hg.1
      have hs : ∑ i, sobSq b m (wd (b i) f + wd (b i) g) ≤
          2 * (∑ i, sobSq b m (wd (b i) f) + ∑ i, sobSq b m (wd (b i) g)) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        exact Finset.sum_le_sum (fun i _ => (key i).2.2)
      have e1 : ∑ i, sobSq b m (wd (b i) f) = ∑ i, sobSq b m (wd (b i) f) := rfl
      simp only [Pi.add_apply] at *
      nlinarith [h0, hs]

theorem Sob.smul {m : ℕ} {f : E → ℝ} (c : ℝ) (hf : Sob b m f) :
    Sob b m (fun x => c * f x) ∧ sobSq b m (fun x => c * f x) = c ^ 2 * sobSq b m f := by
  induction m generalizing f with
  | zero =>
    refine ⟨MemLp.const_mul hf c, ?_⟩
    show ∫ x, (c * f x) ^ 2 = c ^ 2 * ∫ x, f x ^ 2
    rw [← integral_const_mul]; congr 1; funext x; ring
  | succ m ih =>
    rw [Sob.succ_iff b] at hf
    have key : ∀ i, HasWDeriv Set.univ (b i) (fun x => c * f x) (fun x => c * wd (b i) f x) ∧
        Sob b m (fun x => c * wd (b i) f x) ∧
        sobSq b m (fun x => c * wd (b i) f x) = c ^ 2 * sobSq b m (wd (b i) f) := fun i =>
      ⟨(hf.2 i).1.smul c, (ih (hf.2 i).2).1, (ih (hf.2 i).2).2⟩
    have hmem : ∀ i, MemLp (fun x => c * wd (b i) f x) 2 volume := fun i => (key i).2.1.memLp b
    refine ⟨(Sob.succ_iff b).2 ⟨hf.1.const_mul c, fun i => ?_⟩, ?_⟩
    · obtain ⟨h1, h2, h3⟩ := wd_spec (key i).1 (hmem i)
      exact ⟨h1, ((key i).2.1).congr_ae b h3.symm⟩
    · rw [sobSq_succ_eq b (fun i => ⟨(key i).1, hmem i⟩),
        sobSq_succ_eq b (fun i => ⟨(hf.2 i).1, (hf.2 i).2.memLp b⟩)]
      have h0 : ∫ x, (c * f x) ^ 2 = c ^ 2 * ∫ x, f x ^ 2 := by
        rw [← integral_const_mul]; congr 1; funext x; ring
      rw [h0, mul_add, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => (key i).2.2)

/-- Constant in the Leibniz estimate for `H^m` norms. -/
def mulConst (n : ℕ) (K : ℝ) : ℕ → ℝ
  | 0 => K ^ 2
  | m + 1 => K ^ 2 + 2 * ((n : ℝ) + 1) * mulConst n K m

theorem mulConst_nonneg (n : ℕ) (K : ℝ) (m : ℕ) : 0 ≤ mulConst n K m := by
  induction m with
  | zero => exact sq_nonneg _
  | succ m ih => exact add_nonneg (sq_nonneg _) (by positivity)

theorem contDiff_pd {g : E → ℝ} (hg : ContDiff ℝ ∞ g) (v : E) : ContDiff ℝ ∞ (pd v g) :=
  (hg.fderiv_right (by simp)).clm_apply contDiff_const

theorem norm_iteratedFDeriv_pd_le {g : E → ℝ} (hg : ContDiff ℝ ∞ g) (v : E) (k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ k (pd v g) x‖ ≤ ‖v‖ * ‖iteratedFDeriv ℝ (k + 1) g x‖ := by
  have h := norm_iteratedFDeriv_clm_apply_const (𝕜 := ℝ) (f := fderiv ℝ g) (c := v) (x := x)
    (N := ∞) (n := k) ((hg.fderiv_right (by simp)).contDiffAt) (by simp)
  rw [norm_iteratedFDeriv_fderiv] at h
  exact h

theorem integral_sq_mul_le {g f : E → ℝ} {K : ℝ} (hg : Continuous g) (hb : ∀ x, ‖g x‖ ≤ K)
    (hf : MemLp f 2 volume) :
    MemLp (fun x => g x * f x) 2 volume ∧ ∫ x, (g x * f x) ^ 2 ≤ K ^ 2 * ∫ x, f x ^ 2 := by
  have hmem : MemLp (fun x => g x * f x) 2 volume :=
    MemLp.of_le_mul (c := K) hf (hg.aestronglyMeasurable.mul hf.aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun x => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)))
  refine ⟨hmem, ?_⟩
  rw [← integral_const_mul]
  exact integral_mono hmem.integrable_sq (hf.integrable_sq.const_mul _)
    (fun x => by
      simp only
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (by
        have := hb x
        have h0 := norm_nonneg (g x)
        calc g x ^ 2 = ‖g x‖ ^ 2 := by simp
          _ ≤ K ^ 2 := pow_le_pow_left₀ h0 this 2) (sq_nonneg _))

theorem Sob.mul_smooth {m : ℕ} {g f : E → ℝ} (hg : ContDiff ℝ ∞ g) {K : ℝ}
    (hK : ∀ k ≤ m, ∀ x, ‖iteratedFDeriv ℝ k g x‖ ≤ K) (hf : Sob b m f) :
    Sob b m (fun x => g x * f x) ∧
      sobSq b m (fun x => g x * f x) ≤ mulConst (Fintype.card ι) K m * sobSq b m f := by
  induction m generalizing g f with
  | zero =>
    have hb : ∀ x, ‖g x‖ ≤ K := fun x => by
      simpa using hK 0 le_rfl x
    exact integral_sq_mul_le hg.continuous hb (hf : MemLp f 2 volume)
  | succ m ih =>
    set n := Fintype.card ι with hn
    set c := mulConst n K m with hc
    have hc0 : 0 ≤ c := mulConst_nonneg n K m
    rw [Sob.succ_iff b] at hf
    have hfm : Sob b m f := Sob.mono b (Nat.le_succ m) ((Sob.succ_iff b).2 hf)
    have hK' : ∀ k ≤ m, ∀ x, ‖iteratedFDeriv ℝ k g x‖ ≤ K := fun k hk => hK k (by omega)
    have key : ∀ i, HasWDeriv Set.univ (b i) (fun x => g x * f x)
        (fun x => g x * wd (b i) f x + pd (b i) g x * f x) ∧
        Sob b m (fun x => g x * wd (b i) f x + pd (b i) g x * f x) ∧
        sobSq b m (fun x => g x * wd (b i) f x + pd (b i) g x * f x) ≤
          2 * (c * sobSq b m (wd (b i) f) + c * sobSq b m f) := by
      intro i
      have hgi : ContDiff ℝ ∞ (pd (b i) g) := contDiff_pd hg _
      have hKi : ∀ k ≤ m, ∀ x, ‖iteratedFDeriv ℝ k (pd (b i) g) x‖ ≤ K := by
        intro k hk x
        refine (norm_iteratedFDeriv_pd_le hg (b i) k x).trans ?_
        rw [b.norm_eq_one, one_mul]
        exact hK (k + 1) (by omega) x
      obtain ⟨s1, s2⟩ := ih hg hK' (hf.2 i).2
      obtain ⟨t1, t2⟩ := ih hgi hKi hfm
      obtain ⟨a1, a2⟩ := Sob.add b s1 t1
      refine ⟨((hf.2 i).1).mul_smooth isOpen_univ hg, a1, a2.trans ?_⟩
      nlinarith [s2, t2]
    have hmem : ∀ i, MemLp (fun x => g x * wd (b i) f x + pd (b i) g x * f x) 2 volume :=
      fun i => (key i).2.1.memLp b
    have hmem0 : MemLp (fun x => g x * f x) 2 volume := (ih hg hK' hfm).1.memLp b
    have h0 := (ih hg hK' hfm)
    have hb : ∀ x, ‖g x‖ ≤ K := fun x => by
      simpa using hK 0 (Nat.zero_le _) x
    obtain ⟨-, hint⟩ := integral_sq_mul_le hg.continuous hb hf.1
    have hweak : ∀ i, HasWDeriv Set.univ (b i) f (wd (b i) f) ∧ MemLp (wd (b i) f) 2 volume :=
      fun i => ⟨(hf.2 i).1, (hf.2 i).2.memLp b⟩
    refine ⟨(Sob.succ_iff b).2 ⟨hmem0, fun i => ?_⟩, ?_⟩
    · obtain ⟨h1, h2, h3⟩ := wd_spec (key i).1 (hmem i)
      exact ⟨h1, ((key i).2.1).congr_ae b h3.symm⟩
    · rw [sobSq_succ_eq b (fun i => ⟨(key i).1, hmem i⟩)]
      have hS : sobSq b (m + 1) f = (∫ x, f x ^ 2) + ∑ i, sobSq b m (wd (b i) f) :=
        sobSq_succ_eq b hweak
      have hsum : ∑ i, sobSq b m (wd (b i) f) ≤ sobSq b (m + 1) f := by
        rw [hS]
        have : 0 ≤ ∫ x, f x ^ 2 := integral_nonneg (fun x => sq_nonneg _)
        linarith
      have hint0 : ∫ x, f x ^ 2 ≤ sobSq b (m + 1) f := integral_sq_le_sobSq b _ _
      have hm : sobSq b m f ≤ sobSq b (m + 1) f := sobSq_le_succ b m f
      have hsum2 : ∑ i, sobSq b m (fun x => g x * wd (b i) f x + pd (b i) g x * f x) ≤
          ∑ i, (2 * (c * sobSq b m (wd (b i) f) + c * sobSq b m f)) :=
        Finset.sum_le_sum (fun i _ => (key i).2.2)
      have hsum3 : ∑ i, (2 * (c * sobSq b m (wd (b i) f) + c * sobSq b m f)) =
          2 * c * ∑ i, sobSq b m (wd (b i) f) + 2 * c * (n : ℝ) * sobSq b m f := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, ← hn]
        ring
      have e1 : mulConst n K (m + 1) = K ^ 2 + 2 * ((n : ℝ) + 1) * c := rfl
      rw [e1]
      have t1 : 2 * c * ∑ i, sobSq b m (wd (b i) f) ≤ 2 * c * sobSq b (m + 1) f :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      have t2 : 2 * c * (n : ℝ) * sobSq b m f ≤ 2 * c * (n : ℝ) * sobSq b (m + 1) f :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      have t3 : K ^ 2 * ∫ x, f x ^ 2 ≤ K ^ 2 * sobSq b (m + 1) f :=
        mul_le_mul_of_nonneg_left hint0 (sq_nonneg _)
      nlinarith [hsum2, hsum3, t1, t2, t3, hint]

theorem Sob.of_smooth (m : ℕ) {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    Sob b m f ∧ sobSq b m f = sobSmooth b m f := by
  induction m generalizing f with
  | zero => exact ⟨hf.continuous.memLp_of_hasCompactSupport hc, rfl⟩
  | succ m ih =>
    have hmem : MemLp f 2 volume := hf.continuous.memLp_of_hasCompactSupport hc
    have key : ∀ i, HasWDeriv Set.univ (b i) f (pd (b i) f) ∧
        Sob b m (pd (b i) f) ∧ sobSq b m (pd (b i) f) = sobSmooth b m (pd (b i) f) := fun i =>
      ⟨hasWDeriv_of_contDiff (hf.of_le (by simp)) _,
        ih (contDiff_pd hf _) (hc.fderiv_apply ℝ (b i))⟩
    refine ⟨⟨hmem, fun i => ⟨_, (key i).1, (key i).2.1⟩⟩, ?_⟩
    rw [sobSq_succ_eq b (fun i => ⟨(key i).1, (key i).2.1.memLp b⟩)]
    show _ = (∫ x, f x ^ 2) + ∑ i, sobSmooth b m (pd (b i) f)
    congr 1
    exact Finset.sum_congr rfl (fun i _ => (key i).2.2)

end CutoffRigidity.Riemann.Diff
