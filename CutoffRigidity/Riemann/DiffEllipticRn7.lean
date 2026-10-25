module

public import CutoffRigidity.Riemann.DiffEllipticRn6

/-! # Global higher regularity (induction on the order)
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff

set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Diff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)

theorem Sob.sub {m : ℕ} {f g : E → ℝ} (hf : Sob b m f) (hg : Sob b m g) :
    Sob b m (fun x => f x - g x) ∧
      sobSq b m (fun x => f x - g x) ≤ 2 * (sobSq b m f + sobSq b m g) := by
  obtain ⟨h1, h2⟩ := Sob.smul b (-1) hg
  obtain ⟨h3, h4⟩ := Sob.add b hf h1
  have e : (fun x => f x - g x) = f + fun x => -1 * g x := by
    funext x; simp [sub_eq_add_neg]
  rw [e]
  refine ⟨h3, h4.trans ?_⟩
  rw [h2]; nlinarith

theorem sobSq_wd_le (m : ℕ) (u : E → ℝ) (k : ι) : sobSq b m (wd (b k) u) ≤ sobSq b (m + 1) u := by
  show _ ≤ (∫ x, u x ^ 2) + ∑ i, sobSq b m (wd (b i) u)
  have h0 : 0 ≤ ∫ x, u x ^ 2 := integral_nonneg (fun x => sq_nonneg _)
  have := Finset.single_le_sum (f := fun i => sobSq b m (wd (b i) u))
    (fun i _ => sobSq_nonneg b m _) (Finset.mem_univ k)
  linarith

/-- Global higher regularity with constants depending only on `(m, θ, K, #ι)`. -/
theorem global_regularity (θ K : ℝ) (hθ : 0 < θ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ι → ι → E → ℝ), Ell A θ K (m + 1) → ∀ (w F : E → ℝ)
      (G : ι → E → ℝ), Sob b 1 w → AESupp w → Sob b m F → (∀ i, Sob b (m + 1) (G i)) →
      WeakEq b A w F G → Sob b (m + 2) w ∧
        sobSq b (m + 2) w ≤ C * (sobSq b m F + ∑ i, sobSq b (m + 1) (G i) + sobSq b 1 w) := by
  induction m with
  | zero =>
    refine ⟨stepConst (Fintype.card ι) θ K, ?_, ?_⟩
    · unfold stepConst; positivity
    · intro A hA w F G hw hs hF hG heq
      exact regular_step0 b hA hθ hw hs hF hG heq
  | succ m ih =>
    obtain ⟨C, hC0, hC⟩ := ih
    set n := Fintype.card ι with hn
    set mulC := mulConst n K (m + 1) with hmulC
    have hmulC0 : 0 ≤ mulC := mulConst_nonneg n K (m + 1)
    set Fac : ℝ := 1 + 2 * n + 2 * 2 ^ n * (n : ℝ) ^ 2 * mulC * C + C with hFac
    refine ⟨1 + n * C * Fac, ?_, ?_⟩
    · have : 0 ≤ Fac := by rw [hFac]; positivity
      positivity
    intro A hA w F G hw hs hF hG heq
    have hAm : Ell A θ K (m + 1) := hA.mono (Nat.le_succ _)
    have hA1 : Ell A θ K 1 := hA.mono (by omega)
    have hFm : Sob b m F := Sob.mono b (Nat.le_succ m) hF
    have hGm : ∀ i, Sob b (m + 1) (G i) := fun i => Sob.mono b (Nat.le_succ _) (hG i)
    obtain ⟨hw2, hw2b⟩ := hC A hAm w F G hw hs hFm hGm heq
    set D := sobSq b (m + 1) F + ∑ i, sobSq b (m + 1 + 1) (G i) + sobSq b 1 w with hD
    have hD0 : 0 ≤ D := by
      have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sobSq_nonneg b (m + 1 + 1) (G i))
      have := sobSq_nonneg b (m + 1) F
      have := sobSq_nonneg b 1 w
      rw [hD]; linarith
    have hD' : sobSq b m F + ∑ i, sobSq b (m + 1) (G i) + sobSq b 1 w ≤ D := by
      have h1 := sobSq_le_succ b m F
      have h2 : ∑ i, sobSq b (m + 1) (G i) ≤ ∑ i, sobSq b (m + 1 + 1) (G i) :=
        Finset.sum_le_sum (fun i _ => sobSq_le_succ b (m + 1) _)
      rw [hD]; linarith
    set T := C * D with hT
    have hS2 : sobSq b (m + 2) w ≤ T := hw2b.trans (mul_le_mul_of_nonneg_left hD' hC0)
    have hT0 : 0 ≤ T := by rw [hT]; positivity
    -- the equation for the derivative
    have hk : ∀ k, Sob b (m + 2) (wd (b k) w) ∧
        sobSq b (m + 2) (wd (b k) w) ≤ C * D * Fac := by
      intro k
      obtain ⟨-, hwd⟩ := (Sob.succ_iff b).1 hw2
      have hv : Sob b (m + 1) (wd (b k) w) := (hwd k).2
      have hv1 : Sob b 1 (wd (b k) w) := Sob.mono b (by omega) hv
      have hvs : AESupp (wd (b k) w) := aesupp_of_hasWDeriv hs (hwd k).1
      have heqk := WeakEq.deriv b hA1 (Sob.mono b (by omega) hw2) (Sob.mono b (by omega) hF)
        (fun i => Sob.mono b (by omega) (hG i)) heq k
      have hF' : Sob b m (wd (b k) F) := (((Sob.succ_iff b).1 hF).2 k).2
      have hGk : ∀ i, Sob b (m + 1) (wd (b k) (G i)) := fun i => (((Sob.succ_iff b).1 (hG i)).2 k).2
      have hwjm : ∀ j, Sob b (m + 1) (wd (b j) w) := fun j => (hwd j).2
      have hprod : ∀ i j, Sob b (m + 1) (fun x => pd (b k) (A i j) x * wd (b j) w x) ∧
          sobSq b (m + 1) (fun x => pd (b k) (A i j) x * wd (b j) w x) ≤
            mulC * sobSq b (m + 1) (wd (b j) w) := by
        intro i j
        have hKi : ∀ k' ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ k' (pd (b k) (A i j)) x‖ ≤ K := by
          intro k' hk' x
          refine (norm_iteratedFDeriv_pd_le (hA.smooth i j) (b k) k' x).trans ?_
          rw [b.norm_eq_one, one_mul]
          exact hA.bound i j (k' + 1) (by omega) x
        exact Sob.mul_smooth b (contDiff_pd (hA.smooth i j) _) hKi (hwjm j)
      have hsum : ∀ i, Sob b (m + 1) (fun x => ∑ j ∈ Finset.univ, pd (b k) (A i j) x * wd (b j) w x) ∧
          sobSq b (m + 1) (fun x => ∑ j ∈ Finset.univ, pd (b k) (A i j) x * wd (b j) w x) ≤
            2 ^ n * ((n : ℝ) * (mulC * T)) := by
        intro i
        obtain ⟨h1, h2⟩ := Sob.sum b (m + 1) Finset.univ
          (fun j x => pd (b k) (A i j) x * wd (b j) w x) (fun j _ => (hprod i j).1)
        refine ⟨h1, h2.trans ?_⟩
        rw [Finset.card_univ, ← hn]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ∑ j, sobSq b (m + 1) (fun x => pd (b k) (A i j) x * wd (b j) w x)
            ≤ ∑ _j : ι, mulC * T := Finset.sum_le_sum (fun j _ => by
              refine (hprod i j).2.trans (mul_le_mul_of_nonneg_left ?_ hmulC0)
              exact (sobSq_wd_le b (m + 1) w j).trans hS2)
          _ = (n : ℝ) * (mulC * T) := by simp [hn]
      have hG' : ∀ i, Sob b (m + 1) (fun x => wd (b k) (G i) x -
            ∑ j, pd (b k) (A i j) x * wd (b j) w x) ∧
          sobSq b (m + 1) (fun x => wd (b k) (G i) x - ∑ j, pd (b k) (A i j) x * wd (b j) w x)
            ≤ 2 * (D + 2 ^ n * ((n : ℝ) * (mulC * T))) := by
        intro i
        obtain ⟨h1, h2⟩ := Sob.sub b (hGk i) (hsum i).1
        refine ⟨h1, h2.trans ?_⟩
        have h3 : sobSq b (m + 1) (wd (b k) (G i)) ≤ D := by
          refine (sobSq_wd_le b (m + 1) (G i) k).trans ?_
          have := Finset.single_le_sum (f := fun i => sobSq b (m + 1 + 1) (G i))
            (fun i _ => sobSq_nonneg b _ _) (Finset.mem_univ i)
          have := sobSq_nonneg b (m + 1) F
          have := sobSq_nonneg b 1 w
          rw [hD]; linarith
        linarith [(hsum i).2]
      obtain ⟨hv2, hv2b⟩ := hC A hAm (wd (b k) w) (wd (b k) F)
        (fun i x => wd (b k) (G i) x - ∑ j, pd (b k) (A i j) x * wd (b j) w x) hv1 hvs hF'
        (fun i => (hG' i).1) heqk
      refine ⟨hv2, hv2b.trans ?_⟩
      have f1 : sobSq b m (wd (b k) F) ≤ D := by
        refine (sobSq_wd_le b m F k).trans ?_
        have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sobSq_nonneg b (m + 1 + 1) (G i))
        have := sobSq_nonneg b 1 w
        rw [hD]; linarith
      have f2 : ∑ i, sobSq b (m + 1)
          (fun x => wd (b k) (G i) x - ∑ j, pd (b k) (A i j) x * wd (b j) w x) ≤
          n * (2 * (D + 2 ^ n * ((n : ℝ) * (mulC * T)))) := by
        calc _ ≤ ∑ _i : ι, 2 * (D + 2 ^ n * ((n : ℝ) * (mulC * T))) :=
              Finset.sum_le_sum (fun i _ => (hG' i).2)
          _ = _ := by simp [hn]
      have f3 : sobSq b 1 (wd (b k) w) ≤ T := by
        refine (sobSq_wd_le b 1 w k).trans ?_
        exact (sobSq_mono b (by omega : 2 ≤ m + 2) w).trans hS2
      have hfin : sobSq b m (wd (b k) F) + ∑ i, sobSq b (m + 1)
          (fun x => wd (b k) (G i) x - ∑ j, pd (b k) (A i j) x * wd (b j) w x) +
          sobSq b 1 (wd (b k) w) ≤ D * Fac := by
        have : D * Fac = D + n * (2 * (D + 2 ^ n * ((n : ℝ) * (mulC * (C * D))))) + C * D := by
          rw [hFac]; ring
        rw [this]
        linarith
      calc C * (sobSq b m (wd (b k) F) + ∑ i, sobSq b (m + 1)
          (fun x => wd (b k) (G i) x - ∑ j, pd (b k) (A i j) x * wd (b j) w x) +
          sobSq b 1 (wd (b k) w)) ≤ C * (D * Fac) := mul_le_mul_of_nonneg_left hfin hC0
        _ = C * D * Fac := by ring
    refine ⟨?_, ?_⟩
    · refine (Sob.succ_iff b).2 ⟨hw2.memLp b, fun k => ⟨(((Sob.succ_iff b).1 hw2).2 k).1, (hk k).1⟩⟩
    · have e1 : sobSq b (m + 1 + 2) w = (∫ x, w x ^ 2) + ∑ k, sobSq b (m + 2) (wd (b k) w) := by
        have := sobSq_succ_eq b (m := m + 2) (u := w) (w := fun k => wd (b k) w)
          (fun k => ⟨(((Sob.succ_iff b).1 hw2).2 k).1, ((hk k).1).memLp b⟩)
        exact this
      rw [e1]
      have i1 : ∫ x, w x ^ 2 ≤ D := by
        refine (integral_sq_le_sobSq b 1 w).trans ?_
        have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sobSq_nonneg b (m + 1 + 1) (G i))
        have := sobSq_nonneg b (m + 1) F
        rw [hD]; linarith
      have i2 : ∑ k, sobSq b (m + 2) (wd (b k) w) ≤ ∑ _k : ι, C * D * Fac :=
        Finset.sum_le_sum (fun k _ => (hk k).2)
      have i3 : ∑ _k : ι, C * D * Fac = n * (C * D * Fac) := by simp [hn]
      have : (1 + n * C * Fac) * (sobSq b (m + 1) F + ∑ i, sobSq b (m + 1 + 1) (G i) + sobSq b 1 w)
          = D + n * (C * D * Fac) := by rw [← hD]; ring
      rw [this]
      linarith

end CutoffRigidity.Riemann.Diff
