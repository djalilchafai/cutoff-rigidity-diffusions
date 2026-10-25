module

public import CutoffRigidity.Riemann.DiffEllipticRn2

/-! # The `H²` regularity step (difference quotients)
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff

set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Diff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)

/-- Constant of the `H²` step. -/
noncomputable def stepConst (n : ℕ) (θ K : ℝ) : ℝ := 1 + (n : ℝ) ^ 2 * ((1 + n + K * (n : ℝ) ^ 2) / θ) ^ 2

theorem sobSq_one_eq (u : E → ℝ) : sobSq b 1 u = (∫ x, u x ^ 2) + ∑ k, ∫ x, wd (b k) u x ^ 2 := rfl

theorem integral_wd_sq_le_sobSq_one (u : E → ℝ) (k : ι) :
    ∫ x, wd (b k) u x ^ 2 ≤ sobSq b 1 u := by
  rw [sobSq_one_eq]
  have := Finset.single_le_sum (f := fun k => ∫ x, wd (b k) u x ^ 2)
    (fun k _ => integral_nonneg (fun x => sq_nonneg _)) (Finset.mem_univ k)
  have h0 : 0 ≤ ∫ x, u x ^ 2 := integral_nonneg (fun x => sq_nonneg _)
  linarith

/-- The `H²` regularity step. -/
theorem regular_step0 {A : ι → ι → E → ℝ} {θ K : ℝ} (hA : Ell A θ K 1) (hθ : 0 < θ)
    {w F : E → ℝ} {G : ι → E → ℝ} (hw : Sob b 1 w) (hs : AESupp w) (hF : MemLp F 2 volume)
    (hG : ∀ i, Sob b 1 (G i)) (heq : WeakEq b A w F G) :
    Sob b 2 w ∧ sobSq b 2 w ≤ stepConst (Fintype.card ι) θ K *
      ((∫ x, F x ^ 2) + ∑ i, sobSq b 1 (G i) + sobSq b 1 w) := by
  set n := Fintype.card ι with hn
  obtain ⟨hwm, hwd⟩ := Sob.one_wd b hw
  have hGm : ∀ i, MemLp (G i) 2 volume := fun i => (Sob.one_wd b (hG i)).1
  set D := (∫ x, F x ^ 2) + ∑ i, sobSq b 1 (G i) + sobSq b 1 w with hD
  have hF0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg (fun x => sq_nonneg _)
  have hG0 : 0 ≤ ∑ i, sobSq b 1 (G i) := Finset.sum_nonneg (fun i _ => sobSq_nonneg b 1 _)
  have hw0 : 0 ≤ sobSq b 1 w := sobSq_nonneg b 1 _
  have hD0 : 0 ≤ D := by positivity
  have hsq : 0 ≤ Real.sqrt D := Real.sqrt_nonneg _
  have hlF : l2 F ≤ Real.sqrt D := Real.sqrt_le_sqrt (by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sobSq_nonneg b 1 (G i))
    linarith)
  have hlG : ∀ i k, l2 (wd (b k) (G i)) ≤ Real.sqrt D := fun i k => Real.sqrt_le_sqrt (by
    have h1 := integral_wd_sq_le_sobSq_one b (G i) k
    have h2 := Finset.single_le_sum (f := fun i => sobSq b 1 (G i))
      (fun i _ => sobSq_nonneg b 1 _) (Finset.mem_univ i)
    linarith)
  have hlw : ∀ j, l2 (wd (b j) w) ≤ Real.sqrt D := fun j => Real.sqrt_le_sqrt (by
    have h1 := integral_wd_sq_le_sobSq_one b w j
    linarith)
  set Mb : ℝ := ((1 + n + K * (n : ℝ) ^ 2) / θ) * Real.sqrt D with hMb
  have hK0 : 0 ≤ K ∨ ¬ Nonempty ι := by
    by_cases hne : Nonempty ι
    · obtain ⟨i⟩ := hne
      exact Or.inl (le_trans (norm_nonneg _) (hA.sup_bound i i 0))
    · exact Or.inr hne
  have hKn : ∀ k : ι, (l2 F + ∑ i, l2 (wd (b k) (G i)) + K * ∑ _i : ι, ∑ j, l2 (wd (b j) w)) / θ ≤ Mb := by
    intro k
    have : Nonempty ι := ⟨k⟩
    have hK : 0 ≤ K := by
      rcases hK0 with h | h
      · exact h
      · exact absurd ‹Nonempty ι› h
    have h1 : ∑ i, l2 (wd (b k) (G i)) ≤ n * Real.sqrt D := by
      calc ∑ i, l2 (wd (b k) (G i)) ≤ ∑ _i : ι, Real.sqrt D :=
            Finset.sum_le_sum (fun i _ => hlG i k)
        _ = n * Real.sqrt D := by simp [hn]
    have h2 : ∑ _i : ι, ∑ j, l2 (wd (b j) w) ≤ (n : ℝ) ^ 2 * Real.sqrt D := by
      calc ∑ _i : ι, ∑ j, l2 (wd (b j) w) ≤ ∑ _i : ι, ∑ _j : ι, Real.sqrt D :=
            Finset.sum_le_sum (fun _ _ => Finset.sum_le_sum (fun j _ => hlw j))
        _ = (n : ℝ) ^ 2 * Real.sqrt D := by simp [hn]; ring
    rw [hMb, div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hθ.le
    nlinarith [mul_le_mul_of_nonneg_left h2 hK]
  have hex : ∀ j k : ι, ∃ W : E → ℝ, MemLp W 2 volume ∧
      HasWDeriv Set.univ (b k) (wd (b j) w) W ∧ l2 W ≤ Mb := by
    intro j k
    have : Nonempty ι := ⟨k⟩
    have hK : 0 ≤ K := by
      rcases hK0 with h | h
      · exact h
      · exact absurd ‹Nonempty ι› h
    have hMb0 : 0 ≤ Mb := by
      rw [hMb]; positivity
    obtain ⟨W, h1, h2, h3⟩ := exists_hasWDeriv_of_bdd_dq (v := b k) (hwd j).2 hMb0 (fun m => by
      have hh : (1 / ((m : ℝ) + 1)) ≠ 0 := by positivity
      have hE := dq_energy b hA hθ hw hs hF hG heq k hh
      set a := l2 F + ∑ i, l2 (wd (b k) (G i)) + K * ∑ _i : ι, ∑ j, l2 (wd (b j) w) with ha
      have ha0 : 0 ≤ a := by
        rw [ha]
        have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => l2_nonneg (wd (b k) (G i)))
        have h5 : 0 ≤ ∑ _i : ι, ∑ j, l2 (wd (b j) w) :=
          Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun j _ => l2_nonneg _))
        have := l2_nonneg F
        positivity
      have h6 : ∫ x, dq (b k) (1 / ((m : ℝ) + 1)) (wd (b j) w) x ^ 2 ≤ Mb ^ 2 := by
        have h7 := Finset.single_le_sum (f := fun j => ∫ x, dq (b k) (1 / ((m : ℝ) + 1))
          (wd (b j) w) x ^ 2) (fun j _ => integral_nonneg (fun x => sq_nonneg _))
          (Finset.mem_univ j)
        have h8 : (a / θ) ^ 2 ≤ Mb ^ 2 := pow_le_pow_left₀ (by positivity) (hKn k) 2
        linarith
      calc l2 (dq (b k) (1 / ((m : ℝ) + 1)) (wd (b j) w))
          ≤ Real.sqrt (Mb ^ 2) := Real.sqrt_le_sqrt h6
        _ = Mb := Real.sqrt_sq hMb0)
    exact ⟨W, h1, h2, h3⟩
  choose W hWm hWd hWl using hex
  have hsob2 : Sob b 2 w := by
    refine ⟨hwm, fun j => ⟨wd (b j) w, (hwd j).1, (hwd j).2, fun k => ⟨W j k, hWd j k, hWm j k⟩⟩⟩
  refine ⟨hsob2, ?_⟩
  have e1 : ∀ j, sobSq b 1 (wd (b j) w) = (∫ x, wd (b j) w x ^ 2) + ∑ k, ∫ x, W j k x ^ 2 := by
    intro j
    rw [sobSq_succ_eq b (m := 0) (w := W j) (fun k => ⟨hWd j k, hWm j k⟩)]
    rfl
  have e2 : sobSq b 2 w = (∫ x, w x ^ 2) + ∑ j, sobSq b 1 (wd (b j) w) :=
    sobSq_succ_eq b (m := 1) (w := fun j => wd (b j) w) (fun j => ⟨(hwd j).1, (hwd j).2⟩)
  have e3 : sobSq b 1 w = (∫ x, w x ^ 2) + ∑ j, ∫ x, wd (b j) w x ^ 2 :=
    sobSq_one_eq b w
  have hWsq : ∀ j k, ∫ x, W j k x ^ 2 ≤ Mb ^ 2 := fun j k => by
    have := hWl j k
    have h0 : 0 ≤ l2 (W j k) := l2_nonneg _
    have := pow_le_pow_left₀ h0 (hWl j k) 2
    rwa [l2_sq] at this
  have e4 : sobSq b 2 w ≤ sobSq b 1 w + (n : ℝ) ^ 2 * Mb ^ 2 := by
    rw [e2, e3]
    simp only [e1, Finset.sum_add_distrib]
    have : ∑ j, ∑ k, ∫ x, W j k x ^ 2 ≤ ∑ _j : ι, ∑ _k : ι, Mb ^ 2 :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => hWsq j k))
    have e5 : ∑ _j : ι, ∑ _k : ι, Mb ^ 2 = (n : ℝ) ^ 2 * Mb ^ 2 := by simp [hn]; ring
    linarith
  have e6 : (n : ℝ) ^ 2 * Mb ^ 2 = (n : ℝ) ^ 2 * ((1 + n + K * (n : ℝ) ^ 2) / θ) ^ 2 * D := by
    rw [hMb, mul_pow, Real.sq_sqrt hD0]; ring
  have e7 : sobSq b 1 w ≤ D := by
    rw [hD]; linarith
  calc sobSq b 2 w ≤ sobSq b 1 w + (n : ℝ) ^ 2 * Mb ^ 2 := e4
    _ ≤ D + (n : ℝ) ^ 2 * ((1 + n + K * (n : ℝ) ^ 2) / θ) ^ 2 * D := by rw [← e6]; linarith
    _ = stepConst n θ K * D := by unfold stepConst; ring

end CutoffRigidity.Riemann.Diff
