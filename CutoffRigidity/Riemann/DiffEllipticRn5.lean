module

public import CutoffRigidity.Riemann.DiffEllipticRn4

/-! # The differentiated equation
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff

set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Diff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)

theorem IsTest.memLp {ψ : E → ℝ} (hψ : IsTest Set.univ ψ) : MemLp ψ 2 volume :=
  hψ.1.continuous.memLp_of_hasCompactSupport hψ.2.1

theorem integrable_mul_test {f ψ : E → ℝ} (hf : MemLp f 2 volume) (hψ : IsTest Set.univ ψ) :
    Integrable (fun x => f x * ψ x) volume :=
  hf.integrable_mul hψ.memLp

theorem Ell.pd_bound {A : ι → ι → E → ℝ} {θ K : ℝ} {N : ℕ} (hA : Ell A θ K (N + 1)) (i j k : ι)
    (x : E) : ‖pd (b k) (A i j) x‖ ≤ K := by
  have h1 := hA.fderiv_bound i j x
  have h2 : ‖fderiv ℝ (A i j) x (b k)‖ ≤ ‖fderiv ℝ (A i j) x‖ * ‖b k‖ :=
    ContinuousLinearMap.le_opNorm _ _
  rw [b.norm_eq_one, mul_one] at h2
  exact h2.trans h1

theorem Ell.memLp_pd_mul {A : ι → ι → E → ℝ} {θ K : ℝ} {N : ℕ} (hA : Ell A θ K (N + 1))
    (i j k : ι) {f : E → ℝ} (hf : MemLp f 2 volume) :
    MemLp (fun x => pd (b k) (A i j) x * f x) 2 volume :=
  memLp_mul_of_bound (contDiff_pd (hA.smooth i j) _).continuous (hA.pd_bound b i j k) hf

/-- Differentiating the weak equation in direction `b k`. -/
theorem WeakEq.deriv {A : ι → ι → E → ℝ} {θ K : ℝ} (hA : Ell A θ K 1) {w F : E → ℝ}
    {G : ι → E → ℝ} (hw : Sob b 2 w) (hF : Sob b 1 F) (hG : ∀ i, Sob b 1 (G i))
    (heq : WeakEq b A w F G) (k : ι) :
    WeakEq b A (wd (b k) w) (wd (b k) F)
      (fun i x => wd (b k) (G i) x - ∑ j, pd (b k) (A i j) x * wd (b j) w x) := by
  intro φ hφ
  obtain ⟨hwm, hw2⟩ := (Sob.succ_iff b).1 hw
  have hwj : ∀ j, MemLp (wd (b j) w) 2 volume ∧ ∀ k', HasWDeriv Set.univ (b k') (wd (b j) w)
      (wd (b k') (wd (b j) w)) ∧ MemLp (wd (b k') (wd (b j) w)) 2 volume :=
    fun j => Sob.one_wd b (hw2 j).2
  obtain ⟨hFm, hFd⟩ := Sob.one_wd b hF
  have hGd := fun i => Sob.one_wd b (hG i)
  have hψ : ∀ i, IsTest Set.univ (pd (b i) φ) := fun i => hφ.pd (b i)
  have hφk : IsTest Set.univ (pd (b k) φ) := hφ.pd (b k)
  -- the equation tested with `∂_k φ`
  have A1 := heq _ hφk
  have hcomm : ∀ i, pd (b i) (pd (b k) φ) = pd (b k) (pd (b i) φ) := fun i =>
    pd_pd_comm hφ.1 (b k) (b i)
  simp only [hcomm] at A1
  -- terms with the coefficient
  have hprod : ∀ i j, HasWDeriv Set.univ (b k) (fun x => A i j x * wd (b j) w x)
      (fun x => A i j x * wd (b k) (wd (b j) w) x + pd (b k) (A i j) x * wd (b j) w x) :=
    fun i j => (hwj j).2 k |>.1 |> HasWDeriv.mul_smooth isOpen_univ (hA.smooth i j)
  have B1 : ∀ i j, ∫ x, A i j x * wd (b j) w x * pd (b k) (pd (b i) φ) x =
      -((∫ x, A i j x * wd (b k) (wd (b j) w) x * pd (b i) φ x) +
        ∫ x, pd (b k) (A i j) x * wd (b j) w x * pd (b i) φ x) := by
    intro i j
    have := (hprod i j).2.2 _ (hψ i)
    have i1 : Integrable (fun x => A i j x * wd (b k) (wd (b j) w) x * pd (b i) φ x) volume :=
      integrable_mul_test (hA.memLp_mul i j ((hwj j).2 k).2) (hψ i)
    have i2 : Integrable (fun x => pd (b k) (A i j) x * wd (b j) w x * pd (b i) φ x) volume :=
      integrable_mul_test (hA.memLp_pd_mul b i j k (hwj j).1) (hψ i)
    rw [this, ← integral_add i1 i2]
    congr 2; funext x; ring
  have B2 : ∫ x, F x * pd (b k) φ x = -∫ x, wd (b k) F x * φ x := (hFd k).1.2.2 φ hφ
  have B3 : ∀ i, ∫ x, G i x * pd (b k) (pd (b i) φ) x = -∫ x, wd (b k) (G i) x * pd (b i) φ x :=
    fun i => ((hGd i).2 k).1.2.2 _ (hψ i)
  rw [B2] at A1
  simp only [B1, B3] at A1
  -- symmetry of the mixed derivatives
  have hsym : ∀ j, wd (b j) (wd (b k) w) =ᵐ[volume] wd (b k) (wd (b j) w) := by
    intro j
    have hm : HasWDeriv Set.univ (b j) (wd (b k) w) (wd (b k) (wd (b j) w)) :=
      HasWDeriv.mixed (hw2 j).1 (hw2 k).1 ((hwj j).2 k).1
    exact (wd_spec hm ((hwj j).2 k).2).2.2
  have C1 : ∀ i j, ∫ x, A i j x * wd (b j) (wd (b k) w) x * pd (b i) φ x =
      ∫ x, A i j x * wd (b k) (wd (b j) w) x * pd (b i) φ x := by
    intro i j
    refine integral_congr_ae ?_
    filter_upwards [hsym j] with x hx
    rw [hx]
  have hQint : ∀ i j, Integrable (fun x => pd (b k) (A i j) x * wd (b j) w x * pd (b i) φ x)
      volume := fun i j => integrable_mul_test (hA.memLp_pd_mul b i j k (hwj j).1) (hψ i)
  have C2 : ∀ i, ∫ x, (wd (b k) (G i) x - ∑ j, pd (b k) (A i j) x * wd (b j) w x) *
      pd (b i) φ x = (∫ x, wd (b k) (G i) x * pd (b i) φ x) -
        ∑ j, ∫ x, pd (b k) (A i j) x * wd (b j) w x * pd (b i) φ x := by
    intro i
    have e : (fun x => (wd (b k) (G i) x - ∑ j, pd (b k) (A i j) x * wd (b j) w x) *
        pd (b i) φ x) = fun x => wd (b k) (G i) x * pd (b i) φ x -
          ∑ j, pd (b k) (A i j) x * wd (b j) w x * pd (b i) φ x := by
      funext x; rw [sub_mul, Finset.sum_mul]
    rw [e, integral_sub (integrable_mul_test ((hGd i).2 k).2 (hψ i))
      (integrable_finset_sum _ (fun j _ => hQint i j)),
      integral_finset_sum _ (fun j _ => hQint i j)]
  simp only [C1, C2]
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, neg_add, Finset.sum_add_distrib] at A1 ⊢
  linarith

end CutoffRigidity.Riemann.Diff
