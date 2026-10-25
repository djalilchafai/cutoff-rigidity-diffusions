module

public import CutoffRigidity.Riemann.DiffSobolevRn8

/-! # Divergence form equations: data, weak formulation, extension to `H¹_c` test functions
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff

set_option linter.unusedSectionVars false

namespace CutoffRigidity.Riemann.Diff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)

/-- Coefficient matrix: smooth, symmetric, uniformly elliptic with constant `θ`, all derivatives
of order `≤ N` bounded by `K`. -/
structure Ell (A : ι → ι → E → ℝ) (θ K : ℝ) (N : ℕ) : Prop where
  smooth : ∀ i j, ContDiff ℝ ∞ (A i j)
  symm : ∀ i j x, A i j x = A j i x
  elliptic : ∀ x (ξ : ι → ℝ), θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, A i j x * ξ j * ξ i
  bound : ∀ i j, ∀ k ≤ N, ∀ x, ‖iteratedFDeriv ℝ k (A i j) x‖ ≤ K

/-- The weak equation `∫ Σ A_ij ∂_j w ∂_i φ = ∫ F φ + Σ ∫ G_i ∂_i φ` for test functions. -/
def WeakEq (A : ι → ι → E → ℝ) (w F : E → ℝ) (G : ι → E → ℝ) : Prop :=
  ∀ φ, IsTest Set.univ φ →
    ∑ i, ∑ j, ∫ x, A i j x * wd (b j) w x * pd (b i) φ x =
      (∫ x, F x * φ x) + ∑ i, ∫ x, G i x * pd (b i) φ x

/-- `n`-th mollification. -/
noncomputable def molN (n : ℕ) (f : E → ℝ) : E → ℝ :=
  mol (1 / ((n : ℝ) + 1)) (by positivity) f

theorem tendsto_integral_mul_of_L2 {a : E → ℝ} (ha : MemLp a 2 volume) {c : ℕ → E → ℝ} {c' : E → ℝ}
    (hc : ∀ n, MemLp (c n) 2 volume) (hc' : MemLp c' 2 volume)
    (hlim : Filter.Tendsto (fun n => ∫ x, (c n x - c' x) ^ 2) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ x, a x * c n x) Filter.atTop (nhds (∫ x, a x * c' x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 := (Real.continuous_sqrt.tendsto 0).comp hlim
  simp only [Real.sqrt_zero] at h0
  have h1 := h0.const_mul (l2 a)
  rw [mul_zero] at h1
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h1
  have i1 : Integrable (fun x => a x * c n x) volume := ha.integrable_mul (hc n)
  have i2 : Integrable (fun x => a x * c' x) volume := ha.integrable_mul hc'
  have e : (∫ x, a x * c n x) - ∫ x, a x * c' x = ∫ x, a x * (c n x - c' x) := by
    rw [← integral_sub i1 i2]
    congr 1; funext x; ring
  rw [Real.norm_eq_abs, e]
  show _ ≤ l2 a * Real.sqrt _
  exact abs_integral_mul_le_l2 ha ((hc n).sub hc')

theorem tendsto_molN_sq {f : E → ℝ} (hf : MemLp f 2 volume) :
    Filter.Tendsto (fun n => ∫ x, (molN n f x - f x) ^ 2) Filter.atTop (nhds 0) :=
  tendsto_integral_sq_mol_sub f hf

theorem molN_contDiff (n : ℕ) {f : E → ℝ} (hf : MemLp f 2 volume) :
    ContDiff ℝ ∞ (molN n f) :=
  mol_contDiff _ _ (hf.locallyIntegrable (by norm_num))

theorem molN_memLp (n : ℕ) {f : E → ℝ} (hf : MemLp f 2 volume) : MemLp (molN n f) 2 volume :=
  memLp_mol _ _ hf

theorem exists_norm_bound_of_compactSupport {f : E → ℝ} (hc : HasCompactSupport f) :
    ∃ R : ℝ, ∀ x, R < ‖x‖ → f x = 0 := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hc.isCompact.isBounded
  refine ⟨R, fun x hx => ?_⟩
  by_contra h
  exact absurd (hR x (subset_tsupport _ h)) (not_le.2 hx)

/-- Almost everywhere compact support. -/
def AESupp (f : E → ℝ) : Prop := ∃ R : ℝ, ∀ᵐ x ∂(volume : Measure E), R < ‖x‖ → f x = 0

theorem molN_isTest (n : ℕ) {f : E → ℝ} (hf : MemLp f 2 volume) (hc : AESupp f) :
    IsTest Set.univ (molN n f) := by
  obtain ⟨R, hR⟩ := hc
  have h1 : HasCompactSupport (molN n f) := mol_hasCompactSupport _ _ R hR
  exact ⟨molN_contDiff n hf, h1, Set.subset_univ _⟩

theorem Sob.one_wd {w : E → ℝ} (hw : Sob b 1 w) :
    MemLp w 2 volume ∧ ∀ j, HasWDeriv Set.univ (b j) w (wd (b j) w) ∧ MemLp (wd (b j) w) 2 volume := by
  rw [Sob.succ_iff b] at hw
  exact ⟨hw.1, fun j => ⟨(hw.2 j).1, (hw.2 j).2⟩⟩

theorem Ell.memLp_mul {A : ι → ι → E → ℝ} {θ K : ℝ} {N : ℕ} (hA : Ell A θ K N) (i j : ι)
    {f : E → ℝ} (hf : MemLp f 2 volume) : MemLp (fun x => A i j x * f x) 2 volume :=
  (integral_sq_mul_le (hA.smooth i j).continuous
    (fun x => by simpa using hA.bound i j 0 (Nat.zero_le _) x) hf).1

/-- The weak equation extends to compactly supported `H¹` test functions. -/
theorem WeakEq.extend {A : ι → ι → E → ℝ} {θ K : ℝ} {N : ℕ} (hA : Ell A θ K N)
    {w F : E → ℝ} {G : ι → E → ℝ} (hw : Sob b 1 w)
    (hF : MemLp F 2 volume) (hG : ∀ i, MemLp (G i) 2 volume) (heq : WeakEq b A w F G)
    {φ : E → ℝ} {φ' : ι → E → ℝ} (hφ : MemLp φ 2 volume) (hc : AESupp φ)
    (hφ' : ∀ i, HasWDeriv Set.univ (b i) φ (φ' i)) (hφ'm : ∀ i, MemLp (φ' i) 2 volume) :
    ∑ i, ∑ j, ∫ x, A i j x * wd (b j) w x * φ' i x =
      (∫ x, F x * φ x) + ∑ i, ∫ x, G i x * φ' i x := by
  obtain ⟨-, hwd⟩ := Sob.one_wd b hw
  have ha : ∀ i j, MemLp (fun x => A i j x * wd (b j) w x) 2 volume :=
    fun i j => hA.memLp_mul i j (hwd j).2
  have hp : ∀ n i, pd (b i) (molN n φ) = molN n (φ' i) := fun n i => by
    funext x; exact fderiv_mol _ _ (hφ' i) x
  have hlimL : Filter.Tendsto (fun n => ∑ i, ∑ j, ∫ x, A i j x * wd (b j) w x * molN n (φ' i) x)
      Filter.atTop (nhds (∑ i, ∑ j, ∫ x, A i j x * wd (b j) w x * φ' i x)) :=
    tendsto_finset_sum _ (fun i _ => tendsto_finset_sum _ (fun j _ =>
      tendsto_integral_mul_of_L2 (ha i j) (fun n => molN_memLp n (hφ'm i)) (hφ'm i)
        (tendsto_molN_sq (hφ'm i))))
  have hlimR1 : Filter.Tendsto (fun n => ∫ x, F x * molN n φ x) Filter.atTop
      (nhds (∫ x, F x * φ x)) :=
    tendsto_integral_mul_of_L2 hF (fun n => molN_memLp n hφ) hφ (tendsto_molN_sq hφ)
  have hlimR2 : Filter.Tendsto (fun n => ∑ i, ∫ x, G i x * molN n (φ' i) x) Filter.atTop
      (nhds (∑ i, ∫ x, G i x * φ' i x)) :=
    tendsto_finset_sum _ (fun i _ =>
      tendsto_integral_mul_of_L2 (hG i) (fun n => molN_memLp n (hφ'm i)) (hφ'm i)
        (tendsto_molN_sq (hφ'm i)))
  have heqn : ∀ n, (∑ i, ∑ j, ∫ x, A i j x * wd (b j) w x * molN n (φ' i) x) =
      (∫ x, F x * molN n φ x) + ∑ i, ∫ x, G i x * molN n (φ' i) x := by
    intro n
    have := heq _ (molN_isTest n hφ hc)
    simpa only [hp n] using this
  exact tendsto_nhds_unique hlimL (by
    have := hlimR1.add hlimR2
    refine this.congr (fun n => ?_)
    exact (heqn n).symm)

end CutoffRigidity.Riemann.Diff
