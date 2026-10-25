module

public import CutoffRigidity.Statements

/-! # Orthonormal linear images of a standard Brownian motion

Independent real Brownian coordinates form a jointly Gaussian process. A matrix
with orthonormal rows therefore maps a standard Brownian motion on `ℝ^d` to a
standard Brownian motion on `ℝ^k`: each image coordinate is a centered Gaussian
process with covariance `min s t`, and distinct coordinates are uncorrelated.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

@[expose] public section

namespace CutoffRigidity

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- The coordinates of a standard Brownian motion form one jointly Gaussian process. -/
theorem isGaussianProcess_stdBrownian_coord {B : ℝ≥0 → Ω → CutCur.Rd d}
    (hB : CutCur.IsStdBrownian B P) :
    IsGaussianProcess (fun (p : Fin d × ℝ≥0) ω => B p.2 ω p.1) P where
  hasGaussianLaw I := by
    classical
    let J : Finset ℝ≥0 := I.image Prod.snd
    let Z : Fin d → Ω → (J → ℝ) := fun i ω => J.restrict (fun t => B t ω i)
    have hZ : ∀ i, HasGaussianLaw (Z i) P := fun i =>
      ((hB.1 i).toIsPreBrownianReal.isGaussianProcess).hasGaussianLaw J
    have hind : iIndepFun Z P :=
      hB.2.comp (fun _ (x : ℝ≥0 → ℝ) => J.restrict x) (fun _ => by fun_prop)
    have hJ := hind.hasGaussianLaw hZ
    let L : (Fin d → J → ℝ) →L[ℝ] (I → ℝ) :=
      { toFun x p := x p.1.1 ⟨p.1.2, mem_image_of_mem _ p.2⟩
        map_add' x y := by ext; simp
        map_smul' c x := by ext; simp
        cont := by fun_prop }
    have heq : (fun ω => I.restrict (fun p : Fin d × ℝ≥0 => B p.2 ω p.1)) =
        L ∘ fun ω => (Z · ω) := by
      ext ω p
      simp [L, Z, Finset.restrict_def]
    rw [heq]
    exact hJ.map L

/-- An orthonormal-row linear image of a standard Brownian motion is a standard
Brownian motion. -/
theorem isStdBrownian_orthonormal_image {k : ℕ} {B : ℝ≥0 → Ω → CutCur.Rd d}
    (hB : CutCur.IsStdBrownian B P) (a : Fin k → Fin d → ℝ)
    (ha : ∀ j l, ∑ i, a j i * a l i = if j = l then 1 else 0) :
    CutCur.IsStdBrownian
      (fun t ω => (WithLp.toLp 2 fun j => ∑ i, a j i * B t ω i : CutCur.Rd k)) P := by
  classical
  have hG := isGaussianProcess_stdBrownian_coord hB
  have := hG.isProbabilityMeasure
  -- the joint image process indexed by `(j, t)`
  have hY : IsGaussianProcess (fun (p : (_ : Fin k) × ℝ≥0) ω => ∑ i, a p.1 i * B p.2 ω i) P :=
    hG.of_isGaussianProcess fun p => ⟨univ ×ˢ {p.2},
      { toFun x := ∑ i, a p.1 i * x ⟨(i, p.2), by simp⟩
        map_add' x y := by simp [mul_add, sum_add_distrib]
        map_smul' c x := by simp [mul_left_comm, mul_sum]
        cont := by fun_prop }, fun ω => by simp [Finset.restrict_def]⟩
  have hBi (i : Fin d) := (hB.1 i).toIsPreBrownianReal
  have hmem (i : Fin d) (t : ℝ≥0) : MemLp (fun ω => B t ω i) 2 P :=
    (hBi i).isGaussianProcess.hasGaussianLaw_eval t |>.memLp_two
  -- covariance of coordinates of `B`
  have hcovB (i i' : Fin d) (s t : ℝ≥0) :
      cov[fun ω => B s ω i, fun ω => B t ω i'; P] = if i = i' then (min s t : ℝ) else 0 := by
    split_ifs with h
    · subst h; exact (hBi i).covariance_eval s t
    · have hind : IndepFun (fun ω => B s ω i) (fun ω => B t ω i') P :=
        (hB.2.indepFun h).comp (φ := fun x : ℝ≥0 → ℝ => x s) (ψ := fun x : ℝ≥0 → ℝ => x t)
          (by fun_prop) (by fun_prop)
      exact hind.covariance_eq_zero (hmem i s) (hmem i' t)
  have hcov (j l : Fin k) (s t : ℝ≥0) :
      cov[fun ω => ∑ i, a j i * B s ω i, fun ω => ∑ i, a l i * B t ω i; P] =
        (if j = l then 1 else 0) * (min s t : ℝ) := by
    rw [covariance_fun_sum_fun_sum (fun i => (hmem i s).const_mul _)
      (fun i => (hmem i t).const_mul _)]
    simp only [covariance_const_mul_left, covariance_const_mul_right, hcovB, ← ha, sum_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_eq_single i (fun i' _ hi' => by simp [Ne.symm hi']) (by simp)]
    simp; ring
  refine ⟨fun j => ?_, ?_⟩
  · have hYj : IsGaussianProcess (fun t ω => ∑ i, a j i * B t ω i) P :=
      hY.comp_right (fun t => (⟨j, t⟩ : (_ : Fin k) × ℝ≥0))
    have hpre : IsPreBrownianReal (fun t ω => ∑ i, a j i * B t ω i) P := by
      refine hYj.isPreBrownianReal_of_covariance (fun t => ?_) (fun s t hst => ?_)
      · rw [integral_finsetSum _ (fun i _ => ((hBi i).integrable_eval t).const_mul _)]
        simp [integral_const_mul, (hBi _).integral_eval]
      · rw [hcov]; simp only [ite_true, one_mul]; exact min_eq_left (by exact_mod_cast hst)
    refine ⟨hpre, ?_⟩
    have hc : ∀ᵐ ω ∂P, ∀ i, Continuous (fun t => B t ω i) :=
      ae_all_iff.mpr fun i => (hB.1 i).cont
    filter_upwards [hc] with ω hω
    exact continuous_finsetSum _ fun i _ => continuous_const.mul (hω i)
  · have hind := hY.iIndepFun_of_covariance_eq_zero
      (X := fun (j : Fin k) (t : ℝ≥0) ω => ∑ i, a j i * B t ω i)
      (fun j t => Finset.aemeasurable_fun_sum _ fun i _ =>
        ((hBi i).aemeasurable t).const_mul _)
      (fun j l hjl s t => by rw [hcov]; simp [hjl])
    simpa using hind

end CutoffRigidity
