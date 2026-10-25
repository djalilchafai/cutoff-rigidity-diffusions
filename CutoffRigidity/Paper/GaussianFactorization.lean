module

public import CutoffRigidity.Paper.SpectralBridge
public import CutoffRigidity.Paper.SeqData
public import CutoffRigidity.EuclideanGaussianSplitting
public import CutoffRigidity.BarycenterWasserstein
public import CutoffRigidity.EigenfunctionC2Rigidity
public import CutoffRigidity.AffineEigenfunctionOrthogonality

/-! # Theorem 3.1 and Remark 3.2 (Gaussian factorization) on the statement surface -/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The second derivative of a `C²` function along a line is the Hessian quadratic form. -/
theorem deriv_deriv_line {g : E → ℝ} (hg : ContDiff ℝ 2 g) (x z : E) :
    deriv (deriv (fun t : ℝ => g (x + t • z))) 0 = fderiv ℝ (fderiv ℝ g) x z z := by
  have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x + t • z) z t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const z).const_add x
  have h1 : ∀ t : ℝ, deriv (fun t : ℝ => g (x + t • z)) t = fderiv ℝ g (x + t • z) z := fun t => by
    have := (hg.differentiable (by norm_num) (x + t • z)).hasFDerivAt.comp_hasDerivAt t (hline t)
    exact this.deriv
  have h2 : deriv (fun t : ℝ => g (x + t • z)) = fun t => fderiv ℝ g (x + t • z) z := funext h1
  rw [h2]
  have hdg : Differentiable ℝ (fderiv ℝ g) :=
    hg.fderiv_right (m := 1) (by norm_num) |>.differentiable (by norm_num)
  have h3 := (hdg (x + (0 : ℝ) • z)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hline 0)
  have h4 := h3.clm_apply (hasDerivAt_const (0 : ℝ) z)
  simpa using h4.deriv

/-- Sum over the first `k` coordinates, reindexed. -/
theorem sum_filter_lt_eq_sum_castLE {k : ℕ} (hk : k ≤ d) (f : Fin d → ℝ) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < k), f i =
      ∑ j : Fin k, f (Fin.castLE hk j) := by
  refine Finset.sum_bij' (fun i hi => (⟨i.val, (Finset.mem_filter.mp hi).2⟩ : Fin k))
    (fun j _ => Fin.castLE hk j) (fun _ _ => Finset.mem_univ _)
    (fun j _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.2⟩) (fun i _ => Fin.ext rfl)
    (fun j _ => Fin.ext rfl) (fun i _ => congrArg f (Fin.ext rfl))
/-- **Theorem 3.1** (Gaussian factorization) and **Remark 3.2**. -/
theorem euclidean_gaussian_factorization {V : CutCur.Rd d → ℝ} (hV2 : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (CutCur.gibbs V)) {ρ : ℝ} (hρ : 0 < ρ)
    (hconv : ∀ x z : CutCur.Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (hgap : CutCur.spectralGap V = ρ) :
    ∃ (e : OrthonormalBasis (Fin d) ℝ (CutCur.Rd d)) (m : Fin d → ℝ) (U : CutCur.Rd d → ℝ),
      (∀ x, V x = ρ / 2 * ∑ i with i.val < CutCur.firstEigenDim V,
        (inner ℝ (e i) x - m i) ^ 2 + U x) ∧
      (∀ x y, (∀ i, CutCur.firstEigenDim V ≤ i.val → inner ℝ (e i) x = inner ℝ (e i) y) →
        U x = U y) ∧
      (∀ x z, (∀ i, i.val < CutCur.firstEigenDim V → inner ℝ (e i) z = 0) →
        ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ U) x z z) ∧
      ∀ f, CutCur.IsEigenfunction V ρ f → ∃ a : Fin d → ℝ,
        (∀ i, CutCur.firstEigenDim V ≤ i.val → a i = 0) ∧
        (∀ x, f x = ∑ i, a i * (inner ℝ (e i) x - m i)) ∧
        ∑ i, a i ^ 2 = ρ * ∫ x, f x ^ 2 ∂CutCur.gibbs V := by
  have hp' : IsProbabilityMeasure (gibbsMeasure volume V) := gibbs_probability hp
  have hrig : CutCur.RigidCurvature V := ⟨hgap ▸ hρ, fun x z => hgap ▸ hconv x z⟩
  have hG : gibbsSpectralGap hV2 hp' = ρ := by
    rw [← hgap]; exact (spectralGap_eq_gibbsSpectralGap hV2 hp' hrig).symm
  have hd : 0 < d := pos_dim_of_rigidCurvature hp hrig
  have hsplit := euclidean_gaussian_splitting hV2 hp' hd ρ hρ hconv hG
  have hk : CutCur.firstEigenDim V = Module.finrank ℝ (affineEigenRows V ρ) :=
    (firstEigenDim_eq hV2 hp' hrig).trans hsplit.dimension.symm
  obtain ⟨e, he_rows, hVsplit⟩ := hsplit.orthonormal_coordinates
  have hkd : Module.finrank ℝ (affineEigenRows V ρ) ≤ d := affineEigenRows_finrank_le V ρ
  rw [hk]
  set k := Module.finrank ℝ (affineEigenRows V ρ) with hkdef
  set c := affineSplittingCenter V with hc
  have hrowsmem : ∀ j : Fin k, e (Fin.castLE hkd j) ∈ affineEigenRows V ρ := fun j => by
    rw [he_rows j]
    exact (affineEigenRowsBasis V ρ j).2
  have hlow : ∀ i : Fin d, i.val < k → e i ∈ affineEigenRows V ρ := fun i hi => by
    have := hrowsmem ⟨i.val, hi⟩
    exact this
  have hrows_of : ∀ w : E, (∀ i : Fin d, k ≤ i.val → inner ℝ (e i) w = 0) →
      w ∈ affineEigenRows V ρ := by
    intro w hw
    rw [← e.sum_repr' w]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : i.val < k
    · exact Submodule.smul_mem _ _ (hlow i hi)
    · rw [hw i (not_lt.mp hi), zero_smul]
      exact Submodule.zero_mem _
  have hU : ∀ x, V x - ρ / 2 * ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < k),
      (inner ℝ (e i) x - inner ℝ (e i) c) ^ 2 =
      affineComplementPotential V ρ ((affineEigenRows V ρ)ᗮ.orthogonalProjectionOnto (x - c)) := by
    intro x
    have h1 := hVsplit x
    have h2 : ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < k),
        (inner ℝ (e i) x - inner ℝ (e i) c) ^ 2 =
        ∑ j : Fin k, (inner ℝ (e (Fin.castLE hkd j)) (x - c)) ^ 2 := by
      rw [sum_filter_lt_eq_sum_castLE hkd (fun i => (inner ℝ (e i) x - inner ℝ (e i) c) ^ 2)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [inner_sub_right]
    rw [h2]
    linarith
  refine ⟨e, fun i => inner ℝ (e i) c,
    fun x => V x - ρ / 2 * ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < k),
      (inner ℝ (e i) x - inner ℝ (e i) c) ^ 2, fun x => by ring, ?_, ?_, ?_⟩
  · intro x y hxy
    have hxy' : x - y ∈ affineEigenRows V ρ := by
      refine hrows_of _ fun i hi => ?_
      rw [inner_sub_right, hxy i hi, sub_self]
    have hP : (affineEigenRows V ρ)ᗮ.orthogonalProjectionOnto (x - c) =
        (affineEigenRows V ρ)ᗮ.orthogonalProjectionOnto (y - c) := by
      have h0 := Submodule.orthogonalProjectionOnto_orthogonal_apply_eq_zero hxy'
      rw [show x - y = (x - c) - (y - c) by abel, map_sub, sub_eq_zero] at h0
      exact h0
    show V x - _ = V y - _
    rw [hU x, hU y, hP]
  · intro x z hz
    set Q : E → ℝ := fun y => ρ / 2 * ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < k),
      (inner ℝ (e i) y - inner ℝ (e i) c) ^ 2 with hQ
    have hQs : ContDiff ℝ 2 Q := by
      have h : ∀ i ∈ Finset.univ.filter (fun i : Fin d => i.val < k),
          ContDiff ℝ 2 (fun y : E => (inner ℝ (e i) y - inner ℝ (e i) c) ^ 2) := fun i _ =>
        (((innerSL ℝ (e i)).contDiff).sub contDiff_const).pow 2
      exact contDiff_const.mul (ContDiff.sum (s := Finset.univ.filter (fun i : Fin d => i.val < k))
        (f := fun i (y : E) => (inner ℝ (e i) y - inner ℝ (e i) c) ^ 2) h)
    have hUs : ContDiff ℝ 2 (fun y => V y - Q y) := hV2.sub hQs
    have hQline : ∀ t : ℝ, Q (x + t • z) = Q x := fun t => by
      have hsum : ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < k),
          (inner ℝ (e i) (x + t • z) - inner ℝ (e i) c) ^ 2 =
          ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < k),
          (inner ℝ (e i) x - inner ℝ (e i) c) ^ 2 :=
        Finset.sum_congr rfl fun i hi => by
          have hi' := (Finset.mem_filter.mp hi).2
          rw [inner_add_right, inner_smul_right, hz i hi', mul_zero, add_zero]
      simp only [hQ]
      rw [hsum]
    have hline : (fun t : ℝ => V (x + t • z) - Q (x + t • z)) =
        fun t : ℝ => V (x + t • z) - Q x := funext fun t => by rw [hQline t]
    have h1 := deriv_deriv_line hUs x z
    rw [hline] at h1
    have h2 := deriv_deriv_line hV2 x z
    have h3 : deriv (deriv (fun t : ℝ => V (x + t • z) - Q x)) 0 =
        deriv (deriv (fun t : ℝ => V (x + t • z))) 0 := by
      congr 1
      funext t
      exact deriv_sub_const _
    show ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (fun y => V y - Q y)) x z z
    rw [← h1, h3, h2]
    exact hconv x z
  · intro f hf
    obtain ⟨hf2, hfLp, heig⟩ := isEigenfunction_iff.mp hf
    have haff := c2_L2_eigenfunction_is_affine hV2 hf2 hfLp ρ hρ.le hconv heig
    set a : E := gradient f 0 with ha
    set b : ℝ := f 0 with hb
    have hfeq : f = fun y => inner ℝ a y + b := funext fun y => by rw [haff y, add_comm]
    have heig' : ∀ x, langevinDifferentialOperator V (fun y => inner ℝ a y + b) x =
        -ρ * (inner ℝ a x + b) := fun x => by
      rw [← hfeq, heig x, hfeq]
    obtain ⟨harows, hbconst⟩ := (affineEigenRows_iff_eigenfunction V hρ a b).mp heig'
    have hbmean : b = -inner ℝ a c := by
      rw [hbconst]
      exact affineEigenConstant_eq_neg_inner_mean hV2 ρ hρ hconv hp' ⟨a, harows⟩
    have hhigh : ∀ i : Fin d, k ≤ i.val → inner ℝ (e i) a = 0 := by
      intro i hi
      have hrep := (affineEigenRowsBasis V ρ).sum_repr' (⟨a, harows⟩ : affineEigenRows V ρ)
      have := congrArg (fun w : affineEigenRows V ρ => inner ℝ (e i) (w : E)) hrep
      simp only [Submodule.coe_sum, Submodule.coe_smul, inner_sum, inner_smul_right] at this
      rw [← this]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hne : i ≠ Fin.castLE hkd j := fun h => by
        have := congrArg Fin.val h
        simp at this
        omega
      have h0 : inner ℝ (e i) ((affineEigenRowsBasis V ρ j : affineEigenRows V ρ) : E) = 0 := by
        have h00 : inner ℝ (e i) (e (Fin.castLE hkd j)) = 0 := by
          exact e.orthonormal.inner_eq_zero hne
        rw [he_rows j] at h00
        exact h00
      simp [h0]
    refine ⟨fun i => inner ℝ (e i) a, hhigh, fun x => ?_, ?_⟩
    · rw [hfeq]
      show inner ℝ a x + b = _
      have h1 : ∑ i, inner ℝ (e i) a * inner ℝ (e i) x = inner ℝ a x := by
        rw [← e.sum_inner_mul_inner a x]
        exact Finset.sum_congr rfl fun i _ => by rw [real_inner_comm]
      have h2 : ∑ i, inner ℝ (e i) a * inner ℝ (e i) c = inner ℝ a c := by
        rw [← e.sum_inner_mul_inner a c]
        exact Finset.sum_congr rfl fun i _ => by rw [real_inner_comm]
      rw [hbmean]
      simp only [mul_sub, Finset.sum_sub_distrib, h1, h2]
      ring
    · have hnorm : ∑ i, inner ℝ (e i) a ^ 2 = ‖a‖ ^ 2 := by
        have := e.sum_sq_norm_inner_right a
        simpa [Real.norm_eq_abs, sq_abs] using this
      have hsec := affine_eigenfunction_second_moment_all V (hV2.differentiable (by norm_num)) a b ρ hρ
        heig' hp'
      have hint : ∫ x, f x ^ 2 ∂CutCur.gibbs V = ‖a‖ ^ 2 / ρ := by
        rw [hfeq]; exact hsec
      rw [hnorm, hint]
      field_simp

end CutoffRigidity.Paper
