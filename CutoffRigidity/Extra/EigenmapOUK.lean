module

public import CutoffRigidity.Extra.EuclideanDiffusion
public import CutoffRigidity.Paper.EigenmapOU
public import CutoffRigidity.AffineProjectedDistances
public import CutoffRigidity.OUCutoffs

/-! # Lemma 3.3 without Brownian motion (law form)

For a smooth potential with a Euclidean Langevin semigroup `Pt`, rigid curvature and an orthonormal
eigenbasis `T` of the first eigenspace, the pushforward of `Pt t x₀` under the eigenmap
`Tv = (T₁,…,T_{k₁})` is the Ornstein–Uhlenbeck (Mehler) Gaussian
`𝒩(e^{-ρt} Tv x₀, (1 - e^{-2ρt}) I)`. In particular the law of `Tv(X_t)` depends on `x₀` only through
`Tv x₀` (lumping).
-/

public section

namespace CutoffRigidity.Paper

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff

/-- **Lemma 3.3, Brownian-free law form**: the projection `Tv` of `Pt t x₀` on an orthonormal basis
of the first eigenspace is the OU Gaussian `𝒩(e^{-ρt} Tv x₀, (1 - e^{-2ρt}) I)`, the time-`t` marginal
of the process with generator `ρΔ - ρ y·∇` started at `Tv x₀`. -/
theorem eigenmap_is_ou_K {d : ℕ} {V : CutCur.Rd d → ℝ}
    {Pt : ℝ≥0 → Kernel (CutCur.Rd d) (CutCur.Rd d)}
    (hL : CutCur.IsEuclideanLangevin V Pt) (hV : CutCur.RigidCurvature V)
    (T : Fin (CutCur.firstEigenDim V) → CutCur.Rd d → ℝ) (hT : CutCur.IsEigenbasis V T) :
    let ρ := CutCur.spectralGap V
    let Tv := fun x => (WithLp.toLp 2 fun i => T i x : CutCur.Rd (CutCur.firstEigenDim V))
    ∀ (x₀ : CutCur.Rd d) (t : ℝ≥0),
      (Pt t x₀).map Tv = multivariateGaussian (Real.exp (-ρ * (t : ℝ)) • Tv x₀)
        ((1 - Real.exp (-2 * ρ * (t : ℝ))) •
          (1 : Matrix (Fin (CutCur.firstEigenDim V)) (Fin (CutCur.firstEigenDim V)) ℝ)) := by
  intro ρ Tv x₀ t
  have hHess := hV.2
  have hρ : 0 < ρ := hV.1
  have hH0 : ∀ x z : CutCur.Rd d, (0 : ℝ) * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z :=
    fun x z => by simpa using hV.hess_nonneg x z
  obtain ⟨Ω, hΩ, B, P, X, hP, hLX, key⟩ := CutCur.exists_isLangevin_of_rigid hL hV
  have hV2 : ContDiff ℝ 2 V := hLX.1
  have hp' : IsProbabilityMeasure (gibbsMeasure volume V) := gibbs_probability hLX.2.1
  have hB' : IsEuclideanBrownian B P := isStdBrownian_iff.1 hLX.2.2.1
  have hPt : Pt t x₀ = langevinKernel V B P t x₀ := by
    rw [← key t x₀, langevinKernel_apply_eq_process_law hB' hV2 0 le_rfl hH0]
    exact Measure.map_congr (IsLangevinSolution.ae_eq_langevinProcess hB' hV2 0 le_rfl hH0
      (hLX.2.2.2 x₀) t)
  have hTe : ∀ i, ContDiff ℝ 2 (T i) ∧ MemLp (T i) 2 (gibbsMeasure volume V) ∧
      ∀ x, langevinDifferentialOperator V (T i) x = -ρ * T i x :=
    fun i => isEigenfunction_iff.mp (hT.1 i)
  set a : Fin (CutCur.firstEigenDim V) → CutCur.Rd d := fun i => gradient (T i) 0 with ha
  set b : Fin (CutCur.firstEigenDim V) → ℝ := fun i => T i 0 with hb
  have haff : ∀ i x, T i x = b i + inner ℝ (a i) x := fun i x =>
    c2_L2_eigenfunction_is_affine hV2 (hTe i).1 (hTe i).2.1 ρ hρ.le hHess (hTe i).2.2 x
  have hTeq : ∀ i, T i = fun y => inner ℝ (a i) y + b i := fun i =>
    funext fun y => by rw [haff i y, add_comm]
  have heig' : ∀ i x, langevinDifferentialOperator V (fun y => inner ℝ (a i) y + b i) x =
      -ρ * (inner ℝ (a i) x + b i) := fun i x => by
    rw [← hTeq i, (hTe i).2.2 x, hTeq i]
  have horth : ∀ i j, ∫ x, (inner ℝ (a i) x + b i) * (inner ℝ (a j) x + b j)
      ∂gibbsMeasure volume V = if i = j then 1 else 0 := fun i j => by
    have := hT.2 i j
    rw [hTeq i, hTeq j] at this
    exact this
  have h := langevinKernel_map_affineEigenfunctionMap hB' hV2 0 le_rfl hH0 a b ρ hρ heig' hp' horth
    x₀ t
  have hTv : Tv = affineEigenfunctionMap a b := by
    funext x
    show (WithLp.toLp 2 fun i => T i x : CutCur.Rd (CutCur.firstEigenDim V)) = _
    simp only [affineEigenfunctionMap, hTeq]
  rw [hPt, hTv, h, ouLaw_eq_multivariateGaussian hρ.le t.coe_nonneg]

-- Names of the Challenge theorems (kernel statements; the Brownian versions are `*_carrier`).
alias eigenmap_is_ou := eigenmap_is_ou_K

end CutoffRigidity.Paper
