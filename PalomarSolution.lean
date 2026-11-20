module

public import CutoffRigidity

/-!
# Cutoff via rigidity for high dimensional curved diffusions: main results

Proofs of the Palomar statement surface (generated from `Solution.lean` by `scripts/gen-palomar.py`) for
D. Chafaï and M. Fathi, *On cutoff via rigidity for high dimensional curved diffusions*,
Comptes Rendus Mathématique 363 (2025) 1103–1121, in the corrected version arXiv:2412.15969v5
(25 October 2026). It states the numbered results of the paper (Theorems 1.1, 1.5, 1.7, 1.9, 3.1,
3.6, Lemma 3.3, Remark 1.2, Corollaries 1.3, 1.4, 1.6 and display (1.25)), the identification of the
transition kernel with the law of the solution of the SDE (1.1), and the existence of the diffusion and
of solutions of (1.1) for convex potentials, so that the standing hypotheses are not vacuous. Every
object is defined from Mathlib alone; deviations from v5 are flagged in the docstrings. The full set of
68 statements (remarks, examples, Section 4) is `Challenge.lean`, checked with `comparator.json`. -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff Manifold

@[expose] public noncomputable section

namespace CutCur

/-- Non-vacuity of the standing hypothesis `IsLangevin`: for a `C²` potential with nonnegative Hessian (that is, convex) and probability Gibbs measure there are a probability space, a Brownian motion and solutions of the Langevin SDE from every starting point. -/
theorem exists_langevin (d : ℕ) (V : Rd d → ℝ) (hV : ContDiff ℝ 2 V) (hHess : ∀ x z : Rd d, 0 ≤ fderiv ℝ (fderiv ℝ V) x z z)
  (hgibbs : IsProbabilityMeasure (gibbs V)) : ∃ (Ω : Type) (_ : MeasurableSpace Ω) (B : ℝ≥0 → Ω → Rd d) (P : Measure Ω) (X : Rd d → ℝ≥0 → Ω → Rd d),
  IsProbabilityMeasure P ∧ IsLangevin V B P X := by
  apply CutoffRigidity.Paper.exists_langevin <;> assumption

/-- **The kernel is the law of the SDE** (the kernel formulation is faithful): under `RigidCurvature V`, every solution `X` of (1.1) driven by a standard Brownian motion `B` (on any probability space) has `Law(Xₜ) = Pt t x₀` for the Euclidean Langevin semigroup `Pt`. -/
theorem isLangevinSolution_map_eq_kernel_of_rigid {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {V : Rd d → ℝ}
  {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)} (hL : IsEuclideanLangevin V Pt) (hR : RigidCurvature V) {B : ℝ≥0 → Ω → Rd d}
  {P : Measure Ω} (hB : IsStdBrownian B P) {x₀ : Rd d} {X : ℝ≥0 → Ω → Rd d} (hX : IsLangevinSolution V B P x₀ X) (t : ℝ≥0) : P.map (X t) = Pt t x₀ := by
  apply CutoffRigidity.Paper.isLangevinSolution_map_eq_kernel_of_rigid_C2 <;> assumption

/-- Non-vacuity of the standing hypothesis `IsEuclideanLangevin` of the kernel statements: for a `C²` potential with nonnegative Hessian (that is, convex) and probability Gibbs measure, the Euclidean Langevin semigroup exists. -/
theorem exists_euclideanLangevin_of_convex {d : ℕ} {V : Rd d → ℝ} (hV : ContDiff ℝ 2 V) (hHess : ∀ x z : Rd d, 0 ≤ fderiv ℝ (fderiv ℝ V) x z z)
  (hp : IsProbabilityMeasure (gibbs V)) : ∃ Pt : ℝ≥0 → Kernel (Rd d) (Rd d), IsEuclideanLangevin V Pt := by
  exact CutCur.C2U.exists_euclideanLangevin_C2 hV hHess hp

/-- **Theorem 1.1** (main Wasserstein estimate), including the ball refinement; Brownian-free kernel form: `Pt t x₀ = Law(X_t^{x₀})` (`IsEuclideanLangevin`). -/
theorem main_wasserstein_estimate {d : ℕ} {V : Rd d → ℝ} {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)} (hL : IsEuclideanLangevin V Pt) (hV : RigidCurvature V) (t : ℝ≥0) :
    let gap := spectralGap V
    let q := Real.exp (-2 * gap * t)
    let lower := fun Λ : ℝ≥0∞ => ENNReal.ofReal (q / gap) * Λ + ENNReal.ofReal (firstEigenDim V * (1 - Real.sqrt (1 - q)) ^ 2 / gap)
    let W := fun x₀ => wasserstein2 (Pt t x₀) (gibbs V) ^ 2
    (∀ S : Set (Rd d), S.Nonempty → lower (⨆ x₀ ∈ S, eigenLambda V x₀) ≤ ⨆ x₀ ∈ S, W x₀ ∧
      ⨆ x₀ ∈ S, W x₀ ≤ ENNReal.ofReal q * ⨆ x₀ ∈ S, ∫⁻ x, edist x x₀ ^ 2 ∂gibbs V) ∧
    (∫ x, x ∂gibbs V = 0 → ∀ R : ℝ, 0 ≤ R → lower (ENNReal.ofReal (gap * R ^ 2)) ≤ ⨆ x₀ ∈ Metric.closedBall 0 R, W x₀) := by
  apply CutoffRigidity.Paper.main_wasserstein_estimate_C2 <;> assumption

/-- **Remark 1.2**: `1 ≤ k₁ ≤ d`, and `Λ(x₀) = ∑ᵢ |fᵢ(x₀)|²` for every orthonormal basis of `E₁` (the supremum defining `Λ` is attained by every basis). -/
theorem eigenspace_dim_and_lambda {d : ℕ} {V : Rd d → ℝ} (hV2 : ContDiff ℝ 2 V)
  (hp : IsProbabilityMeasure (gibbs V)) (hV : RigidCurvature V) : 1 ≤ firstEigenDim V ∧ firstEigenDim V ≤ d ∧
  ∀ f, IsEigenbasis V f → ∀ x₀, eigenLambda V x₀ = ENNReal.ofReal (∑ i, f i x₀ ^ 2) := by
  apply CutoffRigidity.Paper.eigenspace_dim_and_lambda <;> assumption

/-- **Corollary 1.3** (Wasserstein cutoff on balls `B(m, c√d)`), for `ε ∈ (0,1)`; Brownian-free kernel form. -/
theorem wasserstein_cutoff {V : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
  (h : IsRigidSequenceK V Pt) {c : ℝ} (hc : 0 < c) : HasCutoff (fun n => worstK (Pt n) (meanBall (V n) c)
  (wasserstein2 · (gibbs (V n)))) (fun n => criticalTime n (spectralGap (V n))) ⊤ 0 := by
  apply CutoffRigidity.Paper.wasserstein_cutoff_C2 <;> assumption

/-- **Corollary 1.4** (Fisher information, relative entropy and total variation cutoffs on balls `B(m, c√d)`), under `λ₁⁽ⁿ⁾ = o(log n)`; Brownian-free kernel form. -/
theorem information_cutoff {V : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)} (h : IsRigidSequenceK V Pt)
  (hsmall : (fun n => spectralGap (V n)) =o[atTop] (fun n : ℕ => Real.log n)) {c : ℝ} (hc : 0 < c) :
    let t := fun n => criticalTime n (spectralGap (V n))
    let S := fun n => meanBall (V n) c
    HasCutoff (fun n => worstK (Pt n) (S n) (fisherInfo (V n))) t ⊤ 0 ∧
    HasCutoff (fun n => worstK (Pt n) (S n) (InformationTheory.klDiv · (gibbs (V n)))) t ⊤ 0 ∧
    HasCutoff (fun n => worstK (Pt n) (S n) (fun ν => .ofReal (tvDist ν (gibbs (V n))))) t 1 0 := by
  apply CutoffRigidity.Paper.information_cutoff_C2 <;> assumption

/-- **Display (1.25)** (`Lᵖ` cutoff) under the assumptions of Corollary 1.4, for every finite `p ≥ 1`: the limit before the critical time is `2` for `p = 1` and `+∞` for `p > 1` (`p = ∞` fails, already for Ornstein–Uhlenbeck). Brownian-free kernel form. -/
theorem lp_cutoff {V : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)} (h : IsRigidSequenceK V Pt)
  (hsmall : (fun n => spectralGap (V n)) =o[atTop] (fun n : ℕ => Real.log n)) {c : ℝ} (hc : 0 < c) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) :
  HasCutoff (fun n => worstK (Pt n) (meanBall (V n) c) (relLp · (gibbs (V n)) p)) (fun n => criticalTime n (spectralGap (V n))) (if p = 1 then 2 else ⊤) 0 := by
  apply CutoffRigidity.Paper.lp_cutoff_C2 <;> assumption

/-- **Theorem 1.5** (convex interaction): for `V(x) = ρ|x|²/2 + W(x)` with `W` convex `C²` and invariant under translations along `(1,…,1)`, (i) `λ₁ = ρ` and `x₁+⋯+x_d ∈ E₁`, (ii) `V` is `ρ`-convex and `μ` has the Gaussian factor `𝒩(0, 1/ρ)` along `u = (1,…,1)/√d`, (iii) the curvature condition (1.4) holds. -/
theorem convex_interaction {d : ℕ} (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ) {W : Rd d → ℝ}
  (hW : ContDiff ℝ 2 W) (hconv : ConvexOn ℝ univ W) (hinv : ∀ x (s : ℝ), W (x + s • diagonal d) = W x)
  (hp : IsProbabilityMeasure (gibbs fun x => ρ / 2 * ‖x‖ ^ 2 + W x)) :
    let V := fun x : Rd d => ρ / 2 * ‖x‖ ^ 2 + W x
    let u := (Real.sqrt d)⁻¹ • diagonal d
    let π := fun x : Rd d => x - inner ℝ u x • u
    (spectralGap V = ρ ∧ IsEigenfunction V ρ (fun x => ∑ i, x i)) ∧
    ((∀ x z : Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) ∧ (gibbs V).map (fun x => (inner ℝ u x, π x)) =
      (gaussianReal 0 ρ⁻¹.toNNReal).prod ((gibbs V).map π)) ∧
    RigidCurvature V := by
  apply CutoffRigidity.Paper.convex_interaction <;> assumption

/-- **Corollary 1.6** (cutoff for convex interactions, fixed `ρ > 0`): Wasserstein, Fisher, entropy and total variation cutoffs at `t* = log d / (2ρ)`, from balls `m + B(0, c√d)` and cubes `m + [-c,c]^d`; Brownian-free kernel form. -/
theorem convex_interaction_cutoff {ρ : ℝ} (hρ : 0 < ρ) {W : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)}
  (hW : ∀ n, 0 < n → ContDiff ℝ 2 (W n) ∧ ConvexOn ℝ univ (W n) ∧ ∀ x (s : ℝ), W n (x + s • diagonal n) = W n x)
  (hL : ∀ n, 0 < n → IsEuclideanLangevin (fun x => ρ / 2 * ‖x‖ ^ 2 + W n x) (Pt n)) {c : ℝ} (hc : 0 < c) :
    let V := fun n (x : Rd n) => ρ / 2 * ‖x‖ ^ 2 + W n x
    let t := fun n : ℕ => criticalTime n ρ
    ∀ cube : Bool,
      let S := fun n => if cube then meanCube (V n) c else meanBall (V n) c
      HasCutoff (fun n => worstK (Pt n) (S n) (wasserstein2 · (gibbs (V n)))) t ⊤ 0 ∧
      HasCutoff (fun n => worstK (Pt n) (S n) (fisherInfo (V n))) t ⊤ 0 ∧
      HasCutoff (fun n => worstK (Pt n) (S n) (InformationTheory.klDiv · (gibbs (V n)))) t ⊤ 0 ∧
      HasCutoff (fun n => worstK (Pt n) (S n) (fun ν => .ofReal (tvDist ν (gibbs (V n))))) t 1 0 := by
  apply CutoffRigidity.Paper.convex_interaction_cutoff_C2 <;> assumption

/-- **Theorem 1.7** (curvature product condition), as stated in arXiv v5: TV and entropy cutoff at the mixing time `t₀⁽ⁿ⁾` under `κ⁽ⁿ⁾t₀⁽ⁿ⁾ → ∞` and eventual finiteness of `t₀⁽ⁿ⁾`; Fisher and Wasserstein cutoffs under the additional assumptions `liminf κ⁽ⁿ⁾ > 0` and `t₀⁽ⁿ⁾ → ∞` (added in v5; the v4 and published statements are false without them, see `PAPER_AUDIT.md`). Brownian-free kernel form. -/
theorem product_condition_cutoff {V : ∀ n, Rd n → ℝ} {Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)} {κ : ℕ → ℝ} {S : ∀ n, Set (Rd n)} {η : ℝ}
  (hL : ∀ n, 0 < n → IsEuclideanLangevin (V n) (Pt n) ∧ 0 < κ n ∧ ∀ x z : Rd n, κ n * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (V n)) x z z)
  (hS : ∀ n, 0 < n → (S n).Nonempty) (hη : 0 < η) (hη1 : η < 1) :
    let t₀ := fun n => mixingTimeK (Pt n) (gibbs (V n)) (S n) η
    let prof := fun (δ : ∀ n, Measure (Rd n) → ℝ≥0∞) n => worstK (Pt n) (S n) (δ n)
    (∀ᶠ n in atTop, t₀ n < ⊤) → Tendsto (fun n => κ n * (t₀ n).toReal) atTop atTop → (HasCutoff (prof fun n ν => .ofReal (tvDist ν (gibbs (V n))))
      (fun n => (t₀ n).toReal) 1 0 ∧ HasCutoff (prof fun n ν => InformationTheory.klDiv ν (gibbs (V n))) (fun n => (t₀ n).toReal) ⊤ 0) ∧
      (0 < liminf (fun n => ENNReal.ofReal (κ n)) atTop → Tendsto (fun n => (t₀ n).toReal) atTop atTop →
      HasCutoff (prof fun n => fisherInfo (V n)) (fun n => (t₀ n).toReal) ⊤ 0 ∧
      HasCutoff (prof fun n ν => wasserstein2 ν (gibbs (V n))) (fun n => (t₀ n).toReal) ⊤ 0) := by
  apply CutoffRigidity.Paper.product_condition_cutoff_C2 <;> assumption

/-- **Theorem 3.1** (Gaussian factorization) and **Remark 3.2**: if `V` is `ρ`-convex and `λ₁ = ρ`, there are an orthonormal basis `e` and `m ∈ ℝ^d` with `V(x) = (ρ/2) ∑_{i<k₁} (⟨eᵢ,x⟩ - mᵢ)² + U(x)`, `U` depending only on the coordinates `⟨eᵢ,x⟩`, `i ≥ k₁`, and `ρ`-convex in those coordinates; every `f ∈ E₁` is affine, `f(x) = ∑_{i<k₁} aᵢ(⟨eᵢ,x⟩ - mᵢ)`, with `|a|² = λ₁ ‖f‖²_{L²(μ)}`. -/
theorem euclidean_gaussian_factorization {d : ℕ} {V : Rd d → ℝ} (hV2 : ContDiff ℝ 2 V) (hp : IsProbabilityMeasure (gibbs V)) {ρ : ℝ} (hρ : 0 < ρ)
  (hconv : ∀ x z : Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (hgap : spectralGap V = ρ) :
  ∃ (e : OrthonormalBasis (Fin d) ℝ (Rd d)) (m : Fin d → ℝ) (U : Rd d → ℝ),
  (∀ x, V x = ρ / 2 * ∑ i with i.val < firstEigenDim V, (inner ℝ (e i) x - m i) ^ 2 + U x) ∧
  (∀ x y, (∀ i, firstEigenDim V ≤ i.val → inner ℝ (e i) x = inner ℝ (e i) y) → U x = U y) ∧
  (∀ x z, (∀ i, i.val < firstEigenDim V → inner ℝ (e i) z = 0) → ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ U) x z z) ∧
  ∀ f, IsEigenfunction V ρ f → ∃ a : Fin d → ℝ, (∀ i, firstEigenDim V ≤ i.val → a i = 0) ∧
  (∀ x, f x = ∑ i, a i * (inner ℝ (e i) x - m i)) ∧ ∑ i, a i ^ 2 = ρ * ∫ x, f x ^ 2 ∂gibbs V := by
  apply CutoffRigidity.Paper.euclidean_gaussian_factorization <;> assumption

/-- **Lemma 3.3** (projection on an orthonormal multi-eigenfunction is an OU process), law form without Brownian motion: for an orthonormal basis `T = (f₁,…,f_{k₁})` of `E₁` under `λ₁ = ρ` and `ρ`-convexity, the law of `T(Xₜ)` from `x₀` (the pushforward of `Pt t x₀` by `T`) is the Ornstein–Uhlenbeck marginal `𝒩(e^{-ρt} T(x₀), (1 - e^{-2ρt}) I_{k₁})`, the time-`t` law of `dYₜ = -ρYₜ dt + √(2ρ) dβₜ`, `Y₀ = T x₀` (generator `ρΔ - ρ y·∇`); in particular it depends on `x₀` only through `T x₀`. Divergence: the pathwise statement with a Brownian `β` is replaced by this law form. -/
theorem eigenmap_is_ou {d : ℕ} {V : Rd d → ℝ} {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)} (hL : IsEuclideanLangevin V Pt) (hV : RigidCurvature V)
  (T : Fin (firstEigenDim V) → Rd d → ℝ) (hT : IsEigenbasis V T) :
    let ρ := spectralGap V
    let Tv := fun x => (WithLp.toLp 2 fun i => T i x : Rd (firstEigenDim V))
    ∀ (x₀ : Rd d) (t : ℝ≥0), (Pt t x₀).map Tv = multivariateGaussian (Real.exp (-ρ * (t : ℝ)) • Tv x₀) ((1 - Real.exp (-2 * ρ * (t : ℝ))) •
      (1 : Matrix (Fin (firstEigenDim V)) (Fin (firstEigenDim V)) ℝ)) := by
  apply CutoffRigidity.Paper.eigenmap_is_ou_C2 <;> assumption

section Riemannian

open Bundle

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

variable [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M]

/-- **Theorem 1.9** (Wasserstein estimate on a smooth, connected, complete weighted Riemannian manifold without boundary), including the ball refinement. -/
theorem riemannian_wasserstein_estimate {V : M → ℝ} (hV : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ V)
  {μ : Measure M} [IsProbabilityMeasure μ] (hμ : IsWeightedVolume F μ V) {ρ : ℝ} (hρ : 0 < ρ)
  (hCD : CD F ρ V) (hgap : mSpectralGap F μ = ρ) {Pt : ℝ≥0 → Kernel M M} (hP : IsDiffusionSemigroup F V Pt) (t : ℝ≥0) :
    let q := Real.exp (-2 * ρ * t)
    let lower := fun Λ : ℝ≥0∞ => ENNReal.ofReal (q / ρ) * Λ + ENNReal.ofReal (mFirstEigenDim F μ V * (1 - Real.sqrt (1 - q)) ^ 2 / ρ)
    let W := fun x₀ => wasserstein2 (Pt t x₀) μ ^ 2
    (∀ S : Set M, S.Nonempty → lower (⨆ x₀ ∈ S, mLambda F μ V x₀) ≤ ⨆ x₀ ∈ S, W x₀ ∧ ⨆ x₀ ∈ S, W x₀ ≤ ENNReal.ofReal q * ⨆ x₀ ∈ S, ∫⁻ x, edist x₀ x ^ 2 ∂μ) ∧
    ∀ (m : M) (R : ℝ), 0 ≤ R → mLambda F μ V m = 0 → lower (ENNReal.ofReal (ρ * R ^ 2)) ≤ ⨆ x₀ ∈ {x | edist m x ≤ ENNReal.ofReal R}, W x₀ := by
  apply CutoffRigidity.Paper.riemannian_wasserstein_estimate <;> assumption

/-- **Theorem 3.6** (Riemannian splitting with Gaussian factor) and **Lemma 3.7** (rigidity of first eigenfunctions): `(M, g, μ)` is isometric to `(ℝ^{k₁} × M', |·|² ⊕ g', γ_{k₁,ρ⁻¹} ⊗ μ')` with `(M', g', μ')` a connected complete weighted Riemannian manifold satisfying `CD(ρ,∞)`; the potential splits as `V∘Φ⁻¹(p,y) = ρ|p|²/2 + V'(y) + (k₁/2) log(2π/ρ)`; through this isometry every `f ∈ E₁` is `f = ⟨a, p⟩`, `p` the projection on the Euclidean factor, with `|a|² = ρ ‖f‖²_{L²(μ)}`, and orthogonal eigenfunctions have orthogonal vectors `a`. -/
theorem riemannian_gaussian_splitting {V : M → ℝ} (hV : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ V)
  {μ : Measure M} [IsProbabilityMeasure μ] (hμ : IsWeightedVolume F μ V) {ρ : ℝ} (hρ : 0 < ρ) (hCD : CD F ρ V) (hgap : mSpectralGap F μ = ρ) :
    let k := mFirstEigenDim F μ V
    ∃ (F' : Type) (_ : NormedAddCommGroup F') (_ : InnerProductSpace ℝ F') (_ : FiniteDimensional ℝ F') (N : Type) (_ : EMetricSpace N) (_ : ChartedSpace F' N)
      (_ : IsManifold 𝓘(ℝ, F') ∞ N) (_ : RiemannianBundle (fun y : N => TangentSpace 𝓘(ℝ, F') y))
      (_ : IsContMDiffRiemannianBundle 𝓘(ℝ, F') ∞ F' (fun y : N => TangentSpace 𝓘(ℝ, F') y))
      (_ : IsRiemannianManifold 𝓘(ℝ, F') N) (_ : MeasurableSpace F') (_ : BorelSpace F') (_ : MeasurableSpace N) (_ : BorelSpace N)
      (V' : N → ℝ) (μ' : Measure N) (Φ : M ≃ₘ^∞⟮𝓘(ℝ, F), 𝓘(ℝ, Rd k).prod 𝓘(ℝ, F')⟯ Rd k × N), (ContMDiff 𝓘(ℝ, F') 𝓘(ℝ, ℝ) ∞ V' ∧ IsProbabilityMeasure μ' ∧
      IsWeightedVolume F' μ' V' ∧ CD F' ρ V' ∧ ConnectedSpace N ∧ CompleteSpace N) ∧
      (∀ x y, edist x y ^ 2 = edist (Φ x).1 (Φ y).1 ^ 2 + edist (Φ x).2 (Φ y).2 ^ 2) ∧
      (∀ x, V x = ρ * ‖(Φ x).1‖ ^ 2 / 2 + V' (Φ x).2 + k / 2 * Real.log (2 * Real.pi / ρ)) ∧
      μ.map Φ = (multivariateGaussian 0 (ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ))).prod μ' ∧ (∀ f, IsMEigenfunction F μ V ρ f → ∃ a : Rd k,
      (∀ x, f x = inner ℝ a (Φ x).1) ∧ ‖a‖ ^ 2 = ρ * ∫ x, f x ^ 2 ∂μ) ∧ ∀ f g (a b : Rd k), IsMEigenfunction F μ V ρ f → IsMEigenfunction F μ V ρ g →
      (∀ x, f x = inner ℝ a (Φ x).1) → (∀ x, g x = inner ℝ b (Φ x).1) → ∫ x, f x * g x ∂μ = 0 → inner ℝ a b = 0 := by
  apply CutoffRigidity.Paper.riemannian_gaussian_splitting <;> assumption

end Riemannian

end CutCur
