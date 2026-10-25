module

public import Mathlib

/-!
# Cutoff via rigidity for high-dimensional curved diffusions: statements

Statement surface for D. Chafaï and M. Fathi, *On cutoff via rigidity for
high-dimensional curved diffusions* (local corrected manuscript
`cutcur-lean.tex`, based on arXiv:2412.15969v4). Every object is defined from
Mathlib alone. Each theorem below corresponds to a numbered result of the
paper; amendments to the printed statements are flagged in the docstrings.

Conventions. `ℝ^d` is `EuclideanSpace ℝ (Fin d)`. Suprema of nonnegative
discrepancies over sets of initial conditions are taken in `ℝ≥0∞`, so that
infinite values are meaningful. Laws of processes at a real time `t` use the
time `t.toNNReal`; all times appearing in the statements are nonnegative.

Remark on the definitions of the first eigenspace. `E₁`, `k₁`, `Λ` and `λ₁` are defined
classically: `λ₁` as the infimum of the Rayleigh quotient over smooth compactly supported
functions, and `E₁` through `C²` (Euclidean) or smooth (Riemannian) `L²` eigenfunctions. They agree
with the spectral objects of the paper through elliptic regularity and essential self-adjointness;
the Lean `E₁` is contained in the spectral one, so any discrepancy could only weaken a lower bound.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff Manifold

@[expose] public noncomputable section

namespace CutCur

/-! ## Euclidean objects -/

/-- The Euclidean space `ℝ^d`. -/
abbrev Rd (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The Boltzmann–Gibbs measure `μ(dx) = e^{-V(x)} dx` on `ℝ^d` (paper (1.2)). -/
def gibbs {d : ℕ} (V : Rd d → ℝ) : Measure (Rd d) :=
  volume.withDensity fun x => ENNReal.ofReal (Real.exp (-V x))

/-- The Laplacian `Δf(x) = ∑ᵢ ∂ᵢ²f(x)`. -/
def laplacian {d : ℕ} (f : Rd d → ℝ) (x : Rd d) : ℝ :=
  ∑ i, fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)

/-- The Langevin generator `𝓛f = Δf - ∇V·∇f` (paper (1.3)). -/
def generator {d : ℕ} (V f : Rd d → ℝ) (x : Rd d) : ℝ :=
  laplacian f x - inner ℝ (gradient V x) (gradient f x)

/-- The spectral gap `λ₁` of `-𝓛` in `L²(μ)`, as the optimal Poincaré constant:
the infimum of the Rayleigh quotients `∫|∇f|² dμ / Var_μ(f)` over smooth compactly
supported non-constant test functions (a core of the Dirichlet form). -/
def spectralGap {d : ℕ} (V : Rd d → ℝ) : ℝ :=
  sInf {r : ℝ | ∃ f : Rd d → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    0 < variance f (gibbs V) ∧ r = (∫ x, ‖gradient f x‖ ^ 2 ∂gibbs V) / variance f (gibbs V)}

/-- `f` is an eigenfunction of `-𝓛` with eigenvalue `lam` in `L²(μ)`, with its `C²`
representative (elliptic regularity, paper Remark 1.2). -/
def IsEigenfunction {d : ℕ} (V : Rd d → ℝ) (lam : ℝ) (f : Rd d → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ MemLp f 2 (gibbs V) ∧ ∀ x, generator V f x = -lam * f x

/-- The eigenspace `E₁ ⊆ L²(μ)` of `-𝓛` associated with `λ₁`. -/
def firstEigenspace {d : ℕ} (V : Rd d → ℝ) : Submodule ℝ (Rd d →₂[gibbs V] ℝ) :=
  Submodule.span ℝ {u | ∃ f, IsEigenfunction V (spectralGap V) f ∧ f =ᵐ[gibbs V] u}

/-- `k₁ = dim E₁`. -/
def firstEigenDim {d : ℕ} (V : Rd d → ℝ) : ℕ := Module.finrank ℝ (firstEigenspace V)

/-- `f = (f₁,…,f_{k₁})` is an orthonormal basis of `E₁` (given by continuous representatives). -/
def IsEigenbasis {d : ℕ} (V : Rd d → ℝ) (f : Fin (firstEigenDim V) → Rd d → ℝ) : Prop :=
  (∀ i, IsEigenfunction V (spectralGap V) (f i)) ∧
    ∀ i j, ∫ x, f i x * f j x ∂gibbs V = if i = j then 1 else 0

/-- `Λ(x₀) = sup ∑ᵢ |fᵢ(x₀)|²` over orthonormal bases `(f₁,…,f_{k₁})` of `E₁` (Theorem 1.1). -/
def eigenLambda {d : ℕ} (V : Rd d → ℝ) (x₀ : Rd d) : ℝ≥0∞ :=
  ⨆ (f : Fin (firstEigenDim V) → Rd d → ℝ) (_ : IsEigenbasis V f), ENNReal.ofReal (∑ i, f i x₀ ^ 2)

/-- The curvature condition (1.4) `Hess V ≥ λ₁ I_d` together with `λ₁ > 0`. -/
def RigidCurvature {d : ℕ} (V : Rd d → ℝ) : Prop :=
  0 < spectralGap V ∧ ∀ x z : Rd d, spectralGap V * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z

/-- `B` is a standard Brownian motion on `ℝ^d`: independent real Brownian coordinates. -/
def IsStdBrownian {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (B : ℝ≥0 → Ω → Rd d)
    (P : Measure Ω) : Prop :=
  (∀ i, IsBrownianReal (fun t w => B t w i) P) ∧ iIndepFun (fun i w (t : ℝ≥0) => B t w i) P

/-- `X` solves the SDE (1.1) `dXₜ = -∇V(Xₜ)dt + √2 dBₜ`, `X₀ = x₀`: almost surely the
paths are continuous and satisfy the integral equation. -/
def IsLangevinSolution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (V : Rd d → ℝ)
    (B : ℝ≥0 → Ω → Rd d) (P : Measure Ω) (x₀ : Rd d) (X : ℝ≥0 → Ω → Rd d) : Prop :=
  ∀ᵐ w ∂P, Continuous (fun t => X t w) ∧ ∀ t : ℝ≥0,
    X t w = x₀ - (∫ s in (0 : ℝ)..(t : ℝ), gradient V (X s.toNNReal w)) + Real.sqrt 2 • B t w

/-- The standing assumptions of the Euclidean setting: `V` is `C²`, `μ = e^{-V}` is a
probability measure, `B` is a standard Brownian motion and `X x₀` solves (1.1) from `x₀`.
(The existence of a Brownian motion on some probability space is classical and is not proved
here; it is part of what makes the hypothesis satisfiable.) -/
def IsLangevin {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (V : Rd d → ℝ) (B : ℝ≥0 → Ω → Rd d)
    (P : Measure Ω) (X : Rd d → ℝ≥0 → Ω → Rd d) : Prop :=
  ContDiff ℝ 2 V ∧ IsProbabilityMeasure (gibbs V) ∧ IsStdBrownian B P ∧
    ∀ x₀, IsLangevinSolution V B P x₀ (X x₀)

/-! ## Distances and divergences -/

/-- The `L²` Wasserstein distance: the infimum over couplings `π` of `(∫ d(x,y)² dπ)^{1/2}`. -/
def wasserstein2 {α : Type*} [PseudoEMetricSpace α] [MeasurableSpace α] (μ ν : Measure α) :
    ℝ≥0∞ :=
  (⨅ (π : Measure (α × α)) (_ : π.map Prod.fst = μ ∧ π.map Prod.snd = ν),
    ∫⁻ z, edist z.1 z.2 ^ 2 ∂π) ^ (1 / 2 : ℝ)

/-- Total variation distance `sup_A |μ(A) - ν(A)|`. -/
def tvDist {α : Type*} [MeasurableSpace α] (μ ν : Measure α) : ℝ :=
  ⨆ A : {A : Set α // MeasurableSet A}, |μ.real A - ν.real A|

/-- Relative Fisher information `I(ν | μ) = 4 ∫ |∇√h|² dμ`, `h = dν/dμ`, `μ = e^{-V}`, where
`∇√h` is the weak (distributional) gradient. It is `+∞` when `ν` is not absolutely
continuous or `√h` has no weak gradient in `L²(μ)` (paper, before Corollary 1.4). -/
def fisherInfo {d : ℕ} (V : Rd d → ℝ) (ν : Measure (Rd d)) : ℝ≥0∞ :=
  ⨅ (G : Rd d → Rd d) (_ : ν ≪ gibbs V ∧ MemLp G 2 (gibbs V) ∧
      ∀ φ : Rd d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        ∫ x, Real.sqrt (ν.rnDeriv (gibbs V) x).toReal • gradient φ x = -∫ x, φ x • G x),
    4 * ∫⁻ x, ‖G x‖ₑ ^ 2 ∂gibbs V

/-- The relative density distance `‖dν/dμ - 1‖_{Lᵖ(μ)}` (paper (1.25)); `+∞` if `ν` is
not absolutely continuous with respect to `μ`. -/
def relLp {α : Type*} [MeasurableSpace α] (ν μ : Measure α) (p : ℝ≥0∞) : ℝ≥0∞ := by
  classical
  exact if ν ≪ μ then eLpNorm (fun x => (ν.rnDeriv μ x).toReal - 1) p μ else ⊤

/-- Worst case over initial conditions `x₀ ∈ S` of a discrepancy `δ` of `Law(X_t^{x₀})`. -/
def worst {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] (P : Measure Ω)
    (X : α → ℝ≥0 → Ω → α) (S : Set α) (δ : Measure α → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  ⨆ x₀ ∈ S, δ (P.map (X x₀ t.toNNReal))

/-- Cutoff of a profile at critical times `tₙ`: for every `ε ∈ (0,1)` it tends to `before`
at times `(1-ε)tₙ` and to `after` at times `(1+ε)tₙ`. -/
def HasCutoff (profile : ℕ → ℝ → ℝ≥0∞) (t : ℕ → ℝ) (before after : ℝ≥0∞) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 →
    Tendsto (fun n => profile n ((1 - ε) * t n)) atTop (𝓝 before) ∧
      Tendsto (fun n => profile n ((1 + ε) * t n)) atTop (𝓝 after)

/-- The ball `{x : |x - m| ≤ c√d}` around the mean `m` of `μ` (Corollary 1.3). -/
def meanBall {d : ℕ} (V : Rd d → ℝ) (c : ℝ) : Set (Rd d) :=
  Metric.closedBall (∫ x, x ∂gibbs V) (c * Real.sqrt d)

/-- The cube `m + [-c, c]^d` around the mean `m` of `μ` (Corollary 1.6). -/
def meanCube {d : ℕ} (V : Rd d → ℝ) (c : ℝ) : Set (Rd d) :=
  {x | ∀ i, |x i - (∫ y, y ∂gibbs V) i| ≤ c}

/-! ## Main Euclidean results -/

/-- **Theorem 1.1** (main Wasserstein estimate), including the ball refinement. -/
theorem main_wasserstein_estimate {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {V : Rd d → ℝ} {B : ℝ≥0 → Ω → Rd d} {P : Measure Ω} {X : Rd d → ℝ≥0 → Ω → Rd d}
    (hL : IsLangevin V B P X) (hV : RigidCurvature V) (t : ℝ≥0) :
    let gap := spectralGap V
    let q := Real.exp (-2 * gap * t)
    let lower := fun Λ : ℝ≥0∞ => ENNReal.ofReal (q / gap) * Λ +
      ENNReal.ofReal (firstEigenDim V * (1 - Real.sqrt (1 - q)) ^ 2 / gap)
    let W := fun x₀ => wasserstein2 (P.map (X x₀ t)) (gibbs V) ^ 2
    (∀ S : Set (Rd d), S.Nonempty →
      lower (⨆ x₀ ∈ S, eigenLambda V x₀) ≤ ⨆ x₀ ∈ S, W x₀ ∧
      ⨆ x₀ ∈ S, W x₀ ≤ ENNReal.ofReal q * ⨆ x₀ ∈ S, ∫⁻ x, edist x x₀ ^ 2 ∂gibbs V) ∧
    (∫ x, x ∂gibbs V = 0 → ∀ R : ℝ, 0 ≤ R →
      lower (ENNReal.ofReal (gap * R ^ 2)) ≤ ⨆ x₀ ∈ Metric.closedBall 0 R, W x₀) := by
  sorry

/-- **Remark 1.2**: `1 ≤ k₁ ≤ d`, and `Λ(x₀) = ∑ᵢ |fᵢ(x₀)|²` for every orthonormal basis of `E₁`
(the supremum defining `Λ` is attained by every basis). -/
theorem eigenspace_dim_and_lambda {d : ℕ} {V : Rd d → ℝ} (hV2 : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbs V)) (hV : RigidCurvature V) :
    1 ≤ firstEigenDim V ∧ firstEigenDim V ≤ d ∧
      ∀ f, IsEigenbasis V f → ∀ x₀, eigenLambda V x₀ = ENNReal.ofReal (∑ i, f i x₀ ^ 2) := by
  sorry

/-- The standing assumptions of Corollaries 1.3 and 1.4 for a sequence of dimensions `n`:
the Euclidean setting and the curvature condition (1.4) in every positive dimension, and
`liminf λ₁⁽ⁿ⁾ > 0`. -/
def IsRigidSequence {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (V : ∀ n, Rd n → ℝ)
    (B : ∀ n, ℝ≥0 → Ω n → Rd n) (P : ∀ n, Measure (Ω n)) (X : ∀ n, Rd n → ℝ≥0 → Ω n → Rd n) :
    Prop :=
  (∀ n, 0 < n → IsLangevin (V n) (B n) (P n) (X n) ∧ RigidCurvature (V n)) ∧
    0 < liminf (fun n => ENNReal.ofReal (spectralGap (V n))) atTop

/-- The critical time `t* = log d / (2 λ₁)`. -/
def criticalTime (d : ℕ) (gap : ℝ) : ℝ := Real.log d / (2 * gap)

/-- **Corollary 1.3** (Wasserstein cutoff on balls `B(m, c√d)`), for `ε ∈ (0,1)`. -/
theorem wasserstein_cutoff {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {V : ∀ n, Rd n → ℝ}
    {B : ∀ n, ℝ≥0 → Ω n → Rd n} {P : ∀ n, Measure (Ω n)} {X : ∀ n, Rd n → ℝ≥0 → Ω n → Rd n}
    (h : IsRigidSequence V B P X) {c : ℝ} (hc : 0 < c) :
    HasCutoff (fun n => worst (P n) (X n) (meanBall (V n) c) (wasserstein2 · (gibbs (V n))))
      (fun n => criticalTime n (spectralGap (V n))) ⊤ 0 := by
  sorry

/-- **Corollary 1.4** (Fisher information, relative entropy and total variation cutoffs on
balls `B(m, c√d)`), under the additional assumption `λ₁⁽ⁿ⁾ = o(log n)`. -/
theorem information_cutoff {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {V : ∀ n, Rd n → ℝ}
    {B : ∀ n, ℝ≥0 → Ω n → Rd n} {P : ∀ n, Measure (Ω n)} {X : ∀ n, Rd n → ℝ≥0 → Ω n → Rd n}
    (h : IsRigidSequence V B P X)
    (hsmall : (fun n => spectralGap (V n)) =o[atTop] (fun n : ℕ => Real.log n))
    {c : ℝ} (hc : 0 < c) :
    let t := fun n => criticalTime n (spectralGap (V n))
    let S := fun n => meanBall (V n) c
    HasCutoff (fun n => worst (P n) (X n) (S n) (fisherInfo (V n))) t ⊤ 0 ∧
    HasCutoff (fun n => worst (P n) (X n) (S n) (InformationTheory.klDiv · (gibbs (V n)))) t ⊤ 0 ∧
    HasCutoff (fun n => worst (P n) (X n) (S n) (fun ν => .ofReal (tvDist ν (gibbs (V n))))) t 1 0 := by
  sorry

/-- **Display (1.25)** (`Lᵖ` cutoff) under the assumptions of Corollary 1.4, for every
finite `p ≥ 1`: the limit before the critical time is `2` for `p = 1` and `+∞` for `p > 1`.
(The case `p = ∞` is excluded: it fails already for the Ornstein–Uhlenbeck process.) -/
theorem lp_cutoff {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {V : ∀ n, Rd n → ℝ}
    {B : ∀ n, ℝ≥0 → Ω n → Rd n} {P : ∀ n, Measure (Ω n)} {X : ∀ n, Rd n → ℝ≥0 → Ω n → Rd n}
    (h : IsRigidSequence V B P X)
    (hsmall : (fun n => spectralGap (V n)) =o[atTop] (fun n : ℕ => Real.log n))
    {c : ℝ} (hc : 0 < c) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) :
    HasCutoff (fun n => worst (P n) (X n) (meanBall (V n) c) (relLp · (gibbs (V n)) p))
      (fun n => criticalTime n (spectralGap (V n))) (if p = 1 then 2 else ⊤) 0 := by
  sorry

/-- The diagonal direction `(1,…,1)` of `ℝ^d`. -/
def diagonal (d : ℕ) : Rd d := WithLp.toLp 2 fun _ => 1

/-- **Theorem 1.5** (convex interaction): for `V(x) = ρ|x|²/2 + W(x)` with `W` convex `C²`
and invariant under translations along `(1,…,1)`, (i) `λ₁ = ρ` and `x₁+⋯+x_d ∈ E₁`,
(ii) `V` is `ρ`-convex and `μ` has the Gaussian factor `𝒩(0, 1/ρ)` along `u = (1,…,1)/√d`,
(iii) the curvature condition (1.4) holds. -/
theorem convex_interaction {d : ℕ} (hd : 0 < d) {ρ : ℝ} (hρ : 0 < ρ) {W : Rd d → ℝ}
    (hW : ContDiff ℝ 2 W) (hconv : ConvexOn ℝ univ W)
    (hinv : ∀ x (s : ℝ), W (x + s • diagonal d) = W x)
    (hp : IsProbabilityMeasure (gibbs fun x => ρ / 2 * ‖x‖ ^ 2 + W x)) :
    let V := fun x : Rd d => ρ / 2 * ‖x‖ ^ 2 + W x
    let u := (Real.sqrt d)⁻¹ • diagonal d
    let π := fun x : Rd d => x - inner ℝ u x • u
    (spectralGap V = ρ ∧ IsEigenfunction V ρ (fun x => ∑ i, x i)) ∧
    ((∀ x z : Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) ∧
      (gibbs V).map (fun x => (inner ℝ u x, π x)) =
        (gaussianReal 0 ρ⁻¹.toNNReal).prod ((gibbs V).map π)) ∧
    RigidCurvature V := by
  sorry

/-- **Corollary 1.6** (cutoff for convex interactions, fixed `ρ > 0`): Wasserstein, Fisher,
entropy and total variation cutoffs at `t* = log d / (2ρ)`, from balls `B(m, c√d)` and from
cubes `m + [-c,c]^d`. -/
theorem convex_interaction_cutoff {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {ρ : ℝ}
    (hρ : 0 < ρ) {W : ∀ n, Rd n → ℝ} {B : ∀ n, ℝ≥0 → Ω n → Rd n} {P : ∀ n, Measure (Ω n)}
    {X : ∀ n, Rd n → ℝ≥0 → Ω n → Rd n}
    (hW : ∀ n, 0 < n → ContDiff ℝ 2 (W n) ∧ ConvexOn ℝ univ (W n) ∧
      ∀ x (s : ℝ), W n (x + s • diagonal n) = W n x)
    (hL : ∀ n, 0 < n → IsLangevin (fun x => ρ / 2 * ‖x‖ ^ 2 + W n x) (B n) (P n) (X n))
    {c : ℝ} (hc : 0 < c) :
    let V := fun n (x : Rd n) => ρ / 2 * ‖x‖ ^ 2 + W n x
    let t := fun n : ℕ => criticalTime n ρ
    ∀ cube : Bool,
      let S := fun n => if cube then meanCube (V n) c else meanBall (V n) c
      HasCutoff (fun n => worst (P n) (X n) (S n) (wasserstein2 · (gibbs (V n)))) t ⊤ 0 ∧
      HasCutoff (fun n => worst (P n) (X n) (S n) (fisherInfo (V n))) t ⊤ 0 ∧
      HasCutoff (fun n => worst (P n) (X n) (S n)
        (InformationTheory.klDiv · (gibbs (V n)))) t ⊤ 0 ∧
      HasCutoff (fun n => worst (P n) (X n) (S n)
        (fun ν => .ofReal (tvDist ν (gibbs (V n))))) t 1 0 := by
  sorry

/-- The total variation mixing time `t₀ = inf {t ≥ 0 : sup_{x₀ ∈ S} d_TV(Xₜ, μ) ≤ η}`
(`+∞` if the set is empty). -/
def mixingTime {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (X : Rd d → ℝ≥0 → Ω → Rd d) (μ : Measure (Rd d)) (S : Set (Rd d)) (η : ℝ) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : worst P X S (fun ν => .ofReal (tvDist ν μ)) t ≤ .ofReal η), (t : ℝ≥0∞)

/-- **Theorem 1.7** (curvature product condition), in the amended form of the corrected
manuscript: TV and entropy cutoff at the mixing time `t₀⁽ⁿ⁾` under `κ⁽ⁿ⁾t₀⁽ⁿ⁾ → ∞` and
eventual finiteness of `t₀⁽ⁿ⁾`; Fisher and Wasserstein cutoffs under the additional
assumptions `liminf κ⁽ⁿ⁾ > 0` and `t₀⁽ⁿ⁾ → ∞`. The last assumption is absent from the
archived arXiv v4 statement, which is false without it (see `PAPER_AUDIT.md`). -/
theorem product_condition_cutoff {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {V : ∀ n, Rd n → ℝ} {B : ∀ n, ℝ≥0 → Ω n → Rd n} {P : ∀ n, Measure (Ω n)}
    {X : ∀ n, Rd n → ℝ≥0 → Ω n → Rd n} {κ : ℕ → ℝ} {S : ∀ n, Set (Rd n)} {η : ℝ}
    (hL : ∀ n, 0 < n → IsLangevin (V n) (B n) (P n) (X n) ∧ 0 < κ n ∧
      ∀ x z : Rd n, κ n * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (V n)) x z z)
    (hS : ∀ n, 0 < n → (S n).Nonempty) (hη : 0 < η) (hη1 : η < 1) :
    let t₀ := fun n => mixingTime (P n) (X n) (gibbs (V n)) (S n) η
    let prof := fun (δ : ∀ n, Measure (Rd n) → ℝ≥0∞) n => worst (P n) (X n) (S n) (δ n)
    (∀ᶠ n in atTop, t₀ n < ⊤) → Tendsto (fun n => κ n * (t₀ n).toReal) atTop atTop →
      (HasCutoff (prof fun n ν => .ofReal (tvDist ν (gibbs (V n))))
          (fun n => (t₀ n).toReal) 1 0 ∧
        HasCutoff (prof fun n ν => InformationTheory.klDiv ν (gibbs (V n)))
          (fun n => (t₀ n).toReal) ⊤ 0) ∧
      (0 < liminf (fun n => ENNReal.ofReal (κ n)) atTop →
        Tendsto (fun n => (t₀ n).toReal) atTop atTop →
        HasCutoff (prof fun n => fisherInfo (V n)) (fun n => (t₀ n).toReal) ⊤ 0 ∧
        HasCutoff (prof fun n ν => wasserstein2 ν (gibbs (V n))) (fun n => (t₀ n).toReal) ⊤ 0) := by
  sorry

/-- **Theorem 3.1** (Gaussian factorization) and **Remark 3.2**: if `V` is `ρ`-convex and
`λ₁ = ρ`, there are an orthonormal basis `e` and `m ∈ ℝ^d` with
`V(x) = (ρ/2) ∑_{i<k₁} (⟨eᵢ,x⟩ - mᵢ)² + U(x)`, `U` depending only on the coordinates
`⟨eᵢ,x⟩`, `i ≥ k₁`, and `ρ`-convex in those coordinates; every `f ∈ E₁` is affine,
`f(x) = ∑_{i<k₁} aᵢ(⟨eᵢ,x⟩ - mᵢ)`, with `|a|² = λ₁ ‖f‖²_{L²(μ)}`. -/
theorem euclidean_gaussian_factorization {d : ℕ} {V : Rd d → ℝ} (hV2 : ContDiff ℝ 2 V)
    (hp : IsProbabilityMeasure (gibbs V)) {ρ : ℝ} (hρ : 0 < ρ)
    (hconv : ∀ x z : Rd d, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z) (hgap : spectralGap V = ρ) :
    ∃ (e : OrthonormalBasis (Fin d) ℝ (Rd d)) (m : Fin d → ℝ) (U : Rd d → ℝ),
      (∀ x, V x = ρ / 2 * ∑ i with i.val < firstEigenDim V, (inner ℝ (e i) x - m i) ^ 2 + U x) ∧
      (∀ x y, (∀ i, firstEigenDim V ≤ i.val → inner ℝ (e i) x = inner ℝ (e i) y) → U x = U y) ∧
      (∀ x z, (∀ i, i.val < firstEigenDim V → inner ℝ (e i) z = 0) →
        ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ U) x z z) ∧
      ∀ f, IsEigenfunction V ρ f → ∃ a : Fin d → ℝ, (∀ i, firstEigenDim V ≤ i.val → a i = 0) ∧
        (∀ x, f x = ∑ i, a i * (inner ℝ (e i) x - m i)) ∧
        ∑ i, a i ^ 2 = ρ * ∫ x, f x ^ 2 ∂gibbs V := by
  sorry

/-- **Lemma 3.3** (projection on an orthonormal multi-eigenfunction is an OU process): for an
orthonormal basis `T = (f₁,…,f_{k₁})` of `E₁` under `λ₁ = ρ` and `ρ`-convexity, the process
`Yₜ = T(Xₜ)` solves the Ornstein–Uhlenbeck equation `dYₜ = -ρYₜ dt + √(2ρ) dβₜ` for a standard
Brownian motion `β` on `ℝ^{k₁}`. In particular its generator is `ρΔ - ρ y·∇`. -/
theorem eigenmap_is_ou {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {V : Rd d → ℝ} {B : ℝ≥0 → Ω → Rd d} {P : Measure Ω} {X : Rd d → ℝ≥0 → Ω → Rd d}
    (hL : IsLangevin V B P X) (hV : RigidCurvature V)
    (T : Fin (firstEigenDim V) → Rd d → ℝ) (hT : IsEigenbasis V T) :
    let ρ := spectralGap V
    let Tv := fun x => (WithLp.toLp 2 fun i => T i x : Rd (firstEigenDim V))
    ∃ β : ℝ≥0 → Ω → Rd (firstEigenDim V), IsStdBrownian β P ∧ ∀ x₀, ∀ᵐ w ∂P, ∀ t : ℝ≥0,
      Tv (X x₀ t w) = Tv x₀ - ρ • (∫ s in (0 : ℝ)..(t : ℝ), Tv (X x₀ s.toNNReal w)) +
        Real.sqrt (2 * ρ) • β t w := by
  sorry

/-! ## Weighted Riemannian manifolds (Section 1.4)

`M` is a smooth manifold without boundary modelled on a finite-dimensional inner product
space `F`, with a smooth Riemannian metric, whose extended distance is the Riemannian
distance (`IsRiemannianManifold`). The Hessian uses Mathlib's Levi-Civita connection. -/

section Riemannian

open Bundle

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

/-- The Riemannian gradient: the Riesz representative of the differential. -/
def mgrad (f : M → ℝ) (x : M) : TangentSpace 𝓘(ℝ, F) x :=
  (InnerProductSpace.toDual ℝ (TangentSpace 𝓘(ℝ, F) x)).symm (mvfderiv 𝓘(ℝ, F) f x)

/-- The Laplace–Beltrami operator: the trace of the Levi-Civita Hessian `∇(grad f)`. -/
def mlaplacian (f : M → ℝ) (x : M) : ℝ :=
  ∑ i, inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F f) x
      (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i))
    (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)

/-- The generator (1.27) `𝓛f = Δf - ⟨∇V, ∇f⟩`. -/
def mgenerator (V f : M → ℝ) (x : M) : ℝ :=
  mlaplacian F f x - inner ℝ (mgrad F V x) (mgrad F f x)

/-- The carré du champ `Γ(f,g) = ⟨∇f, ∇g⟩`. -/
def carre (f g : M → ℝ) (x : M) : ℝ := inner ℝ (mgrad F f x) (mgrad F g x)

/-- The iterated carré du champ `Γ₂(f) = ½ 𝓛Γ(f,f) - Γ(f, 𝓛f)`. -/
def carre2 (V f : M → ℝ) (x : M) : ℝ :=
  mgenerator F V (carre F f f) x / 2 - carre F f (mgenerator F V f) x

/-- The Bakry–Émery curvature-dimension condition `CD(ρ,∞)`: `Γ₂(f) ≥ ρ Γ(f)` for every smooth
`f` (equivalently `Ric + Hess V ≥ ρ g`). -/
def CD (ρ : ℝ) (V : M → ℝ) : Prop :=
  ∀ f : M → ℝ, ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f → ∀ x, ρ * carre F f f x ≤ carre2 F V f x

/-- The Riemannian volume density `√det(gᵢⱼ)` of the inverse of the chart at `x₀`, at the chart
point `z`, computed in an orthonormal basis of the model space. -/
def chartVolumeDensity (x₀ : M) (z : F) : ℝ :=
  Real.sqrt (Matrix.det (Matrix.of fun i j =>
    inner ℝ (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (chartAt F x₀).symm z (stdOrthonormalBasis ℝ F i) :
      TangentSpace 𝓘(ℝ, F) ((chartAt F x₀).symm z))
      (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) (chartAt F x₀).symm z (stdOrthonormalBasis ℝ F j))))

/-- `μ = e^{-V} vol_g`: in every chart, `μ` has density `e^{-V} √det(gᵢⱼ)` with respect to
Lebesgue measure. -/
def IsWeightedVolume [MeasurableSpace M] (μ : Measure M) (V : M → ℝ) : Prop :=
  ∀ x₀ : M, (μ.restrict (chartAt F x₀).source).map (chartAt F x₀) =
    (volume.restrict (chartAt F x₀).target).withDensity fun z =>
      ENNReal.ofReal (Real.exp (-V ((chartAt F x₀).symm z)) * chartVolumeDensity F x₀ z)

/-- The spectral gap of `-𝓛` in `L²(μ)` (optimal Poincaré constant over smooth compactly
supported test functions). -/
def mSpectralGap [MeasurableSpace M] (μ : Measure M) : ℝ :=
  sInf {r : ℝ | ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f ∧ HasCompactSupport f ∧
    0 < variance f μ ∧ r = (∫ x, ‖mgrad F f x‖ ^ 2 ∂μ) / variance f μ}

/-- Smooth `L²(μ)` eigenfunctions of `-𝓛` with eigenvalue `lam`. -/
def IsMEigenfunction [MeasurableSpace M] (μ : Measure M) (V : M → ℝ) (lam : ℝ) (f : M → ℝ) :
    Prop :=
  ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f ∧ MemLp f 2 μ ∧ ∀ x, mgenerator F V f x = -lam * f x

/-- `k₁ = dim E₁`, `E₁ ⊆ L²(μ)` the eigenspace of `-𝓛` for `λ₁`. -/
def mFirstEigenDim [MeasurableSpace M] (μ : Measure M) (V : M → ℝ) : ℕ :=
  Module.finrank ℝ (Submodule.span ℝ
    {u : M →₂[μ] ℝ | ∃ f, IsMEigenfunction F μ V (mSpectralGap F μ) f ∧ f =ᵐ[μ] u})

/-- `Λ(x) = sup_{T ∈ 𝕊_{F₁}} |T(x)|²` (Definition 1.8), the supremum over multi-eigenfunctions
`T = (f₁,…,f_{k₁})` with orthonormal coordinates in `E₁`. -/
def mLambda [MeasurableSpace M] (μ : Measure M) (V : M → ℝ) (x : M) : ℝ≥0∞ :=
  ⨆ (T : Fin (mFirstEigenDim F μ V) → M → ℝ)
    (_ : (∀ i, IsMEigenfunction F μ V (mSpectralGap F μ) (T i)) ∧
      ∀ i j, ∫ y, T i y * T j y ∂μ = if i = j then 1 else 0),
    ENNReal.ofReal (∑ i, T i x ^ 2)

/-- The diffusion (1.26) with generator `𝓛`, through its transition kernels `Pₜ(x, ·) = Law(Xₜ)`
from `X₀ = x`: a Markov semigroup solving Kolmogorov's equation
`Pₜf(x) = f(x) + ∫₀ᵗ Pₛ(𝓛f)(x) ds` for smooth compactly supported `f`. Under the standing
hypotheses of the Riemannian theorems (completeness, `CD(ρ,∞)`, `ρ > 0`) there is exactly one such
semigroup, the minimal and conservative diffusion; this is proved in the formalization
(`Riemann/DiffKer*`, `DiffPerron*`) and not assumed. -/
def IsDiffusionSemigroup [MeasurableSpace M] (V : M → ℝ) (Pt : ℝ≥0 → Kernel M M) : Prop :=
  (∀ t, IsMarkovKernel (Pt t)) ∧ (∀ s t, Pt (s + t) = Pt t ∘ₖ Pt s) ∧
    ∀ f : M → ℝ, ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f → HasCompactSupport f → ∀ (x : M) (t : ℝ≥0),
      ∫ y, f y ∂Pt t x = f x + ∫ s in (0 : ℝ)..(t : ℝ), ∫ y, mgenerator F V f y ∂Pt s.toNNReal x

variable [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M]

/-- **Theorem 1.9** (Wasserstein estimate on a smooth, connected, complete weighted Riemannian
manifold without boundary), including the ball refinement. -/
theorem riemannian_wasserstein_estimate {V : M → ℝ} (hV : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ V)
    {μ : Measure M} [IsProbabilityMeasure μ] (hμ : IsWeightedVolume F μ V) {ρ : ℝ} (hρ : 0 < ρ)
    (hCD : CD F ρ V) (hgap : mSpectralGap F μ = ρ) {Pt : ℝ≥0 → Kernel M M}
    (hP : IsDiffusionSemigroup F V Pt) (t : ℝ≥0) :
    let q := Real.exp (-2 * ρ * t)
    let lower := fun Λ : ℝ≥0∞ => ENNReal.ofReal (q / ρ) * Λ +
      ENNReal.ofReal (mFirstEigenDim F μ V * (1 - Real.sqrt (1 - q)) ^ 2 / ρ)
    let W := fun x₀ => wasserstein2 (Pt t x₀) μ ^ 2
    (∀ S : Set M, S.Nonempty →
      lower (⨆ x₀ ∈ S, mLambda F μ V x₀) ≤ ⨆ x₀ ∈ S, W x₀ ∧
      ⨆ x₀ ∈ S, W x₀ ≤ ENNReal.ofReal q * ⨆ x₀ ∈ S, ∫⁻ x, edist x₀ x ^ 2 ∂μ) ∧
    ∀ (m : M) (R : ℝ), 0 ≤ R → mLambda F μ V m = 0 →
      lower (ENNReal.ofReal (ρ * R ^ 2)) ≤ ⨆ x₀ ∈ {x | edist m x ≤ ENNReal.ofReal R}, W x₀ := by
  sorry

/-- **Theorem 3.6** (Riemannian splitting with Gaussian factor) and **Lemma 3.7** (rigidity of
first eigenfunctions): `(M, g, μ)` is isometric to `(ℝ^{k₁} × M', |·|² ⊕ g', γ_{k₁,ρ⁻¹} ⊗ μ')`
with `(M', g', μ')` a weighted Riemannian manifold satisfying `CD(ρ,∞)`; through this
isometry every `f ∈ E₁` is `f = ⟨a, p⟩`, `p` the projection on the Euclidean factor, with
`|a|² = ρ ‖f‖²_{L²(μ)}`, and orthogonal eigenfunctions have orthogonal vectors `a`. -/
theorem riemannian_gaussian_splitting {V : M → ℝ} (hV : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ V)
    {μ : Measure M} [IsProbabilityMeasure μ] (hμ : IsWeightedVolume F μ V) {ρ : ℝ} (hρ : 0 < ρ)
    (hCD : CD F ρ V) (hgap : mSpectralGap F μ = ρ) :
    let k := mFirstEigenDim F μ V
    ∃ (F' : Type) (_ : NormedAddCommGroup F') (_ : InnerProductSpace ℝ F')
      (_ : FiniteDimensional ℝ F') (N : Type) (_ : EMetricSpace N) (_ : ChartedSpace F' N)
      (_ : IsManifold 𝓘(ℝ, F') ∞ N) (_ : RiemannianBundle (fun y : N => TangentSpace 𝓘(ℝ, F') y))
      (_ : IsContMDiffRiemannianBundle 𝓘(ℝ, F') ∞ F' (fun y : N => TangentSpace 𝓘(ℝ, F') y))
      (_ : IsRiemannianManifold 𝓘(ℝ, F') N) (_ : MeasurableSpace F') (_ : BorelSpace F') (_ : MeasurableSpace N) (_ : BorelSpace N)
      (V' : N → ℝ) (μ' : Measure N)
      (Φ : M ≃ₘ^∞⟮𝓘(ℝ, F), 𝓘(ℝ, Rd k).prod 𝓘(ℝ, F')⟯ Rd k × N),
      (ContMDiff 𝓘(ℝ, F') 𝓘(ℝ, ℝ) ∞ V' ∧ IsProbabilityMeasure μ' ∧ IsWeightedVolume F' μ' V' ∧
        CD F' ρ V') ∧
      (∀ x y, edist x y ^ 2 = edist (Φ x).1 (Φ y).1 ^ 2 + edist (Φ x).2 (Φ y).2 ^ 2) ∧
      μ.map Φ = (multivariateGaussian 0 (ρ⁻¹ • (1 : Matrix (Fin k) (Fin k) ℝ))).prod μ' ∧
      (∀ f, IsMEigenfunction F μ V ρ f → ∃ a : Rd k, (∀ x, f x = inner ℝ a (Φ x).1) ∧
        ‖a‖ ^ 2 = ρ * ∫ x, f x ^ 2 ∂μ) ∧
      ∀ f g (a b : Rd k), IsMEigenfunction F μ V ρ f → IsMEigenfunction F μ V ρ g →
        (∀ x, f x = inner ℝ a (Φ x).1) → (∀ x, g x = inner ℝ b (Φ x).1) →
        ∫ x, f x * g x ∂μ = 0 → inner ℝ a b = 0 := by
  sorry

end Riemannian

end CutCur
