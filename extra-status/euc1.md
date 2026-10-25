# euc1: Brownian-free Euclidean setting (foundation file)

File: `CutoffRigidity/Extra/EuclideanDiffusion.lean` (267 lines, module `CutoffRigidity.Extra.EuclideanDiffusion`), `lake build` OK, no warnings, no sorry,
all lemmas depend only on propext/Classical.choice/Quot.sound. Everything lives in namespace `CutCur` (so Challenge-side defs can be moved verbatim; the lemmas
are in `CutCur` too, drop them into `CutoffRigidity.Paper` with `open CutCur` when wiring). Imports: DiffFinal, WitnessMain, Paper.CoreBridge, Paper.ExistsBrownian, LangevinDynkin.
Uses `set_option backward.isDefEq.respectTransparency false` (needed by `isEuclideanDiffusion_iff`).

## Challenge text (definitions, Mathlib-only plus CutCur notions)
```lean
def IsEuclideanDiffusion {d : ℕ} (V : Rd d → ℝ) (Pt : ℝ≥0 → Kernel (Rd d) (Rd d)) : Prop :=
  (∀ t, IsMarkovKernel (Pt t)) ∧ (∀ s t, Pt (s + t) = Pt t ∘ₖ Pt s) ∧
    ∀ f : Rd d → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → ∀ (x : Rd d) (t : ℝ≥0),
      ∫ y, f y ∂Pt t x = f x + ∫ s in (0 : ℝ)..(t : ℝ), ∫ y, generator V f y ∂Pt s.toNNReal x

def IsEuclideanLangevin {d : ℕ} (V : Rd d → ℝ) (Pt : ℝ≥0 → Kernel (Rd d) (Rd d)) : Prop :=
  ContDiff ℝ ∞ V ∧ IsProbabilityMeasure (gibbs V) ∧ IsEuclideanDiffusion V Pt

noncomputable def worstK {d : ℕ} (Pt : ℝ≥0 → Kernel (Rd d) (Rd d)) (S : Set (Rd d))
    (δ : Measure (Rd d) → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ := ⨆ x₀ ∈ S, δ (Pt t.toNNReal x₀)

noncomputable def mixingTimeK (Pt) (μ : Measure (Rd d)) (S : Set (Rd d)) (η : ℝ) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : worstK Pt S (fun ν => .ofReal (tvDist ν μ)) t ≤ .ofReal η), (t : ℝ≥0∞)
-- also mixingTimeW2K (δ := wasserstein2 ν μ) and mixingTimeKLK (δ := InformationTheory.klDiv ν μ)

def IsRigidSequenceK (V : ∀ n, Rd n → ℝ) (Pt : ∀ n, ℝ≥0 → Kernel (Rd n) (Rd n)) : Prop :=
  (∀ n, 0 < n → IsEuclideanLangevin (V n) (Pt n) ∧ RigidCurvature (V n)) ∧
    0 < liminf (fun n => ENNReal.ofReal (spectralGap (V n))) atTop
```
(Exact texts with docstrings are in the file.) `generator V f = Δf - ⟨∇V,∇f⟩` is the existing CutCur.generator.

## Lemmas (all proved, namespace CutCur)
* `isEuclideanDiffusion_iff : IsEuclideanDiffusion V Pt ↔ IsDiffusionSemigroup (Rd d) V Pt`
* `generator_eq_langevinOp (hf : ContDiff ℝ 2 f) x : generator V f x = langevinDifferentialOperator V f x`
* `isEuclideanDiffusion_langevinKernel (hB : IsEuclideanBrownian B P) (hV : ContDiff ℝ 2 V) (rate) (hrate : 0 ≤ rate) (hHess : ∀ x z, rate*‖z‖^2 ≤ fderiv ℝ (fderiv ℝ V) x z z) : IsEuclideanDiffusion V (langevinKernel V B P)`
* `isEuclideanDiffusion_unique (hV : ContDiff ℝ ∞ V) (hp : IsProbabilityMeasure (gibbs V)) (h₁ : IsEuclideanDiffusion V P₁) (h₂ : ... P₂) : ∀ t x, P₁ t x = P₂ t x`
* `isEuclideanLangevin_unique (h₁ : IsEuclideanLangevin V P₁) (h₂ : IsEuclideanLangevin V P₂) : ∀ t x, P₁ t x = P₂ t x`
* `isEuclideanDiffusion_eq_langevinKernel hB hV hp rate hrate hHess (hP : IsEuclideanDiffusion V Pt) t x : Pt t x = langevinKernel V B P t x`
* Non-vacuity: `exists_euclideanLangevin (hV : ContDiff ℝ ∞ V) (hHess : ∀ x z, 0 ≤ fderiv ℝ (fderiv ℝ V) x z z) (hp : IsProbabilityMeasure (gibbs V)) : ∃ Pt, IsEuclideanLangevin V Pt`
  (via a Brownian carrier + `langevinKernel`), and `exists_euclideanLangevin_of_smooth (hV) (hp)` WITHOUT convexity (via the Riemannian canonical kernel `Diff.Kk (Rd d)`).
* KEY transfer lemma:
  `exists_isLangevin_of_isEuclideanLangevin (hL : IsEuclideanLangevin V Pt) (hHess : ∀ x z, 0 ≤ fderiv ℝ (fderiv ℝ V) x z z) :
     ∃ (Ω : Type) (_ : MeasurableSpace Ω) (B : ℝ≥0 → Ω → Rd d) (P : Measure Ω) (X : Rd d → ℝ≥0 → Ω → Rd d),
       IsProbabilityMeasure P ∧ IsLangevin V B P X ∧ ∀ (t : ℝ≥0) (x₀ : Rd d), P.map (X x₀ t) = Pt t x₀`
  and `exists_isLangevin_of_rigid (hL : IsEuclideanLangevin V Pt) (hR : RigidCurvature V)` (same conclusion; `RigidCurvature.hess_nonneg hR` gives convexity).
* Sequence transfer: `exists_isRigidSequence_of_K (h : IsRigidSequenceK V Pt) : ∃ (Ω : ℕ → Type) (_ : ∀ n, MeasurableSpace (Ω n)) B P X,
     (∀ n, 0 < n → IsProbabilityMeasure (P n)) ∧ IsRigidSequence V B P X ∧ ∀ n, 0 < n → ∀ t x₀, (P n).map (X n x₀ t) = Pt n t x₀`
  (dimension 0 gets a dummy carrier `Unit`, never used).
* Profile translation: `worst_eq_worstK (h : ∀ t x₀, P.map (X x₀ t) = Pt t x₀) S δ t : worst P X S δ t = worstK Pt S δ t`;
  `mixingTime_eq_mixingTimeK`, `mixingTimeW2_eq_mixingTimeW2K`, `mixingTimeKL_eq_mixingTimeKLK` (same hypothesis h, give `... P X μ S η = ...K Pt μ S η`);
  `eventually_worst_eq_worstK (h : ∀ n, 0<n → ∀ t x₀, (P n).map (X n x₀ t) = Pt n t x₀) S δ : ∀ᶠ n in atTop, (fun t => worst (P n) (X n) (S n) (δ n) t) = fun t => worstK (Pt n) (S n) (δ n) t`;
  `hasCutoff_congr_eventually (h : ∀ᶠ n in atTop, p n = q n) (hp : HasCutoff p t b a) : HasCutoff q t b a`.

## Recipe for converting a Paper theorem `T (hL : IsLangevin V B P X) ... : concl(P.map (X x₀ t))`
```lean
theorem T_K (hL : IsEuclideanLangevin V Pt) (hHess : ∀ x z, 0 ≤ fderiv ℝ (fderiv ℝ V) x z z) ... : concl(Pt t x₀) := by
  obtain ⟨Ω, _, B, P, X, hP, hLang, key⟩ := exists_isLangevin_of_isEuclideanLangevin hL hHess
  have := Paper.T hLang ...; simpa only [key] using this
```
(for statements with `RigidCurvature`, use `exists_isLangevin_of_rigid`; the convexity hypothesis then disappears.) Sequence version: `obtain ⟨Ω,_,B,P,X,hP,hrig,key⟩ := exists_isRigidSequence_of_K h`,
apply `Paper.T hrig`, then rewrite `worst` by `eventually_worst_eq_worstK` + `hasCutoff_congr_eventually`, and `mixingTime` by `mixingTime_eq_mixingTimeK` for n > 0 (or `Filter.eventually` congr).
Note the carrier lives in `Type` (universe 0), sufficient since `Paper.*` theorems take `Type*`.

## Design note: hypotheses beyond the manuscript (flag in docstrings)
1. `V` is `C^∞` (instead of `C²`): uniqueness of the diffusion (`bridge_final`) needs smooth coefficients (elliptic regularity for resolvent solutions). Amendment.
2. `IsProbabilityMeasure (gibbs V)` is inside `IsEuclideanLangevin` (already part of `IsLangevin`; no new hypothesis).
3. Convexity: the converted statements about a single `V` need `Hess V ≥ 0` (`∀ x z, 0 ≤ fderiv ℝ (fderiv ℝ V) x z z`) because the library's `langevinKernel` / SDE existence+Dynkin theory requires
   one-sided Lipschitz drift; for any statement that already assumes `RigidCurvature V` (all sequence statements, W2/rigid cutoffs) no extra hypothesis is needed. Statements with only the manuscript's
   "V convex" (e.g. OU: `V = ρ/2‖x‖²+c`, convex smooth) are fine. Without convexity one would only get `exists_euclideanLangevin_of_smooth` (existence), not the carrier transfer.
4. `Pt` is determined by `IsEuclideanDiffusion` only up to the uniqueness theorem (smooth V, probability Gibbs): the kernel definition is therefore faithful to `Law(X_t^{x₀})`.
5. The Brownian carrier is produced by `Paper.exists_stdBrownian` (vendored Degenne et al. library), so nothing is assumed.
