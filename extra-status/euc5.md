# euc5: Lemma 3.3 (`eigenmap_is_ou`) without Brownian motion, law form (A) PROVED

File: `CutoffRigidity/Extra/EigenmapOUK.lean` (75 lines, module `CutoffRigidity.Extra.EigenmapOUK`), `lake build` OK, no sorry, no stray #print/#eval.
`#print axioms CutoffRigidity.Paper.eigenmap_is_ou_K`: propext, Classical.choice, Quot.sound only.
Imports: `Extra.EuclideanDiffusion` (euc1), `Paper.EigenmapOU`, `AffineProjectedDistances`, `OUCutoffs`. Nothing existing was edited.

Paper theorem: `CutoffRigidity.Paper.eigenmap_is_ou_K` (qualified `CutCur.*` names). Requires `IsEuclideanLangevin` (and its def from euc1) in Challenge.

## Proposed Challenge text (unqualified names)
```lean
/-- **Lemma 3.3** (projection on an orthonormal multi-eigenfunction is an OU process), Brownian-free law form: for an orthonormal basis
`T = (f₁,…,f_{k₁})` of `E₁` under `λ₁ = ρ` and `ρ`-convexity, and `Pt` the Euclidean Langevin semigroup, the law of `T(Xₜ)` started at `x₀`
(i.e. the pushforward of `Pt t x₀` by `T`) is the Ornstein–Uhlenbeck marginal `𝒩(e^{-ρt} T(x₀), (1 - e^{-2ρt}) I_{k₁})`, the time-`t` law of the
process with generator `ρΔ - ρ y·∇` (equivalently of `dYₜ = -ρYₜ dt + √(2ρ) dβₜ`, `Y₀ = T x₀`) on `ℝ^{k₁}`. In particular the law of `T(Xₜ)` depends
on `x₀` only through `T x₀` (lumping). Amendment: `V` is `C^∞` (inside `IsEuclideanLangevin`) rather than `C²`. -/
theorem eigenmap_is_ou_K {d : ℕ} {V : Rd d → ℝ} {Pt : ℝ≥0 → Kernel (Rd d) (Rd d)}
    (hL : IsEuclideanLangevin V Pt) (hV : RigidCurvature V) (T : Fin (firstEigenDim V) → Rd d → ℝ) (hT : IsEigenbasis V T) :
    let ρ := spectralGap V
    let Tv := fun x => (WithLp.toLp 2 fun i => T i x : Rd (firstEigenDim V))
    ∀ (x₀ : Rd d) (t : ℝ≥0),
      (Pt t x₀).map Tv = multivariateGaussian (Real.exp (-ρ * (t : ℝ)) • Tv x₀)
        ((1 - Real.exp (-2 * ρ * (t : ℝ))) • (1 : Matrix (Fin (firstEigenDim V)) (Fin (firstEigenDim V)) ℝ))
```
Hypotheses match the original `eigenmap_is_ou` (RigidCurvature V = rho-convexity with rho = lambda_1 > 0 as in the original; IsEigenbasis, same `ρ`, `Tv`), with `IsLangevin ... B P X`
replaced by `IsEuclideanLangevin V Pt`. No convexity hypothesis is needed beyond `RigidCurvature` (it implies Hess V >= 0 for the transfer).

## Conventions checked
Original SDE `dY = -ρY dt + √(2ρ) dβ`, `Y_0 = T x₀`: Mehler mean `e^{-ρt}Y_0`, variance `2ρ∫₀ᵗ e^{-2ρ(t-s)}ds = 1 - e^{-2ρt}` times identity. This is exactly the statement proved
(same normalization as `ouLaw ρ t`, the manuscript's "OU scaled by ρ with unit-variance equilibrium"). The pathwise original statement is NOT recoverable from the kernel alone (no Brownian motion), hence the law form.

## Proof
Take a Brownian carrier from the transfer lemma `exists_isLangevin_of_rigid` (so `Pt t x₀ = P.map (X x₀ t)`), identify `X x₀ t` a.e. with `langevinProcess`, hence `Pt t x₀ = langevinKernel V B P t x₀`.
The eigenfunctions are affine (`c2_L2_eigenfunction_is_affine`), and the existing `langevinKernel_map_affineEigenfunctionMap` (via `langevinProcess_eigenmap_hasLaw`, Mehler law of the
projected Wiener integral, already in the project) plus `ouLaw_eq_multivariateGaussian` give the Gaussian. I did not use `Paper.eigenmap_is_ou` (the pathwise β statement); the law result of the project
is used directly. (Note: did not destructure `IsEuclideanLangevin` since the def is not `@[expose]`; the transfer lemma was used instead.)

## What is derivable / not done
* Lumping at kernel level: law (A) shows `(Pt t x₀).map Tv` is a function of `Tv x₀` (the OU kernel `Q_t(y,·) = 𝒩(e^{-ρt}y,(1-e^{-2ρt})I)`), i.e. the intertwining `Pt t ≫ Tv = Tv ≫ Q_t`.
  Not stated as separate theorem. The full Markov property of the path process `T(X_·)` (finite-dimensional laws) is not proved (needs the Markov property of X, not part of the kernel-only setting beyond
  `Pt (s+t) = Pt t ∘ Pt s`; it would follow by combining the semigroup law with (A) for the two-step kernel, but I did not formalize it).
* Fallback generator form (B) `generator V (g ∘ Tv) = ρ Δg - ρ y·∇g` was NOT done (not needed: (A) was achieved).
