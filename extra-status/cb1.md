# cb1: Bochner / CD equivalence, k1 bounds, Riemannian Poincare + LSI

Status: all three deliverables proved, no sorry, axioms only propext, Classical.choice, Quot.sound
(`#print axioms` checked for each), `lake build` of the three modules succeeds. No existing file edited.
Not human reviewed.

Files (all new, `module` style):
* `CutoffRigidity/Extra/RicciBochner.lean`: defs `CutCur.mCurv, mExt, mRic, mHess, mHessSq` (proposed
  Challenge text, written with Mathlib only) and `CutoffRigidity.Paper.bochner_identity`, `Paper.CD_iff_ricci`.
  Helper lemmas: `mCurv_eq_curv` (rfl: Challenge `mCurv` unfolds to project `WBoch.curv`), `mHessSq_eq` (rfl:
  `mHessSq = mHessNormSq`), `mExt_apply_self`, `mExt_smooth`, `curv_tensor` (tensoriality in the three slots).
* `CutoffRigidity/Extra/RiemannK1.lean`: `Paper.riemannian_k1_bounds`.
* `CutoffRigidity/Extra/RiemannPoincareLSI.lean`: `CutCur.mEntropy`, `mEntropy_eq_entropyOf` (rfl on `Rd d`),
  `Paper.riemannian_poincare_lsi`.
Names to move into Challenge: when the lead pastes the defs into Challenge.lean, delete the `namespace CutCur`
blocks in RicciBochner.lean and RiemannPoincareLSI.lean (they are the only definitions there).

## Choices and findings
* The Ricci tensor is CHOICE-FREE: the extension of a tangent vector `v` at `x` is `mExt x v`, constant
  coordinates in Mathlib's `trivializationAt` (smooth at `x`, value `v` at `x`; proved). So no
  `Classical.choose` appears in the Challenge text (the "for all smooth extensions" form was not needed).
  Extension independence is the project lemma `curv_tensor`, used inside the proof of `bochner_identity`.
* Sign: `Ric(v,w) = sum_i <R(e_i,v)w, e_i>` with `R(X,Y)Z = ∇_X∇_Y Z - ∇_Y∇_X Z - ∇_[X,Y] Z`
  (positive on spheres); the proved Bochner identity has `+Ric`, which pins the convention.
* Hypotheses: only smoothness of `V` (and `f`); no completeness, connectedness, measure or `0 < finrank`.
* The CD equivalence is stated with `rho * ‖v‖ ^ 2` (= `inner v v`).
* k1: `0 < finrank F` is NOT needed (the proof gives `1 ≤ k1` directly). The upper bound needs `hgap` (false
  on spheres: lambda_1 = d, k_1 = d+1). The manuscript does not claim it without `hgap`. Statement is
  Theorem 1.9 without `Pt` and `t`.
* Poincare/LSI: no `hgap`, no `0 < finrank`. The LSI constant is `2/ρ`.
* Entropy: generalizing `entropyOf` to
  `def entropyOf {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : α → ℝ) : ℝ := <same body>`
  does not change the meaning of the existing statements (on `Rd d` the instance is the same;
  `mEntropy_eq_entropyOf` is `rfl`). So the lead can replace `entropyOf` by the general def and use it in
  the LSI theorem; I kept the name `mEntropy` in the project only to avoid editing Challenge. The existing
  uses `entropyOf (gibbs V) ...` elaborate unchanged (implicit `{α}` inferred) but Statements.lean/Solution.lean
  should be rebuilt after the change.
* Not done: vector-form Bochner `grad L = L grad - Hess V grad - Ric(grad,.)` (only quoted in the manuscript) and
  the Leibniz identity `Γ(f,g) = 1/2(L(fg) - fLg - gLf)` (separate small item).

## Proposed Challenge text (about 75 lines)
Inside `section Riemannian`, after `CD` (these use the section variables `F`, `M`; `VectorField.` qualified):

```lean
/-- `∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_{[X,Y]} Z` at `x` (the curvature `R(X,Y)Z` for smooth fields). -/
def mCurv (X Y Z : (y : M) → TangentSpace 𝓘(ℝ, F) y) (x : M) : TangentSpace 𝓘(ℝ, F) x :=
  CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M
      (fun y => CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M Z y (Y y)) x (X x)
    - CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M
      (fun y => CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M Z y (X y)) x (Y x)
    - CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M Z x
      (VectorField.mlieBracket 𝓘(ℝ, F) X Y x)

/-- A smooth extension of `v ∈ T_x M`: constant coordinates in the canonical trivialization at `x`. -/
def mExt (x : M) (v : TangentSpace 𝓘(ℝ, F) x) : (y : M) → TangentSpace 𝓘(ℝ, F) y :=
  fun y => (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x).symm y
    ((trivializationAt F (TangentSpace 𝓘(ℝ, F)) x (Bundle.TotalSpace.mk' F x v)).2)

/-- The Ricci tensor `Ric(v,w) = ∑ᵢ ⟨R(eᵢ,v)w, eᵢ⟩`. -/
def mRic (x : M) (v w : TangentSpace 𝓘(ℝ, F) x) : ℝ :=
  ∑ i, inner ℝ (mCurv F (mExt F x (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i))
      (mExt F x v) (mExt F x w) x) (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)

/-- The Hessian `Hess f (v,w) = ⟨∇_v ∇f, w⟩`. -/
def mHess (f : M → ℝ) (x : M) (v w : TangentSpace 𝓘(ℝ, F) x) : ℝ :=
  inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F f) x v) w

/-- The squared Hilbert–Schmidt norm `‖Hess f‖² = ∑ᵢ ‖∇_{eᵢ} ∇f‖²`. -/
def mHessSq (f : M → ℝ) (x : M) : ℝ :=
  ∑ i, ‖CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F f) x
    (stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) x) i)‖ ^ 2

/-- **Bochner identity** (manuscript lines 641–654): `Γ₂(f) = ‖Hess f‖² + Ric(∇f,∇f) + Hess V(∇f,∇f)`. -/
theorem bochner_identity {V f : M → ℝ} (hV : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ V)
    (hf : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    carre2 F V f x = mHessSq F f x +
      (mRic F x (mgrad F f x) (mgrad F f x) + mHess F V x (mgrad F f x) (mgrad F f x)) := by
  sorry

/-- **`CD(ρ,∞)` is `Ric + Hess V ≥ ρ g`** (manuscript lines 655–663). -/
theorem CD_iff_ricci {V : M → ℝ} (hV : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ V) (ρ : ℝ) :
    CD F ρ V ↔ ∀ (x : M) (v : TangentSpace 𝓘(ℝ, F) x), ρ * ‖v‖ ^ 2 ≤ mRic F x v v + mHess F V x v v := by
  sorry
```
Entropy (replace the Challenge `entropyOf`; same body):
```lean
/-- Entropy `Ent_μ(g) = ∫ g log g dμ - (∫ g dμ) log (∫ g dμ)`. -/
def entropyOf {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : α → ℝ) : ℝ :=
  (∫ x, g x * Real.log (g x) ∂μ) - (∫ x, g x ∂μ) * Real.log (∫ x, g x ∂μ)
```
Note `entropyOf` is defined at line 392, before `section Riemannian`, so no reordering is needed. After the
`variable [IsRiemannianManifold ...]` line:
```lean
/-- **Riemannian `k₁` bounds** (manuscript lines 633–636): the first eigenspace is nonzero and
`k₁ ≤ dim M`. Hypotheses of Theorem 1.9 without the semigroup; `λ₁ = ρ` is needed for the upper bound
(on the round sphere `λ₁ = d` and `k₁ = d + 1`). -/
theorem riemannian_k1_bounds {V : M → ℝ} (hV : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ V)
    {μ : Measure M} [IsProbabilityMeasure μ] (hμ : IsWeightedVolume F μ V) {ρ : ℝ} (hρ : 0 < ρ)
    (hCD : CD F ρ V) (hgap : mSpectralGap F μ = ρ) :
    1 ≤ mFirstEigenDim F μ V ∧ mFirstEigenDim F μ V ≤ Module.finrank ℝ F := by
  sorry

/-- **Riemannian Poincaré and log-Sobolev inequalities** (manuscript lines 618–632): under `CD(ρ,∞)`,
`ρ Var_μ f ≤ ∫ |∇f|² dμ` and `Ent_μ(f²) ≤ (2/ρ) ∫ |∇f|² dμ` for smooth compactly supported `f`. -/
theorem riemannian_poincare_lsi {V : M → ℝ} (hV : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ V)
    {μ : Measure M} [IsProbabilityMeasure μ] (hμ : IsWeightedVolume F μ V) {ρ : ℝ} (hρ : 0 < ρ)
    (hCD : CD F ρ V) :
    ∀ f : M → ℝ, ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f → HasCompactSupport f →
      ρ * variance f μ ≤ ∫ x, ‖mgrad F f x‖ ^ 2 ∂μ ∧
      entropyOf μ (fun x => f x ^ 2) ≤ 2 / ρ * ∫ x, ‖mgrad F f x‖ ^ 2 ∂μ := by
  sorry
```
The `bochner_identity` and `CD_iff_ricci` block can be placed before the `[IsRiemannianManifold ...]` variable
line (they need none of its instances); the Paper versions use `CutCur.`-qualified names only.
Wiring in Solution: `exact CutoffRigidity.Paper.<name> F ...` (the Challenge defs equal the project's by `rfl`
for `mCurv`/`mHessSq`; the other defs are used directly).
Wiring caveat: when `entropyOf` is generalized, `Paper.riemannian_poincare_lsi` must use `entropyOf` instead of
`mEntropy` (one-word change; `mEntropy_eq_entropyOf` shows they agree on `Rd d`).
