# geoA: Bochner identity and `CD(rho,inf)  <=>  Ric + Hess V >= rho g`

Bottom line: this item is DONE in scratch. A faithful Ricci tensor can be defined in Lean from Mathlib's
`leviCivitaConnection`, and the Bochner identity and the equivalence are proved. They follow from the project's
existing G2 development (`Riemann/WeightedBochner*.lean`) with about 110 lines of new glue. The scratch file
compiles with no `sorry` and the axioms are only `propext`, `Classical.choice`, `Quot.sound`.
Scratch file: `/tmp/claude-1000/-chome-djay-S--Publis-2025-CRAS-CF-lean/25ce202f-e16f-4c7d-901c-94cac4f5c39d/scratchpad/GeoA1.lean`
(it imports `CutoffRigidity.Riemann.WeightedBochnerMain`; `lake env lean` takes about 5 s).

## 1. Manuscript claim (`cutcur-lean.tex`)
* Lines 589-663 (subsection "Riemannian manifolds"), eq. `eq:BErho` at about 626: `Ric + Hess(V) >= rho g`.
* Lines 641-654: `Gamma(f,g) = 1/2(L(fg) - fLg - gLf)` boils down to `|grad f|^2`, and
  `Gamma_2(f) = Ric(grad f,grad f) + ||Hess f||_HS^2 + <Hess V grad f, grad f>`.
  The text says this follows from the Bochner formula `grad L = L grad - Hess(V) grad - Ric(grad,.)`.
* Lines 655-663: `CD(rho,n)` is `Gamma_2(f) >= rho Gamma(f) + (Lf)^2/n`. "Now CD(rho,inf) is equivalent to
  the curvature lower bound (eq:BErho). In the Euclidean case Ric = 0 and CD(rho,inf) says V is rho-convex."
* Claims to formalize:
  (a) the scalar Bochner identity `Gamma_2(f) = ||Hess f||^2 + (Ric + Hess V)(grad f, grad f)`;
  (b) `CD(rho,inf) <=> (Ric + Hess V)(v,v) >= rho g(v,v)` for all `x` and all `v` in `T_x M`.
* The vector-form Bochner formula `grad L = L grad - ...` is only quoted. It is not the claim used.
* The identification `Gamma(f,g) = 1/2(L(fg) - ...)` (scan item B5) is a separate Leibniz-rule statement.
  Challenge defines `carre` directly as `<grad f, grad g>`. It is not treated here (see section 5).

## 2. What Mathlib provides
* Mathlib has NO Riemann curvature, Ricci or curvature tensor. A grep for `riemannCurvature`, `Ricci` and
  `curvature` in `Mathlib/Geometry` and `Mathlib/Analysis` returns nothing.
* Mathlib has `CovariantDerivative.leviCivitaConnection` (with Koszul formula, torsion-freeness, metric
  compatibility), `mlieBracket` (with `mlieBracket_swap`), and `Trivialization.localFrame` (`LocalFrame.lean`).
  There is no smoothness theorem for the Levi-Civita connection and no tensoriality of curvature.

## 3. What the project provides (all proved, no sorry)
Challenge definitions `mgrad`, `mlaplacian`, `mgenerator`, `carre`, `carre2`, `CD` use the Levi-Civita
Hessian trace. In `CutoffRigidity/Riemann/`:
* `WeightedBochnerDefs`: `nab X Y`, `curv X Y Z x = nab_X nab_Y Z - nab_Y nab_X Z - nab_[X,Y] Z` (textbook `R(X,Y)Z`),
  `SmAt`, `NabSmooth`.
* `WeightedBochnerNabSmooth.nabSmooth`: `nab` of smooth fields is smooth.
* `WeightedBochnerHessian.hessian_symm`, `mvfderiv_mlieBracket`.
* `WeightedBochnerCurv`: tensoriality `curv_congr_left`, `curv_congr_right` (first and third arguments).
* `WeightedBochnerTrace`: `exists_frame_trace`, `msmooth_mlaplacian`.
* `WeightedBochnerQuad`: `carre2_eq`, i.e. `Gamma_2 = 1/2 Delta|grad f|^2 - d(Delta f)(grad f) + Hess V(grad f, grad f)`.
* `WeightedBochnerMain.carre2_sub_hess_eq`: `Gamma_2(f) - ||Hess f||^2 = -sum_i <curv(grad f, Z_i, grad f), e_i> + Hess V(grad f, grad f)`.
  This is Bochner with the Ricci trace written through `curv` and a smooth frame `Z_i`.
* `WeightedBochnerTest.exists_test_function`: for every `v` in `T_x M` there is a smooth `g` with
  `grad g(x) = v` and `Hess g(x) = 0`.
  The local-chart argument for prescribed 2-jets is already there (chart Christoffel correction times a bump).
* `WeightedBochnerMain.weightedBochnerIneq_of_CD`: only the one direction, with an abstract Ric.
  No `Ric` is defined as a named object, so the equivalence statement is missing.

## 4. Draft Lean statement (checked: elaborates and is proved)
Definitions (all in the Challenge `section Riemannian` context with the same `variable`s):
```lean
/-- smooth extension of a tangent vector (choice; only the value at x matters, see riem_indep) -/
noncomputable def ext (x : M) (v : TangentSpace 𝓘(ℝ,F) x) : (y : M) → TangentSpace 𝓘(ℝ,F) y :=
  Classical.choose (exists_ext F x v)   -- ∃ X, ContMDiffAt ... (T% X) x ∧ X x = v
noncomputable def riem (x) (a b c : TangentSpace 𝓘(ℝ,F) x) := curv F (ext F x a) (ext F x b) (ext F x c) x
noncomputable def ric (x) (v w) : ℝ := ∑ i, inner ℝ (riem F x (e i) v w) (e i)   -- e = stdOrthonormalBasis; Ric(v,w)=tr(a↦R(a,v)w)
noncomputable def hessV V x v w : ℝ := inner ℝ (leviCivitaConnection .. (mgrad F V) x v) w
noncomputable def ricV V x v w := ric F x v w + hessV F V x v w
```
with `curv X Y Z x := ∇_X∇_Y Z - ∇_Y∇_X Z - ∇_[X,Y] Z` (unfolded in a Challenge version).
Theorems, both proved in scratch:
```lean
theorem bochner {V f} (hV : MSmooth F V) (hf : MSmooth F f) (x) :
  carre2 F V f x = mHessNormSq F f x + ricV F V x (mgrad F f x) (mgrad F f x)
theorem CD_iff_ricV {V} (hV : MSmooth F V) (ρ : ℝ) :
  CD F ρ V ↔ ∀ x (v : TangentSpace 𝓘(ℝ,F) x), ρ * inner ℝ v v ≤ ricV F V x v v
```
`mHessNormSq` is `manifoldHessianNormSq`, which is `||Hess f||_HS^2` (sum of squared norms of `nabla_{e_i} grad f`).
* Hypotheses: only `hV : ContMDiff .. ∞ V`. It is necessary, because `Hess V` is junk otherwise. No completeness,
  connectedness, finite dimension or measure hypothesis.
  The manuscript assumes a smooth (not just C^2) Riemannian manifold and a smooth potential, so this is faithful.
* The proofs use `exists_ext` (smooth extension of a vector, via `Trivialization.localFrame` with constant
  coefficients; 12 lines, checked), `curv_swap` (from `mlieBracket_swap_apply`), `curv_tensor`
  (extension-independence in all three slots, from the project's `curv_congr_*`), then `bochner` from
  `carre2_sub_hess_eq` and `CD_iff_ricV` from `exists_test_function`.
* Faithfulness of Ric: `curv` is the textbook `R(X,Y)Z`, with Mathlib's Levi-Civita connection and
  `mlieBracket`. `ric(v,w) = tr(a -> R(a,v)w)` is the standard sign convention (positive on spheres).
  The sign is cross-checked by the proved Bochner identity, which has `+Ric`.
  Because `riem` is built from an arbitrary smooth extension, a reader must check independence of the extension
  (`curv_tensor`, which can be stated in the Challenge as a lemma-free remark).
* Choice-free variant for the Challenge (avoids `ext` and `Classical.choose`): state
  `CD ρ V ↔ ∀ x v (E : Fin n → fields) (X : field), SmAt ∧ E i x = e i ∧ X x = v → ρ‖v‖² ≤ Σ_i ⟨curv (E i) X X x, e_i⟩ + Hess V(v,v)`.
  This is as readable and needs the same proof, plus `curv_tensor` and the existence of extensions.
  A Challenge reviewer may prefer it because it has no `Classical.choose`.
* Not covered: the vector-form Bochner formula `grad L = L grad - Hess(V) grad - Ric(grad,.)`, and `CD(rho,n)`
  (Lean already has only the `n = inf` case in Challenge, as does the manuscript's use).

## 5. Effort and risk
* Already done in scratch: `ext`, `riem`, `ric`, `ricV`, `curv_swap`, `curv_tensor`, `bochner`, `CD_iff_ricV`,
  107 lines, compiles in seconds on top of the existing project build.
* To land as a Challenge theorem:
  - Add about 35 lines to `Challenge.lean` (currently 863 lines / 55 KB, limit 1000 lines / 100 KiB). The
    definitions `curv`, `riem`, `ric`, `hessV`, `ricV` go in the Riemannian section, and the theorem goes next to `CD`.
  - Mirror them in `Statements.lean`.
  - Port the scratch proofs into a `module`-style file under `CutoffRigidity/Riemann/` (for example
    `RicciEquiv.lean`, about 150 lines including headers), and state the matching `Paper.` theorem.
  - Expect 0.5 to 1 agent-day, with no new hard mathematics.
* Risks:
  - Challenge must be self-contained (imports only Mathlib). Everything needed (`mlieBracket`,
    `leviCivitaConnection`, `T%`) is in Mathlib, so this is fine.
  - The `Classical.choose` extension is the main reviewer-facing wrinkle; use the choice-free form if preferred.
  - The statement is only as faithful as `curv`. A sanity check that `curv` is tensorial (already proved as
    `curv_congr_*`, `curv_tensor`) and that the Bochner identity holds (proved) pins the definition down.
* Separate small item B5 (`Gamma(f,g) = 1/2(L(fg) - fLg - gLf)` for `carre`, i.e. Leibniz for `mlaplacian`:
  `Delta(fg) = f Delta g + g Delta f + 2<grad f, grad g>`): not attempted. Estimated 80-150 lines using the
  project's `mgrad_mul` and the frame-trace lemmas. It is independent of the Ricci equivalence.
* Euclidean case remark (scan A2/C4): with `M = Rd d` and Ric = 0 one would want `CD (Rd d) rho V <-> Hess V >= rho`.
  This is stated as `temperature_cd` in Challenge (line 741) and follows by applying `CD_iff_ricV` plus Ric = 0 for the
  flat metric (`WitnessBochner.gamma2_euclid` already gives `Gamma_2 = ||D^2 f||^2 + D^2 V(grad f, grad f)` for the flat case).

## 6. Recommendation
DO IT. Add Challenge theorem `CD_iff_ricV` (and, optionally, `bochner`) in the Riemannian section, with the Ricci
tensor defined from `leviCivitaConnection` via `curv`, in the choice-free form if the reviewers dislike
`Classical.choose`. It closes scan items B5 (equivalence part) and A2/C4, and it makes the docstring of `CD`
("equivalently Ric + Hess V >= rho g") an actual theorem. It is the cheapest of the geometric items, because the
G2 development already contains the whole proof. Do it before any item that would reuse Ric, and do the Leibniz
statement (B5) as a small follow-up if the full list of manuscript lines 641-654 is wanted.
