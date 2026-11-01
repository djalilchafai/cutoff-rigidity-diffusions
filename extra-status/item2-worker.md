# Item 2 worker report (not reviewed by a human)

Files: CutoffRigidity/Extra/Item2a.lean, CutoffRigidity/Extra/Item2b.lean (both build with `lake build`; no sorry; all
theorems depend only on propext, Classical.choice, Quot.sound). No existing file edited. (c) not formalized.

## (a) PROVED (Item2a, namespace CutoffRigidity.Paper)
Manuscript (L640-654) defines Gamma(f,g) = (L(fg) - fLg - gLf)/2; project's `carre f g = <grad f, grad g>`. New:
- `carre_eq_operator (hf hg smooth) x : carre F f g x = (mgenerator F V (fun y => f y * g y) x - f x * mgenerator F V g x - g x * mgenerator F V f x)/2`
- `generator_mul : mgenerator F V (fun y => f y * g y) x = f x * mgenerator F V g x + g x * mgenerator F V f x + 2 * carre F f g x`
- `carre_mul_left'`, `carre_mul_right` (Leibniz Gamma(fg,h) = f Gamma(g,h) + g Gamma(f,h), both slots), `carre_symm`
- `generator_comp (hθ : ContDiff ℝ ∞ θ) : mgenerator F V (θ ∘ f) x = deriv θ (f x) * mgenerator F V f x + deriv (deriv θ) (f x) * carre F f f x`
- `carre_comp_left' : carre F (θ ∘ f) g x = deriv θ (f x) * carre F f g x`
- `carre_polarization : carre F f g x = (Gamma(f+g) - Gamma(f-g))/4` (manuscript L1417)
- `noncomputable def carre2Bil V f g x := (L Gamma(f,g) - Gamma(f,Lg) - Gamma(g,Lf))/2` and `carre2Bil_self : carre2Bil F V f f x = carre2 F V f x`
Note: statements carry section instance args `[MeasurableSpace F] [BorelSpace F] [MeasurableSpace M] [BorelSpace M]` (needed by upstream
Diff lemmas, unused mathematically; in Challenge's Riemannian section after the `variable [..MeasurableSpace M]` line they are in scope).
Hypotheses: smooth (ContMDiff ∞) f, g (V arbitrary in the Leibniz/diffusion identities, as mgenerator only uses grad V pointwise).

## (b) PROVED (Item2b)
The scalar `bochner_identity` already has `mHessSq` and `mRic` (it IS the contracted form). What the vector form adds: the identity
before contraction with grad f. Definitions (namespace CutoffRigidity.Paper, explicit Levi-Civita, frame via `mExt`):
- `mSecondDeriv F u X Y x = ∇_{X x}(∇_Y u) - ∇_{∇_{X x} Y} u`
- `mRoughLaplacian F u x = ∑ i, mSecondDeriv F u (mExt F x e_i) (mExt F x e_i) x`
- `mVecGenerator F V u x = mRoughLaplacian F u x - ∇_{∇V(x)} u`
Theorem:
```lean
theorem bochner_vector {V f : M → ℝ} (hV : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ V) (hf : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℝ) ∞ f)
    (x : M) (v : TangentSpace 𝓘(ℝ, F) x) :
    mvfderiv 𝓘(ℝ, F) (mgenerator F V f) x v =
      inner ℝ (mVecGenerator F V (mgrad F f) x) v - mHess F V x (mgrad F f x) v - mRic F x v (mgrad F f x)
```
i.e. d(Lf) = L_vec(grad f) - Hess V(grad f) - Ric(grad f) tested against v (manuscript: ∇L = L∇ - Hess(V)∇ - Ric(∇,.)).
Caveats: (1) Ric slot order is mRic x v (∇f x) (as derived); equals Ric(∇f, v) only if mRic is symmetric (symmetry of mRic not
proved in the project; fine for the contracted v = ∇f). (2) mRoughLaplacian uses the chart-constant frame mExt; frame independence is
not stated as a theorem (it holds, tensoriality of ∇², but only the mExt/frm germ equality `mSecondDeriv_mExt_eq` is proved).
Proof: existing WBoch machinery (mvfderiv_mlaplacian_frm trace derivative, Sx_sub_Sx, inner_Sx_symm, curv_tensor, hessian_symm) +
metric compatibility; helper lemmas `mExt_eventually_frm`, `mSecondDeriv_mExt_eq`, `curv_swap`.

## (c) NOT FORMALIZED (Rothaus remark, L816)
(VW part) ALREADY COVERED by `optimal_constants_extremal` (Challenge, proved in Solution): it gives optimalPI = 1/rho, optimalLSI = 2 optimalPI,
extremality of h = x1+...+xd for PI (0<var, var h = optimalPI * ∫|∇h|²) and, for every real alpha, extremality of exp(alpha h) for LSI with
all integrals finite. Nothing to add.
Rothaus (compact, C_LSI > 2 C_PI => LSI extremal exists): judged NOT feasible at reasonable cost. Needed: (i) compactness of
H¹ -> L² (exists in project as Rellich, DiffRellich*, used for gap_attained_of_compact) but ALSO compactness of H¹ -> L² log L / L^{2+ε}
(Sobolev embedding on a compact manifold; only Rn-chart Sobolev pieces exist, DiffSobolevRn*), (ii) the direct method for
the entropy functional in H¹ (lower semicontinuity, entropy of a weak limit), (iii) the key Rothaus step: excluding that minimizing
sequences converge to constants, via second-order expansion of Ent(1+εg)² at constants vs the PI constant, (iv) statement of
"extremal function" must be in H¹ (not smooth) so the project's smooth-test-function optimalLSI needs a density/identification
lemma, (v) Euler-Lagrange not needed for existence but needed if "extremal" is to mean a critical point/smooth. Estimate: 3000-6000
lines of new Lean, several weeks; also finiteness of the LSI constant on compact manifolds (itself Rothaus/BE-type input) must be
stated or proved. Recommend leaving as an explicitly-not-formalized remark (the manuscript flags it "famous alternative ... see [refs]").
