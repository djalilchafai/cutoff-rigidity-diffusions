# Workstream `diffusion`: uniqueness of the minimal diffusion (invariance, contraction, Mehler, gap attainment)

Verdict (honest): the three `TransportInputs` and `0 < mFirstEigenDim` are TRUE under the Challenge
hypotheses (no counterexample exists: see 2), but they are NOT provable with the tools in the project/Mathlib
within reach. Each needs one of: (a) parabolic/elliptic PDE regularity on manifolds, (b) the L2 spectral theory
of unbounded self-adjoint operators (Friedrichs extension, Hille-Yosida, essential self-adjointness with
elliptic regularity), (c) a second-order Laplacian comparison with smooth Lyapunov functions. None exists in
Mathlib; I estimate each at tens of thousands of lines. So `riemannian_wasserstein_estimate` cannot be closed
unconditionally in this project; an amendment is needed (section 5). What I could prove is recorded below.

## 1. Proved (file `CutoffRigidity/Riemann/DiffusionRegular.lean`, namespace `CutoffRigidity.Riemann`; lead must import it)
Builds with `lake build CutoffRigidity.Riemann.DiffusionRegular`; no sorry; axioms propext, Classical.choice, Quot.sound.
* `mgenerator_eq_zero_of_notMem_tsupport` : f smooth, x not in tsupport f => `mgenerator F V f x = 0`
  (locality of the Levi-Civita connection, `congr_of_eventuallyEq`).
* `hasCompactSupport_mgenerator`, `msmooth_mgenerator` (from G0), `exists_abs_mgenerator_le`: 𝓛f is smooth, compactly supported, bounded.
* `dynkin_bound` : `|∫ f dPt u y - f y| ≤ C * u` for every y, whenever `|𝓛f| ≤ C` (valid with the Bochner junk value too).
* `dynkin_lipschitz_step`, `dynkin_lipschitz`, `continuous_dynkin` : for `IsDiffusionSemigroup F V Pt`, f in C_c^infty, x fixed,
  `t ↦ ∫ f dPt t x` is Lipschitz (constant sup|𝓛f|), via the semigroup law and `Kernel.integral_comp`.
* `continuous_dynkin_integrand`, `dynkin_intervalIntegrable`, `hasDerivAt_dynkin` : the Dynkin integrand is continuous, hence NO
  junk value (non-integrable integrand = 0) can occur; `t ↦ Pt f(x)` is C^1 on (0,infinity) with derivative `Pt(𝓛f)(x)`.
  This settles the "Bochner junk" worry of transport.md section 1 (no pathological Pt from non-measurability in t).

## 2. Why no counterexample, and why uniqueness is genuinely needed
* Fixing x, nu_t = Pt(x,.) is a probability solution of the weak Fokker-Planck equation tested on C_c^infty, nu_0 = delta_x
  (P_0 = id follows from t = 0 in the identity). Everything is equivalent to uniqueness of such solutions.
* Without a curvature bound uniqueness fails (Feller: stochastically incomplete complete manifolds, process re-entering from
  infinity; the identity for functions vanishing near infinity does not see it). Under CD(rho,infty) (rho>0) plus completeness
  Bakry's non-explosion holds and uniqueness is true, so the Challenge is TRUE; but this is exactly the content of the missing theory.
  (In the application M = R^k x N is non-compact when k >= 1; N is an arbitrary complete CD(rho,infty) manifold.)
* The Euclidean part of the Challenge avoids the issue by giving an SDE solution `X` (pathwise uniqueness built in);
  the Riemannian statement abstracts to kernels, which is why the Riemannian one is strictly harder.

## 3. Architecture of the true proof and cost of each ingredient (investigated, not coded)
(a) Khasminskii tightness for ANY Pt (Dynkin only on C_c^infty), given a smooth proper phi >= 0 with
    `𝓛phi <= C(1+phi)` and `Γ(phi) <= C(1+phi)^2`. Test functions `chi_m(phi)` with log-scale cutoffs have
    `(𝓛 chi_m)^- <= C/log m` using ONLY the upper bound on 𝓛phi (chi' <= 0), so `P_t g_m(x) -> 1`; moment bound
    `∫ phi dPt(x,.) <= (phi(x)+Ct)e^{Ct}` from `theta_n(phi) chi_m`, theta_n concave bounded (the Γ-term has a sign), Gronwall, m then n -> infinity.
    Also `∫ |𝓛 chi_m| dPs -> 0` follows from `∫ P_s 𝓛chi_m = P_t chi_m - chi_m(x) -> 0` plus `(𝓛chi_m)^- -> 0`.
    This is elementary given the Lyapunov function, and uses the C^1 regularity of section 1. The Lyapunov function is the
    obstruction: it needs `Δ_V d <= C(1+d)` (Laplacian comparison for Ric_V >= rho via Bochner on the distance function, cut locus /
    barrier sense) and a smoothing that preserves one-sided 𝓛 bounds. The project has only first-order smooth cutoffs
    (`weightedCutoffs_of_complete`, ‖∇chi‖ <= 1/(n+1)); no second-order control. Not in Mathlib.
(b) Mehler law given (a): chain rule `𝓛(h∘T) = Σ ∂_i h(T) 𝓛T_i + Σ ∂_ij h Γ(T_i,T_j)` for T_i with parallel gradients (Leibniz for the
    Levi-Civita connection, `Γ(T_i,T_j) = ρ δ_ij`, `𝓛T_i = -ρ T_i`), then the time-dependent exact test function
    `exp(i e^{-ρ(t-s)}⟨ξ,T⟩ - ½(1-e^{-2ρ(t-s)})|ξ|²)` (needs a time-dependent Dynkin lemma, easy from section 1 plus
    chi_m cutoffs) and `Measure.ext_of_charFun`. All elementary (~1500 lines), but only after (a). Cutoff errors need (a).
(c) Invariance of μ and (d) W2 contraction: genuinely need uniqueness, i.e. regularity of the dual (backward) problem:
    duality `d/ds P_s(u_{t-s})(x) = 0` needs `u_s = e^{sL} g` smooth with 𝓛u_s controlled; the Dirichlet-form route
    gives conservativity from `1 ∈ D(E)` (first-order cutoffs, finite μ) but identifies Pt with e^{tL} only through smoothness of
    e^{sL}g (Sobolev embedding / elliptic regularity, absent) and needs essential self-adjointness (Gaffney with weak solutions =
    elliptic regularity again). Contraction additionally needs Γ(P_t f) <= e^{-2ρt} P_tΓ(f) (Bakry-Emery, requires P_t f smooth)
    plus Kuwada duality, or a coupling construction (SDE on manifolds). None available.
* An attempt to avoid uniqueness for (c) by the stationary-solution trick fails: `μ_t = μ.bind Pt` satisfies the weak FP equation
  `μ_t(f) = μ(f) + ∫_0^t μ_s(𝓛f) ds`, and `μ` is also a solution; uniqueness is the missing point and no L2/density information on μ_t is known.

## 4. `0 < mFirstEigenDim` (gap attainment)
Investigated: no cheaper route than discreteness of the spectrum (Rellich on H^1(μ) via Bakry-Emery LSI/Gaussian tails + local
Rellich + elliptic regularity to get a smooth eigenfunction). The splitting does not help (k = 0 means no eigenfunction, then
M = N and nothing is gained); Bochner `∫(𝓛f)^2 >= ρ∫Γ f` carries no information at the bottom of the spectrum; the ball refinement for
k = 0 is again the same theorem (it would need approximate eigenfunctions plus Mehler for them). Remains exactly the Prop of gap.md:
`∃ f, IsMEigenfunction F μ V ρ f ∧ ∃ x, f x ≠ 0` (`mFirstEigenDim_pos_iff`).

## 5. Recommended amendment (lead's decision; nothing else is blocked)
Minimal true properties of the minimal diffusion that make the proved assembly `riemannian_wasserstein_estimate_of_transport`
complete (all three are fields of `TransportInputs`, all true for the actual diffusion):
1. invariance `μ.bind (Pt t) = μ`  (implied by reversibility, `bind_eq_of_reversible`);
2. W2 contraction `W2Contraction (Pt t) (e^{-2ρt})` (implied by a coupling kernel, `w2Contraction_of_coupling`);
3. Mehler law of `proj` under `Pt t x₀`, equivalently (after (a),(b) above) Dynkin's identity extended to smooth functions with
   suitable growth.
plus `0 < mFirstEigenDim F μ V`. The cleanest amendment: add to the theorem the hypothesis `hinv`, `hcontr`, `hmehler` (or the single
`IsMinimalDiffusion`-type Prop packaging them) and `0 < mFirstEigenDim`; or strengthen `IsDiffusionSemigroup` with μ-reversibility
(and Dynkin's identity for bounded smooth f with bounded 𝓛f, which is true for the minimal diffusion by conservativity).
Section 1 shows the weak Dynkin identity alone behaves well (no junk, C^1 in t).
