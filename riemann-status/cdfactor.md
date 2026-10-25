# cdfactor: splitting item S9 (CD(rho) on the level N)

Status: DONE, no sorry, axioms propext/Classical.choice/Quot.sound. Files (both build with `lake build`):
`CutoffRigidity/Riemann/CDFactorGrad.lean`, `CutoffRigidity/Riemann/CDFactorMain.lean`
(the lead must add `import CutoffRigidity.Riemann.CDFactorMain` to CutoffRigidity.lean).
No file of another agent was edited.

## Route
Not through Levi-Civita comparison (no Gauss formula / total geodesy needed). (I1) is pure linear algebra on tangent
spaces; (I2) is obtained by integration by parts on M and on N with test functions `chi(s) g(pi)` and the measure
factorization, which characterizes the generator.

## Declarations (namespace `CutCur.Frame`, `fr : Frame F M k`, `N = fr.Level`, `E' = LevelModel F (Rd k)`, pi = `fr.toLevel`)
CDFactorGrad:
* `dpi`, `norm_dpi`, `inner_split` (polarized Pythagoras `<v,w> = <ds v, ds w> + <dpi v, dpi w>`), `dsv_apply`, `dpi_X` (dpi kills X_i),
  `surjective_dpi` (via the section `y -> comp (sv x) y`), `mvfderiv_comp_toLevel`, `dsv_mgrad_comp`, `dpi_mgrad_comp`
  (dpi(grad(u' o pi)) = grad u').
* **(I1)** `carre_comp_toLevel`: `Gamma_M(u' o pi, w' o pi) x = Gamma_N(u', w') (pi x)` for smooth u', w' (all x in M).
* `carre_sv_comp_toLevel`: `Gamma_M(chi o s, u' o pi) = 0`.
CDFactorMain:
* `integral_sv_mul_toLevel`: `int chi(s x) h(pi x) dmu = (int chi dnu)(int h dmu')` from `hfact`.
* `hasCompactSupport_sv_mul_toLevel`, `nonpos_of_integral_test` (a continuous D orthogonal to all `chi(s) g(pi)` vanishes; uses only IsOpenPosMeasure of mu and the diffeo `splitEquiv`).
* **(I2)** `mgenerator_comp_toLevel`: `L_M^V (v' o pi) x = L_N^{V'} v' (pi x)`.
* **(S9)** `cd_level`:
  ```
  theorem cd_level {V} (hV : MSmooth F V) {mu} [IsFiniteMeasure mu] (hmu : IsWeightedVolume F mu V)
    {nu : Measure (Rd k)} [SFinite nu] {mu' : Measure fr.Level} [IsFiniteMeasure mu']
    {V' : fr.Level -> R} (hV' : MSmooth E' V') (hmu' : IsWeightedVolume E' mu' V')
    (hfact : mu.map fr.splitEquiv = nu.prod mu') {rho} (hCD : CD F rho V) : CD E' rho V'
  ```

## Interface needed from the `measure` agent (hypotheses of `cd_level`)
`hfact : mu.map fr.splitEquiv = gamma.prod mu'` (gamma = the Gaussian, any s-finite nu works), `IsFiniteMeasure mu'`
(probability), `IsWeightedVolume E' mu' V'`, `MSmooth V'` (V' = V o val + const). No relation between V and V' is
needed in the proof (it is forced by hfact + hmu + hmu'); the constant in V' is irrelevant. This is exactly the Challenge
conclusion items, so S8 feeds `cd_level` directly. rho > 0, hgap, completeness are not used by this step beyond the
instances of `Frame` (M complete Riemannian). `hV`/`hmu` are used for IBP on M (`weightedIBP_of_isWeightedVolume`), `hV'`/`hmu'` for IBP on N.
Instance facts used on N: `levelCharted`, `levelIsManifold`, `levelRiemannianBundle`, `levelIsContMDiffRiemannianBundle`; no completeness of N needed.
