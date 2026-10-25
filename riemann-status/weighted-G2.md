# G2: `weightedBochnerIneq_of_CD` (Bochner inequality from the Challenge `CD`)

Goal: `theorem weightedBochnerIneq_of_CD {V} (hV : MSmooth F V) {ρ} (hCD : CD F ρ V) : CutCur.WeightedBochnerIneq F V ρ`.

## Route (no curvature tensor in Mathlib; we use a *curvature expression* `curv`)
Notation: `u = ∇f`, `A = ∇u` (Hessian endomorphism), `∇_X Y = nab X Y`, `S(X,Y) = ∇_X(∇_Y u) - ∇_{∇_X Y} u`,
`curv X Y Z = ∇_X∇_Y Z - ∇_Y∇_X Z - ∇_{[X,Y]} Z`, `e_i` = `stdOrthonormalBasis` of `T_xM`, `Z_i` smooth fields with `Z_i x = e_i`.

1. (P2, `mlaplacian_carre_self`) `½ Δ|u|²(x) = Σ_i ⟨S(Z_i,Z_i),u⟩ + |∇_{e_i}u|²`.
2. (P3, `exists_frame_trace`) trace derivative: `d(Δf)(v) = Σ_i ⟨∇_v∇_{Z_i}u - ∇_{∇_v Z_i}u, e_i⟩`
   (frame = Mathlib local frame of the chart trivialization; trace = Σ of frame coefficients).
3. (V-terms, `carre2_eq`) `Γ₂(f)(x) = ½Δ(Γf)(x) - d(Δf)(u x) + Hess V(u,u)` (uses Hessian symmetry).
4. Hessian symmetry (`hessian_symm`) from torsion-freeness + `[X,Y]φ = X(Yφ)-Y(Xφ)` (`mvfderiv_mlieBracket`).
5. Ricci: `S(X,Y) - S(Y,X) = curv X Y u` (torsion-free), and `⟨S(X,Y),Z⟩ = ⟨S(X,Z),Y⟩` (differentiate
   the symmetry of `A` along `X`). Hence
   `Γ₂(f)(x) - ‖Hess f‖²(x) = -Σ_i ⟨curv u Z_i u (x), e_i⟩ + Hess V(u,u)`.
6. (`curv_congr_left/right`) `curv X Y Z x` depends only on `X x`, `Z x` (tensoriality; proven by hand with
   smooth germs since Mathlib's `TensorialAt` needs only-differentiable sections).
   So `D(f)(x) := Γ₂(f)(x) - ‖Hess f‖²(x) = Ψ_x(∇f(x))` for a function `Ψ_x` of `T_xM` (via extension of the vector).
7. (`exists_test_function`) for `v ∈ T_xM` a smooth `g` on `M` with `∇g(x)=v`, `Hess g(x)=0`
   (chart Christoffel quadratic correction times a bump).
8. Conclusion: `Γ₂(f)(x) = ‖Hess f‖² + Ψ(∇f x) = ‖Hess f‖² + Γ₂(g)(x) ≥ ‖Hess f‖² + ρ Γ(g)(x) = ‖Hess f‖² + ρΓ(f)(x)`.
9. Smoothness input (`nabSmooth : NabSmooth F M`): `∇_X Y` smooth for smooth fields (Koszul + chart frame).

Statements of all pieces: `riemann-status/weighted-G2-statements.txt` (typechecked with `sorry`).
Files: `CutoffRigidity/Riemann/WeightedBochner{Defs,Hessian,Test,Curv,Trace,Quad,NabSmooth,Main}.lean`.

## STATUS: DONE (all pieces compiled, no sorry; axioms: propext, Classical.choice, Quot.sound)
Final: `CutCur.weightedBochnerIneq_of_CD (F) {V} (hV : MSmooth F V) {ρ} (hCD : CD F ρ V) : WeightedBochnerIneq F V ρ`
(also `CutCur.WBoch.weightedBochnerIneq_of_CD`) in `CutoffRigidity/Riemann/WeightedBochnerMain.lean`.
Pieces: Defs (nab, curv, SmAt, NabSmooth), NabSmooth (`nabSmooth`), Hessian (`mvfderiv_mlieBracket`,
`hessian_eq_fields`, `hessian_symm`), Curv (`curv_congr_left/right`), Trace (`exists_frame_trace`,
`msmooth_mlaplacian`), Quad (`mlaplacian_carre_self`, `carre2_eq`), Test (`exists_test_function`),
Main (`Sx_sub_Sx`, `inner_Sx_symm`, `carre2_sub_hess`, `carre2_sub_hess_eq`).
By-products: Hessian symmetry `hessian_symm`; `[X,Y]φ = X(Yφ)-Y(Xφ)` on manifolds; Gamma_2 formula
`carre2_eq`; smoothness of the Levi-Civita derivative of smooth fields (`nabSmooth`); smoothness of `mlaplacian`.
No Challenge definition obstructs any step. No upstream file was edited.
