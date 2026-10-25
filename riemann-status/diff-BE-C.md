# diff-BE-C: DiffBESemi (abstract Kk with KerCanonical) -- DONE

Fully proved, no sorry/axiom in own files; `#print axioms` = propext, Classical.choice, Quot.sound.
Statements of the stub unchanged (only imports added).

Files (CutoffRigidity/Riemann/):
* DiffBESemi1 : sup-norm Lipschitz (`semi_lip`) and Taylor (`semi_taylor`) in time via hasDerivAt_dynkin + mean value inequality.
* DiffBESemi2 : `energy_bound` (int Gamma v <= ||v|| ||Lv|| mu(M), via integral_carre_cross), AM-GM L1 bound for Gamma(a,b),
                `integral_abs_carre_sub_le`, `integral_abs_carre_deriv_le`.
* DiffBESemi3 : abstract L1 lemmas `sqrt_L1_deriv` (needs extra integrability hyps hGhi hG0i), `hasDerivAt_integral_mul_L1`.
* DiffBESemi4 : remainder bounds along the path. DiffBESemi5 : L1 Lipschitz of Gamma(K_tau f), sqrt(.+eps); `Afun_lip`.
* DiffBESemi  : `inS_semi`, `semi_nonneg`, `integral_semi`, `hasDerivAt_Afun`, `continuousOn_Afun`.
Notes: `A` is in fact globally Lipschitz on R; no endpoint analysis needed. `hasDerivAt_Afun` does not use `hs`/`hst` beyond 0<s<t.
