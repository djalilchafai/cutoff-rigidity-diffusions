# diff-KUWB-HL: Hopf-Lax lemmas (DONE, no sorry, axioms propext/choice/Quot.sound)
Files: CutoffRigidity/Riemann/DiffHopfLax1.lean, DiffHopfLax2.lean, umbrella DiffHopfLax.lean.
Namespace CutoffRigidity.Riemann.Diff. Common hypotheses: hfin, hcpt : ∀ x R, IsCompact {y | dd x y ≤ R},
hh : LipschitzWith Λ h, hb : ∀ z, |h z| ≤ B, hr : 0 < r. Implicit {h Λ B r}.
- continuous_dd hfin : Continuous fun p : X×X => dd p.1 p.2 ; continuous_dd_left hfin y
- hlQ h r y := ⨅ z, h z + dd y z^2/(2r)
- hlQ_le hb hr y z : hlQ h r y ≤ h z + dd y z^2/(2r)
- opt_dist_le hfin hh hb hr (hz : hlQ h r y = h z + ...) : dd y z ≤ 2*r*Λ   (any optimal point)
- exists_opt : ∃ z, hlQ h r y = h z + dd y z^2/(2r) ∧ dd y z ≤ 2*r*Λ
- hlQ_le_self : hlQ h r y ≤ h y ; self_sub_le : h y - r*Λ^2/2 ≤ hlQ h r y ; abs_hlQ_le : |hlQ h r y| ≤ B
- hlQ_anti (hr : 0<r) (hrs : r ≤ s) : hlQ h s y ≤ hlQ h r y
- hlQ_sub_le_time (hs : 0<s) (hsr : s ≤ r) : hlQ h s y - hlQ h r y ≤ 2*Λ^2*(r/s)*(r-s)
- abs_hlQ_sub_le (0<r0) (r0≤s) (r0≤r) (r≤R) : |hlQ h r y - hlQ h s y| ≤ 4*Λ^2*(R/r0)*|r-s|
  (constant 4, not 2, because s is not assumed ≤ R)
- lipschitzWith_hlQ : ∃ C : ℝ≥0, LipschitzWith C (hlQ h r); continuous_hlQ; lipschitzWith_of_abs_le
- opt_dist_stable (Part 2): upper semicontinuity of optimal sets
- hlQ_hj : ∃ E : ℝ, 0 ≤ E ∧ lipAt (hlQ h r) y ≤ E / r ∧ ∀ s > r, hlQ h s y - hlQ h r y ≤ -(E^2*(s-r))/(2*r*s)
