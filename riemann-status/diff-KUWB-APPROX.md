# diff-KUWB-APPROX: DONE (no sorry; axioms propext, Classical.choice, Quot.sound)

Files: CutoffRigidity/Riemann/DiffKuwApprox1.lean, DiffKuwApprox2.lean, umbrella DiffKuwApprox.lean
(namespace CutoffRigidity.Riemann.Diff).

* `sharp_local_smooth` (hfin) (hfc : Continuous f) (hSo : IsOpen S) (hc : 0 ≤ c) (hr : 1 < r)
  (hS : ∀ w ∈ S, ∀ w' ∈ S, |f w - f w'| ≤ c * dd w w') (p) (hp : p ∈ S) :
  ∃ V, IsOpen V ∧ p ∈ V ∧ V ⊆ S ∧ (∃ K, IsCompact K ∧ V ⊆ K) ∧ ∀ δ > 0, ∃ g, (smooth at each x ∈ V) ∧
  (∀ x ∈ V, |g x - f x| ≤ δ) ∧ ∀ x ∈ V, ∀ v, |mvfderiv g x v| ≤ r^2 * c * ‖v‖
* `locLip_le_of_ball_subset`
* `sharpApprox_aux`, and
  `theorem sharpApprox [ConnectedSpace M] [CompleteSpace M] : SharpApprox F M`
  (standard variables incl. MeasurableSpace F, BorelSpace F; no MeasurableSpace M needed).
Proof: r = sqrt(1+η), θ = η/(2(1+η)), local constants locLip ψ p (ε/2) + θ on B(p,ε/2).
