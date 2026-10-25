module
public import CutoffRigidity.CompactTransportDuality
public import CutoffRigidity.CompactLipschitzApproximation

/-! # Compact strong transport duality with genuine Lipschitz tests -/
public section
namespace CutoffRigidity
open MeasureTheory Set
open scoped Topology NNReal
variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] [MetricSpace Y] [CompactSpace Y]
  [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]

theorem integral_continuous_le_of_uniform_approx
    (μ : Measure X) [IsProbabilityMeasure μ] (f g : C(X,ℝ))
    (δ : ℝ) (hδ : ∀ x, |g x-f x| < δ) :
    (∫ x,f x ∂μ) ≤ (∫ x,g x ∂μ)+δ := by
  have hi : (∫ x,f x ∂μ) ≤ ∫ x,g x+δ ∂μ := integral_mono
    (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((g.continuous.add continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (fun x => by have hh := (abs_lt.mp (hδ x)).1; linarith)
  rw [integral_add (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (integrable_const δ)] at hi
  simpa using hi

set_option maxHeartbeats 800000 in
/-- Actual uniform approximation discharges the full continuous dual budget
using only actual Lipschitz dual tests. -/
theorem continuous_transport_dual_budget_of_lipschitz
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (c : C(X×Y,ℝ)) (K : ℝ)
    (hDual : ∀ (f : C(X,ℝ)) (g : C(Y,ℝ)) (L J : ℝ≥0),
      LipschitzWith L f → LipschitzWith J g →
      (∀ x y, f x+g y ≤ c (x,y)) → (∫ x,f x ∂μ)+(∫ y,g y ∂ν) ≤ K) :
    ∀ (f : C(X,ℝ)) (g : C(Y,ℝ)),
      (∀ x y,f x+g y ≤ c (x,y)) → (∫ x,f x ∂μ)+(∫ y,g y ∂ν) ≤ K := by
  intro f g hfg
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε/4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨f',L,hL,hf⟩ := exists_lipschitz_near_compact_continuous f δ hδ
  obtain ⟨g',J,hJ,hg⟩ := exists_lipschitz_near_compact_continuous g δ hδ
  let f0 : C(X,ℝ) := f'-ContinuousMap.const X (2*δ)
  have hL0 : LipschitzWith L f0 := by
    convert! hL.sub (LipschitzWith.const (2*δ)) using 1
    simp only [add_zero]
  have hfg' (x : X) (y : Y) : f0 x+g' y ≤ c (x,y) := by
    have h1 := (abs_lt.mp (hf x)).2
    have h2 := (abs_lt.mp (hg y)).2
    have hh := hfg x y
    change f' x-2*δ+g' y ≤ c (x,y)
    linarith
  have hd := hDual f0 g' L J hL0 hJ hfg'
  have hf0 : (∫ x,f0 x ∂μ) = (∫ x,f' x ∂μ)-2*δ := by
    change (∫ x,f' x-2*δ ∂μ) = _
    rw [integral_sub (f'.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (integrable_const (2*δ))]
    simp
  rw [hf0] at hd
  have hif := integral_continuous_le_of_uniform_approx μ f f' δ hf
  have hig := integral_continuous_le_of_uniform_approx ν g g' δ hg
  dsimp [δ] at hd hif hig
  linarith

theorem exists_compact_transport_coupling_of_lipschitz_dual_budget
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (c : C(X×Y,ℝ)) (K : ℝ)
    (hDual : ∀ (f : C(X,ℝ)) (g : C(Y,ℝ)) (L J : ℝ≥0),
      LipschitzWith L f → LipschitzWith J g →
      (∀ x y, f x+g y ≤ c (x,y)) → (∫ x,f x ∂μ)+(∫ y,g y ∂ν) ≤ K) :
    ∃ π : Measure (X×Y), IsProbabilityMeasure π ∧ π.map Prod.fst = μ ∧
      π.map Prod.snd = ν ∧ (∫ z,c z ∂π) ≤ K :=
  exists_compact_transport_coupling_of_dual_budget μ ν c K
    (continuous_transport_dual_budget_of_lipschitz μ ν c K hDual)

end CutoffRigidity
