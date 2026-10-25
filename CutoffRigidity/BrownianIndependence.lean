module

public import CutoffRigidity.Brownian
public import CutoffRigidity.FiniteIndependence
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Euclidean Brownian future increments and the past

The weak Markov property is obtained from the genuine real Brownian theorem,
independence of coordinate processes, and finite-product regrouping. The
uncountable raw path variables are shown a.e. measurable using continuous
modifications, so no path measurability premise is silently added.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace CutoffRigidity

theorem realBrownian_aemeasurable_path
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) : AEMeasurable (fun ω t => B t ω) P := by
  classical
  let g : Ω → C(ℝ, ℝ) := fun ω =>
    if h : Continuous (fun t => B t ω) then
      ⟨fun t => B t.toNNReal ω, h.comp continuous_real_toNNReal⟩ else 0
  have heq : (fun ω => fun t : ℝ≥0 => g ω (t : ℝ)) =ᵐ[P] (fun ω t => B t ω) := by
    filter_upwards [hB.cont] with ω hω
    funext t
    simp [g, hω]
  have heval (t : ℝ) : AEMeasurable (fun ω => g ω t) P := by
    apply (hB.aemeasurable t.toNNReal).congr
    filter_upwards [hB.cont] with ω hω
    simp [g, hω]
  have hgm : Measurable (fun ω : NullMeasurableSpace Ω P => g ω) := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact (heval t).nullMeasurable.measurable'
  have hgn : NullMeasurable g P := hgm
  have hgc : AEMeasurable (fun ω => fun t : ℝ≥0 => g ω (t : ℝ)) P :=
    (show Measurable (fun f : C(ℝ, ℝ) => fun t : ℝ≥0 => f (t : ℝ)) from
      Measurable.of_eval (fun t => ContinuousMap.measurable_eval (t : ℝ))).comp_aemeasurable
      hgn.aemeasurable
  exact hgc.congr heq

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

omit [Fintype ι] in
theorem IsEuclideanBrownian.shift
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ ι} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) (s : ℝ≥0) :
    IsEuclideanBrownian (fun t ω => B (s + t) ω - B s ω) P := by
  constructor
  · intro i
    change IsBrownianReal (fun t ω => B (s + t) ω i - B s ω i) P
    refine ⟨(hB.coordinate i).toIsPreBrownianReal.shift s, ?_⟩
    filter_upwards [(hB.coordinate i).cont] with ω hω
    exact (hω.comp (continuous_const.add continuous_id)).sub continuous_const
  · exact hB.independent.comp (fun _ f => fun t => f (s + t) - f s)
      (fun _ => by fun_prop)

/-- Future vector increments are independent from the whole vector past. -/
theorem IsEuclideanBrownian.indepFun_shift
    {B : ℝ≥0 → Ω → EuclideanSpace ℝ ι} {P : Measure Ω}
    (hB : IsEuclideanBrownian B P) (s : ℝ≥0) :
    IndepFun (fun ω t => B (s + t) ω - B s ω)
      (fun ω (t : Set.Iic s) => B t ω) P := by
  classical
  have : IsProbabilityMeasure P := hB.isProbabilityMeasure
  have hRaw (i : ι) : AEMeasurable (fun ω => fun t : ℝ≥0 => B t ω i) P :=
    realBrownian_aemeasurable_path (hB.coordinate i)
  have hX (i : ι) : AEMeasurable (fun ω => fun t : ℝ≥0 => B (s + t) ω i - B s ω i) P :=
    (show Measurable (fun f : ℝ≥0 → ℝ => fun t => f (s + t) - f s) by fun_prop).comp_aemeasurable
      (hRaw i)
  have hY (i : ι) : AEMeasurable (fun ω => fun t : Set.Iic s => B t ω i) P :=
    (show Measurable (fun f : ℝ≥0 → ℝ => fun t : Set.Iic s => f t) by fun_prop).comp_aemeasurable
      (hRaw i)
  have hPairs : iIndepFun
      (fun i ω => ((fun t : ℝ≥0 => B (s + t) ω i - B s ω i),
        (fun t : Set.Iic s => B t ω i))) P :=
    hB.independent.comp (fun _ f => ((fun t => f (s + t) - f s),
      (fun t : Set.Iic s => f t))) (fun _ => by fun_prop)
  have h := independent_vectors_of_independent_coordinate_pairs hX hY hPairs
    (fun i => (hB.coordinate i).indepFun_shift s)
  exact h.comp
    (φ := fun f t => WithLp.toLp 2 (fun i => f i t))
    (ψ := fun f t => WithLp.toLp 2 (fun i => f i t)) (by fun_prop) (by fun_prop)

end CutoffRigidity
