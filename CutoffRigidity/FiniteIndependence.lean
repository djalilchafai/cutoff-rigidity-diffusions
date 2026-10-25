module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Separating independent coordinate pairs

Independent coordinate pairs whose two members are independently distributed
can be regrouped into two independent vectors. This is the probability
ingredient for collecting the scalar Brownian future/past identities into
the Euclidean driver used in the paper.
-/

public section

open MeasureTheory ProbabilityTheory

namespace CutoffRigidity

theorem independent_vectors_of_independent_coordinate_pairs
    {Ω ι A B : Type*} [MeasurableSpace Ω] [Fintype ι]
    [MeasurableSpace A] [MeasurableSpace B]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ι → Ω → A} {Y : ι → Ω → B}
    (hX : ∀ i, AEMeasurable (X i) P) (hY : ∀ i, AEMeasurable (Y i) P)
    (hPairs : iIndepFun (fun i ω => (X i ω, Y i ω)) P)
    (hXY : ∀ i, IndepFun (X i) (Y i) P) :
    IndepFun (fun ω i => X i ω) (fun ω i => Y i ω) P := by
  let μ : ι → Measure A := fun i => P.map (X i)
  let ν : ι → Measure B := fun i => P.map (Y i)
  have hμ (i : ι) : IsProbabilityMeasure (μ i) :=
    (Measure.isProbabilityMeasure_map_iff (hX i)).mpr inferInstance
  have hν (i : ι) : IsProbabilityMeasure (ν i) :=
    (Measure.isProbabilityMeasure_map_iff (hY i)).mpr inferInstance
  have : ∀ i, IsProbabilityMeasure (μ i) := hμ
  have : ∀ i, IsProbabilityMeasure (ν i) := hν
  have hPairLaw (i : ι) : HasLaw (fun ω => (X i ω, Y i ω)) ((μ i).prod (ν i)) P :=
    (hXY i).hasLaw_prod (hasLaw_map (hX i)) (hasLaw_map (hY i))
  have hAllPairs := hPairs.hasLaw_pi hPairLaw
  have hSwap := (measurePreserving_arrowProdEquivProdArrow A B ι μ ν).hasLaw
  have hAll := hSwap.comp hAllPairs
  have hIndepX : iIndepFun X P :=
    hPairs.comp (fun _ => Prod.fst) (fun _ => measurable_fst)
  have hIndepY : iIndepFun Y P :=
    hPairs.comp (fun _ => Prod.snd) (fun _ => measurable_snd)
  have hLawX : HasLaw (fun ω i => X i ω) (Measure.pi μ) P :=
    hIndepX.hasLaw_pi (fun i => hasLaw_map (hX i))
  have hLawY : HasLaw (fun ω i => Y i ω) (Measure.pi ν) P :=
    hIndepY.hasLaw_pi (fun i => hasLaw_map (hY i))
  exact (indepFun_iff_hasLaw_prodMk_prod hLawX hLawY).mpr hAll

end CutoffRigidity
