module
public import CutoffRigidity.TransportCouplingCompactness
public import CutoffRigidity.CompactTransportDuality
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Genuine compact nonexpansive exhaustion maps of Euclidean space -/
public section
namespace CutoffRigidity
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

@[expose] def euclideanClip (n : ℕ) (x : E) : E :=
  WithLp.toLp 2 (fun i => max (-((n:ℝ)+1)) (min ((n:ℝ)+1) (x i)))

@[expose] def euclideanClipBox (n : ℕ) : Set E :=
  {x | ∀ i, |x i| ≤ (n:ℝ)+1}

theorem euclideanClip_mem (n : ℕ) (x : E) : euclideanClip n x ∈ euclideanClipBox n := by
  intro i
  change |max (-((n:ℝ)+1)) (min ((n:ℝ)+1) (x i))| ≤ (n:ℝ)+1
  rw [abs_le]
  exact ⟨le_max_left _ _,max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (min_le_left _ _)⟩

theorem euclideanClip_lipschitz (n : ℕ) : LipschitzWith 1 (euclideanClip (d := d) n) := by
  have hs : LipschitzWith 1 (fun r : ℝ => max (-((n:ℝ)+1)) (min ((n:ℝ)+1) r)) := by
    simpa only [min_comm,id_eq] using
      ((LipschitzWith.id.min_const ((n:ℝ)+1)).const_max (-((n:ℝ)+1)))
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul,dist_eq_norm]
  have hSq : ‖euclideanClip n x-euclideanClip n y‖^2 ≤ ‖x-y‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_le_sum
    intro i hi
    have hh := hs.norm_sub_le (x i) (y i)
    simp only [NNReal.coe_one,one_mul] at hh
    have hh2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hh
    simpa only [euclideanClip,WithLp.ofLp_toLp,PiLp.sub_apply,Real.norm_eq_abs,sq_abs] using hh2
  nlinarith [norm_nonneg (euclideanClip n x-euclideanClip n y),norm_nonneg (x-y)]

theorem euclideanClip_eq_self (n : ℕ) (x : E) (hx : ‖x‖ ≤ (n:ℝ)+1) :
    euclideanClip n x = x := by
  ext i
  have hi : |x i| ≤ (n:ℝ)+1 := (PiLp.norm_apply_le x i).trans hx
  change max (-((n:ℝ)+1)) (min ((n:ℝ)+1) (x i)) = x i
  rw [min_eq_right (abs_le.mp hi).2,max_eq_right (abs_le.mp hi).1]

theorem euclideanClip_eventually_eq (x : E) : ∀ᶠ n in atTop, euclideanClip n x = x := by
  have he : ∀ᶠ n : ℕ in atTop, ‖x‖ ≤ (n:ℝ)+1 :=
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).eventually_ge_atTop ‖x‖
  exact he.mono (fun n hn => euclideanClip_eq_self n x hn)

theorem euclideanClipBox_isCompact (n : ℕ) : IsCompact (euclideanClipBox (d := d) n) := by
  have hClosed : IsClosed (euclideanClipBox (d := d) n) := by
    have hh := isClosed_iInter (fun i : Fin d =>
      isClosed_le ((EuclideanSpace.proj i).continuous.abs) (continuous_const (y := (n:ℝ)+1)))
    convert! hh using 1
    ext x; simp only [euclideanClipBox,mem_setOf_eq,mem_iInter]; rfl
  have hBound : euclideanClipBox (d := d) n ⊆ Metric.closedBall (0 : E) (((d:ℝ)+1)*((n:ℝ)+1)) := by
    intro x hx
    rw [Metric.mem_closedBall,dist_zero_right]
    have hs : ‖x‖^2 ≤ (d:ℝ)*((n:ℝ)+1)^2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      calc
        _ ≤ ∑ i : Fin d, ((n:ℝ)+1)^2 := by
          apply Finset.sum_le_sum
          intro i hi
          have hh := hx i
          have hh2 := (sq_le_sq₀ (abs_nonneg (x i)) (by positivity : (0:ℝ) ≤ n+1)).mpr hh
          simpa only [sq_abs] using hh2
        _ = _ := by simp
    have hd := Nat.cast_nonneg (α := ℝ) d
    have hn := Nat.cast_nonneg (α := ℝ) n
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity : (0:ℝ) ≤ ((d:ℝ)+1)*((n:ℝ)+1))).mp
    apply hs.trans
    nlinarith [mul_nonneg (sq_nonneg (d:ℝ)) (sq_nonneg ((n:ℝ)+1)),
      mul_nonneg hd (sq_nonneg ((n:ℝ)+1))]
  exact (isCompact_closedBall (0 : E) _).of_isClosed_subset hClosed hBound

/-- Actual clipping transports every probability law weakly to itself. -/
theorem tendsto_probabilityMeasure_map_euclideanClip (μ : ProbabilityMeasure E) :
    Tendsto (fun n => μ.map (euclideanClip n)) atTop (𝓝 μ) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have hh : Tendsto (fun n => ∫ x,f (euclideanClip n x) ∂(μ : Measure E)) atTop
      (𝓝 (∫ x,f x ∂(μ : Measure E))) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
    · intro n
      exact (f.continuous.comp (euclideanClip_lipschitz n).continuous).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact Eventually.of_forall (fun x => f.norm_coe_le_norm _)
    · filter_upwards with x
      exact tendsto_const_nhds.congr' ((euclideanClip_eventually_eq x).mono (fun n hn => congrArg f hn.symm))
  convert! hh using 1
  ext n
  exact integral_map (euclideanClip_lipschitz n).continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable

end CutoffRigidity
