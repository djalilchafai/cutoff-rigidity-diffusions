module
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

/-! # Exact geometric partitions for the written reciprocal-entropy argument

The geometric increment ratio is constant. Its vanishing-mesh limit is the
logarithmic interval length, with no entropy or diffusion assumptions.
-/
public section
namespace CutoffRigidity
open Filter Set
open scoped Topology

@[expose] noncomputable def salezGeometricRatio (L : ℝ) (n : ℕ) : ℝ :=
  1-Real.exp (-L/((n : ℝ)+1))

@[expose] noncomputable def salezGeometricTime (a b : ℝ) (n j : ℕ) : ℝ :=
  a*Real.exp ((j : ℝ)*Real.log (b/a)/((n : ℝ)+1))

theorem salezGeometricRatio_tendsto_zero (L : ℝ) :
    Tendsto (salezGeometricRatio L) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => 1-Real.exp (-L/((n : ℝ)+1))) atTop (𝓝 0)
  have hh : Tendsto (fun n : ℕ => -L/((n : ℝ)+1)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,one_mul,mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (-L)
  have he := (tendsto_const_nhds (x := (1 : ℝ))).sub (Real.continuous_exp.continuousAt.tendsto.comp hh)
  simpa only [Real.exp_zero,sub_self,Function.comp_def] using he

theorem salezGeometricRatio_pos {L : ℝ} (hL : 0 < L) (n : ℕ) :
    0 < salezGeometricRatio L n := by
  apply sub_pos.mpr
  apply Real.exp_lt_one_iff.mpr
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hL) (by positivity)

theorem salezGeometricRatio_scaled_tendsto {L : ℝ} (hL : 0 < L) :
    Tendsto (fun n : ℕ => ((n : ℝ)+1)*salezGeometricRatio L n) atTop (𝓝 L) := by
  have ht : Tendsto (fun n : ℕ => -L/((n : ℝ)+1)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,one_mul,mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (-L)
  have htNE : Tendsto (fun n : ℕ => -L/((n : ℝ)+1)) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht,Eventually.of_forall (fun n => by
      simpa only [mem_compl_iff,mem_singleton_iff] using
        div_ne_zero (neg_ne_zero.mpr hL.ne') (by positivity : (n : ℝ)+1 ≠ 0))⟩
  have hh := ((Real.hasDerivAt_exp 0).tendsto_slope.comp htNE).const_mul L
  convert! hh using 1
  · funext n
    simp only [Function.comp_def,slope_def_field,Real.exp_zero,sub_zero,salezGeometricRatio]
    field_simp
    ring
  · simp

theorem salezGeometricTime_zero (a b : ℝ) (n : ℕ) : salezGeometricTime a b n 0=a := by
  simp [salezGeometricTime]

theorem salezGeometricTime_terminal {a b : ℝ} (ha : 0 < a) (hab : a < b) (n : ℕ) :
    salezGeometricTime a b n (n+1)=b := by
  have hb : 0 < b := ha.trans hab
  have hN : (n : ℝ)+1 ≠ 0 := by positivity
  simp only [salezGeometricTime,Nat.cast_add,Nat.cast_one,mul_div_cancel_left₀ _ hN]
  rw [Real.exp_log (div_pos hb ha)]
  field_simp

theorem salezGeometricTime_pos {a b : ℝ} (ha : 0 < a) (n j : ℕ) :
    0 < salezGeometricTime a b n j := mul_pos ha (Real.exp_pos _)

theorem salezGeometricTime_mem_Icc {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (n j : ℕ) (hj : j ≤ n+1) : salezGeometricTime a b n j ∈ Icc a b := by
  have hb : 0 < b := ha.trans hab
  have hL : 0 < Real.log (b/a) := Real.log_pos ((one_lt_div ha).mpr hab)
  have hN : (0:ℝ) < n+1 := by positivity
  have hJ : (j : ℝ) ≤ (n : ℝ)+1 := by exact_mod_cast hj
  have hlow : 0 ≤ (j : ℝ)*Real.log (b/a)/((n : ℝ)+1) := by positivity
  have hhigh : (j : ℝ)*Real.log (b/a)/((n : ℝ)+1) ≤ Real.log (b/a) := by
    apply (div_le_iff₀ hN).mpr
    nlinarith
  constructor
  · have hh := Real.one_le_exp_iff.mpr hlow
    simpa only [salezGeometricTime,mul_one] using mul_le_mul_of_nonneg_left hh ha.le
  · have hh := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hhigh) ha.le
    rw [Real.exp_log (div_pos hb ha)] at hh
    simpa only [salezGeometricTime,mul_div_cancel₀ _ ha.ne'] using hh

theorem salezGeometricTime_strictMono {a b : ℝ} (ha : 0 < a) (hab : a < b) (n : ℕ) :
    StrictMono (salezGeometricTime a b n) := by
  intro i j hij
  apply mul_lt_mul_of_pos_left _ ha
  apply Real.exp_lt_exp.mpr
  apply (div_lt_div_iff_of_pos_right (by positivity : (0:ℝ)<n+1)).mpr
  exact mul_lt_mul_of_pos_right (by exact_mod_cast hij)
    (Real.log_pos ((one_lt_div ha).mpr hab))

theorem salezGeometricTime_increment_ratio {a b : ℝ} (ha : 0 < a)
    (n j : ℕ) :
    (salezGeometricTime a b n (j+1)-salezGeometricTime a b n j)/
      salezGeometricTime a b n (j+1)=salezGeometricRatio (Real.log (b/a)) n := by
  have ht := salezGeometricTime_pos (b := b) ha n (j+1)
  rw [sub_div,div_self ht.ne']
  congr 1
  change (a*Real.exp ((j : ℝ)*Real.log (b/a)/((n : ℝ)+1)))/
    (a*Real.exp (((j+1 : ℕ) : ℝ)*Real.log (b/a)/((n : ℝ)+1))) =
      Real.exp (-Real.log (b/a)/((n : ℝ)+1))
  rw [mul_div_mul_left _ _ ha.ne',← Real.exp_sub]
  congr 1
  push_cast
  ring

end CutoffRigidity
