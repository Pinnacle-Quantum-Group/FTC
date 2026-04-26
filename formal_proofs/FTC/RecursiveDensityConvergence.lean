/-
  FTC — Recursive Density Convergence [REVISED]
  Pinnacle Quantum Group — April 2026

  REVISION: Filled convergence_rate_geometric using Metric.tendsto_atTop.
  Reference: FTC README §3, RSSN Theorem 1
-/
import Mathlib

noncomputable section
open Filter Topology

namespace FTC.RecursiveDensityConvergence

/-! ## 1. Monotone Convergence -/

theorem monotone_bounded_converges (f : ℕ → ℝ)
    (hmono : Antitone f) (hbound : ∀ n, 0 ≤ f n) :
    ∃ L : ℝ, Filter.Tendsto f Filter.atTop (nhds L) ∧ 0 ≤ L := by
  refine ⟨iInf f, tendsto_atTop_iInf hmono, ?_⟩
  exact le_ciInf fun n => hbound n

/-! ## 2. Triangle Density: Constant Ratio -/

def triangleF (n : ℕ) (i : ℕ) : ℝ := ↑n ^ i
def triangleG (n : ℕ) (i : ℕ) : ℝ := ↑n ^ (i + 1)

theorem triangle_ratio_constant (n : ℕ) (hn : 1 < n) (i : ℕ) :
    triangleF n i / triangleG n i = (1 : ℝ) / ↑n := by
  unfold triangleF triangleG
  rw [pow_succ]
  have hn_pos : (0 : ℝ) < ↑n := by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num : 0 < 1) (le_of_lt hn)
  field_simp

theorem triangle_density_eq (n : ℕ) (hn : 1 < n) :
    Filter.Tendsto (fun i => triangleF n i / triangleG n i)
      Filter.atTop (nhds ((1 : ℝ) / ↑n)) := by
  simp_rw [triangle_ratio_constant n hn]
  exact tendsto_const_nhds

/-! ## 3. Geometric Decay -/

theorem geometric_ratio_to_zero (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Filter.Tendsto (fun n => r ^ n) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1

theorem square_density_vanishes (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (f : ℕ → ℝ) (hf : ∀ n, f n = c ^ n) :
    Filter.Tendsto f Filter.atTop (nhds 0) := by
  have heq : f = fun n => c ^ n := funext hf
  rw [heq]
  exact geometric_ratio_to_zero c (le_of_lt hc0) hc1

/-! ## 4. Limit Preserves Bounds -/

theorem limit_preserves_lower_bound (f : ℕ → ℝ) (L : ℝ) (b : ℝ)
    (hf : Filter.Tendsto f Filter.atTop (nhds L))
    (hbound : ∀ n, b ≤ f n) : b ≤ L :=
  ge_of_tendsto hf (eventually_atTop.mpr ⟨0, fun n _ => hbound n⟩)

theorem limit_preserves_upper_bound (f : ℕ → ℝ) (L : ℝ) (b : ℝ)
    (hf : Filter.Tendsto f Filter.atTop (nhds L))
    (hbound : ∀ n, f n ≤ b) : L ≤ b :=
  le_of_tendsto hf (eventually_atTop.mpr ⟨0, fun n _ => hbound n⟩)

/-! ## 5. Geometric Convergence Rate (FILLED) -/

theorem convergence_rate_geometric (f : ℕ → ℝ) (L r : ℝ) (C : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hC : 0 < C)
    (hrate : ∀ n, |f n - L| ≤ C * r ^ n) :
    Filter.Tendsto f Filter.atTop (nhds L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hpow : Tendsto (fun n : ℕ => C * r ^ n) atTop (nhds 0) := by
    have := geometric_ratio_to_zero r hr0 hr1
    have := this.const_mul C
    simpa using this
  rw [Metric.tendsto_atTop] at hpow
  obtain ⟨N, hN⟩ := hpow ε hε
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq]
  have hbnd := hN n hn
  rw [Real.dist_eq, sub_zero] at hbnd
  have hpos : 0 ≤ C * r ^ n := mul_nonneg (le_of_lt hC) (pow_nonneg hr0 n)
  rw [abs_of_nonneg hpos] at hbnd
  calc |f n - L| ≤ C * r ^ n := hrate n
    _ < ε := hbnd

/-! ## 6. Cauchy Density Converges -/

theorem cauchy_density_converges (f : ℕ → ℝ) (hcauchy : CauchySeq f) :
    ∃ L : ℝ, Filter.Tendsto f Filter.atTop (nhds L) :=
  cauchySeq_tendsto_of_complete hcauchy

end FTC.RecursiveDensityConvergence
