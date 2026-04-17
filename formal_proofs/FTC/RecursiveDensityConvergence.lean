/-
  FTC — Recursive Density Convergence
  Pinnacle Quantum Group — April 2026

  Proves convergence properties of fractal density functions.
  Key results: monotone bounded sequences converge, Triangle density
  is constant 1/n, Square density converges to 0.
  Reference: FTC README §3, RSSN Theorem 1
-/
import Mathlib

noncomputable section
open Filter Topology

namespace FTC.RecursiveDensityConvergence

/-! ## 1. Monotone Convergence of Density Ratios -/

theorem monotone_bounded_converges (f : ℕ → ℝ)
    (hmono : Antitone f) (hbound : ∀ n, 0 ≤ f n) :
    ∃ L : ℝ, Filter.Tendsto f Filter.atTop (nhds L) ∧ 0 ≤ L := by
  have hbdd : BddBelow (Set.range f) := ⟨0, by rintro _ ⟨n, rfl⟩; exact hbound n⟩
  exact ⟨iInf f, tendsto_atTop_iInf hmono, le_ciInf fun n => hbound n⟩

/-! ## 2. Triangle Density: Constant Ratio -/

def triangleF (n : ℕ) (i : ℕ) : ℝ := ↑n ^ i
def triangleG (n : ℕ) (i : ℕ) : ℝ := ↑n ^ (i + 1)

theorem triangle_ratio_constant (n : ℕ) (hn : 1 < n) (i : ℕ) :
    triangleF n i / triangleG n i = (1 : ℝ) / ↑n := by
  unfold triangleF triangleG
  rw [pow_succ]
  field_simp
  ring

theorem triangle_density_eq (n : ℕ) (hn : 1 < n) :
    Filter.Tendsto (fun i => triangleF n i / triangleG n i)
      Filter.atTop (nhds ((1 : ℝ) / ↑n)) := by
  simp_rw [triangle_ratio_constant n hn]
  exact tendsto_const_nhds

/-! ## 3. Square Density: Ratio Decreases to Zero -/

theorem geometric_ratio_to_zero (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Filter.Tendsto (fun n => r ^ n) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1

theorem square_density_vanishes (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (f : ℕ → ℝ) (hf : ∀ n, f n = c ^ n) :
    Filter.Tendsto f Filter.atTop (nhds 0) := by
  have : f = fun n => c ^ n := funext hf
  rw [this]
  exact geometric_ratio_to_zero c (le_of_lt hc0) hc1

/-! ## 4. Cauchy Criterion for Density -/

theorem cauchy_density_converges (f : ℕ → ℝ)
    (hcauchy : CauchySeq f) :
    ∃ L : ℝ, Filter.Tendsto f Filter.atTop (nhds L) :=
  cauchySeq_tendsto_of_isComplete (s := Set.univ) isComplete_univ
    (fun n => Set.mem_univ _) hcauchy |>.imp fun L hL => hL.2

/-! ## 5. Density Preserves Bounds Under Limits -/

theorem limit_preserves_lower_bound (f : ℕ → ℝ) (L : ℝ) (b : ℝ)
    (hf : Filter.Tendsto f Filter.atTop (nhds L))
    (hbound : ∀ n, b ≤ f n) : b ≤ L :=
  ge_of_tendsto hf (eventually_atTop.mpr ⟨0, fun n _ => hbound n⟩)

theorem limit_preserves_upper_bound (f : ℕ → ℝ) (L : ℝ) (b : ℝ)
    (hf : Filter.Tendsto f Filter.atTop (nhds L))
    (hbound : ∀ n, f n ≤ b) : L ≤ b :=
  le_of_tendsto hf (eventually_atTop.mpr ⟨0, fun n _ => hbound n⟩)

/-! ## 6. Convergence Rate Bound -/

theorem convergence_rate_geometric (f : ℕ → ℝ) (L r : ℝ) (C : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hC : 0 < C)
    (hrate : ∀ n, |f n - L| ≤ C * r ^ n) :
    Filter.Tendsto f Filter.atTop (nhds L) := by
  apply tendsto_of_norm_tendsto_zero
  apply squeeze_zero (fun n => abs_nonneg _) hrate
  have : Filter.Tendsto (fun n => C * r ^ n) Filter.atTop (nhds (C * 0)) :=
    Filter.Tendsto.const_mul (geometric_ratio_to_zero r hr0 hr1) C
  simp at this; exact this

end FTC.RecursiveDensityConvergence
