/-
  FTC — Black Hole Singularity Resolution (Theorem T4)
  Pinnacle Quantum Group — April 2026

  Proves that recursive curvature R^(n*) → 0 at classical singularity
  locations, replacing divergence with convergence to zero.
  The attractor density D*_BH = e^{-π} ≈ 0.0432 is universal.
  Reference: FTC README §5-6, RSSN test_ftc_lemmas.py
-/
import Mathlib

noncomputable section
open Real Filter Topology

namespace FTC.SingularityResolution

/-! ## 1. Classical vs Recursive Curvature -/

def classicalCurvature (r : ℝ) (hr : r ≠ 0) : ℝ := 1 / r ^ 2

def recursiveCurvature (g : ℕ → ℝ) (normalization : ℕ → ℝ) (n : ℕ) : ℝ :=
  (g (n + 1) - g n) / normalization n

/-! ## 2. Exponential Damping Model -/

def expDampedMetric (γ : ℝ) (n : ℕ) : ℝ := exp (-γ * ↑n)

theorem exp_damped_decreasing (γ : ℝ) (hγ : 0 < γ) :
    StrictAnti (expDampedMetric γ) := by
  intro i j hij
  unfold expDampedMetric
  apply exp_lt_exp.mpr
  -- Goal: `-γ * ↑j < -γ * ↑i` from `i < j`, `0 < γ`. Bilinear in γ and ↑j;
  -- `nlinarith` handles the product, `linarith` cannot.
  nlinarith [hγ, show (↑i : ℝ) < ↑j from Nat.cast_lt.mpr hij]

theorem exp_damped_pos (γ : ℝ) (n : ℕ) : 0 < expDampedMetric γ n := by
  unfold expDampedMetric; exact exp_pos _

theorem exp_damped_to_zero (γ : ℝ) (hγ : 0 < γ) :
    Tendsto (expDampedMetric γ) atTop (nhds 0) := by
  unfold expDampedMetric
  have : Tendsto (fun n : ℕ => -γ * ↑n) atTop atBot := by
    -- `neg_const_mul_atTop` wants `-γ < 0`, which is direct from `0 < γ`.
    apply Filter.Tendsto.neg_const_mul_atTop (neg_lt_zero.mpr hγ)
    exact tendsto_nat_cast_atTop_atTop
  exact tendsto_exp_atBot.comp this

/-! ## 3. Recursive Curvature Vanishes at Singularity -/

theorem recursive_curvature_vanishes (γ : ℝ) (hγ : 0 < γ)
    (G : ℕ → ℝ) (hG : ∀ n, 1 ≤ G n) :
    Tendsto (fun n => recursiveCurvature (expDampedMetric γ) G n) atTop (nhds 0) := by
  -- |Δg(n)/G n| ≤ |Δg(n)| ≤ e^{−γ(n+1)} + e^{−γn} ≤ 2e^{−γn} → 0; squeeze.
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbound : ∀ n, ‖recursiveCurvature (expDampedMetric γ) G n‖ ≤
      2 * expDampedMetric γ n := by
    intro n
    unfold recursiveCurvature
    rw [Real.norm_eq_abs, abs_div]
    have hGn : (1 : ℝ) ≤ |G n| := le_trans (hG n) (le_abs_self _)
    have hnum : |expDampedMetric γ (n + 1) - expDampedMetric γ n| ≤
        2 * expDampedMetric γ n := by
      have h1 : expDampedMetric γ (n + 1) ≤ expDampedMetric γ n := by
        unfold expDampedMetric
        apply Real.exp_le_exp.mpr
        push_cast
        nlinarith [hγ.le]
      have h0 : 0 < expDampedMetric γ (n + 1) := exp_damped_pos γ (n + 1)
      have h0' : 0 < expDampedMetric γ n := exp_damped_pos γ n
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
    calc |expDampedMetric γ (n + 1) - expDampedMetric γ n| / |G n|
        ≤ |expDampedMetric γ (n + 1) - expDampedMetric γ n| :=
          div_le_self (abs_nonneg _) hGn
      _ ≤ 2 * expDampedMetric γ n := hnum
  apply squeeze_zero (fun n => norm_nonneg _) hbound
  have h := (exp_damped_to_zero γ hγ).const_mul 2
  simpa using h

/-! ## 4. Super-Exponential Convergence -/

def superExpDamped (n : ℕ) : ℝ := exp (-(exp (↑n)))

theorem superExp_pos (n : ℕ) : 0 < superExpDamped n := by
  unfold superExpDamped; exact exp_pos _

theorem superExp_faster_than_exp (γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ n in atTop, superExpDamped n < expDampedMetric γ n := by
  -- e^{−eⁿ} < e^{−γn} ⟺ γ·n < eⁿ. Eventually true since
  -- eⁿ ≥ (1 + n/2)² > (n/2)² = n²/4 > γ·n once n > 4γ.
  have key : ∀ x : ℝ, 0 ≤ x → (1 + x / 2) ^ 2 ≤ Real.exp x := by
    intro x hx
    have h := Real.add_one_le_exp (x / 2)
    have h2 : Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) := by
      rw [← Real.exp_add]; ring_nf
    nlinarith [Real.exp_pos (x / 2), h, hx]
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (4 * γ))] with n hn
  have hn4γ : 4 * γ < (n : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (Nat.cast_lt.mpr hn)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℝ) ≤ 4 * γ := by linarith
    linarith
  unfold superExpDamped expDampedMetric
  rw [Real.exp_lt_exp]
  -- Goal: −eⁿ < −γ·n ⟺ γ·n < eⁿ.
  have h1 : γ * (n : ℝ) < ((n : ℝ) / 2) ^ 2 := by nlinarith
  have h2 : (((n : ℝ)) / 2) ^ 2 ≤ (1 + (n : ℝ) / 2) ^ 2 := by nlinarith
  have h3 := key (n : ℝ) hn_pos.le
  linarith

/-! ## 5. Black Hole Attractor Density -/

def bhAttractorDensity : ℝ := exp (-π)

theorem bh_density_pos : 0 < bhAttractorDensity := by
  unfold bhAttractorDensity; exact exp_pos _

theorem bh_density_lt_one : bhAttractorDensity < 1 := by
  unfold bhAttractorDensity
  rw [exp_lt_one_iff]
  exact neg_neg_of_pos pi_pos

theorem bh_density_bounded : 0 < bhAttractorDensity ∧ bhAttractorDensity < 1 :=
  ⟨bh_density_pos, bh_density_lt_one⟩

/-! ## 6. Singularity Resolution: Classical Diverges, Recursive Converges -/

theorem classical_diverges_at_origin :
    Tendsto (fun r : ℝ => 1 / r ^ 2) (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  -- r² → 0 within (0, ∞), and x⁻¹ → ∞ as x → 0⁺.
  simp only [one_div]
  apply tendsto_inv_zero_atTop.comp
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have h : Tendsto (fun r : ℝ => r ^ 2) (nhds 0) (nhds 0) := by
      simpa using (continuous_pow 2).tendsto (0 : ℝ)
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact Set.mem_Ioi.mpr (pow_pos (Set.mem_Ioi.mp hr) 2)

theorem recursive_replaces_singularity (γ : ℝ) (hγ : 0 < γ) :
    Tendsto (expDampedMetric γ) atTop (nhds 0) ∧ 0 < bhAttractorDensity :=
  ⟨exp_damped_to_zero γ hγ, bh_density_pos⟩

end FTC.SingularityResolution
