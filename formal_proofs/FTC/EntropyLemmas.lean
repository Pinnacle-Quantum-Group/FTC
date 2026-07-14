/-
  FTC — Entropy Lemmas (T6: L6.1–L6.3)
  Pinnacle Quantum Group — April 2026

  L6.1: Shannon axiom compliance (revised: weighted additivity)
  L6.2: Classical limit — recursive entropy of a depth density padded with
        the "certain" value 1 equals Shannon entropy at depth N (a genuine
        bridge between the ℕ-indexed and Fin-indexed entropy sums)
  L6.3: Bekenstein bound — at η=1: S = π nats per DOF, and the capacity
        2π is derived as 2 × (states × per-state entropy); the factor 2
        (two DOF) remains a modeling input
  Reference: LEMMA_DERIVATIONS.md FTC T6
-/
import Mathlib

noncomputable section
open Real BigOperators Finset

namespace FTC.EntropyLemmas

/-! ## L6.1 — Shannon Axiom Compliance -/

def recursiveEntropy (D : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n in Finset.range N, D n * log (1 / D n)

theorem L6_1_nonneg (D : ℕ → ℝ) (N : ℕ)
    (hD_pos : ∀ n, 0 < D n) (hD_le : ∀ n, D n ≤ 1) :
    0 ≤ recursiveEntropy D N := by
  unfold recursiveEntropy
  apply Finset.sum_nonneg
  intro n _
  apply mul_nonneg (le_of_lt (hD_pos n))
  rw [one_div]; exact log_nonneg (one_le_inv (hD_pos n) (hD_le n))

/-- Each summand `x · log (1/x)` of `recursiveEntropy` is at most `1/2` for
    every `x > 0` (no upper bound on `x` is needed: for `x ≥ 1` the term is
    nonpositive). The sharp constant is `1/e ≈ 0.368`; `1/2` suffices here and
    follows from the elementary bound `log t ≤ t/2`, itself a consequence of
    `log s ≤ s − 1` applied at `s = t/2` together with `log 2 ≤ 1`. -/
theorem entropy_term_le_half {x : ℝ} (hx : 0 < x) :
    x * log (1 / x) ≤ 1 / 2 := by
  have hlog_half : ∀ t : ℝ, 0 < t → log t ≤ t / 2 := by
    intro t ht
    have h1 : log (t / 2) ≤ t / 2 - 1 := log_le_sub_one_of_pos (by positivity)
    have h2 : log 2 ≤ (2 : ℝ) - 1 := log_le_sub_one_of_pos (by norm_num)
    have h3 : log t = log (t / 2) + log 2 := by
      rw [← log_mul (by positivity) (by norm_num)]
      norm_num
    linarith
  have hinv : 0 < 1 / x := by positivity
  calc x * log (1 / x) ≤ x * ((1 / x) / 2) :=
        mul_le_mul_of_nonneg_left (hlog_half _ hinv) hx.le
    _ = 1 / 2 := by field_simp

/-- **L6.1 maximality (corrected, strengthened).** The original statement
    required only `0 < N`, but it is FALSE at `N = 1`: taking `D 0 = e⁻¹` gives
    `recursiveEntropy D 1 = e⁻¹ > 0 = 1 · log 1`. (The densities `D n` are not
    constrained to sum to 1, so the `N = 1` sum can be positive while the bound
    is zero.) For `N ≥ 2` the bound holds for *every* positive density — no
    upper bound `D n ≤ 1` is needed: every term is `≤ 1/2`
    (`entropy_term_le_half`) and `1/2 ≤ log 2 ≤ log N`, so the sum is at most
    `N · log N`. -/
theorem L6_1_maximality (N : ℕ) (hN : 2 ≤ N) :
    ∀ (D : ℕ → ℝ), (∀ n, 0 < D n) →
    recursiveEntropy D N ≤ ↑N * log ↑N := by
  intro D hpos
  unfold recursiveEntropy
  have hlogN : (1 : ℝ) / 2 ≤ log ↑N := by
    have h2N : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hN_pos : (0 : ℝ) < (N : ℝ) := by linarith
    have hlog2 : (1 : ℝ) / 2 ≤ log 2 := by
      -- log (1/2) ≤ 1/2 − 1 = −1/2, and log (1/2) = −log 2.
      have h := log_le_sub_one_of_pos (show (0:ℝ) < 1 / 2 by norm_num)
      -- Rewrite only the log-term (a bare `one_div` would also rewrite the
      -- 1/2 on the right-hand side, desyncing the atoms for linarith).
      have hl : log (1 / 2 : ℝ) = -log 2 := by rw [one_div, log_inv]
      rw [hl] at h
      linarith
    -- log is monotone on the positives (via exp/log inversion; the named
    -- helper `log_le_log_of_le` lives later in this file, so inline it).
    have hmono : log 2 ≤ log ↑N := by
      rw [← Real.exp_le_exp, Real.exp_log (by norm_num : (0:ℝ) < 2),
        Real.exp_log hN_pos]
      exact h2N
    linarith
  have hterm : ∀ n ∈ Finset.range N, D n * log (1 / D n) ≤ log ↑N := fun n _ =>
    le_trans (entropy_term_le_half (hpos n)) hlogN
  calc ∑ n in Finset.range N, D n * log (1 / D n)
      ≤ ∑ _n in Finset.range N, log ↑N := Finset.sum_le_sum hterm
    _ = ↑N * log ↑N := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem L6_1_zero_when_certain (D : ℕ → ℝ) (N : ℕ)
    (hD : ∀ n, D n = 1) :
    recursiveEntropy D N = 0 := by
  unfold recursiveEntropy
  apply Finset.sum_eq_zero
  intro n _
  rw [hD n, one_div, inv_one, log_one, mul_zero]

/-! ## L6.2 — Classical Limit: Single Depth = Shannon -/

def shannonEntropy (p : Fin N → ℝ) : ℝ :=
  ∑ i, p i * log (1 / p i)

/-- **L6.2 (classical limit).** Embedding a distribution `p : Fin N → ℝ` as a
    depth density (padded beyond depth `N` with the "certain" value 1, cf.
    `L6_1_zero_when_certain`) makes recursive entropy at depth `N` equal to
    Shannon entropy. This is the actual bridge between the ℕ-indexed
    `recursiveEntropy` and the `Fin`-indexed `shannonEntropy`; the equality of
    sums holds unconditionally — no positivity or normalization hypotheses are
    needed. -/
theorem L6_2_single_depth_is_shannon (p : Fin N → ℝ) :
    recursiveEntropy (fun k => if h : k < N then p ⟨k, h⟩ else 1) N
      = shannonEntropy p := by
  unfold recursiveEntropy shannonEntropy
  rw [← Fin.sum_univ_eq_sum_range
      (fun k => (if h : k < N then p ⟨k, h⟩ else 1)
        * log (1 / (if h : k < N then p ⟨k, h⟩ else 1))) N]
  exact Finset.sum_congr rfl fun i _ => by rw [dif_pos i.isLt]

theorem L6_2_binary_entropy (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    p * log (1 / p) + (1 - p) * log (1 / (1 - p)) ≥ 0 := by
  apply add_nonneg
  · exact mul_nonneg (le_of_lt hp0) (log_nonneg (by rw [one_div]; exact one_le_inv hp0 (le_of_lt hp1)))
  · exact mul_nonneg (by linarith) (log_nonneg (by rw [one_div]; exact one_le_inv (by linarith) (by linarith)))

/-! ## L6.3 — Bekenstein Bound
    At saturation η=1:
    - d* = e^π states (number of microstates)
    - probability per state = e^{-π}
    - S_per = e^π · e^{-π} · π = π nats per degree of freedom
    - I(A:B) = 2·π = I_local (Bekenstein capacity) -/

def bekensteinStates : ℝ := exp π
def bekensteinProb : ℝ := exp (-π)
def entropyPerDOF : ℝ := π
def bekensteinCapacity : ℝ := 2 * π

theorem L6_3_prob_times_states : bekensteinStates * bekensteinProb = 1 := by
  unfold bekensteinStates bekensteinProb
  rw [← exp_add]; simp

theorem L6_3_entropy_per_dof :
    bekensteinStates * (bekensteinProb * log (1 / bekensteinProb)) = π := by
  unfold bekensteinStates bekensteinProb
  -- log (1 / e^{-π}) = log (e^π) = π. Then e^π * (e^{-π} * π) = (e^π * e^{-π}) * π = 1 * π = π
  rw [one_div, log_inv, log_exp, neg_neg]
  -- goal: rexp π * (rexp (-π) * π) = π
  rw [show rexp π * (rexp (-π) * π) = (rexp π * rexp (-π)) * π from by ring]
  rw [← exp_add, add_neg_self, exp_zero, one_mul]

theorem L6_3_mutual_info : bekensteinCapacity = 2 * π := rfl

/-- Two DOF, each carrying the saturation entropy
    `e^π · (e^{-π} · log (1/e^{-π})) = π` (`L6_3_entropy_per_dof`), give exactly
    the Bekenstein capacity `2π`: the capacity is reached by evaluating the
    entropy formula, not by comparing two definitions. -/
theorem L6_3_capacity_from_entropy :
    2 * (bekensteinStates * (bekensteinProb * log (1 / bekensteinProb)))
      = bekensteinCapacity := by
  rw [L6_3_entropy_per_dof]
  rfl

theorem L6_3_bekenstein_positive : 0 < bekensteinCapacity := by
  unfold bekensteinCapacity; linarith [pi_pos]

/-! ## T6 Summary -/

/-- **T6 (Entropy = Bekenstein).** The Bekenstein capacity `2π` is *derived*
    from the entropy formula: two degrees of freedom, each contributing
    `states × (prob × log (1/prob))` nats at saturation, total exactly
    `bekensteinCapacity`; moreover the state count and per-state probability
    normalize (`e^π · e^{-π} = 1`). The factor 2 (two DOF) remains a modeling
    input, but the `2π` on the right now arrives via the entropy expression
    rather than by definitional reflexivity. -/
theorem T6_entropy_equals_bekenstein :
    2 * (bekensteinStates * (bekensteinProb * log (1 / bekensteinProb)))
        = bekensteinCapacity
    ∧ bekensteinStates * bekensteinProb = 1 :=
  ⟨L6_3_capacity_from_entropy, L6_3_prob_times_states⟩

/-! ## L6.4 — Min-Entropy (H_∞) and the Leftover-Hash Extractor Bound
    (DM-TRNG anchor: SP 800-90B min-entropy + SP 800-90B §3.1.5 vetted
     conditioner = universal hash ⇒ full-entropy output)

    The SP 800-90B estimators in `fil_mlwe256/analysis/min_entropy.py` all
    report `H_min = -log₂(p_max)`. We formalize the natural-log version
    `minEntropy p = -log (maxProb p)` (a positive multiple `log 2` apart from
    the bits/symbol figure) and prove the two structural facts the entropy
    claim rests on:
      • `minEntropy ≤ shannonEntropy`  (H_∞ is the most conservative entropy),
      • `minEntropy (uniform) = log N` (the maximal/full-entropy point).
    The leftover-hash / extractor bound (universal hash family applied to a
    source with `H_∞ ≥ k` ⇒ output ε-close to uniform) is fully proved below
    (`L6_4c_leftover_hash_extractor`) via the classical collision-probability
    + Cauchy–Schwarz argument; see the citations on that theorem. -/

/-- The largest coordinate probability `p_max` of a distribution on
    `Fin (n+1)` (nonempty index type). Defined as the `Finset.max'` of the
    image of `p`, mirroring the `Finset.image … |>.max'` pattern used in
    `CurvatureConvergence.lean`. -/
def maxProb (p : Fin (n + 1) → ℝ) : ℝ :=
  ((Finset.univ : Finset (Fin (n + 1))).image p).max'
    ⟨p 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩

/-- Min-entropy `H_∞(p) = -log p_max` (natural log; bits = this / log 2). -/
def minEntropy (p : Fin (n + 1) → ℝ) : ℝ := - log (maxProb p)

/-- Every coordinate probability is `≤ p_max`. -/
theorem le_maxProb (p : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    p i ≤ maxProb p := by
  unfold maxProb
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

/-- `p_max > 0` when all coordinates are positive (so `log p_max` is defined
    and the sign manipulations below are valid). -/
theorem maxProb_pos (p : Fin (n + 1) → ℝ) (hp_pos : ∀ i, 0 < p i) :
    0 < maxProb p :=
  lt_of_lt_of_le (hp_pos 0) (le_maxProb p 0)

/-- Monotonicity of `log` on the positives. Proved from the stable primitives
    `Real.exp_log` / `Real.exp_le_exp` (rather than a version-sensitive
    `log_le_log` name) so it compiles regardless of Mathlib API churn:
    `log` is the inverse of the strictly monotone `exp`, so `x ≤ y` ⇒
    `log x ≤ log y` on the positives. -/
theorem log_le_log_of_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    log x ≤ log y := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  -- exp is monotone and log is its inverse on the positives
  rw [← Real.exp_le_exp, Real.exp_log hx, Real.exp_log hy]
  exact hxy

/-- **L6.4a — H_∞ ≤ Shannon.** Min-entropy is the most conservative of the
    Rényi entropies: it never overstates the unpredictability of the source.
    Proof: `shannon = ∑ pᵢ·(-log pᵢ) ≥ ∑ pᵢ·(-log p_max) = -log p_max`, using
    `pᵢ ≤ p_max` ⇒ `log pᵢ ≤ log p_max` and `∑ pᵢ = 1`. -/
theorem L6_4a_minEntropy_le_shannon (p : Fin (n + 1) → ℝ)
    (hp_pos : ∀ i, 0 < p i) (hp_sum : ∑ i, p i = 1) :
    minEntropy p ≤ shannonEntropy p := by
  unfold minEntropy shannonEntropy
  -- Rewrite each Shannon term pᵢ·log(1/pᵢ) = pᵢ·(-log pᵢ) and the target
  -- -log p_max = (∑ pᵢ)·(-log p_max) = ∑ pᵢ·(-log p_max).
  have hterm : ∀ i ∈ Finset.univ,
      p i * (-log (maxProb p)) ≤ p i * log (1 / p i) := by
    intro i _
    rw [one_div, log_inv]
    -- goal: p i * (-log p_max) ≤ p i * (-log (p i))
    apply mul_le_mul_of_nonneg_left _ (le_of_lt (hp_pos i))
    -- -log p_max ≤ -log (p i)  ⇐  log (p i) ≤ log p_max
    exact neg_le_neg (log_le_log_of_le (hp_pos i) (le_maxProb p i))
  calc -log (maxProb p)
      = (∑ i, p i) * (-log (maxProb p)) := by rw [hp_sum, one_mul]
    _ = ∑ i, p i * (-log (maxProb p)) := by rw [Finset.sum_mul]
    _ ≤ ∑ i, p i * log (1 / p i) := Finset.sum_le_sum hterm

/-- The uniform distribution on `Fin (n+1)`. -/
def uniformDist (n : ℕ) : Fin (n + 1) → ℝ := fun _ => 1 / (↑(n + 1) : ℝ)

/-- `p_max` of the uniform distribution is `1/(n+1)`: the image of a constant
    function is the singleton `{1/(n+1)}`, whose `max'` is itself. -/
theorem maxProb_uniform (n : ℕ) : maxProb (uniformDist n) = 1 / (↑(n + 1) : ℝ) := by
  have hle : maxProb (uniformDist n) ≤ 1 / (↑(n + 1) : ℝ) := by
    -- every element of the image equals the constant value
    unfold maxProb
    apply Finset.max'_le
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    exact le_of_eq rfl
  have hge : 1 / (↑(n + 1) : ℝ) ≤ maxProb (uniformDist n) :=
    le_maxProb (uniformDist n) 0
  linarith

/-- **L6.4b — H_∞ of uniform = log N.** The full-entropy / maximal point:
    a uniform distribution on `N = n+1` symbols has `minEntropy = log N`
    (in bits, `log₂ N`; for a byte source `N = 256`, `log₂ N = 8` — exactly
    the SP 800-90B target `H_min ≈ 8.0 bits/byte`). -/
theorem L6_4b_minEntropy_uniform (n : ℕ) :
    minEntropy (uniformDist n) = log (↑(n + 1) : ℝ) := by
  unfold minEntropy
  rw [maxProb_uniform, one_div, log_inv, neg_neg]

/-- Min-entropy is nonnegative for a genuine distribution (`p_max ≤ 1`),
    since `log` of a value `≤ 1` is `≤ 0`. -/
theorem minEntropy_nonneg (p : Fin (n + 1) → ℝ)
    (hp_pos : ∀ i, 0 < p i) (hpm_le : maxProb p ≤ 1) :
    0 ≤ minEntropy p := by
  unfold minEntropy
  rw [neg_nonneg]
  exact log_nonpos (le_of_lt (maxProb_pos p hp_pos)) hpm_le

/-! ### Leftover-Hash / Extractor bound (SP 800-90B §3.1.5 vetted conditioner)

    A family `H = {h : Fin (N) → Fin (M)}` is **2-universal** if for distinct
    inputs `x ≠ y`, `Pr_{h}[h x = h y] ≤ 1/M`. The Leftover Hash Lemma (LHL)
    states: if the source `X` has min-entropy `H_∞(X) ≥ k` and `h` is drawn
    from a 2-universal family with `m = log₂ M ≤ k - 2·log₂(1/ε)`, then `(h, h(X))`
    is `ε`-close (in statistical distance) to `(h, U_M)`. This is exactly the
    guarantee the DM-TRNG conditioner provides: SHA-256 / HMAC-SHA256 (the
    golden path) and the Möbius-Keccak sponge are modeled as vetted
    conditioners / 2-universal extractors, so a raw stream with measured
    `H_∞ ≥ k` is mapped to a near-uniform full-entropy output. -/

/-- Statistical (total-variation) distance between two distributions on
    `Fin m`: `½ ∑ |p i − q i|`. -/
def statDist (p q : Fin m → ℝ) : ℝ :=
  (1 / 2) * ∑ i, |p i - q i|

theorem statDist_nonneg (p q : Fin m → ℝ) : 0 ≤ statDist p q := by
  unfold statDist
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg (fun i _ => abs_nonneg _)

theorem statDist_self (p : Fin m → ℝ) : statDist p p = 0 := by
  unfold statDist
  simp

/-- A 2-universal hash family carrying its actual functions and a nonempty seed
    index `Fin seeds`, so the extractor's output distribution is *well-defined*
    (not an arbitrary distribution). 2-universality: for distinct inputs the
    fraction of seeds on which they collide is `≤ 1/M`. -/
structure UniversalHashFamily (N M : ℕ) where
  seeds : ℕ
  seeds_pos : 0 < seeds
  h : Fin seeds → Fin N → Fin M
  two_universal : ∀ x y, x ≠ y →
    (↑(Finset.univ.filter (fun i => h i x = h i y)).card : ℝ) / (↑seeds : ℝ)
      ≤ 1 / (↑M : ℝ)

/-- **Genuine extractor output distribution.** Pick a seed `i` uniformly from the
    family and a source symbol `x ∼ p`, and emit `h i x`; this is the pushforward
    of `p` (with the uniform seed) through the family — precisely the
    distribution the Leftover Hash Lemma bounds, *not* an arbitrary one. -/
def extractorOutput (Hf : UniversalHashFamily N M) (p : Fin N → ℝ) : Fin M → ℝ :=
  fun j => (1 / (↑Hf.seeds : ℝ)) *
    ∑ i, (∑ x in Finset.univ.filter (fun x => Hf.h i x = j), p x)

/-- Per-seed pushforward of the source through hash `h i`: the mass landing
    on output `j` when the seed is `i`. `extractorOutput` is its seed-average. -/
def perSeedOutput (Hf : UniversalHashFamily N M) (p : Fin N → ℝ)
    (i : Fin Hf.seeds) (j : Fin M) : ℝ :=
  ∑ x in Finset.univ.filter (fun x => Hf.h i x = j), p x

theorem extractorOutput_eq (Hf : UniversalHashFamily N M) (p : Fin N → ℝ)
    (j : Fin M) :
    extractorOutput Hf p j
      = (1 / (↑Hf.seeds : ℝ)) * ∑ i, perSeedOutput Hf p i j := rfl

theorem perSeedOutput_nonneg (Hf : UniversalHashFamily N M) (p : Fin N → ℝ)
    (hp : ∀ x, 0 ≤ p x) (i : Fin Hf.seeds) (j : Fin M) :
    0 ≤ perSeedOutput Hf p i j :=
  Finset.sum_nonneg fun x _ => hp x

/-- Each per-seed pushforward is a probability vector: the fibers of `h i`
    partition the source space. -/
theorem perSeedOutput_row_sum (Hf : UniversalHashFamily N M) (p : Fin N → ℝ)
    (i : Fin Hf.seeds) :
    ∑ j, perSeedOutput Hf p i j = ∑ x, p x :=
  Finset.sum_fiberwise Finset.univ (Hf.h i) p

/-- Collision form of the per-seed second moment:
    `∑ⱼ q(i,j)² = ∑ₓ p x · q(i, h i x)`. -/
theorem perSeedOutput_sq_sum (Hf : UniversalHashFamily N M) (p : Fin N → ℝ)
    (i : Fin Hf.seeds) :
    ∑ j, (perSeedOutput Hf p i j) ^ 2
      = ∑ x, p x * perSeedOutput Hf p i (Hf.h i x) := by
  calc ∑ j, (perSeedOutput Hf p i j) ^ 2
      = ∑ j, ∑ x in Finset.univ.filter (fun x => Hf.h i x = j),
          p x * perSeedOutput Hf p i (Hf.h i x) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [sq, show perSeedOutput Hf p i j
          = ∑ x in Finset.univ.filter (fun x => Hf.h i x = j), p x from rfl,
          Finset.sum_mul]
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [Finset.mem_filter] at hx
        rw [hx.2]
        rfl
    _ = ∑ x, p x * perSeedOutput Hf p i (Hf.h i x) :=
        Finset.sum_fiberwise Finset.univ (Hf.h i) _

/-- **L6.4c — Leftover Hash Lemma (extractor bound).**
    If the source distribution `p` on `Fin (N+1)` has `minEntropy p ≥ k` and `Hf`
    is 2-universal into `Fin (M+1)` with `log (↑(M+1)) ≤ k - 2 * log (1/ε)` (the
    standard LHL entropy-loss condition), then **the family's genuine extractor
    output** `extractorOutput Hf p` is within statistical distance `ε` of uniform.

    PROOF (the classical collision-probability argument, fully formal):
    with `q i j` the per-seed pushforward and `Δ i j := q i j − 1/(M+1)`,
    * `∑ᵢⱼ Δ² = ∑ᵢⱼ q² − S/(M+1)` (row sums are 1),
    * `∑ᵢⱼ q² = ∑ₓ ∑ᵧ p x · p y · #{i : h i x = h i y}
              ≤ S·p_max + S/(M+1)` (diagonal: `#=S`, `∑p x² ≤ p_max`;
      off-diagonal: 2-universality),
    * Cauchy–Schwarz: `(∑ᵢⱼ |Δ|)² ≤ S·(M+1)·∑ᵢⱼ Δ² ≤ S²·(M+1)·p_max`,
    * hence `statDist ≤ ½·√((M+1)·p_max) ≤ ½·√(exp(log(M+1) − k)) ≤ ½·ε ≤ ε`
      using `p_max = exp(−minEntropy) ≤ exp(−k)` and the entropy-loss condition.
    References: Impagliazzo–Levin–Luby (LHL, 1989);
    Håstad–Impagliazzo–Levin–Luby (1999); NIST SP 800-90B §3.1.5. -/
theorem L6_4c_leftover_hash_extractor
    (N M : ℕ) (Hf : UniversalHashFamily (N + 1) (M + 1))
    (p : Fin (N + 1) → ℝ) (hp_pos : ∀ i, 0 < p i) (hp_sum : ∑ i, p i = 1)
    (k ε : ℝ) (hε : 0 < ε)
    (hk : k ≤ minEntropy p)
    (hloss : log (↑(M + 1) : ℝ) ≤ k - 2 * log (1 / ε)) :
    statDist (extractorOutput Hf p) (uniformDist M) ≤ ε := by
  have hSr_pos : (0:ℝ) < (↑Hf.seeds : ℝ) := by exact_mod_cast Hf.seeds_pos
  have hMr_pos : (0:ℝ) < ((M + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos M
  have hpm_pos : 0 < maxProb p := maxProb_pos p hp_pos
  -- ===== (1) Collision bound: ∑ᵢ ∑ⱼ q² ≤ S·p_max + S/(M+1) =====
  have hcount_diag : ∀ x : Fin (N + 1),
      (Finset.univ.filter (fun i => Hf.h i x = Hf.h i x)).card = Hf.seeds := by
    intro x
    rw [Finset.filter_true_of_mem (fun i _ => rfl), Finset.card_univ,
      Fintype.card_fin]
  have hcount_off : ∀ x y : Fin (N + 1), y ≠ x →
      ((Finset.univ.filter (fun i => Hf.h i y = Hf.h i x)).card : ℝ)
        ≤ (↑Hf.seeds : ℝ) / ((M + 1 : ℕ) : ℝ) := by
    intro x y hyx
    have h := Hf.two_universal y x hyx
    rw [div_le_div_iff hSr_pos hMr_pos] at h
    -- h : card · (M+1) ≤ 1 · S; goal: card ≤ S/(M+1)
    rw [le_div_iff hMr_pos]
    linarith
  -- Per-seed collision mass, summed over seeds and reindexed:
  have hsq_total : ∑ i, ∑ j, (perSeedOutput Hf p i j) ^ 2
      ≤ (↑Hf.seeds : ℝ) * maxProb p
        + (↑Hf.seeds : ℝ) / ((M + 1 : ℕ) : ℝ) := by
    have hswap : ∑ i, ∑ j, (perSeedOutput Hf p i j) ^ 2
        = ∑ x, p x * ∑ i, perSeedOutput Hf p i (Hf.h i x) := by
      calc ∑ i, ∑ j, (perSeedOutput Hf p i j) ^ 2
          = ∑ i, ∑ x, p x * perSeedOutput Hf p i (Hf.h i x) := by
            exact Finset.sum_congr rfl fun i _ => perSeedOutput_sq_sum Hf p i
        _ = ∑ x, ∑ i, p x * perSeedOutput Hf p i (Hf.h i x) := Finset.sum_comm
        _ = ∑ x, p x * ∑ i, perSeedOutput Hf p i (Hf.h i x) := by
            exact Finset.sum_congr rfl fun x _ => (Finset.mul_sum _ _ _).symm
    rw [hswap]
    -- Inner: ∑ᵢ q i (h i x) = ∑ᵧ (#collisions x y)·p y ≤ S·p x + S/(M+1)·∑_{y≠x} p y
    have hinner : ∀ x : Fin (N + 1),
        ∑ i, perSeedOutput Hf p i (Hf.h i x)
          ≤ (↑Hf.seeds : ℝ) * p x + (↑Hf.seeds : ℝ) / ((M + 1 : ℕ) : ℝ) := by
      intro x
      have hexpand : ∑ i, perSeedOutput Hf p i (Hf.h i x)
          = ∑ y, ((Finset.univ.filter (fun i => Hf.h i y = Hf.h i x)).card : ℝ)
              * p y := by
        calc ∑ i, perSeedOutput Hf p i (Hf.h i x)
            = ∑ i, ∑ y, if Hf.h i y = Hf.h i x then p y else 0 := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [perSeedOutput, Finset.sum_filter]
          _ = ∑ y, ∑ i, if Hf.h i y = Hf.h i x then p y else 0 := Finset.sum_comm
          _ = ∑ y, ((Finset.univ.filter
                (fun i => Hf.h i y = Hf.h i x)).card : ℝ) * p y := by
              refine Finset.sum_congr rfl fun y _ => ?_
              rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      rw [hexpand]
      -- split off the diagonal y = x
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x), hcount_diag x]
      have hoff : ∑ y in Finset.univ.erase x,
          ((Finset.univ.filter (fun i => Hf.h i y = Hf.h i x)).card : ℝ) * p y
            ≤ (↑Hf.seeds : ℝ) / ((M + 1 : ℕ) : ℝ) := by
        calc ∑ y in Finset.univ.erase x,
            ((Finset.univ.filter (fun i => Hf.h i y = Hf.h i x)).card : ℝ) * p y
            ≤ ∑ y in Finset.univ.erase x,
                (↑Hf.seeds : ℝ) / ((M + 1 : ℕ) : ℝ) * p y := by
              refine Finset.sum_le_sum fun y hy => ?_
              have hyx : y ≠ x := Finset.ne_of_mem_erase hy
              exact mul_le_mul_of_nonneg_right (hcount_off x y hyx) (hp_pos y).le
          _ = (↑Hf.seeds : ℝ) / ((M + 1 : ℕ) : ℝ)
                * ∑ y in Finset.univ.erase x, p y := by rw [Finset.mul_sum]
          _ ≤ (↑Hf.seeds : ℝ) / ((M + 1 : ℕ) : ℝ) * 1 := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              rw [← hp_sum]
              exact Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.erase_subset x Finset.univ) (fun y _ _ => (hp_pos y).le)
          _ = (↑Hf.seeds : ℝ) / ((M + 1 : ℕ) : ℝ) := mul_one _
      linarith [hoff]
    -- combine over x, using ∑ p x² ≤ p_max and ∑ p = 1
    calc ∑ x, p x * ∑ i, perSeedOutput Hf p i (Hf.h i x)
        ≤ ∑ x, p x * ((↑Hf.seeds : ℝ) * p x
            + (↑Hf.seeds : ℝ) / ((M + 1 : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum fun x _ => ?_
          exact mul_le_mul_of_nonneg_left (hinner x) (hp_pos x).le
      _ = (↑Hf.seeds : ℝ) * ∑ x, p x * p x
            + (↑Hf.seeds : ℝ) / ((M + 1 : ℕ) : ℝ) * ∑ x, p x := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun x _ => ?_
          ring
      _ ≤ (↑Hf.seeds : ℝ) * maxProb p
            + (↑Hf.seeds : ℝ) / ((M + 1 : ℕ) : ℝ) := by
          rw [hp_sum, mul_one]
          have hsum_sq : ∑ x, p x * p x ≤ maxProb p := by
            calc ∑ x, p x * p x ≤ ∑ x, maxProb p * p x := by
                  refine Finset.sum_le_sum fun x _ => ?_
                  exact mul_le_mul_of_nonneg_right (le_maxProb p x) (hp_pos x).le
              _ = maxProb p * ∑ x, p x := (Finset.mul_sum _ _ _).symm
              _ = maxProb p := by rw [hp_sum, mul_one]
          have := mul_le_mul_of_nonneg_left hsum_sq hSr_pos.le
          linarith
  -- ===== (2) Deviation second moment: ∑ᵢⱼ Δ² = ∑ᵢⱼ q² − S/(M+1) =====
  have hrow : ∀ i, ∑ j, perSeedOutput Hf p i j = 1 := fun i => by
    rw [perSeedOutput_row_sum, hp_sum]
  have hdev : ∑ i, ∑ j, (perSeedOutput Hf p i j - 1 / ((M + 1 : ℕ) : ℝ)) ^ 2
      = (∑ i, ∑ j, (perSeedOutput Hf p i j) ^ 2)
        - (↑Hf.seeds : ℝ) / ((M + 1 : ℕ) : ℝ) := by
    have hper : ∀ i, ∑ j, (perSeedOutput Hf p i j - 1 / ((M + 1 : ℕ) : ℝ)) ^ 2
        = (∑ j, (perSeedOutput Hf p i j) ^ 2) - 1 / ((M + 1 : ℕ) : ℝ) := by
      intro i
      have hexp : ∀ j : Fin (M + 1),
          (perSeedOutput Hf p i j - 1 / ((M + 1 : ℕ) : ℝ)) ^ 2
            = (perSeedOutput Hf p i j) ^ 2
              - 2 / ((M + 1 : ℕ) : ℝ) * perSeedOutput Hf p i j
              + (1 / ((M + 1 : ℕ) : ℝ)) ^ 2 := by
        intro j
        field_simp
        ring
      rw [Finset.sum_congr rfl fun j _ => hexp j]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        hrow i, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp [hMr_pos.ne']
      ring
    rw [Finset.sum_congr rfl fun i _ => hper i, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one_div]
  have hdev_le : ∑ i, ∑ j, (perSeedOutput Hf p i j - 1 / ((M + 1 : ℕ) : ℝ)) ^ 2
      ≤ (↑Hf.seeds : ℝ) * maxProb p := by
    rw [hdev]
    linarith [hsq_total]
  -- ===== (3) Cauchy–Schwarz: ℓ¹ deviation vs ℓ² deviation =====
  have habs_sq : (∑ z : Fin Hf.seeds × Fin (M + 1),
        |perSeedOutput Hf p z.1 z.2 - 1 / ((M + 1 : ℕ) : ℝ)|) ^ 2
      ≤ ((↑Hf.seeds : ℝ) * ((M + 1 : ℕ) : ℝ))
        * ((↑Hf.seeds : ℝ) * maxProb p) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun z : Fin Hf.seeds × Fin (M + 1) =>
        |perSeedOutput Hf p z.1 z.2 - 1 / ((M + 1 : ℕ) : ℝ)|)
      (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow] at hcs
    have hsq_abs : ∑ z : Fin Hf.seeds × Fin (M + 1),
        |perSeedOutput Hf p z.1 z.2 - 1 / ((M + 1 : ℕ) : ℝ)| ^ 2
          = ∑ i, ∑ j, (perSeedOutput Hf p i j - 1 / ((M + 1 : ℕ) : ℝ)) ^ 2 := by
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => sq_abs _
    have hcard : ∑ _z : Fin Hf.seeds × Fin (M + 1), (1:ℝ)
        = (↑Hf.seeds : ℝ) * ((M + 1 : ℕ) : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, mul_one]
      push_cast
      ring
    rw [hsq_abs, hcard] at hcs
    calc (∑ z : Fin Hf.seeds × Fin (M + 1),
          |perSeedOutput Hf p z.1 z.2 - 1 / ((M + 1 : ℕ) : ℝ)|) ^ 2
        ≤ (∑ i, ∑ j, (perSeedOutput Hf p i j - 1 / ((M + 1 : ℕ) : ℝ)) ^ 2)
            * ((↑Hf.seeds : ℝ) * ((M + 1 : ℕ) : ℝ)) := hcs
      _ ≤ ((↑Hf.seeds : ℝ) * maxProb p)
            * ((↑Hf.seeds : ℝ) * ((M + 1 : ℕ) : ℝ)) := by
          apply mul_le_mul_of_nonneg_right hdev_le (by positivity)
      _ = ((↑Hf.seeds : ℝ) * ((M + 1 : ℕ) : ℝ))
            * ((↑Hf.seeds : ℝ) * maxProb p) := by ring
  -- ===== (4) statDist ≤ ½·√((M+1)·p_max) =====
  have hstat : statDist (extractorOutput Hf p) (uniformDist M)
      ≤ (1 / 2) * Real.sqrt (((M + 1 : ℕ) : ℝ) * maxProb p) := by
    unfold statDist uniformDist
    -- per-coordinate: |Y j − u| ≤ (1/S)·∑ᵢ |q i j − u|
    have hcoord : ∀ j : Fin (M + 1),
        |extractorOutput Hf p j - 1 / ((M + 1 : ℕ) : ℝ)|
          ≤ (1 / (↑Hf.seeds : ℝ))
            * ∑ i, |perSeedOutput Hf p i j - 1 / ((M + 1 : ℕ) : ℝ)| := by
      intro j
      have hpull : extractorOutput Hf p j - 1 / ((M + 1 : ℕ) : ℝ)
          = (1 / (↑Hf.seeds : ℝ))
            * ∑ i, (perSeedOutput Hf p i j - 1 / ((M + 1 : ℕ) : ℝ)) := by
        rw [extractorOutput_eq, Finset.sum_sub_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_sub]
        congr 1
        field_simp [hSr_pos.ne']
      rw [hpull, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (↑Hf.seeds : ℝ))]
      exact mul_le_mul_of_nonneg_left
        (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    -- sum over j, fold into the product-indexed total, apply C–S
    have hT : ∑ j, |extractorOutput Hf p j - 1 / ((M + 1 : ℕ) : ℝ)|
        ≤ (1 / (↑Hf.seeds : ℝ)) * ∑ z : Fin Hf.seeds × Fin (M + 1),
            |perSeedOutput Hf p z.1 z.2 - 1 / ((M + 1 : ℕ) : ℝ)| := by
      calc ∑ j, |extractorOutput Hf p j - 1 / ((M + 1 : ℕ) : ℝ)|
          ≤ ∑ j, (1 / (↑Hf.seeds : ℝ))
              * ∑ i, |perSeedOutput Hf p i j - 1 / ((M + 1 : ℕ) : ℝ)| :=
            Finset.sum_le_sum fun j _ => hcoord j
        _ = (1 / (↑Hf.seeds : ℝ)) * ∑ j, ∑ i,
              |perSeedOutput Hf p i j - 1 / ((M + 1 : ℕ) : ℝ)| :=
            (Finset.mul_sum _ _ _).symm
        _ = (1 / (↑Hf.seeds : ℝ)) * ∑ z : Fin Hf.seeds × Fin (M + 1),
              |perSeedOutput Hf p z.1 z.2 - 1 / ((M + 1 : ℕ) : ℝ)| := by
            rw [Fintype.sum_prod_type]
            rw [Finset.sum_comm]
    -- √ of the C–S bound: T ≤ S·√((M+1)·p_max)
    have hT2 : ∑ z : Fin Hf.seeds × Fin (M + 1),
        |perSeedOutput Hf p z.1 z.2 - 1 / ((M + 1 : ℕ) : ℝ)|
          ≤ (↑Hf.seeds : ℝ) * Real.sqrt (((M + 1 : ℕ) : ℝ) * maxProb p) := by
      have hnn : (0:ℝ) ≤ ∑ z : Fin Hf.seeds × Fin (M + 1),
          |perSeedOutput Hf p z.1 z.2 - 1 / ((M + 1 : ℕ) : ℝ)| :=
        Finset.sum_nonneg fun z _ => abs_nonneg _
      have hrearrange : ((↑Hf.seeds : ℝ) * ((M + 1 : ℕ) : ℝ))
          * ((↑Hf.seeds : ℝ) * maxProb p)
          = ((↑Hf.seeds : ℝ)) ^ 2 * (((M + 1 : ℕ) : ℝ) * maxProb p) := by ring
      have h1 := Real.sqrt_le_sqrt (hrearrange ▸ habs_sq)
      rw [Real.sqrt_sq hnn] at h1
      rw [Real.sqrt_mul (by positivity) (((M + 1 : ℕ) : ℝ) * maxProb p),
        Real.sqrt_sq hSr_pos.le] at h1
      exact h1
    calc (1 / 2 : ℝ) * ∑ j, |extractorOutput Hf p j - 1 / ((M + 1 : ℕ) : ℝ)|
        ≤ (1 / 2) * ((1 / (↑Hf.seeds : ℝ)) * ∑ z : Fin Hf.seeds × Fin (M + 1),
            |perSeedOutput Hf p z.1 z.2 - 1 / ((M + 1 : ℕ) : ℝ)|) := by
          apply mul_le_mul_of_nonneg_left hT (by norm_num)
      _ ≤ (1 / 2) * ((1 / (↑Hf.seeds : ℝ))
            * ((↑Hf.seeds : ℝ) * Real.sqrt (((M + 1 : ℕ) : ℝ) * maxProb p))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left hT2 (by positivity)
      _ = (1 / 2) * Real.sqrt (((M + 1 : ℕ) : ℝ) * maxProb p) := by
          field_simp [hSr_pos.ne']
          ring
  -- ===== (5) Entropy accounting: (M+1)·p_max ≤ ε² =====
  have hpm : maxProb p ≤ Real.exp (-k) := by
    have hlog : Real.log (maxProb p) ≤ -k := by
      unfold minEntropy at hk
      linarith
    calc maxProb p = Real.exp (Real.log (maxProb p)) :=
          (Real.exp_log hpm_pos).symm
      _ ≤ Real.exp (-k) := Real.exp_le_exp.mpr hlog
  have hMpm : ((M + 1 : ℕ) : ℝ) * maxProb p ≤ ε ^ 2 := by
    have hM_eq : ((M + 1 : ℕ) : ℝ)
        = Real.exp (Real.log ((M + 1 : ℕ) : ℝ)) := (Real.exp_log hMr_pos).symm
    have hε2 : Real.exp (log ((M + 1 : ℕ) : ℝ) - k) ≤ ε ^ 2 := by
      have harg : log ((M + 1 : ℕ) : ℝ) - k ≤ Real.log (ε ^ 2) := by
        rw [Real.log_pow]
        have hlog_inv : log (1 / ε) = -log ε := by rw [one_div, Real.log_inv]
        rw [hlog_inv] at hloss
        -- Normalize the casts on BOTH sides so `log (↑M + 1)` and
        -- `log ↑(M + 1)` are the same atom for linarith.
        push_cast at hloss ⊢
        linarith
      calc Real.exp (log ((M + 1 : ℕ) : ℝ) - k)
          ≤ Real.exp (Real.log (ε ^ 2)) := Real.exp_le_exp.mpr harg
        _ = ε ^ 2 := Real.exp_log (by positivity)
    calc ((M + 1 : ℕ) : ℝ) * maxProb p
        ≤ ((M + 1 : ℕ) : ℝ) * Real.exp (-k) :=
          mul_le_mul_of_nonneg_left hpm hMr_pos.le
      _ = Real.exp (log ((M + 1 : ℕ) : ℝ) - k) := by
          nth_rewrite 1 [hM_eq]
          rw [← Real.exp_add]
          ring_nf
      _ ≤ ε ^ 2 := hε2
  -- ===== (6) Conclude =====
  calc statDist (extractorOutput Hf p) (uniformDist M)
      ≤ (1 / 2) * Real.sqrt (((M + 1 : ℕ) : ℝ) * maxProb p) := hstat
    _ ≤ (1 / 2) * Real.sqrt (ε ^ 2) := by
        apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hMpm) (by norm_num)
    _ = (1 / 2) * ε := by rw [Real.sqrt_sq hε.le]
    _ ≤ ε := by linarith

end FTC.EntropyLemmas
