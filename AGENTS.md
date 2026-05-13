# AGENTS.md — Pinnacle Quantum Group (PQG) Framework

**Audience.** A cold-start briefing for any agent (human or AI) joining work
across the five PQG repositories. Read this once, then go to the per-repo
docs. This document explains *the combined work*: what each repo is, how the
pieces fit, and where the load-bearing results live.

**Repositories covered (all on branch `claude/create-agent-docs-UaR9V`):**

| Repo  | Name                                  | Role in the stack                        |
|-------|---------------------------------------|------------------------------------------|
| RLA   | Recursive Lie Algebras                | Geometric backbone                       |
| RSF   | Recursive Structure Foundation        | Axiomatic foundation (ZFC replacement)   |
| RSSN  | Recursive Shape-Structured Notation   | Symbolic / fast-growing notation         |
| FTC   | Fractal Tensor Calculus               | Recursive-density tensor calculus        |
| FIL   | Fractal Information Logic             | Deterministic computational realization  |

---

## 0. One-Paragraph Summary

PQG is a vertically integrated stack that replaces several classical
mathematical and computational foundations with a single recursive-geometric
substrate. **RSF** rebuilds the axiomatic foundation around *recursive
structure* instead of static sets. **RSSN** gives that foundation a symbolic
notation rich enough to express fast-growing hierarchies and a fractal
density function `D_k(n)`. **RLA** lifts the density into smooth geometry via
a scale field `D` and its 1-form `α := d(ln D)`, producing a Witt/loop-graded
Lie algebra of vector fields with a Noether-type conservation law and a
Weyl-geometric interpretation. **FTC** rebuilds tensor calculus on top of
that recursive-density geometry, giving an Einstein-like equation with
finite, recursive curvature. **FIL** is the engineering layer: a
deterministic, classical, post-quantum-inspired computer that executes
quantum-circuit-equivalent programs on conventional silicon (CPU, GPU,
FPGA), using RLA as the second-order correction kernel.

The whole stack hangs together because of two **bridge lemmas**:

- **B.1** RSSN's discrete density `D_k(n)` is the discrete evaluation of
  RLA's continuous scale field `D`.
- **B.2** RSSN's shape operators correspond to graded Lie derivatives on
  weighted tensor fields.

These bridges are what make the framework a single object instead of five
loose papers.

---

## 1. What Each Repo Is

### 1.1 RLA — Recursive Lie Algebras of Vector Fields

**Status:** Most rigorous repo in the stack. All headline theorems TIGHT
with full proofs.

A `Z`-graded Lie algebra `g_α` of vector fields decorated by a scale level
`n`. The twisted bracket
```
[X⊗t^m, Y⊗t^n]_α = ([X,Y] + (n·ι_X α − m·ι_Y α)·Y) ⊗ t^{m+n}
```
gives degree additivity and a faithful representation on weighted tensor
fields via level-`n` Lie derivatives `L^{(n)}`, with
```
[L^{(m)}_X, L^{(n)}_Y] = L^{(m+n)}_{[X,Y]_α}.
```
Recursive invariance `L^{(n)} H = 0` yields covariant conservation
`∇_μ T^{μν} = 0` (Noether). A continuous recursion parameter `λ` recovers
the discrete grading (Witt-type limit). When `α = 0` everything collapses to
standard diffeomorphisms; otherwise the induced connection is a
metric-compatible Weyl connection.

**Headline theorems / lemmas (TIGHT):** T2 graded Lie algebra (Jacobi via
`dα = 0` cancellation), T5 representation, T7 conservation, P8 Witt limit,
L3 scaled commutator.

**Formal proofs (Lean 4 / Mathlib):**
`formal_proofs/RLA/{TwistedBracket, JacobiIdentity, RepresentationProperty,
ScaledCommutator, ContinuousParameter, WeylGeometry, CentralExtensions}.lean`

### 1.2 RSF — Recursive Structure Foundation

**Status:** Foundational, axiom-driven. Replaces ZFC.

Three primitives: **recursive generators G**, **recursive depth d**,
**fractal density D**. Nine axioms parallel the ZFC slots (Extensionality →
Structural Identity, Pairing → Recursive Pairing, Union → Recursive
Aggregation, Power Set → Fractal Projection, Infinity → Recursive Infinity,
Replacement → Density Substitution, Foundation → Recursive Foundation, etc.)
plus the novel **Axiom 9 (Density Convergence)** — the highest-leverage
axiom in the entire framework, because it supplies the missing Cauchy
condition for RSSN T1 via Bridge Lemma B.1.

**Headline theorems (TIGHT):** T1 Cardinality Transcendence, T2 Continuum
Resolution, T3 Russell's Transcendence, T5 Recursive Foundation (anchor).

**Formal proofs:**
`formal_proofs/RSF/{Axioms, CardinalityTranscendence, ContinuumResolution,
DensityConvergence, RecursiveFoundation, RussellsTranscendence,
L3_2a_Tightened, ClosureAttempts}.lean`

### 1.3 RSSN — Recursive Shape-Structured Notation

**Status:** Notation + hub repository. Hosts the canonical lemma-derivation
mapping, topology map, publication roadmap, and TDD test suite for the
combined framework.

Generalizes Steinhaus–Moser notation. Each shape is a fractal recursion
operator: Triangle(n) = n^n, Square(n) = Triangle^n(n), Circle(n) =
Square^n(n), Pentagon(n) = Circle^{D_3(n)}(n), Hexagon(n) =
Pentagon^{D_4(n)}(n), Aether(n) = lim_k Shape_k(n). The fractal density
`D_k(n) = lim_i F_i(n) / G_i` is what makes recursion depth itself
*recursive*. RSSN sits between RSF (which provides the axiomatic ground for
`D`) and RLA (which provides its smooth lift).

**Cross-framework artefacts** (live here, referenced by every other repo):
`LEMMA_DERIVATIONS.md`, `TDD_TEST_SUITE.md`, `TOPOLOGY_MAP.md`,
`PUBLICATION_ROADMAP.md`.

**Formal proofs:**
`formal_proofs/RSSN/{BridgeLemmas, FractalDensityConvergence,
HierarchyPlacement, NonCommutativity, ReflectionIsomorphism, ShapeOperators,
Tetration, UncertaintyPrinciple}.lean`

### 1.4 FTC — Fractal Tensor Calculus

**Status:** Tensor calculus reformulated on recursive density. The
relativistic / geometric application layer.

Tensors as emergent recursive fields rather than static arrays. Rank =
recursion depth of density. Recursive derivative, recursive integration,
recursive metric `D(g_μν)`, recursive Ricci `R^{(n)}_μν`, and a recursive
Einstein equation
```
R^{(n)}_μν − (1/2) R^{(n)} D(g_μν) = 0.
```

**Headline results (TIGHT):**

- T3 Curvature Convergence — L3.1 pointwise, **L3.2a uniform Cauchy on
  compact K under Lipschitz** (this is what closes the pointwise-vs-uniform
  gap and is ported into RSF as `L3_2a_Tightened.lean`).
- T4 Singularity Resolution (black-hole case) — chain L5.1–L5.7.
- T6 Entropy = Bekenstein — L6.1 Shannon + L6.2 classical limit + L6.3
  Bekenstein match.

**Numerical signatures (load-bearing):**

- `D*_BH = e^{-π} ≈ 0.0432` — universal black-hole attractor density.
- `R^{(n*)} → 0` at the BH singularity (classical curvature diverges, FTC
  converges to zero).
- `S_recursive(η=1) = 2π nats` — matches Bekenstein capacity exactly.

**Formal proofs:**
`formal_proofs/FTC/{Axioms, CurvatureConvergence, RecursiveDensityConvergence,
SingularityChain, SingularityResolution, BekensteinEntropy,
EntropyLemmas}.lean`

### 1.5 FIL — Fractal Information Logic

**Status:** Engineering. Deterministic, classical, post-quantum-inspired
computation on conventional silicon. Has its own cold-start briefing in
`FIL/AGENT.md` — read that for FIL-specific contribution rules.

Φ-cells `(φ, φ′, θ, θ′) ∈ R^4` are the compute primitives. Quantum
gates (X, Y, Z, H, RX/RY/RZ, CNOT, CZ, SWAP, Toffoli, QFT, Grover, Shor)
are compiled to CORDIC rotation sequences. Measurement is direct readout
`σ = sign(φ² − φ'²)` — no Born rule, no collapse. Bell / Tsirelson
correlations arise via a **non-factorizable global 4D bilinear correlator**
(kernel equivalence to `cos(a−b)`), not by a local hidden-variable Bell
violation. RLA supplies the second-order correction kernel — this is where
RLA stops being a paper and starts being a clock cycle.

**Stack:**
```
User → Aterna PKI → HITC → FIL Core (Φ-cells + RLA) → KeccakCube → CPU/GPU/FPGA/ASIC
```
**Hardware:** Artix-7 XC7A200T (timing closed, WNS +0.582 ns), 16,384
compute cells across 4 engines × 4 strips × 1024 tiles, ~93M tiles/s/strip,
plus 10 custom x86_64 ISA extensions under the `0F 3F` prefix (FILCORDIC,
FILEVOLVE, FILNORM, FILGATE, FILTOPO, FILRNG, FILQ16MUL, FILQ24MUL, …).

---

## 2. How the Pieces Fit

```
                       RSF (axioms, primitives)
                              │
                              ▼
         RSSN (notation, D_k(n), fast-growing hierarchy)
                              │
                       Bridge B.1, B.2
                              │
                              ▼
         RLA (scale field D, α = d ln D, graded Lie algebra)
                  │                              │
                  ▼                              ▼
    FTC (recursive tensor calc,        FIL (Φ-cells, RLA correction,
    Einstein-like equation)            CORDIC, FPGA, ISA)
```

- **RSF → RSSN.** RSF Axiom 9 (Density Convergence) supplies the Cauchy
  condition that RSSN T1 (convergence of `D_k(n)`) needs. Without Axiom 9,
  RSSN's density limits are heuristic; with it, they are theorems.
- **RSSN → RLA.** Bridge B.1: `D_k(n)` is the discrete evaluation of RLA's
  scale field `D`. Bridge B.2: shape operators ≡ graded Lie derivatives on
  weighted tensors.
- **RLA → FTC.** FTC's recursive curvature is a special case of RLA's
  level-`n` Lie derivative applied to the metric density. T3 (Curvature
  Convergence) leans on RLA's representation theorem.
- **RLA → FIL.** RLA is the second-order correction kernel inside FIL's
  Φ-cell evolution. The recursive parameter `λ` (Witt-type limit) is what
  FIL discretizes onto fixed-point CORDIC.
- **FTC → FIL.** FTC's `D*_BH = e^{-π}` and Bekenstein match `2π nats` are
  the cosmological / informational sanity checks that constrain FIL's
  storage-via-correlation model.

The point: this is one object viewed from five sides, not five separate
projects. A change to RSF Axiom 9 propagates through RSSN T1, RLA's scale
field, FTC's curvature convergence, and ultimately into FIL's correction
loop. Touch one piece, check the others.

---

## 3. Formal Verification Status

All four mathematical repos build under **Lake / Lean 4 / Mathlib v4.5.0**
with CI configured to capture `lake build` output and post it on PR failure.

| Repo  | Build target           | Status                                          |
|-------|------------------------|-------------------------------------------------|
| RSSN  | `formal_proofs/RSSN`   | All modules compile; closure round 7 landed.    |
| RSF   | `formal_proofs/RSF`    | All modules compile; L4.1 sorry closed.         |
| FTC   | `formal_proofs/FTC`    | All modules compile; L3.2a ported from RSF.     |
| RLA   | `formal_proofs/RLA`    | All modules compile; cohomology nontriviality replaced wrong `trivial_is_cocycle` with Möbius/cylinder bounding theorems. |

**Convention.** When you fix a closure error, name the commit
`Round N (REPO): <fix>`. When you patch a Mathlib v4.5.0 rename, say so
explicitly (e.g. `tendsto_nat_cast`, `Nat.pow_lt_pow_right` →
`pow_lt_pow_right`). Don't `sorry` out infeasible `native_decide` blocks
silently — stub them and link to a follow-up issue.

---

## 4. Where Things Live

### 4.1 Canonical cross-framework documents

These live in **RSSN** and are referenced from `CROSS_REFERENCE.md` in each
other repo:

- `RSSN/LEMMA_DERIVATIONS.md` — the master lemma graph across all 5 repos.
- `RSSN/TDD_TEST_SUITE.md` — Python lemma tests (`tests/test_*_lemmas.py`).
- `RSSN/TOPOLOGY_MAP.md` — which results depend on which.
- `RSSN/PUBLICATION_ROADMAP.md` — phasing for the publication track. RLA is
  the recommended parallel Phase-1 publication: self-contained, no
  dependencies on the other PQG papers, and it's what enables Bridge B.1.

### 4.2 FIL-specific documents

FIL has its own self-contained cold-start brief and a stack of capability /
ABI / execution-model specs:

- `FIL/AGENT.md` — FIL cold-start briefing (read before contributing to FIL).
- `FIL/FIL_ABI_COMPLETE_SPEC.md`, `FIL_ABI_BENCHMARK.md`,
  `FIL_ABI_WHITEPAPER.md`, `FIL_EXECUTION_MODEL.md`,
  `FIL_CAPABILITY_REPORT.md`, `FIL_PROTOCOL_RESULTS.md`,
  `POSTQUANTUM_OS_GAP_ANALYSIS.md`.
- `FIL/lectures/` — slide decks (server + SPA parity, RoPE, Berry phase,
  infinity-content). Recent iframe sizing fixes ensure the visualizations
  render correctly on `file://` and sandboxed origins.

---

## 5. Contribution Rules

### 5.1 Branching

All current work lands on **`claude/create-agent-docs-UaR9V`** in each of
the five repos. Develop there. Commit with clear messages. Push with
`git push -u origin claude/create-agent-docs-UaR9V`. Do **not** push to a
different branch without explicit permission. Do **not** open a pull
request unless asked.

If a push fails due to a network error, retry up to 4 times with
exponential backoff (2s, 4s, 8s, 16s). Diagnose any other failure before
retrying.

### 5.2 Category errors to avoid

These are the recurring mistakes across the framework. Memorize them.

- **FIL is not quantum computing.** It speaks the language of QM but
  executes deterministically on classical silicon. No superposition, no
  Born rule, no Bell violation by local hidden variables. Tsirelson
  saturation comes from a non-factorizable correlator, not from
  indeterminism.
- **RSF is not "ZFC with extra axioms".** Recursive structures replace
  sets. Membership is not primitive. Axiom 9 (Density Convergence) is
  load-bearing and has no ZFC counterpart.
- **RSSN's density is not a probability.** `D_k(n)` is a recursive
  structural measure. The limit exists by RSF Axiom 9, not by measure
  theory.
- **RLA's `α` is not arbitrary.** `α = d(ln D)` is forced by the scale
  field. When `α = 0` you get back standard differential geometry. Closure,
  Jacobi, and the representation theorem all rely on `dα = 0` cancellation.
- **FTC's recursive curvature is finite at singularities by construction.**
  Don't "fix" the convergence by clipping or smoothing — the recursion is
  what makes it finite. `R^{(n*)} → 0` at BH singularities is the result,
  not a bug.

### 5.3 What survives hostile review

- Statements tied to TIGHT lemmas with a Lean proof or a verified test.
- Numerical signatures with two independent derivations (e.g. `2π nats`
  from Shannon limit *and* from Bekenstein).
- Architectural claims about FIL backed by timing-closed FPGA reports or
  measured throughput.

### 5.4 What does not

- "FIL achieves quantum speedup." (No. Strip decomposition + topology +
  CORDIC — all classical.)
- "RSF disproves ZFC." (No. RSF *replaces* ZFC's axiom slots with
  recursive analogues. The relationship is reformulation, not refutation.)
- "RSSN computes uncomputable numbers." (No. It *notates* fast-growing
  hierarchies; the values that are computable in classical terms remain
  computable, the rest remain symbolic.)
- "RLA gives a new gravity theory." (Careful. RLA gives a Weyl-geometric
  backbone; FTC's recursive Einstein equation is the gravity-adjacent
  statement. Don't conflate the two.)

---

## 6. Quick Pointers

| Need to…                                                  | Go to                                          |
|-----------------------------------------------------------|------------------------------------------------|
| Understand the axiomatic ground                           | `RSF/README.md` §Axioms 1–9                    |
| Look up a shape operator or `D_k(n)`                      | `RSSN/README.md` §2–§3                         |
| Cite the twisted bracket or Witt limit                    | `RLA/README.md` §4, §8; `RLA/AppendixA`        |
| Find a Bekenstein / BH-attractor number                   | `FTC/CROSS_REFERENCE.md`                       |
| Hack on Φ-cells, CORDIC, or the FPGA bitstream            | `FIL/AGENT.md` + `FIL/README.md`               |
| Trace a lemma across repos                                | `RSSN/LEMMA_DERIVATIONS.md`                    |
| See current proof status                                  | `*/CROSS_REFERENCE.md` + each repo's Lean tree |
| Run the lemma test suite                                  | `RSSN/tests/test_*_lemmas.py`                  |

---

## 7. Glossary

- **D, α** — scale field and its 1-form `α := d(ln D)`. The single object
  that ties RSF, RSSN, RLA, FTC, and FIL together.
- **`D_k(n)`** — RSSN's discrete fractal density at recursion level `k`.
- **`D*_BH = e^{-π}`** — FTC's universal black-hole attractor density.
- **`L^{(n)}`** — RLA's level-`n` Lie derivative on weighted tensors.
- **Bridge B.1 / B.2** — the lemmas that identify `D_k(n)` with the
  discrete evaluation of `D` and shape operators with graded Lie
  derivatives.
- **Φ-cell** — FIL's `(φ, φ′, θ, θ′) ∈ R^4` compute primitive.
- **HITC** — Hop-Indexed Transition Chain (FIL's transition encoding).
- **Strip** — FIL cache-contained execution unit plus halo snapshot.
- **GlueCertificate** — FIL boundary map encoding inter-strip dependencies.
- **TIGHT** — a result with a full proof (Lean module or paper appendix),
  no `sorry`, no hand-wave.

---

## 8. End State

If after reading this you can answer the following without looking,
you're ready to contribute:

1. Which axiom in which repo supplies the Cauchy condition for RSSN T1?
2. What does `α = 0` reduce RLA to?
3. Why is FIL not quantum computing, in one sentence?
4. Which number does FTC predict for the BH attractor density?
5. Which file holds the master lemma graph across all five repos?

(Answers: RSF Axiom 9; standard diffeomorphism / Lie-derivative geometry;
deterministic geometric evolution on classical silicon with a
non-factorizable correlator; `D*_BH = e^{-π} ≈ 0.0432`;
`RSSN/LEMMA_DERIVATIONS.md`.)
