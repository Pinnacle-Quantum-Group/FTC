# Cross-Reference: Lemma Derivation Mapping

The complete lemma derivation mapping for the PQG framework is maintained in:

**Repository:** [pinnacle-quantum-group/rssn](https://github.com/pinnacle-quantum-group/rssn)
**Branch:** `claude/lemma-derivation-mapping-WrwCv`

## FTC-Specific Results

| Theorem | Status | Key Lemmas |
|---------|--------|------------|
| FTC T3 (Curvature Convergence) | **PARTIALLY TIGHT** | L3.1 pointwise, L3.2a uniform, L3.3a-c Ricci flow |
| FTC T4 (Singularity Resolution) | **TIGHT (BH)** | L5.1-L5.7 complete chain |
| FTC T6 (Entropy = Bekenstein) | **TIGHT** | L6.1-L6.3 Shannon + classical limit + Bekenstein |

## Key FTC Results

- **D*_BH = e^{-pi} ~ 0.0432** -- universal black hole attractor density
- **R^(n*) -> 0** at BH singularity -- classical curvature diverges, FTC converges to zero
- **S_recursive at eta=1 = 2*pi nats** -- matches Bekenstein capacity exactly
- **Option B (fixed scale n* ~ |R|^{-1/2})** resolves pointwise vs uniform convergence gap

## Test Suite

FTC lemma tests: `rssn/tests/test_ftc_lemmas.py`
Gap 3 analysis: `rssn/tests/test_gap_analysis.py`
