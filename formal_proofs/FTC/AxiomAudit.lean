/-
  Axiom audit — the machine-checked claim → theorem map for FTC.

  Each `#print axioms` below reports the complete axiom footprint of one
  headline result. CI (.github/workflows/lean.yml) runs this file and fails
  if any reported axiom falls outside the standard trust base:

    propext, Classical.choice, Quot.sound

  This makes the results falsifiable in two concrete ways:
  * an admitted proof anywhere beneath a listed theorem surfaces in the
    reported axioms as `sorryAx` and turns CI red (a plain `lake build`
    merely warns about admitted proofs);
  * any custom `axiom` smuggled into the development is listed by name and
    rejected by the CI allowlist.

  If a theorem is renamed or deleted, this file fails to elaborate, so the
  claim map cannot silently drift out of sync with the proofs.
-/
import FTC.Axioms
import FTC.EntropyLemmas
import FTC.BekensteinEntropy
import FTC.CurvatureConvergence
import FTC.RecursiveDensityConvergence
import FTC.SingularityChain
import FTC.SingularityResolution

-- T3: curvature convergence (summary theorem)
#print axioms FTC.CurvatureConvergence.T3_curvature_convergence_summary
-- L3.2a: uniform convergence on compact sets
#print axioms FTC.CurvatureConvergence.L3_2a_uniform_on_compact
-- T4: singularity resolution
#print axioms FTC.SingularityChain.T4_singularity_resolution
-- L5.3: black-hole density value at saturation
#print axioms FTC.SingularityChain.L5_3_from_saturation
-- T6: recursive entropy saturates the Bekenstein bound
#print axioms FTC.EntropyLemmas.T6_entropy_equals_bekenstein
-- L6.1: Shannon-axiom compliance (maximality of the uniform distribution)
#print axioms FTC.EntropyLemmas.L6_1_maximality
-- L6.4c: leftover-hash extractor bound
#print axioms FTC.EntropyLemmas.L6_4c_leftover_hash_extractor
-- Bekenstein entropy from information content
#print axioms FTC.BekensteinEntropy.bekenstein_from_information
-- Classical curvature diverges while the recursive replacement stays finite
#print axioms FTC.SingularityResolution.recursive_replaces_singularity
-- Density-convergence backbone (Cauchy completeness argument)
#print axioms FTC.RecursiveDensityConvergence.cauchy_density_converges
-- Foundational density bounds
#print axioms FTC.Axioms.density_bounded
