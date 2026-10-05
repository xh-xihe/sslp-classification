import MainTheory.KernelAxiomAudit
import MainTheory.CitedFamilyFullKL
import MainTheory.Orbit21WalshRank
import MainTheory.QECCSmithBridge

#certification_axioms [
  MainTheory.CitedFamilyFullKL.hasDistance,
  MainTheory.Orbit21WalshRank.kernel_dimension,
  MainTheory.Orbit21WalshRank.rank_six,
  MainTheory.QECCSmithBridge.finalSmithInvariant_eq_inverseDenominator,
  MainTheory.QECCSmithBridge.finalSmithInvariant_eq_lastFactor,
  MainTheory.QECCSmithBridge.nonempty_smithWitness,
  MainTheory.QECCSmithBridge.smithBeta_betaExact,
  MainTheory.QECCSmithBridge.smithBeta_eq_betaOf
]
