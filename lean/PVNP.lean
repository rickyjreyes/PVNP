import PVNP.PartI
import PVNP.PartII
import PVNP.PartIII
import PVNP.PartIExtended
import PVNP.PartIIExtended
import PVNP.PartIIIExtended
import PVNP.CurvatureBarrier
import PVNP.Communication
import PVNP.Tseitin
import PVNP.PhysicalBounds
import PVNP.CurvatureCommunication
import PVNP.HamiltonianTransport
import PVNP.PhaseObservability
import PVNP.FixedMassNodal
import PVNP.ExpandingDomain
import PVNP.SplitSATCapacity
import PVNP.CrossingCapacity
import PVNP.CrossingTrace
import PVNP.CrossingSplice
import PVNP.CrossingDiagonal
import PVNP.CrossingHennie
import PVNP.CrossingSAT
import PVNP.CrossingSATSets
import PVNP.TMCellCompiler
import PVNP.ReplayCost
import PVNP.LocalityLowerBound
import PVNP.RadiusCausality
import PVNP.MultiStageCausality
import PVNP.TMGlobal
import PVNP.TMStayTrace
import PVNP.MachineCode
import PVNP.MachineDecoder
import PVNP.MachineTableDecoder
import PVNP.MachineDecoderSound
import PVNP.FiniteWCCCode
import PVNP.OracleObstruction
import PVNP.TMHeadMotion
import PVNP.TMHeadSupport
import PVNP.TMHeadUniqueRight
import PVNP.TMHeadUniqueLeft
import PVNP.TMHeadStep
import PVNP.TMMovingTrace
import PVNP.DiscreteMachines
import PVNP.TMtoWCC
import PVNP.WCCtoTM
import PVNP.ComplexityEquivalence
import PVNP.MachineSerialization
import PVNP.BandlimitedNoisyPacking
import PVNP.FourierReceiverProjection
import PVNP.DecisionVsEncodingCounterexample
import PVNP.PartIIIAnalytic
import PVNP.DiscreteCurvatureRail
import PVNP.PhysicalComplexityClasses
import PVNP.WitnessSizeUniformity
import PVNP.FourierTorusReceiver
import PVNP.PSubsetNP
import PVNP.CircleSpectralGap
import PVNP.WCTPlaneWave
import PVNP.TMScan
import PVNP.TMStackScan
import PVNP.SATVerifier
import PVNP.PartIIIHighFreq3D
import PVNP.TransportCalculus
import PVNP.ContinuumFlux
import PVNP.ContinuumFluxBudget
import PVNP.AnalogSplitSATCapacity
import PVNP.R03_CurvatureComplexity
import PVNP.R12_DiscreteEquivalence
import PVNP.R13_PhysicalComplexity
import PVNP.PhysicalModelAudit
import PVNP.WCCRadius
import PVNP.WCCGenerality
import PVNP.WCCDFiniteSupport
import PVNP.WCCDFiniteSnapshot
import PVNP.WCCDFiniteWork
import PVNP.SweepTM
import PVNP.WCCDCyclic
import PVNP.WCCDSweep
import PVNP.WCCDSweepSteps
import PVNP.WCCDSweepLoops
import PVNP.WCCDSweepRound
import PVNP.WCCDSweepBuild
import PVNP.WCCDSweepMain
import PVNP.PartIPsiSat
import PVNP.PartISeparation
import PVNP.WCTDependencyClosure
import PVNP.PartILocality
import PVNP.PartIDimLock
import PVNP.PartIIManuscript
import PVNP.ManuscriptRemarks
import PVNP.PartIITuringModel
import PVNP.PartIITwoPhase
import PVNP.PartIIUniform
import PVNP.UniformSimLib
import PVNP.UniformSimProg
import PVNP.UniformSimSem
import PVNP.UniformSimMath
import PVNP.UniformSimPre
import PVNP.UniformSimGrow
import PVNP.UniformSimLoad
import PVNP.UniformSimInit
import PVNP.UniformSimPack
import PVNP.UniformSimRot
import PVNP.UniformSimApply
import PVNP.UniformSimRound
import PVNP.UniformSimMain
import PVNP.PartIIUniformEquiv
import PVNP.WCTLattice
import PVNP.WCTLatticeGlobalBounds
import PVNP.WCTMeshScaling

import PVNP.DecoderUniformity

import PVNP.WCTLatticeGlobal

-- Phase VI: periodic torus well-posedness and F-1 continuum flux.
import PVNP.TorusWellPosed
import PVNP.TorusFlux

-- Phase IX: exact target statement and no-go theorems for candidate invariants.
import PVNP.SATTarget
import PVNP.TseitinSAT
import PVNP.VerifierCrossing

-- Phase X: first-answer Turing machine simulation by bounded-fan-in circuits.
import PVNP.TMBooleanTableau
import PVNP.SATProjection
import PVNP.CrossingSATMatrix

-- CL-1, part 1: the Cook–Levin tableau formula (mathematical reduction to dense SAT).
import PVNP.CookLevinTableau

-- CL-1, parts 2–3: the uniform Cook–Levin generator (a sweep program compiled to a single-tape
-- TM), its composition with a SAT_dense decider, and SATLowerBound ↔ P_TM ≠ NP_TM.
import PVNP.CookLevinKit
import PVNP.CookLevinHorner
import PVNP.CookLevinBits
import PVNP.CookLevinMain
import PVNP.CookLevinLabels
import PVNP.CookLevinGen
import PVNP.CookLevinDecide
import PVNP.CookLevinUniform

-- Part II, thm:conditional_np_safety (II-24): closure of P_TM under finite modification and the
-- conditional NP-safety theorem under the manuscript's premises (i)–(iii).
import PVNP.FiniteModification
import PVNP.ConditionalNPSafety

-- I-11: explicit diagonal obstruction to unrestricted physical encoders.
import PVNP.PhysicalDiagonal

-- Preserve prior Phase XI quadratic lower-bound and finite toroidal formalizations.
import PVNP.PhaseXIQuadratic
import PVNP.ToroidalDiagonal

-- I-3: formula-independent phase locking is not a SAT criterion.
import PVNP.PhaseLockScope

-- Phase X ranked-DAG construction: explicit register and tableau size bounds.
import PVNP.CircuitCookLevin

-- Original two-phase decoder, phase-energy readout and separator bounds.
import PVNP.TwoPhaseDecoder
import PVNP.TwoPhaseUniform
import PVNP.TwoPhaseRadius
import PVNP.PhasePenaltyMargin
import PVNP.SeparatorPrice
-- First-answer complexity with the two length/decider quantifier orders.
import PVNP.FiniteHorizonSAT
import PVNP.QuadraticHorizon

-- Phase XIII: uniform unsatisfiable logical-energy gap and certified readout.
import PVNP.PhasePenaltyGap

-- Phase XIII: exact one-dimensional canonical W_M lattice bitmap.
import PVNP.TwoPhaseWindowShape

-- Phase XIV: full canonical one-dimensional W_M window output word.
import PVNP.TwoPhaseWindowWord

-- Phase XIV: an actual finite-state zero-radius MTM lattice FP witness.
import PVNP.TwoPhaseConstantWindow

-- Phase XIV: literal-output finite-control MTM and constant-radius W_M FP candidate.
import PVNP.TwoPhaseFixedWord
