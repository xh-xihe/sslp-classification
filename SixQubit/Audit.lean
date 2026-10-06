import MainTheory.KernelAxiomAudit
import SixQubit.Order9
import SixQubit.Orbit8RaisingGram
import SixQubit.Orbit9MagnitudeCounts
import SixQubit.Orbit31MomentPolytope
import SixQubit.Generated.Orbit2Gram.All
import SixQubit.Generated.Orbit3SexticIdentity
import SixQubit.Generated.Orbit3Scalar
import SixQubit.Generated.Orbit3PositiveSquare
import SixQubit.ParityPauliScalars
import SixQubit.Orbit26
import SixQubit.Block33
import SixQubit.Orbit33
import SixQubit.Orbit34
import SixQubit.Orbit57
import SixQubit.Orbit59
import SixQubit.Orbit64
import SixQubit.Orbit40
import SixQubit.Orbit60
import SixQubit.Orbit63
import SixQubit.Orbit28
import SixQubit.Orbit7Marginal
import SixQubit.Orbit8OperatorQP

import SixQubit.Orbit39
import SixQubit.Orbit65
import SixQubit.Orbit55
import SixQubit.Orbit53
import SixQubit.Pair29
import SixQubit.Orbit29
import SixQubit.Orbit30

import SixQubit.Orbit61
import SixQubit.Orbit62

import SixQubit.Orbit27
import SixQubit.Orbit35

import SixQubit.Orbit54

import SixQubit.Table31
import SixQubit.Orbit31
import SixQubit.Orbit32

import SixQubit.Orbit58

import SixQubit.Orbit38

import SixQubit.Orbit37

import SixQubit.Orbit56

import SixQubit.Orbit25
import SixQubit.Orbit47
import SixQubit.Orbit48
import SixQubit.Orbit18
import SixQubit.Orbit41
import SixQubit.Orbit42
import SixQubit.Orbit43
import SixQubit.Orbit52
import SixQubit.Orbit44
import SixQubit.Orbit46
import SixQubit.Triangle
import SixQubit.Orbit50
import SixQubit.Orbit13
import SixQubit.Frame
import SixQubit.Orbit12
import SixQubit.Orbit14
import SixQubit.Orbit15
import SixQubit.Orbit17
import SixQubit.Orbit19
import SixQubit.Orbit20
import SixQubit.Orbit24
import SixQubit.Orbit49
import SixQubit.Orbit51
import SixQubit.Spinor
import SixQubit.ParityFour
import SixQubit.Hafnian
import SixQubit.Trace5
import SixQubit.Orbit5
import SixQubit.Orbit6
import SixQubit.Flip5
import SixQubit.Kernel5
import SixQubit.CodeOrbit12
import SixQubit.CodeOrbit13
import SixQubit.CodeOrbit14
import SixQubit.CodeOrbit15
import SixQubit.CodeOrbit17
import SixQubit.CodeOrbit18
import SixQubit.CodeOrbit19
import SixQubit.CodeOrbit20
import SixQubit.CodeOrbit24
import SixQubit.CodeOrbit25
import SixQubit.CodeOrbit26
import SixQubit.CodeOrbit27
import SixQubit.CodeOrbit28
import SixQubit.CodeOrbit29
import SixQubit.CodeOrbit30
import SixQubit.CodeOrbit31
import SixQubit.CodeOrbit32
import SixQubit.CodeOrbit33
import SixQubit.CodeOrbit34
import SixQubit.CodeOrbit35
import SixQubit.CodeOrbit37
import SixQubit.CodeOrbit38
import SixQubit.CodeOrbit39
import SixQubit.CodeOrbit40
import SixQubit.CodeOrbit41
import SixQubit.CodeOrbit42
import SixQubit.CodeOrbit43
import SixQubit.CodeOrbit44
import SixQubit.CodeOrbit46
import SixQubit.CodeOrbit47
import SixQubit.CodeOrbit48
import SixQubit.CodeOrbit49
import SixQubit.CodeOrbit5
import SixQubit.CodeOrbit50
import SixQubit.CodeOrbit51
import SixQubit.CodeOrbit52
import SixQubit.CodeOrbit53
import SixQubit.CodeOrbit54
import SixQubit.CodeOrbit55
import SixQubit.CodeOrbit56
import SixQubit.CodeOrbit57
import SixQubit.CodeOrbit58
import SixQubit.CodeOrbit59
import SixQubit.CodeOrbit6
import SixQubit.CodeOrbit60
import SixQubit.CodeOrbit61
import SixQubit.CodeOrbit62
import SixQubit.CodeOrbit63
import SixQubit.CodeOrbit64
import SixQubit.CodeOrbit65
import SixQubit.Vacuity
import SixQubit.CodeOrder9
import SixQubit.K4Kernel
import SixQubit.Orbit36Code
import SixQubit.Orbit36
import SixQubit.Orbit36Phase
import SixQubit.Orbit36Enum
import SixQubit.CodeEquiv
import SixQubit.Orbit36Class
import SixQubit.Orbit36Enum4
import SixQubit.MacWilliams
import SixQubit.Orbit36Final
import SixQubit.Orbit36Vacuity
import SixQubit.CodeOrbit36
import SixQubit.Realize
import SixQubit.Shadow
import SixQubit.ShadowTwisted
import SixQubit.Averaging
import SixQubit.Orbit21Sym
import SixQubit.Orbit21Cert
import SixQubit.Orbit21Coef
import SixQubit.Orbit21Bound
import SixQubit.Orbit21Bridge
import SixQubit.Orbit21Chain
import SixQubit.Orbit21Walsh
import SixQubit.Orbit21Residual
import SixQubit.Orbit21Farkas
import SixQubit.Orbit21Enum
import SixQubit.Pin
import SixQubit.Orbit10Enum
import SixQubit.Orbit11Enum
import SixQubit.Orbit16Enum
import SixQubit.Orbit22Enum
import SixQubit.Orbit23Enum
import SixQubit.BEnumerator
import SixQubit.CodeEquivEnum
import SixQubit.Orbit36Transport
import SixQubit.Orbit36Certified
import SixQubit.Orbit7Attain
import SixQubit.Orbit8Attain
import SixQubit.Orbit9Attain
import SixQubit.Orbit7Real
import SixQubit.Orbit8Real
import SixQubit.Orbit9Real
import SixQubit.Orbit7UniversalFinal
import SixQubit.Orbit9UniversalFinal
import SixQubit.Orbit8UniversalFinal
import SixQubit.Orbit10Real
import SixQubit.Orbit11Real
import SixQubit.Orbit16Real
import SixQubit.Orbit21Real
import SixQubit.Orbit22Real
import SixQubit.Orbit23Real
import SixQubit.Orbit45Real
import SixQubit.Orbit45Final
import SixQubit.Bridge

open SixQubit

#certification_axioms [
  SixQubit.Order9.S0_eq_fiber,
  SixQubit.Order9.MomentSystem.solution,
  SixQubit.Order9.MomentSystem.pos,
  SixQubit.Order9.no_go_of_moments,
  SixQubit.Block33.block_contradiction,
  SixQubit.Orbit33.S0_eq_fiber,
  SixQubit.Orbit33.S1_eq_fiber,
  SixQubit.Orbit33.refl01_0,
  SixQubit.Orbit33.refl01_3,
  SixQubit.Orbit33.no_go_of_moments,
  SixQubit.Orbit34.S0_eq_fiber,
  SixQubit.Orbit34.MomentSystem.solution,
  SixQubit.Orbit34.MomentSystem.pos,
  SixQubit.Orbit34.no_go_of_moments,
  SixQubit.Orbit57.S0_eq_fiber,
  SixQubit.Orbit57.MomentSystem.solution,
  SixQubit.Orbit57.MomentSystem.pos,
  SixQubit.Orbit57.no_go_of_moments,
  SixQubit.Orbit59.S0_eq_fiber,
  SixQubit.Orbit59.MomentSystem.solution,
  SixQubit.Orbit59.MomentSystem.pos,
  SixQubit.Orbit59.no_go_of_moments,
  SixQubit.Orbit64.S0_eq_fiber,
  SixQubit.Orbit64.MomentSystem.solution,
  SixQubit.Orbit64.MomentSystem.pos,
  SixQubit.Orbit64.no_go_of_moments,
  SixQubit.Orbit40.S0_eq_fiber,
  SixQubit.Orbit40.S1_residue,
  SixQubit.Orbit40.MomentSystem.endpoints,
  SixQubit.Orbit40.MomentSystem.endpoints_pos,
  SixQubit.Orbit40.no_go_of_moments,
  SixQubit.Orbit60.S0_eq_fiber,
  SixQubit.Orbit60.S1_residue,
  SixQubit.Orbit60.MomentSystem.endpoints,
  SixQubit.Orbit60.MomentSystem.endpoints_pos,
  SixQubit.Orbit60.no_go_of_moments,
  SixQubit.Orbit63.S0_eq_fiber,
  SixQubit.Orbit63.S1_residue,
  SixQubit.Orbit63.MomentSystem.endpoints,
  SixQubit.Orbit63.MomentSystem.endpoints_pos,
  SixQubit.Orbit63.no_go_of_moments,
  SixQubit.Orbit28.S0_eq_fiber,
  SixQubit.Orbit28.S1_eq_fiber,
  SixQubit.Orbit28.MomentSystem.spurious_zero,
  SixQubit.Orbit28.MomentSystem.endpoints,
  SixQubit.Orbit28.MomentSystem.endpoints_pos,
  SixQubit.Orbit28.no_go_of_moments,
  SixQubit.Orbit39.S0_eq_fiber,
  SixQubit.Orbit39.S1_eq_fiber,
  SixQubit.Orbit39.MomentSystem.endpoints,
  SixQubit.Orbit39.MomentSystem.endpoints_pos,
  SixQubit.Orbit39.target_zero,
  SixQubit.Orbit39.no_go_of_moments,
  SixQubit.Orbit65.S0_eq_fiber,
  SixQubit.Orbit65.S1_eq_fiber,
  SixQubit.Orbit65.MomentSystem.endpoints,
  SixQubit.Orbit65.MomentSystem.endpoints_pos,
  SixQubit.Orbit65.target_zero,
  SixQubit.Orbit65.no_go_of_moments,
  SixQubit.Orbit55.S0_eq_fiber,
  SixQubit.Orbit55.S1_eq_fiber,
  SixQubit.Orbit55.MomentSystem.endpoints,
  SixQubit.Orbit55.MomentSystem.endpoints_pos,
  SixQubit.Orbit55.target_zero,
  SixQubit.Orbit55.no_go_of_moments,
  SixQubit.Orbit53.S0_eq_fiber,
  SixQubit.Orbit53.S1_eq_fiber,
  SixQubit.Orbit53.MomentSystem.endpoints,
  SixQubit.Orbit53.MomentSystem.endpoints_pos,
  SixQubit.Orbit53.target_zero,
  SixQubit.Orbit53.no_go_of_moments,
  SixQubit.Pair29.par_edge,
  SixQubit.Pair29.endgame,
  SixQubit.Pair29.pair_contradiction,
  SixQubit.Orbit29.S0_eq_fiber,
  SixQubit.Orbit29.S1_eq_fiber,
  SixQubit.Orbit29.mq,
  SixQubit.Orbit29.me,
  SixQubit.Orbit29.no_go_of_moments,
  SixQubit.Orbit30.S0_eq_fiber,
  SixQubit.Orbit30.S1_eq_fiber,
  SixQubit.Orbit30.MomentSystem.endpoints,
  SixQubit.Orbit30.MomentSystem.endpoints_pos,
  SixQubit.Orbit30.target_zero,
  SixQubit.Orbit30.no_go_of_moments,
  SixQubit.Orbit61.S0_eq_fiber,
  SixQubit.Orbit61.S1_eq_fiber,
  SixQubit.Orbit61.MomentSystem.pos,
  SixQubit.Orbit61.no_go_of_moments,
  SixQubit.Orbit62.S0_eq_fiber,
  SixQubit.Orbit62.S1_eq_fiber,
  SixQubit.Orbit62.MomentSystem.pos,
  SixQubit.Orbit62.no_go_of_moments,
  SixQubit.Orbit27.S0_eq_fiber,
  SixQubit.Orbit27.S1_eq_fiber,
  SixQubit.Orbit27.MomentSystem.anchors,
  SixQubit.Orbit27.MomentSystem.infeasible,
  SixQubit.Orbit27.no_go_of_moments,
  SixQubit.Orbit35.S0_eq_fiber,
  SixQubit.Orbit35.S1_eq_fiber,
  SixQubit.Orbit35.MomentSystem.anchors,
  SixQubit.Orbit35.MomentSystem.infeasible,
  SixQubit.Orbit35.no_go_of_moments,
  SixQubit.Orbit35.MomentSystem.stage0,
  SixQubit.Orbit54.S0_eq_fiber,
  SixQubit.Orbit54.S1_eq_fiber,
  SixQubit.Orbit54.pinned,
  SixQubit.Orbit54.no_go_of_moments,
  SixQubit.Table31.gram_eq,
  SixQubit.Table31.M_eq_of_raw,
  SixQubit.Orbit31.S0_eq_fiber,
  SixQubit.Orbit31.S1_eq_fiber,
  SixQubit.Orbit31.no_go_of_moments,
  SixQubit.Orbit32.S0_eq_fiber,
  SixQubit.Orbit32.S1_eq_fiber,
  SixQubit.Orbit32.local_nogo,
  SixQubit.Orbit32.MomentSystem.reflection,
  SixQubit.Orbit32.MomentSystem.rowsum,
  SixQubit.Orbit32.MomentSystem.some_pos,
  SixQubit.Orbit32.no_go_of_moments,
  SixQubit.Orbit58.S0_eq_fiber,
  SixQubit.Orbit58.S1_eq_fiber,
  SixQubit.Orbit58.pinned,
  SixQubit.Orbit58.collapse,
  SixQubit.Orbit58.no_go_of_moments,
  SixQubit.Orbit38.S0_eq_fiber,
  SixQubit.Orbit38.S1_eq_fiber,
  SixQubit.Orbit38.MomentSystem.facts,
  SixQubit.Orbit38.hub,
  SixQubit.Orbit38.bridge2,
  SixQubit.Orbit38.no_go_of_moments,
  SixQubit.Orbit37.S0_eq_fiber,
  SixQubit.Orbit37.S1_eq_fiber,
  SixQubit.Orbit37.MomentSystem.facts,
  SixQubit.Orbit37.MomentSystem.columns,
  SixQubit.Orbit37.grid_rec,
  SixQubit.Orbit37.hub,
  SixQubit.Orbit37.to_bottom,
  SixQubit.Orbit37.two_active,
  SixQubit.Orbit37.three_active,
  SixQubit.Orbit37.no_go_of_moments,
  SixQubit.Orbit56.S0_eq_fiber,
  SixQubit.Orbit56.S1_eq_fiber,
  SixQubit.Orbit56.MomentSystem.hubpos,
  SixQubit.Orbit56.hub,
  SixQubit.Orbit56.to_bottom,
  SixQubit.Orbit56.no_go_of_moments,
  SixQubit.Orbit25.S0_eq_fiber,
  SixQubit.Orbit25.S1_eq_fiber,
  SixQubit.Orbit25.pinned,
  SixQubit.Orbit25.hb6,
  SixQubit.Orbit25.drel,
  SixQubit.Orbit25.erel,
  SixQubit.Orbit25.erel5,
  SixQubit.Orbit25.no_go_of_moments,
  SixQubit.Orbit26.S0_eq_fiber,
  SixQubit.Orbit26.S1_eq_fiber,
  SixQubit.Orbit26.quad,
  SixQubit.Orbit26.ipw,
  SixQubit.Orbit26.sandwich,
  SixQubit.Orbit26.core,
  SixQubit.Orbit26.no_go_of_moments,
  SixQubit.Orbit47.no_go_of_moments,
  SixQubit.Orbit47.S0_eq_fiber,
  SixQubit.Orbit47.S1_eq_fiber,
  SixQubit.Orbit48.no_go_of_moments,
  SixQubit.Orbit48.S0_eq_fiber,
  SixQubit.Orbit48.S1_eq_fiber,
  SixQubit.Orbit18.no_go_of_moments,
  SixQubit.Orbit18.S0_eq_fiber,
  SixQubit.Orbit18.S1_eq_fiber,
  SixQubit.Orbit41.no_go_of_moments,
  SixQubit.Orbit41.S0_eq_fiber,
  SixQubit.Orbit41.S1_eq_fiber,
  SixQubit.Orbit42.no_go_of_moments,
  SixQubit.Orbit42.S0_eq_fiber,
  SixQubit.Orbit42.S1_eq_fiber,
  SixQubit.Orbit43.no_go_of_moments,
  SixQubit.Orbit43.S0_eq_fiber,
  SixQubit.Orbit43.S1_eq_fiber,
  SixQubit.Orbit52.no_go_of_moments,
  SixQubit.Orbit52.S0_eq_fiber,
  SixQubit.Orbit52.S1_eq_fiber,
  SixQubit.Orbit44.no_go_of_moments,
  SixQubit.Orbit44.S0_eq_fiber,
  SixQubit.Orbit44.S1_eq_fiber,
  SixQubit.Orbit46.no_go_of_moments,
  SixQubit.Orbit46.S0_eq_fiber,
  SixQubit.Orbit46.S1_eq_fiber,
  SixQubit.Triangle.contradiction_of_normSq,
  SixQubit.Orbit50.no_go_of_moments,
  SixQubit.Orbit50.S0_eq_fiber,
  SixQubit.Orbit50.S1_eq_fiber,
  SixQubit.Orbit13.no_go_of_moments,
  SixQubit.Orbit13.S0_eq_fiber,
  SixQubit.Orbit13.S1_eq_fiber,
  SixQubit.Frame.block_zero,
  SixQubit.Orbit6.no_go_of_moments,
  SixQubit.Orbit6.S0_eq_fiber,
  SixQubit.Orbit6.S1_eq_fiber,
  SixQubit.Orbit12.no_go_of_moments,
  SixQubit.Orbit12.S0_eq_fiber,
  SixQubit.Orbit12.S1_eq_fiber,
  SixQubit.Orbit14.no_go_of_moments,
  SixQubit.Orbit14.S0_eq_fiber,
  SixQubit.Orbit14.S1_eq_fiber,
  SixQubit.Orbit15.no_go_of_moments,
  SixQubit.Orbit15.S0_eq_fiber,
  SixQubit.Orbit15.S1_eq_fiber,
  SixQubit.Orbit17.no_go_of_moments,
  SixQubit.Orbit17.S0_eq_fiber,
  SixQubit.Orbit17.S1_eq_fiber,
  SixQubit.Orbit19.no_go_of_moments,
  SixQubit.Orbit19.S0_eq_fiber,
  SixQubit.Orbit19.S1_eq_fiber,
  SixQubit.Orbit20.no_go_of_moments,
  SixQubit.Orbit20.S0_eq_fiber,
  SixQubit.Orbit20.S1_eq_fiber,
  SixQubit.Orbit24.no_go_of_moments,
  SixQubit.Orbit24.S0_eq_fiber,
  SixQubit.Orbit24.S1_eq_fiber,
  SixQubit.Orbit49.no_go_of_moments,
  SixQubit.Orbit49.S0_eq_fiber,
  SixQubit.Orbit49.S1_eq_fiber,
  SixQubit.Orbit51.no_go_of_moments,
  SixQubit.Orbit51.S0_eq_fiber,
  SixQubit.Orbit51.S1_eq_fiber,
  SixQubit.Orbit5.S0_eq_fiber,
  SixQubit.Orbit5.S1_eq_fiber,
  SixQubit.Orbit5.no_go_of_moments,
  SixQubit.Orbit12.no_code,
  SixQubit.Orbit13.no_code,
  SixQubit.Orbit14.no_code,
  SixQubit.Orbit15.no_code,
  SixQubit.Orbit17.no_code,
  SixQubit.Orbit18.no_code,
  SixQubit.Orbit19.no_code,
  SixQubit.Orbit20.no_code,
  SixQubit.Orbit24.no_code,
  SixQubit.Orbit25.no_code,
  SixQubit.Orbit26.no_code,
  SixQubit.Orbit27.no_code,
  SixQubit.Orbit28.no_code,
  SixQubit.Orbit29.no_code,
  SixQubit.Orbit30.no_code,
  SixQubit.Orbit31.no_code,
  SixQubit.Orbit32.no_code,
  SixQubit.Orbit33.no_code,
  SixQubit.Orbit34.no_code,
  SixQubit.Orbit35.no_code,
  SixQubit.Orbit37.no_code,
  SixQubit.Orbit38.no_code,
  SixQubit.Orbit39.no_code,
  SixQubit.Orbit40.no_code,
  SixQubit.Orbit41.no_code,
  SixQubit.Orbit42.no_code,
  SixQubit.Orbit43.no_code,
  SixQubit.Orbit44.no_code,
  SixQubit.Orbit46.no_code,
  SixQubit.Orbit47.no_code,
  SixQubit.Orbit48.no_code,
  SixQubit.Orbit49.no_code,
  SixQubit.Orbit5.no_code,
  SixQubit.Orbit50.no_code,
  SixQubit.Orbit51.no_code,
  SixQubit.Orbit52.no_code,
  SixQubit.Orbit53.no_code,
  SixQubit.Orbit54.no_code,
  SixQubit.Orbit55.no_code,
  SixQubit.Orbit56.no_code,
  SixQubit.Orbit57.no_code,
  SixQubit.Orbit58.no_code,
  SixQubit.Orbit59.no_code,
  SixQubit.Orbit6.no_code,
  SixQubit.Orbit60.no_code,
  SixQubit.Orbit61.no_code,
  SixQubit.Orbit62.no_code,
  SixQubit.Orbit63.no_code,
  SixQubit.Orbit64.no_code,
  SixQubit.Orbit65.no_code,
  SixQubit.Order9.no_code,
  SixQubit.Vacuity.live_Orbit5,
  SixQubit.Vacuity.live_Orbit6,
  SixQubit.Vacuity.live_Orbit12,
  SixQubit.Vacuity.live_Orbit13,
  SixQubit.Vacuity.live_Orbit14,
  SixQubit.Vacuity.live_Orbit15,
  SixQubit.Vacuity.live_Orbit17,
  SixQubit.Vacuity.live_Orbit18,
  SixQubit.Vacuity.live_Orbit19,
  SixQubit.Vacuity.live_Orbit20,
  SixQubit.Vacuity.live_Orbit24,
  SixQubit.Vacuity.live_Orbit25,
  SixQubit.Vacuity.live_Orbit26,
  SixQubit.Vacuity.live_Orbit27,
  SixQubit.Vacuity.live_Orbit28,
  SixQubit.Vacuity.live_Orbit29,
  SixQubit.Vacuity.live_Orbit30,
  SixQubit.Vacuity.live_Orbit31,
  SixQubit.Vacuity.live_Orbit32,
  SixQubit.Vacuity.live_Orbit33,
  SixQubit.Vacuity.live_Orbit34,
  SixQubit.Vacuity.live_Orbit35,
  SixQubit.Vacuity.live_Orbit37,
  SixQubit.Vacuity.live_Orbit38,
  SixQubit.Vacuity.live_Orbit39,
  SixQubit.Vacuity.live_Orbit40,
  SixQubit.Vacuity.live_Orbit41,
  SixQubit.Vacuity.live_Orbit42,
  SixQubit.Vacuity.live_Orbit43,
  SixQubit.Vacuity.live_Orbit44,
  SixQubit.Vacuity.live_Orbit46,
  SixQubit.Vacuity.live_Orbit47,
  SixQubit.Vacuity.live_Orbit48,
  SixQubit.Vacuity.live_Orbit49,
  SixQubit.Vacuity.live_Orbit50,
  SixQubit.Vacuity.live_Orbit51,
  SixQubit.Vacuity.live_Orbit52,
  SixQubit.Vacuity.live_Orbit53,
  SixQubit.Vacuity.live_Orbit54,
  SixQubit.Vacuity.live_Orbit55,
  SixQubit.Vacuity.live_Orbit56,
  SixQubit.Vacuity.live_Orbit57,
  SixQubit.Vacuity.live_Orbit58,
  SixQubit.Vacuity.live_Orbit59,
  SixQubit.Vacuity.live_Orbit60,
  SixQubit.Vacuity.live_Orbit61,
  SixQubit.Vacuity.live_Orbit62,
  SixQubit.Vacuity.live_Orbit63,
  SixQubit.Vacuity.live_Orbit64,
  SixQubit.Vacuity.live_Orbit65,
  SixQubit.Vacuity.live_Order9,
  SixQubit.Orbit36Code.canonical_is_code,
  SixQubit.Orbit36Code.c36_normalized,
  SixQubit.Orbit36Code.d36_normalized,
  SixQubit.Orbit36Code.S0_eq_fiber,
  SixQubit.Orbit36Code.S1_eq_fiber,
  SixQubit.Orbit36.magnitudes_forced,
  SixQubit.Orbit36.full_support,
  SixQubit.Orbit36Phase.A1_eq_zero,
  SixQubit.K4Kernel.sumSq_eq_zero,
  SixQubit.K4Kernel.det_K4,
  SixQubit.Orbit36Enum.A2_value,
  SixQubit.Orbit36Enum.A3_value,
  SixQubit.Orbit36Enum.top_form,
  SixQubit.Orbit36Enum.unique_enumerator,
  SixQubit.CodeEquiv.hasDistance_iff,
  SixQubit.CodeEquiv.detectsRaw_permAct,
  SixQubit.CodeEquiv.detectsRaw_dAct,
  SixQubit.CodeEquiv.detectsRaw_swap,
  SixQubit.Orbit36Class.orbit36_rigidity,
  SixQubit.Orbit36Class.orbit36_theorem,
  SixQubit.Orbit36Class.solution_hasDistance,
  SixQubit.Orbit36Enum4.A4_value,
  SixQubit.Orbit36Enum4.A5_value,
  SixQubit.Orbit36Enum4.A6_value,
  SixQubit.Orbit36Enum4.enumerator_value,
  SixQubit.Orbit36Final.orbit36_rigidity,
  SixQubit.Orbit36Final.orbit36_enumerator,
  SixQubit.Orbit36Final.enumerator_sum,
  SS.MacWilliams.subset_macwilliams,
  SS.MacWilliams.macwilliams_six,
  SixQubit.Orbit36Vacuity.canonical_moments,
  SixQubit.Orbit36Vacuity.canonical_offSum,
  SixQubit.Orbit36Vacuity.hypotheses_satisfiable,
  SixQubit.Orbit36Vacuity.rigidity_nonvacuous,
  SixQubit.Orbit36.moments,
  SixQubit.Orbit36.klRows,
  SixQubit.Orbit36.rigid_code,
  SixQubit.Realize.is_code_of_check,
  SixQubit.Realize.normalized_of,
  SixQubit.Realize.matElt_eq,
  SixQubit.Orbit7Real.is_code,
  SixQubit.Orbit7Real.w0_normalized,
  SixQubit.Orbit7Real.w1_normalized,
  SixQubit.Orbit7Real.L0_in_fiber,
  SixQubit.Orbit7Real.L1_in_fiber,
  SixQubit.Orbit7Real.check_all,
  SixQubit.Orbit8Real.is_code,
  SixQubit.Orbit8Real.w0_normalized,
  SixQubit.Orbit8Real.w1_normalized,
  SixQubit.Orbit8Real.L0_in_fiber,
  SixQubit.Orbit8Real.L1_in_fiber,
  SixQubit.Orbit8Real.check_all,
  SixQubit.Orbit9Real.is_code,
  SixQubit.Orbit9Real.w0_normalized,
  SixQubit.Orbit9Real.w1_normalized,
  SixQubit.Orbit9Real.L0_in_fiber,
  SixQubit.Orbit9Real.L1_in_fiber,
  SixQubit.Orbit9Real.check_all,
  SixQubit.Orbit10Real.is_code,
  SixQubit.Orbit10Real.w0_normalized,
  SixQubit.Orbit10Real.w1_normalized,
  SixQubit.Orbit10Real.L0_in_fiber,
  SixQubit.Orbit10Real.L1_in_fiber,
  SixQubit.Orbit10Real.check_all,
  SixQubit.Orbit11Real.is_code,
  SixQubit.Orbit11Real.w0_normalized,
  SixQubit.Orbit11Real.w1_normalized,
  SixQubit.Orbit11Real.L0_in_fiber,
  SixQubit.Orbit11Real.L1_in_fiber,
  SixQubit.Orbit11Real.check_all,
  SixQubit.Orbit16Real.is_code,
  SixQubit.Orbit16Real.w0_normalized,
  SixQubit.Orbit16Real.w1_normalized,
  SixQubit.Orbit16Real.L0_in_fiber,
  SixQubit.Orbit16Real.L1_in_fiber,
  SixQubit.Orbit16Real.check_all,
  SixQubit.Orbit21Real.is_code,
  SixQubit.Orbit21Real.w0_normalized,
  SixQubit.Orbit21Real.w1_normalized,
  SixQubit.Orbit21Real.L0_in_fiber,
  SixQubit.Orbit21Real.L1_in_fiber,
  SixQubit.Orbit21Real.check_all,
  SixQubit.Orbit22Real.is_code,
  SixQubit.Orbit22Real.w0_normalized,
  SixQubit.Orbit22Real.w1_normalized,
  SixQubit.Orbit22Real.L0_in_fiber,
  SixQubit.Orbit22Real.L1_in_fiber,
  SixQubit.Orbit22Real.check_all,
  SixQubit.Orbit23Real.is_code,
  SixQubit.Orbit23Real.w0_normalized,
  SixQubit.Orbit23Real.w1_normalized,
  SixQubit.Orbit23Real.L0_in_fiber,
  SixQubit.Orbit23Real.L1_in_fiber,
  SixQubit.Orbit23Real.check_all,
  SixQubit.Orbit45Real.is_code,
  SixQubit.Orbit45Real.w0_normalized,
  SixQubit.Orbit45Real.w1_normalized,
  SixQubit.Orbit45Real.L0_in_fiber,
  SixQubit.Orbit45Real.L1_in_fiber,
  SixQubit.Orbit45Real.check_all,
  SS.Shadow.core_eq_sum_normSq,
  SS.Shadow.core_eq_nonneg_real,
  SS.Shadow.melTr_eq_RR,
  SS.Shadow.sum4_comm,
  SS.Shadow.altsign_factor,
  SS.Shadow.star_melTr_eq,
  SS.Shadow.normSq_melTr_expand,
  SS.Shadow.z_sum_collapse,
  SS.Shadow.alt_sum_eq_core,
  SS.Shadow.alt_sum_nonneg,
  SS.Shadow.alt_sum_as_Aco,
  SS.Shadow.shadow_bound,
  SS.ShadowTwisted.altsignT_factor,
  SS.ShadowTwisted.coreT_eq_sum_normSq,
  SS.ShadowTwisted.zT_sum_collapse,
  SS.ShadowTwisted.altT_sum_eq_coreT,
  SS.ShadowTwisted.altT_sum_nonneg,
  SixQubit.Averaging.sum_shift,
  SixQubit.Averaging.sum_average_four,
  SixQubit.Averaging.sum_eq_zero_of_average,
  SixQubit.Orbit21Sym.melTr_shift,
  SixQubit.Orbit21Sym.normSq_trProj_shift,
  SixQubit.Orbit21Cert.bdot_gmask,
  SixQubit.Orbit21Cert.bdot_band_gmask,
  SixQubit.Orbit21Cert.chi_gmask_one,
  SixQubit.Orbit21Cert.chi_band_one,
  SixQubit.Orbit21Coef.coef_group_sum,
  SixQubit.Orbit21Bound.bound_of_certificate,
  SixQubit.Orbit21Bound.residual_eq_zero,
  SixQubit.Orbit21Bound.enumerator_of_A2_bound,
  SixQubit.Orbit21Bridge.num_bxor,
  SixQubit.Orbit21Bridge.num_band,
  SixQubit.Orbit21Bridge.cf_group_sum,
  SixQubit.Orbit21Chain.residual_vanishes,
  SixQubit.Orbit21Walsh.fourierCoef_zero,
  SixQubit.Orbit21Residual.walsh_zero_on_pairs,
  SixQubit.Orbit21Residual.residual_vanishes,
  SixQubit.Orbit21Farkas.residual_expansion,
  SixQubit.Orbit21Farkas.positiveRhs_nonneg,
  SixQubit.Orbit21Farkas.certificate_identity,
  SixQubit.Orbit21Farkas.four_le_Aco_two,
  SixQubit.Orbit21Enum.enumerator_pair_unique_fiber,
  SixQubit.Orbit21Enum.enumerator_pair_attained,
  SixQubit.Orbit21Enum.fully_certified,
  SixQubit.Pin.Aco_zero,
  SixQubit.Pin.four_le_Aco,
  SixQubit.Pin.zstring_fixes,
  SixQubit.Pin.pin_low,
  SixQubit.Pin.enumerator_of_forced,
  SixQubit.Pin.pin_line,
  SixQubit.Pin.pin_low_of_bound,
  SixQubit.Pin.pin_low_neg,
  SixQubit.Pin.zstring_negates,
  SixQubit.Pin.four_le_Aco_neg,
  SixQubit.Pin.enumerator_of_forced_neg,
  SixQubit.Orbit7Attain.zmask_L0,
  SixQubit.Orbit7Attain.zmask_L1,
  SixQubit.Orbit7Attain.zmask_wt,
  SixQubit.Orbit7Attain.enumerator,
  SixQubit.Orbit8Attain.zmask_L0,
  SixQubit.Orbit8Attain.zmask_L1,
  SixQubit.Orbit8Attain.zmask_wt,
  SixQubit.Orbit8Attain.enumerator,
  SixQubit.Orbit9Attain.zmask_L0,
  SixQubit.Orbit9Attain.zmask_L1,
  SixQubit.Orbit9Attain.zmask_wt,
  SixQubit.Orbit9Attain.enumerator,
  SixQubit.Orbit9Universal.active_card_ne_two,
  SixQubit.Orbit9Universal.equal_pair_of_card_four,
  SixQubit.Orbit9Universal.original_universal_certification,
  SixQubit.Orbit9Universal.uniform_weightTwo_scalar,
  SixQubit.Orbit9Universal.fully_kernel_certified,
  SixQubit.Orbit8Universal.singleton_support_le_two,
  SixQubit.Orbit8Universal.universal_converse,
  SixQubit.Orbit8Universal.interval_attainment,
  SixQubit.Orbit8Universal.fully_certified,
  SixQubit.Orbit7Universal.full_support_independent_target,
  SixQubit.Orbit7Universal.pairRankTwo_of_targetStar,
  SixQubit.Orbit7Universal.uniform_universal_converse,
  SixQubit.Orbit7Universal.original_universal_converse,
  SixQubit.Orbit7Universal.interval_attainment,
  SixQubit.Orbit7Universal.fully_certified,
  SixQubit.Orbit10Enum.L0_eq_fiber,
  SixQubit.Orbit10Enum.L1_eq_fiber,
  SixQubit.Orbit10Enum.enumerator_unique_fiber,
  SixQubit.Orbit11Enum.L0_eq_fiber,
  SixQubit.Orbit11Enum.L1_eq_fiber,
  SixQubit.Orbit11Enum.enumerator_unique_fiber,
  SixQubit.Orbit16Enum.L0_eq_fiber,
  SixQubit.Orbit16Enum.L1_eq_fiber,
  SixQubit.Orbit16Enum.enumerator_unique_fiber,
  SixQubit.Orbit22Enum.L0_eq_fiber,
  SixQubit.Orbit22Enum.L1_eq_fiber,
  SixQubit.Orbit22Enum.enumerator_unique_fiber,
  SixQubit.Orbit23Enum.L0_eq_fiber,
  SixQubit.Orbit23Enum.L1_eq_fiber,
  SixQubit.Orbit23Enum.enumerator_unique_fiber,
  SixQubit.Orbit10Enum.zmask_L0,
  SixQubit.Orbit10Enum.zmask_L1,
  SixQubit.Orbit10Enum.zmask_wt,
  SixQubit.Orbit10Enum.enumerator_unique,
  SixQubit.Orbit10Enum.enumerator_attained,
  SixQubit.Orbit11Enum.zmask_L0,
  SixQubit.Orbit11Enum.zmask_L1,
  SixQubit.Orbit11Enum.zmask_wt,
  SixQubit.Orbit11Enum.enumerator_unique,
  SixQubit.Orbit11Enum.enumerator_attained,
  SixQubit.Orbit16Enum.zmask_L0,
  SixQubit.Orbit16Enum.zmask_L1,
  SixQubit.Orbit16Enum.zmask_wt,
  SixQubit.Orbit16Enum.enumerator_unique,
  SixQubit.Orbit16Enum.enumerator_attained,
  SixQubit.Orbit22Enum.zmask_L0,
  SixQubit.Orbit22Enum.zmask_L1,
  SixQubit.Orbit22Enum.zmask_wt,
  SixQubit.Orbit22Enum.enumerator_unique,
  SixQubit.Orbit22Enum.enumerator_attained,
  SixQubit.Orbit23Enum.zmask_L0,
  SixQubit.Orbit23Enum.zmask_L1,
  SixQubit.Orbit23Enum.zmask_wt,
  SixQubit.Orbit23Enum.enumerator_unique,
  SixQubit.Orbit23Enum.enumerator_attained,
  SS.MacWilliams.summed_duality_six,
  SS.MacWilliams.bco_transform_six,
  SS.MacWilliams.e1B_of_e1A,
  SS.MacWilliams.e2B_of_e2A,
  SixQubit.Orbit10Enum.enumerator_pair_unique_fiber,
  SixQubit.Orbit10Enum.enumerator_pair_attained,
  SixQubit.Orbit11Enum.enumerator_pair_unique_fiber,
  SixQubit.Orbit11Enum.enumerator_pair_attained,
  SixQubit.Orbit16Enum.enumerator_pair_unique_fiber,
  SixQubit.Orbit16Enum.enumerator_pair_attained,
  SixQubit.Orbit22Enum.enumerator_pair_unique_fiber,
  SixQubit.Orbit22Enum.enumerator_pair_attained,
  SixQubit.Orbit23Enum.enumerator_pair_unique_fiber,
  SixQubit.Orbit23Enum.enumerator_pair_attained,
  SixQubit.Orbit45Final.universal_converse_full_fibres,
  SixQubit.Orbit45Final.interval_attainment_full_fibres,
  SixQubit.Orbit45Final.fully_certified,
  SixQubit.CodeEquiv.Equivalent.symm,
  SixQubit.CodeEquiv.Equivalent.trans,
  SixQubit.CodeEquiv.Aco_permAct,
  SixQubit.CodeEquiv.Aco_flipAct,
  SixQubit.CodeEquiv.Aco_swap,
  SixQubit.CodeEquiv.Bco_permAct,
  SixQubit.CodeEquiv.Bco_flipAct,
  SixQubit.CodeEquiv.Bco_swap,
  SixQubit.Orbit36Transport.weight_transport,
  SixQubit.Orbit36Transport.equivalent_transport,
  SixQubit.Orbit36Transport.original_table_nonempty,
  SixQubit.Orbit36Transport.original_magnitudes,
  SixQubit.Orbit36Transport.original_full_support,
  SixQubit.Orbit36Certified.Aco_transport,
  SixQubit.Orbit36Certified.Bco_transport,
  SixQubit.Orbit36Certified.orbit36B_of_A,
  SixQubit.Orbit36Certified.original_A,
  SixQubit.Orbit36Certified.original_enumerator_pair,
  SixQubit.Orbit36Certified.original_equivalent_canonical,
  SixQubit.Orbit36Certified.table_representative_rigid,
  SixQubit.Orbit36Certified.table_representative_attained,
  SixQubit.Orbit8RaisingGram.raisingGram_eq_normalMatrix,
  SixQubit.Orbit8RaisingGram.fully_certified,
  SixQubit.Orbit9Universal.original_magnitude_pattern,
  SixQubit.Orbit9Universal.eleven_coefficient_pattern,
  SixQubit.Orbit9Universal.magnitudes_fully_certified,
  SixQubit.Orbit31.vectorMomentSystem_iff_normalForm,
  SixQubit.Orbit31.momentMatrix_rank,
  SixQubit.Orbit31.momentPolytope_iff_normalForm,
  SixQubit.Orbit31.momentPolytope_affine_dimension,
  SixQubit.innerC_eq_diagMatElt,
  SixQubit.innerC_flip_eq_offdiagMatElt,
  SixQubit.diagMatElt_eq_zero_of_innerC,
  SixQubit.offdiagMatElt_eq_zero_of_innerC,
  SixQubit.Orbit7Universal.weight_flip_ne,
  SixQubit.Orbit7Universal.offdiag_zero,
  SixQubit.Orbit7Universal.active_marginal_maximally_mixed,
  SixQubit.Orbit8Universal.Qact_smul,
  SixQubit.Orbit8Universal.Qact_add,
  SixQubit.Orbit8Universal.QP_eq,
  SixQubit.Generated.Orbit2Gram.all_blocks_posDef,
  SixQubit.Generated.Orbit3SexticIdentity.coefficients,
  SixQubit.Generated.Orbit3SexticIdentity.identity_on_moments,
  SixQubit.Generated.Orbit3SexticIdentity.target_zero_of_constraints,
  SixQubit.Generated.Orbit3Scalar.lower_bounds,
  SixQubit.Generated.Orbit3Scalar.zero_categories,
  SixQubit.Generated.Orbit3Scalar.low_mass_bound,
  SixQubit.ParityPauliScalars.odd_trace_zero,
  SixQubit.ParityPauliScalars.diagonal_relation,
  SixQubit.ParityPauliScalars.shadow_zero,
  SixQubit.Generated.Orbit3PositiveSquare.square_quadratic_form,
  SixQubit.Generated.Orbit3PositiveSquare.target_zero_of_psd
]
