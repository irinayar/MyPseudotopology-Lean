import LeanCheck.AppendixB
import LeanCheck.ChainLemmas
import LeanCheck.ChainDigits
import LeanCheck.ChainDichotomy
import LeanCheck.ChainCRT
import LeanCheck.ChainG
import LeanCheck.ChainJoin
import LeanCheck.ChainNonInt
import LeanCheck.ChainCapstone
import LeanCheck.ChainTop
import LeanCheck.ChainTopZeta
import LeanCheck.ChainTopDict
import LeanCheck.ChainTopMain
import LeanCheck.ChainHom
import LeanCheck.ChainLift
import LeanCheck.ChainTransfer
import LeanCheck.ChainTransferDual
import LeanCheck.ChainLQC
import LeanCheck.ChainTransferOpen
import LeanCheck.ChainTransferQ
import LeanCheck.ChainSaturation
import LeanCheck.ChainHamel
import LeanCheck.ChainHamelDual
import LeanCheck.ChainHamelStrict
import LeanCheck.ChainHamelTau
import LeanCheck.ChainHamelScalar
import LeanCheck.ChainHamelFinal
import LeanCheck.ChainPrecompact
import LeanCheck.ChainDualityCore
import LeanCheck.ChainDuality
import LeanCheck.ChainPell
import LeanCheck.ChainUniversal
import LeanCheck.ChainUniversal2
import LeanCheck.ChainIso1
import LeanCheck.ChainIso2
import LeanCheck.ChainIso3
import LeanCheck.ChainIso4
import LeanCheck.ChainIso5
import LeanCheck.ChainIso6
import LeanCheck.ChainIso7
import LeanCheck.ChainKronecker
import LeanCheck.ChainComp1
import LeanCheck.ChainComp2
import LeanCheck.ChainComp3
import LeanCheck.ChainComp4
import LeanCheck.ChainComp5
import LeanCheck.ChainComp6
import LeanCheck.ChainComp7
import LeanCheck.ChainArtinSchreier
import LeanCheck.ChainFieldUniversal
import LeanCheck.ChainPW1
import LeanCheck.ChainPW2
import LeanCheck.ChainPW3
import LeanCheck.ChainPW4
import LeanCheck.ChainPW5
import LeanCheck.ChainPW6
import LeanCheck.ChainPW7
import LeanCheck.ChainPW8
import LeanCheck.ChainBaire
import LeanCheck.ChainNecessaryMackey
import LeanCheck.ChainX1
import LeanCheck.ChainX2
import LeanCheck.ChainX3
import LeanCheck.ChainX4
import LeanCheck.ChainT1
import LeanCheck.ChainT2
import LeanCheck.ChainT3
import LeanCheck.ChainT4
import LeanCheck.ChainT5
import LeanCheck.ChainY1
import LeanCheck.ChainY2
import LeanCheck.ChainY3
import LeanCheck.ChainY4
import LeanCheck.ChainY5
import LeanCheck.ChainY6
import LeanCheck.ChainY7
import LeanCheck.ChainZ1
import LeanCheck.ChainZ2
import LeanCheck.ChainZ3
import LeanCheck.ChainZ4
import LeanCheck.ChainZ5
import LeanCheck.ChainW1
import LeanCheck.ChainW2
import LeanCheck.ChainV1
import LeanCheck.ChainV2
import LeanCheck.ChainV3
import LeanCheck.ChainV4
import LeanCheck.ChainU1
import LeanCheck.ChainU2
import LeanCheck.ChainU3
import LeanCheck.ChainD1
import LeanCheck.ChainD2
import LeanCheck.ChainD3
import LeanCheck.ChainD4
import LeanCheck.ChainD5
import LeanCheck.ChainD6
import LeanCheck.ChainD7
import LeanCheck.ChainE1
import LeanCheck.ChainE2
import LeanCheck.ChainE3
import LeanCheck.ChainE4
import LeanCheck.ChainE5
import LeanCheck.ChainE6
import LeanCheck.ChainE7
import LeanCheck.ChainF3
import LeanCheck.ChainG3
import LeanCheck.ChainH1
import LeanCheck.ChainK2
import LeanCheck.ChainM1
import LeanCheck.ChainN2
import LeanCheck.ChainN1
import LeanCheck.ChainL1
import LeanCheck.ChainK1
import LeanCheck.ChainG2
import LeanCheck.ChainG1
import LeanCheck.ChainF2
import LeanCheck.ChainF1
#print axioms LeanCheck.lemmaB1
#print axioms LeanCheck.propB2
#print axioms LeanCheck.propB3
#print axioms LeanCheck.odd_half_not_hausdorff
#print axioms LeanCheck.contraction_step
#print axioms LeanCheck.run_contraction
#print axioms LeanCheck.run_bottom_small
#print axioms LeanCheck.near_of_all_multiples
#print axioms LeanCheck.crossing
#print axioms LeanCheck.geom_tail
#print axioms LeanCheck.digit_int
#print axioms LeanCheck.digit_rec
#print axioms LeanCheck.digit_zeta
#print axioms LeanCheck.single_digit_small
#print axioms LeanCheck.single_digit_int
#print axioms LeanCheck.digit_bound
#print axioms LeanCheck.step1
#print axioms LeanCheck.theta_rel
#print axioms LeanCheck.caseI
#print axioms LeanCheck.caseII_false
#print axioms LeanCheck.case_dichotomy
#print axioms LeanCheck.crt_solvable
#print axioms LeanCheck.gcd_lcm_dvd
#print axioms LeanCheck.crt_step
#print axioms LeanCheck.two_chains_exists
#print axioms LeanCheck.gG_runs
#print axioms LeanCheck.factorial_dvd_gG
#print axioms LeanCheck.gG_null
#print axioms LeanCheck.WG_dvd
#print axioms LeanCheck.WG_null
#print axioms LeanCheck.theoremH_data
#print axioms LeanCheck.run_near
#print axioms LeanCheck.join_cont
#print axioms LeanCheck.counterexample_core
#print axioms LeanCheck.gG_mono
#print axioms LeanCheck.q_double
#print axioms LeanCheck.q_ge
#print axioms LeanCheck.Psum_le
#print axioms LeanCheck.tail_dvd
#print axioms LeanCheck.zetaG_not_integer
#print axioms LeanCheck.zetaG_residues_exist
#print axioms LeanCheck.zetaG_not_M_integer
#print axioms LeanCheck.Mseq_of_chain
#print axioms LeanCheck.capstone
#print axioms LeanCheck.basisOf
#print axioms LeanCheck.quarter_of_continuous
#print axioms LeanCheck.continuous_of_quarter
#print axioms LeanCheck.continuous_of_quarter_join
#print axioms LeanCheck.zetaHom
#print axioms LeanCheck.zetaHom_apply
#print axioms LeanCheck.chi_eq
#print axioms LeanCheck.xe_obs
#print axioms LeanCheck.cont_of_continuous
#print axioms LeanCheck.zeta_not_continuous
#print axioms LeanCheck.zeta_eq_Psum
#print axioms LeanCheck.topological_capstone
#print axioms LeanCheck.zeta_join_continuous
#print axioms LeanCheck.zeta_not_int
#print axioms LeanCheck.torsion_form
#print axioms LeanCheck.hom_is_zeta
#print axioms LeanCheck.intHom_continuous
#print axioms LeanCheck.dual_exact
#print axioms LeanCheck.t2_basisOf
#print axioms LeanCheck.final_capstone
#print axioms LeanCheck.gam_group
#print axioms LeanCheck.gam_scalar
#print axioms LeanCheck.dual_gam_mp
#print axioms LeanCheck.dual_gam_mpr
#print axioms LeanCheck.dual_gam
#print axioms LeanCheck.lift_incompatible
#print axioms LeanCheck.gam_t2
#print axioms LeanCheck.lift_capstone
#print axioms LeanCheck.f_ratmul
#print axioms LeanCheck.Tf_group
#print axioms LeanCheck.Tf_dilation
#print axioms LeanCheck.Tf_inf
#print axioms LeanCheck.Tf_t2
#print axioms LeanCheck.chiH_continuous
#print axioms LeanCheck.ker_uncountable
#print axioms LeanCheck.transfer_obstruction
#print axioms LeanCheck.transfer_capstone
#print axioms LeanCheck.linearize
#print axioms LeanCheck.Hker_dense
#print axioms LeanCheck.indep_reduction
#print axioms LeanCheck.Hmap_surj
#print axioms LeanCheck.pi_box
#print axioms LeanCheck.packaged
#print axioms LeanCheck.dual_Tf_mp
#print axioms LeanCheck.dual_Tf
#print axioms LeanCheck.lift_capstone_scalar
#print axioms LeanCheck.transfer_capstone_exact
#print axioms LeanCheck.exists_coefficient
#print axioms LeanCheck.QuasiConvex
#print axioms LeanCheck.LocQC
#print axioms LeanCheck.qc_preimage
#print axioms LeanCheck.lqc_induced
#print axioms LeanCheck.lqc_inf
#print axioms LeanCheck.lqc_iInf
#print axioms LeanCheck.lqc_uR
#print axioms LeanCheck.lqc_basisOf
#print axioms LeanCheck.lqc_gam
#print axioms LeanCheck.lqc_Tf
#print axioms LeanCheck.final_capstone_lqc
#print axioms LeanCheck.lift_capstone_lqc
#print axioms LeanCheck.transfer_capstone_Cf
#print axioms LeanCheck.tf_nhds_sub
#print axioms LeanCheck.Tf_image_nhds
#print axioms LeanCheck.Tf_isOpenMap
#print axioms LeanCheck.f_surjective
#print axioms LeanCheck.Tf_coinduced
#print axioms LeanCheck.Tf_le_iff
#print axioms LeanCheck.Tf_injective
#print axioms LeanCheck.transfer_join_quotient
#print axioms LeanCheck.Tq_group
#print axioms LeanCheck.Tq_t2
#print axioms LeanCheck.Tq_rat_dilation
#print axioms LeanCheck.Tq_inf
#print axioms LeanCheck.lqc_Tq
#print axioms LeanCheck.Tq_image_nhds
#print axioms LeanCheck.isOpenMap_of_image_nhds
#print axioms LeanCheck.Tq_isOpenMap
#print axioms LeanCheck.Tq_coinduced
#print axioms LeanCheck.Tq_le_iff
#print axioms LeanCheck.dual_Tq_mp
#print axioms LeanCheck.dual_Tq
#print axioms LeanCheck.transferQ_obstruction
#print axioms LeanCheck.Tq_gamma0
#print axioms LeanCheck.Tq_join_compat
#print axioms LeanCheck.transfer_capstone_Q
#print axioms LeanCheck.satn_succ_le
#print axioms LeanCheck.sat_group
#print axioms LeanCheck.sat_t2
#print axioms LeanCheck.sat_lqc
#print axioms LeanCheck.sat_rat_cont
#print axioms LeanCheck.sat_least
#print axioms LeanCheck.satn_dual
#print axioms LeanCheck.sat_dual
#print axioms LeanCheck.saturation
#print axioms LeanCheck.mackey_equivalence
#print axioms LeanCheck.Hq_ratInv
#print axioms LeanCheck.no_greatest_compatible_Q
#print axioms LeanCheck.gamma0_eq_gam
#print axioms LeanCheck.sigmaT_eq
#print axioms LeanCheck.tauT_le_sigmaT
#print axioms LeanCheck.sigmaT_le_betaT
#print axioms LeanCheck.betaT_group
#print axioms LeanCheck.betaT_t2
#print axioms LeanCheck.TfS_group
#print axioms LeanCheck.TfS_t2
#print axioms LeanCheck.TfS_dilation
#print axioms LeanCheck.circ_dual
#print axioms LeanCheck.gamma0_dual
#print axioms LeanCheck.dual_TfS_mp
#print axioms LeanCheck.mixed_zero
#print axioms LeanCheck.chiH_unique
#print axioms LeanCheck.dual_sigma
#print axioms LeanCheck.dual_beta
#print axioms LeanCheck.usual_char
#print axioms LeanCheck.pfHom_not_usual
#print axioms LeanCheck.sigmaT_lt_usual
#print axioms LeanCheck.HkerG_dense
#print axioms LeanCheck.sigma_nhds_sub
#print axioms LeanCheck.sigma_unbounded
#print axioms LeanCheck.not_cont_sigma_rat
#print axioms LeanCheck.faR_cont_tau
#print axioms LeanCheck.tauT_lt_sigmaT
#print axioms LeanCheck.no_rat_dual_beta
#print axioms LeanCheck.dual_tau_real
#print axioms LeanCheck.mem_of_tau_cont
#print axioms LeanCheck.mem_of_pf_cont_beta
#print axioms LeanCheck.mem_of_pf_cont_sigma
#print axioms LeanCheck.betaT_dilation
#print axioms LeanCheck.scalar_tau
#print axioms LeanCheck.scalar_sigma
#print axioms LeanCheck.scalar_beta
#print axioms LeanCheck.order_beta
#print axioms LeanCheck.order_sigma
#print axioms LeanCheck.order_tau
#print axioms LeanCheck.betaT_injective
#print axioms LeanCheck.sigmaT_injective
#print axioms LeanCheck.tauT_injective
#print axioms LeanCheck.dual_sigma_real
#print axioms LeanCheck.TfS_not_isolated
#print axioms LeanCheck.betaT_not_isolated
#print axioms LeanCheck.beta_nhds_sub
#print axioms LeanCheck.beta_unbounded
#print axioms LeanCheck.beta_not_le_usual
#print axioms LeanCheck.usual_not_le_beta
#print axioms LeanCheck.dual_beta_real
#print axioms LeanCheck.scalarRing_algebra
#print axioms LeanCheck.hamel_prop_basic
#print axioms LeanCheck.theta_group
#print axioms LeanCheck.theta_t2
#print axioms LeanCheck.sep_of_theta_t2
#print axioms LeanCheck.theta_precompact
#print axioms LeanCheck.precompact_of_le
#print axioms LeanCheck.theta_ratdil
#print axioms LeanCheck.theta_ptvgq
#print axioms LeanCheck.dualGroup_ratInv
#print axioms LeanCheck.theta_injective
#print axioms LeanCheck.theta_le_iff
#print axioms LeanCheck.dualGroup_theta
#print axioms LeanCheck.classification
#print axioms LeanCheck.classificationEquiv
#print axioms LeanCheck.theta_scalar
#print axioms LeanCheck.pc_zero
#print axioms LeanCheck.HQ_separates
#print axioms LeanCheck.HQ_ratInv
#print axioms LeanCheck.thetaQ_ptvgq
#print axioms LeanCheck.thetaQ_eq
#print axioms LeanCheck.thetaQ_metrizable
#print axioms LeanCheck.thetaQ_scalar
#print axioms LeanCheck.thetaQ_minimal
#print axioms LeanCheck.thetaQ_lt_bohr
#print axioms LeanCheck.betaT_eq_theta
#print axioms LeanCheck.dual_theta_Hset
#print axioms LeanCheck.integral_char_eq_zero
#print axioms LeanCheck.char_in_span
#print axioms LeanCheck.fourier_reduction
#print axioms LeanCheck.dual_theta_iff
#print axioms LeanCheck.dualThetaFact
#print axioms LeanCheck.theta_injective_unc
#print axioms LeanCheck.theta_le_iff_unc
#print axioms LeanCheck.theta_scalar_unc
#print axioms LeanCheck.thetaQ_scalar_unc
#print axioms LeanCheck.thetaQ_lt_bohr_unc
#print axioms LeanCheck.theta_realdil
#print axioms LeanCheck.theta_ptvg
#print axioms LeanCheck.dualGroup_realInv
#print axioms LeanCheck.classification_TVG
#print axioms LeanCheck.no_greatest_compatible_TVG
#print axioms LeanCheck.classification
#print axioms LeanCheck.thetaQ_minimal
#print axioms LeanCheck.pq_plus
#print axioms LeanCheck.pq_minus
#print axioms LeanCheck.pz_tendsto_zero
#print axioms LeanCheck.qn_tendsto
#print axioms LeanCheck.tendsto_TfS_iff
#print axioms LeanCheck.tendsto_sigma_iff
#print axioms LeanCheck.tendsto_tau_iff
#print axioms LeanCheck.g_pz
#print axioms LeanCheck.g_pz_real
#print axioms LeanCheck.g_pz_int
#print axioms LeanCheck.abs_g_pz_tendsto
#print axioms LeanCheck.modular_conv
#print axioms LeanCheck.modular_conv_beta
#print axioms LeanCheck.pell_criterion
#print axioms LeanCheck.pell_separates_iff
#print axioms LeanCheck.not_compact_of_cluster
#print axioms LeanCheck.pell_scaled
#print axioms LeanCheck.no_universal
#print axioms LeanCheck.no_universal_sequence
#print axioms LeanCheck.no_universal_separating
#print axioms LeanCheck.exists_indep_subseq
#print axioms LeanCheck.finite_universal
#print axioms LeanCheck.universal_necessary
#print axioms LeanCheck.exists_eps
#print axioms LeanCheck.approx_irr
#print axioms LeanCheck.obs_real
#print axioms LeanCheck.obs_int
#print axioms LeanCheck.abs_obs_tendsto
#print axioms LeanCheck.cover_nonzero
#print axioms LeanCheck.universal_sufficient
#print axioms LeanCheck.reduce_irrational
#print axioms LeanCheck.universal_complete
#print axioms LeanCheck.universal_complete_beta
#print axioms LeanCheck.finite_codim_universal
#print axioms LeanCheck.rigidity_beta
#print axioms LeanCheck.rigidity_sigma
#print axioms LeanCheck.scale_cont_beta_iff
#print axioms LeanCheck.scale_cont_sigma_iff
#print axioms LeanCheck.iso_iff_beta
#print axioms LeanCheck.iso_iff_sigma
#print axioms LeanCheck.scalarCont_eq_of_iso_beta
#print axioms LeanCheck.scalarCont_eq_of_iso_sigma
#print axioms LeanCheck.iso_algebra_beta
#print axioms LeanCheck.iso_algebra_sigma
#print axioms LeanCheck.iso_fixed_beta
#print axioms LeanCheck.iso_fixed_sigma
#print axioms LeanCheck.iso_Q_beta
#print axioms LeanCheck.iso_Q_sigma
#print axioms LeanCheck.not_iso_beta_sigma
#print axioms LeanCheck.not_iso_sigma_beta
#print axioms LeanCheck.rat_dual_tau
#print axioms LeanCheck.tau_real_iff
#print axioms LeanCheck.tau_rat_iff
#print axioms LeanCheck.tau_hom_necessary
#print axioms LeanCheck.tau_hom_sufficient
#print axioms LeanCheck.tau_hom_iff
#print axioms LeanCheck.tau_iso_inverse
#print axioms LeanCheck.tau_iso_criterion
#print axioms LeanCheck.tau_iso_rep
#print axioms LeanCheck.tau_iso_iff
#print axioms LeanCheck.scalarCont_eq_of_iso_tau
#print axioms LeanCheck.iso_algebra_tau
#print axioms LeanCheck.iso_fixed_tau
#print axioms LeanCheck.iso_Q_tau
#print axioms LeanCheck.Lcs_comp
#print axioms LeanCheck.Lcs_Linv
#print axioms LeanCheck.Linv_Lcs
#print axioms LeanCheck.ainv_unit_iff
#print axioms LeanCheck.tau_auto_iff
#print axioms LeanCheck.Mshear_comp
#print axioms LeanCheck.shear_hom
#print axioms LeanCheck.shear_section
#print axioms LeanCheck.shear_section_mul
#print axioms LeanCheck.shear_kernel
#print axioms LeanCheck.shear_comm_left
#print axioms LeanCheck.shear_comm_right
#print axioms LeanCheck.shear_nonabelian
#print axioms LeanCheck.shear_auto
#print axioms LeanCheck.count_types
#print axioms LeanCheck.card_addHom
#print axioms LeanCheck.card_nonzero_addHom
#print axioms LeanCheck.class_le
#print axioms LeanCheck.count_beta_types
#print axioms LeanCheck.count_sigma_types
#print axioms LeanCheck.count_tau_types
#print axioms LeanCheck.trig_dense
#print axioms LeanCheck.kronecker_mem
#print axioms LeanCheck.kronecker_range
#print axioms LeanCheck.pd_isClosedEmbedding
#print axioms LeanCheck.PD.compact
#print axioms LeanCheck.PD.complete
#print axioms LeanCheck.PD.isUniformAddGroup
#print axioms LeanCheck.ISigma_inducing
#print axioms LeanCheck.JBeta_inducing
#print axioms LeanCheck.pd_basic_open
#print axioms LeanCheck.approx_chars
#print axioms LeanCheck.ISigma_denseRange
#print axioms LeanCheck.JBeta_denseRange
#print axioms LeanCheck.completion_sigma
#print axioms LeanCheck.completion_beta
#print axioms LeanCheck.Fa_indep
#print axioms LeanCheck.faR_cont_span
#print axioms LeanCheck.GTau_inducing
#print axioms LeanCheck.GTau_denseRange
#print axioms LeanCheck.completion_tau
#print axioms LeanCheck.countable_span_int
#print axioms LeanCheck.beta_not_firstCountable
#print axioms LeanCheck.beta_not_metrizable
#print axioms LeanCheck.sigma_metrizable_Q
#print axioms LeanCheck.tau_metrizable_Q
#print axioms LeanCheck.completion_rational
#print axioms LeanCheck.circ_char_zero
#print axioms LeanCheck.eS_inducing
#print axioms LeanCheck.eS_denseRange
#print axioms LeanCheck.completion_thetaS
#print axioms LeanCheck.thetaQ_eq_thetaS
#print axioms LeanCheck.completion_thetaQ
#print axioms LeanCheck.completion_unique
#print axioms LeanCheck.completion_iso_completion
#print axioms LeanCheck.exists_basis_of_submodule
#print axioms LeanCheck.completion_literal_sigma
#print axioms LeanCheck.completion_literal_beta
#print axioms LeanCheck.completion_literal_tau
#print axioms LeanCheck.completion_literal_thetaS
#print axioms LeanCheck.no_prime_index_odd
#print axioms LeanCheck.no_prime_index_two
#print axioms LeanCheck.finrank_eq_one_of_I_mem
#print axioms LeanCheck.finite_index_subfield_real
#print axioms LeanCheck.field_cover_iff
#print axioms LeanCheck.field_universal
#print axioms LeanCheck.PW.Tk_compact
#print axioms LeanCheck.PW.exists_common_eigenvector
#print axioms LeanCheck.PW.Tconv_comm
#print axioms LeanCheck.PW.Dop_ne_zero
#print axioms LeanCheck.PW.exists_char_ne
#print axioms LeanCheck.exists_circ_char
#print axioms LeanCheck.finite_chars_in_nhds
#print axioms LeanCheck.completion_compactSpace
#print axioms LeanCheck.generatedFact
#print axioms LeanCheck.precompactDuality
#print axioms LeanCheck.classification_unc
#print axioms LeanCheck.classificationEquiv_unc
#print axioms LeanCheck.thetaQ_minimal_unc
#print axioms LeanCheck.classification_TVG_unc
#print axioms LeanCheck.QCompat.of_Lcls
#print axioms LeanCheck.half_ne_zero_circ
#print axioms LeanCheck.ker_closed
#print axioms LeanCheck.fQ_surjective
#print axioms LeanCheck.fQ_isOpenMap
#print axioms LeanCheck.QuotQ_isTopologicalAddGroup
#print axioms LeanCheck.QuotQ_t2
#print axioms LeanCheck.QuotQ_dual
#print axioms LeanCheck.QuotQ_not_discrete
#print axioms LeanCheck.quotient_lemma
#print axioms LeanCheck.not_baire
#print axioms LeanCheck.not_baire_Ccls
#print axioms LeanCheck.not_locallyCompact
#print axioms LeanCheck.not_completelyMetrizable
#print axioms LeanCheck.Gam_ratInv
#print axioms LeanCheck.lamTop_dual
#print axioms LeanCheck.Tq_mem_Ccls
#print axioms LeanCheck.lam_le
#print axioms LeanCheck.necessary_mackey_rational
#print axioms LeanCheck.no_mackey_rational
#print axioms LeanCheck.no_greatest_via_quotient
#print axioms LeanCheck.tvgq_division_equiv
#print axioms LeanCheck.scalarCont_subring
#print axioms LeanCheck.isHomeomorph_mul_iff
#print axioms LeanCheck.scalarRing_inv_iff
#print axioms LeanCheck.homeo_iff_scalar_beta
#print axioms LeanCheck.homeo_iff_scalar_sigma
#print axioms LeanCheck.homeo_iff_scalar_tau
#print axioms LeanCheck.transcendental_example
#print axioms LeanCheck.directed_join_Lcls
#print axioms LeanCheck.directed_join_Ccls
#print axioms LeanCheck.exists_maximal_ext
#print axioms LeanCheck.greatest_criterion
#print axioms LeanCheck.compatible_scalars
#print axioms LeanCheck.strict_compatible_refinement
#print axioms LeanCheck.delta2_not_precompact
#print axioms LeanCheck.greatest_restrictions
#print axioms LeanCheck.rational_not_baire
#print axioms LeanCheck.greatest_rational_restrictions
#print axioms LeanCheck.scalar_field_of_locallyCompact
#print axioms LeanCheck.scalarCont_subfield
#print axioms LeanCheck.scalarCont_subfield_compact
#print axioms LeanCheck.joint_continuity_of_orbit
#print axioms LeanCheck.lift_unique
#print axioms LeanCheck.tvg_totally_disconnected
#print axioms LeanCheck.lift_pf
#print axioms LeanCheck.lift_chi
#print axioms LeanCheck.modular_comparison
#print axioms LeanCheck.modular_incomparable
#print axioms LeanCheck.modular_count
#print axioms LeanCheck.tvg_rigidity
#print axioms LeanCheck.tvg_isomorphism_classification
#print axioms LeanCheck.tvg_endomorphisms
#print axioms LeanCheck.tvg_isomorphism_count
#print axioms LeanCheck.tvg_maps_between_families
#print axioms LeanCheck.sigmaI_unbounded
#print axioms LeanCheck.sigmaI_dual_rat
#print axioms LeanCheck.family_properties
#print axioms LeanCheck.vanishing_family
#print axioms LeanCheck.family_joins
#print axioms LeanCheck.representation_failure
#print axioms LeanCheck.bohr_lt_beta
#print axioms LeanCheck.tvg_coarser_iff
#print axioms LeanCheck.tvg_finer_iff
#print axioms LeanCheck.tvg_weaker_consequences
#print axioms LeanCheck.char_Q_real
#print axioms LeanCheck.xi_neg
#print axioms LeanCheck.irrational_series
#print axioms LeanCheck.key_prop
#print axioms LeanCheck.xi_dual_of_finite
#print axioms LeanCheck.xi_dual_seq
#print axioms LeanCheck.chains_F_seq
#print axioms LeanCheck.tors_neg
#print axioms LeanCheck.tors_pos
#print axioms LeanCheck.chains_G_seq
#print axioms LeanCheck.tors_dual_finite
#print axioms LeanCheck.HSet_union
#print axioms LeanCheck.HSet_finite
#print axioms LeanCheck.HSeq_iff_HSet
#print axioms LeanCheck.chains_F_set
#print axioms LeanCheck.compat_iff_HSet
#print axioms LeanCheck.xi_inf_union
#print axioms LeanCheck.lam_inf_union
#print axioms LeanCheck.Fjoin
#print axioms LeanCheck.Gjoin
#print axioms LeanCheck.psiR_not_mem
#print axioms LeanCheck.scalar_ring_rat
#print axioms LeanCheck.irrational_witness
#print axioms LeanCheck.irrational_probe_sequences
#print axioms LeanCheck.irrational_join_test
#print axioms LeanCheck.HSet_fac
#print axioms LeanCheck.fac_full_dual
#print axioms LeanCheck.usual_le_xi
#print axioms LeanCheck.qfac_null
#print axioms LeanCheck.qfac_not_null_usual
#print axioms LeanCheck.fac_fac_not_null
#print axioms LeanCheck.xi_fac_strict
#print axioms LeanCheck.dyadic_bounded_gaps
#print axioms LeanCheck.dyadic_long_blocks
#print axioms LeanCheck.dyadic_partition
#print axioms LeanCheck.alternating_blocks
#print axioms LeanCheck.odd_segments_not_T2
#print axioms LeanCheck.odd_segments_character_discontinuous
#print axioms LeanCheck.bohr_to_usual
#print axioms LeanCheck.beta_null_iff_sigma_null
#print axioms LeanCheck.conv_beta_iff
#print axioms LeanCheck.conv_sigma_iff
#print axioms LeanCheck.conv_tau_iff
#print axioms LeanCheck.beta_sigma_same_sequences
#print axioms LeanCheck.pell_unscaled_top
#print axioms LeanCheck.finite_span_onto
#print axioms LeanCheck.finite_span_tau
#print axioms LeanCheck.finite_span_sigma
#print axioms LeanCheck.finite_span_beta
#print axioms LeanCheck.one_dim_no_separation
#print axioms LeanCheck.two_dim_separation
#print axioms LeanCheck.compact_sigma_iff
#print axioms LeanCheck.compact_tau_iff
#print axioms LeanCheck.compact_beta_of
#print axioms LeanCheck.directed_join_mem
#print axioms LeanCheck.exists_minimal_ext
#print axioms LeanCheck.greatest_iff_binary
#print axioms LeanCheck.binary_join_mem_iff
#print axioms LeanCheck.Hf_dilInv
#print axioms LeanCheck.rho_mem
#print axioms LeanCheck.automatic_tvg
#print axioms LeanCheck.aut_converse
#print axioms LeanCheck.rho_le_iff
#print axioms LeanCheck.rho_directed_iff
#print axioms LeanCheck.real_saturation
#print axioms LeanCheck.mackey_implies_conjecture
#print axioms LeanCheck.QuotQ_dualF
#print axioms LeanCheck.quotient_lemma_F
#print axioms LeanCheck.lamTop_dualF
#print axioms LeanCheck.Tf_mem_Kcls
#print axioms LeanCheck.lam_le_F
#print axioms LeanCheck.necessary_mackey_F
#print axioms LeanCheck.sandwich
#print axioms LeanCheck.xi_t2
#print axioms LeanCheck.xi_scalar
#print axioms LeanCheck.xi_lqc
#print axioms LeanCheck.xi_mem_Ccls
#print axioms LeanCheck.HSet_sq
#print axioms LeanCheck.gamma_p_dual
#print axioms LeanCheck.gamma_p_mem
#print axioms LeanCheck.prime_not_finer
#print axioms LeanCheck.gamma2_gamma3_incomparable
#print axioms LeanCheck.conditional_witness
#print axioms LeanCheck.ultralimit_test
#print axioms LeanCheck.ultralimit_incompatible
#print axioms LeanCheck.ulimChar_of_tendsto
#print axioms LeanCheck.ultrafilter_criterion
#print axioms LeanCheck.countable_of_separated
#print axioms LeanCheck.discrete_of_countable_nhd
#print axioms LeanCheck.join_usual_nondiscrete
#print axioms LeanCheck.join_precompact_nondiscrete
#print axioms LeanCheck.exists_minimal_nd
#print axioms LeanCheck.exists_maximal_nondiscrete
#print axioms LeanCheck.torsionfree_Q
#print axioms LeanCheck.torsionfree_Hf
#print axioms LeanCheck.lqc_circ
#print axioms LeanCheck.lqc_betaT
#print axioms LeanCheck.lqc_sigmaT
#print axioms LeanCheck.sigma_mem_Kcls
#print axioms LeanCheck.beta_least
#print axioms LeanCheck.sigma_least
#print axioms LeanCheck.additive_dual
#print axioms LeanCheck.necessary_condition
#print axioms LeanCheck.rational_target_lemma
#print axioms LeanCheck.sigmaT_top_eq_Tf
#print axioms LeanCheck.sqrt2_f_not_mem
#print axioms LeanCheck.strictly_finer_compatible
#print axioms LeanCheck.minimal_iff_line
#print axioms LeanCheck.no_least_TVG
#print axioms LeanCheck.sigma_not_firstCountable
#print axioms LeanCheck.sigma_not_metrizable
#print axioms LeanCheck.sigma_not_complete
#print axioms LeanCheck.beta_not_complete
#print axioms LeanCheck.sigma_not_locallyCompact
#print axioms LeanCheck.beta_not_locallyCompact
#print axioms LeanCheck.sigma_completion_not_firstCountable
#print axioms LeanCheck.beta_completion_not_firstCountable
#print axioms LeanCheck.integer_polar_reduction
#print axioms LeanCheck.lamTop_rational_scalar
#print axioms LeanCheck.card_Chars
#print axioms LeanCheck.card_chooseBasisIndex
#print axioms LeanCheck.card_precompact_TVG
#print axioms LeanCheck.card_minimal_TVG
#print axioms LeanCheck.precompact_count
#print axioms LeanCheck.dirichlet_multi
#print axioms LeanCheck.exists_large_in_joint
#print axioms LeanCheck.join_contains_large_integers
#print axioms LeanCheck.join_weaker_than_usual
#print axioms LeanCheck.tendsto_profT_zero
#print axioms LeanCheck.isCompact_of_null
#print axioms LeanCheck.twochains_complete
#print axioms LeanCheck.twochains_compact_union
#print axioms LeanCheck.seq_universal_tau
#print axioms LeanCheck.seq_universal_sigma
#print axioms LeanCheck.seq_universal_beta
#print axioms LeanCheck.exists_decay_functional
#print axioms LeanCheck.seq_dependence
#print axioms LeanCheck.aSeq_weak_null
#print axioms LeanCheck.aSeq_not_gamma
#print axioms LeanCheck.HM_surj
#print axioms LeanCheck.HM_ker_dense
#print axioms LeanCheck.HM_openSurj
#print axioms LeanCheck.HM_openSurj_gamma0
#print axioms LeanCheck.nu_dual_mp
#print axioms LeanCheck.exists_patterns
#print axioms LeanCheck.no_greatest_nondiscrete
#print axioms LeanCheck.nonunique_maximal
#print axioms LeanCheck.metrizable_rat
#print axioms LeanCheck.gamma_p_metrizable
#print axioms LeanCheck.gamma_p_not_precompact
#print axioms LeanCheck.exists_metrizable_between
#print axioms LeanCheck.reduction_to_metrizable
#print axioms LeanCheck.sum_cos_grid
#print axioms LeanCheck.sum_Qf_grid
#print axioms LeanCheck.exists_large_Pl_set
#print axioms LeanCheck.cover_Kset
#print axioms LeanCheck.covering_exp_bound
#print axioms LeanCheck.Kset_dimH
#print axioms LeanCheck.mixed_dual_dimH_zero
#print axioms LeanCheck.Hint_Z16
#print axioms LeanCheck.mixed_dual_null
