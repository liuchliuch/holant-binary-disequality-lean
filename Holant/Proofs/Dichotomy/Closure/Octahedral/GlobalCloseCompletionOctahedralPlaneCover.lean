import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralMaskChecks0
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralMaskChecks1
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralMaskChecks2
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralMaskChecks3
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralCoverChecks0
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralCoverChecks1
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralCoverChecks2
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralCoverChecks3
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralCoverChecks4
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralCoverChecks5
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralCoverChecks6
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralCoverChecks7
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralPairChecks
set_option maxRecDepth 100000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankThree
open Holant.Certificates.OctahedralSeparator
theorem plane_mask_bound (p : Fin 120) : (planeMask p).card≤9 := by
  fin_cases p
  · exact plane_mask_bound_0
  · exact plane_mask_bound_1
  · exact plane_mask_bound_2
  · exact plane_mask_bound_3
  · exact plane_mask_bound_4
  · exact plane_mask_bound_5
  · exact plane_mask_bound_6
  · exact plane_mask_bound_7
  · exact plane_mask_bound_8
  · exact plane_mask_bound_9
  · exact plane_mask_bound_10
  · exact plane_mask_bound_11
  · exact plane_mask_bound_12
  · exact plane_mask_bound_13
  · exact plane_mask_bound_14
  · exact plane_mask_bound_15
  · exact plane_mask_bound_16
  · exact plane_mask_bound_17
  · exact plane_mask_bound_18
  · exact plane_mask_bound_19
  · exact plane_mask_bound_20
  · exact plane_mask_bound_21
  · exact plane_mask_bound_22
  · exact plane_mask_bound_23
  · exact plane_mask_bound_24
  · exact plane_mask_bound_25
  · exact plane_mask_bound_26
  · exact plane_mask_bound_27
  · exact plane_mask_bound_28
  · exact plane_mask_bound_29
  · exact plane_mask_bound_30
  · exact plane_mask_bound_31
  · exact plane_mask_bound_32
  · exact plane_mask_bound_33
  · exact plane_mask_bound_34
  · exact plane_mask_bound_35
  · exact plane_mask_bound_36
  · exact plane_mask_bound_37
  · exact plane_mask_bound_38
  · exact plane_mask_bound_39
  · exact plane_mask_bound_40
  · exact plane_mask_bound_41
  · exact plane_mask_bound_42
  · exact plane_mask_bound_43
  · exact plane_mask_bound_44
  · exact plane_mask_bound_45
  · exact plane_mask_bound_46
  · exact plane_mask_bound_47
  · exact plane_mask_bound_48
  · exact plane_mask_bound_49
  · exact plane_mask_bound_50
  · exact plane_mask_bound_51
  · exact plane_mask_bound_52
  · exact plane_mask_bound_53
  · exact plane_mask_bound_54
  · exact plane_mask_bound_55
  · exact plane_mask_bound_56
  · exact plane_mask_bound_57
  · exact plane_mask_bound_58
  · exact plane_mask_bound_59
  · exact plane_mask_bound_60
  · exact plane_mask_bound_61
  · exact plane_mask_bound_62
  · exact plane_mask_bound_63
  · exact plane_mask_bound_64
  · exact plane_mask_bound_65
  · exact plane_mask_bound_66
  · exact plane_mask_bound_67
  · exact plane_mask_bound_68
  · exact plane_mask_bound_69
  · exact plane_mask_bound_70
  · exact plane_mask_bound_71
  · exact plane_mask_bound_72
  · exact plane_mask_bound_73
  · exact plane_mask_bound_74
  · exact plane_mask_bound_75
  · exact plane_mask_bound_76
  · exact plane_mask_bound_77
  · exact plane_mask_bound_78
  · exact plane_mask_bound_79
  · exact plane_mask_bound_80
  · exact plane_mask_bound_81
  · exact plane_mask_bound_82
  · exact plane_mask_bound_83
  · exact plane_mask_bound_84
  · exact plane_mask_bound_85
  · exact plane_mask_bound_86
  · exact plane_mask_bound_87
  · exact plane_mask_bound_88
  · exact plane_mask_bound_89
  · exact plane_mask_bound_90
  · exact plane_mask_bound_91
  · exact plane_mask_bound_92
  · exact plane_mask_bound_93
  · exact plane_mask_bound_94
  · exact plane_mask_bound_95
  · exact plane_mask_bound_96
  · exact plane_mask_bound_97
  · exact plane_mask_bound_98
  · exact plane_mask_bound_99
  · exact plane_mask_bound_100
  · exact plane_mask_bound_101
  · exact plane_mask_bound_102
  · exact plane_mask_bound_103
  · exact plane_mask_bound_104
  · exact plane_mask_bound_105
  · exact plane_mask_bound_106
  · exact plane_mask_bound_107
  · exact plane_mask_bound_108
  · exact plane_mask_bound_109
  · exact plane_mask_bound_110
  · exact plane_mask_bound_111
  · exact plane_mask_bound_112
  · exact plane_mask_bound_113
  · exact plane_mask_bound_114
  · exact plane_mask_bound_115
  · exact plane_mask_bound_116
  · exact plane_mask_bound_117
  · exact plane_mask_bound_118
  · exact plane_mask_bound_119
theorem plane_triple_mem (p : Fin 120) (i : Fin 3) : planeTriple p i∈planeMask p := by
  fin_cases p
  · exact plane_triple_mem_0 i
  · exact plane_triple_mem_1 i
  · exact plane_triple_mem_2 i
  · exact plane_triple_mem_3 i
  · exact plane_triple_mem_4 i
  · exact plane_triple_mem_5 i
  · exact plane_triple_mem_6 i
  · exact plane_triple_mem_7 i
  · exact plane_triple_mem_8 i
  · exact plane_triple_mem_9 i
  · exact plane_triple_mem_10 i
  · exact plane_triple_mem_11 i
  · exact plane_triple_mem_12 i
  · exact plane_triple_mem_13 i
  · exact plane_triple_mem_14 i
  · exact plane_triple_mem_15 i
  · exact plane_triple_mem_16 i
  · exact plane_triple_mem_17 i
  · exact plane_triple_mem_18 i
  · exact plane_triple_mem_19 i
  · exact plane_triple_mem_20 i
  · exact plane_triple_mem_21 i
  · exact plane_triple_mem_22 i
  · exact plane_triple_mem_23 i
  · exact plane_triple_mem_24 i
  · exact plane_triple_mem_25 i
  · exact plane_triple_mem_26 i
  · exact plane_triple_mem_27 i
  · exact plane_triple_mem_28 i
  · exact plane_triple_mem_29 i
  · exact plane_triple_mem_30 i
  · exact plane_triple_mem_31 i
  · exact plane_triple_mem_32 i
  · exact plane_triple_mem_33 i
  · exact plane_triple_mem_34 i
  · exact plane_triple_mem_35 i
  · exact plane_triple_mem_36 i
  · exact plane_triple_mem_37 i
  · exact plane_triple_mem_38 i
  · exact plane_triple_mem_39 i
  · exact plane_triple_mem_40 i
  · exact plane_triple_mem_41 i
  · exact plane_triple_mem_42 i
  · exact plane_triple_mem_43 i
  · exact plane_triple_mem_44 i
  · exact plane_triple_mem_45 i
  · exact plane_triple_mem_46 i
  · exact plane_triple_mem_47 i
  · exact plane_triple_mem_48 i
  · exact plane_triple_mem_49 i
  · exact plane_triple_mem_50 i
  · exact plane_triple_mem_51 i
  · exact plane_triple_mem_52 i
  · exact plane_triple_mem_53 i
  · exact plane_triple_mem_54 i
  · exact plane_triple_mem_55 i
  · exact plane_triple_mem_56 i
  · exact plane_triple_mem_57 i
  · exact plane_triple_mem_58 i
  · exact plane_triple_mem_59 i
  · exact plane_triple_mem_60 i
  · exact plane_triple_mem_61 i
  · exact plane_triple_mem_62 i
  · exact plane_triple_mem_63 i
  · exact plane_triple_mem_64 i
  · exact plane_triple_mem_65 i
  · exact plane_triple_mem_66 i
  · exact plane_triple_mem_67 i
  · exact plane_triple_mem_68 i
  · exact plane_triple_mem_69 i
  · exact plane_triple_mem_70 i
  · exact plane_triple_mem_71 i
  · exact plane_triple_mem_72 i
  · exact plane_triple_mem_73 i
  · exact plane_triple_mem_74 i
  · exact plane_triple_mem_75 i
  · exact plane_triple_mem_76 i
  · exact plane_triple_mem_77 i
  · exact plane_triple_mem_78 i
  · exact plane_triple_mem_79 i
  · exact plane_triple_mem_80 i
  · exact plane_triple_mem_81 i
  · exact plane_triple_mem_82 i
  · exact plane_triple_mem_83 i
  · exact plane_triple_mem_84 i
  · exact plane_triple_mem_85 i
  · exact plane_triple_mem_86 i
  · exact plane_triple_mem_87 i
  · exact plane_triple_mem_88 i
  · exact plane_triple_mem_89 i
  · exact plane_triple_mem_90 i
  · exact plane_triple_mem_91 i
  · exact plane_triple_mem_92 i
  · exact plane_triple_mem_93 i
  · exact plane_triple_mem_94 i
  · exact plane_triple_mem_95 i
  · exact plane_triple_mem_96 i
  · exact plane_triple_mem_97 i
  · exact plane_triple_mem_98 i
  · exact plane_triple_mem_99 i
  · exact plane_triple_mem_100 i
  · exact plane_triple_mem_101 i
  · exact plane_triple_mem_102 i
  · exact plane_triple_mem_103 i
  · exact plane_triple_mem_104 i
  · exact plane_triple_mem_105 i
  · exact plane_triple_mem_106 i
  · exact plane_triple_mem_107 i
  · exact plane_triple_mem_108 i
  · exact plane_triple_mem_109 i
  · exact plane_triple_mem_110 i
  · exact plane_triple_mem_111 i
  · exact plane_triple_mem_112 i
  · exact plane_triple_mem_113 i
  · exact plane_triple_mem_114 i
  · exact plane_triple_mem_115 i
  · exact plane_triple_mem_116 i
  · exact plane_triple_mem_117 i
  · exact plane_triple_mem_118 i
  · exact plane_triple_mem_119 i
theorem plane_covers_triple (i j k : Fin 24) : i∈planeMask (planeCode i j k) ∧ j∈planeMask (planeCode i j k) ∧ k∈planeMask (planeCode i j k) := by
  fin_cases i
  · exact plane_cover_0 j k
  · exact plane_cover_1 j k
  · exact plane_cover_2 j k
  · exact plane_cover_3 j k
  · exact plane_cover_4 j k
  · exact plane_cover_5 j k
  · exact plane_cover_6 j k
  · exact plane_cover_7 j k
  · exact plane_cover_8 j k
  · exact plane_cover_9 j k
  · exact plane_cover_10 j k
  · exact plane_cover_11 j k
  · exact plane_cover_12 j k
  · exact plane_cover_13 j k
  · exact plane_cover_14 j k
  · exact plane_cover_15 j k
  · exact plane_cover_16 j k
  · exact plane_cover_17 j k
  · exact plane_cover_18 j k
  · exact plane_cover_19 j k
  · exact plane_cover_20 j k
  · exact plane_cover_21 j k
  · exact plane_cover_22 j k
  · exact plane_cover_23 j k
theorem pair_table_exact (i j : Fin 24) : pairTable 0 i j=rawPair (rawPoint 0 i) (rawPoint 0 j) := by
  fin_cases i
  · exact pair_table_exact_0_0 j
  · exact pair_table_exact_0_1 j
  · exact pair_table_exact_0_2 j
  · exact pair_table_exact_0_3 j
  · exact pair_table_exact_0_4 j
  · exact pair_table_exact_0_5 j
  · exact pair_table_exact_0_6 j
  · exact pair_table_exact_0_7 j
  · exact pair_table_exact_0_8 j
  · exact pair_table_exact_0_9 j
  · exact pair_table_exact_0_10 j
  · exact pair_table_exact_0_11 j
  · exact pair_table_exact_0_12 j
  · exact pair_table_exact_0_13 j
  · exact pair_table_exact_0_14 j
  · exact pair_table_exact_0_15 j
  · exact pair_table_exact_0_16 j
  · exact pair_table_exact_0_17 j
  · exact pair_table_exact_0_18 j
  · exact pair_table_exact_0_19 j
  · exact pair_table_exact_0_20 j
  · exact pair_table_exact_0_21 j
  · exact pair_table_exact_0_22 j
  · exact pair_table_exact_0_23 j
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankThree
