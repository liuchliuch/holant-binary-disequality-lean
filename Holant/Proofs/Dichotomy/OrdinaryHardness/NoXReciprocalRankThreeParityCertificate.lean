import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityCert00
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityCert01
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityCert02
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityCert03
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityCert04
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityCert05
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityCert06
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityCert07
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityCert08
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityCert09
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityCert10
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityCert11
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityCert12
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityCert13
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityCert14
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityCert15

/-! Bounded finite certificates combined into the exact linear-face operator interface. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityCertificates
open NoXReciprocalRankThreeParityData
set_option maxHeartbeats 800000
set_option Elab.async false

theorem selected (p n : Fin 128) (hp:p.val≠127) (hn:n.val≠127) (hc:n.val≠127-p.val) :
    dot p (selector p n)=0 ∧ dot n (selector p n)=0 := by
  fin_cases p
  · exact selected_0 n hp hn hc
  · exact selected_1 n hp hn hc
  · exact selected_2 n hp hn hc
  · exact selected_3 n hp hn hc
  · exact selected_4 n hp hn hc
  · exact selected_5 n hp hn hc
  · exact selected_6 n hp hn hc
  · exact selected_7 n hp hn hc
  · exact selected_8 n hp hn hc
  · exact selected_9 n hp hn hc
  · exact selected_10 n hp hn hc
  · exact selected_11 n hp hn hc
  · exact selected_12 n hp hn hc
  · exact selected_13 n hp hn hc
  · exact selected_14 n hp hn hc
  · exact selected_15 n hp hn hc
  · exact selected_16 n hp hn hc
  · exact selected_17 n hp hn hc
  · exact selected_18 n hp hn hc
  · exact selected_19 n hp hn hc
  · exact selected_20 n hp hn hc
  · exact selected_21 n hp hn hc
  · exact selected_22 n hp hn hc
  · exact selected_23 n hp hn hc
  · exact selected_24 n hp hn hc
  · exact selected_25 n hp hn hc
  · exact selected_26 n hp hn hc
  · exact selected_27 n hp hn hc
  · exact selected_28 n hp hn hc
  · exact selected_29 n hp hn hc
  · exact selected_30 n hp hn hc
  · exact selected_31 n hp hn hc
  · exact selected_32 n hp hn hc
  · exact selected_33 n hp hn hc
  · exact selected_34 n hp hn hc
  · exact selected_35 n hp hn hc
  · exact selected_36 n hp hn hc
  · exact selected_37 n hp hn hc
  · exact selected_38 n hp hn hc
  · exact selected_39 n hp hn hc
  · exact selected_40 n hp hn hc
  · exact selected_41 n hp hn hc
  · exact selected_42 n hp hn hc
  · exact selected_43 n hp hn hc
  · exact selected_44 n hp hn hc
  · exact selected_45 n hp hn hc
  · exact selected_46 n hp hn hc
  · exact selected_47 n hp hn hc
  · exact selected_48 n hp hn hc
  · exact selected_49 n hp hn hc
  · exact selected_50 n hp hn hc
  · exact selected_51 n hp hn hc
  · exact selected_52 n hp hn hc
  · exact selected_53 n hp hn hc
  · exact selected_54 n hp hn hc
  · exact selected_55 n hp hn hc
  · exact selected_56 n hp hn hc
  · exact selected_57 n hp hn hc
  · exact selected_58 n hp hn hc
  · exact selected_59 n hp hn hc
  · exact selected_60 n hp hn hc
  · exact selected_61 n hp hn hc
  · exact selected_62 n hp hn hc
  · exact selected_63 n hp hn hc
  · exact selected_64 n hp hn hc
  · exact selected_65 n hp hn hc
  · exact selected_66 n hp hn hc
  · exact selected_67 n hp hn hc
  · exact selected_68 n hp hn hc
  · exact selected_69 n hp hn hc
  · exact selected_70 n hp hn hc
  · exact selected_71 n hp hn hc
  · exact selected_72 n hp hn hc
  · exact selected_73 n hp hn hc
  · exact selected_74 n hp hn hc
  · exact selected_75 n hp hn hc
  · exact selected_76 n hp hn hc
  · exact selected_77 n hp hn hc
  · exact selected_78 n hp hn hc
  · exact selected_79 n hp hn hc
  · exact selected_80 n hp hn hc
  · exact selected_81 n hp hn hc
  · exact selected_82 n hp hn hc
  · exact selected_83 n hp hn hc
  · exact selected_84 n hp hn hc
  · exact selected_85 n hp hn hc
  · exact selected_86 n hp hn hc
  · exact selected_87 n hp hn hc
  · exact selected_88 n hp hn hc
  · exact selected_89 n hp hn hc
  · exact selected_90 n hp hn hc
  · exact selected_91 n hp hn hc
  · exact selected_92 n hp hn hc
  · exact selected_93 n hp hn hc
  · exact selected_94 n hp hn hc
  · exact selected_95 n hp hn hc
  · exact selected_96 n hp hn hc
  · exact selected_97 n hp hn hc
  · exact selected_98 n hp hn hc
  · exact selected_99 n hp hn hc
  · exact selected_100 n hp hn hc
  · exact selected_101 n hp hn hc
  · exact selected_102 n hp hn hc
  · exact selected_103 n hp hn hc
  · exact selected_104 n hp hn hc
  · exact selected_105 n hp hn hc
  · exact selected_106 n hp hn hc
  · exact selected_107 n hp hn hc
  · exact selected_108 n hp hn hc
  · exact selected_109 n hp hn hc
  · exact selected_110 n hp hn hc
  · exact selected_111 n hp hn hc
  · exact selected_112 n hp hn hc
  · exact selected_113 n hp hn hc
  · exact selected_114 n hp hn hc
  · exact selected_115 n hp hn hc
  · exact selected_116 n hp hn hc
  · exact selected_117 n hp hn hc
  · exact selected_118 n hp hn hc
  · exact selected_119 n hp hn hc
  · exact selected_120 n hp hn hc
  · exact selected_121 n hp hn hc
  · exact selected_122 n hp hn hc
  · exact selected_123 n hp hn hc
  · exact selected_124 n hp hn hc
  · exact selected_125 n hp hn hc
  · exact selected_126 n hp hn hc
  · exact selected_127 n hp hn hc

theorem column_value (r : Fin 64) (i j : Fin 7) :
    column r i j=if functional r i then 1 else 0 := by
  fin_cases r
  · exact column_0 i j
  · exact column_1 i j
  · exact column_2 i j
  · exact column_3 i j
  · exact column_4 i j
  · exact column_5 i j
  · exact column_6 i j
  · exact column_7 i j
  · exact column_8 i j
  · exact column_9 i j
  · exact column_10 i j
  · exact column_11 i j
  · exact column_12 i j
  · exact column_13 i j
  · exact column_14 i j
  · exact column_15 i j
  · exact column_16 i j
  · exact column_17 i j
  · exact column_18 i j
  · exact column_19 i j
  · exact column_20 i j
  · exact column_21 i j
  · exact column_22 i j
  · exact column_23 i j
  · exact column_24 i j
  · exact column_25 i j
  · exact column_26 i j
  · exact column_27 i j
  · exact column_28 i j
  · exact column_29 i j
  · exact column_30 i j
  · exact column_31 i j
  · exact column_32 i j
  · exact column_33 i j
  · exact column_34 i j
  · exact column_35 i j
  · exact column_36 i j
  · exact column_37 i j
  · exact column_38 i j
  · exact column_39 i j
  · exact column_40 i j
  · exact column_41 i j
  · exact column_42 i j
  · exact column_43 i j
  · exact column_44 i j
  · exact column_45 i j
  · exact column_46 i j
  · exact column_47 i j
  · exact column_48 i j
  · exact column_49 i j
  · exact column_50 i j
  · exact column_51 i j
  · exact column_52 i j
  · exact column_53 i j
  · exact column_54 i j
  · exact column_55 i j
  · exact column_56 i j
  · exact column_57 i j
  · exact column_58 i j
  · exact column_59 i j
  · exact column_60 i j
  · exact column_61 i j
  · exact column_62 i j
  · exact column_63 i j


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeParityCertificates
