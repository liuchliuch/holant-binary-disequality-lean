import Holant.Certificates.AffineEndpointCounts.RetainedRoutesTrue
namespace Holant.Certificates.AffineEndpointCounts
open Holant.Certificates.AffineEndpoint Holant.Certificates.AffineEndpoint.BaseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option maxErrors 1
set_option backward.isDefEq.respectTransparency false

 theorem retained_true_000 (c : Fin 1) (hr : BaseRetained 0 c.val true) :
    (0,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 0 true 0 packetData0807 (candidatePairList true)
    packetPass0807 route0807 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_001 (c : Fin 1) (hr : BaseRetained 1 c.val true) :
    (1,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 1 true 0 packetData0808 (candidatePairList true)
    packetPass0808 route0808 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_002 (c : Fin 1) (hr : BaseRetained 2 c.val true) :
    (2,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 2 true 0 packetData0809 (candidatePairList true)
    packetPass0809 route0809 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_003 (c : Fin 1) (hr : BaseRetained 3 c.val true) :
    (3,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 3 true 0 packetData0810 (candidatePairList true)
    packetPass0810 route0810 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_004 (c : Fin 1) (hr : BaseRetained 4 c.val true) :
    (4,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 4 true 0 packetData0811 (candidatePairList true)
    packetPass0811 route0811 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_005 (c : Fin 1) (hr : BaseRetained 5 c.val true) :
    (5,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 5 true 0 packetData0812 (candidatePairList true)
    packetPass0812 route0812 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_006 (c : Fin 1) (hr : BaseRetained 6 c.val true) :
    (6,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 6 true 0 packetData0813 (candidatePairList true)
    packetPass0813 route0813 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_007 (c : Fin 1) (hr : BaseRetained 7 c.val true) :
    (7,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 7 true 0 packetData0814 (candidatePairList true)
    packetPass0814 route0814 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_008 (c : Fin 1) (hr : BaseRetained 8 c.val true) :
    (8,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 8 true 0 packetData0815 (candidatePairList true)
    packetPass0815 route0815 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_009 (c : Fin 1) (hr : BaseRetained 9 c.val true) :
    (9,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 9 true 0 packetData0816 (candidatePairList true)
    packetPass0816 route0816 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_010 (c : Fin 1) (hr : BaseRetained 10 c.val true) :
    (10,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 10 true 0 packetData0817 (candidatePairList true)
    packetPass0817 route0817 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_011 (c : Fin 1) (hr : BaseRetained 11 c.val true) :
    (11,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 11 true 0 packetData0818 (candidatePairList true)
    packetPass0818 route0818 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_012 (c : Fin 1) (hr : BaseRetained 12 c.val true) :
    (12,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 12 true 0 packetData0819 (candidatePairList true)
    packetPass0819 route0819 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_013 (c : Fin 1) (hr : BaseRetained 13 c.val true) :
    (13,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 13 true 0 packetData0820 (candidatePairList true)
    packetPass0820 route0820 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_014 (c : Fin 1) (hr : BaseRetained 14 c.val true) :
    (14,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 14 true 0 packetData0821 (candidatePairList true)
    packetPass0821 route0821 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_015 (c : Fin 1) (hr : BaseRetained 15 c.val true) :
    (15,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 15 true 0 packetData0822 (candidatePairList true)
    packetPass0822 route0822 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_016 (c : Fin 4) (hr : BaseRetained 16 c.val true) :
    (16,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 16 true 0 packetData0823 (candidatePairList true)
    packetPass0823 route0823 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_017 (c : Fin 4) (hr : BaseRetained 17 c.val true) :
    (17,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 17 true 0 packetData0824 (candidatePairList true)
    packetPass0824 route0824 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_018 (c : Fin 4) (hr : BaseRetained 18 c.val true) :
    (18,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 18 true 0 packetData0825 (candidatePairList true)
    packetPass0825 route0825 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_019 (c : Fin 4) (hr : BaseRetained 19 c.val true) :
    (19,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 19 true 0 packetData0826 (candidatePairList true)
    packetPass0826 route0826 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_020 (c : Fin 4) (hr : BaseRetained 20 c.val true) :
    (20,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 20 true 0 packetData0827 (candidatePairList true)
    packetPass0827 route0827 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_021 (c : Fin 4) (hr : BaseRetained 21 c.val true) :
    (21,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 21 true 0 packetData0828 (candidatePairList true)
    packetPass0828 route0828 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_022 (c : Fin 4) (hr : BaseRetained 22 c.val true) :
    (22,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 22 true 0 packetData0829 (candidatePairList true)
    packetPass0829 route0829 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_023 (c : Fin 4) (hr : BaseRetained 23 c.val true) :
    (23,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 23 true 0 packetData0830 (candidatePairList true)
    packetPass0830 route0830 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_024 (c : Fin 4) (hr : BaseRetained 24 c.val true) :
    (24,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 24 true 0 packetData0831 (candidatePairList true)
    packetPass0831 route0831 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_025 (c : Fin 4) (hr : BaseRetained 25 c.val true) :
    (25,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 25 true 0 packetData0832 (candidatePairList true)
    packetPass0832 route0832 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_026 (c : Fin 4) (hr : BaseRetained 26 c.val true) :
    (26,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 26 true 0 packetData0833 (candidatePairList true)
    packetPass0833 route0833 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_027 (c : Fin 4) (hr : BaseRetained 27 c.val true) :
    (27,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 27 true 0 packetData0834 (candidatePairList true)
    packetPass0834 route0834 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_028 (c : Fin 4) (hr : BaseRetained 28 c.val true) :
    (28,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 28 true 0 packetData0835 (candidatePairList true)
    packetPass0835 route0835 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_029 (c : Fin 4) (hr : BaseRetained 29 c.val true) :
    (29,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 29 true 0 packetData0836 (candidatePairList true)
    packetPass0836 route0836 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_030 (c : Fin 4) (hr : BaseRetained 30 c.val true) :
    (30,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 30 true 0 packetData0837 (candidatePairList true)
    packetPass0837 route0837 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_031 (c : Fin 4) (hr : BaseRetained 31 c.val true) :
    (31,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 31 true 0 packetData0838 (candidatePairList true)
    packetPass0838 route0838 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_032 (c : Fin 4) (hr : BaseRetained 32 c.val true) :
    (32,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 32 true 0 packetData0839 (candidatePairList true)
    packetPass0839 route0839 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_033 (c : Fin 4) (hr : BaseRetained 33 c.val true) :
    (33,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 33 true 0 packetData0840 (candidatePairList true)
    packetPass0840 route0840 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_034 (c : Fin 4) (hr : BaseRetained 34 c.val true) :
    (34,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 34 true 0 packetData0841 (candidatePairList true)
    packetPass0841 route0841 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_035 (c : Fin 4) (hr : BaseRetained 35 c.val true) :
    (35,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 35 true 0 packetData0842 (candidatePairList true)
    packetPass0842 route0842 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_036 (c : Fin 4) (hr : BaseRetained 36 c.val true) :
    (36,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 36 true 0 packetData0843 (candidatePairList true)
    packetPass0843 route0843 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_037 (c : Fin 4) (hr : BaseRetained 37 c.val true) :
    (37,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 37 true 0 packetData0844 (candidatePairList true)
    packetPass0844 route0844 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_038 (c : Fin 4) (hr : BaseRetained 38 c.val true) :
    (38,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 38 true 0 packetData0845 (candidatePairList true)
    packetPass0845 route0845 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_039 (c : Fin 4) (hr : BaseRetained 39 c.val true) :
    (39,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 39 true 0 packetData0846 (candidatePairList true)
    packetPass0846 route0846 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_040 (c : Fin 4) (hr : BaseRetained 40 c.val true) :
    (40,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 40 true 0 packetData0847 (candidatePairList true)
    packetPass0847 route0847 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_041 (c : Fin 4) (hr : BaseRetained 41 c.val true) :
    (41,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 41 true 0 packetData0848 (candidatePairList true)
    packetPass0848 route0848 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_042 (c : Fin 4) (hr : BaseRetained 42 c.val true) :
    (42,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 42 true 0 packetData0849 (candidatePairList true)
    packetPass0849 route0849 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_043 (c : Fin 4) (hr : BaseRetained 43 c.val true) :
    (43,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 43 true 0 packetData0850 (candidatePairList true)
    packetPass0850 route0850 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_044 (c : Fin 4) (hr : BaseRetained 44 c.val true) :
    (44,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 44 true 0 packetData0851 (candidatePairList true)
    packetPass0851 route0851 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_045 (c : Fin 4) (hr : BaseRetained 45 c.val true) :
    (45,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 45 true 0 packetData0852 (candidatePairList true)
    packetPass0852 route0852 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_046 (c : Fin 4) (hr : BaseRetained 46 c.val true) :
    (46,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 46 true 0 packetData0853 (candidatePairList true)
    packetPass0853 route0853 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_047 (c : Fin 4) (hr : BaseRetained 47 c.val true) :
    (47,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 47 true 0 packetData0854 (candidatePairList true)
    packetPass0854 route0854 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_048 (c : Fin 4) (hr : BaseRetained 48 c.val true) :
    (48,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 48 true 0 packetData0855 (candidatePairList true)
    packetPass0855 route0855 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_049 (c : Fin 4) (hr : BaseRetained 49 c.val true) :
    (49,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 49 true 0 packetData0856 (candidatePairList true)
    packetPass0856 route0856 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_050 (c : Fin 4) (hr : BaseRetained 50 c.val true) :
    (50,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 50 true 0 packetData0857 (candidatePairList true)
    packetPass0857 route0857 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_051 (c : Fin 4) (hr : BaseRetained 51 c.val true) :
    (51,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 51 true 0 packetData0858 (candidatePairList true)
    packetPass0858 route0858 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_052 (c : Fin 4) (hr : BaseRetained 52 c.val true) :
    (52,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 52 true 0 packetData0859 (candidatePairList true)
    packetPass0859 route0859 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_053 (c : Fin 4) (hr : BaseRetained 53 c.val true) :
    (53,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 53 true 0 packetData0860 (candidatePairList true)
    packetPass0860 route0860 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_054 (c : Fin 4) (hr : BaseRetained 54 c.val true) :
    (54,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 54 true 0 packetData0861 (candidatePairList true)
    packetPass0861 route0861 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_055 (c : Fin 4) (hr : BaseRetained 55 c.val true) :
    (55,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 55 true 0 packetData0862 (candidatePairList true)
    packetPass0862 route0862 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_056 (c : Fin 4) (hr : BaseRetained 56 c.val true) :
    (56,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 56 true 0 packetData0863 (candidatePairList true)
    packetPass0863 route0863 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_057 (c : Fin 4) (hr : BaseRetained 57 c.val true) :
    (57,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 57 true 0 packetData0864 (candidatePairList true)
    packetPass0864 route0864 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_058 (c : Fin 4) (hr : BaseRetained 58 c.val true) :
    (58,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 58 true 0 packetData0865 (candidatePairList true)
    packetPass0865 route0865 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_059 (c : Fin 4) (hr : BaseRetained 59 c.val true) :
    (59,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 59 true 0 packetData0866 (candidatePairList true)
    packetPass0866 route0866 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_060 (c : Fin 4) (hr : BaseRetained 60 c.val true) :
    (60,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 60 true 0 packetData0867 (candidatePairList true)
    packetPass0867 route0867 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_061 (c : Fin 4) (hr : BaseRetained 61 c.val true) :
    (61,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 61 true 0 packetData0868 (candidatePairList true)
    packetPass0868 route0868 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_062 (c : Fin 4) (hr : BaseRetained 62 c.val true) :
    (62,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 62 true 0 packetData0869 (candidatePairList true)
    packetPass0869 route0869 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_063 (c : Fin 4) (hr : BaseRetained 63 c.val true) :
    (63,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 63 true 0 packetData0870 (candidatePairList true)
    packetPass0870 route0870 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_064 (c : Fin 4) (hr : BaseRetained 64 c.val true) :
    (64,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 64 true 0 packetData0871 (candidatePairList true)
    packetPass0871 route0871 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_065 (c : Fin 4) (hr : BaseRetained 65 c.val true) :
    (65,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 65 true 0 packetData0872 (candidatePairList true)
    packetPass0872 route0872 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_066 (c : Fin 4) (hr : BaseRetained 66 c.val true) :
    (66,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 66 true 0 packetData0873 (candidatePairList true)
    packetPass0873 route0873 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_067 (c : Fin 4) (hr : BaseRetained 67 c.val true) :
    (67,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 67 true 0 packetData0874 (candidatePairList true)
    packetPass0874 route0874 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_068 (c : Fin 4) (hr : BaseRetained 68 c.val true) :
    (68,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 68 true 0 packetData0875 (candidatePairList true)
    packetPass0875 route0875 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_069 (c : Fin 4) (hr : BaseRetained 69 c.val true) :
    (69,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 69 true 0 packetData0876 (candidatePairList true)
    packetPass0876 route0876 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_070 (c : Fin 4) (hr : BaseRetained 70 c.val true) :
    (70,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 70 true 0 packetData0877 (candidatePairList true)
    packetPass0877 route0877 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_071 (c : Fin 4) (hr : BaseRetained 71 c.val true) :
    (71,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 71 true 0 packetData0878 (candidatePairList true)
    packetPass0878 route0878 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_072 (c : Fin 4) (hr : BaseRetained 72 c.val true) :
    (72,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 72 true 0 packetData0879 (candidatePairList true)
    packetPass0879 route0879 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_073 (c : Fin 4) (hr : BaseRetained 73 c.val true) :
    (73,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 73 true 0 packetData0880 (candidatePairList true)
    packetPass0880 route0880 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_074 (c : Fin 4) (hr : BaseRetained 74 c.val true) :
    (74,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 74 true 0 packetData0881 (candidatePairList true)
    packetPass0881 route0881 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_075 (c : Fin 4) (hr : BaseRetained 75 c.val true) :
    (75,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 75 true 0 packetData0882 (candidatePairList true)
    packetPass0882 route0882 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_076 (c : Fin 4) (hr : BaseRetained 76 c.val true) :
    (76,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 76 true 0 packetData0883 (candidatePairList true)
    packetPass0883 route0883 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_077 (c : Fin 4) (hr : BaseRetained 77 c.val true) :
    (77,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 77 true 0 packetData0884 (candidatePairList true)
    packetPass0884 route0884 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_078 (c : Fin 4) (hr : BaseRetained 78 c.val true) :
    (78,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 78 true 0 packetData0885 (candidatePairList true)
    packetPass0885 route0885 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_079 (c : Fin 4) (hr : BaseRetained 79 c.val true) :
    (79,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 79 true 0 packetData0886 (candidatePairList true)
    packetPass0886 route0886 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_080 (c : Fin 4) (hr : BaseRetained 80 c.val true) :
    (80,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 80 true 0 packetData0887 (candidatePairList true)
    packetPass0887 route0887 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_081 (c : Fin 4) (hr : BaseRetained 81 c.val true) :
    (81,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 81 true 0 packetData0888 (candidatePairList true)
    packetPass0888 route0888 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_082 (c : Fin 4) (hr : BaseRetained 82 c.val true) :
    (82,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 82 true 0 packetData0889 (candidatePairList true)
    packetPass0889 route0889 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_083 (c : Fin 4) (hr : BaseRetained 83 c.val true) :
    (83,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 83 true 0 packetData0890 (candidatePairList true)
    packetPass0890 route0890 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_084 (c : Fin 4) (hr : BaseRetained 84 c.val true) :
    (84,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 84 true 0 packetData0891 (candidatePairList true)
    packetPass0891 route0891 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_085 (c : Fin 4) (hr : BaseRetained 85 c.val true) :
    (85,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 85 true 0 packetData0892 (candidatePairList true)
    packetPass0892 route0892 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_086 (c : Fin 4) (hr : BaseRetained 86 c.val true) :
    (86,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 86 true 0 packetData0893 (candidatePairList true)
    packetPass0893 route0893 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_087 (c : Fin 4) (hr : BaseRetained 87 c.val true) :
    (87,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 87 true 0 packetData0894 (candidatePairList true)
    packetPass0894 route0894 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_088 (c : Fin 4) (hr : BaseRetained 88 c.val true) :
    (88,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 88 true 0 packetData0895 (candidatePairList true)
    packetPass0895 route0895 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_089 (c : Fin 4) (hr : BaseRetained 89 c.val true) :
    (89,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 89 true 0 packetData0896 (candidatePairList true)
    packetPass0896 route0896 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_090 (c : Fin 4) (hr : BaseRetained 90 c.val true) :
    (90,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 90 true 0 packetData0897 (candidatePairList true)
    packetPass0897 route0897 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_091 (c : Fin 4) (hr : BaseRetained 91 c.val true) :
    (91,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 91 true 0 packetData0898 (candidatePairList true)
    packetPass0898 route0898 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_092 (c : Fin 4) (hr : BaseRetained 92 c.val true) :
    (92,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 92 true 0 packetData0899 (candidatePairList true)
    packetPass0899 route0899 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_093 (c : Fin 4) (hr : BaseRetained 93 c.val true) :
    (93,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 93 true 0 packetData0900 (candidatePairList true)
    packetPass0900 route0900 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_094 (c : Fin 4) (hr : BaseRetained 94 c.val true) :
    (94,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 94 true 0 packetData0901 (candidatePairList true)
    packetPass0901 route0901 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_095 (c : Fin 4) (hr : BaseRetained 95 c.val true) :
    (95,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 95 true 0 packetData0902 (candidatePairList true)
    packetPass0902 route0902 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_096 (c : Fin 4) (hr : BaseRetained 96 c.val true) :
    (96,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 96 true 0 packetData0903 (candidatePairList true)
    packetPass0903 route0903 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_097 (c : Fin 4) (hr : BaseRetained 97 c.val true) :
    (97,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 97 true 0 packetData0904 (candidatePairList true)
    packetPass0904 route0904 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_098 (c : Fin 4) (hr : BaseRetained 98 c.val true) :
    (98,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 98 true 0 packetData0905 (candidatePairList true)
    packetPass0905 route0905 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_099 (c : Fin 4) (hr : BaseRetained 99 c.val true) :
    (99,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 99 true 0 packetData0906 (candidatePairList true)
    packetPass0906 route0906 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_100 (c : Fin 4) (hr : BaseRetained 100 c.val true) :
    (100,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 100 true 0 packetData0907 (candidatePairList true)
    packetPass0907 route0907 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_101 (c : Fin 4) (hr : BaseRetained 101 c.val true) :
    (101,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 101 true 0 packetData0908 (candidatePairList true)
    packetPass0908 route0908 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_102 (c : Fin 4) (hr : BaseRetained 102 c.val true) :
    (102,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 102 true 0 packetData0909 (candidatePairList true)
    packetPass0909 route0909 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_103 (c : Fin 4) (hr : BaseRetained 103 c.val true) :
    (103,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 103 true 0 packetData0910 (candidatePairList true)
    packetPass0910 route0910 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_104 (c : Fin 4) (hr : BaseRetained 104 c.val true) :
    (104,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 104 true 0 packetData0911 (candidatePairList true)
    packetPass0911 route0911 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_105 (c : Fin 4) (hr : BaseRetained 105 c.val true) :
    (105,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 105 true 0 packetData0912 (candidatePairList true)
    packetPass0912 route0912 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_106 (c : Fin 4) (hr : BaseRetained 106 c.val true) :
    (106,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 106 true 0 packetData0913 (candidatePairList true)
    packetPass0913 route0913 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_107 (c : Fin 4) (hr : BaseRetained 107 c.val true) :
    (107,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 107 true 0 packetData0914 (candidatePairList true)
    packetPass0914 route0914 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_108 (c : Fin 4) (hr : BaseRetained 108 c.val true) :
    (108,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 108 true 0 packetData0915 (candidatePairList true)
    packetPass0915 route0915 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_109 (c : Fin 4) (hr : BaseRetained 109 c.val true) :
    (109,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 109 true 0 packetData0916 (candidatePairList true)
    packetPass0916 route0916 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_110 (c : Fin 4) (hr : BaseRetained 110 c.val true) :
    (110,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 110 true 0 packetData0917 (candidatePairList true)
    packetPass0917 route0917 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_111 (c : Fin 4) (hr : BaseRetained 111 c.val true) :
    (111,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 111 true 0 packetData0918 (candidatePairList true)
    packetPass0918 route0918 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_112 (c : Fin 4) (hr : BaseRetained 112 c.val true) :
    (112,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 112 true 0 packetData0919 (candidatePairList true)
    packetPass0919 route0919 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_113 (c : Fin 4) (hr : BaseRetained 113 c.val true) :
    (113,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 113 true 0 packetData0920 (candidatePairList true)
    packetPass0920 route0920 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_114 (c : Fin 4) (hr : BaseRetained 114 c.val true) :
    (114,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 114 true 0 packetData0921 (candidatePairList true)
    packetPass0921 route0921 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_115 (c : Fin 4) (hr : BaseRetained 115 c.val true) :
    (115,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 115 true 0 packetData0922 (candidatePairList true)
    packetPass0922 route0922 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_116 (c : Fin 4) (hr : BaseRetained 116 c.val true) :
    (116,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 116 true 0 packetData0923 (candidatePairList true)
    packetPass0923 route0923 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_117 (c : Fin 4) (hr : BaseRetained 117 c.val true) :
    (117,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 117 true 0 packetData0924 (candidatePairList true)
    packetPass0924 route0924 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_118 (c : Fin 4) (hr : BaseRetained 118 c.val true) :
    (118,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 118 true 0 packetData0925 (candidatePairList true)
    packetPass0925 route0925 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_119 (c : Fin 4) (hr : BaseRetained 119 c.val true) :
    (119,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 119 true 0 packetData0926 (candidatePairList true)
    packetPass0926 route0926 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_120 (c : Fin 4) (hr : BaseRetained 120 c.val true) :
    (120,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 120 true 0 packetData0927 (candidatePairList true)
    packetPass0927 route0927 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_121 (c : Fin 4) (hr : BaseRetained 121 c.val true) :
    (121,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 121 true 0 packetData0928 (candidatePairList true)
    packetPass0928 route0928 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_122 (c : Fin 4) (hr : BaseRetained 122 c.val true) :
    (122,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 122 true 0 packetData0929 (candidatePairList true)
    packetPass0929 route0929 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_123 (c : Fin 4) (hr : BaseRetained 123 c.val true) :
    (123,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 123 true 0 packetData0930 (candidatePairList true)
    packetPass0930 route0930 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_124 (c : Fin 4) (hr : BaseRetained 124 c.val true) :
    (124,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 124 true 0 packetData0931 (candidatePairList true)
    packetPass0931 route0931 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_125 (c : Fin 4) (hr : BaseRetained 125 c.val true) :
    (125,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 125 true 0 packetData0932 (candidatePairList true)
    packetPass0932 route0932 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_126 (c : Fin 4) (hr : BaseRetained 126 c.val true) :
    (126,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 126 true 0 packetData0933 (candidatePairList true)
    packetPass0933 route0933 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_127 (c : Fin 4) (hr : BaseRetained 127 c.val true) :
    (127,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 127 true 0 packetData0934 (candidatePairList true)
    packetPass0934 route0934 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_128 (c : Fin 4) (hr : BaseRetained 128 c.val true) :
    (128,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 128 true 0 packetData0935 (candidatePairList true)
    packetPass0935 route0935 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_129 (c : Fin 4) (hr : BaseRetained 129 c.val true) :
    (129,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 129 true 0 packetData0936 (candidatePairList true)
    packetPass0936 route0936 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_130 (c : Fin 4) (hr : BaseRetained 130 c.val true) :
    (130,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 130 true 0 packetData0937 (candidatePairList true)
    packetPass0937 route0937 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_131 (c : Fin 4) (hr : BaseRetained 131 c.val true) :
    (131,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 131 true 0 packetData0938 (candidatePairList true)
    packetPass0938 route0938 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_132 (c : Fin 4) (hr : BaseRetained 132 c.val true) :
    (132,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 132 true 0 packetData0939 (candidatePairList true)
    packetPass0939 route0939 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_133 (c : Fin 4) (hr : BaseRetained 133 c.val true) :
    (133,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 133 true 0 packetData0940 (candidatePairList true)
    packetPass0940 route0940 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_134 (c : Fin 4) (hr : BaseRetained 134 c.val true) :
    (134,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 134 true 0 packetData0941 (candidatePairList true)
    packetPass0941 route0941 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_135 (c : Fin 4) (hr : BaseRetained 135 c.val true) :
    (135,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 135 true 0 packetData0942 (candidatePairList true)
    packetPass0942 route0942 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_136 (c : Fin 32) (hr : BaseRetained 136 c.val true) :
    (136,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 136 true 0 packetData0943 (candidatePairList true)
    packetPass0943 route0943 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_137 (c : Fin 32) (hr : BaseRetained 137 c.val true) :
    (137,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 137 true 0 packetData0944 (candidatePairList true)
    packetPass0944 route0944 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_138 (c : Fin 32) (hr : BaseRetained 138 c.val true) :
    (138,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 138 true 0 packetData0945 (candidatePairList true)
    packetPass0945 route0945 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_139 (c : Fin 32) (hr : BaseRetained 139 c.val true) :
    (139,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 139 true 0 packetData0946 (candidatePairList true)
    packetPass0946 route0946 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_140 (c : Fin 32) (hr : BaseRetained 140 c.val true) :
    (140,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 140 true 0 packetData0947 (candidatePairList true)
    packetPass0947 route0947 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_141 (c : Fin 32) (hr : BaseRetained 141 c.val true) :
    (141,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 141 true 0 packetData0948 (candidatePairList true)
    packetPass0948 route0948 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_142 (c : Fin 32) (hr : BaseRetained 142 c.val true) :
    (142,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 142 true 0 packetData0949 (candidatePairList true)
    packetPass0949 route0949 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_143 (c : Fin 32) (hr : BaseRetained 143 c.val true) :
    (143,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 143 true 0 packetData0950 (candidatePairList true)
    packetPass0950 route0950 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_144 (c : Fin 32) (hr : BaseRetained 144 c.val true) :
    (144,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 144 true 0 packetData0951 (candidatePairList true)
    packetPass0951 route0951 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_145 (c : Fin 32) (hr : BaseRetained 145 c.val true) :
    (145,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 145 true 0 packetData0952 (candidatePairList true)
    packetPass0952 route0952 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_146 (c : Fin 32) (hr : BaseRetained 146 c.val true) :
    (146,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 146 true 0 packetData0953 (candidatePairList true)
    packetPass0953 route0953 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_147 (c : Fin 32) (hr : BaseRetained 147 c.val true) :
    (147,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 147 true 0 packetData0954 (candidatePairList true)
    packetPass0954 route0954 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_148 (c : Fin 32) (hr : BaseRetained 148 c.val true) :
    (148,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 148 true 0 packetData0955 (candidatePairList true)
    packetPass0955 route0955 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_149 (c : Fin 32) (hr : BaseRetained 149 c.val true) :
    (149,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 149 true 0 packetData0956 (candidatePairList true)
    packetPass0956 route0956 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_150 (c : Fin 32) (hr : BaseRetained 150 c.val true) :
    (150,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 150 true 0 packetData0957 (candidatePairList true)
    packetPass0957 route0957 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_151 (c : Fin 32) (hr : BaseRetained 151 c.val true) :
    (151,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 151 true 0 packetData0958 (candidatePairList true)
    packetPass0958 route0958 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_152 (c : Fin 32) (hr : BaseRetained 152 c.val true) :
    (152,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 152 true 0 packetData0959 (candidatePairList true)
    packetPass0959 route0959 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_153 (c : Fin 32) (hr : BaseRetained 153 c.val true) :
    (153,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 153 true 0 packetData0960 (candidatePairList true)
    packetPass0960 route0960 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_154 (c : Fin 32) (hr : BaseRetained 154 c.val true) :
    (154,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 154 true 0 packetData0961 (candidatePairList true)
    packetPass0961 route0961 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_155 (c : Fin 32) (hr : BaseRetained 155 c.val true) :
    (155,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 155 true 0 packetData0962 (candidatePairList true)
    packetPass0962 route0962 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_156 (c : Fin 32) (hr : BaseRetained 156 c.val true) :
    (156,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 156 true 0 packetData0963 (candidatePairList true)
    packetPass0963 route0963 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_157 (c : Fin 32) (hr : BaseRetained 157 c.val true) :
    (157,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 157 true 0 packetData0964 (candidatePairList true)
    packetPass0964 route0964 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_158 (c : Fin 32) (hr : BaseRetained 158 c.val true) :
    (158,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 158 true 0 packetData0965 (candidatePairList true)
    packetPass0965 route0965 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_159 (c : Fin 32) (hr : BaseRetained 159 c.val true) :
    (159,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 159 true 0 packetData0966 (candidatePairList true)
    packetPass0966 route0966 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_160 (c : Fin 32) (hr : BaseRetained 160 c.val true) :
    (160,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 160 true 0 packetData0967 (candidatePairList true)
    packetPass0967 route0967 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_161 (c : Fin 32) (hr : BaseRetained 161 c.val true) :
    (161,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 161 true 0 packetData0968 (candidatePairList true)
    packetPass0968 route0968 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_162 (c : Fin 32) (hr : BaseRetained 162 c.val true) :
    (162,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 162 true 0 packetData0969 (candidatePairList true)
    packetPass0969 route0969 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_163 (c : Fin 32) (hr : BaseRetained 163 c.val true) :
    (163,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 163 true 0 packetData0970 (candidatePairList true)
    packetPass0970 route0970 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_164 (c : Fin 32) (hr : BaseRetained 164 c.val true) :
    (164,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 164 true 0 packetData0971 (candidatePairList true)
    packetPass0971 route0971 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_165 (c : Fin 32) (hr : BaseRetained 165 c.val true) :
    (165,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 165 true 0 packetData0972 (candidatePairList true)
    packetPass0972 route0972 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_166 (c : Fin 32) (hr : BaseRetained 166 c.val true) :
    (166,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 166 true 0 packetData0973 (candidatePairList true)
    packetPass0973 route0973 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_167 (c : Fin 32) (hr : BaseRetained 167 c.val true) :
    (167,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 167 true 0 packetData0974 (candidatePairList true)
    packetPass0974 route0974 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_168 (c : Fin 32) (hr : BaseRetained 168 c.val true) :
    (168,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 168 true 0 packetData0975 (candidatePairList true)
    packetPass0975 route0975 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_169 (c : Fin 32) (hr : BaseRetained 169 c.val true) :
    (169,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 169 true 0 packetData0976 (candidatePairList true)
    packetPass0976 route0976 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_170 (c : Fin 32) (hr : BaseRetained 170 c.val true) :
    (170,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 170 true 0 packetData0977 (candidatePairList true)
    packetPass0977 route0977 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_171 (c : Fin 32) (hr : BaseRetained 171 c.val true) :
    (171,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 171 true 0 packetData0978 (candidatePairList true)
    packetPass0978 route0978 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_172 (c : Fin 32) (hr : BaseRetained 172 c.val true) :
    (172,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 172 true 0 packetData0979 (candidatePairList true)
    packetPass0979 route0979 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_173 (c : Fin 32) (hr : BaseRetained 173 c.val true) :
    (173,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 173 true 0 packetData0980 (candidatePairList true)
    packetPass0980 route0980 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_174 (c : Fin 32) (hr : BaseRetained 174 c.val true) :
    (174,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 174 true 0 packetData0981 (candidatePairList true)
    packetPass0981 route0981 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_175 (c : Fin 32) (hr : BaseRetained 175 c.val true) :
    (175,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 175 true 0 packetData0982 (candidatePairList true)
    packetPass0982 route0982 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_176 (c : Fin 32) (hr : BaseRetained 176 c.val true) :
    (176,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 176 true 0 packetData0983 (candidatePairList true)
    packetPass0983 route0983 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_177 (c : Fin 32) (hr : BaseRetained 177 c.val true) :
    (177,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 177 true 0 packetData0984 (candidatePairList true)
    packetPass0984 route0984 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_178 (c : Fin 32) (hr : BaseRetained 178 c.val true) :
    (178,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 178 true 0 packetData0985 (candidatePairList true)
    packetPass0985 route0985 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_179 (c : Fin 32) (hr : BaseRetained 179 c.val true) :
    (179,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 179 true 0 packetData0986 (candidatePairList true)
    packetPass0986 route0986 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_180 (c : Fin 32) (hr : BaseRetained 180 c.val true) :
    (180,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 180 true 0 packetData0987 (candidatePairList true)
    packetPass0987 route0987 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_181 (c : Fin 32) (hr : BaseRetained 181 c.val true) :
    (181,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 181 true 0 packetData0988 (candidatePairList true)
    packetPass0988 route0988 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_182 (c : Fin 32) (hr : BaseRetained 182 c.val true) :
    (182,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 182 true 0 packetData0989 (candidatePairList true)
    packetPass0989 route0989 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_183 (c : Fin 32) (hr : BaseRetained 183 c.val true) :
    (183,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 183 true 0 packetData0990 (candidatePairList true)
    packetPass0990 route0990 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_184 (c : Fin 32) (hr : BaseRetained 184 c.val true) :
    (184,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 184 true 0 packetData0991 (candidatePairList true)
    packetPass0991 route0991 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_185 (c : Fin 32) (hr : BaseRetained 185 c.val true) :
    (185,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 185 true 0 packetData0992 (candidatePairList true)
    packetPass0992 route0992 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_186 (c : Fin 32) (hr : BaseRetained 186 c.val true) :
    (186,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 186 true 0 packetData0993 (candidatePairList true)
    packetPass0993 route0993 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_187 (c : Fin 32) (hr : BaseRetained 187 c.val true) :
    (187,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 187 true 0 packetData0994 (candidatePairList true)
    packetPass0994 route0994 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_188 (c : Fin 32) (hr : BaseRetained 188 c.val true) :
    (188,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 188 true 0 packetData0995 (candidatePairList true)
    packetPass0995 route0995 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_189 (c : Fin 32) (hr : BaseRetained 189 c.val true) :
    (189,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 189 true 0 packetData0996 (candidatePairList true)
    packetPass0996 route0996 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_190 (c : Fin 32) (hr : BaseRetained 190 c.val true) :
    (190,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 190 true 0 packetData0997 (candidatePairList true)
    packetPass0997 route0997 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_191 (c : Fin 32) (hr : BaseRetained 191 c.val true) :
    (191,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 191 true 0 packetData0998 (candidatePairList true)
    packetPass0998 route0998 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_192 (c : Fin 32) (hr : BaseRetained 192 c.val true) :
    (192,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 192 true 0 packetData0999 (candidatePairList true)
    packetPass0999 route0999 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_193 (c : Fin 32) (hr : BaseRetained 193 c.val true) :
    (193,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 193 true 0 packetData1000 (candidatePairList true)
    packetPass1000 route1000 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_194 (c : Fin 32) (hr : BaseRetained 194 c.val true) :
    (194,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 194 true 0 packetData1001 (candidatePairList true)
    packetPass1001 route1001 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_195 (c : Fin 32) (hr : BaseRetained 195 c.val true) :
    (195,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 195 true 0 packetData1002 (candidatePairList true)
    packetPass1002 route1002 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_196 (c : Fin 32) (hr : BaseRetained 196 c.val true) :
    (196,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 196 true 0 packetData1003 (candidatePairList true)
    packetPass1003 route1003 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_197 (c : Fin 32) (hr : BaseRetained 197 c.val true) :
    (197,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 197 true 0 packetData1004 (candidatePairList true)
    packetPass1004 route1004 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_198 (c : Fin 32) (hr : BaseRetained 198 c.val true) :
    (198,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 198 true 0 packetData1005 (candidatePairList true)
    packetPass1005 route1005 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_199 (c : Fin 32) (hr : BaseRetained 199 c.val true) :
    (199,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 199 true 0 packetData1006 (candidatePairList true)
    packetPass1006 route1006 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_200 (c : Fin 32) (hr : BaseRetained 200 c.val true) :
    (200,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 200 true 0 packetData1007 (candidatePairList true)
    packetPass1007 route1007 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_201 (c : Fin 32) (hr : BaseRetained 201 c.val true) :
    (201,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 201 true 0 packetData1008 (candidatePairList true)
    packetPass1008 route1008 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_202 (c : Fin 32) (hr : BaseRetained 202 c.val true) :
    (202,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 202 true 0 packetData1009 (candidatePairList true)
    packetPass1009 route1009 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_203 (c : Fin 32) (hr : BaseRetained 203 c.val true) :
    (203,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 203 true 0 packetData1010 (candidatePairList true)
    packetPass1010 route1010 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_204 (c : Fin 32) (hr : BaseRetained 204 c.val true) :
    (204,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 204 true 0 packetData0020 (candidatePairList true)
    packetPass0020 route0020 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_205 (c : Fin 32) (hr : BaseRetained 205 c.val true) :
    (205,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 205 true 0 packetData1011 (candidatePairList true)
    packetPass1011 route1011 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_206 (c : Fin 32) (hr : BaseRetained 206 c.val true) :
    (206,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 206 true 0 packetData1012 (candidatePairList true)
    packetPass1012 route1012 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_207 (c : Fin 32) (hr : BaseRetained 207 c.val true) :
    (207,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 207 true 0 packetData1013 (candidatePairList true)
    packetPass1013 route1013 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_208 (c : Fin 32) (hr : BaseRetained 208 c.val true) :
    (208,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 208 true 0 packetData1014 (candidatePairList true)
    packetPass1014 route1014 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_209 (c : Fin 32) (hr : BaseRetained 209 c.val true) :
    (209,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 209 true 0 packetData1015 (candidatePairList true)
    packetPass1015 route1015 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_210 (c : Fin 32) (hr : BaseRetained 210 c.val true) :
    (210,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 210 true 0 packetData1016 (candidatePairList true)
    packetPass1016 route1016 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_211 (c : Fin 32) (hr : BaseRetained 211 c.val true) :
    (211,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 211 true 0 packetData1017 (candidatePairList true)
    packetPass1017 route1017 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_212 (c : Fin 32) (hr : BaseRetained 212 c.val true) :
    (212,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 212 true 0 packetData1018 (candidatePairList true)
    packetPass1018 route1018 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_213 (c : Fin 32) (hr : BaseRetained 213 c.val true) :
    (213,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 213 true 0 packetData1019 (candidatePairList true)
    packetPass1019 route1019 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_214 (c : Fin 32) (hr : BaseRetained 214 c.val true) :
    (214,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 214 true 0 packetData1020 (candidatePairList true)
    packetPass1020 route1020 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_215 (c : Fin 32) (hr : BaseRetained 215 c.val true) :
    (215,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 215 true 0 packetData1021 (candidatePairList true)
    packetPass1021 route1021 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_216 (c : Fin 32) (hr : BaseRetained 216 c.val true) :
    (216,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 216 true 0 packetData1022 (candidatePairList true)
    packetPass1022 route1022 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_217 (c : Fin 32) (hr : BaseRetained 217 c.val true) :
    (217,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 217 true 0 packetData1023 (candidatePairList true)
    packetPass1023 route1023 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_218 (c : Fin 32) (hr : BaseRetained 218 c.val true) :
    (218,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 218 true 0 packetData1024 (candidatePairList true)
    packetPass1024 route1024 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_219 (c : Fin 32) (hr : BaseRetained 219 c.val true) :
    (219,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 219 true 0 packetData1025 (candidatePairList true)
    packetPass1025 route1025 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_220 (c : Fin 32) (hr : BaseRetained 220 c.val true) :
    (220,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 220 true 0 packetData1026 (candidatePairList true)
    packetPass1026 route1026 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_221 (c : Fin 32) (hr : BaseRetained 221 c.val true) :
    (221,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 221 true 0 packetData1027 (candidatePairList true)
    packetPass1027 route1027 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_222 (c : Fin 32) (hr : BaseRetained 222 c.val true) :
    (222,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 222 true 0 packetData1028 (candidatePairList true)
    packetPass1028 route1028 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_223 (c : Fin 32) (hr : BaseRetained 223 c.val true) :
    (223,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 223 true 0 packetData1029 (candidatePairList true)
    packetPass1029 route1029 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_224 (c : Fin 32) (hr : BaseRetained 224 c.val true) :
    (224,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 224 true 0 packetData1030 (candidatePairList true)
    packetPass1030 route1030 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_225 (c : Fin 32) (hr : BaseRetained 225 c.val true) :
    (225,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 225 true 0 packetData1031 (candidatePairList true)
    packetPass1031 route1031 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_226 (c : Fin 32) (hr : BaseRetained 226 c.val true) :
    (226,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 226 true 0 packetData1032 (candidatePairList true)
    packetPass1032 route1032 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_227 (c : Fin 32) (hr : BaseRetained 227 c.val true) :
    (227,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 227 true 0 packetData1033 (candidatePairList true)
    packetPass1033 route1033 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_228 (c : Fin 32) (hr : BaseRetained 228 c.val true) :
    (228,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 228 true 0 packetData1034 (candidatePairList true)
    packetPass1034 route1034 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_229 (c : Fin 32) (hr : BaseRetained 229 c.val true) :
    (229,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 229 true 0 packetData1035 (candidatePairList true)
    packetPass1035 route1035 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_230 (c : Fin 32) (hr : BaseRetained 230 c.val true) :
    (230,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 230 true 0 packetData1036 (candidatePairList true)
    packetPass1036 route1036 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_231 (c : Fin 32) (hr : BaseRetained 231 c.val true) :
    (231,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 231 true 0 packetData1037 (candidatePairList true)
    packetPass1037 route1037 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_232 (c : Fin 32) (hr : BaseRetained 232 c.val true) :
    (232,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 232 true 0 packetData1038 (candidatePairList true)
    packetPass1038 route1038 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_233 (c : Fin 32) (hr : BaseRetained 233 c.val true) :
    (233,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 233 true 0 packetData1039 (candidatePairList true)
    packetPass1039 route1039 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_234 (c : Fin 32) (hr : BaseRetained 234 c.val true) :
    (234,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 234 true 0 packetData1040 (candidatePairList true)
    packetPass1040 route1040 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_235 (c : Fin 32) (hr : BaseRetained 235 c.val true) :
    (235,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 235 true 0 packetData1041 (candidatePairList true)
    packetPass1041 route1041 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_236 (c : Fin 32) (hr : BaseRetained 236 c.val true) :
    (236,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 236 true 0 packetData0021 (candidatePairList true)
    packetPass0021 route0021 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_237 (c : Fin 32) (hr : BaseRetained 237 c.val true) :
    (237,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 237 true 0 packetData1042 (candidatePairList true)
    packetPass1042 route1042 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_238 (c : Fin 32) (hr : BaseRetained 238 c.val true) :
    (238,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 238 true 0 packetData1043 (candidatePairList true)
    packetPass1043 route1043 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_239 (c : Fin 32) (hr : BaseRetained 239 c.val true) :
    (239,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 239 true 0 packetData1044 (candidatePairList true)
    packetPass1044 route1044 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_240 (c : Fin 32) (hr : BaseRetained 240 c.val true) :
    (240,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 240 true 0 packetData1045 (candidatePairList true)
    packetPass1045 route1045 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_241 (c : Fin 32) (hr : BaseRetained 241 c.val true) :
    (241,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 241 true 0 packetData1046 (candidatePairList true)
    packetPass1046 route1046 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_242 (c : Fin 32) (hr : BaseRetained 242 c.val true) :
    (242,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 242 true 0 packetData1047 (candidatePairList true)
    packetPass1047 route1047 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_243 (c : Fin 32) (hr : BaseRetained 243 c.val true) :
    (243,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 243 true 0 packetData1048 (candidatePairList true)
    packetPass1048 route1048 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_244 (c : Fin 32) (hr : BaseRetained 244 c.val true) :
    (244,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 244 true 0 packetData1049 (candidatePairList true)
    packetPass1049 route1049 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_245 (c : Fin 32) (hr : BaseRetained 245 c.val true) :
    (245,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 245 true 0 packetData1050 (candidatePairList true)
    packetPass1050 route1050 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_246 (c : Fin 32) (hr : BaseRetained 246 c.val true) :
    (246,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 246 true 0 packetData1051 (candidatePairList true)
    packetPass1051 route1051 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_247 (c : Fin 32) (hr : BaseRetained 247 c.val true) :
    (247,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 247 true 0 packetData1052 (candidatePairList true)
    packetPass1052 route1052 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_248 (c : Fin 32) (hr : BaseRetained 248 c.val true) :
    (248,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 248 true 0 packetData0022 (candidatePairList true)
    packetPass0022 route0022 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_249 (c : Fin 32) (hr : BaseRetained 249 c.val true) :
    (249,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 249 true 0 packetData1053 (candidatePairList true)
    packetPass1053 route1053 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_250 (c : Fin 32) (hr : BaseRetained 250 c.val true) :
    (250,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 250 true 0 packetData1054 (candidatePairList true)
    packetPass1054 route1054 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_251 (c : Fin 32) (hr : BaseRetained 251 c.val true) :
    (251,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 251 true 0 packetData1055 (candidatePairList true)
    packetPass1055 route1055 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_252 (c : Fin 32) (hr : BaseRetained 252 c.val true) :
    (252,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 252 true 0 packetData1056 (candidatePairList true)
    packetPass1056 route1056 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_253 (c : Fin 32) (hr : BaseRetained 253 c.val true) :
    (253,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 253 true 0 packetData1057 (candidatePairList true)
    packetPass1057 route1057 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_254 (c : Fin 32) (hr : BaseRetained 254 c.val true) :
    (254,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 254 true 0 packetData1058 (candidatePairList true)
    packetPass1058 route1058 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_255 (c : Fin 32) (hr : BaseRetained 255 c.val true) :
    (255,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 255 true 0 packetData1059 (candidatePairList true)
    packetPass1059 route1059 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_256 (c : Fin 32) (hr : BaseRetained 256 c.val true) :
    (256,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 256 true 0 packetData1060 (candidatePairList true)
    packetPass1060 route1060 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_257 (c : Fin 32) (hr : BaseRetained 257 c.val true) :
    (257,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 257 true 0 packetData1061 (candidatePairList true)
    packetPass1061 route1061 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_258 (c : Fin 32) (hr : BaseRetained 258 c.val true) :
    (258,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 258 true 0 packetData1062 (candidatePairList true)
    packetPass1062 route1062 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_259 (c : Fin 32) (hr : BaseRetained 259 c.val true) :
    (259,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 259 true 0 packetData1063 (candidatePairList true)
    packetPass1063 route1063 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_260 (c : Fin 32) (hr : BaseRetained 260 c.val true) :
    (260,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 260 true 0 packetData1064 (candidatePairList true)
    packetPass1064 route1064 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_261 (c : Fin 32) (hr : BaseRetained 261 c.val true) :
    (261,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 261 true 0 packetData1065 (candidatePairList true)
    packetPass1065 route1065 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_262 (c : Fin 32) (hr : BaseRetained 262 c.val true) :
    (262,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 262 true 0 packetData1066 (candidatePairList true)
    packetPass1066 route1066 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_263 (c : Fin 32) (hr : BaseRetained 263 c.val true) :
    (263,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 263 true 0 packetData1067 (candidatePairList true)
    packetPass1067 route1067 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_264 (c : Fin 32) (hr : BaseRetained 264 c.val true) :
    (264,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 264 true 0 packetData1068 (candidatePairList true)
    packetPass1068 route1068 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_265 (c : Fin 32) (hr : BaseRetained 265 c.val true) :
    (265,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 265 true 0 packetData1069 (candidatePairList true)
    packetPass1069 route1069 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_266 (c : Fin 32) (hr : BaseRetained 266 c.val true) :
    (266,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 266 true 0 packetData1070 (candidatePairList true)
    packetPass1070 route1070 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_267 (c : Fin 32) (hr : BaseRetained 267 c.val true) :
    (267,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 267 true 0 packetData1071 (candidatePairList true)
    packetPass1071 route1071 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_268 (c : Fin 32) (hr : BaseRetained 268 c.val true) :
    (268,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 268 true 0 packetData1072 (candidatePairList true)
    packetPass1072 route1072 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_269 (c : Fin 32) (hr : BaseRetained 269 c.val true) :
    (269,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 269 true 0 packetData1073 (candidatePairList true)
    packetPass1073 route1073 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_270 (c : Fin 32) (hr : BaseRetained 270 c.val true) :
    (270,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 270 true 0 packetData1074 (candidatePairList true)
    packetPass1074 route1074 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_271 (c : Fin 32) (hr : BaseRetained 271 c.val true) :
    (271,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 271 true 0 packetData1075 (candidatePairList true)
    packetPass1075 route1075 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_272 (c : Fin 32) (hr : BaseRetained 272 c.val true) :
    (272,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 272 true 0 packetData1076 (candidatePairList true)
    packetPass1076 route1076 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_273 (c : Fin 32) (hr : BaseRetained 273 c.val true) :
    (273,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 273 true 0 packetData1077 (candidatePairList true)
    packetPass1077 route1077 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_274 (c : Fin 32) (hr : BaseRetained 274 c.val true) :
    (274,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 274 true 0 packetData1078 (candidatePairList true)
    packetPass1078 route1078 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_275 (c : Fin 32) (hr : BaseRetained 275 c.val true) :
    (275,c.val) ∈ candidatePairList true := by
  have h := packet_retained_route 275 true 0 packetData1079 (candidatePairList true)
    packetPass1079 route1079 c.val c.isLt (by simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [Nat.zero_add, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_276 (c : Fin 512) (hr : BaseRetained 276 c.val true) :
    (276,c.val) ∈ candidatePairList true := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 276 (p.val*64) (packets_1_276 p) (candidatePairList true) = true := by
    intro p
    fin_cases p
    · exact route1080
    · exact route1081
    · exact route1082
    · exact route1083
    · exact route1084
    · exact route1085
    · exact route1086
    · exact route1087
  have hi : c.val%64 < (packets_1_276 p).size := by rw [packets_size_1_276]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 276 true (p.val*64) (packets_1_276 p) (candidatePairList true)
    (packets_pass_1_276 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_277 (c : Fin 512) (hr : BaseRetained 277 c.val true) :
    (277,c.val) ∈ candidatePairList true := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 277 (p.val*64) (packets_1_277 p) (candidatePairList true) = true := by
    intro p
    fin_cases p
    · exact route1088
    · exact route1089
    · exact route1090
    · exact route1091
    · exact route1092
    · exact route1093
    · exact route1094
    · exact route1095
  have hi : c.val%64 < (packets_1_277 p).size := by rw [packets_size_1_277]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 277 true (p.val*64) (packets_1_277 p) (candidatePairList true)
    (packets_pass_1_277 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_278 (c : Fin 512) (hr : BaseRetained 278 c.val true) :
    (278,c.val) ∈ candidatePairList true := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 278 (p.val*64) (packets_1_278 p) (candidatePairList true) = true := by
    intro p
    fin_cases p
    · exact route1096
    · exact route1097
    · exact route1098
    · exact route1099
    · exact route1100
    · exact route1101
    · exact route1102
    · exact route1103
  have hi : c.val%64 < (packets_1_278 p).size := by rw [packets_size_1_278]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 278 true (p.val*64) (packets_1_278 p) (candidatePairList true)
    (packets_pass_1_278 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_279 (c : Fin 512) (hr : BaseRetained 279 c.val true) :
    (279,c.val) ∈ candidatePairList true := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 279 (p.val*64) (packets_1_279 p) (candidatePairList true) = true := by
    intro p
    fin_cases p
    · exact route1104
    · exact route1105
    · exact route1106
    · exact route1107
    · exact route1108
    · exact route1109
    · exact route1110
    · exact route1111
  have hi : c.val%64 < (packets_1_279 p).size := by rw [packets_size_1_279]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 279 true (p.val*64) (packets_1_279 p) (candidatePairList true)
    (packets_pass_1_279 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_280 (c : Fin 512) (hr : BaseRetained 280 c.val true) :
    (280,c.val) ∈ candidatePairList true := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 280 (p.val*64) (packets_1_280 p) (candidatePairList true) = true := by
    intro p
    fin_cases p
    · exact route1112
    · exact route0023
    · exact route1113
    · exact route1114
    · exact route1115
    · exact route1116
    · exact route1117
    · exact route1118
  have hi : c.val%64 < (packets_1_280 p).size := by rw [packets_size_1_280]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 280 true (p.val*64) (packets_1_280 p) (candidatePairList true)
    (packets_pass_1_280 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_281 (c : Fin 512) (hr : BaseRetained 281 c.val true) :
    (281,c.val) ∈ candidatePairList true := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 281 (p.val*64) (packets_1_281 p) (candidatePairList true) = true := by
    intro p
    fin_cases p
    · exact route1119
    · exact route1120
    · exact route1121
    · exact route1122
    · exact route1123
    · exact route1124
    · exact route1125
    · exact route1126
  have hi : c.val%64 < (packets_1_281 p).size := by rw [packets_size_1_281]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 281 true (p.val*64) (packets_1_281 p) (candidatePairList true)
    (packets_pass_1_281 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_282 (c : Fin 512) (hr : BaseRetained 282 c.val true) :
    (282,c.val) ∈ candidatePairList true := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 282 (p.val*64) (packets_1_282 p) (candidatePairList true) = true := by
    intro p
    fin_cases p
    · exact route1127
    · exact route1128
    · exact route1129
    · exact route1130
    · exact route1131
    · exact route1132
    · exact route1133
    · exact route1134
  have hi : c.val%64 < (packets_1_282 p).size := by rw [packets_size_1_282]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 282 true (p.val*64) (packets_1_282 p) (candidatePairList true)
    (packets_pass_1_282 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_283 (c : Fin 512) (hr : BaseRetained 283 c.val true) :
    (283,c.val) ∈ candidatePairList true := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 283 (p.val*64) (packets_1_283 p) (candidatePairList true) = true := by
    intro p
    fin_cases p
    · exact route1135
    · exact route1136
    · exact route1137
    · exact route1138
    · exact route1139
    · exact route1140
    · exact route1141
    · exact route1142
  have hi : c.val%64 < (packets_1_283 p).size := by rw [packets_size_1_283]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 283 true (p.val*64) (packets_1_283 p) (candidatePairList true)
    (packets_pass_1_283 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_284 (c : Fin 512) (hr : BaseRetained 284 c.val true) :
    (284,c.val) ∈ candidatePairList true := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 284 (p.val*64) (packets_1_284 p) (candidatePairList true) = true := by
    intro p
    fin_cases p
    · exact route1143
    · exact route0024
    · exact route1144
    · exact route1145
    · exact route1146
    · exact route1147
    · exact route1148
    · exact route1149
  have hi : c.val%64 < (packets_1_284 p).size := by rw [packets_size_1_284]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 284 true (p.val*64) (packets_1_284 p) (candidatePairList true)
    (packets_pass_1_284 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_285 (c : Fin 512) (hr : BaseRetained 285 c.val true) :
    (285,c.val) ∈ candidatePairList true := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 285 (p.val*64) (packets_1_285 p) (candidatePairList true) = true := by
    intro p
    fin_cases p
    · exact route1150
    · exact route1151
    · exact route1152
    · exact route1153
    · exact route1154
    · exact route1155
    · exact route1156
    · exact route1157
  have hi : c.val%64 < (packets_1_285 p).size := by rw [packets_size_1_285]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 285 true (p.val*64) (packets_1_285 p) (candidatePairList true)
    (packets_pass_1_285 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_286 (c : Fin 512) (hr : BaseRetained 286 c.val true) :
    (286,c.val) ∈ candidatePairList true := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 286 (p.val*64) (packets_1_286 p) (candidatePairList true) = true := by
    intro p
    fin_cases p
    · exact route1158
    · exact route1159
    · exact route1160
    · exact route1161
    · exact route0025
    · exact route1162
    · exact route1163
    · exact route1164
  have hi : c.val%64 < (packets_1_286 p).size := by rw [packets_size_1_286]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 286 true (p.val*64) (packets_1_286 p) (candidatePairList true)
    (packets_pass_1_286 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_287 (c : Fin 512) (hr : BaseRetained 287 c.val true) :
    (287,c.val) ∈ candidatePairList true := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 287 (p.val*64) (packets_1_287 p) (candidatePairList true) = true := by
    intro p
    fin_cases p
    · exact route1165
    · exact route1166
    · exact route1167
    · exact route1168
    · exact route1169
    · exact route1170
    · exact route1171
    · exact route1172
  have hi : c.val%64 < (packets_1_287 p).size := by rw [packets_size_1_287]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 287 true (p.val*64) (packets_1_287 p) (candidatePairList true)
    (packets_pass_1_287 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_288 (c : Fin 512) (hr : BaseRetained 288 c.val true) :
    (288,c.val) ∈ candidatePairList true := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 288 (p.val*64) (packets_1_288 p) (candidatePairList true) = true := by
    intro p
    fin_cases p
    · exact route1173
    · exact route1174
    · exact route1175
    · exact route1176
    · exact route1177
    · exact route1178
    · exact route1179
    · exact route1180
  have hi : c.val%64 < (packets_1_288 p).size := by rw [packets_size_1_288]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 288 true (p.val*64) (packets_1_288 p) (candidatePairList true)
    (packets_pass_1_288 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_289 (c : Fin 512) (hr : BaseRetained 289 c.val true) :
    (289,c.val) ∈ candidatePairList true := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 289 (p.val*64) (packets_1_289 p) (candidatePairList true) = true := by
    intro p
    fin_cases p
    · exact route1181
    · exact route1182
    · exact route1183
    · exact route1184
    · exact route1185
    · exact route1186
    · exact route1187
    · exact route1188
  have hi : c.val%64 < (packets_1_289 p).size := by rw [packets_size_1_289]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 289 true (p.val*64) (packets_1_289 p) (candidatePairList true)
    (packets_pass_1_289 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_290 (c : Fin 512) (hr : BaseRetained 290 c.val true) :
    (290,c.val) ∈ candidatePairList true := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 290 (p.val*64) (packets_1_290 p) (candidatePairList true) = true := by
    intro p
    fin_cases p
    · exact route1189
    · exact route1190
    · exact route1191
    · exact route1192
    · exact route1193
    · exact route1194
    · exact route1195
    · exact route1196
  have hi : c.val%64 < (packets_1_290 p).size := by rw [packets_size_1_290]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 290 true (p.val*64) (packets_1_290 p) (candidatePairList true)
    (packets_pass_1_290 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_291 (c : Fin 512) (hr : BaseRetained 291 c.val true) :
    (291,c.val) ∈ candidatePairList true := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 291 (p.val*64) (packets_1_291 p) (candidatePairList true) = true := by
    intro p
    fin_cases p
    · exact route1197
    · exact route1198
    · exact route1199
    · exact route1200
    · exact route1201
    · exact route1202
    · exact route1203
    · exact route1204
  have hi : c.val%64 < (packets_1_291 p).size := by rw [packets_size_1_291]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 291 true (p.val*64) (packets_1_291 p) (candidatePairList true)
    (packets_pass_1_291 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_292 (c : Fin 512) (hr : BaseRetained 292 c.val true) :
    (292,c.val) ∈ candidatePairList true := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 292 (p.val*64) (packets_1_292 p) (candidatePairList true) = true := by
    intro p
    fin_cases p
    · exact route1205
    · exact route0026
    · exact route1206
    · exact route1207
    · exact route1208
    · exact route1209
    · exact route1210
    · exact route1211
  have hi : c.val%64 < (packets_1_292 p).size := by rw [packets_size_1_292]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 292 true (p.val*64) (packets_1_292 p) (candidatePairList true)
    (packets_pass_1_292 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_293 (c : Fin 512) (hr : BaseRetained 293 c.val true) :
    (293,c.val) ∈ candidatePairList true := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 293 (p.val*64) (packets_1_293 p) (candidatePairList true) = true := by
    intro p
    fin_cases p
    · exact route1212
    · exact route1213
    · exact route1214
    · exact route1215
    · exact route1216
    · exact route1217
    · exact route1218
    · exact route1219
  have hi : c.val%64 < (packets_1_293 p).size := by rw [packets_size_1_293]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 293 true (p.val*64) (packets_1_293 p) (candidatePairList true)
    (packets_pass_1_293 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_294 (c : Fin 512) (hr : BaseRetained 294 c.val true) :
    (294,c.val) ∈ candidatePairList true := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 294 (p.val*64) (packets_1_294 p) (candidatePairList true) = true := by
    intro p
    fin_cases p
    · exact route1220
    · exact route1221
    · exact route1222
    · exact route1223
    · exact route0027
    · exact route1224
    · exact route1225
    · exact route1226
  have hi : c.val%64 < (packets_1_294 p).size := by rw [packets_size_1_294]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 294 true (p.val*64) (packets_1_294 p) (candidatePairList true)
    (packets_pass_1_294 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_295 (c : Fin 512) (hr : BaseRetained 295 c.val true) :
    (295,c.val) ∈ candidatePairList true := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 295 (p.val*64) (packets_1_295 p) (candidatePairList true) = true := by
    intro p
    fin_cases p
    · exact route1227
    · exact route1228
    · exact route1229
    · exact route1230
    · exact route1231
    · exact route1232
    · exact route1233
    · exact route1234
  have hi : c.val%64 < (packets_1_295 p).size := by rw [packets_size_1_295]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 295 true (p.val*64) (packets_1_295 p) (candidatePairList true)
    (packets_pass_1_295 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_296 (c : Fin 512) (hr : BaseRetained 296 c.val true) :
    (296,c.val) ∈ candidatePairList true := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 296 (p.val*64) (packets_1_296 p) (candidatePairList true) = true := by
    intro p
    fin_cases p
    · exact route1235
    · exact route1236
    · exact route1237
    · exact route1238
    · exact route1239
    · exact route1240
    · exact route1241
    · exact route1242
  have hi : c.val%64 < (packets_1_296 p).size := by rw [packets_size_1_296]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 296 true (p.val*64) (packets_1_296 p) (candidatePairList true)
    (packets_pass_1_296 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_297 (c : Fin 512) (hr : BaseRetained 297 c.val true) :
    (297,c.val) ∈ candidatePairList true := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 297 (p.val*64) (packets_1_297 p) (candidatePairList true) = true := by
    intro p
    fin_cases p
    · exact route1243
    · exact route1244
    · exact route1245
    · exact route1246
    · exact route1247
    · exact route1248
    · exact route1249
    · exact route1250
  have hi : c.val%64 < (packets_1_297 p).size := by rw [packets_size_1_297]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 297 true (p.val*64) (packets_1_297 p) (candidatePairList true)
    (packets_pass_1_297 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_298 (c : Fin 512) (hr : BaseRetained 298 c.val true) :
    (298,c.val) ∈ candidatePairList true := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 298 (p.val*64) (packets_1_298 p) (candidatePairList true) = true := by
    intro p
    fin_cases p
    · exact route1251
    · exact route1252
    · exact route1253
    · exact route1254
    · exact route1255
    · exact route0028
    · exact route1256
    · exact route1257
  have hi : c.val%64 < (packets_1_298 p).size := by rw [packets_size_1_298]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 298 true (p.val*64) (packets_1_298 p) (candidatePairList true)
    (packets_pass_1_298 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_299 (c : Fin 512) (hr : BaseRetained 299 c.val true) :
    (299,c.val) ∈ candidatePairList true := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 299 (p.val*64) (packets_1_299 p) (candidatePairList true) = true := by
    intro p
    fin_cases p
    · exact route1258
    · exact route1259
    · exact route1260
    · exact route1261
    · exact route1262
    · exact route1263
    · exact route1264
    · exact route1265
  have hi : c.val%64 < (packets_1_299 p).size := by rw [packets_size_1_299]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 299 true (p.val*64) (packets_1_299 p) (candidatePairList true)
    (packets_pass_1_299 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_300 (c : Fin 512) (hr : BaseRetained 300 c.val true) :
    (300,c.val) ∈ candidatePairList true := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 300 (p.val*64) (packets_1_300 p) (candidatePairList true) = true := by
    intro p
    fin_cases p
    · exact route1266
    · exact route1267
    · exact route1268
    · exact route1269
    · exact route1270
    · exact route1271
    · exact route1272
    · exact route1273
  have hi : c.val%64 < (packets_1_300 p).size := by rw [packets_size_1_300]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 300 true (p.val*64) (packets_1_300 p) (candidatePairList true)
    (packets_pass_1_300 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_301 (c : Fin 512) (hr : BaseRetained 301 c.val true) :
    (301,c.val) ∈ candidatePairList true := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 301 (p.val*64) (packets_1_301 p) (candidatePairList true) = true := by
    intro p
    fin_cases p
    · exact route1274
    · exact route1275
    · exact route1276
    · exact route1277
    · exact route1278
    · exact route1279
    · exact route1280
    · exact route1281
  have hi : c.val%64 < (packets_1_301 p).size := by rw [packets_size_1_301]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 301 true (p.val*64) (packets_1_301 p) (candidatePairList true)
    (packets_pass_1_301 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_302 (c : Fin 512) (hr : BaseRetained 302 c.val true) :
    (302,c.val) ∈ candidatePairList true := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 302 (p.val*64) (packets_1_302 p) (candidatePairList true) = true := by
    intro p
    fin_cases p
    · exact route1282
    · exact route1283
    · exact route1284
    · exact route1285
    · exact route1286
    · exact route1287
    · exact route1288
    · exact route1289
  have hi : c.val%64 < (packets_1_302 p).size := by rw [packets_size_1_302]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 302 true (p.val*64) (packets_1_302 p) (candidatePairList true)
    (packets_pass_1_302 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_303 (c : Fin 512) (hr : BaseRetained 303 c.val true) :
    (303,c.val) ∈ candidatePairList true := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 303 (p.val*64) (packets_1_303 p) (candidatePairList true) = true := by
    intro p
    fin_cases p
    · exact route1290
    · exact route1291
    · exact route1292
    · exact route1293
    · exact route1294
    · exact route1295
    · exact route1296
    · exact route1297
  have hi : c.val%64 < (packets_1_303 p).size := by rw [packets_size_1_303]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 303 true (p.val*64) (packets_1_303 p) (candidatePairList true)
    (packets_pass_1_303 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_304 (c : Fin 512) (hr : BaseRetained 304 c.val true) :
    (304,c.val) ∈ candidatePairList true := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 304 (p.val*64) (packets_1_304 p) (candidatePairList true) = true := by
    intro p
    fin_cases p
    · exact route0029
    · exact route0030
    · exact route0031
    · exact route0032
    · exact route0033
    · exact route1298
    · exact route0034
    · exact route1299
  have hi : c.val%64 < (packets_1_304 p).size := by rw [packets_size_1_304]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 304 true (p.val*64) (packets_1_304 p) (candidatePairList true)
    (packets_pass_1_304 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_305 (c : Fin 512) (hr : BaseRetained 305 c.val true) :
    (305,c.val) ∈ candidatePairList true := by
  let p : Fin 8 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 8, packetRouteCheck 305 (p.val*64) (packets_1_305 p) (candidatePairList true) = true := by
    intro p
    fin_cases p
    · exact route0035
    · exact route1300
    · exact route1301
    · exact route1302
    · exact route1303
    · exact route1304
    · exact route1305
    · exact route1306
  have hi : c.val%64 < (packets_1_305 p).size := by rw [packets_size_1_305]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 305 true (p.val*64) (packets_1_305 p) (candidatePairList true)
    (packets_pass_1_305 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_306 (c : Fin 16384) (hr : BaseRetained 306 c.val true) :
    (306,c.val) ∈ candidatePairList true := by
  let p : Fin 256 := ⟨c.val/64,by have h := c.isLt; omega⟩
  have hroute : ∀p : Fin 256, packetRouteCheck 306 (p.val*64) (packets_1_306 p) (candidatePairList true) = true := by
    intro p
    fin_cases p
    · exact route1307
    · exact route1308
    · exact route1309
    · exact route1310
    · exact route1311
    · exact route1312
    · exact route1313
    · exact route1314
    · exact route1315
    · exact route1316
    · exact route1317
    · exact route1318
    · exact route1319
    · exact route1320
    · exact route1321
    · exact route1322
    · exact route1323
    · exact route1324
    · exact route1325
    · exact route1326
    · exact route1327
    · exact route1328
    · exact route1329
    · exact route1330
    · exact route1331
    · exact route1332
    · exact route1333
    · exact route1334
    · exact route1335
    · exact route1336
    · exact route1337
    · exact route1338
    · exact route1339
    · exact route1340
    · exact route1341
    · exact route1342
    · exact route1343
    · exact route1344
    · exact route1345
    · exact route1346
    · exact route1347
    · exact route1348
    · exact route0036
    · exact route1349
    · exact route1350
    · exact route1351
    · exact route1352
    · exact route1353
    · exact route1354
    · exact route1355
    · exact route1356
    · exact route1357
    · exact route1358
    · exact route1359
    · exact route1360
    · exact route1361
    · exact route1362
    · exact route1363
    · exact route1364
    · exact route1365
    · exact route1366
    · exact route1367
    · exact route1368
    · exact route1369
    · exact route1370
    · exact route1371
    · exact route1372
    · exact route1373
    · exact route1374
    · exact route1375
    · exact route1376
    · exact route1377
    · exact route1378
    · exact route1379
    · exact route1380
    · exact route1381
    · exact route1382
    · exact route1383
    · exact route1384
    · exact route1385
    · exact route1386
    · exact route1387
    · exact route1388
    · exact route1389
    · exact route1390
    · exact route0037
    · exact route1391
    · exact route1392
    · exact route1393
    · exact route1394
    · exact route1395
    · exact route1396
    · exact route1397
    · exact route1398
    · exact route1399
    · exact route1400
    · exact route1401
    · exact route1402
    · exact route1403
    · exact route1404
    · exact route1405
    · exact route1406
    · exact route1407
    · exact route1408
    · exact route1409
    · exact route1410
    · exact route1411
    · exact route0038
    · exact route1412
    · exact route1413
    · exact route0039
    · exact route1414
    · exact route1415
    · exact route1416
    · exact route1417
    · exact route1418
    · exact route1419
    · exact route1420
    · exact route1421
    · exact route1422
    · exact route1423
    · exact route1424
    · exact route0040
    · exact route1425
    · exact route1426
    · exact route1427
    · exact route1428
    · exact route1429
    · exact route1430
    · exact route1431
    · exact route1432
    · exact route1433
    · exact route1434
    · exact route1435
    · exact route1436
    · exact route1437
    · exact route1438
    · exact route1439
    · exact route0041
    · exact route1440
    · exact route1441
    · exact route1442
    · exact route1443
    · exact route1444
    · exact route1445
    · exact route1446
    · exact route1447
    · exact route1448
    · exact route1449
    · exact route1450
    · exact route1451
    · exact route1452
    · exact route1453
    · exact route1454
    · exact route1455
    · exact route0042
    · exact route1456
    · exact route1457
    · exact route0043
    · exact route1458
    · exact route1459
    · exact route1460
    · exact route0044
    · exact route1461
    · exact route1462
    · exact route1463
    · exact route1464
    · exact route0045
    · exact route0046
    · exact route1465
    · exact route0047
    · exact route1466
    · exact route1467
    · exact route0048
    · exact route1468
    · exact route1469
    · exact route1470
    · exact route1471
    · exact route1472
    · exact route1473
    · exact route1474
    · exact route1475
    · exact route0049
    · exact route1476
    · exact route1477
    · exact route0050
    · exact route1478
    · exact route1479
    · exact route1480
    · exact route1481
    · exact route1482
    · exact route1483
    · exact route1484
    · exact route1485
    · exact route1486
    · exact route1487
    · exact route1488
    · exact route1489
    · exact route1490
    · exact route1491
    · exact route1492
    · exact route1493
    · exact route1494
    · exact route1495
    · exact route1496
    · exact route1497
    · exact route1498
    · exact route1499
    · exact route1500
    · exact route1501
    · exact route1502
    · exact route1503
    · exact route1504
    · exact route1505
    · exact route1506
    · exact route1507
    · exact route1508
    · exact route1509
    · exact route0051
    · exact route1510
    · exact route1511
    · exact route1512
    · exact route1513
    · exact route1514
    · exact route1515
    · exact route1516
    · exact route1517
    · exact route1518
    · exact route1519
    · exact route1520
    · exact route0052
    · exact route1521
    · exact route1522
    · exact route0053
    · exact route1523
    · exact route1524
    · exact route1525
    · exact route1526
    · exact route1527
    · exact route1528
    · exact route1529
    · exact route1530
    · exact route1531
    · exact route1532
    · exact route1533
    · exact route1534
    · exact route1535
    · exact route1536
    · exact route1537
    · exact route1538
    · exact route1539
    · exact route1540
    · exact route1541
    · exact route1542
    · exact route1543
    · exact route0054
  have hi : c.val%64 < (packets_1_306 p).size := by rw [packets_size_1_306]; omega
  have he : p.val*64+c.val%64=c.val := by dsimp [p]; omega
  have h := packet_retained_route 306 true (p.val*64) (packets_1_306 p) (candidatePairList true)
    (packets_pass_1_306 p) (hroute p) (c.val%64) hi (by simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using hr)
  simpa only [he, Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

 theorem retained_true_complete (c : InputCode) (hr : BaseRetained c.1 c.2.val true) :
    (c.1.val,c.2.val) ∈ candidatePairList true := by
  rcases c with ⟨s,c⟩
  fin_cases s
  · exact retained_true_000 c hr
  · exact retained_true_001 c hr
  · exact retained_true_002 c hr
  · exact retained_true_003 c hr
  · exact retained_true_004 c hr
  · exact retained_true_005 c hr
  · exact retained_true_006 c hr
  · exact retained_true_007 c hr
  · exact retained_true_008 c hr
  · exact retained_true_009 c hr
  · exact retained_true_010 c hr
  · exact retained_true_011 c hr
  · exact retained_true_012 c hr
  · exact retained_true_013 c hr
  · exact retained_true_014 c hr
  · exact retained_true_015 c hr
  · exact retained_true_016 c hr
  · exact retained_true_017 c hr
  · exact retained_true_018 c hr
  · exact retained_true_019 c hr
  · exact retained_true_020 c hr
  · exact retained_true_021 c hr
  · exact retained_true_022 c hr
  · exact retained_true_023 c hr
  · exact retained_true_024 c hr
  · exact retained_true_025 c hr
  · exact retained_true_026 c hr
  · exact retained_true_027 c hr
  · exact retained_true_028 c hr
  · exact retained_true_029 c hr
  · exact retained_true_030 c hr
  · exact retained_true_031 c hr
  · exact retained_true_032 c hr
  · exact retained_true_033 c hr
  · exact retained_true_034 c hr
  · exact retained_true_035 c hr
  · exact retained_true_036 c hr
  · exact retained_true_037 c hr
  · exact retained_true_038 c hr
  · exact retained_true_039 c hr
  · exact retained_true_040 c hr
  · exact retained_true_041 c hr
  · exact retained_true_042 c hr
  · exact retained_true_043 c hr
  · exact retained_true_044 c hr
  · exact retained_true_045 c hr
  · exact retained_true_046 c hr
  · exact retained_true_047 c hr
  · exact retained_true_048 c hr
  · exact retained_true_049 c hr
  · exact retained_true_050 c hr
  · exact retained_true_051 c hr
  · exact retained_true_052 c hr
  · exact retained_true_053 c hr
  · exact retained_true_054 c hr
  · exact retained_true_055 c hr
  · exact retained_true_056 c hr
  · exact retained_true_057 c hr
  · exact retained_true_058 c hr
  · exact retained_true_059 c hr
  · exact retained_true_060 c hr
  · exact retained_true_061 c hr
  · exact retained_true_062 c hr
  · exact retained_true_063 c hr
  · exact retained_true_064 c hr
  · exact retained_true_065 c hr
  · exact retained_true_066 c hr
  · exact retained_true_067 c hr
  · exact retained_true_068 c hr
  · exact retained_true_069 c hr
  · exact retained_true_070 c hr
  · exact retained_true_071 c hr
  · exact retained_true_072 c hr
  · exact retained_true_073 c hr
  · exact retained_true_074 c hr
  · exact retained_true_075 c hr
  · exact retained_true_076 c hr
  · exact retained_true_077 c hr
  · exact retained_true_078 c hr
  · exact retained_true_079 c hr
  · exact retained_true_080 c hr
  · exact retained_true_081 c hr
  · exact retained_true_082 c hr
  · exact retained_true_083 c hr
  · exact retained_true_084 c hr
  · exact retained_true_085 c hr
  · exact retained_true_086 c hr
  · exact retained_true_087 c hr
  · exact retained_true_088 c hr
  · exact retained_true_089 c hr
  · exact retained_true_090 c hr
  · exact retained_true_091 c hr
  · exact retained_true_092 c hr
  · exact retained_true_093 c hr
  · exact retained_true_094 c hr
  · exact retained_true_095 c hr
  · exact retained_true_096 c hr
  · exact retained_true_097 c hr
  · exact retained_true_098 c hr
  · exact retained_true_099 c hr
  · exact retained_true_100 c hr
  · exact retained_true_101 c hr
  · exact retained_true_102 c hr
  · exact retained_true_103 c hr
  · exact retained_true_104 c hr
  · exact retained_true_105 c hr
  · exact retained_true_106 c hr
  · exact retained_true_107 c hr
  · exact retained_true_108 c hr
  · exact retained_true_109 c hr
  · exact retained_true_110 c hr
  · exact retained_true_111 c hr
  · exact retained_true_112 c hr
  · exact retained_true_113 c hr
  · exact retained_true_114 c hr
  · exact retained_true_115 c hr
  · exact retained_true_116 c hr
  · exact retained_true_117 c hr
  · exact retained_true_118 c hr
  · exact retained_true_119 c hr
  · exact retained_true_120 c hr
  · exact retained_true_121 c hr
  · exact retained_true_122 c hr
  · exact retained_true_123 c hr
  · exact retained_true_124 c hr
  · exact retained_true_125 c hr
  · exact retained_true_126 c hr
  · exact retained_true_127 c hr
  · exact retained_true_128 c hr
  · exact retained_true_129 c hr
  · exact retained_true_130 c hr
  · exact retained_true_131 c hr
  · exact retained_true_132 c hr
  · exact retained_true_133 c hr
  · exact retained_true_134 c hr
  · exact retained_true_135 c hr
  · exact retained_true_136 c hr
  · exact retained_true_137 c hr
  · exact retained_true_138 c hr
  · exact retained_true_139 c hr
  · exact retained_true_140 c hr
  · exact retained_true_141 c hr
  · exact retained_true_142 c hr
  · exact retained_true_143 c hr
  · exact retained_true_144 c hr
  · exact retained_true_145 c hr
  · exact retained_true_146 c hr
  · exact retained_true_147 c hr
  · exact retained_true_148 c hr
  · exact retained_true_149 c hr
  · exact retained_true_150 c hr
  · exact retained_true_151 c hr
  · exact retained_true_152 c hr
  · exact retained_true_153 c hr
  · exact retained_true_154 c hr
  · exact retained_true_155 c hr
  · exact retained_true_156 c hr
  · exact retained_true_157 c hr
  · exact retained_true_158 c hr
  · exact retained_true_159 c hr
  · exact retained_true_160 c hr
  · exact retained_true_161 c hr
  · exact retained_true_162 c hr
  · exact retained_true_163 c hr
  · exact retained_true_164 c hr
  · exact retained_true_165 c hr
  · exact retained_true_166 c hr
  · exact retained_true_167 c hr
  · exact retained_true_168 c hr
  · exact retained_true_169 c hr
  · exact retained_true_170 c hr
  · exact retained_true_171 c hr
  · exact retained_true_172 c hr
  · exact retained_true_173 c hr
  · exact retained_true_174 c hr
  · exact retained_true_175 c hr
  · exact retained_true_176 c hr
  · exact retained_true_177 c hr
  · exact retained_true_178 c hr
  · exact retained_true_179 c hr
  · exact retained_true_180 c hr
  · exact retained_true_181 c hr
  · exact retained_true_182 c hr
  · exact retained_true_183 c hr
  · exact retained_true_184 c hr
  · exact retained_true_185 c hr
  · exact retained_true_186 c hr
  · exact retained_true_187 c hr
  · exact retained_true_188 c hr
  · exact retained_true_189 c hr
  · exact retained_true_190 c hr
  · exact retained_true_191 c hr
  · exact retained_true_192 c hr
  · exact retained_true_193 c hr
  · exact retained_true_194 c hr
  · exact retained_true_195 c hr
  · exact retained_true_196 c hr
  · exact retained_true_197 c hr
  · exact retained_true_198 c hr
  · exact retained_true_199 c hr
  · exact retained_true_200 c hr
  · exact retained_true_201 c hr
  · exact retained_true_202 c hr
  · exact retained_true_203 c hr
  · exact retained_true_204 c hr
  · exact retained_true_205 c hr
  · exact retained_true_206 c hr
  · exact retained_true_207 c hr
  · exact retained_true_208 c hr
  · exact retained_true_209 c hr
  · exact retained_true_210 c hr
  · exact retained_true_211 c hr
  · exact retained_true_212 c hr
  · exact retained_true_213 c hr
  · exact retained_true_214 c hr
  · exact retained_true_215 c hr
  · exact retained_true_216 c hr
  · exact retained_true_217 c hr
  · exact retained_true_218 c hr
  · exact retained_true_219 c hr
  · exact retained_true_220 c hr
  · exact retained_true_221 c hr
  · exact retained_true_222 c hr
  · exact retained_true_223 c hr
  · exact retained_true_224 c hr
  · exact retained_true_225 c hr
  · exact retained_true_226 c hr
  · exact retained_true_227 c hr
  · exact retained_true_228 c hr
  · exact retained_true_229 c hr
  · exact retained_true_230 c hr
  · exact retained_true_231 c hr
  · exact retained_true_232 c hr
  · exact retained_true_233 c hr
  · exact retained_true_234 c hr
  · exact retained_true_235 c hr
  · exact retained_true_236 c hr
  · exact retained_true_237 c hr
  · exact retained_true_238 c hr
  · exact retained_true_239 c hr
  · exact retained_true_240 c hr
  · exact retained_true_241 c hr
  · exact retained_true_242 c hr
  · exact retained_true_243 c hr
  · exact retained_true_244 c hr
  · exact retained_true_245 c hr
  · exact retained_true_246 c hr
  · exact retained_true_247 c hr
  · exact retained_true_248 c hr
  · exact retained_true_249 c hr
  · exact retained_true_250 c hr
  · exact retained_true_251 c hr
  · exact retained_true_252 c hr
  · exact retained_true_253 c hr
  · exact retained_true_254 c hr
  · exact retained_true_255 c hr
  · exact retained_true_256 c hr
  · exact retained_true_257 c hr
  · exact retained_true_258 c hr
  · exact retained_true_259 c hr
  · exact retained_true_260 c hr
  · exact retained_true_261 c hr
  · exact retained_true_262 c hr
  · exact retained_true_263 c hr
  · exact retained_true_264 c hr
  · exact retained_true_265 c hr
  · exact retained_true_266 c hr
  · exact retained_true_267 c hr
  · exact retained_true_268 c hr
  · exact retained_true_269 c hr
  · exact retained_true_270 c hr
  · exact retained_true_271 c hr
  · exact retained_true_272 c hr
  · exact retained_true_273 c hr
  · exact retained_true_274 c hr
  · exact retained_true_275 c hr
  · exact retained_true_276 c hr
  · exact retained_true_277 c hr
  · exact retained_true_278 c hr
  · exact retained_true_279 c hr
  · exact retained_true_280 c hr
  · exact retained_true_281 c hr
  · exact retained_true_282 c hr
  · exact retained_true_283 c hr
  · exact retained_true_284 c hr
  · exact retained_true_285 c hr
  · exact retained_true_286 c hr
  · exact retained_true_287 c hr
  · exact retained_true_288 c hr
  · exact retained_true_289 c hr
  · exact retained_true_290 c hr
  · exact retained_true_291 c hr
  · exact retained_true_292 c hr
  · exact retained_true_293 c hr
  · exact retained_true_294 c hr
  · exact retained_true_295 c hr
  · exact retained_true_296 c hr
  · exact retained_true_297 c hr
  · exact retained_true_298 c hr
  · exact retained_true_299 c hr
  · exact retained_true_300 c hr
  · exact retained_true_301 c hr
  · exact retained_true_302 c hr
  · exact retained_true_303 c hr
  · exact retained_true_304 c hr
  · exact retained_true_305 c hr
  · exact retained_true_306 c hr

end Holant.Certificates.AffineEndpointCounts
