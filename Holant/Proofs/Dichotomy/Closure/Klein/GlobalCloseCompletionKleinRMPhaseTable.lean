import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinGramCertificate

/-! Exact finite phase obstruction on signed RM8 tables. The zero-word sign
is fixed to +1. Seven explicit two-copy Pauli wirings leave only the sixteen
linear characters; the contraction-to-table source bridge is separate. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinRMPhaseTable
open scoped BigOperators
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

def sign (m i : ℕ) : ℤ := if (2*m).testBit i then -1 else 1

def values (m : ℕ) (j : Fin 7) : Fin 4→ℤ :=
  ![![(sign m 0*sign m 0) + (sign m 3*sign m 9),(sign m 5*sign m 14) + (sign m 6*sign m 7),(sign m 9*sign m 8) + (sign m 10*sign m 1),(sign m 12*sign m 6) + (sign m 15*sign m 15)],
    ![(sign m 0*sign m 11) + -(sign m 8*sign m 3),-(sign m 6*sign m 15) + (sign m 14*sign m 7),-(sign m 1*sign m 8) + (sign m 9*sign m 0),(sign m 7*sign m 12) + -(sign m 15*sign m 4)],
    ![(sign m 2*sign m 3),(sign m 5*sign m 4),-(sign m 10*sign m 11),-(sign m 13*sign m 12)],
    ![(sign m 0*sign m 8) + (sign m 13*sign m 10),-(sign m 6*sign m 0) + -(sign m 11*sign m 2),(sign m 4*sign m 13) + (sign m 9*sign m 15),-(sign m 2*sign m 5) + -(sign m 15*sign m 7)],
    ![-(sign m 2*sign m 12),(sign m 3*sign m 14),-(sign m 12*sign m 1),(sign m 13*sign m 3)],
    ![(sign m 0*sign m 13) + -(sign m 13*sign m 1),-(sign m 12*sign m 8) + (sign m 1*sign m 4),(sign m 14*sign m 11) + -(sign m 3*sign m 7),-(sign m 2*sign m 14) + (sign m 15*sign m 2)],
    ![(sign m 14*sign m 7) + -(sign m 10*sign m 3),(sign m 7*sign m 2) + -(sign m 3*sign m 6),-(sign m 12*sign m 9) + (sign m 8*sign m 13),-(sign m 5*sign m 12) + (sign m 1*sign m 8)]] j

def positions (j : Fin 7) : Fin 4→Fin 16 :=
  ![![0,6,9,15],
    ![2,7,8,13],
    ![3,5,10,12],
    ![2,4,11,13],
    ![2,7,8,13],
    ![2,4,11,13],
    ![1,4,11,14]] j

def safe (m : ℕ) (j : Fin 7) : Prop :=
  (∀k,values m j k=0) ∨ (∏k,values m j k)=(if j=2 ∨ j=4 then 1 else 16)

def linearMask (m : ℕ) : Prop := m∈[0,2040,6630,7710,10965,11565,13107,13515,19275,19635,21165,21845,24990,26214,30840,32640]

def block (h : Fin 16) : Prop := ∀l : Fin 2048,
  linearMask (2048*h.val+l.val) ∨ ∃j : Fin 7,¬safe (2048*h.val+l.val) j

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinRMPhaseTable
