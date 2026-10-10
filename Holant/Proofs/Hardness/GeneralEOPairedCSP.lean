import Holant.Proofs.Hardness.GeneralEOPairedCSPCycles
import Holant.Proofs.Hardness.GeneralEOPairedCSPScan
import Holant.Proofs.Hardness.GeneralEONegativeClosedSupport

/-! Exact arbitrary-arity ordinary CSP compilation into original-signature EO
networks under a derived or supplied whole-support covering pairing. Isolated
variables contribute exactly 2^unused; no surjectivity, positive-arity, or
nonempty-instance premise is imposed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSP
open Holant Holant.Tractable
open scoped BigOperators
namespace C
export GeneralEOPairedCSPCycles (Slot incidence Covers compress Consistent weight value network denote_original)
end C
namespace S
export GeneralEOPairedCSPScan (next constant_iff)
end S
namespace U
export GeneralCSPUnused (unusedCount ConsistentAssignment assignment_sum)
end U
set_option backward.isDefEq.respectTransparency false

variable {n N m : ℕ} (p : OrientedPerfectPairing n)

def value {K : Type*} [CommSemiring K] (g : Signature K p.count)
    (scope : C.Slot (N:=N) p→Fin m) : K :=
  ∑x : Fin m→Bool,∏v : Fin N,g (fun j=>x (scope (C.incidence p v j)))

theorem cycle_value {K : Type*} [CommSemiring K] (g : Signature K p.count)
    (scope : C.Slot (N:=N) p→Fin m) :
    value p g scope=(2:K)^U.unusedCount scope*C.value p g (S.next scope) := by
  classical
  have hc (a : C.Slot (N:=N) p→Bool) :
      GeneralCSPUnused.FiberConstant scope a ↔ C.Consistent p (S.next scope) a :=
    S.constant_iff scope a
  have hv : C.value p g (S.next scope)=
      ∑a : U.ConsistentAssignment scope,C.weight p g a.val := by
    unfold C.value
    simp only [←hc]
    rw [←Finset.sum_filter]
    exact Finset.sum_subtype (p:=GeneralCSPUnused.FiberConstant scope) _
      (by intro a; simp) (C.weight p g)
  rw [hv]
  exact U.assignment_sum scope (C.weight p g)

/-- A single actual original-f native-X query and a known power of two recover
 the ordinary CSP partition function, including all isolated variables. -/
theorem native_value {K : Type*} [CommSemiring K] (f : Signature K n)
    (hf : C.Covers p f) (scope : C.Slot (N:=N) p→Fin m) :
    value p (C.compress p f) scope=(2:K)^U.unusedCount scope*
      (C.network p f (S.next scope)).denote Fin.elim0 := by
  rw [C.denote_original p f hf]
  exact cycle_value p _ scope

/-- The exact scalar exponent has a total natural-list scan implementation. -/
theorem native_value_scan {K : Type*} [CommSemiring K] (f : Signature K n)
    (hf : C.Covers p f) (scope : C.Slot (N:=N) p→Fin m) :
    value p (C.compress p f) scope=
      (2:K)^(GeneralEOPairedCSPScan.NatScan.unused m
        (GeneralEOPairedCSPScan.NatScan.addresses scope)).length*
      (C.network p f (S.next scope)).denote Fin.elim0 := by
  rw [←GeneralEOPairedCSPScan.NatScan.unusedCount_filter]
  exact native_value p f hf scope

/-- Existing central/XOR closure machinery supplies the required covering
pairing internally, so this application carries no arbitrary-pair oracle. -/
theorem closed_support_value (f : Signature AlgebraicComplex n)
    (he : Signature.CentralSupport f) (hn : f≠0)
    (hc : GeneralEONegativeClosedSupport.Closed f)
    (scope : C.Slot (N:=N) (GeneralEONegativeClosedSupport.pairing f he hn hc)→Fin m) :
    value (GeneralEONegativeClosedSupport.pairing f he hn hc)
      ((GeneralEONegativeClosedSupport.pairing f he hn hc).restrict f) scope=
      (2:AlgebraicComplex)^U.unusedCount scope*
        (C.network (GeneralEONegativeClosedSupport.pairing f he hn hc) f
          (S.next scope)).denote Fin.elim0 := by
  apply native_value
  exact GeneralEONegativeClosedSupport.covers f he hn hc

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSP
