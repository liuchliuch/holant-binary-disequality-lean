import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeOneSidedSparse

/-! An actual infinite-order native antidiagonal closes every endpoint-live
q4 with at least one live middle coefficient. Exact native interpolation
installs a one-sided antidiagonal; no equality or phase vertex is assumed.
The subsequent factor/cap source retains the whole original dictionary. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeSparseInfinite
open Holant Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace S
export NativeAntiTargetSource (Output arity table old old_literal label literal source)
export PaperTerminalBridgeDenseSemantic (family output anti_eq)
end S
namespace C
export GeneralCancellationCapPin (antiTensor)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
variable {K : Type} [Field K] [NumberField K] {s degree : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (F : FixedField K degree)
variable (q : Signature K 4) (label : Fin s)
variable (literal : (⟨a label.val,H label⟩ : AnySignature K)=⟨4,q⟩)
variable (even : EvenSupport q) (first : (entries q).a≠0) (last : (entries q).x≠0)
variable (middle : PaperTerminalBridgeSparseOrders.MiddleLive q)
variable (t : K) (nonzero : t≠0)
variable (actual : PaperTerminalBridgeAntiGroup.Available (S.family H) t)
variable (infinite : ¬IsOfFinOrder t)
include literal even first last middle nonzero actual infinite in
theorem extension_exists : Nonempty (PaperTerminalBridgeOneSidedSource.Extension H F) := by
  classical
  have notone : t≠1 := by
    rintro rfl
    exact infinite (isOfFinOrder_iff_pow_eq_one.mpr ⟨1,by omega,by simp⟩)
  obtain ⟨c,hc,N,form⟩:=S.output H t actual notone
  have powers : ∀n : ℕ,0<n→(c*t/c)^n≠1 := by
    intro n hn root
    apply infinite
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨n,hn,?_⟩
    have ratio : c*t/c=t := by field_simp
    rwa [ratio] at root
  let J:=S.table H F N c (c*t) 0
  let j:=S.old label
  have jq : (⟨S.arity H N j.val,J j⟩ : AnySignature K)=⟨4,q⟩ :=
    (S.old_literal H F N c (c*t) 0 label).trans literal
  have pinMember : (⟨2,C.antiTensor 1 0⟩ : AnySignature K)∈S.family J := by
    rw [←S.anti_eq]
    exact ⟨S.label,S.literal H F N c (c*t) 0⟩
  have oneSided : PaperTerminalBridgeDenseSource.OneSided (S.family J) := by
    refine ⟨1,0,⟨1,one_ne_zero,?_⟩,Or.inr ⟨one_ne_zero,rfl⟩⟩
    simpa only [one_mul] using Gadget.realizes_of_mem (S.family J) .disequality _ pinMember
  let E:=PaperTerminalBridgeOneSidedSparse.produce J F q j jq even first last middle oneSided
  exact ⟨{
    count:=E.count
    b:=E.b
    table:=E.table
    old:=fun i=>E.old (S.old i)
    old_literal:=fun i=>(E.old_literal (S.old i)).trans (S.old_literal H F N c (c*t) 0 i)
    label:=E.label
    p:=E.p
    q:=E.q
    p_nonzero:=E.p_nonzero
    q_nonzero:=E.q_nonzero
    literal:=E.literal
    source:=Programme.compose E.source
      (S.source H F N c (c*t) 0 hc (mul_ne_zero hc nonzero) powers form) }⟩

def produce : PaperTerminalBridgeOneSidedSource.Extension H F :=
  (extension_exists H F q label literal even first last middle t nonzero actual infinite).some

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeSparseInfinite
end
