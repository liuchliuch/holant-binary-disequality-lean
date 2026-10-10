import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeSparseOrders

/-! A one-sided actual antidiagonal and any live weight-two coefficient of
the endpoint q4 supply a literal nonsingular weighted equality. The chosen
port order is implemented by an original-row macro before factor exposure.
All old rows and the exact original oracle remain retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeOneSidedSparse
open Holant Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace S
export PaperTerminalBridgeDenseSemantic (family)
export PaperTerminalBridgeOneSidedSource (Extension)
end S
namespace O
export PaperTerminalBridgeSparseOrders (MiddleLive reordered first last even selected output output_value)
end O
namespace A
export NativeNormalizedGraphAdjoin (arity signatures old old_literal newLabel normalized_literal source)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option Elab.async false
variable {K : Type} [Field K] [NumberField K] {s degree : ℕ} {a : ℕ→ℕ}

theorem oneSided_mono {F G : SignatureFamily K} (included : F⊆G)
    (oneSided : PaperTerminalBridgeDenseSource.OneSided F) : PaperTerminalBridgeDenseSource.OneSided G := by
  obtain ⟨p,q,⟨c,hc,actual⟩,side⟩ := oneSided
  exact ⟨p,q,⟨c,hc,actual.mono included⟩,side⟩

variable (H : (i : Fin s)→Signature K (a i.val)) (F : FixedField K degree)
variable (q : Signature K 4) (label : Fin s)
variable (literal : (⟨a label.val,H label⟩ : AnySignature K)=⟨4,q⟩)
variable (even : EvenSupport q) (first : (entries q).a≠0) (last : (entries q).x≠0)
variable (middle : O.MiddleLive q)
variable (oneSided : PaperTerminalBridgeDenseSource.OneSided (S.family H))

include literal even first last middle oneSided in
theorem extension_exists : Nonempty (S.Extension H F) := by
  classical
  obtain ⟨k,live⟩ := O.selected q middle
  let N := O.output H q label literal k
  let q' := O.reordered q k
  have form : N.network.denote=fun x=>1*q' x := by
    simpa only [one_mul] using O.output_value H q label literal k
  let J := A.signatures F H N 1
  let j := A.newLabel H
  have jq : (⟨A.arity H N j.val,J j⟩ : AnySignature K)=⟨4,q'⟩ :=
    A.normalized_literal F H N 1 q' one_ne_zero form
  have included : S.family H⊆S.family J := by
    rintro f ⟨i,rfl⟩
    exact ⟨A.old H i,A.old_literal F H N 1 i⟩
  have first' : (entries q').a≠0 := by rw [O.first];exact first
  have last' : (entries q').x≠0 := by rw [O.last];exact last
  let E := PaperTerminalBridgeOneSidedMiddle.produce J F q' j jq
    (O.even q even k) first' live last' (oneSided_mono included oneSided)
  exact ⟨{
    count:=E.count
    b:=E.b
    table:=E.table
    old:=fun i=>E.old (A.old H i)
    old_literal:=fun i=>(E.old_literal (A.old H i)).trans (A.old_literal F H N 1 i)
    label:=E.label
    p:=E.p
    q:=E.q
    p_nonzero:=E.p_nonzero
    q_nonzero:=E.q_nonzero
    literal:=E.literal
    source:=Programme.compose E.source (A.source F H N 1 one_ne_zero) }⟩

def produce : S.Extension H F :=
  (extension_exists H F q label literal even first last middle oneSided).some

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeOneSidedSparse
end
