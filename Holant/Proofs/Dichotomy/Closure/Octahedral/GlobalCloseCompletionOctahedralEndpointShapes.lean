import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralInverseTransport
import Holant.Certificates.OctahedralSeparator.TensorData
import Holant.Certificates.OctahedralSeparator.TensorSemantics
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo
open Holant Holant.Certificates.OctahedralSeparator

def OriginalEndpoint {L : Type*} [Field L] (q : Signature L 4) : Prop :=
  q (fun _=>false)≠0 ∧ q (fun _=>true)≠0 ∧ ∀x,Holant.weight x%2=1 → q x=0

def literalEquality {L : Type*} [Field L] : Signature L 4 := fun x=>
  if x=(fun _=>false) ∨ x=(fun _=>true) then 1 else 0

/-- Its scalar is the actual first coordinate, not a selected unit. -/
def EqualityTest {L : Type*} [Field L] (q : Signature L 4) : Prop :=
  q (fun _ => false) ≠ 0 ∧
    ∀ x,q x = q (fun _ => false)*literalEquality x

theorem equality_endpoint {L : Type*} [Field L] (q : Signature L 4)
    (h : EqualityTest q) : OriginalEndpoint q := by
  refine ⟨h.1,?_,?_⟩
  · rw [h.2 (fun _ => true)]
    simpa [literalEquality] using h.1
  · intro x hx
    have h0 : x ≠ (fun _ => false) := by
      intro he
      subst x
      norm_num [Holant.weight] at hx
    have h1 : x ≠ (fun _ => true) := by
      intro he
      subst x
      norm_num [Holant.weight] at hx
    rw [h.2 x]
    simp [literalEquality,h0,h1]


/-- The exact coefficients of the preserved printed endpoint row 9. -/
def printedNine : Signature Scalar 4 := fun x=>
  if Holant.Marked.SupportAtlas.parity x then 0 else
    if x=(fun _=>false) ∨ x=(fun _=>true) then 1 else -1

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankTwo
