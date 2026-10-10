import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureComplete
import Holant.Proofs.Dichotomy.Main.PaperQuaternaryPureResidual
import Holant.Proofs.Dichotomy.Main.PaperQuaternaryPositive

/-! Exact third main dichotomy on the original finite native-X family.
No identity is supplied. The source-preserving pure Eq4 event is consumed
by a proved shared phase classifier and actual controlled graph sources. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternary
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.EightVertex.ProductAnchor
namespace I
export NoIOriginalInput (field presentation table source ambient)
end I
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
abbrev family := PaperLiteralEqualityCriterion.family G
abbrev Criterion := Tract (familyAction sourceKBasis (family G))
abbrev Hard := PaperLiteralEqualityCriterion.Hard G
abbrev inputEncoding := PaperLiteralEqualityCriterion.inputEncoding (s:=s) (a:=a)
abbrev presentation := PaperLiteralEqualityCriterion.presentation G
abbrev value := PaperLiteralEqualityCriterion.value G
variable (q : Signature AlgebraicComplex 4) (label : Fin s)
variable (literal : (⟨a label.val,G label⟩ : AnySignature AlgebraicComplex) = ⟨4,q⟩)
variable (endpoint : EndpointEven q)

include literal endpoint in
theorem criterion_or_controlledHard : Criterion G ∨ (PaperLiteralEqualityHardness.target G).Hard := by
  have even : Holant.LocalDrafts.Hardness.EightVertexNonexception.EvenSupport q := by
    intro x odd
    exact endpoint.2.2 x (by omega)
  have zeroWord : (![false,false,false,false] : Fin 4 → Bool) = (fun _ => false) := by
    funext i
    fin_cases i <;> rfl
  have oneWord : (![true,true,true,true] : Fin 4 → Bool) = (fun _ => true) := by
    funext i
    fin_cases i <;> rfl
  have first : (Holant.LocalDrafts.Hardness.EightVertexNonexception.entries q).a ≠ 0 := by
    simpa only [Holant.LocalDrafts.Hardness.EightVertexNonexception.entries,zeroWord] using endpoint.1
  have last : (Holant.LocalDrafts.Hardness.EightVertexNonexception.entries q).x ≠ 0 := by
    simpa only [Holant.LocalDrafts.Hardness.EightVertexNonexception.entries,oneWord] using endpoint.2.1
  rcases PaperQuaternaryPureResidual.source G q label literal even first last with good|hard|pure
  · exact Or.inl good
  · exact Or.inr hard
  · obtain ⟨D⟩ := pure
    rcases NoIPureComplete.event (I.field G) (I.table G) (I.presentation G) D with good|hard
    · exact Or.inl (by simpa only [I.ambient] using good)
    · exact Or.inr (NoIOrdinaryRaw.Target.Hard.compose
        (S:=NoISuppliedIdentityConsumer.target (I.field G) (I.table G) (I.presentation G))
        (T:=PaperLiteralEqualityHardness.target G) hard (I.source G))

include literal endpoint in
theorem positive (criterion : Criterion G) :
    InFP (inputEncoding (s:=s) (a:=a)) (presentation G).encoding (value G) :=
  PaperQuaternaryPositive.inFP_of_tract G ⟨label,literal⟩ endpoint criterion

include literal endpoint in
theorem controlledNegative (negative : ¬Criterion G) : (PaperLiteralEqualityHardness.target G).Hard :=
  (criterion_or_controlledHard G q label literal endpoint).resolve_left negative

include literal endpoint in
theorem negative (notCriterion : ¬Criterion G) : Hard G :=
  NoIOrdinaryRaw.Target.Hard.witness (controlledNegative G q label literal endpoint notCriterion)

include literal endpoint in
theorem dichotomy :
    (Criterion G → InFP (inputEncoding (s:=s) (a:=a)) (presentation G).encoding (value G)) ∧
    (¬Criterion G → Hard G) :=
  ⟨positive G q label literal endpoint,negative G q label literal endpoint⟩

/-- The retained prime endpoint from the manuscript is an instance of the
proved endpoint theorem; its exact original membership is retained. -/
theorem dichotomy_of_member (member : (⟨4,q⟩ : AnySignature AlgebraicComplex) ∈ family G)
    (even : EndpointEven q) (_prime : Holant.Certificates.EqualityQuaternary.TensorPrime q) :
    (Criterion G → InFP (inputEncoding (s:=s) (a:=a)) (presentation G).encoding (value G)) ∧
    (¬Criterion G → Hard G) := by
  obtain ⟨j,literal⟩ := member
  exact dichotomy G q j literal even


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternary
end
