import Holant.Proofs.Hardness.GeneralEOZeroSidedCapProgramme
import Holant.Proofs.Hardness.GeneralEOZeroSidedCapOrientation
import Holant.Proofs.Hardness.GeneralEOOriginalCapSource

/-! Original-field pin elimination for an actual original-row cap with exactly
one nonzero middle coefficient. Reversing the two retained ports handles either
orientation; all queries use the unchanged original dictionary and codec. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOZeroSidedCapSource
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
namespace P
export GeneralEOZeroSidedCapProgramme
  (Input inputEncoding targetEncoding pinValue literalSource query query_counts pin_recovery atMostOne)
end P
namespace I
export GeneralEOOriginalCapInterpolation (cap p q sourceSignatures)
end I
namespace B
export GeneralEOOriginalCapSource (original coefficient cap_value coefficient_mem original_eo)
end B
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalField originalPresentation originalTables originalValue)
end O
namespace R
export GeneralEOZeroSidedCapOrientation (swapped first_swapped second_swapped)
end R
set_option backward.isDefEq.respectTransparency false
variable {s r : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance fieldAlgebra : Algebra ℚ (O.originalField G) := (O.originalField G).algebra'
variable (j : Fin s) (e : Fin (a j.val) ≃ (Fin 2 ⊕ (Fin r×Bool)))

abbrev original := B.original G
abbrev presentation := O.originalPresentation G
abbrev Input := P.Input (original G) j e
abbrev inputEncoding := P.inputEncoding (original G) j e
abbrev pinValue := P.pinValue (original G) j e
abbrev targetEncoding := RawClosedNetwork.validatedEncoding s 1 a
abbrev scale := I.p (original G) j e

/-- The scale and its inverse live in the original field, without adjoining
any new coefficient or choosing a new answer presentation. -/
theorem scale_value : (scale G j e : AlgebraicComplex)=B.coefficient G j e ![false,true] :=
  B.cap_value G j e _

theorem inverse_value : ((scale G j e)⁻¹ : O.originalField G)=
    ⟨(B.coefficient G j e ![false,true])⁻¹,
      (O.originalField G).inv_mem (B.coefficient_mem G j e _)⟩ := by
  apply Subtype.ext
  change ((scale G j e : AlgebraicComplex))⁻¹=_
  rw [scale_value]

variable (he : Signature.CentralSupport (G j))
variable (hp : B.coefficient G j e ![false,true]≠0)
variable (hq : B.coefficient G j e ![true,false]=0)

include hp in
theorem scale_nonzero : scale G j e≠0 := by
  intro hz
  apply hp
  rw [←scale_value G j e,hz]
  rfl

include hq in
theorem second_zero : I.q (original G) j e=0 := by
  apply Subtype.ext
  exact (B.cap_value G j e ![true,false]).trans hq

/-- The sole extra label is the literal ordered directed01 pin. -/
theorem source_pin :
    (⟨GeneralEOZeroSidedCapProgramme.A (original G) j e s,
      I.sourceSignatures (original G) j e ⟨s,Nat.lt_succ_self s⟩⟩ : AnySignature (O.originalField G))=
      ⟨2,fun x=>if x 0=false ∧ x 1=true then 1 else 0⟩ :=
  GeneralEOOriginalCapInterpolation.source_pin (original G) j e

theorem source_old (i : Fin s) :
    (⟨GeneralEOZeroSidedCapProgramme.A (original G) j e i.val,
      I.sourceSignatures (original G) j e ⟨i.val,Nat.lt_trans i.isLt (Nat.lt_succ_self s)⟩⟩ :
        AnySignature (O.originalField G))=⟨a i.val,original G i⟩ :=
  GeneralEOOriginalCapInterpolation.source_old (original G) j e i

/-- Unrestricted literal pin multiplicity reduces to the unchanged original
family by one actual finite Boolean caller and its field-scalar correction. -/
def source : LengthControlledOracleReduction (inputEncoding G j e) (presentation G).encoding
    (targetEncoding (s:=s) (a:=a)) (presentation G).encoding (pinValue G j e) (O.originalValue G) :=
  P.literalSource (original G) j e (presentation G) (B.original_eo G j he)
    (scale_nonzero G j e hp) (second_zero G j e hq)

/-- Either orientation is accepted, but the zero cap is explicitly excluded. -/
def Coefficients : Prop :=
  (B.coefficient G j e ![false,true]≠0 ∧ B.coefficient G j e ![true,false]=0) ∨
  (B.coefficient G j e ![false,true]=0 ∧ B.coefficient G j e ![true,false]≠0)

theorem first_swapped : B.coefficient G j (R.swapped e) ![false,true]=
    B.coefficient G j e ![true,false] := by
  rw [←GeneralEOOriginalCapSource.ambient_cap,←GeneralEOOriginalCapSource.ambient_cap]
  exact R.first_swapped e (G j)

theorem second_swapped : B.coefficient G j (R.swapped e) ![true,false]=
    B.coefficient G j e ![false,true] := by
  rw [←GeneralEOOriginalCapSource.ambient_cap,←GeneralEOOriginalCapSource.ambient_cap]
  exact R.second_swapped e (G j)

/-- This changes only the two boundary port names of the actual graph. -/
def oriented := if B.coefficient G j e ![false,true]=0 then R.swapped e else e

variable (hc : Coefficients G j e)
include hc in
theorem oriented_spec :
    B.coefficient G j (oriented G j e) ![false,true]≠0 ∧
    B.coefficient G j (oriented G j e) ![true,false]=0 := by
  rcases hc with ⟨hp,hq⟩ | ⟨hp,hq⟩
  · simpa only [oriented,if_neg hp] using And.intro hp hq
  · simpa only [oriented,if_pos hp,first_swapped,second_swapped] using And.intro hq hp

def eitherSource := source G j (oriented G j e) he
  (oriented_spec G j e hc).1 (oriented_spec G j e hc).2

include hp hq in
theorem forward_coefficients : Coefficients G j e := Or.inl ⟨hp,hq⟩

theorem zero_excluded (h0 : B.coefficient G j e ![false,true]=0)
    (h1 : B.coefficient G j e ![true,false]=0) : ¬Coefficients G j e := by
  rintro (h | h)
  · exact h.1 h0
  · exact h.2 h1

abbrev Choice := GeneralEOOriginalCapSource.Choice s a

def Applicable : Prop := ∃c : Choice (s:=s) (a:=a),
  Signature.CentralSupport (G c.1) ∧ Coefficients G c.1 c.2

include he hc in
theorem applicable_of_coefficients : Applicable G := by
  have hn := GeneralEOOriginalCapGraph.arity_eq e
  have hr : r=a j.val/2-1 := by omega
  subst r
  exact ⟨⟨j,e⟩,he,hc⟩

def selected (h : Applicable G) : Choice (s:=s) (a:=a) := Classical.choose h

theorem selected_spec (h : Applicable G) :
    Signature.CentralSupport (G (selected G h).1) ∧
      Coefficients G (selected G h).1 (selected G h).2 := Classical.choose_spec h

/-- Finite fixed-family selection, including opposite orientation, leaves no
runtime matching certificate or pin-realization premise in the programme. -/
def selectedSource (h : Applicable G) := eitherSource G (selected G h).1 (selected G h).2
  (selected_spec G h).1 (selected_spec G h).2

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOZeroSidedCapSource
