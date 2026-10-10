import Holant.Proofs.Reductions.SingleWeightCompletion.OptionalQuery
import Holant.Proofs.Reductions.GeneralExtraction.GeneralOriginalTarget
import Holant.Proofs.Algorithms.FieldCodec


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.SingleWeightCompletion.AnswerField
open Holant.Tractable
open Computability Holant.Algebraic Holant.Complexity
open BinaryCompose
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.GeneralExtraction
attribute [local instance] Classical.propDecidable
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val)) (d : Fin s → ℕ)

abbrev Source := GeneralOriginalTarget.originalField G
abbrev Target := GeneralOriginalTarget.originalField (table G d)
abbrev sourcePresentation := GeneralOriginalTarget.originalPresentation G
abbrev targetPresentation := GeneralOriginalTarget.originalPresentation (table G d)
abbrev sourceValue := GeneralOriginalTarget.originalValue G
abbrev targetValue := GeneralOriginalTarget.originalValue (table G d)

theorem entry_range (i : Fin s) : Set.range (table G d i) = Set.range (completed (G i) (d i)) :=
  congrArg (fun f : AnySignature AlgebraicComplex => Set.range f.2)
    ((table_label G d i).trans (completed_exact (G i) (d i)).symm)

theorem target_le : Target G d ≤ Source G := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨⟨i,x⟩,rfl⟩
  have hm : table G d i x ∈ Set.range (completed (G i) (d i)) := by
    rw [←entry_range G d i]
    exact ⟨x,rfl⟩
  obtain ⟨y,hy⟩ := hm
  change table G d i x ∈ Source G
  rw [←hy,completed_apply]
  split
  · exact coefficient_mem_familyField (GeneralOriginalTarget.coefficients G) ⟨i,restrict (d i) y⟩
  · exact (Source G).zero_mem

theorem source_le : Source G ≤ Target G d := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨⟨i,x⟩,rfl⟩
  have hm : G i x ∈ Set.range (completed (G i) (d i)) :=
    ⟨extend (d i) x,completed_extend (G i) (d i) x⟩
  rw [←entry_range G d i] at hm
  obtain ⟨y,hy⟩ := hm
  change G i x ∈ Target G d
  rw [←hy]
  exact coefficient_mem_familyField (GeneralOriginalTarget.coefficients (table G d)) ⟨i,y⟩

theorem fields_equal : Target G d=Source G := le_antisymm (target_le G d) (source_le G d)
def recover : Target G d →ₐ[ℚ] Source G := IntermediateField.inclusion (target_le G d)
def send : Source G →ₐ[ℚ] Target G d := IntermediateField.inclusion (source_le G d)
def recoverComputes : Computes (targetPresentation G d).encoding (sourcePresentation G).encoding (recover G d) :=
  FieldCodec.computes (targetPresentation G d) (sourcePresentation G) (recover G d).toLinearMap
def sendComputes : Computes (sourcePresentation G).encoding (targetPresentation G d).encoding (send G d) :=
  FieldCodec.computes (sourcePresentation G) (targetPresentation G d) (send G d).toLinearMap
@[simp] theorem recover_send (x : Source G) : recover G d (send G d x)=x := Subtype.ext rfl
@[simp] theorem send_recover (x : Target G d) : send G d (recover G d x)=x := Subtype.ext rfl

theorem accepted (r : OptionalQuery.Good G d) :
    recover G d (targetValue G d (OptionalQuery.goodQuery G d r))=sourceValue G r.val := by
  apply Subtype.ext
  change ((targetValue G d (OptionalQuery.goodQuery G d r) : Target G d) : AlgebraicComplex)=_
  rw [GeneralOriginalTarget.target_exact,GeneralOriginalTarget.target_exact]
  exact OptionalQuery.accepted_value G d r

theorem rejected (hd : ∀ i, Signature.SingleLayer (G i) (d i))
    (r : Input (s:=s) (a:=a)) (h : ¬ OptionalQuery.Accept G d r) : sourceValue G r=0 := by
  apply Subtype.ext
  change ((sourceValue G r : Source G) : AlgebraicComplex)=0
  rw [GeneralOriginalTarget.target_exact]
  exact OptionalQuery.reject_zero G d hd r h

def targetOutput : PolynomialOutputBound (OptionalQuery.targetEncoding (a:=a) d)
    (targetPresentation G d).encoding (targetValue G d) :=
  (GeneralOriginalTarget.originalTables (table G d)).outputBound (targetPresentation G d)

end Holant.LocalDrafts.Hardness.SingleWeightCompletion.AnswerField
