import Holant.Proofs.Hardness.EOBinaryPlaneChoiceGadgets
import Holant.Proofs.Hardness.OriginalPortAccess

/-! The complete five-candidate producer is a finite family of actual templates.
The first two use one original vertex and a boundary order; the other three use
two original vertices and two native-X edges. Every boundary has arity four. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneCandidateGadgets
open Holant Holant.Complexity FixedGadgetSubstitution
namespace B
export EOBinaryPlaneCore (lift)
end B
namespace N
export EOBinaryPlaneChoiceGadgets (output template template_valid template_denote counts)
end N
namespace P
export OriginalPortAccess (template template_valid template_denote normalized)
end P
set_option backward.isDefEq.respectTransparency false

def transposePorts : Equiv.Perm (Fin 4) where
  toFun := ![2,3,0,1]
  invFun := ![2,3,0,1]
  left_inv := by decide
  right_inv := by decide

def transpose {K : Type} (f : Signature K 2) : Signature K 2 := fun z=>f ![z 1,z 0]

theorem transpose_lift {K : Type} [Zero K] (f : Signature K 2) :
    P.normalized (B.lift f) transposePorts=B.lift (transpose f) := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  all_goals simp [P.normalized,transposePorts,B.lift,transpose,h0,h1,h2,h3]

def output {K : Type} [Semiring K] (f : Signature K 2) (kind : Fin 5) : Signature K 2 :=
  ![f,transpose f,N.output f 0,N.output f 1,N.output f 2] kind

def selected (kind : Fin 5) : Template :=
  ![P.template (L:=ℚ) (fun _=>0) (Equiv.refl _),
    P.template (L:=ℚ) (fun _=>0) transposePorts,N.template 0,N.template 1,N.template 2] kind

def template (kind : Fin 5) : Template where
  boundary := 4
  vertices := (selected kind).vertices
  edges := (selected kind).edges

theorem template_eq (kind : Fin 5) : template kind=selected kind := by fin_cases kind <;> rfl

theorem valid (kind : Fin 5) : (template kind).WellFormed 1 1 (fun _=>4) := by
  rw [template_eq]
  fin_cases kind
  · exact P.template_valid (L:=ℚ) (fun _=>0) (Equiv.refl _)
  · exact P.template_valid (L:=ℚ) (fun _=>0) transposePorts
  · exact N.template_valid 0
  · exact N.template_valid 1
  · exact N.template_valid 2

theorem template_denote {K : Type} [Field K] [Algebra ℚ K]
    (f : Signature K 2) (kind : Fin 5) :
    ((template kind).network (valid kind) (fun _=>B.lift f)
      (fun _=>Signature.disequality)).denote=B.lift (output f kind) := by
  fin_cases kind
  · exact P.template_denote (B.lift f) (Equiv.refl _)
  · exact (P.template_denote (B.lift f) transposePorts).trans (transpose_lift f)
  · exact N.template_denote f 0
  · exact N.template_denote f 1
  · exact N.template_denote f 2

theorem counts (kind : Fin 5) : (template kind).vertices.length≤2 ∧
    (template kind).edges.length≤2 := by fin_cases kind <;> decide

theorem counts_exact (kind : Fin 5) :
    (template kind).vertices.length=(if kind.val<2 then 1 else 2) ∧
      (template kind).edges.length=(if kind.val<2 then 0 else 2) := by fin_cases kind <;> decide

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneCandidateGadgets
