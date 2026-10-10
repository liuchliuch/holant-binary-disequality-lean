import Holant.Complexity.FixedGadgetSubstitution.TemplateCorrespondence

/-! Retained signatures compile to a single literal vertex, with every original
ordered boundary endpoint preserved and no additional edge or scalar resource. -/
namespace Holant.Complexity.FixedGadgetSubstitution
open RawClosedNetwork
set_option backward.isDefEq.respectTransparency false

def identityShape (n : ℕ) : NetworkShape n where
  vertices := 1
  arity _ := n
  edges := 0
  ports := {
    toFun p := .inl p.2
    invFun := Sum.elim (fun i => ⟨0,i⟩) (fun p => Fin.elim0 p.1)
    left_inv p := by rcases p with ⟨v,i⟩; have h : v=0 := Subsingleton.elim _ _; subst v; rfl
    right_inv p := by cases p with
      | inl i => rfl
      | inr e => exact Fin.elim0 e.1 }

def identityLabelling {s b : ℕ} (arity : ℕ → ℕ) (label : Fin s) :
    Labelling (identityShape (arity label.val)) s b arity where
  vertex _ := label
  vertex_arity _ := rfl
  edge := Fin.elim0

/-- Static original-family identity template; no value table is stored in input. -/
def identityTemplate (arity : ℕ → ℕ) (label : ℕ) : Template where
  boundary := arity label
  vertices := List.ofFn fun _ : Fin 1 =>
    (label,List.ofFn fun i : Fin (arity label) => (Sum.inl i.val : LocalEndpoint))
  edges := []

 theorem identity_template_eq {s b : ℕ} (arity : ℕ → ℕ) (label : Fin s) :
    identityTemplate arity label.val = (identityLabelling (b:=b) arity label).template := rfl

 theorem identityTemplate_wellFormed {s b : ℕ} (arity : ℕ → ℕ) (label : Fin s) :
    (identityTemplate arity label.val).WellFormed s b arity :=
  (identityLabelling arity label).wellFormed

 theorem identityTemplate_denote {K : Type*} [CommSemiring K] {s b : ℕ}
    (arity : ℕ → ℕ) (label : Fin s)
    (signatures : (i : Fin s) → Signature K (arity i.val))
    (kernels : Fin b → Bool → Bool → K) :
    ((identityTemplate arity label.val).network (identityTemplate_wellFormed arity label)
      signatures kernels).denote = signatures label := by
  change (((identityLabelling (b:=b) arity label).template).network
    (identityLabelling arity label).wellFormed signatures kernels).denote = _
  rw [Labelling.denote_template]
  funext x
  simp [Labelling.sourceNetwork,identityLabelling,identityShape,Network.denote,
    NetworkShape.assignment]

end Holant.Complexity.FixedGadgetSubstitution
