import Holant.Complexity.FixedGadgetSubstitution.TemplateCorrespondence
import Holant.Complexity.FixedGadgetSubstitution.Adjoin

/-! Reversing a fixed physical gadget means permuting its two genuine ordered
boundary occurrences. Its vertices, edge labels and all disconnected components
remain present. The two exact replacement compilers share the same input codec. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Complexity.UniversalPairReduction
open Computability BinaryCompose FixedGadgetSubstitution

/-- Relabel only external positions, retaining every internal edge occurrence. -/
def permuteBoundary {n : ℕ} (S : NetworkShape n) (p : Equiv.Perm (Fin n)) : NetworkShape n where
  vertices := S.vertices
  arity := S.arity
  edges := S.edges
  ports := S.ports.trans (Equiv.sumCongr p (Equiv.refl _))

def permuteLabelling {n s b : ℕ} {S : NetworkShape n} {arity : ℕ → ℕ}
    (L : Labelling S s b arity) (p : Equiv.Perm (Fin n)) :
    Labelling (permuteBoundary S p) s b arity where
  vertex := L.vertex
  vertex_arity := L.vertex_arity
  edge := L.edge

variable {K : Type*} [CommSemiring K] {n s b : ℕ} {arity : ℕ → ℕ}
variable {S : NetworkShape n} (L : Labelling S s b arity)
variable (signatures : (i : Fin s) → Signature K (arity i.val))
variable (kernels : Fin b → Bool → Bool → K)

theorem permute_assignment (p : Equiv.Perm (Fin n)) (x : Fin n → Bool)
    (z : (Fin S.edges × Bool) → Bool) (v : Fin S.vertices) :
    (permuteBoundary S p).assignment x z v = S.assignment (fun j => x (p j)) z v := by
  funext i
  change Sum.elim x z ((Equiv.sumCongr p (Equiv.refl _)) (S.ports ⟨v,i⟩)) =
    Sum.elim (fun j => x (p j)) z (S.ports ⟨v,i⟩)
  cases S.ports ⟨v,i⟩ <;> rfl

theorem denote_permute (p : Equiv.Perm (Fin n)) (x : Fin n → Bool) :
    ((permuteLabelling L p).sourceNetwork signatures kernels).denote x =
      (L.sourceNetwork signatures kernels).denote (fun j => x (p j)) := by
  unfold Network.denote
  dsimp only [Labelling.sourceNetwork,permuteLabelling]
  simp_rw [permute_assignment]
  rfl

/-- The reverse-order tensor has a literal well-formed fixed template. -/
theorem template_permute (p : Equiv.Perm (Fin n)) (x : Fin n → Bool) :
    (((permuteLabelling L p).template).network (permuteLabelling L p).wellFormed
      signatures kernels).denote x =
      (L.sourceNetwork signatures kernels).denote (fun j => x (p j)) := by
  rw [Labelling.denote_template]
  exact denote_permute L signatures kernels p x

/-- Original labels followed by the distinguished binary label. -/
def extendedArity (s : ℕ) (arity : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i<s then arity i else 2

namespace OrderedQueries
variable {s b : ℕ} {arity : ℕ → ℕ} {S : NetworkShape 2}
variable (L : Labelling S s b arity)

abbrev Input := { r : RawClosedNetwork // r.WellFormed (s+1) b (extendedArity s arity) }

abbrev templates (p : Equiv.Perm (Fin 2)) :=
  Adjoin.templates s arity (permuteLabelling L p).template

theorem valid (p : Equiv.Perm (Fin 2)) : ∀i<s+1,
    (templates L p i).WellFormed s b arity ∧
      (templates L p i).boundary=extendedArity s arity i := by
  intro i hi
  refine ⟨Adjoin.wellFormed _ (permuteLabelling L p).wellFormed i hi,?_⟩
  by_cases h : i<s
  · simp [templates,Adjoin.templates,h,identityTemplate,extendedArity]
  · simp [templates,Adjoin.templates,h,extendedArity,Labelling.template]

def query (p : Equiv.Perm (Fin 2)) (r : Input (s:=s) (b:=b) (arity:=arity)) :
    { r : RawClosedNetwork // r.WellFormed s b arity } :=
  Compiler.value (s+1) b (extendedArity s arity) (templates L p) s arity (valid L p) r

/-- A real finite Boolean-stack compiler from the original bytes to the query;
no new incidence certificate or already-processed network is supplied. -/
def computes (p : Equiv.Perm (Fin 2)) :
    Computes (RawClosedNetwork.validatedEncoding (s+1) b (extendedArity s arity))
      (RawClosedNetwork.validatedEncoding s b arity) (query L p) :=
  Compiler.computes (s+1) b (extendedArity s arity) (templates L p) s arity (valid L p)

abbrev plus := query L (Equiv.refl _)
abbrev minus := query L (Equiv.swap 0 1)

/-- Both ordered queries are produced in actual polynomial time. -/
def bothComputes :
    Computes (RawClosedNetwork.validatedEncoding (s+1) b (extendedArity s arity))
      (FixedFieldMachines.pairEncoding
        (RawClosedNetwork.validatedEncoding s b arity)
        (RawClosedNetwork.validatedEncoding s b arity))
      (fun r => (plus L r,minus L r)) :=
  FixedFieldMachines.pairComputes (computes L (Equiv.refl _)) (computes L (Equiv.swap 0 1))

end OrderedQueries
end Holant.Complexity.UniversalPairReduction
