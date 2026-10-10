import Holant.Proofs.Tractability.EOEvaluation.CandidateExecution.Queries
import Holant.Proofs.Tractability.ProductMachine.FamilyFieldSolver
import Holant.Proofs.Algorithms.OriginalFamily
import Holant.Proofs.Algorithms.FamilyAnswerTransport


namespace Holant.LocalDrafts.Tractability.EOEvaluation.CandidateExecution.Catalogue
open Holant Holant.Tractable Holant.Complexity
open LocalAffineMachine.Relabel
noncomputable section
variable {s : ℕ} {arity : ℕ → ℕ}

abbrev Label := Σ i : Fin s, Option (PairingTemplates.Label (arity i.val))
abbrev count := Fintype.card (Label (s := s) (arity := arity))
def codes := Fintype.equivFin (Label (s := s) (arity := arity))
def code (a : Label (s := s) (arity := arity)) : ℕ := (codes a).val
def targetArity (k : ℕ) := if h : k < count (s := s) (arity := arity) then
  arity ((codes.symm ⟨k, h⟩).1.val) else 0
@[simp] theorem arity_index (i : Fin (count (s := s) (arity := arity))) :
    targetArity (s := s) (arity := arity) i.val = arity ((codes.symm i).1.val) := by
  simp only [targetArity, dif_pos i.isLt]
@[simp] theorem arity_code (a : Label (s := s) (arity := arity)) :
    targetArity (s := s) (arity := arity) (code a) = arity a.1.val := by
  simpa only [code, Equiv.symm_apply_apply] using
    (arity_index (s := s) (arity := arity) (codes a))

def pairing {n : ℕ} (p : PairingTemplates.Label n) : OrientedPerfectPairing n :=
  ⟨n / 2, PairingTemplates.decode p⟩
variable (D : Source.Family s arity)
def tensor (a : Label (s := s) (arity := arity)) : Signature AlgebraicComplex (arity a.1.val) :=
  match a.2 with
  | none => 0
  | some p => PairLift.restrict (pairing p) (D.signatures a.1)

theorem shared_exists : ∃ C : EOClass, ∀ a : Label (s := s) (arity := arity), C.Holds (tensor D a) := by
  obtain ⟨_, C, _, hp⟩ := Source.shared_conditions D
  refine ⟨C, ?_⟩
  rintro ⟨i, p⟩
  cases p with
  | none => cases C <;> first | exact affine_zero _ | exact product_zero _
  | some p => exact PairLift.class_lift (pairing p) C (hp i (pairing p))

def branch : EOClass := Classical.choose (shared_exists D)
theorem tensor_class (a : Label (s := s) (arity := arity)) : (branch D).Holds (tensor D a) :=
  Classical.choose_spec (shared_exists D) a

def signatures (i : Fin (count (s := s) (arity := arity))) :
    Signature AlgebraicComplex (targetArity (s := s) (arity := arity) i.val) :=
  LocalAffineMachine.Relabel.Catalogue.transport (arity_index i).symm (tensor D (codes.symm i))
def kernels (_ : Fin 1) : Kernel AlgebraicComplex := Signature.disequality

theorem signatures_class (i : Fin (count (s := s) (arity := arity))) :
    (branch D).Holds (signatures D i) := by
  have transport_class {m n : ℕ} (h : m = n) (C : EOClass)
      (f : Signature AlgebraicComplex m) (hf : C.Holds f) :
      C.Holds (LocalAffineMachine.Relabel.Catalogue.transport h f) := by
    cases h
    change C.Holds (fun x => f (fun j => x j))
    exact hf
  exact transport_class _ _ _ (tensor_class D _)

theorem vertex_lookup (i : Fin (count (s := s) (arity := arity)))
    (a : Label (s := s) (arity := arity)) (hi : i = codes a)
    (x : Fin (targetArity (s := s) (arity := arity) i.val) → Bool) :
    signatures D i x = tensor D a (fun j => x (Fin.cast
      (show arity a.1.val = targetArity (s := s) (arity := arity) i.val by
        subst i
        exact (arity_code a).symm) j)) := by
  subst i
  have lookup (c : Label (s := s) (arity := arity)) (hc : c = a)
      (h : arity c.1.val = targetArity (s := s) (arity := arity) (codes a).val) :
      tensor D c (fun j => x (Fin.cast h j)) =
        tensor D a (fun j => x (Fin.cast (arity_code a).symm j)) := by
    subst c
    rfl
  exact lookup (codes.symm (codes a)) (codes.symm_apply_apply a) (arity_index (codes a)).symm

theorem kernel_affine : Holant.Tractable.Affine
    (fun x : Fin 2 → Bool => Signature.disequality (x 0) (x 1)) := by
  let S : Holant.Tractable.AffineSystem 2 := ⟨1, fun _ _ => 1, fun _ => 1⟩
  have hs (x : Fin 2 → Bool) : S.Holds x ↔ x 0 ≠ x 1 := by
    simp only [AffineSystem.Holds, S, Fin.forall_fin_one, Fin.sum_univ_two, one_mul]
    cases h0 : x 0 <;> cases h1 : x 1 <;> decide
  convert Holant.Tractable.affine_indicator S using 1
  funext x
  simp only [hs]
  by_cases h : x 0 = x 1 <;> simp [Signature.disequality, h]

def affineFamily (h : branch D = .affine) :
    AffineMachine.Assembly.Family (count (s := s) (arity := arity)) 1 (targetArity (s := s) (arity := arity)) where
  signatures := signatures D
  kernels := kernels
  vertexAffine i := by simpa only [h, EOClass.Holds] using signatures_class D i
  edgeAffine _ := Holant.LocalDrafts.Tractability.EOEvaluation.CandidateExecution.Catalogue.kernel_affine

def productFamily (h : branch D = .product) :
    ProductElimination.FamilyData (count (s := s) (arity := arity)) 1 (targetArity (s := s) (arity := arity)) where
  signatures := signatures D
  kernels := kernels
  vertex i := ProductElimination.ofProduct (by simpa only [h, EOClass.Holds] using signatures_class D i)
  edge _ := ProductElimination.ofProduct (product_disequality (0 : Fin 2) 1)

end
end Holant.LocalDrafts.Tractability.EOEvaluation.CandidateExecution.Catalogue
