import Holant.Proofs.Closure.ClosureSixPortSupportOrder
import Holant.Proofs.Closure.ClosureRootPencilSource

/-! Literal finite support certificates for P/P and P/C. The atlas includes
all three residual matchings, their parities, both sector orientations, and
both singleton endpoint orientations. It does not assert that an arbitrary
tensor has one of these supports. No bit dressing changes the original phase
kernel: every witness is an actual ordered coordinate pair. -/
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
open Holant
namespace Proportional

def MatchingCoset (k : Fin 3) (a b : Bool) (x : Word 4) : Prop :=
  match k.val with
  | 0 => (x 0 ^^ x 1)=a ∧ (x 2 ^^ x 3)=b
  | 1 => (x 0 ^^ x 2)=a ∧ (x 1 ^^ x 3)=b
  | _ => (x 0 ^^ x 3)=a ∧ (x 1 ^^ x 2)=b

instance matchingCosetDecidable (k : Fin 3) (a b : Bool) (x : Word 4) :
    Decidable (MatchingCoset k a b x) := by unfold MatchingCoset; split <;> infer_instance

set_option maxRecDepth 100000 in
theorem pairing_coset : ∀ i j k l : Fin 4,
    (i≠j ∧ i≠k ∧ i≠l ∧ j≠k ∧ j≠l ∧ k≠l) → ∀ a b : Bool,
    ∃ key : Fin 3, ∃ r s : Bool, ∀ x : Word 4,
      ((x i ^^ x j)=a ∧ (x k ^^ x l)=b) ↔ MatchingCoset key r s x := by
  intro i j k l distinct a b
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp_all
  all_goals revert a b; decide

set_option maxRecDepth 100000 in
theorem matchingCoset_nonempty (k : Fin 3) (a b : Bool) :
    ∃ x : Word 4, MatchingCoset k a b x := by
  fin_cases k <;> cases a <;> cases b <;> decide

set_option maxRecDepth 100000 in
theorem matchingCoset_parity (k : Fin 3) (a b : Bool) (x : Word 4)
    (member : MatchingCoset k a b x) : parity x=bit (a ^^ b) := by
  have finite : ∀ k : Fin 3, ∀ a b : Bool, ∀ x : Word 4,
      MatchingCoset k a b x → parity x=bit (a ^^ b) := by decide
  exact finite k a b x member

def PPSupport (ke ko : Fin 3) (ae be ao bo : Bool)
    (fe fo : Bool → Bool) : Finset (Word 6) := Finset.univ.filter (fun x =>
  if x 0 ^^ x 1 then fo (x 0)=true ∧ MatchingCoset ko ao bo (residualSix (Equiv.refl _) x)
  else fe (x 0)=true ∧ MatchingCoset ke ae be (residualSix (Equiv.refl _) x))

def ProjectionOverflow (S : Finset (Word 6)) (i j : Fin 6) (p : Bool) : Prop :=
  i≠j ∧ 4 < (selectedOutputs S (pairOrder i j) p).card

instance projectionOverflowDecidable (S : Finset (Word 6)) (i j : Fin 6) (p : Bool) :
    Decidable (ProjectionOverflow S i j p) := by unfold ProjectionOverflow; infer_instance

def cWord (edge : Fin 6) (a b o z w : Bool) : Word 4 :=
  residualSix (Equiv.refl _) (secondFlat edge a b o z w)

def CSupport (edge : Fin 6) (a b o z : Bool) : Finset (Word 4) :=
  Finset.univ.image (cWord edge a b o z)

def PCSupport (kp : Fin 3) (ap bp : Bool) (flags : Bool → Bool)
    (sector : Bool) (edge : Fin 6) (a b o : Bool) : Finset (Word 6) :=
  Finset.univ.filter (fun x =>
    if (x 0 ^^ x 1)=sector then
      flags (x 0)=true ∧ MatchingCoset kp ap bp (residualSix (Equiv.refl _) x)
    else residualSix (Equiv.refl _) x ∈ CSupport edge a b o (x 0))

def ProjectionCertificate (S : Finset (Word 6)) (i j : Fin 6) (p : Bool) : Prop :=
  i≠j ∧ (4 < (selectedOutputs S (pairOrder i j) p).card ∨
    ((selectedWords S (pairOrder i j) p).card=2 ∧
      (selectedOutputs S (pairOrder i j) p).card=2))

instance projectionCertificateDecidable (S : Finset (Word 6)) (i j : Fin 6) (p : Bool) :
    Decidable (ProjectionCertificate S i j p) := by unfold ProjectionCertificate; infer_instance


end Proportional
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
