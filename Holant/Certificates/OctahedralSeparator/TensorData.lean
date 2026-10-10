import Holant.Certificates.OctahedralSeparator.Data
import Holant.Certificates.TetrahedralDeck.FiniteData
import Holant.BoundaryAction
import Holant.TwoPorts

/-! Literal source tensors. The six deficient cards are reconstructed first,
then contracted on original ports 1/3 with I. -/
namespace Holant.Certificates.OctahedralSeparator
open Holant

def p0 (U V : Mat) : Signature Scalar 4 := fun x => U (x 0) (x 1)*V (x 2) (x 3)
def p1 (U V : Mat) : Signature Scalar 4 := fun x => U (x 0) (x 2)*V (x 1) (x 3)
def p2 (U V : Mat) : Signature Scalar 4 := fun x => U (x 0) (x 3)*V (x 1) (x 2)
def tensorScale {n : ℕ} (c : Scalar) (f : Signature Scalar n) : Signature Scalar n := fun x => c*f x
def aTensor := p0 (q 0) (q 0)
def bTensor := p1 (q 0) (q 0)
def cTensor := p2 (q 2) (q 2)

/-- R0,R1,R3,R01+-,R01-+,R03+-,R03-+,R13++,R13--. -/
def regular : Fin 9 → Signature Scalar 4 :=
  ![tensorScale (rat (1/2)) (p2 (q 0) (q 0)),
    tensorScale (rat (-1/2)) (p2 (q 1) (q 1)),
    tensorScale (rat (-1/2)) (p2 (q 3) (q 3)),
    tensorScale (rat (1/4)) (p2 (q 0+q 1) (q 0-q 1)),
    tensorScale (rat (1/4)) (p2 (q 0-q 1) (q 0+q 1)),
    tensorScale (rat (1/4)) (p2 (q 0+q 3) (q 0-q 3)),
    tensorScale (rat (1/4)) (p2 (q 0-q 3) (q 0+q 3)),
    tensorScale (rat (-1/4)) (p2 (q 1+q 3) (q 1+q 3)),
    tensorScale (rat (-1/4)) (p2 (q 1-q 3) (q 1-q 3))]

def permutations : Fin 6 → Fin 3 → Fin 3 :=
  ![![0,1,2],![1,2,0],![2,0,1],![0,2,1],![1,0,2],![2,1,0]]
def frames : Fin 4 → Fin 3 → Fin 9 := ![![0,1,2],![0,7,8],![1,5,6],![2,3,4]]
def fullImages (frame : Fin 4) (order : Fin 6) : Fin 4 → Signature Scalar 4 :=
  ![tensorScale (rat (1/2)) cTensor,
    regular (frames frame (permutations order 0)),
    regular (frames frame (permutations order 1)),
    regular (frames frame (permutations order 2))]
def deficientImages (order : Fin 6) : Fin 4 → Signature Scalar 4 :=
  Fin.cons (tensorScale (rat (1/2)) cTensor)
    (fun j => ![0,tensorScale (rat (1/2)) aTensor,tensorScale (rat (1/2)) bTensor]
      (permutations order j))
def dual (μ : Fin 4) : Mat := ms (if μ=1 ∨ μ=3 then rat (-1/2) else rat (1/2)) (q μ)
def reconstruct (F : Fin 4 → Signature Scalar 4) : Signature Scalar 6 := fun x =>
  ∑ μ : Fin 4, dual μ (x 0) (x 1)*F μ (fun j => x j.succ.succ)
def firstKernel : Mat := q 0+q 1
def regularCard (r : Fin 9) : Signature Scalar 4 := tensorScale (rat (1/2)) cTensor+regular r
def deficientCard (p : Fin 6) : Signature Scalar 4 :=
  Signature.contract (q 0)
    (Tensor.reindex (Holant.Certificates.TetrahedralDeck.portOrder 1).symm
      (reconstruct (deficientImages p)))
def baseCard : Fin 15 → Signature Scalar 4 := Fin.addCases (m := 9) (n := 6) (motive := fun _ : Fin 15 => Signature Scalar 4) regularCard deficientCard

def sixLegs (f : Form) : Fin 6 → Mat :=
  ![mt (conjugator f),inverseConjugator f,inverseConjugator f,
    mt (conjugator f),inverseConjugator f,mt (conjugator f)]
def fullAncestor (f : Form) (frame : Fin 4) (order : Fin 6) : Signature Scalar 6 :=
  Signature.coordinateAction (sixLegs f) (reconstruct (fullImages frame order))
def deficientAncestor (f : Form) (order : Fin 6) : Signature Scalar 6 :=
  Signature.coordinateAction (sixLegs f) (reconstruct (deficientImages order))
def coefficientCard (f : Form) (r : Fin 15) : Signature Scalar 4 :=
  Signature.coordinateAction (coefficientLegs f) (baseCard r)
def correctedCard (f : Form) (r : Fin 15) : Signature Scalar 4 :=
  Signature.coordinateAction (fun _ => inverseConjugator f) (baseCard r)

def admissible (f : Form) (r : Fin 15) : Prop := r.val<9 ∨ 2≤f.val
instance (f : Form) (r : Fin 15) : Decidable (admissible f r) := by unfold admissible; infer_instance

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

theorem four_frames_sum : ∀ frame : Fin 4,
    regular (frames frame 0)+regular (frames frame 1)+regular (frames frame 2) =
      tensorScale (rat (1/2)) (aTensor+bTensor) := by decide +kernel

theorem ordered_cases_count : Fintype.card (Form × Fin 4 × Fin 6)+
    Fintype.card (Fin 2 × Fin 6)=108 := by decide

theorem direct_rows_count : (Finset.univ.filter (fun p : Form × Fin 15 => admissible p.1 p.2)).card=48 := by decide

end Holant.Certificates.OctahedralSeparator
