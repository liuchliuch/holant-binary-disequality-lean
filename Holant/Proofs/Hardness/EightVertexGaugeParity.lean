import Holant.Proofs.Hardness.EightVertexGaugePorts
import Holant.Certificates.EqualityQuaternary.MonomialDeck

/-! Parity provenance of the actual gauge escape. Every tested two-row
output is even, and the final representative cap is monomial. Consequently
the escaping binary has one fixed parity. A singular nonzero such binary
has exactly one supported entry, with its original coefficient retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeParity
open Holant Holant.Tractable Holant.Marked Holant.Marked.SupportAtlas
open Holant.Certificates.EqualityQuaternary
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseResidualGaugeCore
open EightVertexGaugePorts EightVertexGaugeTwoRowAlgebra

def BinaryParity {K : Type*} [Zero K] (B : Bool → Bool → K) : Prop :=
  (B false true = 0 ∧ B true false = 0) ∨
    (B false false = 0 ∧ B true true = 0)

def OneHot {K : Type*} [Zero K] (B : Bool → Bool → K) : Prop :=
  ∃ a b, B a b ≠ 0 ∧ ∀ c d, c ≠ a ∨ d ≠ b → B c d = 0

theorem table_even {K : Type*} [Zero K] (v : Entries K) : EvenSupport (table v) := by
  intro x hx
  rw [word_eta x] at hx ⊢
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  all_goals simp only [h0,h1,h2,h3] at hx ⊢
  all_goals first | rfl | exact False.elim (hx (by decide))

theorem onPorts_even (a b : AlgebraicComplex) (u v : Fin 4 → AlgebraicComplex)
    (e f : Equiv.Perm (Fin 4)) (cross : Bool) :
    EvenSupport (EightVertexGaugeTwoRowNetwork.onPorts
      (weighted a u) (weighted b v) e f cross).denote := by
  rw [onPorts_output]
  exact table_even _

theorem reorder_even (q : Signature AlgebraicComplex 4) (hq : EvenSupport q)
    (e : Equiv.Perm (Fin 4)) : EvenSupport (reorder q e) := by
  intro x hx
  apply hq
  have weightEq : weight (permuteWord e x) = weight x :=
    Equiv.sum_comp e.symm (fun i => if x i then 1 else 0)
  simpa only [weightEq] using hx

theorem physical_card_parity {m : ℕ} (F : SignatureFamily AlgebraicComplex)
    (reps : MonomialRepresentatives F m) (q : Signature AlgebraicComplex 4)
    (hq : EvenSupport q) (e : Equiv.Perm (Fin 4)) (p : Bool) (t : Phase m) :
    BinaryParity (physicalCard q e (reps.matrix p t)) := by
  have hr := reorder_even q hq e
  have h1 := hr ![false,false,false,true] (by decide)
  have h2 := hr ![false,false,true,false] (by decide)
  have h3 := hr ![false,true,false,false] (by decide)
  have h4 := hr ![false,true,true,true] (by decide)
  have h5 := hr ![true,false,false,false] (by decide)
  have h6 := hr ![true,false,true,true] (by decide)
  have h7 := hr ![true,true,false,true] (by decide)
  have h8 := hr ![true,true,true,false] (by decide)
  rw [reps.normal_form]
  cases p
  · left
    constructor <;> simp [physicalCard,contract0,Kernel.mul_apply,
      Signature.disequality,scale,standard,R,diagonalKernel,h1,h2,h7,h8]
  · right
    constructor <;> simp [physicalCard,contract0,Kernel.mul_apply,
      Signature.disequality,scale,standard,S,R,diagonalKernel,h3,h4,h5,h6]

theorem singular_oneHot {K : Type*} [Field K] (B : Matrix Bool Bool K)
    (parity : BinaryParity B) (nonzero : B ≠ 0) (singular : Matrix.det B = 0) : OneHot B := by
  have det := singular
  have formula : Matrix.det B = B false false * B true true - B false true * B true false := by
    rw [← Matrix.det_reindex_self finTwoEquiv.symm B,Matrix.det_fin_two]
    rfl
  rw [formula] at det
  rcases parity with ⟨off01,off10⟩ | ⟨diag00,diag11⟩
  · have product : B false false * B true true = 0 := by simpa [off01,off10] using det
    rcases mul_eq_zero.mp product with h0 | h1
    · have live : B true true ≠ 0 := by
        intro hz
        apply nonzero
        ext a b
        cases a <;> cases b <;> simp [h0,hz,off01,off10]
      refine ⟨true,true,live,?_⟩
      intro a b h
      cases a <;> cases b <;> simp_all
    · have live : B false false ≠ 0 := by
        intro hz
        apply nonzero
        ext a b
        cases a <;> cases b <;> simp [h1,hz,off01,off10]
      refine ⟨false,false,live,?_⟩
      intro a b h
      cases a <;> cases b <;> simp_all
  · have product : B false true * B true false = 0 := by
      simpa [diag00,diag11] using det
    rcases mul_eq_zero.mp product with h0 | h1
    · have live : B true false ≠ 0 := by
        intro hz
        apply nonzero
        ext a b
        cases a <;> cases b <;> simp [h0,hz,diag00,diag11]
      refine ⟨true,false,live,?_⟩
      intro a b h
      cases a <;> cases b <;> simp_all
    · have live : B false true ≠ 0 := by
        intro hz
        apply nonzero
        ext a b
        cases a <;> cases b <;> simp [h1,hz,diag00,diag11]
      refine ⟨false,true,live,?_⟩
      intro a b h
      cases a <;> cases b <;> simp_all

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeParity
end
