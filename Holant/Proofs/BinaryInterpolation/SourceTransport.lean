import Holant.Proofs.BinaryInterpolation.SourceCapstone
import Holant.Proofs.BinaryInterpolation.SingularExtraction.SourceReduction
import Holant.Proofs.Algorithms.RingHomRealization
import Holant.Projective.BoundedTorsion.DeterminantOne
import Holant.Projective.BoundedTorsion.ActualTransfers


noncomputable section
namespace Holant.LocalDrafts.BinaryInterpolation.SourceTransport
open Holant Holant.Tractable Holant.Complexity Holant.Complexity.BinaryInterpolation
open Holant.Certificates.MatchingContractionClosure Holant.Projective.BoundedTorsion
namespace RH
export Holant.LocalDrafts.MainChain.RingHomRealization
  (mapSignature mapAny mapFamily realizes_map)
end RH
set_option backward.isDefEq.respectTransparency false

def inclusion : AlgebraicComplex →+* ℂ := (algebraicClosure ℚ ℂ).subtype

variable {s : ℕ} {arity : ℕ → ℕ}
def family (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val)) :
    (i : Fin s) → Signature ℂ (arity i.val) := fun i x => inclusion (G i x)
def binary (B : Binary (K:=AlgebraicComplex)) : Binary (K:=ℂ) := B.map inclusion

theorem family_algebraic (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
    (i : Fin s) (x : Fin (arity i.val) → Bool) : IsAlgebraic ℚ (family G i x) :=
  (G i x).property.isAlgebraic

theorem family_finite (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val)) :
    (Set.range (fun i => (⟨arity i.val,G i⟩ : AnySignature AlgebraicComplex))).Finite :=
  Set.finite_range _

theorem family_image (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val)) :
    RH.mapFamily inclusion (Set.range (fun i => (⟨arity i.val,G i⟩ : AnySignature AlgebraicComplex))) =
      Set.range (fun i => (⟨arity i.val,family G i⟩ : AnySignature ℂ)) := by
  ext f
  constructor
  · rintro ⟨g,⟨i,rfl⟩,rfl⟩
    exact ⟨i,rfl⟩
  · rintro ⟨i,rfl⟩
    exact ⟨⟨arity i.val,G i⟩,⟨i,rfl⟩,rfl⟩

theorem realizes (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
    (B : Binary (K:=AlgebraicComplex))
    (h : Gadget.Realizes (Set.range (fun i => (⟨arity i.val,G i⟩ : AnySignature AlgebraicComplex)))
      .disequality (Chains.binarySignature B)) :
    Gadget.Realizes (Set.range (fun i => (⟨arity i.val,family G i⟩ : AnySignature ℂ)))
      .disequality (Chains.binarySignature (binary B)) := by
  have hm := RH.realizes_map inclusion h
  rw [family_image] at hm
  exact hm

theorem binary_nonzero (B : Binary (K:=AlgebraicComplex)) (hB : B ≠ 0) : binary B ≠ 0 := by
  intro h
  apply hB
  apply Matrix.ext
  intro i j
  apply inclusion.injective
  simpa [binary] using congrFun₂ h i j

theorem map_X : (X : Binary (K:=AlgebraicComplex)).map inclusion = X := by
  ext a b
  cases a <;> cases b <;> rfl

theorem transfer_map (B : Binary (K:=AlgebraicComplex)) :
    binary (B*X) = binary B*X := by rw [binary, Matrix.map_mul, map_X]; rfl

theorem determinant_map (B : Binary (K:=AlgebraicComplex)) :
    Matrix.det (binary B) = inclusion (Matrix.det B) := by
  rw [det_entries, det_entries]
  simp [binary, Matrix.map_apply]

theorem transfer_det_nonzero (B : Binary (K:=AlgebraicComplex)) (h : Matrix.det (B*X) ≠ 0) :
    Matrix.det (binary B*X) ≠ 0 := by
  rw [← transfer_map, determinant_map]
  exact fun hz => h (inclusion.injective (hz.trans inclusion.map_zero.symm))

/-- Reflection needs no algebraicity premise on an externally supplied scalar:
the diagonal entry of A^r is already in the smaller field. -/
theorem projectivelyFinite_map_iff {K L : Type*} [Field K] [Field L]
    (φ : K →+* L) (A : Binary (K:=K)) : ProjectivelyFinite (A.map φ) ↔ ProjectivelyFinite A := by
  constructor
  · rintro ⟨r,hr,c,hc,hp⟩
    have hd : φ ((A^r) false false) = c := by
      have h := congrFun₂ hp false false
      rw [← Matrix.map_pow] at h
      simpa using h
    refine ⟨r,hr,(A^r) false false,?_,?_⟩
    · intro hz
      apply hc
      rw [← hd,hz,map_zero]
    · ext i j
      apply φ.injective
      have h := congrFun₂ hp i j
      rw [← Matrix.map_pow] at h
      cases i <;> cases j <;> simpa [hd] using h
  · intro h
    exact h.map φ

theorem transfer_infinite (B : Binary (K:=AlgebraicComplex)) (h : ¬ ProjectivelyFinite (B*X)) :
    ¬ ProjectivelyFinite (binary B*X) := by
  rw [← transfer_map]
  exact fun hf => h ((projectivelyFinite_map_iff inclusion (B*X)).mp hf)

theorem closed_value (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
    (q : ExactSignatureTables.Input s 1 arity) :
    inclusion ((q.val.realize q.property G (fun _ => Signature.disequality)).denote Fin.elim0) =
      (q.val.realize q.property (family G) (fun _ => Signature.disequality)).denote Fin.elim0 := by
  rw [← Network.denote_map]
  congr 1
  unfold Network.map RawClosedNetwork.realize family
  congr 1
  funext e a b
  cases a <;> cases b <;> rfl

end Holant.LocalDrafts.BinaryInterpolation.SourceTransport
