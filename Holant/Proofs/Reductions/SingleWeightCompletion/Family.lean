import Holant.Proofs.Reductions.SingleWeightCompletion.OrderedPins


noncomputable section
namespace Holant.LocalDrafts.Hardness.SingleWeightCompletion
open Holant.Tractable
variable {K : Type} [Field K] {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature K (a i.val)) (d : Fin s → ℕ)

def sourceFamily : SignatureFamily K := Set.range (fun i => (⟨a i.val,G i⟩ : AnySignature K))
def arity (j : ℕ) : ℕ := a j + if hj : j < s then extra (a j) (d ⟨j,hj⟩) else 0
def table (i : Fin s) : Signature K (arity (a:=a) d i.val) := by
  rw [arity,dif_pos i.isLt]
  exact completed (G i) (d i)
def label (i : Fin s) : AnySignature K := Signature.completeToEO (G i) (d i)
theorem table_label (i : Fin s) : (⟨arity (a:=a) d i.val,table G d i⟩ : AnySignature K) = label G d i := by
  have ha : arity (a:=a) d i.val = a i.val + extra (a i.val) (d i) := by
    simp only [arity,dite_eq_left i.isLt]
  have hmpr {α β : Type} (h : α=β) (x : β) : HEq (h.mpr x) x := by
    cases h
    rfl
  have ht : HEq (table G d i) (completed (G i) (d i)) := by
    unfold table
    apply HEq.trans (hmpr _ _)
    exact hmpr _ _
  simpa only [label] using (Sigma.ext ha ht).trans (completed_exact (G i) (d i))
theorem table_nonzero (i : Fin s) : table G d i ≠ 0 ↔ G i ≠ 0 := by
  have he := (table_label G d i).trans (completed_exact (G i) (d i)).symm
  rw [congrArg (fun f : AnySignature K => f.2≠0) he]
  exact completed_nonzero_iff (G i) (d i)
theorem table_central (h : ∀ i, Signature.SingleLayer (G i) (d i)) (i : Fin s) :
    Signature.CentralSupport (table G d i) := by
  have he := (table_label G d i).trans (completed_exact (G i) (d i)).symm
  exact (congrArg (fun f : AnySignature K => Signature.CentralSupport f.2) he).mpr
    (completed_central (G i) (d i) (h i))
include G in
theorem table_even (i : Fin s) : ∃ k, arity (a:=a) d i.val = 2*k := by
  have ha : arity (a:=a) d i.val = a i.val + extra (a i.val) (d i) := by
    simp only [arity,dite_eq_left i.isLt]
  obtain ⟨k,hk⟩ := completed_even (G i) (d i)
  exact ⟨k,ha.trans hk⟩

variable (A : (i : Fin s) → Signature AlgebraicComplex (a i.val))
theorem nonzero_image (h : ∀ i, Signature.SingleLayer (A i) (d i)) :
    Set.range (fun i : {i : Fin s // A i ≠ 0} => label A d i.val) = completionFamily (sourceFamily A) := by
  ext f
  constructor
  · rintro ⟨⟨i,hi⟩,rfl⟩
    exact ⟨⟨a i.val,A i⟩,⟨i,rfl⟩,hi,d i,h i,rfl⟩
  · rintro ⟨g,⟨i,rfl⟩,hi,e,he,rfl⟩
    have hd : e = d i := Signature.singleLayer_unique hi he (h i)
    subst e
    exact ⟨⟨i,hi⟩,rfl⟩

end Holant.LocalDrafts.Hardness.SingleWeightCompletion
