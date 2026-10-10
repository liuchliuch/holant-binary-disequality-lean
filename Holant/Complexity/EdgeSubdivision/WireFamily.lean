import Holant.Complexity.EdgeSubdivision.WireSize
import Holant.Realization

/-! The extra label is exactly the literal binary, with all original signatures
unchanged. Coincident signatures and the empty original family are included. -/
namespace Holant.Complexity.EdgeSubdivision
variable {K : Type*} {s : ℕ} {arity : ℕ → ℕ}

theorem extended_family
    (source : (i : Fin s) → Signature K (arity i.val)) (B : Bool → Bool → K) :
    Set.range (fun i : Fin (s+1) =>
      (⟨targetArity s arity i.val,extendedSignatures source (fun _ : Fin 1 => B) i⟩ : AnySignature K)) =
    Set.range (fun i : Fin s => (⟨arity i.val,source i⟩ : AnySignature K)) ∪
      {(⟨2,fun x => B (x 0) (x 1)⟩ : AnySignature K)} := by
  ext f
  constructor
  · rintro ⟨i,rfl⟩
    by_cases hi : i.val<s
    · left
      refine ⟨⟨i.val,hi⟩,?_⟩
      exact (Sigma.ext (by simp [targetArity,hi])
        (extendedSignatures_old_heq source (fun _ : Fin 1 => B) ⟨i.val,hi⟩)).symm
    · right
      have hv : i.val=s := by have hb := i.isLt; omega
      have hie : i=Fin.natAdd s (0 : Fin 1) := Fin.ext hv
      rw [hie]
      exact Sigma.ext (by simp [targetArity])
        (extendedSignatures_new_heq source (fun _ : Fin 1 => B) (0 : Fin 1))
  · intro h
    rcases h with ⟨i,rfl⟩ | h
    · refine ⟨Fin.castAdd 1 i,?_⟩
      exact Sigma.ext (by simp [targetArity,i.isLt])
        (extendedSignatures_old_heq source (fun _ : Fin 1 => B) i)
    · change f=(⟨2,fun x => B (x 0) (x 1)⟩ : AnySignature K) at h
      subst f
      refine ⟨Fin.natAdd s (0 : Fin 1),?_⟩
      exact Sigma.ext (by simp [targetArity])
        (extendedSignatures_new_heq source (fun _ : Fin 1 => B) (0 : Fin 1))

theorem kernel_false [CommSemiring K] : WirePath.kernel (K:=K) false=Signature.equality := by
  funext a b
  cases a <;> cases b <;> rfl

theorem kernel_true [CommSemiring K] : WirePath.kernel (K:=K) true=Signature.disequality := by
  funext a b
  cases a <;> cases b <;> rfl

end Holant.Complexity.EdgeSubdivision
