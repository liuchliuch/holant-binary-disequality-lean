import Holant.Complexity.EdgeSubdivision.Raw

/-! The target family retains every original label and appends exactly the old
edge matrices as binary vertex labels. There are no new coefficient constants. -/
namespace Holant.Complexity.EdgeSubdivision
variable {K : Type*} {s b : ℕ} {arity : ℕ → ℕ}

def extendedSignatures
    (source : (i : Fin s) → Signature K (arity i.val))
    (binary : Fin b → Bool → Bool → K) :
    (i : Fin (s+b)) → Signature K (targetArity s arity i.val) :=
  fun i x => if h : i.val<s then
    source ⟨i.val,h⟩ (fun j => x (Fin.cast (by simp [targetArity,h]) j))
  else
    binary ⟨i.val-s,by have hi := i.isLt; omega⟩
      (x (Fin.cast (by simp [targetArity,h]) (0 : Fin 2)))
      (x (Fin.cast (by simp [targetArity,h]) (1 : Fin 2)))

theorem extendedSignatures_old
    (source : (i : Fin s) → Signature K (arity i.val))
    (binary : Fin b → Bool → Bool → K) (i : Fin s)
    (x : Fin (targetArity s arity i.val) → Bool) :
    extendedSignatures source binary (Fin.castAdd b i) x =
      source i (fun j => x (Fin.cast (by simp [targetArity,i.isLt]) j)) := by
  simp [extendedSignatures,i.isLt]

theorem extendedSignatures_new
    (source : (i : Fin s) → Signature K (arity i.val))
    (binary : Fin b → Bool → Bool → K) (j : Fin b)
    (x : Fin (targetArity s arity (s+j.val)) → Bool) :
    extendedSignatures source binary (Fin.natAdd s j) x =
      binary j (x (Fin.cast (by simp [targetArity]) (0 : Fin 2)))
        (x (Fin.cast (by simp [targetArity]) (1 : Fin 2))) := by
  simp [extendedSignatures]

theorem signature_cast_heq {m n : ℕ} (h : m=n) (f : Signature K m) :
    HEq (fun x : Fin n → Bool => f (fun i => x (Fin.cast h i))) f := by
  cases h
  rfl

theorem extendedSignatures_old_heq
    (source : (i : Fin s) → Signature K (arity i.val))
    (binary : Fin b → Bool → Bool → K) (i : Fin s) :
    HEq (extendedSignatures source binary (Fin.castAdd b i)) (source i) := by
  exact (heq_of_eq (funext (extendedSignatures_old source binary i))).trans
    (signature_cast_heq (by simp [targetArity,i.isLt]) (source i))

theorem extendedSignatures_new_heq
    (source : (i : Fin s) → Signature K (arity i.val))
    (binary : Fin b → Bool → Bool → K) (j : Fin b) :
    HEq (extendedSignatures source binary (Fin.natAdd s j))
      (fun x : Fin 2 → Bool => binary j (x 0) (x 1)) := by
  exact (heq_of_eq (funext (extendedSignatures_new source binary j))).trans
    (signature_cast_heq (by simp [targetArity])
      (fun x : Fin 2 → Bool => binary j (x 0) (x 1)))

end Holant.Complexity.EdgeSubdivision
