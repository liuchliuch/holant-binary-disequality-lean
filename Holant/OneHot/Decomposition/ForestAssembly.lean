import Holant.OneHot.NetworkBridge

/-! Assemble an ordered forest from a finite family, with exact node addresses. -/

set_option backward.isDefEq.respectTransparency false

namespace Holant.OneHot.Decomposition

/-- The explicit first/rest partition of a dependent finite family. -/
def sigmaFinSucc {n : ℕ} (P : Fin (n + 1) → Type*) :
    (Σ i, P i) ≃ (P 0 ⊕ Σ i : Fin n, P i.succ) where
  toFun p := Fin.cases (fun x => .inl x) (fun i x => .inr ⟨i, x⟩) p.1 p.2
  invFun p := match p with
    | .inl x => ⟨0, x⟩
    | .inr ⟨i, x⟩ => ⟨i.succ, x⟩
  left_inv p := by
    rcases p with ⟨i, x⟩
    cases i using Fin.cases <;> rfl
  right_inv p := by cases p <;> rfl

end Holant.OneHot.Decomposition

namespace Holant.OneHot.Forest

variable {K : Type*}

/-- An ordered forest with one actual child for each index, in index order. -/
def ofFn : {n : ℕ} → (Fin n → K) → (Fin n → Tree K) → Forest K
  | 0, _, _ => .nil
  | n + 1, b, ts => .cons (b 0) (ts 0) (ofFn (fun i : Fin n => b i.succ)
      (fun i : Fin n => ts i.succ))

/-- Every actual child-tree vertex appears exactly once in the assembled forest. -/
def ofFnVertex : {n : ℕ} → (b : Fin n → K) → (ts : Fin n → Tree K) →
    (ofFn b ts).Vertex ≃ (Σ i, (ts i).Vertex)
  | 0, _, _ => {
      toFun := Empty.elim
      invFun := fun p => Fin.elim0 p.1
      left_inv := fun p => Empty.elim p
      right_inv := fun p => Fin.elim0 p.1 }
  | n + 1, b, ts =>
      (Equiv.sumCongr (Equiv.refl _) (ofFnVertex (fun i : Fin n => b i.succ)
        (fun i : Fin n => ts i.succ))).trans
          (Decomposition.sigmaFinSucc (fun i => (ts i).Vertex)).symm

@[simp] theorem length_ofFn {n : ℕ} (b : Fin n → K) (ts : Fin n → Tree K) :
    (ofFn b ts).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [ofFn, length, ih]

/-- Child singleton coefficients preserve the enumeration's exact order. -/
theorem coefficients_ofFn {n : ℕ} (b : Fin n → K) (ts : Fin n → Tree K)
    (i : Fin (ofFn b ts).length) :
    (ofFn b ts).coefficients i = b (Fin.cast (length_ofFn b ts) i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      change (ofFn (fun i : Fin n => b i.succ) (fun i : Fin n => ts i.succ)).coefficients i = _
      rw [ih]
      rfl

/-- The assembled node keeps its child tree's original zero-word coefficient. -/
theorem zeroCoefficient_ofFn {n : ℕ} (b : Fin n → K) (ts : Fin n → Tree K)
    (x : (ofFn b ts).Vertex) :
    (ofFn b ts).zeroCoefficient x =
      (ts ((ofFnVertex b ts) x).1).zeroCoefficient ((ofFnVertex b ts) x).2 := by
  induction n with
  | zero => exact Empty.elim x
  | succ n ih =>
    rcases x with x | x
    · rfl
    · exact ih (fun i => b i.succ) (fun i => ts i.succ) x

/-- Local arity is unchanged when child node addresses are assembled. -/
theorem arity_ofFn {n : ℕ} (b : Fin n → K) (ts : Fin n → Tree K)
    (x : (ofFn b ts).Vertex) :
    (ofFn b ts).arity x = (ts ((ofFnVertex b ts) x).1).arity ((ofFnVertex b ts) x).2 := by
  induction n with
  | zero => exact Empty.elim x
  | succ n ih =>
    rcases x with x | x
    · rfl
    · exact ih (fun i => b i.succ) (fun i => ts i.succ) x

/-- Every internal ordered port coefficient is unchanged by forest assembly. -/
theorem portCoefficient_ofFn {n : ℕ} (b : Fin n → K) (ts : Fin n → Tree K)
    (x : (ofFn b ts).Vertex) (i : Fin ((ofFn b ts).arity x)) :
    (ofFn b ts).portCoefficient x i =
      (ts ((ofFnVertex b ts) x).1).portCoefficient ((ofFnVertex b ts) x).2
        (Fin.cast (arity_ofFn b ts x) i) := by
  induction n with
  | zero => exact Empty.elim x
  | succ n ih =>
    rcases x with x | x
    · rfl
    · exact ih (fun i => b i.succ) (fun i => ts i.succ) x i

end Holant.OneHot.Forest
