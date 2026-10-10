import Holant.NetworkGluing.Finite
import Holant.OrderedTensor
import Mathlib.Tactic.Ring


namespace Holant.LocalDrafts.Hardness.GeneralExtraction.Carrier

open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

variable {O E K : Type*} {m n p r : ℕ}

abbrev OldVertex (O : Type*) (p r : ℕ) := O ⊕ (Fin p ⊕ (Fin p ⊕ Fin r))
abbrev NewVertex (O : Type*) (p r : ℕ) := O ⊕ (Fin p ⊕ Fin r)

def oldArity (a : O → ℕ) (m n : ℕ) : OldVertex O p r → ℕ :=
  Sum.elim a (Sum.elim (fun _ => m) (fun _ => n))

def newArity (a : O → ℕ) (m n : ℕ) : NewVertex O p r → ℕ :=
  Sum.elim a (fun _ => m + n)

abbrev OldPort (a : O → ℕ) (m n p r : ℕ) :=
  Σ v : OldVertex O p r, Fin (oldArity a m n v)

abbrev NewPort (a : O → ℕ) (m n p r : ℕ) :=
  Σ v : NewVertex O p r, Fin (newArity a m n v)

/-- Exactly one source incidence for each old port and each fresh f port. -/
def splitPort (a : O → ℕ) :
    NewPort a m n p r → (Fin r × Fin m) ⊕ OldPort a m n p r
  | ⟨.inl o, i⟩ => .inr ⟨.inl o, i⟩
  | ⟨.inr (.inl j), i⟩ =>
      match finSumFinEquiv.symm i with
      | .inl k => .inr ⟨.inr (.inl j), k⟩
      | .inr k => .inr ⟨.inr (.inr (.inl j)), k⟩
  | ⟨.inr (.inr j), i⟩ =>
      match finSumFinEquiv.symm i with
      | .inl k => .inl (j, k)
      | .inr k => .inr ⟨.inr (.inr (.inr j)), k⟩

def joinPort (a : O → ℕ) :
    (Fin r × Fin m) ⊕ OldPort a m n p r → NewPort a m n p r
  | .inl (j, i) => ⟨.inr (.inr j), finSumFinEquiv (.inl i)⟩
  | .inr ⟨.inl o, i⟩ => ⟨.inl o, i⟩
  | .inr ⟨.inr (.inl j), i⟩ => ⟨.inr (.inl j), finSumFinEquiv (.inl i)⟩
  | .inr ⟨.inr (.inr (.inl j)), i⟩ =>
      ⟨.inr (.inl j), finSumFinEquiv (.inr i)⟩
  | .inr ⟨.inr (.inr (.inr j)), i⟩ =>
      ⟨.inr (.inr j), finSumFinEquiv (.inr i)⟩

def portSplit (a : O → ℕ) :
    NewPort a m n p r ≃ (Fin r × Fin m) ⊕ OldPort a m n p r where
  toFun := splitPort a
  invFun := joinPort a
  left_inv := by
    rintro ⟨o | (j | j), i⟩
    · rfl
    · obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
      cases i <;> simp [splitPort, joinPort]
    · obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
      cases i <;> simp [splitPort, joinPort]
  right_inv := by
    rintro (⟨j, i⟩ | ⟨o | (j | (j | j)), i⟩) <;>
      simp [splitPort, joinPort]

/-- A closed carrier's full incidence, including loops and parallel edges.
There are no extra unlabelled equality vertices or pinning resources. -/
structure Wiring (a : O → ℕ) (m n p r : ℕ) (E : Type*) where
  ends : OldPort a m n p r ≃ E × Bool

def closedBoundary (E : Type*) : E × Bool ≃ Fin 0 ⊕ (E × Bool) where
  toFun := Sum.inr
  invFun := Sum.elim Fin.elim0 id
  left_inv := fun _ => rfl
  right_inv := by
    intro q
    cases q with
    | inl i => exact Fin.elim0 i
    | inr q => rfl

def original (a : O → ℕ) (W : Wiring a m n p r E)
    (background : (o : O) → Signature K (a o))
    (f : Signature K m) (g : Signature K n)
    (edge : E → Bool → Bool → K) :
    FiniteNetwork K (OldVertex O p r) E 0 where
  arity := oldArity a m n
  ports := W.ends.trans (closedBoundary E)
  vertex := fun v => match v with
    | .inl o => background o
    | .inr (.inl _) => f
    | .inr (.inr _) => g
  edge := edge

def extracted [Mul K] (a : O → ℕ) (W : Wiring a m n p r E)
    (background : (o : O) → Signature K (a o))
    (f : Signature K m) (g : Signature K n)
    (edge : E → Bool → Bool → K) :
    FiniteNetwork K (NewVertex O p r) E (r * m) where
  arity := newArity a m n
  ports := (portSplit a).trans
    (Equiv.sumCongr finProdFinEquiv W.ends)
  vertex := fun v => match v with
    | .inl o => background o
    | .inr _ => Signature.tensor f g
  edge := edge

/-- The ordering is copy-major, then the original ordered f port. -/
def blockPower [CommMonoid K] (f : Signature K m) (r : ℕ) : Signature K (r * m) :=
  fun x => ∏ j : Fin r, f (fun i => x (finProdFinEquiv (j, i)))

/-- The extraction application requires a genuine positive surplus. The
zero-surplus graph identity is still valid, but only exposes a nullary unit. -/
theorem positive_surplus (hr : 0 < r) : p < p + r := Nat.lt_add_of_pos_right hr

theorem blockPower_one [CommMonoid K] (f : Signature K m) (x : Fin (1 * m) → Bool) :
    blockPower f 1 x = f (fun i => x (finProdFinEquiv (0, i))) := by
  simp [blockPower]

def blockPivot (x : Fin m → Bool) (r : ℕ) : Fin (r * m) → Bool :=
  fun i => x (finProdFinEquiv.symm i).2

theorem blockPower_pivot [CommMonoid K] (f : Signature K m)
    (x : Fin m → Bool) : blockPower f r (blockPivot x r) = f x ^ r := by
  simp [blockPower, blockPivot]

theorem blockPower_pivot_nonzero [CommMonoidWithZero K] [Nontrivial K]
    [NoZeroDivisors K] (f : Signature K m) (x : Fin m → Bool) (hx : f x ≠ 0) :
    blockPower f r (blockPivot x r) ≠ 0 := by
  rw [blockPower_pivot]
  exact pow_ne_zero r hx

variable [Fintype O] [Fintype E] [CommSemiring K]

/-- Equality of actual finite assignment sums. No nonzero assumption is used
in constructing the graph or proving its semantics. -/
theorem extracted_denote (a : O → ℕ) (W : Wiring a m n p r E)
    (background : (o : O) → Signature K (a o))
    (f : Signature K m) (g : Signature K n)
    (edge : E → Bool → Bool → K) (x : Fin (r * m) → Bool) :
    (extracted a W background f g edge).denote x =
      (original a W background f g edge).denote Fin.elim0 * blockPower f r x := by
  classical
  unfold FiniteNetwork.denote
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  simp only [extracted, original, Fintype.prod_sum_type, Signature.tensor_apply,
    newArity, oldArity, Equiv.trans_apply, Equiv.sumCongr_apply,
    portSplit, splitPort, closedBoundary, Equiv.coe_fn_mk, Sum.elim_inl, Sum.elim_inr,
    Equiv.symm_apply_apply, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd,
    Finset.prod_mul_distrib, blockPower, Sum.map_inl, Sum.map_inr]
  ac_rfl

/-- Conversion is to the repository's ordinary ordered-port graph model. -/
theorem extracted_network_denote (a : O → ℕ) (W : Wiring a m n p r E)
    (background : (o : O) → Signature K (a o))
    (f : Signature K m) (g : Signature K n)
    (edge : E → Bool → Bool → K) (x : Fin (r * m) → Bool) :
    (extracted a W background f g edge).toNetwork.denote x =
      (original a W background f g edge).toNetwork.denote Fin.elim0 *
        blockPower f r x := by
  rw [FiniteNetwork.denote_toNetwork, FiniteNetwork.denote_toNetwork]
  exact extracted_denote a W background f g edge x

theorem extracted_vertex_count (a : O → ℕ) (W : Wiring a m n p r E)
    (background : (o : O) → Signature K (a o))
    (f : Signature K m) (g : Signature K n) (edge : E → Bool → Bool → K) :
    (extracted a W background f g edge).toNetwork.shape.vertices =
      Fintype.card O + p + r := by
  simp [FiniteNetwork.toNetwork, NewVertex, Nat.add_assoc]

theorem extracted_edge_count (a : O → ℕ) (W : Wiring a m n p r E)
    (background : (o : O) → Signature K (a o))
    (f : Signature K m) (g : Signature K n) (edge : E → Bool → Bool → K) :
    (extracted a W background f g edge).toNetwork.shape.edges = Fintype.card E := rfl

end Holant.LocalDrafts.Hardness.GeneralExtraction.Carrier
