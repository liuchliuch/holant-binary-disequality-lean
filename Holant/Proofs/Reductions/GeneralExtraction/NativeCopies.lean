import Holant.Proofs.Reductions.GeneralExtraction.BinaryCarrier


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.GeneralExtraction.NativeCopies
open NamedContraction SupportDescent
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction

variable {K : Type*} [Field K] {n m : ℕ}

theorem tensor_uses (F : SignatureFamily K) (L : Network K n) (R : Network K m)
    (hL : Uses L F) (hR : Uses R F) : Uses (L.tensor R) F := by
  intro v
  change (⟨_, (Network.tensorFinite L R).vertex
    ((Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm v)⟩ : AnySignature K) ∈ F
  cases (Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm v with
  | inl v => exact hL v
  | inr v => exact hR v

theorem tensor_native (L : Network K n) (R : Network K m)
    (hL : Native L) (hR : Native R) : Native (L.tensor R) := by
  intro e
  change (Network.tensorFinite L R).edge
    ((Fintype.equivFin (Fin L.shape.edges ⊕ Fin R.shape.edges)).symm e) = _
  cases (Fintype.equivFin (Fin L.shape.edges ⊕ Fin R.shape.edges)).symm e with
  | inl e => exact hL e
  | inr e => exact hR e

def appendWord (x : Fin n → Bool) (y : Fin m → Bool) : Fin (n + m) → Bool :=
  Fin.addCases x y

theorem balance_append (b : Bool) (x : Fin n → Bool) (y : Fin m → Bool) :
    balance b (appendWord x y) = balance b x + balance b y := by
  simp [balance, appendWord, Fin.sum_univ_add]

theorem tensor_word (L : Network K n) (R : Network K m)
    (x : Fin n → Bool) (y : Fin m → Bool) :
    (L.tensor R).denote (appendWord x y) = L.denote x * R.denote y := by
  simp [Network.denote_tensor, Signature.tensor_apply, appendWord]

def copyArity (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 => n + copyArity n r

def copies (N : Network K n) : (r : ℕ) → Network K (copyArity n r)
  | 0 => Network.empty
  | r + 1 => N.tensor (copies N r)

def copyWord (x : Fin n → Bool) : (r : ℕ) → Fin (copyArity n r) → Bool
  | 0 => Fin.elim0
  | r + 1 => appendWord x (copyWord x r)

theorem copyArity_eq (n r : ℕ) : copyArity n r = r * n := by
  induction r <;> simp [copyArity, *, Nat.succ_mul, Nat.add_comm]

theorem copies_uses (F : SignatureFamily K) (N : Network K n) (h : Uses N F) (r : ℕ) :
    Uses (copies N r) F := by
  induction r with
  | zero => intro v; exact Fin.elim0 v
  | succ r ih => exact tensor_uses F N (copies N r) h ih

theorem copies_native (N : Network K n) (h : Native N) (r : ℕ) : Native (copies N r) := by
  induction r with
  | zero => intro e; exact Fin.elim0 e
  | succ r ih => exact tensor_native N (copies N r) h ih

theorem copies_vertices (N : Network K n) (r : ℕ) :
    (copies N r).shape.vertices = r * N.shape.vertices := by
  induction r <;> simp [copies, Network.empty, NetworkShape.empty, *, Nat.succ_mul, Nat.add_comm]

theorem copies_word (N : Network K n) (x : Fin n → Bool) (r : ℕ) :
    (copies N r).denote (copyWord x r) = N.denote x ^ r := by
  induction r with
  | zero => simpa only [copies, copyWord, pow_zero] using (Network.denote_empty (K:=K) Fin.elim0)
  | succ r ih =>
    change (N.tensor (copies N r)).denote (appendWord x (copyWord x r)) = _
    rw [tensor_word, ih, pow_succ, mul_comm]

theorem balance_copy (b : Bool) (x : Fin n → Bool) (r : ℕ) :
    balance b (copyWord x r) = r * balance b x := by
  induction r with
  | zero => change (∑ i : Fin 0, _) = (0 : ℤ) * _; simp
  | succ r ih =>
    rw [copyWord, balance_append, ih]
    push_cast
    ring

end Holant.LocalDrafts.Hardness.GeneralExtraction.NativeCopies
