import Holant.Complexity.BinaryInterpolation.Chains.Enumeration
import Holant.NetworkContraction
import Holant.Certificates.MatchingContractionClosure.GroupAlgebra

/-!
Positive ordinary binary chains for source Lemma 3.1. Every series step joins
two existing boundary occurrences with one native X edge. The construction has
no zero-length case and never inserts an identity vertex or free boundary stub.
-/
namespace Holant.Complexity.BinaryInterpolation.Chains
open Holant.Certificates.MatchingContractionClosure
variable {K : Type*} [Field K]
set_option backward.isDefEq.respectTransparency false

/-- The row and column indices are respectively ordinary boundary ports 0 and 1. -/
def binarySignature (B : Binary (K := K)) : Signature K 2 := fun x => B (x 0) (x 1)

def reindex {n : ℕ} (N : Network K n) (e : Equiv.Perm (Fin n)) : Network K n where
  shape := {
    vertices := N.shape.vertices
    arity := N.shape.arity
    edges := N.shape.edges
    ports := N.shape.ports.trans (Equiv.sumCongr e (Equiv.refl _)) }
  vertex := N.vertex
  edge := N.edge

theorem reindex_denote {n : ℕ} (N : Network K n) (e : Equiv.Perm (Fin n)) :
    (reindex N e).denote = Tensor.reindex e N.denote := by
  funext x
  unfold Network.denote Tensor.reindex
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  congr 1
  funext i
  dsimp [NetworkShape.assignment, reindex]
  cases N.shape.ports ⟨v, i⟩ <;> rfl

/-- Old boundary [L0,L1,R0,R1] becomes [L1,R0,L0,R1]. -/
def seriesOrder : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv := by decide
  right_inv := by decide

/-- Join L1 to R0, leaving L0 and R1 in that boundary order. -/
def series (L R : Network K 2) : Network K 2 :=
  (reindex (tensor L R) seriesOrder).contract Signature.disequality

theorem series_denote (L R : Network K 2) (A B : Binary (K := K))
    (hL : L.denote = binarySignature A) (hR : R.denote = binarySignature B) :
    (series L R).denote = binarySignature (A * X * B) := by
  rw [series, Network.denote_contract, reindex_denote,
    tensor_denote, hL, hR]
  funext x
  change (∑ a : Bool, ∑ b : Bool,
    Signature.disequality a b * (A (x 0) a * B b (x 1))) =
    ∑ b : Bool, (∑ a : Bool, A (x 0) a * X a b) * B b (x 1)
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  change Signature.disequality a b * (A (x 0) a * B b (x 1)) =
    A (x 0) a * Signature.disequality a b * B b (x 1)
  ring

@[simp] theorem series_vertices (L R : Network K 2) :
    (series L R).shape.vertices = L.shape.vertices + R.shape.vertices := by
  simp [series, reindex]

@[simp] theorem series_edges (L R : Network K 2) :
    (series L R).shape.edges = L.shape.edges + R.shape.edges + 1 := by
  simp [series, reindex]

def Uses {n : ℕ} (N : Network K n) (F : SignatureFamily K) : Prop :=
  ∀ v, (⟨N.shape.arity v, N.vertex v⟩ : AnySignature K) ∈ F

def Native {n : ℕ} (N : Network K n) : Prop :=
  ∀ e, N.edge e = (Signature.disequality : Kernel K)

theorem series_uses (L R : Network K 2) (F : SignatureFamily K)
    (hL : Uses L F) (hR : Uses R F) : Uses (series L R) F := by
  intro v
  change (⟨_, (Network.tensorFinite L R).vertex
    (finSumFinEquiv.symm v)⟩ :
      AnySignature K) ∈ F
  cases finSumFinEquiv.symm v with
  | inl v => exact hL v
  | inr v => exact hR v

theorem series_native (L R : Network K 2)
    (hL : Native L) (hR : Native R) : Native (series L R) := by
  intro e
  refine Fin.cases ?_ (fun e => ?_) e
  · rfl
  · change (Network.tensorFinite L R).edge
      (finSumFinEquiv.symm e) = _
    cases finSumFinEquiv.symm e with
    | inl e => exact hL e
    | inr e => exact hR e

/-- A positive chain of k+1 copies of an actual two-port network. -/
def copies (N : Network K 2) : ℕ → Network K 2
  | 0 => N
  | k + 1 => series (copies N k) N

@[simp] theorem copies_vertices (N : Network K 2) (k : ℕ) :
    (copies N k).shape.vertices = (k + 1) * N.shape.vertices := by
  induction k with
  | zero => simp [copies]
  | succ k ih => simp only [copies, series_vertices, ih, Nat.add_mul, Nat.one_mul]

@[simp] theorem copies_edges (N : Network K 2) (k : ℕ) :
    (copies N k).shape.edges = (k + 1) * N.shape.edges + k := by
  induction k with
  | zero => simp [copies]
  | succ k ih => simp only [copies, series_edges, ih, Nat.add_mul, Nat.one_mul]; omega

theorem copies_uses (N : Network K 2) (F : SignatureFamily K)
    (hN : Uses N F) (k : ℕ) : Uses (copies N k) F := by
  induction k with
  | zero => exact hN
  | succ k ih => exact series_uses _ _ F ih hN

theorem copies_native (N : Network K 2) (hN : Native N) (k : ℕ) :
    Native (copies N k) := by
  induction k with
  | zero => exact hN
  | succ k ih => exact series_native _ _ ih hN

theorem copies_denote (N : Network K 2) (B : Binary (K := K))
    (hN : N.denote = binarySignature B) (k : ℕ) :
    (copies N k).denote = binarySignature ((B * X) ^ (k + 1) * X) := by
  induction k with
  | zero => simpa only [copies, Nat.zero_add, pow_one, Matrix.mul_assoc, X_mul_X,
      Matrix.mul_one] using hN
  | succ k ih =>
    rw [copies, series_denote _ _ _ _ ih hN]
    congr 1
    rw [pow_succ (B * X) (k + 1)]
    simp only [Matrix.mul_assoc, X_mul_X, Matrix.mul_one]

/-- The literal positive B chain: k+1 B vertices and exactly k native edges. -/
def literal (B : Binary (K := K)) (k : ℕ) : Network K 2 :=
  copies (Network.corolla (binarySignature B)) k

@[simp] theorem literal_vertices (B : Binary (K := K)) (k : ℕ) :
    (literal B k).shape.vertices = k + 1 := by simp [literal, Network.corolla]

@[simp] theorem literal_edges (B : Binary (K := K)) (k : ℕ) :
    (literal B k).shape.edges = k := by simp [literal, Network.corolla]

theorem literal_denote (B : Binary (K := K)) (k : ℕ) :
    (literal B k).denote = binarySignature ((B * X) ^ (k + 1) * X) :=
  copies_denote _ B (Network.denote_corolla _) k

theorem literal_uses (B : Binary (K := K)) (F : SignatureFamily K)
    (hB : (⟨2, binarySignature B⟩ : AnySignature K) ∈ F) (k : ℕ) :
    Uses (literal B k) F :=
  copies_uses _ F (fun _ => hB) k

theorem literal_native (B : Binary (K := K)) (k : ℕ) : Native (literal B k) :=
  copies_native _ (fun e => Fin.elim0 e) k

/-- The physically available resource is only B; Γ need not contain literal I. -/
theorem literal_realizes (B : Binary (K := K)) (F : SignatureFamily K)
    (hB : (⟨2, binarySignature B⟩ : AnySignature K) ∈ F) (k : ℕ) :
    Gadget.Realizes F .disequality (binarySignature ((B * X) ^ (k + 1) * X)) := by
  rw [← literal_denote]
  exact Gadget.realizes_network _ _ _ (literal_uses B F hB k) (literal_native B k)

/-- Source-indexed form: t must be strictly positive, and every count is exact. -/
theorem positive_chain (B : Binary (K := K)) (F : SignatureFamily K)
    (hB : (⟨2, binarySignature B⟩ : AnySignature K) ∈ F) (t : ℕ) (ht : 0 < t) :
    ∃ N : Network K 2, N.shape.vertices = t ∧ N.shape.edges = t - 1 ∧
      Uses N F ∧ Native N ∧ N.denote = binarySignature ((B * X) ^ t * X) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  exact ⟨literal B k, literal_vertices B k, by simpa using literal_edges B k,
    literal_uses B F hB k, literal_native B k, literal_denote B k⟩

end Holant.Complexity.BinaryInterpolation.Chains
