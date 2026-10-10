import Holant.Proofs.Reductions.EightVertexNonexception.NativeChain
import Holant.Complexity.BinaryInterpolation.Chains.Compiler.OriginalFamily
import Holant.Complexity.BinaryInterpolation.SpectralForms
import Holant.Complexity.BinaryInterpolation.BinaryFactors
import Holant.Complexity.BinaryInterpolation.CommonDenominator
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.CharP.Algebra


namespace Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation
open Holant Holant.Complexity Holant.Complexity.BinaryInterpolation
open Holant.Complexity.BinaryInterpolation.Chains
open Holant.Certificates.MatchingContractionClosure
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

section Semiring
variable {K : Type*} [CommSemiring K]

def selfLoop (q : Signature K 4) : Network K 2 :=
  (Network.corolla q).contract Signature.disequality

def weightedX (u v : K) : Matrix Bool Bool K := fun a b =>
  if a then (if b then 0 else v) else (if b then u else 0)

def sparseU (p : Entries K) : K := p.c * (p.d + p.z)
def sparseV (p : Entries K) : K := p.c * p.z + p.d ^ 2 + p.d * p.z

theorem selfLoop_sum (q : Signature K 4) (t : Fin 2 → Bool) :
    (selfLoop q).denote t =
      q ![false,true,t 0,t 1] + q ![true,false,t 0,t 1] := by
  rw [selfLoop, Network.denote_contract, Network.denote_corolla]
  rw [Signature.contract_disequality]
  have hword (a b : Bool) : Fin.cons a (Fin.cons b t) = ![a,b,t 0,t 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hword,hword]

theorem selfLoop_sparse (p : Entries K) :
    (selfLoop (table (sparseEntries p))).denote =
      fun t => weightedX (sparseU p) (sparseV p) (t 0) (t 1) := by
  funext t
  rw [selfLoop_sum]
  cases h₀ : t 0 <;> cases h₁ : t 1 <;>
    simp [table,sparseEntries,weightedX,sparseU,sparseV,h₀,h₁] <;> ring

theorem original_selfLoop (M : Signature K 4) (hM : EvenSupport M)
    (hs : SparseCase M) :
    (selfLoop (nativeChain M).denote).denote =
      fun t => weightedX (sparseU (entries M)) (sparseV (entries M)) (t 0) (t 1) := by
  rw [nativeChain_sparse M hM hs]
  exact selfLoop_sparse (entries M)

theorem selfLoop_vertices (q : Signature K 4) : (selfLoop q).shape.vertices = 1 := rfl
theorem selfLoop_edges (q : Signature K 4) : (selfLoop q).shape.edges = 1 := rfl
theorem selfLoop_vertex (q : Signature K 4) (v : Fin (selfLoop q).shape.vertices) :
    (selfLoop q).vertex v = q := rfl
theorem selfLoop_edge (q : Signature K 4) (e : Fin (selfLoop q).shape.edges) :
    (selfLoop q).edge e = Signature.disequality := by
  fin_cases e
  rfl
end Semiring

section Field
variable {K : Type*} [Field K]

def diagonal (u v : K) : Binary (K:=K) := fun a b =>
  if a = b then (if a then v else u) else 0

def leftPin : Binary (K:=K) := weightedX 0 1
def rightPin : Binary (K:=K) := weightedX 1 0

theorem weightedX_transfer (u v : K) : weightedX u v * X = diagonal u v := by
  ext a b
  cases a <;> cases b <;> simp [weightedX,diagonal,X,Matrix.mul_apply,Signature.disequality]

theorem diagonal_mul (u v u' v' : K) :
    diagonal u v * diagonal u' v' = diagonal (u*u') (v*v') := by
  ext a b
  cases a <;> cases b <;> simp [diagonal,Matrix.mul_apply]

theorem diagonal_power (u v : K) (t : ℕ) :
    (diagonal u v)^t = diagonal (u^t) (v^t) := by
  induction t with
  | zero =>
    ext a b
    cases a <;> cases b <;> simp [diagonal]
  | succ t ih => rw [pow_succ,ih,diagonal_mul,pow_succ,pow_succ]

theorem diagonal_X (u v : K) : diagonal u v * X = weightedX u v := by
  ext a b
  cases a <;> cases b <;> simp [diagonal,weightedX,X,Matrix.mul_apply,Signature.disequality]

theorem weightedX_power (u v : K) (t : ℕ) :
    (weightedX u v * X)^t * X = weightedX (u^t) (v^t) := by
  rw [weightedX_transfer,diagonal_power,diagonal_X]

/-- A literal power identity derived from the actual two weights. The left
and right matrices are fixed ordered one-orientation pins, not chosen gates. -/
theorem power_pencil (u v : K) (hv : v ≠ 0) (t : ℕ) :
    (weightedX u v * X)^t * X =
      v^t • (leftPin + (u/v)^t • rightPin) := by
  rw [weightedX_power]
  ext a b
  cases a <;> cases b <;>
    simp [weightedX,leftPin,rightPin,Matrix.smul_apply,smul_eq_mul,div_pow] <;>
      field_simp [pow_ne_zero t hv]

theorem rightPin_nonzero : (rightPin : Binary (K:=K)) ≠ 0 := by
  intro h
  have h' := congrFun₂ h false true
  exact one_ne_zero h'

theorem rightPin_rank : (rightPin : Binary (K:=K)).rank = 1 := by
  apply singular_binary_rank _ rightPin_nonzero
  rw [det_entries]
  simp [rightPin,weightedX]

/-- Physical copies retain the self-loop at *every* q occurrence. In a
positive chain of t copies there are t q vertices and 2t-1 native-X edges. -/
theorem selfLoop_chain (M : Signature K 4) (hM : EvenSupport M) (hs : SparseCase M)
    (k : ℕ) :
    (copies (selfLoop (nativeChain M).denote) k).shape.vertices = k+1 ∧
    (copies (selfLoop (nativeChain M).denote) k).shape.edges = 2*(k+1)-1 ∧
    (copies (selfLoop (nativeChain M).denote) k).denote =
      binarySignature (weightedX ((sparseU (entries M))^(k+1))
        ((sparseV (entries M))^(k+1))) := by
  refine ⟨?_,?_,?_⟩
  · rw [copies_vertices,selfLoop_vertices,mul_one]
  · rw [copies_edges,selfLoop_edges,mul_one]
    omega
  · have hloop : (selfLoop (nativeChain M).denote).denote =
        Chains.binarySignature (weightedX (sparseU (entries M)) (sparseV (entries M))) :=
      original_selfLoop M hM hs
    rw [copies_denote _ (weightedX (sparseU (entries M)) (sparseV (entries M))) hloop,
      weightedX_power]

/-- Node separation is recovered from the *computed finite denominator*.
It is not supplied as an independent interpolation correctness premise. -/
theorem nodes_injective_of_denominator {m : ℕ} (nodes c : Fin (m+1) → K)
    (hd : commonDenominator (queryDenominator nodes c) ≠ 0) :
    Function.Injective nodes := by
  intro i j he
  by_contra hne
  have hi : queryDenominator nodes c i ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hd i (Finset.mem_univ i)
  have hp : interpolationDenominator nodes i ≠ 0 := (mul_ne_zero_iff.mp hi).2
  have hj : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨Ne.symm hne,Finset.mem_univ j⟩
  exact (Finset.prod_ne_zero_iff.mp hp j hj) (sub_eq_zero.mpr he)

/-- This bounded branch is genuinely decidable from the original two weights
and original occurrence count. No assertion of infinite order is made. -/
theorem first_nodes_injective (u v : K) (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : u ≠ v) (m : ℕ) (hm : m ≤ 1) :
    Function.Injective (fun i : Fin (m+1) => (u/v)^(i.val+1)) := by
  have hr : u/v ≠ 0 := div_ne_zero hu hv
  have hr₁ : u/v ≠ 1 := by
    intro h
    exact huv ((div_eq_one_iff_eq hv).mp h)
  have hp : u/v ≠ (u/v)^2 := by
    intro h
    have h' : (u/v)*1 = (u/v)*(u/v) := by simpa only [mul_one,pow_two] using h
    exact hr₁ (mul_left_cancel₀ hr h').symm
  interval_cases m
  · intro i j _
    change Fin 1 at i j
    exact (Fin.eq_zero i).trans (Fin.eq_zero j).symm
  · intro i j he
    change Fin 2 at i j
    fin_cases i <;> fin_cases j
    · rfl
    · change (u/v)^1 = (u/v)^2 at he
      rw [pow_one] at he
      exact (hp he).elim
    · change (u/v)^2 = (u/v)^1 at he
      rw [pow_one] at he
      exact (hp he.symm).elim
    · rfl

/-- A concrete algebraic coefficient branch yields all-size separation.
Characteristic zero is later produced by the original rational algebra.
No desired infinite-order premise is accepted. -/
theorem doubling_nodes_injective [CharZero K] (m : ℕ) :
    Function.Injective (fun i : Fin (m+1) => (2 : K)^(i.val+1)) := by
  have ht : (2 : K) ≠ 0 := by exact_mod_cast (show (2 : ℕ) ≠ 0 by decide)
  apply geometric_nodes_injective (2 : K) ht
  intro r hr he
  have hn : (2 : ℕ)^r = 1 := by exact_mod_cast he
  have hp : 1 < (2 : ℕ)^r := one_lt_pow₀ (by decide) (Nat.ne_of_gt hr)
  exact (Nat.ne_of_gt hp) hn
end Field
end Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation
