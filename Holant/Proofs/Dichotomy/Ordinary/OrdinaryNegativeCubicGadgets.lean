import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeCubicCore
import Holant.Proofs.Hardness.LabelledNetwork
import Holant.Proofs.CountingMachines.CircuitNative.GateAlphabet
import Holant.EightVertex.ProductAnchor.NetworksData
import Holant.Complexity.BinaryInterpolation.Chains.Template

/-! Physical ordinary negative-phase gadgets. Every gate uses only the
retained cubic-sign row, Eq4, and the two retained pins. The NAND macro has
the exact nonzero scale two; no unary or Boolean gate is freely adjoined. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeCubicGadgets
open Holant Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.RemoteWork.CountingBridge
namespace C
export Holant.Complexity.BinaryInterpolation.Chains (tensor reindex tensor_denote reindex_denote seriesOrder)
end C
namespace L
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.LabelledNetwork
  (Exact tensor reindex contract exact_tensor exact_reindex exact_contract)
end L
open OrdinaryNegativeCubicCore (cubic)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {K : Type} [Field K] {s : ℕ} {a : ℕ → ℕ}
variable (H : (i : Fin s) → Signature K (a i.val))

/-- An actual ordered network with its unchanged original row labels. -/
structure Macro (n : ℕ) where
  network : Network K n
  labels : Labelling network.shape s 1 a
  exact : L.Exact H network labels
  edges : ∀e,network.edge e=Signature.equality

namespace Macro
variable {H}

def row {n : ℕ} (j : Fin s) (f : Signature K n)
    (h : (⟨a j.val,H j⟩ : AnySignature K)=⟨n,f⟩) : Macro H n where
  network := Network.corolla f
  labels := {
    vertex := fun _=>j
    vertex_arity := fun _=>congrArg Sigma.fst h
    edge := Fin.elim0 }
  exact := fun _=>h
  edges := fun e=>Fin.elim0 e

def tensor {m n : ℕ} (N : Macro H m) (M : Macro H n) : Macro H (m+n) where
  network := C.tensor N.network M.network
  labels := L.tensor N.network M.network N.labels M.labels
  exact := L.exact_tensor N.network M.network N.labels M.labels H N.exact M.exact
  edges := by
    intro e
    change Sum.elim N.network.edge M.network.edge (finSumFinEquiv.symm e)=_
    cases finSumFinEquiv.symm e with
    | inl e => exact N.edges e
    | inr e => exact M.edges e

def reindex {n : ℕ} (N : Macro H n) (p : Equiv.Perm (Fin n)) : Macro H n where
  network := C.reindex N.network p
  labels := L.reindex N.network N.labels p
  exact := L.exact_reindex N.network N.labels H N.exact p
  edges := N.edges

def contract {n : ℕ} (N : Macro H (n+2)) : Macro H n where
  network := N.network.contract Signature.equality
  labels := L.contract N.network N.labels 0 Signature.equality
  exact := L.exact_contract H N.network N.labels N.exact 0 Signature.equality
  edges := by
    intro e
    exact Fin.cases rfl (fun j=>N.edges j) e

@[simp] theorem row_denote {n : ℕ} (j : Fin s) (f : Signature K n)
    (h : (⟨a j.val,H j⟩ : AnySignature K)=⟨n,f⟩) :
    (row j f h).network.denote=f := Network.denote_corolla f

@[simp] theorem tensor_denote {m n : ℕ} (N : Macro H m) (M : Macro H n) :
    (N.tensor M).network.denote=Signature.tensor N.network.denote M.network.denote :=
  C.tensor_denote _ _

@[simp] theorem reindex_denote {n : ℕ} (N : Macro H n) (p : Equiv.Perm (Fin n)) :
    (N.reindex p).network.denote=Tensor.reindex p N.network.denote :=
  C.reindex_denote _ _

@[simp] theorem contract_denote {n : ℕ} (N : Macro H (n+2)) (x : Fin n → Bool) :
    N.contract.network.denote x=N.network.denote (Fin.cons false (Fin.cons false x))+
      N.network.denote (Fin.cons true (Fin.cons true x)) :=
  Network.denote_contract_equality _ _

abbrev template {n : ℕ} (N : Macro H n) := N.labels.template

theorem template_exact {n : ℕ} (N : Macro H n) :
    (N.template.network N.labels.wellFormed H (fun _ : Fin 1=>Signature.equality)).denote=
      N.network.denote :=
  N.labels.denote_template_of_labels H (fun _ : Fin 1=>Signature.equality)
    N.network.vertex N.network.edge (fun v x=>
      Holant.Complexity.BinaryInterpolation.Chains.signature_cast_apply
        (H (N.labels.vertex v)) (N.network.vertex v) (N.exact v)
        (N.labels.vertex_arity v) x)
    (fun e b c=>congrFun (congrFun (N.edges e).symm b) c)
end Macro

@[simp] private theorem cons2_two {n : ℕ} (b c : Bool) (x : Fin (n+1) → Bool) :
    (Fin.cons b (Fin.cons c x) : Fin (n+3) → Bool) 2=x 0 := rfl
@[simp] private theorem cons2_three {n : ℕ} (b c : Bool) (x : Fin (n+2) → Bool) :
    (Fin.cons b (Fin.cons c x) : Fin (n+4) → Bool) 3=x 1 := rfl
@[simp] private theorem cons2_four {n : ℕ} (b c : Bool) (x : Fin (n+3) → Bool) :
    (Fin.cons b (Fin.cons c x) : Fin (n+5) → Bool) 4=x 2 := rfl

variable (j e p₀ p₁ : Fin s)
variable (hj : (⟨a j.val,H j⟩ : AnySignature K)=⟨3,cubic⟩)
variable (he : (⟨a e.val,H e⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)
variable (h₀ : (⟨a p₀.val,H p₀⟩ : AnySignature K)=⟨1,Gates.pin false⟩)
variable (h₁ : (⟨a p₁.val,H p₁⟩ : AnySignature K)=⟨1,Gates.pin true⟩)

abbrev phase := Macro.row j cubic hj
abbrev equality := Macro.row e Holant.EightVertex.ProductAnchor.equalityFour he
abbrev pin₀ := Macro.row p₀ (Gates.pin false) h₀
abbrev pin₁ := Macro.row p₁ (Gates.pin true) h₁

def free : Macro H 1 := ((pin₀ H p₀ h₀).tensor
  (((pin₀ H p₀ h₀).tensor (phase H j hj)).contract)).contract

def hadamard : Macro H 2 := ((pin₁ H p₁ h₁).tensor (phase H j hj)).contract

def sign : Macro H 1 := ((pin₁ H p₁ h₁).tensor (hadamard H j p₁ hj h₁)).contract

def copy : Macro H 3 := ((free H j p₀ hj h₀).tensor (equality H e he)).contract

def signedEquality : Macro H 2 :=
  ((sign H j p₁ hj h₁).tensor (copy H j e p₀ hj he h₀)).contract

def signedHadamard : Macro H 2 :=
  (((signedEquality H j e p₀ p₁ hj he h₀ h₁).tensor (hadamard H j p₁ hj h₁)).reindex
    C.seriesOrder).contract

def nandOrder : Equiv.Perm (Fin 5) where
  toFun := ![2,3,0,1,4]
  invFun := ![2,3,0,1,4]
  left_inv := by decide
  right_inv := by decide

def nand : Macro H 3 :=
  (((phase H j hj).tensor (signedHadamard H j e p₀ p₁ hj he h₀ h₁)).reindex
    nandOrder).contract

theorem free_exact : (free H j p₀ hj h₀).network.denote=Gates.free := by
  funext x
  simp [free,Macro.contract_denote,Macro.tensor_denote,Signature.tensor_apply,
    Gates.pin,Gates.free,cubic]

theorem hadamard_exact : (hadamard H j p₁ hj h₁).network.denote=
    fun x=>if x 0 && x 1 then -1 else 1 := by
  funext x
  simp [hadamard,Macro.contract_denote,Macro.tensor_denote,Signature.tensor_apply,
    Gates.pin,cubic]

theorem sign_exact : (sign H j p₁ hj h₁).network.denote=
    fun x=>if x 0 then -1 else 1 := by
  funext x
  simp [sign,Macro.contract_denote,Macro.tensor_denote,Signature.tensor_apply,
    hadamard_exact,Gates.pin]

theorem copy_exact : (copy H j e p₀ hj he h₀).network.denote=Gates.copy := by
  funext x
  rw [copy,Macro.contract_denote]
  simp only [Macro.tensor_denote,free_exact,Macro.row_denote,Signature.tensor_apply]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    simp [Gates.free,Gates.copy,Holant.EightVertex.ProductAnchor.equalityFour,
      Fin.forall_fin_succ,h0,h1,h2]

theorem signedEquality_exact : (signedEquality H j e p₀ p₁ hj he h₀ h₁).network.denote=
    fun x=>if x 0=x 1 then (if x 0 then -1 else 1) else 0 := by
  funext x
  rw [signedEquality,Macro.contract_denote]
  simp only [Macro.tensor_denote,sign_exact,copy_exact,Signature.tensor_apply]
  cases h0 : x 0 <;> cases h1 : x 1 <;> simp [Gates.copy,h0,h1]

theorem signedHadamard_exact :
    (signedHadamard H j e p₀ p₁ hj he h₀ h₁).network.denote=
      fun x=>(if x 0 then -1 else 1)*(if x 0 && x 1 then -1 else 1) := by
  funext x
  rw [signedHadamard,Macro.contract_denote]
  simp only [Macro.reindex_denote,Macro.tensor_denote,signedEquality_exact,
    hadamard_exact,Tensor.reindex,Signature.tensor_apply]
  cases h0 : x 0 <;> cases h1 : x 1 <;> simp [C.seriesOrder,h0,h1]

theorem nand_exact : (nand H j e p₀ p₁ hj he h₀ h₁).network.denote=(2 : K) • Gates.nand := by
  funext x
  rw [nand,Macro.contract_denote]
  simp only [Macro.reindex_denote,Macro.tensor_denote,Macro.row_denote,
    signedHadamard_exact,Tensor.reindex,Signature.tensor_apply]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    simp [nandOrder,cubic,Gates.nand,h0,h1,h2,one_add_one_eq_two]

/-- The source alphabet is exactly free, false, true, COPY, NAND. -/
def gate (i : ℕ) : Macro H (Gates.arity i) :=
  match i with
  | 0 => free H j p₀ hj h₀
  | 1 => pin₀ H p₀ h₀
  | 2 => pin₁ H p₁ h₁
  | 3 => copy H j e p₀ hj he h₀
  | _+4 => nand H j e p₀ p₁ hj he h₀ h₁

theorem gate_exact (i : Fin 5) :
    (gate H j e p₀ p₁ hj he h₀ h₁ i.val).network.denote=
      (if i.val=4 then (2 : K) else 1) • Gates.signatures i := by
  fin_cases i
  · simpa [gate,Gates.signatures] using free_exact H j p₀ hj h₀
  · simp [gate,Gates.signatures]
  · simp [gate,Gates.signatures]
  · simpa [gate,Gates.signatures] using copy_exact H j e p₀ hj he h₀
  · simpa [gate,Gates.signatures] using nand_exact H j e p₀ p₁ hj he h₀ h₁

/-- Exact fixed-template sizes; the scale-two NAND uses ten retained
vertices and nine ordinary edges, including its physical pin occurrences. -/
theorem gate_vertices (i : Fin 5) :
    (gate H j e p₀ p₁ hj he h₀ h₁ i.val).network.shape.vertices=![3,1,1,4,10] i := by
  fin_cases i <;> rfl

theorem gate_edges (i : Fin 5) :
    (gate H j e p₀ p₁ hj he h₀ h₁ i.val).network.shape.edges=![2,0,0,3,9] i := by
  fin_cases i <;> rfl

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeCubicGadgets
end
