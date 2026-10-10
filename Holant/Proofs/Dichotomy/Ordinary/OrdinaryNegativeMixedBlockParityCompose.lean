import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockCompose

/-! Even outer recipes also admit odd-interface inner gadgets. Constant
ports of each inner recipe must be even; each formal free port must be odd.
The exact modular incidence identity retains every repeated occurrence. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockParityCompose
open Holant
open OrdinaryNegativeMixedBlockData
open scoped BigOperators
namespace C
export OrdinaryNegativeMixedBlockCompose (compose ports_compose count_map substitute)
end C
namespace O
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseOccurrences (count_ofFn)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {u v s : ℕ} {a b c : ℕ→ℕ}

def OddInterface (inner : Recipe (u:=v) (s:=s) (a:=b) (b:=c)) : Prop :=
  (∀i q,Even ((ports inner i).count (.inl q))) ∧
  (∀i j,Odd ((ports inner i).count (.inr j)))

def interfaceCount {n : ℕ} : Bool ⊕ Fin n→ℕ
  | .inl _=>0
  | .inr _=>1

theorem interface_mod (inner : Recipe (u:=v) (s:=s) (a:=b) (b:=c)) (h : OddInterface inner)
    (i : Fin v) (q : Bool ⊕ Fin (b i.val)) :
    Nat.ModEq 2 ((ports inner i).count q) (interfaceCount q) := by
  cases q with
  | inl q => exact (even_iff_two_dvd.mp (h.1 i q)).modEq_zero_nat
  | inr j => exact Nat.odd_iff.mp (h.2 i j)

theorem sum_mod {A : Type*} [DecidableEq A] (S : Finset A) (f g : A→ℕ)
    (h : ∀i∈S,Nat.ModEq 2 (f i) (g i)) : Nat.ModEq 2 (∑i∈S,f i) (∑i∈S,g i) := by
  induction S using Finset.induction_on with
  | empty => simp [Nat.ModEq]
  | insert i S hi ih =>
      rw [Finset.sum_insert hi,Finset.sum_insert hi]
      exact (h i (by simp)).add (ih (fun j hj=>h j (by simp [hj])))

theorem list_sum_mod {A : Type*} (xs : List A) (f g : A→ℕ)
    (h : ∀i∈xs,Nat.ModEq 2 (f i) (g i)) :
    Nat.ModEq 2 ((xs.map f).sum) ((xs.map g).sum) := by
  induction xs with
  | nil => simp [Nat.ModEq]
  | cons i xs ih =>
      simp only [List.map_cons,List.sum_cons]
      exact (h i (by simp)).add (ih (fun j hj=>h j (by simp [hj])))

theorem node_mod (inner : Recipe (u:=v) (s:=s) (a:=b) (b:=c)) (h : OddInterface inner)
    {i : Fin u} (node : Node (u:=u) (s:=v) (a:=a) (b:=b) i) (q : Bool ⊕ Fin (a i.val)) :
    Nat.ModEq 2 (((ports inner node.1).map (C.substitute node.2)).count q)
      ((List.ofFn node.2).count q) := by
  rw [C.count_map]
  have hm := sum_mod Finset.univ
    (fun p=>(ports inner node.1).count p*(if C.substitute node.2 p=q then 1 else 0))
    (fun p=>interfaceCount p*(if C.substitute node.2 p=q then 1 else 0))
    (fun p _=>(interface_mod inner h node.1 p).mul_right _)
  have he : (∑p : Bool ⊕ Fin (b node.1.val),interfaceCount p*(if C.substitute node.2 p=q then 1 else 0))=
      (List.ofFn node.2).count q := by
    rw [Fintype.sum_sum_type,O.count_ofFn]
    simp only [interfaceCount,C.substitute,Sum.elim_inl,Sum.elim_inr,zero_mul,one_mul,Finset.sum_const_zero,zero_add]
    rfl
  rw [he] at hm
  exact hm

theorem compose_mod (outer : Recipe (u:=u) (s:=v) (a:=a) (b:=b))
    (inner : Recipe (u:=v) (s:=s) (a:=b) (b:=c)) (h : OddInterface inner)
    (i : Fin u) (q : Bool ⊕ Fin (a i.val)) :
    Nat.ModEq 2 ((ports (C.compose outer inner) i).count q) ((ports outer i).count q) := by
  rw [C.ports_compose]
  simp only [ports,List.count_flatMap]
  apply list_sum_mod
  intro node _
  exact node_mod inner h node q

theorem even_compose (outer : Recipe (u:=u) (s:=v) (a:=a) (b:=b))
    (inner : Recipe (u:=v) (s:=s) (a:=b) (b:=c))
    (ho : EvenRecipe outer) (hi : OddInterface inner) : EvenRecipe (C.compose outer inner) := by
  intro i q
  apply even_iff_two_dvd.mpr
  apply Nat.modEq_zero_iff_dvd.mp
  exact (compose_mod outer inner hi i q).trans ((even_iff_two_dvd.mp (ho i q)).modEq_zero_nat)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockParityCompose
end
