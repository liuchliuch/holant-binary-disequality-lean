import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockSigned

/-! Signed even blocks using an actual full weighted antidiagonal, without a
literal disequality row. Opposite orientations occur at every coordinate,
including unsigned coordinates. Their product is a fixed nonzero scalar,
so no assignment-dependent weight is discarded. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedAntiSigned
open Holant Holant.Tractable
open OrdinaryNegativeMixedBlockData
open scoped BigOperators
namespace M
export OrdinaryNegativeMixedBlockCompose (compose coefficient_compose even_compose even_flatMap)
export OrdinaryNegativeMixedBlockSource (trace)
end M
namespace L
export OrdinaryNegativeMixedBlockLiteral (nodes nodes_ports nodes_value)
end L
namespace B
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseBundle (evaluate)
end B
namespace X
export OrdinaryNegativeMixedBlockSigned (external flipped port outer substituted splitPrivate)
end X
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable {s u k n : ℕ} {b : ℕ→ℕ}
variable (blocks : Recipe (u:=1) (s:=s) (a:=fun _=>n+k) (b:=b))
variable (signs : Fin u→Fin n→Bool)
variable (antiLabel : Fin s) (ha : b antiLabel.val=2)

def guard (i : Fin u) (q : Fin n) :
    List (Node (u:=u) (s:=s) (a:=fun _=>n+(n+k)) (b:=b) i) :=
  L.nodes i antiLabel ha [
    fun j=>.inr (if j=0 then X.external q else X.flipped q),
    fun j=>.inr (if j=0 then X.flipped q else X.external q)]

def guards (i : Fin u) : List (Node (u:=u) (s:=s) (a:=fun _=>n+(n+k)) (b:=b) i) :=
  (List.finRange n).flatMap (guard (k:=k) antiLabel ha i)

def recipe : Recipe (u:=u) (s:=s) (a:=fun _=>n+(n+k)) (b:=b) :=
  fun i=>M.compose (X.outer signs) blocks i++guards (n:=n) (k:=k) antiLabel ha i

theorem guard_even (i : Fin u) (q : Fin n) (p : Bool ⊕ Fin (n+(n+k))) :
    Even (((guard (k:=k) antiLabel ha i q).flatMap (fun node=>List.ofFn node.2)).count p) := by
  rw [guard,L.nodes_ports]
  change Even (([.inr (X.external q),.inr (X.flipped q),.inr (X.flipped q),.inr (X.external q)] :
    List (Bool ⊕ Fin (n+(n+k)))).count p)
  refine ⟨(([.inr (X.external q),.inr (X.flipped q)] : List (Bool ⊕ Fin (n+(n+k)))).count p),?_⟩
  simp only [List.count_cons,List.count_nil]
  omega

theorem even_recipe (hb : EvenRecipe blocks) : EvenRecipe (recipe blocks signs antiLabel ha) := by
  intro i p
  unfold ports recipe
  rw [List.flatMap_append,List.count_append]
  apply (M.even_compose (X.outer signs) blocks hb i p).add
  rw [guards,List.flatMap_assoc]
  apply M.even_flatMap
  intro q _ p
  exact guard_even antiLabel ha i q p

variable {K : Type} [Field K]

def anti (a b : K) : Signature K 2 :=
  fun z=>if z 0 then (if z 1 then 0 else b) else (if z 1 then a else 0)

variable (H : (j : Fin s)→Signature K (b j.val)) (left right : K)
variable (a_lit : (⟨b antiLabel.val,H antiLabel⟩ : AnySignature K)=⟨2,anti left right⟩)

include a_lit in
theorem guard_value (i : Fin u) (q : Fin n) (x z : Fin n→Bool) (y : Fin k→Bool) :
    ((guard (k:=k) antiLabel (congrArg Sigma.fst a_lit) i q).map
      (fun node=>H node.1 (fun j=>Sum.elim id (Fin.addCases x (Fin.addCases z y)) (node.2 j)))).prod=
      (left*right)*(if z q=!(x q) then 1 else 0) := by
  unfold guard
  erw [L.nodes_value (a:=fun _=>n+(n+k)) H i antiLabel _ a_lit]
  cases hxq : x q <;> cases hzq : z q <;>
    simp [B.evaluate,Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor.substitute,
      X.external,X.flipped,anti,hxq,hzq,mul_comm]

include a_lit in
theorem guards_value (i : Fin u) (x z : Fin n→Bool) (y : Fin k→Bool) :
    ((guards (n:=n) (k:=k) antiLabel (congrArg Sigma.fst a_lit) i).map
      (fun node=>H node.1 (fun j=>Sum.elim id (Fin.addCases x (Fin.addCases z y)) (node.2 j)))).prod=
      (left*right)^n*(if z=(fun q=>!(x q)) then 1 else 0) := by
  unfold guards
  rw [List.map_flatMap,List.flatMap_def,List.prod_flatten]
  simp only [List.map_map,Function.comp_def,guard_value antiLabel H left right a_lit]
  rw [←List.ofFn_eq_map,List.prod_ofFn,Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,Fintype.prod_boole]
  simp only [funext_iff]
  split_ifs <;> rfl

include a_lit in
theorem coefficient_value (i : Fin u) (x z : Fin n→Bool) (y : Fin k→Bool) :
    coefficient H (recipe blocks signs antiLabel (congrArg Sigma.fst a_lit)) i
      (Fin.addCases x (Fin.addCases z y))=
      coefficient H blocks 0 (Fin.addCases (fun q=>if signs i q then z q else x q) y)*
        ((left*right)^n*(if z=(fun q=>!(x q)) then 1 else 0)) := by
  change ((M.compose (X.outer signs) blocks i++guards (n:=n) (k:=k) antiLabel (congrArg Sigma.fst a_lit) i).map _).prod=_
  erw [List.map_append,List.prod_append,guards_value antiLabel H left right a_lit]
  congr 1
  change coefficient H (M.compose (X.outer signs) blocks) i _=_
  rw [M.coefficient_compose]
  simp only [coefficient,Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue.coefficient,
    X.outer,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
  erw [X.substituted]

private theorem xor_eq (sign x : Fin n→Bool) :
    (fun q=>if sign q then !(x q) else x q)=fun q=>Bool.xor (sign q) (x q) := by
  funext q
  cases sign q <;> cases x q <;> rfl

include a_lit in
theorem trace_value (i : Fin u) (x : Fin n→Bool) :
    M.trace H (n+k) (recipe blocks signs antiLabel (congrArg Sigma.fst a_lit)) i x=
      (left*right)^n*M.trace H k blocks 0 (fun q=>Bool.xor (signs i q) (x q)) := by
  unfold M.trace
  rw [←(X.splitPrivate (k:=k)).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  change (∑z : Fin n→Bool,∑y : Fin k→Bool,coefficient H
    (recipe blocks signs antiLabel (congrArg Sigma.fst a_lit)) i
    (Fin.addCases x (Fin.addCases z y)))=_
  simp_rw [coefficient_value blocks signs antiLabel H left right a_lit]
  simp only [←Finset.sum_mul]
  simp [mul_ite,xor_eq,mul_comm]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedAntiSigned
end
