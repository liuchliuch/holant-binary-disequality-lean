import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockLiteral
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockTotal

/-! Actual sign variants of an even positive fixed-arity block. Fresh private
bits realize all requested complements with literal X. Every X and auxiliary
pin is doubled, so all original external/private incidence stays even. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockSigned
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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable {s u k n : ℕ} {b : ℕ→ℕ}
variable (blocks : Recipe (u:=1) (s:=s) (a:=fun _=>n+k) (b:=b))
variable (signs : Fin u→Fin n→Bool)
variable (xLabel p0 : Fin s) (hx : b xLabel.val=2) (h0 : b p0.val=1)

def external (q : Fin n) : Fin (n+(n+k)) := Fin.castAdd (n+k) q
def flipped (q : Fin n) : Fin (n+(n+k)) := Fin.natAdd n (Fin.castAdd k q)

def port (sign : Fin n→Bool) : Fin (n+k)→Bool ⊕ Fin (n+(n+k)) :=
  Fin.addCases (fun q=>.inr (if sign q then flipped q else external q))
    (fun j=>.inr (Fin.natAdd n (Fin.natAdd n j)))

def outer : Recipe (u:=u) (s:=1) (a:=fun _=>n+(n+k)) (b:=fun _=>n+k) :=
  fun i=>[⟨0,port (signs i)⟩]

def guard (i : Fin u) (q : Fin n) : List (Node (u:=u) (s:=s) (a:=fun _=>n+(n+k)) (b:=b) i) :=
  if signs i q then
    L.nodes i xLabel hx [fun j=>.inr (if j=0 then external q else flipped q),
      fun j=>.inr (if j=0 then external q else flipped q)]
  else L.nodes i p0 h0 [fun _=>.inr (flipped q),fun _=>.inr (flipped q)]

def guards (i : Fin u) : List (Node (u:=u) (s:=s) (a:=fun _=>n+(n+k)) (b:=b) i) :=
  (List.finRange n).flatMap (guard (k:=k) signs xLabel p0 hx h0 i)

def recipe : Recipe (u:=u) (s:=s) (a:=fun _=>n+(n+k)) (b:=b) :=
  fun i=>M.compose (outer signs) blocks i++guards (k:=k) signs xLabel p0 hx h0 i

theorem guard_even (i : Fin u) (q : Fin n) (p : Bool ⊕ Fin (n+(n+k))) :
    Even (((guard (k:=k) signs xLabel p0 hx h0 i q).flatMap (fun node=>List.ofFn node.2)).count p) := by
  unfold guard
  split_ifs <;> rw [L.nodes_ports] <;>
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.count_append] <;> exact ⟨_,rfl⟩

theorem even_recipe (hb : EvenRecipe blocks) : EvenRecipe (recipe blocks signs xLabel p0 hx h0) := by
  intro i p
  unfold ports recipe
  rw [List.flatMap_append,List.count_append]
  apply (M.even_compose (outer signs) blocks hb i p).add
  rw [guards,List.flatMap_assoc]
  apply M.even_flatMap
  intro q _ p
  exact guard_even signs xLabel p0 hx h0 i q p

variable {K : Type} [Field K]
variable (H : (j : Fin s)→Signature K (b j.val))
variable (x_lit : (⟨b xLabel.val,H xLabel⟩ : AnySignature K)=⟨2,fun x=>Signature.disequality (x 0) (x 1)⟩)
variable (p_lit : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin false⟩)

def fill (sign x : Fin n→Bool) : Fin n→Bool := fun q=>if sign q then !(x q) else false

theorem substituted (sign x z : Fin n→Bool) (y : Fin k→Bool) :
    (fun j=>Sum.elim id (Fin.addCases x (Fin.addCases z y)) (port sign j))=
      Fin.addCases (fun q=>if sign q then z q else x q) y := by
  funext j
  refine Fin.addCases (fun q=>?_) (fun q=>?_) j
  · cases hs : sign q <;> simp [port,hs,external,flipped]
  · simp [port]

theorem fill_xor (sign x : Fin n→Bool) :
    (fun q=>if sign q then fill sign x q else x q)=fun q=>Bool.xor (sign q) (x q) := by
  funext q
  cases hs : sign q <;> cases ht : x q <;> simp [fill,hs,ht]

include x_lit p_lit in
theorem guard_value (i : Fin u) (q : Fin n) (x z : Fin n→Bool) (y : Fin k→Bool) :
    ((guard (k:=k) signs xLabel p0 (congrArg Sigma.fst x_lit) (congrArg Sigma.fst p_lit) i q).map
      (fun node=>H node.1 (fun j=>Sum.elim id (Fin.addCases x (Fin.addCases z y)) (node.2 j)))).prod=
      if z q=fill (signs i) x q then 1 else 0 := by
  unfold guard
  by_cases hs : signs i q
  · rw [if_pos hs]
    erw [L.nodes_value (a:=fun _=>n+(n+k)) H i xLabel _ x_lit]
    cases hxq : x q <;> cases hzq : z q <;>
      simp [B.evaluate,Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor.substitute,
        external,flipped,Signature.disequality,fill,hs,hxq,hzq]
  · rw [if_neg hs]
    erw [L.nodes_value (a:=fun _=>n+(n+k)) H i p0 _ p_lit]
    cases hzq : z q <;>
      simp [B.evaluate,Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor.substitute,
        external,flipped,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin,fill,hs,hzq]

include x_lit p_lit in
theorem guards_value (i : Fin u) (x z : Fin n→Bool) (y : Fin k→Bool) :
    ((guards (k:=k) signs xLabel p0 (congrArg Sigma.fst x_lit) (congrArg Sigma.fst p_lit) i).map
      (fun node=>H node.1 (fun j=>Sum.elim id (Fin.addCases x (Fin.addCases z y)) (node.2 j)))).prod=
      if z=fill (signs i) x then 1 else 0 := by
  unfold guards
  rw [List.map_flatMap,List.flatMap_def,List.prod_flatten]
  simp only [List.map_map,Function.comp_def,guard_value signs xLabel p0 H x_lit p_lit]
  rw [←List.ofFn_eq_map,List.prod_ofFn,Fintype.prod_boole]
  simp only [funext_iff]
  split_ifs <;> rfl

include x_lit p_lit in
theorem coefficient_value (i : Fin u) (x z : Fin n→Bool) (y : Fin k→Bool) :
    coefficient H (recipe blocks signs xLabel p0 (congrArg Sigma.fst x_lit) (congrArg Sigma.fst p_lit)) i
      (Fin.addCases x (Fin.addCases z y))=
      coefficient H blocks 0 (Fin.addCases (fun q=>if signs i q then z q else x q) y)*
        (if z=fill (signs i) x then 1 else 0) := by
  change ((M.compose (outer signs) blocks i++guards (k:=k) signs xLabel p0 (congrArg Sigma.fst x_lit)
      (congrArg Sigma.fst p_lit) i).map _).prod=_
  erw [List.map_append,List.prod_append,guards_value signs xLabel p0 H x_lit p_lit]
  congr 1
  change coefficient H (M.compose (outer signs) blocks) i _=_
  rw [M.coefficient_compose]
  simp only [coefficient,Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue.coefficient,
    outer,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
  erw [substituted]

def splitPrivate : (Fin (n+k)→Bool) ≃ ((Fin n→Bool)×(Fin k→Bool)) where
  toFun w := (fun q=>w (Fin.castAdd k q),fun j=>w (Fin.natAdd n j))
  invFun w := Fin.addCases w.1 w.2
  left_inv w := by
    funext j
    refine Fin.addCases (fun q=>?_) (fun q=>?_) j <;> simp
  right_inv w := by
    apply Prod.ext <;> funext j <;> simp

include x_lit p_lit in
theorem trace_value (i : Fin u) (x : Fin n→Bool) :
    M.trace H (n+k) (recipe blocks signs xLabel p0 (congrArg Sigma.fst x_lit) (congrArg Sigma.fst p_lit)) i x=
      M.trace H k blocks 0 (fun q=>Bool.xor (signs i q) (x q)) := by
  unfold M.trace
  rw [←(splitPrivate (k:=k)).symm.sum_comp]
  simp only [Fintype.sum_prod_type,Equiv.symm_apply_apply]
  change (∑z : Fin n→Bool,∑y : Fin k→Bool,coefficient H
    (recipe blocks signs xLabel p0 (congrArg Sigma.fst x_lit) (congrArg Sigma.fst p_lit)) i
    (Fin.addCases x (Fin.addCases z y)))=_
  simp_rw [coefficient_value blocks signs xLabel p0 H x_lit p_lit]
  simp only [←Finset.sum_mul]
  simp [mul_ite,fill_xor]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockSigned
end
