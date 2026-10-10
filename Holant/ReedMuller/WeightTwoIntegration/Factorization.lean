import Holant.ReedMuller.WeightTwoIntegration.LogicalSlices
import Holant.Pauli.ExoticKlein.FiberFactor

/-! Logical product coefficients yield an exact binary product in the original
physical basis, hence a genuine nontrivial tensor factorization. No factor
gadget availability is inferred. -/
noncomputable section
namespace Holant.ReedMuller.WeightTwoIntegration
open Holant Holant.ReedMuller.ZeroCardGraph Holant.ReedMuller.MatchingConsistency
open Holant.ReedMuller.CoefficientAtlas Holant.ReedMuller.FixedCoreDeck
open Holant.Certificates.MatchingContractionClosure
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

 theorem OriginalPairing.support_ports {f : Signature ℂ n} (C : OriginalPairing f) (x : Fin n → Bool) :
    C.matching.Support x ↔ ∀e,x (C.ports (e,false))=x (C.ports (e,true)) := by
  constructor
  · intro h e
    have hh := h (C.ports (e,true))
    have he : C.matching.mate (C.ports (e,true))=C.ports (e,false) := originalPorts_mate C.matching e true
    rw [he] at hh
    exact hh
  · intro h p
    obtain ⟨⟨e,b⟩,rfl⟩ := C.ports.surjective p
    change x (C.matching.mate (originalPorts C.matching (e,b)))=x (originalPorts C.matching (e,b))
    rw [originalPorts_mate C.matching e b]
    cases b
    · exact (h e).symm
    · exact h e

 def diagonalBinary (rho : ℂˣ) : Kernel ℂ := fun a b =>
   if a=b then (rho:ℂ)^(if a then 1 else 0 : ℕ) else 0

 theorem OriginalPairing.analytic_product {f : Signature ℂ n} (C : OriginalPairing f)
    (htwo : (2:ℂ)≠0) (H : Consistent f) (hd : EqualityDeck f) (hn : 6≤n)
    (rho : Fin C.count → ℂˣ)
    (hp : ∀t,C.normalizedLogical htwo H hd hn t=∏i,rho i^(if t i then 1 else 0 : ℕ)) :
    f=productValue C.ports (fun e=>diagonalBinary (rho e)) (C.logical (fun _=>false)) := by
  classical
  funext x
  have hv (t : Fin C.count → Bool) : C.logical t=C.logical (fun _=>false)*
      ∏e,(rho e:ℂ)^(if t e then 1 else 0 : ℕ) := by
    have hh := congrArg (fun a : ℂˣ=>(a:ℂ)) (hp t)
    simp only [OriginalPairing.normalizedLogical,Units.val_div_eq_div_val,Units.val_mk0,
      Units.coe_prod,Units.val_pow_eq_pow_val] at hh
    exact ((div_eq_iff (C.logical_nonzero htwo H hd hn _)).mp hh).trans (mul_comm _ _)
  rw [C.tensor_exact H x]
  simp only [productValue,diagonalBinary,Fintype.prod_ite_zero,←C.support_ports]
  split_ifs with hx
  · exact hv _
  · exact (mul_zero _).symm

 def physicalBinary (rho : ℂˣ) : Kernel ℂ := fun a b =>
   ∑u : Bool,∑v : Bool,walshKernel a u*walshKernel b v*diagonalBinary rho u v

 theorem OriginalPairing.physical_product (q : Signature ℂ n) (C : OriginalPairing (walsh q))
    (htwo : (2:ℂ)≠0) (H : Consistent (walsh q)) (hd : EqualityDeck (walsh q)) (hn : 6≤n)
    (rho : Fin C.count → ℂˣ)
    (hp : ∀t,C.normalizedLogical htwo H hd hn t=∏i,rho i^(if t i then 1 else 0 : ℕ)) :
    q=productValue C.ports (fun e=>physicalBinary (rho e)) (C.logical (fun _=>false)) := by
  conv_lhs => rw [←physical_of_walsh q,C.analytic_product htwo H hd hn rho hp,
    coordinateAction_productValue]
  rfl

 theorem product_has_proper_factor {r : ℕ} (hr : 2≤r) (p : (Fin r × Bool) ≃ Fin n)
    (A : Fin r → Kernel ℂ) (c : ℂ) (hnon : productValue p A c≠0) :
    Pauli.ExoticKlein.Fiber.HasProperTensorFactor (productValue p A c) := by
  let e : Fin r := ⟨0,by omega⟩
  let B : Tensor ℂ Bool := fun x=>A e (x false) (x true)
  let R : Tensor ℂ (OtherEdges e × Bool) := fun x=>
    c*∏d : OtherEdges e,A d.val (x (d,false)) (x (d,true))
  have he : productValue p A c=Tensor.reindex ((Pauli.ExoticKlein.Fiber.splitEdge e).trans p)
      (Tensor.tensor B R) := by
    funext x
    change c*(∏d,A d (x (p (d,false))) (x (p (d,true))))=
      A e (x (p (e,false))) (x (p (e,true)))*(c*∏d : OtherEdges e,
        A d.val (x (p (d.val,false))) (x (p (d.val,true))))
    rw [Fintype.prod_eq_mul_prod_compl e]
    rw [Finset.prod_subtype (p:=fun d : Fin r=>d≠e) {e}ᶜ (by intro d;simp)]
    ring
  apply Pauli.ExoticKlein.Fiber.factor_of_split _ B R _ (by decide) _ hnon he
  exact Fintype.card_pos_iff.mpr ⟨(⟨⟨1,by omega⟩,by intro h;have hh:=congrArg Fin.val h;change 1=0 at hh;omega⟩,false)⟩

 theorem OriginalPairing.physical_factor (q : Signature ℂ n) (hq : q≠0)
    (C : OriginalPairing (walsh q)) (htwo : (2:ℂ)≠0) (H : Consistent (walsh q))
    (hd : EqualityDeck (walsh q)) (hn : 6≤n) (rho : Fin C.count → ℂˣ)
    (hp : ∀t,C.normalizedLogical htwo H hd hn t=∏i,rho i^(if t i then 1 else 0 : ℕ)) :
    Pauli.ExoticKlein.Fiber.HasProperTensorFactor q := by
  have he := C.physical_product q htwo H hd hn rho hp
  rw [he] at hq ⊢
  exact product_has_proper_factor (by have hh:=C.count_ge_three hn;omega) _ _ _ hq

end Holant.ReedMuller.WeightTwoIntegration
