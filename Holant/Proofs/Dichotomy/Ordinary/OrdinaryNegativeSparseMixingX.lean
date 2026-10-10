import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseMixingCore

/-! Convert every literal opposite bundle into a doubled positive bundle
using actual disequality vertices. One original row and n binary X rows have
n private wires, each used twice; each external logical port is also used
twice. Original normalization scales are retained exactly. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseMixingX
open Holant Holant.Tractable
open OrdinaryNegativeMixedBlockData OrdinaryNegativeSparseMixingCore
open scoped BigOperators
namespace O
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseOccurrences (count_ofFn)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

def arity (n j : ℕ) : ℕ := if j=0 then n+n else 2

def xports {n : ℕ} (i : Fin n) : Fin 2→Bool ⊕ Fin (n+n) :=
  ![.inr (Fin.castAdd n i),.inr (Fin.natAdd n i)]

def recipe (n : ℕ) : Recipe (u:=1) (s:=2) (a:=fun _=>n+n) (b:=arity n) :=
  fun _=>⟨0,Sum.inr⟩::List.ofFn (fun i : Fin n=>⟨1,xports i⟩)

theorem ports_count (n : ℕ) (i : Fin 1) (q : Bool ⊕ Fin (n+n)) :
    (ports (recipe n) i).count q=
      (List.ofFn (Sum.inr : Fin (n+n)→Bool ⊕ Fin (n+n))).count q+
      (List.ofFn (Sum.inr : Fin (n+n)→Bool ⊕ Fin (n+n))).count q := by
  simp only [ports,recipe,List.flatMap_cons,List.count_append]
  congr 1
  simp only [List.count_flatMap,List.map_ofFn,List.sum_ofFn,Function.comp_def,O.count_ofFn]
  change (∑x : Fin n,∑j : Fin 2,if xports x j=q then 1 else 0 : ℕ)=
    ∑j : Fin (n+n),if Sum.inr j=q then 1 else 0
  simp only [Fin.sum_univ_two,xports,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [Finset.sum_add_distrib,Fin.sum_univ_add]

theorem even_recipe (n : ℕ) : EvenRecipe (recipe n) := by
  intro i q
  rw [ports_count]
  exact ⟨_,rfl⟩

variable {K : Type} [CommSemiring K] {n : ℕ}
def table (f : Signature K n) (d : K) (j : Fin 2) : Signature K (arity n j.val) :=
  match j with
  | ⟨0,_⟩ => opposite f
  | ⟨1,_⟩ => fun (x : Fin 2→Bool)=>d*Signature.disequality (x 0) (x 1)
  | ⟨j+2,h⟩ => False.elim (by omega)

theorem coefficient_value (f : Signature K n) (d : K) (w : Fin (n+n)→Bool) :
    coefficient (table f d) (recipe n) 0 w=
      opposite f w*∏i : Fin n,d*Signature.disequality (w (Fin.castAdd n i)) (w (Fin.natAdd n i)) := by
  simp [coefficient,Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue.coefficient,
    recipe,table,arity,List.map_ofFn,List.prod_ofFn,xports]

def trace (f : Signature K n) (d : K) : Signature K n := fun x=>
  ∑y : Fin n→Bool,coefficient (table f d) (recipe n) 0 (Fin.addCases x y)

/-- Exactly one private assignment survives. No virtual negation or parity
edge is available: every flip is evaluated by its actual binary X row. -/
theorem trace_value (f : Signature K n) (d : K) (x : Fin n→Bool) :
    trace f d x=d^n*f x := by
  classical
  unfold trace
  simp_rw [coefficient_value,opposite_addCases]
  rw [Finset.sum_eq_single (fun i=>!(x i))]
  · simp only [ite_true,Fin.addCases_left,Fin.addCases_right]
    have hd (i : Fin n) : Signature.disequality (K:=K) (x i) (!(x i))=1 := by
      cases x i <;> rfl
    simp only [hd,mul_one,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    exact mul_comm _ _
  · intro y _ hy
    simp [hy]
  · simp

theorem scaled_trace (f : Signature K n) (c d : K) (x : Fin n→Bool) :
    trace (fun x=>c*f x) d x=(c*d^n)*f x := by
  rw [trace_value]
  ring

/-- Non-affineness belongs to the actually computed compressed row; it is
preserved with the complete nonzero normalization coefficient. -/
theorem not_affine (f : Signature AlgebraicComplex n) (d : AlgebraicComplex)
    (hd : d≠0) (hf : ¬Affine f) : ¬Affine (trace f d) := by
  intro h
  apply hf
  convert h.scale ((d^n)⁻¹) using 1
  funext x
  rw [trace_value,←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ hd),one_mul]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseMixingX
end
